/-
# Can a *wrong* body pass the pre-fix `Nat.gcd` / `Nat.bitwise` gate?

Run with `lake env lean scripts/primitive-false-audit.lean`.  It prints a table and asserts
nothing.  Companion to `scripts/primitive-wf-refutation.lean`; see `docs/handoff-primitive-false.md`.

`Lean4Lean.TypeChecker.reduceNat` dispatches on the constant *name*: any two-argument
application of a constant called `Nat.gcd` at two numerals is reduced to the value of the *real*
`Nat.gcd`, whatever the declaration named `Nat.gcd` actually is.  So a declaration named
`Nat.gcd` whose body disagrees with gcd would give `False`:

    theorem e1 : Nat.gcd = myCopy   := rfl   -- same closed value under two names, no reduceNat
    theorem e2 : Nat.gcd 4 6 = 2    := rfl   -- reduceNat, the *real* gcd
    theorem e3 : myCopy  4 6 = 3    := rfl   -- delta, the *declared* body
    -- congrFun e1 .. : Nat.gcd 4 6 = myCopy 4 6, hence 2 = 3, hence False.

The question this file answers empirically: **does the pre-fix gate let such a body through?**
Each row declares a well-typed, terminating Lean definition and asks the pre-fix
`Environment.checkPrimitiveDef` whether it would accept that body *under the name `Nat.gcd`*.
-/
import Lean4Lean.Primitive
open Lean Lean4Lean

/-! ## Measure variations: the body is gcd's, only the termination measure changes. -/

/-- Kernel-opaque: `Classical.choice` is an axiom, so no delta rule reduces it. -/
noncomputable def Stuck : Nat := @Classical.choice Nat ⟨0⟩
theorem stuck_mul (n : Nat) : n + 0 * Stuck = n := by simp

/-- The witness of `scripts/primitive-wf-refutation.lean`: gcd's body, unevaluable measure. -/
noncomputable def badGcd (m n : Nat) : Nat :=
  if m = 0 then n else badGcd (n % m) m
termination_by m + 0 * Stuck
decreasing_by simp only [stuck_mul]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- gcd's body, an evaluable but non-standard measure. -/
def bigGcd (m n : Nat) : Nat :=
  if m = 0 then n else bigGcd (n % m) m
termination_by 2 * m + 7
decreasing_by
  have := Nat.mod_lt n (Nat.pos_of_ne_zero ‹m ≠ 0›)
  omega

/-! ## Body variations: bodies that *disagree* with `Nat.gcd`. -/

/-- Wrong base case.  `w1 0 n = n+1`, so `w1 4 6 = 3` where `Nat.gcd 4 6 = 2`. -/
def w1 (m n : Nat) : Nat :=
  if m = 0 then n + 1 else w1 (n % m) m
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Wrong step: an extra `+1` on the recursive call. -/
def w2 (m n : Nat) : Nat :=
  if m = 0 then n else w2 (n % m) m + 1
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Wrong second argument in the recursive call. -/
def w3 (m n : Nat) : Nat :=
  if m = 0 then n else w3 (n % m) (m + 1)
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Right values, wrong *shape*: `Nat.gcd`'s graph by structural recursion, no `WellFounded.Nat.fix`. -/
def s1 : Nat → Nat → Nat
  | 0, n => n
  | m@(_+1), n => Nat.gcd (n % m) m

/-! ## Bitwise. -/

noncomputable def badBitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then (if f false true then m else 0)
  else if m = 0 then (if f true false then n else 0)
  else
    let r := badBitwise f (n / 2) (m / 2)
    if f (n % 2 = 1) (m % 2 = 1) then r + r + 1 else r + r
termination_by n + 0 * Stuck
decreasing_by
  simp only [stuck_mul]; exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (Nat.le_refl 2)

/-- Wrong bitwise: swaps the two `f` arguments in the recursion's bit test. -/
def wb (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then (if f false true then m else 0)
  else if m = 0 then (if f true false then n else 0)
  else
    let r := wb f (n / 2) (m / 2)
    if f (m % 2 = 1) (n % 2 = 1) then r + r + 1 else r + r
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (Nat.le_refl 2)

/-! ## Instruments. -/

/-- Does the *Lean kernel* accept `lhs = rhs` by `rfl`? -/
def kernelRfl (ty : Expr) (lhs rhs : Expr) : MetaM Bool := do
  let t := mkApp3 (.const ``Eq [1]) ty lhs rhs
  let val := mkApp2 (.const ``rfl [1]) ty lhs
  match (← getEnv).toKernelEnv.addDecl {}
      (.thmDecl { name := `__probe, levelParams := [], type := t, value := val }) with
  | .ok _ => return true
  | .error _ => return false

/-- Does Lean4Lean's primitive recognizer accept `src`'s value declared under the name `as`? -/
def recognizes (as : Name) (src : Name) : MetaM String := do
  let some (.defnInfo bg) := (← getEnv).find? src | throwError "no {src}"
  let v : DefinitionVal :=
    { name := as, levelParams := [], type := bg.type, value := bg.value,
      hints := bg.hints, safety := .safe, all := [as] }
  try
    let (b, _) ← Elab.Term.TermElabM.run (Environment.checkPrimitiveDef v)
    return if b then "ACCEPTED" else "not-a-primitive"
  catch _ => return "rejected"

/-- The escape route's first step: the same closed value under a second name.  `Nat.gcd`'s own
value is `fun m n => Nat.gcd._unary ⟨m, n⟩`; `reduceNat` fires only on a *two-argument*
application of the constant `Nat.gcd`, so comparing the two constants at arity 0 goes through
delta and never touches the native reduction. -/
noncomputable def gcdAlias : Nat → Nat → Nat := fun m n => Nat.gcd._unary ⟨m, n⟩

/-! ## The two `primitives` entries whose *value* nothing constrains.

`Char.ofNat` and `String.ofList` are not `reduceNat` rows, but they are name-dispatched all the
same: `Lean4Lean.Expr.strLitToConstructor` expands a `String` literal into
`String.ofList [Char.ofNat c₁, …]`, and `TypeChecker.tryStringLitExpansion` uses that expansion
in `isDefEq`.  Their branches in `checkPrimitiveDef` check the *declared type* (syntactically)
and nothing else -- no equation on the value at all. -/

def collapseOfNat : Nat → Char := fun _ => ⟨0, by decide⟩
def collapseOfList : List Char → String := fun _ => ""

def nat := Expr.const ``Nat []
def natnatnat : Expr := .forallE `a nat (.forallE `b nat nat .default) .default
def g2 (f : Name) (a b : Nat) := mkApp2 (.const f []) (mkNatLit a) (mkNatLit b)

run_meta do
  IO.println "name        recognizer-as-Nat.gcd   kernel: X 4 6 = 2   kernel: X 4 6 = <wrong>"
  for (n, a, b, gcdv, wrong) in
      [(``Nat.gcd, 4, 6, 2, 3), (``badGcd, 4, 6, 2, 3), (``bigGcd, 4, 6, 2, 3),
       (``w1, 4, 6, 2, 3), (``w2, 4, 6, 2, 4), (``w3, 1, 5, 1, 2), (``s1, 4, 6, 2, 3)] do
    let r ← recognizes ``Nat.gcd n
    let k2 ← kernelRfl nat (g2 n a b) (mkNatLit gcdv)
    let kw ← kernelRfl nat (g2 n a b) (mkNatLit wrong)
    IO.println s!"{n} {a} {b}: {r} | ={gcdv}(gcd): {k2} | ={wrong}(wrong): {kw}"
  IO.println ""
  for n in [``Nat.bitwise, ``badBitwise, ``wb] do
    let r ← recognizes ``Nat.bitwise n
    IO.println s!"{n}  recognizer-as-Nat.bitwise: {r}"
  IO.println ""
  for (as, src) in [(``Char.ofNat, ``collapseOfNat), (``String.ofList, ``collapseOfList)] do
    IO.println s!"recognizer, constant-function {as}: {← recognizes as src}"
  IO.println ""
  IO.println "-- the escape route around reduceNat's name dispatch --"
  IO.println s!"kernel: (Nat.gcd = gcdAlias) by rfl : \
{← kernelRfl natnatnat (.const ``Nat.gcd []) (.const ``gcdAlias [])}"
  IO.println s!"kernel: Nat.gcd 4 6 = 2   by rfl : {← kernelRfl nat (g2 ``Nat.gcd 4 6) (mkNatLit 2)}"
  IO.println s!"kernel: gcdAlias 4 6 = 2  by rfl : {← kernelRfl nat (g2 ``gcdAlias 4 6) (mkNatLit 2)}"

/-! ## The mathematical core of the verdict.

The pre-fix gate does not pin `Nat.gcd`'s *reduction behaviour*, but it does pin its *values*.
What it forces (see `docs/handoff-primitive-false.md` for the derivation) is exactly these two
recurrences, propositionally, with the environment's own -- separately gated -- `Nat.mod`.
These two theorems say that that is already enough to determine the function. -/

theorem gcd_unique (g : Nat → Nat → Nat)
    (h0 : ∀ m, g 0 m = m)
    (hs : ∀ n m, g (n+1) m = g (m % (n+1)) (n+1)) :
    ∀ a b, g a b = Nat.gcd a b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    match a with
    | 0 => simpa using (h0 b).trans (Nat.gcd_zero_left b).symm
    | (n+1) =>
      rw [hs n b, Nat.gcd_succ]
      exact ih _ (Nat.mod_lt _ (Nat.succ_pos n)) _

theorem bitwise_unique (g : (Bool → Bool → Bool) → Nat → Nat → Nat)
    (hg : ∀ f n m, g f n m =
      if n = 0 then (if f false true then m else 0)
      else if m = 0 then (if f true false then n else 0)
      else
        let n' := n / 2
        let m' := m / 2
        let b₁ := n % 2 = 1
        let b₂ := m % 2 = 1
        let r := g f n' m'
        if f (decide b₁) (decide b₂) then r + r + 1 else r + r) :
    ∀ f n m, g f n m = Nat.bitwise f n m := by
  intro f n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m
    rw [hg, Nat.bitwise]
    split
    · rfl
    · next hn =>
      split
      · rfl
      · simp only []
        rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
