/-
# The witness that made `checkPrimitiveDef.WF.rest`'s `Nat.gcd` / `Nat.bitwise` branches false

Run with `lake env lean scripts/primitive-wf-refutation.lean`.  It prints eight lines and
asserts nothing, so it never breaks a build; read the table.

`VEnv.HasPrimitives` demands `ReflectsNatNatNat ``Nat.gcd Nat.gcd`, i.e. an `IsDefEqU` between
`Nat.gcd (natLit a) (natLit b)` and `natLit (Nat.gcd a b)` -- *definitional* equality, at
numerals.  Up to 2026-08-30 the recognizer's `Nat.gcd` and `Nat.bitwise` branches placed **no
constraint at all on the measure** `h` that `WellFounded.Nat.fix h F` recurses on.  That is
what this file exhibits: `badGcd` and `badBitwise` below are ordinary, well-typed, terminating
Lean definitions with the *same* bodies as the real ones and a measure that is propositionally
equal to the real one (`n + 0 * Stuck = n`, by `Nat.zero_mul`) but that the **kernel cannot
reduce**, because `Stuck` is `Classical.choice`, an axiom.  `WellFounded.Nat.fix` reduces only
once `h x` evaluates to a ground value -- that is exactly what the `Nat.eager` gadget in its
definition enforces -- so `badGcd 4 6` does not reduce to `2` in the kernel at all.

Before the fix the recognizer accepted both under the names `Nat.gcd` / `Nat.bitwise`.  Since
the kernel refutes `badGcd 4 6 = 2` by `rfl`, `ReflectsNatNatNat` fails for the accepted
declaration, and `PrimitiveResult.preserves` -- hence `checkPrimitiveDef.WF.rest` -- was
**false**, not merely unproved.

Expected output *after* the fix (`measureIs` in `unfoldNatWellFounded`):

```
kernel  Nat.gcd 4 6 = 2          : true
kernel  badGcd  4 6 = 2          : false
kernel  bitwise and 12 10 = 8    : true
kernel  badBitwise and 12 10 = 8 : false
recognizer, real Nat.gcd         : accepted = true
recognizer, badGcd as Nat.gcd    : REJECTED
recognizer, real Nat.bitwise     : accepted = true
recognizer, badBitwise as ~      : REJECTED
```

Before the fix, the two `REJECTED` lines read `accepted = true`.
-/
import Lean4Lean.Primitive
open Lean Lean4Lean

/-- Kernel-opaque: `Classical.choice` is an axiom, so no delta rule reduces it. -/
noncomputable def Stuck : Nat := @Classical.choice Nat ⟨0⟩

theorem stuck_mul (n : Nat) : n + 0 * Stuck = n := by simp

noncomputable def badGcd (m n : Nat) : Nat :=
  if m = 0 then n else badGcd (n % m) m
termination_by m + 0 * Stuck
decreasing_by
  simp only [stuck_mul]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

noncomputable def badBitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then
    if f false true then m else 0
  else if m = 0 then
    if f true false then n else 0
  else
    let n' := n / 2
    let m' := m / 2
    let b₁ := n % 2 = 1
    let b₂ := m % 2 = 1
    let r := badBitwise f n' m'
    if f b₁ b₂ then r + r + 1 else r + r
termination_by n + 0 * Stuck
decreasing_by
  simp only [stuck_mul]
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (Nat.le_refl 2)

/-- Does the *kernel* accept `lhs = rhs` by `rfl`? -/
def kernelRfl (lhs rhs : Expr) : MetaM Bool := do
  let ty := mkApp3 (.const ``Eq [1]) (.const ``Nat []) lhs rhs
  let val := mkApp2 (.const ``rfl [1]) (.const ``Nat []) lhs
  match (← getEnv).toKernelEnv.addDecl {}
      (.thmDecl { name := `__probe, levelParams := [], type := ty, value := val }) with
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
    return s!"accepted = {b}"
  catch _ => return "REJECTED"

run_meta do
  let g (f : Name) := mkApp2 (.const f []) (mkNatLit 4) (mkNatLit 6)
  let b (f : Name) := mkApp3 (.const f []) (.const ``Bool.and []) (mkNatLit 12) (mkNatLit 10)
  IO.println s!"kernel  Nat.gcd 4 6 = 2          : {← kernelRfl (g ``Nat.gcd) (mkNatLit 2)}"
  IO.println s!"kernel  badGcd  4 6 = 2          : {← kernelRfl (g ``badGcd) (mkNatLit 2)}"
  IO.println s!"kernel  bitwise and 12 10 = 8    : {← kernelRfl (b ``Nat.bitwise) (mkNatLit 8)}"
  IO.println s!"kernel  badBitwise and 12 10 = 8 : {← kernelRfl (b ``badBitwise) (mkNatLit 8)}"
  IO.println s!"recognizer, real Nat.gcd         : {← recognizes ``Nat.gcd ``Nat.gcd}"
  IO.println s!"recognizer, badGcd as Nat.gcd    : {← recognizes ``Nat.gcd ``badGcd}"
  IO.println s!"recognizer, real Nat.bitwise     : {← recognizes ``Nat.bitwise ``Nat.bitwise}"
  IO.println s!"recognizer, badBitwise as ~      : {← recognizes ``Nat.bitwise ``badBitwise}"
