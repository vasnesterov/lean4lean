import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Primitive

/-!
# Reflection lemmas for the primitive `Nat` operations

`Lean4Lean/Primitive.lean` recognizes a handful of `Nat` definitions by comparing their values
against a fixed set of defining equations, and the kernel then evaluates those constants with
GMP arithmetic.  The semantic content of that trade is `VEnv.HasPrimitives`, whose fields
(`VEnv.ReflectsNatNat`, `…NatNat`, `…NatNatBool`) say that applying the constant to numerals is
`IsDefEqU` to the numeral of the answer.

This module proves those reflection facts for the nine **structurally recursive** operations:

    Nat.add  Nat.pred  Nat.sub  Nat.mul  Nat.pow  Nat.beq  Nat.ble
    Nat.shiftLeft  Nat.shiftRight

The remaining seven (`Nat.mod`, `Nat.div`, `Nat.gcd`, `Nat.bitwise`, `Nat.land`, `Nat.lor`,
`Nat.xor`) recurse through fuel or `WellFounded.Nat.fix` and are not treated here.

Everything is stated for an abstract `F : VExpr` standing for the *value* of the definition,
with hypotheses in the "instantiated at numerals" form.  `Lean4Lean/Verify/Environment/
Boundaries.lean` is expected to produce those from the recognizer's `isDefEq` checks by

* `TypeChecker.isDefEq.WF`, giving `IsDefEqU 0 Δ.toCtx _ _` under the `withLocalDecl`-bound
  free variables (so `Δ.toCtx` is `[.nat]` or `[.nat, .nat]`), then
* `IsDefEqU.instNat` / `IsDefEqU.instNat2` below, substituting numerals for those variables, and
* `VEnv.ReflectsNatNatNat.of_defeq` &c., transporting from the value `F` to the constant
  `.const fc []` along the defining equation added by `VEnv.addDefEq`.

The main reusable pieces are:

* `VEnv.HasPrimitives.natLit_hasType` and `VEnv.NatLits` — numerals are `Nat`s.  The reflection
  lemmas take `NatLits`, not the whole `HasPrimitives` record: at the assembly site the
  reflection fact has to hold in the *extended* environment, whose `HasPrimitives` record is
  the thing being built, so requiring the record would be circular.  `NatLits` transfers from
  the smaller environment by `VEnv.NatLits.mono`, and so do the auxiliary reflection facts the
  `Nat.sub`/`mul`/`pow`/`shiftLeft`/`shiftRight` branches consume (`hprim.natPred hc` &c.);
* `IsDefEqU.app_congr_arg`, `IsDefEqU.app2_congr_arg1`, `IsDefEqU.app_congr_fn` — congruence
  that extracts the typing it needs from the equation it is chaining onto, so no separate
  hypothesis about the type of the operator is required;
* `VEnv.reflects_rec2`, `VEnv.reflects_rec2_tail`, `VEnv.reflects_rec2_diag` — the three
  recursion shapes the nine operations fall into;
* `VEnv.PrimField`, `VEnv.HasPrimitives.addDef`, `VEnv.const_defeq_value` — the environment
  side: which single `HasPrimitives` field a declaration is responsible for, how the other
  twenty-one transfer across the step that adds it, and the defining equation
  `.const v.name [] ≡ v.value` that step contributes.

A finished branch therefore reads, e.g. for `Nat.add`,

    VEnv.ReflectsNatNatNat.of_defeq henv hlit hFty hdef
      (VEnv.reflects_natAdd henv hlit h0 hS)

where `h0`/`hS` come from `IsDefEqU.instNat`/`IsDefEqU.instNat2`; the resulting `VExpr.inst`
applications are computed by `simp [VExpr.inst]` together with the `@[simp]` lemmas below and
`VExpr.ClosedN.instN_eq` for the value `F` itself (which is closed, by `IsDefEq.closedN`
applied to `hFty`).  Feeding that to `primField_Nat_add.2` and `VEnv.HasPrimitives.addDef`
yields the `HasPrimitives` record `PrimitiveResult.preserves` demands.

**`checkPrimitiveDef.WF` cannot yet consume any of this**: the recognizer calls
`TypeChecker.isDefEq` on `v.type` and on terms built from `v.value` before either has been
type-checked, which pollutes the `EquivManager` and makes `TypeChecker.VState.WF` — hence the
`M.WF` obligation — fail.  See the docstring of `checkPrimitiveDef.WF` in
`Lean4Lean/Verify/Environment/Boundaries.lean` for the counterexample and the required change
to `Lean4Lean/Primitive.lean`.

Note that `checkPrimitiveDef`'s `defeq2` binds the outer variable first, so `bvar 1` is the
*outer* one; which of the two is the operation's first argument differs per branch
(`Nat.add` uses the outer one, `Nat.shiftLeft` the inner one).  The statements below are phrased
in terms of the arguments of `F`, not of the binders, so they are unambiguous.
-/

namespace Lean4Lean
open Lean4Lean VEnv

/-! ## Numerals in `VExpr` -/

namespace VExpr

theorem natLit_zero : VExpr.natLit 0 = .natZero := rfl

theorem natLit_succ (n : Nat) : VExpr.natLit (n + 1) = .app .natSucc (.natLit n) := rfl

theorem natLit_one : VExpr.natLit 1 = .app .natSucc .natZero := rfl

/-- The `two` the `Nat.shiftLeft`/`Nat.shiftRight` branches of the recognizer build. -/
theorem natLit_two : VExpr.natLit 2 = .app .natSucc (.app .natSucc .natZero) := rfl

@[simp] theorem inst_nat : VExpr.nat.inst e k = .nat := rfl
@[simp] theorem inst_natZero : VExpr.natZero.inst e k = .natZero := rfl
@[simp] theorem inst_natSucc : VExpr.natSucc.inst e k = .natSucc := rfl
@[simp] theorem inst_bool : VExpr.bool.inst e k = .bool := rfl
@[simp] theorem inst_boolFalse : VExpr.boolFalse.inst e k = .boolFalse := rfl
@[simp] theorem inst_boolTrue : VExpr.boolTrue.inst e k = .boolTrue := rfl

@[simp] theorem inst_natLit (n : Nat) : (VExpr.natLit n).inst e k = .natLit n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natLit_succ, VExpr.inst, inst_natSucc, ih]

@[simp] theorem inst_boolLit (b : Bool) : (VExpr.boolLit b).inst e k = .boolLit b := by
  cases b <;> rfl

theorem closedN_natLit (n : Nat) : (VExpr.natLit n).ClosedN k := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨trivial, ih⟩

end VExpr

/-! ## Typing of numerals -/

namespace VEnv.HasPrimitives

variable {env : VEnv} {Γ : List VExpr}

theorem natZero_hasType (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) :
    env.HasType 0 Γ .natZero .nat := by
  obtain ⟨⟨_, h⟩, -⟩ := hprim.nat hnat
  cases hprim.natZero h
  exact HasType.const (U := 0) (Γ := Γ) (ls := []) h (by simp) rfl

theorem natSucc_hasType (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) :
    env.HasType 0 Γ .natSucc (.forallE .nat .nat) := by
  obtain ⟨-, ⟨_, h⟩⟩ := hprim.nat hnat
  cases hprim.natSucc h
  exact HasType.const (U := 0) (Γ := Γ) (ls := []) h (by simp) rfl

theorem natLit_hasType (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) :
    ∀ n, env.HasType 0 Γ (.natLit n) .nat
  | 0 => hprim.natZero_hasType hnat
  | n + 1 => by
    have := (hprim.natSucc_hasType hnat (Γ := Γ)).app (hprim.natLit_hasType hnat n)
    rwa [VExpr.inst_nat] at this

theorem boolFalse_hasType (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) :
    env.HasType 0 Γ .boolFalse .bool := by
  obtain ⟨⟨_, h⟩, -⟩ := hprim.bool hbool
  cases hprim.boolFalse h
  exact HasType.const (U := 0) (Γ := Γ) (ls := []) h (by simp) rfl

theorem boolTrue_hasType (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) :
    env.HasType 0 Γ .boolTrue .bool := by
  obtain ⟨-, ⟨_, h⟩⟩ := hprim.bool hbool
  cases hprim.boolTrue h
  exact HasType.const (U := 0) (Γ := Γ) (ls := []) h (by simp) rfl

theorem boolLit_hasType (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) :
    ∀ b, env.HasType 0 Γ (.boolLit b) .bool
  | false => hprim.boolFalse_hasType hbool
  | true => hprim.boolTrue_hasType hbool

end VEnv.HasPrimitives

/-- Everything the reflection lemmas below need from `VEnv.HasPrimitives`: numerals are `Nat`s.
Taking this rather than the whole record matters at the assembly site, where the reflection
fact has to be established in the *extended* environment whose `HasPrimitives` record is what
is being built -- passing the record itself would be circular, while `NatLits` transfers from
the smaller environment by `NatLits.mono`. -/
def VEnv.NatLits (env : VEnv) : Prop := ∀ n : Nat, env.HasType 0 [] (.natLit n) .nat

theorem VEnv.HasPrimitives.natLits {env : VEnv} (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) : env.NatLits := fun n => hprim.natLit_hasType hnat n

theorem VEnv.NatLits.mono {env env' : VEnv} (hle : env ≤ env') (h : env.NatLits) : env'.NatLits :=
  fun n => (h n).mono hle

/-- The `Bool` analogue of `VEnv.NatLits`, for the `Nat.land`/`lor`/`xor` branches, whose
recognizer compares open terms under a `Bool`-typed free variable. -/
def VEnv.BoolLits (env : VEnv) : Prop := ∀ b : Bool, env.HasType 0 [] (.boolLit b) .bool

theorem VEnv.HasPrimitives.boolLits {env : VEnv} (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) : env.BoolLits := fun b => hprim.boolLit_hasType hbool b

theorem VEnv.BoolLits.mono {env env' : VEnv} (hle : env ≤ env') (h : env.BoolLits) :
    env'.BoolLits := fun b => (h b).mono hle

/-! ## Congruence

The recognizer never checks the *type* of an auxiliary constant such as `Nat.pred`, so a
congruence rule that demanded `env.HasType 0 [] (.const ``Nat.pred []) (.forallE .nat .nat)`
would not be usable.  Instead each rule below reads the typing it needs off the very equation
it is chaining onto: `hu` witnesses that the application at the numeral is well-typed, and
`HasType.app_inv` recovers the operator's Π-type from it. -/

namespace VEnv

variable {env : VEnv}

/-- Replace the argument of an application by anything defeq to it, chaining onto an equation
`.app u a ≡ w` which also supplies the well-typedness of `.app u a`. -/
theorem IsDefEqU.app_congr_arg (henv : env.WF) {u a a' w : VExpr}
    (hu : env.IsDefEqU 0 [] (.app u a) w) (h : env.IsDefEqU 0 [] a' a) :
    env.IsDefEqU 0 [] (.app u a') w := by
  obtain ⟨_, hu'⟩ := hu
  obtain ⟨_, _, h1, h2⟩ :=
    VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial ⟨_, hu'.hasType.1⟩
  exact IsDefEqU.trans henv trivial ⟨_, .appDF h1 (h.of_r henv trivial h2)⟩ ⟨_, hu'⟩

/-- Replace the *first* argument of a two-argument application. -/
theorem IsDefEqU.app2_congr_arg1 (henv : env.WF) {u a a' v w : VExpr}
    (hu : env.IsDefEqU 0 [] (.app (.app u a) v) w) (h : env.IsDefEqU 0 [] a' a) :
    env.IsDefEqU 0 [] (.app (.app u a') v) w := by
  obtain ⟨_, hu'⟩ := hu
  obtain ⟨_, _, h1, h2⟩ :=
    VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial ⟨_, hu'.hasType.1⟩
  have key : env.IsDefEqU 0 [] (.app u a') (.app u a) :=
    IsDefEqU.app_congr_arg henv ⟨_, h1⟩ h
  exact IsDefEqU.trans henv trivial ⟨_, .appDF (key.of_r henv trivial h1) h2⟩ ⟨_, hu'⟩

/-- Replace the head of an application. -/
theorem IsDefEqU.app_congr_fn (henv : env.WF) {f g a A B : VExpr}
    (hf : env.IsDefEqU 0 [] f g) (hg : env.HasType 0 [] g (.forallE A B))
    (ha : env.HasType 0 [] a A) :
    env.IsDefEqU 0 [] (.app f a) (.app g a) :=
  ⟨_, .appDF (hf.of_r henv trivial hg) ha⟩

/-! ## From the recognizer's open equations to closed instances

`Lean4Lean/Primitive.lean` compares open terms under `withLocalDecl`-bound `Nat` variables, so
the equations arrive in a context `.nat :: Γ`.  These lemmas substitute numerals for those
variables. -/

theorem IsDefEqU.instNat (henv : env.WF) (hlit : env.NatLits)
    {Γ : List VExpr} {e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 (.nat :: Γ) e₁ e₂) (n : Nat) :
    env.IsDefEqU 0 Γ (e₁.inst (.natLit n)) (e₂.inst (.natLit n)) :=
  IsDefEqU.instN henv.ordered .zero H ((hlit n).weak0 henv.ordered)

/-- The `Bool` analogue of `IsDefEqU.instNat`. -/
theorem IsDefEqU.instBool (henv : env.WF) (hlit : env.BoolLits)
    {Γ : List VExpr} {e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 (.bool :: Γ) e₁ e₂) (b : Bool) :
    env.IsDefEqU 0 Γ (e₁.inst (.boolLit b)) (e₂.inst (.boolLit b)) :=
  IsDefEqU.instN henv.ordered .zero H ((hlit b).weak0 henv.ordered)

/-- Two nested `withLocalDecl`s.  `checkPrimitiveDef`'s `defeq2` introduces its `y` binder
first, so `bvar 1` is `y` and `bvar 0` is the inner `x`: here `n` is substituted for `bvar 0`
and `m` for `bvar 1`. -/
theorem IsDefEqU.instNat2 (henv : env.WF) (hlit : env.NatLits) {e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 [.nat, .nat] e₁ e₂) (m n : Nat) :
    env.IsDefEqU 0 [] ((e₁.inst (.natLit n)).inst (.natLit m))
      ((e₂.inst (.natLit n)).inst (.natLit m)) :=
  (H.instNat henv hlit n).instNat henv hlit m

/-! ## Recursion shapes

All nine in-scope operations are instances of one of the three principles below. -/

/-- **Structural recursion on the second argument.**  `S a e` is the term the recognizer
compares `F a (b+1)` against, with `e` in the recursive-call slot; `hSrefl` says `S` reflects
the intended step once that slot holds a numeral, which is exactly what
`IsDefEqU.app_congr_arg` / `IsDefEqU.app2_congr_arg1` deliver. -/
theorem reflects_rec2 (henv : env.WF) {F : VExpr} {S : Nat → VExpr → VExpr}
    {g : Nat → Nat → Nat}
    (h0 : ∀ a, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit 0)) (.natLit (g a 0)))
    (hS : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit (b + 1)))
      (S a (.app (.app F (.natLit a)) (.natLit b))))
    (hSrefl : ∀ a b e, env.IsDefEqU 0 [] e (.natLit (g a b)) →
      env.IsDefEqU 0 [] (S a e) (.natLit (g a (b + 1)))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (g a b)) := by
  intro a b
  induction b with
  | zero => exact h0 a
  | succ b ih => exact IsDefEqU.trans henv trivial (hS a b) (hSrefl a b _ ih)

/-- **Tail recursion on the second argument, transforming the first.**  This is the shape of
`Nat.shiftLeft`, whose recognizer equation is `shl x (succ y) ≡ shl (mul 2 x) y`: the induction
has to be generalized over the first argument. -/
theorem reflects_rec2_tail (henv : env.WF) {F : VExpr} {T : Nat → VExpr} {t : Nat → Nat}
    {g : Nat → Nat → Nat}
    (h0 : ∀ a, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit 0)) (.natLit (g a 0)))
    (hS : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit (b + 1)))
      (.app (.app F (T a)) (.natLit b)))
    (hT : ∀ a, env.IsDefEqU 0 [] (T a) (.natLit (t a)))
    (hg : ∀ a b, g a (b + 1) = g (t a) b) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (g a b)) := by
  intro a b
  induction b generalizing a with
  | zero => exact h0 a
  | succ b ih =>
    refine IsDefEqU.trans henv trivial (hS a b) ?_
    rw [hg]
    exact IsDefEqU.app2_congr_arg1 henv (ih (t a)) (hT a)

/-- **Recursion on both arguments simultaneously**, as `Nat.beq` and `Nat.ble` are defined.
The result lives in an arbitrary type of literals so that this covers `Bool`-valued
operations. -/
theorem reflects_rec2_diag (henv : env.WF) {α : Type _} {F : VExpr} {lit : α → VExpr}
    {g : Nat → Nat → α}
    (h00 : env.IsDefEqU 0 [] (.app (.app F (.natLit 0)) (.natLit 0)) (lit (g 0 0)))
    (h0S : ∀ b, env.IsDefEqU 0 [] (.app (.app F (.natLit 0)) (.natLit (b + 1)))
      (lit (g 0 (b + 1))))
    (hS0 : ∀ a, env.IsDefEqU 0 [] (.app (.app F (.natLit (a + 1))) (.natLit 0))
      (lit (g (a + 1) 0)))
    (hSS : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit (a + 1))) (.natLit (b + 1)))
      (.app (.app F (.natLit a)) (.natLit b)))
    (hg : ∀ a b, g (a + 1) (b + 1) = g a b) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (lit (g a b)) := by
  intro a
  induction a with
  | zero => intro b; cases b with
    | zero => exact h00
    | succ b => exact h0S b
  | succ a ih => intro b; cases b with
    | zero => exact hS0 a
    | succ b => rw [hg]; exact IsDefEqU.trans henv trivial (hSS a b) (ih b)

/-! ## Transport from the definition's value to its constant

After `VEnv.addDefEq`, `IsDefEq.extra0` gives `.const fc [] ≡ F`; these lemmas push that through
the two arguments.  `hFty` is available from the recognizer's `isDefEq v.type q(Nat → …)` check
together with `TrDefVal`'s `env.HasType 0 [] F type'`. -/

theorem ReflectsNatNat.of_defeq (henv : env.WF) (hlit : env.NatLits)
    {fc : Name} {F : VExpr} {g : Nat → Nat}
    (hFty : env.HasType 0 [] F (.forallE .nat .nat))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a, env.IsDefEqU 0 [] (.app F (.natLit a)) (.natLit (g a))) :
    env.ReflectsNatNat fc g := by
  intro _ a
  refine IsDefEqU.trans henv trivial ?_ (H a)
  exact IsDefEqU.app_congr_fn henv hdef hFty (hlit a)

theorem ReflectsNatNatNat.of_defeq (henv : env.WF) (hlit : env.NatLits)
    {fc : Name} {F : VExpr} {g : Nat → Nat → Nat}
    (hFty : env.HasType 0 [] F (.forallE .nat (.forallE .nat .nat)))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (g a b))) :
    env.ReflectsNatNatNat fc g := by
  intro _ a b
  refine IsDefEqU.trans henv trivial ?_ (H a b)
  have h1 : env.IsDefEqU 0 [] (.app (.const fc []) (.natLit a)) (.app F (.natLit a)) :=
    IsDefEqU.app_congr_fn henv hdef hFty (hlit a)
  have h2 : env.HasType 0 [] (.app F (.natLit a)) (.forallE .nat .nat) := by
    have := hFty.app (hlit a)
    rwa [VExpr.inst, VExpr.inst_nat, VExpr.inst_nat] at this
  exact IsDefEqU.app_congr_fn henv h1 h2 (hlit b)

theorem ReflectsNatNatBool.of_defeq (henv : env.WF) (hlit : env.NatLits)
    {fc : Name} {F : VExpr} {g : Nat → Nat → Bool}
    (hFty : env.HasType 0 [] F (.forallE .nat (.forallE .nat .bool)))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.boolLit (g a b))) :
    env.ReflectsNatNatBool fc g := by
  intro _ a b
  refine IsDefEqU.trans henv trivial ?_ (H a b)
  have h1 : env.IsDefEqU 0 [] (.app (.const fc []) (.natLit a)) (.app F (.natLit a)) :=
    IsDefEqU.app_congr_fn henv hdef hFty (hlit a)
  have h2 : env.HasType 0 [] (.app F (.natLit a)) (.forallE .nat .bool) := by
    have := hFty.app (hlit a)
    rwa [VExpr.inst, VExpr.inst_nat, VExpr.inst_bool] at this
  exact IsDefEqU.app_congr_fn henv h1 h2 (hlit b)

end VEnv

/-! ## The nine operations

Each hypothesis is written in exactly the shape `Lean4Lean.Environment.checkPrimitiveDef`
produces after `IsDefEqU.instNat`/`IsDefEqU.instNat2`: `zero` is `VExpr.natZero`, `succ e` is
`.app VExpr.natSucc e`, and in `defeq2` the *outer* binder `y` is the first argument. -/

namespace VEnv

variable {env : VEnv}

/-- `Nat.add`: `add x 0 ≡ x` and `add y (succ x) ≡ succ (add y x)`. -/
theorem reflects_natAdd (henv : env.WF) (hlit : env.NatLits) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app .natSucc (.app (.app F (.natLit a)) (.natLit b)))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.add a b)) := by
  refine reflects_rec2 henv (S := fun _ e => .app .natSucc e) (g := Nat.add) h0 hS ?_
  intro a b e he
  refine IsDefEqU.app_congr_arg henv (a := .natLit (Nat.add a b)) ?_ he
  exact ⟨_, hlit (Nat.add a (b + 1))⟩

/-- `Nat.pred`: `pred 0 ≡ 0` and `pred (succ x) ≡ x`.  Not a recursion. -/
theorem reflects_natPred {F : VExpr}
    (h0 : env.IsDefEqU 0 [] (.app F .natZero) .natZero)
    (hS : ∀ a : Nat, env.IsDefEqU 0 [] (.app F (.app .natSucc (.natLit a))) (.natLit a)) :
    ∀ a, env.IsDefEqU 0 [] (.app F (.natLit a)) (.natLit (Nat.pred a))
  | 0 => h0
  | _ + 1 => hS _

/-- `Nat.sub`: `sub x 0 ≡ x` and `sub y (succ x) ≡ Nat.pred (sub y x)`. -/
theorem reflects_natSub (henv : env.WF)
    (hpred : ∀ n : Nat, env.IsDefEqU 0 []
      (.app (.const ``Nat.pred []) (.natLit n)) (.natLit (Nat.pred n))) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.const ``Nat.pred []) (.app (.app F (.natLit a)) (.natLit b)))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.sub a b)) := by
  refine reflects_rec2 henv (S := fun _ e => .app (.const ``Nat.pred []) e) (g := Nat.sub)
    h0 hS ?_
  intro a b e he
  exact IsDefEqU.app_congr_arg henv (hpred (Nat.sub a b)) he

/-- `Nat.mul`: `mul x 0 ≡ 0` and `mul y (succ x) ≡ Nat.add (mul y x) y`. -/
theorem reflects_natMul (henv : env.WF)
    (hadd : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.add []) (.natLit a)) (.natLit b)) (.natLit (Nat.add a b)))
    {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) .natZero)
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app (.const ``Nat.add []) (.app (.app F (.natLit a)) (.natLit b))) (.natLit a))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.mul a b)) := by
  refine reflects_rec2 henv
    (S := fun a e => .app (.app (.const ``Nat.add []) e) (.natLit a)) (g := Nat.mul) h0 hS ?_
  intro a b e he
  exact IsDefEqU.app2_congr_arg1 henv (hadd (Nat.mul a b) a) he

/-- `Nat.pow`: `pow x 0 ≡ 1` and `pow y (succ x) ≡ Nat.mul (pow y x) y`. -/
theorem reflects_natPow (henv : env.WF)
    (hmul : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mul []) (.natLit a)) (.natLit b)) (.natLit (Nat.mul a b)))
    {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero)
      (.app .natSucc .natZero))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app (.const ``Nat.mul []) (.app (.app F (.natLit a)) (.natLit b))) (.natLit a))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.pow a b)) := by
  refine reflects_rec2 henv
    (S := fun a e => .app (.app (.const ``Nat.mul []) e) (.natLit a)) (g := Nat.pow) h0 hS ?_
  intro a b e he
  exact IsDefEqU.app2_congr_arg1 henv (hmul (Nat.pow a b) a) he

/-- `Nat.beq`. -/
theorem reflects_natBEq (henv : env.WF) {F : VExpr}
    (h00 : env.IsDefEqU 0 [] (.app (.app F .natZero) .natZero) .boolTrue)
    (h0S : ∀ b : Nat, env.IsDefEqU 0 []
      (.app (.app F .natZero) (.app .natSucc (.natLit b))) .boolFalse)
    (hS0 : ∀ a : Nat, env.IsDefEqU 0 []
      (.app (.app F (.app .natSucc (.natLit a))) .natZero) .boolFalse)
    (hSS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.app .natSucc (.natLit a))) (.app .natSucc (.natLit b)))
      (.app (.app F (.natLit a)) (.natLit b))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b))
      (.boolLit (Nat.beq a b)) :=
  reflects_rec2_diag henv (lit := VExpr.boolLit) (g := Nat.beq)
    h00 h0S hS0 hSS (fun _ _ => rfl)

/-- `Nat.ble`. -/
theorem reflects_natBLE (henv : env.WF) {F : VExpr}
    (h00 : env.IsDefEqU 0 [] (.app (.app F .natZero) .natZero) .boolTrue)
    (h0S : ∀ b : Nat, env.IsDefEqU 0 []
      (.app (.app F .natZero) (.app .natSucc (.natLit b))) .boolTrue)
    (hS0 : ∀ a : Nat, env.IsDefEqU 0 []
      (.app (.app F (.app .natSucc (.natLit a))) .natZero) .boolFalse)
    (hSS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.app .natSucc (.natLit a))) (.app .natSucc (.natLit b)))
      (.app (.app F (.natLit a)) (.natLit b))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b))
      (.boolLit (Nat.ble a b)) :=
  reflects_rec2_diag henv (lit := VExpr.boolLit) (g := Nat.ble)
    h00 h0S hS0 hSS (fun _ _ => rfl)

/-- `Nat.shiftLeft`: `shl x 0 ≡ x` and `shl x (succ y) ≡ shl (Nat.mul 2 x) y`.  Note that here
the recognizer's `defeq2` binds `y` outermost, so the *second* argument is the outer one. -/
theorem reflects_natShiftLeft (henv : env.WF)
    (hmul : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mul []) (.natLit a)) (.natLit b)) (.natLit (Nat.mul a b)))
    {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app F (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.natLit a))) (.natLit b))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b))
      (.natLit (Nat.shiftLeft a b)) := by
  refine reflects_rec2_tail henv
    (T := fun a => .app (.app (.const ``Nat.mul []) (.natLit 2)) (.natLit a))
    (t := fun a => Nat.mul 2 a) (g := Nat.shiftLeft) h0 hS ?_ (fun _ _ => rfl)
  intro a
  exact hmul 2 a

/-- `Nat.shiftRight`: `shr x 0 ≡ x` and `shr x (succ y) ≡ Nat.div (shr x y) 2`. -/
theorem reflects_natShiftRight (henv : env.WF)
    (hdiv : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.div []) (.natLit a)) (.natLit b)) (.natLit (Nat.div a b)))
    {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app (.const ``Nat.div []) (.app (.app F (.natLit a)) (.natLit b))) (.natLit 2))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b))
      (.natLit (Nat.shiftRight a b)) := by
  refine reflects_rec2 henv
    (S := fun _ e => .app (.app (.const ``Nat.div []) e) (.natLit 2)) (g := Nat.shiftRight)
    h0 hS ?_
  intro a b e he
  exact IsDefEqU.app2_congr_arg1 henv (hdiv (Nat.shiftRight a b) 2) he

end VEnv


/-! ## The three operations built on `Nat.bitwise`

`Nat.land`, `Nat.lor` and `Nat.xor` are literally `Nat.bitwise` applied to a boolean
combinator, and their recognizer branches check only that combinator's truth table.  The
recursion is entirely inside `Nat.bitwise`, whose reflection is the `HasPrimitives` field
`natBitwise` -- and that field is relativized to every extension precisely so that it can be
used here, where the combinator is a term of the *later* declaration. -/

namespace VEnv

variable {env : VEnv}

/-- `Nat.bitwise` applied to a combinator whose truth table is known.  This is
`VEnv.HasPrimitives.natBitwise` instantiated at the environment itself. -/
theorem reflects_natBitwiseApp (hbw : env.ReflectsNatBitwise) (hc : env.contains ``Nat.bitwise)
    {f : VExpr} {g : Bool → Bool → Bool} (hf : env.ReflectsBoolBoolBool f g) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise g a b)) :=
  hbw hc env VEnv.LE.rfl f g hf a b

/-- `Nat.land`'s combinator: the recognizer checks `and false x ≡ false` and `and true x ≡ x`
under a `Bool`-typed free variable. -/
theorem reflectsBoolBoolBool_and {f : VExpr}
    (h0 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolFalse) (.boolLit b)) .boolFalse)
    (h1 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolTrue) (.boolLit b)) (.boolLit b)) :
    env.ReflectsBoolBoolBool f and
  | false, b => h0 b
  | true, b => h1 b

/-- `Nat.lor`'s combinator: `or false x ≡ x` and `or true x ≡ true`. -/
theorem reflectsBoolBoolBool_or {f : VExpr}
    (h0 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolFalse) (.boolLit b)) (.boolLit b))
    (h1 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolTrue) (.boolLit b)) .boolTrue) :
    env.ReflectsBoolBoolBool f or
  | false, b => h0 b
  | true, b => h1 b

/-- `Nat.xor`'s combinator is `bne`, and the recognizer checks all four closed cases. -/
theorem reflectsBoolBoolBool_bne {f : VExpr}
    (hff : env.IsDefEqU 0 [] (.app (.app f .boolFalse) .boolFalse) .boolFalse)
    (htf : env.IsDefEqU 0 [] (.app (.app f .boolTrue) .boolFalse) .boolTrue)
    (hft : env.IsDefEqU 0 [] (.app (.app f .boolFalse) .boolTrue) .boolTrue)
    (htt : env.IsDefEqU 0 [] (.app (.app f .boolTrue) .boolTrue) .boolFalse) :
    env.ReflectsBoolBoolBool f bne
  | false, false => hff
  | true, false => htf
  | false, true => hft
  | true, true => htt

/-- `Nat.land`, whose value the recognizer destructures as `Nat.bitwise and`. -/
theorem reflects_natLAnd (hbw : env.ReflectsNatBitwise) (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f and) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.land a b)) := reflects_natBitwiseApp hbw hc hf a b

/-- `Nat.lor`, whose value the recognizer destructures as `Nat.bitwise or`. -/
theorem reflects_natLOr (hbw : env.ReflectsNatBitwise) (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f or) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.lor a b)) := reflects_natBitwiseApp hbw hc hf a b

/-- `Nat.xor`, whose value the recognizer destructures as `Nat.bitwise bne`. -/
theorem reflects_natXor (hbw : env.ReflectsNatBitwise) (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f bne) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.xor a b)) := reflects_natBitwiseApp hbw hc hf a b

end VEnv

/-! ## Transferring `VEnv.HasPrimitives` across the step that adds one constant

`PrimitiveResult.preserves` in `Lean4Lean/Verify/Environment/Boundaries.lean` must produce a
whole `VEnv.HasPrimitives` record for `(env'.addDefEq ci'.toDefEq)`, given one for the
environment the recognizer ran in.  Twenty-one of the twenty-two fields are about names other
than the one being declared, so they transfer mechanically; the twenty-second is the branch's
actual content.  `VEnv.PrimField` names that field and `VEnv.HasPrimitives.addDef` does the
transfer, so a recognizer branch only ever has to supply `PrimField`. -/

namespace VEnv

variable {env env' : VEnv}

theorem contains.mono (hle : env ≤ env') (h : env.contains n) : env'.contains n :=
  let ⟨_, hci⟩ := h; ⟨_, hle.1 hci⟩

theorem contains_of_constants_eq (hc : env'.constants n = env.constants n)
    (h : env'.contains n) : env.contains n :=
  let ⟨ci, hci⟩ := h; ⟨ci, hc ▸ hci⟩

theorem constants_addConst {n m : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') (hm : m ≠ n) : env'.constants m = env.constants m := by
  rw [VEnv.addConst] at h
  split at h
  · exact absurd h nofun
  · cases h; simp [Ne.symm hm]

theorem constants_addConst_addDefEq {n m : Name} {ci : VConstant} {df : VDefEq}
    (h : env.addConst n ci = some env') (hm : m ≠ n) :
    (env'.addDefEq df).constants m = env.constants m := by
  show env'.constants m = env.constants m; exact constants_addConst h hm

theorem constants_self_addDefEq {n : Name} {ci : VConstant} {df : VDefEq}
    (h : env.addConst n ci = some env') : (env'.addDefEq df).constants n = some ci := by
  show env'.constants n = some ci; exact VEnv.addConst_self h

theorem ReflectsNatNat.mono {fc g} (hle : env ≤ env')
    (hc : env'.constants fc = env.constants fc) (H : env.ReflectsNatNat fc g) :
    env'.ReflectsNatNat fc g := fun h a => (H (contains_of_constants_eq hc h) a).mono hle

theorem ReflectsNatNatNat.mono {fc g} (hle : env ≤ env')
    (hc : env'.constants fc = env.constants fc) (H : env.ReflectsNatNatNat fc g) :
    env'.ReflectsNatNatNat fc g := fun h a b => (H (contains_of_constants_eq hc h) a b).mono hle

theorem ReflectsNatNatBool.mono {fc g} (hle : env ≤ env')
    (hc : env'.constants fc = env.constants fc) (H : env.ReflectsNatNatBool fc g) :
    env'.ReflectsNatNatBool fc g := fun h a b => (H (contains_of_constants_eq hc h) a b).mono hle

/-- `ReflectsNatBitwise` is already relativized to every extension, so it transfers without
touching its `ReflectsBoolBoolBool` premise -- which is exactly why the field is stated that
way (the premise occurs negatively, so a non-relativized version would not be monotone). -/
theorem ReflectsNatBitwise.mono (hle : env ≤ env')
    (hc : env'.constants ``Nat.bitwise = env.constants ``Nat.bitwise)
    (H : env.ReflectsNatBitwise) : env'.ReflectsNatBitwise :=
  fun h env₂ hle₂ f g hg a b => H (contains_of_constants_eq hc h) env₂ (hle.trans hle₂) f g hg a b

/-- The names `Environment.checkPrimitiveInductive`, not `checkPrimitiveDef`, is responsible
for.  A `.defnDecl` can never carry one of them, so the corresponding `HasPrimitives` fields
always transfer unchanged. -/
def primInductiveNames : List Name :=
  [``Bool, ``Bool.false, ``Bool.true, ``Nat, ``Nat.zero, ``Nat.succ]

/-- The single `VEnv.HasPrimitives` field that a declaration named `n` is responsible for;
`True` for a name that is not a primitive at all. -/
def PrimField (env : VEnv) (n : Name) : Prop :=
  if n = ``Nat.add then env.ReflectsNatNatNat ``Nat.add Nat.add else
  if n = ``Nat.pred then env.ReflectsNatNat ``Nat.pred Nat.pred else
  if n = ``Nat.sub then env.ReflectsNatNatNat ``Nat.sub Nat.sub else
  if n = ``Nat.mul then env.ReflectsNatNatNat ``Nat.mul Nat.mul else
  if n = ``Nat.pow then env.ReflectsNatNatNat ``Nat.pow Nat.pow else
  if n = ``Nat.gcd then env.ReflectsNatNatNat ``Nat.gcd Nat.gcd else
  if n = ``Nat.mod then env.ReflectsNatNatNat ``Nat.mod Nat.mod else
  if n = ``Nat.div then env.ReflectsNatNatNat ``Nat.div Nat.div else
  if n = ``Nat.beq then env.ReflectsNatNatBool ``Nat.beq Nat.beq else
  if n = ``Nat.ble then env.ReflectsNatNatBool ``Nat.ble Nat.ble else
  if n = ``Nat.bitwise then env.ReflectsNatBitwise else
  if n = ``Nat.land then env.ReflectsNatNatNat ``Nat.land Nat.land else
  if n = ``Nat.lor then env.ReflectsNatNatNat ``Nat.lor Nat.lor else
  if n = ``Nat.xor then env.ReflectsNatNatNat ``Nat.xor Nat.xor else
  if n = ``Nat.shiftLeft then env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft else
  if n = ``Nat.shiftRight then env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight else
  if n = ``Char.ofNat then
    ∀ {ci : VConstant}, env.constants ``Char.ofNat = some ci →
      ci = { uvars := 0, type := .forallE .nat .char }
  else if n = ``String.ofList then
    ∀ {ci : VConstant}, env.constants ``String.ofList = some ci →
      ci = { uvars := 0, type := .forallE .listChar .string } ∧
      env.HasType 0 [] .listCharNil .listChar ∧
      env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)
  else True

@[simp] theorem primField_Nat_add :
    env.PrimField ``Nat.add ↔ env.ReflectsNatNatNat ``Nat.add Nat.add := by simp [PrimField]

@[simp] theorem primField_Nat_pred :
    env.PrimField ``Nat.pred ↔ env.ReflectsNatNat ``Nat.pred Nat.pred := by simp [PrimField]

@[simp] theorem primField_Nat_sub :
    env.PrimField ``Nat.sub ↔ env.ReflectsNatNatNat ``Nat.sub Nat.sub := by simp [PrimField]

@[simp] theorem primField_Nat_mul :
    env.PrimField ``Nat.mul ↔ env.ReflectsNatNatNat ``Nat.mul Nat.mul := by simp [PrimField]

@[simp] theorem primField_Nat_pow :
    env.PrimField ``Nat.pow ↔ env.ReflectsNatNatNat ``Nat.pow Nat.pow := by simp [PrimField]

@[simp] theorem primField_Nat_gcd :
    env.PrimField ``Nat.gcd ↔ env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by simp [PrimField]

@[simp] theorem primField_Nat_mod :
    env.PrimField ``Nat.mod ↔ env.ReflectsNatNatNat ``Nat.mod Nat.mod := by simp [PrimField]

@[simp] theorem primField_Nat_div :
    env.PrimField ``Nat.div ↔ env.ReflectsNatNatNat ``Nat.div Nat.div := by simp [PrimField]

@[simp] theorem primField_Nat_beq :
    env.PrimField ``Nat.beq ↔ env.ReflectsNatNatBool ``Nat.beq Nat.beq := by simp [PrimField]

@[simp] theorem primField_Nat_ble :
    env.PrimField ``Nat.ble ↔ env.ReflectsNatNatBool ``Nat.ble Nat.ble := by simp [PrimField]

@[simp] theorem primField_Nat_bitwise :
    env.PrimField ``Nat.bitwise ↔ env.ReflectsNatBitwise := by simp [PrimField]

@[simp] theorem primField_Nat_land :
    env.PrimField ``Nat.land ↔ env.ReflectsNatNatNat ``Nat.land Nat.land := by simp [PrimField]

@[simp] theorem primField_Nat_lor :
    env.PrimField ``Nat.lor ↔ env.ReflectsNatNatNat ``Nat.lor Nat.lor := by simp [PrimField]

@[simp] theorem primField_Nat_xor :
    env.PrimField ``Nat.xor ↔ env.ReflectsNatNatNat ``Nat.xor Nat.xor := by simp [PrimField]

@[simp] theorem primField_Nat_shiftLeft :
    env.PrimField ``Nat.shiftLeft ↔ env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft := by
  simp [PrimField]

@[simp] theorem primField_Nat_shiftRight :
    env.PrimField ``Nat.shiftRight ↔ env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight := by
  simp [PrimField]

@[simp] theorem primField_Char_ofNat :
    env.PrimField ``Char.ofNat ↔
      ∀ {ci : VConstant}, env.constants ``Char.ofNat = some ci →
        ci = { uvars := 0, type := .forallE .nat .char } := by simp [PrimField]

@[simp] theorem primField_String_ofList :
    env.PrimField ``String.ofList ↔
      ∀ {ci : VConstant}, env.constants ``String.ofList = some ci →
        ci = { uvars := 0, type := .forallE .listChar .string } ∧
        env.HasType 0 [] .listCharNil .listChar ∧
        env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar) := by
  simp [PrimField]

/-- Transfer `HasPrimitives` across an extension whose only new constant is `n`. -/
theorem HasPrimitives.extend {n : Name} (hprim : env.HasPrimitives) (hle : env ≤ env')
    (hagree : ∀ {m}, m ≠ n → env'.constants m = env.constants m)
    (hstruct : n ∉ primInductiveNames) (hnew : env'.PrimField n) : env'.HasPrimitives := by
  simp only [primInductiveNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hstruct
  obtain ⟨hB, hBf, hBt, hN, hNz, hNs⟩ := hstruct
  refine
    { bool := ?_, boolFalse := ?_, boolTrue := ?_, nat := ?_, natZero := ?_, natSucc := ?_
      natAdd := ?_, natPred := ?_, natSub := ?_, natMul := ?_, natPow := ?_, natGcd := ?_
      natMod := ?_, natDiv := ?_, natBEq := ?_, natBLE := ?_, natBitwise := ?_
      natLAnd := ?_, natLOr := ?_, natXor := ?_, natShiftLeft := ?_, natShiftRight := ?_
      charOfNat := ?_, stringOfList := ?_ }
  · exact fun h =>
      have ⟨h1, h2⟩ := hprim.bool (contains_of_constants_eq (hagree (Ne.symm hB)) h)
      ⟨h1.mono hle, h2.mono hle⟩
  · exact fun h => hprim.boolFalse (hagree (Ne.symm hBf) ▸ h)
  · exact fun h => hprim.boolTrue (hagree (Ne.symm hBt) ▸ h)
  · exact fun h =>
      have ⟨h1, h2⟩ := hprim.nat (contains_of_constants_eq (hagree (Ne.symm hN)) h)
      ⟨h1.mono hle, h2.mono hle⟩
  · exact fun h => hprim.natZero (hagree (Ne.symm hNz) ▸ h)
  · exact fun h => hprim.natSucc (hagree (Ne.symm hNs) ▸ h)
  all_goals first
    | (by_cases h : n = ``Nat.add
       · subst h; exact (primField_Nat_add).1 hnew
       · exact hprim.natAdd.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.pred
       · subst h; exact (primField_Nat_pred).1 hnew
       · exact hprim.natPred.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.sub
       · subst h; exact (primField_Nat_sub).1 hnew
       · exact hprim.natSub.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.mul
       · subst h; exact (primField_Nat_mul).1 hnew
       · exact hprim.natMul.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.pow
       · subst h; exact (primField_Nat_pow).1 hnew
       · exact hprim.natPow.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.gcd
       · subst h; exact (primField_Nat_gcd).1 hnew
       · exact hprim.natGcd.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.mod
       · subst h; exact (primField_Nat_mod).1 hnew
       · exact hprim.natMod.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.div
       · subst h; exact (primField_Nat_div).1 hnew
       · exact hprim.natDiv.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.beq
       · subst h; exact (primField_Nat_beq).1 hnew
       · exact hprim.natBEq.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.ble
       · subst h; exact (primField_Nat_ble).1 hnew
       · exact hprim.natBLE.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.bitwise
       · subst h; exact (primField_Nat_bitwise).1 hnew
       · exact hprim.natBitwise.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.land
       · subst h; exact (primField_Nat_land).1 hnew
       · exact hprim.natLAnd.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.lor
       · subst h; exact (primField_Nat_lor).1 hnew
       · exact hprim.natLOr.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.xor
       · subst h; exact (primField_Nat_xor).1 hnew
       · exact hprim.natXor.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.shiftLeft
       · subst h; exact (primField_Nat_shiftLeft).1 hnew
       · exact hprim.natShiftLeft.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Nat.shiftRight
       · subst h; exact (primField_Nat_shiftRight).1 hnew
       · exact hprim.natShiftRight.mono hle (hagree (Ne.symm h)))
    | (by_cases h : n = ``Char.ofNat
       · subst h; exact fun hci => (primField_Char_ofNat).1 hnew hci
       · exact fun hci => hprim.charOfNat (hagree (Ne.symm h) ▸ hci))
    | (by_cases h : n = ``String.ofList
       · subst h; exact fun hci => (primField_String_ofList).1 hnew hci
       · exact fun hci =>
           have ⟨a1, a2, a3⟩ := hprim.stringOfList (hagree (Ne.symm h) ▸ hci)
           ⟨a1, a2.mono hle, a3.mono hle⟩)

/-- The form `PrimitiveResult.preserves` needs: the recognizer's declaration is added as a
constant and then as a defining equation, so the only new constant is `v.name`. -/
theorem HasPrimitives.addDef {v : VDefVal} (hprim : env.HasPrimitives)
    (hadd : env.addConst v.name v.toVConstant = some env')
    (hstruct : v.name ∉ primInductiveNames)
    (hnew : (env'.addDefEq v.toDefEq).PrimField v.name) :
    (env'.addDefEq v.toDefEq).HasPrimitives :=
  hprim.extend ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le)
    (fun hm => constants_addConst_addDefEq hadd hm) hstruct hnew

theorem _root_.Lean4Lean.VLevel.params_zero : VLevel.params 0 = [] := by simp [VLevel.params]

/-- The defining equation the declaration contributes, in the form the reflection lemmas
consume: `.const v.name [] ≡ v.value`.  `VLevel.params 0 = []`, so the level arguments vanish
exactly when the declaration has no level parameters -- which the recognizer checks. -/
theorem const_defeq_value {v : VDefVal} (hv : v.uvars = 0)
    (hty : v.toVConstant.WF env) (hval : env.HasType v.uvars [] v.value v.type)
    (hadd : env.addConst v.name v.toVConstant = some env') :
    (env'.addDefEq v.toDefEq).IsDefEqU 0 [] (.const v.name []) v.value := by
  have hle : env ≤ env'.addDefEq v.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hlhs : (env'.addDefEq v.toDefEq).HasType v.uvars []
      (.const v.name (VLevel.params v.uvars)) v.type :=
    VEnv.HasType.const0 (constants_self_addDefEq hadd) (hty.mono hle)
  have hdf : (v.toDefEq).WF (env'.addDefEq v.toDefEq) := ⟨hlhs, hval.mono hle⟩
  have h := VEnv.IsDefEq.extra0 (df := v.toDefEq) VEnv.addDefEq_self hdf
  rw [show (v.toDefEq).uvars = v.uvars from rfl, hv] at h
  rw [show (v.toDefEq).lhs = .const v.name (VLevel.params v.uvars) from rfl, hv,
    VLevel.params_zero] at h
  exact ⟨_, h⟩

end VEnv

/-! ## The recognizer's own type-checking steps

`Lean4Lean.Environment.checkPrimValue` and `checkIsType` exist so that the recognizer never hands
an unchecked term to `isDefEq`; these are their specifications.  Both *produce* the `TrExprS`
witnesses the rest of the assembly needs, which is the whole point of the change. -/

open Lean hiding Environment Exception
open Kernel TypeChecker

/-- `Verify/Environment/Checker.lean` proves this too, but it imports `Boundaries.lean`, so it
cannot be the source for a lemma `Boundaries.lean` needs. -/
theorem checkNoMVarNoFVar.WF' (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVarNoFVar env name e).WF fun _ => e.FVarsIn fun _ => False := by
  have h1 : (Environment.checkNoMVar env name e).WF fun _ => e.hasMVar = false := by
    intro _ h
    cases hm : e.hasMVar
    · rfl
    · rw [Environment.checkNoMVar, hm] at h; simp at h
  have h2 : (Environment.checkNoFVar env name e).WF fun _ => e.hasFVar = false := by
    intro _ h
    cases hf : e.hasFVar
    · rfl
    · rw [Environment.checkNoFVar, hf] at h; simp at h
  refine h1.bind fun _ hmv => h2.mono fun _ hfv => ?_
  refine fvarsIn_iff.2 ⟨?_, fvarsIn_iff_hasMVar hmv⟩
  intro fv hmem
  rw [fvarsList_eq_nil hfv] at hmem
  simp at hmem

namespace TypeChecker

/-- What `checkPrimValue` establishes: both the declared shape `ty` and the definition's value
have translations, and the value has the type `ty` denotes.  `hfail` is discharged by
`M.WF.throw` at every call site, where `fail` is a `throw`. -/
theorem checkPrimValue.WF {c : VContext} {s : VState} {v : Lean.DefinitionVal} {ty : Expr}
    {fail : ∀ {α}, TypeChecker.M α}
    (hfail : ∀ {α : Type} {s' : VState} {Q : α → VState → Prop}, M.WF c s' fail Q)
    (hty : ty.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkPrimValue v ty fail) fun _ _ =>
      ∃ ty' F, c.TrExprS ty ty' ∧ c.TrExprS v.value F ∧ c.HasType F ty' := by
  unfold Lean4Lean.Environment.checkPrimValue
  refine M.WF.bind getEnv.WF fun _ _ _ h => ?_
  obtain ⟨rfl, rfl⟩ := h
  refine (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)).bind fun _ _ _ hclosed => ?_
  have hclosed' : v.value.FVarsIn (· ∈ c.vlctx.fvars) := hclosed.mono nofun
  refine (checkType.WF hty).bind fun _ _ _ ⟨ty', _, _, hty', _, _⟩ => ?_
  refine (checkType.WF hclosed').bind fun vt _ _ ⟨F, vt', _, hF, hvt, hFty⟩ => ?_
  refine (isDefEq.WF hvt hty').bind fun b _ _ hb => ?_
  split <;> [skip; exact hfail]
  exact .pure ⟨ty', F, hty', hF, hFty.defeqU_r c.Ewf c.Δwf.toCtx (hb (by simpa using ‹_›))⟩

/-- What `checkedIsDefEq` establishes: translations for *both* sides, and -- when it answers
`true` -- that they are definitionally equal.  Handing the caller the witnesses is the point:
the recognizer's right-hand sides mention primitives whose types `VEnv.HasPrimitives` does not
pin down, so a `TrExprS` for them cannot be reconstructed, only read off a successful check. -/
theorem checkedIsDefEq.WF {c : VContext} {s : VState} {a b : Expr}
    (ha : a.FVarsIn (· ∈ c.vlctx.fvars)) (hb : b.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkedIsDefEq a b) fun r _ =>
      ∃ a' b', c.TrExprS a a' ∧ c.TrExprS b b' ∧ (r = true → c.IsDefEqU a' b') := by
  unfold Lean4Lean.Environment.checkedIsDefEq
  refine (checkType.WF ha).bind fun _ _ _ ⟨a', _, _, ha', _, _⟩ => ?_
  refine (checkType.WF hb).bind fun _ _ _ ⟨b', _, _, hb', _, _⟩ => ?_
  exact (isDefEq.WF ha' hb').mono fun _ _ _ h => ⟨a', b', ha', hb', h⟩

/-- What `checkedTypeIs` establishes. -/
theorem checkedTypeIs.WF {c : VContext} {s : VState} {e ty : Expr}
    (he : e.FVarsIn (· ∈ c.vlctx.fvars)) (hty : ty.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkedTypeIs e ty) fun r _ =>
      ∃ e' A' ty', c.TrExprS e e' ∧ c.HasType e' A' ∧ c.TrExprS ty ty' ∧
        (r = true → c.IsDefEqU A' ty') := by
  unfold Lean4Lean.Environment.checkedTypeIs
  refine (checkType.WF he).bind fun _ _ _ ⟨e', A', _, he', hA', hty1⟩ => ?_
  refine (checkType.WF hty).bind fun _ _ _ ⟨ty', _, _, hty', _, _⟩ => ?_
  exact (isDefEq.WF hA' hty').mono fun _ _ _ h => ⟨e', A', ty', he', hty1, hty', h⟩

/-- `checkedIsDefEq` when the caller can build both translations itself. -/
theorem checkedIsDefEq.WF' {c : VContext} {s : VState} {a b : Expr} {a' b' : VExpr}
    (ha : c.TrExprS a a') (hb : c.TrExprS b b') :
    M.WF c s (Lean4Lean.Environment.checkedIsDefEq a b) fun r _ =>
      r = true → c.IsDefEqU a' b' := by
  unfold Lean4Lean.Environment.checkedIsDefEq
  refine (checkType.WF ha.fvarsIn).bind fun _ _ _ _ => ?_
  refine (checkType.WF hb.fvarsIn).bind fun _ _ _ _ => ?_
  exact isDefEq.WF ha hb

/-- `checkedIsDefEq` when the caller can build the right translation but not the left one. -/
theorem checkedIsDefEq.WFl {c : VContext} {s : VState} {a b : Expr} {b' : VExpr}
    (ha : a.FVarsIn (· ∈ c.vlctx.fvars)) (hb : c.TrExprS b b') :
    M.WF c s (Lean4Lean.Environment.checkedIsDefEq a b) fun r _ =>
      ∃ a', c.TrExprS a a' ∧ (r = true → c.IsDefEqU a' b') := by
  unfold Lean4Lean.Environment.checkedIsDefEq
  refine (checkType.WF ha).bind fun _ _ _ ⟨a', _, _, ha', _, _⟩ => ?_
  refine (checkType.WF hb.fvarsIn).bind fun _ _ _ _ => ?_
  exact (isDefEq.WF ha' hb).mono fun _ _ _ h => ⟨a', ha', h⟩

/-- `checkedIsDefEq` when the caller can build the left translation but not the right one -- the
usual case, since the right-hand side of a recognizer equation mentions another primitive whose
type is not pinned by `VEnv.HasPrimitives`. -/
theorem checkedIsDefEq.WFr {c : VContext} {s : VState} {a b : Expr} {a' : VExpr}
    (ha : c.TrExprS a a') (hb : b.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkedIsDefEq a b) fun r _ =>
      ∃ b', c.TrExprS b b' ∧ (r = true → c.IsDefEqU a' b') := by
  unfold Lean4Lean.Environment.checkedIsDefEq
  refine (checkType.WF ha.fvarsIn).bind fun _ _ _ _ => ?_
  refine (checkType.WF hb).bind fun _ _ _ ⟨b', _, _, hb', _, _⟩ => ?_
  exact (isDefEq.WF ha hb').mono fun _ _ _ h => ⟨b', hb', h⟩

/-- What `checkIsType` establishes: `e` has a translation and is a type. -/
theorem checkIsType.WF {c : VContext} {s : VState} {e : Expr}
    (he : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkIsType e) fun _ _ =>
      ∃ e', c.TrExprS e e' ∧ c.IsType e' := by
  unfold Lean4Lean.Environment.checkIsType
  refine (checkType.WF he).bind fun _ _ _ ⟨e', A', _, he', hA', hty⟩ => ?_
  refine (ensureSort.WF hA').mono fun _ _ _ h => ?_
  obtain ⟨⟨_, h1, h2⟩, u, rfl⟩ := h
  let .sort h1 := h1
  exact ⟨e', he', _, hty.defeqU_r c.Ewf c.Δwf.toCtx h2.symm⟩

end TypeChecker

namespace TypeChecker

/-- `RecM.WF.withLocalDecl` at the `M` level, which is where the recognizer's `defeq1`/`defeq2`
comparisons live. -/
protected theorem M.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → M α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (H : ∀ id cwf' s', s ≤ s' → ¬s.ngen.Reserves id →
      M.WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q) :
    M.WF (c.withMLC m) s (withLocalDecl name bi ty f) Q :=
  RecM.WF.withLocalDecl (f := fun e => (f e : RecM α)) hty hty' VState.LE.rfl
    (fun id cwf' s' h1 h2 => M.WF.lift (H id cwf' s' h1 h2)) _
    (Methods.withFuel.WF (n := 0))

end TypeChecker

/-! ## Inverting the recognizer's shape checks

`checkPrimValue` type-checks the shape `ty` as well as the value, so the branch gets a `TrExprS`
for the shape.  Inverting it yields both the shape's translation and the facts about `Nat`
(`TrExprS (.const ``Nat []) .nat`, `IsType .nat`) that the `withLocalDecl`s in `defeq1`/`defeq2`
need -- in particular that `Nat` is declared with no universe parameters, which `env.contains`
alone does not give. -/

namespace TypeChecker

variable {c : VContext}

theorem trExprS_const_nil_inv {Δ : VLCtx} {n : Name} {e' : VExpr}
    (h : TrExprS c.venv c.lparams Δ (.const n []) e') : e' = .const n [] := by
  let .const _ h2 _ := h
  simp at h2; subst h2; rfl

theorem trExprS_arrow_inv {Δ : VLCtx} {nm : Name} {A B : Expr} {bi} {e' : VExpr}
    (h : TrExprS c.venv c.lparams Δ (.forallE nm A B bi) e') :
    ∃ A' B', e' = .forallE A' B' ∧
      TrExprS c.venv c.lparams Δ A A' ∧ c.venv.IsType c.lparams.length Δ.toCtx A' ∧
      TrExprS c.venv c.lparams ((none, .vlam A') :: Δ) B B' :=
  let .forallE h1 _ h3 h4 := h; ⟨_, _, rfl, h3, h1, h4⟩

/-- The `Nat` facts a branch needs, read off a successful check of a shape whose domain is
`Nat`. -/
structure NatFacts (c : VContext) : Prop where
  tr : c.TrExprS (.const ``Nat []) .nat
  isType : c.IsType .nat

theorem NatFacts.of_arrow {nm B bi e'}
    (h : c.TrExprS (.forallE nm (.const ``Nat []) B bi) e') : NatFacts c := by
  have ⟨_, _, _, h1, h2, _⟩ := trExprS_arrow_inv h
  cases trExprS_const_nil_inv h1
  exact ⟨h1, h2⟩

/-- `Nat → Nat`. -/
theorem trExprS_natArrow1_inv {nm bi e'}
    (h : c.TrExprS (.forallE nm (.const ``Nat []) (.const ``Nat []) bi) e') :
    e' = .forallE .nat .nat := by
  obtain ⟨_, _, rfl, h1, _, h3⟩ := trExprS_arrow_inv h
  cases trExprS_const_nil_inv h1; cases trExprS_const_nil_inv h3; rfl

/-- `Nat → Nat → Nat`. -/
theorem trExprS_natArrow2_inv {nm₁ nm₂ bi₁ bi₂ e'}
    (h : c.TrExprS (.forallE nm₁ (.const ``Nat [])
      (.forallE nm₂ (.const ``Nat []) (.const ``Nat []) bi₂) bi₁) e') :
    e' = .forallE .nat (.forallE .nat .nat) := by
  obtain ⟨_, _, rfl, h1, _, h3⟩ := trExprS_arrow_inv h
  cases trExprS_const_nil_inv h1
  obtain ⟨_, _, rfl, h4, _, h5⟩ := trExprS_arrow_inv h3
  cases trExprS_const_nil_inv h4; cases trExprS_const_nil_inv h5; rfl

/-- `Nat → Nat → Bool`. -/
theorem trExprS_natArrowBool_inv {nm₁ nm₂ bi₁ bi₂ e'}
    (h : c.TrExprS (.forallE nm₁ (.const ``Nat [])
      (.forallE nm₂ (.const ``Nat []) (.const ``Bool []) bi₂) bi₁) e') :
    e' = .forallE .nat (.forallE .nat .bool) := by
  obtain ⟨_, _, rfl, h1, _, h3⟩ := trExprS_arrow_inv h
  cases trExprS_const_nil_inv h1
  obtain ⟨_, _, rfl, h4, _, h5⟩ := trExprS_arrow_inv h3
  cases trExprS_const_nil_inv h4; cases trExprS_const_nil_inv h5; rfl

end TypeChecker

/-! ## Building the terms the recognizer compares -/

namespace TypeChecker

variable {c : VContext}

/-- The variable a `withLocalDecl` has just bound. -/
theorem trExprS_lastFVar {m : MLCtx} {id name ty ty' bi}
    [cwf : c.MLCWF (.vlam id name ty ty' bi m)] :
    (c.withMLC (.vlam id name ty ty' bi m)).TrExprS (.fvar id) (.bvar 0) := by
  refine .fvar (A := ty'.lift) ?_
  simp [VContext.withMLC, VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]

theorem hasType_lastFVar {m : MLCtx} {id name ty ty' bi}
    [cwf : c.MLCWF (.vlam id name ty ty' bi m)] :
    (c.withMLC (.vlam id name ty ty' bi m)).HasType (.bvar 0) ty'.lift := .bvar .zero

/-- A value known to have type `Nat → A`, applied to one `Nat`. -/
theorem trExprS_app1 {F a' A : VExpr} {value a : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE .nat A))
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat) :
    c.TrExprS (mkApp value a) (.app F a') ∧ c.HasType (.app F a') (A.inst a') :=
  ⟨.app hFty haty hF ha, hFty.app haty⟩

/-- A value known to have type `Nat → Nat`, applied to one `Nat`. -/
theorem trExprS_app1_nat {F a' : VExpr} {value a : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE .nat .nat))
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat) :
    c.TrExprS (mkApp value a) (.app F a') ∧ c.HasType (.app F a') .nat := by
  refine ⟨.app hFty haty hF ha, ?_⟩
  have := hFty.app haty; rwa [VExpr.inst_nat] at this

/-- A value known to have type `Nat → Nat → A`, applied to two `Nat`s. -/
theorem trExprS_app2 {F a' b' A : VExpr} {value a b : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE .nat (.forallE .nat A)))
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat)
    (hb : c.TrExprS b b') (hbty : c.HasType b' .nat) :
    c.TrExprS (mkApp2 value a b) (.app (.app F a') b') := by
  have h1 : c.HasType (.app F a') (.forallE .nat (A.inst a' 1)) := by
    have := hFty.app haty; rwa [VExpr.inst, VExpr.inst_nat] at this
  exact .app h1 hbty (.app hFty haty hF ha) hb

/-- The specialisation the `Nat` branches use: the shape is `Nat → Nat → Nat`, so the
application's type is again `Nat`. -/
theorem trExprS_app2_nat {F a' b' : VExpr} {value a b : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE .nat (.forallE .nat .nat)))
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat)
    (hb : c.TrExprS b b') (hbty : c.HasType b' .nat) :
    c.TrExprS (mkApp2 value a b) (.app (.app F a') b') ∧
    c.HasType (.app (.app F a') b') .nat := by
  refine ⟨trExprS_app2 hF hFty ha haty hb hbty, ?_⟩
  have h1 : c.HasType (.app F a') (.forallE .nat .nat) := by
    have := hFty.app haty; rwa [VExpr.inst, VExpr.inst_nat, VExpr.inst_nat] at this
  have := h1.app hbty; rwa [VExpr.inst_nat] at this

theorem trExprS_app2_bool {F a' b' : VExpr} {value a b : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE .nat (.forallE .nat .bool)))
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat)
    (hb : c.TrExprS b b') (hbty : c.HasType b' .nat) :
    c.TrExprS (mkApp2 value a b) (.app (.app F a') b') := trExprS_app2 hF hFty ha haty hb hbty

/-! Reading a recognizer right-hand side back.

The right-hand sides mention primitives whose types `VEnv.HasPrimitives` does not pin, so their
translations cannot be built; `checkedIsDefEq` hands one back instead, and these lemmas rewrite
it into the shape the reflection lemmas expect.  All the typing they need comes out of the
`TrExprS.app` nodes themselves. -/

theorem rhs_const_app {n : Name} {X : Expr} {rhs' Xi : VExpr}
    (hrhs : c.TrExprS (mkApp (.const n []) X) rhs') (hXi : c.TrExprS X Xi) :
    c.IsDefEqU rhs' (.app (.const n []) Xi) := by
  let .app h1 h2 h3 h4 := hrhs
  cases trExprS_const_nil_inv h3
  exact ⟨_, .appDF h1 ((h4.uniq c.Ewf (.refl c.Ewf c.Δwf) hXi).of_l c.Ewf c.Δwf.toCtx h2)⟩

theorem rhs_const_app2 {n : Name} {X Y : Expr} {rhs' Xi Yi : VExpr}
    (hrhs : c.TrExprS (mkApp2 (.const n []) X Y) rhs')
    (hXi : c.TrExprS X Xi) (hYi : c.TrExprS Y Yi) :
    c.IsDefEqU rhs' (.app (.app (.const n []) Xi) Yi) := by
  let .app h1 h2 h3 h4 := hrhs
  let .app g1 g2 g3 g4 := h3
  cases trExprS_const_nil_inv g3
  have hf : c.IsDefEqU (.app _ _) (.app (.const n []) Xi) :=
    ⟨_, .appDF g1 ((g4.uniq c.Ewf (.refl c.Ewf c.Δwf) hXi).of_l c.Ewf c.Δwf.toCtx g2)⟩
  exact ⟨_, .appDF (hf.of_l c.Ewf c.Δwf.toCtx h1)
    ((h4.uniq c.Ewf (.refl c.Ewf c.Δwf) hYi).of_l c.Ewf c.Δwf.toCtx h2)⟩

/-- The `Nat.shiftLeft` shape: the head is the definition's own value (so its translation *is*
known), but the first argument is an application of another primitive, handled by `hA`. -/
theorem rhs_val_app2 {value A B : Expr} {rhs' F Ai Bi : VExpr}
    (hrhs : c.TrExprS (mkApp2 value A B) rhs') (hF : c.TrExprS value F)
    (hA : ∀ X, c.TrExprS A X → c.IsDefEqU X Ai) (hBi : c.TrExprS B Bi) :
    c.IsDefEqU rhs' (.app (.app F Ai) Bi) := by
  let .app h1 h2 h3 h4 := hrhs
  let .app g1 g2 g3 g4 := h3
  have hFF := (g3.uniq c.Ewf (.refl c.Ewf c.Δwf) hF).of_l c.Ewf c.Δwf.toCtx g1
  have hf : c.IsDefEqU (.app _ _) (.app F Ai) :=
    ⟨_, .appDF hFF ((hA _ g4).of_l c.Ewf c.Δwf.toCtx g2)⟩
  exact ⟨_, .appDF (hf.of_l c.Ewf c.Δwf.toCtx h1)
    ((h4.uniq c.Ewf (.refl c.Ewf c.Δwf) hBi).of_l c.Ewf c.Δwf.toCtx h2)⟩

/-- The most general form: a two-argument application all three of whose parts are only known up
to `IsDefEqU`.  This is what the `Nat.land`/`Nat.lor`/`Nat.xor` branches need, since the boolean
combinator they destructure out of the value has no type the recognizer knows. -/
theorem app2_uniq {u X Y : Expr} {lhs' Ui Xi Yi : VExpr}
    (hlhs : c.TrExprS (mkApp2 u X Y) lhs') (hUi : c.TrExprS u Ui)
    (hX : ∀ Z, c.TrExprS X Z → c.IsDefEqU Z Xi) (hY : ∀ Z, c.TrExprS Y Z → c.IsDefEqU Z Yi) :
    c.IsDefEqU lhs' (.app (.app Ui Xi) Yi) := by
  let .app h1 h2 h3 h4 := hlhs
  let .app g1 g2 g3 g4 := h3
  have hUU := (g3.uniq c.Ewf (.refl c.Ewf c.Δwf) hUi).of_l c.Ewf c.Δwf.toCtx g1
  have hf : c.IsDefEqU (.app _ _) (.app Ui Xi) :=
    ⟨_, .appDF hUU ((hX _ g4).of_l c.Ewf c.Δwf.toCtx g2)⟩
  exact ⟨_, .appDF (hf.of_l c.Ewf c.Δwf.toCtx h1) ((hY _ h4).of_l c.Ewf c.Δwf.toCtx h2)⟩

theorem trExprS_bitwiseApp_inv {andE : Expr} {F : VExpr}
    (hF : c.TrExprS (mkApp (.const ``Nat.bitwise []) andE) F) :
    ∃ G, F = .app (.const ``Nat.bitwise []) G ∧ c.TrExprS andE G := by
  let .app _ _ h3 h4 := hF
  cases trExprS_const_nil_inv h3
  exact ⟨_, rfl, h4⟩

/-- `Nat.succ` applied to a `Nat`. -/
theorem trExprS_succ {a' : VExpr} {a : Expr}
    (ha : c.TrExprS a a') (haty : c.HasType a' .nat)
    (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat) :
    c.TrExprS (mkApp (.const ``Nat.succ []) a) (.app .natSucc a') ∧
    c.HasType (.app .natSucc a') .nat := by
  have ⟨h1, h2⟩ := TrExprS.natSucc (Us := c.lparams) (Δ := c.vlctx) hprim hnat
  refine ⟨.app h2 haty h1 ha, ?_⟩
  have := h2.app haty; rwa [VExpr.inst_nat] at this

end TypeChecker

/-! ## Moving closed facts under a `withLocalDecl` binder

The recognizer's equations mention the definition's value, which is closed, so weakening it into
the extended context is the identity on the abstract side. -/

namespace TypeChecker

variable {c : VContext}

theorem TrExprS.weakLam {m : MLCtx} (mwf : c.MLCWF m) {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi m)) {e : Expr} {e' : VExpr}
    (h : (c.withMLC m (wf := mwf)).TrExprS e e') (hc : e'.ClosedN 0) :
    (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf)).TrExprS e e' := by
  have := h.weakFV c.Ewf
    (Δ' := (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf)).vlctx)
    (.skip_fvar _ _ .refl) cwf.1.tr.wf
  rwa [hc.liftN_eq (Nat.zero_le _)] at this

theorem HasType.weakLam {m : MLCtx} (mwf : c.MLCWF m) {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi m)) {e' A' : VExpr}
    (h : (c.withMLC m (wf := mwf)).HasType e' A') (hc : e'.ClosedN 0) (hA : A'.ClosedN 0) :
    (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf)).HasType e' A' := by
  have := h.weakN c.Ewf.ordered (n := 1) (k := 0)
    (Γ' := ty' :: (c.withMLC m (wf := mwf)).vlctx.toCtx) .one
  rwa [hc.liftN_eq (Nat.zero_le _), hA.liftN_eq (Nat.zero_le _)] at this

/-- `c.mlctx = .nil`, so the base context is empty and everything in it is closed. -/
theorem closedN_of_nil {e' A' : VExpr} (hnil : c.vlctx = [])
    (h : c.HasType e' A') : e'.ClosedN 0 ∧ A'.ClosedN 0 := by
  have := h.closedN' c.Ewf.ordered.closed (Γ := c.vlctx.toCtx) (by rw [hnil]; trivial)
  rw [hnil] at this
  exact ⟨this.1, this.2.2⟩

end TypeChecker

namespace TypeChecker

variable {c : VContext}

/-- `M.WF.withLocalDecl` with the ambient context in the form the recognizer's branches meet it
(`c`, rather than `c.withMLC c.mlctx`). -/
protected theorem M.WF.withLocalDecl0 {s : VState} {f : Expr → M α} {Q name ty ty' bi}
    (hty : c.TrExprS ty ty') (hty' : c.IsType ty')
    (H : ∀ id (cwf' : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) s', s ≤ s' →
      ¬s.ngen.Reserves id →
      M.WF (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf')) s' (f (.fvar id)) Q) :
    M.WF c s (withLocalDecl name bi ty f) Q := by
  have h := M.WF.withLocalDecl (c := c) (m := c.mlctx) (cwf := inferInstance)
    (ty' := ty') (bi := bi) (name := name) (f := f)
    (by rwa [VContext.withMLC_self]) (by rwa [VContext.withMLC_self]) H
  rwa [VContext.withMLC_self] at h

/-- What `Environment.withCheckedLocalDecl` establishes, and the form the four fuel /
well-founded branches need it in.

`M.WF.withLocalDecl0` demands a `TrExprS` and an `IsType` for the binder's domain, and the
domains those branches introduce (`1 ≤ y`, `Nat.succ x ≤ Nat.succ fuel`, `r.type p Bool.true`,
the type recovered from a `whnf`) are built out of constants that `VEnv.HasPrimitives` only
requires to be *present*, so neither fact can be reconstructed -- it can only be read off a
successful check.  `withCheckedLocalDecl` performs that check, and this lemma hands the
continuation the two witnesses along with the free variable.

Note the `FVarsIn` side condition is on `ty` only: the continuation is entered in the extended
context, where the new variable is available. -/
protected theorem M.WF.withCheckedLocalDecl {s : VState} {f : Expr → M α} {Q : α → VState → Prop}
    {name ty bi} (hty : ty.FVarsIn (· ∈ c.vlctx.fvars))
    (H : ∀ ty' id (cwf' : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) s', s ≤ s' →
      c.TrExprS ty ty' → c.IsType ty' →
      M.WF (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf')) s' (f (.fvar id)) Q) :
    M.WF c s (Lean4Lean.Environment.withCheckedLocalDecl name bi ty f) Q := by
  unfold Lean4Lean.Environment.withCheckedLocalDecl
  refine (checkIsType.WF hty).bind fun _ s₁ hs₁ h => ?_
  obtain ⟨ty', hty', histy⟩ := h
  exact M.WF.withLocalDecl0 hty' histy fun id cwf' s' hle _ =>
    H ty' id cwf' s' (hs₁.trans hle) hty' histy

theorem TrExprS.weakLam0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) {e : Expr} {e' : VExpr}
    (h : c.TrExprS e e') (hc : e'.ClosedN 0) :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).TrExprS e e' :=
  TrExprS.weakLam inferInstance cwf (by rwa [VContext.withMLC_self]) hc

theorem HasType.weakLam0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) {e' A' : VExpr}
    (h : c.HasType e' A') (hc : e'.ClosedN 0) (hA : A'.ClosedN 0) :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).HasType e' A' :=
  HasType.weakLam inferInstance cwf (by rwa [VContext.withMLC_self]) hc hA

/-- Weakening under a binder without a closedness assumption: the abstract term is lifted.  This
is what carries the *outer* bound variable of `defeq2` into the inner context. -/
theorem TrExprS.weakLift0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) {e : Expr} {e' : VExpr}
    (h : c.TrExprS e e') :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).TrExprS e e'.lift := by
  have h' : (c.withMLC c.mlctx).TrExprS e e' := by rwa [VContext.withMLC_self]
  have := h'.weakFV c.Ewf
    (Δ' := (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).vlctx)
    (.skip_fvar _ _ .refl) cwf.1.tr.wf
  rw [VExpr.lift]
  exact this

theorem NatFacts.contains (h : NatFacts c) : c.venv.contains ``Nat :=
  let .const h1 _ _ := h.tr; ⟨_, h1⟩

theorem NatFacts.weakLam0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) (h : NatFacts c) :
    NatFacts (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)) :=
  ⟨TrExprS.weakLam0 cwf h.tr trivial,
   let ⟨_, hu⟩ := h.isType; ⟨_, HasType.weakLam0 cwf hu trivial trivial⟩⟩

theorem trExprS_lastFVar0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).TrExprS (.fvar id) (.bvar 0) :=
  trExprS_lastFVar

theorem hasType_lastFVar0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) (hc : ty'.ClosedN 0) :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).HasType (.bvar 0) ty' := by
  have := hasType_lastFVar (c := c) (m := c.mlctx) (cwf := cwf) (id := id) (name := name)
    (ty := ty) (ty' := ty') (bi := bi)
  rwa [VExpr.lift, hc.liftN_eq (Nat.zero_le _)] at this

end TypeChecker

/-! ## The `PrimitiveResult.preserves` obligation

One lemma serves every branch: it does all the environment plumbing (uniqueness of the value's
translation, well-formedness of the extended environment, the defining equation the declaration
contributes) and leaves the branch with a single obligation, `VEnv.PrimField`, stated in the
extended environment. -/

theorem preserves_glue {checked : VEnv} {value : Expr} {F : VExpr} {nm : Name}
    {vv : Lean.DefinitionVal}
    (hname : vv.name = nm) (hlp : vv.levelParams = []) (hvalue : vv.value = value)
    (hn : nm ∉ VEnv.primInductiveNames)
    (hFtr : TrExprS checked [] [] value F)
    (hrefl : ∀ (venv env₂ : VEnv), checked ≤ venv → venv ≤ env₂ → env₂.WF →
      venv.HasPrimitives → env₂.IsDefEqU 0 [] (.const nm []) F → env₂.PrimField nm)
    {sf : DefinitionSafety} {venv env' : VEnv} {ci' : VDefVal}
    (hle : checked ≤ venv) (hwf : venv.WF) (hprim : venv.HasPrimitives)
    (htr : TrDefVal sf venv (.defnInfo vv) ci') (hci : ci'.WF venv)
    (hadd : venv.addConst vv.name ci'.toVConstant = some env') :
    (env'.addDefEq ci'.toDefEq).HasPrimitives := by
  obtain ⟨⟨⟨-, huv, -⟩, hnm⟩, hval⟩ := htr
  have huv0 : ci'.uvars = 0 := by
    have : vv.levelParams.length = ci'.uvars := huv
    rw [hlp] at this; exact this.symm
  simp [ConstantInfo.value!, ConstantInfo.value?, hvalue] at hval
  have hnm2 : ci'.name = nm := hnm.symm.trans hname
  rw [hname, ← hnm2] at hadd
  have hcty : ci'.toVConstant.WF venv := hci.isType hwf.ordered trivial
  have hle₂ : venv ≤ env'.addDefEq ci'.toDefEq :=
    (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have henv₂ : (env'.addDefEq ci'.toDefEq).WF :=
    let ⟨_, hds⟩ := hwf; ⟨_, .decl (.def hci hadd) hds⟩
  have hdef := VEnv.const_defeq_value huv0 hcty hci hadd
  have huniq : venv.IsDefEqU 0 [] F ci'.value :=
    TrExprS.uniq hwf (Us := []) (Δ₁ := []) (Δ₂ := []) (.refl hwf trivial) (hFtr.mono hle)
      (hlp ▸ hval)
  have hdefF : (env'.addDefEq ci'.toDefEq).IsDefEqU 0 [] (.const nm []) F := by
    rw [← hnm2]
    exact VEnv.IsDefEqU.trans henv₂ trivial hdef (huniq.mono hle₂).symm
  refine hprim.addDef hadd (by rw [hnm2]; exact hn) ?_
  rw [hnm2]
  exact hrefl venv _ hle hle₂ henv₂ hprim hdefF

/-- The shape a binary-`Nat` branch's `hrefl` obligation takes: the branch supplies the closed
reflection, this supplies the numeral typing and the transport to the constant. -/
theorem reflectsNNN_of_open {venv env₂ : VEnv} {F : VExpr} {nm : Name} {g : Nat → Nat → Nat}
    (hle₂ : venv ≤ env₂) (henv₂ : env₂.WF) (hprim : venv.HasPrimitives)
    (hnat : venv.contains ``Nat)
    (hdefF : env₂.IsDefEqU 0 [] (.const nm []) F)
    (hFty : env₂.HasType 0 [] F (.forallE .nat (.forallE .nat .nat)))
    (H : env₂.NatLits →
      ∀ a b, env₂.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (g a b))) :
    env₂.ReflectsNatNatNat nm g :=
  let hlit := (hprim.natLits hnat).mono hle₂
  VEnv.ReflectsNatNatNat.of_defeq henv₂ hlit hFty hdefF (H hlit)

theorem reflectsNNB_of_open {venv env₂ : VEnv} {F : VExpr} {nm : Name} {g : Nat → Nat → Bool}
    (hle₂ : venv ≤ env₂) (henv₂ : env₂.WF) (hprim : venv.HasPrimitives)
    (hnat : venv.contains ``Nat)
    (hdefF : env₂.IsDefEqU 0 [] (.const nm []) F)
    (hFty : env₂.HasType 0 [] F (.forallE .nat (.forallE .nat .bool)))
    (H : env₂.NatLits →
      ∀ a b, env₂.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.boolLit (g a b))) :
    env₂.ReflectsNatNatBool nm g :=
  let hlit := (hprim.natLits hnat).mono hle₂
  VEnv.ReflectsNatNatBool.of_defeq henv₂ hlit hFty hdefF (H hlit)

theorem reflectsNN_of_open {venv env₂ : VEnv} {F : VExpr} {nm : Name} {g : Nat → Nat}
    (hle₂ : venv ≤ env₂) (henv₂ : env₂.WF) (hprim : venv.HasPrimitives)
    (hnat : venv.contains ``Nat)
    (hdefF : env₂.IsDefEqU 0 [] (.const nm []) F)
    (hFty : env₂.HasType 0 [] F (.forallE .nat .nat))
    (H : env₂.NatLits → ∀ a, env₂.IsDefEqU 0 [] (.app F (.natLit a)) (.natLit (g a))) :
    env₂.ReflectsNatNat nm g :=
  let hlit := (hprim.natLits hnat).mono hle₂
  VEnv.ReflectsNatNat.of_defeq henv₂ hlit hFty hdefF (H hlit)

namespace TypeChecker

variable {c : VContext}

theorem HasType.weakLift0 {id name ty ty' bi}
    (cwf : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) {e' A' : VExpr}
    (h : c.HasType e' A') :
    (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf)).HasType e'.lift A'.lift := by
  have h' : (c.withMLC c.mlctx).HasType e' A' := by rwa [VContext.withMLC_self]
  exact h'.weakN c.Ewf.ordered (n := 1) (k := 0)
    (Γ' := ty' :: (c.withMLC c.mlctx).vlctx.toCtx) .one

/-- The *outer* variable of `defeq2`, seen from inside the inner binder. -/
theorem hasType_fvar1 {idy namey tyy tyy' biy}
    (cwfy : c.MLCWF (.vlam idy namey tyy tyy' biy c.mlctx))
    {idx namex tyx tyx' bix}
    (cwfx : (c.withMLC (.vlam idy namey tyy tyy' biy c.mlctx) (wf := cwfy)).MLCWF
      (.vlam idx namex tyx tyx' bix
        (c.withMLC (.vlam idy namey tyy tyy' biy c.mlctx) (wf := cwfy)).mlctx))
    (hc : tyy'.ClosedN 0) :
    ((c.withMLC (.vlam idy namey tyy tyy' biy c.mlctx) (wf := cwfy)).withMLC
      (.vlam idx namex tyx tyx' bix _) (wf := cwfx)).HasType (.bvar 1) tyy' := by
  have := HasType.weakLift0 cwfx (hasType_lastFVar0 cwfy hc)
  rw [VExpr.lift, VExpr.lift, hc.liftN_eq (Nat.zero_le _)] at this
  exact this


end TypeChecker

namespace TypeChecker

variable {c : VContext}

theorem primitives_contains_iff {a : Name} :
    Environment.primitives.contains a ↔ a ∈ ([``Bool, ``Bool.false, ``Bool.true,
      ``Nat, ``Nat.zero, ``Nat.succ, ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
      ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble, ``Nat.bitwise, ``Nat.land,
      ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList,
      ``Char.ofNat] : List Name) := by
  simp [Environment.primitives, NameSet.contains, NameSet.ofList]

theorem primitives_Nat : Environment.primitives.contains ``Nat = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_Bool : Environment.primitives.contains ``Bool = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_natPred : Environment.primitives.contains ``Nat.pred = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_natAdd : Environment.primitives.contains ``Nat.add = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_natMul : Environment.primitives.contains ``Nat.mul = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_natDiv : Environment.primitives.contains ``Nat.div = true := by
  simpa using primitives_contains_iff.2 (by simp)
theorem primitives_natBitwise : Environment.primitives.contains ``Nat.bitwise = true := by
  simpa using primitives_contains_iff.2 (by simp)

/-- Uniqueness of translations in a `VContext`, with the context's own well-formedness. -/
theorem trExprS_uniq {e : Expr} {e₁ e₂ : VExpr}
    (h1 : c.TrExprS e e₁) (h2 : c.TrExprS e e₂) : c.IsDefEqU e₁ e₂ :=
  h1.uniq c.Ewf (.refl c.Ewf c.Δwf) h2

/-- Transitivity of `IsDefEqU` in a `VContext`, with the context's own well-formedness. -/
theorem VContext.trans {a b d : VExpr} (h1 : c.IsDefEqU a b) (h2 : c.IsDefEqU b d) :
    c.IsDefEqU a d := VEnv.IsDefEqU.trans c.Ewf c.Δwf.toCtx h1 h2

/-- An already-declared primitive constant has an abstract counterpart, and by
`VEnvs.WF.safePrimitives` it has no level parameters -- which is what `TrExprS.const` needs and
what `env.contains` alone does not give. -/
theorem VContext.primConst (hsf : c.safety = .safe) {n : Name}
    (h : c.env.contains n = true) (hp : Environment.primitives.contains n) :
    ∃ ci', c.venv.constants n = some ci' ∧ ci'.uvars = 0 := by
  have hwf := c.trenv.map_wf
  have hfind : ∃ ci, c.env.find? n = some ci := by
    rw [Kernel.Environment.find?, hwf.find?'_eq_find?]
    have hc : c.env.constants.contains n = true := h
    rw [hwf.find?_isSome] at hc
    exact Option.isSome_iff_exists.1 hc
  obtain ⟨ci, hci⟩ := hfind
  obtain ⟨hs, hlp⟩ := c.safePrimitives hci hp
  obtain ⟨ci', h1, h2⟩ := c.trenv.find? hci (by rw [hsf, hs]; exact DefinitionSafety.le_rfl)
  exact ⟨ci', h1, by rw [← h2.2.1, hlp]; rfl⟩

theorem trExprS_primConst (hsf : c.safety = .safe) {n : Name}
    (h : c.env.contains n = true) (hp : Environment.primitives.contains n) :
    c.TrExprS (.const n []) (.const n []) := by
  obtain ⟨ci, h1, h2⟩ := VContext.primConst hsf h hp
  exact .const h1 (by simp) (by simp [h2])

/-- `Bool` translated, and a type: the `Nat.land`/`lor`/`xor` branches bind a `Bool`-typed
variable. -/
theorem trExprS_bool (hsf : c.safety = .safe) (h : c.env.contains ``Bool = true) :
    c.TrExprS (.const ``Bool []) .bool := trExprS_primConst hsf h primitives_Bool

theorem isType_bool (hprim : c.venv.HasPrimitives) (hb : c.venv.contains ``Bool)
    (hlp : c.lparams = []) : c.IsType .bool := by
  obtain ⟨⟨ci, h⟩, -⟩ := hprim.bool hb
  cases hprim.boolFalse h
  obtain ⟨u, hu⟩ := c.Ewf.ordered.constWF h
  exact ⟨u, by rw [hlp]; exact hu.weak0 c.Ewf.ordered⟩

theorem contains_primConst (hsf : c.safety = .safe) {n : Name}
    (h : c.env.contains n = true) (hp : Environment.primitives.contains n) :
    c.venv.contains n :=
  let ⟨_, h1, _⟩ := VContext.primConst hsf h hp; ⟨_, h1⟩

/-- The typing needed to *apply* an already-declared primitive, recovered from its reflection
fact: `HasPrimitives` pins the primitive's behaviour but not its type, and the reflection fact
witnesses that the application at a numeral is well-typed, which is enough. -/
theorem prim_domain_nat {env : VEnv} (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {u : VExpr} {n : Nat} {w : VExpr}
    (hu : env.IsDefEqU 0 [] (.app u (.natLit n)) w) :
    ∃ A B, env.HasType 0 [] u (.forallE A B) ∧ ∃ lv, env.IsDefEq 0 [] A .nat (.sort lv) := by
  obtain ⟨T, hu'⟩ := hu
  obtain ⟨A, B, h1, h2⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial
    ⟨_, hu'.hasType.1⟩
  exact ⟨A, B, h1, h2.uniq henv trivial (hprim.natLit_hasType hnat n)⟩

end TypeChecker

/-- `PrimitiveResult.preserves` for the two branches that pin a *type* rather than a reflection
(`Char.ofNat`, `String.ofList`); they never look at the definition's value. -/
theorem preserves_glue_const {checked : VEnv} {nm : Name} {vv : Lean.DefinitionVal}
    (hname : vv.name = nm) (hlp : vv.levelParams = []) (hn : nm ∉ VEnv.primInductiveNames)
    (hfield : ∀ (venv : VEnv) (ci' : VDefVal), checked ≤ venv → venv.HasPrimitives →
      TrExprS venv [] [] vv.type ci'.type → ci'.uvars = 0 →
      ∀ env₂ : VEnv, venv ≤ env₂ → env₂.constants nm = some ci'.toVConstant →
        env₂.PrimField nm)
    {sf : DefinitionSafety} {venv env' : VEnv} {ci' : VDefVal}
    (hle : checked ≤ venv) (hwf : venv.WF) (hprim : venv.HasPrimitives)
    (htr : TrDefVal sf venv (.defnInfo vv) ci') (hci : ci'.WF venv)
    (hadd : venv.addConst vv.name ci'.toVConstant = some env') :
    (env'.addDefEq ci'.toDefEq).HasPrimitives := by
  obtain ⟨⟨⟨-, huv, htype⟩, hnm⟩, -⟩ := htr
  have huv0 : ci'.uvars = 0 := by
    have : vv.levelParams.length = ci'.uvars := huv
    rw [hlp] at this; exact this.symm
  have hnm2 : ci'.name = nm := hnm.symm.trans hname
  rw [hname, ← hnm2] at hadd
  refine hprim.addDef hadd (by rw [hnm2]; exact hn) ?_
  rw [hnm2]
  refine hfield venv ci' hle hprim (hlp ▸ htype) huv0 _
    ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le) ?_
  rw [← hnm2]; exact VEnv.constants_self_addDefEq hadd

namespace TypeChecker

variable {c : VContext}

end TypeChecker

/-! Raw (context-free) versions of the inversions, for the branches whose obligation is about
the declared type and is discharged inside `PrimitiveResult.preserves`, where no `VContext` is
in scope. -/

theorem trExprS_const_nil_inv' {env : VEnv} {Us Δ} {n : Name} {e' : VExpr}
    (h : TrExprS env Us Δ (.const n []) e') : e' = .const n [] := by
  let .const _ h2 _ := h
  simp at h2; subst h2; rfl

theorem trExprS_arrow_inv' {env : VEnv} {Us Δ} {nm : Name} {A B : Expr} {bi} {e' : VExpr}
    (h : TrExprS env Us Δ (.forallE nm A B bi) e') :
    ∃ A' B', e' = .forallE A' B' ∧ TrExprS env Us Δ A A' ∧
      TrExprS env Us ((none, .vlam A') :: Δ) B B' :=
  let .forallE _ _ h3 h4 := h; ⟨_, _, rfl, h3, h4⟩

/-- `Nat → Char`, the type `Char.ofNat` is pinned to. -/
theorem trExprS_natChar_inv' {env : VEnv} {Us Δ} {nm bi e'}
    (h : TrExprS env Us Δ (.forallE nm (.const ``Nat []) (.const ``Char []) bi) e') :
    e' = .forallE .nat .char := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1; cases trExprS_const_nil_inv' h3; rfl

theorem trExprS_const_zero_inv' {env : VEnv} {Us Δ} {n : Name} {e' : VExpr}
    (h : TrExprS env Us Δ (.const n [.zero]) e') : e' = .const n [.zero] := by
  let .const _ h2 _ := h
  simp [VLevel.ofLevel] at h2
  rw [← h2]

/-- `List Char`, and `List Char → String`, the type `String.ofList` is pinned to. -/
theorem trExprS_constAppChar_inv' {env : VEnv} {Us Δ} {n : Name} {e'}
    (h : TrExprS env Us Δ (.app (.const n [.zero]) (.const ``Char [])) e') :
    e' = .app (.const n [.zero]) .char := by
  let .app _ _ g3 g4 := h
  cases trExprS_const_nil_inv' g4
  cases trExprS_const_zero_inv' g3
  rfl

theorem trExprS_listChar_inv' {env : VEnv} {Us Δ} {e'}
    (h : TrExprS env Us Δ (.app (.const ``List [.zero]) (.const ``Char [])) e') :
    e' = .listChar := trExprS_constAppChar_inv' h

/-- `Char → List Char → List Char`, the type of `List.cons` at `Char`. -/
theorem trExprS_consType_inv' {env : VEnv} {Us Δ} {n₁ n₂ bi₁ bi₂ e'}
    (h : TrExprS env Us Δ (.forallE n₁ (.const ``Char [])
      (.forallE n₂ (.app (.const ``List [.zero]) (.const ``Char []))
        (.app (.const ``List [.zero]) (.const ``Char [])) bi₂) bi₁) e') :
    e' = .forallE .char (.forallE .listChar .listChar) := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g3⟩ := trExprS_arrow_inv' h3
  cases trExprS_listChar_inv' g1
  cases trExprS_listChar_inv' g3
  rfl

theorem trExprS_listCharString_inv' {env : VEnv} {Us Δ} {nm bi e'}
    (h : TrExprS env Us Δ (.forallE nm (.app (.const ``List [.zero]) (.const ``Char []))
      (.const ``String []) bi) e') : e' = .forallE .listChar .string := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h3
  cases trExprS_listChar_inv' h1
  rfl
