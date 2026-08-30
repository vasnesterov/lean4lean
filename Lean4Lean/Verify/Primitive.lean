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
theorem reflects_natBitwiseApp (henv : env.WF) (hbw : env.ReflectsNatBitwise)
    (hc : env.contains ``Nat.bitwise)
    {f : VExpr} {g : Bool → Bool → Bool} (hf : env.ReflectsBoolBoolBool f g) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise g a b)) :=
  hbw hc env VEnv.LE.rfl f g henv hf a b

/-- `Nat.land`'s combinator: the recognizer checks `and false x ≡ false` and `and true x ≡ x`
under a `Bool`-typed free variable. -/
theorem reflectsBoolBoolBool_and {f : VExpr}
    (hty : env.HasType 0 [] f (.forallE .bool (.forallE .bool .bool)))
    (h0 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolFalse) (.boolLit b)) .boolFalse)
    (h1 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolTrue) (.boolLit b)) (.boolLit b)) :
    env.ReflectsBoolBoolBool f and :=
  ⟨hty, fun
    | false, b => h0 b
    | true, b => h1 b⟩

/-- `Nat.lor`'s combinator: `or false x ≡ x` and `or true x ≡ true`. -/
theorem reflectsBoolBoolBool_or {f : VExpr}
    (hty : env.HasType 0 [] f (.forallE .bool (.forallE .bool .bool)))
    (h0 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolFalse) (.boolLit b)) (.boolLit b))
    (h1 : ∀ b : Bool, env.IsDefEqU 0 [] (.app (.app f .boolTrue) (.boolLit b)) .boolTrue) :
    env.ReflectsBoolBoolBool f or :=
  ⟨hty, fun
    | false, b => h0 b
    | true, b => h1 b⟩

/-- `Nat.xor`'s combinator is `bne`, and the recognizer checks all four closed cases. -/
theorem reflectsBoolBoolBool_bne {f : VExpr}
    (hty : env.HasType 0 [] f (.forallE .bool (.forallE .bool .bool)))
    (hff : env.IsDefEqU 0 [] (.app (.app f .boolFalse) .boolFalse) .boolFalse)
    (htf : env.IsDefEqU 0 [] (.app (.app f .boolTrue) .boolFalse) .boolTrue)
    (hft : env.IsDefEqU 0 [] (.app (.app f .boolFalse) .boolTrue) .boolTrue)
    (htt : env.IsDefEqU 0 [] (.app (.app f .boolTrue) .boolTrue) .boolFalse) :
    env.ReflectsBoolBoolBool f bne :=
  ⟨hty, fun
    | false, false => hff
    | true, false => htf
    | false, true => hft
    | true, true => htt⟩

/-- `Nat.land`, whose value the recognizer destructures as `Nat.bitwise and`. -/
theorem reflects_natLAnd (henv : env.WF) (hbw : env.ReflectsNatBitwise)
    (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f and) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.land a b)) := reflects_natBitwiseApp henv hbw hc hf a b

/-- `Nat.lor`, whose value the recognizer destructures as `Nat.bitwise or`. -/
theorem reflects_natLOr (henv : env.WF) (hbw : env.ReflectsNatBitwise)
    (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f or) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.lor a b)) := reflects_natBitwiseApp henv hbw hc hf a b

/-- `Nat.xor`, whose value the recognizer destructures as `Nat.bitwise bne`. -/
theorem reflects_natXor (henv : env.WF) (hbw : env.ReflectsNatBitwise)
    (hc : env.contains ``Nat.bitwise)
    {f : VExpr} (hf : env.ReflectsBoolBoolBool f bne) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.xor a b)) := reflects_natBitwiseApp henv hbw hc hf a b

end VEnv

/-! ## Conditionals: the `Condition` reflection lemma

`docs/handoff-primitive.md` §5(a): three of the four open branches (`Nat.mod`, `Nat.div`,
`Nat.bitwise`) state their defining equations with `Condition.ite` / `Condition.dite`, i.e.
with `@ite`/`@dite` at the *instance* `cond.dec`, and there was no lemma anywhere about
conditionals in the abstract syntax.  This section is that lemma, together with the
congruence and instantiation tools its consumers need.

**What is here and what is not.**  `reflects_condApp` takes the three checked facts already
instantiated and β-reduced and produces the reduction rule.  What it does *not* do is perform
that instantiation and β-reduction for a particular branch: `Reflection.ite` is a four-fold λ
and `Reflection.checkITE` compares under two binders whose domains are `Prop` and
`r.type p b`, so the connection is four `IsDefEqU.beta'`s, two `IsDefEqU.inst0`s and two
`app_congr_fn'`s per equation.  Those tools are here; wiring them to
`Boundaries.lean`'s `Nat.mod`/`Nat.div` branches is the next step, and it is the only thing
between this section and §5(b)'s fuel induction. -/

/-- A conditional application in the abstract syntax: `F c inst t e`, where `F` is the
conditional's head already applied to its result type (`@ite α`, or `@dite Nat` as
`Condition.dite` builds it) and the `Decidable` instance is an ordinary argument.

Leaving `F` abstract is deliberate: the constant name and the universe come from whatever
`TrExprS` hands back for the recognizer's `q(@ite.{1})` / `q(@dite Nat)`, so nothing here is
hard-wired, and the same shape serves both `Condition.ite` and `Condition.dite`. -/
def VExpr.condApp (F c inst t e : VExpr) : VExpr := ((((F.app c).app inst).app t).app e)

namespace VEnv
variable {env : VEnv}

theorem _root_.Lean4Lean.VExpr.WF.app_fn' (henv : env.WF) {u a : VExpr}
    (h : VExpr.WF env 0 [] (.app u a)) : VExpr.WF env 0 [] u :=
  let ⟨_, _, h1, _⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial h
  ⟨_, h1⟩

theorem _root_.Lean4Lean.VExpr.WF.app_arg' (henv : env.WF) {u a : VExpr}
    (h : VExpr.WF env 0 [] (.app u a)) : VExpr.WF env 0 [] a :=
  let ⟨_, _, _, h2⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial h
  ⟨_, h2⟩

theorem IsDefEqU.app_congr_arg' (henv : env.WF) {u a a' : VExpr}
    (hu : VExpr.WF env 0 [] (.app u a)) (h : env.IsDefEqU 0 [] a a') :
    env.IsDefEqU 0 [] (.app u a) (.app u a') := by
  obtain ⟨_, _, h1, h2⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial hu
  exact ⟨_, .appDF h1 (h.of_l henv trivial h2)⟩

theorem IsDefEqU.app_congr_fn' (henv : env.WF) {u u' a : VExpr}
    (hu : VExpr.WF env 0 [] (.app u a)) (h : env.IsDefEqU 0 [] u u') :
    env.IsDefEqU 0 [] (.app u a) (.app u' a) := by
  obtain ⟨_, _, h1, h2⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial hu
  exact ⟨_, .appDF (h.of_l henv trivial h1) h2⟩

theorem IsDefEqU.wf_r {a b : VExpr} (h : env.IsDefEqU 0 [] a b) :
    VExpr.WF env 0 [] b := let ⟨_, h⟩ := h; ⟨_, h.hasType.2⟩

/-- Replace the `Decidable` instance of a conditional application. -/
theorem IsDefEqU.condApp_congr_inst (henv : env.WF) {F c i i' t e : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) (h : env.IsDefEqU 0 [] i i') :
    env.IsDefEqU 0 [] (VExpr.condApp F c i t e) (VExpr.condApp F c i' t e) :=
  IsDefEqU.app_congr_fn' henv hwt <|
    IsDefEqU.app_congr_fn' henv (hwt.app_fn' henv) <|
      IsDefEqU.app_congr_arg' henv ((hwt.app_fn' henv).app_fn' henv) h

/-! ### Recovering an argument's *declared* type from a well-typed application

**`docs/handoff-primitive.md` §4.2, resolved.**  `reflects_condApp`'s `hsel` had only
`VExpr.WF env 0 [] (VExpr.condApp …)` in hand, while `IsDefEqU.inst4` -- the only tool that can
supply it, since the recognizer proves the selection equation under four binders -- needs the
four arguments typed at the conditional head's *declared* domains.  `VExpr.WF.app_inv` invents
an existential domain, so the two cannot be joined without Pi-injectivity.

They join *with* it, at no cost: `VEnv.HasType.piUniq` (`Verify/Typing/Lemmas.lean`, itself
`IsDefEq.uniqU` composed with `IsDefEqU.forallE_inv`) is **already inside
`checkPrimitiveDef.WF`'s forward cone** -- measured with a reachability scan over
`ConstantInfo.value?`, not argued -- so this is inherited taint and not a new hole.  The
alternative considered (strengthening `ReflectsCondApp` itself) would have had to be re-checked
against three already-proved consumers; this route changes nothing downstream of
`reflects_condApp`. -/

/-- **One application step with the function's Pi-type known.**  Exactly the step
`VExpr.WF.app_inv` cannot make alone: it returns the *declared* domain, not an existential
one. -/
theorem _root_.Lean4Lean.VExpr.WF.app_arg_typed (henv : env.WF) {f a A B : VExpr}
    (hf : env.HasType 0 [] f (.forallE A B)) (h : VExpr.WF env 0 [] (.app f a)) :
    env.HasType 0 [] a A :=
  let ⟨_, _, hf', ha'⟩ := VExpr.WF.app_inv (U := 0) (Γ := []) henv.ordered trivial h
  let ⟨⟨_, hAA⟩, _⟩ := VEnv.HasType.piUniq henv trivial hf' hf
  HasType.defeqU_r henv trivial ⟨_, hAA⟩ ha'

/-- **The fully general form**: the four arguments of a four-fold application are typed at the
head's four declared domains, each instantiated by the arguments before it.  No closedness and
no shape assumption -- `dite`, whose two branch domains are `c → Nat` and `¬c → Nat` and so
*do* depend on the earlier arguments, is the case that needs this generality. -/
theorem condApp_typed' (henv : env.WF) {F A₀ A₁ A₂ A₃ R c i t e : VExpr}
    (hF : env.HasType 0 [] F (.forallE A₀ (.forallE A₁ (.forallE A₂ (.forallE A₃ R)))))
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) :
    env.HasType 0 [] c A₀ ∧ env.HasType 0 [] i (A₁.inst c) ∧
      env.HasType 0 [] t ((A₂.inst c 1).inst i) ∧
      env.HasType 0 [] e (((A₃.inst c 2).inst i 1).inst t) := by
  have h1 : VExpr.WF env 0 [] (.app F c) := ((hwt.app_fn' henv).app_fn' henv).app_fn' henv
  have hc := VExpr.WF.app_arg_typed henv hF h1
  have hFc := hF.app hc
  have h2 : VExpr.WF env 0 [] (.app (.app F c) i) := (hwt.app_fn' henv).app_fn' henv
  have hi := VExpr.WF.app_arg_typed henv hFc h2
  have hFci := hFc.app hi
  have h3 : VExpr.WF env 0 [] (.app (.app (.app F c) i) t) := hwt.app_fn' henv
  have ht := VExpr.WF.app_arg_typed henv hFci h3
  exact ⟨hc, hi, ht, VExpr.WF.app_arg_typed henv (hFci.app ht) hwt⟩

/-- **The `ite` case, in the shape `VEnv.reflects_condApp` consumes.**  `F` is the conditional
already applied to its result type, so its type is `(c : Prop) -> Dc c -> Aα -> Aα -> Aα`; `Aα`
is closed because `Reflection.checkITE` `checkIsType`s it at the base context, which is what
makes the two branch domains need no lifting.  `Reflection.checkITE` pins `@ite`'s own type,
which is where `hF` comes from. -/
theorem condApp_typed (henv : env.WF) {F Dc Aα c i t e : VExpr} (hA0 : Aα.ClosedN 0)
    (hF : env.HasType 0 []
      F (.forallE (.sort .zero) (.forallE Dc (.forallE Aα (.forallE Aα Aα)))))
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) :
    env.HasType 0 [] c (.sort .zero) ∧ env.HasType 0 [] i (Dc.inst c) ∧
      env.HasType 0 [] t Aα ∧ env.HasType 0 [] e Aα := by
  have hid : ∀ {u : VExpr} {j}, Aα.inst u j = Aα := fun {_ _} => hA0.instN_eq (Nat.zero_le _)
  have h1 : VExpr.WF env 0 [] (.app F c) := ((hwt.app_fn' henv).app_fn' henv).app_fn' henv
  have hc := VExpr.WF.app_arg_typed henv hF h1
  have hFc : env.HasType 0 [] (.app F c)
      (.forallE (Dc.inst c) (.forallE Aα (.forallE Aα Aα))) := by
    have := hF.app hc; simpa [VExpr.inst, hid] using this
  have h2 : VExpr.WF env 0 [] (.app (.app F c) i) := (hwt.app_fn' henv).app_fn' henv
  have hi := VExpr.WF.app_arg_typed henv hFc h2
  have hFci : env.HasType 0 [] (.app (.app F c) i) (.forallE Aα (.forallE Aα Aα)) := by
    have := hFc.app hi; simpa [VExpr.inst, hid] using this
  have h3 : VExpr.WF env 0 [] (.app (.app (.app F c) i) t) := hwt.app_fn' henv
  have ht := VExpr.WF.app_arg_typed henv hFci h3
  have hFcit : env.HasType 0 [] (.app (.app (.app F c) i) t) (.forallE Aα Aα) := by
    have := hFci.app ht; simpa [VExpr.inst, hid] using this
  exact ⟨hc, hi, ht, VExpr.WF.app_arg_typed henv hFcit hwt⟩


/-! ### From the recognizer's binders to `reflects_condApp`'s hypotheses

`Reflection.checkITE` and `Reflection.checkNatDITE` compare terms under `withCheckedLocalDecl`
binders whose domains are `Prop` and `r.type p b` — not `Nat`, so `IsDefEqU.instNat` does not
apply.  These are the general tools. -/

/-- Instantiate a defeq proved under one binder of *arbitrary* domain.  `IsDefEqU.instNat` is
this at `A = .nat` with the numeral's typing supplied by `NatLits`. -/
theorem IsDefEqU.inst0 (henv : env.WF) {A a e₁ e₂ : VExpr} {Γ : List VExpr}
    (H : env.IsDefEqU 0 (A :: Γ) e₁ e₂) (ha : env.HasType 0 Γ a A) :
    env.IsDefEqU 0 Γ (e₁.inst a) (e₂.inst a) :=
  IsDefEqU.instN henv.ordered .zero H ha

/-- **Instantiate a defeq proved under four nested binders** whose only dependency is on the
outermost one -- exactly the shape `Reflection.checkITE` (`p`, `H`, `t`, `e`) and
`Reflection.checkNatDITE` (`p`, `H`, `a`, `b`) leave behind.  The outermost binder is
substituted first, by `IsDefEqU.instN` at depth 3, which instantiates the three inner domains
as it goes; the remaining three domains are then closed, so three `inst0`s finish the job.

This is why the recognizer binds `p` outermost: with any other order the inner domains still
mention `p` when their turn comes and no `HasType` in the empty context can be supplied for
them. -/
theorem IsDefEqU.inst4 (henv : env.WF) {A B C D p a b c e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 [C, B, A, D] e₁ e₂)
    (hp : env.HasType 0 [] p D)
    (ha : env.HasType 0 [] a (A.inst p 0))
    (hb : env.HasType 0 [] b (B.inst p 1))
    (hc : env.HasType 0 [] c (C.inst p 2)) :
    env.IsDefEqU 0 [] ((((e₁.inst p 3).inst c).inst b).inst a)
      ((((e₂.inst p 3).inst c).inst b).inst a) :=
  let h3 := IsDefEqU.instN henv.ordered (.succ (.succ (.succ .zero))) H hp
  let h2 := IsDefEqU.instN henv.ordered .zero h3 (hc.weak0 henv.ordered)
  let h1 := IsDefEqU.instN henv.ordered .zero h2 (hb.weak0 henv.ordered)
  IsDefEqU.instN henv.ordered .zero h1 (ha.weak0 henv.ordered)

/-- **Instantiate a defeq proved under two independent binders** of arbitrary closed domains --
the shape `Condition.check`'s `.bool` branch leaves behind (`t`, `e` at a fixed result type).
`IsDefEqU.instNat2` is this at `A = B = .nat`. -/
theorem IsDefEqU.inst2 (henv : env.WF) {A B a b e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 [B, A] e₁ e₂)
    (ha : env.HasType 0 [] a A) (hb : env.HasType 0 [] b B) :
    env.IsDefEqU 0 [] ((e₁.inst b).inst a) ((e₂.inst b).inst a) :=
  let h1 := IsDefEqU.instN henv.ordered .zero H (hb.weak0 henv.ordered)
  IsDefEqU.instN henv.ordered .zero h1 (ha.weak0 henv.ordered)

/-- β, packaged at `IsDefEqU`.  `Reflection.ite` is a four-fold λ, so getting from the
equation the recognizer checks to `reflects_condApp`'s `hsel` is four of these. -/
theorem IsDefEqU.beta' {A b a B : VExpr}
    (hb : env.HasType 0 [A] b B) (ha : env.HasType 0 [] a A) :
    env.IsDefEqU 0 [] (.app (.lam A b) a) (b.inst a) := ⟨_, .beta hb ha⟩

/-- Apply a function-level defeq to two further arguments — the step from
`r.ite p b H α ≡ f` to the `condApp` shape. -/
theorem IsDefEqU.app2_congr_fn (henv : env.WF) {f f' x y : VExpr}
    (hwt : VExpr.WF env 0 [] ((f.app x).app y)) (h : env.IsDefEqU 0 [] f f') :
    env.IsDefEqU 0 [] ((f.app x).app y) ((f'.app x).app y) :=
  IsDefEqU.app_congr_fn' henv hwt (IsDefEqU.app_congr_fn' henv (hwt.app_fn' henv) h)

/-- **What the four fuel/well-founded branches need of a `Condition`.**  Its conditional at a
pair of numerals reduces to the branch the boolean `g` selects.

`P` is the translated `cond.prop`, `D` the translated `cond.dec`, `F` the conditional head. -/
def ReflectsCondApp (env : VEnv) (F P D : VExpr) (g : Nat → Nat → Bool) : Prop :=
  ∀ (a b : Nat) (t e : VExpr),
    VExpr.WF env 0 [] (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
      (.app (.app D (.natLit a)) (.natLit b)) t e) →
    env.IsDefEqU 0 []
      (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
        (.app (.app D (.natLit a)) (.natLit b)) t e)
      (bif g a b then t else e)

/-- **The `Condition` reflection lemma.**

Every hypothesis is the abstract reading of one comparison `Condition.check` /
`Reflection.checkITE` / `Reflection.checkNatDITE` actually makes:

* `hdec` is `isDefEq e cond.dec` with `e = fun x y => toDec (prop x y) (asBool x y) (proof x y)`,
  β-reduced at the two numerals;
* `hB` is the reflection of `cond.impl`'s `asBool` — for `Condition.natLE` that is
  `Nat.ble`, and `hB` is `VEnv.HasPrimitives.natBLE`;
* `hsel` is the pair of equations `checkITE` (resp. `checkNatDITE`) checks under its `p` and
  `H` binders, instantiated and β-reduced through `Reflection.ite`'s λ.

Nothing is assumed about `toDec` beyond `hsel`: the decision procedure is a black box whose
only property is that at a *literal* boolean it selects. -/
theorem reflects_condApp (henv : env.WF) {F P D TD B PR RT Dc Aα : VExpr}
    {g : Nat → Nat → Bool} (hA0 : Aα.ClosedN 0)
    (hF : env.HasType 0 []
      F (.forallE (.sort .zero) (.forallE Dc (.forallE Aα (.forallE Aα Aα)))))
    (hdec : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))))
    (hB : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app B (.natLit a)) (.natLit b))
      (.boolLit (g a b)))
    (hPR : ∀ a b : Nat, env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (g a b))))
    (hsel : ∀ (p H t e : VExpr) (v : Bool),
      env.HasType 0 [] p (.sort .zero) →
      env.HasType 0 [] H (.app (.app RT p) (.boolLit v)) →
      env.HasType 0 [] t Aα → env.HasType 0 [] e Aα →
      env.IsDefEqU 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e)
        (bif v then t else e)) :
    env.ReflectsCondApp F P D g := by
  intro a b t e hwt
  have s1 := IsDefEqU.condApp_congr_inst henv hwt (hdec a b)
  have hwt1 := s1.wf_r
  have hslot : VExpr.WF env 0 []
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))) :=
    ((hwt1.app_fn' henv).app_fn' henv).app_arg' henv
  have s2 := IsDefEqU.condApp_congr_inst henv hwt1
    (IsDefEqU.app_congr_fn' henv hslot
      (IsDefEqU.app_congr_arg' henv (hslot.app_fn' henv) (hB a b)))
  obtain ⟨hc, -, ht, he⟩ := condApp_typed henv hA0 hF s2.wf_r
  exact IsDefEqU.trans henv trivial s1 <|
    IsDefEqU.trans henv trivial s2 (hsel _ _ _ _ _ hc (hPR a b) ht he)

/-- **`Condition.natLE`, the one the `Nat.mod` and `Nat.div` branches use.**  Its `asBool` is
`Nat.ble`, so the boolean side is the `HasPrimitives` field `natBLE` and the caller supplies
nothing for it. -/
theorem reflects_condApp_natLE (henv : env.WF) (hprim : env.HasPrimitives)
    (hble : env.contains ``Nat.ble) {F P D TD PR RT Dc Aα : VExpr} (hA0 : Aα.ClosedN 0)
    (hF : env.HasType 0 []
      F (.forallE (.sort .zero) (.forallE Dc (.forallE Aα (.forallE Aα Aα)))))
    (hdec : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
          (.app (.app (.const ``Nat.ble []) (.natLit a)) (.natLit b)))
        (.app (.app PR (.natLit a)) (.natLit b))))
    (hPR : ∀ a b : Nat, env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (Nat.ble a b))))
    (hsel : ∀ (p H t e : VExpr) (v : Bool),
      env.HasType 0 [] p (.sort .zero) →
      env.HasType 0 [] H (.app (.app RT p) (.boolLit v)) →
      env.HasType 0 [] t Aα → env.HasType 0 [] e Aα →
      env.IsDefEqU 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e)
        (bif v then t else e)) :
    env.ReflectsCondApp F P D Nat.ble :=
  reflects_condApp henv hA0 hF hdec (fun a b => hprim.natBLE hble a b) hPR hsel

/-- **`hsel` from the shape `Reflection.checkITE` actually leaves behind** -- the acceptance
test for the interface above.

`checkITE` compares its two equations under the four binders `p : Prop`, `H : r.type p b`,
`t e : α`, so what the verification reads off it is an `IsDefEqU` in the context
`[Aα, Aα, RT (bvar 0) (boolLit v), .sort .zero]`.  `hsel`'s four typing hypotheses are
*precisely* `IsDefEqU.inst4`'s four, and the closedness side conditions are all derivable
(`VExpr.WF.closedN` at the empty context), so the instantiation goes through with no further
input.  Without this lemma `hsel` would be a hypothesis nobody had ever discharged. -/
theorem hsel_of_checkITE (henv : env.WF) {F TD RT Aα : VExpr}
    (hFc : F.ClosedN 0) (hTDc : TD.ClosedN 0) (hRTc : RT.ClosedN 0) (hA0 : Aα.ClosedN 0)
    (h : ∀ v : Bool, env.IsDefEqU 0
        [Aα, Aα, .app (.app RT (.bvar 0)) (.boolLit v), .sort .zero]
        (VExpr.condApp F (.bvar 3)
          (.app (.app (.app TD (.bvar 3)) (.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
        (bif v then .bvar 1 else .bvar 0)) :
    ∀ (p H t e : VExpr) (v : Bool),
      env.HasType 0 [] p (.sort .zero) →
      env.HasType 0 [] H (.app (.app RT p) (.boolLit v)) →
      env.HasType 0 [] t Aα → env.HasType 0 [] e Aα →
      env.IsDefEqU 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e)
        (bif v then t else e) := by
  intro p H t e v hp hH ht he
  have cl : ∀ {u T : VExpr}, env.HasType 0 [] u T → ∀ (w : VExpr) (j : Nat), u.inst w j = u :=
    fun hu _ _ => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).instN_eq (Nat.zero_le _)
  have lf : ∀ {u T : VExpr}, env.HasType 0 [] u T → u.lift = u :=
    fun hu => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).lift_eq
  have eF : ∀ (w : VExpr) (j : Nat), F.inst w j = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
  have eTD : ∀ (w : VExpr) (j : Nat), TD.inst w j = TD := fun _ _ => hTDc.instN_eq (Nat.zero_le _)
  have eRT : ∀ (w : VExpr) (j : Nat), RT.inst w j = RT := fun _ _ => hRTc.instN_eq (Nat.zero_le _)
  have eA : ∀ (w : VExpr) (j : Nat), Aα.inst w j = Aα := fun _ _ => hA0.instN_eq (Nat.zero_le _)
  have ep := cl hp; have eH := cl hH; have et := cl ht; have ee := cl he
  have lp := lf hp; have lH := lf hH; have lt := lf ht; have le' := lf he
  have key := IsDefEqU.inst4 (A := .app (.app RT (.bvar 0)) (.boolLit v)) (B := Aα) (C := Aα)
    (D := .sort .zero) (p := p) (a := H) (b := t) (c := e) henv (h v)
    hp (by simpa [VExpr.inst, eRT] using hH) (by simpa [eA] using ht) (by simpa [eA] using he)
  cases v <;>
    simpa [VExpr.condApp, VExpr.inst, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar,
      eF, eTD, ep, eH, et, ee, lp, lH, lt, le'] using key

/-! ### The `dite` rule, which is **not** `ReflectsCondApp`

`Condition.dite` (`Lean4Lean/Primitive.lean`) wraps both branches in a λ over the decision's
proof -- `mkApp4 q(@dite Nat) (prop args) (dec args) (.lam0 (prop args) t) (.lam0 (Not …) e)` --
and `@dite`'s reduction **applies** the selected λ to that proof: `Reflection.checkNatDITE`
checks `dite p (toDec p true H) a b ≡ a (ofTrue p H)`, not `≡ a`.

`VEnv.ReflectsCondApp` says `condApp F … t e ≡ bif g a b then t else e`, which is therefore the
`ite` rule and **only** the `ite` rule.  The `Nat.mod` and `Nat.div` `go` equations are `dite`s
(`Lean4Lean/Primitive.lean`, the `c.dite #[y, x] …` lines), so they need the statement below.
This corrects `reflects_fuel_go`'s old `hdite : ReflectsCondApp …` hypothesis, which could not
have been supplied: its `t` slot was `wrap (VExpr.app5 GO …)` and `hbase` forced its `e` slot to
be *syntactically* `.natLit (sem x b)`, while the term the recognizer builds has a λ in each. -/

/-- **The `dite` selection rule at a pair of numerals.** -/
def ReflectsCondAppD (env : VEnv) (F P D OT OF PR : VExpr) (g : Nat → Nat → Bool) : Prop :=
  ∀ (a b : Nat) (t e : VExpr),
    VExpr.WF env 0 [] (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
      (.app (.app D (.natLit a)) (.natLit b)) t e) →
    env.IsDefEqU 0 []
      (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
        (.app (.app D (.natLit a)) (.natLit b)) t e)
      (bif g a b then
          .app t (.app (.app OT (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b)))
        else .app e (.app (.app OF (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b))))

/-- **`reflects_condApp` for `dite`.**  Same two congruence steps -- replace the instance by the
`toDec` application `Condition.check`'s `isDefEq e cond.dec` proves it equal to, then replace
the boolean by its literal -- and then the selection rule the recognizer checked.

`hsel` keeps the `VExpr.WF` premise (which is available) rather than the branch typings, because
`dite`'s branch domains `c → Nat` and `¬c → Nat` depend on `c`: its supplier recovers them with
`VEnv.condApp_typed'` from `@dite Nat`'s type, which `Reflection.checkNatDITE` pins. -/
theorem reflects_condAppD (henv : env.WF) {F P D TD B PR RT OT OF : VExpr}
    {g : Nat → Nat → Bool}
    (hdec : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))))
    (hB : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app B (.natLit a)) (.natLit b))
      (.boolLit (g a b)))
    (hPR : ∀ a b : Nat, env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (g a b))))
    (hsel : ∀ (p H t e : VExpr) (v : Bool),
      VExpr.WF env 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e) →
      env.HasType 0 [] H (.app (.app RT p) (.boolLit v)) →
      env.IsDefEqU 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e)
        (bif v then .app t (.app (.app OT p) H) else .app e (.app (.app OF p) H))) :
    env.ReflectsCondAppD F P D OT OF PR g := by
  intro a b t e hwt
  have s1 := IsDefEqU.condApp_congr_inst henv hwt (hdec a b)
  have hwt1 := s1.wf_r
  have hslot : VExpr.WF env 0 []
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))) :=
    ((hwt1.app_fn' henv).app_fn' henv).app_arg' henv
  have s2 := IsDefEqU.condApp_congr_inst henv hwt1
    (IsDefEqU.app_congr_fn' henv hslot
      (IsDefEqU.app_congr_arg' henv (hslot.app_fn' henv) (hB a b)))
  exact IsDefEqU.trans henv trivial s1 <|
    IsDefEqU.trans henv trivial s2 (hsel _ _ _ _ _ s2.wf_r (hPR a b))

/-- The reading `reflects_fuel_go`'s `hsel` wants for a `dite`: `b ≤ x` decides the branch. -/
theorem ReflectsCondAppD.natLE_le {F P D OT OF PR : VExpr}
    (h : env.ReflectsCondAppD F P D OT OF PR Nat.ble) (a b : Nat) (t e : VExpr)
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
      (.app (.app D (.natLit a)) (.natLit b)) t e)) :
    env.IsDefEqU 0 []
      (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
        (.app (.app D (.natLit a)) (.natLit b)) t e)
      (if a ≤ b then
          .app t (.app (.app OT (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b)))
        else .app e (.app (.app OF (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b)))) := by
  have := h a b t e hwt
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    rwa [show Nat.ble a b = true by rw [Nat.ble_eq]; exact hab] at this
  · rw [if_neg hab]
    rwa [show Nat.ble a b = false by
      cases hc : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hc) hab] at this

/-- The reading the `Nat.mod`/`Nat.div` recursions want: `a ≤ b` decides the branch. -/
theorem ReflectsCondApp.natLE_le (h : env.ReflectsCondApp F P D Nat.ble) (a b : Nat)
    (t e : VExpr)
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
      (.app (.app D (.natLit a)) (.natLit b)) t e)) :
    env.IsDefEqU 0 []
      (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
        (.app (.app D (.natLit a)) (.natLit b)) t e)
      (if a ≤ b then t else e) := by
  have := h a b t e hwt
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    rwa [show Nat.ble a b = true by rw [Nat.ble_eq]; exact hab] at this
  · rw [if_neg hab]
    rwa [show Nat.ble a b = false by
      cases h : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hab] at this

end VEnv

/-! ## Fuel recursion: `Nat.mod` and `Nat.div`

`docs/handoff-primitive.md` §5(b).  Both branches constrain `Nat.modCore.go` / `Nat.div.go`
*only* at `Nat.succ fuel`; the `fuel = 0` case is unreachable and staying inside that is the
`x < fuel` invariant carried below.  This is an ordinary induction on the fuel, and it is the
*same* induction twice — `reflects_fuel_go` is parametrised by the wrapper (`id` for `mod`,
`Nat.succ` for `div`), the fuel-exhausted branch (`x` for `mod`, `0` for `div`) and the
arithmetic recurrence.

**The conditional is abstracted away, and must be.**  An earlier version took
`hdite : ReflectsCondApp Fd Pd Dd Nat.ble` and stated `hgo`'s right-hand side as a
`VExpr.condApp` whose branch slots were `wrap (VExpr.app5 GO …)` and `base x`.  That hypothesis
**cannot be supplied**: the `go` equations the recognizer checks are `Condition.dite`s, which
wrap both branches in a λ over the decision's proof, and `hbase` forces the `e` slot to be
*syntactically* `.natLit (sem x b)`.  `hgo` now names an abstract right-hand side `RHS` and
`hsel` says it selects; the branch builds `hsel` from `VEnv.ReflectsCondAppD` (for a `dite`) or
`VEnv.ReflectsCondApp` (for an `ite`), and the induction no longer cares which.

The two proof arguments `go` carries (`1 ≤ y` and `Nat.succ x ≤ fuel`) are opaque `VExpr`s
here.  They are handled by a predicate `Ok` the caller chooses and a proof-builder `K` for the
recursive call — the shape `Nat.div_rec_fuel_lemma` has in the recognizer — with the single
requirement `hK` that `K` preserves `Ok`.  Nothing about their *types* is needed, which is
what makes the induction independent of the branch's plumbing.

**`Ok` is indexed by the fuel and the numerator, and must be.**  An earlier version of this
section wrote `Ok : Nat → VExpr → VExpr → Prop`, i.e. `Ok b hy h` with no dependence on `f`
and `x`.  That version is true but *unusable*: `hgo b f x hy h` asserts a defeq whose left
side is `GO b hy (f+1) x h`, and `IsDefEqU` entails well-typedness, so `h` must have type
`x+1 ≤ f+1` for these particular `f` and `x`.  A three-argument `Ok` cannot say that — it is
carried unchanged across the recursive call, where the fuel is `f` and the numerator `x - b`,
and a proof of `x+1 ≤ f+1` is not a proof of `x-b+1 ≤ f`.  Any `Ok` strong enough to make
`hgo` provable is therefore empty, and the conclusion is then vacuous at every call site.
Indexing `Ok` by `f` and `x` costs the induction nothing (`hK` steps the indices down exactly
as the recursive call does) and is what the `Nat.mod` / `Nat.div` branches can actually
supply. -/

/-- A five-fold application: the shape `Nat.modCore.go y hy fuel x h` and `Nat.div.go` have. -/
def VExpr.app5 (F a b c d e : VExpr) : VExpr := ((((F.app a).app b).app c).app d).app e

namespace VEnv
variable {env : VEnv}

/-- **Fuel induction, for both `Nat.mod` and `Nat.div`.** -/
theorem reflects_fuel_go (henv : env.WF)
    {GO : VExpr} {RHS K : Nat → Nat → Nat → VExpr → VExpr → VExpr}
    {Ok : Nat → VExpr → Nat → Nat → VExpr → Prop} {wrap : VExpr → VExpr} {base : Nat → VExpr}
    {sem : Nat → Nat → Nat} {w : Nat → Nat}
    (hgo : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      env.IsDefEqU 0 []
        (VExpr.app5 GO (.natLit b) hy (.natLit (f + 1)) (.natLit x) h)
        (RHS b f x hy h))
    (hsel : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      VExpr.WF env 0 [] (RHS b f x hy h) →
      env.IsDefEqU 0 [] (RHS b f x hy h)
        (if b ≤ x then
            wrap (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit (x - b)) (K b f x hy h))
          else base x))
    (hK : ∀ b f x hy h, Ok b hy (f+1) x h → Ok b hy f (x - b) (K b f x hy h))
    (hwrap : ∀ (n : Nat) (u : VExpr), env.IsDefEqU 0 [] u (.natLit n) →
      env.IsDefEqU 0 [] (wrap u) (.natLit (w n)))
    (hrec : ∀ x b : Nat, 1 ≤ b → b ≤ x → sem x b = w (sem (x - b) b))
    (hbase : ∀ x b : Nat, 1 ≤ b → ¬ b ≤ x → base x = .natLit (sem x b)) :
    ∀ (f x b : Nat), 1 ≤ b → x < f → ∀ hy h, Ok b hy f x h →
      env.IsDefEqU 0 [] (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit x) h)
        (.natLit (sem x b)) := by
  intro f
  induction f with
  | zero => intro x b _ hx; exact absurd hx (by omega)
  | succ f ih =>
    intro x b hb hx hy h hok
    have e1 := hgo b f x hy h hok
    have e2 := hsel b f x hy h hok e1.wf_r
    refine IsDefEqU.trans henv trivial e1 (IsDefEqU.trans henv trivial e2 ?_)
    by_cases hbx : b ≤ x
    · rw [if_pos hbx, hrec x b hb hbx]
      exact hwrap _ _ (ih (x - b) b hb (by omega) hy _ (hK b f x hy h hok))
    · have hw : VExpr.WF env 0 [] (base x) := by rw [if_neg hbx] at e2; exact e2.wf_r
      rw [if_neg hbx]
      rw [hbase x b hb hbx] at hw ⊢
      exact IsDefEqU.refl hw


/-- `Nat.succ` applied to a term that reflects `n` reflects `n+1`. -/
theorem reflects_succ (henv : env.WF) (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    (n : Nat) {u : VExpr} (h : env.IsDefEqU 0 [] u (.natLit n)) :
    env.IsDefEqU 0 [] (.app .natSucc u) (.natLit (n + 1)) :=
  ⟨_, .appDF (hprim.natSucc_hasType hnat) (h.of_r henv trivial (hprim.natLit_hasType hnat n))⟩

/-- **`Nat.mod`'s fuel recursion.**  The wrapper is the identity and the fuel-exhausted branch
returns the numerator, which is `x % b` exactly when `x < b`. -/
theorem reflects_fuel_mod (henv : env.WF)
    {GO : VExpr} {RHS K : Nat → Nat → Nat → VExpr → VExpr → VExpr}
    {Ok : Nat → VExpr → Nat → Nat → VExpr → Prop}
    (hgo : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      env.IsDefEqU 0 []
        (VExpr.app5 GO (.natLit b) hy (.natLit (f + 1)) (.natLit x) h)
        (RHS b f x hy h))
    (hsel : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      VExpr.WF env 0 [] (RHS b f x hy h) →
      env.IsDefEqU 0 [] (RHS b f x hy h)
        (if b ≤ x then
            VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit (x - b)) (K b f x hy h)
          else .natLit x))
    (hK : ∀ b f x hy h, Ok b hy (f+1) x h → Ok b hy f (x - b) (K b f x hy h)) :
    ∀ (f x b : Nat), 1 ≤ b → x < f → ∀ hy h, Ok b hy f x h →
      env.IsDefEqU 0 [] (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit x) h)
        (.natLit (x % b)) :=
  reflects_fuel_go (wrap := id) (w := id) (base := fun x => .natLit x) (sem := (· % ·))
    henv hgo hsel hK (fun _ _ h => h)
    (fun _ _ _ hbx => Nat.mod_eq_sub_mod hbx)
    (fun x b _ hbx => congrArg VExpr.natLit (Nat.mod_eq_of_lt (by omega)).symm)

/-- **`Nat.div`'s fuel recursion.**  Same induction, with `Nat.succ` as the wrapper and `0` as
the fuel-exhausted branch. -/
theorem reflects_fuel_div (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat)
    {GO : VExpr} {RHS K : Nat → Nat → Nat → VExpr → VExpr → VExpr}
    {Ok : Nat → VExpr → Nat → Nat → VExpr → Prop}
    (hgo : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      env.IsDefEqU 0 []
        (VExpr.app5 GO (.natLit b) hy (.natLit (f + 1)) (.natLit x) h)
        (RHS b f x hy h))
    (hsel : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy (f+1) x h →
      VExpr.WF env 0 [] (RHS b f x hy h) →
      env.IsDefEqU 0 [] (RHS b f x hy h)
        (if b ≤ x then
            .app .natSucc
              (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit (x - b)) (K b f x hy h))
          else .natLit 0))
    (hK : ∀ b f x hy h, Ok b hy (f+1) x h → Ok b hy f (x - b) (K b f x hy h)) :
    ∀ (f x b : Nat), 1 ≤ b → x < f → ∀ hy h, Ok b hy f x h →
      env.IsDefEqU 0 [] (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit x) h)
        (.natLit (x / b)) :=
  reflects_fuel_go (wrap := (.app .natSucc ·)) (w := (· + 1))
    (base := fun _ => .natLit 0) (sem := (· / ·))
    henv hgo hsel hK (fun n u h => reflects_succ henv hprim hnat n h)
    (fun _ _ hb hbx => Nat.div_eq_sub_div (by omega) hbx)
    (fun x b _ hbx => congrArg VExpr.natLit (Nat.div_eq_of_lt (by omega)).symm)

end VEnv


/-! ## `Nat.bitwise`: the second-order field

`docs/handoff-primitive.md` §5(d).  `VEnv.ReflectsNatBitwise` is the one `HasPrimitives` field
whose statement quantifies over an arbitrary later extension and an arbitrary combinator `f`,
and the recursion it describes steps on `n / 2` and `m / 2` rather than on a constructor.  The
induction below is the whole content of that field, stated over the equation the recognizer
checks and nothing else.

**Why `VEnv.ReflectsBoolBoolBool` carries a typing conjunct, and `ReflectsNatBitwise` an
`env'.WF`.**  As originally stated (no typing conjunct, no `env'.WF`) `ReflectsNatBitwise` was
*not provable*, for an information-flow reason, and `checkPrimitiveDef.WF.rest` was therefore
**false** at its `Nat.bitwise` branch rather than merely open.  Its conclusion is

```
env'.IsDefEqU 0 [] (Nat.bitwise · f · a · b) (natLit (Nat.bitwise g a b))
```

and `IsDefEqU` entails well-typedness, so the conclusion *asserts* that `f` may be applied at
`Nat.bitwise`'s domain — i.e. that `env'.HasType 0 [] f (Bool → Bool → Bool)`.  The only
hypothesis about `f` was the truth table, which says that `f` applied to two boolean *literals*
reduces to a literal; that does not give the typing.  A term `f : (x : Bool) → Q x` in an
environment carrying `Q Bool.true ≡ Bool → Bool` and `Q Bool.false ≡ Bool → Bool` — and nothing
about `Q` at a variable — satisfies the truth table while `Nat.bitwise · f` is ill-typed; `env'`
ranges over *arbitrary* extensions, so nothing rules that environment out.  Separately, the
proof below chains `IsDefEqU` steps and `IsDefEqU.trans` needs a well-formed environment, which
`env ≤ env'` alone does not supply for the new `f`.

Both hypotheses are now part of the definitions in `Verify/Typing/Expr.lean`, and the
`Nat.land` / `Nat.lor` / `Nat.xor` recognizer branches supply the typing with a
`checkedTypeIs _ q(Bool → Bool → Bool)`.  The repair loses no content: whenever `Nat.bitwise`'s
own type is `(Bool → Bool → Bool) → Nat → Nat → Nat`, which the recognizer's `checkPrimValue`
pins, the conclusion at an `f` *without* that typing was false anyway.  See
`docs/handoff-primitive.md` §3. -/

/-! ### Conditionals with one boolean scrutinee, and conditionals at non-literal arguments -/

/-- Two-fold application, the shape every argument position of the `Nat.bitwise` equation
has. -/
def VExpr.app2' (F a b : VExpr) : VExpr := (F.app a).app b

/-- A primitive binary `Nat` operation applied to two terms. -/
def VExpr.natOp (n : Name) (a b : VExpr) : VExpr := VExpr.app2' (.const n []) a b

namespace VEnv
variable {env : VEnv}

theorem _root_.Lean4Lean.VExpr.WF.app2_fn (henv : env.WF) {F u v : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.app2' F u v)) : VExpr.WF env 0 [] F :=
  (h.app_fn' henv).app_fn' henv

theorem _root_.Lean4Lean.VExpr.WF.app2_arg1 (henv : env.WF) {F u v : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.app2' F u v)) : VExpr.WF env 0 [] u :=
  (h.app_fn' henv).app_arg' henv

theorem _root_.Lean4Lean.VExpr.WF.app2_arg2 (henv : env.WF) {F u v : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.app2' F u v)) : VExpr.WF env 0 [] v := h.app_arg' henv

theorem _root_.Lean4Lean.VExpr.WF.condApp_cond (henv : env.WF) {F c i t e : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) : VExpr.WF env 0 [] c :=
  (((h.app_fn' henv).app_fn' henv).app_fn' henv).app_arg' henv

theorem _root_.Lean4Lean.VExpr.WF.condApp_inst (henv : env.WF) {F c i t e : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) : VExpr.WF env 0 [] i :=
  ((h.app_fn' henv).app_fn' henv).app_arg' henv

theorem _root_.Lean4Lean.VExpr.WF.condApp_t (henv : env.WF) {F c i t e : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) : VExpr.WF env 0 [] t :=
  (h.app_fn' henv).app_arg' henv

theorem _root_.Lean4Lean.VExpr.WF.condApp_e (henv : env.WF) {F c i t e : VExpr}
    (h : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) : VExpr.WF env 0 [] e := h.app_arg' henv

theorem IsDefEqU.app2_congr_args (henv : env.WF) {F u u' v v' : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.app2' F u v))
    (hu : env.IsDefEqU 0 [] u u') (hv : env.IsDefEqU 0 [] v v') :
    env.IsDefEqU 0 [] (VExpr.app2' F u v) (VExpr.app2' F u' v') := by
  have h1 : env.IsDefEqU 0 [] (VExpr.app2' F u v) (VExpr.app2' F u' v) :=
    IsDefEqU.app_congr_fn' henv hwt (IsDefEqU.app_congr_arg' henv (hwt.app_fn' henv) hu)
  exact IsDefEqU.trans henv trivial h1 (IsDefEqU.app_congr_arg' henv h1.wf_r hv)

/-- Replace a conditional's *condition* (not its instance). -/
theorem IsDefEqU.condApp_congr_cond (henv : env.WF) {F c c' i t e : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F c i t e)) (h : env.IsDefEqU 0 [] c c') :
    env.IsDefEqU 0 [] (VExpr.condApp F c i t e) (VExpr.condApp F c' i t e) :=
  IsDefEqU.app_congr_fn' henv hwt <|
    IsDefEqU.app_congr_fn' henv (hwt.app_fn' henv) <|
      IsDefEqU.app_congr_fn' henv ((hwt.app_fn' henv).app_fn' henv) <|
        IsDefEqU.app_congr_arg' henv (((hwt.app_fn' henv).app_fn' henv).app_fn' henv) h

/-- A `ReflectsCondApp` read at arguments that merely *reflect* numerals -- the shape
`Nat.bitwise`'s equation has, where the scrutinee of the parity conditionals is
`Nat.mod n 2` rather than a literal. -/
theorem ReflectsCondApp.ofDefeq (henv : env.WF) {F P D : VExpr} {g : Nat → Nat → Bool}
    (h : env.ReflectsCondApp F P D g) {u v : VExpr} (a b : Nat)
    (hu : env.IsDefEqU 0 [] u (.natLit a)) (hv : env.IsDefEqU 0 [] v (.natLit b))
    (t e : VExpr)
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F (VExpr.app2' P u v) (VExpr.app2' D u v) t e)) :
    env.IsDefEqU 0 [] (VExpr.condApp F (VExpr.app2' P u v) (VExpr.app2' D u v) t e)
      (bif g a b then t else e) := by
  have hc := IsDefEqU.condApp_congr_cond henv hwt
    (IsDefEqU.app2_congr_args henv (hwt.condApp_cond henv) hu hv)
  have hi := IsDefEqU.condApp_congr_inst henv hc.wf_r
    (IsDefEqU.app2_congr_args henv (hc.wf_r.condApp_inst henv) hu hv)
  exact IsDefEqU.trans henv trivial hc
    (IsDefEqU.trans henv trivial hi (h a b t e hi.wf_r))

/-- **A conditional with a single boolean scrutinee**: `Condition.bool`, which `Nat.bitwise`'s
equation uses three times.  There is no `Reflection` layer here -- the recognizer's `.bool`
branch checks the two selections directly. -/
def ReflectsCondApp1 (env : VEnv) (F P D : VExpr) : Prop :=
  ∀ (v : Bool) (t e : VExpr),
    VExpr.WF env 0 [] (VExpr.condApp F (P.app (.boolLit v)) (D.app (.boolLit v)) t e) →
    env.IsDefEqU 0 [] (VExpr.condApp F (P.app (.boolLit v)) (D.app (.boolLit v)) t e)
      (bif v then t else e)

/-- `ReflectsCondApp1` at a scrutinee that merely reflects a boolean literal. -/
theorem ReflectsCondApp1.ofDefeq (henv : env.WF) {F P D : VExpr}
    (h : env.ReflectsCondApp1 F P D) {u : VExpr} (v : Bool)
    (hu : env.IsDefEqU 0 [] u (.boolLit v)) (t e : VExpr)
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F (P.app u) (D.app u) t e)) :
    env.IsDefEqU 0 [] (VExpr.condApp F (P.app u) (D.app u) t e) (bif v then t else e) := by
  have hc := IsDefEqU.condApp_congr_cond henv hwt
    (IsDefEqU.app_congr_arg' henv (hwt.condApp_cond henv) hu)
  have hi := IsDefEqU.condApp_congr_inst henv hc.wf_r
    (IsDefEqU.app_congr_arg' henv (hc.wf_r.condApp_inst henv) hu)
  exact IsDefEqU.trans henv trivial hc
    (IsDefEqU.trans henv trivial hi (h v t e hi.wf_r))

end VEnv

/-! ### The `Nat.bitwise` recursion -/

/-- The `Bool` the recognizer's `Condition.natEq.decide #[Nat.mod n 2, 1]` builds. -/
def VExpr.bitParity (Ib Pe De : VExpr) (a : Nat) : VExpr :=
  VExpr.condApp Ib
    (VExpr.app2' Pe (VExpr.natOp ``Nat.mod (.natLit a) (.natLit 2)) (.natLit 1))
    (VExpr.app2' De (VExpr.natOp ``Nat.mod (.natLit a) (.natLit 2)) (.natLit 1))
    .boolTrue .boolFalse

/-- The recursive call the equation makes: `BW (Nat.div a 2) (Nat.div b 2)`. -/
def VExpr.bitwiseRec (BW : VExpr) (a b : Nat) : VExpr :=
  VExpr.app2' BW (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
    (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2))

/-- **The right-hand side the `Nat.bitwise` branch checks**, at a pair of numerals.  `In` and
`Ib` are `@ite.{1}` applied to `Nat` and to `Bool`; `Pe`/`De` are `Condition.natEq`'s
proposition and instance, `Pb`/`Db` are `Condition.bool`'s. -/
def VExpr.bitwiseRhs (In Ib Pe De Pb Db BW f : VExpr) (a b : Nat) : VExpr :=
  let r := VExpr.bitwiseRec BW a b
  let sel (c t e : VExpr) := VExpr.condApp In (Pb.app c) (Db.app c) t e
  VExpr.condApp In (VExpr.app2' Pe (.natLit a) (.natLit 0))
      (VExpr.app2' De (.natLit a) (.natLit 0))
    (sel (VExpr.app2' f .boolFalse .boolTrue) (.natLit b) (.natLit 0))
    (VExpr.condApp In (VExpr.app2' Pe (.natLit b) (.natLit 0))
        (VExpr.app2' De (.natLit b) (.natLit 0))
      (sel (VExpr.app2' f .boolTrue .boolFalse) (.natLit a) (.natLit 0))
      (sel (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b))
        (VExpr.natOp ``Nat.add (VExpr.natOp ``Nat.add r r) (.natLit 1))
        (VExpr.natOp ``Nat.add r r)))

namespace VEnv
variable {env : VEnv}

theorem reflects_natOp (henv : env.WF) {n : Name} {op : Nat → Nat → Nat}
    (h : env.ReflectsNatNatNat n op) (hc : env.contains n) {u v : VExpr} {a b : Nat}
    (hwt : VExpr.WF env 0 [] (VExpr.natOp n u v))
    (hu : env.IsDefEqU 0 [] u (.natLit a)) (hv : env.IsDefEqU 0 [] v (.natLit b)) :
    env.IsDefEqU 0 [] (VExpr.natOp n u v) (.natLit (op a b)) :=
  IsDefEqU.trans henv trivial (IsDefEqU.app2_congr_args henv hwt hu hv) (h hc a b)

theorem bif_boolLit (v : Bool) :
    (bif v then VExpr.boolTrue else VExpr.boolFalse) = .boolLit v := by cases v <;> rfl

theorem natBeq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  induction a generalizing b with
  | zero => cases b <;> simp [Nat.beq]
  | succ n ih => cases b <;> simp [Nat.beq, ih]

/-- The parity bit the equation computes: `Condition.natEq.decide #[Nat.mod a 2, 1]` reflects
`decide (a % 2 = 1)`. -/
theorem reflects_bitParity (henv : env.WF) (hlit : env.NatLits)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod) (hmodC : env.contains ``Nat.mod)
    {Ib Pe De : VExpr}
    (hcEb : env.ReflectsCondApp Ib Pe De Nat.beq) (x : Nat)
    (hwt : VExpr.WF env 0 [] (VExpr.bitParity Ib Pe De x)) :
    env.IsDefEqU 0 [] (VExpr.bitParity Ib Pe De x) (.boolLit (decide (x % 2 = 1))) := by
  have h := ReflectsCondApp.ofDefeq henv hcEb (x % 2) 1
    (hmod hmodC x 2) (IsDefEqU.refl ⟨_, hlit 1⟩) _ _ hwt
  rwa [natBeq_eq_decide, bif_boolLit] at h

/-- **`Nat.bitwise`'s recursion.**  `BW` is the checker's `Nat.bitwise` applied to the
combinator `f`; `heq` is the single equation the branch checks, instantiated at numerals. -/
theorem reflects_natBitwise_go (henv : env.WF) (hlit : env.NatLits)
    (hadd : env.ReflectsNatNatNat ``Nat.add Nat.add) (haddC : env.contains ``Nat.add)
    (hdiv : env.ReflectsNatNatNat ``Nat.div Nat.div) (hdivC : env.contains ``Nat.div)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod) (hmodC : env.contains ``Nat.mod)
    {In Ib Pe De Pb Db BW f : VExpr} {g : Bool → Bool → Bool}
    (hf : env.ReflectsBoolBoolBool f g)
    (hcE : env.ReflectsCondApp In Pe De Nat.beq)
    (hcEb : env.ReflectsCondApp Ib Pe De Nat.beq)
    (hcB : env.ReflectsCondApp1 In Pb Db)
    (heq : ∀ a b : Nat, env.IsDefEqU 0 [] (VExpr.app2' BW (.natLit a) (.natLit b))
      (VExpr.bitwiseRhs In Ib Pe De Pb Db BW f a b)) :
    ∀ a b : Nat, env.IsDefEqU 0 [] (VExpr.app2' BW (.natLit a) (.natLit b))
      (.natLit (Nat.bitwise g a b)) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro b
  refine IsDefEqU.trans henv trivial (heq a b) ?_
  have hw := (heq a b).wf_r
  -- the outer conditional, on `a = 0`
  have o1 := hcE a 0 _ _ hw
  rw [natBeq_eq_decide] at o1
  by_cases ha : a = 0
  · subst ha
    simp only [decide_true, cond_true] at o1
    refine IsDefEqU.trans henv trivial o1 ?_
    have hs := ReflectsCondApp1.ofDefeq henv hcB (g false true) (hf.2 false true) _ _ o1.wf_r
    refine IsDefEqU.trans henv trivial hs ?_
    rw [Nat.bitwise]
    cases hgb : g false true
    · rw [hgb] at hs
      simp only [cond_false, Bool.false_eq_true, if_false, reduceIte]
      exact IsDefEqU.refl hs.wf_r
    · rw [hgb] at hs
      simp only [cond_true, reduceIte]
      exact IsDefEqU.refl hs.wf_r
  · simp only [decide_eq_false ha, cond_false] at o1
    refine IsDefEqU.trans henv trivial o1 ?_
    have o2 := hcE b 0 _ _ o1.wf_r
    rw [natBeq_eq_decide] at o2
    by_cases hb : b = 0
    · subst hb
      simp only [decide_true, cond_true] at o2
      refine IsDefEqU.trans henv trivial o2 ?_
      have hs := ReflectsCondApp1.ofDefeq henv hcB (g true false) (hf.2 true false) _ _ o2.wf_r
      refine IsDefEqU.trans henv trivial hs ?_
      rw [Nat.bitwise]
      cases hgb : g true false
      · rw [hgb] at hs
        simp only [cond_false, if_neg ha, reduceIte]
        exact IsDefEqU.refl hs.wf_r
      · rw [hgb] at hs
        simp only [cond_true, if_neg ha, reduceIte]
        exact IsDefEqU.refl hs.wf_r
    · simp only [decide_eq_false hb, cond_false] at o2
      refine IsDefEqU.trans henv trivial o2 ?_
      have hsel := o2.wf_r
      -- the parity bits reflect
      have hcond := hsel.condApp_cond henv
      have hfab : VExpr.WF env 0 []
          (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b)) :=
        hcond.app_arg' henv
      have hp1 := reflects_bitParity henv hlit hmod hmodC hcEb a (hfab.app2_arg1 henv)
      have hp2 := reflects_bitParity henv hlit hmod hmodC hcEb b (hfab.app2_arg2 henv)
      have hfb : env.IsDefEqU 0 []
          (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b))
          (.boolLit (g (decide (a % 2 = 1)) (decide (b % 2 = 1)))) :=
        IsDefEqU.trans henv trivial (IsDefEqU.app2_congr_args henv hfab hp1 hp2)
          (hf.2 _ _)
      -- the recursive call reflects
      have hrw : VExpr.WF env 0 [] (VExpr.natOp ``Nat.add
          (VExpr.natOp ``Nat.add (VExpr.bitwiseRec BW a b) (VExpr.bitwiseRec BW a b))
          (.natLit 1)) := hsel.condApp_t henv
      have hrr := hrw.app2_arg1 henv
      have hr := hrr.app2_arg1 henv
      have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
      have hrec : env.IsDefEqU 0 [] (VExpr.bitwiseRec BW a b)
          (.natLit (Nat.bitwise g (a / 2) (b / 2))) :=
        IsDefEqU.trans henv trivial
          (IsDefEqU.app2_congr_args henv hr (hdiv hdivC a 2) (hdiv hdivC b 2))
          (ih (a / 2) hlt (b / 2))
      have hsum : env.IsDefEqU 0 []
          (VExpr.natOp ``Nat.add (VExpr.bitwiseRec BW a b) (VExpr.bitwiseRec BW a b))
          (.natLit (Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2))) :=
        reflects_natOp henv hadd haddC hrr hrec hrec
      have hsum1 : env.IsDefEqU 0 []
          (VExpr.natOp ``Nat.add
            (VExpr.natOp ``Nat.add (VExpr.bitwiseRec BW a b) (VExpr.bitwiseRec BW a b))
            (.natLit 1))
          (.natLit (Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2) + 1)) :=
        reflects_natOp henv hadd haddC hrw hsum (IsDefEqU.refl ⟨_, hlit 1⟩)
      have hs := ReflectsCondApp1.ofDefeq henv hcB _ hfb _ _ hsel
      refine IsDefEqU.trans henv trivial hs ?_
      have hbw : Nat.bitwise g a b =
          (if g (decide (a % 2 = 1)) (decide (b % 2 = 1)) then
            Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2) + 1
          else Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2)) := by
        conv =>
          lhs
          rw [Nat.bitwise]
        simp only [if_neg ha, if_neg hb]
      rw [hbw]
      cases hgb : g (decide (a % 2 = 1)) (decide (b % 2 = 1))
      · simp only [hgb, cond_false, Bool.false_eq_true, if_false, reduceIte]
        exact hsum
      · simp only [hgb, cond_true, if_true, reduceIte]
        exact hsum1

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
  fun h env₂ hle₂ f g henv₂ hg a b =>
    H (contains_of_constants_eq hc h) env₂ (hle.trans hle₂) f g henv₂ hg a b

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

/-- One step of an application spine at an **arbitrary** domain.  `trExprS_app1` is its
`A = Nat` specialisation; the dependent telescopes of `Nat.modCore.go` / `Nat.div.go`
(`∀ b, 1 ≤ b → ∀ fuel x, x + 1 ≤ fuel → Nat`) need the general form, since neither the domains
nor the codomains after instantiation are constants. -/
theorem trExprS_appD {F a' A B : VExpr} {value a : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE A B))
    (ha : c.TrExprS a a') (haty : c.HasType a' A) :
    c.TrExprS (.app value a) (.app F a') ∧ c.HasType (.app F a') (B.inst a') :=
  ⟨.app hFty haty hF ha, hFty.app haty⟩

/-- **The length-5 application spine**, at a fully general dependent telescope.  This is the
tool `docs/handoff-primitive.md` §6.1 names as the one thing missing from the `Nat.mod` /
`Nat.div` branches: their `go` is `Nat.modCore.go` / `Nat.div.go` applied to five arguments,
of which the second and fifth are *proofs* whose types mention the earlier arguments, so no
`Nat`-domain lemma applies.

Each `eᵢ` is the caller's obligation to compute one instantiation of the telescope; at the
shapes the branches use these are `rfl` or a `simp` away, because the abstract counterparts of
`1 ≤ b` and `x + 1 ≤ fuel` are applications of a closed `P` to closed numerals and to the
bound variables already substituted.  The final `R` is the result type (`Nat` for both
branches). -/
theorem trExprS_app5 {F a₁' a₂' a₃' a₄' a₅' A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ R : VExpr}
    {value a₁ a₂ a₃ a₄ a₅ : Expr}
    (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE A₁ B₁))
    (h₁ : c.TrExprS a₁ a₁') (t₁ : c.HasType a₁' A₁) (e₁ : B₁.inst a₁' = .forallE A₂ B₂)
    (h₂ : c.TrExprS a₂ a₂') (t₂ : c.HasType a₂' A₂) (e₂ : B₂.inst a₂' = .forallE A₃ B₃)
    (h₃ : c.TrExprS a₃ a₃') (t₃ : c.HasType a₃' A₃) (e₃ : B₃.inst a₃' = .forallE A₄ B₄)
    (h₄ : c.TrExprS a₄ a₄') (t₄ : c.HasType a₄' A₄) (e₄ : B₄.inst a₄' = .forallE A₅ B₅)
    (h₅ : c.TrExprS a₅ a₅') (t₅ : c.HasType a₅' A₅) (e₅ : B₅.inst a₅' = R) :
    c.TrExprS (mkApp5 value a₁ a₂ a₃ a₄ a₅) (VExpr.app5 F a₁' a₂' a₃' a₄' a₅') ∧
      c.HasType (VExpr.app5 F a₁' a₂' a₃' a₄' a₅') R := by
  obtain ⟨s₁, y₁⟩ := trExprS_appD hF hFty h₁ t₁; rw [e₁] at y₁
  obtain ⟨s₂, y₂⟩ := trExprS_appD s₁ y₁ h₂ t₂; rw [e₂] at y₂
  obtain ⟨s₃, y₃⟩ := trExprS_appD s₂ y₂ h₃ t₃; rw [e₃] at y₃
  obtain ⟨s₄, y₄⟩ := trExprS_appD s₃ y₃ h₄ t₄; rw [e₄] at y₄
  obtain ⟨s₅, y₅⟩ := trExprS_appD s₄ y₄ h₅ t₅; rw [e₅] at y₅
  exact ⟨s₅, y₅⟩

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

/-- `Bool → Bool → Bool`: the type the `Nat.land` / `Nat.lor` / `Nat.xor` branches pin on the
combinator they hand to `Nat.bitwise`.  `VEnv.ReflectsBoolBoolBool` needs it -- see the
`Nat.bitwise` section note above. -/
theorem trExprS_boolArrow2_inv {nm₁ nm₂ bi₁ bi₂ e'}
    (h : c.TrExprS (.forallE nm₁ (.const ``Bool [])
      (.forallE nm₂ (.const ``Bool []) (.const ``Bool []) bi₂) bi₁) e') :
    e' = .forallE .bool (.forallE .bool .bool) := by
  obtain ⟨_, _, rfl, h1, _, h3⟩ := trExprS_arrow_inv h
  cases trExprS_const_nil_inv h1
  obtain ⟨_, _, rfl, h4, _, h5⟩ := trExprS_arrow_inv h3
  cases trExprS_const_nil_inv h4; cases trExprS_const_nil_inv h5; rfl

/-- `checkedTypeIs` when the caller already holds both translations: on success it delivers the
typing *at those translations*, rather than at the ones `checkType` happened to build.  The two
are identified by `trExprS_uniq`, and the resulting conversions are absorbed by
`HasType.defeqU_l` / `.defeqU_r`. -/
theorem checkedTypeIs.WF' {s : VState} {e ty : Expr} {e' : VExpr}
    (he : c.TrExprS e e') (hty : ty.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (Lean4Lean.Environment.checkedTypeIs e ty) fun r _ =>
      ∃ ty', c.TrExprS ty ty' ∧ (r = true → c.HasType e' ty') := by
  refine (checkedTypeIs.WF he.fvarsIn hty).mono fun _ _ _ h => ?_
  obtain ⟨e₁, A', ty₁, he₁, hA₁, hty₁, hdd⟩ := h
  refine ⟨ty₁, hty₁, fun hr => ?_⟩
  exact (hA₁.defeqU_r c.Ewf c.Δwf.toCtx (hdd hr)).defeqU_l c.Ewf c.Δwf.toCtx
    (trExprS_uniq he₁ he)

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

/-! ### The `Nat.mod` / `Nat.div` fuel telescope

`Nat.modCore.go` and `Nat.div.go` are checked against
`∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat`.  The two `≤`
occurrences sit at binder depths 1 and 4, but `@LE.le Nat instLENat` is a closed term built from
constants, so its translation is `VExpr.natLE` at *every* context.  The inversion is therefore a
plain iterated `trExprS_arrow_inv'`, with no weakening of the base-context `checkedTypeIs`
output and no appeal to `TrExprS.unique`. -/

/-- The bound variable a `vlam` has just introduced. -/
theorem trExprS_bvar0_inv' {env : VEnv} {Us Δ} {A : VExpr} {e' : VExpr}
    (h : TrExprS env Us ((none, .vlam A) :: Δ) (.bvar 0) e') : e' = .bvar 0 := by
  let .bvar h1 := h
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value] at h1
  exact h1.1.symm

/-- The bound variable one `vlam` further out. -/
theorem trExprS_bvar1_inv' {env : VEnv} {Us Δ} {A B : VExpr} {e' : VExpr}
    (h : TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: Δ) (.bvar 1) e') :
    e' = .bvar 1 := by
  let .bvar h1 := h
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.depth, VExpr.liftN] at h1
  exact h1.1.symm

/-- `@LE.le Nat instLENat` translates to `VExpr.natLE`, at any context. -/
theorem trExprS_natLE_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (.app (.app (.const ``LE.le [.zero]) (.const ``Nat []))
      (.const ``instLENat [])) e') : e' = .natLE := by
  let .app _ _ g3 g4 := h
  cases trExprS_const_nil_inv' g4
  let .app _ _ f3 f4 := g3
  cases trExprS_const_nil_inv' f4
  cases trExprS_const_zero_inv' f3
  rfl

/-- `a ≤ b` at `Nat`. -/
theorem trExprS_natLEApp_inv' {env : VEnv} {Us Δ} {a b : Expr} {e' : VExpr}
    (h : TrExprS env Us Δ (.app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``Nat []))
      (.const ``instLENat [])) a) b) e') :
    ∃ a' b', e' = .natLEApp a' b' ∧
      TrExprS env Us Δ a a' ∧ TrExprS env Us Δ b b' := by
  let .app _ _ g3 g4 := h
  let .app _ _ f3 f4 := g3
  cases trExprS_natLE_inv' f3
  exact ⟨_, _, rfl, f4, g4⟩

/-- `Nat.succ Nat.zero` translates to `VExpr.natLit 1`. -/
theorem trExprS_one_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (.app (.const ``Nat.succ []) (.const ``Nat.zero [])) e') :
    e' = .natLit 1 := by
  let .app _ _ g3 g4 := h
  cases trExprS_const_nil_inv' g3
  cases trExprS_const_nil_inv' g4
  rfl

/-- `Nat → Nat → Prop`, the type the recognizer checks `@LE.le Nat _` against. -/
theorem trExprS_natArrowProp_inv' {env : VEnv} {Us Δ} {nm₁ nm₂ bi₁ bi₂} {e' : VExpr}
    (h : TrExprS env Us Δ (.forallE nm₁ (.const ``Nat [])
      (.forallE nm₂ (.const ``Nat []) (.sort .zero) bi₂) bi₁) e') :
    e' = .forallE .nat (.forallE .nat (.sort .zero)) := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g3⟩ := trExprS_arrow_inv' h3
  cases trExprS_const_nil_inv' g1
  let .sort hs := g3
  simp [VLevel.ofLevel] at hs
  rw [← hs]; rfl

/-- The telescope inversion the `Nat.mod` and `Nat.div` branches need: the type
`Nat.modCore.go` / `Nat.div.go` is checked against determines its translation on the nose. -/
theorem trExprS_goType_inv' {env : VEnv} {Us Δ} {n₁ n₂ n₃ n₄ n₅ bi₁ bi₂ bi₃ bi₄ bi₅}
    {e' : VExpr}
    (h : TrExprS env Us Δ
      (.forallE n₁ (.const ``Nat [])
        (.forallE n₂ (.app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``Nat []))
            (.const ``instLENat [])) (.app (.const ``Nat.succ []) (.const ``Nat.zero [])))
          (.bvar 0))
          (.forallE n₃ (.const ``Nat [])
            (.forallE n₄ (.const ``Nat [])
              (.forallE n₅ (.app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``Nat []))
                  (.const ``instLENat [])) (.app (.const ``Nat.succ []) (.bvar 0))) (.bvar 1))
                (.const ``Nat []) bi₅) bi₄) bi₃) bi₂) bi₁) e') :
    e' = .goType := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_arrow_inv' h2
  obtain ⟨_, _, rfl, ga, gb⟩ := trExprS_natLEApp_inv' g1
  cases trExprS_one_inv' ga
  cases trExprS_bvar0_inv' gb
  obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_arrow_inv' g2
  cases trExprS_const_nil_inv' k1
  obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_arrow_inv' k2
  cases trExprS_const_nil_inv' m1
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_arrow_inv' m2
  obtain ⟨_, _, rfl, pa, pb⟩ := trExprS_natLEApp_inv' p1
  let .app _ _ pa1 pa2 := pa
  cases trExprS_const_nil_inv' pa1
  cases trExprS_bvar0_inv' pa2
  cases trExprS_bvar1_inv' pb
  cases trExprS_const_nil_inv' p2
  rfl

/-- Every explicit universe level a recognizer term carries is a closed `Level`, so a `.const`
inversion needs no more than the level translation the caller can compute.  This subsumes
`trExprS_const_nil_inv'` and `trExprS_const_zero_inv'`. -/
theorem trExprS_const_inv' {env : VEnv} {Us Δ} {n : Name} {us : List Level} {us' : List VLevel}
    {e' : VExpr} (h : TrExprS env Us Δ (.const n us) e')
    (hus : us.mapM (VLevel.ofLevel Us) = some us') : e' = .const n us' := by
  let .const _ h2 _ := h
  rw [hus] at h2; cases h2; rfl

/-- `Prop`. -/
theorem trExprS_prop_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (.sort .zero) e') : e' = .sort .zero := by
  let .sort hs := h
  simp [VLevel.ofLevel] at hs
  rw [← hs]

/-- `Prop → Bool → Prop`, the type a `Reflection`'s `type` field is checked against. -/
theorem trExprS_propBoolProp_inv' {env : VEnv} {Us Δ} {nm₁ nm₂ bi₁ bi₂} {e' : VExpr}
    (h : TrExprS env Us Δ (.forallE nm₁ (.sort .zero)
      (.forallE nm₂ (.const ``Bool []) (.sort .zero) bi₂) bi₁) e') :
    e' = .forallE (.sort .zero) (.forallE .bool (.sort .zero)) := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_prop_inv' h1
  obtain ⟨_, _, rfl, g1, g3⟩ := trExprS_arrow_inv' h3
  cases trExprS_const_nil_inv' g1
  cases trExprS_prop_inv' g3
  rfl

/-- **The reflection proof, read at a pair of numerals.**  `Condition.check` pins `proof`'s
type at the base context (see `Lean4Lean/Primitive.lean`), and this is the only use the
verification makes of that check: it is `VEnv.reflects_condApp`'s `hPR`, the one hypothesis of
`hsel` that no amount of inversion can recover -- `TrExprS.app` hands back the *existential*
domain the application invented, and pinning it needs `toDec`'s declared telescope, which
nothing checks. -/
theorem VEnv.reflProof_inst {env : VEnv} (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    {PR RT P B : VExpr} (hRTc : RT.ClosedN 0) (hPc : P.ClosedN 0) (hBc : B.ClosedN 0)
    (h : env.HasType 0 [] PR (.forallE .nat (.forallE .nat
      (.app (.app RT (.app (.app P (.bvar 1)) (.bvar 0))) (.app (.app B (.bvar 1)) (.bvar 0))))))
    (a b : Nat) :
    env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) := by
  have hcl : ∀ {u : VExpr} {w : VExpr} {j}, u.ClosedN 0 → u.inst w j = u :=
    fun hu => hu.instN_eq (Nat.zero_le _)
  have hla : ∀ {n j}, (VExpr.natLit n).liftN j = VExpr.natLit n :=
    fun {n _} => (VExpr.closedN_natLit n).liftN_eq (Nat.zero_le _)
  have h1 := h.app (hprim.natLit_hasType hnat (Γ := ([] : List VExpr)) a)
  simp only [VExpr.inst, VExpr.nat, hcl hRTc, hcl hPc, hcl hBc,
    VExpr.instVar_zero, VExpr.instVar_lower, VExpr.instVar_succ, hla] at h1
  have h2 := h1.app (hprim.natLit_hasType hnat (Γ := ([] : List VExpr)) b)
  simpa only [VExpr.inst, VExpr.nat, hcl hRTc, hcl hPc, hcl hBc, hcl (VExpr.closedN_natLit a),
    VExpr.instVar_zero, VExpr.instVar_lower, VExpr.instVar_succ, hla] using h2

/-- **A closed term's translation does not move under a bound-variable binder.**

Every `_inv'` lemma above inverts a *constant-only* term, whose translation is
context-independent for a structural reason.  This is the general fact, and it is what lets the
recognizer's abstract sub-terms (`Reflection.type`, `Condition.prop`, a `Condition`'s `asBool`)
be recognised inside a `∀ n m : Nat, …` type, whose translation is built under two `.vlam`
entries. -/
theorem trExprS_weakBV0 {env : VEnv} {Us} {Δ : VLCtx} {A : VExpr} {e : Expr} {e' : VExpr}
    (henv : env.Ordered) (h : TrExprS env Us Δ e e')
    (hb : e.looseBVarRange' = 0) (hc : e'.ClosedN 0) :
    TrExprS env Us ((none, .vlam A) :: Δ) e e' := by
  have := h.weakBV henv (Δ' := (none, .vlam A) :: Δ) (.skip (.vlam A) .refl)
  rwa [Expr.liftLooseBVars_eq_self (by simp [hb]), hc.liftN_eq (Nat.zero_le _)] at this

/-- **The type `Condition.check` pins the reflection proof against**:
`∀ n m : Nat, r.type (cond.prop n m) (asBool n m)`.

The three abstract sub-terms are identified with their base-context translations by
`trExprS_weakBV0` (they are closed) plus `TrExprS.unique` (they are `IsUnique`); the two bound
variables are pinned outright, because `TrExprS.bvar` reads a deterministic `VLCtx.find?`. -/
theorem trExprS_reflProofType_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {rty prp asB : Expr} {RT P B : VExpr} {n₁ n₂ bi₁ bi₂} {e' : VExpr} (henv : env.Ordered)
    (hRT : TrExprS env Us Δ rty RT) (hRTu : TrExprS.IsUnique rty)
    (hRTb : rty.looseBVarRange' = 0) (hRTc : RT.ClosedN 0)
    (hP : TrExprS env Us Δ prp P) (hPu : TrExprS.IsUnique prp)
    (hPb : prp.looseBVarRange' = 0) (hPc : P.ClosedN 0)
    (hB : TrExprS env Us Δ asB B) (hBu : TrExprS.IsUnique asB)
    (hBb : asB.looseBVarRange' = 0) (hBc : B.ClosedN 0)
    (h : TrExprS env Us Δ
      (.forallE n₁ (.const ``Nat []) (.forallE n₂ (.const ``Nat [])
        (mkApp2 rty (mkApp2 prp (.bvar 1) (.bvar 0)) (mkApp2 asB (.bvar 1) (.bvar 0))) bi₂) bi₁)
      e') :
    e' = .forallE .nat (.forallE .nat
      (.app (.app RT (.app (.app P (.bvar 1)) (.bvar 0))) (.app (.app B (.bvar 1)) (.bvar 0)))) := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_arrow_inv' h2
  cases trExprS_const_nil_inv' g1
  -- the two `.vlam .nat` entries the two `∀ n m : Nat` binders introduce
  have wk : ∀ {u : Expr} {u' : VExpr}, TrExprS env Us Δ u u' → u.looseBVarRange' = 0 →
      u'.ClosedN 0 →
      TrExprS env Us ((none, .vlam .nat) :: (none, .vlam .nat) :: Δ) u u' := fun hu hb hc =>
    trExprS_weakBV0 henv (trExprS_weakBV0 henv hu hb hc) hb hc
  let .app _ _ a3 a4 := g2
  let .app _ _ b3 b4 := a3
  cases TrExprS.unique hRTu b3 (wk hRT hRTb hRTc)
  let .app _ _ c3 c4 := b4
  let .app _ _ d3 d4 := c3
  cases TrExprS.unique hPu d3 (wk hP hPb hPc)
  cases trExprS_bvar1_inv' d4
  cases trExprS_bvar0_inv' c4
  let .app _ _ e3 e4 := a4
  let .app _ _ f3 f4 := e3
  cases TrExprS.unique hBu f3 (wk hB hBb hBc)
  cases trExprS_bvar1_inv' f4
  cases trExprS_bvar0_inv' e4
  rfl

namespace TypeChecker

variable {c : VContext}

/-- What `Reflection.check` establishes: the reflection predicate has a translation, and that
translation is a `Prop → Bool → Prop`.

This is the first of the facts `Condition.check` produces and the only one of them that is a
single check; the rest (`Reflection.checkITE`, `Reflection.checkNatDITE`, and the four
comparisons `Condition.check` makes itself) are still open.  See `docs/handoff-primitive.md`. -/
theorem Reflection.check.WF {s : VState} {r : Lean4Lean.Environment.Reflection}
    {fail : ∀ {α}, TypeChecker.M α}
    (hfail : ∀ {α : Type} {s' : VState} {Q : α → VState → Prop}, M.WF c s' fail Q)
    (hty : r.type.FVarsIn (· ∈ c.vlctx.fvars))
    (htd : r.toDec.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (r.check fail) fun _ _ =>
      (∃ RT, c.TrExprS r.type RT ∧
        c.HasType RT (.forallE (.sort .zero) (.forallE .bool (.sort .zero)))) ∧
      ∃ TD TDA, c.TrExprS r.toDec TD ∧ c.HasType TD TDA := by
  unfold Lean4Lean.Environment.Reflection.check
  refine M.WF.bind (checkedTypeIs.WF hty (by simp [FVarsIn] <;> rfl)) fun _ _ _ h => ?_
  obtain ⟨RT, A', ty', hRT, hA', hty', hd⟩ := h
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hb
  cases trExprS_propBoolProp_inv' hty'
  refine M.WF.bind (checkType.WF htd) fun _ _ _ h2 => ?_
  obtain ⟨TD, TDA, -, hTD, -, hTDA⟩ := h2
  exact .pure ⟨⟨RT, hRT, hA'.defeqU_r c.Ewf c.Δwf.toCtx (hd (by simpa using hb))⟩,
    TD, TDA, hTD, hTDA⟩

end TypeChecker

/-! ## `Reflection.checkITE`

The recognizer checks, per result type `α`:

* `@ite.{1} α : ∀ (c : Prop), Decidable c → α → α → α` -- the conditional head's declared
  Pi-type, **already applied to the result type**, which is the form `VEnv.condApp_typed`
  consumes;
* under `p : Prop`, `H : r.type p b`, `t e : α`, the two selection equations
  `@ite.{1} α p (r.toDec p b H) t e ≡ t` (for `b = true`) and `≡ e` (for `b = false`).

`Reflection.checkITE.WF` below reads both back, and its second output is *exactly*
`VEnv.hsel_of_checkITE`'s hypothesis -- the acceptance test of §1.2 of
`docs/handoff-primitive.md`, now with a supplier. -/

/-- **The conditional head's declared type, at one result type.**

`α` is an arbitrary `Expr` (an element of `Condition.check`'s `iteTypes`), so its two occurrences
under the `c` and `Decidable c` binders are identified with the base-context translation by
`trExprS_weakBV0` (it is closed) plus `TrExprS.unique` (it is `IsUnique`) -- the same device as
`trExprS_reflProofType_inv'`. -/
theorem trExprS_iteHeadType_inv' {env : VEnv} {Us} {Δ : VLCtx} {α : Expr} {Aα : VExpr}
    {n₁ n₂ n₃ n₄ bi₁ bi₂ bi₃ bi₄} {e' : VExpr} (henv : env.Ordered)
    (hA : TrExprS env Us Δ α Aα) (hAu : TrExprS.IsUnique α)
    (hAb : α.looseBVarRange' = 0) (hAc : Aα.ClosedN 0)
    (h : TrExprS env Us Δ (.forallE n₁ (.sort .zero)
      (.forallE n₂ (.app (.const ``Decidable []) (.bvar 0))
        (.forallE n₃ α (.forallE n₄ α α bi₄) bi₃) bi₂) bi₁) e') :
    e' = .forallE (.sort .zero) (.forallE (.app (.const ``Decidable []) (.bvar 0))
      (.forallE Aα (.forallE Aα Aα))) := by
  have wk1 : ∀ {A : VExpr}, TrExprS env Us ((none, .vlam A) :: Δ) α Aα := fun {_} =>
    trExprS_weakBV0 henv hA hAb hAc
  have wk2 : ∀ {A B : VExpr},
      TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: Δ) α Aα := fun {_ _} =>
    trExprS_weakBV0 henv wk1 hAb hAc
  have wk3 : ∀ {A B C : VExpr},
      TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: (none, .vlam C) :: Δ) α Aα :=
    fun {_ _ _} => trExprS_weakBV0 henv wk2 hAb hAc
  have wk4 : ∀ {A B C D : VExpr}, TrExprS env Us
      ((none, .vlam A) :: (none, .vlam B) :: (none, .vlam C) :: (none, .vlam D) :: Δ) α Aα :=
    fun {_ _ _ _} => trExprS_weakBV0 henv wk3 hAb hAc
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  cases trExprS_prop_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_arrow_inv' h2
  let .app _ _ d1 d2 := g1
  cases trExprS_const_nil_inv' d1
  cases trExprS_bvar0_inv' d2
  obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_arrow_inv' g2
  cases TrExprS.unique hAu k1 wk2
  obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_arrow_inv' k2
  cases TrExprS.unique hAu m1 wk3
  cases TrExprS.unique hAu m2 wk4
  rfl

/-- Inversion for an application, in the `_inv'` family's raw form. -/
theorem trExprS_app_inv' {env : VEnv} {Us Δ} {f a : Lean.Expr} {e' : VExpr}
    (h : TrExprS env Us Δ (.app f a) e') :
    ∃ f' a', e' = .app f' a' ∧ TrExprS env Us Δ f f' ∧ TrExprS env Us Δ a a' :=
  let .app _ _ h3 h4 := h; ⟨_, _, rfl, h3, h4⟩


namespace TypeChecker

variable {c : VContext}

set_option maxHeartbeats 1000000 in
theorem Reflection.checkITEHalf.WF {s : VState}
    {r : Lean4Lean.Environment.Reflection} {α : Lean.Expr} {v : Bool} {bn : Name}
    {sel : Lean.Expr → Lean.Expr → Lean.Expr} {fail : ∀ {β}, TypeChecker.M β}
    {RT TD F Aα : VExpr}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hbn : ∀ {Δ : VLCtx} {X : VExpr},
      TrExprS c.venv c.lparams Δ (.const bn []) X → X = VExpr.boolLit v)
    (hsel : ∀ t e : Lean.Expr, sel t e = bif v then t else e)
    (hα : c.TrExprS α Aα) (hαu : TrExprS.IsUnique α) (hAc : Aα.ClosedN 0)
    (hRT : c.TrExprS r.type RT) (hRTu : TrExprS.IsUnique r.type) (hRTc : RT.ClosedN 0)
    (hTD : c.TrExprS r.toDec TD) (hTDu : TrExprS.IsUnique r.toDec) (hTDc : TD.ClosedN 0)
    (hF : c.TrExprS (mkApp (.const ``ite [.succ .zero]) α) F) (hFc : F.ClosedN 0) :
    M.WF c s (r.checkITEHalf α (.const bn []) sel fail) fun _ _ =>
      c.venv.IsDefEqU 0 [Aα, Aα, .app (.app RT (.bvar 0)) (VExpr.boolLit v), .sort .zero]
        (VExpr.condApp F (.bvar 3)
          (.app (.app (.app TD (.bvar 3)) (VExpr.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
        (bif v then .bvar 1 else .bvar 0) := by
  unfold Lean4Lean.Environment.Reflection.checkITEHalf
  refine M.WF.withCheckedLocalDecl (by exact rfl) fun PT idp cwfp s1 _ hPT _ => ?_
  cases trExprS_prop_inv' hPT
  have hα1 := TrExprS.weakLam0 cwfp hα hAc
  have hRT1 := TrExprS.weakLam0 cwfp hRT hRTc
  have hTD1 := TrExprS.weakLam0 cwfp hTD hTDc
  have hF1 := TrExprS.weakLam0 cwfp hF hFc
  have hp1 := trExprS_lastFVar0 cwfp
  refine M.WF.withCheckedLocalDecl
    (by exact ⟨⟨hRT1.fvarsIn, hp1.fvarsIn⟩, by simp [FVarsIn]⟩)
    fun HT idH cwfH s2 _ hHT _ => ?_
  -- pin the `H` binder's domain: `r.type p b` translates to `RT (bvar 0) (boolLit v)`
  obtain ⟨_, _, rfl, z3, z4⟩ := trExprS_app_inv' hHT
  cases hbn z4
  obtain ⟨_, _, rfl, y3, y4⟩ := trExprS_app_inv' z3
  cases TrExprS.unique hRTu y3 hRT1
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial y4 hp1
  have hα2 := TrExprS.weakLam0 cwfH hα1 hAc
  have hRT2 := TrExprS.weakLam0 cwfH hRT1 hRTc
  have hTD2 := TrExprS.weakLam0 cwfH hTD1 hTDc
  have hF2 := TrExprS.weakLam0 cwfH hF1 hFc
  refine M.WF.withCheckedLocalDecl (by exact hα2.fvarsIn) fun AT₁ idt cwft s3 _ hAT₁ _ => ?_
  cases TrExprS.unique hαu hAT₁ hα2
  have hα3 := TrExprS.weakLam0 cwft hα2 hAc
  have hRT3 := TrExprS.weakLam0 cwft hRT2 hRTc
  have hTD3 := TrExprS.weakLam0 cwft hTD2 hTDc
  have hF3 := TrExprS.weakLam0 cwft hF2 hFc
  refine M.WF.withCheckedLocalDecl (by exact hα3.fvarsIn) fun AT₂ ide cwfe s4 _ hAT₂ _ => ?_
  cases TrExprS.unique hαu hAT₂ hα3
  have hTD4 := TrExprS.weakLam0 cwfe hTD3 hTDc
  have hF4 := TrExprS.weakLam0 cwfe hF3 hFc
  have hp4 := TrExprS.weakLift0 cwfe (TrExprS.weakLift0 cwft
    (TrExprS.weakLift0 cwfH hp1))
  have hH4 := TrExprS.weakLift0 cwfe (TrExprS.weakLift0 cwft (trExprS_lastFVar0 cwfH))
  have ht4 := TrExprS.weakLift0 cwfe (trExprS_lastFVar0 cwft)
  have he4 := trExprS_lastFVar0 cwfe
  simp only [VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, show ¬ (0:Nat) < 0 by omega,
    if_false, Nat.reduceAdd, show ¬ (1:Nat) < 0 by omega, show ¬ (2:Nat) < 0 by omega] at hp4 hH4 ht4
  refine M.WF.bind (checkedIsDefEq.WFl (b' := bif v then .bvar 1 else .bvar 0)
    ⟨⟨⟨⟨hF4.fvarsIn, hp4.fvarsIn⟩,
        ⟨⟨⟨hTD4.fvarsIn, hp4.fvarsIn⟩, by simp [FVarsIn]⟩, hH4.fvarsIn⟩⟩,
      ht4.fvarsIn⟩, he4.fvarsIn⟩
    (by rw [hsel]; cases v; exacts [he4, ht4])) fun b _ _ hb => ?_
  obtain ⟨LHS, hLHS, hdd⟩ := hb
  split
  case isFalse => exact hfail
  rename_i hbt
  have hdefeq := hdd (by simpa using hbt)
  obtain ⟨_, _, rfl, n3, n4⟩ := trExprS_app_inv' hLHS
  cases TrExprS.unique (e := Lean.Expr.fvar ide) trivial n4 he4
  obtain ⟨_, _, rfl, m3, m4⟩ := trExprS_app_inv' n3
  cases TrExprS.unique (e := Lean.Expr.fvar idt) trivial m4 ht4
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' m3
  obtain ⟨_, _, rfl, j3, j4⟩ := trExprS_app_inv' k3
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial j4 hp4
  cases TrExprS.unique (e := Lean.mkApp (.const ``ite [.succ .zero]) α) ⟨trivial, hαu⟩ j3 hF4
  obtain ⟨_, _, rfl, g3, g4⟩ := trExprS_app_inv' k4
  cases TrExprS.unique (e := Lean.Expr.fvar idH) trivial g4 hH4
  obtain ⟨_, _, rfl, f3, f4⟩ := trExprS_app_inv' g3
  cases hbn f4
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' f3
  cases TrExprS.unique hTDu e3 hTD4
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial e4 hp4
  refine .pure ?_
  simpa [VContext.IsDefEqU, VContext.withMLC, VLCtx.toCtx, hlp, hnil, VExpr.condApp]
    using hdefeq

set_option maxHeartbeats 1000000 in
theorem Reflection.checkITE.WF {s : VState}
    {r : Lean4Lean.Environment.Reflection} {α : Lean.Expr} {fail : ∀ {β}, TypeChecker.M β}
    {RT TD RTA TDA : VExpr}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hαfv : α.FVarsIn (· ∈ c.vlctx.fvars)) (hαu : TrExprS.IsUnique α)
    (hαb : α.looseBVarRange' = 0)
    (hRT : c.TrExprS r.type RT) (hRTu : TrExprS.IsUnique r.type) (hRTty : c.HasType RT RTA)
    (hTD : c.TrExprS r.toDec TD) (hTDu : TrExprS.IsUnique r.toDec) (hTDty : c.HasType TD TDA) :
    M.WF c s (r.checkITE α fail) fun _ _ =>
      ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧ F.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧
        c.HasType F (.forallE (.sort .zero)
          (.forallE (.app (.const ``Decidable []) (.bvar 0)) (.forallE Aα (.forallE Aα Aα)))) ∧
        ∀ v : Bool, c.venv.IsDefEqU 0
          [Aα, Aα, .app (.app RT (.bvar 0)) (VExpr.boolLit v), .sort .zero]
          (VExpr.condApp F (.bvar 3)
            (.app (.app (.app TD (.bvar 3)) (VExpr.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
          (bif v then .bvar 1 else .bvar 0) := by
  unfold Lean4Lean.Environment.Reflection.checkITE
  refine (checkIsType.WF hαfv).bind fun _ _ _ h => ?_
  obtain ⟨Aα, hAα, u, hAu'⟩ := h
  have hAc := (closedN_of_nil hnil hAu').1
  have hRTc := (closedN_of_nil hnil hRTty).1
  have hTDc := (closedN_of_nil hnil hTDty).1
  refine M.WF.bind (checkedTypeIs.WF ⟨by simp [FVarsIn]; rfl, hαfv⟩
    ⟨by exact rfl, ⟨⟨by simp [FVarsIn], trivial⟩, ⟨hαfv, ⟨hαfv, hαfv⟩⟩⟩⟩) fun _ _ _ h => ?_
  obtain ⟨F, FA, FT, hF, hFA, hFT, hFd⟩ := h
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hb
  cases trExprS_iteHeadType_inv' c.Ewf.ordered hAα hαu hαb hAc hFT
  have hFty := hFA.defeqU_r c.Ewf c.Δwf.toCtx (hFd (by simpa using hb))
  have hFc := (closedN_of_nil hnil hFty).1
  refine M.WF.bind (Reflection.checkITEHalf.WF (v := true) (bn := ``Bool.true) hfail hnil hlp
      (fun h => trExprS_const_nil_inv' h) (fun _ _ => rfl)
      hAα hαu hAc hRT hRTu hRTc hTD hTDu hTDc hF hFc) fun _ _ _ htrue => ?_
  refine (Reflection.checkITEHalf.WF (v := false) (bn := ``Bool.false) hfail hnil hlp
      (fun h => trExprS_const_nil_inv' h) (fun _ _ => rfl)
      hAα hαu hAc hRT hRTu hRTc hTD hTDu hTDc hF hFc).mono fun _ _ _ hfalse => ?_
  exact ⟨Aα, F, hAα, hAc, hFc, hF, hFty, fun v => by cases v; exacts [hfalse, htrue]⟩

end TypeChecker

namespace VEnv
variable {env : VEnv}

/-- **The acceptance test for `Reflection.checkITE.WF`**, machine-checking that its two outputs
are the two inputs `VEnv.reflects_condApp` cannot otherwise be given.

`hF` is `Reflection.checkITE.WF`'s typing output verbatim (its `Dc` is
`Decidable (bvar 0)`, which is what `Reflection.checkITE`'s type check pins), and `hite` is its
selection output verbatim.  What is left is exactly `hdec`, `hB` and `hPR` -- the three facts
`Condition.check` establishes, none of which `Reflection.checkITE` sees.

This is the same discipline as `hsel_of_checkITE`: a hypothesis you can *construct* from the
shape the recognizer leaves is one you cannot have gotten wrong. -/
theorem reflects_condApp_of_checkITE (henv : env.WF) {F P D TD B PR RT Aα : VExpr}
    {g : Nat → Nat → Bool}
    (hFc : F.ClosedN 0) (hTDc : TD.ClosedN 0) (hRTc : RT.ClosedN 0) (hA0 : Aα.ClosedN 0)
    (hF : env.HasType 0 [] F (.forallE (.sort .zero)
      (.forallE (.app (.const ``Decidable []) (.bvar 0)) (.forallE Aα (.forallE Aα Aα)))))
    (hdec : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))))
    (hB : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app B (.natLit a)) (.natLit b))
      (.boolLit (g a b)))
    (hPR : ∀ a b : Nat, env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (g a b))))
    (hite : ∀ v : Bool, env.IsDefEqU 0
      [Aα, Aα, .app (.app RT (.bvar 0)) (.boolLit v), .sort .zero]
      (VExpr.condApp F (.bvar 3)
        (.app (.app (.app TD (.bvar 3)) (.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
      (bif v then .bvar 1 else .bvar 0)) :
    env.ReflectsCondApp F P D g :=
  reflects_condApp henv hA0 hF hdec hB hPR (hsel_of_checkITE henv hFc hTDc hRTc hA0 hite)

end VEnv

/-! ### Non-vacuity: the hypotheses `Reflection.checkITE.WF` leaves to its caller

`Reflection.checkITE.WF` asks the caller for `TrExprS.IsUnique` and `looseBVarRange' = 0` on
`r.type`, `r.toDec` and the result type `α`.  `IsUnique` is `False` at a `.proj`, so this is a
real vacuity risk rather than bookkeeping: if either shipped `Reflection` mentioned a
projection, the lemma could never be applied.  Both do not, and both are closed. -/

theorem Reflection.defn₁_type_isUnique :
    TrExprS.IsUnique (Lean4Lean.Environment.Reflection.defn₁.type) := by
  simp [Lean4Lean.Environment.Reflection.defn₁, TrExprS.IsUnique]

theorem Reflection.defn₁_toDec_isUnique :
    TrExprS.IsUnique (Lean4Lean.Environment.Reflection.defn₁.toDec) := by
  simp [Lean4Lean.Environment.Reflection.defn₁, TrExprS.IsUnique]

theorem Reflection.defn₂_type_isUnique :
    TrExprS.IsUnique (Lean4Lean.Environment.Reflection.defn₂.type) := by
  simp [Lean4Lean.Environment.Reflection.defn₂, TrExprS.IsUnique]

theorem Reflection.defn₂_toDec_isUnique :
    TrExprS.IsUnique (Lean4Lean.Environment.Reflection.defn₂.toDec) := by
  simp [Lean4Lean.Environment.Reflection.defn₂, TrExprS.IsUnique]

theorem Reflection.defn₁_type_closed :
    (Lean4Lean.Environment.Reflection.defn₁.type).looseBVarRange' = 0 := rfl

theorem Reflection.defn₁_toDec_closed :
    (Lean4Lean.Environment.Reflection.defn₁.toDec).looseBVarRange' = 0 := rfl

theorem Reflection.defn₂_type_closed :
    (Lean4Lean.Environment.Reflection.defn₂.type).looseBVarRange' = 0 := rfl

theorem Reflection.defn₂_toDec_closed :
    (Lean4Lean.Environment.Reflection.defn₂.toDec).looseBVarRange' = 0 := rfl

/-! ## `Reflection.checkNatDITE`

The `dite` counterpart of the `checkITE` block above.  Three things differ, and all three are
forced by `@dite`'s type rather than chosen:

* the two branch domains are `p → Nat` and `¬p → Nat`, so they *depend* on the first binder and
  the head's type is not the four-fold `Aα` Pi that `VEnv.condApp_typed` consumes -- the general
  `VEnv.condApp_typed'` is used instead;
* the selected branch is **applied** to the decision's proof (`a (ofTrue p H)`), so the abstract
  statement is `VEnv.ReflectsCondAppD`, not `VEnv.ReflectsCondApp`;
* `ofTrue` and `ofFalse` are extra checked terms, and their translations appear in the
  conclusion.
-/

/-- The bound variable two `vlam`s further out. -/
theorem trExprS_bvar2_inv' {env : VEnv} {Us Δ} {A B C : VExpr} {e' : VExpr}
    (h : TrExprS env Us
      ((none, .vlam A) :: (none, .vlam B) :: (none, .vlam C) :: Δ) (.bvar 2) e') :
    e' = .bvar 2 := by
  let .bvar h1 := h
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.depth, VExpr.liftN] at h1
  exact h1.1.symm

/-- **`@dite.{1} Nat`'s declared type.**  Unlike `trExprS_iteHeadType_inv'` this needs no
uniqueness side condition: every leaf of the type is a constant or a bound variable, because the
result type is fixed at `Nat`. -/
theorem trExprS_diteHeadType_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {n₁ n₂ n₃ n₄ n₅ n₆ bi₁ bi₂ bi₃ bi₄ bi₅ bi₆} {e' : VExpr}
    (h : TrExprS env Us Δ (.forallE n₁ (.sort .zero)
      (.forallE n₂ (.app (.const ``Decidable []) (.bvar 0))
        (.forallE n₃ (.forallE n₄ (.bvar 1) (.const ``Nat []) bi₄)
          (.forallE n₅ (.forallE n₆ (.app (.const ``Not []) (.bvar 2)) (.const ``Nat []) bi₆)
            (.const ``Nat []) bi₅) bi₃) bi₂) bi₁) e') :
    e' = .forallE (.sort .zero) (.forallE (.app (.const ``Decidable []) (.bvar 0))
      (.forallE (.forallE (.bvar 1) .nat)
        (.forallE (.forallE (.app (.const ``Not []) (.bvar 2)) .nat) .nat))) := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  cases trExprS_prop_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_arrow_inv' h2
  let .app _ _ d1 d2 := g1
  cases trExprS_const_nil_inv' d1
  cases trExprS_bvar0_inv' d2
  obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_arrow_inv' g2
  obtain ⟨_, _, rfl, a1, a2⟩ := trExprS_arrow_inv' k1
  cases trExprS_bvar1_inv' a1
  cases trExprS_const_nil_inv' a2
  obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_arrow_inv' k2
  obtain ⟨_, _, rfl, b1, b2⟩ := trExprS_arrow_inv' m1
  let .app _ _ c1 c2 := b1
  cases trExprS_const_nil_inv' c1
  cases trExprS_bvar2_inv' c2
  cases trExprS_const_nil_inv' b2
  cases trExprS_const_nil_inv' m2
  rfl

namespace VEnv
variable {env : VEnv}

/-- **`reflects_condAppD`'s `hsel` from the shape `Reflection.checkNatDITE` leaves behind** --
the acceptance test for the `dite` interface, and the exact counterpart of
`VEnv.hsel_of_checkITE`.

The four binder domains are `Prop`, `RT p (boolLit v)`, `p → Nat` and `¬p → Nat`; only the first
two are closed, so the instantiation genuinely uses `IsDefEqU.inst4`'s dependency on the
outermost binder.  The three typings `inst4` needs are recovered from the head's declared type
by `VEnv.condApp_typed'`, which is why `Reflection.checkNatDITE` checks `@dite Nat` **applied**. -/
theorem hsel_of_checkNatDITE (henv : env.WF) {FD TD RT OT OF : VExpr}
    (hFc : FD.ClosedN 0) (hTDc : TD.ClosedN 0) (hRTc : RT.ClosedN 0)
    (hOTc : OT.ClosedN 0) (hOFc : OF.ClosedN 0)
    (hFD : env.HasType 0 [] FD (.forallE (.sort .zero)
      (.forallE (.app (.const ``Decidable []) (.bvar 0))
        (.forallE (.forallE (.bvar 1) .nat)
          (.forallE (.forallE (.app (.const ``Not []) (.bvar 2)) .nat) .nat)))))
    (h : ∀ v : Bool, env.IsDefEqU 0
      [.forallE (.app (.const ``Not []) (.bvar 2)) .nat, .forallE (.bvar 1) .nat,
        .app (.app RT (.bvar 0)) (.boolLit v), .sort .zero]
      (VExpr.condApp FD (.bvar 3)
        (.app (.app (.app TD (.bvar 3)) (.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
      (bif v then .app (.bvar 1) (.app (.app OT (.bvar 3)) (.bvar 2))
        else .app (.bvar 0) (.app (.app OF (.bvar 3)) (.bvar 2)))) :
    ∀ (p H t e : VExpr) (v : Bool),
      VExpr.WF env 0 [] (VExpr.condApp FD p (.app (.app (.app TD p) (.boolLit v)) H) t e) →
      env.HasType 0 [] H (.app (.app RT p) (.boolLit v)) →
      env.IsDefEqU 0 [] (VExpr.condApp FD p (.app (.app (.app TD p) (.boolLit v)) H) t e)
        (bif v then .app t (.app (.app OT p) H) else .app e (.app (.app OF p) H)) := by
  intro p H t e v hwt hH
  obtain ⟨hp, -, ht, he⟩ := condApp_typed' henv hFD hwt
  have cl : ∀ {u T : VExpr}, env.HasType 0 [] u T → ∀ (w : VExpr) (j : Nat), u.inst w j = u :=
    fun hu _ _ => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).instN_eq (Nat.zero_le _)
  have lf : ∀ {u T : VExpr}, env.HasType 0 [] u T → ∀ j : Nat, u.liftN j = u :=
    fun hu _ => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).liftN_eq (Nat.zero_le _)
  have eF : ∀ (w : VExpr) (j : Nat), FD.inst w j = FD := fun _ _ => hFc.instN_eq (Nat.zero_le _)
  have eTD : ∀ (w : VExpr) (j : Nat), TD.inst w j = TD := fun _ _ => hTDc.instN_eq (Nat.zero_le _)
  have eRT : ∀ (w : VExpr) (j : Nat), RT.inst w j = RT := fun _ _ => hRTc.instN_eq (Nat.zero_le _)
  have eOT : ∀ (w : VExpr) (j : Nat), OT.inst w j = OT := fun _ _ => hOTc.instN_eq (Nat.zero_le _)
  have eOF : ∀ (w : VExpr) (j : Nat), OF.inst w j = OF := fun _ _ => hOFc.instN_eq (Nat.zero_le _)
  have ep := cl hp; have eH := cl hH; have et := cl ht; have ee := cl he
  have lp := lf hp; have lH := lf hH; have lt := lf ht; have le' := lf he
  have key := IsDefEqU.inst4
    (A := .app (.app RT (.bvar 0)) (.boolLit v))
    (B := .forallE (.bvar 1) .nat)
    (C := .forallE (.app (.const ``Not []) (.bvar 2)) .nat)
    (D := .sort .zero) (p := p) (a := H) (b := t) (c := e) henv (h v)
    hp (by simpa [VExpr.inst, eRT] using hH)
    (by simpa [VExpr.inst, VExpr.nat, VExpr.lift, ep, lp] using ht)
    (by simpa [VExpr.inst, VExpr.nat, VExpr.lift, ep, lp] using he)
  cases v <;>
    simpa [VExpr.condApp, VExpr.inst, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar,
      eF, eTD, eOT, eOF, ep, eH, et, ee, lp, lH, lt, le'] using key

end VEnv

namespace TypeChecker

variable {c : VContext}

set_option maxHeartbeats 1000000 in
/-- **One half of `Reflection.checkNatDITE`**, at a single boolean literal.

`ob` is the `Reflection.ofTrue` / `ofFalse` field the selected branch is applied to; the two
calls differ only in that field and in the literal, which is why one lemma serves both.  Unlike
`Reflection.checkITEHalf.WF` the two branch binders' domains are *not* closed -- they are
`p → Nat` and `¬p → Nat` -- so they are pinned by inverting an arrow rather than by
`TrExprS.unique` against a base-context translation. -/
theorem Reflection.checkNatDITEHalf.WF {s : VState}
    {r : Lean4Lean.Environment.Reflection} {v : Bool} {bn : Name}
    {sel : Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr}
    {ob : Lean.Expr} {fail : ∀ {β}, TypeChecker.M β}
    {RT TD FD OB : VExpr}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hbn : ∀ {Δ : VLCtx} {X : VExpr},
      TrExprS c.venv c.lparams Δ (.const bn []) X → X = VExpr.boolLit v)
    (hsel : ∀ p H a b : Lean.Expr, sel p H a b =
      bif v then Lean.mkApp a (Lean.mkApp2 ob p H) else Lean.mkApp b (Lean.mkApp2 ob p H))
    (hRT : c.TrExprS r.type RT) (hRTu : TrExprS.IsUnique r.type) (hRTc : RT.ClosedN 0)
    (hTD : c.TrExprS r.toDec TD) (hTDu : TrExprS.IsUnique r.toDec) (hTDc : TD.ClosedN 0)
    (hOB : c.TrExprS ob OB) (hOBu : TrExprS.IsUnique ob) (hOBc : OB.ClosedN 0)
    (hFD : c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD)
    (hFDc : FD.ClosedN 0) :
    M.WF c s (r.checkNatDITEHalf (.const bn []) sel fail) fun _ _ =>
      c.venv.IsDefEqU 0
        [.forallE (.app (.const ``Not []) (.bvar 2)) .nat, .forallE (.bvar 1) .nat,
          .app (.app RT (.bvar 0)) (VExpr.boolLit v), .sort .zero]
        (VExpr.condApp FD (.bvar 3)
          (.app (.app (.app TD (.bvar 3)) (VExpr.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
        (bif v then .app (.bvar 1) (.app (.app OB (.bvar 3)) (.bvar 2))
          else .app (.bvar 0) (.app (.app OB (.bvar 3)) (.bvar 2))) := by
  unfold Lean4Lean.Environment.Reflection.checkNatDITEHalf
  refine M.WF.withCheckedLocalDecl (by exact rfl) fun PT idp cwfp s1 _ hPT _ => ?_
  cases trExprS_prop_inv' hPT
  have hRT1 := TrExprS.weakLam0 cwfp hRT hRTc
  have hTD1 := TrExprS.weakLam0 cwfp hTD hTDc
  have hOB1 := TrExprS.weakLam0 cwfp hOB hOBc
  have hFD1 := TrExprS.weakLam0 cwfp hFD hFDc
  have hp1 := trExprS_lastFVar0 cwfp
  refine M.WF.withCheckedLocalDecl
    (by exact ⟨⟨hRT1.fvarsIn, hp1.fvarsIn⟩, by simp [FVarsIn]⟩)
    fun HT idH cwfH s2 _ hHT _ => ?_
  obtain ⟨_, _, rfl, z3, z4⟩ := trExprS_app_inv' hHT
  cases hbn z4
  obtain ⟨_, _, rfl, y3, y4⟩ := trExprS_app_inv' z3
  cases TrExprS.unique hRTu y3 hRT1
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial y4 hp1
  have hRT2 := TrExprS.weakLam0 cwfH hRT1 hRTc
  have hTD2 := TrExprS.weakLam0 cwfH hTD1 hTDc
  have hOB2 := TrExprS.weakLam0 cwfH hOB1 hOBc
  have hFD2 := TrExprS.weakLam0 cwfH hFD1 hFDc
  have hp2 := TrExprS.weakLift0 cwfH hp1
  simp only [VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, show ¬ (0:Nat) < 0 by omega,
    if_false, Nat.reduceAdd] at hp2
  -- `a : p → Nat`
  refine M.WF.withCheckedLocalDecl (by exact ⟨hp2.fvarsIn, by simp [FVarsIn]⟩)
    fun AT ida cwfa s3 _ hAT _ => ?_
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_arrow_inv' hAT
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial q1 hp2
  cases trExprS_const_nil_inv' q2
  have hTD3 := TrExprS.weakLam0 cwfa hTD2 hTDc
  have hOB3 := TrExprS.weakLam0 cwfa hOB2 hOBc
  have hFD3 := TrExprS.weakLam0 cwfa hFD2 hFDc
  have hp3 := TrExprS.weakLift0 cwfa hp2
  simp only [VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, show ¬ (1:Nat) < 0 by omega,
    if_false, Nat.reduceAdd] at hp3
  -- `b : ¬p → Nat`
  refine M.WF.withCheckedLocalDecl
    (by exact ⟨⟨by simp [FVarsIn], hp3.fvarsIn⟩, by simp [FVarsIn]⟩)
    fun BT idb cwfb s4 _ hBT _ => ?_
  obtain ⟨_, _, rfl, w1, w2⟩ := trExprS_arrow_inv' hBT
  obtain ⟨_, _, rfl, w3, w4⟩ := trExprS_app_inv' w1
  cases trExprS_const_nil_inv' w3
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial w4 hp3
  cases trExprS_const_nil_inv' w2
  have hTD4 := TrExprS.weakLam0 cwfb hTD3 hTDc
  have hOB4 := TrExprS.weakLam0 cwfb hOB3 hOBc
  have hFD4 := TrExprS.weakLam0 cwfb hFD3 hFDc
  have hp4 := TrExprS.weakLift0 cwfb hp3
  have hH4 := TrExprS.weakLift0 cwfb (TrExprS.weakLift0 cwfa (trExprS_lastFVar0 cwfH))
  have ha4 := TrExprS.weakLift0 cwfb (trExprS_lastFVar0 cwfa)
  have hb4 := trExprS_lastFVar0 cwfb
  simp only [VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, show ¬ (0:Nat) < 0 by omega,
    if_false, Nat.reduceAdd, show ¬ (1:Nat) < 0 by omega, show ¬ (2:Nat) < 0 by omega]
    at hp4 hH4 ha4
  refine M.WF.bind (checkedIsDefEq.WF
    ⟨⟨⟨⟨hFD4.fvarsIn, hp4.fvarsIn⟩,
        ⟨⟨hTD4.fvarsIn, hp4.fvarsIn⟩, by simp [FVarsIn]⟩, hH4.fvarsIn⟩, ha4.fvarsIn⟩,
      hb4.fvarsIn⟩
    (by rw [hsel]; cases v <;>
      exact ⟨by first | exact hb4.fvarsIn | exact ha4.fvarsIn,
        ⟨hOB4.fvarsIn, hp4.fvarsIn⟩, hH4.fvarsIn⟩)) fun bb _ _ hb => ?_
  obtain ⟨LHS, RHS, hLHS, hRHS, hdd⟩ := hb
  split
  case isFalse => exact hfail
  rename_i hbt
  have hdefeq := hdd (by simpa using hbt)
  -- the left-hand side: `@dite Nat p (toDec p bl H) a b`
  obtain ⟨_, _, rfl, n3, n4⟩ := trExprS_app_inv' hLHS
  cases TrExprS.unique (e := Lean.Expr.fvar idb) trivial n4 hb4
  obtain ⟨_, _, rfl, m3, m4⟩ := trExprS_app_inv' n3
  cases TrExprS.unique (e := Lean.Expr.fvar ida) trivial m4 ha4
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' m3
  obtain ⟨_, _, rfl, j3, j4⟩ := trExprS_app_inv' k3
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial j4 hp4
  cases TrExprS.unique
    (e := Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) ⟨trivial, trivial⟩ j3 hFD4
  obtain ⟨_, _, rfl, g3, g4⟩ := trExprS_app_inv' k4
  cases TrExprS.unique (e := Lean.Expr.fvar idH) trivial g4 hH4
  obtain ⟨_, _, rfl, f3, f4⟩ := trExprS_app_inv' g3
  cases hbn f4
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' f3
  cases TrExprS.unique hTDu e3 hTD4
  cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial e4 hp4
  -- the right-hand side: the selected branch applied to `ob p H`
  rw [hsel] at hRHS
  have hR : RHS = (bif v then .app (.bvar 1) (.app (.app OB (.bvar 3)) (.bvar 2))
      else .app (.bvar 0) (.app (.app OB (.bvar 3)) (.bvar 2))) := by
    cases v <;>
    · obtain ⟨_, _, rfl, t3, t4⟩ := trExprS_app_inv' hRHS
      obtain ⟨_, _, rfl, u3, u4⟩ := trExprS_app_inv' t4
      cases TrExprS.unique (e := Lean.Expr.fvar idH) trivial u4 hH4
      obtain ⟨_, _, rfl, p3, p4⟩ := trExprS_app_inv' u3
      cases TrExprS.unique (e := Lean.Expr.fvar idp) trivial p4 hp4
      cases TrExprS.unique hOBu p3 hOB4
      first
      | (cases TrExprS.unique (e := Lean.Expr.fvar ida) trivial t3 ha4; rfl)
      | (cases TrExprS.unique (e := Lean.Expr.fvar idb) trivial t3 hb4; rfl)
  subst hR
  refine .pure ?_
  simpa [VContext.IsDefEqU, VContext.withMLC, VLCtx.toCtx, hlp, hnil, VExpr.condApp, VExpr.nat]
    using hdefeq


set_option maxHeartbeats 1000000 in
/-- **The `dite` selection rule at result type `Nat`**, read back from the four checks and the
two halves.

The output is exactly `VEnv.hsel_of_checkNatDITE`'s hypothesis, plus the `@dite Nat` typing that
lemma needs and the two `of` translations its conclusion mentions.  `r.ofTrue` / `r.ofFalse` are
checked here only so that their translations exist and are closed; their *declared* types are
not part of the abstract statement, because `VEnv.ReflectsCondAppD` treats the branch's argument
as a black box. -/
theorem Reflection.checkNatDITE.WF {s : VState}
    {r : Lean4Lean.Environment.Reflection} {fail : ∀ {β}, TypeChecker.M β}
    {RT TD RTA TDA : VExpr}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hRT : c.TrExprS r.type RT) (hRTu : TrExprS.IsUnique r.type) (hRTty : c.HasType RT RTA)
    (hTD : c.TrExprS r.toDec TD) (hTDu : TrExprS.IsUnique r.toDec) (hTDty : c.HasType TD TDA)
    (hOTfv : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars)) (hOTu : TrExprS.IsUnique r.ofTrue)
    (hOFfv : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars)) (hOFu : TrExprS.IsUnique r.ofFalse) :
    M.WF c s (r.checkNatDITE fail) fun _ _ =>
      ∃ FD OT OF, FD.ClosedN 0 ∧ OT.ClosedN 0 ∧ OF.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
        c.TrExprS r.ofTrue OT ∧ c.TrExprS r.ofFalse OF ∧
        c.HasType FD (.forallE (.sort .zero)
          (.forallE (.app (.const ``Decidable []) (.bvar 0))
            (.forallE (.forallE (.bvar 1) .nat)
              (.forallE (.forallE (.app (.const ``Not []) (.bvar 2)) .nat) .nat)))) ∧
        ∀ v : Bool, c.venv.IsDefEqU 0
          [.forallE (.app (.const ``Not []) (.bvar 2)) .nat, .forallE (.bvar 1) .nat,
            .app (.app RT (.bvar 0)) (VExpr.boolLit v), .sort .zero]
          (VExpr.condApp FD (.bvar 3)
            (.app (.app (.app TD (.bvar 3)) (VExpr.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
          (bif v then .app (.bvar 1) (.app (.app OT (.bvar 3)) (.bvar 2))
            else .app (.bvar 0) (.app (.app OF (.bvar 3)) (.bvar 2))) := by
  have hRTc := (closedN_of_nil hnil hRTty).1
  have hTDc := (closedN_of_nil hnil hTDty).1
  unfold Lean4Lean.Environment.Reflection.checkNatDITE
  -- `Not : Prop → Prop`
  refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn])
    (by exact ⟨rfl, rfl⟩)) fun _ _ _ _ => ?_
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  -- `@dite.{1} Nat : ∀ (c : Prop), Decidable c → (c → Nat) → (¬c → Nat) → Nat`
  refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl)
    (by exact ⟨rfl, ⟨by simp [FVarsIn], by simp [FVarsIn]⟩,
      ⟨by simp [FVarsIn], by simp [FVarsIn]⟩,
      ⟨⟨by simp [FVarsIn], by simp [FVarsIn]⟩, by simp [FVarsIn]⟩,
      by simp [FVarsIn]⟩)) fun _ _ _ h => ?_
  obtain ⟨FD, FA, FT, hFD, hFA, hFT, hFd⟩ := h
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hb2
  cases trExprS_diteHeadType_inv' hFT
  have hFDty := hFA.defeqU_r c.Ewf c.Δwf.toCtx (hFd (by simpa using hb2))
  have hFDc := (closedN_of_nil hnil hFDty).1
  -- `r.ofTrue`
  refine M.WF.bind (checkedTypeIs.WF hOTfv
    (by exact ⟨rfl, ⟨⟨hRT.fvarsIn, trivial⟩, by simp [FVarsIn]⟩, trivial⟩))
    fun _ _ _ h => ?_
  obtain ⟨OT, OTA, -, hOT, hOTA, -, -⟩ := h
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  have hOTc := (closedN_of_nil hnil hOTA).1
  -- `r.ofFalse`
  refine M.WF.bind (checkedTypeIs.WF hOFfv
    (by exact ⟨rfl, ⟨⟨hRT.fvarsIn, trivial⟩, by simp [FVarsIn]⟩,
      ⟨by simp [FVarsIn], trivial⟩⟩)) fun _ _ _ h => ?_
  obtain ⟨OF, OFA, -, hOF, hOFA, -, -⟩ := h
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  have hOFc := (closedN_of_nil hnil hOFA).1
  refine M.WF.bind (Reflection.checkNatDITEHalf.WF (v := true) (bn := ``Bool.true)
      (OB := OT) hfail hnil hlp (fun h => trExprS_const_nil_inv' h) (fun _ _ _ _ => rfl)
      hRT hRTu hRTc hTD hTDu hTDc hOT hOTu hOTc hFD hFDc) fun _ _ _ htrue => ?_
  refine (Reflection.checkNatDITEHalf.WF (v := false) (bn := ``Bool.false)
      (OB := OF) hfail hnil hlp (fun h => trExprS_const_nil_inv' h) (fun _ _ _ _ => rfl)
      hRT hRTu hRTc hTD hTDu hTDc hOF hOFu hOFc hFD hFDc).mono fun _ _ _ hfalse => ?_
  exact ⟨FD, OT, OF, hFDc, hOTc, hOFc, hFD, hOT, hOF, hFDty,
    fun v => by cases v; exacts [hfalse, htrue]⟩

end TypeChecker

namespace VEnv
variable {env : VEnv}

/-- **The acceptance test for `Reflection.checkNatDITE.WF`**, the `dite` counterpart of
`VEnv.reflects_condApp_of_checkITE`: its two outputs are fed to `VEnv.reflects_condAppD` and
what is left over is exactly `hdec`, `hB`, `hPR` -- the same three facts, established by
`Condition.check` itself, that the `ite` side leaves. -/
theorem reflects_condAppD_of_checkNatDITE (henv : env.WF) {FD P D TD B PR RT OT OF : VExpr}
    {g : Nat → Nat → Bool}
    (hFc : FD.ClosedN 0) (hTDc : TD.ClosedN 0) (hRTc : RT.ClosedN 0)
    (hOTc : OT.ClosedN 0) (hOFc : OF.ClosedN 0)
    (hFD : env.HasType 0 [] FD (.forallE (.sort .zero)
      (.forallE (.app (.const ``Decidable []) (.bvar 0))
        (.forallE (.forallE (.bvar 1) .nat)
          (.forallE (.forallE (.app (.const ``Not []) (.bvar 2)) .nat) .nat)))))
    (hdec : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))))
    (hB : ∀ a b : Nat, env.IsDefEqU 0 [] (.app (.app B (.natLit a)) (.natLit b))
      (.boolLit (g a b)))
    (hPR : ∀ a b : Nat, env.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (g a b))))
    (hdite : ∀ v : Bool, env.IsDefEqU 0
      [.forallE (.app (.const ``Not []) (.bvar 2)) .nat, .forallE (.bvar 1) .nat,
        .app (.app RT (.bvar 0)) (.boolLit v), .sort .zero]
      (VExpr.condApp FD (.bvar 3)
        (.app (.app (.app TD (.bvar 3)) (.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
      (bif v then .app (.bvar 1) (.app (.app OT (.bvar 3)) (.bvar 2))
        else .app (.bvar 0) (.app (.app OF (.bvar 3)) (.bvar 2)))) :
    env.ReflectsCondAppD FD P D OT OF PR g :=
  reflects_condAppD henv hdec hB hPR
    (hsel_of_checkNatDITE henv hFc hTDc hRTc hOTc hOFc hFD hdite)

end VEnv

/-! ### `Condition.check`'s decision term

`Condition.check` builds `e := fun x y => toDec (prop x y) (asBool x y) (proof x y)` and compares
it with `cond.dec`.  Read abstractly that comparison is `VEnv.reflects_condApp`'s `hdec`: the
translation of `e` is a two-fold λ, and instantiating it at a pair of numerals is two β-steps.
The type of the λ's body is *not* recovered by inverting a `HasType` (that would need
Π-injectivity twice); it is read off `TrExprS.app`, which carries the function's Pi-type at every
application node. -/

/-- Inversion for a λ, in the `_inv'` family's raw form. -/
theorem trExprS_lam_inv' {env : VEnv} {Us Δ} {nm : Name} {A B : Lean.Expr} {bi} {e' : VExpr}
    (h : TrExprS env Us Δ (.lam nm A B bi) e') :
    ∃ A' B', e' = .lam A' B' ∧ TrExprS env Us Δ A A' ∧
      TrExprS env Us ((none, .vlam A') :: Δ) B B' :=
  let .lam _ h3 h4 := h; ⟨_, _, rfl, h3, h4⟩

/-- **The decision term `Condition.check` compares against `cond.dec`.**  Same device as
`trExprS_reflProofType_inv'`: the four abstract sub-terms are closed and `IsUnique`, so they are
identified with their base-context translations, and the two bound variables are pinned
outright. -/
theorem trExprS_decisionTerm_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {td prp asB prf : Lean.Expr} {TD P B PR : VExpr} {e' : VExpr} (henv : env.Ordered)
    (hTD : TrExprS env Us Δ td TD) (hTDu : TrExprS.IsUnique td)
    (hTDb : td.looseBVarRange' = 0) (hTDc : TD.ClosedN 0)
    (hP : TrExprS env Us Δ prp P) (hPu : TrExprS.IsUnique prp)
    (hPb : prp.looseBVarRange' = 0) (hPc : P.ClosedN 0)
    (hB : TrExprS env Us Δ asB B) (hBu : TrExprS.IsUnique asB)
    (hBb : asB.looseBVarRange' = 0) (hBc : B.ClosedN 0)
    (hPR : TrExprS env Us Δ prf PR) (hPRu : TrExprS.IsUnique prf)
    (hPRb : prf.looseBVarRange' = 0) (hPRc : PR.ClosedN 0)
    (h : TrExprS env Us Δ (.lam0 (.const ``Nat []) (.lam0 (.const ``Nat [])
      (Lean.mkApp3 td (Lean.mkApp2 prp (.bvar 1) (.bvar 0))
        (Lean.mkApp2 asB (.bvar 1) (.bvar 0)) (Lean.mkApp2 prf (.bvar 1) (.bvar 0))))) e') :
    e' = .lam .nat (.lam .nat
      (.app (.app (.app TD (.app (.app P (.bvar 1)) (.bvar 0)))
        (.app (.app B (.bvar 1)) (.bvar 0))) (.app (.app PR (.bvar 1)) (.bvar 0)))) := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_lam_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_lam_inv' h2
  cases trExprS_const_nil_inv' g1
  have wk : ∀ {u : Lean.Expr} {u' : VExpr}, TrExprS env Us Δ u u' → u.looseBVarRange' = 0 →
      u'.ClosedN 0 →
      TrExprS env Us ((none, .vlam (.const ``Nat [])) ::
        (none, .vlam (.const ``Nat [])) :: Δ) u u' := fun hu hb hc =>
    trExprS_weakBV0 henv (trExprS_weakBV0 henv hu hb hc) hb hc
  obtain ⟨_, _, rfl, a3, a4⟩ := trExprS_app_inv' g2
  obtain ⟨_, _, rfl, b3, b4⟩ := trExprS_app_inv' a3
  obtain ⟨_, _, rfl, c3, c4⟩ := trExprS_app_inv' b3
  cases TrExprS.unique hTDu c3 (wk hTD hTDb hTDc)
  obtain ⟨_, _, rfl, d3, d4⟩ := trExprS_app_inv' c4
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' d3
  cases TrExprS.unique hPu e3 (wk hP hPb hPc)
  cases trExprS_bvar1_inv' e4
  cases trExprS_bvar0_inv' d4
  obtain ⟨_, _, rfl, f3, f4⟩ := trExprS_app_inv' b4
  obtain ⟨_, _, rfl, i3, i4⟩ := trExprS_app_inv' f3
  cases TrExprS.unique hBu i3 (wk hB hBb hBc)
  cases trExprS_bvar1_inv' i4
  cases trExprS_bvar0_inv' f4
  obtain ⟨_, _, rfl, j3, j4⟩ := trExprS_app_inv' a4
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' j3
  cases TrExprS.unique hPRu k3 (wk hPR hPRb hPRc)
  cases trExprS_bvar1_inv' k4
  cases trExprS_bvar0_inv' j4
  rfl

namespace VEnv
variable {env : VEnv}

/-- **Two β-steps under a term the checker has only proved defeq to.**  `Condition.check`'s
last comparison is `isDefEq e cond.dec`, so what the verification holds is `E ≈ D` with `E` a
two-fold λ; the reflection statements want `D` applied to a pair of numerals.  The two
congruences and the two βs are here. -/
theorem IsDefEqU.lam2_beta (henv : env.WF) (hlit : env.NatLits) (hnat : env.IsType 0 [] .nat)
    {body T D : VExpr} (hbody : env.HasType 0 [.nat, .nat] body T)
    (h : env.IsDefEqU 0 [] (.lam .nat (.lam .nat body)) D) (a b : Nat) :
    env.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      ((body.inst (.natLit a) 1).inst (.natLit b)) := by
  obtain ⟨u, hnatu⟩ := hnat
  have hnatu1 : env.HasType 0 [.nat] .nat (.sort u) := hnatu.weak0 henv.ordered
  have hlam1 : env.HasType 0 [.nat] (.lam .nat body) (.forallE .nat T) :=
    HasType.lam hnatu1 hbody
  have hE : env.HasType 0 [] (.lam .nat (.lam .nat body)) (.forallE .nat (.forallE .nat T)) :=
    HasType.lam hnatu hlam1
  have ha : env.HasType 0 [] (.natLit a) .nat := hlit a
  have hb : env.HasType 0 [] (.natLit b) .nat := hlit b
  have hEa : env.HasType 0 [] (.app (.lam .nat (.lam .nat body)) (.natLit a))
      (.forallE .nat (T.inst (.natLit a) 1)) := by
    have := hE.app ha; simpa [VExpr.inst, VExpr.nat] using this
  have hwt : VExpr.WF env 0 []
      (.app (.app (.lam .nat (.lam .nat body)) (.natLit a)) (.natLit b)) := ⟨_, hEa.app hb⟩
  have beta1 : env.IsDefEqU 0 [] (.app (.lam .nat (.lam .nat body)) (.natLit a))
      (.lam .nat (body.inst (.natLit a) 1)) := by
    have := IsDefEqU.beta' hlam1 ha
    simpa [VExpr.inst, VExpr.nat] using this
  have hbody1 : env.HasType 0 [.nat] (body.inst (.natLit a) 1) (T.inst (.natLit a) 1) := by
    have := hbody.instN henv.ordered (Γ₀ := []) (A₀ := .nat) (.succ .zero) ha
    simpa [VExpr.inst, VExpr.nat] using this
  have beta2 : env.IsDefEqU 0 [] (.app (.lam .nat (body.inst (.natLit a) 1)) (.natLit b))
      ((body.inst (.natLit a) 1).inst (.natLit b)) := IsDefEqU.beta' hbody1 hb
  have step1 := IsDefEqU.app_congr_fn' henv hwt beta1
  have step0 := IsDefEqU.app2_congr_fn henv hwt h
  exact IsDefEqU.trans henv trivial step0.symm
    (IsDefEqU.trans henv trivial step1 beta2)

end VEnv

/-! ## `Condition.check`

The whole `.reflectNatNat` arm, read back as the two abstract statements the four fuel /
well-founded branches consume: one `VEnv.ReflectsCondApp` per element of `iteTypes`, and -- when
the branch asks for it -- one `VEnv.ReflectsCondAppD`.

Everything the arm's own checks contribute is assembled here:

* `hdec` from `isDefEq e cond.dec`, β-reduced through the decision term's two λs by
  `VEnv.IsDefEqU.lam2_beta`;
* `hB` from the caller's `hg`, which for the two shipped conditions is
  `VEnv.HasPrimitives.natBLE` / `natBEq`;
* `hPR` from `checkedTypeIs proof …` through `trExprS_reflProofType_inv'` and
  `VEnv.reflProof_inst`, with the boolean side rewritten by `hg`;
* the selection equations from `Reflection.checkITE.WF` / `Reflection.checkNatDITE.WF`.

The `iteTypes` loop is handled by `M.WF.forIn` with the invariant "`iteTypes` splits as
`pre ++ vs`, and every element of `pre` has been read back"; the accumulator is `PUnit`, so the
processed prefix has to live in the invariant rather than in the accumulator. -/

namespace TypeChecker
variable {c : VContext}

set_option maxHeartbeats 2000000 in
theorem Condition.check.WF {s : VState} {cond : Lean4Lean.Environment.Condition}
    {asBool proof : Lean.Expr} {r : Lean4Lean.Environment.Reflection}
    {iteTypes : List Lean.Expr} {dite : Bool}
    {fail : ∀ {α}, TypeChecker.M α} {g : Nat → Nat → Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hnat : c.venv.contains ``Nat) (hnatty : c.venv.IsType 0 [] .nat)
    (himpl : cond.impl = .reflectNatNat asBool r proof)
    (hdecfv : cond.dec.FVarsIn (· ∈ c.vlctx.fvars))
    (hpropfv : cond.prop.FVarsIn (· ∈ c.vlctx.fvars)) (hpropu : TrExprS.IsUnique cond.prop)
    (hpropb : cond.prop.looseBVarRange' = 0)
    (hrtyfv : r.type.FVarsIn (· ∈ c.vlctx.fvars)) (hrtyu : TrExprS.IsUnique r.type)
    (hrtyb : r.type.looseBVarRange' = 0)
    (htdfv : r.toDec.FVarsIn (· ∈ c.vlctx.fvars)) (htdu : TrExprS.IsUnique r.toDec)
    (htdb : r.toDec.looseBVarRange' = 0)
    (hoTfv : r.ofTrue.FVarsIn (· ∈ c.vlctx.fvars)) (hoTu : TrExprS.IsUnique r.ofTrue)
    (hoFfv : r.ofFalse.FVarsIn (· ∈ c.vlctx.fvars)) (hoFu : TrExprS.IsUnique r.ofFalse)
    (hasBfv : asBool.FVarsIn (· ∈ c.vlctx.fvars)) (hasBu : TrExprS.IsUnique asBool)
    (hasBb : asBool.looseBVarRange' = 0)
    (hprffv : proof.FVarsIn (· ∈ c.vlctx.fvars)) (hprfu : TrExprS.IsUnique proof)
    (hprfb : proof.looseBVarRange' = 0)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0)
    (hg : ∀ {Δ : VLCtx} {X : VExpr}, TrExprS c.venv c.lparams Δ asBool X →
      ∀ a b : Nat, c.venv.IsDefEqU 0 [] (.app (.app X (.natLit a)) (.natLit b))
        (.boolLit (g a b))) :
    M.WF c s (cond.check fail iteTypes dite) fun _ _ =>
      ∃ P D, c.TrExprS cond.prop P ∧ c.TrExprS cond.dec D ∧ P.ClosedN 0 ∧ D.ClosedN 0 ∧
        (∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
          c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
          c.venv.ReflectsCondApp F P D g) ∧
        (dite = true → ∃ FD OT OF PR,
          c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
          c.TrExprS r.ofTrue OT ∧ c.TrExprS r.ofFalse OF ∧ c.TrExprS proof PR ∧
          c.venv.ReflectsCondAppD FD P D OT OF PR g) := by
  unfold Lean4Lean.Environment.Condition.check
  simp only []
  refine M.WF.bind (checkType.WF hdecfv) fun _ _ _ hD => ?_
  obtain ⟨D, DA, -, hD, -, hDty⟩ := hD
  rw [himpl]
  have hprim := c.hasPrimitives
  have hlit : c.venv.NatLits := VEnv.HasPrimitives.natLit_hasType hprim hnat
  have hDc := (closedN_of_nil hnil hDty).1
  -- `cond.prop : Nat → Nat → Prop`
  refine M.WF.bind (checkedTypeIs.WF hpropfv (by simp [FVarsIn]; rfl)) fun _ _ _ hP => ?_
  obtain ⟨P, PA, PT, hP, hPA, hPT, hPd⟩ := hP
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hpb
  cases trExprS_natArrowProp_inv' hPT
  have hPty := hPA.defeqU_r c.Ewf c.Δwf.toCtx (hPd (by simpa using hpb))
  have hPc := (closedN_of_nil hnil hPty).1
  -- `Reflection.check`
  refine M.WF.bind (Reflection.check.WF (fun {_ _ _} => hfail) hrtyfv htdfv) fun _ _ _ hr => ?_
  obtain ⟨⟨RT, hRT, hRTty⟩, TD, TDA, hTD, hTDty⟩ := hr
  have hRTc := (closedN_of_nil hnil hRTty).1
  have hTDc := (closedN_of_nil hnil hTDty).1
  -- the `iteTypes` loop
  refine M.WF.bind (M.WF.forIn
    (Inv := fun (vs : List Lean.Expr) (_ : PUnit) (_ : VState) => ∃ pre, iteTypes = pre ++ vs ∧
      ∀ α ∈ pre, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧ F.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧
        c.HasType F (.forallE (.sort .zero)
          (.forallE (.app (.const ``Decidable []) (.bvar 0)) (.forallE Aα (.forallE Aα Aα)))) ∧
        ∀ v : Bool, c.venv.IsDefEqU 0
          [Aα, Aα, .app (.app RT (.bvar 0)) (VExpr.boolLit v), .sort .zero]
          (VExpr.condApp F (.bvar 3)
            (.app (.app (.app TD (.bvar 3)) (VExpr.boolLit v)) (.bvar 2)) (.bvar 1) (.bvar 0))
          (bif v then .bvar 1 else .bvar 0))
    (fun α vs _ _ hinv => ?_) ⟨[], rfl, by simp⟩) fun _ _ _ hloop => ?_
  · obtain ⟨pre, hpre, hall⟩ := hinv
    obtain ⟨hαfv, hαu, hαb⟩ := hitefv α (by rw [hpre]; simp)
    refine M.WF.bind (Reflection.checkITE.WF (fun {_ _ _ _} => hfail) hnil hlp
      hαfv hαu hαb hRT hrtyu hRTty hTD htdu hTDty) fun _ _ _ h => ?_
    exact .pure ⟨_, rfl, pre ++ [α], by simp [hpre], by
      intro β hβ
      rcases List.mem_append.1 hβ with hβ | hβ
      · exact hall β hβ
      · cases List.mem_singleton.1 hβ; exact h⟩
  have hnatfv : Lean.Expr.FVarsIn (· ∈ c.vlctx.fvars) (.const ``Nat []) := by simp [FVarsIn]
  -- `asBool : Nat → Nat → Bool`
  refine M.WF.bind (checkedTypeIs.WF hasBfv (by simp [FVarsIn])) fun _ _ _ hBo => ?_
  obtain ⟨B, BA, BT, hB, hBA, hBT, hBd⟩ := hBo
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  have hBc := (closedN_of_nil hnil hBA).1
  -- `isProp (← checkType proof)`
  refine M.WF.bind (checkType.WF hprffv) fun _ _ _ hpr0 => ?_
  obtain ⟨PR0, PRT0, -, hPR0, hPRT0, hPR0ty⟩ := hpr0
  refine M.WF.bind (isProp.WF hPRT0) fun _ _ _ _ => ?_
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  -- `proof : ∀ n m : Nat, r.type (cond.prop n m) (asBool n m)`
  refine M.WF.bind (checkedTypeIs.WF hprffv
    ⟨hnatfv, hnatfv, ⟨⟨hrtyfv, ⟨hpropfv, trivial⟩, trivial⟩, ⟨hasBfv, trivial⟩, trivial⟩⟩)
    fun _ _ _ hPRo => ?_
  obtain ⟨PR, PRA, PRT, hPR, hPRA, hPRT, hPRd⟩ := hPRo
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hprb
  cases trExprS_reflProofType_inv' c.Ewf.ordered hRT hrtyu hrtyb hRTc hP hpropu hpropb hPc
    hB hasBu hasBb hBc hPRT
  have hPRty := hPRA.defeqU_r c.Ewf c.Δwf.toCtx (hPRd (by simpa using hprb))
  have hPRc := (closedN_of_nil hnil hPRty).1
  have hctx : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  have hUs : c.lparams.length = 0 := by rw [hlp]; rfl
  have raw : ∀ {e A : VExpr}, c.HasType e A → c.venv.HasType 0 [] e A := by
    intro e A h; rwa [VContext.HasType, hctx, hUs] at h
  -- `checkType e`, then `isDefEq e cond.dec`
  refine M.WF.bind (checkType.WF
    ⟨hnatfv, hnatfv, ⟨⟨htdfv, ⟨hpropfv, trivial⟩, trivial⟩, ⟨hasBfv, trivial⟩, trivial⟩,
      ⟨hprffv, trivial⟩, trivial⟩) fun _ _ _ hEo => ?_
  obtain ⟨E, EA, -, hE, -, hEty⟩ := hEo
  cases trExprS_decisionTerm_inv' c.Ewf.ordered hTD htdu htdb hTDc hP hpropu hpropb hPc
    hB hasBu hasBb hBc hPR hprfu hprfb hPRc hE
  obtain ⟨-, T1, hlam1⟩ := VEnv.HasType.lam_inv c.Ewf.ordered trivial (raw hEty)
  obtain ⟨-, T, hbody⟩ := VEnv.HasType.lam_inv (Γ := [VExpr.nat]) c.Ewf.ordered
    (show OnCtx [VExpr.nat] (c.venv.IsType 0) from ⟨trivial, hnatty⟩) hlam1
  refine M.WF.bind (isDefEq.WF hE hD) fun _ _ _ hde => ?_
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  rename_i hdeb
  have hED : c.venv.IsDefEqU 0 []
      (.lam .nat (.lam .nat
        (.app (.app (.app TD (.app (.app P (.bvar 1)) (.bvar 0)))
          (.app (.app B (.bvar 1)) (.bvar 0))) (.app (.app PR (.bvar 1)) (.bvar 0))))) D := by
    have := hde (by simpa using hdeb); rwa [VContext.IsDefEqU, hctx, hUs] at this
  -- `hdec`: the decision term at a pair of numerals
  have hdec : ∀ a b : Nat, c.venv.IsDefEqU 0 [] (.app (.app D (.natLit a)) (.natLit b))
      (.app (.app (.app TD (.app (.app P (.natLit a)) (.natLit b)))
        (.app (.app B (.natLit a)) (.natLit b))) (.app (.app PR (.natLit a)) (.natLit b))) := by
    intro a b
    have := VEnv.IsDefEqU.lam2_beta c.Ewf hlit hnatty hbody hED a b
    simpa [VExpr.inst, VExpr.instVar, hTDc.instN_eq (Nat.zero_le _), hPc.instN_eq (Nat.zero_le _),
      hBc.instN_eq (Nat.zero_le _), hPRc.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _)] using this
  -- `hB` and `hPR`
  have hBg : ∀ a b : Nat, c.venv.IsDefEqU 0 [] (.app (.app B (.natLit a)) (.natLit b))
      (.boolLit (g a b)) := hg hB
  have hPRfact : ∀ a b : Nat, c.venv.HasType 0 [] (.app (.app PR (.natLit a)) (.natLit b))
      (.app (.app RT (.app (.app P (.natLit a)) (.natLit b))) (.boolLit (g a b))) := by
    intro a b
    have h1 := VEnv.reflProof_inst hprim hnat hRTc hPc hBc (raw hPRty) a b
    obtain ⟨u, hu⟩ := h1.isType c.Ewf.ordered trivial
    exact VEnv.HasType.defeqU_r c.Ewf trivial
      (VEnv.IsDefEqU.app_congr_arg' c.Ewf ⟨_, hu⟩ (hBg a b)) h1
  obtain ⟨pre, hpre, hloop'⟩ := hloop
  rw [List.append_nil] at hpre
  subst hpre
  have hites : ∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
      c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
      c.venv.ReflectsCondApp F P D g := by
    intro α hα
    obtain ⟨Aα, F, hAα, hAc, hFc, hF, hFty, hsel⟩ := hloop' α hα
    exact ⟨Aα, F, hAα, hAc, hF, hFc,
      VEnv.reflects_condApp_of_checkITE c.Ewf hFc hTDc hRTc hAc (raw hFty) hdec hBg hPRfact hsel⟩
  split
  · refine (Reflection.checkNatDITE.WF hfail hnil hlp hRT hrtyu hRTty
      hTD htdu hTDty hoTfv hoTu hoFfv hoFu).mono fun _ _ _ hnd => ?_
    obtain ⟨FD, OT, OF, hFDc, hOTc, hOFc, hFD, hOT, hOF, hFDty, hditeeq⟩ := hnd
    exact ⟨P, D, hP, hD, hPc, hDc, hites, fun _ => ⟨FD, OT, OF, PR, hFD, hOT, hOF, hPR,
      VEnv.reflects_condAppD_of_checkNatDITE c.Ewf hFDc hTDc hRTc hOTc hOFc (raw hFDty)
        hdec hBg hPRfact hditeeq⟩⟩
  · rename_i hd
    exact .pure ⟨P, D, hP, hD, hPc, hDc, hites, fun h => absurd h hd⟩


/-! ### Acceptance: the hypotheses are dischargeable at the two shipped `Condition`s -/

open Lean4Lean.Environment in
theorem Condition.check.WF_natLE {s : VState} {fail : ∀ {α}, TypeChecker.M α}
    {iteTypes : List Lean.Expr} {dite : Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hnat : c.venv.contains ``Nat) (hnatty : c.venv.IsType 0 [] .nat)
    (hble : c.venv.contains ``Nat.ble)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (Condition.natLE.check fail iteTypes dite) fun _ _ =>
      ∃ P D, c.TrExprS Condition.natLE.prop P ∧ c.TrExprS Condition.natLE.dec D ∧
        P.ClosedN 0 ∧ D.ClosedN 0 ∧
        (∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
          c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
          c.venv.ReflectsCondApp F P D Nat.ble) ∧
        (dite = true → ∃ FD OT OF PR,
          c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
          c.TrExprS Reflection.defn₁.ofTrue OT ∧
          c.TrExprS Reflection.defn₁.ofFalse OF ∧
          c.venv.ReflectsCondAppD FD P D OT OF PR Nat.ble) := by
  refine (Condition.check.WF (c := c) (s := s) (cond := Condition.natLE)
    (iteTypes := iteTypes) (dite := dite) (g := Nat.ble) (himpl := rfl)
    (hfail := hfail) (hnil := hnil) (hlp := hlp) (hnat := hnat) (hnatty := hnatty)
    (hitefv := hitefv)
    (hdecfv := by simp [Condition.natLE, FVarsIn])
    (hpropfv := by simp [Condition.natLE, FVarsIn, Lean.Level.hasMVar'])
    (hpropu := by simp [Condition.natLE, TrExprS.IsUnique])
    (hpropb := rfl)
    (hrtyfv := by simp [Reflection.defn₁, FVarsIn, Lean.Level.hasMVar'])
    (hrtyu := Reflection.defn₁_type_isUnique)
    (hrtyb := Reflection.defn₁_type_closed)
    (htdfv := by simp [Reflection.defn₁, FVarsIn, Lean.Level.hasMVar'])
    (htdu := Reflection.defn₁_toDec_isUnique)
    (htdb := Reflection.defn₁_toDec_closed)
    (hoTfv := by simp [Reflection.defn₁, FVarsIn, Lean.Level.hasMVar'])
    (hoTu := by simp [Reflection.defn₁, TrExprS.IsUnique])
    (hoFfv := by simp [Reflection.defn₁, FVarsIn, Lean.Level.hasMVar'])
    (hoFu := by simp [Reflection.defn₁, TrExprS.IsUnique])
    (hasBfv := by simp [FVarsIn])
    (hasBu := by simp [TrExprS.IsUnique])
    (hasBb := rfl)
    (hprffv := by simp [FVarsIn, Lean.Level.hasMVar'])
    (hprfu := by simp [TrExprS.IsUnique])
    (hprfb := rfl)
    (hg := fun h a b => by
      cases trExprS_const_nil_inv' h; exact c.hasPrimitives.natBLE hble a b)).mono
    fun _ _ _ h => ?_
  obtain ⟨P, D, hP, hD, hPc, hDc, hite, hdite⟩ := h
  refine ⟨P, D, hP, hD, hPc, hDc, hite, fun hd => ?_⟩
  obtain ⟨FD, OT, OF, PR, h1, h2, h3, -, h5⟩ := hdite hd
  exact ⟨FD, OT, OF, PR, h1, h2, h3, h5⟩

open Lean4Lean.Environment in
theorem Condition.check.WF_natEq {s : VState} {fail : ∀ {α}, TypeChecker.M α}
    {iteTypes : List Lean.Expr} {dite : Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hnat : c.venv.contains ``Nat) (hnatty : c.venv.IsType 0 [] .nat)
    (hbeq : c.venv.contains ``Nat.beq)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (Condition.natEq.check fail iteTypes dite) fun _ _ =>
      ∃ P D, c.TrExprS Condition.natEq.prop P ∧ c.TrExprS Condition.natEq.dec D ∧
        P.ClosedN 0 ∧ D.ClosedN 0 ∧
        (∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
          c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
          c.venv.ReflectsCondApp F P D Nat.beq) ∧
        (dite = true → ∃ FD OT OF PR,
          c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
          c.TrExprS Reflection.defn₂.ofTrue OT ∧
          c.TrExprS Reflection.defn₂.ofFalse OF ∧
          c.venv.ReflectsCondAppD FD P D OT OF PR Nat.beq) := by
  refine (Condition.check.WF (c := c) (s := s) (cond := Condition.natEq)
    (iteTypes := iteTypes) (dite := dite) (g := Nat.beq) (himpl := rfl)
    (hfail := hfail) (hnil := hnil) (hlp := hlp) (hnat := hnat) (hnatty := hnatty)
    (hitefv := hitefv)
    (hdecfv := by simp [Condition.natEq, FVarsIn])
    (hpropfv := by simp [Condition.natEq, FVarsIn, Lean.Level.hasMVar'])
    (hpropu := by simp [Condition.natEq, TrExprS.IsUnique])
    (hpropb := rfl)
    (hrtyfv := by simp [Reflection.defn₂, FVarsIn, Lean.Level.hasMVar'])
    (hrtyu := Reflection.defn₂_type_isUnique)
    (hrtyb := Reflection.defn₂_type_closed)
    (htdfv := by simp [Reflection.defn₂, FVarsIn, Lean.Level.hasMVar'])
    (htdu := Reflection.defn₂_toDec_isUnique)
    (htdb := Reflection.defn₂_toDec_closed)
    (hoTfv := by simp [Reflection.defn₂, FVarsIn, Lean.Level.hasMVar'])
    (hoTu := by simp [Reflection.defn₂, TrExprS.IsUnique])
    (hoFfv := by simp [Reflection.defn₂, FVarsIn, Lean.Level.hasMVar'])
    (hoFu := by simp [Reflection.defn₂, TrExprS.IsUnique])
    (hasBfv := by simp [FVarsIn])
    (hasBu := by simp [TrExprS.IsUnique])
    (hasBb := rfl)
    (hprffv := by simp [FVarsIn, Lean.Level.hasMVar'])
    (hprfu := by simp [TrExprS.IsUnique])
    (hprfb := rfl)
    (hg := fun h a b => by
      cases trExprS_const_nil_inv' h; exact c.hasPrimitives.natBEq hbeq a b)).mono
    fun _ _ _ h => ?_
  obtain ⟨P, D, hP, hD, hPc, hDc, hite, hdite⟩ := h
  refine ⟨P, D, hP, hD, hPc, hDc, hite, fun hd => ?_⟩
  obtain ⟨FD, OT, OF, PR, h1, h2, h3, -, h5⟩ := hdite hd
  exact ⟨FD, OT, OF, PR, h1, h2, h3, h5⟩


theorem primitives_natBLE : Environment.primitives.contains ``Nat.ble = true := by
  simpa using primitives_contains_iff.2 (by simp)

open Lean4Lean.Environment in
/-- **The collapse test for the `Nat.mod` / `Nat.div` branches.**  `Condition.check.WF_natLE`'s
existential `P` and `D` are pinned to the abstract terms those branches actually carry:
`P = VExpr.natLE`, because `Condition.natLE.prop` is `@LE.le Nat instLENat`, and
`D = .const ``Nat.decLe []`.  Both branches build their conditionals with
`Condition.ite` / `Condition.dite`, i.e. with `cond.prop` and `cond.dec` in exactly those two
slots, so this is the form `VEnv.reflects_fuel_mod` / `_div` consume. -/
theorem Condition.check.WF_natLE_pinned {s : VState} {fail : ∀ {α}, TypeChecker.M α}
    {iteTypes : List Lean.Expr} {dite : Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = []) (hsafe : c.safety = .safe)
    (hnat : c.venv.contains ``Nat) (hnatty : c.venv.IsType 0 [] .nat)
    (hbleE : c.env.contains ``Nat.ble = true)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (Condition.natLE.check fail iteTypes dite) fun _ _ =>
      (∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
        c.venv.ReflectsCondApp F .natLE (.const ``Nat.decLe []) Nat.ble) ∧
      (dite = true → ∃ FD OT OF PR,
        c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
        c.TrExprS Reflection.defn₁.ofTrue OT ∧ c.TrExprS Reflection.defn₁.ofFalse OF ∧
        c.venv.ReflectsCondAppD FD .natLE (.const ``Nat.decLe []) OT OF PR Nat.ble) := by
  refine (Condition.check.WF_natLE hfail hnil hlp hnat hnatty
    (contains_primConst hsafe hbleE primitives_natBLE) hitefv).mono fun _ _ _ h => ?_
  obtain ⟨P, D, hP, hD, -, -, hite, hdite⟩ := h
  cases trExprS_natLE_inv' (Us := c.lparams) (Δ := c.vlctx) hP
  cases trExprS_const_nil_inv' (Us := c.lparams) (Δ := c.vlctx) hD
  exact ⟨hite, hdite⟩

end TypeChecker

/-! ## `Condition.check`'s `.bool` arm

`Condition.bool` has no `Reflection` layer: its scrutinee is a `Bool` and the recognizer checks
the two selections directly, so the abstract statement is `VEnv.ReflectsCondApp1` (two binders,
`t` and `e`) rather than `VEnv.ReflectsCondApp` (four).  Everything the statement needs is
established *before* the `iteTypes` loop, so unlike the `.reflectNatNat` arm the reflection fact
is assembled inside the loop body rather than after it.

The arm ends in `if dite then throw …`, so the `dite = true` case is discharged by
`M.WF.throw` and the conclusion carries no `dite` clause. -/

namespace VEnv
variable {env : VEnv}

/-- **`ReflectsCondApp1` from the shape `Condition.check`'s `.bool` arm leaves behind.**  Two
binders, not four: there is no `Reflection` layer, so the scrutinee is the boolean literal
itself and only `t` and `e` are abstracted. -/
theorem reflectsCondApp1_of_checkBoolITE (henv : env.WF) {F P D Aα : VExpr}
    (hFc : F.ClosedN 0) (hPc : P.ClosedN 0) (hDc : D.ClosedN 0) (hA0 : Aα.ClosedN 0)
    {Dc : VExpr}
    (hF : env.HasType 0 [] F (.forallE (.sort .zero) (.forallE Dc (.forallE Aα (.forallE Aα Aα)))))
    (h : ∀ v : Bool, env.IsDefEqU 0 [Aα, Aα]
      (VExpr.condApp F (.app P (.boolLit v)) (.app D (.boolLit v)) (.bvar 1) (.bvar 0))
      (bif v then .bvar 1 else .bvar 0)) :
    env.ReflectsCondApp1 F P D := by
  intro v t e hwt
  obtain ⟨-, -, ht, he⟩ := condApp_typed henv hA0 hF hwt
  have cl : ∀ {u T : VExpr}, env.HasType 0 [] u T → ∀ (w : VExpr) (j : Nat), u.inst w j = u :=
    fun hu _ _ => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).instN_eq (Nat.zero_le _)
  have lf : ∀ {u T : VExpr}, env.HasType 0 [] u T → ∀ j : Nat, u.liftN j = u :=
    fun hu _ => (VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial).liftN_eq (Nat.zero_le _)
  have eF : ∀ (w : VExpr) (j : Nat), F.inst w j = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
  have eP : ∀ (w : VExpr) (j : Nat), P.inst w j = P := fun _ _ => hPc.instN_eq (Nat.zero_le _)
  have eD : ∀ (w : VExpr) (j : Nat), D.inst w j = D := fun _ _ => hDc.instN_eq (Nat.zero_le _)
  have et := cl ht; have ee := cl he; have lt := lf ht; have le' := lf he
  have key := IsDefEqU.inst2 (A := Aα) (B := Aα) (a := t) (b := e) henv (h v) ht he
  cases v <;>
    simpa [VExpr.condApp, VExpr.inst, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar,
      eF, eP, eD, et, ee, lt, le'] using key

end VEnv

namespace TypeChecker
variable {c : VContext}

set_option maxHeartbeats 1000000 in
theorem Condition.checkBoolITEHalf.WF {s : VState}
    {cond : Lean4Lean.Environment.Condition} {α : Lean.Expr} {v : Bool} {bn : Name}
    {sel : Lean.Expr → Lean.Expr → Lean.Expr} {fail : ∀ {β}, TypeChecker.M β}
    {P D F Aα : VExpr}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hbn : ∀ {Δ : VLCtx} {X : VExpr},
      TrExprS c.venv c.lparams Δ (.const bn []) X → X = VExpr.boolLit v)
    (hsel : ∀ t e : Lean.Expr, sel t e = bif v then t else e)
    (hα : c.TrExprS α Aα) (hαu : TrExprS.IsUnique α) (hAc : Aα.ClosedN 0)
    (hP : c.TrExprS cond.prop P) (hPu : TrExprS.IsUnique cond.prop) (hPc : P.ClosedN 0)
    (hD : c.TrExprS cond.dec D) (hDu : TrExprS.IsUnique cond.dec) (hDc : D.ClosedN 0)
    (hF : c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F) (hFc : F.ClosedN 0) :
    M.WF c s (cond.checkBoolITEHalf α (.const bn []) sel fail) fun _ _ =>
      c.venv.IsDefEqU 0 [Aα, Aα]
        (VExpr.condApp F (.app P (VExpr.boolLit v)) (.app D (VExpr.boolLit v))
          (.bvar 1) (.bvar 0))
        (bif v then .bvar 1 else .bvar 0) := by
  unfold Lean4Lean.Environment.Condition.checkBoolITEHalf
  refine M.WF.withCheckedLocalDecl (by exact hα.fvarsIn) fun AT₁ idt cwft s1 _ hAT₁ _ => ?_
  cases TrExprS.unique hαu hAT₁ hα
  have hα1 := TrExprS.weakLam0 cwft hα hAc
  have hP1 := TrExprS.weakLam0 cwft hP hPc
  have hD1 := TrExprS.weakLam0 cwft hD hDc
  have hF1 := TrExprS.weakLam0 cwft hF hFc
  refine M.WF.withCheckedLocalDecl (by exact hα1.fvarsIn) fun AT₂ ide cwfe s2 _ hAT₂ _ => ?_
  cases TrExprS.unique hαu hAT₂ hα1
  have hP2 := TrExprS.weakLam0 cwfe hP1 hPc
  have hD2 := TrExprS.weakLam0 cwfe hD1 hDc
  have hF2 := TrExprS.weakLam0 cwfe hF1 hFc
  have ht2 := TrExprS.weakLift0 cwfe (trExprS_lastFVar0 cwft)
  have he2 := trExprS_lastFVar0 cwfe
  simp only [VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, show ¬ (0:Nat) < 0 by omega,
    if_false, Nat.reduceAdd] at ht2
  refine M.WF.bind (checkedIsDefEq.WFl (b' := bif v then .bvar 1 else .bvar 0)
    ⟨⟨⟨⟨hF2.fvarsIn, ⟨hP2.fvarsIn, by simp [FVarsIn]⟩⟩,
        ⟨hD2.fvarsIn, by simp [FVarsIn]⟩⟩, ht2.fvarsIn⟩, he2.fvarsIn⟩
    (by rw [hsel]; cases v; exacts [he2, ht2])) fun b _ _ hb => ?_
  obtain ⟨LHS, hLHS, hdd⟩ := hb
  split
  case isFalse => exact hfail
  rename_i hbt
  have hdefeq := hdd (by simpa using hbt)
  obtain ⟨_, _, rfl, n3, n4⟩ := trExprS_app_inv' hLHS
  cases TrExprS.unique (e := Lean.Expr.fvar ide) trivial n4 he2
  obtain ⟨_, _, rfl, m3, m4⟩ := trExprS_app_inv' n3
  cases TrExprS.unique (e := Lean.Expr.fvar idt) trivial m4 ht2
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' m3
  obtain ⟨_, _, rfl, j3, j4⟩ := trExprS_app_inv' k3
  obtain ⟨_, _, rfl, i3, i4⟩ := trExprS_app_inv' j4
  cases hbn i4
  cases TrExprS.unique hPu i3 hP2
  cases TrExprS.unique
    (e := Lean.mkApp (.const ``ite [.succ .zero]) α) ⟨trivial, hαu⟩ j3 hF2
  obtain ⟨_, _, rfl, g3, g4⟩ := trExprS_app_inv' k4
  cases hbn g4
  cases TrExprS.unique hDu g3 hD2
  refine .pure ?_
  simpa [VContext.IsDefEqU, VContext.withMLC, VLCtx.toCtx, hlp, hnil, VExpr.condApp]
    using hdefeq

end TypeChecker

namespace TypeChecker
variable {c : VContext}

set_option maxHeartbeats 1000000 in
theorem Condition.check.WF_bool {s : VState} {cond : Lean4Lean.Environment.Condition}
    {iteTypes : List Lean.Expr} {dite : Bool} {fail : ∀ {α}, TypeChecker.M α}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (himpl : cond.impl = .bool)
    (hdecfv : cond.dec.FVarsIn (· ∈ c.vlctx.fvars)) (hdecu : TrExprS.IsUnique cond.dec)
    (hpropfv : cond.prop.FVarsIn (· ∈ c.vlctx.fvars)) (hpropu : TrExprS.IsUnique cond.prop)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (cond.check fail iteTypes dite) fun _ _ =>
      ∃ P D, c.TrExprS cond.prop P ∧ c.TrExprS cond.dec D ∧ P.ClosedN 0 ∧ D.ClosedN 0 ∧
        ∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
          c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
          c.venv.ReflectsCondApp1 F P D := by
  have hctx : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  have hUs : c.lparams.length = 0 := by rw [hlp]; rfl
  have raw : ∀ {e A : VExpr}, c.HasType e A → c.venv.HasType 0 [] e A := by
    intro e A h; rwa [VContext.HasType, hctx, hUs] at h
  unfold Lean4Lean.Environment.Condition.check
  simp only []
  refine M.WF.bind (checkType.WF hdecfv) fun _ _ _ hDo => ?_
  obtain ⟨D, DA, -, hD, -, hDty⟩ := hDo
  have hDc := (closedN_of_nil hnil hDty).1
  rw [himpl]
  refine M.WF.bind (checkedTypeIs.WF hpropfv (by exact ⟨by simp [FVarsIn], rfl⟩))
    fun _ _ _ hPo => ?_
  obtain ⟨P, PA, -, hP, hPA, -, -⟩ := hPo
  have hPc := (closedN_of_nil hnil hPA).1
  split
  case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
  refine M.WF.bind (M.WF.forIn
    (Inv := fun (vs : List Lean.Expr) (_ : PUnit) (_ : VState) => ∃ pre, iteTypes = pre ++ vs ∧
      ∀ α ∈ pre, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
        c.venv.ReflectsCondApp1 F P D)
    (fun α vs _ _ hinv => ?_) ⟨[], rfl, by simp⟩) fun _ _ _ hloop => ?_
  · obtain ⟨pre, hpre, hall⟩ := hinv
    obtain ⟨hαfv, hαu, hαb⟩ := hitefv α (by rw [hpre]; simp)
    refine (checkIsType.WF hαfv).bind fun _ _ _ hAo => ?_
    obtain ⟨Aα, hAα, u, hAu'⟩ := hAo
    have hAc := (closedN_of_nil hnil hAu').1
    refine M.WF.bind (checkedTypeIs.WF ⟨by simp [FVarsIn]; rfl, hαfv⟩
      ⟨by exact rfl, ⟨⟨by simp [FVarsIn], trivial⟩, ⟨hαfv, ⟨hαfv, hαfv⟩⟩⟩⟩) fun _ _ _ hFo => ?_
    obtain ⟨F, FA, FT, hF, hFA, hFT, hFd⟩ := hFo
    split
    case isFalse => exact M.WF.bind (Q := fun _ _ => False) hfail nofun
    rename_i hb
    cases trExprS_iteHeadType_inv' c.Ewf.ordered hAα hαu hαb hAc hFT
    have hFty := hFA.defeqU_r c.Ewf c.Δwf.toCtx (hFd (by simpa using hb))
    have hFc := (closedN_of_nil hnil hFty).1
    refine M.WF.bind (Condition.checkBoolITEHalf.WF (v := true) (bn := ``Bool.true) hfail hnil hlp
        (fun h => trExprS_const_nil_inv' h) (fun _ _ => rfl)
        hAα hαu hAc hP hpropu hPc hD hdecu hDc hF hFc) fun _ _ _ htrue => ?_
    refine (Condition.checkBoolITEHalf.WF (v := false) (bn := ``Bool.false) hfail hnil hlp
        (fun h => trExprS_const_nil_inv' h) (fun _ _ => rfl)
        hAα hαu hAc hP hpropu hPc hD hdecu hDc hF hFc).bind fun _ _ _ hfalse => ?_
    refine .pure ⟨_, rfl, pre ++ [α], by simp [hpre], ?_⟩
    intro β hβ
    rcases List.mem_append.1 hβ with hβ | hβ
    · exact hall β hβ
    · cases List.mem_singleton.1 hβ
      have hFty' : c.venv.HasType 0 [] F (.forallE (.sort .zero)
          (.forallE (.app (.const ``Decidable []) (.bvar 0))
            (.forallE Aα (.forallE Aα Aα)))) := raw hFty
      exact ⟨Aα, F, hAα, hAc, hF, hFc, VEnv.reflectsCondApp1_of_checkBoolITE c.Ewf hFc hPc hDc
        hAc hFty' fun v => by cases v; exacts [hfalse, htrue]⟩
  obtain ⟨pre, hpre, hloop'⟩ := hloop
  rw [List.append_nil] at hpre
  subst hpre
  split
  · exact M.WF.throw
  · exact .pure ⟨P, D, hP, hD, hPc, hDc, hloop'⟩


open Lean4Lean.Environment in
/-- Acceptance: every hypothesis of `Condition.check.WF_bool` is dischargeable at
`Condition.bool`, the only `.bool` condition the recognizer ships (`Nat.bitwise` and
`unfoldNatWellFounded` use it). -/
theorem Condition.check.WF_boolCond {s : VState} {fail : ∀ {α}, TypeChecker.M α}
    {iteTypes : List Lean.Expr} {dite : Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = [])
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (Condition.bool.check fail iteTypes dite) fun _ _ =>
      ∃ P D, c.TrExprS Condition.bool.prop P ∧ c.TrExprS Condition.bool.dec D ∧
        P.ClosedN 0 ∧ D.ClosedN 0 ∧
        ∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
          c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
          c.venv.ReflectsCondApp1 F P D :=
  Condition.check.WF_bool (cond := Condition.bool) hfail hnil hlp rfl
    (by simp [Condition.bool, FVarsIn]) (by simp [Condition.bool, TrExprS.IsUnique])
    (by simp [Condition.bool, FVarsIn, Lean.Level.hasMVar'])
    (by simp [Condition.bool, TrExprS.IsUnique])
    hitefv

end TypeChecker

namespace TypeChecker
variable {c : VContext}

/-- `NatFacts.isType` in the raw form `Condition.check.WF` (and `VEnv.IsDefEqU.lam2_beta`
underneath it) consumes.  `NatFacts` states it with the `VContext` abbrevs, which at an abstract
`c` with only *propositional* `hnil` / `hlp` are not syntactically `0` and `[]`. -/
theorem NatFacts.isType0 (h : NatFacts c) (hnil : c.vlctx = []) (hlp : c.lparams = []) :
    c.venv.IsType 0 [] VExpr.nat := by
  have := h.isType
  rwa [VContext.IsType, show c.vlctx.toCtx = [] by rw [hnil]; rfl,
    show c.lparams.length = 0 by rw [hlp]; rfl] at this

end TypeChecker
