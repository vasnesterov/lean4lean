import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.EnvLemmas

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

* `VEnv.HasPrimitives.natLit_hasType` — numerals are `Nat`s;
* `IsDefEqU.app_congr_arg`, `IsDefEqU.app2_congr_arg1`, `IsDefEqU.app_congr_fn` — congruence
  that extracts the typing it needs from the equation it is chaining onto, so no separate
  hypothesis about the type of the operator is required;
* `VEnv.reflects_rec2`, `VEnv.reflects_rec2_tail`, `VEnv.reflects_rec2_diag` — the three
  recursion shapes the nine operations fall into.

A finished branch therefore reads, e.g. for `Nat.add`,

    VEnv.ReflectsNatNatNat.of_defeq henv hprim hnat hFty hdef
      (VEnv.reflects_natAdd henv hprim hnat h0 hS)

where `h0`/`hS` come from `IsDefEqU.instNat`/`IsDefEqU.instNat2`; the resulting `VExpr.inst`
applications are computed by `simp [VExpr.inst]` together with the `@[simp]` lemmas below and
`VExpr.ClosedN.instN_eq` for the value `F` itself (which is closed, by `IsDefEq.closedN`
applied to `hFty`).

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

theorem IsDefEqU.instNat (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {Γ : List VExpr} {e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 (.nat :: Γ) e₁ e₂) (n : Nat) :
    env.IsDefEqU 0 Γ (e₁.inst (.natLit n)) (e₂.inst (.natLit n)) :=
  IsDefEqU.instN henv.ordered .zero H (hprim.natLit_hasType hnat n)

/-- Two nested `withLocalDecl`s.  `checkPrimitiveDef`'s `defeq2` introduces its `y` binder
first, so `bvar 1` is `y` and `bvar 0` is the inner `x`: here `n` is substituted for `bvar 0`
and `m` for `bvar 1`. -/
theorem IsDefEqU.instNat2 (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {e₁ e₂ : VExpr}
    (H : env.IsDefEqU 0 [.nat, .nat] e₁ e₂) (m n : Nat) :
    env.IsDefEqU 0 [] ((e₁.inst (.natLit n)).inst (.natLit m))
      ((e₂.inst (.natLit n)).inst (.natLit m)) :=
  (H.instNat henv hprim hnat n).instNat henv hprim hnat m

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

theorem ReflectsNatNat.of_defeq (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {fc : Name} {F : VExpr} {g : Nat → Nat}
    (hFty : env.HasType 0 [] F (.forallE .nat .nat))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a, env.IsDefEqU 0 [] (.app F (.natLit a)) (.natLit (g a))) :
    env.ReflectsNatNat fc g := by
  intro _ a
  refine IsDefEqU.trans henv trivial ?_ (H a)
  exact IsDefEqU.app_congr_fn henv hdef hFty (hprim.natLit_hasType hnat a)

theorem ReflectsNatNatNat.of_defeq (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {fc : Name} {F : VExpr} {g : Nat → Nat → Nat}
    (hFty : env.HasType 0 [] F (.forallE .nat (.forallE .nat .nat)))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (g a b))) :
    env.ReflectsNatNatNat fc g := by
  intro _ a b
  refine IsDefEqU.trans henv trivial ?_ (H a b)
  have h1 : env.IsDefEqU 0 [] (.app (.const fc []) (.natLit a)) (.app F (.natLit a)) :=
    IsDefEqU.app_congr_fn henv hdef hFty (hprim.natLit_hasType hnat a)
  have h2 : env.HasType 0 [] (.app F (.natLit a)) (.forallE .nat .nat) := by
    have := hFty.app (hprim.natLit_hasType hnat a)
    rwa [VExpr.inst, VExpr.inst_nat, VExpr.inst_nat] at this
  exact IsDefEqU.app_congr_fn henv h1 h2 (hprim.natLit_hasType hnat b)

theorem ReflectsNatNatBool.of_defeq (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {fc : Name} {F : VExpr} {g : Nat → Nat → Bool}
    (hFty : env.HasType 0 [] F (.forallE .nat (.forallE .nat .bool)))
    (hdef : env.IsDefEqU 0 [] (.const fc []) F)
    (H : ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.boolLit (g a b))) :
    env.ReflectsNatNatBool fc g := by
  intro _ a b
  refine IsDefEqU.trans henv trivial ?_ (H a b)
  have h1 : env.IsDefEqU 0 [] (.app (.const fc []) (.natLit a)) (.app F (.natLit a)) :=
    IsDefEqU.app_congr_fn henv hdef hFty (hprim.natLit_hasType hnat a)
  have h2 : env.HasType 0 [] (.app F (.natLit a)) (.forallE .nat .bool) := by
    have := hFty.app (hprim.natLit_hasType hnat a)
    rwa [VExpr.inst, VExpr.inst_nat, VExpr.inst_bool] at this
  exact IsDefEqU.app_congr_fn henv h1 h2 (hprim.natLit_hasType hnat b)

end VEnv

/-! ## The nine operations

Each hypothesis is written in exactly the shape `Lean4Lean.Environment.checkPrimitiveDef`
produces after `IsDefEqU.instNat`/`IsDefEqU.instNat2`: `zero` is `VExpr.natZero`, `succ e` is
`.app VExpr.natSucc e`, and in `defeq2` the *outer* binder `y` is the first argument. -/

namespace VEnv

variable {env : VEnv}

/-- `Nat.add`: `add x 0 ≡ x` and `add y (succ x) ≡ succ (add y x)`. -/
theorem reflects_natAdd (henv : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app .natSucc (.app (.app F (.natLit a)) (.natLit b)))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.add a b)) := by
  refine reflects_rec2 henv (S := fun _ e => .app .natSucc e) (g := Nat.add) h0 hS ?_
  intro a b e he
  refine IsDefEqU.app_congr_arg henv (a := .natLit (Nat.add a b)) ?_ he
  exact ⟨_, hprim.natLit_hasType hnat (Nat.add a (b + 1))⟩

/-- `Nat.pred`: `pred 0 ≡ 0` and `pred (succ x) ≡ x`.  Not a recursion. -/
theorem reflects_natPred {F : VExpr}
    (h0 : env.IsDefEqU 0 [] (.app F .natZero) .natZero)
    (hS : ∀ a : Nat, env.IsDefEqU 0 [] (.app F (.app .natSucc (.natLit a))) (.natLit a)) :
    ∀ a, env.IsDefEqU 0 [] (.app F (.natLit a)) (.natLit (Nat.pred a))
  | 0 => h0
  | _ + 1 => hS _

/-- `Nat.sub`: `sub x 0 ≡ x` and `sub y (succ x) ≡ Nat.pred (sub y x)`. -/
theorem reflects_natSub (henv : env.WF) (hprim : env.HasPrimitives)
    (hpred : env.contains ``Nat.pred) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) (.natLit a))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.const ``Nat.pred []) (.app (.app F (.natLit a)) (.natLit b)))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.sub a b)) := by
  refine reflects_rec2 henv (S := fun _ e => .app (.const ``Nat.pred []) e) (g := Nat.sub)
    h0 hS ?_
  intro a b e he
  exact IsDefEqU.app_congr_arg henv (hprim.natPred hpred (Nat.sub a b)) he

/-- `Nat.mul`: `mul x 0 ≡ 0` and `mul y (succ x) ≡ Nat.add (mul y x) y`. -/
theorem reflects_natMul (henv : env.WF) (hprim : env.HasPrimitives)
    (hadd : env.contains ``Nat.add) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero) .natZero)
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app (.const ``Nat.add []) (.app (.app F (.natLit a)) (.natLit b))) (.natLit a))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.mul a b)) := by
  refine reflects_rec2 henv
    (S := fun a e => .app (.app (.const ``Nat.add []) e) (.natLit a)) (g := Nat.mul) h0 hS ?_
  intro a b e he
  exact IsDefEqU.app2_congr_arg1 henv (hprim.natAdd hadd (Nat.mul a b) a) he

/-- `Nat.pow`: `pow x 0 ≡ 1` and `pow y (succ x) ≡ Nat.mul (pow y x) y`. -/
theorem reflects_natPow (henv : env.WF) (hprim : env.HasPrimitives)
    (hmul : env.contains ``Nat.mul) {F : VExpr}
    (h0 : ∀ a : Nat, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) .natZero)
      (.app .natSucc .natZero))
    (hS : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app (.app F (.natLit a)) (.app .natSucc (.natLit b)))
      (.app (.app (.const ``Nat.mul []) (.app (.app F (.natLit a)) (.natLit b))) (.natLit a))) :
    ∀ a b, env.IsDefEqU 0 [] (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.pow a b)) := by
  refine reflects_rec2 henv
    (S := fun a e => .app (.app (.const ``Nat.mul []) e) (.natLit a)) (g := Nat.pow) h0 hS ?_
  intro a b e he
  exact IsDefEqU.app2_congr_arg1 henv (hprim.natMul hmul (Nat.pow a b) a) he

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
theorem reflects_natShiftLeft (henv : env.WF) (hprim : env.HasPrimitives)
    (hmul : env.contains ``Nat.mul) {F : VExpr}
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
  exact hprim.natMul hmul 2 a

/-- `Nat.shiftRight`: `shr x 0 ≡ x` and `shr x (succ y) ≡ Nat.div (shr x y) 2`. -/
theorem reflects_natShiftRight (henv : env.WF) (hprim : env.HasPrimitives)
    (hdiv : env.contains ``Nat.div) {F : VExpr}
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
  exact IsDefEqU.app2_congr_arg1 henv (hprim.natDiv hdiv (Nat.shiftRight a b) 2) he

end VEnv
