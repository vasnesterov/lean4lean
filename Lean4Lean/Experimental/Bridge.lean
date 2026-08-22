import Lean4Lean.Experimental.SExpr

/-!
# Forward translation `VExpr → SExpr`

`SExpr.mk` (`Lean4Lean/Experimental/SExpr.lean`) maps a `VExpr` to the corresponding
`SExpr`, replacing each `VLevel` by its semantic quotient `SLevel`. This file proves that
`mk` commutes with lifting, instantiation and level-instantiation, and that it is a
*simulation*: every `VEnv.IsDefEq` derivation maps to an `SExpr.IsDefEq` derivation.

This is the direction of the bridge that needs nothing from `SExpr` beyond the definitions
— in particular it consumes none of `SExpr.lean`'s open declarations, and no `sorry`.

The two `VLevel` congruence rules (`sortDF`, `constDF`) become *reflexivity* on the
`SExpr` side, because `SLevel.mk` identifies exactly the `≈`-equivalent levels
(`SLevel.mk_inj`). That is the whole point of the `SExpr` calculus.

`Params.univs` plays no role here: `SLevel` records only "is the evaluation of *some*
`VLevel`", so the `SExpr` judgment imposes no level well-formedness conditions and no
hypothesis relating `U` to `Params.univs` is needed.
-/

namespace Lean4Lean

open Lean4Lean Params

variable [Params]

/-! ## Levels -/

namespace SLevel

@[simp] theorem mk_zero : mk .zero = .zero := rfl

theorem mk_inj {u v : VLevel} : mk u = mk v ↔ u ≈ v :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- `SLevel.mk` identifies `≈`-equivalent levels: this is what makes the `sortDF` and
`constDF` congruences collapse to reflexivity in `SExpr`. -/
theorem mk_congr {u v : VLevel} (h : u ≈ v) : mk u = mk v := mk_inj.2 h

@[simp] theorem mk_succ {u : VLevel} : mk u.succ = (mk u).succ := rfl

@[simp] theorem mk_max {u v : VLevel} : mk (.max u v) = (mk u).max (mk v) := rfl

@[simp] theorem mk_imax {u v : VLevel} : mk (.imax u v) = (mk u).imax (mk v) := rfl

theorem mk_list_congr {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    ls.map mk = ls'.map mk := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [mk_congr h, ih]

@[simp] theorem mk_inst {u : VLevel} {ls : List VLevel} :
    mk (u.inst ls) = (mk u).inst (ls.map mk) := by
  refine Subtype.ext (funext fun v => ?_)
  simp only [val_mk, SLevel.inst, VLevel.eval_inst, List.map_map]
  rfl

end SLevel

/-! ## Expressions -/

namespace SExpr

@[simp] theorem mk_bvar {i : Nat} : mk (.bvar i) = .bvar i := rfl
@[simp] theorem mk_sort {u : VLevel} : mk (.sort u) = .sort (.mk u) := rfl
@[simp] theorem mk_const {c : Name} {us : List VLevel} :
    mk (.const c us) = .const c (us.map .mk) := rfl
@[simp] theorem mk_app {f a : VExpr} : mk (.app f a) = .app (mk f) (mk a) := rfl
@[simp] theorem mk_lam {A e : VExpr} : mk (.lam A e) = .lam (mk A) (mk e) := rfl
@[simp] theorem mk_forallE {A B : VExpr} : mk (.forallE A B) = .forallE (mk A) (mk B) := rfl

@[simp] theorem mk_lift' {e : VExpr} {ρ : Lift} : mk (e.lift' ρ) = (mk e).lift' ρ := by
  induction e generalizing ρ <;> simp [VExpr.lift', SExpr.lift', mk, *]

@[simp] theorem mk_lift {e : VExpr} : mk e.lift = (mk e).lift := by
  rw [VExpr.lift_eq_lift', SExpr.lift, mk_lift']

@[simp] theorem mk_instL {e : VExpr} {ls : List VLevel} :
    mk (e.instL ls) = (mk e).instL (ls.map .mk) := by
  induction e <;>
    simp [VExpr.instL, SExpr.instL, mk, List.map_map, Function.comp_def, *]

/-- Generalised commutation of `mk` with instantiation: any `SExpr.Subst` agreeing
pointwise with `VExpr.instVar` transports. -/
theorem mk_inst_of {a : VExpr} : ∀ {e : VExpr} {k : Nat} {σ : Subst},
    (∀ i, mk (VExpr.instVar i a k) = σ i) → mk (e.inst a k) = (mk e).subst σ := by
  intro e
  induction e with intro k σ hσ
  | bvar i => exact hσ i
  | sort | const => rfl
  | app _ _ ih1 ih2 => simp [VExpr.inst, SExpr.subst, ih1 hσ, ih2 hσ]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    have hσ' : ∀ i, mk (VExpr.instVar i a (k + 1)) = σ.lift i := fun i =>
      match i with
      | 0 => rfl
      | i+1 => by rw [VExpr.instVar_succ, mk_lift, hσ i]; rfl
    simp [VExpr.inst, SExpr.subst, ih1 hσ, ih2 hσ']

@[simp] theorem mk_inst {e a : VExpr} : mk (e.inst a) = (mk e).inst (mk a) := by
  show mk (e.inst a) = (mk e).subst (.one (mk a))
  refine mk_inst_of fun i => ?_
  match i with
  | 0 => rw [VExpr.instVar_zero]; rfl
  | _+1 => rw [VExpr.instVar_upper]; rfl

end SExpr

/-! ## Contexts -/

theorem Lookup.toSExpr {Γ : List VExpr} {i : Nat} {A : VExpr} (H : Lookup Γ i A) :
    SExpr.Lookup (Γ.map SExpr.mk) i (SExpr.mk A) := by
  induction H with
  | zero => exact SExpr.mk_lift ▸ .zero
  | succ _ ih => exact SExpr.mk_lift ▸ .succ ih

/-! ## The simulation -/

open SExpr in
/--
**Forward simulation.** Every `VEnv.IsDefEq` derivation in the environment carried by the
`Params` instance maps to an `SExpr.IsDefEq` derivation under `SExpr.mk`.
-/
theorem VEnv.IsDefEq.toSExpr {Γ : List VExpr} {e₁ e₂ A : VExpr} {U : Nat}
    (H : Params.env.IsDefEq U Γ e₁ e₂ A) :
    SExpr.IsDefEq (Γ.map SExpr.mk) (SExpr.mk e₁) (SExpr.mk e₂) (SExpr.mk A) := by
  induction H with
  | bvar h => exact .bvar h.toSExpr
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    simp only [mk_sort, SLevel.mk_succ, SLevel.mk_congr h3]; exact .sort
  | constDF h1 _ _ h4 h5 =>
    rw [mk_const, mk_const, ← SLevel.mk_list_congr h5, mk_instL]
    exact .const h1 (by rw [List.length_map]; exact h4)
  | appDF _ _ ih1 ih2 => rw [mk_app, mk_app, mk_inst]; exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => rw [mk_lam, mk_lam, mk_forallE]; exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 =>
    rw [mk_forallE, mk_forallE, mk_sort, SLevel.mk_imax]; exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => rw [mk_app, mk_lam, mk_inst, mk_inst]; exact .beta ih1 ih2
  | eta _ ih => rw [mk_lam, mk_app, mk_lift]; exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 _ h3 =>
    rw [mk_instL, mk_instL, mk_instL]
    exact .extra h1 (by simpa using h3)

/-- A well-formed `VExpr` context maps to a well-formed `SExpr` context. This makes the
`Ctx.WF` hypothesis of the `SExpr`-side injectivity results free on the `VExpr` side: the
statements in `Theory/Typing/Injectivity.lean` already carry `OnCtx Γ (env.IsType U)`. -/
theorem _root_.Lean4Lean.OnCtx.toSExpr : ∀ {Γ : List VExpr} {U : Nat},
    OnCtx Γ (Params.env.IsType U) → SExpr.Ctx.WF (Γ.map SExpr.mk)
  | [], _, _ => trivial
  | _::_, _, ⟨h1, _, h2⟩ => ⟨h1.toSExpr, _, VEnv.IsDefEq.toSExpr h2⟩

theorem VEnv.HasType.toSExpr {Γ : List VExpr} {e A : VExpr} {U : Nat}
    (H : Params.env.HasType U Γ e A) :
    SExpr.IsDefEq (Γ.map SExpr.mk) (SExpr.mk e) (SExpr.mk e) (SExpr.mk A) :=
  IsDefEq.toSExpr H

theorem VEnv.IsDefEqU.toSExpr {Γ : List VExpr} {e₁ e₂ : VExpr} {U : Nat}
    (H : Params.env.IsDefEqU U Γ e₁ e₂) :
    ∃ A, SExpr.IsDefEq (Γ.map SExpr.mk) (SExpr.mk e₁) (SExpr.mk e₂) A :=
  let ⟨_, H⟩ := H; ⟨_, IsDefEq.toSExpr H⟩

end Lean4Lean
