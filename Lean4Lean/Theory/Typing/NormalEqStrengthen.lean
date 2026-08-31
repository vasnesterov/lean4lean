import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.StrengthenNarrow

/-!
# `NormalEq`-strengthening needs only *type-level* conversion strengthening

(header written at the end)
-/

namespace Lean4Lean
namespace VEnv

open VExpr

section
variable {env : VEnv} {U : Nat}

/-! ## 1. The residual: conversion strengthening at a sort type -/

/-- **Type-level conversion strengthening.**  `Strengthening` (`Strengthen.lean` §2) with the
two endpoints required to be *types*: the shared type of the premise is a sort. -/
def SortConvStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr} {u : VLevel}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (.sort u) → env.IsDefEqU U Γ e1 e2

/-- The residual is a consequence of the hole, so nothing below assumes more than the hole. -/
theorem Strengthening.sortConv (H : Strengthening env U) : SortConvStrengthening env U :=
  fun W hΓ hΓ' h => H W hΓ hΓ' ⟨_, h⟩

end

section
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## 2. `NormalEq.weakN_inv_DFC` from the typing half plus the sort residual -/

theorem NormalEq.weakN_inv_DFC'
    (HT : TypingStrengthening env univs) (HS : SortConvStrengthening env univs)
    {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (IsType env univs))
    {n k : Nat} {Γ Γ₁ Γ₂ : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1.liftN n k ≡ₚ e2.liftN n k) : Γ ⊢ e1 ≡ₚ e2 := by
  generalize eq1 : e1.liftN n k = e1' at H
  generalize eq2 : e2.liftN n k = e2' at H
  induction H generalizing Γ Γ₂ e1 e2 k with
  | refl h =>
    cases eq2; cases liftN_inj.1 eq1
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h'⟩ := HT.wf_inv henv W hΓ₂ ⟨_, h.defeqDFC henv W₂⟩
    exact .refl h'
  | sortDF h1 h2 h3 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h1 := h1.defeqDFC henv W₂
    replace h3 := h3.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have hΓ := HT.onCtx_inv henv W hΓ₂
    have ⟨_, _, l1, l2⟩ :=
      let ⟨_, h⟩ := HT.wf_inv henv W hΓ₂ (e := .app ..) ⟨_, h1.app h3⟩
      HasType.app_inv henv hΓ h
    have hf := ih1 W W₂ rfl rfl
    have ha := ih2 W W₂ rfl rfl
    exact .appDF l1 ((hf.defeq hΓ).of_l henv hΓ l1).hasType.2
      l2 ((ha.defeq hΓ).of_l henv hΓ l2).hasType.2 hf ha
  | lamDF h1 h2 _ ih1 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have hΓ := HT.onCtx_inv henv W hΓ₂
    have hup := IsDefEq.defeqDFC henv W₂ (h2.symm.trans h1)
    have ⟨_, hA₂⟩ := TypingStrengthening.sortDescend henv HT W hΓ hΓ₂ hup.hasType.1
      (HT.wf_inv henv W hΓ₂ ⟨_, hup.hasType.1⟩)
    have this' := (HS W hΓ hΓ₂ hup).of_l henv hΓ hA₂
    exact .lamDF this' this'.hasType.1 (ih1 W.succ (W₂.succ h2) rfl rfl)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂' := ((W₂.succ h1).symm henv).isType' hΓ₀
    have h3' := h3.defeqDFC henv (W₂.succ h1)
    replace h4 := HT.hasType_inv henv (A := .sort _) W.succ hΓ₂' h3'
    have := HT.hasType_inv henv (A := .sort _) W hΓ₂'.1
      (IsDefEq.defeqDFC henv W₂ h1.hasType.2)
    exact .forallEDF this (ih1 W W₂ rfl rfl) h4 (ih2 W.succ (W₂.succ h1) rfl rfl)
  | etaL h1 _ ih =>
    cases e1 <;> cases eq1
    subst eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := HT.wf_inv henv W.succ hΓ₂' ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := HT.hasType_inv henv (A := .forallE ..) W hΓ₂'.1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaL this (ih W.succ (W₂.succ hA) rfl (by simp [liftN, lift_liftN']))
  | etaR h1 _ ih =>
    subst eq1
    cases e2 <;> cases eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := HT.wf_inv henv W.succ hΓ₂' ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := HT.hasType_inv henv (A := .forallE ..) W hΓ₂'.1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaR this (ih W.succ (W₂.succ hA) (by simp [liftN, lift_liftN']) rfl)
  | proofIrrel h1 h2 h3 =>
    subst eq1; subst eq2
    have h1' := h1.defeqDFC henv W₂
    have h2' := h2.defeqDFC henv W₂
    have h3' := h3.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h⟩ := HT.wf_inv henv W hΓ₂ ⟨_, h2'⟩
    have ⟨_, hw⟩ := h2'.uniq henv hΓ₂ (h.weakN henv W)
    exact .proofIrrel
      (HT.hasType_inv henv (A := .sort _) W hΓ₂ (h1'.defeqU_l henv hΓ₂ ⟨_, hw⟩))
      (HT.hasType_inv henv W hΓ₂ (hw.defeq h2'))
      (HT.hasType_inv henv W hΓ₂ (hw.defeq h3'))

end
