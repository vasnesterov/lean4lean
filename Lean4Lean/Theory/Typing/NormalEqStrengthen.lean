import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.StrengthenNarrow

/-!
# `NormalEq`-strengthening needs only the *typing* half

`IsDefEqU.weakN_iff` (`UniqueTyping.lean:174`, **296 transitive users** at `d67375b`) is the largest hole in
the theory half of this development: if `e1.liftN n k ≡ e2.liftN n k` upstairs then `e1 ≡ e2`
downstairs.  `Strengthen.lean` §§1-9 and `StrengthenNarrow.lean` located the whole difficulty in
one of `IsDefEq`'s twelve rules: `trans`, whose middle term lives upstairs and need not be in the
image of the lift.  Everything else strengthens by structural induction.

`NormalEq` (`ChurchRosser.lean:165`) is the conversion relation with **no `trans` constructor**:
nine constructors, `refl sortDF constDF appDF lamDF forallEDF etaL etaR proofIrrel`
(`NormalEq.trans` at `:481` is a theorem, and its proof needs confluence).  So the induction that
`Strengthening` cannot complete, `NormalEq`-strengthening *can* — provided the conversion
premises carried inside the `NormalEq` constructors can themselves be strengthened.  This file
carries that out and measures the result.

## What is proved

* §1 `SortConvStrengthening`: `Strengthening` restricted to premises typed by a **sort**.
* §1b `SortConvStrengthening.of_typing`: **it follows from the typing half.**  Given
  `A₂↑ ≡ A₁↑ : Sort u` upstairs, the identity function `fun (_ : A₂) => bvar 0` can be retyped
  by `defeqDF` at `A₁ → A₁` — a *typing* judgment both of whose sides are lifts — so
  `TypingStrengthening` descends it, and `uniqU` + `forallE_inv` downstairs recovers `A₂ ≡ A₁`.
  A conversion between *types* is encodable in a typing judgement because `forallE` has slots
  that take types; §4's `sortConv_encoding_vacuous` shows why the same move cannot encode a
  conversion between general *terms*, which is exactly why `TransStrengtheningNarrow` survives.
* §1c `TransStrengtheningNarrow.at_sort`: hence every **sort-typed** instance of
  `StrengthenNarrow.lean`'s residual — where 253 of the 296 users sit — is closed by the typing
  half.
* §2 `NormalEq.weakN_inv_DFC'`: `ChurchRosser.lean:361` reproved from `TypingStrengthening` plus
  §1's residual, with `IsDefEqU.weakN_iff` nowhere in the proof.  `appDF`'s genuine conversion
  use is *eliminated* rather than weakened (see the section comment).
* §3 `NormalEq.weakN_inv_DFC_of_typing`, `NormalEq.weakN_iff_of_typing`: §1b discharges the
  residual, so `TypingStrengthening` alone suffices.  Then, with confluence as the **explicit**
  hypothesis `NormalEqComplete`, `StrengtheningTarget.of_normalEqComplete` and
  `StrengtheningTarget.iff_piDescend_of_normalEqComplete` close the hole itself.
* §4 negative controls: §2 subsumes the original, `NormalEqComplete` is load-bearing, and the
  term-level encoding is vacuous.

## Honest statement of the consequence

`TypingStrengthening` has **no unconditional inhabitant in this tree** — by
`TypingStrengthening.iff_piDescend` it is equivalent to `PiDescend`, still open.  So the result
is "`NormalEq`-strengthening reduces to `PiDescend`", *not* "the hole is closed".

The reduction removes **one of the two** entries of the circularity that blocked this route:
`NormalEq.weakN_iff → NormalEq.weakN_inv_DFC → IsDefEqU.weakN_iff` is gone.  The other entry,
`NormalEq.parRed → ParRed.weakN_inv → IsDefEqU.weakN_iff`, is **untouched** by this file;
`ParRedK` defers it behind a `WeakNInvDS` hypothesis and discharging that reinstates it.
`NormalEqComplete` is stated here rather than instantiated from `IsDefEq.church_rosser` for two
reasons: that proof's cone still contains `IsDefEqU.weakN_iff`, and it routes through
`NormalEq.parRed`, whose statement `ParRedPropRefute.lean` refutes.

## Measured cone (`scripts/hole-cone.lean`'s `deps`, `allowOpaque := true`)

| seed | holes in cone |
| --- | --- |
| `NormalEq.weakN_inv_DFC` (original) | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `NormalEq.weakN_iff` (original) | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `IsDefEq.church_rosser` | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| **every result in this file** | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TypingStrengthening.onCtx_inv` (baseline) | `forallE_inv_stratified`, `rigidShapeUniqNS` |

`IsDefEqU.weakN_iff` is absent from all of §§1-4; the two remaining holes are the ones the
baseline `Strengthen` machinery already carries, so nothing new is taken on.  §4's controls and
`Strengthening.sortConv` are fully axiom-clean (`[propext]`, `[propext, Quot.sound]`).
Sorry census: 14 before, 14 after.

## Proposed edit to `ChurchRosser.lean` (NOT made here — that file is owned elsewhere)

Thread `(HT : TypingStrengthening env univs)` through `NormalEq.weakN_inv_DFC` (`:361`) and
`NormalEq.weakN_iff` (`:466`), and replace their bodies with `weakN_inv_DFC_of_typing` /
`weakN_iff_of_typing` from this file — i.e. replace the `IsDefEqU.weakN_iff`,
`VExpr.WF.weakN_iff`, `HasType.weakN_iff` and `OnCtx.weakN_inv` appeals in `:361-470` by
`HT.wf_inv`, `HT.hasType_inv` and `HT.onCtx_inv`.  Downstream users of `NormalEq.weakN_iff`
then also carry the hypothesis, which is the point: the dependency on the hole becomes a
dependency on `PiDescend`.
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

/-! ### 1a. Two lift equations

The collapse below hinges on these two: the identity function on `A₂` and the type `A₁ → A₁`
are **both in the image of the lift** whenever `A₁` and `A₂` are.  If either failed, the trick
would be circular (it would need conversion strengthening at a non-lifted type), so they are
named rather than inlined. -/

theorem VExpr.liftN_lam_bvar0 {n k : Nat} (A : VExpr) :
    (VExpr.lam A (.bvar 0)).liftN n k = .lam (A.liftN n k) (.bvar 0) := by
  simp [VExpr.liftN, liftVar]

theorem VExpr.liftN_forallE_self_lift {n k : Nat} (A : VExpr) :
    (VExpr.forallE A A.lift).liftN n k = .forallE (A.liftN n k) ((A.liftN n k).lift) := by
  simp [VExpr.liftN, VExpr.lift_liftN']

/-! ### 1b. The collapse: the sort residual **is** the typing half

`SortConvStrengthening` is not an extra unknown.  Given `Γ' ⊢ A₂↑ ≡ A₁↑ : Sort u` upstairs, the
identity function `λ x : A₂↑. x` — whose natural type is `A₂↑ → A₂↑` — may be retyped by
`defeqDF` at `A₁↑ → A₁↑`.  **Both** the subject and that type are lifts (§1a), so *typing*
strengthening applies and hands back `Γ ⊢ λ x : A₂. x : A₁ → A₁` downstairs.  Downstairs the
same term also has its natural type `A₂ → A₂`, so uniqueness of types gives
`A₂ → A₂ ≡ A₁ → A₁` and `Π`-injectivity gives `A₂ ≡ A₁`.

So a conversion **between types** is encoded in a typing judgment, and typing strengthening
decodes it.  The encoding needs a type former with a slot for a *type*, which `forallE`
provides; there is no such slot for a general *term*, which is why the trick does not extend to
`Strengthening` and why `TransStrengtheningNarrow` survives it (§4). -/

variable! (henv : VEnv.WF env) in
theorem SortConvStrengthening.of_typing (HT : TypingStrengthening env U) :
    SortConvStrengthening env U := by
  intro n k Γ Γ' A₂ A₁ u W hΓ hΓ' h
  have hA₂' : env.HasType U Γ' (A₂.liftN n k) (.sort u) := h.hasType.1
  have hlam : env.HasType U Γ' (.lam (A₂.liftN n k) (.bvar 0))
      (.forallE (A₂.liftN n k) ((A₂.liftN n k).lift)) := .lamDF hA₂' (.bvar .zero)
  have hpi : env.IsDefEq U Γ' (.forallE (A₂.liftN n k) ((A₂.liftN n k).lift))
      (.forallE (A₁.liftN n k) ((A₁.liftN n k).lift)) (.sort (.imax u u)) :=
    .forallEDF h (h.weakN henv .one)
  have hid : env.HasType U Γ' ((VExpr.lam A₂ (.bvar 0)).liftN n k)
      ((VExpr.forallE A₁ A₁.lift).liftN n k) := by
    rw [VExpr.liftN_lam_bvar0, VExpr.liftN_forallE_self_lift]; exact .defeqDF hpi hlam
  have hd := HT.hasType_inv henv W hΓ' hid
  have ⟨_, hA₂⟩ := TypingStrengthening.sortDescend henv HT W hΓ hΓ' hA₂' (HT W hΓ hΓ' hA₂')
  have uu := (IsDefEq.lamDF hA₂ (.bvar .zero)).uniqU henv hΓ hd
  exact have ⟨_, h⟩ := (uu.forallE_inv henv hΓ).1; ⟨_, h⟩

/-- The same, as a projection off `TypingStrengthening`. -/
theorem TypingStrengthening.sortConv (henv : VEnv.WF env) (HT : TypingStrengthening env U) :
    SortConvStrengthening env U := SortConvStrengthening.of_typing henv HT

/-- **`SortConvStrengthening` is no stronger than `PiDescend`.**  With `Strengthen.lean` §9(b)
collapsing the two descent statements, §1b says the sort fragment of the hole is not a new
unknown at all: it is implied by the *typing* half, which is `PiDescend`.

**Correction (2026-09-01): this docstring used to say "is exactly `PiDescend`", and only the
`⟸` direction is proved -- here and nowhere else in the tree.**  The converse
`SortConvStrengthening → TypingStrengthening` is *not* available: recovering a Π shape for the
subject's downstairs type from `C.liftN ≡ .forallE A B` upstairs would need
`SortConvStrengthening` at a pair whose right-hand side is `.forallE A B`, which is not in the
image of the lift (its codomain lives in the extended upstairs context).  So the sort fragment
is a consequence of the typing half, not a restatement of it, and it may be strictly weaker. -/
theorem SortConvStrengthening.of_piDescend (henv : VEnv.WF env) (HP : PiDescend env U) :
    SortConvStrengthening env U :=
  SortConvStrengthening.of_typing henv ((TypingStrengthening.iff_piDescend henv).2 HP)

/-! ### 1c. The sort-typed instances of the narrow `trans` residual are closed

`StrengthenNarrow.lean` §1's `TransStrengtheningNarrow` is where 253 of the hole's 296 users
sit.  §1b closes every instance of it whose shared type is a sort, so the residual may be
narrowed once more: only instances whose endpoints are **not types** are left. -/

/-- **The narrow `trans` residual, at a sort type, from the typing half alone.** -/
theorem TransStrengtheningNarrow.at_sort (henv : VEnv.WF env) (HT : TypingStrengthening env U)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b : VExpr} {u : VLevel}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (h1 : env.IsDefEq U Γ' (e1.liftN n k) b (.sort u))
    (h2 : env.IsDefEq U Γ' b (e2.liftN n k) (.sort u)) : env.IsDefEqU U Γ e1 e2 :=
  SortConvStrengthening.of_typing henv HT W hΓ hΓ' (h1.trans h2)

end

section
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## 2. `NormalEq.weakN_inv_DFC` from the typing half plus the sort residual

`HS` is consumed in **exactly one** of the ten cases, `lamDF`, and §1b then discharges it, so
§3's `weakN_inv_DFC_of_typing` needs `TypingStrengthening` and nothing else.  The other nine
cases: `sortDF`/`constDF` need nothing; `refl`, `etaL`, `etaR` and `proofIrrel` call the hole
only at *reflexive* instances (`⟨_, h⟩` with `h` a `HasType`), i.e. at `VExpr.WF.weakN_iff`;
`forallEDF` and the rest of `etaL`/`etaR`/`proofIrrel` call it at `HasType.weakN_iff`; and
`appDF`'s genuine conversion use — the `.trans` of two `uniqU`s, whose middle term is the
upstairs type and need not be a lift — is **eliminated**, not weakened: the two induction
hypotheses already give `NormalEq Γ f₁ f₂` and `NormalEq Γ a₁ a₂` downstairs, and
`NormalEq.defeq` turns them into the conversions that retype `f₂` and `a₂` at `f₁`'s and
`a₁`'s types.  That is the one substantive change to the original proof. -/

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

/-! ## 3. `HS` discharged, and the transport corollary

§1b turns §2's second hypothesis into a theorem, so `NormalEq`-strengthening rests on the
*typing* half alone — equivalently, by `Strengthen.lean` §9(b), on `PiDescend`.  The `trans`
obstruction is not solved here, it is **bypassed**: `NormalEq` has no `trans` constructor, so
the induction of §2 never meets the one case of `Strengthening`'s induction that resists.

`TypingStrengthening` has no unconditional inhabitant in this tree — it is equivalent to
`PiDescend`, still open — so the honest reading of §3 is "`NormalEq`-strengthening reduces to
`PiDescend`", not "the hole is closed". -/

/-- **`NormalEq.weakN_inv_DFC` from the typing half alone.**  The hypothesis is implied by the
hole (`Strengthening.typing`) and by `PiDescend`, and nothing else is needed. -/
theorem NormalEq.weakN_inv_DFC_of_typing (HT : TypingStrengthening env univs)
    {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (IsType env univs))
    {n k : Nat} {Γ Γ₁ Γ₂ : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1.liftN n k ≡ₚ e2.liftN n k) : Γ ⊢ e1 ≡ₚ e2 :=
  NormalEq.weakN_inv_DFC' HT (SortConvStrengthening.of_typing henv HT) hΓ₀ W W₂ H

/-- `NormalEq.weakN_iff` (`ChurchRosser.lean:466`) from the typing half alone. -/
theorem NormalEq.weakN_iff_of_typing (HT : TypingStrengthening env univs)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}
    (hΓ' : OnCtx Γ' (IsType env univs)) (W : Ctx.LiftN n k Γ Γ') :
    (Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k) ↔ (Γ ⊢ e1 ≡ₚ e2) :=
  ⟨fun H => H.weakN_inv_DFC_of_typing HT hΓ' W .zero, fun H => H.weakN W⟩

/-- **Confluence, as an explicit hypothesis.**  This is `IsDefEq.church_rosser`'s content in the
only form §3 needs.  It is *not* instantiated from `ChurchRosser.lean`'s `church_rosser`: that
proof's cone contains `IsDefEqU.weakN_iff` (which is what §2 removes) and routes through
`NormalEq.parRed`, whose statement is refuted outright by `ParRedPropRefute.lean`.  The point of
§3 is to convert "repair confluence" into "close the 296-user hole". -/
def NormalEqComplete : Prop :=
  ∀ {Γ : List VExpr} {e1 e2 A : VExpr}, OnCtx Γ (IsType env univs) →
    (Γ ⊢ e1 ≡ e2 : A) → Γ ⊢ e1 ≡ₚ e2

/-- **Confluence plus the typing half closes the hole.**  `e1↑ ≡ e2↑` upstairs, `NormalEq`
upstairs by `HN`, `NormalEq` downstairs by §3, conversion downstairs by `NormalEq.defeq`. -/
theorem StrengtheningTarget.of_normalEqComplete (HN : NormalEqComplete)
    (HT : TypingStrengthening env univs) : StrengtheningTarget env univs := by
  intro n k Γ Γ' e1 e2 W hΓ' h
  have ⟨_, h⟩ := h
  exact (NormalEq.weakN_inv_DFC_of_typing HT hΓ' W .zero (HN hΓ' h)).defeq
    (HT.onCtx_inv henv W hΓ')

/-- **Given confluence, the hole is exactly `PiDescend`.**  Compare
`StrengthenNarrow.lean` §3's `StrengtheningTarget.iff_piDescend_narrow`, which needs
`PiDescend` **and** the narrow `trans` residual: under `HN` the second conjunct is free. -/
theorem StrengtheningTarget.iff_piDescend_of_normalEqComplete (HN : NormalEqComplete) :
    StrengtheningTarget env univs ↔ PiDescend env univs :=
  ⟨fun H => (TypingStrengthening.iff_piDescend henv).1
     (Strengthening.typing (StrengtheningTarget.strengthening H)),
   fun H => StrengtheningTarget.of_normalEqComplete HN
     ((TypingStrengthening.iff_piDescend henv).2 H)⟩

/-- The same, against `StrengthenNarrow.lean`'s residual: **confluence plus `PiDescend` closes
the narrow `trans` residual**, where 253 of the hole's 296 users sit. -/
theorem TransStrengtheningNarrow.of_normalEqComplete (HN : NormalEqComplete)
    (HP : PiDescend env univs) : TransStrengtheningNarrow env univs :=
  ((StrengtheningTarget.iff_typing_narrow henv).1
    (StrengtheningTarget.of_normalEqComplete HN
      ((TypingStrengthening.iff_piDescend henv).2 HP))).2

/-! ## 4. Negative controls

The failure mode this section guards against is the one that has cost this project the most: a
reduction that is secretly a tautology.  §4 is sorry-free throughout. -/

/-- **§2 subsumes the original.**  `ChurchRosser.lean:361` is the special case of §2 at the
hypothesis the hole supplies, so §2 is strictly more general and proves nothing less. -/
theorem NormalEq.weakN_inv_DFC_of_strengthening (H : Strengthening env univs)
    {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (IsType env univs))
    {n k : Nat} {Γ Γ₁ Γ₂ : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H' : Γ₁ ⊢ e1.liftN n k ≡ₚ e2.liftN n k) : Γ ⊢ e1 ≡ₚ e2 :=
  NormalEq.weakN_inv_DFC' H.typing H.sortConv hΓ₀ W W₂ H'

/-- **`HN` is where §3's content is.**  Deleting it is not an option: a hypothesis-free
`TypingStrengthening → StrengtheningTarget` would make the hole *equal* to its own typing half,
i.e. would close `TransStrengthening` outright.  So §3 is not a tautology in the direction that
matters — its `←` cannot be improved by dropping `HN` without closing the hole. -/
theorem normalEqComplete_load_bearing
    (H : TypingStrengthening env univs → StrengtheningTarget env univs) :
    StrengtheningTarget env univs ↔ TypingStrengthening env univs :=
  ⟨fun h => Strengthening.typing (StrengtheningTarget.strengthening h), H⟩

end

section
variable {env : VEnv} {U : Nat}

/-- **The `forallE` encoding of §1b does not extend to terms.**  The obvious way to push a
*term-level* conversion into a sort-typed one is to apply a constant function into a sort; and
that is information-free.  Both sides β-reduce to `Sort 0`, so the encoded conversion holds with
**no hypothesis relating `e1` and `e2` at all** — hence §1b's trick cannot be re-run to derive
the full `Strengthening` from `TypingStrengthening`, and `TransStrengtheningNarrow` survives
§1c.  (`forallE` works in §1b precisely because its slots take *types*.) -/
theorem sortConv_encoding_vacuous {Γ : List VExpr} {T e1 e2 : VExpr}
    (h1 : env.HasType U Γ e1 T) (h2 : env.HasType U Γ e2 T) :
    env.IsDefEq U Γ (.app (.lam T (.sort .zero)) e1) (.app (.lam T (.sort .zero)) e2)
      (.sort (.succ .zero)) :=
  have hs : env.HasType U (T::Γ) (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  (IsDefEq.beta hs h1).trans (IsDefEq.beta hs h2).symm

end

