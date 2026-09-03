import Lean4Lean.Theory.SetModel.IffRecLarge
import Lean4Lean.Theory.SetModel.StablePrelude  -- 2026-09-03: `L.Stable` is weakened to `L.StableLift` throughout this file.  The two are NOT interchangeable in general -- `PropSplit.stable_iff_lift_and_inst` splits `Stable` into a lift half and an inst half -- but no consumer mixes them, and `interp_closed_ctx`, the ONLY substantive use of `hS` here, is a corollary of the lift half alone (`interp_closed_ctx_lift`).  The point is that the lift half is FREE at the split `UpperBound.OracleInput` fixes: `propSplitUp_stableLift` needs only `env.Ordered`, `PropUniq`, `PropTypeAgree` -- the inputs `propSplitUp` already takes.  Full `Stable` is not free and never will be: `propSplitUp_stable_iff` proves it is EQUIVALENT to `env.InstDescendUp nv`, an open assumption whose only producers are `PropDescend` (no producer anywhere) and `UpperBound.InstDescendInput`.  So this weakening is what makes `inductOracleOK_*` `hle`-only.

/-!
# `eqIndDecl`'s ι-rule: `InductOracleOK`'s `rules` field at the `Eq` block

`EqRecLarge.lean` §10 measures the rule's three components and §10.1 types both of its sides
(`eqRule_WF`, from `VInductDecl'.iotaRules_WF` and `VInductDecl'.WF.iotaCtx`, twelve lines and
hole-free).  **Neither of those is the `rules` field.**  `CnstRecursion.DefEqOK` asks for two
things at each ι-rule, and typing supplies at most the *second*:

1. `⟦lhs⟧ = ⟦rhs⟧` at the empty valuation — the ι-computation itself, which for this block is
   `eqRecFn ‘ α ‘ a ‘ f ‘ m ‘ a ‘ • = m`, six `mkLam_value` steps plus a `•`-collapse at the
   constructor application;
2. `⟦lhs⟧ ∈ ⟦type⟧` — four `mkLam_mem_mkForallType` steps once the domains are known.

Both split on `u.eval M.ls = 0` exactly as the recursor cell does
(`EqLargeAudit.eqRuleSort_eval_eq_zero_iff`), and on the `= 0` branch both sides are `•` with no
set-theoretic content at all.

## What this file needs that §10.1 does not supply

The typing that `iotaRules_WF` gives is of the *whole* λ-nest.  `interp` is defined by cases on
the term, and its `app` clause consults `L.IsProof` at each **prefix** of the recursor spine, so
the six prefixes have to be typed individually and their types' sorts exhibited.  §2 does that:
the prefixes come from `EqAudit.hasType_app'` with `rfl` at every `.inst` equation (the arguments
are bound variables, so every instantiation is a closed computation), and their sorts from
`HasType.instN` against `EqAudit.hasType_recB*`.  That is the part two earlier costings priced at
zero.
-/

namespace Lean4Lean.SetModel.EqIotaAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.EqAudit
open Lean4Lean.SetModel.EqZeroAudit
open Lean4Lean.SetModel.EqLargeAudit
open scoped Classical

/-! ## 1. `eqEnv` is `Ordered`, and the recursor constant at the ι-context -/

section Env

theorem eqEnv_WF' : eqEnv.WF := ⟨_, .decl (.induct (eqIndDecl_WF _) eqEnv_add) .empty⟩

theorem eqEnv_ordered : eqEnv.Ordered := VEnv.WF.ordered eqEnv_WF'

end Env

section Spine

variable {nv : ℕ} {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
variable (Γ : List VExpr)

include hu hv in
/-- `Eq.rec.{u,v}`, with its type in the `.forallE` shape `hasType_app'` can consume. -/
theorem hasType_EqRecC :
    eqEnv.HasType nv Γ (.const ``Eq.rec [u, v]) (.forallE (.sort v) (recBA u v)) := by
  have h : eqEnv.HasType nv Γ (.const ``Eq.rec [u, v])
      ((eqIndDecl.recType 0).instL [u, v]) :=
    .constDF eqEnv_EqRecC (by simp [hu, hv]) (by simp [hu, hv]) rfl
      (.cons (by rfl) (.cons (by rfl) .nil))
  rwa [eqRecType_instL] at h

/-! ### The four variables of the ι-context, read at the ι-context itself

`ectxN Γ u v` **is** the reverse of `(eqIndDecl.iotaCtx eqCtor).map (instL [u,v])`
(`EqLargeAudit.eq_iotaCtx_reverse`), so these are the ι-rule's own binders. -/

theorem hasType_a_ctxN : eqEnv.HasType nv (ectxN Γ u v) (.bvar 2) (.bvar 3) :=
  .bvar (.succ (.succ .zero))

theorem hasType_mot_ctxN :
    eqEnv.HasType nv (ectxN Γ u v) (.bvar 1)
      (.forallE (.bvar 3) (.forallE (eqAp v (.bvar 4) (.bvar 3) (.bvar 0)) (.sort u))) :=
  .bvar (.succ .zero)

theorem hasType_min_ctxN : eqEnv.HasType nv (ectxN Γ u v) (.bvar 0) ((minTyE v).lift) :=
  .bvar .zero

include hv in
/-- `Eq.refl α a : Eq α a a` at the ι-context — the major premise of the ι-rule's left side. -/
theorem hasType_reflAp_ctxN :
    eqEnv.HasType nv (ectxN Γ u v) (reflAp v (.bvar 3) (.bvar 2))
      (eqAp v (.bvar 3) (.bvar 2) (.bvar 2)) :=
  hasType_reflAp hv (hasType_al_ctxN Γ) (hasType_a_ctxN Γ)

/-! ### The six prefixes of the recursor spine, typed

Every `.inst` equation is `rfl`: the arguments are `.bvar` numerals, so `VExpr.inst` and the
`VExpr.liftN 0` it produces are closed computations.  This is the ladder `EqOracle.lean`'s
`hasType_app'` docstring warns about at *abstract* arguments; at an ι-rule the arguments are the
telescope's own variables and the warning does not apply. -/

include hu hv in
theorem hasType_recAp1 :
    eqEnv.HasType nv (ectxN Γ u v) (.app (.const ``Eq.rec [u, v]) (.bvar 3))
      ((recBA u v).inst (.bvar 3)) :=
  hasType_app' (hasType_EqRecC hu hv (ectxN Γ u v)) (hasType_al_ctxN Γ) rfl

end Spine


/-! ## 2. The left-hand side's body, applied out

`interp`'s `app` clause consults `L.IsProof` at each of the spine's six prefixes, so each one is
typed here and each type's sort exhibited.  The constructor application `Eq.refl α a` is the one
node where the *positive* branch is taken: it is a proof, so `interp` discards `a` and returns `•`
-- which is exactly why the ι-rule's right-hand side can be `m` with no `Eq`-specific content. -/

section Body

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

/-- The ι-rule's left-hand body: `Eq.rec α a motive m a (Eq.refl α a)`, over the ι-context.
`EqLargeAudit.eqRule_lhs_instL` is the measurement that this is what `iotaRule` produces. -/
abbrev iotaLhsBodyE (u v : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Eq.rec [u, v]) (.bvar 3)) (.bvar 2))
    (.bvar 1)) (.bvar 0)) (.bvar 2)) (reflAp v (.bvar 3) (.bvar 2))

include hu hv in
/-- **The left-hand body, typed at the ι-context.**  Six `hasType_app'` steps, every `.inst`
equation `rfl`.  `EqRecLarge` §10.1 gets the *whole nest* typed for free from
`VInductDecl'.iotaRules_WF`; `interp` needs this, the body alone, because `interp_lam_congr_of_type`
peels one binder at a time. -/
theorem hasType_iotaLhsBodyE (Γ : List VExpr) :
    eqEnv.HasType nv (ectxN Γ u v) (iotaLhsBodyE u v) ((minTyE v).lift) :=
  hasType_app' (hasType_app' (hasType_app' (hasType_app' (hasType_app'
    (hasType_app' (hasType_EqRecC hu hv (ectxN Γ u v)) (hasType_al_ctxN Γ) rfl)
    (hasType_a_ctxN Γ) rfl) (hasType_mot_ctxN Γ) rfl) (hasType_min_ctxN Γ) rfl)
    (hasType_a_ctxN Γ) rfl) (hasType_reflAp_ctxN hv Γ) rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
/-- `Eq.refl α` **is** a proof at the ι-context: its type `∀ x : α, Eq α x x` has sort
`imax v 0 = 0`. -/
theorem isProof_reflC1_ctxN (hΓ : OnCtx (ectxN ([] : List VExpr) u v) (eqEnv.IsType nv)) :
    L.IsProof M (ectxN ([] : List VExpr) u v) (.app (.const ``Eq.refl [v]) (.bvar 3)) := by
  have h1 : eqEnv.HasType nv (ectxN ([] : List VExpr) u v)
      (.app (.const ``Eq.refl [v]) (.bvar 3))
      (.forallE (.bvar 3) (eqAp v (.bvar 4) (.bvar 0) (.bvar 0))) :=
    hasType_app' (hasType_EqRefl hv _) (hasType_al_ctxN _) rfl
  have h2 : eqEnv.HasType nv (ectxN ([] : List VExpr) u v)
      (.forallE (.bvar 3) (eqAp v (.bvar 4) (.bvar 0) (.bvar 0))) (.sort (.imax v .zero)) :=
    .forallEDF (hasType_al_ctxN _)
      (hasType_eqAp hv (.bvar (.succ (.succ (.succ (.succ .zero))))) (.bvar .zero) (.bvar .zero))
  exact (isProof_iff hle hΓ h1 h2 ⟨hv, trivial⟩).2 rfl

include hu hv hle in
/-- **The spine, applied out.**  Six `interp_app_type` steps, one `interp_app_proof`, four
`snoc` reads. -/
theorem interp_iotaLhsBody_app (hn : u.eval M.ls ≠ 0) {α a f m : V} :
    (interp M L (ectxN ([] : List VExpr) u v) (iotaLhsBodyE u v)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m)
      = (((((((M.cnst ``Eq.rec [u, v]) ‘ α) ‘ a) ‘ f) ‘ m) ‘ a) ‘ (pt : V)) := by
  have hON : OnCtx (ectxN ([] : List VExpr) u v) (eqEnv.IsType nv) := onCtx_N (Γ := ([] : List VExpr)) hu hv trivial
  -- the six prefixes, typed
  have h1 := hasType_EqRecC hu hv (ectxN ([] : List VExpr) u v)
  have h2 := hasType_app' h1 (hasType_al_ctxN _) rfl
  have h3 := hasType_app' h2 (hasType_a_ctxN _) rfl
  have h4 := hasType_app' h3 (hasType_mot_ctxN _) rfl
  have h5 := hasType_app' h4 (hasType_min_ctxN _) rfl
  have h6 := hasType_app' h5 (hasType_a_ctxN _) rfl
  -- their types' sorts
  have hA1 : eqEnv.HasType nv (ectxN ([] : List VExpr) u v)
      (.forallE (.sort v) (recBA u v)) (.sort (eqRecSort u v)) :=
    .forallEDF (.sortDF hv hv rfl) (hasType_recBA hu hv _)
  have hA2 := (hasType_recBA hu hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered .zero (hasType_al_ctxN _)
  have hA3 := ((hasType_recBM hu hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ .zero) (hasType_al_ctxN _)).instN
    eqEnv_ordered .zero (hasType_a_ctxN _)
  have hA4 := (((hasType_recBN hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ (.succ .zero)) (hasType_al_ctxN _)).instN
    eqEnv_ordered (.succ .zero) (hasType_a_ctxN _)).instN
    eqEnv_ordered .zero (hasType_mot_ctxN _)
  have hA5 := ((((hasType_recBB hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ (.succ (.succ .zero))) (hasType_al_ctxN _)).instN
    eqEnv_ordered (.succ (.succ .zero)) (hasType_a_ctxN _)).instN
    eqEnv_ordered (.succ .zero) (hasType_mot_ctxN _)).instN
    eqEnv_ordered .zero (hasType_min_ctxN _)
  have hA6 := (((((hasType_recBH hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ (.succ (.succ (.succ .zero)))) (hasType_al_ctxN _)).instN
    eqEnv_ordered (.succ (.succ (.succ .zero))) (hasType_a_ctxN _)).instN
    eqEnv_ordered (.succ (.succ .zero)) (hasType_mot_ctxN _)).instN
    eqEnv_ordered (.succ .zero) (hasType_min_ctxN _)).instN
    eqEnv_ordered .zero (hasType_a_ctxN _)
  -- the six `¬IsProof`s
  have hnp1 := fun hp ↦ hn (eqRecSort_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h1 hA1 (eqRecSort_wf hu hv)).1 hp))
  have hnp2 := fun hp ↦ hn (sortAE_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h2 hA2 (sortAE_wf hu hv)).1 hp))
  have hnp3 := fun hp ↦ hn (sortME_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h3 hA3 (sortME_wf hu hv)).1 hp))
  have hnp4 := fun hp ↦ hn (sortNE_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h4 hA4 (sortNE_wf hu hv)).1 hp))
  have hnp5 := fun hp ↦ hn (sortBE_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h5 hA5 (sortBE_wf hu hv)).1 hp))
  have hnp6 := fun hp ↦ hn (sortHE_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h6 hA6 (sortHE_wf hu)).1 hp))
  rw [interp_app_type M L hnp6, interp_app_type M L hnp5, interp_app_type M L hnp4,
    interp_app_type M L hnp3, interp_app_type M L hnp2, interp_app_type M L hnp1,
    interp_app_proof M L (isProof_reflC1_ctxN hv hle hON), interp_const,
    interp_bvar, interp_bvar, interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, show (4 - 1 - 2 : ℕ) = 1 from rfl,
    show (4 - 1 - 1 : ℕ) = 2 from rfl, show (4 - 1 - 0 : ℕ) = 3 from rfl,
    r4_0, r4_1, r4_2, r4_3]

end Body


/-! ## 3. The ι-computation proper: `eqRecFn` at a reflexivity major premise

Six `mkLam_value` steps down `eqRecFn`'s own nest.  The last layer's domain is `⟦Eq α a a⟧`, which
`eqFn_value` collapses to `{•}`, and its body is `ρ ‘ 3` -- the minor premise.  **This is the whole
set-theoretic content of the ι-rule**, and it is why `lamH`'s body was written as a read of the
minor premise rather than as anything `Eq`-specific. -/

section Compute

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`eqRecFn ‘ α ‘ a ‘ f ‘ m ‘ a ‘ • = m`.** -/
theorem eqRecFn_app_refl (κ : ℕ → V) (nu nv : ℕ) {α a f m : V}
    (hα : α ∈ U κ nv) (ha : a ∈ α)
    (hf : f ∈ motSet κ nu nv (snoc (snoc (∅ : V) α) a))
    (hm : m ∈ ((f ‘ a) ‘ (pt : V))) :
    ((((((eqRecFn κ nu nv) ‘ α) ‘ a) ‘ f) ‘ m) ‘ a) ‘ (pt : V) = m := by
  have v1 : (eqRecFn κ nu nv) ‘ α = lamA κ nu nv (snoc (∅ : V) α) := by
    unfold eqRecFn; exact mkLam_value hα
  have v2 : (lamA κ nu nv (snoc (∅ : V) α)) ‘ a
      = lamF κ nu nv (snoc (snoc (∅ : V) α) a) := by
    unfold lamA; exact mkLam_value (by rw [r1_0]; exact ha)
  have v3 : (lamF κ nu nv (snoc (snoc (∅ : V) α) a)) ‘ f
      = lamM κ nv (snoc (snoc (snoc (∅ : V) α) a) f) := by
    unfold lamF; exact mkLam_value hf
  have v4 : (lamM κ nv (snoc (snoc (snoc (∅ : V) α) a) f)) ‘ m
      = lamB κ nv (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) := by
    unfold lamM; exact mkLam_value (by rw [r3_2, r3_1]; exact hm)
  have v5 : (lamB κ nv (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m)) ‘ a
      = lamH κ nv (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) a) := by
    unfold lamB; exact mkLam_value (by rw [r4_0]; exact ha)
  have v6 : (lamH κ nv (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) a)) ‘ (pt : V) = m := by
    unfold lamH
    rw [mkLam_value (ρ := snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) a) (v := (pt : V))
      (by rw [r5_0, r5_1, r5_4, eqFn_value hα ha ha, if_pos rfl]; exact mem_singleton_iff.2 rfl)]
    exact r5_3
  rw [v1, v2, v3, v4, v5, v6]

end Compute


/-! ## 4. The rule's own type, one binder at a time

`EqLargeAudit.eqRule_type_instL` measures the shape; these give it a *derivation*, with the sort
written out at every stage.  The top sort is `EqLargeAudit.eqRuleSort`, so
`eqRuleSort_eval_eq_zero_iff` is the level branch of the ι-rule and of the four λ-nests below it. -/

section RuleType

variable {nv : ℕ} {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
variable (Γ : List VExpr)

abbrev ruleSortN (u : VLevel) : VLevel := .imax u u
abbrev ruleSortM (u v : VLevel) : VLevel := .imax (motSortE u v) (ruleSortN u)
abbrev ruleSortP (u v : VLevel) : VLevel := .imax v (ruleSortM u v)

include hu in
theorem ruleSortN_wf : (ruleSortN u).WF nv := ⟨hu, hu⟩
include hu hv in
theorem ruleSortM_wf : (ruleSortM u v).WF nv := ⟨motSortE_wf hu hv, ruleSortN_wf hu⟩
include hu hv in
theorem ruleSortP_wf : (ruleSortP u v).WF nv := ⟨hv, ruleSortM_wf hu hv⟩
include hu hv in
theorem eqRuleSort_wf : (eqRuleSort u v).WF nv := ⟨hv, ruleSortP_wf hu hv⟩

theorem ruleSortN_eval_eq_zero_iff {ls : List ℕ} :
    (ruleSortN u).eval ls = 0 ↔ u.eval ls = 0 := imax_eq_zero_iff
theorem ruleSortM_eval_eq_zero_iff {ls : List ℕ} :
    (ruleSortM u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans ruleSortN_eval_eq_zero_iff
theorem ruleSortP_eval_eq_zero_iff {ls : List ℕ} :
    (ruleSortP u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans ruleSortM_eval_eq_zero_iff
theorem eqRuleSort_eval_eq_zero_iff' {ls : List ℕ} :
    (eqRuleSort u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans ruleSortP_eval_eq_zero_iff

include hv in
/-- The ι-rule's common type at its innermost binder: `motive a (Eq.refl α a)`, one binder deeper
than `minTyE`, i.e. `(minTyE v).lift`.  This is `(eqIndDecl.iotaType 0 eqCtor).instL [u, v]`. -/
theorem hasType_iotaTypeE :
    eqEnv.HasType nv (ectxN Γ u v) ((minTyE v).lift) (.sort u) :=
  (hasType_minTyE hv Γ).weak eqEnv_ordered

include hv in
theorem hasType_piN :
    eqEnv.HasType nv (ectxM Γ u v) (.forallE (minTyE v) ((minTyE v).lift))
      (.sort (ruleSortN u)) :=
  .forallEDF (hasType_minTyE hv Γ) (hasType_iotaTypeE hv Γ)

include hu hv in
theorem hasType_piM :
    eqEnv.HasType nv (ectxP Γ v)
      (.forallE (motTyE u v) (.forallE (minTyE v) ((minTyE v).lift))) (.sort (ruleSortM u v)) :=
  .forallEDF (hasType_motTyE hu hv Γ) (hasType_piN hv Γ)

include hu hv in
theorem hasType_piP :
    eqEnv.HasType nv (ectxA Γ v)
      (.forallE (.bvar 0) (.forallE (motTyE u v) (.forallE (minTyE v) ((minTyE v).lift))))
      (.sort (ruleSortP u v)) :=
  .forallEDF (.bvar .zero) (hasType_piM hu hv Γ)

include hu hv in
/-- **The ι-rule's type, typed, with its sort.**  `EqLargeAudit.eqRule_type_instL` says this
expression *is* `(eqIndDecl.iotaRule 0 0 eqCtor).type.instL [u, v]`. -/
theorem hasType_ruleType :
    eqEnv.HasType nv Γ
      (.forallE (.sort v) (.forallE (.bvar 0)
        (.forallE (motTyE u v) (.forallE (minTyE v) ((minTyE v).lift)))))
      (.sort (eqRuleSort u v)) :=
  .forallEDF (.sortDF hv hv rfl) (hasType_piP hu hv Γ)

end RuleType


/-! ## 5. The right-hand side's body

`iotaRule`'s `rhs` is deliberately the η-expansion `λ Γ'. (iotaLam) Γ'`
(`Theory/Inductive/Decl.lean`: "do not simplify `rhs` to `iotaLam`'s body"), so the body carries a
four-fold β-redex over the *closed* nest `λ α a motive m, m`.  `interp` does not reduce β, so the
redex has to be computed: four `interp_app_type` steps, then `interp_closed_ctx` to read the closed
nest at the empty context, then four `mkLam_value` steps.

**`interp_closed_ctx` costs `L.Stable`** -- the one hypothesis in this file that is not discharged
in the tree (`StableAudit.lean`; it is `propSplitUp_stable` at the consumer, from
`UpperBound.InstDescendInput`).  It buys the right to compute the closed nest against
`EqZeroAudit`'s existing `Γ = []` domain lemmas instead of restating all of them at the ι-context. -/

section Rhs

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

/-- `λ (m : motive a (Eq.refl α a)), m`, over `[motive, a, α]`. -/
abbrev lamNE (v : VLevel) : VExpr := .lam (minTyE v) (.bvar 0)
/-- …one binder out. -/
abbrev lamME (u v : VLevel) : VExpr := .lam (motTyE u v) (lamNE v)
abbrev lamPE (u v : VLevel) : VExpr := .lam (.bvar 0) (lamME u v)
/-- **`eqIndDecl.iotaLam 0 eqCtor`, instantiated**: `λ α a motive m, m`. -/
abbrev iotaLamE (u v : VLevel) : VExpr := .lam (.sort v) (lamPE u v)

abbrev ruleTyN (v : VLevel) : VExpr := .forallE (minTyE v) ((minTyE v).lift)
abbrev ruleTyM (u v : VLevel) : VExpr := .forallE (motTyE u v) (ruleTyN v)
abbrev ruleTyP (u v : VLevel) : VExpr := .forallE (.bvar 0) (ruleTyM u v)
abbrev ruleTyA (u v : VLevel) : VExpr := .forallE (.sort v) (ruleTyP u v)

/-- The ι-rule's right-hand body: the four-fold β-redex. -/
abbrev iotaRhsBodyE (u v : VLevel) : VExpr :=
  .app (.app (.app (.app (iotaLamE u v) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)

section Typing
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv))

include hu hv hΓ in
theorem hasType_lamNE : eqEnv.HasType nv (ectxM Γ u v) (lamNE v) (ruleTyN v) :=
  VEnv.HasType.mkLams (As := [minTyE v]) (onCtx_N hu hv hΓ) (.bvar .zero)

include hu hv hΓ in
theorem hasType_lamME : eqEnv.HasType nv (ectxP Γ v) (lamME u v) (ruleTyM u v) :=
  VEnv.HasType.mkLams (As := [motTyE u v, minTyE v]) (onCtx_N hu hv hΓ) (.bvar .zero)

include hu hv hΓ in
theorem hasType_lamPE : eqEnv.HasType nv (ectxA Γ v) (lamPE u v) (ruleTyP u v) :=
  VEnv.HasType.mkLams (As := [(.bvar 0 : VExpr), motTyE u v, minTyE v])
    (onCtx_N hu hv hΓ) (.bvar .zero)

include hu hv hΓ in
theorem hasType_iotaLamE : eqEnv.HasType nv Γ (iotaLamE u v) (ruleTyA u v) :=
  VEnv.HasType.mkLams (As := [.sort v, (.bvar 0 : VExpr), motTyE u v, minTyE v])
    (onCtx_N hu hv hΓ) (.bvar .zero)

end Typing

include hu hv in
theorem iotaLamE_closed : (iotaLamE u v).ClosedN 0 :=
  (hasType_iotaLamE (Γ := ([] : List VExpr)) hu hv trivial).closedN eqEnv_ordered trivial

/-! ### The four `¬IsProof`s inside the closed nest, and the nest's value -/

include hu hv hle in
theorem interp_iotaLamE_app (hn : u.eval M.ls ≠ 0) {α a f m : V}
    (hα : α ∈ U M.κ (v.eval M.ls))
    (ha : a ∈ (interp M L (ectxA ([] : List VExpr) v) (.bvar 0)).toFun (snoc (∅ : V) α))
    (hf : f ∈ (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun
      (snoc (snoc (∅ : V) α) a))
    (hm : m ∈ (interp M L (ectxM ([] : List VExpr) u v) (minTyE v)).toFun
      (snoc (snoc (snoc (∅ : V) α) a) f)) :
    (((((interp M L ([] : List VExpr) (iotaLamE u v)).toFun ∅) ‘ α) ‘ a) ‘ f) ‘ m = m := by
  have hnpP : ¬ L.IsProof M (ectxA ([] : List VExpr) v) (lamPE u v) := fun hp ↦
    hn (ruleSortP_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
      (onCtx_A (Γ := ([] : List VExpr)) hv trivial) (hasType_lamPE (Γ := ([] : List VExpr)) hu hv trivial) (hasType_piP hu hv _)
      (ruleSortP_wf hu hv)).1 hp))
  have hnpM : ¬ L.IsProof M (ectxP ([] : List VExpr) v) (lamME u v) := fun hp ↦
    hn (ruleSortM_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
      (onCtx_P (Γ := ([] : List VExpr)) hv trivial) (hasType_lamME (Γ := ([] : List VExpr)) hu hv trivial) (hasType_piM hu hv _)
      (ruleSortM_wf hu hv)).1 hp))
  have hnpN : ¬ L.IsProof M (ectxM ([] : List VExpr) u v) (lamNE v) := fun hp ↦
    hn (ruleSortN_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
      (onCtx_M (Γ := ([] : List VExpr)) hu hv trivial) (hasType_lamNE (Γ := ([] : List VExpr)) hu hv trivial) (hasType_piN hv _)
      (ruleSortN_wf hu)).1 hp))
  have hnpB : ¬ L.IsProof M (ectxN ([] : List VExpr) u v) (.bvar 0) := fun hp ↦
    hn ((isProof_iff (L := L) (M := M) hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial) (.bvar .zero)
      (hasType_iotaTypeE hv _) hu).1 hp)
  have e1 : ((interp M L ([] : List VExpr) (iotaLamE u v)).toFun ∅) ‘ α
      = (interp M L (ectxA ([] : List VExpr) v) (lamPE u v)).toFun (snoc (∅ : V) α) := by
    rw [interp_lam_type M L hnpP]
    exact mkLam_value (by rw [interp_sort]; exact hα)
  have e2 : ((interp M L (ectxA ([] : List VExpr) v) (lamPE u v)).toFun (snoc (∅ : V) α)) ‘ a
      = (interp M L (ectxP ([] : List VExpr) v) (lamME u v)).toFun (snoc (snoc (∅ : V) α) a) := by
    rw [interp_lam_type M L hnpM]; exact mkLam_value ha
  have e3 : ((interp M L (ectxP ([] : List VExpr) v) (lamME u v)).toFun
        (snoc (snoc (∅ : V) α) a)) ‘ f
      = (interp M L (ectxM ([] : List VExpr) u v) (lamNE v)).toFun
        (snoc (snoc (snoc (∅ : V) α) a) f) := by
    rw [interp_lam_type M L hnpN]; exact mkLam_value hf
  have e4 : ((interp M L (ectxM ([] : List VExpr) u v) (lamNE v)).toFun
        (snoc (snoc (snoc (∅ : V) α) a) f)) ‘ m
      = (interp M L (ectxN ([] : List VExpr) u v) (.bvar 0)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) := by
    rw [interp_lam_type M L hnpB]; exact mkLam_value hm
  rw [e1, e2, e3, e4, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 0 : ℕ) = 3 from rfl]
  exact r4_3

end Rhs


/-! ## 6. The two bodies' values, at the ι-context -/

section Bodies

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **`⟦(iotaLam) α a motive m⟧ = m`.**  The β-redex, computed. -/
theorem interp_iotaRhsBody_val (hS : L.StableLift) (hn : u.eval M.ls ≠ 0) {α a f m : V}
    (hα : α ∈ U M.κ (v.eval M.ls))
    (ha : a ∈ (interp M L (ectxA ([] : List VExpr) v) (.bvar 0)).toFun (snoc (∅ : V) α))
    (hf : f ∈ (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun
      (snoc (snoc (∅ : V) α) a))
    (hm : m ∈ (interp M L (ectxM ([] : List VExpr) u v) (minTyE v)).toFun
      (snoc (snoc (snoc (∅ : V) α) a) f)) :
    (interp M L (ectxN ([] : List VExpr) u v) (iotaRhsBodyE u v)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) = m := by
  have hON : OnCtx (ectxN ([] : List VExpr) u v) (eqEnv.IsType nv) :=
    onCtx_N (Γ := ([] : List VExpr)) hu hv trivial
  have q1 := hasType_iotaLamE (Γ := ectxN ([] : List VExpr) u v) hu hv hON
  have q2 := hasType_app' q1 (hasType_al_ctxN _) rfl
  have q3 := hasType_app' q2 (hasType_a_ctxN _) rfl
  have q4 := hasType_app' q3 (hasType_mot_ctxN _) rfl
  have hB1 := hasType_ruleType hu hv (ectxN ([] : List VExpr) u v)
  have hB2 := (hasType_piP hu hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered .zero (hasType_al_ctxN _)
  have hB3 := ((hasType_piM hu hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ .zero) (hasType_al_ctxN _)).instN
    eqEnv_ordered .zero (hasType_a_ctxN _)
  have hB4 := (((hasType_piN hv (ectxN ([] : List VExpr) u v)).instN
    eqEnv_ordered (.succ (.succ .zero)) (hasType_al_ctxN _)).instN
    eqEnv_ordered (.succ .zero) (hasType_a_ctxN _)).instN
    eqEnv_ordered .zero (hasType_mot_ctxN _)
  have hq1 := fun hp ↦ hn (eqRuleSort_eval_eq_zero_iff'.1
    ((isProof_iff (L := L) (M := M) hle hON q1 hB1 (eqRuleSort_wf hu hv)).1 hp))
  have hq2 := fun hp ↦ hn (ruleSortP_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q2 hB2 (ruleSortP_wf hu hv)).1 hp))
  have hq3 := fun hp ↦ hn (ruleSortM_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q3 hB3 (ruleSortM_wf hu hv)).1 hp))
  have hq4 := fun hp ↦ hn (ruleSortN_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q4 hB4 (ruleSortN_wf hu)).1 hp))
  -- the ι-context's valuation really is a valuation
  have hc0 : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have hc1 : (snoc (∅ : V) α) ∈ interpCtx M L (ectxA ([] : List VExpr) v) :=
    (mem_interpCtx_cons M L).2 ⟨∅, hc0, α, by rw [interp_sort]; exact hα, rfl⟩
  have hc2 : (snoc (snoc (∅ : V) α) a) ∈ interpCtx M L (ectxP ([] : List VExpr) v) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc1, a, ha, rfl⟩
  have hc3 : (snoc (snoc (snoc (∅ : V) α) a) f) ∈ interpCtx M L (ectxM ([] : List VExpr) u v) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc2, f, hf, rfl⟩
  have hc4 : (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m)
      ∈ interpCtx M L (ectxN ([] : List VExpr) u v) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc3, m, hm, rfl⟩
  rw [interp_app_type M L hq4, interp_app_type M L hq3, interp_app_type M L hq2,
    interp_app_type M L hq1, interp_bvar, interp_bvar, interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, show (4 - 1 - 2 : ℕ) = 1 from rfl,
    show (4 - 1 - 1 : ℕ) = 2 from rfl, show (4 - 1 - 0 : ℕ) = 3 from rfl,
    r4_0, r4_1, r4_2, r4_3,
    interp_closed_ctx_lift M L hS (iotaLamE_closed hu hv) hc4]
  exact interp_iotaLamE_app hu hv hle hn hα ha hf hm

end Bodies


/-! ## 7. The two nests, named, typed, and split

`EqLargeAudit.eqRule_lhs_instL` / `_rhs_instL` say these abbreviations *are* the ι-rule's two
sides at the instantiation `[u, v]`; `lhsA_eq` / `rhsA_eq` re-check that by `rfl`. -/

section Nests

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

abbrev lhsN (u v : VLevel) : VExpr := .lam (minTyE v) (iotaLhsBodyE u v)
abbrev lhsM (u v : VLevel) : VExpr := .lam (motTyE u v) (lhsN u v)
abbrev lhsP (u v : VLevel) : VExpr := .lam (.bvar 0) (lhsM u v)
abbrev lhsA (u v : VLevel) : VExpr := .lam (.sort v) (lhsP u v)

abbrev rhsN (u v : VLevel) : VExpr := .lam (minTyE v) (iotaRhsBodyE u v)
abbrev rhsM (u v : VLevel) : VExpr := .lam (motTyE u v) (rhsN u v)
abbrev rhsP (u v : VLevel) : VExpr := .lam (.bvar 0) (rhsM u v)
abbrev rhsA (u v : VLevel) : VExpr := .lam (.sort v) (rhsP u v)

theorem lhsA_eq : (eqIndDecl.iotaRule 0 0 eqCtor).lhs.instL [u, v] = lhsA u v := rfl
theorem rhsA_eq : (eqIndDecl.iotaRule 0 0 eqCtor).rhs.instL [u, v] = rhsA u v := rfl
theorem ruleTyA_eq : (eqIndDecl.iotaRule 0 0 eqCtor).type.instL [u, v] = ruleTyA u v := rfl

section Typing
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv))

include hu hv hΓ in
theorem hasType_lhsN : eqEnv.HasType nv (ectxM Γ u v) (lhsN u v) (ruleTyN v) :=
  VEnv.HasType.mkLams (As := [minTyE v]) (onCtx_N hu hv hΓ) (hasType_iotaLhsBodyE hu hv Γ)

include hu hv hΓ in
theorem hasType_lhsM : eqEnv.HasType nv (ectxP Γ v) (lhsM u v) (ruleTyM u v) :=
  VEnv.HasType.mkLams (As := [motTyE u v, minTyE v]) (onCtx_N hu hv hΓ)
    (hasType_iotaLhsBodyE hu hv Γ)

include hu hv hΓ in
theorem hasType_lhsP : eqEnv.HasType nv (ectxA Γ v) (lhsP u v) (ruleTyP u v) :=
  VEnv.HasType.mkLams (As := [(.bvar 0 : VExpr), motTyE u v, minTyE v]) (onCtx_N hu hv hΓ)
    (hasType_iotaLhsBodyE hu hv Γ)

include hu hv hΓ in
theorem hasType_iotaRhsBodyE :
    eqEnv.HasType nv (ectxN Γ u v) (iotaRhsBodyE u v) ((minTyE v).lift) :=
  hasType_app' (hasType_app' (hasType_app'
    (hasType_app' (hasType_iotaLamE (Γ := ectxN Γ u v) hu hv (onCtx_N hu hv hΓ))
      (hasType_al_ctxN Γ) rfl) (hasType_a_ctxN Γ) rfl) (hasType_mot_ctxN Γ) rfl)
    (hasType_min_ctxN Γ) rfl

include hu hv hΓ in
theorem hasType_rhsN : eqEnv.HasType nv (ectxM Γ u v) (rhsN u v) (ruleTyN v) :=
  VEnv.HasType.mkLams (As := [minTyE v]) (onCtx_N hu hv hΓ) (hasType_iotaRhsBodyE hu hv hΓ)

include hu hv hΓ in
theorem hasType_rhsM : eqEnv.HasType nv (ectxP Γ v) (rhsM u v) (ruleTyM u v) :=
  VEnv.HasType.mkLams (As := [motTyE u v, minTyE v]) (onCtx_N hu hv hΓ)
    (hasType_iotaRhsBodyE hu hv hΓ)

include hu hv hΓ in
theorem hasType_rhsP : eqEnv.HasType nv (ectxA Γ v) (rhsP u v) (ruleTyP u v) :=
  VEnv.HasType.mkLams (As := [(.bvar 0 : VExpr), motTyE u v, minTyE v]) (onCtx_N hu hv hΓ)
    (hasType_iotaRhsBodyE hu hv hΓ)

end Typing

/-! ### The level branch at each of the four binders -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProp_ruleTyP (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProp M (ectxA ([] : List VExpr) v) (ruleTyP u v) := fun hp ↦
  hn (ruleSortP_eval_eq_zero_iff.1 ((isProp_iff hle (onCtx_A (Γ := ([] : List VExpr)) hv trivial)
    (hasType_piP hu hv _) (ruleSortP_wf hu hv)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProp_ruleTyM (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProp M (ectxP ([] : List VExpr) v) (ruleTyM u v) := fun hp ↦
  hn (ruleSortM_eval_eq_zero_iff.1 ((isProp_iff hle (onCtx_P (Γ := ([] : List VExpr)) hv trivial)
    (hasType_piM hu hv _) (ruleSortM_wf hu hv)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProp_ruleTyN (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProp M (ectxM ([] : List VExpr) u v) (ruleTyN v) := fun hp ↦
  hn (ruleSortN_eval_eq_zero_iff.1 ((isProp_iff hle (onCtx_M (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_piN hv _) (ruleSortN_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProp_iotaTypeE (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProp M (ectxN ([] : List VExpr) u v) ((minTyE v).lift) := fun hp ↦
  hn ((isProp_iff hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_iotaTypeE hv _) hu).1 hp)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_lhsP (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProof M (ectxA ([] : List VExpr) v) (lhsP u v) := fun hp ↦
  hn (ruleSortP_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtx_A (Γ := ([] : List VExpr)) hv trivial) (hasType_lhsP hu hv trivial)
    (hasType_piP hu hv _) (ruleSortP_wf hu hv)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_lhsM (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProof M (ectxP ([] : List VExpr) v) (lhsM u v) := fun hp ↦
  hn (ruleSortM_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtx_P (Γ := ([] : List VExpr)) hv trivial) (hasType_lhsM hu hv trivial)
    (hasType_piM hu hv _) (ruleSortM_wf hu hv)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_lhsN (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProof M (ectxM ([] : List VExpr) u v) (lhsN u v) := fun hp ↦
  hn (ruleSortN_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtx_M (Γ := ([] : List VExpr)) hu hv trivial) (hasType_lhsN hu hv trivial)
    (hasType_piN hv _) (ruleSortN_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_iotaLhsBodyE (hn : u.eval M.ls ≠ 0) :
    ¬ L.IsProof M (ectxN ([] : List VExpr) u v) (iotaLhsBodyE u v) := fun hp ↦
  hn ((isProof_iff (L := L) (M := M) hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_iotaLhsBodyE hu hv _) (hasType_iotaTypeE hv _) hu).1 hp)

end Nests


/-! ## 8. `⟦motive a (Eq.refl α a)⟧` at the ι-context

`EqZeroAudit.interp_minTyE_val` computes this one binder further out; the ι-rule's common *type* is
the same expression lifted, so it has to be recomputed at `ectxN`.  Both `¬IsProof`s here are
**unconditional**: the motive's type and `motive a`'s type both have `.succ u` in codomain position,
so neither sort can be `0`. -/

section IotaType

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv in
theorem hasType_motTyN (Γ : List VExpr) :
    eqEnv.HasType nv (ectxN Γ u v)
      (.forallE (.bvar 3) (.forallE (eqAp v (.bvar 4) (.bvar 3) (.bvar 0)) (.sort u)))
      (.sort (motSortE u v)) :=
  ((hasType_motTyE hu hv Γ).weak eqEnv_ordered).weak eqEnv_ordered

theorem hasType_motA_ctxN (Γ : List VExpr) :
    eqEnv.HasType nv (ectxN Γ u v) (.app (.bvar 1) (.bvar 2))
      (.forallE (eqAp v (.bvar 3) (.bvar 2) (.bvar 2)) (.sort u)) :=
  hasType_app' (hasType_mot_ctxN Γ) (hasType_a_ctxN Γ) rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_mot_ctxN : ¬ L.IsProof M (ectxN ([] : List VExpr) u v) (.bvar 1) := by
  rw [isProof_iff (L := L) (M := M) hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_mot_ctxN _) (hasType_motTyN hu hv _) (motSortE_wf hu hv)]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle in
theorem not_isProof_motA_ctxN :
    ¬ L.IsProof M (ectxN ([] : List VExpr) u v) (.app (.bvar 1) (.bvar 2)) := by
  rw [isProof_iff (L := L) (M := M) hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_motA_ctxN _)
    (.forallEDF (hasType_eqAp hv (hasType_al_ctxN _) (hasType_a_ctxN _) (hasType_a_ctxN _))
      (.sortDF hu hu rfl)) ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

include hu hv hle in
/-- **`⟦motive a (Eq.refl α a)⟧ = (f ‘ a) ‘ •`** at the ι-context. -/
theorem interp_iotaTypeE_val {α a f m : V} :
    (interp M L (ectxN ([] : List VExpr) u v) ((minTyE v).lift)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) = ((f ‘ a) ‘ (pt : V)) := by
  show (interp M L (ectxN ([] : List VExpr) u v)
    (.app (.app (.bvar 1) (.bvar 2)) (.app (.app (.const ``Eq.refl [v]) (.bvar 3))
      (.bvar 2)))).toFun _ = _
  rw [interp_app_type M L (not_isProof_motA_ctxN hu hv hle),
    interp_app_type M L (not_isProof_mot_ctxN hu hv hle),
    interp_app_proof M L (isProof_reflC1_ctxN hv hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)),
    interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 1 : ℕ) = 2 from rfl, show (4 - 1 - 2 : ℕ) = 1 from rfl, r4_1, r4_2]

end IotaType


/-! ## 9. The `≠ 0` slice of the ι-rule

`Cnst.interp_lam_congr_of_type` peels all four binders **uniformly** -- no case analysis at any
binder, because both sides carry the ι-rule's own type -- and the whole level split appears once, at
the bodies.  That is the design note in `Cnst.lean` §"Defining equations", used here for the first
time at an inductive block. -/

section SliceNe

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **The ι-computation, at the ι-context.**  `⟦Eq.rec α a motive m a (Eq.refl α a)⟧ = m`. -/
theorem interp_iotaLhsBody_val (hn : u.eval M.ls ≠ 0) (hspec : EqSpec M v)
    (hcnst : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls))
    {α a f m : V} (hα : α ∈ U M.κ (v.eval M.ls))
    (ha : a ∈ (interp M L (ectxA ([] : List VExpr) v) (.bvar 0)).toFun (snoc (∅ : V) α))
    (hf : f ∈ (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun
      (snoc (snoc (∅ : V) α) a))
    (hm : m ∈ (interp M L (ectxM ([] : List VExpr) u v) (minTyE v)).toFun
      (snoc (snoc (snoc (∅ : V) α) a) f)) :
    (interp M L (ectxN ([] : List VExpr) u v) (iotaLhsBodyE u v)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) = m := by
  have ha' : a ∈ α := by rw [interp_alTy_ctxA, r1_0] at ha; exact ha
  have hf' : f ∈ motSet M.κ (u.eval M.ls) (v.eval M.ls) (snoc (snoc (∅ : V) α) a) := by
    rwa [← motSet_eq_interp_motTyE hu hv hle hspec hα ha'] at hf
  have hm' : m ∈ ((f ‘ a) ‘ (pt : V)) := by rwa [interp_minTyE_val hu hv hle] at hm
  rw [interp_iotaLhsBody_app hu hv hle hn, hcnst]
  exact eqRecFn_app_refl M.κ (u.eval M.ls) (v.eval M.ls) hα ha' hf' hm'

include hu hv hle in
/-- **`⟦lhs⟧ = ⟦rhs⟧` at every non-`Prop` instantiation of the elimination universe.** -/
theorem interp_sides_eq_of_ne (hS : L.StableLift) (hn : u.eval M.ls ≠ 0) (hspec : EqSpec M v)
    (hcnst : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅
      = (interp M L ([] : List VExpr) (rhsA u v)).toFun ∅ := by
  refine interp_lam_congr_of_type hle (onCtx_A (Γ := ([] : List VExpr)) hv trivial)
    (hasType_lhsP hu hv trivial) (hasType_rhsP hu hv trivial) (hasType_piP hu hv _)
    (ruleSortP_wf hu hv) (fun α hα ↦ ?_)
  rw [interp_sort] at hα
  refine interp_lam_congr_of_type hle (onCtx_P (Γ := ([] : List VExpr)) hv trivial)
    (hasType_lhsM hu hv trivial) (hasType_rhsM hu hv trivial) (hasType_piM hu hv _)
    (ruleSortM_wf hu hv) (fun a ha ↦ ?_)
  refine interp_lam_congr_of_type hle (onCtx_M (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_lhsN hu hv trivial) (hasType_rhsN hu hv trivial) (hasType_piN hv _)
    (ruleSortN_wf hu) (fun f hf ↦ ?_)
  refine interp_lam_congr_of_type hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial)
    (hasType_iotaLhsBodyE hu hv _) (hasType_iotaRhsBodyE hu hv trivial)
    (hasType_iotaTypeE hv _) hu (fun m hm ↦ ?_)
  rw [interp_iotaLhsBody_val hu hv hle hn hspec hcnst hα ha hf hm,
    interp_iotaRhsBody_val hu hv hle hS hn hα ha hf hm]

include hu hv hle in
/-- **`⟦lhs⟧ ∈ ⟦type⟧` at every non-`Prop` instantiation.**  Four `mkLam_mem_mkForallType` steps
over *identical* domains -- the ι-rule's binders are the recursor's own, so no domain has to be
recomputed -- and the body step is `m ∈ (f ‘ a) ‘ •`, the minor premise in its own type. -/
theorem interp_lhs_mem_ruleType_of_ne (hn : u.eval M.ls ≠ 0) (hspec : EqSpec M v)
    (hcnst : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅
      ∈ (interp M L ([] : List VExpr) (ruleTyA u v)).toFun ∅ := by
  rw [interp_lam_type M L (not_isProof_lhsP hu hv hle hn),
    interp_forallE_type M L (not_isProp_ruleTyP hu hv hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun α hα ↦ ?_)
  rw [interp_sort] at hα
  rw [interp_lam_type M L (not_isProof_lhsM hu hv hle hn),
    interp_forallE_type M L (not_isProp_ruleTyM hu hv hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun a ha ↦ ?_)
  rw [interp_lam_type M L (not_isProof_lhsN hu hv hle hn),
    interp_forallE_type M L (not_isProp_ruleTyN hu hv hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun f hf ↦ ?_)
  rw [interp_lam_type M L (not_isProof_iotaLhsBodyE hu hv hle hn),
    interp_forallE_type M L (not_isProp_iotaTypeE hu hv hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun m hm ↦ ?_)
  rw [interp_iotaLhsBody_val hu hv hle hn hspec hcnst hα ha hf hm, interp_iotaTypeE_val hu hv hle]
  rwa [interp_minTyE_val hu hv hle] at hm

end SliceNe


/-! ## 10. The `= 0` slice of the ι-rule

At a `Prop` elimination universe the ι-rule's type is itself a proposition
(`EqLargeAudit.eqRuleSort_eval_eq_zero_iff`), so **both sides are `•`** and the equation has no
set-theoretic content -- one `interp_lam_proof` per side.  The membership half is not free: it is
four `mkForallProp` steps ending at `• ∈ (f ‘ a) ‘ •`, which needs the motive's values to be truth
values (`EqZeroAudit.motive_value_mem_UProp`, where `h0` is spent) plus the minor premise to
witness that this one is *true*. -/

section SliceZero

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable (h0 : u.eval M.ls = 0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProof_lhsP : L.IsProof M (ectxA ([] : List VExpr) v) (lhsP u v) :=
  (isProof_iff (L := L) (M := M) hle (onCtx_A (Γ := ([] : List VExpr)) hv trivial)
    (hasType_lhsP hu hv trivial) (hasType_piP hu hv _)
    (ruleSortP_wf hu hv)).2 (ruleSortP_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProof_rhsP : L.IsProof M (ectxA ([] : List VExpr) v) (rhsP u v) :=
  (isProof_iff (L := L) (M := M) hle (onCtx_A (Γ := ([] : List VExpr)) hv trivial)
    (hasType_rhsP hu hv trivial) (hasType_piP hu hv _)
    (ruleSortP_wf hu hv)).2 (ruleSortP_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProp_ruleTyP : L.IsProp M (ectxA ([] : List VExpr) v) (ruleTyP u v) :=
  (isProp_iff hle (onCtx_A (Γ := ([] : List VExpr)) hv trivial) (hasType_piP hu hv _)
    (ruleSortP_wf hu hv)).2 (ruleSortP_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProp_ruleTyM : L.IsProp M (ectxP ([] : List VExpr) v) (ruleTyM u v) :=
  (isProp_iff hle (onCtx_P (Γ := ([] : List VExpr)) hv trivial) (hasType_piM hu hv _)
    (ruleSortM_wf hu hv)).2 (ruleSortM_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProp_ruleTyN : L.IsProp M (ectxM ([] : List VExpr) u v) (ruleTyN v) :=
  (isProp_iff hle (onCtx_M (Γ := ([] : List VExpr)) hu hv trivial) (hasType_piN hv _)
    (ruleSortN_wf hu)).2 (ruleSortN_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle h0 in
theorem isProp_iotaTypeE : L.IsProp M (ectxN ([] : List VExpr) u v) ((minTyE v).lift) :=
  (isProp_iff hle (onCtx_N (Γ := ([] : List VExpr)) hu hv trivial) (hasType_iotaTypeE hv _)
    hu).2 h0

include hu hv hle h0 in
/-- **Both sides are `•` at a `Prop` elimination universe.** -/
theorem interp_sides_eq_of_zero :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅
      = (interp M L ([] : List VExpr) (rhsA u v)).toFun ∅ := by
  rw [interp_lam_proof M L (isProof_lhsP hu hv hle h0),
    interp_lam_proof M L (isProof_rhsP hu hv hle h0)]

include hu hv hle h0 in
/-- **`• ∈ ⟦type⟧` at a `Prop` elimination universe.** -/
theorem interp_lhs_mem_ruleType_of_zero (hspec : EqSpec M v) :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅
      ∈ (interp M L ([] : List VExpr) (ruleTyA u v)).toFun ∅ := by
  rw [interp_lam_proof M L (isProof_lhsP hu hv hle h0)]
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyP hu hv hle h0)).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sort] at hα
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyM hu hv hle h0)).2 ⟨rfl, fun a ha ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyN hu hv hle h0)).2 ⟨rfl, fun f hf ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L (isProp_iotaTypeE hu hv hle h0)).2 ⟨rfl, fun m hm ↦ ?_⟩
  have ha' : a ∈ α := by rw [interp_alTy_ctxA, r1_0] at ha; exact ha
  have hm' : m ∈ ((f ‘ a) ‘ (pt : V)) := by rwa [interp_minTyE_val hu hv hle] at hm
  have hX : ((f ‘ a) ‘ (pt : V)) ∈ (UProp : V) :=
    motive_value_mem_UProp hu hv hle h0 hf ha'
      (by rw [hspec α hα a ha' a ha', if_pos rfl]; exact mem_singleton_iff.2 rfl)
  rw [interp_iotaTypeE_val hu hv hle]
  rcases eq_empty_or_eq_true_of_mem_UProp hX with h | h
  · exact absurd (h ▸ hm') not_mem_empty
  · rw [h]; exact mem_singleton_iff.2 rfl

end SliceZero


/-! ## 11. `InductOracleOK`'s `rules` field at `eqIndDecl`

`eqIndDecl.iotaRules` is a **singleton** (`EqLargeAudit.eq_iotaRules_eq`, `rfl`), so the field is
exactly `DefEqOK` at `eqIndDecl.iotaRule 0 0 eqCtor`.  The two hypotheses on the model are the same
two the recursor's `consts` cell needs -- `EqSpec` at every level and the `Eq.rec` value -- plus
`L.Stable`, which only the right-hand side's β-redex uses. -/

section Rules

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}

/-- **`DefEqOK` at `eqIndDecl`'s ι-rule**, both level slices, at any model meeting `EqSpec` and
assigning `Eq.rec` the value `eqRecVal`. -/
theorem defEqOK_eqRule (hS : L.StableLift) (hle : eqEnv ≤ envF)
    (hspec : ∀ w : VLevel, EqSpec M w)
    (hcnst : ∀ us : List VLevel, M.cnst ``Eq.rec us = eqRecVal M.κ M.ls us) :
    DefEqOK L M (eqIndDecl.iotaRule 0 0 eqCtor) := by
  intro us hw hlen
  rw [eqRule_uvars] at hlen
  obtain ⟨u, v, rfl⟩ := eq_pair_of_length_two hlen
  have hu : u.WF nv := hw u (by simp)
  have hv : v.WF nv := hw v (by simp)
  rw [lhsA_eq, rhsA_eq, ruleTyA_eq]
  by_cases h0 : u.eval M.ls = 0
  · exact ⟨Above.pure (interp_sides_eq_of_zero hu hv hle h0),
      Above.pure (interp_lhs_mem_ruleType_of_zero hu hv hle h0 (hspec v))⟩
  · have hc : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls) := by
      rw [hcnst, eqRecVal_pair, if_neg h0]
    exact ⟨Above.pure (interp_sides_eq_of_ne hu hv hle hS h0 (hspec v) hc),
      Above.pure (interp_lhs_mem_ruleType_of_ne hu hv hle h0 (hspec v) hc)⟩

/-- **The `rules` field of `InductOracleOK` at `eqIndDecl`.** -/
theorem inductOracleOK_rules_Eq (hS : L.StableLift) (hle : eqEnv ≤ envF)
    (hspec : ∀ w : VLevel, EqSpec M w)
    (hcnst : ∀ us : List VLevel, M.cnst ``Eq.rec us = eqRecVal M.κ M.ls us) :
    ∀ df ∈ eqIndDecl.iotaRules, DefEqOK L M df := by
  intro df hdf
  rw [eq_iotaRules_eq] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  exact defEqOK_eqRule hS hle hspec hcnst

/-- **…at the shared witness `SetModel.preludeWitness`** -- the assignment `PreludeOracle.lean`
actually uses (`NEAudit.neM_eq`).  No side oracle parameter, no chosen `κ`, no chain hypothesis. -/
theorem inductOracleOK_rules_Eq_preludeWitness (hS : L.StableLift) (hle : eqEnv ≤ envF)
    (κ : ℕ → V) (ls : List ℕ) :
    ∀ df ∈ eqIndDecl.iotaRules, DefEqOK L (preludeWitness κ ls) df :=
  inductOracleOK_rules_Eq hS hle (preludeWitness_eq κ ls) (preludeWitness_cnst_eqRec κ ls)

/-! ### Anti-vacuity: the membership half is not satisfied by every set

`DefEqOK`'s second conjunct is a membership, and a membership in a `mkForallType` over an *empty*
domain is satisfied by `∅ = •` (`UnitAudit`'s note).  Here is the same statement with `•` in place
of `⟦lhs⟧`, **refuted**, at one `L`, one `M`, one level tuple and one `interp` -- so
`interp_lhs_mem_ruleType_of_ne` is a statement about the value and not about the type. -/

theorem pt_not_mem_ruleType_of_ne {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
    (hle : eqEnv ≤ envF) (hn : u.eval M.ls ≠ 0) {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    (pt : V) ∉ (interp M L ([] : List VExpr) (ruleTyA u v)).toFun ∅ := by
  rw [interp_forallE_type M L (not_isProp_ruleTyP hu hv hle hn)]
  refine UnitAudit.pt_not_mem_mkForallType_of_nonempty (x := x) ?_
  rw [interp_sort]
  exact hx

/-- **The ι-rule's membership half discriminates.**  One environment, one `L`, one `M`, one level
tuple, **one `interp`**: `⟦lhs⟧` is in the rule's type and `•` -- the value the `= 0` slice hands
the same cell -- is not.  The `≠ 0` slice of the ι-rule is therefore not the `= 0` slice's
statement in disguise. -/
theorem eqRule_discriminates {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
    (hn : u.eval M.ls ≠ 0) (hspec : EqSpec M v)
    (hcnst : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls))
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅
        ∈ (interp M L ([] : List VExpr) (ruleTyA u v)).toFun ∅ ∧
      (pt : V) ∉ (interp M L ([] : List VExpr) (ruleTyA u v)).toFun ∅ :=
  ⟨interp_lhs_mem_ruleType_of_ne hu hv hle hn hspec hcnst,
    pt_not_mem_ruleType_of_ne hu hv hle hn hx⟩

/-- …and therefore the two sides' common value is **not** `•` at a non-`Prop` elimination
universe, which the `= 0` slice's `interp_sides_eq_of_zero` says it is there. -/
theorem interp_lhs_ne_pt_of_ne {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
    (hle : eqEnv ≤ envF) (hn : u.eval M.ls ≠ 0) (hspec : EqSpec M v)
    (hcnst : M.cnst ``Eq.rec [u, v] = eqRecFn M.κ (u.eval M.ls) (v.eval M.ls))
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u v)).toFun ∅ ≠ (pt : V) := fun h ↦
  (pt_not_mem_ruleType_of_ne hu hv hle hn hx)
    (h ▸ interp_lhs_mem_ruleType_of_ne hu hv hle hn hspec hcnst)

end Rules


/-! ## 13. **`InductOracleOK` at `eqIndDecl`, assembled**

Both fields, at the shared witness.  The `consts` cells were already in the tree:
`EqTFAudit.oracleOK_Eq` (the type former), `EqZeroAudit.pt_mem_interp_EqReflType` (the
constructor -- packaged as an `OracleOK` here for the first time) and
`IffLargeAudit.oracleOK_EqRec_preludeWitness` (the recursor, both level slices).  §11 supplies
`rules`.  The only hypotheses are `hle : eqEnv ≤ envF` (discharged at `preludeEnv` by
`EqAudit.eqEnv_le_preludeEnv`) and `hS : L.Stable`. -/

section Assemble

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- The block's three constants, **with their types** -- not just their names, as
`EqAudit.eq_allConsts` gives.  `rfl`, so this is a measurement of `eqIndDecl`. -/
theorem eq_allConsts' : eqIndDecl.allConsts =
    [(``Eq, ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩),
     (``Eq.refl, ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (eqAp (.param 0) (.bvar 1) (.bvar 0) (.bvar 0)))⟩),
     (``Eq.rec, ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩)] := rfl

theorem preludeWitness_cnst_eqRefl (us : List VLevel) :
    (preludeWitness (V := V) κ ls).cnst ``Eq.refl us = (pt : V) := by
  simp [preludeWitness, pt]

/-- **The constructor cell, as an `OracleOK`.**  `EqZeroAudit.pt_mem_interp_EqReflType` is the
membership; this adds the level-congruence field, which is `rfl` because the value is `•` at every
instantiation. -/
theorem oracleOK_EqRefl (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Eq.refl
      ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (eqAp (.param 0) (.bvar 1) (.bvar 0) (.bvar 0)))⟩ :=
  oracleOK_of (L := L)
    (fun _ _ _ ↦ by rw [preludeWitness_cnst_eqRefl, preludeWitness_cnst_eqRefl])
    (fun {us} hw hlen ↦ by
      obtain ⟨w, rfl⟩ := NEAudit.eq_singleton_of_length_one hlen
      rw [preludeWitness_cnst_eqRefl]
      exact pt_mem_interp_EqReflType (hw w (List.mem_singleton.2 rfl)) hle
        (preludeWitness_eq κ ls w))

/-- **The `consts` field at `eqIndDecl`**, all three cells. -/
theorem inductOracleOK_consts_Eq (hle : eqEnv ≤ envF) :
    ∀ p ∈ eqIndDecl.allConsts,
      OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst p.1 p.2 := by
  intro p hp
  rw [eq_allConsts'] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact EqTFAudit.oracleOK_Eq L κ ls hle
  · exact oracleOK_EqRefl L κ ls hle
  · exact IffLargeAudit.oracleOK_EqRec_preludeWitness L κ ls hle

/-- **`InductOracleOK` at `eqIndDecl`.**  Both fields, at `SetModel.preludeWitness` --
the assignment `PreludeOracle.lean` uses (`NEAudit.neM_eq`).  No side oracle parameter, no chosen
`κ`, no chain hypothesis; `Above` is discharged by `Above.pure` throughout. -/
theorem inductOracleOK_Eq (hS : L.StableLift) (hle : eqEnv ≤ envF) :
    InductOracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst eqIndDecl :=
  ⟨inductOracleOK_consts_Eq L κ ls hle,
    inductOracleOK_rules_Eq_preludeWitness hS hle κ ls⟩

/-! ## The payoff of the `StableLift` weakening

`inductOracleOK_Eq` above is stated at an arbitrary `L` and therefore still carries a hypothesis.
Instantiating it at the split `UpperBound.OracleInput` actually fixes discharges that hypothesis
outright, because `StableLift` is *free* there (`propSplitUp_stableLift` needs only `Ordered`,
`PropUniq`, `PropTypeAgree` -- and `hU`/`hT` are already **data** arguments of `propSplitUp`, which
`OracleInput` takes, so this adds no obligation at the consumer).

What this does **not** buy: `InstDescendUp` does not leave the main theorem.  `interp_inst` still
needs the two `inst` fields, so `ModelFits` and `UpperBound.consistent_of_inputs` still do.  What
leaves is that input's appearance in the prelude's `.induct` steps, and no more. -/
theorem inductOracleOK_Eq_at_propSplitUp {envF : VEnv} {nv : ℕ} (henv : envF.Ordered)
    (hU : envF.PropUniq nv) (hT : envF.PropTypeAgree nv) (κ : ℕ → V) (ls : List ℕ)
    (hle : eqEnv ≤ envF) :
    InductOracleOK (propSplitUp envF nv henv hU hT) κ ls
      (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst eqIndDecl :=
  inductOracleOK_Eq _ κ ls (propSplitUp_stableLift henv hU hT) hle

#print axioms Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_Eq_at_propSplitUp

end Assemble

/-! ## 12. Axiom audit, **by namespace**

This file declares into `Lean4Lean.SetModel.EqIotaAudit`; the names it reuses live in
`Lean4Lean.SetModel` (`eqRecFn`, `preludeWitness`, `interp_closed_ctx`),
`…EqAudit`, `…EqZeroAudit`, `…EqLargeAudit` and `…UnitAudit`.  Every name below is
`Lean4Lean.SetModel.EqIotaAudit.*` unless written out. -/

#print axioms Lean4Lean.SetModel.EqIotaAudit.eqEnv_ordered
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_EqRecC
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_a_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_mot_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_min_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_reflAp_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_iotaLhsBodyE
#print axioms Lean4Lean.SetModel.EqIotaAudit.isProof_reflC1_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_iotaLhsBody_app
#print axioms Lean4Lean.SetModel.EqIotaAudit.eqRecFn_app_refl
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_iotaTypeE
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_piN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_piM
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_piP
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_ruleType
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_iotaLamE
#print axioms Lean4Lean.SetModel.EqIotaAudit.iotaLamE_closed
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_iotaLamE_app
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_iotaRhsBody_val
#print axioms Lean4Lean.SetModel.EqIotaAudit.lhsA_eq
#print axioms Lean4Lean.SetModel.EqIotaAudit.rhsA_eq
#print axioms Lean4Lean.SetModel.EqIotaAudit.ruleTyA_eq
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_lhsP
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_iotaRhsBodyE
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_rhsP
#print axioms Lean4Lean.SetModel.EqIotaAudit.not_isProp_ruleTyP
#print axioms Lean4Lean.SetModel.EqIotaAudit.not_isProof_lhsP
#print axioms Lean4Lean.SetModel.EqIotaAudit.not_isProof_iotaLhsBodyE
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_motTyN
#print axioms Lean4Lean.SetModel.EqIotaAudit.hasType_motA_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.not_isProof_mot_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.not_isProof_motA_ctxN
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_iotaTypeE_val
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_iotaLhsBody_val
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_sides_eq_of_ne
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_lhs_mem_ruleType_of_ne
#print axioms Lean4Lean.SetModel.EqIotaAudit.isProof_lhsP
#print axioms Lean4Lean.SetModel.EqIotaAudit.isProof_rhsP
#print axioms Lean4Lean.SetModel.EqIotaAudit.isProp_ruleTyP
#print axioms Lean4Lean.SetModel.EqIotaAudit.isProp_iotaTypeE
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_sides_eq_of_zero
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_lhs_mem_ruleType_of_zero
#print axioms Lean4Lean.SetModel.EqIotaAudit.defEqOK_eqRule
#print axioms Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_rules_Eq
#print axioms Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_rules_Eq_preludeWitness
#print axioms Lean4Lean.SetModel.EqIotaAudit.pt_not_mem_ruleType_of_ne
#print axioms Lean4Lean.SetModel.EqIotaAudit.eqRule_discriminates
#print axioms Lean4Lean.SetModel.EqIotaAudit.interp_lhs_ne_pt_of_ne
#print axioms Lean4Lean.SetModel.EqIotaAudit.eq_allConsts'
#print axioms Lean4Lean.SetModel.EqIotaAudit.oracleOK_EqRefl
#print axioms Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_consts_Eq
#print axioms Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_Eq


end Lean4Lean.SetModel.EqIotaAudit
