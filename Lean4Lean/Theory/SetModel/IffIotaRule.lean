import Lean4Lean.Theory.SetModel.IffConsts
import Lean4Lean.Theory.SetModel.StablePrelude  -- 2026-09-03: `L.Stable` is weakened to `L.StableLift` throughout this file.  The two are NOT interchangeable in general -- `PropSplit.stable_iff_lift_and_inst` splits `Stable` into a lift half and an inst half -- but no consumer mixes them, and `interp_closed_ctx`, the ONLY substantive use of `hS` here, is a corollary of the lift half alone (`interp_closed_ctx_lift`).  The point is that the lift half is FREE at the split `UpperBound.OracleInput` fixes: `propSplitUp_stableLift` needs only `env.Ordered`, `PropUniq`, `PropTypeAgree` -- the inputs `propSplitUp` already takes.  Full `Stable` is not free and never will be: `propSplitUp_stable_iff` proves it is EQUIVALENT to `env.InstDescendUp nv`, an open assumption whose only producers are `PropDescend` (no producer anywhere) and `UpperBound.InstDescendInput`.  So this weakening is what makes `inductOracleOK_*` `hle`-only.

/-!
# `iffIndDecl`'s ι-rule: `InductOracleOK`'s `rules` field at the `Iff` block

`IffConsts.lean` §4 completes the `consts` field at this block; this file supplies `rules`, and §14
assembles **`InductOracleOK` at `iffIndDecl`** -- both fields, at the shared
`SetModel.preludeWitness`.  `EqIotaRule.lean` is the template section for section; what is new is
listed in §10, and the four structural differences from `eqIndDecl` are:

1. **Six binders, not four.**  `iffIndDecl` has two parameters and its constructor has **two
   fields**; `eqIndDecl` has two parameters and no fields.  So the ι-context is
   `[mpr, mp, minor, motive, b, a]` and both sides are six-fold λ-nests, with a **six**-fold β-redex
   on the right.
2. **The ι-context is `IffAudit.ictxN` plus the two fields** (`iff_iotaCtx_reverse`, `rfl`), so
   everything `IffOracle.lean` and `IffRecLarge.lean` state at `ictxA`/`ictxB`/`ictxM`/`ictxN`
   transfers by `.weak`.  What does **not** transfer is anything at `ictxP`/`ictxQ` -- the contexts
   *inside* the minor premise, which omit the minor-premise binder.  Every index there is one lower
   than the ι-context's, so `impSet01_eq_interp_mpTy`, `impSet10_eq_interp_mprTy`,
   `hasType_introC3`, `isProof_introC3` and `eq_of_mem_mpTy_mprTy` all had to be restated (§§3, 10).
   The binder the recursor's contexts lack is the **minor premise**, not the motive.
3. **The ι-computation *applies* the minor premise.**  `eqRecFn`'s innermost body reads it;
   `iffRecFn`'s is `((ρ ‘ 3) ‘ •) ‘ •`.  So the rule is true only because both constructor fields are
   forced to `•` -- their types are propositions, so `interp` takes the impredicative branch and
   every member of a `mkForallProp` is `•` (`mp_eq_pt`, `mpr_eq_pt`).  `a = b`, which
   `iffRecFn`'s last `mkLam` domain needs, comes from those same two binders being *inhabited*
   (`eq_of_mem_mpTyJ_mprTyJ`).
4. **The `= 0` slice needs no `IffSpec`.**  At the recursor cell `IffSpec` is spent turning the major
   premise's existence into `a = b`; the ι-rule has no major-premise binder and gets `a = b` from the
   fields.  This is the only obligation at this block free of the block's own spec.

Both slices split on `u.eval M.ls = 0` exactly as the recursor cell does, and the ι-rule's own sort
has the same branch (`iffRuleSort_eval_eq_zero_iff`).

## Bounds

`Above` occurs in **no hypothesis** here: both `DefEqOK` conjuncts are produced by `Above.pure`, at
an arbitrary `κ : ℕ → V`, with no `IsInaccessibleChain` anywhere.  Unlike `EqIotaAudit`'s controls,
the negative control `pt_not_mem_ruleType_of_ne` needs **no** hypothesis about the parameter space
either: the outermost binder is a parameter over `Prop` and `∅ ∈ U κ 0` at every `κ`.
Two hypotheses remain: `hle : iffEnv ≤ envF`, discharged at `preludeEnv` by
`IffAudit.iffEnv_le_preludeEnv`, and **`hS : L.Stable`**, undischarged in this tree -- see §7.
-/

namespace Lean4Lean.SetModel.IffIotaAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.IffAudit
open Lean4Lean.SetModel.IffLargeAudit
open scoped Classical

/-! ## 1. The ι-rule's three components, measured -/

section Shapes

/-- `Iff.intro`, as the block stores it. -/
abbrev iffCtor : VIndCtor := ((iffIndDecl.types.getD 0 default).ctors.getD 0 default)

theorem iff_iotaRules_eq : iffIndDecl.iotaRules = [iffIndDecl.iotaRule 0 0 iffCtor] := rfl

theorem iffRule_uvars : (iffIndDecl.iotaRule 0 0 iffCtor).uvars = 1 := rfl

/-- `mp : a → b`, over the ι-context's tail `[minor, motive, b, a]` -- **one binder deeper** than
`IffAudit.ictxP`'s spelling, because the ι-context binds the minor premise. -/
abbrev mpTyJ : VExpr := .forallE (.bvar 3) (.bvar 3)
/-- `mpr : b → a`, over `[mp, minor, motive, b, a]`. -/
abbrev mprTyJ : VExpr := .forallE (.bvar 3) (.bvar 5)

variable (Γ : List VExpr)

/-- `mp, minor, motive, b, a`. -/
abbrev jctxP (u : VLevel) : List VExpr := mpTyJ :: ictxN Γ u
/-- **The ι-context**: `mpr, mp, minor, motive, b, a`. -/
abbrev jctxQ (u : VLevel) : List VExpr := mprTyJ :: jctxP Γ u

/-- The ι-rule's common type at its innermost binder: `motive (Iff.intro a b mp mpr)`. -/
abbrev iotaTypeJ : VExpr := .app (.bvar 3) (introAp (.bvar 5) (.bvar 4) (.bvar 1) (.bvar 0))

theorem iff_iotaCtx : iffIndDecl.iotaCtx iffCtor
    = [.sort .zero, .sort .zero, motTyI (.param 0), minTyI, mpTyJ, mprTyJ] := rfl

theorem iff_iotaCtx_reverse (u : VLevel) :
    ((iffIndDecl.iotaCtx iffCtor).map (VExpr.instL [u])).reverse = jctxQ [] u := rfl

theorem iff_iotaType (u : VLevel) :
    (iffIndDecl.iotaType 0 iffCtor).instL [u] = iotaTypeJ := rfl

/-- **`(minTyI).lift` is the ι-rule's type after its four outer binders.** -/
theorem minTyI_lift_eq : (minTyI.lift) = .forallE mpTyJ (.forallE mprTyJ iotaTypeJ) := rfl

/-- **The left-hand side**: `λ a b motive minor mp mpr, Iff.rec a b motive minor
(Iff.intro a b mp mpr)`. -/
theorem iffRule_lhs_instL (u : VLevel) :
    (iffIndDecl.iotaRule 0 0 iffCtor).lhs.instL [u]
      = .lam (.sort .zero) (.lam (.sort .zero) (.lam (motTyI u) (.lam minTyI
          (.lam mpTyJ (.lam mprTyJ
            (.app (.app (.app (.app (.app (.const ``Iff.rec [u]) (.bvar 5)) (.bvar 4))
              (.bvar 3)) (.bvar 2)) (introAp (.bvar 5) (.bvar 4) (.bvar 1) (.bvar 0)))))))) := rfl

/-- **The right-hand side**: the η-expansion, i.e. a **six**-fold β-redex over
`λ a b motive minor mp mpr, minor mp mpr`. -/
theorem iffRule_rhs_instL (u : VLevel) :
    (iffIndDecl.iotaRule 0 0 iffCtor).rhs.instL [u]
      = .lam (.sort .zero) (.lam (.sort .zero) (.lam (motTyI u) (.lam minTyI
          (.lam mpTyJ (.lam mprTyJ
            (.app (.app (.app (.app (.app (.app
              (.lam (.sort .zero) (.lam (.sort .zero) (.lam (motTyI u) (.lam minTyI
                (.lam mpTyJ (.lam mprTyJ (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))))))
              (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))))) := rfl

/-- **The common type**: `∀ a b motive minor, (minTyI).lift`. -/
theorem iffRule_type_instL (u : VLevel) :
    (iffIndDecl.iotaRule 0 0 iffCtor).type.instL [u]
      = .forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (motTyI u)
          (.forallE minTyI (.forallE mpTyJ (.forallE mprTyJ iotaTypeJ))))) := rfl

end Shapes

/-! ## 2. `iffEnv` is `Ordered`, and the two field binders typed at the ι-context

The ι-context is `IffAudit.ictxN` extended by the two constructor fields, so every typing
derivation of `IffOracle.lean` §3 and `IffRecLarge.lean` §§4--5 that is stated at `ictxN` transfers
by `.weak`; what does **not** transfer is anything stated at `ictxP`/`ictxQ`, the contexts *inside*
the minor premise, because those omit the minor premise binder itself.  Every index there is one
lower than the ι-context's. -/

section Env

theorem iffEnv_WF' : iffEnv.WF :=
  ⟨_, .decl (.induct (iffIndDecl_WF _) iffEnv_add)
    (.decl (.induct (eqIndDecl_WF _) eqEnv_add) .empty)⟩

theorem iffEnv_ordered : iffEnv.Ordered := VEnv.WF.ordered iffEnv_WF'

end Env

section Ctx

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable (Γ : List VExpr)

/-! ### The ι-context's six entries, indexed

`jctxP = [mp, minor, motive, b, a]` and `jctxQ = [mpr, mp, minor, motive, b, a]`, so at the
ι-context `a` is `.bvar 5` and `b` is `.bvar 4` -- **one higher** than at `IffAudit.ictxQ`, whose
five entries are `[mpr, mp, motive, b, a]`: that context omits the minor premise. -/

/-- Inside `mp`'s own arrow, over `[minor, motive, b, a]`. -/
abbrev jctxPa (w : VLevel) : List VExpr := (.bvar 3 : VExpr) :: ictxN Γ w
/-- Inside `mpr`'s own arrow, over `[mp, minor, motive, b, a]`. -/
abbrev jctxQb (w : VLevel) : List VExpr := (.bvar 3 : VExpr) :: jctxP Γ w

theorem hasType_b_jctxPa : iffEnv.HasType nv (jctxPa Γ u) (.bvar 3) (.sort .zero) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_b_jctxP : iffEnv.HasType nv (jctxP Γ u) (.bvar 3) (.sort .zero) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_a_jctxP : iffEnv.HasType nv (jctxP Γ u) (.bvar 4) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

theorem hasType_a_jctxQb : iffEnv.HasType nv (jctxQb Γ u) (.bvar 5) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))

theorem hasType_a_jctxQ : iffEnv.HasType nv (jctxQ Γ u) (.bvar 5) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))

theorem hasType_b_jctxQ : iffEnv.HasType nv (jctxQ Γ u) (.bvar 4) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

/-- `mp : a → b`, at the context it is *declared* in (`ictxN`, one binder deeper than
`IffAudit.hasType_mpTyI`'s `ictxM`). -/
theorem hasType_mpTyJ : iffEnv.HasType nv (ictxN Γ u) mpTyJ (.sort mpSortI) :=
  .forallEDF (.bvar (.succ (.succ (.succ .zero)))) (hasType_b_jctxPa Γ)

/-- `mpr : b → a`, one binder further in. -/
theorem hasType_mprTyJ : iffEnv.HasType nv (jctxP Γ u) mprTyJ (.sort mpSortI) :=
  .forallEDF (hasType_b_jctxP Γ) (hasType_a_jctxQb Γ)

include hu in
theorem onCtxJ_P (hΓ : OnCtx Γ (iffEnv.IsType nv)) : OnCtx (jctxP Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_N hu hΓ, _, hasType_mpTyJ Γ⟩

include hu in
theorem onCtxJ_Q (hΓ : OnCtx Γ (iffEnv.IsType nv)) : OnCtx (jctxQ Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxJ_P hu Γ hΓ, _, hasType_mprTyJ Γ⟩

end Ctx

/-! ## 3. The recursor spine at the ι-context, and its five prefixes

`interp`'s `app` clause consults `L.IsProof` at **each prefix**, so the five prefixes of
`Iff.rec a b motive minor (Iff.intro a b mp mpr)` are typed individually and each type's sort is
exhibited.  As at `eqIndDecl`, every `.inst` equation is `rfl`: the arguments are `.bvar`
numerals, so `VExpr.inst` and the `VExpr.liftN 0` it produces are closed computations. -/

section Spine

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable (Γ : List VExpr)

include hu in
/-- `Iff.rec.{u}`, with its type in the `.forallE` shape `EqAudit.hasType_app'` can consume. -/
theorem hasType_IffRecC :
    iffEnv.HasType nv Γ (.const ``Iff.rec [u]) (.forallE (.sort .zero) (recBB u)) := by
  have h : iffEnv.HasType nv Γ (.const ``Iff.rec [u]) ((iffIndDecl.recType 0).instL [u]) :=
    .constDF iffEnv_IffRecC (by simp [hu]) (by simp [hu]) rfl (.cons (by rfl) .nil)
  rwa [iffRecType_instL] at h

/-- The motive variable at the ι-context: **`.bvar 3`**, with `a` at `5` and `b` at `4`.
`IffAudit.hasType_mot_ctxQ` is the same statement one binder lower and does not apply. -/
theorem hasType_mot_jctxQ :
    iffEnv.HasType nv (jctxQ Γ u) (.bvar 3)
      (.forallE (iffAp (.bvar 5) (.bvar 4)) (.sort u)) :=
  .bvar (.succ (.succ (.succ .zero)))

/-- The minor premise variable at the ι-context, `.bvar 2`, its type lifted three times. -/
theorem hasType_min_jctxQ :
    iffEnv.HasType nv (jctxQ Γ u) (.bvar 2) (minTyI.lift.lift.lift) :=
  .bvar (.succ (.succ .zero))

include hu in
/-- The motive's own type at the ι-context, with its sort. -/
theorem hasType_motTyJ :
    iffEnv.HasType nv (jctxQ Γ u) (.forallE (iffAp (.bvar 5) (.bvar 4)) (.sort u))
      (.sort (motSortI u)) :=
  .forallEDF (hasType_iffAp (hasType_a_jctxQ Γ) (hasType_b_jctxQ Γ)) (.sortDF hu hu rfl)

/-- **`Iff.intro a b mp : (b → a) → Iff a b` at the ι-context** -- `IffLargeAudit.hasType_introC3`
one binder lower, so restated here with `a` at `5`, `b` at `4`. -/
theorem hasType_introC3J :
    iffEnv.HasType nv (jctxQ Γ u)
      (.app (.app (.app (.const ``Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1))
      (.forallE (.forallE (.bvar 4) (.bvar 6)) (iffAp (.bvar 6) (.bvar 5))) :=
  .appDF (.appDF (.appDF (hasType_IffIntro (jctxQ Γ u)) (hasType_a_jctxQ Γ))
    (hasType_b_jctxQ Γ)) (.bvar (.succ .zero))

/-- …and its sort, `imax (imax 0 0) 0`, which is `0` at **every** level valuation. -/
theorem hasType_introC3JTy :
    iffEnv.HasType nv (jctxQ Γ u)
      (.forallE (.forallE (.bvar 4) (.bvar 6)) (iffAp (.bvar 6) (.bvar 5)))
      (.sort (.imax mpSortI .zero)) :=
  .forallEDF
    (.forallEDF (hasType_b_jctxQ Γ)
      (.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
    (hasType_iffAp (.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))

/-- `Iff.intro a b mp mpr : Iff a b` at the ι-context. -/
theorem hasType_introAp_jctxQ :
    iffEnv.HasType nv (jctxQ Γ u)
      (introAp (.bvar 5) (.bvar 4) (.bvar 1) (.bvar 0)) (iffAp (.bvar 5) (.bvar 4)) :=
  .appDF (hasType_introC3J Γ) (.bvar .zero)

/-- The ι-rule's left-hand body. -/
abbrev iotaLhsBodyJ (u : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Iff.rec [u]) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2))
    (introAp (.bvar 5) (.bvar 4) (.bvar 1) (.bvar 0))

include hu in
/-- **The left-hand body, typed at the ι-context**, with the ι-rule's own common type.  Five
`EqAudit.hasType_app'` steps, every `.inst` equation `rfl`. -/
theorem hasType_iotaLhsBodyJ :
    iffEnv.HasType nv (jctxQ Γ u) (iotaLhsBodyJ u) iotaTypeJ :=
  EqAudit.hasType_app' (EqAudit.hasType_app' (EqAudit.hasType_app' (EqAudit.hasType_app'
    (EqAudit.hasType_app' (hasType_IffRecC hu (jctxQ Γ u)) (hasType_a_jctxQ Γ) rfl)
    (hasType_b_jctxQ Γ) rfl) (hasType_mot_jctxQ Γ) rfl) (hasType_min_jctxQ Γ) rfl)
    (hasType_introAp_jctxQ Γ) rfl

/-- The innermost body's sort is `u` itself: `motive (Iff.intro a b mp mpr) : Sort u`. -/
theorem hasType_iotaTypeJ :
    iffEnv.HasType nv (jctxQ Γ u) iotaTypeJ (.sort u) :=
  .appDF (hasType_mot_jctxQ Γ) (hasType_introAp_jctxQ Γ)

end Spine

/-! ## 4. The rule's own type, one binder at a time

Six `.forallE` layers, of which the inner two **are** `minTyI.lift` (`minTyI_lift_eq`, `rfl`): the
ι-rule's type is the *minor premise's* type generalised over the block's parameters, motive and
minor premise, exactly as at `eqIndDecl`.  Its sort's level branch is therefore the recursor's
(`IffAudit.iffRecSort_eval_eq_zero_iff`) once more. -/

section RuleType

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable (Γ : List VExpr)

abbrev ruleTyQ : VExpr := .forallE mprTyJ iotaTypeJ
abbrev ruleTyP : VExpr := .forallE mpTyJ ruleTyQ
abbrev ruleTyN : VExpr := .forallE minTyI ruleTyP
abbrev ruleTyM (u : VLevel) : VExpr := .forallE (motTyI u) ruleTyN
abbrev ruleTyB (u : VLevel) : VExpr := .forallE (.sort .zero) (ruleTyM u)
abbrev ruleTyJ (u : VLevel) : VExpr := .forallE (.sort .zero) (ruleTyB u)

abbrev jSortQ (u : VLevel) : VLevel := .imax mpSortI u
abbrev jSortN (u : VLevel) : VLevel := .imax (minSortI u) (minSortI u)
abbrev jSortM (u : VLevel) : VLevel := .imax (motSortI u) (jSortN u)
abbrev jSortB (u : VLevel) : VLevel := .imax (.succ .zero) (jSortM u)
/-- **The ι-rule's sort.**  Six `imax`es; two of them (`b`, `a`) have `Prop`-typed domains. -/
abbrev iffRuleSort (u : VLevel) : VLevel := .imax (.succ .zero) (jSortB u)

/-- **The rule's type, measured.** -/
theorem ruleTyJ_eq : (iffIndDecl.iotaRule 0 0 iffCtor).type.instL [u] = ruleTyJ u := rfl

/-! ### The level branch, six `imax`es deep -/

section Levels
variable {ls : List ℕ}

theorem jSortQ_eval_eq_zero_iff : (jSortQ u).eval ls = 0 ↔ u.eval ls = 0 := imax_eq_zero_iff

theorem minSortI_eval_eq_zero_iff : (minSortI u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans imax_eq_zero_iff

theorem jSortN_eval_eq_zero_iff : (jSortN u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans minSortI_eval_eq_zero_iff

theorem jSortM_eval_eq_zero_iff : (jSortM u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans jSortN_eval_eq_zero_iff

theorem jSortB_eval_eq_zero_iff : (jSortB u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans jSortM_eval_eq_zero_iff

/-- **The ι-rule's level branch**, the same one the recursor cell splits on. -/
theorem iffRuleSort_eval_eq_zero_iff : (iffRuleSort u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans jSortB_eval_eq_zero_iff

end Levels

include hu in
theorem minSortI_wf : (minSortI u).WF nv := ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hu⟩
include hu in
theorem jSortQ_wf : (jSortQ u).WF nv := ⟨⟨trivial, trivial⟩, hu⟩
include hu in
theorem jSortN_wf : (jSortN u).WF nv := ⟨minSortI_wf hu, minSortI_wf hu⟩
include hu in
theorem jSortM_wf : (jSortM u).WF nv := ⟨⟨trivial, hu⟩, jSortN_wf hu⟩
include hu in
theorem jSortB_wf : (jSortB u).WF nv := ⟨trivial, jSortM_wf hu⟩
include hu in
theorem iffRuleSort_wf : (iffRuleSort u).WF nv := ⟨trivial, jSortB_wf hu⟩

/-! ### The six layers, typed -/

theorem hasType_ruleTyQ :
    iffEnv.HasType nv (jctxP Γ u) ruleTyQ (.sort (jSortQ u)) :=
  .forallEDF (hasType_mprTyJ Γ) (hasType_iotaTypeJ Γ)

/-- The inner two layers **are** `minTyI` lifted, so this is `IffAudit.hasType_minTyI` weakened --
the one place in this file where a recursor-context lemma transfers unchanged. -/
theorem hasType_ruleTyP :
    iffEnv.HasType nv (ictxN Γ u) ruleTyP (.sort (minSortI u)) :=
  (hasType_minTyI Γ).weak iffEnv_ordered

theorem hasType_ruleTyN :
    iffEnv.HasType nv (ictxM Γ u) ruleTyN (.sort (jSortN u)) :=
  .forallEDF (hasType_minTyI Γ) (hasType_ruleTyP Γ)

include hu in
theorem hasType_ruleTyM :
    iffEnv.HasType nv (ictxB Γ) (ruleTyM u) (.sort (jSortM u)) :=
  .forallEDF (hasType_motTyI hu Γ) (hasType_ruleTyN Γ)

include hu in
theorem hasType_ruleTyB :
    iffEnv.HasType nv (ictxA Γ) (ruleTyB u) (.sort (jSortB u)) :=
  .forallEDF (.sortDF trivial trivial rfl) (hasType_ruleTyM hu Γ)

include hu in
/-- **The ι-rule's type, typed, with its sort.** -/
theorem hasType_ruleTyJ :
    iffEnv.HasType nv Γ (ruleTyJ u) (.sort (iffRuleSort u)) :=
  .forallEDF (.sortDF trivial trivial rfl) (hasType_ruleTyB hu Γ)

end RuleType

/-! ## 5. The ι-computation proper: `iffRecFn` at a `Iff.intro` major premise

Five `mkLam_value` steps down `iffRecFn`'s nest.  The last layer's domain is `⟦Iff a b⟧`, which
`iffFn_value` collapses to `{•}` once `a = b`, and its body is `((ρ ‘ 3) ‘ •) ‘ •` -- the minor
premise applied to **two** `•`s.  **This is the whole set-theoretic content of the ι-rule**, and it
is the shape `Eq` did not have: `eqRecFn`'s innermost body reads the minor premise, `iffRecFn`'s
*applies* it, once per constructor field. -/

section Compute

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`iffRecFn ‘ a ‘ b ‘ f ‘ m ‘ • = (m ‘ •) ‘ •`.** -/
theorem iffRecFn_app_intro (κ : ℕ → V) (nu : ℕ) {a b f m : V}
    (ha : a ∈ (UProp : V)) (hb : b ∈ (UProp : V)) (hab : a = b)
    (hf : f ∈ motSetI κ nu (snoc (snoc (∅ : V) a) b))
    (hm : m ∈ minSet (snoc (snoc (snoc (∅ : V) a) b) f)) :
    (((((iffRecFn κ nu) ‘ a) ‘ b) ‘ f) ‘ m) ‘ (pt : V) = ((m ‘ (pt : V)) ‘ (pt : V)) := by
  have haU : a ∈ U κ 0 := by rw [U_zero]; exact ha
  have hbU : b ∈ U κ 0 := by rw [U_zero]; exact hb
  have v1 : (iffRecFn κ nu) ‘ a = lamBI κ nu (snoc (∅ : V) a) := by
    unfold iffRecFn; exact mkLam_value haU
  have v2 : (lamBI κ nu (snoc (∅ : V) a)) ‘ b = lamFI κ nu (snoc (snoc (∅ : V) a) b) := by
    unfold lamBI; exact mkLam_value hbU
  have v3 : (lamFI κ nu (snoc (snoc (∅ : V) a) b)) ‘ f
      = lamNI (snoc (snoc (snoc (∅ : V) a) b) f) := by
    unfold lamFI; exact mkLam_value hf
  have v4 : (lamNI (snoc (snoc (snoc (∅ : V) a) b) f)) ‘ m
      = lamHI (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) := by
    unfold lamNI; exact mkLam_value hm
  have v5 : (lamHI (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m)) ‘ (pt : V)
      = ((m ‘ (pt : V)) ‘ (pt : V)) := by
    unfold lamHI
    rw [mkLam_value (ρ := snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) (v := (pt : V))
      (by rw [EqZeroAudit.r4_0, EqZeroAudit.r4_1, iffFn_value ha hb, if_pos hab]
          exact mem_singleton_iff.2 rfl)]
    rw [EqLargeAudit.r4_3]
  rw [v1, v2, v3, v4, v5]

end Compute

/-! ## 6. The left-hand body, applied out

`interp`'s `app` clause consults `L.IsProof` at each of the spine's five prefixes, so each is typed
here and each type's sort exhibited.  The constructor application `Iff.intro a b mp mpr` is the one
node where the *positive* branch is taken: its head `Iff.intro a b mp` is a proof
(`isProof_introC3J`), so `interp` discards `mpr` and the whole node is `•`. -/

section Body

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hle in
/-- **`Iff.intro a b mp` IS a proof at the ι-context** -- `IffLargeAudit.isProof_introC3` one binder
lower.  Unconditional in the level: its type's sort is `imax (imax 0 0) 0 = 0`. -/
theorem isProof_introC3J (hΓ : OnCtx (jctxQ ([] : List VExpr) u) (iffEnv.IsType nv)) :
    L.IsProof M (jctxQ ([] : List VExpr) u)
      (.app (.app (.app (.const ``Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1)) :=
  (isProof_iff hle hΓ (hasType_introC3J _) (hasType_introC3JTy _)
    ⟨⟨trivial, trivial⟩, trivial⟩).2 (imax_eq_zero_iff.2 rfl)

include hu hle in
/-- **The spine, applied out.**  Five `interp_app_type` steps, one `interp_app_proof`, four
`snoc` reads. -/
theorem interp_iotaLhsBody_app (hn : u.eval M.ls ≠ 0) {a b f m mp mpr : V} :
    (interp M L (jctxQ ([] : List VExpr) u) (iotaLhsBodyJ u)).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr)
      = ((((((M.cnst ``Iff.rec [u]) ‘ a) ‘ b) ‘ f) ‘ m) ‘ (pt : V)) := by
  have hON : OnCtx (jctxQ ([] : List VExpr) u) (iffEnv.IsType nv) :=
    onCtxJ_Q hu ([] : List VExpr) trivial
  -- the five prefixes, typed
  have h1 := hasType_IffRecC hu (jctxQ ([] : List VExpr) u)
  have h2 := EqAudit.hasType_app' h1 (hasType_a_jctxQ ([] : List VExpr)) rfl
  have h3 := EqAudit.hasType_app' h2 (hasType_b_jctxQ ([] : List VExpr)) rfl
  have h4 := EqAudit.hasType_app' h3 (hasType_mot_jctxQ ([] : List VExpr)) rfl
  have h5 := EqAudit.hasType_app' h4 (hasType_min_jctxQ ([] : List VExpr)) rfl
  -- their types' sorts
  have hA1 : iffEnv.HasType nv (jctxQ ([] : List VExpr) u)
      (.forallE (.sort .zero) (recBB u)) (.sort (iffRecSort u)) :=
    .forallEDF (.sortDF trivial trivial rfl) (hasType_recBB hu _)
  have hA2 := (hasType_recBB hu (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered .zero (hasType_a_jctxQ _)
  have hA3 := ((hasType_recBM hu (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ .zero) (hasType_a_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_b_jctxQ _)
  have hA4 := (((hasType_recBN (nv := nv) (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ (.succ .zero)) (hasType_a_jctxQ _)).instN
    iffEnv_ordered (.succ .zero) (hasType_b_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_mot_jctxQ _)
  have hA5 := ((((hasType_recBH (nv := nv) (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ (.succ (.succ .zero))) (hasType_a_jctxQ _)).instN
    iffEnv_ordered (.succ (.succ .zero)) (hasType_b_jctxQ _)).instN
    iffEnv_ordered (.succ .zero) (hasType_mot_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_min_jctxQ _)
  -- the five `¬IsProof`s
  have hnp1 := fun hp ↦ hn (iffRecSort_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h1 hA1 (iffRecSort_wf hu)).1 hp))
  have hnp2 := fun hp ↦ hn (sortB_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h2 hA2 (sortB_wf hu)).1 hp))
  have hnp3 := fun hp ↦ hn (sortM_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h3 hA3 (sortM_wf hu)).1 hp))
  have hnp4 := fun hp ↦ hn (sortN_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h4 hA4 (sortN_wf hu)).1 hp))
  have hnp5 := fun hp ↦ hn (sortH_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON h5 hA5 (sortH_wf hu)).1 hp))
  rw [interp_app_type M L hnp5, interp_app_type M L hnp4, interp_app_type M L hnp3,
    interp_app_type M L hnp2, interp_app_type M L hnp1,
    interp_app_proof M L (isProof_introC3J hle hON), interp_const,
    interp_bvar, interp_bvar, interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (6 - 1 - 5 : ℕ) = 0 from rfl, show (6 - 1 - 4 : ℕ) = 1 from rfl,
    show (6 - 1 - 3 : ℕ) = 2 from rfl, show (6 - 1 - 2 : ℕ) = 3 from rfl,
    EqZeroAudit.r6_0, EqZeroAudit.r6_1, EqZeroAudit.r6_2, EqLargeAudit.r6_3]

end Body

/-! ## 7. The right-hand side's body

`iotaRule`'s `rhs` is deliberately the η-expansion `λ Γ'. (iotaLam) Γ'`
(`Theory/Inductive/Decl.lean`: "do not simplify `rhs` to `iotaLam`'s body"), so the body carries a
**six**-fold β-redex over the *closed* nest `λ a b motive minor mp mpr, minor mp mpr`.  `interp` does
not reduce β, so the redex has to be computed: six `interp_app_type` steps, then `interp_closed_ctx`
to read the closed nest at the empty context, then six `mkLam_value` steps.

**`interp_closed_ctx` costs `L.Stable`**, exactly as at `eqIndDecl` (§23.3 item 3 of the handoff).
The alternative -- restating every `Γ = []` domain lemma at the ι-context -- is *more* expensive here
than there (six layers, two of them the constructor's own field spaces), and it would not remove the
hypothesis from the prelude's residual anyway, because `EqIotaAudit.inductOracleOK_Eq` already
depends on it. -/

section Rhs

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

/-- `minor mp mpr`, at the ι-context. -/
abbrev lamBodyJ : VExpr := .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)
abbrev lamQJ : VExpr := .lam mprTyJ lamBodyJ
abbrev lamPJ : VExpr := .lam mpTyJ lamQJ
abbrev lamNJ : VExpr := .lam minTyI lamPJ
abbrev lamMJ (u : VLevel) : VExpr := .lam (motTyI u) lamNJ
abbrev lamBJ (u : VLevel) : VExpr := .lam (.sort .zero) (lamMJ u)
/-- **`iffIndDecl.iotaLam 0 iffCtor`, instantiated**: `λ a b motive minor mp mpr, minor mp mpr`. -/
abbrev iotaLamJ (u : VLevel) : VExpr := .lam (.sort .zero) (lamBJ u)

/-- The ι-rule's right-hand body: the six-fold β-redex. -/
abbrev iotaRhsBodyJ (u : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.app (iotaLamJ u) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2))
    (.bvar 1)) (.bvar 0)

section Typing
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv))

omit hΓ in
/-- **`minor mp mpr` has the ι-rule's own common type.**  Two `hasType_app'` steps against the
minor premise's *thrice-lifted* type; both `.inst` equations `rfl`. -/
theorem hasType_lamBodyJ (Γ : List VExpr) : iffEnv.HasType nv (jctxQ Γ u) lamBodyJ iotaTypeJ :=
  EqAudit.hasType_app' (EqAudit.hasType_app' (hasType_min_jctxQ Γ)
    (.bvar (.succ .zero)) rfl) (.bvar .zero) rfl

include hu hΓ in
theorem hasType_iotaLamJ : iffEnv.HasType nv Γ (iotaLamJ u) (ruleTyJ u) :=
  VEnv.HasType.mkLams (As := [.sort .zero, .sort .zero, motTyI u, minTyI, mpTyJ, mprTyJ])
    (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

include hu hΓ in
theorem hasType_lamBJ : iffEnv.HasType nv (ictxA Γ) (lamBJ u) (ruleTyB u) :=
  VEnv.HasType.mkLams (As := [.sort .zero, motTyI u, minTyI, mpTyJ, mprTyJ])
    (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

include hu hΓ in
theorem hasType_lamMJ : iffEnv.HasType nv (ictxB Γ) (lamMJ u) (ruleTyM u) :=
  VEnv.HasType.mkLams (As := [motTyI u, minTyI, mpTyJ, mprTyJ])
    (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

include hu hΓ in
theorem hasType_lamNJ : iffEnv.HasType nv (ictxM Γ u) lamNJ ruleTyN :=
  VEnv.HasType.mkLams (As := [minTyI, mpTyJ, mprTyJ])
    (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

include hu hΓ in
theorem hasType_lamPJ : iffEnv.HasType nv (ictxN Γ u) lamPJ ruleTyP :=
  VEnv.HasType.mkLams (As := [mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

include hu hΓ in
theorem hasType_lamQJ : iffEnv.HasType nv (jctxP Γ u) lamQJ ruleTyQ :=
  VEnv.HasType.mkLams (As := [mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_lamBodyJ Γ)

end Typing

include hu in
theorem iotaLamJ_closed : (iotaLamJ u).ClosedN 0 :=
  (hasType_iotaLamJ (Γ := ([] : List VExpr)) hu trivial).closedN iffEnv_ordered trivial

/-! ### The minor premise's two partial applications, typed

`minor` and `minor mp` are the two nodes `interp`'s `app` clause tests inside the *body* of the
closed nest -- `eqIndDecl`'s body was a bare `.bvar 0`, so it had none.  Both types are the ι-rule's
own type layers **weakened**, which is what keeps this cheap: `minor : ruleTyP.lift.lift` and
`minor mp : ruleTyQ.lift`. -/

section MinorApp
variable (Γ : List VExpr)

theorem hasType_minTyJ3 :
    iffEnv.HasType nv (jctxQ Γ u) (minTyI.lift.lift.lift) (.sort (minSortI u)) :=
  ((hasType_ruleTyP Γ).weak iffEnv_ordered).weak iffEnv_ordered

theorem hasType_minAp1 :
    iffEnv.HasType nv (jctxQ Γ u) (.app (.bvar 2) (.bvar 1)) (ruleTyQ.lift) :=
  EqAudit.hasType_app' (hasType_min_jctxQ Γ) (.bvar (.succ .zero)) rfl

theorem hasType_minAp1Ty :
    iffEnv.HasType nv (jctxQ Γ u) (ruleTyQ.lift) (.sort (jSortQ u)) :=
  (hasType_ruleTyQ Γ).weak iffEnv_ordered

end MinorApp

/-! ### The six `¬IsProof`s of the closed nest, the two of its body, and the nest's value -/

section Values

variable (hn : u.eval M.ls ≠ 0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_min_jctxQ : ¬ L.IsProof M (jctxQ ([] : List VExpr) u) (.bvar 2) := fun hp ↦
  hn (minSortI_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxJ_Q hu ([] : List VExpr) trivial) (hasType_min_jctxQ _) (hasType_minTyJ3 _)
    (minSortI_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_minAp1 :
    ¬ L.IsProof M (jctxQ ([] : List VExpr) u) (.app (.bvar 2) (.bvar 1)) := fun hp ↦
  hn (jSortQ_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxJ_Q hu ([] : List VExpr) trivial) (hasType_minAp1 _) (hasType_minAp1Ty _)
    (jSortQ_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamBodyJ :
    ¬ L.IsProof M (jctxQ ([] : List VExpr) u) lamBodyJ := fun hp ↦
  hn ((isProof_iff (L := L) (M := M) hle (onCtxJ_Q hu ([] : List VExpr) trivial)
    (hasType_lamBodyJ _) (hasType_iotaTypeJ _) hu).1 hp)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamQJ : ¬ L.IsProof M (jctxP ([] : List VExpr) u) lamQJ := fun hp ↦
  hn (jSortQ_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxJ_P hu ([] : List VExpr) trivial) (hasType_lamQJ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyQ _)
    (jSortQ_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamPJ : ¬ L.IsProof M (ictxN ([] : List VExpr) u) lamPJ := fun hp ↦
  hn (minSortI_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_N (Γ := ([] : List VExpr)) hu trivial) (hasType_lamPJ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyP _)
    (minSortI_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamNJ : ¬ L.IsProof M (ictxM ([] : List VExpr) u) lamNJ := fun hp ↦
  hn (jSortN_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_M (Γ := ([] : List VExpr)) hu trivial) (hasType_lamNJ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyN _)
    (jSortN_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamMJ : ¬ L.IsProof M (ictxB ([] : List VExpr)) (lamMJ u) := fun hp ↦
  hn (jSortM_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_B (Γ := ([] : List VExpr)) trivial) (hasType_lamMJ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyM hu _)
    (jSortM_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lamBJ : ¬ L.IsProof M (ictxA ([] : List VExpr)) (lamBJ u) := fun hp ↦
  hn (jSortB_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_A (Γ := ([] : List VExpr)) trivial) (hasType_lamBJ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyB hu _)
    (jSortB_wf hu)).1 hp))

end Values

include hu hle in
/-- **The closed nest, applied to its six arguments**: `⟦λ a b motive minor mp mpr, minor mp mpr⟧`
applied out is `(m ‘ mp) ‘ mpr`.  Six `interp_lam_type`/`mkLam_value` peels, then the body's two
`interp_app_type` steps and three `snoc` reads. -/
theorem interp_iotaLamJ_app (hn : u.eval M.ls ≠ 0) {a b f m mp mpr : V}
    (ha : a ∈ U M.κ 0) (hb : b ∈ U M.κ 0)
    (hf : f ∈ (interp M L (ictxB ([] : List VExpr)) (motTyI u)).toFun (snoc (snoc (∅ : V) a) b))
    (hm : m ∈ (interp M L (ictxM ([] : List VExpr) u) minTyI).toFun
      (snoc (snoc (snoc (∅ : V) a) b) f))
    (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
      (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m))
    (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
      (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) :
    (((((((interp M L ([] : List VExpr) (iotaLamJ u)).toFun ∅) ‘ a) ‘ b) ‘ f) ‘ m) ‘ mp) ‘ mpr
      = ((m ‘ mp) ‘ mpr) := by
  have e1 : ((interp M L ([] : List VExpr) (iotaLamJ u)).toFun ∅) ‘ a
      = (interp M L (ictxA ([] : List VExpr)) (lamBJ u)).toFun (snoc (∅ : V) a) := by
    rw [interp_lam_type M L (not_isProof_lamBJ hu hle hn)]
    exact mkLam_value (by rw [interp_sort]; exact ha)
  have e2 : ((interp M L (ictxA ([] : List VExpr)) (lamBJ u)).toFun (snoc (∅ : V) a)) ‘ b
      = (interp M L (ictxB ([] : List VExpr)) (lamMJ u)).toFun (snoc (snoc (∅ : V) a) b) := by
    rw [interp_lam_type M L (not_isProof_lamMJ hu hle hn)]
    exact mkLam_value (by rw [interp_sort]; exact hb)
  have e3 : ((interp M L (ictxB ([] : List VExpr)) (lamMJ u)).toFun (snoc (snoc (∅ : V) a) b)) ‘ f
      = (interp M L (ictxM ([] : List VExpr) u) lamNJ).toFun
        (snoc (snoc (snoc (∅ : V) a) b) f) := by
    rw [interp_lam_type M L (not_isProof_lamNJ hu hle hn)]; exact mkLam_value hf
  have e4 : ((interp M L (ictxM ([] : List VExpr) u) lamNJ).toFun
        (snoc (snoc (snoc (∅ : V) a) b) f)) ‘ m
      = (interp M L (ictxN ([] : List VExpr) u) lamPJ).toFun
        (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) := by
    rw [interp_lam_type M L (not_isProof_lamPJ hu hle hn)]; exact mkLam_value hm
  have e5 : ((interp M L (ictxN ([] : List VExpr) u) lamPJ).toFun
        (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m)) ‘ mp
      = (interp M L (jctxP ([] : List VExpr) u) lamQJ).toFun
        (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) := by
    rw [interp_lam_type M L (not_isProof_lamQJ hu hle hn)]; exact mkLam_value hmp
  have e6 : ((interp M L (jctxP ([] : List VExpr) u) lamQJ).toFun
        (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) ‘ mpr
      = (interp M L (jctxQ ([] : List VExpr) u) lamBodyJ).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr) := by
    rw [interp_lam_type M L (not_isProof_lamBodyJ hu hle hn)]; exact mkLam_value hmpr
  rw [e1, e2, e3, e4, e5, e6,
    interp_app_type M L (not_isProof_minAp1 hu hle hn),
    interp_app_type M L (not_isProof_min_jctxQ hu hle hn),
    interp_bvar, interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (6 - 1 - 2 : ℕ) = 3 from rfl, show (6 - 1 - 1 : ℕ) = 4 from rfl,
    show (6 - 1 - 0 : ℕ) = 5 from rfl,
    EqLargeAudit.r6_3, EqZeroAudit.r6_4, EqZeroAudit.r6_5]

end Rhs

/-! ## 8. The two bodies' values, at the ι-context -/

section Bodies

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

theorem hasType_mp_jctxQ (Γ : List VExpr) :
    iffEnv.HasType nv (jctxQ Γ u) (.bvar 1) (mpTyJ.lift.lift) := .bvar (.succ .zero)

include hu hle in
/-- **`⟦(iotaLam) a b motive minor mp mpr⟧ = (m ‘ mp) ‘ mpr`.**  The six-fold β-redex, computed.
`interp_closed_ctx` is what lets the closed nest be read at the *empty* context, against the
existing `Γ = []` domain lemmas, instead of restating all six at the ι-context; it costs
`L.Stable`. -/
theorem interp_iotaRhsBody_val (hS : L.StableLift) (hn : u.eval M.ls ≠ 0) {a b f m mp mpr : V}
    (ha : a ∈ U M.κ 0) (hb : b ∈ U M.κ 0)
    (hf : f ∈ (interp M L (ictxB ([] : List VExpr)) (motTyI u)).toFun (snoc (snoc (∅ : V) a) b))
    (hm : m ∈ (interp M L (ictxM ([] : List VExpr) u) minTyI).toFun
      (snoc (snoc (snoc (∅ : V) a) b) f))
    (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
      (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m))
    (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
      (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) :
    (interp M L (jctxQ ([] : List VExpr) u) (iotaRhsBodyJ u)).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr)
      = ((m ‘ mp) ‘ mpr) := by
  have hON : OnCtx (jctxQ ([] : List VExpr) u) (iffEnv.IsType nv) :=
    onCtxJ_Q hu ([] : List VExpr) trivial
  have q1 := hasType_iotaLamJ (Γ := jctxQ ([] : List VExpr) u) hu hON
  have q2 := EqAudit.hasType_app' q1 (hasType_a_jctxQ ([] : List VExpr)) rfl
  have q3 := EqAudit.hasType_app' q2 (hasType_b_jctxQ ([] : List VExpr)) rfl
  have q4 := EqAudit.hasType_app' q3 (hasType_mot_jctxQ ([] : List VExpr)) rfl
  have q5 := EqAudit.hasType_app' q4 (hasType_min_jctxQ ([] : List VExpr)) rfl
  have q6 := EqAudit.hasType_app' q5 (hasType_mp_jctxQ ([] : List VExpr)) rfl
  have hB1 := hasType_ruleTyJ hu (jctxQ ([] : List VExpr) u)
  have hB2 := (hasType_ruleTyB hu (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered .zero (hasType_a_jctxQ _)
  have hB3 := ((hasType_ruleTyM hu (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ .zero) (hasType_a_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_b_jctxQ _)
  have hB4 := (((hasType_ruleTyN (nv := nv) (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ (.succ .zero)) (hasType_a_jctxQ _)).instN
    iffEnv_ordered (.succ .zero) (hasType_b_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_mot_jctxQ _)
  have hB5 := ((((hasType_ruleTyP (nv := nv) (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ (.succ (.succ .zero))) (hasType_a_jctxQ _)).instN
    iffEnv_ordered (.succ (.succ .zero)) (hasType_b_jctxQ _)).instN
    iffEnv_ordered (.succ .zero) (hasType_mot_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_min_jctxQ _)
  have hB6 := (((((hasType_ruleTyQ (nv := nv) (jctxQ ([] : List VExpr) u)).instN
    iffEnv_ordered (.succ (.succ (.succ (.succ .zero)))) (hasType_a_jctxQ _)).instN
    iffEnv_ordered (.succ (.succ (.succ .zero))) (hasType_b_jctxQ _)).instN
    iffEnv_ordered (.succ (.succ .zero)) (hasType_mot_jctxQ _)).instN
    iffEnv_ordered (.succ .zero) (hasType_min_jctxQ _)).instN
    iffEnv_ordered .zero (hasType_mp_jctxQ _)
  have hq1 := fun hp ↦ hn (iffRuleSort_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q1 hB1 (iffRuleSort_wf hu)).1 hp))
  have hq2 := fun hp ↦ hn (jSortB_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q2 hB2 (jSortB_wf hu)).1 hp))
  have hq3 := fun hp ↦ hn (jSortM_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q3 hB3 (jSortM_wf hu)).1 hp))
  have hq4 := fun hp ↦ hn (jSortN_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q4 hB4 (jSortN_wf hu)).1 hp))
  have hq5 := fun hp ↦ hn (minSortI_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q5 hB5 (minSortI_wf hu)).1 hp))
  have hq6 := fun hp ↦ hn (jSortQ_eval_eq_zero_iff.1
    ((isProof_iff (L := L) (M := M) hle hON q6 hB6 (jSortQ_wf hu)).1 hp))
  -- the ι-context's valuation really is a valuation
  have hc0 : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have hc1 : (snoc (∅ : V) a) ∈ interpCtx M L (ictxA ([] : List VExpr)) :=
    (mem_interpCtx_cons M L).2 ⟨∅, hc0, a, by rw [interp_sort]; exact ha, rfl⟩
  have hc2 : (snoc (snoc (∅ : V) a) b) ∈ interpCtx M L (ictxB ([] : List VExpr)) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc1, b, by rw [interp_sort]; exact hb, rfl⟩
  have hc3 : (snoc (snoc (snoc (∅ : V) a) b) f) ∈ interpCtx M L (ictxM ([] : List VExpr) u) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc2, f, hf, rfl⟩
  have hc4 : (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m)
      ∈ interpCtx M L (ictxN ([] : List VExpr) u) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc3, m, hm, rfl⟩
  have hc5 : (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)
      ∈ interpCtx M L (jctxP ([] : List VExpr) u) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc4, mp, hmp, rfl⟩
  have hc6 : (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr)
      ∈ interpCtx M L (jctxQ ([] : List VExpr) u) :=
    (mem_interpCtx_cons M L).2 ⟨_, hc5, mpr, hmpr, rfl⟩
  rw [interp_app_type M L hq6, interp_app_type M L hq5, interp_app_type M L hq4,
    interp_app_type M L hq3, interp_app_type M L hq2, interp_app_type M L hq1,
    interp_bvar, interp_bvar, interp_bvar, interp_bvar, interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (6 - 1 - 5 : ℕ) = 0 from rfl, show (6 - 1 - 4 : ℕ) = 1 from rfl,
    show (6 - 1 - 3 : ℕ) = 2 from rfl, show (6 - 1 - 2 : ℕ) = 3 from rfl,
    show (6 - 1 - 1 : ℕ) = 4 from rfl, show (6 - 1 - 0 : ℕ) = 5 from rfl,
    EqZeroAudit.r6_0, EqZeroAudit.r6_1, EqZeroAudit.r6_2, EqLargeAudit.r6_3,
    EqZeroAudit.r6_4, EqZeroAudit.r6_5,
    interp_closed_ctx_lift M L hS (iotaLamJ_closed hu) hc6]
  exact interp_iotaLamJ_app hu hle hn ha hb hf hm hmp hmpr

end Bodies

/-! ## 9. The two nests, named, typed, and split

`iffRule_lhs_instL` / `_rhs_instL` (§1) say these abbreviations *are* the ι-rule's two sides at the
instantiation `[u]`; `lhsA_eq` / `rhsA_eq` re-check that by `rfl`. -/

section Nests

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

abbrev lhsQ (u : VLevel) : VExpr := .lam mprTyJ (iotaLhsBodyJ u)
abbrev lhsP (u : VLevel) : VExpr := .lam mpTyJ (lhsQ u)
abbrev lhsN (u : VLevel) : VExpr := .lam minTyI (lhsP u)
abbrev lhsM (u : VLevel) : VExpr := .lam (motTyI u) (lhsN u)
abbrev lhsB (u : VLevel) : VExpr := .lam (.sort .zero) (lhsM u)
abbrev lhsA (u : VLevel) : VExpr := .lam (.sort .zero) (lhsB u)

abbrev rhsQ (u : VLevel) : VExpr := .lam mprTyJ (iotaRhsBodyJ u)
abbrev rhsP (u : VLevel) : VExpr := .lam mpTyJ (rhsQ u)
abbrev rhsN (u : VLevel) : VExpr := .lam minTyI (rhsP u)
abbrev rhsM (u : VLevel) : VExpr := .lam (motTyI u) (rhsN u)
abbrev rhsB (u : VLevel) : VExpr := .lam (.sort .zero) (rhsM u)
abbrev rhsA (u : VLevel) : VExpr := .lam (.sort .zero) (rhsB u)

theorem lhsA_eq : (iffIndDecl.iotaRule 0 0 iffCtor).lhs.instL [u] = lhsA u := rfl
theorem rhsA_eq : (iffIndDecl.iotaRule 0 0 iffCtor).rhs.instL [u] = rhsA u := rfl
theorem ruleTyA_eq : (iffIndDecl.iotaRule 0 0 iffCtor).type.instL [u] = ruleTyJ u := rfl

section Typing
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv))

include hu hΓ in
theorem hasType_lhsQ : iffEnv.HasType nv (jctxP Γ u) (lhsQ u) ruleTyQ :=
  VEnv.HasType.mkLams (As := [mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_iotaLhsBodyJ hu Γ)

include hu hΓ in
theorem hasType_lhsP : iffEnv.HasType nv (ictxN Γ u) (lhsP u) ruleTyP :=
  VEnv.HasType.mkLams (As := [mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_iotaLhsBodyJ hu Γ)

include hu hΓ in
theorem hasType_lhsN : iffEnv.HasType nv (ictxM Γ u) (lhsN u) ruleTyN :=
  VEnv.HasType.mkLams (As := [minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaLhsBodyJ hu Γ)

include hu hΓ in
theorem hasType_lhsM : iffEnv.HasType nv (ictxB Γ) (lhsM u) (ruleTyM u) :=
  VEnv.HasType.mkLams (As := [motTyI u, minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaLhsBodyJ hu Γ)

include hu hΓ in
theorem hasType_lhsB : iffEnv.HasType nv (ictxA Γ) (lhsB u) (ruleTyB u) :=
  VEnv.HasType.mkLams (As := [.sort .zero, motTyI u, minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaLhsBodyJ hu Γ)

include hu hΓ in
theorem hasType_iotaRhsBodyJ : iffEnv.HasType nv (jctxQ Γ u) (iotaRhsBodyJ u) iotaTypeJ :=
  EqAudit.hasType_app' (EqAudit.hasType_app' (EqAudit.hasType_app' (EqAudit.hasType_app'
    (EqAudit.hasType_app' (EqAudit.hasType_app'
      (hasType_iotaLamJ (Γ := jctxQ Γ u) hu (onCtxJ_Q hu Γ hΓ)) (hasType_a_jctxQ Γ) rfl)
      (hasType_b_jctxQ Γ) rfl) (hasType_mot_jctxQ Γ) rfl) (hasType_min_jctxQ Γ) rfl)
    (hasType_mp_jctxQ Γ) rfl) (.bvar .zero) rfl

include hu hΓ in
theorem hasType_rhsQ : iffEnv.HasType nv (jctxP Γ u) (rhsQ u) ruleTyQ :=
  VEnv.HasType.mkLams (As := [mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_iotaRhsBodyJ hu hΓ)

include hu hΓ in
theorem hasType_rhsP : iffEnv.HasType nv (ictxN Γ u) (rhsP u) ruleTyP :=
  VEnv.HasType.mkLams (As := [mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ) (hasType_iotaRhsBodyJ hu hΓ)

include hu hΓ in
theorem hasType_rhsN : iffEnv.HasType nv (ictxM Γ u) (rhsN u) ruleTyN :=
  VEnv.HasType.mkLams (As := [minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaRhsBodyJ hu hΓ)

include hu hΓ in
theorem hasType_rhsM : iffEnv.HasType nv (ictxB Γ) (rhsM u) (ruleTyM u) :=
  VEnv.HasType.mkLams (As := [motTyI u, minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaRhsBodyJ hu hΓ)

include hu hΓ in
theorem hasType_rhsB : iffEnv.HasType nv (ictxA Γ) (rhsB u) (ruleTyB u) :=
  VEnv.HasType.mkLams (As := [.sort .zero, motTyI u, minTyI, mpTyJ, mprTyJ]) (onCtxJ_Q hu Γ hΓ)
    (hasType_iotaRhsBodyJ hu hΓ)

end Typing

/-! ### The level branch at each of the six binders

`isProp_iff`/`isProof_iff` against the six sorts of §4; every one is `0` exactly when `u` is. -/

section Branch
variable (hn : u.eval M.ls ≠ 0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_ruleTyB : ¬ L.IsProp M (ictxA ([] : List VExpr)) (ruleTyB u) := fun hp ↦
  hn (jSortB_eval_eq_zero_iff.1 ((isProp_iff hle (onCtxI_A (Γ := ([] : List VExpr)) trivial)
    (hasType_ruleTyB hu _) (jSortB_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_ruleTyM : ¬ L.IsProp M (ictxB ([] : List VExpr)) (ruleTyM u) := fun hp ↦
  hn (jSortM_eval_eq_zero_iff.1 ((isProp_iff hle (onCtxI_B (Γ := ([] : List VExpr)) trivial)
    (hasType_ruleTyM hu _) (jSortM_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_ruleTyN : ¬ L.IsProp M (ictxM ([] : List VExpr) u) ruleTyN := fun hp ↦
  hn (jSortN_eval_eq_zero_iff.1 ((isProp_iff hle (onCtxI_M (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyN _) (jSortN_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_ruleTyP : ¬ L.IsProp M (ictxN ([] : List VExpr) u) ruleTyP := fun hp ↦
  hn (minSortI_eval_eq_zero_iff.1 ((isProp_iff hle (onCtxI_N (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyP _) (minSortI_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_ruleTyQ : ¬ L.IsProp M (jctxP ([] : List VExpr) u) ruleTyQ := fun hp ↦
  hn (jSortQ_eval_eq_zero_iff.1 ((isProp_iff hle (onCtxJ_P hu ([] : List VExpr) trivial)
    (hasType_ruleTyQ _) (jSortQ_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProp_iotaTypeJ : ¬ L.IsProp M (jctxQ ([] : List VExpr) u) iotaTypeJ := fun hp ↦
  hn ((isProp_iff hle (onCtxJ_Q hu ([] : List VExpr) trivial) (hasType_iotaTypeJ _) hu).1 hp)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lhsB : ¬ L.IsProof M (ictxA ([] : List VExpr)) (lhsB u) := fun hp ↦
  hn (jSortB_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_A (Γ := ([] : List VExpr)) trivial) (hasType_lhsB (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyB hu _) (jSortB_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lhsM : ¬ L.IsProof M (ictxB ([] : List VExpr)) (lhsM u) := fun hp ↦
  hn (jSortM_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_B (Γ := ([] : List VExpr)) trivial) (hasType_lhsM (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyM hu _) (jSortM_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lhsN : ¬ L.IsProof M (ictxM ([] : List VExpr) u) (lhsN u) := fun hp ↦
  hn (jSortN_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_M (Γ := ([] : List VExpr)) hu trivial)
    (hasType_lhsN (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyN _) (jSortN_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lhsP : ¬ L.IsProof M (ictxN ([] : List VExpr) u) (lhsP u) := fun hp ↦
  hn (minSortI_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxI_N (Γ := ([] : List VExpr)) hu trivial)
    (hasType_lhsP (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyP _) (minSortI_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_lhsQ : ¬ L.IsProof M (jctxP ([] : List VExpr) u) (lhsQ u) := fun hp ↦
  hn (jSortQ_eval_eq_zero_iff.1 ((isProof_iff (L := L) (M := M) hle
    (onCtxJ_P hu ([] : List VExpr) trivial) (hasType_lhsQ (Γ := ([] : List VExpr)) hu trivial)
    (hasType_ruleTyQ _) (jSortQ_wf hu)).1 hp))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hn in
theorem not_isProof_iotaLhsBodyJ :
    ¬ L.IsProof M (jctxQ ([] : List VExpr) u) (iotaLhsBodyJ u) := fun hp ↦
  hn ((isProof_iff (L := L) (M := M) hle (onCtxJ_Q hu ([] : List VExpr) trivial)
    (hasType_iotaLhsBodyJ hu _) (hasType_iotaTypeJ _) hu).1 hp)

end Branch

end Nests

/-! ## 10. The three facts with content

Everything above is bookkeeping; these three are where the ι-rule is *true*.

1. **Both constructor fields are `•`.**  `mp`'s and `mpr`'s types are propositions
   (`imax 0 0 = 0`), so `interp` takes the impredicative branch at them and their interpretations are
   `mkForallProp`s, all of whose members are `•`.  That is what makes the left side's
   `iffRecFn … ‘ •` -- whose innermost body applies the minor premise to **two `•`s** -- equal to the
   right side's `min ‘ mp ‘ mpr`.  `eqIndDecl` has no analogue: its constructor has no fields.
2. **`a = b`.**  Needed to collapse `⟦Iff a b⟧` to `{•}` inside `iffRecFn`'s last `mkLam`.  It comes
   from the two field spaces being *inhabited* -- the argument `IffConstsAudit.eq_of_mem_mpTy_mprTy`
   makes at `Iff.intro`'s contexts, restated here at the ι-context (indices `3/3` and `3/5` against
   that file's `1/1` and `1/3`, and a five- and six-`snoc` valuation against its two and three).
3. **`⟦motive (Iff.intro a b mp mpr)⟧ = f ‘ •`**, the ι-rule's common type at the ι-context. -/

section Content

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hu in
theorem onCtxJ_Pa {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv)) :
    OnCtx (jctxPa Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_N hu hΓ, .zero, .bvar (.succ (.succ (.succ .zero)))⟩

include hu in
theorem onCtxJ_Qb {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv)) :
    OnCtx (jctxQb Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxJ_P hu Γ hΓ, .zero, hasType_b_jctxP Γ⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle in
/-- **`mp`'s codomain `b` IS a proposition** at the ι-context. -/
theorem isProp_mpCodJ : L.IsProp M (jctxPa ([] : List VExpr) u) (.bvar 3) :=
  (isProp_iff hle (onCtxJ_Pa hu (Γ := ([] : List VExpr)) trivial)
    (hasType_b_jctxPa ([] : List VExpr)) trivial).2 rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle in
/-- **`mpr`'s codomain `a` IS a proposition** at the ι-context. -/
theorem isProp_mprCodJ : L.IsProp M (jctxQb ([] : List VExpr) u) (.bvar 5) :=
  (isProp_iff hle (onCtxJ_Qb hu (Γ := ([] : List VExpr)) trivial)
    (hasType_a_jctxQb ([] : List VExpr)) trivial).2 rfl

variable {a b f m mp mpr : V}

include hu hle in
/-- **`mp = •`.**  `⟦a → b⟧` is a `mkForallProp`, and every member of one is `•`. -/
theorem mp_eq_pt (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
    (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m)) : mp = (pt : V) :=
  ((mem_interp_forallE_prop_iff M L (isProp_mpCodJ hu hle)).1 hmp).1

include hu hle in
/-- **`mpr = •`.** -/
theorem mpr_eq_pt (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
    (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) : mpr = (pt : V) :=
  ((mem_interp_forallE_prop_iff M L (isProp_mprCodJ hu hle)).1 hmpr).1

include hu hle in
/-- **The two field binders force `a = b`, at the ι-context.**  Each field space is an implication
between two truth values; `UProp` has two elements, so both being inhabited is `a = b`. -/
theorem eq_of_mem_mpTyJ_mprTyJ (ha : a ∈ (UProp : V)) (hb : b ∈ (UProp : V))
    (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
      (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m))
    (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
      (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) : a = b := by
  obtain ⟨-, hxf⟩ := (mem_interp_forallE_prop_iff M L (isProp_mpCodJ hu hle)).1 hmp
  obtain ⟨-, hyf⟩ := (mem_interp_forallE_prop_iff M L (isProp_mprCodJ hu hle)).1 hmpr
  have hxf' : ∀ w ∈ a, mp ∈ b := by
    intro w hw
    have h1 := hxf w (by
      rw [interp_bvar]
      simp only [List.length_cons, List.length_nil]
      rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, EqZeroAudit.r4_0]
      exact hw)
    rw [interp_bvar] at h1
    simp only [List.length_cons, List.length_nil] at h1
    rwa [show (5 - 1 - 3 : ℕ) = 1 from rfl, EqZeroAudit.r5_1] at h1
  have hyf' : ∀ w ∈ b, mpr ∈ a := by
    intro w hw
    have h1 := hyf w (by
      rw [interp_bvar]
      simp only [List.length_cons, List.length_nil]
      rw [show (5 - 1 - 3 : ℕ) = 1 from rfl, EqZeroAudit.r5_1]
      exact hw)
    rw [interp_bvar] at h1
    simp only [List.length_cons, List.length_nil] at h1
    rwa [show (6 - 1 - 5 : ℕ) = 0 from rfl, EqZeroAudit.r6_0] at h1
  rcases eq_empty_or_eq_true_of_mem_UProp ha with rfl | rfl
  · rcases eq_empty_or_eq_true_of_mem_UProp hb with rfl | rfl
    · rfl
    · exact absurd (hyf' pt (mem_singleton_iff.2 rfl)) not_mem_empty
  · rcases eq_empty_or_eq_true_of_mem_UProp hb with rfl | rfl
    · exact absurd (hxf' pt (mem_singleton_iff.2 rfl)) not_mem_empty
    · rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle in
/-- The motive variable is not a proof: its type's sort is `imax 0 (u+1) = u+1`. -/
theorem not_isProof_mot_jctxQ : ¬ L.IsProof M (jctxQ ([] : List VExpr) u) (.bvar 3) := by
  rw [isProof_iff (L := L) (M := M) hle (onCtxJ_Q hu ([] : List VExpr) trivial)
    (hasType_mot_jctxQ _) (hasType_motTyJ hu _) ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

include hu hle in
/-- **`⟦motive (Iff.intro a b mp mpr)⟧ = f ‘ •`** at the ι-context. -/
theorem interp_iotaTypeJ_val :
    (interp M L (jctxQ ([] : List VExpr) u) iotaTypeJ).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr)
      = (f ‘ (pt : V)) := by
  show (interp M L (jctxQ ([] : List VExpr) u)
    (.app (.bvar 3) (.app (.app (.app (.app (.const ``Iff.intro []) (.bvar 5)) (.bvar 4))
      (.bvar 1)) (.bvar 0)))).toFun _ = _
  rw [interp_app_type M L (not_isProof_mot_jctxQ hu hle),
    interp_app_proof M L (isProof_introC3J hle (onCtxJ_Q hu ([] : List VExpr) trivial)),
    interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (6 - 1 - 3 : ℕ) = 2 from rfl, EqZeroAudit.r6_2]

end Content

/-! ## 11. The `≠ 0` slice of the ι-rule

`Cnst.interp_lam_congr_of_type` peels all six binders **uniformly** -- no case analysis at any
binder, because both sides carry the ι-rule's own type -- and the whole level split appears once, at
the bodies. -/

section SliceNe

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
variable {a b f m mp mpr : V}

include hu hle in
/-- **The ι-computation, at the ι-context.**
`⟦Iff.rec a b motive minor (Iff.intro a b mp mpr)⟧ = (m ‘ mp) ‘ mpr`. -/
theorem interp_iotaLhsBody_val (hn : u.eval M.ls ≠ 0) (hspec : IffSpec M)
    (hcnst : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls))
    (ha : a ∈ U M.κ 0) (hb : b ∈ U M.κ 0)
    (hf : f ∈ (interp M L (ictxB ([] : List VExpr)) (motTyI u)).toFun (snoc (snoc (∅ : V) a) b))
    (hm : m ∈ (interp M L (ictxM ([] : List VExpr) u) minTyI).toFun
      (snoc (snoc (snoc (∅ : V) a) b) f))
    (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
      (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m))
    (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
      (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) :
    (interp M L (jctxQ ([] : List VExpr) u) (iotaLhsBodyJ u)).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp) mpr)
      = ((m ‘ mp) ‘ mpr) := by
  have ha' : a ∈ (UProp : V) := by rwa [U_zero] at ha
  have hb' : b ∈ (UProp : V) := by rwa [U_zero] at hb
  have hab : a = b := eq_of_mem_mpTyJ_mprTyJ hu hle ha' hb' hmp hmpr
  have hf' : f ∈ motSetI M.κ (u.eval M.ls) (snoc (snoc (∅ : V) a) b) := by
    rwa [← motSetI_eq_interp_motTyI hu hle hspec ha' hb'] at hf
  have hm' : m ∈ minSet (snoc (snoc (snoc (∅ : V) a) b) f) := by
    rwa [← minSet_eq_interp_minTyI hu hle hn] at hm
  rw [interp_iotaLhsBody_app hu hle hn, hcnst,
    iffRecFn_app_intro M.κ (u.eval M.ls) ha' hb' hab hf' hm',
    mp_eq_pt hu hle hmp, mpr_eq_pt hu hle hmpr]

include hu hle in
/-- **The innermost membership**: `(m ‘ mp) ‘ mpr ∈ f ‘ •`.  Two `value_mem_of_mem_mkForallType`
steps down `minSet`, with `•` supplied at both field binders by
`IffLargeAudit.pt_mem_impSet01`/`pt_mem_impSet10`. -/
theorem minAp_mem_motAp (hn : u.eval M.ls ≠ 0)
    (ha : a ∈ U M.κ 0) (hb : b ∈ U M.κ 0)
    (hm : m ∈ (interp M L (ictxM ([] : List VExpr) u) minTyI).toFun
      (snoc (snoc (snoc (∅ : V) a) b) f))
    (hmp : mp ∈ (interp M L (ictxN ([] : List VExpr) u) mpTyJ).toFun
      (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m))
    (hmpr : mpr ∈ (interp M L (jctxP ([] : List VExpr) u) mprTyJ).toFun
      (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) mp)) :
    ((m ‘ mp) ‘ mpr) ∈ (f ‘ (pt : V)) := by
  have ha' : a ∈ (UProp : V) := by rwa [U_zero] at ha
  have hb' : b ∈ (UProp : V) := by rwa [U_zero] at hb
  have hab : a = b := eq_of_mem_mpTyJ_mprTyJ hu hle ha' hb' hmp hmpr
  have hm' : m ∈ minSet (snoc (snoc (snoc (∅ : V) a) b) f) := by
    rwa [← minSet_eq_interp_minTyI hu hle hn] at hm
  rw [mp_eq_pt hu hle hmp, mpr_eq_pt hu hle hmpr]
  unfold minSet at hm'
  have h1 := EqZeroAudit.value_mem_of_mem_mkForallType hm'
    (x := (pt : V)) (pt_mem_impSet01 ha' hab)
  have h2 := EqZeroAudit.value_mem_of_mem_mkForallType h1
    (x := (pt : V)) (pt_mem_impSet10 ha' hab)
  rwa [EqZeroAudit.r4_2] at h2

include hu hle in
/-- **`⟦lhs⟧ = ⟦rhs⟧` at every non-`Prop` instantiation of the elimination universe.** -/
theorem interp_sides_eq_of_ne (hS : L.StableLift) (hn : u.eval M.ls ≠ 0) (hspec : IffSpec M)
    (hcnst : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅
      = (interp M L ([] : List VExpr) (rhsA u)).toFun ∅ := by
  refine interp_lam_congr_of_type hle (onCtxI_A (Γ := ([] : List VExpr)) trivial)
    (hasType_lhsB (Γ := ([] : List VExpr)) hu trivial)
    (hasType_rhsB (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyB hu _)
    (jSortB_wf hu) (fun a ha ↦ ?_)
  rw [interp_sort] at ha
  refine interp_lam_congr_of_type hle (onCtxI_B (Γ := ([] : List VExpr)) trivial)
    (hasType_lhsM (Γ := ([] : List VExpr)) hu trivial)
    (hasType_rhsM (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyM hu _)
    (jSortM_wf hu) (fun b hb ↦ ?_)
  rw [interp_sort] at hb
  refine interp_lam_congr_of_type hle (onCtxI_M (Γ := ([] : List VExpr)) hu trivial)
    (hasType_lhsN (Γ := ([] : List VExpr)) hu trivial)
    (hasType_rhsN (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyN _)
    (jSortN_wf hu) (fun f hf ↦ ?_)
  refine interp_lam_congr_of_type hle (onCtxI_N (Γ := ([] : List VExpr)) hu trivial)
    (hasType_lhsP (Γ := ([] : List VExpr)) hu trivial)
    (hasType_rhsP (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyP _)
    (minSortI_wf hu) (fun m hm ↦ ?_)
  refine interp_lam_congr_of_type hle (onCtxJ_P hu ([] : List VExpr) trivial)
    (hasType_lhsQ (Γ := ([] : List VExpr)) hu trivial)
    (hasType_rhsQ (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyQ _)
    (jSortQ_wf hu) (fun mp hmp ↦ ?_)
  refine interp_lam_congr_of_type hle (onCtxJ_Q hu ([] : List VExpr) trivial)
    (hasType_iotaLhsBodyJ hu _) (hasType_iotaRhsBodyJ hu trivial)
    (hasType_iotaTypeJ _) hu (fun mpr hmpr ↦ ?_)
  rw [interp_iotaLhsBody_val hu hle hn hspec hcnst ha hb hf hm hmp hmpr,
    interp_iotaRhsBody_val hu hle hS hn ha hb hf hm hmp hmpr]

include hu hle in
/-- **`⟦lhs⟧ ∈ ⟦type⟧` at every non-`Prop` instantiation.**  Six `mkLam_mem_mkForallType` steps over
*identical* domains, and the body step is `minAp_mem_motAp`. -/
theorem interp_lhs_mem_ruleType_of_ne (hn : u.eval M.ls ≠ 0) (hspec : IffSpec M)
    (hcnst : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅
      ∈ (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ := by
  rw [interp_lam_type M L (not_isProof_lhsB hu hle hn),
    interp_forallE_type M L (not_isProp_ruleTyB hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun a ha ↦ ?_)
  rw [interp_sort] at ha
  rw [interp_lam_type M L (not_isProof_lhsM hu hle hn),
    interp_forallE_type M L (not_isProp_ruleTyM hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun b hb ↦ ?_)
  rw [interp_sort] at hb
  rw [interp_lam_type M L (not_isProof_lhsN hu hle hn),
    interp_forallE_type M L (not_isProp_ruleTyN hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun f hf ↦ ?_)
  rw [interp_lam_type M L (not_isProof_lhsP hu hle hn),
    interp_forallE_type M L (not_isProp_ruleTyP hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun m hm ↦ ?_)
  rw [interp_lam_type M L (not_isProof_lhsQ hu hle hn),
    interp_forallE_type M L (not_isProp_ruleTyQ hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun mp hmp ↦ ?_)
  rw [interp_lam_type M L (not_isProof_iotaLhsBodyJ hu hle hn),
    interp_forallE_type M L (not_isProp_iotaTypeJ hu hle hn)]
  refine UnitAudit.mkLam_mem_mkForallType_of_dom rfl (fun mpr hmpr ↦ ?_)
  rw [interp_iotaLhsBody_val hu hle hn hspec hcnst ha hb hf hm hmp hmpr,
    interp_iotaTypeJ_val hu hle]
  exact minAp_mem_motAp hu hle hn ha hb hm hmp hmpr

end SliceNe

/-! ## 12. The `= 0` slice of the ι-rule

At a `Prop` elimination universe the ι-rule's type is itself a proposition
(`iffRuleSort_eval_eq_zero_iff`), so **both sides are `•`** and the equation is two
`interp_lam_proof`s.  The membership is the expensive half, as at `eqIndDecl`: six `mkForallProp`
steps ending at `• ∈ f ‘ •`, which needs the minor premise's *own* impredicative decomposition
(`IffLargeAudit.isProp_minInner_of_zero` / `_minBody_of_zero`, both stated at the recursor's
contexts `ictxP`/`ictxQ` -- and those **do** transfer, because `minTyI`'s internal binders sit below
the ι-context's extra one).

**No `IffSpec` is needed here.**  At the recursor's `= 0` slice
(`IffLargeAudit.pt_mem_interp_iffRecType_of_zero`) `IffSpec` is spent turning the major premise's
existence into `a = b`; the ι-rule has no major premise binder, and `a = b` comes from the two
*field* binders instead (`eq_of_mem_mpTyJ_mprTyJ`).  So the ι-rule's `= 0` slice is the one
obligation at this block that is free of the block's own spec. -/

section SliceZero

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
variable (h0 : u.eval M.ls = 0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProof_lhsB : L.IsProof M (ictxA ([] : List VExpr)) (lhsB u) :=
  (isProof_iff (L := L) (M := M) hle (onCtxI_A (Γ := ([] : List VExpr)) trivial)
    (hasType_lhsB (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyB hu _)
    (jSortB_wf hu)).2 (jSortB_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProof_rhsB : L.IsProof M (ictxA ([] : List VExpr)) (rhsB u) :=
  (isProof_iff (L := L) (M := M) hle (onCtxI_A (Γ := ([] : List VExpr)) trivial)
    (hasType_rhsB (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyB hu _)
    (jSortB_wf hu)).2 (jSortB_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_ruleTyB_of_zero : L.IsProp M (ictxA ([] : List VExpr)) (ruleTyB u) :=
  (isProp_iff hle (onCtxI_A (Γ := ([] : List VExpr)) trivial) (hasType_ruleTyB hu _)
    (jSortB_wf hu)).2 (jSortB_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_ruleTyM_of_zero : L.IsProp M (ictxB ([] : List VExpr)) (ruleTyM u) :=
  (isProp_iff hle (onCtxI_B (Γ := ([] : List VExpr)) trivial) (hasType_ruleTyM hu _)
    (jSortM_wf hu)).2 (jSortM_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_ruleTyN_of_zero : L.IsProp M (ictxM ([] : List VExpr) u) ruleTyN :=
  (isProp_iff hle (onCtxI_M (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyN _)
    (jSortN_wf hu)).2 (jSortN_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_ruleTyP_of_zero : L.IsProp M (ictxN ([] : List VExpr) u) ruleTyP :=
  (isProp_iff hle (onCtxI_N (Γ := ([] : List VExpr)) hu trivial) (hasType_ruleTyP _)
    (minSortI_wf hu)).2 (minSortI_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_ruleTyQ_of_zero : L.IsProp M (jctxP ([] : List VExpr) u) ruleTyQ :=
  (isProp_iff hle (onCtxJ_P hu ([] : List VExpr) trivial) (hasType_ruleTyQ _)
    (jSortQ_wf hu)).2 (jSortQ_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle h0 in
theorem isProp_iotaTypeJ_of_zero : L.IsProp M (jctxQ ([] : List VExpr) u) iotaTypeJ :=
  (isProp_iff hle (onCtxJ_Q hu ([] : List VExpr) trivial) (hasType_iotaTypeJ _) hu).2 h0

include hu hle h0 in
/-- **Both sides are `•` at a `Prop` elimination universe.**  Two lines. -/
theorem interp_sides_eq_of_zero :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅
      = (interp M L ([] : List VExpr) (rhsA u)).toFun ∅ := by
  rw [interp_lam_proof M L (isProof_lhsB hu hle h0),
    interp_lam_proof M L (isProof_rhsB hu hle h0)]

include hu hle h0 in
/-- **`• ∈ ⟦type⟧` at a `Prop` elimination universe** -- the expensive half of this slice. -/
theorem interp_lhs_mem_ruleType_of_zero :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅
      ∈ (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ := by
  rw [interp_lam_proof M L (isProof_lhsB hu hle h0)]
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyB_of_zero hu hle h0)).2
    ⟨rfl, fun a ha ↦ ?_⟩
  rw [interp_sort] at ha
  have ha' : a ∈ (UProp : V) := ha
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyM_of_zero hu hle h0)).2
    ⟨rfl, fun b hb ↦ ?_⟩
  rw [interp_sort] at hb
  have hb' : b ∈ (UProp : V) := hb
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyN_of_zero hu hle h0)).2
    ⟨rfl, fun f _ ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyP_of_zero hu hle h0)).2
    ⟨rfl, fun m hm ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L (isProp_ruleTyQ_of_zero hu hle h0)).2
    ⟨rfl, fun mp hmp ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L (isProp_iotaTypeJ_of_zero hu hle h0)).2
    ⟨rfl, fun mpr hmpr ↦ ?_⟩
  have hab : a = b := eq_of_mem_mpTyJ_mprTyJ hu hle ha' hb' hmp hmpr
  rw [interp_iotaTypeJ_val hu hle]
  rw [show (minTyI : VExpr) = .forallE (.forallE (.bvar 2) (.bvar 2))
      (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))) from rfl] at hm
  obtain ⟨rfl, hm2⟩ := (mem_interp_forallE_prop_iff M L
    (isProp_minInner_of_zero (Γ := ([] : List VExpr)) hu hle trivial h0)).1 hm
  have h1 := hm2 (pt : V)
    (by rw [← impSet01_eq_interp_mpTy hu hle]; exact pt_mem_impSet01 ha' hab)
  obtain ⟨-, h2⟩ := (mem_interp_forallE_prop_iff M L
    (isProp_minBody_of_zero (Γ := ([] : List VExpr)) hu hle trivial h0)).1 h1
  have h3 := h2 (pt : V)
    (by rw [← impSet10_eq_interp_mprTy hu hle]; exact pt_mem_impSet10 ha' hab)
  rwa [interp_minBody_val hu hle] at h3

end SliceZero

/-! ## 13. `InductOracleOK`'s `rules` field at `iffIndDecl`

`iffIndDecl.iotaRules` is a **singleton** (`iff_iotaRules_eq`, `rfl`), so the field is exactly
`DefEqOK` at `iffIndDecl.iotaRule 0 0 iffCtor`.  `DefEqOK` quantifies over **every** `us` with
`us.length = 1`, so the hypothesis on the `Iff.rec` value is stated at every `us`, not at a chosen
one -- the mistake §23's `Eq` round records as having cost two rounds. -/

section Rules

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}

/-- **`DefEqOK` at `iffIndDecl`'s ι-rule**, both level slices, at any model meeting `IffSpec` and
assigning `Iff.rec` the value `iffRecVal`. -/
theorem defEqOK_iffRule (hS : L.StableLift) (hle : iffEnv ≤ envF) (hspec : IffSpec M)
    (hcnst : ∀ us : List VLevel, M.cnst ``Iff.rec us = iffRecVal M.κ M.ls us) :
    DefEqOK L M (iffIndDecl.iotaRule 0 0 iffCtor) := by
  intro us hw hlen
  rw [iffRule_uvars] at hlen
  obtain ⟨u, rfl⟩ := eq_single_of_length_one hlen
  have hu : u.WF nv := hw u (by simp)
  rw [lhsA_eq, rhsA_eq, ruleTyA_eq]
  by_cases h0 : u.eval M.ls = 0
  · exact ⟨Above.pure (interp_sides_eq_of_zero hu hle h0),
      Above.pure (interp_lhs_mem_ruleType_of_zero hu hle h0)⟩
  · have hc : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls) := by
      rw [hcnst, iffRecVal_single, if_neg h0]
    exact ⟨Above.pure (interp_sides_eq_of_ne hu hle hS h0 hspec hc),
      Above.pure (interp_lhs_mem_ruleType_of_ne hu hle h0 hspec hc)⟩

/-- **The `rules` field of `InductOracleOK` at `iffIndDecl`.** -/
theorem inductOracleOK_rules_Iff (hS : L.StableLift) (hle : iffEnv ≤ envF) (hspec : IffSpec M)
    (hcnst : ∀ us : List VLevel, M.cnst ``Iff.rec us = iffRecVal M.κ M.ls us) :
    ∀ df ∈ iffIndDecl.iotaRules, DefEqOK L M df := by
  intro df hdf
  rw [iff_iotaRules_eq] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  exact defEqOK_iffRule hS hle hspec hcnst

/-- **…at the shared witness `SetModel.preludeWitness`.**  No side oracle parameter, no chosen `κ`,
no chain hypothesis. -/
theorem inductOracleOK_rules_Iff_preludeWitness (hS : L.StableLift) (hle : iffEnv ≤ envF)
    (κ : ℕ → V) (ls : List ℕ) :
    ∀ df ∈ iffIndDecl.iotaRules, DefEqOK L (preludeWitness κ ls) df :=
  inductOracleOK_rules_Iff hS hle (preludeWitness_iff κ ls) (preludeWitness_cnst_iffRec κ ls)

/-! ### Anti-vacuity: the membership half is not satisfied by every set

`DefEqOK`'s second conjunct is a membership, and a membership in a `mkForallType` over an *empty*
domain is satisfied by `∅ = •`.  Here is the same statement with `•` in place of `⟦lhs⟧`,
**refuted**, at one `L`, one `M`, one level and one `interp`.  Unlike `EqIotaAudit`'s control this
one needs **no parameter-space hypothesis at all**: the ι-rule's outermost binder is a parameter over
`Prop`, and `∅ ∈ U κ 0` at every `κ`, so the domain is unconditionally non-empty -- the same
simplification `IffAudit.pt_not_mem_interp_iffRecType_of_ne` records at the recursor cell. -/

theorem pt_not_mem_ruleType_of_ne {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
    (hn : u.eval M.ls ≠ 0) :
    (pt : V) ∉ (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ := by
  rw [interp_forallE_type M L (not_isProp_ruleTyB hu hle hn)]
  refine UnitAudit.pt_not_mem_mkForallType_of_nonempty (x := (∅ : V)) ?_
  rw [interp_sort]
  show (∅ : V) ∈ U M.κ 0
  rw [U_zero]
  exact mem_UProp_iff.mpr (by simp)

/-- **The ι-rule's membership half discriminates.**  One environment, one `L`, one `M`, one level,
**one `interp`**: `⟦lhs⟧` is in the rule's type and `•` -- the value the `= 0` slice hands the same
cell -- is not.  So the `≠ 0` slice of the ι-rule is not the `= 0` slice's statement in disguise. -/
theorem iffRule_discriminates {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
    (hn : u.eval M.ls ≠ 0) (hspec : IffSpec M)
    (hcnst : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅
        ∈ (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ ∧
      (pt : V) ∉ (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ :=
  ⟨interp_lhs_mem_ruleType_of_ne hu hle hn hspec hcnst, pt_not_mem_ruleType_of_ne hu hle hn⟩

/-- …and therefore the two sides' common value is **not** `•` at a non-`Prop` elimination universe,
which `interp_sides_eq_of_zero` says it is at a `Prop` one. -/
theorem interp_lhs_ne_pt_of_ne {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
    (hn : u.eval M.ls ≠ 0) (hspec : IffSpec M)
    (hcnst : M.cnst ``Iff.rec [u] = iffRecFn M.κ (u.eval M.ls)) :
    (interp M L ([] : List VExpr) (lhsA u)).toFun ∅ ≠ (pt : V) := fun h ↦
  (pt_not_mem_ruleType_of_ne hu hle hn) (h ▸ interp_lhs_mem_ruleType_of_ne hu hle hn hspec hcnst)

/-! ### Anti-vacuity at the `= 0` slice too

`interp_lhs_mem_ruleType_of_zero` has **no `IffSpec` hypothesis**, so it is worth saying why it is
not free.  At `u.eval = 0` the rule's type is a proposition, hence its interpretation is a member of
`UProp`, hence `∅` or `{•}` -- and `∅` is a live alternative (that is exactly what
`IffAudit.eq_pt_of_mem_interp_iffRecType_of_zero` leaves open at the recursor cell before its slice
is proved).  So the `= 0` slice asserts *which* truth value, and the two lemmas together pin it. -/

theorem interp_ruleType_mem_UProp_of_zero {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
    (h0 : u.eval M.ls = 0) :
    (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ ∈ (UProp : V) :=
  interp_forallE_prop_mem_UProp M L (isProp_ruleTyB_of_zero hu hle h0) ∅

/-- **The `= 0` slice pins the truth value.**  `⟦type⟧ = {•}`, not `∅` -- the other member of
`UProp`.  So `interp_lhs_mem_ruleType_of_zero` is a statement with two possible answers and it gives
one, rather than a membership every set satisfies. -/
theorem interp_ruleType_eq_true_of_zero {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
    (h0 : u.eval M.ls = 0) :
    (interp M L ([] : List VExpr) (ruleTyJ u)).toFun ∅ = ({pt} : V) := by
  rcases eq_empty_or_eq_true_of_mem_UProp (interp_ruleType_mem_UProp_of_zero hu hle h0) with h | h
  · exact absurd (h ▸ interp_lhs_mem_ruleType_of_zero hu hle h0) not_mem_empty
  · exact h

end Rules


/-! ## 14. **`InductOracleOK` at `iffIndDecl`, assembled**

Both fields, at the shared witness.  `consts` is `IffConstsAudit.inductOracleOK_consts_Iff`; §13
supplies `rules`.  The only hypotheses are `hle : iffEnv ≤ envF` (discharged at `preludeEnv` by
`IffAudit.iffEnv_le_preludeEnv`) and `hS : L.Stable` (undischarged in this tree; available at the
consumer as `PropSplitUp.propSplitUp_stable`, exactly as for `EqIotaAudit.inductOracleOK_Eq`). -/

section Assemble

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **`InductOracleOK` at `iffIndDecl`.**  Both fields, at `SetModel.preludeWitness` -- the
assignment `PreludeOracle.lean` uses (`NEAudit.neM_eq`).  No side oracle parameter, no chosen `κ`,
no chain hypothesis; `Above` is discharged by `Above.pure` throughout. -/
theorem inductOracleOK_Iff (hS : L.StableLift) (hle : iffEnv ≤ envF) :
    InductOracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst iffIndDecl :=
  ⟨IffConstsAudit.inductOracleOK_consts_Iff L κ ls hle,
    inductOracleOK_rules_Iff_preludeWitness hS hle κ ls⟩

/-! ## The payoff of the `StableLift` weakening

`inductOracleOK_Eq` above is stated at an arbitrary `L` and therefore still carries a hypothesis.
Instantiating it at the split `UpperBound.OracleInput` actually fixes discharges that hypothesis
outright, because `StableLift` is *free* there (`propSplitUp_stableLift` needs only `Ordered`,
`PropUniq`, `PropTypeAgree` -- and `hU`/`hT` are already **data** arguments of `propSplitUp`, which
`OracleInput` takes, so this adds no obligation at the consumer).

What this does **not** buy: `InstDescendUp` does not leave the main theorem.  `interp_inst` still
needs the two `inst` fields, so `ModelFits` and `UpperBound.consistent_of_inputs` still do.  What
leaves is that input's appearance in the prelude's `.induct` steps, and no more. -/
theorem inductOracleOK_Iff_at_propSplitUp {envF : VEnv} {nv : ℕ} (henv : envF.Ordered)
    (hU : envF.PropUniq nv) (hT : envF.PropTypeAgree nv) (κ : ℕ → V) (ls : List ℕ)
    (hle : iffEnv ≤ envF) :
    InductOracleOK (propSplitUp envF nv henv hU hT) κ ls
      (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst iffIndDecl :=
  inductOracleOK_Iff _ κ ls (propSplitUp_stableLift henv hU hT) hle

#print axioms Lean4Lean.SetModel.IffIotaAudit.inductOracleOK_Iff_at_propSplitUp

end Assemble


/-! ## 15. Axiom audit, **by namespace**

This file declares into `Lean4Lean.SetModel.IffIotaAudit`; the names it reuses live in
`Lean4Lean.SetModel` (`iffRecFn`, `minSet`, `motSetI`, `iffFn`, `preludeWitness`,
`interp_closed_ctx`), `…IffAudit`, `…IffLargeAudit`, `…IffConstsAudit`, `…EqAudit`,
`…EqZeroAudit`, `…EqLargeAudit` and `…UnitAudit`.  Every name below is
`Lean4Lean.SetModel.IffIotaAudit.*`. -/

#print axioms Lean4Lean.SetModel.IffIotaAudit.iff_iotaRules_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRule_uvars
#print axioms Lean4Lean.SetModel.IffIotaAudit.iff_iotaCtx
#print axioms Lean4Lean.SetModel.IffIotaAudit.iff_iotaCtx_reverse
#print axioms Lean4Lean.SetModel.IffIotaAudit.iff_iotaType
#print axioms Lean4Lean.SetModel.IffIotaAudit.minTyI_lift_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRule_lhs_instL
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRule_rhs_instL
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRule_type_instL
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffEnv_WF'
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffEnv_ordered
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_mpTyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_mprTyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.onCtxJ_P
#print axioms Lean4Lean.SetModel.IffIotaAudit.onCtxJ_Q
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_IffRecC
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_mot_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_min_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_motTyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_introC3J
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_introC3JTy
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_introAp_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_iotaLhsBodyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_iotaTypeJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.ruleTyJ_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRuleSort_eval_eq_zero_iff
#print axioms Lean4Lean.SetModel.IffIotaAudit.minSortI_eval_eq_zero_iff
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRuleSort_wf
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyP
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyN
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyM
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyB
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_ruleTyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRecFn_app_intro
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProof_introC3J
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_iotaLhsBody_app
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_lamBodyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_iotaLamJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.iotaLamJ_closed
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_minTyJ3
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_minAp1
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_minAp1Ty
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_min_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_minAp1
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_lamBodyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_lamBJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_iotaLamJ_app
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_mp_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_iotaRhsBody_val
#print axioms Lean4Lean.SetModel.IffIotaAudit.lhsA_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.rhsA_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.ruleTyA_eq
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_lhsB
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_iotaRhsBodyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.hasType_rhsB
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProp_ruleTyB
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProp_iotaTypeJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_lhsB
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_iotaLhsBodyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.onCtxJ_Pa
#print axioms Lean4Lean.SetModel.IffIotaAudit.onCtxJ_Qb
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProp_mpCodJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProp_mprCodJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.mp_eq_pt
#print axioms Lean4Lean.SetModel.IffIotaAudit.mpr_eq_pt
#print axioms Lean4Lean.SetModel.IffIotaAudit.eq_of_mem_mpTyJ_mprTyJ
#print axioms Lean4Lean.SetModel.IffIotaAudit.not_isProof_mot_jctxQ
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_iotaTypeJ_val
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_iotaLhsBody_val
#print axioms Lean4Lean.SetModel.IffIotaAudit.minAp_mem_motAp
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_sides_eq_of_ne
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_lhs_mem_ruleType_of_ne
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProof_lhsB
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProof_rhsB
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProp_ruleTyB_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.isProp_iotaTypeJ_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_sides_eq_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_lhs_mem_ruleType_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.defEqOK_iffRule
#print axioms Lean4Lean.SetModel.IffIotaAudit.inductOracleOK_rules_Iff
#print axioms Lean4Lean.SetModel.IffIotaAudit.inductOracleOK_rules_Iff_preludeWitness
#print axioms Lean4Lean.SetModel.IffIotaAudit.pt_not_mem_ruleType_of_ne
#print axioms Lean4Lean.SetModel.IffIotaAudit.iffRule_discriminates
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_lhs_ne_pt_of_ne
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_ruleType_mem_UProp_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.interp_ruleType_eq_true_of_zero
#print axioms Lean4Lean.SetModel.IffIotaAudit.inductOracleOK_Iff


end Lean4Lean.SetModel.IffIotaAudit
