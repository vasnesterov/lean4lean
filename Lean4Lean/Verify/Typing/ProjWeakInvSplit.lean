import Lean4Lean.Verify.Typing.ProjInhab
import Lean4Lean.Theory.Typing.StrengthenNarrow

/-!
# `TrProj.weak'_inv` split: the typing half of `weakN_iff`, plus one conversion statement

`Verify/Typing/ProjWeakInv.lean` reduces `TrProj.weak'_inv` to `VEnv.ConstAppTypeStrengthen`
(`TrProj.weak'_inv_of_strengthen`, the hole's statement verbatim) and bounds that residual three
ways; `Verify/Typing/ProjInhab.lean` then pins the remaining case to `VEnv.Consistent`.  Both
files leave the residual as **one** opaque `Prop` mixing two different obligations: recovering a
typing for the subject in the smaller context, and recovering the *head* of that typing.

This file separates them, and the separation is the point:

    VEnv.TypingStrengthening env U           -- the TYPING half of the `weakN_iff` hole,
                                             -- an existing named statement (`Strengthen.lean`)
    VEnv.ConstAppDefeqStrengthen env U       -- NEW: a `c`-spine definitionally equal to a lift
                                             -- is definitionally a `c`-spine one context down
    ─────────────────────────────────────────
    VEnv.ConstAppTypeStrengthen env U        -- the ProjWeakInv residual
    ⟹ `TrProj.weak'_inv`'s exact statement  (`TrProj.weak'_inv_of_typing_head`)

Three consequences, each measured rather than argued:

1. **The subject half of the residual is not new content.**  It is `VEnv.TypingStrengthening`,
   `Strengthen.lean` §2's "typing half" — the gate `scripts/weakn-gate-split.lean` measures as
   sufficient for 43 of `IsDefEqU.weakN_iff`'s 296 users.  So the only part of
   `ConstAppTypeStrengthen` that is not already a named piece of the `weakN_iff` hole is the
   *head* statement.
2. **The head statement is not an instance of the `weakN_iff` hole, and that is machine-checked
   rather than read off the shape.**  `Strengthening`/`StrengtheningTarget`/`IsDefEqU.weakN_iff`
   all require *both* sides of the conversion to be lifts.  Here the right-hand side is a
   `c`-spine whose arguments live in `Γ'`, and `constAppDefeqStrengthen_rhs_not_skips` exhibits
   an instance whose hypothesis holds while the right-hand side **does not skip** the stripped
   binder — so no instantiation of the strengthening hole has that hypothesis.  `weak'_inv` is
   therefore *not* a corollary of the strengthening hole, however that hole is discharged; the
   head statement is a genuinely separate obligation, and it is the whole of what is separate.
3. **`us' = us` and `as' = as` are both unavailable in general.**  The witness of point 2 is a
   spine whose single argument must be *converted* away, not renamed: `as' ≠ as` there
   (`constAppDefeqStrengthen_moves`).  So the `∃ as'` of both statements is load-bearing.

## What is *not* claimed

Nothing here discharges a `sorry`, and the census does not move.  `ConstAppDefeqStrengthen` is
open, exactly as `ConstAppTypeStrengthen` was, and the honest reading of the split is a *negative*
one: it separates out the part of `TrProj.weak'_inv` that discharging the strengthening hole
cannot pay for.  For that part the routes on offer are unchanged and both are shut —
rigidity (`VEnv.ConstRigidPat`, whose only producer needs the refuted `VEnv.WeakNorm`) or
confluence with lift-preservation (`church_rosser` + `ParRed.weakN_inv`, which re-imports the
refuted `NormalEq.descend`).

## Bounds on the new statement, all hole-free

* `constAppDefeqStrengthen_depth_zero` — holds at every lift of depth 0.
* `constAppDefeqStrengthen_inhab` — holds at every depth across a `Ctx.InhabLift`, with `us' = us`
  on the nose; the same instantiation mechanism as `constAppTypeStrengthen_inhab`.
* `VEnv.AllTypesInhabited.constAppDefeqStrengthen` and
  `exists_univInhabEnv_typing_and_head` — **both** hypotheses of the split hold simultaneously at
  a `VEnv.WF` environment, so the reduction is not vacuous as a reduction.  (That environment is
  inconsistent, per `ProjInhab.lean` §2; it is a satisfiability witness and no more.)
* `constAppDefeqStrengthen_fires_degenerate` — hypotheses satisfiable at the degenerate instance
  `Γ = []`, depth-one lift, empty spine.
* `constAppDefeqStrengthen_rhs_not_skips` / `_moves` — point 2 and point 3 above.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean VExpr

/-! ## 1. The head statement -/

/-- **The head half of the projection residual.**  A `c`-headed application that is
definitionally equal, in the larger context, to a *lift* is definitionally equal, in the smaller
context, to a `c`-headed application of the same length and pointwise-equivalent levels.

Nothing about typing: this is a statement about `IsDefEqU` alone.  Compare
`VEnv.ConstAppTypeStrengthen` (`Verify/Typing/ProjWeakInv.lean`), which additionally has to
produce the typing of the subject — that part is `VEnv.TypingStrengthening`. -/
def VEnv.ConstAppDefeqStrengthen (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {B : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' → (∀ u ∈ us, u.WF U) →
    env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us').mkApp as')

/-! ## 2. The split -/

/-- **The split.**  The `ProjWeakInv` residual is the typing half of the `weakN_iff` hole
together with the head statement, and nothing else.

Route: `TypingStrengthening.wf_weak'_inv` recovers *some* type `B₀` for `e` in `Γ`;
`HasType.weak'` pushes it back up; `IsDefEq.uniqU` identifies `B₀.lift' l` with the given
`c`-spine; the head statement moves that identification down to `Γ`; `HasType.defeqU_r`
retypes `e`.  `OnCtx Γ` comes from `TypingStrengthening.onCtx_weak'_inv`, **not** from
`OnCtx.weak'_inv` — so no appeal to `IsDefEqU.weakN_iff` is made anywhere. -/
theorem constAppTypeStrengthen_of_typing_head {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (HT : env.TypingStrengthening U) (HR : env.ConstAppDefeqStrengthen U) :
    env.ConstAppTypeStrengthen U := by
  intro l Γ Γ' e c us as hΓ' W hlv hty
  have hΓ : OnCtx Γ (env.IsType U) := HT.onCtx_weak'_inv henv W hΓ'
  obtain ⟨B₀, hB₀⟩ : VExpr.WF env U Γ e := HT.wf_weak'_inv henv rfl W hΓ' ⟨_, hty⟩
  have hlift : env.HasType U Γ' (e.lift' l) (B₀.lift' l) := hB₀.weak' henv.ordered W
  have heq : env.IsDefEqU U Γ' (B₀.lift' l) ((VExpr.const c us).mkApp as) :=
    VEnv.IsDefEq.uniqU henv hΓ' hlift hty
  obtain ⟨us', as', hlv', huseq, hlen, hdef⟩ := HR hΓ' W hlv heq
  exact ⟨us', as', hlv', huseq, hlen, VEnv.HasType.defeqU_r henv hΓ hdef hB₀⟩

/-- **`TrProj.weak'_inv`'s exact statement** from the typing half and the head statement.  Same
conclusion as the `sorry` in `Verify/Typing/Lemmas.lean`, with `OnCtx Γ'` as there; `OnCtx Γ` is
obtained from `HT` rather than from `OnCtx.weak'_inv`, which is what keeps `IsDefEqU.weakN_iff`
out of this theorem's cone. -/
theorem TrProj.weak'_inv_of_typing_head {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (HT : env.TypingStrengthening U) (HR : env.ConstAppDefeqStrengthen U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_strengthen_onCtx henv
    (constAppTypeStrengthen_of_typing_head henv HT HR) hΓ' (HT.onCtx_weak'_inv henv W hΓ') W H

/-! ## 3. The head statement is bounded, exactly as the residual was -/

/-- **Not false: it holds at every lift of depth zero**, with `us' = us`, `as' = as`. -/
theorem constAppDefeqStrengthen_depth_zero {env : VEnv} {U : Nat} {l : Lift}
    {Γ Γ' : List VExpr} {B : VExpr} {c : Lean.Name} {us : List VLevel} {as : List VExpr}
    (hd : l.depth = 0) (W : Ctx.Lift' l Γ Γ') (hlv : ∀ u ∈ us, u.WF U)
    (H : env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us').mkApp as') := by
  cases W.depth_zero hd
  rw [VExpr.lift'_depth_zero hd] at H
  exact ⟨us, as, hlv, .rfl fun _ _ => rfl, rfl, H⟩

/-- The conversion-level analogue of `hasType_const_mkApp_of_inhabLift`: across an inhabited
lift the equation descends by instantiation, at every depth. -/
theorem isDefEqU_const_mkApp_of_inhabLift {env : VEnv} {U : Nat} (henv : env.Ordered)
    {c : Lean.Name} {us : List VLevel} :
    ∀ {l : Lift} {Γ Γ' : List VExpr}, Ctx.InhabLift env U l Γ Γ' →
      ∀ {B : VExpr} {as : List VExpr},
      env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as) →
      ∃ as', as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us).mkApp as') := by
  intro l Γ Γ' W
  induction W with
  | refl => intro B as H; exact ⟨as, rfl, by simpa using H⟩
  | step W1 WL ht WI ih =>
    intro B as H
    rw [VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have H2 := H.instN henv WI ht
    rw [VExpr.inst_liftN, VExpr.inst_mkApp,
      show (VExpr.const c us).inst _ _ = VExpr.const c us from rfl] at H2
    obtain ⟨as', hlen, H3⟩ := ih H2
    exact ⟨as', by simpa using hlen, H3⟩

/-- **The head statement holds at every inhabited lift**, with `us` untouched. -/
theorem constAppDefeqStrengthen_inhab {env : VEnv} {U : Nat} (henv : env.Ordered) {l : Lift}
    {Γ Γ' : List VExpr} {B : VExpr} {c : Lean.Name} {us : List VLevel} {as : List VExpr}
    (W : Ctx.InhabLift env U l Γ Γ') (hlv : ∀ u ∈ us, u.WF U)
    (H : env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us').mkApp as') :=
  let ⟨as', h1, h2⟩ := isDefEqU_const_mkApp_of_inhabLift henv W H
  ⟨us, as', hlv, .rfl fun _ _ => rfl, h1, h2⟩

/-! ## 4. Both hypotheses of the split hold at one environment -/

/-- The `AllTypesInhabited` route for the head statement, mirroring
`constAppTypeStrengthen_of_allTypesInhabited_aux` (`Verify/Typing/ProjInhab.lean`) at the
conversion level: peel the outermost inserted binder, instantiate it with an inhabitant, recurse
with the smaller context's well-formedness recovered by `Ctx.InstN.wf`. -/
theorem constAppDefeqStrengthen_of_allTypesInhabited_aux {env : VEnv} {U : Nat}
    (henv : env.Ordered) (hinh : env.AllTypesInhabited U) {c : Lean.Name} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {B : VExpr} {us : List VLevel} {as : List VExpr},
      l.depth = n → Ctx.Lift' l Γ Γ' → OnCtx Γ' (env.IsType U) →
      env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as) →
      ∃ as', as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us).mkApp as') := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' B us as hd W hΓ' H
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at H
    exact ⟨as, rfl, H⟩
  | succ n ih =>
    intro l Γ Γ' B us as hd W hΓ' H
    obtain ⟨l, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W2.exists_instN_typed hΓ'
    obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
    have H2 := H.instN henv (hI e₀) h₀
    rw [VExpr.inst_liftN, VExpr.inst_mkApp,
      show (VExpr.const c us).inst _ _ = VExpr.const c us from rfl] at H2
    have hΓ₂ : OnCtx Γ₂ (env.IsType U) := (Ctx.InstN.wf henv (hI e₀) h₀ hΓ').2
    obtain ⟨as', hlen, h3⟩ := ih (by simpa using hdl) W1 hΓ₂ H2
    exact ⟨as', by simpa using hlen, h3⟩

/-- `AllTypesInhabited` closes the head statement too, at every depth and with `us' = us`. -/
theorem VEnv.AllTypesInhabited.constAppDefeqStrengthen {env : VEnv} {U : Nat}
    (henv : env.Ordered) (hinh : env.AllTypesInhabited U) : env.ConstAppDefeqStrengthen U :=
  fun hΓ' W hlv H =>
    let ⟨as', hlen, h⟩ :=
      constAppDefeqStrengthen_of_allTypesInhabited_aux henv hinh _ rfl W hΓ' H
    ⟨_, as', hlv, .rfl fun _ _ => rfl, hlen, h⟩

/-- **The split is not vacuous as a reduction**: both of its hypotheses hold, simultaneously, at
a `VEnv.WF` environment — `ProjInhab.lean` §3's `univInhab` environment.  The typing half comes
from `AllTypesInhabited.strengtheningTarget`, the head statement from the theorem above.

Read with `ProjInhab.lean` §2: that environment is **inconsistent** and has no uninhabited binder
at any well-formed context, so this is a satisfiability witness for the two hypotheses and no
evidence at all about the obstruction. -/
theorem exists_univInhabEnv_typing_and_head :
    ∃ env : VEnv, VEnv.WF env ∧ ¬ env.Consistent ∧
      ∀ U, env.TypingStrengthening U ∧ env.ConstAppDefeqStrengthen U := by
  obtain ⟨env, henv, hc⟩ := exists_univInhabEnv_constants
  refine ⟨env, henv, VEnv.AllTypesInhabited.not_consistent (allTypesInhabited_of_univInhab hc),
    fun U => ⟨?_, VEnv.AllTypesInhabited.constAppDefeqStrengthen henv.ordered
      (allTypesInhabited_of_univInhab hc)⟩⟩
  exact VEnv.Strengthening.typing (VEnv.StrengtheningTarget.strengthening
    (VEnv.AllTypesInhabited.strengtheningTarget henv (allTypesInhabited_of_univInhab hc)))

/-- **`TrProj.weak'_inv`'s exact statement at that environment, through the split.**  Like
`exists_univInhabEnv_trProj_weak'_inv` (`ProjInhab.lean`) this is **not** hole-free: the
`TrProj` reduction it goes through carries `IsDefEqU.forallE_inv_stratified` and
`WF.rigidShapeUniqNS` of its own, from `HasArgs.of_mkApp`.  Kept to show the composite fires. -/
theorem exists_univInhabEnv_trProj_weak'_inv_split :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ {U : Nat} {Γ Γ' : List VExpr} {l : Lift}
      {s : Lean.Name} {i : Nat} {e e' : VExpr}, OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e'' := by
  obtain ⟨env, henv, _, h⟩ := exists_univInhabEnv_typing_and_head
  exact ⟨env, henv, fun hΓ' W H =>
    TrProj.weak'_inv_of_typing_head henv (h _).1 (h _).2 hΓ' W H⟩

/-! ## 5. The degenerate instance, and why the strengthening hole cannot reach this statement -/

/-- **The degenerate instance**: `Γ = []`, a depth-one lift, the empty spine.  The hypotheses are
satisfiable and the conclusion is discharged by `constAppDefeqStrengthen_inhab`, in every
environment declaring a `Sort 0`-valued constant. -/
theorem constAppDefeqStrengthen_fires_degenerate {env : VEnv} {U : Nat} {c : Lean.Name}
    (henv : env.Ordered) (hc : env.constants c = some ⟨0, .sort .zero⟩) :
    OnCtx [VExpr.sort (.succ .zero)] (env.IsType U) ∧
      Ctx.InhabLift env U (.skip .refl) [] [VExpr.sort (.succ .zero)] ∧
      env.IsDefEqU U [VExpr.sort (.succ .zero)]
        ((VExpr.const c []).lift' (.skip .refl)) ((VExpr.const c []).mkApp []) ∧
      ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' ([] : List VLevel) ∧
        as'.length = ([] : List VExpr).length ∧
        env.IsDefEqU U [] (VExpr.const c []) ((VExpr.const c us').mkApp as') := by
  have hW : Ctx.InhabLift env U (.skip .refl) [] [VExpr.sort (.succ .zero)] :=
    Ctx.InhabLift.refl.skip (t := .sort .zero) (VEnv.HasType.sort trivial)
  have hH : env.IsDefEqU U [VExpr.sort (.succ .zero)]
      ((VExpr.const c []).lift' (.skip .refl)) ((VExpr.const c []).mkApp []) := by
    exact ⟨VExpr.sort .zero, by
      simpa [VEnv.HasType, VExpr.mkApp] using
        hasType_const_sortZero (env := env) (U := U) (Γ := [VExpr.sort (.succ .zero)]) hc⟩
  exact ⟨⟨trivial, _, VEnv.HasType.sort trivial⟩, hW, hH,
    constAppDefeqStrengthen_inhab henv hW (by simp) hH⟩

/-- The spine argument of the witness below: a β-redex that mentions the stripped binder and
converts to a closed term. -/
def constAppBetaArg : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0)

/-- **The strengthening hole cannot reach the head statement, and the reason is exhibited rather
than read off the shape.**  `VEnv.Strengthening`, `VEnv.StrengtheningTarget` and
`IsDefEqU.weakN_iff` all require *both* endpoints of the conversion to be lifts of terms of the
smaller context — syntactically, `.Skips n k`.  The head statement's right-hand side is a
`c`-spine whose arguments live in `Γ'`, and here is an instance where its hypothesis holds while
that right-hand side does **not** skip the stripped binder: so no instantiation of the
strengthening hole has this hypothesis, and discharging that hole — however it is discharged —
does not discharge this.

The witness needs one constant `c : Sort 1 → Sort 1` and one β-redex, and it also settles that
the `∃ as'` is load-bearing: the spine argument has to be *converted* away, so the produced
`as'` differs from `as` (`constAppDefeqStrengthen_moves`). -/
theorem constAppDefeqStrengthen_rhs_not_skips {env : VEnv} {U : Nat} {c : Lean.Name}
    (hc : env.constants c = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    OnCtx [VExpr.sort (.succ .zero)] (env.IsType U) ∧
      Ctx.Lift' (.skip .refl) [] [VExpr.sort (.succ .zero)] ∧
      env.IsDefEqU U [VExpr.sort (.succ .zero)]
        (((VExpr.const c []).app (.sort .zero)).lift' (.skip .refl))
        ((VExpr.const c []).mkApp [constAppBetaArg]) ∧
      ¬ ((VExpr.const c []).mkApp [constAppBetaArg]).Skips 1 0 := by
  have hconst : ∀ Γ : List VExpr, env.IsDefEq U Γ (.const c []) (.const c [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := fun Γ => by
    have := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
      hc (by simp) (by simp) (by simp) (List.Forall₂.rfl fun _ _ => rfl)
    simpa [VExpr.instL, VLevel.inst] using this
  have hbvar : env.HasType U [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := by
    have := VEnv.HasType.bvar (env := env) (U := U) (Γ := [VExpr.sort (.succ .zero)]) (i := 0)
      (A := _) .zero
    simpa [VExpr.lift, VExpr.liftN] using this
  have hbeta : env.IsDefEq U [VExpr.sort (.succ .zero)] constAppBetaArg (.sort .zero)
      (.sort (.succ .zero)) := by
    have := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := [VExpr.sort (.succ .zero)])
      (A := .sort (.succ .zero)) (e := .sort .zero) (B := .sort (.succ .zero))
      (e' := .bvar 0) (VEnv.HasType.sort trivial) hbvar
    simpa [constAppBetaArg, VExpr.inst] using this
  refine ⟨⟨trivial, _, VEnv.HasType.sort trivial⟩, .skip .refl,
    ⟨VExpr.sort (.succ .zero), ?_⟩, ?_⟩
  · have := VEnv.IsDefEq.appDF (hconst [VExpr.sort (.succ .zero)]) hbeta.symm
    simpa [VExpr.mkApp, VExpr.inst] using this
  · rw [VExpr.skips_iff]
    simp [VExpr.Skips', VExpr.mkApp, constAppBetaArg]

/-- **`as' = as` is not available**: at the same witness the only conversion available in the
smaller context replaces the β-redex by its reduct, so the spine genuinely moves. -/
theorem constAppDefeqStrengthen_moves {env : VEnv} {U : Nat} {c : Lean.Name}
    (hc : env.constants c = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    ([VExpr.sort .zero] : List VExpr) ≠ [constAppBetaArg] ∧
      ([VExpr.sort .zero] : List VExpr).length = ([constAppBetaArg] : List VExpr).length ∧
      env.IsDefEqU U [] ((VExpr.const c []).app (.sort .zero))
        ((VExpr.const c []).mkApp [VExpr.sort .zero]) := by
  refine ⟨by simp [constAppBetaArg], rfl, ⟨VExpr.sort (.succ .zero), ?_⟩⟩
  have hconst := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := ([] : List VExpr))
    (ls := []) (ls' := []) hc (by simp) (by simp) (by simp) (List.Forall₂.rfl fun _ _ => rfl)
  have := VEnv.IsDefEq.appDF (by simpa [VExpr.instL, VLevel.inst] using hconst)
    (VEnv.HasType.sort (env := env) (U := U) (Γ := ([] : List VExpr))
      (l := VLevel.zero) trivial)
  simpa [VExpr.mkApp, VExpr.inst] using this

/-! ## 6. The tight form: what the consumer actually supplies

`constAppTypeStrengthen_of_typing_head` calls the head statement at a `B` it has just produced a
*typing* for — `Γ ⊢ e : B` — so the head statement may take that as a premise and still be enough.
Doing so makes it strictly weaker, hence a tighter description of what is left, and every bound of
§3–§5 transfers to it through `VEnv.ConstAppDefeqStrengthen.inh`.

One further premise is available at the call site and is deliberately **not** taken:
`TrProj.mk`'s own `hS : env.IsStructure S D T C`, so the head could be restricted to structure
names.  It is not taken because it repairs nothing on either known route — rigidity's gate is
`VEnv.WeakNorm` (weak-head-normal-form *existence*), not the head condition, and
`VEnv.IsStructure.ruleFreeHead` already discharges the head condition — while its non-vacuity
would need an `IsStructure` witness, i.e. a full `addInduct'` staging.  Recorded so the next round
knows the premise is there for the taking. -/

/-- **The tight head statement**: as `VEnv.ConstAppDefeqStrengthen`, but the type `B` being
strengthened is additionally *inhabited in the smaller context* — which is exactly the situation
the split creates, the inhabitant being the projection's own subject. -/
def VEnv.ConstAppDefeqStrengthenInh (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {t B : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' → (∀ u ∈ us, u.WF U) →
    env.HasType U Γ t B →
    env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us').mkApp as')

/-- The tight form is weaker, so every bound on the general form bounds it too. -/
theorem VEnv.ConstAppDefeqStrengthen.inh {env : VEnv} {U : Nat}
    (H : env.ConstAppDefeqStrengthen U) : env.ConstAppDefeqStrengthenInh U :=
  fun hΓ' W hlv _ h => H hΓ' W hlv h

/-- **The split, at the tight head statement.**  Same conclusion as
`constAppTypeStrengthen_of_typing_head`, with the head hypothesis narrowed to inhabited types. -/
theorem constAppTypeStrengthen_of_typing_head_inh {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (HT : env.TypingStrengthening U) (HR : env.ConstAppDefeqStrengthenInh U) :
    env.ConstAppTypeStrengthen U := by
  intro l Γ Γ' e c us as hΓ' W hlv hty
  have hΓ : OnCtx Γ (env.IsType U) := HT.onCtx_weak'_inv henv W hΓ'
  obtain ⟨B₀, hB₀⟩ : VExpr.WF env U Γ e := HT.wf_weak'_inv henv rfl W hΓ' ⟨_, hty⟩
  have hlift : env.HasType U Γ' (e.lift' l) (B₀.lift' l) := hB₀.weak' henv.ordered W
  have heq : env.IsDefEqU U Γ' (B₀.lift' l) ((VExpr.const c us).mkApp as) :=
    VEnv.IsDefEq.uniqU henv hΓ' hlift hty
  obtain ⟨us', as', hlv', huseq, hlen, hdef⟩ := HR hΓ' W hlv hB₀ heq
  exact ⟨us', as', hlv', huseq, hlen, VEnv.HasType.defeqU_r henv hΓ hdef hB₀⟩

/-- **`TrProj.weak'_inv`'s exact statement** from the typing half and the *tight* head statement. -/
theorem TrProj.weak'_inv_of_typing_head_inh {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (HT : env.TypingStrengthening U)
    (HR : env.ConstAppDefeqStrengthenInh U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_strengthen_onCtx henv
    (constAppTypeStrengthen_of_typing_head_inh henv HT HR) hΓ'
    (HT.onCtx_weak'_inv henv W hΓ') W H

/-- **The witness of §5 survives the extra premise**: with one further constant
`d : c (Sort 0)` the strengthened type is inhabited in `Γ = []`, so the instance whose right-hand
side does not skip the stripped binder is an instance of the **tight** statement as well.  Without
this the narrowing of §6 could have been vacuous at exactly the instances that carry its content. -/
theorem constAppDefeqStrengthenInh_rhs_not_skips {env : VEnv} {U : Nat} {c d : Lean.Name}
    (hc : env.constants c = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hd : env.constants d = some ⟨0, (VExpr.const c []).app (.sort .zero)⟩) :
    env.HasType U [] (.const d []) ((VExpr.const c []).app (.sort .zero)) ∧
      OnCtx [VExpr.sort (.succ .zero)] (env.IsType U) ∧
      Ctx.Lift' (.skip .refl) [] [VExpr.sort (.succ .zero)] ∧
      env.IsDefEqU U [VExpr.sort (.succ .zero)]
        (((VExpr.const c []).app (.sort .zero)).lift' (.skip .refl))
        ((VExpr.const c []).mkApp [constAppBetaArg]) ∧
      ¬ ((VExpr.const c []).mkApp [constAppBetaArg]).Skips 1 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := constAppDefeqStrengthen_rhs_not_skips (U := U) hc
  refine ⟨?_, h1, h2, h3, h4⟩
  have := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := ([] : List VExpr))
    (ls := []) (ls' := []) hd (by simp) (by simp) (by simp) (List.Forall₂.rfl fun _ _ => rfl)
  simpa [VEnv.HasType, VExpr.instL, VLevel.inst] using this

/-! ## 7. Rigidity closes the head statement — so the split's residual is (C) together with (B)

`Verify/Typing/Lemmas.lean`'s Update 7 replaced the rigidity route by a strengthening residual and
recorded that "(C) is *sufficient* for the shape step, not necessary".  That is right as a
statement about necessity, and it left the sufficiency direction as prose.  Here it is a theorem,
at the *split's* residual rather than at the whole hole:

    (C) `VEnv.ConstRigid` + (B) `ConstAppInvStmt`  ⟹  the head statement, pointwise

with the levels and the arity coming from (B) and the head from (C), exactly as that docstring's
Update 1 predicted.  What this pins down is the shape of the remaining obstruction: the head
statement is **bounded above** by the classical rigidity/injectivity pair, and (C)'s only producer
in the tree is `VEnv.constRigidPat_of_weakNorm`, whose antecedent is refuted sorry-free
(`Verify/Typing/WeakNormRefute.lean`).  (B) is available modulo `PatWF`
(`VEnv.const_app_inv_of_patWF`).

Both are taken as *hypotheses*, so this theorem is hole-free; nothing here claims either is
available. -/

/-- A lift that *is* a spine is a spine of lifts, head included.  The inversion `WHRedS.weakU_inv`
leaves behind. -/
theorem VExpr.lift'_eq_mkApp_inv {l : Lift} :
    ∀ {as : List VExpr} {X f : VExpr}, X.lift' l = f.mkApp as →
      ∃ (g : VExpr) (as₀ : List VExpr),
        X = g.mkApp as₀ ∧ f = g.lift' l ∧ as = as₀.map (·.lift' l)
  | [], X, f, h => ⟨X, [], rfl, h.symm, rfl⟩
  | a :: as, X, f, h => by
    obtain ⟨g, as₀, rfl, hf, rfl⟩ := VExpr.lift'_eq_mkApp_inv (as := as) (X := X) h
    match g, hf with
    | .app g b, hf =>
      refine ⟨g, b :: as₀, rfl, ?_, ?_⟩
      · simp at hf; exact hf.1
      · simp at hf; simp [hf.2]

/-- The `const`-headed case: the head cannot have moved. -/
theorem VExpr.lift'_eq_constApp_inv {l : Lift} {X : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr} (h : X.lift' l = (VExpr.const c us).mkApp as) :
    ∃ as₀ : List VExpr, X = (VExpr.const c us).mkApp as₀ ∧ as = as₀.map (·.lift' l) := by
  obtain ⟨g, as₀, rfl, hg, hmap⟩ := VExpr.lift'_eq_mkApp_inv h
  match g, hg with
  | .const c' us', hg => cases hg; exact ⟨as₀, rfl, hmap⟩

/-- **(C) + (B) close the head statement.**  Route, one step per ingredient:

1. **(C) at `Γ'`** (`VEnv.ConstRigid.at_lift`) — the lifted subject weak-head reduces to a
   `c`-spine `(const c us₁).mkApp as₁`.
2. `WHRedS.defeq` turns that reduction into a `Γ'`-conversion, so
   `(const c us).mkApp as ≡ (const c us₁).mkApp as₁`.
3. **(B)** (`ConstAppInvStmt`) reads off `us ≈ us₁` pointwise and `as ≡ as₁` pointwise — the
   levels and, through `List.Forall₂.length_eq`, the **arity**, neither of which (C) supplies.
4. `WHRedS.weakU_inv` moves the reduction of step 1 into `Γ`; its reduct is a lift, and
   `VExpr.lift'_eq_constApp_inv` reads the pre-image spine `as₂` off it.
5. `WHRedS.defeq` again, now in `Γ`, at the type of `B` supplied by the inhabitant `t`.
6. The levels' well-formedness comes from the reduct's own typing (`IsDefEq.levelWF`,
   `VExpr.levelWF_mkApp`), not from `us ≈ us₁`, which does not transport it. -/
theorem constAppDefeqStrengthenInh_of_constRigid [VEnv.Params]
    (HC : VEnv.ConstRigid) (HB : ConstAppInvStmt VEnv.Params.env VEnv.Params.univs)
    {l : Lift} {Γ Γ' : List VExpr} {t B : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr}
    (hΓ' : OnCtx Γ' (VEnv.Params.env.IsType VEnv.Params.univs))
    (hΓ : OnCtx Γ (VEnv.Params.env.IsType VEnv.Params.univs))
    (W : Ctx.Lift' l Γ Γ')
    (hrf : VEnv.Params.env.RuleFreeHead c)
    (hIT : VEnv.Params.env.IsType VEnv.Params.univs Γ' ((VExpr.const c us).mkApp as))
    (ht : VEnv.Params.env.HasType VEnv.Params.univs Γ t B)
    (hdf : VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ' (B.lift' l)
      ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF VEnv.Params.univs) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧
      VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ B ((VExpr.const c us').mkApp as') := by
  have henv := VEnv.Params.henv
  obtain ⟨T, hBT⟩ := hdf
  -- 1.
  obtain ⟨us₁, as₁, hred⟩ := HC.at_lift hΓ' W hrf hIT ⟨T, hBT⟩
  -- 2.
  have hred_df : VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ' (B.lift' l)
      ((VExpr.const c us₁).mkApp as₁) := ⟨T, hred.defeq hΓ' hBT.hasType.1⟩
  have h23 : VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ' ((VExpr.const c us).mkApp as)
      ((VExpr.const c us₁).mkApp as₁) :=
    VEnv.IsDefEqU.trans henv hΓ' ⟨T, hBT.symm⟩ hred_df
  -- 3.
  obtain ⟨hlvs, hargs⟩ := HB Γ' c us us₁ as as₁ hΓ' hrf hIT h23
  -- 4.
  obtain ⟨X, hXeq, hredΓ⟩ := hred.weakU_inv hΓ' W
  obtain ⟨as₂, rfl, hmap⟩ := VExpr.lift'_eq_constApp_inv hXeq.symm
  -- 5.
  obtain ⟨u, hBs⟩ := ht.isType henv hΓ
  have hconc : VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ B
      ((VExpr.const c us₁).mkApp as₂) := ⟨_, hredΓ.defeq hΓ hBs⟩
  -- 6.
  have hlvWF : ∀ u ∈ us₁, u.WF VEnv.Params.univs := by
    obtain ⟨_, hc⟩ := hconc
    have := (hc.levelWF (onCtx_levelWF hΓ)).2.1
    exact (VExpr.levelWF_mkApp.1 this).1
  refine ⟨us₁, as₂, hlvWF, ?_, ?_, hconc⟩
  · exact hlvs.flip.imp fun _ _ h => VLevel.equiv_def'.2 (VLevel.equiv_def'.1 h).symm
  · have h1 : as.length = as₁.length := hargs.length_eq
    simp [hmap] at h1
    omega

/-! ## 8. Closing the loop at a structure head: `weak'_inv` from the typing half, (C) and (B)

§7 gives the head statement only at *rule-free* heads, which is all (C) is stated for.  The head
`TrProj` needs is a **structure** name, and there `VEnv.IsStructure.ruleFreeHead`
(`Theory/Typing/StructureRuleFree.lean`, proved, sorry-free) supplies exactly that side condition.
Threading it means the residual has to carry `hS`, so this section restates the `ProjWeakInv`
reduction in a structure-headed form.

`TrProj.weak'_inv_of_structStrengthen`'s proof is `TrProj.weak'_inv_of_strengthen_onCtx`'s
(`Verify/Typing/ProjWeakInv.lean:150`) verbatim, with the residual call passing `hS`; it is
duplicated rather than reused because the residual there is universally quantified over the head
and cannot see that the head is a structure.  The composite is
`TrProj.weak'_inv_of_constRigid`: **`TrProj.weak'_inv`'s exact statement, at a `VEnv.Params`
environment, from the typing half of `weakN_iff` together with (C) and (B) — every other side
condition discharged.**  That is the sharpest available statement of what the hole needs, and it
is also why the route is *closed* rather than merely expensive: (C)'s only producer is
`VEnv.constRigidPat_of_weakNorm`, and `VEnv.WeakNorm` is refuted sorry-free. -/

/-- The `ProjWeakInv` residual with the structure hypothesis carried, so that `RuleFreeHead` is
available to the head statement. -/
def VEnv.ConstAppTypeStrengthenStruct (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {e : VExpr} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {as : List VExpr},
    env.IsStructure S D T C → OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
    (∀ u ∈ us, u.WF U) → env.HasType U Γ' (e.lift' l) ((VExpr.const S us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const S us').mkApp as')

/-- The general residual is stronger, so nothing is conceded by the structure-headed form. -/
theorem VEnv.ConstAppTypeStrengthen.struct {env : VEnv} {U : Nat}
    (H : env.ConstAppTypeStrengthen U) : env.ConstAppTypeStrengthenStruct U :=
  fun _ hΓ' W hlv hty => H hΓ' W hlv hty

/-- **The head statement at rule-free heads only** — the form (C) can supply, with every premise
the call site of §8 actually has available. -/
def VEnv.ConstAppDefeqStrengthenRF (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {t B : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr},
    env.RuleFreeHead c → OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) →
    Ctx.Lift' l Γ Γ' → (∀ u ∈ us, u.WF U) →
    env.IsType U Γ' ((VExpr.const c us).mkApp as) → env.HasType U Γ t B →
    env.IsDefEqU U Γ' (B.lift' l) ((VExpr.const c us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.IsDefEqU U Γ B ((VExpr.const c us').mkApp as')

/-- **(C) + (B) give the rule-free head statement.**  Wrapper around
`constAppDefeqStrengthenInh_of_constRigid`. -/
theorem constAppDefeqStrengthenRF_of_constRigid [VEnv.Params] (HC : VEnv.ConstRigid)
    (HB : ConstAppInvStmt VEnv.Params.env VEnv.Params.univs) :
    VEnv.Params.env.ConstAppDefeqStrengthenRF VEnv.Params.univs :=
  fun hrf hΓ' hΓ W _ hIT ht hdf =>
    constAppDefeqStrengthenInh_of_constRigid HC HB hΓ' hΓ W hrf hIT ht hdf

/-- **The split, structure-headed**: the typing half plus the rule-free head statement give the
structure-headed residual, `RuleFreeHead` coming from `VEnv.IsStructure.ruleFreeHead`. -/
theorem constAppTypeStrengthenStruct_of_typing_headRF {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (HT : env.TypingStrengthening U) (HR : env.ConstAppDefeqStrengthenRF U) :
    env.ConstAppTypeStrengthenStruct U := by
  intro l Γ Γ' e S D T C us as hS hΓ' W hlv hty
  have hΓ : OnCtx Γ (env.IsType U) := HT.onCtx_weak'_inv henv W hΓ'
  obtain ⟨B₀, hB₀⟩ : VExpr.WF env U Γ e := HT.wf_weak'_inv henv rfl W hΓ' ⟨_, hty⟩
  have hlift : env.HasType U Γ' (e.lift' l) (B₀.lift' l) := hB₀.weak' henv.ordered W
  have heq : env.IsDefEqU U Γ' (B₀.lift' l) ((VExpr.const S us).mkApp as) :=
    VEnv.IsDefEq.uniqU henv hΓ' hlift hty
  obtain ⟨us', as', hlv', huseq, hlen, hdef⟩ :=
    HR (hS.ruleFreeHead henv) hΓ' hΓ W hlv (hty.isType henv hΓ') hB₀ heq
  exact ⟨us', as', hlv', huseq, hlen, VEnv.HasType.defeqU_r henv hΓ hdef hB₀⟩

/-- `TrProj.weak'_inv`'s statement from the structure-headed residual.  Proof copied from
`TrProj.weak'_inv_of_strengthen_onCtx` (`Verify/Typing/ProjWeakInv.lean:150`) with `hS` passed to
the residual; see §8's docstring for why it cannot be reused. -/
theorem TrProj.weak'_inv_of_structStrengthen {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (hst : env.ConstAppTypeStrengthenStruct U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' := by
  cases H with
  | @mk S D T C us ps ιs _ _ _ hS hty hus hps hιs hi hlv hargs hιargs hF17 =>
    obtain ⟨us', as', hlv', huseq, hlen, hty'⟩ := hst hS hΓ' W hlv hty
    have hus' : us'.length = D.uvars := huseq.length_eq.trans hus
    -- the structure's declared type, at `Γ`
    have hconst : env.HasType U Γ (.const s us') (T.type.instL us') :=
      .constDF hS.const_ty hlv' hlv' hus' (List.Forall₂.rfl fun _ _ => rfl)
    -- F1: the declared type is only *definitionally* the canonical Π-telescope
    obtain ⟨env₀, env₁, hWF, hadd, hle⟩ := hS.decl
    have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
    have hT : T ∈ D.types := by rw [hS.types]; exact List.mem_singleton_self _
    obtain ⟨u₀, hcanon⟩ := (hWF.types T hT).canon
    have hcanonD : env.IsDefEqU U Γ (T.type.instL us') ((T.canonType D).instL us') := by
      have := ((hcanon.mono hle₀).instL (U' := U) hlv').weak0 henv.ordered (Γ := Γ)
      exact ⟨_, by simpa using this⟩
    have hcanon' : env.HasType U Γ (.const s us') ((T.canonType D).instL us') :=
      VEnv.HasType.defeqU_r henv hΓ hcanonD hconst
    -- the canonical telescope, in the shape `HasArgs.of_mkApp` wants
    have hAs : (T.canonType D).instL us'
        = mkPi (List.map (VExpr.instL us') D.params ++ List.map (VExpr.instL us') T.indices)
            (.sort (VLevel.inst us' D.lvl)) := by
      simp [VIndType.canonType, VExpr.instL_mkPi, VExpr.instL]
    rw [hAs] at hcanon'
    -- split `as'` at the parameter/index boundary
    obtain ⟨ps', ιs', rfl, hps', hιs'⟩ :
        ∃ ps' ιs', as' = ps' ++ ιs' ∧ ps'.length = ps.length ∧ ιs'.length = ιs.length := by
      refine ⟨as'.take ps.length, as'.drop ps.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
      · simp [hlen]
      · simp [hlen]
    obtain ⟨u₁, hspine⟩ := hty'.isType henv hΓ
    have hargs' := VEnv.HasArgs.of_mkApp henv hΓ (ps' ++ ιs')
      (by simp [hps', hιs', hps, hιs, VInductDecl'.np]) hcanon' hspine
    obtain ⟨hP, hI⟩ := VEnv.HasArgs.append_inv
      (by simp [hps', hps, VInductDecl'.np]) hargs'
    -- F17 transports along the level equivalence
    have hF17' : D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
        VLevel.inst us' (C.fields.getD k default).lvl ≈ .zero :=
      hF17.imp_right fun h k hk hu =>
        (VLevel.equiv_congr_left (VLevel.inst_congr rfl huseq)).2 (h k hk hu)
    exact ⟨_, .mk hS hty' hus' (hps'.trans hps) (hιs'.trans hιs) hi hlv' hP hI hF17'⟩

/-- **`TrProj.weak'_inv`, from the typing half of `weakN_iff` together with (C) and (B).**  Exactly
the `sorry`'s statement, at a `VEnv.Params` environment (which `VEnv.paramsOfWF` builds from
`VEnv.WF` plus `PatWF`).  Every other side condition — `RuleFreeHead`, `IsType` of the spine, an
inhabitant of the strengthened type, both contexts' well-formedness — is discharged inside. -/
theorem TrProj.weak'_inv_of_constRigid [VEnv.Params]
    (HT : VEnv.Params.env.TypingStrengthening VEnv.Params.univs)
    (HC : VEnv.ConstRigid) (HB : ConstAppInvStmt VEnv.Params.env VEnv.Params.univs)
    {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (hΓ' : OnCtx Γ' (VEnv.Params.env.IsType VEnv.Params.univs))
    (W : Ctx.Lift' l Γ Γ')
    (H : TrProj VEnv.Params.env VEnv.Params.univs Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj VEnv.Params.env VEnv.Params.univs Γ s i e e'' :=
  TrProj.weak'_inv_of_structStrengthen VEnv.Params.henv
    (constAppTypeStrengthenStruct_of_typing_headRF VEnv.Params.henv HT
      (constAppDefeqStrengthenRF_of_constRigid HC HB))
    hΓ' (HT.onCtx_weak'_inv VEnv.Params.henv W hΓ') W H

end Lean4Lean
