import Lean4Lean.Theory.Inductive.IotaWit

/-!
# `IotaHargs` at the block's **own** member — the sibling producer of `IotaHargsGen` §4

`Theory/Inductive/IotaHargsGen.lean` §4 (`VIndRestore.iotaHargs_of_heads`, arity 38) produces
`R.IotaHargs D σ e j C` from `htele`, two `hargs` bundles, `hidx` and `hres`.  It carries
`hK : T.name ∈ K`, inherited from `substC_tyApp'_defeq_tyAppR'_comp` /
`substC_ctorApp'_defeq_ctorAppR_comp`, where `hK` is load-bearing: it is what makes `substC`
fire on the head constant.  `Theory/Inductive/IotaWit.lean` §1 measures that at the member the
step *declares* `hK` is **false** (`mp_own_not_mem_K`, `ntree_own_not_mem_K`), so §4 covers 1 of
`MP`'s 2 ι-rules and 2 of `NTree`'s 3 and **is not by itself a producer of `hdata` for a block**.

This file is the missing sibling: `T.name ∉ K`.  The measured lead was that at those rules the
type head does not move (`IotaWit.lean` §1a), so a producer off `VIndRestore.OwnId.tyAppR'_eq`
should be available.  It is, and it is *cheaper than the lead suggested*: at the own member both
conversions of `IotaHargs` degenerate to **typings**, and both of those typings are D-series facts
moved across `σ` by `CSubst.WFD`.  So the own-member producer's only residual is `htele`.

Layout:

* §1 — the two own-member head equations, **without** `hp : D.params = []`.  `NestedRules.lean`
  §7.4's `substC_tyApp'_eq_tyAppR'` / `substC_ctorApp'_eq_ctorAppR` prove the same equations
  under `hp` + `hcl0`, and both hypotheses are used **only in their `T.name ∈ K` branch**.  So
  the own-member half was already there, welded to two hypotheses it does not need.
* §2 — the three D-series inputs at the ι-rule's context: the major premise's typing, its type's
  typing, and the index `HasArgs`.  All three are the internal `have`s of
  `VInductDecl'.iotaLhs_hasType` (`Lemmas.lean` §E5), which are not exported.
* §3 — the producer, `VIndRestore.iotaHargs_of_own`.  Residual: `htele`.
* §4 — instantiated at **both** parameterised blocks' own rules, and joint inhabitation.
* §5 — `hdata` for a whole block: §3 for the own rules, `IotaHargsGen` §4 for the companions.
* §6 — what is *not* closed, and the honest grading.

**This is not the flip.**  (C) is not discharged in general: §3 still takes `htele`, and §5's
`hdata` at a whole block is stated *conditionally on* the per-rule `htele`s.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)

/-! ## §1 The own-member head equations, without `D.params = []`

`VIndRestore.substC_tyApp'_eq_tyAppR'` (`NestedRules.lean:415`) proves
`(D.tyApp' j k args).substC σ = D.tyAppR' R j k (args.map (substC · σ))` from
`hp : D.params = []`, `hown`, `hat` and `hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0`.  Its proof
is a `by_cases hK : T.name ∈ K`, and **only the `∈ K` branch uses `hp` or `hcl0`**: `hp` to strip
`tyVal`'s `mkLams D.params`, `hcl0` to kill the `liftN` in `tyAppH`.  The `∉ K` branch is four
rewrites off `hat.tyNone` and `hown.tyAppR'_eq`.

The parameterised witnesses **refute** both discarded hypotheses (`ntree_params_ne_nil` below,
and `InductiveDeclExamples.ntree_not_tyArgs_closed0` for `hcl0`), so splitting the branch out is
what makes the own member reachable at `D.np > 0` at all.  This is the same class of finding as
the `substC_tyAppR` trim named in `docs/handoff-hyptrim.md`: a hypothesis carried past the branch
that needs it, invisible in the source because the section's `include` suppresses
`linter.unusedSectionVars`. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}
variable {j : Nat} {T : VIndType} {C : VIndCtor}

/-- **The primed type head at a member off `K`: the substitution is the identity on it.**
No `D.params = []`, no closedness of `R.tyArgs`. -/
theorem substC_tyApp'_eq_tyAppR'_own (hown : R.OwnId D K) (hat : R.SubstAt D K σ)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (k : Nat) (args : List VExpr) :
    (D.tyApp' j k args).substC σ = D.tyAppR' R j k (args.map (VExpr.substC · σ)) := by
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    VExpr.substC_const_none (by rw [hg]; exact hat.tyNone j T hT hK),
    hown.tyAppR'_eq hT hK, VInductDecl'.tyApp']

/-- …and the constructor head likewise. -/
theorem substC_ctorApp'_eq_ctorAppR_own (hown : R.OwnId D K) (hat : R.SubstAt D K σ)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (hC : C ∈ T.ctors)
    (k : Nat) (args : List VExpr) :
    (D.ctorApp' C k args).substC σ = D.ctorAppR R j C k (args.map (VExpr.substC · σ)) := by
  rw [VInductDecl'.ctorApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    VExpr.substC_const_none (hat.ctorNone j T hT hK C hC),
    hown.ctorAppR_eq hT hK hC, VInductDecl'.ctorApp']

end
end VIndRestore

/-! ## §2 The three D-series inputs at the ι-rule's context

`VInductDecl'.iotaLhs_hasType` (`Lemmas.lean` §E5) builds exactly the three facts §3 needs, as
internal `have`s: `hidx` (the index spine), `hz` (the major premise) and — implicitly, inside
`recApp_hasType` — the major premise's *type* being a type.  None of the three is exported, so
they are re-derived here from the same ingredients (`VIndCtor.WF.args_ty`, `.result`,
`ctorApp'_hasType`).  Everything in this section lives in the **unsubstituted** environment; §3
moves all three across `σ` with `CSubst.WFD`.

Nothing here mentions `R`, `K` or `σ`: the own-member restriction plays no part in §2. -/

namespace VInductDecl'
section
variable {env : VEnv} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}

/-- `atRecCtx` on a two-block reversed context, spelled as two reversed `atRecTele`s. -/
theorem atRecCtx_fields_params (D : VInductDecl') (C : VIndCtor) :
    D.atRecCtx ((C.fields.map (·.type)).reverse ++ D.params.reverse)
      = (D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse := by
  rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse]; rfl

/-- **The weakening into the ι-rule's context.**  The constructor's own context is
`fields.reverse ++ params.reverse`; the ι-rule's inserts the motive and minor blocks between
them, i.e. `D.nm + D.nmin` binders at cut `C.fields.length`. -/
theorem iotaCtx_liftN (D : VInductDecl') (C : VIndCtor) :
    Ctx.LiftN (D.nm + D.nmin) C.fields.length
      ((D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse)
      ((D.iotaCtx C).reverse) := by
  have hMD : (D.minors.reverse ++ D.motives.reverse).length = D.nm + D.nmin := by
    rw [List.length_append, List.length_reverse, List.length_reverse,
      VInductDecl'.length_minors, VInductDecl'.length_motives]; omega
  have WD : Ctx.LiftN (D.nm + D.nmin) 0 (D.atRecTele D.params).reverse
      (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) :=
    .zero (D.minors.reverse ++ D.motives.reverse) hMD
  have h := Ctx.LiftN.tele (As := D.atRecTele (C.fields.map (·.type))) WD
  rw [show (0:Nat) + (D.atRecTele (C.fields.map (·.type))).length = C.fields.length from by
    rw [Nat.zero_add, VInductDecl'.length_atRecTele, List.length_map]] at h
  rw [D.iotaCtx_reverse' C]
  exact h

/-- **`iotaLhs_hasType`'s `hz`, exported.**  The major premise — the constructor at the parameter
and field variables — has the canonical result type at the ι-rule's numbering. -/
theorem iotaMajor_hasType (hI : D.IotaCtx env) (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hCall : (j, C) ∈ D.ctorsAll) :
    env.HasType D.recUvars ((D.iotaCtx C).reverse)
      (D.ctorApp' C (C.fields.length + (D.nm + D.nmin)) (bvars 0 C.fields.length))
      (D.tyApp' j (D.nm + D.nmin + C.fields.length)
        (C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)) := by
  have hR := hI.toRecCtx
  have hMD : (D.minors.reverse ++ D.motives.reverse).length = D.nm + D.nmin := by
    rw [List.length_append, List.length_reverse, List.length_reverse,
      VInductDecl'.length_minors, VInductDecl'.length_motives]; omega
  have h := VInductDecl'.ctorApp'_hasType hR hT hC hCall (m := D.nm + D.nmin)
    (Δ := D.minors.reverse ++ D.motives.reverse) hMD (VInductDecl'.onCtxMinors hR)
  rw [VIndCtor.canonResult, D.liftN_atRec_tyApp (Nat.le_refl _) rfl,
    ← D.iotaCtx_reverse' C] at h
  exact h

/-- **The major premise's type is a type**, at the ι-rule's context: `VIndCtor.WF.result` under
`atRec`, weakened by §2's `iotaCtx_liftN`. -/
theorem iotaMajorType_hasType (hI : D.IotaCtx env) (hT : D.types[j]? = some T)
    (hC : C ∈ T.ctors) :
    env.HasType D.recUvars ((D.iotaCtx C).reverse)
      (D.tyApp' j (D.nm + D.nmin + C.fields.length)
        (C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length))
      (.sort (D.lvl.inst D.selfLvls)) := by
  have hR := hI.toRecCtx
  have h0 := D.atRec_hasType ((hR.ctors j T hT C hC).result)
  rw [D.atRecCtx_fields_params C] at h0
  have h := h0.weakN hR.ordered (D.iotaCtx_liftN C)
  rwa [VIndCtor.canonResult, D.liftN_atRec_tyApp (Nat.le_refl _) rfl] at h

/-- **`iotaLhs_hasType`'s `hidx`, exported — in the *motive's* telescope shape.**  The index
spine, typed against `T.indices` as the motive block presents it: `liftTele j` for the motives
below `j`, then `liftTele (k+1)` for the entries between the motive and the ι-context's top.  This
is the shape `VIndRestore.iotaHargs_hfunM` consumes; `iotaLhs_hasType` states the same fact with
the two lifts already fused. -/
theorem iotaIdx_hasArgs (hI : D.IotaCtx env) (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hj : j < D.nm) :
    env.HasArgs D.recUvars ((D.iotaCtx C).reverse)
      (liftTele (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)
        (liftTele j (D.atRecTele T.indices) 0) 0)
      (C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length) := by
  have hR := hI.toRecCtx
  have h0 := D.atRec_hasArgs ((hR.ctors j T hT C hC).args_ty)
  rw [D.atRecCtx_fields_params C, VInductDecl'.atRec_liftTele] at h0
  have h := VEnv.HasArgs.weakN hR.ordered (D.iotaCtx_liftN C) h0
  rw [VExpr.liftTele_liftTele (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero _).symm),
    List.map_map] at h
  rw [VExpr.liftTele_liftTele (Nat.le_refl 0) (Nat.zero_le _),
    show j + (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)
      = C.fields.length + (D.nm + D.nmin) from by omega]
  exact h

end
end VInductDecl'

/-! ## §3 The producer at `T.name ∉ K`

`IotaHargs` is `htele ∧ ∃ A₀ v, hfunM ∧ hconv ∧ hmaj`.  At the own member:

* `hmaj`'s two sides are the **same term** — `substC_ctorAppR` (§7.4) on the right and §1's
  `substC_ctorApp'_eq_ctorAppR_own` on the left land on `D.ctorAppR R j C k (bvars 0 nf)` — so
  `hmaj` degenerates from a conversion to the major premise's *typing*;
* choosing `A₀` to be that typing's type makes `hconv` degenerate to `IsType` of it.

Both typings are §2's, moved across `σ`.  So the *entire* residual is `htele`: no `hargs` bundle,
no `hres`, no `hpi`/`hsort` shape identity, no bound on `D.np`.

Compare `IotaHargsGen`'s §4 (arity 38, eleven hypotheses `docs/handoff-iotahargs.md` §5d grades
"inhabitation unknown"): here there is one. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {env e : VEnv}
variable {j : Nat} {T : VIndType} {C : VIndCtor}

/-- **`R.IotaHargs D σ e j C` at the block's own member, from `htele` and nothing else.**

The environment inputs (`hI`, `hσD`) are the ones `VEnv.iotaRulesRS_wf_of_hargsD` already
carries, so at the call site they are free.  `hown`/`hat`/`hfr` are the restoration's standing
interface, and `hK : T.name ∉ K` is what `IotaHargsGen` §4 cannot have.

**This is a reduction, not a discharge**: `htele` remains, and `htele` is *not* free here — the
own member's constructors have fields mentioning the companion types, which is why
`ntree_iota_components_ne` reports all nine components of `ntreeAux`'s three rules as moving. -/
theorem iotaHargs_of_own (hown : R.OwnId D K) (hat : R.SubstAt D K σ) (hfr : R.SubstFree D σ)
    (hσ : σ.Closed) (hσD : σ.WFD env e D.recUvars) (hI : D.IotaCtx env)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (hC : C ∈ T.ctors)
    (hCall : (j, C) ∈ D.ctorsAll) (hj : j < D.nm)
    (htele : e.TeleDefEq D.recUvars [] ((D.iotaCtx C).map (VExpr.substC · σ))
      ((D.iotaCtxR R C).map (VExpr.substC · σ))) :
    R.IotaHargs D σ e j C := by
  have hΓ : ((D.iotaCtx C).reverse).map (VExpr.substC · σ)
      = ((D.iotaCtx C).map (VExpr.substC · σ)).reverse := List.map_reverse ..
  -- the index spine, moved across σ
  have hidx := (D.iotaIdx_hasArgs hI hT hC hj).substCD hσD
  rw [hΓ, VExpr.map_substC_liftTele hσ] at hidx
  -- the major premise and its type, moved across σ
  have hmaj := (D.iotaMajor_hasType hI hT hC hCall).substCD hσD
  have hty := (D.iotaMajorType_hasType hI hT hC).substCD hσD
  rw [hΓ] at hmaj hty
  -- the two sides of `hmaj` are the same term
  have heq : (D.ctorApp' C (C.fields.length + (D.nm + D.nmin)) (bvars 0 C.fields.length)).substC σ
      = (D.ctorAppR R j C (C.fields.length + (D.nm + D.nmin))
          (bvars 0 C.fields.length)).substC σ := by
    rw [substC_ctorApp'_eq_ctorAppR_own hown hat hT hK hC,
      substC_ctorAppR hfr hT hC, VExpr.map_substC_bvars]
  refine ⟨htele, _, D.lvl.inst D.selfLvls,
    iotaHargs_hfunM hσ hT hj ((hI.toRecCtx.ctors j T hT C hC).args_len) hidx, hty, ?_⟩
  rw [← heq]
  exact hmaj

end
end VIndRestore

/-! ## §4 §3 instantiated at the own rule of **both** parameterised blocks

`docs/vacuity-ledger.md` §0: a clean axiom line is not content, and a per-hypothesis check is not
a joint one.  §3 has one non-environment hypothesis, so joint satisfiability is cheap to state —
but the point of instantiating is not the hypothesis set, it is that §3's *conclusion* is the one
the hand proofs needed.  Both blocks' own rules already have hand proofs (`rIotaRest_node` at
`ntreeAux`, `mpIotaHargs_obj` at `mpAux mpAuxNodeB`), so if §3's `A₀` or numbering were wrong the
declarations below would not typecheck. -/

namespace InductiveDeclExamples

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hE₃ : E₂.addIndRecs ntreeAux = some E₃)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)
variable (hF₃ : F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **§3 at `ntreeAux`'s own ι-rule** (`j = 0`, `C = NTree.node`) — the rule `IotaHargsGen` §4
cannot reach.  `htele` is §J's `rIotaTele_node`; everything else is discharged. -/
theorem ntree_iotaHargs_node_own :
    ntreeRestore.IotaHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₃ 0 ntreeNode :=
  VIndRestore.iotaHargs_of_own (K := ntreeK) (T := ntreeAux.types.getD 0 default)
    ntreeRestore_ownId ntreeRestore_domSep.substAt ntreeRestore_substFree ntree_csubst_closed
    (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (ntreeAux_WF'.iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃)
    rfl ntree_own_not_mem_K (List.Mem.head _) (by rw [ntreeAux_ctorsAll_eq]; simp) (by decide)
    (rIotaTele_node (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃))

end

/-- **ARITY 0**: §3's hypothesis set is jointly inhabited at `ntreeAux`'s own rule. -/
theorem ntree_iotaHargs_node_own_inhabited :
    ∃ (E₃ F₃ : VEnv), (ntreeRestore.csubst ntreeAux ntreeK).WFD E₃ F₃ 2 ∧
      ntreeRestore.IotaHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₃ 0 ntreeNode := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  exact ⟨E₃, F₃, ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃,
    ntree_iotaHargs_node_own h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃⟩

end InductiveDeclExamples

/-! ### §4a …and at the own rule of the NON-canonical parameterised redex block

`MRedex.MPWit.mpAux mpAuxNodeB`'s own rule is `j = 0`, `C = mpObj`.  `htele` is §17's
`mpIotaTele_obj`; the environment inputs are §18's. -/

namespace MRedex.MPWit

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' MRWit.mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hE₃ : E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)
variable (hF₃ : F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃)
variable (hD : F₃.constants ``MRWit.MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F₃.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F₃.constants ``MRWit.MDep.node = some ⟨0, MRWit.mrNode.type MRWit.mrDepDecl 0⟩)
variable (hOb : F₃.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ hD hP hNd hOb in
/-- **§3 at `MP`'s own ι-rule** (`j = 0`, `C = mpObj`) — the rule `IotaHargsGen` §4 cannot reach,
at the non-canonical block. -/
theorem mp_iotaHargs_obj_own :
    mpRestore.IotaHargs (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) F₃ 0 mpObj :=
  VIndRestore.iotaHargs_of_own (K := mpK) (T := (mpAux mpAuxNodeB).types.getD 0 default)
    mpRestore_ownId mpRestore_domSep.substAt mpRestore_substFree mp_csubst_closed
    (mp_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃)
    rfl mp_own_not_mem_K (List.Mem.head _) (by rw [mpAuxB_ctorsAll_eq]; simp) (by decide)
    (mpIotaTele_obj hD hP hNd hOb)

end
end MRedex.MPWit

/-! ## §5 `hdata` for a WHOLE block: the own rules are free, the companions are not

§3 and `IotaHargsGen` §4 partition the ι-rules of a block by `T.name ∈ K`, so together they are a
producer of `hdata` — the input `VEnv.iotaRulesRS_wf_of_hargsD` wants — for *every* rule.  §5.1
states that as one lemma: after the per-rule `htele`s, the residual of `hdata` is `IotaHargs` at
the **companion** rules only.  This is the statement `IotaHargsGen` §4 could not make.

`docs/handoff-iotahargs.md` §6's residual table for (C) is therefore over-stated for a block whose
own member has constructors: the two `hargs` bundles, `hres`, `hpiT`/`hpiC`/`hsortT` and `hidx` are
needed **only at the rules of companion members**. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {env e : VEnv}

/-- **`hdata` at a whole block, from the per-rule `htele`s and the companion rules alone.**

The own member's rules are discharged by §3; `hcomp` is asked for only where `T.name ∈ K`.  At a
block whose own member has constructors this is strictly weaker than `hdata`: at `ntreeAux` it
drops 1 of 3 rules, at `MRedex.MPWit.mpAux` 1 of 2. -/
theorem hdata_of_companions (hown : R.OwnId D K) (hat : R.SubstAt D K σ) (hfr : R.SubstFree D σ)
    (hσ : σ.Closed) (hσD : σ.WFD env e D.recUvars) (hI : D.IotaCtx env)
    (htele : ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) →
      e.TeleDefEq D.recUvars [] ((D.iotaCtx C).map (VExpr.substC · σ))
        ((D.iotaCtxR R C).map (VExpr.substC · σ)))
    (hcomp : ∀ (q j : Nat) (C : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (j, C) →
      D.types[j]? = some T → T.name ∈ K → R.IotaHargs D σ e j C) :
    ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) → R.IotaHargs D σ e j C := by
  intro q j C hqC
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hqC)
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  by_cases hK : T.name ∈ K
  · exact hcomp q j C T hqC hT hK
  · exact iotaHargs_of_own hown hat hfr hσ hσD hI hT hK hC
      (List.mem_of_getElem? hqC) hj (htele q j C hqC)

end
end VIndRestore

/-! ### §5a `hdata` at `MP` with EVERY rule from a general producer

`IotaWit.lean` §3's `mp_hdata_gen` routes the companion rule through `IotaHargsGen` §4 and the own
rule through the **hand** witness `mpIotaHargs_obj`.  Here both come from general producers, so no
hand ι-witness is used at all. -/

namespace MRedex.MPWit

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' MRWit.mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hE₃ : E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)
variable (hF₃ : F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃)
variable (hD : F₃.constants ``MRWit.MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F₃.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F₃.constants ``MRWit.MDep.node = some ⟨0, MRWit.mrNode.type MRWit.mrDepDecl 0⟩)
variable (hOb : F₃.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ hD hP hNd hOb in
/-- **`hdata` at `MP`, both rules through general producers** — §3 for `MP.obj`,
`IotaHargsGen` §4 for the companion. -/
theorem mp_hdata_own_gen (henv : F₃.Ordered) :
    ∀ (q j : Nat) (C : VIndCtor), (mpAux mpAuxNodeB).ctorsAll[q]? = some (j, C) →
      mpRestore.IotaHargs (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) F₃ j C := by
  refine VIndRestore.hdata_of_companions mpRestore_ownId mpRestore_domSep.substAt
    mpRestore_substFree mp_csubst_closed (mp_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃) ?_ ?_
  · intro q j C hq
    rw [mpAuxB_ctorsAll_eq] at hq
    match q with
    | 0 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact mpIotaTele_obj hD hP hNd hOb
    | 1 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact mpIotaTele_node hD hP hNd hOb
    | (n+2) => simp at hq
  · intro q j C T hq hT hK
    rw [mpAuxB_ctorsAll_eq] at hq
    match q with
    | 0 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      refine absurd hK ?_
      rw [show T = (mpAux mpAuxNodeB).types.getD 0 default from by
        rw [List.getD_eq_getElem?_getD, hT]; rfl]
      exact mp_own_not_mem_K
    | 1 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact mp_iotaHargs_node_gen hD hP hNd hOb henv
    | (n+2) => simp at hq

end

/-- **ARITY 0 — obligation (C) at `MP` with no hand ι-witness anywhere.**  `mp_iotaRulesRS_wf_gen`
(`IotaWit.lean` §5) still used `mpIotaHargs_obj` for the own rule; this does not. -/
theorem mp_iotaRulesRS_wf_own_gen :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv),
      VEnv.empty.addInduct' MRWit.mrDepDecl = some env₁ ∧
      env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃ ∧
      env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ ∧
      F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ ∧
      F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃ ∧
      (∀ df ∈ (mpAux mpAuxNodeB).iotaRulesRS mpRestore mpK, VDefEq.WF F₃ df) := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := mp_stage₃_exists
  refine ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃, ?_⟩
  exact VEnv.iotaRulesRS_wf_of_hargsD mpRestore_ownId mpRestore_domSep.substAt
    mpRestore_substFree mp_csubst_closed
    (mp_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃)
    (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃) mpAuxB_recArg_lt
    (mp_hdata_own_gen h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃
      (mpF₃_mdep h hF₁ hF₂ hF₃) (mpF₃_mp hF₁ hF₂ hF₃) (mpF₃_mdepNode h hF₁ hF₂ hF₃)
      (mpF₃_obj hF₂ hF₃) (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃))

end MRedex.MPWit

/-! ### §5b …and at `ntreeAux`, where the companions still need hand witnesses

At the canonical block §5.1 drops the own rule (`NTree.node`) from `hdata`'s obligation, leaving
`nlistNil` and `nlistCons`.  Those two are `IotaHargsGen` §4's territory, and **§4 has never been
instantiated at `ntreeAux`** (`docs/handoff-iotahargs.md` §8 item 2 is exactly that job, still
open), so they are taken from §T16.15's hand triples here.  So at `ntreeAux` `hdata` does *not* yet
follow from the two general producers alone; at `MP` (§5a) it does. -/

namespace InductiveDeclExamples

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hE₃ : E₂.addIndRecs ntreeAux = some E₃)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)
variable (hF₃ : F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **`hdata` at `ntreeAux` with the own rule from §3** and only the two companion rules assumed.
Compare `ntreeAux_hdata_of_rest`, which assumes all three. -/
theorem ntree_hdata_own_gen (h1 : rIotaRest F₃ 1 nlistNil) (h2 : rIotaRest F₃ 1 nlistCons) :
    ∀ (q j : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (j, C) →
      ntreeRestore.IotaHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₃ j C := by
  refine VIndRestore.hdata_of_companions ntreeRestore_ownId ntreeRestore_domSep.substAt
    ntreeRestore_substFree ntree_csubst_closed (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (ntreeAux_WF'.iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃) ?_ ?_
  · intro q j C hq
    rw [ntreeAux_ctorsAll_eq] at hq
    match q with
    | 0 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact rIotaTele_node (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
    | 1 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact rIotaTele_nil (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
    | 2 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact rIotaTele_cons (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
    | (n+3) => simp at hq
  · intro q j C T hq hT hK
    rw [ntreeAux_ctorsAll_eq] at hq
    match q with
    | 0 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      refine absurd hK ?_
      rw [show T = ntreeAux.types.getD 0 default from by
        rw [List.getD_eq_getElem?_getD, hT]; rfl]
      exact ntree_own_not_mem_K
    | 1 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact ⟨rIotaTele_nil (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃), h1⟩
    | 2 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact ⟨rIotaTele_cons (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃), h2⟩
    | (n+3) => simp at hq

end

/-- **ARITY 0 — obligation (C) at `ntreeAux` with the own rule from §3.**  The two companion
triples are still `rIotaRest_nil`/`_cons`; `rIotaRest_node` is no longer used. -/
theorem ntree_iotaRulesRS_wf_own_gen :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      E₂.addIndRecs ntreeAux = some E₃ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃ ∧
      ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  refine ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃, ?_⟩
  exact ntreeAux_obligationC_of_hdata h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃
    (ntree_hdata_own_gen h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃
      (rIotaRest_nil (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃))
      (rIotaRest_cons (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_cons h hF₁ hF₂ hF₃)))

end InductiveDeclExamples

/-! ## §6 What is measured, stated apart from hole-freeness

`docs/vacuity-ledger.md` §0: the axiom lines of §7 say only that nothing is missing.  These are
the content checks, and none of them is an instance of §1, §3 or §5.

**The central measurement is already in the tree, and this is the connection nobody had made.**
`InductiveDeclExamples.rMaj_node_eq` (`Theory/Typing/ConstSubstNested.lean:3028`, `decide`) and
`MRedex.MPWit.mpMaj_obj_eq` (`Theory/Inductive/ParamRedex.lean:2044`, `decide`) say that at the own
member the substituted `ctorApp'` and the substituted `ctorAppR` are the **same term**, and
`rMaj_nil_ne` / `rMaj_cons_ne` / `mpMaj_node_ne` say they are not at the companions.  Those four
are *exactly* `IotaHargs`' `hmaj` at those rules — which is why §3 needs no conversion and why
`IotaHargsGen` §4 is not redundant.  `docs/handoff-iotahargs.md` §1 cited `rMaj_node_eq` only as
"a `rfl` discount applies to one of route 1's nine"; the discount is the whole own-member rule.

I elaborated all four statements again here before deleting them as duplicates — `mpMaj_obj_eq`
already has a second copy in the tree (`mpMaj_obj_eq'`, `ParamRedex.lean:2711`), and a third was
not worth adding. -/

namespace InductiveDeclExamples

/-- §1's dropped `hp : D.params = []` is **refuted** at the canonical block, so splitting the
`∉ K` branch out of `substC_tyApp'_eq_tyAppR'` is what makes the own member reachable at all —
not a tidying. -/
theorem ntree_params_ne_nil : ntreeAux.params ≠ [] := by decide

/-- The own member **has** constructors, so §5.1 is a strict weakening of `hdata` rather than a
restatement: it drops 1 of `ntreeAux`'s 3 rules. -/
theorem ntree_own_ctors_ne_nil : (ntreeAux.types.getD 0 default).ctors ≠ [] := by decide

/-- …and the own rule is not free for other reasons: its ι-context really moves under
restoration, which is why §3 still takes `htele`.  (Quoted from §I; re-stated as the premise §5b
relies on.) -/
theorem ntree_own_htele_nontrivial :
    (ntreeAux.iotaCtx ntreeNode).map (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
      ≠ (ntreeAux.iotaCtxR ntreeRestore ntreeNode).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK)) :=
  rIotaCtx_node_ne

end InductiveDeclExamples

namespace MRedex.MPWit

theorem mp_params_ne_nil : (mpAux mpAuxNodeB).params ≠ [] := by decide

theorem mp_own_ctors_ne_nil : ((mpAux mpAuxNodeB).types.getD 0 default).ctors ≠ [] := by decide

theorem mp_own_htele_nontrivial :
    ((mpAux mpAuxNodeB).iotaCtx mpObj).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      ≠ ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpObj).map
          (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) :=
  mpIotaCtx_obj_ne

end MRedex.MPWit

/-! ## §7 Axiom audit

**Hole-freeness only** (`docs/vacuity-ledger.md` §0).  §6 is the content; §4a/§5a/§5b are the
joint-inhabitation certificates; no line below is either. -/

#print axioms Lean4Lean.VIndRestore.substC_tyApp'_eq_tyAppR'_own
#print axioms Lean4Lean.VIndRestore.substC_ctorApp'_eq_ctorAppR_own
#print axioms Lean4Lean.VInductDecl'.atRecCtx_fields_params
#print axioms Lean4Lean.VInductDecl'.iotaCtx_liftN
#print axioms Lean4Lean.VInductDecl'.iotaMajor_hasType
#print axioms Lean4Lean.VInductDecl'.iotaMajorType_hasType
#print axioms Lean4Lean.VInductDecl'.iotaIdx_hasArgs
#print axioms Lean4Lean.VIndRestore.iotaHargs_of_own
#print axioms Lean4Lean.VIndRestore.hdata_of_companions
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iotaHargs_node_own
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iotaHargs_node_own_inhabited
#print axioms Lean4Lean.MRedex.MPWit.mp_iotaHargs_obj_own
#print axioms Lean4Lean.MRedex.MPWit.mp_hdata_own_gen
#print axioms Lean4Lean.MRedex.MPWit.mp_iotaRulesRS_wf_own_gen
#print axioms Lean4Lean.InductiveDeclExamples.ntree_hdata_own_gen
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iotaRulesRS_wf_own_gen
#print axioms Lean4Lean.InductiveDeclExamples.ntree_params_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_own_ctors_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_own_htele_nontrivial
#print axioms Lean4Lean.MRedex.MPWit.mp_params_ne_nil
#print axioms Lean4Lean.MRedex.MPWit.mp_own_ctors_ne_nil
#print axioms Lean4Lean.MRedex.MPWit.mp_own_htele_nontrivial


/-! ### §6a The shape check at the own index, and `hK`'s irremovability

`IotaHargsGen` §7's `ntree_A0_*_eq` checks §4's invented `A₀` against the hand proofs; its
`_node_eq` row sits at `j = 0`, the rule §4 cannot reach, so §7 bounded 2 rules and not 3.  The
own-index check belongs here instead — against **§3's** `A₀`, which is the *unrestored* head
substituted rather than `tyAppR'`.

Then the reason the split is forced: `hK` is not decoration on
`substC_tyApp'_comp` / `substC_ctorApp'_comp`.  Their conclusions are **false** at the own member —
measured, not read off the proof — so no amount of hypothesis-trimming turns `IotaHargsGen` §4 into
a producer for the own rule. -/

namespace InductiveDeclExamples

/-- **§3's `A₀` at `ntreeAux`'s own rule is `rIotaRest_node`'s.**

Not new content: it is `ntree_own_tyhead_fixed` (`IotaWit.lean` §1a) composed with
`ntree_A0_node_eq` (`IotaHargsGen` §7) — the two existing facts, at the same `k = 7` and the same
empty argument spine.  It is stated here because §3's `A₀` is the *unrestored* head substituted,
not `tyAppR'`, and that is the form the composition has to land in. -/
theorem ntree_own_A0_eq :
    (ntreeAux.tyApp' 0 (ntreeAux.nm + ntreeAux.nmin + ntreeNode.fields.length)
        (ntreeNode.args.map fun a =>
          (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) ntreeNode.fields.length)).substC
        (ntreeRestore.csubst ntreeAux ntreeK)
      = .app rNt (.bvar 7) := by decide

/-- **`substC_tyApp'_comp`'s conclusion is FALSE at the own member.**  Its right-hand side is a
saturated `D.np`-fold redex; at `j = 0` the substitution never fires, so the left-hand side is the
bare head.  Hence `hK : T.name ∈ K` cannot be dropped or weakened there. -/
theorem ntree_own_tyApp'_comp_false :
    (ntreeAux.tyApp' 0 7 []).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (VExpr.mkLams (ntreeAux.atRecTele ntreeAux.params)
          (ntreeAux.atRec (ntreeRestore.tyBody ntreeAux 0))).mkApp
          (VExpr.bvars 7 ntreeAux.np) := by decide

/-- …and the same for the constructor head. -/
theorem ntree_own_ctorApp'_comp_false :
    (ntreeAux.ctorApp' ntreeNode (ntreeNode.fields.length + (ntreeAux.nm + ntreeAux.nmin))
        (VExpr.bvars 0 ntreeNode.fields.length)).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (VExpr.mkLams (ntreeAux.atRecTele ntreeAux.params)
          (ntreeAux.atRec (ntreeRestore.ctorBody ntreeAux 0 ntreeNode))).mkApp
          (VExpr.bvars (ntreeNode.fields.length + (ntreeAux.nm + ntreeAux.nmin)) ntreeAux.np
            ++ (VExpr.bvars 0 ntreeNode.fields.length).map
              (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))) := by decide

end InductiveDeclExamples

namespace MRedex.MPWit

/-- **§3's `A₀` at `MP`'s own rule is `mpIotaHargs_obj`'s** (`.app mpNt (.bvar 5)`, chosen
independently by the hand proof in `ParamRedex.lean` §17.2). -/
theorem mp_own_A0_eq :
    ((mpAux mpAuxNodeB).tyApp' 0
        ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin + mpObj.fields.length)
        (mpObj.args.map fun a =>
          ((mpAux mpAuxNodeB).atRec a).liftN
            ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin) mpObj.fields.length)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = .app mpNt (.bvar 5) := by decide

/-- `substC_tyApp'_comp`'s conclusion is false at `MP`'s own member too. -/
theorem mp_own_tyApp'_comp_false :
    ((mpAux mpAuxNodeB).tyApp' 0 6 []).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      ≠ (VExpr.mkLams ((mpAux mpAuxNodeB).atRecTele (mpAux mpAuxNodeB).params)
          ((mpAux mpAuxNodeB).atRec (mpRestore.tyBody (mpAux mpAuxNodeB) 0))).mkApp
          (VExpr.bvars 6 (mpAux mpAuxNodeB).np) := by decide

end MRedex.MPWit

/-! ### §7a Axiom audit for §6a -/

#print axioms Lean4Lean.InductiveDeclExamples.ntree_own_A0_eq
#print axioms Lean4Lean.InductiveDeclExamples.ntree_own_tyApp'_comp_false
#print axioms Lean4Lean.InductiveDeclExamples.ntree_own_ctorApp'_comp_false
#print axioms Lean4Lean.MRedex.MPWit.mp_own_A0_eq
#print axioms Lean4Lean.MRedex.MPWit.mp_own_tyApp'_comp_false

end Lean4Lean
