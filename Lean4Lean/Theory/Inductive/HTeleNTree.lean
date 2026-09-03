import Lean4Lean.Theory.Inductive.OwnRule

/-!
# `IotaHargsGen` §4 at the CANONICAL block's companion rules — and obligation (C) there

`docs/handoff-iotahargs.md` §8 item 2 sets this job: *"a single simultaneous instance of §4 at
`ntreeAux`/`nlistNil`, to convert §5d's 'inhabitation unknown' into a certificate"*, and
`docs/handoff-ownrule.md` §5 records that **§4 has never been instantiated at `ntreeAux`**, which
is why `hdata` at the canonical block still needed the two hand triples `rIotaRest_nil` /
`rIotaRest_cons`.  This file does it at **both** companion rules, so (C) at the canonical block
now follows from general producers alone — `ntree_iotaRulesRS_wf_all_gen`, arity 0, with no hand
ι-witness anywhere.

Layout:

* §0/§0a/§0b — the two companion ι-contexts, their splits over the parameter block, the two
  presented heads (`List (NTree #0)` and `List.nil`/`List.cons` at it), and the two `hpiC`
  equations.  All `decide`/`rfl` on closed data.
* §1 — the typings: `hbodyT`, `hbodyC` at each rule, and the `nlistCons` ι-context as a context.
* §2 — `VIndRestore.IotaHeadHargs`: `IotaHargsGen` §4's twelve **non-`htele`** hypotheses,
  bundled, plus §4 restated over the bundle.  The point of the split is that `htele` can then be
  supplied from a different source — which is what `Theory/Inductive/HTeleGen.lean` §3 does.
* §2a — the bundle **inhabited** at both companion rules of the canonical block.
* §2b — `IotaHargs` at both, through §4.
* §3 — `hdata` at the whole block from general producers only (own rule from `OwnRule` §3,
  companions from §2b), then obligation (C), arity 0.
* §4 — what is degenerate here and what is not, stated apart from hole-freeness.
* §5 — axiom audit (hole-freeness only).

**This is not the flip**, and it is not a discharge of (C) in general: `htele` is still supplied
by the hand telescope proofs `rIotaTele_*` at this block, and §2a's bundle is a witness
inhabitation, not a general producer.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)

namespace InductiveDeclExamples

abbrev nD : VInductDecl' := ntreeAux
abbrev nS : CSubst := ntreeRestore.csubst ntreeAux ntreeK

/-! ## §0 The two companion ι-contexts, written out -/

theorem nIotaGamma_nil :
    ((nD.iotaCtx nlistNil).map (VExpr.substC · nS)).reverse = rTele.reverse := by
  rw [rIotaCtx_nil_eq]

theorem nIotaGamma_cons :
    ((nD.iotaCtx nlistCons).map (VExpr.substC · nS)).reverse
      = [.app rV (.bvar 6), .app rNt (.bvar 5)] ++ rTele.reverse := by decide

theorem nParams_rev : (nD.atRecTele nD.params).reverse = [rA0] := by decide

theorem n_pcl : VExpr.ClosedTele (nD.atRecTele nD.params) 0 := ⟨trivial, trivial⟩

theorem nIotaGamma_nil_split :
    ((nD.iotaCtx nlistNil).map (VExpr.substC · nS)).reverse
      = [rA5, rA4, rA3, rA2, rA1] ++ ((nD.atRecTele nD.params).reverse ++ []) := by decide

theorem nIotaGamma_cons_split :
    ((nD.iotaCtx nlistCons).map (VExpr.substC · nS)).reverse
      = [.app rV (.bvar 6), .app rNt (.bvar 5), rA5, rA4, rA3, rA2, rA1]
        ++ ((nD.atRecTele nD.params).reverse ++ []) := by decide

/-! ## §0a The presented companion heads -/

theorem n_atRec_tyBody_one : nD.atRec (ntreeRestore.tyBody nD 1) = .app rLt (.app rNt (.bvar 0)) :=
  rfl

theorem n_atRec_ctorBody_nil :
    nD.atRec (ntreeRestore.ctorBody nD 1 nlistNil)
      = .app (.const ``List.nil [.param 1]) (.app rNt (.bvar 0)) := rfl

theorem n_atRec_ctorBody_cons :
    nD.atRec (ntreeRestore.ctorBody nD 1 nlistCons)
      = .app (.const ``List.cons [.param 1]) (.app rNt (.bvar 0)) := rfl

/-! ## §0b The shape equations -/

theorem n_hpiC_nil :
    instAll (.app rLt (.app rNt (.bvar 0)))
      (bvars (nlistNil.fields.length + (nD.nm + nD.nmin)) nD.np)
      = mkPi [] (.app rLt (.app rNt (.bvar 5))) := by decide

theorem n_hpiC_cons :
    instAll (.forallE (.app rNt (.bvar 0))
        (.forallE (.app rLt (.app rNt (.bvar 1))) (.app rLt (.app rNt (.bvar 2)))))
      (bvars (nlistCons.fields.length + (nD.nm + nD.nmin)) nD.np)
      = mkPi [.app rNt (.bvar 7), .app rLt (.app rNt (.bvar 8))]
          (.app rLt (.app rNt (.bvar 9))) := by decide


/-! ## §1 The typings and the ι-contexts as contexts -/

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

include hL hN in
/-- `hbodyT` at either companion rule: the restored companion **type** head, typed at the
parameter block over any context. -/
theorem n_hbodyT {Γ : List VExpr} :
    F.HasType 2 (rA0 :: Γ) (.app rLt (.app rNt (.bvar 0))) (.sort (.succ (.param 1))) :=
  .appDF (rLC hL) (.appDF (rNC hN) (.bvar .zero))

include hN hnil in
/-- `hbodyC` at `nlistNil`: the restored `List.nil (NTree #0)`. -/
theorem n_hbodyC_nil {Γ : List VExpr} :
    F.HasType 2 (rA0 :: Γ) (.app (.const ``List.nil [.param 1]) (.app rNt (.bvar 0)))
      (.app rLt (.app rNt (.bvar 0))) :=
  .appDF (rNilC hnil) (.appDF (rNC hN) (.bvar .zero))

include hN hcons in
/-- `hbodyC` at `nlistCons`: the restored `List.cons (NTree #0)`. -/
theorem n_hbodyC_cons {Γ : List VExpr} :
    F.HasType 2 (rA0 :: Γ) (.app (.const ``List.cons [.param 1]) (.app rNt (.bvar 0)))
      (.forallE (.app rNt (.bvar 0))
        (.forallE (.app rLt (.app rNt (.bvar 1))) (.app rLt (.app rNt (.bvar 2))))) :=
  .appDF (rConsC hcons) (.appDF (rNC hN) (.bvar .zero))

include hL hN hnil hcons hnode in
/-- The `nlistCons` ι-context is a context: `rOnCtx` plus the constructor's own two fields. -/
theorem nOnCtxIotaCons :
    OnCtx (((nD.iotaCtx nlistCons).map (VExpr.substC · nS)).reverse) (F.IsType 2) := by
  rw [nIotaGamma_cons]
  refine ⟨⟨rOnCtx hL hN hnil hcons hnode, ?_⟩, ?_⟩
  · exact ⟨_, (.appDF (rNC hN) (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))⟩
  · exact ⟨_, (rbetaL hL hN (k := 6)
      (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))).hasType.1⟩

end

/-! ## §2 `IotaHeadHargs`: §4's residual with `htele` taken out -/

end InductiveDeclExamples

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {j : Nat} {T : VIndType} {C : VIndCtor}

/-- **The twelve non-`htele` hypotheses of `IotaHargsGen` §4, bundled.**  Copied verbatim from
`VIndRestore.iotaHargs_of_heads`'s signature, with the six shape witnesses existentially
quantified.  Its point is to let `htele` be supplied from a *different* source than the head
data — which is what `HTeleGen.lean` §3 does. -/
def IotaHeadHargs (R : VIndRestore) (D : VInductDecl') (σ : CSubst) (e : VEnv)
    (j : Nat) (T : VIndType) (C : VIndCtor) : Prop :=
  ∃ (AsT AsC : List VExpr) (BT BT' BC BC' : VExpr) (v : VLevel),
    e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (liftTele (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)
        ((liftTele j (D.atRecTele T.indices) 0).map (VExpr.substC · σ)) 0)
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)) ∧
    OnCtx ((D.atRecTele D.params).reverse ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (e.IsType D.recUvars) ∧
    e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (D.atRecTele D.params) (bvars (D.nm + D.nmin + C.fields.length) D.np) ∧
    e.HasType D.recUvars ((D.atRecTele D.params).reverse
      ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse) (D.atRec (R.tyBody D j)) BT ∧
    instAll BT (bvars (D.nm + D.nmin + C.fields.length) D.np) = mkPi AsT BT' ∧
    e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse) AsT
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)) ∧
    instAll BT' ((C.args.map fun a =>
      (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)) = .sort v ∧
    e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (D.atRecTele D.params) (bvars (C.fields.length + (D.nm + D.nmin)) D.np) ∧
    e.HasType D.recUvars ((D.atRecTele D.params).reverse
      ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse) (D.atRec (R.ctorBody D j C)) BC ∧
    instAll BC (bvars (C.fields.length + (D.nm + D.nmin)) D.np) = mkPi AsC BC' ∧
    e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse) AsC
      (bvars 0 C.fields.length) ∧
    instAll BC' (bvars 0 C.fields.length)
      = D.tyAppR' R j (D.nm + D.nmin + C.fields.length)
          ((C.args.map fun a =>
            (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ))

/-- `IotaHargsGen` §4, restated over the bundle. -/
theorem iotaHargs_of_headHargs (hat : R.SubstAt D K σ) (hfr : R.SubstFree D σ) (hσ : σ.Closed)
    (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (henv : e.Ordered)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) (hC : C ∈ T.ctors) (hj : j < D.nm)
    (hlen : C.args.length = T.indices.length)
    (htele : e.TeleDefEq D.recUvars [] ((D.iotaCtx C).map (VExpr.substC · σ))
      ((D.iotaCtxR R C).map (VExpr.substC · σ)))
    (hb : R.IotaHeadHargs D σ e j T C) : R.IotaHargs D σ e j C := by
  obtain ⟨AsT, AsC, BT, BT', BC, BC', v, hidx, hOnp, hbvT, hbodyT, hpiT, hAsT, hsortT,
    hbvC, hbodyC, hpiC, hAsC, hres⟩ := hb
  exact iotaHargs_of_heads (K := K) hat hfr hσ hcl henv hT hK hC hj hlen htele hidx hOnp
    hbvT hbodyT hpiT hAsT hsortT hbvC hbodyC hpiC hAsC hres

end
end VIndRestore

/-! ## §2a The bundle, INHABITED at the canonical block's two companion rules -/

namespace InductiveDeclExamples

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

include hL hN hnil hcons hnode in
/-- **`IotaHeadHargs` at `nlistNil`.**  `nf = 0`, so `AsT = AsC = []`; the only content is
`hbodyT`/`hbodyC` (`List (NTree #0)` and `List.nil (NTree #0)`) and the two `np = 1` parameter
lookups. -/
theorem n_headHargs_nil (henv : F.Ordered) :
    ntreeRestore.IotaHeadHargs nD nS F 1 (nD.types.getD 1 default) nlistNil := by
  refine ⟨[], [], .sort (.succ (.param 1)), .sort (.succ (.param 1)),
    .app rLt (.app rNt (.bvar 0)), .app rLt (.app rNt (.bvar 5)), .succ (.param 1),
    .nil, ?_, ?_, ?_, rfl, .nil, rfl, ?_, ?_, n_hpiC_nil, .nil, by decide⟩
  · rw [nParams_rev, nIotaGamma_nil]
    exact VEnv.onCtx_params_append henv n_pcl (by rw [nParams_rev]; exact ⟨trivial, rIsTypeA0⟩)
      (nIotaGamma_nil ▸ rOnCtx hL hN hnil hcons hnode)
  · rw [nIotaGamma_nil_split]; exact VIndRestore.hasArgs_params_bvars_ctx n_pcl rfl
  · rw [nParams_rev]; exact n_hbodyT hL hN
  · rw [nIotaGamma_nil_split]; exact VIndRestore.hasArgs_params_bvars_ctx n_pcl rfl
  · rw [nParams_rev]; exact n_hbodyC_nil hN hnil

include hL hN hnil hcons hnode in
/-- **`IotaHeadHargs` at `nlistCons`.**  `nf = 2`, so `hpiC` moves and `hAsC` types two
arguments — the second at a domain that needs a **β conversion**, which is the structural
feature `MRedex.MPWit`'s witness does not have. -/
theorem n_headHargs_cons (henv : F.Ordered) :
    ntreeRestore.IotaHeadHargs nD nS F 1 (nD.types.getD 1 default) nlistCons := by
  refine ⟨[], [.app rNt (.bvar 7), .app rLt (.app rNt (.bvar 8))],
    .sort (.succ (.param 1)), .sort (.succ (.param 1)),
    .forallE (.app rNt (.bvar 0))
      (.forallE (.app rLt (.app rNt (.bvar 1))) (.app rLt (.app rNt (.bvar 2)))),
    .app rLt (.app rNt (.bvar 9)), .succ (.param 1),
    .nil, ?_, ?_, ?_, rfl, .nil, rfl, ?_, ?_, n_hpiC_cons, ?_, by decide⟩
  · rw [nParams_rev]
    exact VEnv.onCtx_params_append henv n_pcl (by rw [nParams_rev]; exact ⟨trivial, rIsTypeA0⟩)
      (nOnCtxIotaCons hL hN hnil hcons hnode)
  · rw [nIotaGamma_cons_split]; exact VIndRestore.hasArgs_params_bvars_ctx n_pcl rfl
  · rw [nParams_rev]; exact n_hbodyT hL hN
  · rw [nIotaGamma_cons_split]; exact VIndRestore.hasArgs_params_bvars_ctx n_pcl rfl
  · rw [nParams_rev]; exact n_hbodyC_cons hN hcons
  · rw [nIotaGamma_cons]
    exact .cons (.bvar (.succ .zero))
      (.cons (.defeqDF (rbetaL hL hN (k := 7)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))  (.bvar .zero)) .nil)

/-! ## §2b …and `IotaHargs` at both, through `IotaHargsGen` §4 -/

include hL hN hnil hcons hnode in
/-- **`IotaHargsGen` §4 at the canonical block's `nlistNil` rule** — the job
`docs/handoff-iotahargs.md` §8 item 2 sets, and `docs/handoff-ownrule.md` §5 records as never
having been done. -/
theorem n_iotaHargs_nil_gen (henv : F.Ordered) :
    ntreeRestore.IotaHargs nD nS F 1 nlistNil :=
  VIndRestore.iotaHargs_of_headHargs (K := ntreeK) ntreeRestore_domSep.substAt
    ntreeRestore_substFree ntree_csubst_closed (ntree_tyArgs_closedN_np 1) henv rfl
    (by decide) (List.Mem.head _) (by decide) rfl
    (rIotaTele_nil hL hN hnil hcons hnode) (n_headHargs_nil hL hN hnil hcons hnode henv)

include hL hN hnil hcons hnode in
/-- …and at `nlistCons`. -/
theorem n_iotaHargs_cons_gen (henv : F.Ordered) :
    ntreeRestore.IotaHargs nD nS F 1 nlistCons :=
  VIndRestore.iotaHargs_of_headHargs (K := ntreeK) ntreeRestore_domSep.substAt
    ntreeRestore_substFree ntree_csubst_closed (ntree_tyArgs_closedN_np 1) henv rfl
    (by decide) (.tail _ (.head _)) (by decide) rfl
    (rIotaTele_cons hL hN hnil hcons hnode) (n_headHargs_cons hL hN hnil hcons hnode henv)

end

/-! ## §3 `hdata` at the CANONICAL block from general producers only, and (C) -/

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
/-- **`hdata` at `ntreeAux`, all three ι-rules through general producers**: `OwnRule` §3 for the
own rule, `IotaHargsGen` §4 for the two companions. -/
theorem n_hdata_all_gen :
    ∀ (q j : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (j, C) →
      ntreeRestore.IotaHargs ntreeAux nS F₃ j C := by
  refine VIndRestore.hdata_of_companions ntreeRestore_ownId ntreeRestore_domSep.substAt
    ntreeRestore_substFree ntree_csubst_closed (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    ((ntreeAux_WF h).iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃) ?_ ?_
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
      exact n_iotaHargs_nil_gen (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
        (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃)
    | 2 =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
      exact n_iotaHargs_cons_gen (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
        (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
        (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃)
    | (n+3) => simp at hq

end

/-- **ARITY 0 — obligation (C) at the CANONICAL block with no hand ι-witness anywhere.** -/
theorem ntree_iotaRulesRS_wf_all_gen :
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
    (n_hdata_all_gen h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)

/-! ## §4 What is degenerate here and what is not

`docs/vacuity-ledger.md` §0: the axiom lines of §5 are hole-freeness and nothing else.  The brief
warned that the `instAll` index window is empty at every pre-existing witness but one and told me
to **check rather than assume**; §4a checks it here, and §4b is what is *not* degenerate. -/

/-! ### §4a Re-measured, not cited: the index window at THIS block is empty -/

theorem n_companion_unindexed : (nD.types.getD 1 default).indices = [] := by decide

theorem n_nil_args_nil : nlistNil.args = [] := by decide

theorem n_cons_args_nil : nlistCons.args = [] := by decide

/-- So `hidx`, `hAsT`, `hpiT` and `hsortT` of §2a sit at the **empty** window: four of the twelve
slots are degenerate at this witness, exactly as at `MRedex.MPWit.mpAux`. -/
theorem n_window_empty :
    (nlistNil.args.map fun a =>
        (nD.atRec a).liftN (nD.nm + nD.nmin) nlistNil.fields.length).map (VExpr.substC · nS) = []
      ∧ (nlistCons.args.map fun a =>
        (nD.atRec a).liftN (nD.nm + nD.nmin) nlistCons.fields.length).map
          (VExpr.substC · nS) = [] := by decide

/-! ### §4b …and the eight that are not

`hbvT`/`hbvC` are real `np = 1` parameter lookups (`nD.np = 1`, so the spine is a singleton, not
`HasArgs.nil`); `hpiC`/`hres` move at `nlistCons`; and `hAsC` at `nlistCons` needs a **β
conversion**, which is the structural difference from `MRedex.MPWit`'s instance — there
(`mp_hAsC_second_is_redex`) the second `AsC` entry was *syntactically* the context entry, so the
`HasArgs` step was a bare `Lookup`; here it is not. -/

theorem n_np_pos : nD.np = 1 := by decide

theorem n_hbv_spine_ne_nil : bvars (nD.nm + nD.nmin + nlistNil.fields.length) nD.np ≠ [] := by
  decide

/-- `hpiC` at `nlistCons` is not an identity. -/
theorem n_hpiC_cons_moves :
    instAll (.forallE (.app rNt (.bvar 0))
        (.forallE (.app rLt (.app rNt (.bvar 1))) (.app rLt (.app rNt (.bvar 2)))))
      (bvars (nlistCons.fields.length + (nD.nm + nD.nmin)) nD.np)
      ≠ .forallE (.app rNt (.bvar 0))
        (.forallE (.app rLt (.app rNt (.bvar 1))) (.app rLt (.app rNt (.bvar 2)))) := by decide

/-- `hres` moves at `nlistCons` (index `9 ↦ 7`) and is the identity at `nlistNil` (`nf = 0`) —
the second is disclosed as degenerate, not claimed as content. -/
theorem n_hres_cons_moves : (VExpr.app rLt (.app rNt (.bvar 9))) ≠ .app rLt (.app rNt (.bvar 7)) := by
  decide

theorem n_hres_nil_identity :
    instAll (.app rLt (.app rNt (.bvar 5))) (bvars 0 nlistNil.fields.length)
      = .app rLt (.app rNt (.bvar 5)) := by decide

/-- **`hAsC`'s second argument needs a β step at `nlistCons`.**  The ι-context declares the field
at the *stored* type `rV #7`; §4's `AsC` presents it at the *restored* `List (NTree #7)`, and the
two are different terms — so the `HasArgs.cons` step is `.defeqDF (rbetaL …) (.bvar .zero)` and not
a bare lookup.  `MRedex.MPWit`'s witness did not exercise this. -/
theorem n_hAsC_needs_beta : (VExpr.app rV (.bvar 7)) ≠ .app rLt (.app rNt (.bvar 7)) := by decide

/-- **The two `hbody` slots that `docs/handoff-iotahargs.md` §6 calls "genuinely data … the
irreducible core" are discharged outright here**, and this is the honest reading: at this block the
restored companion heads are `List` and `List.nil`/`List.cons` from the *pre-existing* `listDecl`,
so their typings are two `constDF`s and an `appDF` each (§1).  "Irreducible" is a statement about
the general case; at every parameterised witness in the tree it is discharged. -/
theorem n_tyBody_is_stored_const :
    nD.atRec (ntreeRestore.tyBody nD 1) = .app (.const ``List [.param 1]) (.app rNt (.bvar 0)) :=
  rfl

/-! ## §5 Axiom audit — hole-freeness only -/

#print axioms Lean4Lean.InductiveDeclExamples.nIotaGamma_nil
#print axioms Lean4Lean.InductiveDeclExamples.nIotaGamma_cons
#print axioms Lean4Lean.InductiveDeclExamples.nParams_rev
#print axioms Lean4Lean.InductiveDeclExamples.nIotaGamma_nil_split
#print axioms Lean4Lean.InductiveDeclExamples.nIotaGamma_cons_split
#print axioms Lean4Lean.InductiveDeclExamples.n_hpiC_nil
#print axioms Lean4Lean.InductiveDeclExamples.n_hpiC_cons
#print axioms Lean4Lean.InductiveDeclExamples.n_hbodyT
#print axioms Lean4Lean.InductiveDeclExamples.n_hbodyC_nil
#print axioms Lean4Lean.InductiveDeclExamples.n_hbodyC_cons
#print axioms Lean4Lean.InductiveDeclExamples.nOnCtxIotaCons
#print axioms Lean4Lean.VIndRestore.iotaHargs_of_headHargs
#print axioms Lean4Lean.InductiveDeclExamples.n_headHargs_nil
#print axioms Lean4Lean.InductiveDeclExamples.n_headHargs_cons
#print axioms Lean4Lean.InductiveDeclExamples.n_iotaHargs_nil_gen
#print axioms Lean4Lean.InductiveDeclExamples.n_iotaHargs_cons_gen
#print axioms Lean4Lean.InductiveDeclExamples.n_hdata_all_gen
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iotaRulesRS_wf_all_gen
#print axioms Lean4Lean.InductiveDeclExamples.n_companion_unindexed
#print axioms Lean4Lean.InductiveDeclExamples.n_window_empty
#print axioms Lean4Lean.InductiveDeclExamples.n_np_pos
#print axioms Lean4Lean.InductiveDeclExamples.n_hbv_spine_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.n_hpiC_cons_moves
#print axioms Lean4Lean.InductiveDeclExamples.n_hres_cons_moves
#print axioms Lean4Lean.InductiveDeclExamples.n_hres_nil_identity
#print axioms Lean4Lean.InductiveDeclExamples.n_hAsC_needs_beta
#print axioms Lean4Lean.InductiveDeclExamples.n_tyBody_is_stored_const

end InductiveDeclExamples
end Lean4Lean
