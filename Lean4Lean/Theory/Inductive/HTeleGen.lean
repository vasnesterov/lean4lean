import Lean4Lean.Theory.Inductive.HTeleNTree

/-!
# `htele` in general — and what is left of obligation (C) once it is gone

`docs/handoff-ownrule.md` §5 leaves obligation (C) standing on **`htele`** — the ι-context
telescope defeq — plus `IotaHargs` at the companion rules.  `VIndRestore.iotaHargs_of_own` takes
`htele` as its *whole* residual, and `IotaHargsGen` §4 takes it as one of thirteen.

The measured answer is that `htele` is **not a new obligation**:

* `VInductDecl'.iotaCtx_teleDefEq` (§T15.4) already splits it into `hmot`, `hmin`, `hfld`, and its
  own docstring says `hmot`/`hmin` are *"literally the same hypotheses"* as obligation (B)'s
  motive- and minor-entry defeqs — `Theory/Inductive/RecTyped.lean` §3 has producers for both
  branches of both (`∈ K` from `hargs`, `∉ K` free).
* `hfld` is **obligation (B)'s own field-block defeq one index past the minor block**: (B) asks for
  it at each minor index `q < D.nmin`, (C) asks for the same predicate at `q = D.nmin`, where
  `List.take D.nmin` is the whole minor block.  §1 is that identity — one `List.take_of_length_le`
  and one `VExpr.map_substC_liftTele`, so `σ.Closed` and nothing else.

§2 is then (C) at a whole block from (B)'s three entry families plus `IotaHeadHargs`
(`HTeleNTree.lean` §2) at the **companion** rules; §3 discharges the `q = D.nmin` field defeq at
the canonical block at all three ι-rules; §4 instantiates §2 there, leaving **(B)'s two entry
defeq families as the only hypotheses**.

**This is a reduction, not a discharge, and the flip is not made.**  (B)'s entry defeqs are, at
`T.name ∈ K`, the open `hargs` obligation (`RecTyped.lean` §6c;
`VIndRestore.instAt_indep_of_tyArgs`).  §5 grades what is and is not established.

**Deliberately RecTyped-free.**  This file states (B)'s two entry families in the shape
`iotaCtx_teleDefEq` binds rather than importing `RecTyped.lean`'s `MotiveHargs`/`MinorCtorHargs`
bundles, because that file is a concurrent stream's and was mid-edit while this was written (§5c).
`Theory/Inductive/HTeleRecB.lean` does the import and the routing.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)

/-! ## §1 (C)'s field block is (B)'s, one index past the minor block

`RecTyped.lean`'s `VIndRestore.MinorFldDefEq q C` is

    e.TeleDefEq D.recUvars
      (((D.minors.map (substC · σ)).take q).reverse
        ++ ((D.motives.map (substC · σ)).reverse ++ ((D.atRecTele D.params).map (substC · σ)).reverse))
      (liftTele (D.nm + q) ((D.atRecTele (C.fields.map (·.type))).map (substC · σ)))
      (liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (substC · σ)))

and (C)'s `hfld` is that at `q = D.nmin`, with the `substC` outside the `liftTele`.  The body is
spelled out below rather than imported, so this file does not depend on a file in flight. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {σ : CSubst} {e : VEnv} {C : VIndCtor}

/-- **(C)'s `hfld` from the `q = D.nmin` instance of (B)'s field-block defeq.**  `List.take D.nmin`
of the minor block is the whole of it (`VInductDecl'.length_minors`), and the two `substC`/`liftTele`
commutations are `VExpr.map_substC_liftTele`. -/
theorem teleDefEq_fld_iota_of_minorFld (hσc : σ.Closed)
    (hfldI : e.TeleDefEq D.recUvars
      (((D.minors.map (VExpr.substC · σ)).take D.nmin).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
          ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      (liftTele (D.nm + D.nmin) ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (liftTele (D.nm + D.nmin) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)))) :
    e.TeleDefEq D.recUvars
      ((D.minors.map (VExpr.substC · σ)).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
          ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type)))).map
        (VExpr.substC · σ))
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fieldTypesR D R))).map
        (VExpr.substC · σ)) := by
  have htk : (D.minors.map (VExpr.substC · σ)).take D.nmin = D.minors.map (VExpr.substC · σ) := by
    rw [List.take_of_length_le]
    rw [List.length_map, VInductDecl'.length_minors]
    exact Nat.le_refl _
  rw [VExpr.map_substC_liftTele (σ := σ) hσc, VExpr.map_substC_liftTele (σ := σ) hσc]
  rw [htk] at hfldI
  exact hfldI

end
end VIndRestore

/-! ## §2 (C) at a whole block, with nothing left that is not (B)'s

`hmot`/`hmin` below are `VInductDecl'.iotaCtx_teleDefEq`'s, i.e. (B)'s two entry families verbatim;
`hfldI` is §1's; `hheadD` is `IotaHeadHargs` at the **companion** rules.  The own rules' `IotaHargs`
costs nothing beyond `hmot`/`hmin`/`hfldI` (`OwnRule` §3 + §5.1). -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {env e : VEnv}

/-- **`hdata` at a whole block from (B)'s entry families, the `q = D.nmin` field defeq, and the
companion head bundles.**  Nothing else: no `hσ.WF`, no `hp : D.params = []`, no `hcl0`, no bound
on `D.np`. -/
theorem hdata_of_entries_and_heads
    (hown : R.OwnId D K) (hat : R.SubstAt D K σ) (hfr : R.SubstFree D σ) (hσc : σ.Closed)
    (hσD : σ.WFD env e D.recUvars) (hI : D.IotaCtx env) (he : e.Ordered)
    (hcl : ∀ t : Nat, ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    (hmot : ∀ t : Nat, t < D.nm → ∃ u, e.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) ((D.motiveTypeR R t).substC σ) (.sort u))
    (hmin : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') → ∃ u,
      e.IsDefEq D.recUvars
        (((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
        ((D.minorType q t C').substC σ) ((D.minorTypeR R q t C').substC σ) (.sort u))
    (hfldI : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') →
      e.TeleDefEq D.recUvars
        (((D.minors.map (VExpr.substC · σ)).take D.nmin).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
        (liftTele (D.nm + D.nmin) ((D.atRecTele (C'.fields.map (·.type))).map (VExpr.substC · σ)))
        (liftTele (D.nm + D.nmin) ((D.atRecTele (C'.fieldTypesR D R)).map (VExpr.substC · σ))))
    (hheadD : ∀ (q j : Nat) (C : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (j, C) →
      D.types[j]? = some T → T.name ∈ K → R.IotaHeadHargs D σ e j T C) :
    ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) → R.IotaHargs D σ e j C := by
  have htele : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') →
      e.TeleDefEq D.recUvars [] ((D.iotaCtx C').map (VExpr.substC · σ))
        ((D.iotaCtxR R C').map (VExpr.substC · σ)) := fun q t C' hq =>
    VInductDecl'.iotaCtx_teleDefEq hmot hmin
      (VIndRestore.teleDefEq_fld_iota_of_minorFld hσc (hfldI q t C' hq))
  refine hdata_of_companions hown hat hfr hσc hσD hI htele ?_
  intro q j C T hq hT hK
  obtain ⟨T', hT', hC⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq)
  cases hT.symm.trans hT'
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  exact iotaHargs_of_headHargs (K := K) hat hfr hσc (hcl j) he hT hK hC hj
    ((hI.toRecCtx.ctors j T hT C hC).args_len) (htele q j C hq) (hheadD q j C T hq hT hK)

end
end VIndRestore

/-! ## §3 The `q = D.nmin` field defeq, INHABITED at the canonical block

The one thing (C)'s telescope asks for that (B)'s does not.  At `ntreeAux` the ambient context is
§E's recursor telescope `rTele` on the nose, and each field block is at most two entries, of which
the second is one `rbetaL` step — the same step `rIotaTele_node` performs. -/

namespace InductiveDeclExamples

abbrev gD : VInductDecl' := ntreeAux
abbrev gS : CSubst := ntreeRestore.csubst ntreeAux ntreeK

/-- The ambient context of the `q = D.nmin` field defeq at this block is §E's telescope. -/
theorem n_minorFld_iota_ctx :
    (((gD.minors.map (VExpr.substC · gS)).take gD.nmin).reverse
      ++ ((gD.motives.map (VExpr.substC · gS)).reverse
        ++ ((gD.atRecTele gD.params).map (VExpr.substC · gS)).reverse)) = rTele.reverse := by
  decide

theorem n_minorFld_node_lhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fields.map (·.type))).map
      (VExpr.substC · gS)) = [.bvar 5, .app rV (.bvar 6)] := by decide

theorem n_minorFld_node_rhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS)) = [.bvar 5, .app rLt (.app rNt (.bvar 6))] := by decide

theorem n_minorFld_nil_lhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fields.map (·.type))).map
      (VExpr.substC · gS)) = [] := by decide

theorem n_minorFld_nil_rhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS)) = [] := by decide

theorem n_minorFld_cons_lhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fields.map (·.type))).map
      (VExpr.substC · gS)) = [.app rNt (.bvar 5), .app rV (.bvar 6)] := by decide

theorem n_minorFld_cons_rhs :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS)) = [.app rNt (.bvar 5), .app rLt (.app rNt (.bvar 6))] := by decide

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)

include hL hN in
/-- At the own ι-rule: one `rbetaL`. -/
theorem n_minorFldI_node : F.TeleDefEq gD.recUvars
    (((gD.minors.map (VExpr.substC · gS)).take gD.nmin).reverse
      ++ ((gD.motives.map (VExpr.substC · gS)).reverse
        ++ ((gD.atRecTele gD.params).map (VExpr.substC · gS)).reverse))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fields.map (·.type))).map
      (VExpr.substC · gS)))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS))) := by
  rw [n_minorFld_iota_ctx, n_minorFld_node_lhs, n_minorFld_node_rhs]
  exact .rfl (.cons (rbetaL hL hN (k := 6)
    (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) .nil)

/-- At the `nlistNil` ι-rule the field block is **empty**, so this one is free — measured, not
assumed: Lean's `unusedSectionVars` linter reports `hL`/`hN` unused here and used at the other
two, which is why the `omit` is there. -/
theorem n_minorFldI_nil : F.TeleDefEq gD.recUvars
    (((gD.minors.map (VExpr.substC · gS)).take gD.nmin).reverse
      ++ ((gD.motives.map (VExpr.substC · gS)).reverse
        ++ ((gD.atRecTele gD.params).map (VExpr.substC · gS)).reverse))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fields.map (·.type))).map
      (VExpr.substC · gS)))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS))) := by
  rw [n_minorFld_iota_ctx, n_minorFld_nil_lhs, n_minorFld_nil_rhs]
  exact .nil

include hL hN in
/-- …and at the `nlistCons` ι-rule. -/
theorem n_minorFldI_cons : F.TeleDefEq gD.recUvars
    (((gD.minors.map (VExpr.substC · gS)).take gD.nmin).reverse
      ++ ((gD.motives.map (VExpr.substC · gS)).reverse
        ++ ((gD.atRecTele gD.params).map (VExpr.substC · gS)).reverse))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fields.map (·.type))).map
      (VExpr.substC · gS)))
    (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fieldTypesR gD ntreeRestore)).map
      (VExpr.substC · gS))) := by
  rw [n_minorFld_iota_ctx, n_minorFld_cons_lhs, n_minorFld_cons_rhs]
  exact .rfl (.cons (rbetaL hL hN (k := 6)
    (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) .nil)

include hL hN in
/-- **§2's whole `hfldI` family, at the canonical block.** -/
theorem n_minorFldI_all : ∀ (q t : Nat) (C' : VIndCtor), gD.ctorsAll[q]? = some (t, C') →
    F.TeleDefEq gD.recUvars
      (((gD.minors.map (VExpr.substC · gS)).take gD.nmin).reverse
        ++ ((gD.motives.map (VExpr.substC · gS)).reverse
          ++ ((gD.atRecTele gD.params).map (VExpr.substC · gS)).reverse))
      (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (C'.fields.map (·.type))).map
        (VExpr.substC · gS)))
      (liftTele (gD.nm + gD.nmin) ((gD.atRecTele (C'.fieldTypesR gD ntreeRestore)).map
        (VExpr.substC · gS))) := by
  intro q t C' hq
  rw [ntreeAux_ctorsAll_eq] at hq
  match q with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact n_minorFldI_node hL hN
  | 1 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact n_minorFldI_nil
  | 2 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact n_minorFldI_cons hL hN
  | (n+3) => simp at hq

end

/-! ## §4 §2 INSTANTIATED at the canonical block: (B)'s two entry families are all that is left -/

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
/-- **Obligation (C) at the canonical parameterised nested block from (B)'s two entry defeq
families alone.**  `hmot` and `hmin` are `VInductDecl'.iotaCtx_teleDefEq`'s, which its own docstring
says are (B)'s *"literally the same hypotheses"*; everything else — the ι-stage environment facts,
the `q = D.nmin` field defeq (§3) and `IotaHeadHargs` at both companion rules
(`HTeleNTree` §2a) — is discharged from the staging equations.

So **after this file (C) at this block asks for nothing beyond (B)'s entry defeqs.** -/
theorem ntree_obligationC_of_entries
    (hmot : ∀ t : Nat, t < ntreeAux.nm → ∃ u, F₃.IsDefEq ntreeAux.recUvars
      (((ntreeAux.motives.map (VExpr.substC · gS)).take t).reverse
        ++ ((ntreeAux.atRecTele ntreeAux.params).map (VExpr.substC · gS)).reverse)
      ((ntreeAux.motiveType t).substC gS) ((ntreeAux.motiveTypeR ntreeRestore t).substC gS)
      (.sort u))
    (hmin : ∀ (q t : Nat) (C' : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C') → ∃ u,
      F₃.IsDefEq ntreeAux.recUvars
        (((ntreeAux.minors.map (VExpr.substC · gS)).take q).reverse
          ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
            ++ ((ntreeAux.atRecTele ntreeAux.params).map (VExpr.substC · gS)).reverse))
        ((ntreeAux.minorType q t C').substC gS)
        ((ntreeAux.minorTypeR ntreeRestore q t C').substC gS) (.sort u)) :
    ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df := by
  have hFo := ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃
  refine ntreeAux_obligationC_of_hdata h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ ?_
  refine VIndRestore.hdata_of_entries_and_heads ntreeRestore_ownId
    ntreeRestore_domSep.substAt ntreeRestore_substFree ntree_csubst_closed
    (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    ((ntreeAux_WF h).iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃) hFo
    ntree_tyArgs_closedN_np hmot hmin
    (n_minorFldI_all (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)) ?_
  intro q j C T hq hT hK
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
    rw [show T = ntreeAux.types.getD 1 default from by
      rw [List.getD_eq_getElem?_getD, hT]; rfl]
    exact n_headHargs_nil (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃) hFo
  | 2 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    rw [show T = ntreeAux.types.getD 1 default from by
      rw [List.getD_eq_getElem?_getD, hT]; rfl]
    exact n_headHargs_cons (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃) hFo
  | (n+3) => simp at hq

end

/-! ## §5 What is and is not established

`docs/vacuity-ledger.md` §0: the `#print axioms` block of §6 is **hole-freeness only**.

### 5a Established

* §1's identity — (C)'s field block is (B)'s field-block defeq at `q = D.nmin` — from `σ.Closed`
  and nothing else.
* §3 — that instance **inhabited** at the canonical block at all three ι-rules, free at
  `nlistNil` and one `rbetaL` each at the other two.
* §4 — obligation (C) at the canonical block from (B)'s two entry defeq families alone.

### 5b NOT established

* §2's and §4's hypothesis sets are **not known jointly satisfiable at `D.np > 0`**: at
  `T.name ∈ K` the entry defeqs are the open `hargs` obligation, inhabited nowhere at `D.np > 0`
  (`RecTyped.lean` §6c; `VIndRestore.instAt_indep_of_tyArgs`).  Grade §2/§4 as *hole-free, composed
  end to end, inhabitation of the entry families unknown*.
* At **both** parameterised witnesses `htele` is already proved *without any of this*
  (`rIotaTele_nil`/`_node`/`_cons` from five constant lookups; `mpIotaTele_obj`/`_node`).  So §2 is
  **weaker at the witness** than what the tree already had; its value is generality, and
  `HTeleNTree` §3's `ntree_iotaRulesRS_wf_all_gen` (arity 0) is the stronger statement at this
  block.

### 5c Foreign file in flight, seen and not fixed

`Theory/Inductive/RecTyped.lean` (a concurrent stream's) changed `VIndRestore.MinorCtorHargs` from
seven components to three while `VEnv.recConstsR_wf_of_recHargsD` at `:996` still destructures
`⟨As, B, B', hcbody, hpi, hAs, hfun⟩`, so that file did not elaborate while this one was written.
An earlier draft of this file imported it and was blocked; the import was dropped and (B)'s two
entry families restated in the shape `iotaCtx_teleDefEq` binds.  Their file is untouched.

### 5d Anti-degeneracy for §1 and §3 -/

/-- The field blocks §3 relates really move at the two constructors that have fields. -/
theorem n_minorFldI_node_moves :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fields.map (·.type))).map
        (VExpr.substC · gS))
      ≠ liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fieldTypesR gD ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

theorem n_minorFldI_cons_moves :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fields.map (·.type))).map
        (VExpr.substC · gS))
      ≠ liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistCons.fieldTypesR gD ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

/-- …and `nlistNil`'s does not, which bounds the "one `rbetaL` per constructor with fields" claim
on both sides. -/
theorem n_minorFldI_nil_trivial :
    liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fields.map (·.type))).map
        (VExpr.substC · gS))
      = liftTele (gD.nm + gD.nmin) ((gD.atRecTele (nlistNil.fieldTypesR gD ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

/-- **`q = D.nmin` is a genuinely new index, not one of (B)'s.**  At the own constructor (B) asks
for the field block at `q = 0`, lifted by `D.nm + 0`; the two lifts differ. -/
theorem n_minorFld_iota_ne_own :
    liftTele (gD.nm + 0) ((gD.atRecTele (ntreeNode.fields.map (·.type))).map
        (VExpr.substC · gS))
      ≠ liftTele (gD.nm + gD.nmin) ((gD.atRecTele (ntreeNode.fields.map (·.type))).map
        (VExpr.substC · gS)) := by decide

/-- …and it is past every minor index: the block has exactly `D.nmin` ι-rules. -/
theorem n_ctorsAll_length : gD.ctorsAll.length = gD.nmin := by decide

/-- **§2 is not the vacuous `∈ K`-for-all-types version** `RecTyped.lean` §6a refutes: the own
member's name is not in `K`, so the off-`K` branches of `hmot`/`hmin` are reached. -/
theorem n_hmot_offK_branch_reached :
    ¬ (∀ (t : Nat) (T : VIndType), gD.types[t]? = some T → T.name ∈ ntreeK) := by
  intro hall
  have h0 : gD.types[0]? = some (gD.types.getD 0 default) := rfl
  exact absurd (hall 0 _ h0) (by decide)

end InductiveDeclExamples

/-! ## §6 Axiom audit — hole-freeness only -/

#print axioms Lean4Lean.VIndRestore.teleDefEq_fld_iota_of_minorFld
#print axioms Lean4Lean.VIndRestore.hdata_of_entries_and_heads
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFld_iota_ctx
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_node
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_nil
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_cons
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_all
#print axioms Lean4Lean.InductiveDeclExamples.ntree_obligationC_of_entries
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_node_moves
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_cons_moves
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFldI_nil_trivial
#print axioms Lean4Lean.InductiveDeclExamples.n_minorFld_iota_ne_own
#print axioms Lean4Lean.InductiveDeclExamples.n_ctorsAll_length
#print axioms Lean4Lean.InductiveDeclExamples.n_hmot_offK_branch_reached

end Lean4Lean
