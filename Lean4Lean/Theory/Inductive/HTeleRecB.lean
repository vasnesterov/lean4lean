import Lean4Lean.Theory.Inductive.HTeleGen
import Lean4Lean.Theory.Inductive.RecTyped

/-!
# `htele` all the way down to `hargs`: (C)'s telescope routed through (B)'s producers

`Theory/Inductive/HTeleGen.lean` §2 takes obligation (B)'s two **entry defeq** families as
hypotheses, because `RecTyped.lean` — where their producers live — is a concurrent stream's file and
was mid-edit (`HTeleGen.lean` §5c).  This file is the last link: it imports that file and derives
the two entry families from (B)'s four **data** families, so that (C) at a whole block stands on

* `MotiveHargs`, `MinorCtorHargs`, `MinorFldDefEq` — obligation (B)'s own data, unchanged;
* `MinorFldDefEq` at `q = D.nmin` — the one extra instance of a family (B) already has
  (`HTeleGen.lean` §1/§3);
* `IotaHeadHargs` at the **companion** rules (`HTeleNTree.lean` §2).

and on nothing else.  `RecBodyHargs`, (B)'s fourth family, is **not** needed: it is the recursor
*body*, which (C)'s telescope does not contain.

**Reduction, not discharge.**  (B)'s data families are inhabited nowhere at `D.np > 0`
(`RecTyped.lean` §6c).  §4 is the joint check that everything *else* holds at the canonical block.

**Fragile by construction**: this is the only file of mine that imports a file in flight.  If
`RecTyped.lean` changes `MotiveHargs`/`MinorCtorHargs`, this file breaks and `HTeleGen.lean` does
not.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)

/-! ## §1 (B)'s two entry families from (B)'s data families

Both are `VEnv.recConstsR_wf_of_recHargsD`'s own case splits, lifted out of that proof so (C) can
reuse them.  Note the two branches: at `T.name ∈ K` the data is demanded, off `K` the entry defeq
is reflexive and free — which is what keeps the premise set inhabitable at a real nested block
(`RecTyped.lean` §6a). -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}
variable {env₀ E₂ e₂ : VEnv}

/-- **`iotaCtx_teleDefEq`'s `hmot` from `MotiveHargs`.** -/
theorem iotaMot_of_recHargs
    (henv : env₀.Ordered) (hD : D.WF env₀) (hfresh : σ.FreshIn env₀)
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WFD E₂ e₂ D.recUvars) (hσc : σ.Closed)
    (he₂ : e₂.Ordered) (hfr : R.SubstFree D σ) (hat : R.SubstAt D K σ)
    (hown : R.OwnId D K) (helim : D.elimLvl.WF D.recUvars)
    (hcl : ∀ t : Nat, ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    (hmotD : ∀ (t : Nat) (T : VIndType), D.types[t]? = some T → T.name ∈ K →
      R.MotiveHargs D σ e₂ t T) :
    ∀ t : Nat, t < D.nm → ∃ u, e₂.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) ((D.motiveTypeR R t).substC σ) (.sort u) := by
  have hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩ := by
    intro j T hT
    exact hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩) (by
      simp only [VInductDecl'.recConsts, List.mem_map]
      exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)
  intro t ht
  obtain ⟨Tt, hTt⟩ : ∃ Tt, D.types[t]? = some Tt := by
    rcases hlt : D.types[t]? with _ | Tt
    · exact absurd (by simpa using List.getElem?_eq_none_iff.1 hlt) (by simpa using ht)
    · exact ⟨Tt, rfl⟩
  by_cases hKt : Tt.name ∈ K
  · obtain ⟨As, B, B', w, hbody, hpi, hAs, hsort⟩ := hmotD t Tt hTt hKt
    exact motiveEntry_defeq_of_hargs henv hD hfresh he₂ hσ hσc hfr hat helim
      (VInductDecl'.getD_types hTt) (hrec t Tt hTt) hTt hKt ht (hcl t) hbody hpi hAs hsort
  · exact _root_.Lean4Lean.motiveEntry_defeq_off_K he₂ hσ hown
      (VInductDecl'.getD_types hTt) (hrec t Tt hTt) hTt hKt ht

/-- **`iotaCtx_teleDefEq`'s `hmin` from `MinorCtorHargs` and `MinorFldDefEq`.** -/
theorem iotaMin_of_recHargs
    (henv : env₀.Ordered) (hD : D.WF env₀) (hfresh : σ.FreshIn env₀)
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WFD E₂ e₂ D.recUvars) (hσc : σ.Closed)
    (he₂ : e₂.Ordered) (hfr : R.SubstFree D σ) (hat : R.SubstAt D K σ)
    (hown : R.OwnId D K)
    (hcl : ∀ t : Nat, ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    (hfldD : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') →
      R.MinorFldDefEq D σ e₂ q C')
    (hminD : ∀ (q t : Nat) (C' : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (t, C') →
      D.types[t]? = some T → T.name ∈ K → R.MinorCtorHargs D σ e₂ q t C') :
    ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') → ∃ u,
      e₂.IsDefEq D.recUvars
        (((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
        ((D.minorType q t C').substC σ) ((D.minorTypeR R q t C').substC σ) (.sort u) := by
  have hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩ := by
    intro j T hT
    exact hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩) (by
      simp only [VInductDecl'.recConsts, List.mem_map]
      exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)
  intro q t C' hq
  obtain ⟨T, hT, hC'⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq)
  have hqlt : q < D.minors.length := by
    simpa using (List.getElem?_eq_some_iff.1 hq).1
  by_cases hKt : T.name ∈ K
  · obtain ⟨As, B, B', hcbody, hpi, hAs, hfun⟩ := hminD q t C' T hq hT hKt
    exact minorEntry_defeq_of_hargs henv hD hfresh he₂ hσ hσc hfr hat
      (VInductDecl'.getD_types hT) (hrec t T hT) hT hKt hC' hq hqlt (hcl t)
      (hfldD q t C' hq) hcbody hpi hAs hfun
  · exact minorEntry_defeq_off_K he₂ hσ hσc hown
      (VInductDecl'.getD_types hT) (hrec t T hT) hT hKt hC' hq hqlt (hfldD q t C' hq)

end
end VIndRestore

/-! ## §2 (C) at a whole block from (B)'s DATA families

`HTeleGen.lean` §2 fed by §1.  `hfldI` is `MinorFldDefEq` at `q = D.nmin`, which is definitionally
the shape §1's sibling asks for at `q < D.nmin` — the same family, one index over. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}
variable {env₀ env e : VEnv}

/-- **`hdata` at a whole block from (B)'s three data families, `MinorFldDefEq` at `q = D.nmin`,
and `IotaHeadHargs` at the companion rules.**  Nothing else is (C)-specific. -/
theorem hdata_of_recHargs_and_heads
    (henv : env₀.Ordered) (hD : D.WF env₀) (hfresh : σ.FreshIn env₀)
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF env c.2)
    (hσD : σ.WFD env e D.recUvars) (hσc : σ.Closed) (he : e.Ordered) (hI : D.IotaCtx env)
    (hfr : R.SubstFree D σ) (hat : R.SubstAt D K σ) (hown : R.OwnId D K)
    (helim : D.elimLvl.WF D.recUvars)
    (hcl : ∀ t : Nat, ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    (hmotD : ∀ (t : Nat) (T : VIndType), D.types[t]? = some T → T.name ∈ K →
      R.MotiveHargs D σ e t T)
    (hfldD : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') →
      R.MinorFldDefEq D σ e q C')
    (hminD : ∀ (q t : Nat) (C' : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (t, C') →
      D.types[t]? = some T → T.name ∈ K → R.MinorCtorHargs D σ e q t C')
    (hfldI : ∀ (q t : Nat) (C' : VIndCtor), D.ctorsAll[q]? = some (t, C') →
      R.MinorFldDefEq D σ e D.nmin C')
    (hheadD : ∀ (q j : Nat) (C : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (j, C) →
      D.types[j]? = some T → T.name ∈ K → R.IotaHeadHargs D σ e j T C) :
    ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) → R.IotaHargs D σ e j C :=
  hdata_of_entries_and_heads hown hat hfr hσc hσD hI he hcl
    (iotaMot_of_recHargs henv hD hfresh hsrc hσD hσc he hfr hat hown helim hcl hmotD)
    (iotaMin_of_recHargs henv hD hfresh hsrc hσD hσc he hfr hat hown hcl hfldD hminD)
    (fun q t C' hq => hfldI q t C' hq) hheadD

end
end VIndRestore

/-! ## §3 …and obligation (C) at the canonical block from (B)'s data families alone -/

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

include h hE₁ hE₂ hE₃ in
/-- `hsrc` at the ι-**stage** source environment.  `ntree_recConsts_wf` is stated at `E₂`; the
recursor block's own addition is monotone. -/
theorem ntree_recConsts_wf₃ : ∀ c ∈ ntreeAux.recConsts, VConstant.WF E₃ c.2 :=
  fun c hc => (ntree_recConsts_wf h hE₁ hE₂ c hc).mono (VEnv.addIndRecs_le hE₃)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **Obligation (C) at the canonical parameterised nested block from (B)'s three data families
alone.**  Compare `ntreeAux_obligationB_of_bundles` (`RecTyped.lean` §6b), which is obligation (B)
from the same families plus `RecBodyHargs`. -/
theorem ntree_obligationC_of_recHargs
    (hmotD : ∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
      ntreeRestore.MotiveHargs ntreeAux gS F₃ t T)
    (hfldD : ∀ (q t : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C) →
      ntreeRestore.MinorFldDefEq ntreeAux gS F₃ q C)
    (hminD : ∀ (q t : Nat) (C : VIndCtor) (T : VIndType),
      ntreeAux.ctorsAll[q]? = some (t, C) → ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
      ntreeRestore.MinorCtorHargs ntreeAux gS F₃ q t C) :
    ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df := by
  refine ntree_obligationC_of_entries h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ ?_ ?_
  · exact VIndRestore.iotaMot_of_recHargs (listEnv_ordered h) (ntreeAux_WF h)
      (ntree_csubst_fresh h) (ntree_recConsts_wf₃ h hE₁ hE₂ hE₃)
      (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃) ntree_csubst_closed
      (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃) ntreeRestore_substFree
      ntreeRestore_domSep.substAt ntreeRestore_ownId (by decide) ntree_tyArgs_closedN_np hmotD
  · exact VIndRestore.iotaMin_of_recHargs (listEnv_ordered h) (ntreeAux_WF h)
      (ntree_csubst_fresh h) (ntree_recConsts_wf₃ h hE₁ hE₂ hE₃)
      (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃) ntree_csubst_closed
      (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃) ntreeRestore_substFree
      ntreeRestore_domSep.substAt ntreeRestore_ownId ntree_tyArgs_closedN_np hfldD hminD

end

/-- **`RecBodyHargs` is NOT among (C)'s inputs**, and the reason is structural rather than lucky:
(C)'s telescope is `iotaCtx`, which has no recursor-body entry.  Recorded because the count "(B)
has four data families, (C) uses three" is the summary of this file. -/
theorem n_iotaCtx_has_no_body_entry :
    ntreeAux.iotaCtx nlistNil
      = ntreeAux.atRecTele ntreeAux.params ++ ntreeAux.motives ++ ntreeAux.minors
        ++ VExpr.liftTele (ntreeAux.nm + ntreeAux.nmin)
            (ntreeAux.atRecTele (nlistNil.fields.map (·.type))) := rfl

end InductiveDeclExamples

/-! ## §4 Axiom audit — hole-freeness only -/

#print axioms Lean4Lean.VIndRestore.iotaMot_of_recHargs
#print axioms Lean4Lean.VIndRestore.iotaMin_of_recHargs
#print axioms Lean4Lean.VIndRestore.hdata_of_recHargs_and_heads
#print axioms Lean4Lean.InductiveDeclExamples.ntree_recConsts_wf₃
#print axioms Lean4Lean.InductiveDeclExamples.ntree_obligationC_of_recHargs
#print axioms Lean4Lean.InductiveDeclExamples.n_iotaCtx_has_no_body_entry

end Lean4Lean
