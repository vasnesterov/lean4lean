import Lean4Lean.Theory.Inductive.FamInhabNTree
import Lean4Lean.Theory.Inductive.HTeleRecB

/-!
# `FamInhabC`: obligation (C) at `ntreeAux` from the data families, with the families supplied

`Theory/Inductive/FamInhabNTree.lean` inhabits obligation (B)'s four data families at the canonical
parameterised nested block.  `Theory/Inductive/HTeleRecB.lean` §3 reduces obligation (C) at that
block to **three** of them.  This file composes the two, so that `ntree_obligationC_of_recHargs`
stops being a reduction with an unknown premise set.

**Why this is a separate file.**  `HTeleRecB.lean` is a concurrent stream's, it imports
`RecTyped.lean` (another stream's), and both changed under me during this session —
`VIndRestore.MinorCtorHargs` went from a four-conjunct to a three-conjunct bundle and
`iotaMin_of_recHargs` grew two side-condition hypotheses.  `FamInhabNTree.lean` deliberately imports
only `RecTyped` and `HTeleGen`, so a break in `HTeleRecB` costs this file and not that one.  Same
blast-radius decision `HTeleGen.lean` §6 records for itself.
-/

namespace Lean4Lean

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
/-- **OBLIGATION (C) AT THE CANONICAL PARAMETERISED NESTED BLOCK, THROUGH THE GENERAL DATA-FAMILY
ROUTE, WITH THE FAMILIES SUPPLIED.**

`HTeleRecB.lean`'s `ntree_obligationC_of_recHargs` had arity 3 and its own §4b graded it
*"hole-free, composed end to end, inhabitation of the data families unknown"*.
`FamInhabNTree.lean` §1 supplies the three, so the grade becomes **inhabited**. -/
theorem fi_ntreeAux_obligationC :
    ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df :=
  ntree_obligationC_of_recHargs h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃
    (fi_hmotD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃))
    (fi_hfldD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃))
    (fi_hminD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃))

end

/-- **…arity 0.**  `ntree_stage₃_exists` supplies the seven staging equations, so obligation (C)
holds at a parameterised nested block through the data-family route with **nothing assumed**.

Compare `HTeleNTree.lean`'s `ntree_iotaRulesRS_wf_all_gen`, which is also arity 0 but goes through
`IotaHargsGen` §4 directly.  The point of this one is the *route*: it certifies
`VIndRestore.hdata_of_recHargs_and_heads`, and hence obligation (B)'s data families as (C)'s
inputs, non-vacuous above `np = 0`. -/
theorem fi_obligationC_inhabited :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      E₂.addIndRecs ntreeAux = some E₃ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃ ∧
      ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  exact ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃,
    fi_ntreeAux_obligationC h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃⟩


/-! ## §2 The GENERAL (C) closure itself, instantiated

§1 goes through `ntree_obligationC_of_recHargs`, which routes via `HTeleGen.lean` §4's
`ntree_obligationC_of_entries`.  `VIndRestore.hdata_of_recHargs_and_heads` — the *general* closure —
is one composition further out, and it is the declaration `docs/handoff-htele.md` §4b grades
"inhabitation of the data families unknown".  This section applies it directly, so that grade
changes for the closure itself and not only for its `ntreeAux` corollary.

Its two (C)-specific extra inputs are already inhabited at this block and are simply passed:
`hfldI` is `HTeleGen.lean` §3's `n_minorFldI_all` and `hheadD` is `HTeleNTree.lean` §2a's two
`IotaHeadHargs` witnesses, assembled here because no family-shaped form of them existed. -/

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
/-- `hdata_of_recHargs_and_heads`' `hheadD`, at this block: the companion's two ι-rules.  The
`ntreeNode` rule is off `K`, so the guard discharges it. -/
theorem fi_hheadD (henv : F.Ordered) :
    ∀ (q j : Nat) (C : VIndCtor) (T : VIndType), ntreeAux.ctorsAll[q]? = some (j, C) →
      ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ntreeRestore.IotaHeadHargs ntreeAux gS F j T C := by
  intro q j C T hq hT hK
  rw [ntreeAux_ctorsAll_eq] at hq
  match q with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    cases hT; exact absurd hK (by decide)
  | 1 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    cases hT; exact n_headHargs_nil hL hN hnil hcons hnode henv
  | 2 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    cases hT; exact n_headHargs_cons hL hN hnil hcons hnode henv
  | (n+3) => simp at hq

end

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
/-- **`VIndRestore.hdata_of_recHargs_and_heads` — the general (C) closure — INSTANTIATED at a
parameterised nested block, with every one of its nineteen hypotheses discharged.**

This is the certificate `docs/handoff-htele.md` §4b says is missing: the closure's premise set is
jointly satisfiable at `D.np = 1`. -/
theorem fi_hdata_general_instantiated :
    ∀ (q j : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (j, C) →
      ntreeRestore.IotaHargs ntreeAux gS F₃ j C :=
  VIndRestore.hdata_of_recHargs_and_heads (listEnv_ordered h) (ntreeAux_WF h)
    (ntree_csubst_fresh h) (ntree_recConsts_wf₃ h hE₁ hE₂ hE₃)
    (ntree_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃) ntree_csubst_closed
    (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃)
    ((ntreeAux_WF h).iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃)
    ntreeRestore_substFree ntreeRestore_domSep.substAt ntreeRestore_ownId (by decide)
    ntree_tyArgs_closedN_np
    (fi_hmotD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃))
    (fi_hfldD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃))
    (fi_hminD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃))
    ntree_minor_hσfD ntree_minor_hclFD
    (fun _ _ _ _ => n_minorFldI_all (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃) _ _ _
      (by assumption))
    (fi_hheadD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃) (ntreeF₃_node hF₂ hF₃)
      (ntreeF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃))

end

/-- **…arity 0.** -/
theorem fi_hdata_general_inhabited :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      E₂.addIndRecs ntreeAux = some E₃ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃ ∧
      ∀ (q j : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (j, C) →
        ntreeRestore.IotaHargs ntreeAux gS F₃ j C := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  exact ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃,
    fi_hdata_general_instantiated h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃⟩

/-! ## Axiom audit — hole-freeness only -/

#print axioms Lean4Lean.InductiveDeclExamples.fi_ntreeAux_obligationC
#print axioms Lean4Lean.InductiveDeclExamples.fi_obligationC_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.fi_hheadD
#print axioms Lean4Lean.InductiveDeclExamples.fi_hdata_general_instantiated
#print axioms Lean4Lean.InductiveDeclExamples.fi_hdata_general_inhabited

end InductiveDeclExamples
end Lean4Lean
