/-
# `FlipPriceCompose`: §12 of `FlipPrice.lean`, attempted and answered

The brief for this stream asked whether `VExpr.NoConstIn.noCSubst` at `P := IsNestedName`,
composed against `IsNestedName` being a *prefix* test (so that it covers a companion's
constructor and recursor names, not just its type name), discharges the `csubst`-domain
obstruction that `docs/vacuity-ledger.md` row 28 and `Theory/Inductive/NestedOrdered.lean`'s
third STATUS entry record against obligations **(B)** and **(C)**.

**Answer: yes, and the composition was already in the tree before this stream started.**  It is
`VIndRestore.NameBarrier` (`Verify/Inductive/NestedRestore.lean` §2):

* `NameBarrier.dom` = `VIndRestore.csubst_dom` (`Theory/Inductive/NestedRules.lean` §7.2) plus the
  barrier's three `aux*` clauses — *"everything in `csubst`'s domain satisfies `P`"*, which is
  literally `noCSubst`'s `hdom`;
* `NameBarrier.substFree`'s `tyArgs` field is `(h.resArgs j a ha).noCSubst fun _ _ => h.dom` —
  the composition, spelled out;
* `NestedBarrier := NameBarrier … IsNestedName` is the instance at the prefix test, and
  `mkRestore_nestedBarrier`'s `auxRec` clause is exactly `IsNestedName.mkRecName_iff.2`, i.e. the
  prefix-test half of §12's pair.

So there is nothing to *invent* here.  What was genuinely missing is the end-to-end statement:
nobody had written down (B) or (C) with the barrier in place of `SubstFree`, which is what makes
"the obstruction is discharged" checkable rather than an argument about docstrings.  That is what
this file does, and every proof below is a single application — which is the honest measure of
how much of §12 was left.

Nothing here is a new mathematical result.  It is a composition, and it is offered as evidence
for `docs/handoff-flipprice.md` §5.
-/
import Lean4Lean.Verify.Inductive.NestedRestore
import Lean4Lean.Theory.Inductive.NestedTele

namespace Lean4Lean

open Lean (Name)

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-! ## 1. (B) and (C) at `np = 0`, from the `_nested` barrier

`VEnv.recConstsR_wf_of_np_zero` / `VEnv.iotaRulesRS_wf_of_np_zero`
(`Theory/Inductive/NestedRules.lean` §7.7) each take `hfr : R.SubstFree D (R.csubst D K)`.  That
hypothesis **is** row 28's obstruction, restated: it is the condition `D.blockNames` could not
reach.  Here it is discharged from the reserved-prefix barrier and nothing else — no `env`, no
`Faithful`, no `Canonical`. -/

/-- **Obligation (B) at `D.params = []`, with the `csubst`-domain obstruction discharged from the
reserved `_nested` prefix.** -/
theorem VEnv.recConstsR_wf_of_np_zero_of_barrier {E₂ e₂ : VEnv}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WF E₂ e₂ D.recUvars)
    (hp : D.params = []) (hown : R.OwnId D K)
    (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hb : R.NestedBarrier D K) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 :=
  VEnv.recConstsR_wf_of_np_zero hsrc hσ hp hown hsep hcl0 hb.substFree

/-- **Obligation (C) at `D.params = []`, same discharge.** -/
theorem VEnv.iotaRulesRS_wf_of_np_zero_of_barrier {E₃ e₃ : VEnv}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, (R.csubst D K).WF E₃ e₃ df.uvars)
    (hp : D.params = []) (hown : R.OwnId D K)
    (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hb : R.NestedBarrier D K)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_np_zero hsrc hσ hp hown hsep hcl0 hb.substFree hpos

/-! ### 1a. …and with `DomSep` also gone, from the block's own `Nodup`

`VIndRestore.domSep_of_allNames_nodup` derives `DomSep`'s three `= none` clauses from
`D.allNames.Nodup`.  Composing that too leaves, of the *name-discipline* hypotheses, only
`OwnId`, `DomNodup` and the barrier. -/

theorem VEnv.recConstsR_wf_of_np_zero_of_barrier' {E₂ e₂ : VEnv}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WF E₂ e₂ D.recUvars)
    (hp : D.params = []) (hown : R.OwnId D K)
    (hnd0 : D.allNames.Nodup) (hdn : R.DomNodup D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hb : R.NestedBarrier D K) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 :=
  VEnv.recConstsR_wf_of_np_zero_of_barrier hsrc hσ hp hown
    (VIndRestore.domSep_of_allNames_nodup hnd0 hdn) hcl0 hb

theorem VEnv.iotaRulesRS_wf_of_np_zero_of_barrier' {E₃ e₃ : VEnv}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, (R.csubst D K).WF E₃ e₃ df.uvars)
    (hp : D.params = []) (hown : R.OwnId D K)
    (hnd0 : D.allNames.Nodup) (hdn : R.DomNodup D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hb : R.NestedBarrier D K)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_np_zero_of_barrier hsrc hσ hp hown
    (VIndRestore.domSep_of_allNames_nodup hnd0 hdn) hcl0 hb hpos

/-! ## 2. The composition where it actually matters: `D.np > 0`

This is the half the brief's §12 was reaching for and the half that is *not* redundant with §1.
`VEnv.iotaRulesRS_wf_of_hargsD` (`Theory/Inductive/NestedTele.lean` §T16.11) is (C) for a
**parameterful** block, and it too takes `hfr : R.SubstFree D (R.csubst D K)`.  With the barrier
discharging `hfr` and `DomSep.substAt` discharging `hat`, the *only* restoration-shaped input
left is `hdata` — the per-constructor typed conversions of `R.IotaHargs`.

That is the honest statement of what still blocks (C) in general, and it is a **typed** residual,
not a syntactic one: the syntactic list bridge is refuted at `np = 1`
(`InductiveDeclExamples.ntree_iotaRules_bridge_false`). -/

/-- **Obligation (C) at `D.np > 0`, with every name-discipline input discharged from the barrier
and the block's own `Nodup`, leaving `hdata` alone.** -/
theorem VEnv.iotaRulesRS_wf_of_hargsD_of_barrier {env e₃ : VEnv}
    (hown : R.OwnId D K)
    (hnd0 : D.allNames.Nodup) (hdn : R.DomNodup D K)
    (hb : R.NestedBarrier D K)
    (hσc : (R.csubst D K).Closed)
    (hσ : (R.csubst D K).WFD env e₃ D.recUvars) (hI : D.IotaCtx env) (henv : e₃.Ordered)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    (hdata : ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) →
      R.IotaHargs D (R.csubst D K) e₃ j C) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_hargsD hown
    (VIndRestore.domSep_of_allNames_nodup hnd0 hdn).substAt hb.substFree hσc hσ hI henv hpos hdata

/-! ## 3. …and from the checker's own data, with no barrier hypothesis at all

`ElimNestedInductive.Result.RestoreData.mkRestore_nestedBarrier` supplies the barrier for the
restoration the *implementation* builds.  Composing it removes the barrier from the premises of
§2 entirely, which is what says the discharge is not merely relative to an assumption nothing
satisfies. -/

namespace ElimNestedInductive.Result.RestoreData
variable {r : ElimNestedInductive.Result} {types : List Lean.InductiveType}
  {D : VInductDecl'} {K : List Name} {ls : Nat → List VLevel} {as : Nat → List VExpr}

/-- **(C) at `D.np > 0` for the restoration the checker actually constructs.**  No `SubstFree`,
no `NestedBarrier`, no `SubstAt` — only `OwnId`-free name data (`h`), the block's `Nodup`, and
the typed residual `hdata`. -/
theorem mkRestore_iotaRulesRS_wf_of_hargsD {env e₃ : VEnv}
    (h : RestoreData r types D K as)
    (hnd0 : D.allNames.Nodup)
    (hdn : (r.mkRestore types D.uvars D.np ls as).DomNodup D K)
    (hσc : ((r.mkRestore types D.uvars D.np ls as).csubst D K).Closed)
    (hσ : ((r.mkRestore types D.uvars D.np ls as).csubst D K).WFD env e₃ D.recUvars)
    (hI : D.IotaCtx env) (henv : e₃.Ordered)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r' : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r' → r'.idx < D.nm)
    (hdata : ∀ (q j : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (j, C) →
      (r.mkRestore types D.uvars D.np ls as).IotaHargs D
        ((r.mkRestore types D.uvars D.np ls as).csubst D K) e₃ j C) :
    ∀ df ∈ D.iotaRulesRS (r.mkRestore types D.uvars D.np ls as) K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_hargsD_of_barrier h.mkRestore_ownId hnd0 hdn h.mkRestore_nestedBarrier
    hσc hσ hI henv hpos hdata

end ElimNestedInductive.Result.RestoreData

/-! ## 4. Non-vacuity: the six name/shape hypotheses of §1 hold **jointly** at the witness

A clean axiom line is not evidence of content (`docs/vacuity-ledger.md` §0), so the barrier route
is checked to be *inhabited* rather than merely provable.  Two facts, and neither is an axiom
print:

1. `NestedBarrier` is bounded **both** ways at the `NFn`/`PFn` witness, field by field:
   `nfnRestore_nestedBarrier` holds, and each of the four `res*` fields is separately refuted by a
   junk restoration (`nfnBarrierJunkTy/Rec/Ctor/Args_not_barrier`), with `not_nestedBarrier_nil`
   showing it is not `K`-vacuous.  All in `Verify/Inductive/NestedRestore.lean` §7.
2. `nfnRestore_substFree'` (same file, `:666`) is the *hand* proof's conclusion re-derived through
   `NameBarrier.substFree`, so the composition is not weaker than what it replaces.

What follows is the conjunction §1 actually consumes.  It is deliberately **only** the
name/shape half: `hsrc` and `hσ` are environment-shaped and belong to the staging argument, not
to the restoration, and pretending to discharge them here would be the vacuity this file is
guarding against. -/

namespace InductiveDeclExamples

/-- **Every non-environment hypothesis of `VEnv.iotaRulesRS_wf_of_np_zero_of_barrier'` at once,
at the `NFn`/`PFn` block.**  So §1's (C) is a genuine reduction of the two environment
obligations, not a statement over an empty domain. -/
theorem nfn_barrier_route_inhabited :
    nfnAux.params = [] ∧ nfnRestore.OwnId nfnAux nfnK ∧ nfnAux.allNames.Nodup ∧
      nfnRestore.DomNodup nfnAux nfnK ∧
      (∀ i, ∀ a ∈ nfnRestore.tyArgs i, a.ClosedN 0) ∧
      nfnRestore.NestedBarrier nfnAux nfnK ∧
      (∀ (t : Nat) (C : VIndCtor), (t, C) ∈ nfnAux.ctorsAll →
        ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
          F.recArg = some r → r.idx < nfnAux.nm ∧ ∀ B ∈ r.binders, nfnAux.NoBlock B) :=
  ⟨nfnAux_params_nil, nfnRestore_ownId, nfnAux_allNames_nodup, nfnRestore_domNodup,
    nfnRestore_tyArgs_closed0, nfnRestore_nestedBarrier, nfnAux_pos⟩

end InductiveDeclExamples

/-! ## 5. Axiom audit

Every declaration above is a single application; the axiom lines are therefore those of the
theorems composed, and they are printed so that the claim in `docs/handoff-flipprice.md` §5 rests
on a measurement. -/

#print axioms Lean4Lean.InductiveDeclExamples.nfn_barrier_route_inhabited

/-! ### The ingredients of the composition, and the two consumers it also feeds

`VIndRestore.KeysFree` is the other thing `docs/critical-path.md` item 2 lists as needing to
"stop being a hypothesis", with the note that it is *not* derivable from `Faithful` + `OwnId` +
freshness.  `NameBarrier.keysFree` / `mkRestore_keysFree` derive it — from name discipline, which
is a different premise, so the note is not contradicted, only bypassed. -/
#print axioms Lean4Lean.VIndRestore.NameBarrier.dom
#print axioms Lean4Lean.VIndRestore.NameBarrier.substFree
#print axioms Lean4Lean.VIndRestore.NameBarrier.keysFree
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_nestedBarrier
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_substFree
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_keysFree
#print axioms Lean4Lean.InductiveDeclExamples.nfnRestore_nestedBarrier
#print axioms Lean4Lean.InductiveDeclExamples.nfnRestore_substFree'
#print axioms Lean4Lean.InductiveDeclExamples.not_nestedBarrier_nil

#print axioms Lean4Lean.VEnv.recConstsR_wf_of_np_zero_of_barrier
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_np_zero_of_barrier
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_np_zero_of_barrier'
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_np_zero_of_barrier'
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_hargsD_of_barrier
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_iotaRulesRS_wf_of_hargsD

end Lean4Lean
