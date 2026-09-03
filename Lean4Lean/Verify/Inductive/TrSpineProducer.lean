import Lean4Lean.Verify.Inductive.StrengthenFamily
import Lean4Lean.Verify.Inductive.ValAtParam
import Lean4Lean.Verify.Inductive.SpineClosedLand

/-!
# The general producer of `TrIndDeclN.trSpine` at `numNested > 0`

`Verify/Environment/InductR.lean` carries the spine datum as a field, `TrIndDeclN.trSpine`, and
`Verify/Inductive/SpineClosedLand.lean` turns it into `hargs` per companion member
(`TrIndDeclN.hargsAt`) and into the nested step predicate's consequence
(`InductStepNested.spineHargsC`).  All three of the field's construction sites were *witnesses* or
the non-nested `TrIndDecl.toN`; **there was no general nested producer.**  This file is that
producer.

## The question this file was opened to answer, and the answer

`ValAtParam.lean` §6 measures the producer as sitting on the cycle whose entry
`RestrictStep.lean`'s `restrictStep_entry` locates at `VEnv.AxiomConservativityWF` ≡ the forward
direction of `VEnv.IsDefEqU.weakN_iff` (the `sorry` at `Theory/Typing/UniqueTyping.lean:193`).  That
measurement is **correct** — `VIndRestore.spineHargsC_iff_valStrengthen` is an `↔`, so the clause is
no cheaper door than the hole.

The open question was whether `StrengthenFamily.lean`'s bypass
(`VIndRestore.argsTypedK_of_succLevel`, which discharges `ValStrengthen` **without** `weakN_iff` by
substituting *any* inhabitant of the block's result sort) reaches this obligation, or is silent on
it as it is on obligations (B)/(C) (`docs/vacuity-ledger.md` rows 235/235b).  The cheap test
recorded there is: **is the value in question pinned?**

**It is not, and the bypass covers the producer.**  `VIndRestore.SpineHargsN` — which *is* the
`trSpine` field (`SpineClosedLand.lean`'s `TrIndDeclN.spineHargsN` is `h.trSpine` with no bridge,
`declTele` being an `abbrev`) — is a `VEnv.HasArgs` about the **presented spine**.  It mentions `R`
only through `tyName`/`tyLvls`/`tyArgs`; it mentions no `CSubst`, no `R.tyVal`, no `R.ctorVal`, no
`R.recVal` and no `csubstTy`.  So there is nothing for `WFD.val` — rows 235/235b's pinning
mechanism, which fixed the value to `R.ctorVal` / `R.recVal` and left the inhabited/uninhabited
split no purchase — to pin here, and the type is not empty (§3's witness, and `ValAtParam.lean`
§4's `ntreeAux_spineHargsN` before it).

**That is stated rather than asserted.**  §1's producer is quantified over an arbitrary inhabitant
`b : VIndType → VExpr`, so the freedom the bypass buys is *in the statement*; §3 runs it at a `b`
whose substituted value is provably **different** from the intended `ntreeVal`
(`StrengthenFamily.lean`'s `ntree_junkVal_ne_tyVal`).  A pinned obligation could not be discharged
at such a `b`; this one is.

**And the `SortWitness` refutation does not bite here.**  `Verify/Inductive/SortWitEnv.lean` refutes
the existence of a `Sort u`-valued constant at the environments this corner runs at, which kills
`VInductDecl'.resultSortInhab_of_const` — the **fourth** clause.  §2 uses the **first**
(`resultSortInhab_of_succ`), whose side conditions are level facts and which needs no environment
condition at all; `ntreeAux.lvl = .succ (.param 0)`, so it fires at the witness by `decide`.

## Statement-level notes on what is deliberately *not* used

Nothing below mentions `VEnv.HasArgs.of_mkApp` (measured to reach `sorryAx` through two holes),
`VEnv.IsDefEq.uniq`, or `VEnv.AxiomConservativityWF`.  The strongest transport reached is
`VEnv.IsDefEq.substC`, inside `StrengthenFamily.lean` §2.  §4 records exactly which blocks the
producer still misses, and it is `StrengthenFamily.lean` §8's residue verbatim — not a new one.

No structure gains a field here and no frozen file is touched.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The producer, from an arbitrary inhabitant of the result sort

Three composed arrows, all hole-free and all already in the tree:

    ResultSortInhab  --argsTypedK_of_resultSortInhab-->  ArgsTypedK K e₁ occ    (the bypass)
                     --cyc_datum_to_spine-->             SpineHargsK K e₁ occ
                     --SpineHargsC.of_spineHargsK-->     SpineHargsC D K env e₁
                     --spineHargsN_of_spineHargsC-->     SpineHargsN = the field

`b` is universally quantified: **this is the not-pinned verdict as a statement.**  The obligation
holds for *every* inhabitant of the result sort, so no particular companion value is required of it
— which is exactly what rows 235/235b found false for obligations (B)/(C), where `WFD.val` fixed
the value to `R.ctorVal` / `R.recVal`. -/

namespace VIndRestore

/-- **THE CHECKER-SIDE CLAUSE, IN GENERAL, HOLE-FREE.**  `StrengthenFamily.lean`'s bypass composed
with `RestrictStep.lean`'s arrow 1 → 2 and `SpineClause.lean` §3's arrow back to the checker-side
form.

*Why the weaker premise and not the general strengthening statement* (recorded at the statement, as
six rounds running have): `VEnv.AxiomConservativityWF` is forbidden here and would in any case cost
`weakN_iff`; `ResultSortInhab` is what the bypass actually needs, and it is a statement about the
block's own result sort with no `IsDefEqU` in it. -/
theorem spineHargsC_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b) : R.SpineHargsC D K env e₁ :=
  .of_spineHargsK C.built (cyc_datum_to_spine (argsTypedK_of_resultSortInhab C H₂ hb).2)

/-- **THE FIELD, IN GENERAL, HOLE-FREE.**  `SpineHargsN` is the `trSpine` field text; the staging
premise is discharged by `C.stage₁`, since `addIndTypesC` is a function and so pins the field's
universally quantified `env₁` to the configuration's `e₁`.

`hcomp` is `TrIndDeclN.companions`, so at a construction site it is free. -/
theorem spineHargsN_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types := by
  refine spineHargsN_of_spineHargsC hcomp fun e h₁ => ?_
  cases Option.some.inj (h₁.symm.trans C.stage₁)
  exact spineHargsC_of_resultSortInhab C H₂ hb

/-- **…AND THE FIELD TEXT SPELLED OUT**, exactly as `Verify/Environment/InductR.lean` writes it
(`declTele` is an `abbrev` that file does not import, so it splits `splitPis` by hand).  This is the
term a `TrIndDeclN` construction site supplies for `trSpine`; that it is the *same statement* as
`SpineHargsN` is `rfl`, which is what the absence of any rewriting below records. -/
theorem trSpine_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
        ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
          env₁.HasArgs D.uvars D.params.reverse
            (VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j) :=
  spineHargsN_of_resultSortInhab C H₂ hb hcomp

end VIndRestore

/-! ## §2 The successor-level form: the shape every non-`Prop` block Lean emits has

`StrengthenFamily.lean` §4a's first clause, so the premise is a **level** condition and not an
environment one.  This matters: `Verify/Inductive/SortWitEnv.lean` refutes the environment
condition that §4a's *fourth* clause needs (`not_sortWitness_of_restrictStepCfg₃`, at all three of
`env`, `e₂`, `e₁`), and that refutation is silent about this clause. -/

namespace VIndRestore

/-- **THE FIELD FROM THE BLOCK'S RESULT LEVEL ALONE.**  No environment condition, no `weakN_iff`,
no `AxiomConservativityWF`. -/
theorem spineHargsN_of_succLevel {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {v : VLevel}
    {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hv : v.WF D.uvars) (hlv : D.lvl.WF D.uvars) (heq : VLevel.succ v ≈ D.lvl)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types :=
  spineHargsN_of_resultSortInhab C H₂ (VInductDecl'.resultSortInhab_of_succ hv hlv heq) hcomp

/-- …and the zero-level companion clause, for completeness: a `Prop`-valued block. -/
theorem spineHargsN_of_zeroLevel {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hlv : D.lvl.WF D.uvars) (heq : VLevel.imax (.succ .zero) .zero ≈ D.lvl)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types :=
  spineHargsN_of_resultSortInhab C H₂ (VInductDecl'.resultSortInhab_of_zero hlv heq) hcomp

/-- **THE SMALLEST SUFFICIENT PREMISE, AS AN `↔`.**  `ValAtParam.lean` §6's equivalence lifted to
the field text: the field is *equivalent* to the strengthening instance at the configuration, so
`ResultSortInhab` is sufficient and the field is no weaker than what the bypass discharges.  Both
directions are hole-free; neither uses `AxiomConservativityWF` — the `↔` is transported, not
derived from the hole. -/
theorem spineHargsN_iff_valStrengthen {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types ↔ R.ValStrengthen D K e₂ e₁ := by
  refine ⟨fun h => (spineHargsC_iff_valStrengthen C H₂).1
      (spineHargsC_of_spineHargsN hcomp C.stage₁ h), fun h => ?_⟩
  refine spineHargsN_of_spineHargsC hcomp fun e h₁ => ?_
  cases Option.some.inj (h₁.symm.trans C.stage₁)
  exact (spineHargsC_iff_valStrengthen C H₂).2 h

end VIndRestore

/-! ## §2b The field is no longer an obligation at a construction site

Bookkeeping, and said to be bookkeeping: the hypothesis is *exactly* "every field but `trSpine`",
so the theorem says no more than that §2 supplies the missing one.  It is here because it is the
shape a `TrIndDeclN` construction site uses, and because it makes the identification of the field
with `SpineHargsN` checkable **in this file** rather than by reading `InductR.lean` — the reverse
direction being `SpineClosedLand.lean`'s `TrIndDeclN.spineHargsN`, which is `h.trSpine` on the
nose. -/

/-- **`trSpine` DISCHARGED AT A CONSTRUCTION SITE**, from the configuration and the block's result
level.  Everything else the site already had. -/
theorem trIndDeclN_of_succLevel {env e₂ e₁ : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List Lean.InductiveType} {iu : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} {occ : Nat → VNestedOcc} {v : VLevel}
    (hrest : R.SpineHargsN D K env types →
      TrIndDeclN env Us nparams types iu numNested D K R)
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hv : v.WF D.uvars) (hlv : D.lvl.WF D.uvars) (heq : VLevel.succ v ≈ D.lvl)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    TrIndDeclN env Us nparams types iu numNested D K R :=
  hrest (VIndRestore.spineHargsN_of_succLevel C H₂ hv hlv heq hcomp)

/-- …and the round trip, so that "the field *is* `SpineHargsN`" is machine-checked here and will
break loudly if `InductR.lean`'s field text ever drifts from `SpineClause.lean` §5's definition. -/
example {env : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List Lean.InductiveType} {iu : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} (h : TrIndDeclN env Us nparams types iu numNested D K R) :
    R.SpineHargsN D K env types := h.trSpine

/-! ## §3 The witness: `ntreeAux`, arity 0, existentially closed, general route only

`ntreeAux` is `NTree α` with a `List (NTree α)` field — `np = 1`, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `lvl = .succ (.param 0)`, the block Lean's own kernel runs
the nested elimination on.  Deliberately **not** `nfnAux`, which is degenerate (`uvars = 0`,
`params = []`); the contrast is checked below.

Everything block-specific here is *configuration data* (`ntreeAux_restrictStepCfg`, the datum at
`e₂` from `D.WF`, `ntreeAux_companions`); the route to the conclusion is §2's general theorem and
nothing else.  In particular this does **not** go through `ntreeAux_datum_at_stage₁` /
`ntreeAux_spineHargsC`, which is `ValAtParam.lean`'s concrete-spine route. -/

namespace InductiveDeclExamples

/-- **THE FIELD AT THE PARAMETERISED NESTED BLOCK, THROUGH THE GENERAL PRODUCER, NOTHING
HYPOTHESISED.**  Compare `ValAtParam.lean` §4's `ntreeAux_spineHargsN`, which reaches the same
conclusion from the datum measured at stage 1: here the only inputs are the configuration, `D.WF`,
and the block's **result level**. -/
theorem ntreeAux_trSpine :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, h, VIndRestore.spineHargsN_of_succLevel (ntreeAux_restrictStepCfg h h₂ h₃)
    (ntreeAux_argsTypedK_of_wf h₂) (v := .param 0) (by decide) (by decide) (.refl _)
    ntreeAux_companions⟩

/-- **THE NOT-PINNED VERDICT, INSTANTIATED.**  The field holds at a configuration whose companion
substitution carries the **junk** value `λ (α : Type u), Sort u`, which
`StrengthenFamily.lean`'s `ntree_junkVal_ne_tyVal` proves is *not* the intended `ntreeVal`
(`λ (α : Type u), List.{u} (NTree.{u} α)`).  An obligation that pinned the value — rows 235/235b's
(B)/(C), where `WFD.val` fixes it to `R.ctorVal` / `R.recVal` — could not be discharged from this
data; this one is. -/
theorem ntreeAux_trSpine_not_pinned :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeAux.CompanionVals ntreeK env₂ env₃ (ntreeAux.junkSubst ntreeK ntreeJunk) ∧
      ntreeAux.junkVal ntreeJunk (ntreeAux.types.getD 1 default) ≠ ntreeVal ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  have C := ntreeAux_restrictStepCfg h h₂ h₃
  exact ⟨env₁, env₂, env₃, h, h₃,
    ntreeAux.companionVals_junk C ntreeAux_resultSortInhab, ntree_junkVal_ne_tyVal,
    VIndRestore.spineHargsN_of_succLevel C (ntreeAux_argsTypedK_of_wf h₂)
      (v := .param 0) (by decide) (by decide) (.refl _) ntreeAux_companions⟩

/-- …and the `↔` at the witness, so §2's equivalence is not a statement about an empty
configuration class. -/
theorem ntreeAux_trSpine_iff_valStrengthen :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      (ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] ↔
        ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, env₂, env₃, h, VIndRestore.spineHargsN_iff_valStrengthen
    (ntreeAux_restrictStepCfg h h₂ h₃) (ntreeAux_argsTypedK_of_wf h₂) ntreeAux_companions⟩

/-! ### §3a Non-degeneracy, by computation

`docs/vacuity-ledger.md` §0: hole-freeness is §5, this is the other question.  The four facts that
stop this witness from being `nfnAux` under another name, plus the collapse test. -/

/-- One universe parameter. -/
example : ntreeAux.uvars = 1 := rfl
/-- The parameter telescope is not empty, so the parameter-context conditions are not `trivial`. -/
example : ntreeAux.params = [.sort (.succ (.param 0))] := rfl
/-- The presented spine is **parameter-dependent**, so the `HasArgs` is a genuine `.cons`. -/
example : ntreeRestore.tyArgs 1 = [.app (.const ``NTree [.param 0]) (.bvar 0)] := rfl
/-- `ntreeK ≠ []`, so `SpineClause.lean` §6's collapse (`spineHargsC_nil`) does not apply and the
conclusion is not vacuously true — i.e. this really is the `numNested > 0` case. -/
example : ntreeK = [`_nested.List_1] := rfl
/-- The result level is a successor, which is what §2's clause fires on. -/
example : ntreeAux.lvl = .succ (.param 0) := rfl
/-- And for contrast, the block this file is **not** using. -/
example : nfnAux.uvars = 0 ∧ nfnAux.params = [] := ⟨rfl, rfl⟩

end InductiveDeclExamples

end Lean4Lean

/-! ## §4 What the producer still misses, and it is `StrengthenFamily.lean` §8's residue verbatim

Two premises are *not* discharged in general by anything here, and neither is new:

1. **`ResultSortInhab`** — sufficient, and covered by four clauses (`_of_succ`, `_of_zero`,
   `_of_lookup`, `_of_const`).  The residue is a block whose `D.lvl` is `.param i`, with **no**
   telescope binder at that level, in an environment with **no** `Sort u`-valued constant.
   `Verify/Inductive/SortWitEnv.lean` shows the last conjunct is not idle: the fourth clause's
   environment condition is *refuted* at the environments this corner runs at.  For such a block
   the producer above does not fire, and §2's `↔` says its cost is then exactly the strengthening
   instance — i.e. `weakN_iff`.
2. **`D.ArgsTypedK K e₂ occ`, the datum at `e₂`** — taken as a premise, as
   `RestrictStep.lean` §4(c) records: `D.WF` + `stage₂` is where it comes from
   (`VInductDecl'.WF.recField_canonResult` is the general extraction), but the last step from that
   clause to `ArgsTypedH` is per-occurrence telescope arithmetic and exists in the tree only at the
   two witnesses (`listOcc_argsTypedH_of_wf`, `pfnOcc_argsTypedH_of_wf`).  Not this file's corner,
   and flagged rather than assumed away.

**Not circular, and that is checked upstream rather than asserted here.**  `RestrictStep.lean`
§4(b) audits the configuration field by field and finds **none of the nine is a typing at `e₁`**:
`ordered`/`ordered₁` are `VEnv` well-formedness, `stage₂`/`stage₁` the two `addConstList`
equations, `fresh`/`closed` syntactic facts about `csubstTy`, `lvls` a level condition, `built` ten
clauses of names/members/`OccursN`/`OwnId`/`Nodup`/`KFresh`, and `wf` is `D.WF env` at the
**pre-block** environment.  So the premise set is not `SpineHargsN` in disguise — the field is a
`HasArgs` at `e₁`, and nothing in the premises is one.

Also not claimed: that `ResultSortInhab` is *necessary* for the field (it is not proved to be), and
nothing about `Built` / `FreshIn` / `tyLvls`-WF (`RestoreData` business) or `Faithful`
(`RestoreFaithful.lean`'s job), which are the flip's other remaining items. -/

/-! ## §5 Grading: hole-freeness, per declaration -/

#print axioms Lean4Lean.VIndRestore.spineHargsC_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.trSpine_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_succLevel
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_zeroLevel
#print axioms Lean4Lean.VIndRestore.spineHargsN_iff_valStrengthen
#print axioms Lean4Lean.trIndDeclN_of_succLevel
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_not_pinned
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_iff_valStrengthen
