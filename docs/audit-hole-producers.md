# Audit: does a producer already exist for each remaining hole?

Round purpose: twice in two days, content in this tree was reported absent when it existed
*and was citable*. This audit asks, systematically, for every remaining hole: **is there already
something in the tree that produces it, or materially shrinks it, and can the hole's own module
cite it?**

Census baseline: `HOLES 13` (10 machinery + 3 targets), verified by the orchestrator today.

This file is written by an audit stream that writes **no Lean**. Nothing here is applied.

## §0 Verdict table

### §0.a PRIORS (written before any measurement; never revised — misses recorded in §4)

| # | hole | prior: producer? | prior reasoning |
|---|------|------------------|-----------------|
| 1 | `Lean4Lean.TrProj.weak'_inv` | PARTIAL | HEAD commit says "TrProj.weak'_inv reduced -- both residuals bounded", so a reducing lemma should already exist |
| 2 | `Lean4Lean.TypeChecker.Inner.inferProj.WF` | NONE | expect it to be gated on #1, not on a missing local lemma |
| 3 | `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` | NONE (vacuity plausible) | brief says vacuous until the flip; I half-expect the vacuity claim to be wrong |
| 4 | `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` | NONE (vacuity plausible) | same |
| 5 | `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | PARTIAL | `Theory/Typing/Injectivity.lean` already carries stratified machinery; expect an un-stratified or one-level sibling |
| 6 | `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | PARTIAL | two dedicated scripts (`weakn-gate-split.lean`, `weakn-residual-map.lean`) imply a mapped-out residual, i.e. partial producer |
| 7 | `Lean4Lean.VEnv.NormalEq.descend` | stream active (known FALSE) | citability question only |
| 8 | `Lean4Lean.VEnv.WF.rigidShapeUniqNS` | PARTIAL, citable | `Verify/Typing/Rigidity.lean` + HEAD "rigidity flips" suggests a non-NS or single-shape version exists |
| 9 | `Lean4Lean.VIndRecArg.exists_indep` | stream active | citability question only |
| 10 | `Lean4Lean.addDecl.WF` | stream active | citability question only |

Prior tally: 0 full producers, 4 partial, 3 none, 3 not-my-business.

### §0.b MEASURED

(filled in below as each measurement lands)

Census re-run by this stream today (`lake env lean scripts/sorry-census.lean`): **13**, matching
the orchestrator. Transitive-user counts, which reorder everything below:

    forallE_inv_stratified 742 · rigidShapeUniqNS 461 · weakN_iff 311 · NormalEq.descend 200
    TrProj.weak'_inv 90 · tryEtaStructCore.WF 71 · inferProj.WF 70 · isDefEqUnitLike.WF 70
    addDecl.WF 8 · exists_indep 0 · kernel_sound 0 · kernel_complete 0 · equiconsistency 0

## §M Measurement log (appended in order; raw)

### M1 — batch `exists.lean`, 462-module population

| name | module | arity | cone | holes in cone |
|---|---|---|---|---|
| `Lean4Lean.VEnv.ConstAppTypeStrengthen` | `Verify.Typing.ProjWeakInv` | 2 | 619 | none (def) |
| `Lean4Lean.VEnv.ConstAppDefeqStrengthen` | `Verify.Typing.ProjWeakInvSplit` | 2 | 620 | none (def) |
| `Lean4Lean.VEnv.TypingStrengthening` | `Theory.Typing.GateBodyDescend` | 2 | 157 | none (def) |
| `Lean4Lean.VEnv.Strengthening` | `Theory.Typing.Strengthen` | 2 | 156 | none (def) |
| `Lean4Lean.VEnv.StrengtheningTarget` | `Theory.Typing.Strengthen` | 2 | 156 | none (def); WATCHED |
| `Lean4Lean.VEnv.PiDescend` | `Theory.Typing.GateBodyDescend` | 2 | 157 | none (def) |
| `Lean4Lean.VEnv.TransStrengtheningNarrow` | `Theory.Typing.StrengthenNarrow` | 2 | 194 | none (def) |
| `Lean4Lean.VEnv.StrengtheningTarget.iff_piDescend_narrow` | `Theory.Typing.StrengthenNarrow` | 3 | 3699 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.VEnv.ConstRigid` | `Verify.Typing.Rigidity` | 1 | 411 | none (def) |
| `Lean4Lean.VEnv.ConstRigidPat` | `Verify.Typing.Rigidity` | 1 | 63 | none (def) |
| `Lean4Lean.VEnv.WeakNorm` | `Verify.Typing.ConstSpine` | 1 | 38 | none (def) |
| `Lean4Lean.VEnv.PiInv` | `Theory.Typing.Injectivity` | 2 | 31 | none (def) |
| `Lean4Lean.VEnv.PiInvStrat` | `Theory.Typing.Injectivity` | 2 | 34 | none (def) |
| `Lean4Lean.VEnv.SortUniq` | `Theory.Typing.SortUniq` | 2 | 583 | none (def) |
| `Lean4Lean.VEnv.RigidShapeUniqNS` | `Theory.Typing.Injectivity` | 2 | 622 | none (def) |
| `Lean4Lean.VEnv.RigidPiUniq` | `Theory.Typing.Injectivity` | 2 | 30 | none (def) |
| `Lean4Lean.VEnv.AllTypesInhabited` | `Verify.Typing.ProjInhab` | 2 | 29 | none (def) |
| `Lean4Lean.VEnv.ConstAppDefeqStrengthenRF` | `Verify.Typing.ProjWeakInvSplit` | 2 | 629 | none (def) |
| `Lean4Lean.VEnv.ConstAppTypeStrengthenStruct` | `Verify.Typing.ProjWeakInvSplit` | 2 | 623 | none (def) |
| `Lean4Lean.VEnv.ConstAppSkipUninhab` | `Verify.Typing.ProjWeakInv` | 2 | 606 | none (def) |
| `Lean4Lean.VEnv.ConstAppDefeqStrengthenInh` | `Verify.Typing.ProjWeakInvSplit` | 2 | 620 | none (def) |

All of these are `def`s of `Prop`s — as `exists.lean` warns, their cone size says nothing about
satisfiability. Recorded so later rows can be read against them.

**First substantive reading of M1:** `iff_piDescend_narrow` (cone 3699) carries holes
`{forallE_inv_stratified, rigidShapeUniqNS}` and **not** `weakN_iff` itself — so hole #6's
reduction to `PiDescend ∧ TransStrengtheningNarrow` is genuinely available and not circular,
confirming `UniqueTyping.lean`'s in-file comment.

### M2 — the three `TypeChecker` holes have named, hole-free, same-file vacuity producers

Measured (`exists.lean`, 464-module population):

| producer | module | arity | cone | `sorryAx` in cone |
|---|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.inferProj_always_throws` | `Verify.TypeChecker.InferType` | 9 | 6973 | **no** |
| `Lean4Lean.TypeChecker.Inner.tryEtaStructCore_never_true` | `Verify.TypeChecker.IsDefEq` | 6 | 6794 | **no** |
| `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike_never_true` | `Verify.TypeChecker.IsDefEq` | 6 | 6522 | **no** |

Each lives in the **same module** as the hole it would close, above it, so citability is trivially
YES for all three. The non-vacuous siblings, for contrast:

| non-vacuous sibling | arity | cone | holes carried |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF_of_structEta` | 10 | 12462 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF_of_structEta` | 10 | 10957 | same four |

So **#2, #3 and #4 are all in the same vacuous-until-the-flip class**, and #2 is not the exception
the brief expected (see §4).

### M3 — `TrProj.weak'_inv` (#1): five conditional producers, all downstream, all holier

| name | module | arity | cone | holes carried |
|---|---|---|---|---|
| `Lean4Lean.TrProj.weak'_inv` (the hole) | `Verify.Typing.Lemmas` | 13 | 90 | itself |
| `Lean4Lean.TrProj.weak'_inv_of_strengthen` | `Verify.Typing.ProjWeakInv` | 14 | 3698 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.TrProj.weak'_inv_of_strengthen_onCtx` | `Verify.Typing.ProjWeakInv` | 15 | 3665 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.TrProj.weak'_inv_of_typing_head` | `Verify.Typing.ProjWeakInvSplit` | 15 | 3716 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.TrProj.weak'_inv_of_structStrengthen` | `Verify.Typing.ProjWeakInvSplit` | 15 | 3665 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.TrProj.weak'_inv_of_constRigid` | `Verify.Typing.ProjWeakInvSplit` | 14 | 5804 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |

Every one of these is *conditional* — it takes the strengthening statement as an explicit
hypothesis — so none discharges the hole, and the cone comparison (90 vs 3665+) says that even a
successful migration would **enlarge** this hole's cone and pull #5 and #8 into it. Sole consumer
`Lean4Lean.TrExprS.weakFV'_inv` (arity 16, cone 8641) already carries all five machinery holes.

### M4 — the `Injectivity` circle is real: #5's cheap producers are circular, measured

| name | arity | cone | holes carried | reading |
|---|---|---|---|---|
| `Lean4Lean.VEnv.piInvStrat_axiom` | 3 | — | the hole | *is* hole #5, repackaged |
| `Lean4Lean.VEnv.WF.sortUniq'` | 3 | 3441 | `forallE_inv_stratified` | `SortUniq` from `VEnv.WF` — but through #5 |
| `Lean4Lean.VEnv.piInv_axiom` | 3 | 3576 | `forallE_inv_stratified`, `rigidShapeUniqNS` | `PiInv`, through #5 and #8 |
| `Lean4Lean.VEnv.piInvStrat_of` | 5 | 3253 | **none** | #5 ⟸ `SortUniq ∧ PiInv`, hole-free |
| `Lean4Lean.VEnv.sortUniq_of_piInvStrat` | 4 | — | none | `SortUniq` ⟸ #5 |
| `Lean4Lean.VEnv.RigidShapeUniqNS.piInv` | 6 | 3479 | **none** | `PiInv` ⟸ #8 |
| `Lean4Lean.VEnv.piInv_of_propAgreeOn` | 5 | 3453 | **none** | `PiInv` ⟸ `WF ∧ PropAgreeOn ∧ #8`, no `SortUniq` |
| `Lean4Lean.VEnv.piInvStrat_of_propAgreeOn` | 6 | 3547 | **none** | #5 ⟸ `PropAgreeOn ∧ ConvStep2 ∧ ShapeMidShapeless` |

So `#5 ⟸ SortUniq ∧ PiInv` and `SortUniq ⟸ #5` — the only in-tree producer of `SortUniq` from
`VEnv.WF` alone (`WF.sortUniq'`) routes through #5 itself. `ConvStep2 ⟸ SortUniq`
(`convStep2_of_sortUniq`), and `ShapeMidShapeless` is stated in-tree as **equivalent** to the
target (`InjOneFact.shapeMidShapeless_iff`), so `piInvStrat_of_propAgreeOn` is not a route either.
No non-circular producer of #5 exists in the tree.

### M5 — `PropAgreeOn` (the one genuinely independent ingredient) and its own gate

`Lean4Lean.VEnv.PropAgreeOn` (`Theory.Typing.SortInvIndep`, cone 578) and
`Lean4Lean.VEnv.PropTypeAgreeOnCtx` (`Theory.SetModel.PropSplitAudit`, cone 578) are the same
`Prop` under two names, in the same `VEnv` namespace, in two modules on opposite sides of the
`Theory/Typing` → `Theory/SetModel` layer edge.

`Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (arity 4, cone 2703,
**`sorryAx`-free**) produces it — from `VEnv.Ordered env`, `∀ n, env.PropTypeAgreeN 0 n` and
`∀ n, env.PropUniqN 0 n`. Both `∀ n` hypotheses are open targets of `Theory/Typing/PropConv.lean`
and `PropShadow.lean`; the file itself records that they hold **only at index 0** unconditionally
(`propUniqN_zero`, `propTypeAgreeN_zero`) and that this does *not* discharge the `∀ n` form.
So: a real near-miss with a precisely stated missing hypothesis, not a producer.

### M6 — citability (`scripts/can-cite.py`) and the layer facts

`python3 scripts/layer-check.py`: 11 of 281 `Theory` modules are transitively downstream of
`Verify/` (`CRSEScope`, `CommutationLemmas`, `ConfluenceRebuildPrice`, `ConstAppInvSIProof`,
`EtaGuardLand`, `EtaOrient`, `NoConfRepair`, `ParamsStruct`, `SEReduce`, `SEReerectionScope`,
`StructEtaPrice`). **None** of `Injectivity`, `UniqueTyping`, `ChurchRosser`,
`Inductive/Decl` is among them, so no `Theory→Verify` citation is available to any of the
five Theory holes.

| consumer (hole's module) | declaration | verdict |
|---|---|---|
| `Verify.TypeChecker.InferType` | `TypeChecker.Inner.inferProj_always_throws` | **YES** (same module) |
| `Verify.TypeChecker.IsDefEq` | `TypeChecker.Inner.tryEtaStructCore_never_true` | **YES** (same module) |
| `Verify.TypeChecker.IsDefEq` | `TypeChecker.Inner.isDefEqUnitLike_never_true` | **YES** (same module) |
| `Verify.Typing.Lemmas` | `TrProj.weak'_inv_of_typing_head` | NO — `ProjWeakInvSplit` imports `Lemmas` |
| `Verify.Typing.Lemmas` | `TrProj.weak'_inv_of_strengthen_onCtx` | NO — `ProjWeakInv` imports `Lemmas` |
| `Theory.Typing.Injectivity` | `VEnv.piInvStrat_of_propAgreeOn` | NO — `ForallInvPrice` imports `Injectivity` |
| `Theory.Typing.Injectivity` | `VEnv.piInv_of_propAgreeOn` | NO — `SortInvIndep` imports `Injectivity` |
| `Theory.Typing.Injectivity` | `VEnv.rigidShapeUniqNS_of_constSpine` | NO — `PiInvResidual` imports `Injectivity` |
| `Theory.Typing.Injectivity` | `VEnv.RigidShapeVUniqNS.rigidShapeUniqNS` | NO — `ShapeVar` imports `Injectivity` |
| `Theory.Typing.Injectivity` | `VEnv.rigidShapeUniqNS_of_sortPiDisjUC` | NO — `SortPiDisjPrice` imports `Injectivity` |
| `Theory.Typing.Injectivity` | `SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` | NO — `SetModel` is downstream of all `Theory/Typing` |
| `Theory.Typing.UniqueTyping` | `VEnv.StrengtheningTarget.iff_piDescend_narrow` | NO — `StrengthenNarrow` imports `UniqueTyping` |
| `Theory.Typing.UniqueTyping` | `VEnv.StrengtheningTarget.iff_piDescend_of_normalEqComplete` | NO — `NormalEqStrengthen` imports `UniqueTyping` |
| `Theory.Typing.UniqueTyping` | `VEnv.TypingStrengthening.piDescend` | **YES** — `GateBodyDescend` is upstream |
| `Theory.Typing.ChurchRosser` | `Lean4Lean.not_descendStatement` | NO — `DescendRefute` imports `ChurchRosser` |
| `Theory.Typing.ChurchRosser` | `Lean4Lean.descend_uniq_sortUniq_not_all` | NO — same |
| `Theory.Inductive.Decl` | `VIndRecArg.indepGoalPair_of_bindersIndep` | NO — `RecArgIndep` imports `Decl` |
| `Theory.Inductive.Decl` | `VIndRecArg.indepGoal_of_bindersIndep` | NO — same |
| `Verify.Environment` | `Lean4Lean.addDecl.WF_honest` | NO — `Verify.Inductive.AddDeclWF` imports `Environment` |

Every NO here is **genuinely blocked, not a migration**: in each case the producer's module
imports the hole's module (checked directly on the import closures, not inferred from the
`can-cite` message). The single YES that is not a same-module vacuity witness,
`VEnv.TypingStrengthening.piDescend`, runs the wrong way (it *consumes* the strengthening
statement to produce `PiDescend`).

### M7 — hole cones, re-measured today

| hole | arity | own cone | holes in its cone |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | 16 | 48 | itself |
| `Lean4Lean.VEnv.WF.rigidShapeUniqNS` | 3 | 630 | itself |
| `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | 11 | 3231 | itself |
| `Lean4Lean.VEnv.NormalEq.descend` | 12 | 3874 | itself, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `Lean4Lean.VIndRecArg.exists_indep` | 18 | 851 | itself |
| `Lean4Lean.TrProj.weak'_inv` | 13 | 90 | itself |
| `Lean4Lean.addDecl.WF` | 5 | 20365 | itself + 8: `TrProj.weak'_inv`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`, `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend`, `inferProj.WF` |
| `Lean4Lean.kernel_sound` | 6 | 7915 | **itself only** |

`VIndRecArg.exists_indep` is **not** in `addDecl.WF`'s cone.

### M8 — the three one-line closes, elaborated (MCP `lean_run_code`, nothing written to the repo)

All three compile today, warnings only (unused binders):

* `inferProj.WF … := inferProj_always_throws hty`
* `tryEtaStructCore.WF … := (tryEtaStructCore_never_true he₂).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun`
* `isDefEqUnitLike.WF … := (isDefEqUnitLike_never_true he₁).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun`

This is a measurement of my own, not a repetition of the docstrings' claim.

---

## §0.b Verdict table (measured)

| # | hole | statement, one line | producer found | citable | next action |
|---|------|---------------------|----------------|---------|-------------|
| 1 | `Lean4Lean.TrProj.weak'_inv` | a `TrProj` of a lifted subject descends to a `TrProj` one context down | 7, all **conditional**; the sharpest is `TrProj.weak'_inv_of_projDataStrengthen` (cone 717, **hole-free**), whose hypothesis `VEnv.ProjDataStrengthen` is proved **equivalent** to the hole — see §M9 | **NO** (all downstream of `Verify/Typing/Lemmas`) | attack `VEnv.ProjDataStrengthen`; ignore the #5/#8 route |
| 2 | `TypeChecker.Inner.inferProj.WF` | `inferProj` returns a type with a `TrTyping` for `.proj` | `TypeChecker.Inner.inferProj_always_throws`, same module, cone 6973, **hole-free** | **YES** | orchestrator decision: close vacuously (13→12) or keep the marker |
| 3 | `TypeChecker.Inner.isDefEqUnitLike.WF` | `isDefEqUnitLike = true → IsDefEqU` | `TypeChecker.Inner.isDefEqUnitLike_never_true`, same module, cone 6522, **hole-free** | **YES** | same decision |
| 4 | `TypeChecker.Inner.tryEtaStructCore.WF` | `tryEtaStructCore = true → IsDefEqU` | `TypeChecker.Inner.tryEtaStructCore_never_true`, same module, cone 6794, **hole-free** | **YES** | same decision |
| 5 | `VEnv.IsDefEqU.forallE_inv_stratified` | Π-injectivity with stratified typings on both conjuncts | **NONE non-circular** (`piInvStrat_of` is hole-free but needs `SortUniq`, whose only `WF`-only producer routes through this hole) | n/a | genuinely open; see §3.1 |
| 6 | `VEnv.IsDefEqU.weakN_iff` | conversion between two lifts descends to the smaller context | **NONE** (`iff_piDescend_narrow` restates, does not produce) | NO (downstream) | genuinely open; see §3.2 |
| 7 | `VEnv.NormalEq.descend` | — | stream active; **known FALSE**, refutation in `Theory/Typing/DescendRefute.lean` | **NO** — `DescendRefute` imports `ChurchRosser` | stream active |
| 8 | `VEnv.WF.rigidShapeUniqNS` | 8 of the 9 rigid-shape-uniqueness entries at every `VEnv.WF` env | **NONE non-circular**; every producer's hypothesis is proved *equivalent* to it in-tree | n/a | genuinely open; see §3.3 |
| 9 | `VIndRecArg.exists_indep` | — | stream active; `Theory/Inductive/RecArgIndep.lean` prices it | **NO** — `RecArgIndep` imports `Decl` | stream active |
| 10 | `Lean4Lean.addDecl.WF` | — | stream active; `addDecl.WF_honest` is the honest replacement | **NO** — `Verify/Inductive/AddDeclWF` imports `Environment` | stream active; **statement FALSE as written** (machine-checked in-tree) |

**Count.** Of the ten machinery holes: **3** have an existing producer that is citable
(#2, #3, #4 — all vacuity witnesses, all verified by me to elaborate); **0** need only a
migration; **5** are genuinely open (#1, #5, #6, #8, #9); **1** is known false (#7); **1** is
false as written (#10). Five of the ten are therefore false, vacuous, or false-as-written —
which is the single most useful number in this file.

---

## §1 The actionable ones, ranked

Ranked by (information gained) ÷ (risk), which puts all three vacuity closes together at the
top and leaves nothing else in this section. **I have applied none of these.**

### 1.1 `TypeChecker.Inner.tryEtaStructCore.WF` (#4) — one line, same file, verified

File `Lean4Lean/Verify/TypeChecker/IsDefEq.lean`. Replace the `:= sorry` on the declaration
that currently reads (docstring unchanged):

    theorem tryEtaStructCore.WF {c : VContext} {s : VState}
        (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
        RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
      (tryEtaStructCore_never_true he₂).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun

`he₁` becomes unused, so it needs `_he₁` (or a `set_option linter.unusedVariables false`)
unless the binder is kept deliberately for the flip.

### 1.2 `TypeChecker.Inner.isDefEqUnitLike.WF` (#3) — one line, same file, verified

Same file. Replace its `:= sorry` with

    theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
        (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
        RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
      (isDefEqUnitLike_never_true he₁).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun

Here `he₂` becomes the unused one.

### 1.3 `TypeChecker.Inner.inferProj.WF` (#2) — one line, same file, verified

File `Lean4Lean/Verify/TypeChecker/InferType.lean`:

    theorem inferProj.WF
        (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
        (inferProj st i e ety).WF c s fun ty _ =>
          ∃ e'' ty'', c.TrTyping (.proj st i e) ty e'' ty'' :=
      inferProj_always_throws hty

`he` and `hasty` become unused.

### 1.4 The argument against applying 1.1–1.3, stated fairly

Each close costs a census row and buys nothing mathematical: the vacuity witnesses are
**already landed and already go red at the flip**, so the tripwire exists either way (this is
`InferType.lean`'s own argument, and I re-measured its premise: all three witnesses are in the
built environment and `sorryAx`-free). The one asymmetry I did find and the docstrings do not
state in these terms: **#2's statement is asserted false once the branch is live** (`inferProj`
never checks recursiveness, `IsStructure.noRec` demands `C.recFields = []`, `bugs-found.md`
item 10), whereas #3 and #4 are merely un-provable-non-vacuously, not false. So if any of the
three is closed, #2 is the one where the `sorry` is carrying real information — closing it
would replace a "this is open" marker with a "this is proved" claim about a statement the tree
elsewhere argues is false. My recommendation: **close #3 and #4, leave #2 open**, or leave all
three; do not close #2 alone.

---

## §2 Near-misses — the exact extra hypothesis, and whether it is available

### 2.1 #1 `TrProj.weak'_inv` ⟸ `TypingStrengthening ∧ ConstAppDefeqStrengthen`

`Lean4Lean.TrProj.weak'_inv_of_typing_head` (arity 15, cone 3716) proves the hole's exact
statement from those two. `VEnv.TypingStrengthening` is the typing half of hole #6;
`VEnv.ConstAppDefeqStrengthen` (a `c`-spine definitionally equal to a lift is definitionally a
`c`-spine one context down) has **no producer** except from `VEnv.ConstRigid` at a
`VEnv.Params` environment, and `ConstRigid`'s only producer needs `VEnv.WeakNorm`, which
`Verify/Typing/WeakNormRefute.lean` **refutes**. Availability: neither hypothesis is available.
Extra fact worth not rediscovering: `VEnv.AllTypesInhabited.constAppDefeqStrengthen` discharges
the second at an all-types-inhabited environment — i.e. at an inconsistent one, which is why it
is a satisfiability witness and not a route.

### 2.2 #5 `forallE_inv_stratified` ⟸ `PropAgreeOn ∧ ConvStep2 ∧ ShapeMidShapeless`

`Lean4Lean.VEnv.piInvStrat_of_propAgreeOn` (arity 6, cone 3547, **hole-free**). Of the three:
`ConvStep2` follows from `SortUniq` (`convStep2_of_sortUniq`), which follows from the hole;
`ShapeMidShapeless` is stated in-tree as **equivalent** to the target
(`InjOneFact.shapeMidShapeless_iff`). Only `PropAgreeOn` is genuinely independent, and
`SortInvIndep.lean`'s own §-header proves it *cannot* deliver `SortUniq` (it gives
`u.eval ls = 0 ↔ u'.eval ls = 0`, never `u ≈ u'`). Availability: one of three, and the wrong one.

### 2.3 `PropAgreeOn` itself ⟸ `∀ n, PropTypeAgreeN 0 n` and `∀ n, PropUniqN 0 n`

`Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (arity 4, cone 2703,
**`sorryAx`-free**). The two `∀ n` hypotheses are the open targets of
`Theory/Typing/PropConv.lean` and `PropShadow.lean`; only their `n = 0` instances are theorems
(`propUniqN_zero`, `propTypeAgreeN_zero`). Availability: no. Note the citability wrinkle even
if they landed: the producer is in `Theory/SetModel`, which is downstream of every
`Theory/Typing` module, and `layer-check.py`'s HARD RULE forbids the reverse edge — so
consuming it from `Injectivity.lean` would require moving `propTypeAgreeOnCtx_of_stratifiedN`
up into `Theory/Typing`, which is possible only if its proof uses no model content (it uses
`stratifyN`, `PropTypeAgreeN`, `PropUniqN`, `equivZero_iff_eval_zero` — all `Theory/Typing`
names, so this migration looks feasible and is the one genuinely under-explored move I found).

### 2.4 #6 `weakN_iff` ⟸ `PiDescend ∧ TransStrengtheningNarrow`

`Lean4Lean.VEnv.StrengtheningTarget.iff_piDescend_narrow` (arity 3, cone 3699), whose holes are
`{forallE_inv_stratified, rigidShapeUniqNS}` and **not** `weakN_iff` — so the reduction is not
circular. Availability: `PiDescend` has no producer (`Theory/Typing/GateBodyDescend.lean`'s own
module docstring says so and measures it); `TransStrengtheningNarrow` follows from
`NormalEqComplete` (`TransStrengtheningNarrow.of_normalEqComplete`, cone 3752, holes #5 and #8),
and `NormalEqComplete` is confluence, whose in-tree route is `NormalEq.parRed` — refuted by
`ParRedPropRefute.lean` — or `NormalEq.descend` — hole #7, false.

### 2.5 #8 `rigidShapeUniqNS` ⟸ four different hypotheses, all measured equivalent to it

`rigidShapeUniqNS_of_sortPiDisjUC` (cone 3538) pairs with `sortPiDisjUC_of_rigidShapeUniqNS` to
give an explicit `↔` (`sortPiDisjUC_iff_rigidShapeUniqNS`); likewise
`constFamily_iff_rigidShapeUniqNS` and `rigidShapeUniqNS_iff_family`. `RigidShapeVUniqNS` and
`RigidShapeVSUniqNS` (arity-3 producers, cones 653/681, hole-free) are variable-restricted
forms — cheap-looking, and the cheapest thing in the tree that concludes #8, but I did not find
a producer for *them* either. Availability: none.

---

## §3 The genuinely open ones, as mathematical claims

### 3.1 #5 — what is actually missing

*A definitional equation between two Π-types, at two stratified typings of possibly different
indices, yields a domain conversion and a codomain conversion at a **common level**.* The
obstruction is level alignment: the conversion's level comes from the derivation being
inverted, the stratified derivation's level from the typing hypothesis, and nothing upstream of
`Injectivity.lean` pins them together. The tree's own reduction says this is exactly
`SortUniq ∧ PiInv`, and `SortUniq` — *a term's two sort-typings have equivalent levels* — has
no producer that does not route back through this hole. That is the mathematical content:
**universe uniqueness for Lean's type theory, at every well-formed environment, without
normalisation.** (`VEnv.SortUniq` unqualified over `env` is refuted —
`SortUniqDown.sortUniq_badEnv` — so the `VEnv.WF` guard is load-bearing.)

### 3.2 #6 — what is actually missing

*If two lifted terms are convertible in the larger context, they are convertible in the
smaller one.* Reduced in-tree to `PiDescend` — *a Π-type convertible with a lift has a
lift-shaped Π* — plus a `trans` residual restricted to middle terms that genuinely mention a
stripped variable. Both are statements about conversion with no derivation-level induction that
terminates: the `trans` case re-instantiates at the whole statement unless narrowed, and the
narrowing is what makes the residual real. The classical route is confluence, and both in-tree
confluence statements are refuted.

### 3.3 #8 — what is actually missing

*A well-typed non-proof is convertible with at most one rigid shape, up to `Compat`* — eight of
the nine shape pairs (the `sort`/`sort` pair is a theorem from `SortUniq`). The tree has
machine-checked that the shared type carries no information across differing shapes
(`UnivDiscrim.lean`: `.sort u` and `.forallE (.sort u) (.sort u)` both live at `.succ u`), so
the cheap route is exhausted rather than unfinished. What is missing is a **normalisation or
confluence argument** for the conversion relation — the same missing ingredient as #6 and #7.

### 3.4 #1 — what is actually missing

*A `c`-headed constant application definitionally equal to a lift is definitionally a
`c`-headed application in the smaller context* (`VEnv.ConstAppDefeqStrengthen`). Measured
in-tree to be genuinely separate from #6: `constAppDefeqStrengthen_rhs_not_skips` exhibits an
instance where the hypothesis holds and the right-hand side does not skip the stripped binder,
so no strengthening lemma that requires both endpoints to be lifts can reach it.

---

## §4 Corrections

### 4.1 To the brief

* **"#3 and #4 are vacuous until the flip" — CONFIRMED**, and I verified the one-line closes
  elaborate rather than trusting the docstrings. But the brief listed **#2 as a primary target**
  expecting a real attack; #2 is in the *same* vacuous class, with a hole-free same-module
  witness (`inferProj_always_throws`, cone 6973). That is the brief's one factual miss.
* **"Your primary targets are #1, #2, #5, #6, #8."** After measurement, #2 is bookkeeping, and
  #1 is not independent: its measured residual is #5 + #8 + one separate statement whose only
  route is refuted. The genuinely independent Theory holes are **#5, #6, #8**, and they share
  one missing ingredient (normalisation/confluence for the conversion relation).
* **"`Theory/Typing/` has a 10-module cluster transitively downstream of `Verify/` — check,
  don't assume."** Checked: it is **11** modules today, not 10, and **none of them is a hole's
  module**, so the cluster buys nothing for any of the five Theory holes.

### 4.2 To in-tree claims

* **`Verify/TypeChecker/InferType.lean` (`inferProj.WF` docstring), false as measured.** It says
  closing the hole takes "guard 2's hole set 9 → 8" and calls them "`kernel_sound`'s nine holes".
  `Lean4Lean.kernel_sound`'s own forward cone is **7915 constants containing exactly one hole —
  itself** (its value is `sorryAx`, so nothing downstream is reached). The nine-hole set is
  `Lean4Lean.addDecl.WF`'s cone (20365 constants, 9 holes). The number is right, the attribution
  is not, and the same docstring gets it right two bullets later ("It *is* on `addDecl.WF`'s
  cone"). Same error in `Verify/Typing/Lemmas.lean`'s Update 6, which states the correct version.
* **`Theory/Typing/DescendRefute.lean` module docstring, minor internal inconsistency.** Its
  prose says `NormalEq.descend` "carries **three** `sorry`s … **Three of the five** goals are
  false", and the sentence after the table says "The remaining two". Three of five and three of
  three cannot both be right; the table lists three witnesses, and the census counts `descend`
  as one hole. Cosmetic, but this file is cited as the authority on what is refuted.
* **`Theory/Typing/UniqueTyping.lean`'s `weakN_iff` comment is accurate** — I checked its two
  load-bearing claims. `iff_piDescend_narrow` really does carry only `{forallE_inv_stratified,
  rigidShapeUniqNS}` (measured cone 3699), so "not circular with `WF.rigidShapeUniqNS` /
  `IsDefEqU.forallE_inv_stratified`" is true in the intended sense (the *reduction* is
  hole-free of `weakN_iff`), though a reader could take it to mean the reduction avoids those
  two holes, which it does not.
* **`Verify/Typing/Lemmas.lean`'s `TrProj.weak'_inv` docstring (Updates 7–8) is accurate**, and
  the cone figures it quotes (3661/3628/3679) are within a few constants of what I measure today
  (3698/3665/3716) — drift from concurrent commits, not error.

### 4.3 A claim of my own I could not confirm either way

`Theory/Typing/SortInvIndep.lean` says `PropAgreeOn` and `SetModel/PropSplitAudit`'s
`PropTypeAgreeOnCtx` are definitionally identical, checked once in a scratch file. I did not
re-run that `Iff.rfl`; what I can report is that both are `Lean4Lean.VEnv`-namespace `Prop`s
with **identical cone size 578**, which is consistent with the claim and is not a proof of it.

---

## §5 What my method could have missed

1. **Producers whose conclusion is stated through a `def` that unfolds to the hole's shape.**
   `shape.lean` matches head constants in the *type*; a producer concluding
   `env.SomeWrapper U` where `SomeWrapper` unfolds to the hole's statement matches nothing.
   This tree does exactly that constantly (`PiInvStrat`, `RigidShapeUniqNS`, `StrengtheningTarget`
   are all such wrappers), so I searched by wrapper name as well — but only for wrappers I found
   by reading. **A wrapper nobody's docstring mentions is invisible to everything I ran.** How to
   find one: enumerate every `def _ : Prop` in `Theory/Typing` and `Verify/Typing` and check each
   for definitional equality with each hole's statement, mechanically.
2. **Structure fields.** `shape.lean` reports fields first and found **none** for any head I
   queried (0 fields on `RigidShapeUniqNS`, `PiInvStrat`, `PiDescend`). But I only ran three
   shape queries; #1's and #6's conclusion shapes I searched by name and by reading, not with
   `shape.lean`. The `VInductDecl'.WF.params` failure mode is therefore **not** excluded for
   #1 and #6. Running `HEADS="TrProj Ctx.Lift'"` and `HEADS="VEnv.IsDefEqU Ctx.LiftN"` would
   close that gap.
3. **`Experimental/`.** `exists.lean` and `shape.lean` both exclude `Lean4Lean.Experimental` (it
   is not in `defaultTargets`). A producer sitting there would read as absent everywhere in this
   file. `Experimental/Reflect/Capstone.lean` is named in `Injectivity.lean` as having tried and
   failed at exactly #5's pinning problem, so the exclusion is not idle.
4. **Unbuilt modules.** The population was 462–464 built modules across my runs (it grew during
   the round — four streams are committing). Anything not built at the moment of a run is absent
   from that run. The numbers in §M are therefore accurate to within one commit, not exactly.
5. **Conditional producers I priced by cone size.** "Cone 3665, holes {#5, #8}" says what a
   *proof* would drag in; it says nothing about whether the extra hypothesis is satisfiable. I
   used the in-tree anti-vacuity witnesses where they exist (`exists_univInhabEnv_*`,
   `hyp_inhabited_iff`, `rai_hyps_all`) rather than deriving satisfiability myself.
6. **I did not open #7's, #9's or #10's working files** beyond their module docstrings, per the
   brief. Their rows are citability facts and nothing more.

---

## §M9 — LATE MEASUREMENT (after §5 was written; §5 item 2 was the reason I ran it)

I ran the two conclusion-shape queries §5.2 flagged as gaps. Both found declarations that
**every earlier section of this file missed**, so the gap was real and is now closed. Neither
query returned any structure field (0 of 13, 0 of 19), so the `VInductDecl'.WF.params` failure
mode is excluded for #1 and #6.

`HEADS="TrProj Ctx.Lift'"` → 13 hits; `HEADS="VEnv.IsDefEqU Ctx.LiftN"` → 19 hits. New:

| name | module | arity | cone | holes |
|---|---|---|---|---|
| `Lean4Lean.TrProj.weak'_inv_of_projStrengthen` | `Verify.Typing.ProjExistClose` | 14 | **84** | **none** |
| `Lean4Lean.TrProj.weak'_inv_of_projDataStrengthen` | `Verify.Typing.ProjExistClose` | 14 | **717** | **none** |
| `Lean4Lean.VEnv.ProjDataStrengthen` | `Verify.Typing.ProjExistClose` | 2 | 696 | none (def) |
| `Lean4Lean.trProj_weak'_inv_fires` | `Verify.Typing.ProjExistClose` | 0 | 4358 | none |
| `Lean4Lean.VEnv.weakN_iff_forward_of_target` | `Theory.Typing.WeakNForward` | 12 | 157 | none; WATCHED `StrengtheningTarget` |
| `Lean4Lean.VEnv.weakN_iff_of_target_ordered` | `Theory.Typing.WeakNForward` | 12 | 1081 | none; WATCHED `StrengtheningTarget` |
| `Lean4Lean.VEnv.weakNForward_vacuous_at_zero` | `Theory.Typing.WeakNForward` | 9 | 225 | none |
| `Lean4Lean.VEnv.IsDefEqU.strengthen_at_prop_no_premises` | `Theory.Typing.StrengthenPiProp` | 16 | 3633 | #5, #8 |
| `Lean4Lean.VEnv.piDescend_of_no_neutral_pi` | `Theory.Typing.PiDescendFstCod` | 5 | 3664 | #5, #8 |

**This changes the verdict on #1's residual, and it is the best result in this file.**

* `VEnv.ProjStrengthen` is the hole's statement `∀`-quantified (`projStrengthen_iff_weak'_inv`
  says so), so `weak'_inv_of_projStrengthen` at cone 84 is a repackaging, not a producer —
  a textbook "admire, don't instantiate" hit, correctly labelled as such in its own file.
* `VEnv.ProjDataStrengthen` is different: `Verify/Typing/ProjExistClose.lean` §1 proves it
  **equivalent** (`iff`) to `ProjStrengthen`, and the reduction is **hole-free** — the round-trip
  never calls `VEnv.HasArgs.of_mkApp`, so `rigidShapeUniqNS` and `forallE_inv_stratified` both
  leave the cone (717 with no holes, against `weak'_inv_of_strengthen`'s 3698 with three).
  Its hypotheses are also shown non-vacuous there.

So **#1's residual is exactly `VEnv.ProjDataStrengthen`** — an equivalent, hole-free,
data-level restatement — and *not* "#5 + #8 + `ConstAppDefeqStrengthen`", which is the weaker
upper bound reached by the `ConstAppTypeStrengthen` route (`projDataStrengthen_of_…` at line 337
of that file derives `ProjDataStrengthen` from `ConstAppTypeStrengthen`, i.e. that route is one
side of the bound, not the residual). Amend §0.b row 1 and §2.1/§3.4 accordingly.

Citability is unchanged and still **NO**: `Verify/Typing/ProjExistClose.lean` imports
`ProjWeakInv.lean`, which imports `Verify/Typing/Lemmas.lean`.

For #6 the two `WeakNForward` hits are **not** producers: both carry `VEnv.StrengtheningTarget`
in their cone, which `exists.lean`'s WATCH list flags precisely because it is the hole restated.
`weakNForward_vacuous_at_zero` is an anti-vacuity control, not a route.

## §4.4 Correction to my own §M3 and to an in-tree docstring, both found by §M9

* **My §M3 table is incomplete.** It listed five conditional producers for #1 and missed the two
  in `Verify/Typing/ProjExistClose.lean`, including the only hole-free equivalence in the set.
  Cause: I found #1's producers by reading `Verify/Typing/Lemmas.lean`'s docstring (which
  predates `ProjExistClose.lean`) instead of by conclusion shape. This is the exact failure this
  round exists to prevent, committed by the round itself; the shape query caught it.
* **`Verify/TypeChecker/InferType.lean`'s `inferProj.WF` docstring contains a false
  parenthesis.** It says the statement is "**vacuously true today** (`TrProj` has no inhabitants
  until the keystone lands)". `Verify/Typing/ProjExistClose.lean` §2 exhibits a `VEnv.WF`
  environment with `structure Prj : Type where fld : Prop` at which **all ten `TrProj` fields
  hold with no hypotheses** (`trProj_weak'_inv_fires`, arity 0, cone 4358, `sorryAx`-free), and
  says in terms that "the parenthesis is false". The *conclusion* (that `inferProj.WF` is
  vacuous today) still stands — it comes from `inferProj` always throwing via
  `TrEnv.not_inductInfo`, not from `TrProj` being empty — but the reason given is wrong, and the
  same parenthesis is repeated across the projection docs. §1.3's edit is unaffected; §1.4's
  recommendation is unaffected.
