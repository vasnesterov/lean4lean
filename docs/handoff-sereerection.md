# handoff-sereerection.md — pricing the re-erection of NormalEq/ParRed/church_rosser over IsDefEqSE

Round scope: **pricing only**. No edits to any existing file. I own exactly this file and
(if a claim needs machine checking) `Lean4Lean/Theory/Typing/SEReerectionScope.lean`.

## 0. Priors (written 2026-09-04, BEFORE the first measurement)

Recorded so the round can be scored against them. Each is a falsifiable guess.

P1. **Size of the re-erection.** I expect `Theory/Typing/NormalEq.lean` +
    `ParRed`-bearing modules + `ChurchRosser.lean` to hold on the order of
    **60–150 declarations** mentioning the defeq relation, of which maybe
    **half** are genuinely relation-polymorphic (statable once, over a
    parameter) and half are relation-specific. Confidence: low-medium. The
    "136 induction sites" figure on record for the 14th-constructor route
    suggests the induction-site count and the declaration count are the same
    order of magnitude, so I expect **80–200 induction sites** on the
    proof-term walk. I explicitly expect grep to undercount, since sites are
    `induction H with | ...`.

P2. **(b) The VDefEq-route verdict — the question the orchestrator most wants.**
    My prior is **NO, the VDefEq route does not make the rule invisible to the
    confluence layer**, i.e. re-erection is NOT avoided. Reasoning: `extra`
    carries a closed `VDefEq` rule, and a closed rule still has to be *joined*
    by ParRed — church_rosser must show the rule commutes with beta/iota, and
    structure eta is exactly the rule that does **not** commute syntactically
    (eta expands, beta contracts; the critical pair `(S.mk x.1 x.2)` vs `x`
    against a projection redex is real). If `ParRed` has an `extra`/rule case
    at all, it must be re-proved for the *larger* rule set, and if it does not,
    then closed rules are currently handled by some inertness argument that
    structure eta will break, because eta's LHS is not closed in the
    relevant sense (it mentions a free variable under the mk). So I expect the
    confluence layer to **see** it. Confidence: medium-high (0.75). The
    counter-scenario I take seriously: `ParRed` may quantify over the rule set
    abstractly and already prove church_rosser *for any* set of rules
    satisfying a side condition, in which case the price is discharging that
    side condition once, and the answer flips to essentially **0 re-erection**.
    That is the outcome that would most change the plan, so I will look for it
    first.

P3. **(c) Layering.** The orchestrator's report says `DescendRefute`, `KDescend`,
    `KSite7App`, `ParRedPropRefute` are all downstream of `ChurchRosser`, and
    the calibration note says *attributions and scan summaries have been wrong
    three rounds running while conclusions survived*. Prior: the **direction**
    is right (they are downstream) but at least one of the four is
    mis-attributed — I'd bet on `KSite7App` or `KDescend` being only
    transitively downstream, or downstream of a *different* module. A working
    layering almost certainly exists via a `ChurchRosserCore` split (parametric
    core, then two instantiations), because that is what "no in-place rewiring"
    usually means: the cycle is through *proofs*, not through *statements*.
    Confidence: medium.

P4. **(d) The model.** I expect `Lean4Lean.SetModel.eq_singleton_of_recProp` to
    exist and be hole-free, and I expect the model to validate structure eta.
    But I expect the "validation is *forced*" claim to be the weak link —
    "forced" is an attribution-flavoured claim and those have been the wrong
    ones. Prior: the model **can** validate eta but I expect at least one
    further obligation from `Theory/SetModel/` for confluence over the extended
    relation, most likely a *pointwise* soundness lemma for the new rule at the
    `VDefEq`/`extra` interface. Confidence: medium-low.

P5. **Overall shape of the answer.** I expect the honest answer to be "this is a
    large independent project", with a price in the **several-hundred-line,
    multi-round** range rather than the tens-of-lines range, and I expect the
    cheapest true win this round to be a *parametric* restatement (prove
    church_rosser over an abstract rule set once) rather than a copy.

P6. **Instrument risk.** Fourteen API crashes this session, four at the
    measure-to-author transition. So: every measurement below is appended
    before the next one is taken, and no result is held in context.

---

## 1. Measurement log (append-only, one entry per instrument call)

### M1 [2026-09-04T02:03:48Z] locate relevant modules
```
-- ls Lean4Lean/Theory/Typing/
AppCase.lean
AppCodConvSort.lean
AppCodLevelWF.lean
AppCodType0.lean
AppUniqRefute.lean
AppUniqWF.lean
BaseUniqChain.lean
BaseUniqTerm.lean
Basic.lean
CRBetaGen.lean
CRPiDescend.lean
ChurchRosser.lean
ConfluenceRebuildPrice.lean
ConstAppInvSIProof.lean
ConstInvWitness.lean
ConstSubst.lean
ConstSubstNested.lean
ConstVar.lean
CtxConvIndex.lean
CycleConv.lean
DeclRules.lean
DefInvRefute.lean
DeltaUnique.lean
DescendAttack.lean
DescendConstSpineK.lean
DescendRefute.lean
DescendRestate.lean
Enlarged.lean
EnlargedModel.lean
Env.lean
EnvLemmas.lean
EtaGuardLand.lean
ForallInvPrice.lean
GateBodyDescend.lean
GateBodyWitness.lean
HeadRedStuck.lean
HeadReduction.lean
InductiveLemmas.lean
InjChainLower.lean
InjChainStep.lean
InjCorner.lean
InjMidLocal.lean
InjMidpoint.lean
InjOneFact.lean
InjPiInhab.lean
InjPiRogue.lean
InjSortPiModel.lean
InjSpineTransport.lean
Injectivity.lean
KCanonical.lean
KDescend.lean
KDiamondJoin.lean
KEta.lean
KEtaDiamond.lean
KKetaRow.lean
KMeasure.lean
KRule.lean
KSite7.lean
KSite7App.lean
KSite7Rows.lean
Lemmas.lean
LiftTrimWitness.lean
LogRelRowZero.lean
Meta.lean
NoConfRepair.lean
NormalEqStrengthen.lean
NotProof.lean
ParRedCycle.lean
ParRedKGraded.lean
ParRedKWeakN.lean
ParRedMissing.lean
ParRedPropRefute.lean
ParamsBuild.lean
ParamsWitness.lean
PatAppParams.lean
PatKHead.lean
PatWF.lean
PatWFIota.lean
Pattern.lean
PatternDecode.lean
PatternRules.lean
PiDescendFstCod.lean
PiDescendSplit.lean
PiInvResidual.lean
PiLevelPin.lean
ProofRetypeHeads.lean
PropAgreeGuarded.lean
PropConv.lean
PropShadow.lean
QuotKAppEta.lean
QuotLemmas.lean
RawDefEq.lean
RegPiSat.lean
RetypeAdmissible.lean
RetypeCase.lean
RigidConstPrice.lean
RigidNodeCircle.lean
ShapeIndep.lean
ShapeIndepFresh.lean
ShapeIndepStep.lean
ShapeSpine.lean
ShapeVar.lean
SortClauses.lean
SortDisjPiLvl.lean
SortInvIndep.lean
SortPiDisjPrice.lean
SortRedApp.lean
SortUniq.lean
SortUniqDown.lean
SortUniqFacts.lean
SpineInv.lean
SpineVar.lean
SpineVarClosed.lean
SpineVarVacuity.lean
StratLevelWF.lean
Stratified.lean
Strengthen.lean
StrengthenAudit.lean
StrengthenAxiom.lean
StrengthenCanon.lean
StrengthenInhabGate.lean
StrengthenNarrow.lean
StrengthenPiProp.lean
StrengthenVerdict.lean
StrengthenWitness.lean
Strong.lean
StructEtaPrice.lean
StructureRuleFree.lean
SubstCRefute.lean
SubstTRefute.lean
UniqSort.lean
UniqueTyping.lean
UniqueTypingN.lean
UnivDiscrim.lean
WeakNForward.lean
WeakNProjGate.lean

-- files mentioning IsDefEqSE
Lean4Lean/Theory/Typing/EtaGuardLand.lean
Lean4Lean/Theory/Typing/StructEtaPrice.lean
Lean4Lean/Theory/Typing/NoConfRepair.lean
Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean

-- files mentioning ParRed
scripts/kernel-sound-path.lean
scripts/weakn-residual-map.lean
Lean4Lean/Verify/QuotAppParams.lean
Lean4Lean/Verify/Typing/WeakNormRefute.lean
Lean4Lean/Verify/Typing/QuotKEta.lean
Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean
Lean4Lean/Verify/Typing/ProjWeakInv.lean
Lean4Lean/Verify/Typing/Rigidity.lean
Lean4Lean/Verify/Typing/ConstSpine.lean
Lean4Lean/Theory/Typing/KEta.lean
Lean4Lean/Theory/Typing/KDescend.lean
Lean4Lean/Theory/Typing/PatAppParams.lean
Lean4Lean/Theory/Typing/PatKHead.lean
Lean4Lean/Theory/Typing/NormalEqStrengthen.lean
Lean4Lean/Theory/Typing/EtaGuardLand.lean
Lean4Lean/Theory/Typing/DescendRestate.lean
Lean4Lean/Theory/Typing/Injectivity.lean
Lean4Lean/Theory/Typing/KEtaDiamond.lean
Lean4Lean/Theory/Typing/InjMidLocal.lean
Lean4Lean/Theory/Typing/NoConfRepair.lean
Lean4Lean/Theory/Typing/ParRedKWeakN.lean
Lean4Lean/Theory/Typing/DescendConstSpineK.lean
Lean4Lean/Theory/Typing/ParRedPropRefute.lean
Lean4Lean/Theory/Typing/InjOneFact.lean
Lean4Lean/Theory/Typing/StructEtaPrice.lean
Lean4Lean/Theory/Typing/CRPiDescend.lean
Lean4Lean/Theory/Typing/ParRedKGraded.lean
Lean4Lean/Theory/Typing/QuotKAppEta.lean
Lean4Lean/Theory/Typing/ParRedMissing.lean
Lean4Lean/Theory/Typing/KMeasure.lean
Lean4Lean/Theory/Typing/ParamsWitness.lean
Lean4Lean/Theory/Typing/CRBetaGen.lean
Lean4Lean/Theory/Typing/StrengthenAudit.lean
Lean4Lean/Theory/Typing/KKetaRow.lean
Lean4Lean/Theory/Typing/HeadReduction.lean
Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean
Lean4Lean/Theory/Typing/KSite7.lean
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean
Lean4Lean/Theory/Typing/KSite7App.lean
Lean4Lean/Theory/Typing/ChurchRosser.lean
Lean4Lean/Theory/Typing/KSite7Rows.lean
Lean4Lean/Theory/Typing/DescendAttack.lean
Lean4Lean/Theory/Inductive/NestedRules.lean
Lean4Lean/Experimental/CoinductiveLogRel.lean
Lean4Lean/Theory/Typing/DescendRefute.lean
Lean4Lean/Experimental/MoreStepIndexed.lean
Lean4Lean/Theory/Typing/WeakNForward.lean
Lean4Lean/Theory/Typing/KDiamondJoin.lean
Lean4Lean/Theory/Typing/ParRedCycle.lean
Lean4Lean/Theory/Typing/KCanonical.lean
Lean4Lean/Experimental/ConeJoin.lean
Lean4Lean/Experimental/ParallelReduction.lean
Lean4Lean/Experimental/SExpr.lean
Lean4Lean/Theory/Typing/KRule.lean

-- files mentioning church_rosser
scripts/hole-cone.lean
scripts/weakn-residual-map.lean
Lean4Lean/Verify/QuotAppParams.lean
Lean4Lean/Verify/Typing/ProjWeakInv.lean
Lean4Lean/Verify/Typing/ConstSpineWF.lean
Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean
Lean4Lean/Verify/Typing/Rigidity.lean
Lean4Lean/Verify/Typing/ConstSpine.lean
Lean4Lean/Verify/Typing/NoConfGuard.lean
Lean4Lean/Theory/Typing/KEta.lean
Lean4Lean/Theory/Typing/RigidNodeCircle.lean
Lean4Lean/Theory/Typing/ParamsWitness.lean
Lean4Lean/Theory/Typing/DescendConstSpineK.lean
Lean4Lean/Verify/TypeChecker/WHNF.lean
Lean4Lean/Theory/Typing/NormalEqStrengthen.lean
Lean4Lean/Theory/Typing/Injectivity.lean
Lean4Lean/Theory/Typing/KEtaDiamond.lean
Lean4Lean/Theory/Typing/InjPiRogue.lean
Lean4Lean/Theory/Typing/NoConfRepair.lean
Lean4Lean/Theory/Typing/KDiamondJoin.lean
Lean4Lean/Theory/Typing/StrengthenNarrow.lean
Lean4Lean/Theory/Typing/ShapeIndep.lean
Lean4Lean/Theory/Typing/StructEtaPrice.lean
Lean4Lean/Theory/Typing/KCanonical.lean
Lean4Lean/Theory/Typing/ParRedMissing.lean
Lean4Lean/Theory/Typing/ParRedCycle.lean
Lean4Lean/Theory/Typing/HeadReduction.lean
Lean4Lean/Theory/Typing/KSite7App.lean
Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean
Lean4Lean/Theory/Typing/ChurchRosser.lean
Lean4Lean/Theory/Typing/ParamsBuild.lean
Lean4Lean/Experimental/ConeJoin.lean
Lean4Lean/Experimental/ParallelReduction.lean

-- files mentioning NormalEq
scripts/appcodtype0-cone.lean
scripts/appcodlevelwf-cone.lean
scripts/weakn-gate-split.lean
scripts/kernel-sound-path.lean
scripts/appcodconvsort-cone.lean
scripts/hole-rank.lean
scripts/sorry-census.lean
Lean4Lean/Verify/QuotAppParams.lean
Lean4Lean/Verify/QuotReach.lean
Lean4Lean/Verify/Typing/Rigidity.lean
Lean4Lean/Verify/Typing/ConstSpineWF.lean
Lean4Lean/Verify/Typing/ConstSpine.lean
Lean4Lean/Verify/Typing/ProjWeakInv.lean
Lean4Lean/Verify/Typing/NoConfGuard.lean
Lean4Lean/Verify/Typing/Lemmas.lean
Lean4Lean/Verify/Environment/AddDeclPath.lean
Lean4Lean/Verify/TypeChecker/WHNF.lean
Lean4Lean/Verify/TypeChecker/IsDefEq.lean
Lean4Lean/Theory/Typing/StrengthenInhabGate.lean
Lean4Lean/Verify/TypeChecker/EtaResidual.lean
Lean4Lean/Verify/TypeChecker/EtaUnitRefute.lean
Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean
Lean4Lean/Verify/TypeChecker/EtaStructG.lean
Lean4Lean/Verify/TypeChecker/UnitEta.lean
Lean4Lean/Theory/Typing/PatAppParams.lean
Lean4Lean/Theory/Typing/KRule.lean
Lean4Lean/Theory/Typing/KEtaDiamond.lean
Lean4Lean/Theory/Typing/KEta.lean
Lean4Lean/Theory/SemanticRouteClosed.lean
Lean4Lean/Theory/Typing/StrengthenNarrow.lean
Lean4Lean/Theory/Typing/Injectivity.lean
Lean4Lean/Theory/Typing/EtaGuardLand.lean
Lean4Lean/Theory/Typing/DescendRestate.lean
Lean4Lean/Theory/Typing/RawDefEq.lean
Lean4Lean/Theory/Typing/ParRedKWeakN.lean
Lean4Lean/Theory/Typing/InjMidLocal.lean
Lean4Lean/Theory/Typing/StructEtaPrice.lean
Lean4Lean/Theory/Typing/DescendRefute.lean
Lean4Lean/Theory/Typing/KDescend.lean
Lean4Lean/Theory/Typing/NormalEqStrengthen.lean
Lean4Lean/Theory/Typing/DescendConstSpineK.lean
Lean4Lean/Theory/Typing/RigidNodeCircle.lean
Lean4Lean/Theory/Typing/DescendAttack.lean
Lean4Lean/Theory/Typing/KMeasure.lean
Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean
Lean4Lean/Theory/Typing/InjPiRogue.lean
Lean4Lean/Theory/Typing/InjOneFact.lean
Lean4Lean/Theory/Typing/KSite7App.lean
Lean4Lean/Theory/Typing/PiDescendFstCod.lean
Lean4Lean/Theory/Typing/ParamsWitness.lean
Lean4Lean/Theory/Typing/KSite7Rows.lean
Lean4Lean/Theory/Typing/WeakNForward.lean
Lean4Lean/Theory/Typing/CRPiDescend.lean
Lean4Lean/Theory/Typing/Pattern.lean
Lean4Lean/Theory/Typing/KSite7.lean
Lean4Lean/Theory/Typing/InjChainLower.lean
Lean4Lean/Theory/Typing/ParamsBuild.lean
Lean4Lean/Theory/Typing/KKetaRow.lean
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean
Lean4Lean/Theory/Typing/NoConfRepair.lean
Lean4Lean/Theory/Typing/NotProof.lean
Lean4Lean/Theory/Typing/StrengthenAudit.lean
Lean4Lean/Theory/Typing/StrengthenPiProp.lean
Lean4Lean/Theory/Typing/KCanonical.lean
Lean4Lean/Theory/Typing/ParRedCycle.lean
Lean4Lean/Theory/Typing/KDiamondJoin.lean
Lean4Lean/Theory/Typing/ChurchRosser.lean
Lean4Lean/Theory/Typing/ParRedMissing.lean
Lean4Lean/Theory/Inductive/StructureEta.lean
Lean4Lean/Theory/SetModel/CnstRecursion.lean
Lean4Lean/Experimental/ConeJoin.lean
Lean4Lean/Theory/Typing/PiDescendSplit.lean
Lean4Lean/Experimental/NormalEq.lean
Lean4Lean/Experimental/ParallelReduction.lean
Lean4Lean/Theory/Typing/CRBetaGen.lean
Lean4Lean/Theory/Typing/ParRedPropRefute.lean
Lean4Lean/Theory/Typing/InjPiInhab.lean
Lean4Lean/Theory/Typing/ParRedKGraded.lean
Lean4Lean/Experimental/MoreStepIndexed.lean
Lean4Lean/Experimental/SExpr.lean
```

### M2 [2026-09-04T02:04:12Z] where are NormalEq / ParRed / church_rosser DEFINED
```
-- inductive/def NormalEq
Lean4Lean/Theory/Typing/NormalEqStrengthen.lean:343:def NormalEqComplete : Prop :=
Lean4Lean/Theory/Typing/KKetaRow.lean:133:def EtaKNormalEqInv : Prop :=
Lean4Lean/Theory/Typing/ChurchRosser.lean:165:inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:371:inductive NormalEqSE : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Experimental/NormalEq.lean:164:inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Experimental/SExpr.lean:2685:inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
-- inductive/def ParRed
Lean4Lean/Theory/Typing/KEta.lean:341:inductive ParRedK : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/KEta.lean:389:def ParRedKS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedK Γ)
Lean4Lean/Theory/Typing/KEtaDiamond.lean:162:def ParRedKSDomConv : Prop :=
Lean4Lean/Theory/Typing/KSite7.lean:29:def ParRedKStatement : Prop :=
Lean4Lean/Theory/Typing/KCanonical.lean:459:def ParRedStatement : Prop :=
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:417:inductive ParRedSE : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:438:def ParRedSES (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedSE Γ)
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:618:def ParRedStatementSE : Prop :=
Lean4Lean/Theory/Typing/KKetaRow.lean:301:inductive ParRedKn : Nat → List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/KKetaRow.lean:422:def ParRedKStatementN (N : Nat) : Prop :=
Lean4Lean/Theory/Typing/ParRedMissing.lean:16:def ParRedProofRepl : Prop :=
Lean4Lean/Theory/Typing/ParRedMissing.lean:141:def ParRedProofRepl : Prop :=
Lean4Lean/Theory/Typing/ParRedMissing.lean:146:def ParRedEtaContract : Prop :=
Lean4Lean/Theory/Typing/ParRedMissing.lean:154:inductive ParRedP : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/ParRedMissing.lean:162:def ParRedPS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedP Γ)
Lean4Lean/Theory/Typing/ChurchRosser.lean:752:inductive ParRed : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/ChurchRosser.lean:787:inductive CParRed : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/ChurchRosser.lean:1231:def ParRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed Γ)
Lean4Lean/Theory/Typing/ChurchRosser.lean:1305:inductive ParRedExt : Type where
Lean4Lean/Theory/Typing/ChurchRosser.lean:1310:def ParRedExt.depth : ParRedExt → Nat
Lean4Lean/Theory/Typing/ChurchRosser.lean:1315:def ParRedExt.apply : ParRedExt → VExpr → VExpr
Lean4Lean/Theory/Typing/ChurchRosser.lean:1320:def ParRedExt.meas : ParRedExt → Nat
Lean4Lean/Experimental/ParallelReduction.lean:18:inductive ParRed : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Experimental/ParallelReduction.lean:33:inductive CParRed : List VExpr → VExpr → VExpr → Prop where
Lean4Lean/Experimental/ParallelReduction.lean:439:def ParRedS (TY : Typing) (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed TY Γ)
Lean4Lean/Experimental/ParallelReduction.lean:509:inductive ParRedExt : Type where
Lean4Lean/Experimental/ParallelReduction.lean:514:def ParRedExt.depth : ParRedExt → Nat
Lean4Lean/Experimental/ParallelReduction.lean:519:def ParRedExt.apply : ParRedExt → VExpr → VExpr
Lean4Lean/Experimental/ParallelReduction.lean:524:def ParRedExt.meas : ParRedExt → Nat
Lean4Lean/Experimental/SExpr.lean:2532:inductive ParRed : List SExpr → SExpr → SExpr → Prop where
Lean4Lean/Experimental/SExpr.lean:2555:def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
-- theorem church_rosser
scripts/hole-cone.lean:71:   ``Lean4Lean.VEnv.IsDefEq.church_rosser,
scripts/weakn-residual-map.lean:60:   ``Lean4Lean.VEnv.IsDefEq.church_rosser]
Lean4Lean/Verify/QuotAppParams.lean:8:`NormalEq.parRed` and `IsDefEq.church_rosser`
Lean4Lean/Verify/QuotAppParams.lean:37:4. **`NormalEq.parRed`'s and `IsDefEq.church_rosser`'s statements are refuted here**
Lean4Lean/Verify/QuotAppParams.lean:98:sites of `IsDefEq.church_rosser` in `Verify/Typing/ConstSpine.lean` and `Rigidity.lean` rest on
Lean4Lean/Verify/QuotAppParams.lean:560:/-! ## 7. …and `IsDefEq.church_rosser`'s statement goes too
Lean4Lean/Verify/QuotAppParams.lean:627:/-- **`IsDefEq.church_rosser`'s statement is refuted at the canonical instance.**  No `hK`: only
Lean4Lean/Verify/Typing/ProjWeakInv.lean:82:   likewise reaches it, via `constApp_inv_of_patWF → IsDefEq.constApp_inv → church_rosser`.
Lean4Lean/Verify/Typing/ProjWeakInv.lean:90:re-derive it: `IsDefEq.church_rosser` gives reducts with `NormalEq X' Y'`, `Y'` stays
Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean:49:confluence with lift-preservation (`church_rosser` + `ParRed.weakN_inv`, which re-imports the
Lean4Lean/Verify/Typing/ConstSpineWF.lean:33:`VEnv.IsDefEq.church_rosser`, and `VEnv.not_crStatement_of_kstep`
Lean4Lean/Verify/Typing/ConstSpineWF.lean:34:(`Theory/Typing/KCanonical.lean`) refutes `church_rosser`'s *statement* at any `Params`
Lean4Lean/Verify/Typing/ConstSpineWF.lean:41:  with the hole `church_rosser` is waiting on.
Lean4Lean/Verify/Typing/Rigidity.lean:19:Both go through `VEnv.IsDefEq.church_rosser`; see `Verify/Typing/ConstSpine.lean`'s module
Lean4Lean/Verify/Typing/Rigidity.lean:238:residual of the whole family never arises, because `IsDefEq.church_rosser` has already paid
Lean4Lean/Verify/Typing/Rigidity.lean:317:this tree: `VEnv.WF` → `paramsOfWF` → `IsDefEq.church_rosser` → the spine analysis.  They are
Lean4Lean/Verify/Typing/ConstSpine.lean:17:theorem, and `VEnv.IsDefEq.church_rosser` has already paid for it — so an argument routed
Lean4Lean/Verify/Typing/ConstSpine.lean:243:`trans` constructor: transitivity there is a *theorem*, and `IsDefEq.church_rosser` has
Lean4Lean/Verify/Typing/ConstSpine.lean:255:  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
Lean4Lean/Verify/Typing/ConstSpine.lean:342:  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
Lean4Lean/Verify/Typing/ConstSpine.lean:355:  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
Lean4Lean/Verify/Typing/ConstSpine.lean:509:  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := hdf₀.church_rosser hΓ
Lean4Lean/Verify/Typing/NoConfGuard.lean:504:   `church_rosser`.**  That is the machine-checked form of `RigidNodeCircle.lean`'s "circular"
Lean4Lean/Theory/Typing/KEta.lean:8:* `VEnv.not_crStatement_of_kstep` -- `IsDefEq.church_rosser`'s statement, verbatim, is
Lean4Lean/Theory/Typing/RigidNodeCircle.lean:74:`IsDefEq.church_rosser` plus `VEnv.PatWF`, and `Theory/Typing/PatWFIota.lean`'s `patWF` gives
Lean4Lean/Theory/Typing/RigidNodeCircle.lean:79:`IsDefEq.church_rosser`, whose cone runs through `IsDefEqU.forallE_inv`, whose cone is
Lean4Lean/Verify/TypeChecker/WHNF.lean:85:pressure.  `VEnv.IsDefEq.church_rosser` and `VEnv.NormalEq.descend` are **not** in the cone
Lean4Lean/Theory/Typing/ParamsWitness.lean:169:Proved by hand, so this statement is `sorry`-free -- unlike `IsDefEq.church_rosser`, which
Lean4Lean/Theory/Typing/ParamsWitness.lean:170:would also produce it (see `propLoopEnv_church_rosser_fires`). -/
Lean4Lean/Theory/Typing/ParamsWitness.lean:179:**This one is not `sorry`-free**: `IsDefEq.church_rosser` carries `sorryAx` from
Lean4Lean/Theory/Typing/ParamsWitness.lean:183:theorem propLoopEnv_church_rosser_fires :
Lean4Lean/Theory/Typing/ParamsWitness.lean:185:  IsDefEq.church_rosser (Γ := []) trivial (.extra (ls := []) propLoopEnv_defeqs_A nofun rfl)
Lean4Lean/Theory/Typing/StrengthenNarrow.lean:81:| `IsDefEq.church_rosser`, `NormalEq.descend` | all four, `IsDefEqU.weakN_iff` included |
Lean4Lean/Theory/Typing/KDiamondJoin.lean:201:* Not that `IsDefEq.church_rosser` or `NormalEq.parRed` are repaired.  They are refuted **as
Lean4Lean/Theory/Typing/InjPiRogue.lean:1184:`n+1` by "all the results of `sec:church_rosser` follow".  **There is no route in the reference to
Lean4Lean/Theory/Typing/Injectivity.lean:875:**Confluence, in the form of `IsDefEq.church_rosser`** (`Theory/Typing/ChurchRosser.lean`,
Lean4Lean/Theory/Typing/Injectivity.lean:968:`IsDefEq.church_rosser`), for why `NormalEq.descend`'s conclusion does not, and for the two
Lean4Lean/Theory/Typing/KEtaDiamond.lean:102:  things `KSite7App.lean`'s ledger says `church_rosser`-on-`ParRedK` still owes; `ParRed.triangle`
Lean4Lean/Theory/Typing/KCanonical.lean:66:`IsDefEq.church_rosser` itself, not merely to `KDiamond`.  Building one needs an environment
Lean4Lean/Theory/Typing/KCanonical.lean:450:eta-expansion step) has to grow, and that changes `IsDefEq.church_rosser`'s conclusion, i.e.
-- IsDefEqSE decl
Lean4Lean/Theory/Typing/EtaGuardLand.lean:350:be zero-field-only (`zeroFieldOnlyNoConf_false_for_IsDefEqSE`). -/
Lean4Lean/Theory/Typing/EtaGuardLand.lean:398:is what `zeroFieldOnlyNoConf_false_for_IsDefEqSE` says a repair must do.
Lean4Lean/Theory/Typing/NoConfRepair.lean:9:fourteen-constructor relation (`constNoConf_false_for_IsDefEqSE`).  The conclusion drawn there is
Lean4Lean/Theory/Typing/NoConfRepair.lean:59:* `¬ IsProof` alone — refuted, in the tree (`constNoConf_false_for_IsDefEqSE`).
Lean4Lean/Theory/Typing/NoConfRepair.lean:111:(`Ty := fun e A => env.IsDefEqSE U Γ e e A`) and the closed-`VDefEq` alternative of §7 alike.
Lean4Lean/Theory/Typing/NoConfRepair.lean:469:    bigEnv.IsDefEqSE 0 [] (.const `MutField.foo []) (.const `MutField.A.mk [])
Lean4Lean/Theory/Typing/NoConfRepair.lean:476:    bigEnv.IsDefEqSE 0 [] (.const `MutField.foo2 []) (.const `MutField.A.mk [])
Lean4Lean/Theory/Typing/NoConfRepair.lean:487:    bigEnv.IsDefEqSE 0 [] ((VExpr.const `MutField.bar []).mkApp [])
Lean4Lean/Theory/Typing/NoConfRepair.lean:507:`VEnv.IsDefEqSE` both have them as constructors), and the two eta instances, which
Lean4Lean/Theory/Typing/NoConfRepair.lean:529:theorem exemptingCtorNoConf_false_for_IsDefEqSE :
Lean4Lean/Theory/Typing/NoConfRepair.lean:533:      MutField.bigEnv.IsDefEqSE 0 [] ((VExpr.const c ls).mkApp as)
Lean4Lean/Theory/Typing/NoConfRepair.lean:537:      (fun a b => MutField.bigEnv.IsDefEqSE 0 [] a b (.const `MutField.A []))
Lean4Lean/Theory/Typing/NoConfRepair.lean:556:theorem zeroFieldOnlyNoConf_false_for_IsDefEqSE :
Lean4Lean/Theory/Typing/NoConfRepair.lean:560:      MutField.bigEnv.IsDefEqSE 0 [] ((VExpr.const c ls).mkApp as)
Lean4Lean/Theory/Typing/NoConfRepair.lean:704:| `zeroFieldOnlyNoConf_false_for_IsDefEqSE` | 3979 | none |
Lean4Lean/Theory/Typing/NoConfRepair.lean:705:| `exemptingCtorNoConf_false_for_IsDefEqSE` | 4282 | none |
Lean4Lean/Theory/Typing/NoConfRepair.lean:742:#print axioms Lean4Lean.exemptingCtorNoConf_false_for_IsDefEqSE
Lean4Lean/Theory/Typing/NoConfRepair.lean:743:#print axioms Lean4Lean.zeroFieldOnlyNoConf_false_for_IsDefEqSE
Lean4Lean/Theory/Typing/StructEtaPrice.lean:68:* `IsDefEqSE` (§3) — the fourteen-constructor relation, so the constructor is *stated* rather
Lean4Lean/Theory/Typing/StructEtaPrice.lean:79:  same time.  Instantiated at `IsDefEqSE`, this says `VEnv.IsDefEq.constApp_inv`
Lean4Lean/Theory/Typing/StructEtaPrice.lean:119:   and `he` is `IsDefEqSE Γ e e ((const S us).mkApp ps)`.  `VEnv.StructEtaG` states them in
Lean4Lean/Theory/Typing/StructEtaPrice.lean:143:inductive IsDefEqSE : List VExpr → VExpr → VExpr → VExpr → Prop where
Lean4Lean/Theory/Typing/StructEtaPrice.lean:144:  | bvar : Lookup Γ i A → IsDefEqSE Γ (.bvar i) (.bvar i) A
Lean4Lean/Theory/Typing/StructEtaPrice.lean:145:  | symm : IsDefEqSE Γ e e' A → IsDefEqSE Γ e' e A
Lean4Lean/Theory/Typing/StructEtaPrice.lean:146:  | trans : IsDefEqSE Γ e₁ e₂ A → IsDefEqSE Γ e₂ e₃ A → IsDefEqSE Γ e₁ e₃ A
Lean4Lean/Theory/Typing/StructEtaPrice.lean:149:    IsDefEqSE Γ (.sort l) (.sort l') (.sort (.succ l))
Lean4Lean/Theory/Typing/StructEtaPrice.lean:156:    IsDefEqSE Γ (.const c ls) (.const c ls') (ci.type.instL ls)
Lean4Lean/Theory/Typing/StructEtaPrice.lean:158:    IsDefEqSE Γ f f' (.forallE A B) →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:159:    IsDefEqSE Γ a a' A →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:160:    IsDefEqSE Γ (.app f a) (.app f' a') (B.inst a)
Lean4Lean/Theory/Typing/StructEtaPrice.lean:162:    IsDefEqSE Γ A A' (.sort u) →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:163:    IsDefEqSE (A::Γ) body body' B →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:164:    IsDefEqSE Γ (.lam A body) (.lam A' body') (.forallE A B)
Lean4Lean/Theory/Typing/StructEtaPrice.lean:166:    IsDefEqSE Γ A A' (.sort u) →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:167:    IsDefEqSE (A::Γ) body body' (.sort v) →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:168:    IsDefEqSE Γ (.forallE A body) (.forallE A' body') (.sort (.imax u v))
Lean4Lean/Theory/Typing/StructEtaPrice.lean:169:  | defeqDF : IsDefEqSE Γ A B (.sort u) → IsDefEqSE Γ e1 e2 A → IsDefEqSE Γ e1 e2 B
Lean4Lean/Theory/Typing/StructEtaPrice.lean:171:    IsDefEqSE (A::Γ) e e B → IsDefEqSE Γ e' e' A →
Lean4Lean/Theory/Typing/StructEtaPrice.lean:172:    IsDefEqSE Γ (.app (.lam A e) e') (e.inst e') (B.inst e')
Lean4Lean/Theory/Typing/StructEtaPrice.lean:174:    IsDefEqSE Γ e e (.forallE A B) →
```

### M3 [2026-09-04T02:04:22Z] ConfluenceRebuildPrice.lean — size + docstring head
```
   769 Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean
   668 Lean4Lean/Theory/Typing/StructEtaPrice.lean
  2525 Lean4Lean/Theory/Typing/ChurchRosser.lean
  3962 total
---- ConfluenceRebuildPrice.lean 1-120 ----
import Lean4Lean.Theory.Typing.StructEtaPrice
import Lean4Lean.Theory.Typing.ParRedPropRefute
import Lean4Lean.Theory.Typing.EtaGuardLand

/-!
# Pricing the confluence-layer rebuild: is it one job with structure eta, or two?

Round of 2026-09-04.  This file is a **pricing** file: it establishes no new confluence
result and repairs nothing.  It answers one question with theorems instead of prose —

> Two central statements of `Theory/Typing/ChurchRosser.lean` are false as written
> (`NormalEq.descend`, `NormalEq.parRed`).  Structure eta must eventually enter the abstract
> relation.  **Is rebuilding the confluence layer over the extended relation
> `VEnv.IsDefEqSE` the same job as repairing the two false statements, or two jobs?**

**Answer: two jobs, and the file's §3–§5 are the machine-checked reason.**  The repair the two
false statements need is an extension of the *reduction* relation (a proof-replacement / `K⁺`
step); the eta job is an extension of the *conversion* relation.  Those are moves in opposite
directions, and §4 shows the eta extension is **provably inert** — pointwise equal to the old
relation — at the very environment where `descend` is refuted.  So re-erecting the layer over
`IsDefEqSE` leaves both refutations standing verbatim; it cannot be the repair.

## What each section is

* **§1** `CRSchema`, the confluence statement with its three relations abstracted, plus the
  anti-strawman check that it *is* `VEnv.ParRedStatement` on the nose, plus the transport
  lemma: pointwise-equal ingredients give the *same proposition*.
* **§2** The same for the descent: `DescentLamP` / `DescentOutP` / `DescendStatementP`, the
  layer's statements with the three relation ingredients abstracted, each checked equal to the
  real one by `rfl`.  This is where the "how relation-polymorphic is the layer?" question gets
  an answer: **three ingredients** — a conversion, a multi-step reduction, and a typing
  judgment — and nothing else.
* **§3** `IsDefEqSE` is **inert at a defeq-free environment**: the fourteenth constructor and
  the `extra` constructor are both dead there, so `IsDefEqSE = IsDefEq` pointwise.
* **§4** The same at the *layer* level: `NormalEqSE` (the conversion relation re-erected over
  `IsDefEqSE`, **with two structure-eta rules added**) and `ParRedSE` (the reduction relation
  re-erected, with a structure-eta reduction added) are pointwise equal to `NormalEq` /
  `ParRed` at a defeq-free environment.
* **§5** The verdict, transported: at `refEnv` (`Theory/Typing/DescendRefute.lean`) the
  re-erected descent statement is the **same proposition** as `DescendStatement refParams`, so
  `descend_uniq_sortUniq_not_all` refutes it unchanged.  Two jobs.
* **§6** The converse separation: the eta job's witnesses and the confluence job's witness are
  **disjoint**.  `refEnv` holds no structure at all (so the eta rule has nothing to do there),
  and the environments where eta fires (`MutField.bigEnv`) are not where either statement is
  refuted.
* **§7** Vacuity, per the brief: the transport is not a statement about a relation that relates
  nothing.  Reduction and non-trivial conversion both happen at `refEnv`.

## What this file does NOT claim

It does **not** claim `NormalEq.descend` is unconditionally false.  What is `sorryAx`-free is
`Lean4Lean.descend_uniq_sortUniq_not_all`, a **trilemma**:
`¬ (DescendStatement refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0)`.  The
unconditional form `Lean4Lean.not_descendStatement_of_wf` is `sorryAx`-tainted through
`IsDefEqU.forallE_inv_stratified`, and `DescendRefute.lean` says so itself
("satisfiability is therefore **open**, not settled").  Everything below is stated so that the
trilemma, not the tainted corollary, is what carries the weight.
-/

namespace Lean4Lean

open VExpr

/-! ## §1 The confluence statement, with its relations abstracted

`VEnv.ParRedStatement` mentions three relations: a conversion (`NormalEq`), a one-step
reduction (`ParRed`) and its reflexive-transitive closure (`ParRedS`).  Abstracting all three
turns "would the rebuilt layer's statement be a different proposition?" into a question with a
proof rather than an opinion. -/

/-- The confluence statement's shape.  `W` is the context well-formedness side condition, `N`
the conversion, `R` the one-step reduction, `RS` its closure. -/
def CRSchema (W : List VExpr → Prop)
    (N RS : List VExpr → VExpr → VExpr → Prop)
    (R : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ e₃ : VExpr}, W Γ → N Γ e₁ e₂ → R Γ e₂ e₃ →
    ∃ o, RS Γ e₁ o ∧ N Γ o e₃

namespace VEnv

section
variable [Params]
open Params

/-- **Anti-strawman check for §1.**  `CRSchema` at the real three relations is
`VEnv.ParRedStatement` — `NormalEq.parRed`'s statement — definitionally. -/
theorem crSchema_eq_parRedStatement :
    CRSchema (fun Γ => OnCtx Γ (IsType env univs)) NormalEq ParRedS ParRed
      = @ParRedStatement _ := rfl

end

end VEnv

/-- **Transport: pointwise-equal ingredients give the same proposition.**

This is the whole content of "the rebuilt layer's statement is/is not a different statement".
It is deliberately stated with `Iff`s rather than equalities, because the two relations being
compared are *different inductive types* (`NormalEq` and a re-erected `NormalEqSE`), so no
`rfl` is available and nothing but a pointwise equivalence can be had. -/
theorem crSchema_congr {W W' : List VExpr → Prop}
    {N N' RS RS' R R' : List VExpr → VExpr → VExpr → Prop}
    (hW : ∀ Γ, W Γ ↔ W' Γ)
    (hN : ∀ Γ a b, N Γ a b ↔ N' Γ a b)
    (hRS : ∀ Γ a b, RS Γ a b ↔ RS' Γ a b)
    (hR : ∀ Γ a b, R Γ a b ↔ R' Γ a b) :
    CRSchema W N RS R ↔ CRSchema W' N' RS' R' := by
  constructor
  · intro H _ _ _ _ hw hn hr
    obtain ⟨o, h1, h2⟩ := H ((hW _).2 hw) ((hN _ _ _).2 hn) ((hR _ _ _).2 hr)
    exact ⟨o, (hRS _ _ _).1 h1, (hN _ _ _).1 h2⟩
  · intro H _ _ _ _ hw hn hr
    obtain ⟨o, h1, h2⟩ := H ((hW _).1 hw) ((hN _ _ _).1 hn) ((hR _ _ _).1 hr)
    exact ⟨o, (hRS _ _ _).2 h1, (hN _ _ _).2 h2⟩

/-- **The negative form, which is the one the verdict uses.**  A refuted confluence statement
stays refuted under any *inert* change of ingredients — in particular under enlarging the
conversion relation by rules that cannot fire. -/
theorem not_crSchema_of_inert {W W' : List VExpr → Prop}
    {N N' RS RS' R R' : List VExpr → VExpr → VExpr → Prop}
```

### M4 [2026-09-04T02:04:35Z] ChurchRosser.lean: NormalEq (165-) and ParRed (752-) constructor lists
```
---- NormalEq 160-240 ----
    exact a.rec (ih1 hf) (ih2 ha)

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ .sort l₂
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ .const c ls'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    A::Γ ⊢ body₁ ≡ₚ body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e →
    Γ ⊢ e' ≡ₚ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ h'

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e1 ≡ e2 := by
  induction H with
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 =>
    exact ⟨_, .appDF ((ih1 hΓ).of_l henv hΓ hf₁) ((ih2 hΓ).of_l henv hΓ ha₁)⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | lamDF hA₁ hA₂ _ ihB =>
    have ⟨_, hB⟩ := ihB ⟨hΓ, _, hA₁.hasType.1⟩
    exact ⟨_, .trans (.symm <| .lamDF hA₁ hB.symm) (.lamDF hA₂ hB.hasType.2)⟩
  | forallEDF hA₁ hA hB₁ _ ihA ihB =>
    exact have hΓ' := ⟨hΓ, _, hA₁.hasType.1⟩
      ⟨_, .trans (.symm <| .forallEDF hA₁ hB₁)
        (.forallEDF (hA₁.transU_l henv hΓ (ihA hΓ)) ((ihB hΓ').of_l henv hΓ' hB₁))⟩
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_r henv hΓ ⟨_, .lamDF hA he⟩ (.eta h1)⟩
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_l henv hΓ (.symm (.eta h1)) ⟨_, .lamDF hA he⟩⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, .proofIrrel h1 h2 h3⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e2 ≡ₚ e1 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | lamDF h1 h2 h3 ih1 => exact .lamDF h2 h1 (ih1 ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := ⟨hΓ, _, h1.hasType.1⟩
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | etaL h1 _ ih =>
---- ParRed 745-800 ----
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact iha path _ he

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⋙ " e2:36 => CParRed Γ e1 e2

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- **E6**: a rule's `Check` obligations survive replacing the matched arguments by
`NormalEq`-related ones.

Needed by every route through `parRed`'s `appDF` × `extra` case: the rule fires on the
left-hand term with *its* matched arguments, so `r3`'s obligations — stated at the right-hand
term's arguments — have to be transported.  The leafwise hypothesis is the same one
`NormalEq.apply_pat` takes, and this is proved by composing two of those with the clause's
own `IsDefEqU`. -/
theorem _root_.Lean4Lean.Pattern.Check.OK.congr_normalEq {p : Pattern} (ck : p.Check)
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (hne : ∀ x A, Γ ⊢ m2 x : A → Γ ⊢ m2 x ≡ₚ m2' x)
    (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 m2' := by
  refine H.map fun a b h => ?_
  obtain ⟨T, hT⟩ := h
  have ha := NormalEq.apply_pat hΓ hne hT.hasType.1
  have hb := NormalEq.apply_pat hΓ hne hT.hasType.2
  exact ((ha.defeq hΓ).symm.trans henv hΓ ⟨_, hT⟩).trans henv hΓ (hb.defeq hΓ)

def NonNeutral (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  (∃ p r m1 m2, Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : ¬NonNeutral Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | app : ¬NonNeutral Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ⋙ m2' a) → Γ ⊢ e ⋙ r.1.apply m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
```

### M5 [2026-09-04T02:04:48Z] the Pat/Params rule interface (what ParRed.extra ranges over)
```
-- Params class def
Lean4Lean/Theory/Typing/ChurchRosser.lean:12:class Params where
Lean4Lean/Experimental/SExpr.lean:787:class Params where
Lean4Lean/Experimental/SExpr.lean:1487:class ParamsExtra [Params] where
---- ChurchRosser.lean: Params / Pat context, first 160 lines ----
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean
open Lean4Lean

namespace VEnv

open VExpr

class Params where
  env : VEnv
  henv : env.WF
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  /--
  `hΓ` is not optional.  Proving this field means applying the λ-abstracted rule
  (`VDefEq.lhs = mkLams Δ L`) to the matched arguments, and `IsDefEq.appDF` needs each
  argument well-typed at the *declared* domain -- so the typing of `e` has to be inverted.
  Both available routes require a well-formed context: `HasType.app_inv`
  (`Typing/Strong.lean`) goes through `H.strong henv hΓ`, and `IsDefEq.uniq`
  (`Typing/UniqueTyping.lean`) takes `hΓ` directly.  Without it the field is very likely
  still *true* -- an ill-formed `Γ` only lets `bvar` carry junk types, while the application
  rules still pin the recursor's arguments -- but it is not provable by any route in the
  tree.  The sole consumer (`NormalEq.parRed`'s `extra` case, below) already has `hΓ` in
  scope and passes it to `.trans_l henv hΓ` in the same expression, so this costs nothing.

  Compare `SExpr.IsDefEq.strong`, which was *false* for the same structural reason.  On this
  development, a rule stated about an arbitrary `Γ` with no well-formedness hypothesis
  should be treated as suspect by default.
  -/
  pat_wf : Pat p r → p.Matches e m1 m2 → OnCtx Γ (IsType env univs) →
    HasType env univs Γ e A →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  /--
  Every `extra` rule of `env` is a `Pat`-registered pattern **under some leading lambdas**.

  The λ-peeling is forced: `VDefEq.lhs` is a closed term, so a rule with parameters is
  λ-wrapped (`quotDefEq`'s lhs is `fun α r β f c a => Quot.lift α r β f c (Quot.mk r a)`),
  while `Pattern.Matches` only walks `const`/`app` spines. Without peeling this field is
  satisfiable only by environments whose every defeq is a bare δ-rule, which is why nothing
  instantiates `Params`. Peeling leaves `IsDefEq`, `VDefEq`, `Matches`, the `vdefeq`
  elaborator and `Theory/Quot.lean` untouched; the rejected alternative — storing `VDefEq`
  in applied form — would force `quotDefEq`, the elaborator and `QuotLemmas.lean` to be
  re-encoded.

  Note the `Check` obligations are discharged in the *extended* context `Δ.reverse ++ Γ`,
  which is exactly where the `ParRed.extra` step fires once `ParRed.lams` has wrapped it in
  `Δ.length` congruences.

  `hΓ` is not optional, for the same reason as `pat_wf`'s.  An ι-rule's index clauses are
  discharged by β-reducing `mkLams tel a` applied to the matched constructor arguments;
  `IsDefEq.beta` needs the function typed, typing a `mkLams` needs its telescope to be a
  well-formed context, and `OnCtx (tel.reverse ++ Δ.reverse ++ Γ)` unfolds to include
  `OnCtx Γ`.  Tail-weakening is free for `Lookup` — which is why the δ and quot cases need
  nothing — but `OnCtx` quantifies over every entry.  The sole consumer already holds the
  fact: `NormalEq.parRed`'s `extra` case (below) sits inside `IsDefEq.church_rosser`, whose
  `Γ` is an *index* of `IsDefEq`, so `induction H` reverts `hΓ` and reintroduces it in every
  case — which is why the sibling cases use it freely.  So this costs one argument at one
  call site.

  Compare `SExpr.IsDefEq.strong`, which was *false* for exactly this reason, and `pat_wf`,
  which was under-hypothesised for it.  Three for three: on this development a rule stated
  about an arbitrary `Γ` with no well-formedness hypothesis is suspect by default.

  **Level hypothesis at `univs`, not at a stray `uvars`.**  This field previously read
  `∀ l ∈ ls, l.WF uvars`, where `uvars` was an *auto-bound implicit* of the field -- a fresh
  universally quantified `Nat`, unrelated to `Params.univs`.  (`uvars` is the section
  variable of `Theory/Typing/Basic.lean`, where `IsDefEq.extra` states the same hypothesis
  correctly; inside this class it auto-bound instead of resolving.)  That made the field ask
  for the conclusion at level lists that are *not* well-formed for the judgment, which
  `Theory/Typing/PatternRules.lean`'s `Pat.extra` cannot supply -- its ι case needs
  `IsDefEqU.instL`, which needs `l.WF univs`.  The sole consumer
  (`NormalEq.parRed`'s `extra` case) holds `l.WF univs`, so narrowing costs it nothing.
  -/
  extra_pat : OnCtx Γ (IsType env univs) →
    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
      Pat p r ∧ p.Matches L m1 m2 ∧
      r.2.OK (IsDefEqU env univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2

variable [Params]
open Params

theorem Params.pat_not_var : ¬Pat (.var p) r := (nomatch pat_simple ·)

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- **Universe uniqueness at `Params`' environment — derived, not assumed.**

`appDF_proofIrrel` and `descend`'s two E3 branches used to take this as an explicit
hypothesis `hsu`, on the stated grounds that getting it from `IsDefEqU.sort_inv` "would be
circular, since it is one of the facts confluence exists to deliver".  **That is false as of
today.**  Three checks, all mechanical:

* `Params.henv` is `env.WF`, and `VEnv.WF.sortUniq'` (`Theory/Typing/Injectivity.lean`)
  proves `env.SortUniq U` from it.
* `Injectivity.lean` is *already* in this file's import closure -- `ChurchRosser` imports
  `UniqueTyping`, which imports `Injectivity` -- so no import moves and no cycle is created.
  The dependency runs `ChurchRosser → Injectivity`, i.e. confluence **consumes** the
  Π/sort-inversion family; it does not supply it.
* Using it widens no cone: `WF.sortUniq'` is already a transitive dependency of
  `IsDefEq.uniq` and `IsDefEqU.of_l`, which `appDF_proofIrrel` and `descend` call directly.

`SortUniq` carries the two side conditions `u.WF univs`, `v.WF univs` that `hsu` did not;
they are recovered from the typings themselves by `HasType.sort_inv`. -/
theorem Params.sortUniq {Γ : List VExpr} {e : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (h1 : Γ ⊢ e : .sort u) (h2 : Γ ⊢ e : .sort v) : u ≈ v :=
  WF.sortUniq' (U := univs) henv hΓ
```

### M6 [2026-09-04T02:05:39Z] StructEtaPrice.lean: the 14th constructor + StructEtaG statement
```
import Lean4Lean.Verify.TypeChecker.EtaUnitRefute
import Lean4Lean.Theory.SetModel.UnitOracleLarge

/-!
# Pricing the fourteenth constructor

`Verify/TypeChecker/EtaResidual.lean` reduces both eta holes
(`Verify/TypeChecker/IsDefEq.lean:558`, `:1054`) to the single hypothesis `c.venv.StructEtaG`,
and `Verify/TypeChecker/EtaUnitRefute.lean` **refutes** deriving that from environment
well-formedness: `MutField.unitEnv` has a proved `VEnv.WF` and satisfies neither `UnitEta` nor
`StructEtaG`.  So structure eta has to become a fourteenth constructor of `VEnv.IsDefEq`
(`Theory/Typing/Basic.lean`, currently thirteen).

**This file is the price, not the change.**  Nothing here edits `IsDefEq`, or any existing file.
It states the constructor in a private copy of the relation, fires it at two real structures,
and — the part that matters — measures what breaks.

## 1. The induction-site count, measured 2026-09-03, 17:01–17:25 UTC

Not grepped: computed.  A scratch script walked the built population (421 modules) and, for
every declaration in `Lean4Lean`, asked whether its **proof term** applies an eliminator of the
relation (`.rec`, `.recOn`, `.casesOn`, `.brecOn`, `.below.*`, `.ndrec`, `.induct`).  The
compiler-generated eliminators of the inductive's own module are netted out; what is left is
hand-written induction and `cases`.

| relation | hand-written eliminator sites | must gain the constructor? |
|---|---|---|
| `VEnv.IsDefEq` | **22** | yes — this is the change |
| `VEnv.IsDefEqStrong` (`Strong.lean`) | **31** | yes — `IsDefEq.strong'` converts |
| `VEnv.NormalEq` (`ChurchRosser.lean`) | **31** | yes — `church_rosser`'s target |
| `VEnv.ParRed` (`ChurchRosser.lean`) | **26** | yes — `NormalEq`'s engine |
| `VEnv.ParRedK` (`KEta.lean`) | **23** | yes — `ParRed.toK` |
| `VEnv.IsDefEqE` (`Enlarged.lean`) | **3** | yes — `IsDefEq.toE` converts |
| `VEnv.IsDefEqRaw` (`RawDefEq.lean`) | **0** | yes — `IsDefEq.raw` converts, nothing inducts |
| `VEnv.ParRedS` | 0 | no — it is a closure `def`, not an inductive |
| **total** | **136** | |

`IsDefEq`'s own 22, by module: `Typing/Lemmas` 9 (`weakN`, `instN`, `instL`, `mono`, `closedN'`,
`levelWF`, `isType'`, `forallE_inv'`, `sort_inv'`), `Typing/Strong` 2 (`strong'`, `mono_uvars`),
`Typing/ConstSubst` 2 (`substC`, `noCSubst'`), and one each in `Typing/{Strengthen,
StrengthenNarrow,RawDefEq,CycleConv,ChurchRosser,ConstSubstNested,ConstVar}` and
`SetModel/Consts` (`constsIn`).  `SetModel/SoundInduction`'s `soundAbove` is on the
`IsDefEqStrong` line, not this one — the model induction runs on the strong relation.

**Which of the 136 are real work.**  The new rule's left-hand side is a *bare variable* `e`,
so **no case can be discharged by `nofun` or by a head-shape `simp`** — the split that would
normally let an inversion lemma drop a case does not exist here.  Concretely:

* **~40 congruence/stability sites** (`weakN`, `instN`, `instL`, `mono`, `mono_uvars`,
  `closedN'`, `levelWF`, `isType'`, and their `Strong`/`E`/`Raw` counterparts) need the
  η-expansion to commute with the operation.  `VInductDecl'.etaExpansion_instL` and
  `projAll_instL` exist; `projTerm_instN` exists; **`projTerm_weakN`, `projTermG_weakN`,
  `etaExpansion_weakN`, `etaExpansionG_weakN` and `etaExpansionG_instL` do not**
  (`scripts/exists.lean`, this round).  Five missing commutation lemmas over a recursor spine
  is the floor.
* **~20 inversion sites** (`forallE_inv'`, `sort_inv'`, `Injectivity`'s five,
  `Shape`/`Spine`/`Sort*`'s twelve) currently dismiss `extra` and friends by head shape.  The
  new case arrives with an arbitrary `e` on the left and a `const`-headed spine on the right, so
  each needs a *typing* argument — "no term is simultaneously a sort and an inhabitant of a
  structure" — instead of a shape argument.  That is the `SortUniq`/`UnivDiscrim` machinery,
  and it is where the existing injectivity holes live.
* **1 site is the model** (`SetModel/soundAbove`), §8 below.
* **1 site is the wall** (`church_rosser`): the rule is not a rewrite, and §6 shows it is not
  merely hard but **incompatible with the no-confusion lemma that chain exists to prove**.

## 2. What this file adds

* `IsDefEqSE` (§3) — the fourteen-constructor relation, so the constructor is *stated* rather
  than described.  `IsDefEq.toSE` embeds the thirteen, one line each: that is the machine-checked
  form of "each induction gains exactly one case".
* `VEnv.StructEtaGSE` and `structEtaGSE` (§4) — the constructor is **strong enough**: it gives
  `StructEtaG`'s statement over the new relation *by construction*, so
  `TypeChecker.Inner.etaHoles_of_structEtaG` applies verbatim once the swap is made.
* Two firings (§5): at `MutField.unitEnv`'s zero-field member with an **axiom** inhabitant, and
  at `MutField.declEnv`'s positive-field member.  Both are real structures in `Type` inside a
  two-type mutual block, so the rule is not vacuous and not zero-field-only.
* `eta_and_constNoConf_incompatible` (§6) — **the price, and it is route-independent**: *no*
  relation whatever can satisfy structure eta at `unitEnv` and const-head no-confusion at the
  same time.  Instantiated at `IsDefEqSE`, this says `VEnv.IsDefEq.constApp_inv`
  (`Verify/Typing/ConstSpine.lean:248`, 187 transitive users) is **false** for the extended
  relation, not merely unproved.  §6 also records that this is a fact about *Lean*, not about
  this design: `structure A where` / `axiom foo : A` / `example : foo = A.mk := rfl` typechecks
  in Lean 4, so const-head no-confusion is false in the real kernel and the existing
  `constApp_inv` is a lemma about a relation strictly weaker than real definitional equality.
* `eq_singleton_of_recProp` (§8) — the set-model verdict, machine-checked: the model **does**
  validate zero-field surjective pairing, and it is *forced* rather than chosen, by the
  membership obligation `InductOracleOK` already puts on the **recursor**.  This contradicts
  `SetModel/UnitEtaPairing.lean`'s claim that "a model satisfying `InductOracleOK` may interpret
  a zero-field structure as a two-element set and refute eta outright"; §6 says exactly which
  step that claim misses.

## 3. A cost nobody has named: the constructor cannot be written where `IsDefEq` lives

`Theory/Typing/Basic.lean` imports `Theory/VEnv` and nothing else.  The η-expansion needs
`VInductDecl'.etaExpansionG`, hence `projTermG` (`Verify/Typing/ProjGen.lean`), hence
`VInductDecl'` (`Theory/Inductive/Decl.lean`) — and `Decl.lean` imports `Theory/Typing/Lemmas`,
which imports `Basic`.  **Writing the constructor into `Basic.lean` is a dependency cycle.**

It is breakable, and the shape of the break is the third cost line: `VInductDecl'`, `projCore`,
`projArgs`, `projTerm`, `projTermG` and `etaExpansion(G)` are *purely syntactic* — `Telescope.lean`
imports only `Theory/VExpr` — so `Decl.lean` and `Structure.lean` split into a syntax half
(below `Basic.lean`) and a `WF` half (above it), and `ProjGen.lean`'s `projTermG` definition moves
with them.  That is a three-file split plus an import re-layer, before a single proof case is
written.  §7's alternative avoids it.
-/

namespace Lean4Lean

open VExpr

/-! ## 3. The fourteen-constructor relation

`VEnv.IsDefEq`'s thirteen constructors verbatim (`Theory/Typing/Basic.lean:18`), plus
`structEta`.  Kept in a private copy so that the real relation is untouched.

**Three deliberate choices in `structEta`, each of which is a claim about the right shape.**

1. **The typing premises are in the *new* relation**, not the old one: `hpsA` is `HasArgsSE`
   and `he` is `IsDefEqSE Γ e e ((const S us).mkApp ps)`.  `VEnv.StructEtaG` states them in
   the thirteen-constructor relation because it has to — it is a predicate *about* that
   relation — but a constructor whose premises could not use the rule itself would not be
   closed under its own conclusion, and the bridge from `TrExprS` supplies typing in whatever
   relation `venv` carries.  This is `beta`/`eta`/`proofIrrel`'s convention.
2. **`IsStructureG` stays as it is.**  It is environment data (`env.constants`, a `VEnv.WF'`
   history), not a typing judgement, so it does not move with the relation.
3. **`recFields = []` is kept** and `IsStructureG`'s `types` narrowing is not reinstated —
   exactly `VEnv.StructEtaG`'s choice, for exactly its reasons (`EtaStructG.lean`: the checker's
   gate `isNonRecStructure` does read `isRec`, so the bridge can supply `recFields = []` at
   every site, and dropping it is not known to keep the right-hand side typeable).

The F17 clause `D.isLE = true ∨ ∀ k < n, (fields.getD k).lvl.inst us ≈ .zero` is not optional:
`IsDefEq` implies both sides are well typed, so without it the rule is *false* rather than
useless at a small-eliminating structure with a large field
(`Verify/Typing/ProjLevelWitness.lean`'s `barDecl`). -/

namespace VEnv

variable (env : VEnv) (uvars : Nat)

mutual

/-- **`VEnv.IsDefEq` with structure eta as a fourteenth constructor.** -/
---- the eta constructors of IsDefEqSE (174-215) ----
    IsDefEqSE Γ e e (.forallE A B) →
    IsDefEqSE Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)
  | proofIrrel :
    IsDefEqSE Γ p p (.sort .zero) → IsDefEqSE Γ h h p → IsDefEqSE Γ h' h' p →
    IsDefEqSE Γ h h' p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    IsDefEqSE Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)
  /-- **Structure eta (surjective pairing).**  `VEnv.StructEtaG`'s clauses, as a rule. -/
  | structEta {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
      {us : List VLevel} {ps : List VExpr} {e : VExpr} :
    env.IsStructureG S D j T C →
    T.indices = [] →
    C.recFields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF uvars) →
    ps.length = D.np →
    HasArgsSE Γ (D.params.map (VExpr.instL us)) ps →
    IsDefEqSE Γ e e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    IsDefEqSE Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)

/-- `VEnv.HasArgs` over the extended relation; `structEta`'s parameter-spine premise. -/
inductive HasArgsSE : List VExpr → List VExpr → List VExpr → Prop where
  | nil : HasArgsSE Γ [] []
  | cons :
    IsDefEqSE Γ a a A → HasArgsSE Γ (VExpr.instTele a As) as →
    HasArgsSE Γ (A :: As) (a :: as)

end

/-! ## 4. The thirteen embed, and the new rule is strong enough

`toSE` is the machine-checked form of "each induction gains exactly one case": thirteen
one-line cases, no side conditions, no reshuffling.  Every one of the 136 sites in §1 that is a
*congruence* induction has this shape — the work there is not the thirteen old cases, it is the
fourteenth. -/

variable {env : VEnv} {uvars : Nat}

mutual

```

### M7 [2026-09-04T02:05:51Z] StructEtaPrice.lean §7 — the closed-VDefEq alternative (structEta_of_extra)
```
-- §7 starts at line 378
/-! ## 7. The alternative that needs **no** new constructor, priced

`docs/design-inductive.md` §6.3 records that structure eta "cannot be added as a `VDefEq`,
because `Pattern.Matches` only matches `const`-headed spines and the rule's left-hand side is a
variable".  **The premise is right and the conclusion does not follow.**  The rule's left-hand
side is a variable only if you insist on stating the rule *pointwise*.  State it between the two
closed functions instead —

```
    (fun ps… x => x)  ≡  (fun ps… x => S.mk ps (proj₀ x) … )   :  ∀ ps…, S ps → S ps
```

— and both sides are closed `VExpr`s, so the pair is a perfectly ordinary `VDefEq` and the
existing `extra` constructor carries it.  Every pointwise instance comes back by `appDF` and
`beta`, which are already there.

`structEta_of_extra` below is that derivation, machine-checked at the zero-parameter zero-field
case (which is `isDefEqUnitLike`'s hole exactly): from `env.defeqs (etaDfZ S mk)` and the term's
type, `e ≡ S.mk : S` **using only the thirteen constructors**.  `extra`, `appDF`, two `beta`s, a
`symm` and two `trans`.

### Price comparison


| | 14th constructor (§3) | closed `VDefEq` (§7) |
|---|---|---|
| induction cases added | **136** (§1), ~20 of them needing typing arguments | **0** |
| missing commutation lemmas | 5 (`projTermG_weakN`, …) | **0** — `extra`'s `instL` case already exists |
| file split / import re-layer | 3 files (§3 end) | **0** |
| `church_rosser` | new `NormalEq`/`ParRed` rule, no rewrite orientation | `extra` case, already written |
| `constApp_inv` (187 users) | **refuted** (§6) | **refuted** (§6) — route-independent |
| `PatWF` / `PatFreeHead` | unchanged | must admit a `lam`-headed rule, or exempt these rules |
| new work in `addInduct'` | none | `D.etaRules : List VDefEq` + `VDefEq.WF` for each |
| right-hand side typeable | needed | needed (same `StructureClosed` chain) |

**The `VDefEq` route is cheaper on every line except two**, and those two are where its work
concentrates: `VEnv.PatWF` currently expects every rule in `env.defeqs` to be a `Pattern`, and a
`lam`-headed rule is not one.  That is a *localised* statement change (one predicate, plus
`patWF_of_wf`) against §1's 136 sites, and it is forced in the other route too — §6 shows
`PatFreeHead`-based no-confusion has to give either way.  `addInduct'` gaining an `etaRules` fold
mirrors the `iotaRules` fold it already performs, and `VDefEq.WF` for the eta rule is the same
projection-typing obligation the constructor's F17 clause encodes.

**What this section does not settle.**  The telescoped form (parameters, positive fields) is not written
here: `structEta_of_extra` is the zero-parameter zero-field instance.  The general schema is the
same three moves per binder (`appDF` down the parameter spine, then `beta` on both sides), and
`Theory/Inductive/Telescope.lean`'s `instAllTele`/`instTele` lemmas are what it would run on; the
`beta` chain over a telescope is the one piece of real work, and `VEnv.HasArgsDF`
(`StructureClosed.lean:500`) is the shape it wants.  Estimated at one file.  That is the number
to compare against 136. -/

/-- The zero-parameter zero-field structure-eta rule, as a `VDefEq`: `(fun x => x) ≡ (fun x => mk)`
at `S → S`.  Both sides closed, so `VEnv.IsDefEq.extra` carries it. -/
def etaDfZ (S mk : Lean.Name) : VDefEq where
  uvars := 0
  lhs := .lam (.const S []) (.bvar 0)
  rhs := .lam (.const S []) (.const mk [])
  type := .forallE (.const S []) (.const S [])

/-- **Structure eta from the *existing* thirteen constructors**, given the rule as environment
data.  No fourteenth constructor, no induction case anywhere.

`extra` fires at the closed pair, `appDF` applies both sides to `e`, and the two `beta`s collapse
the redexes to `e` and to `S.mk`.  This is the whole content of the table's "induction cases
added: 0" row. -/
theorem structEta_of_extra {env : VEnv} {U : Nat} {Γ : List VExpr} {S mk : Lean.Name} {e : VExpr}
    (hdf : env.defeqs (etaDfZ S mk))
    (hmk : env.constants mk = some ⟨0, .const S []⟩)
    (he : env.HasType U Γ e (.const S [])) :
    env.IsDefEq U Γ e (.const mk []) (.const S []) := by
  have hx : env.IsDefEq U Γ (.lam (.const S []) (.bvar 0))
      (.lam (.const S []) (.const mk [])) (.forallE (.const S []) (.const S [])) := by
    have h := VEnv.IsDefEq.extra (env := env) (uvars := U) (Γ := Γ) (ls := []) hdf nofun rfl
    simpa [etaDfZ, VExpr.instL] using h
  have h1 : env.IsDefEq U Γ (.app (.lam (.const S []) (.bvar 0)) e)
      (.app (.lam (.const S []) (.const mk [])) e) (.const S []) := by
    simpa [VExpr.inst] using hx.appDF he
  have h2 : env.IsDefEq U Γ (.app (.lam (.const S []) (.bvar 0)) e) e (.const S []) := by
    have h := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ) (A := .const S [])
      (e := .bvar 0) (B := .const S []) (.bvar (.zero ..)) he
    simpa [VExpr.inst] using h
  have h3 : env.IsDefEq U Γ (.app (.lam (.const S []) (.const mk [])) e)
      (.const mk []) (.const S []) := by
    have hc : env.IsDefEq U (.const S [] :: Γ) (.const mk []) (.const mk []) (.const S []) := by
      simpa [VExpr.instL] using
        VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := .const S [] :: Γ)
          (ls := []) (ls' := []) hmk nofun nofun rfl .nil
    have h := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ) (A := .const S [])
      (e := .const mk []) (B := .const S []) hc he
    simpa [VExpr.inst] using h
  exact h2.symm.trans (h1.trans h3)

/-- **Anti-vacuity for §7**: the hypothesis is satisfiable and the derivation lands.  At
`MutField.unitEnv` with the rule added, the *thirteen*-constructor relation already proves
`foo ≡ A.mk` — the very instance §6 shows no-confusion cannot survive.

Note what this does and does not certify.  It certifies that the thirteen constructors suffice
*given the rule*.  It does **not** certify that the rule may be added to a well-formed
environment: `VEnv.addDefEq` is total and answers to no `VDecl.WF`, so making the rule legitimate
means extending `addInduct'` with an `etaRules` fold and proving `VDefEq.WF` for each — the
table's last-but-two row, and the alternative's real cost. -/
theorem MutField.structEta_of_extra_fires :
    (MutField.unitEnv.addDefEq (etaDfZ `MutField.A `MutField.A.mk)).IsDefEq 0 []
      (.const `MutField.foo []) (.const `MutField.A.mk []) (.const `MutField.A []) := by
  have hle : MutField.unitEnv ≤ MutField.unitEnv.addDefEq (etaDfZ `MutField.A `MutField.A.mk) :=
    ⟨id, Or.inr⟩
  exact structEta_of_extra (Or.inl rfl) (hle.constants MutField.unitEnv_Amk)
    (by simpa using (MutField.unitEnv_foo_hasType).mono hle)

/-! ## 8. The set model: verdict, with evidence

**Verdict: the set model *does* validate structure eta, and it is forced rather than chosen.**
`SetModel/UnitEtaPairing.lean`'s stated residual —

> `OracleOK` constrains a type former's denotation by **membership only**, so a model satisfying
> `InductOracleOK` may interpret a zero-field structure as a two-element set and refute eta
> outright

— **is wrong**, and the step it misses is named exactly: `InductOracleOK.consts` quantifies over
`D.allConsts`, and `allConsts` contains the **recursor** (`SetModel/EqOracle.lean`'s
`eq_allConsts` computes it: `[Eq, Eq.refl, Eq.rec]`).  The recursor's own `OracleOK.type` field
asks `o (S.rec) us ∈ interp (D.recType j).instL us`, and `recType` ends in `∀ x : S ps, motive … x`
after quantifying `motive` over the **full** set-theoretic function space — `interp`'s `forallE`
clause is `mkForallType`, `{f ∈ (⋃…)^(Gρ) ; …}`, not a definable-families subset
(`Theory/SetModel/Interp.lean:186`).  So the motive may be the *characteristic family of the
constructor*, and then an inhabitant of the recursor type exists only if every element of the
type former's denotation is the constructor's value.  That is surjective pairing, and it is a
consequence of an obligation the model already carries — no new one.

`eq_singleton_of_recProp` below is that argument, machine-checked, at zero fields: the
set-theoretic core with no `interp`, no `VInductDecl'`, no `Above`.  Read it together with
`SetModel/UnitOracleLarge.lean`, which is the same fact from the other side: its oracle sends
`Unit1 ↦ {•}` — a singleton — and closes `InductOracleOK` there, and its
`pt_not_mem_interpL_recType_of_ne` is this file's contradiction step at a domain that happens to
be a singleton already.

**What is still owed, precisely.**  Two steps, and both are bookkeeping rather than mathematics:

1. *The unfolding.*  `interp (D.recType j)` must be peeled to the shape `eq_singleton_of_recProp`
   consumes.  `SetModel/UnitOracleLarge.lean` performs exactly this peel at `unitDeclLE`
   (`interpL_motTyU`, six `mkLam_mem_mkForallType_of_dom` layers); at a general block it is
   `recType`'s telescope instead of two binders.  `mkForallType_const_eq_pow` below is the one
   general lemma that peel was missing — `mkForallType_singleton_const` only covers a singleton
   domain, which is the case being *proved* and so cannot be assumed.
2. *The `PropSplit` side condition.*  `interp (.app f a)` collapses to `pt` when
   `L.IsProof M Γ f`.  The argument needs the motive not to be classified as a proof, which
   `PropSplit`'s agreement with typing gives (a motive has type `S ps → Sort u`, not a
   proposition) but which no lemma in the tree states in that form.

**At positive fields** the same argument gives the full rule rather than the singleton: take the
family `m x = ⟦x = mk ps (proj₀ x) … ⟧` and the recursor's type forces it inhabited everywhere,
which is `SetModel/Inductive.lean`'s `mem_Ind_iff` ("no junk") read through the oracle instead of
through the fixpoint.  The model's carrier is *built* from Kuratowski tuples precisely so this
holds on the nose (`Inductive.lean:241`), and `mem_Ind₃_fibre_iff_of_zero_field` is the zero-field
half already proved.  So the model is not the obstacle; **the obstacle is §6.** -/

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **`mkForallType` with a constant codomain over a *non-empty* domain is the function space.**

The general form of `UnitAudit.mkForallType_singleton_const`, whose `G ρ = {a}` hypothesis cannot
be used here: a singleton domain is the *conclusion* of `eq_singleton_of_recProp`, so assuming it
would beg the question.  Non-emptiness is all that is needed, and the constructor supplies it. -/
theorem mkForallType_const_eq_pow {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ Y a : V}
    (ha : a ∈ G ρ) (hF0 : ∀ v ∈ G ρ, F ρ v = Y) :
    mkForallType G hG F hF ρ = (Y ^ G ρ : V) := by
  have hFU : mkFamUnion G hG F hF ρ = Y := by
    rw [mem_ext_iff]; intro y
    rw [mem_mkFamUnion_iff]
    exact ⟨fun ⟨v, hv, hy⟩ ↦ (hF0 v hv) ▸ hy, fun hy ↦ ⟨a, ha, (hF0 a ha) ▸ hy⟩⟩
  rw [mem_ext_iff]; intro f
  rw [mem_mkForallType_iff, hFU]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun v hv y hy ↦ ?_⟩⟩
  rw [hF0 v hv]
  exact (mem_of_mem_functions h hy).2

/-- The body of the characteristic family: `{•}` at `mkv`, `∅` elsewhere.  Written with `sep`
rather than an `if` because `definability` does not see through `ite`. -/
noncomputable def charBody (mkv : V) : V → V → V := fun _ v ↦ {_z ∈ ({pt} : V) ; v = mkv}

theorem charBody_definable (mkv : V) : ℒₛₑₜ-function₂[V] (charBody mkv) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T _ v ↦ T = charBody mkv ∅ v) by exact this
  have e : ∀ T ρ v : V, T = charBody mkv ρ v ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ v = mkv) := by
    intro T ρ v; rw [mem_ext_iff]; simp [charBody, mem_sep_iff]
  simp only [e]; definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem constDom_definable (Sv : V) : ℒₛₑₜ-function₁[V] (fun _ : V ↦ Sv) := by definability

/-- **The characteristic family of `{mkv}` over `Sv`, as an element of `UProp ^ Sv`.**  This is
the motive the recursor's type obligation cannot survive unless `Sv = {mkv}`.  It is a legal
motive because `interp`'s `forallE` clause is the *full* function space. -/
noncomputable def charFam (Sv mkv : V) : V :=
  mkLam (fun _ ↦ Sv) (constDom_definable Sv) (charBody mkv) (charBody_definable mkv) ∅

theorem charFam_value {Sv mkv v : V} (hv : v ∈ Sv) :
    (charFam Sv mkv) ‘ v = {_z ∈ ({pt} : V) ; v = mkv} :=
  mkLam_value (G := fun _ ↦ Sv) hv

theorem charFam_mem_pow {Sv mkv : V} : charFam Sv mkv ∈ ((UProp : V) ^ Sv : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hv, mem_UProp_iff.mpr sep_subset⟩
  · exact ⟨charBody mkv ∅ v, mem_mkLam_iff.mpr ⟨v, hv, rfl⟩, fun y hy ↦ by
      obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
      obtain ⟨rfl, rfl⟩ := kpair_inj he; rfl⟩

/-- **Zero-field surjective pairing is *forced* in the set model.**

`H` is what `OracleOK.type` says at the recursor of a zero-field, index-free, one-constructor
block, with `interp`'s binders peeled: for every motive `m` in the motive space, every inhabitant
of `m mk`, and every `x` in the type former's denotation, the recursor's value lands in `m x`.
(At `elimLvl = .zero` the whole `recType` is propositional and the value is `•` itself, which is
the shape written here; at a large eliminator the value is a function and `pt` is replaced by
"some element of", with the same proof.)

The conclusion is that the denotation is the *singleton* `{mk}` — so any two inhabitants are
equal in the model, which is exactly what `isDefEqUnitLike` reports and what
`VEnv.UnitEta.unitLike` states in the spec.

**No `Above`, no `κ`, no chain of inaccessibles**: the argument is finite and uses only
Replacement and Power. -/
theorem eq_singleton_of_recProp {Sv mkv : V} (hmk : mkv ∈ Sv)
    (H : ∀ m ∈ ((UProp : V) ^ Sv : V), pt ∈ m ‘ mkv → ∀ x ∈ Sv, pt ∈ m ‘ x) :
    Sv = ({mkv} : V) := by
  rw [mem_ext_iff]
  intro x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (mem_singleton_iff.mp hx) ▸ hmk⟩
  have h1 : pt ∈ (charFam Sv mkv) ‘ mkv := by
    rw [charFam_value hmk]; exact mem_sep_iff.mpr ⟨by simp, rfl⟩
  have h2 := H _ charFam_mem_pow h1 x hx
  rw [charFam_value hx] at h2
  exact mem_singleton_iff.mpr (mem_sep_iff.mp h2).2

/-- **The bound the other way: the hypothesis is not vacuous and not trivially true.**  Drop the
`pt ∈ m ‘ mkv` premise and `H` becomes false at every `Sv` with an element (take `m` to be the
characteristic family of a *different* point); keep it and `H` is satisfied at `Sv = {mkv}`
itself.  So `eq_singleton_of_recProp` is a real implication at a satisfiable hypothesis. -/
theorem recProp_at_singleton {mkv : V} :
    ∀ m ∈ ((UProp : V) ^ ({mkv} : V) : V), pt ∈ m ‘ mkv → ∀ x ∈ ({mkv} : V), pt ∈ m ‘ x :=
  fun _ _ h _x hx => (mem_singleton_iff.mp hx) ▸ h

end SetModel

end Lean4Lean

/-! ## 9. Axiom bar

Nothing here introduces an axiom.

**CORRECTED 2026-09-03 — this paragraph was wrong on both counts, and both were measured.**  It
claimed `structEtaSE_foo` and `eta_and_constNoConf_incompatible` both inherit `sorryAx` through
the same four census holes.  In fact:

* `MutField.structEtaSE_foo` (cone 4217) is **hole-free** — its cone does not reach `sorryAx` at
  all, so the eta instance this file's argument rests on costs nothing;
* `eta_and_constNoConf_incompatible` (cone 5237) reaches **exactly one** hole,
  `VEnv.IsDefEqU.forallE_inv_stratified` — **not four**.

That matters for how the headline may be stated: the incompatibility is conditional on **one**
open statement, not on a four-hole cluster.  It also means "route-independent" (true of its
quantification over `R`) must not be read as "independent of the thirteen"; it is not.

**Also corrected**: §6's remark that the surviving side condition does not exist in the tree.  It
does — it is `VEnv.ConstNoConf`'s existing `IsType` guard, and `Theory/Typing/NoConfRepair.lean`
shows that guard survives eta while `¬ IsProof` does not.  The two conditions §6 offers instead
(exempt structure-constructor heads; restrict to zero-field or subsingleton structures) are both
**refuted** there, hole-free: `guard_rejects_an_axiom` (cone 382) shows *any* guard on head names
must reject an axiom inhabitant, because transitivity produces a violating pair from which the
constructor is absent.  The **model** section, the **alternative** section, the embedding and both firings are
hole-free: `after ⊆ before` on every line. -/

#print axioms Lean4Lean.VEnv.IsDefEq.toSE
#print axioms Lean4Lean.VEnv.HasArgs.toSE
#print axioms Lean4Lean.VEnv.structEtaGSE
#print axioms Lean4Lean.MutField.structEtaSE_foo
#print axioms Lean4Lean.MutField.structEtaSE_B
#print axioms Lean4Lean.eta_and_constNoConf_incompatible
#print axioms Lean4Lean.constNoConf_false_for_IsDefEqSE
#print axioms Lean4Lean.structEta_of_extra
#print axioms Lean4Lean.MutField.structEta_of_extra_fires
#print axioms Lean4Lean.SetModel.mkForallType_const_eq_pow
#print axioms Lean4Lean.SetModel.charFam_mem_pow
#print axioms Lean4Lean.SetModel.eq_singleton_of_recProp
#print axioms Lean4Lean.SetModel.recProp_at_singleton
```

### M8 [2026-09-04T02:06:27Z] Pattern / SimplePattern / Matches / mkLams
```
-- Pattern.lean outline
8:inductive Pattern where
13:def Pattern.varN (p : Pattern) : Nat → Pattern
17:inductive Subpattern (p : Pattern) : Pattern → Prop where
23:theorem Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
27:theorem Subpattern.trans {p₁ p₂ p₃} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₃) : Subpattern p₁ p₃ := by
34:theorem Subpattern.sizeOf_le {p₁ p₂} (H₁ : Subpattern p₁ p₂) : sizeOf p₁ ≤ sizeOf p₂ := by
37:theorem Subpattern.antisymm {p₁ p₂} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₁) : p₂ = p₁ := by
45:inductive Arity (p : Pattern) : Nat → Pattern → Prop where
50:theorem Arity.subpattern : Arity p n p' → Subpattern p p'
55:def Pattern.inter : Pattern → Pattern → Option Pattern
63:theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]
65:theorem Pattern.inter_comm (p q : Pattern) : p.inter q = q.inter p := by
68:inductive Pattern.LE : Pattern → Pattern → Prop where
74:def Pattern.Path : Pattern → Type
85:def Pattern.LPath : Pattern → Type
91:def Pattern.LPath.head : (p : Pattern) → p.LPath
96:inductive Pattern.Matches :
103:theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
114:def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
119:inductive Pattern.RHS (p : Pattern) where
125:inductive Pattern.Check (p : Pattern) where
132:def Pattern.RHS.apply {p : Pattern} (m1 : p.LPath → List VLevel)
138:theorem Pattern.RHS.lift'_apply {p : Pattern} {m1 m2} (r : p.RHS) :
143:theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
147:theorem Pattern.matches_lift' {p : Pattern} {e : VExpr} {m1 m2'} :
175:theorem Pattern.matches_liftN {p : Pattern} {e : VExpr} {m1 m2'} :
179:theorem Pattern.RHS.instN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
184:theorem Pattern.matches_instN {p : Pattern} {e : VExpr} {m1 m2} (H : p.Matches e m1 m2) :
195:theorem Pattern.matches_inter {p q : Pattern} {e : VExpr} :
247:theorem Pattern.matches_determ
250:def Pattern.Check.OK (defeq : VExpr → VExpr → Prop) {p : Pattern}
257:theorem VLevel.forall₂_getD {l l' : List VLevel}
267:theorem Pattern.Check.OK.map_levels
279:theorem Pattern.Check.OK.map
287:inductive SimplePattern where
291:def SimplePattern.toPattern : SimplePattern → Pattern
---- inductive Pattern + Matches + SimplePattern bodies ----
inductive Pattern where
  | const (c : Name)
  | app (f a : Pattern)
  | var (f : Pattern)

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')

inductive Pattern.Matches :
    (p : Pattern) → VExpr → (p.LPath → List VLevel) → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

inductive Pattern.RHS (p : Pattern) where
  /-- A closed term, instantiated at the levels found at the `const` leaf `lp`. -/
  | fixed (c : VExpr) (lp : p.LPath) (_ : c.Closed)
  | app (f a : RHS p)
  | var (e : p.Path)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)
  /-- `(m1 x).getD i ≈ (m1 y).getD j`: the level agreement an ι-rule needs between the
  recursor's leaf and the constructor's. -/
  | level (x : p.LPath) (i : Nat) (y : p.LPath) (j : Nat) (rest : Check p)

/-- The `const` leaves of a pattern. `Matches` records the universe level list found at
each of them, not just the head's: an ι-rule's pattern is `rec.{ls} a … (c.{ls'} b …)`,
and bridging `c.{ls'} b` to `c.{ls} b` needs `ls ≈ ls'`, which was not stateable while
`Matches` kept a single `List VLevel`. Requiring `ls' = ls` syntactically instead would be
unsound for confluence: `rec.{max u v} … (c.{max v u} …)` and `rec.{max u v} … (c.{max u v} …)`
are `NormalEq`-related by `constDF`, but only the second would be a redex. -/
def Pattern.LPath : Pattern → Type
  | .const _ => Unit
  | .app f a => f.LPath ⊕ a.LPath
  | .var f => f.LPath

/-- The leftmost `const` leaf: the pattern's head. -/
def Pattern.LPath.head : (p : Pattern) → p.LPath
  | .const _ => ()
  | .app f _ => .inl (LPath.head f)
  | .var f => LPath.head f

inductive Pattern.Matches :
    (p : Pattern) → VExpr → (p.LPath → List VLevel) → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (H1 : Pattern.Matches p e m1 m2) (H2 : Pattern.Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 with
  | const => let .const := H2; exact ⟨rfl, rfl⟩
  | var _ ih =>
    let .var h := H2
    obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | app _ _ ih1 ih2 =>
    let .app h1 h2 := H2
    obtain ⟨rfl, rfl⟩ := ih1 h1; obtain ⟨rfl, rfl⟩ := ih2 h2; exact ⟨rfl, rfl⟩

def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
  | .const .. => True
  | .var f => f.OnArgs P
  | .app f a => f.OnArgs P ∧ a.OnArgs P ∧ ∀ e m1 m2, a.Matches e m1 m2 → P e

-- SimplePattern
inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)
-- mkLams def
Lean4Lean/Theory/Inductive/Telescope.lean:32:def mkLams : List VExpr → VExpr → VExpr
Lean4Lean/Experimental/SExpr.lean:1466:def mkLams : List SExpr → SExpr → SExpr
```

### M9 [2026-09-04T02:07:18Z] Subpattern, inter, varN, mkLams; and: does ANYTHING instantiate Params?
```
def Pattern.varN (p : Pattern) : Nat → Pattern
  | 0 => p
  | n+1 => (p.varN n).var

inductive Subpattern (p : Pattern) : Pattern → Prop where
  | refl : Subpattern p p
  | appL : Subpattern p f → Subpattern p (.app f a)
  | appR : Subpattern p a → Subpattern p (.app f a)
  | varL : Subpattern p f → Subpattern p (.var f)

theorem Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
  | 0 => h
  | _+1 => .varL (.varN h)

theorem Subpattern.trans {p₁ p₂ p₃} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₃) : Subpattern p₁ p₃ := by
  induction H₂ with
  | refl => exact H₁
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | varL _ ih => exact .varL ih

theorem Subpattern.sizeOf_le {p₁ p₂} (H₁ : Subpattern p₁ p₂) : sizeOf p₁ ≤ sizeOf p₂ := by
  induction H₁ <;> simp <;> omega

theorem Subpattern.antisymm {p₁ p₂} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₁) : p₂ = p₁ := by
  cases id H₂ with
  | refl => rfl
  | _ h₂ =>
    have H₁ := H₁.sizeOf_le
    have h₂ := h₂.sizeOf_le
    simp at H₁; omega

inductive Arity (p : Pattern) : Nat → Pattern → Prop where
  | refl : Arity p 0 p
  | app : Arity p n f → Arity p (n+1) (.app f a)
  | var : Arity p n f → Arity p (n+1) (.var f)

theorem Arity.subpattern : Arity p n p' → Subpattern p p'
  | .refl => .refl
  | .app h => .appL h.subpattern
  | .var h => .varL h.subpattern

def Pattern.inter : Pattern → Pattern → Option Pattern
  | .const c, .const c' => if c = c' then some (.const c) else none
  | .app f a, .app f' a' => return .app (← f.inter f') (← a.inter a')
  | .var f, .var f' => return .var (← f.inter f')
  | .app f a, .var f' => return .app (← f.inter f') a
  | .var f, .app f' a' => return .app (← f.inter f') a'
  | _, _ => none

theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]

theorem Pattern.inter_comm (p q : Pattern) : p.inter q = q.inter p := by
  induction p generalizing q <;> cases q <;> simp [*, eq_comm, inter] <;> split <;> simp [*]

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')
-- mkLams
  | [], B => B
  | A :: As, B => .forallE A (mkPi As B)

/-- `mkLams [A₁,…,Aₙ] b = fun A₁ … Aₙ => b`. -/
def mkLams : List VExpr → VExpr → VExpr
  | [], b => b
  | A :: As, b => .lam A (mkLams As b)

/-- `f.mkApp [a₁,…,aₙ] = f a₁ … aₙ`. -/
def mkApp (f : VExpr) : List VExpr → VExpr
  | [] => f
  | a :: as => (VExpr.app f a).mkApp as

-- instances of Params / uses of Params.mk
Lean4Lean/Verify/QuotAppParams.lean:123:@[instance_reducible] def quotParams : Params :=
Lean4Lean/Verify/QuotAppParams.lean:331:attribute [local instance] quotParams
Lean4Lean/Verify/QuotAppParams.lean:424:attribute [local instance] quotParams
Lean4Lean/Verify/QuotAppParams.lean:511:attribute [local instance] quotParams
Lean4Lean/Verify/QuotAppParams.lean:598:attribute [local instance] quotParams
Lean4Lean/Verify/Typing/WeakNormRefute.lean:76:attribute [local instance] propLoopParams
Lean4Lean/Verify/Typing/WeakNormRefute.lean:114:attribute [local instance] propLoopParamsOfWF
Lean4Lean/Verify/Typing/WeakNormRefute.lean:153:theorem not_forall_weakNorm : ¬ ∀ P : Params, @WeakNorm P :=
Lean4Lean/Verify/Typing/QuotKEta.lean:87:inherits that instance's two holes and adds none: `quotParams := paramsOfPiInv …
Lean4Lean/Verify/Typing/QuotKEta.lean:147:attribute [local instance] quotParams
Lean4Lean/Verify/Inductive/RunIdentity.lean:96:  `withParams_mkForall_eq` and `QuotConsts.lean` already do;
Lean4Lean/Verify/Inductive/NestedRunInvariant.lean:775:theorem withParams_mkForall_eq {lctx : LocalContext} {ps : Array Expr} {fvs : List FVarId}
Lean4Lean/Theory/Typing/KEta.lean:302:/-- `EtaK` is empty at the witness instance, because `KStep` is (`refParams_no_kstep`) and
Lean4Lean/Theory/Typing/PatWF.lean:402:    (hpi : env.PiInv U) (hfree : env.IotaFree) : Params :=
Lean4Lean/Theory/Typing/KDescend.lean:218:    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
Lean4Lean/Theory/Typing/DescendConstSpineK.lean:147:attribute [local instance] propLoopParams
Lean4Lean/Theory/Typing/DescendConstSpineK.lean:194:* There is a **fourth** `Theory/` instance: `Theory/Typing/PatAppParams.lean`'s `appParams`
Lean4Lean/Theory/Typing/ParamsWitness.lean:132:@[instance_reducible] def propLoopParams : Params where
Lean4Lean/Theory/Typing/ParamsWitness.lean:147:attribute [local instance] propLoopParams
Lean4Lean/Theory/Typing/ParamsWitness.lean:217:@[instance_reducible] def propLoopParamsOfWF : Params :=
Lean4Lean/Theory/Typing/PatAppParams.lean:221:@[instance_reducible] def appParams : Params where
Lean4Lean/Theory/Typing/PatAppParams.lean:259:attribute [local instance] appParams
Lean4Lean/Theory/Typing/PatternRules.lean:1799:    noncomputable def paramsOfWF {e : VEnv} (henv : e.WF) (U : Nat) : Params :=
Lean4Lean/Theory/Typing/PatternRules.lean:1800:      Params.mk e henv.ordered U (Pat e) e.classify Pat.simple
Lean4Lean/Theory/Typing/KEtaDiamond.lean:38:`.app`-pattern instance (modulo the injectivity corner), and `quotParams_not_patMajorCanonical`
Lean4Lean/Theory/Typing/KEtaDiamond.lean:261:attribute [local instance] appParams
Lean4Lean/Theory/Typing/KEtaDiamond.lean:462:attribute [local instance] appParams
Lean4Lean/Theory/Typing/ParRedKWeakN.lean:322:4. *Cost to existing instances.*  `Params` is constructed at `ParamsBuild.lean:52` and `:105`,
Lean4Lean/Theory/Typing/KSite7App.lean:242:    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
Lean4Lean/Theory/Typing/KSite7App.lean:378:    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
-- PatternRules.lean outline
30:definition must discharge asks *what does this actually have to supply?* — and only the
62:instance has never had this check applied to it.
89:def iotaPat (T : VIndType) (C : VIndCtor) : Pattern :=
93:theorem iotaPat_eq (T : VIndType) (C : VIndCtor) :
106:def iotaRHSOf (_j q : Nat) (T : VIndType) (C : VIndCtor) (h : (D.iotaLam q C).Closed) :
112:def ctorArgRHS (T : VIndType) (C : VIndCtor) : List (D.iotaPat T C).RHS :=
119:def iotaLevelPairs : List (Nat × Nat) :=
131:def iotaComputed (T : VIndType) (C : VIndCtor)
143:def iotaCheckOf (T : VIndType) (C : VIndCtor)
154:theorem VLevel.map_inst_params {u : Nat} {ls : List VLevel} (h : ls.length = u) :
170:theorem Lookup.exists_of_lt : ∀ {Δ : List VExpr} {i : Nat}, i < Δ.length → ∀ Γ,
177:theorem VEnv.isDefEqU_bvar {env : VEnv} {U : Nat} {Δ Γ : List VExpr} {i : Nat}
183:def quotLiftArgs : List VExpr := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]
184:def quotMkArgs : List VExpr := [.bvar 5, .bvar 4, .bvar 0]
186:theorem argPaths5 (c : Lean.Name) : Pattern.argPaths (.const c) 5
190:theorem argPaths3 (c : Lean.Name) : Pattern.argPaths (.const c) 3
193:theorem instL_peelLams_quotDefEq_lhs {ls : List VLevel} (hlen : ls.length = 2) :
203:theorem instL_quotDefEq_lhs {ls : List VLevel} (hlen : ls.length = 2) :
214:theorem instL_quotDefEq_rhs {ls : List VLevel} :
238:def quotPat : Pattern := (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern
247:def quotRHS : quotPat.RHS :=
265:def quotCheck : quotPat.Check :=
270:inductive Pat (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop
336:theorem VInductDecl'.piBodyHead_recType (D : VInductDecl') (j : Nat) {T : VIndType}
346:theorem VIndCtor.piBodyHead_type (C : VIndCtor) (D : VInductDecl') (j : Nat) :
352:theorem recType_ne_ctorType {D D' : VInductDecl'} {j j' : Nat} {T : VIndType} {C : VIndCtor}
362:theorem rec_ne_ctor {env : VEnv} {D D' : VInductDecl'} {j j' : Nat} {T : VIndType}
372:theorem mkRecName_ne_quotLift (n : Lean.Name) : Lean.mkRecName n ≠ ``Quot.lift := by
375:theorem mkRecName_ne_quotMk (n : Lean.Name) : Lean.mkRecName n ≠ ``Quot.mk := by
382:theorem quotLift_ne_ctor {env : VEnv} {D : VInductDecl'} {j : Nat} {C : VIndCtor}
407:theorem VDefVal.value_closed {env : VEnv} {ci : VDefVal} (henv : env.Ordered) (h : ci.WF env) :
411:theorem VInductDecl'.iotaLam_closed {env : VEnv} {D : VInductDecl'} (henv : env.Ordered)
420:theorem VIndCtor.args_closed {env : VEnv} {D : VInductDecl'} {j : Nat} {T : VIndType}
432:inductive VEnv.RuleShape (env : VEnv) : VDefEq → Prop
468:theorem VEnv.RuleShape.mono {env env' : VEnv} (hle : env ≤ env') {df} :
480:theorem VInductDecl'.iotaCtx_of_staged {env env₀ env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
495:theorem VEnv.ruleShape_def {env env' : VEnv} {ci : VDefVal} (henv : env.Ordered)
505:theorem VEnv.ruleShape_unsafeDef {env env' : VEnv} {cis : List VDefVal} (henv : env.Ordered)
516:theorem VEnv.ruleShape_quot {env env' : VEnv} (h : env.addQuot = some env')
533:theorem VEnv.ruleShape_induct {env env' : VEnv} {D : VInductDecl'} (henv : env.Ordered)
```

### M10 [2026-09-04T02:07:35Z] Pat inductive (PatternRules:270) + is paramsOfWF real code or prose?
```
inductive Pat (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop
  | delta {c : Lean.Name} {u : Nat} {v t : VExpr} (h : v.Closed) :
      env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩ →
      Pat env (.const c) (deltaRHS c v h, Pattern.Check.true)
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
      (h : (D.iotaLam q C).Closed)
      (hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
      D.types[j]? = some T → C ∈ T.ctors → env.defeqs (D.iotaRule j q C) →
      -- the two constants the pattern's leaves name are really declared, at the types
      -- `addInduct'` gave them.  Not decoration: see `Pat.rec_ne_ctor`.
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      -- F3.  Recorded because `Pat.isCtorLeaf_piArity` has to reconcile the pattern's
      -- constructor arity, which `iotaPat` states as `D.np + |C.fields|`, with the Π-count of
      -- the *stored* type, which binds `C.params`.  Every construction site holds it
      -- (`VEnv.RuleShape.iota` carries it, from `VIndCtor.WF.params_len`).
      C.params.length = D.np →
      -- F5's arity, recorded for exactly the same reason as F3 above, and found by the same
      -- route: `pat_wf`'s ι case has to match the *pattern's* index block, whose width
      -- `iotaPat` reads off `T.indices`, against the *rule's*, whose width `iotaLhs` reads
      -- off `C.args`.  Without this field the two widths are unrelated, the two spines have
      -- different lengths, and no congruence can relate a matched redex to the fired rule --
      -- `pat_wf`'s ι case is then not merely hard but unprovable.  Deriving it instead would
      -- need Π-vs-application discrimination (an under- or over-applied recursor's type is a
      -- `mkPi` while `iotaType` is an application), i.e. the open injectivity corner.  Every
      -- construction site holds it: `VEnv.RuleShape.iota` carries it, from
      -- `VIndCtor.WF.args_len`, exactly as it carries `params_len`.
      C.args.length = T.indices.length →
      Pat env (D.iotaPat T C) (D.iotaRHSOf j q T C h, D.iotaCheckOf T C hargs)
  /-- The quotient rule.  `env.constants ``Quot.lift` is not decoration: it is what
  `Pat.quotLift_ne_ctor` needs, exactly as `Pat.iota`'s two constant fields feed
  `rec_ne_ctor`.

  `Quot.mk`'s constant was deliberately *not* recorded here for as long as nothing consumed
  it.  `Pat.isCtorLeaf_piArity` now does — it reads every constructor leaf's arity off the
  stored type, and `Quot.mk` is a constructor leaf — so the field is added.  The earlier
  absence was correct at the time and is exactly the discipline the module docstring asks
  for: a field with no consumer hides which premises are load-bearing. -/
  | quot : env.defeqs quotDefEq → env.constants ``Quot.lift = some quotLiftConst →
      env.constants ``Quot.mk = some quotMkConst →
      Pat env quotPat (quotRHS, quotCheck)

/-! ## The global name-distinctness side condition

`pat_app_uniq` bottoms out in `(.const r).inter (.const c) = none` where `r` is one
registered pattern's *recursor* leaf and `c` another's *constructor* leaf — patterns that may
come from different blocks.  So it needs: no recursor name is any constructor name, anywhere
in the environment.

Within a block that is `addInduct'`'s freshness (`allNames` is added by `addConstList`, which
fails on a duplicate).  Across blocks it is **not** derivable from `addConstList_fresh`, which
only gives freshness against the environment as it stood when *that* block was added.

What makes it derivable is `VEnv.addConst` rejecting duplicates outright: a name declared
twice is impossible in any environment built by declarations, so if a recursor name equalled
a constructor name they would be the *same constant*, and their stored types would be equal.
Those types are syntactically distinguishable — a recursor's, under its binders, is a motive
application with a `bvar` head, a constructor's is `I p args` with a `const` head.

That argument needs the two constants to be *present*, which `env.defeqs (D.iotaRule …)` does
not give: a rule being in `defeqs` says nothing about `constants`.  Hence the two
`env.constants … = some …` hypotheses on `Pat.iota` above.  They are discharged where the
evidence exists — `VInductDecl'.WF.iotaCtx` supplies exactly these from `addInduct'` — rather
than assumed globally. -/

/-- A recursor's stored type, under its binders, is a *motive application* — a `bvar` head. -/
theorem VInductDecl'.piBodyHead_recType (D : VInductDecl') (j : Nat) {T : VIndType}
    (hT : D.types[j]? = some T) :
    VExpr.piBodyHead (D.recType j)
      = .bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j)) := by
  rw [VInductDecl'.recType, getD_types hT,
---- around 1780-1830 (paramsOfWF) ----
  arity now has to be read off its constant.  That field was deliberately absent while nothing
  consumed it, and its absence was right at the time.

**The downstream shim.**  `classify` and `pat_wf` mention `Classification` and `Pattern.WF`,
which live in `Experimental/SExpr.lean`; `Theory/` must not import `Experimental/`, so they
belong in a module downstream of both.  That shim is **written and machine-checked** (65
lines, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`), and it is short because
everything above is done:

    noncomputable def VEnv.classify (env : VEnv) (c : Name) : Option Classification :=
      if ∃ n, Pat.IsRecLeaf env c n then
        some (.symb ((env.constants c).elim 0 (·.type.piArity)))
      else if ∃ n, Pat.IsCtorLeaf env c n then
        some (.ctor ((env.constants c).elim 0 (·.type.piArity)))
      else if Pat.IsDeltaHead env c then some (.symb 0) else none

with one auxiliary (`Pattern.WF cl ((Pattern.const c).varN n) top k ↔ cl c = some …`, a
four-line induction), the three cascade equations from the exclusivity lemmas below, and

    noncomputable def paramsOfWF {e : VEnv} (henv : e.WF) (U : Nat) : Params :=
      Params.mk e henv.ordered U (Pat e) e.classify Pat.simple
        (e.classify_pat_wf henv) (Pat.uniq henv)

So **all eight fields of the shape model's `Params` are discharged for an arbitrary
`VEnv.WF env`**.  What remains for the shape-model route is `SExpr.ParamsExtra`, whose
`extra_pat` is refuted as stated (see the closing section) and whose `ctor_ty` is satisfiable.
`Classical.choice` enters exactly once, in the cascade's decidability, and nowhere else. -/

/-- `piArity` counts what `peelPis` peels. -/
theorem VExpr.piArity_eq_length_peelPis : ∀ e : VExpr, e.piArity = (peelPis e).1.length
  | .forallE _ B => by rw [VExpr.piArity, VExpr.peelPis, piArity_eq_length_peelPis B]; rfl
  | .bvar .. | .sort .. | .const .. | .app .. | .lam .. => rfl

theorem VInductDecl'.recType_piArity (D : VInductDecl') (j : Nat) :
    (D.recType j).piArity
      = D.np + D.nm + D.nmin + (D.types.getD j default).indices.length + 1 := by
  rw [VExpr.piArity_eq_length_peelPis, VInductDecl'.length_peelPis_recType]

/-- `c` is the **recursor leaf** of a registered pattern, at recursor arity `n`. -/
inductive Pat.IsRecLeaf (env : VEnv) : Lean.Name → Nat → Prop
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor} :
      D.types[j]? = some T → env.defeqs (D.iotaRule j q C) →
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      IsRecLeaf env (Lean.mkRecName T.name) (D.np + D.nm + D.nmin + T.indices.length)
  | quot : env.defeqs quotDefEq → env.constants ``Quot.lift = some quotLiftConst →
      IsRecLeaf env ``Quot.lift 5

/-- `c` is the **constructor leaf** of a registered pattern, at constructor arity `n`. -/
inductive Pat.IsCtorLeaf (env : VEnv) : Lean.Name → Nat → Prop
  | iota {D : VInductDecl'} {j q : Nat} {C : VIndCtor} :
      env.defeqs (D.iotaRule j q C) →
---- ParamsBuild.lean:40-115 ----

Semantically: a registered rule, fired at a term the environment actually types, is a
definitional equality of that environment. -/
def PatWF (env : VEnv) (U : Nat) : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr} {Γ : List VExpr},
    Pat env p r → p.Matches e m1 m2 → OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → r.2.OK (env.IsDefEqU U Γ) m1 m2 →
    env.IsDefEqU U Γ e (r.1.apply m1 m2)

/-- **`Params` from `VEnv.WF` plus `PatWF`.**  Nine of the ten fields come from `env.WF`
alone. -/
@[instance_reducible] def paramsOfWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : PatWF env U) : Params where
  env := env
  henv := henv
  univs := U
  Pat := Pat env
  pat_simple := Pat.simple
  pat_uniq := Pat.uniq henv
  pat_wf := hwf
  pat_app_l_uniq := Pat.app_l_uniq
...
  obtain ⟨c, rfl⟩ := hd hp
  cases hp with
  | delta hv hrule => exact patWF_delta henv hv hrule hm hΓ hT

/-- **`Params` for a δ-fragment environment, from `VEnv.WF` alone.** -/
@[instance_reducible] def paramsOfDelta {env : VEnv} (henv : env.WF) (U : Nat) (hd : DeltaFragment env) : Params :=
  paramsOfWF henv U (patWF_of_deltaFragment henv U hd)

/-! ## What the instance unlocks

`IsDefEq.church_rosser` is stated about `Params.env`; through `paramsOfWF` it becomes a
statement about an arbitrary `VEnv.WF` environment.  **Not `sorry`-free**: it inherits
`sorryAx` from `NormalEq.descend` and `IsDefEqU.forallE_inv_stratified`.  Recorded because it
is the exact statement the strengthening route wants, and because typechecking it is the
check that `paramsOfWF` really discharges every obligation `church_rosser` asks for. -/
theorem church_rosser_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : PatWF env U)
```

### M11 [2026-09-04T02:07:46Z] paramsOfWF's extra_pat field — how is 'every defeq is a Pat' discharged?
```
/-- **`Params` from `VEnv.WF` plus `PatWF`.**  Nine of the ten fields come from `env.WF`
alone. -/
@[instance_reducible] def paramsOfWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : PatWF env U) : Params where
  env := env
  henv := henv
  univs := U
  Pat := Pat env
  pat_simple := Pat.simple
  pat_uniq := Pat.uniq henv
  pat_wf := hwf
  pat_app_l_uniq := Pat.app_l_uniq
  pat_app_uniq := Pat.app_uniq
  extra_pat := fun _ h1 h2 h3 => Pat.extra henv h1 h2 h3

/-! ## The δ fragment

`PatWF`'s δ case needs nothing that is not already proved: `HasType.const_inv` pins the
matched level list to the rule's `uvars`, and `IsDefEq.extra` is the rule.  It is the ι and
quotient cases that need `IsDefEqU.forallE_inv` (open, `Theory/Typing/Injectivity.lean`), so
an environment that registers only δ-rules gets a `Params` instance outright. -/

/-- Every pattern the environment registers is a δ-rule's: a bare `.const`. -/
def DeltaFragment (env : VEnv) : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat env p r → ∃ c, p = .const c

/-- **The δ case of `PatWF`, unconditionally.**  Stated separately from
`patWF_of_deltaFragment` so that a future ι/quot proof can reuse it. -/
theorem patWF_delta {env : VEnv} (henv : env.WF) {U : Nat} {c : Lean.Name} {u : Nat}
    {v t e A : VExpr} {m1 m2} {Γ : List VExpr} (hv : v.Closed)
    (hrule : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩)
    (hm : (Pattern.const c).Matches e m1 m2) (hΓ : OnCtx Γ (env.IsType U))
    (hT : env.HasType U Γ e A) :
    env.IsDefEqU U Γ e ((deltaRHS c v hv).apply m1 m2) := by
  cases hm
  rename_i ls
  obtain ⟨ci, hci, hlsWF, hlen⟩ := HasType.const_inv henv.ordered hΓ hT
  obtain ⟨ci', hci', -, hlen'⟩ :=
    HasType.const_inv (Γ := []) henv.ordered trivial (henv.ordered.defEqWF hrule).1
  rw [hci] at hci'
  cases hci'
  simp only [VLevel.params_length] at hlen'
  have hls : ls.length = u := by omega
  refine ⟨t.instL ls, ?_⟩
  have h := IsDefEq.extra (env := env) (uvars := U) (Γ := Γ) hrule hlsWF hls
  simpa [VExpr.instL, VLevel.inst_map_id hls, deltaRHS, Pattern.RHS.apply] using h

/-- **`PatWF` on the δ fragment.** -/
theorem patWF_of_deltaFragment {env : VEnv} (henv : env.WF) (U : Nat)
    (hd : DeltaFragment env) : PatWF env U := by
  intro p r e A m1 m2 Γ hp hm hΓ hT _
  obtain ⟨c, rfl⟩ := hd hp
-- Pat.extra / extra_pat proof site
Lean4Lean/Verify/Typing/QuotKEta.lean:30:  defeq whatsoever, while `AppPat` claims two rules, which `Params` permits (`extra_pat`
Lean4Lean/Verify/Typing/Rigidity.lean:29:(`extra_pat`), so under an abstract instance the hypothesis cannot reach the step.  The repaired
Lean4Lean/Verify/Typing/Rigidity.lean:377:(`extra_pat` : every rule is a registered pattern under leading λs); nothing forbids an
Lean4Lean/Verify/Typing/StructureUniq.lean:58:`∀`s, because two statements produced in this development (`Params.extra_pat`,
Lean4Lean/Verify/Typing/ConstSpine.lean:82:relates `Pat` to `defeqs` in one direction only (`extra_pat`: every rule is a registered
Lean4Lean/Theory/Typing/ParamsWitness.lean:16:rules are not well-founded as a *head*-reduction (`propLoop_headStep_not_wf`), so `extra_pat`
Lean4Lean/Theory/Typing/ParamsWitness.lean:25:**Correction to an earlier reading.**  `extra_pat` was singled out as "the field `VEnv.WF`
Lean4Lean/Theory/Typing/ParamsWitness.lean:114:theorem extra_pat {Γ df ls uvars} (_hΓ : OnCtx Γ (propLoopEnv.IsType 0))
Lean4Lean/Theory/Typing/ParamsWitness.lean:142:  extra_pat := PropLoopParams.extra_pat
Lean4Lean/Theory/Typing/PatAppParams.lean:207:/-- `extra_pat` is vacuous: `cycEnv` registers no defeq rule at all.  That is *not* a defect of
Lean4Lean/Theory/Typing/PatAppParams.lean:231:  extra_pat := AppPat.extra
Lean4Lean/Theory/Typing/KRule.lean:55:   ι-redex, so `extra_pat` would still be satisfiable; but `Params.pat_wf` would then have to
Lean4Lean/Theory/Typing/PatternRules.lean:212:/-- The two sides share their λ-telescope, so a single `Δ` serves both — which `extra_pat`
Lean4Lean/Theory/Typing/PatternRules.lean:223:/-! ## `extra_pat`, one rule shape at a time -/
Lean4Lean/Theory/Typing/PatternRules.lean:234:This is `PLAN.md`'s "`extra_pat` is unsatisfiable" finding one layer down: λ-peeling fixed
Lean4Lean/Theory/Typing/PatternRules.lean:259:  where `extra_pat` discharges them.
Lean4Lean/Theory/Typing/PatternRules.lean:393:`extra_pat` quantifies over an arbitrary `df` with `env.defeqs df` and must produce a `Pat`,
Lean4Lean/Theory/Typing/PatternRules.lean:400:cannot be routed around, because nothing else can tell `extra_pat` what shape a rule has.
Lean4Lean/Theory/Typing/PatternRules.lean:445:  clauses of `extra_pat` need in order to reach `VInductDecl'.onCtxIota`.
Lean4Lean/Theory/Typing/PatternRules.lean:1370:/-- **`Params.extra_pat` for a δ-rule.**  No λ-peeling (the left-hand side is already a bare
Lean4Lean/Theory/Typing/PatternRules.lean:1385:/-- **`Params.extra_pat` for the quotient rule.**  Six binders peel off, the body matches
Lean4Lean/Theory/Typing/PatternRules.lean:1436:`extra_pat` moves it to `ls` and over `Γ` with `IsDefEqU.instL` and `IsDefEq.weakR`.
Lean4Lean/Theory/Typing/PatternRules.lean:1566:/-- **`Params.extra_pat` for an ι-rule.**  The rule's binder context peels off whole
Lean4Lean/Theory/Typing/PatternRules.lean:1571:`Params.extra_pat`'s docstring (`Theory/Typing/ChurchRosser.lean`, the paragraph beginning
Lean4Lean/Theory/Typing/PatternRules.lean:1582:So: no case of `extra_pat` consumes `hΓ` — `Pat.extra_delta`, `Pat.extra_quot`,
Lean4Lean/Theory/Typing/PatternRules.lean:1585:should infer from that docstring that an `extra_pat` proof must have `OnCtx Γ` available.
Lean4Lean/Theory/Typing/PatternRules.lean:1729:/-- **`Params.extra_pat`, whole.**  `VEnv.WF.ruleShape` says every rule of a well-formed
Lean4Lean/Theory/Typing/PatternRules.lean:1805:`extra_pat` is refuted as stated (see the closing section) and whose `ctor_ty` is satisfiable.
Lean4Lean/Theory/Typing/PatternRules.lean:1987:/-! ## `Params.extra_pat` — done, and what it cost
Lean4Lean/Theory/Typing/PatternRules.lean:1991:`pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`) and one open (`pat_wf`, which needs
Lean4Lean/Theory/Typing/PatternRules.lean:2025:  mainline's semantic `pat_wf`, `pat_app_*` and `extra_pat` are present in that file only as
Lean4Lean/Theory/Typing/PatternRules.lean:2053:`PLAN.md`'s original finding was that `extra_pat` cannot hold for any environment with a
Lean4Lean/Theory/Typing/PatternRules.lean:2089:**`extra_pat`'s `OnCtx Γ` is not needed by any case.**  Its docstring argues that the ι index
Lean4Lean/Theory/Typing/QuotKAppEta.lean:55:(`extra_pat`: every rule of `env` is registered), so a `Params` instance may register patterns
Lean4Lean/Theory/Typing/ChurchRosser.lean:84:  extra_pat : OnCtx Γ (IsType env univs) →
Lean4Lean/Theory/Typing/ChurchRosser.lean:806:/-- `Δ.length` nested `lam` congruences. This is what turns a λ-peeled `extra_pat` back
Lean4Lean/Theory/Typing/ChurchRosser.lean:2521:    obtain ⟨Δ, L, R, p, r, m1, m2, e1, e2, a1, a2, a3, a4⟩ := extra_pat hΓ h1 h2 h3 (Γ := Γ)
Lean4Lean/Theory/Inductive/StructureClosed.lean:339:ι rule at a constructor spine), `Theory/Typing/PatternRules.lean`'s quotient `extra_pat`, and
Lean4Lean/Theory/Inductive/Decl.lean:873:β-redex chain, `Reduce.lean:99–107`), and it makes `Params.extra_pat` hold **on the nose**,
Lean4Lean/Theory/Inductive/Decl.lean:878:is six fields: `pat_simple`, `pat_uniq`, `pat_wf`, `extra_pat`, `pat_app_l_uniq` and
Lean4Lean/Theory/Inductive/Decl.lean:884:Of the six, `pat_simple` holds by construction of `SimplePattern.iota`, `extra_pat`'s
Lean4Lean/Theory/Inductive/Decl.lean:1108:a leaf must agree), of `extra_pat`'s context weakening (take a preimage rather than transport),
Lean4Lean/Theory/Typing/DeltaUnique.lean:785:`extra_pat` must produce a `Pat` from `env.defeqs df` alone, so it needs to know that `df` is
Lean4Lean/Theory/Typing/PatternDecode.lean:8:with `extra_pat`, which says that *every* rule of the environment is a `Pat`-registered
Lean4Lean/Theory/Typing/PatternDecode.lean:522:`extra_pat` alone would be satisfied by `Check.true`: the rule's own left-hand side has the
Lean4Lean/Theory/Typing/PatternDecode.lean:524:so any clause relating them holds by `rfl` and dropping the clauses only makes `extra_pat`
Lean4Lean/Theory/Typing/PatternDecode.lean:531:So the clauses below are the ones `pat_wf` demands, and `extra_pat` discharges them for
Lean4Lean/Theory/Typing/ParamsBuild.lean:20:| `extra_pat` | `Pat.extra henv` |
Lean4Lean/Theory/Typing/ParamsBuild.lean:62:  extra_pat := fun _ h1 h2 h3 => Pat.extra henv h1 h2 h3
Lean4Lean/Theory/Inductive/NestedKeys.lean:499:   `Params.extra_pat` then have to accept the restored form.  This is the largest remaining
Lean4Lean/Experimental/BridgeInjectivity.lean:21:   `extra_pat` field is *false* for any environment carrying a definitional equality rule.
Lean4Lean/Experimental/NormalEq.lean:94:  extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
Lean4Lean/Experimental/ParamsInstance.lean:40:`extra_pat` is **unsatisfiable as stated** — it matches `Pattern.MatchesS` against the
Lean4Lean/Experimental/ParamsInstance.lean:42:original `extra_pat` finding: the mainline field was cured by λ-peeling, the copy in
Lean4Lean/Experimental/ParamsInstance.lean:173:under the `extra_pat` λ-peel: `Pattern.MatchesS` recorded a **single** `List SLevel` for a whole
Lean4Lean/Experimental/ParamsInstance.lean:180:and `extra_pat` quantifies over every `ls` — so `ParamsExtra` was still unsatisfiable after the
Lean4Lean/Experimental/ParamsInstance.lean:207:* **`extra_pat` asks nothing about level well-formedness**, while `Pat.extra` needs it.  Any
Lean4Lean/Experimental/ParamsInstance.lean:371:theorem extra_pat_paramsOfWF {e : VEnv} (henv : e.WF) (univs : Nat)
Lean4Lean/Experimental/ShapeLogRelAdequacy.lean:437:      let ⟨_, _, _, _, _, a1, a2, a3, a4, a5⟩ := ParamsExtra.extra_pat Γ₀ h1 h2
Lean4Lean/Experimental/ParallelReduction.lean:903:    have ⟨_, _, _, _, a1, a2, a3, a4⟩ := TY.extra_pat h1 h2 h3 (Γ := Γ)
Lean4Lean/Experimental/ShapeLogRel.lean:57:  (C) THE `extra_pat` PEEL -- 2 instances, in `LE_Interp.strongSoundS`'s `extra` case.
Lean4Lean/Experimental/ShapeLogRel.lean:385:          Consequence: `Params.pat_wf` + `ParamsExtra.extra_pat` would make `ParamsExtra`
Lean4Lean/Experimental/ShapeLogRel.lean:434:## 9. `ParamsExtra.extra_pat` WAS UNSATISFIABLE.  IT IS NOW λ-PEELED.
Lean4Lean/Experimental/ShapeLogRel.lean:446:This is `PLAN.md`'s original "`extra_pat` is unsatisfiable" finding.  The MAINLINE
Lean4Lean/Experimental/ShapeLogRel.lean:447:`VEnv.Params.extra_pat` was cured by λ-peeling (that is what `Pat.extra` /
Lean4Lean/Experimental/ShapeLogRel.lean:541:Section 9 peeled `extra_pat`'s λ-telescope.  **That was not enough**: `ParamsExtra` was still
Lean4Lean/Experimental/ShapeLogRel.lean:553:`ls.getD (i+1) = ls.getD i`, and `extra_pat` demands that for ARBITRARY `ls`.  False for any
Lean4Lean/Experimental/ShapeLogRel.lean:4559:`Params.pat_wf : Pat p r -> p.WF classify` plus `ParamsExtra.extra_pat` (every
Lean4Lean/Experimental/ShapeLogRel.lean:7317:      ParamsExtra.extra_pat Γ₀ h1 h2
Lean4Lean/Experimental/ShapeLogRel.lean:7319:    -- **OPEN, and honest.**  `ParamsExtra.extra_pat` is now λ-peeled -- its unpeeled form is
```

### M12 [2026-09-04T02:08:51Z] iotaPat + Pattern.Path + RHS.apply (for the pat_uniq collision)
```

/-- The pattern of the ι-rule for constructor `C` of block type `T`: the recursor applied to
its parameters, motives, minors and indices, then to the constructor applied to its
parameters and fields. -/
def iotaPat (T : VIndType) (C : VIndCtor) : Pattern :=
  (SimplePattern.iota (Lean.mkRecName T.name) (D.np + D.nm + D.nmin + T.indices.length)
    C.name (D.np + C.fields.length)).toPattern

theorem iotaPat_eq (T : VIndType) (C : VIndCtor) :
    D.iotaPat T C
      = (SimplePattern.iota (Lean.mkRecName T.name)
          (D.np + D.nm + D.nmin + T.indices.length) C.name (D.np + C.fields.length)).toPattern :=
  rfl

/-- The ι-rule's right-hand side: `iotaLam` applied to the parameters, motives and minors
taken from the *recursor's* matched arguments, then the fields from the *constructor's*.

The cut points are exactly `iotaLhs`'s: the recursor's spine is `np + nm + nmin` variable
blocks followed by the index terms, and the constructor's is `np` parameters followed by
`nf` fields.  Taking the parameters from the recursor's side and dropping the constructor's
copy is sound because `iotaParamsCheck` relates them. -/
def iotaRHSOf (_j q : Nat) (T : VIndType) (C : VIndCtor) (h : (D.iotaLam q C).Closed) :
    (D.iotaPat T C).RHS :=
  iotaRHS (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
    (D.np + C.fields.length) (D.iotaLam q C) h (D.np + D.nm + D.nmin) D.np

/-- The matched constructor arguments, as right-hand sides. -/
def ctorArgRHS (T : VIndType) (C : VIndCtor) : List (D.iotaPat T C).RHS :=
  (Pattern.argPaths (.const C.name) (D.np + C.fields.length)).map fun y =>
    Pattern.RHS.var (p := D.iotaPat T C) (Sum.inr y)

/-- The level-index pairs relating the recursor leaf's list to the constructor leaf's.  The
block's own universes sit at `i` on the constructor's side and, when `isLE` prepends a fresh
elimination universe, at `i + 1` on the recursor's. -/
def iotaLevelPairs : List (Nat × Nat) :=
  (List.range D.uvars).map fun i => (if D.isLE then i + 1 else i, i)

/-- The constructor's result indices, as right-hand sides: each `a ∈ C.args` abstracted over
the constructor's own binders — a *closed* term, as `RHS.fixed` demands — and applied back to
the matched constructor arguments.

Derived rather than taken as a parameter.  It has to be: `pat_uniq` concludes `r ≍ r'`
whenever two registered patterns intersect, and with `p₁ = p₂ = p₃` and `Pattern.inter_self`
that forces the datum to be a *function of the pattern*.  A free `computed` parameter would
let one pattern carry two different checks and make `pat_uniq` false.  The closedness proofs
are `Prop`, so `pmap` over different proofs yields equal lists and uniqueness survives. -/
def iotaComputed (T : VIndType) (C : VIndCtor)
    (h : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
    List (D.iotaPat T C).RHS :=
  C.args.pmap (fun a ha =>
    Pattern.RHS.mkApp
      (Pattern.RHS.fixed (p := D.iotaPat T C)
        (mkLams (C.params ++ C.fields.map (·.type)) a)
        (iotaLeafCtor (Lean.mkRecName T.name) C.name
          (D.np + D.nm + D.nmin + T.indices.length) (D.np + C.fields.length)) ha)
      (D.ctorArgRHS T C)) h

/-- The ι-rule's check: parameter agreement, index agreement, level agreement. -/
def iotaCheckOf (T : VIndType) (C : VIndCtor)
    (h : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
    (D.iotaPat T C).Check :=
  iotaCheck (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
    (D.np + C.fields.length) D.np (D.np + D.nm + D.nmin)
    (D.iotaComputed T C h) D.iotaLevelPairs

end VInductDecl'
-- Pattern.Path
def Pattern.Path : Pattern → Type
  | .const _ => Empty
  | .app f a => f.Path ⊕ a.Path
  | .var f => Option f.Path

/-- The `const` leaves of a pattern. `Matches` records the universe level list found at
each of them, not just the head's: an ι-rule's pattern is `rec.{ls} a … (c.{ls'} b …)`,
and bridging `c.{ls'} b` to `c.{ls} b` needs `ls ≈ ls'`, which was not stateable while
`Matches` kept a single `List VLevel`. Requiring `ls' = ls` syntactically instead would be
unsound for confluence: `rec.{max u v} … (c.{max v u} …)` and `rec.{max u v} … (c.{max u v} …)`
are `NormalEq`-related by `constDF`, but only the second would be a redex. -/
def Pattern.LPath : Pattern → Type
  | .const _ => Unit
  | .app f a => f.LPath ⊕ a.LPath
  | .var f => f.LPath

/-- The leftmost `const` leaf: the pattern's head. -/
def Pattern.LPath.head : (p : Pattern) → p.LPath
  | .const _ => ()
  | .app f _ => .inl (LPath.head f)
  | .var f => LPath.head f

inductive Pattern.Matches :
-- RHS.apply
def Pattern.RHS.apply {p : Pattern} (m1 : p.LPath → List VLevel)
    (m2 : p.Path → VExpr) : p.RHS → VExpr
  | .fixed c lp _ => c.instL (m1 lp)
  | .var path => m2 path
  | .app f a => .app (f.apply m1 m2) (a.apply m1 m2)

theorem Pattern.RHS.lift'_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).lift' ρ = (r.apply m1 fun x => (m2 x).lift' ρ) := by
  induction r <;> simp [*, apply, lift', ← instL_lift']
  rw [ClosedN.lift'_eq ‹_› (by trivial)]

theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).liftN n k = (r.apply m1 fun x => (m2 x).liftN n k) := by
  simp [← lift'_consN_skipN, lift'_apply]

theorem Pattern.matches_lift' {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).lift' ρ := by
  constructor
```

### M13 [2026-09-04T02:09:42Z] (c) RECOMPUTED import closures — targets vs ChurchRosser
```
modules discovered: 468
ChurchRosser import-closure size: 44

module                                                     |closure| imports CR?    CR imports it?
T.T.DescendRefute                                              54 YES            no            
T.T.KDescend                                                   58 YES            no            
T.T.KSite7App                                                  63 YES            no            
T.T.ParRedPropRefute                                           61 YES            no            
T.T.StructEtaPrice                                            181 YES            no            
T.T.ConfluenceRebuildPrice                                    224 YES            no            
T.T.NoConfRepair                                              182 YES            no            
T.T.EtaGuardLand                                              222 YES            no            
T.T.KEta                                                       60 YES            no            
T.T.PatternRules                                               44 no             no            
T.T.ParamsBuild                                                52 YES            no            
T.T.Pattern                                                    10 no             YES           
T.T.KCanonical                                                 59 YES            no            
T.T.KKetaRow                                                   65 YES            no            

Lean4Lean.Theory.Typing.DescendRefute -> Theory.Typing.DescendRefute -> Theory.Typing.ParamsBuild -> Theory.Typing.ChurchRosser
Lean4Lean.Theory.Typing.KDescend -> Theory.Typing.KDescend -> Theory.Typing.DescendRefute -> Theory.Typing.ParamsBuild -> Theory.Typing.ChurchRosser
Lean4Lean.Theory.Typing.KSite7App -> Theory.Typing.KSite7App -> Theory.Typing.KSite7 -> Theory.Typing.KMeasure -> Theory.Typing.KEta -> Theory.Typing.KCanonical -> Theory.Typing.KDescend -> Theory.Typing.DescendRefute -> Theory.Typing.ParamsBuild -> Theory.Typing.ChurchRosser
Lean4Lean.Theory.Typing.ParRedPropRefute -> Theory.Typing.ParRedPropRefute -> Theory.Typing.KEta -> Theory.Typing.KCanonical -> Theory.Typing.KDescend -> Theory.Typing.DescendRefute -> Theory.Typing.ParamsBuild -> Theory.Typing.ChurchRosser

direct importers of ChurchRosser:
    Lean4Lean.Theory
    Lean4Lean.Theory.Typing.CRBetaGen
    Lean4Lean.Theory.Typing.CRPiDescend
    Lean4Lean.Theory.Typing.HeadReduction
    Lean4Lean.Theory.Typing.NormalEqStrengthen
    Lean4Lean.Theory.Typing.ParRedKWeakN
    Lean4Lean.Theory.Typing.ParamsBuild
    Lean4Lean.Theory.Typing.ParamsWitness
    Lean4Lean.Theory.Typing.PatKHead
```

### M14 [2026-09-04T02:13:05Z] (b) VERDICT, machine-checked: Lean4Lean/Theory/Typing/SEReerectionScope.lean builds
```
Build completed successfully (1277 jobs). Axiom bar, verbatim from the build log:
'Lean4Lean.Pattern.not_matches_bvar' does not depend on any axioms
'Lean4Lean.Pattern.not_matches_lam' does not depend on any axioms
'Lean4Lean.VEnv.Params.not_defeqs_etaDfZ' depends on axioms: [propext, Quot.sound]
'Lean4Lean.VEnv.Params.not_pat_ctorSpine' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SimplePattern.eq_defn_of_toPattern_varN' depends on axioms: [propext]
'Lean4Lean.VEnv.Params.not_pat_ctorSpine_of_pos' depends on axioms: [propext, Quot.sound]

ALL SIX HOLE-FREE -- no sorryAx anywhere.

VERDICT on StructEtaPrice.lean §7's price table:
  row 'induction cases added: 0'            -> CONFIRMED (ParRed.extra/CParRed.extra are generic over Pat)
  row 'church_rosser: extra case, already written' -> REFUTED.
The VDefEq route does not add a case to ParRed; it makes VEnv.Params UNINHABITABLE.
  orientation 1 (lhs = the variable, i.e. StructEtaPrice.etaDfZ, the rule §7 actually checks):
     Params.extra_pat refuted -- the lambda-peel is either a lam or a bvar, and
     Pattern.Matches walks const/app spines only.  Route-independent inside the pattern
     language: no new Pat / SimplePattern / RuleShape constructor repairs it.
  orientation 2 (lhs = the S.mk spine), zero params + zero fields:
     Params.pat_uniq refuted -- the pattern IS VInductDecl'.iotaPat's constructor block.
  orientation 2, positive np + fields:
     Params.pat_simple refuted first -- SimplePattern has only .defn (arity 0) and .iota.
  => no surviving orientation at any structure.
```

### M15 [2026-09-04T02:13:05Z] does VEnv.WF already forbid the eta rule? (RuleShape)
```
inductive VEnv.RuleShape (env : VEnv) : VDefEq → Prop
  | delta (ci : VDefVal) : ci.value.Closed → RuleShape env ci.toDefEq
  | quot : env.constants ``Quot.lift = some quotLiftConst →
      env.constants ``Quot.mk = some quotMkConst → RuleShape env quotDefEq
  /-- `args_len` is the R3 field: `iotaPat` reports the recursor arity as
  `np + nm + nmin + T.indices.length` while the rule's spine carries `|C.args|` index
  arguments, and nothing in `Pat.iota`'s data relates them.  It is discharged from
  `VIndCtor.WF.args_len` in `WF'.ruleShape` below; the obligation lands on whoever builds a
  `RuleShape`, it does not disappear.

  The last five premises are the **staging data**: the environments the block was
  declared over, together with `env₃ ≤ env`.  They are what `VInductDecl'.WF.recCtx` needs,
  and `RuleShape.iotaCtx` below turns them into `D.IotaCtx env` — which is what the index
  clauses of `extra_pat` need in order to reach `VInductDecl'.onCtxIota`.

  **Why not carry `D.IotaCtx env` directly.**  `RuleShape.mono` would then need an
  `IotaCtx.mono`, and none exists — `IotaCtx` is not monotone in `env` (`RecCtx.ordered`
  is, but `VIndCtor.WF.params_eq` and friends are monotone only because *every* field of
  `RecCtx` happens to be, which is a theorem nobody has stated).  The staging data is
  monotone for free: only the last premise mentions `env`, and it is an `≤`.  This works
  because `WF.recCtx`'s signature already takes `env₂ ≤ env₃` and `env₃.Ordered` and
  concludes `RecCtx env₃`: the monotonicity is built into the constructor rather than
  stated as a lemma, which is why no name or shape search finds it. -/
  | iota {env₀ env₁ env₂ env₃ : VEnv}
      (D : VInductDecl') (j q : Nat) (T : VIndType) (C : VIndCtor) :
      (D.iotaLam q C).Closed →
      (∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) →
      C.args.length = T.indices.length →
      C.params.length = D.np →
      D.types[j]? = some T → C ∈ T.ctors →
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      D.WF env₀ → env₀.addIndTypes D = some env₁ → env₁.addIndCtors D = some env₂ →
      env₂.addIndRecs D = some env₃ → env₃ ≤ env →
      RuleShape env (D.iotaRule j q C)

theorem VEnv.RuleShape.mono {env env' : VEnv} (hle : env ≤ env') {df} :
    env.RuleShape df → env'.RuleShape df
  | .delta ci h => .delta ci h
-- WF.ruleShape statement
505:theorem VEnv.ruleShape_unsafeDef {env env' : VEnv} {cis : List VDefVal} (henv : env.Ordered)
516:theorem VEnv.ruleShape_quot {env env' : VEnv} (h : env.addQuot = some env')
533:theorem VEnv.ruleShape_induct {env env' : VEnv} {D : VInductDecl'} (henv : env.Ordered)
563:theorem VEnv.WF'.ruleShape {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
573:    | «def» hci h => exact VEnv.ruleShape_def henv hci h ih
574:    | unsafeDef hcon h hval => exact VEnv.ruleShape_unsafeDef henv hcon h hval ih
575:    | quot _ h => exact VEnv.ruleShape_quot h ih
576:    | induct hdecl h => exact VEnv.ruleShape_induct henv hdecl h ih
578:theorem VEnv.WF.ruleShape {env : VEnv} (h : env.WF) {df} (hdf : env.defeqs df) :
579:    env.RuleShape df := WF'.ruleShape h.choose_spec df hdf
1729:/-- **`Params.extra_pat`, whole.**  `VEnv.WF.ruleShape` says every rule of a well-formed
1742:  cases henv.ruleShape hdf with
/-- **`Params.extra_pat`, whole.**  `VEnv.WF.ruleShape` says every rule of a well-formed
environment is a δ-rule, the quotient rule or an ι-rule, and carries exactly what the
corresponding case needs; this dispatches on it.

The `OnCtx Γ` the field offers is unused — see `Pat.extra_iota`'s docstring. -/
theorem Pat.extra {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {df : VDefEq} {ls : List VLevel}
    (hdf : env.defeqs df) (hlsWF : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars) :
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = mkLams Δ L ∧ df.rhs.instL ls = mkLams Δ R ∧
      Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
      (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2 := by
  have ho := VEnv.WF.ordered henv
  cases henv.ruleShape hdf with
  | delta ci hcl => exact Pat.extra_delta hcl hdf hlen
  | quot hlift hmk => exact Pat.extra_quot hdf hlift hmk hlen
  | iota D j q T C hcl hargs hal hplen hT hC hrec hctor hD s1 s2 s3 s4 =>
    exact Pat.extra_iota ho (VInductDecl'.iotaCtx_of_staged ho hD s1 s2 s3 s4)
      hcl hargs hal hplen hT hC hdf hrec hctor hlsWF hlen

/-! ## The leaf roles: what a `classify` function has to be told

`Lean4Lean.Params` (the shape model's class, `Experimental/SExpr.lean`) carries a field
`classify : Name → Option Classification` and a field
`pat_wf : Pat p r → Pattern.WF classify p`.  Unfolding `Pattern.WF` at the two registered
shapes leaves exactly three demands on `classify`:

* the recursor leaf `R` of an ι- or quot-pattern of recursor arity `M` must get `.symb (M+1)`,
* the constructor leaf `K` of arity `N` must get `.ctor N`,
* a δ-rule's head `c` must get `.symb 0`.

so `classify` is a three-way cascade and its correctness is: the three roles are **mutually
```

### M16 [2026-09-04T02:13:27Z] (d) does ChurchRosser's closure touch Theory/SetModel? + Injectivity's model dependence
```
Theory.Typing.ChurchRosser                     closure= 44  SetModel modules in closure: 0
Theory.Typing.Injectivity                      closure= 40  SetModel modules in closure: 0
Theory.Typing.ParamsBuild                      closure= 52  SetModel modules in closure: 0
Theory.Typing.PatternRules                     closure= 44  SetModel modules in closure: 0
Theory.Typing.Pattern                          closure= 10  SetModel modules in closure: 0
```

### M17 [2026-09-04T02:14:25Z] scripts/exists.lean, population 443 built modules, watching 6
```
FOUND       Lean4Lean.Pattern.not_matches_bvar
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 4, cone 92
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.Pattern.not_matches_lam
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 5, cone 92
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.Params.not_defeqs_etaDfZ
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 4, cone 733
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.Params.not_pat_ctorSpine
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 8, cone 679
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.SimplePattern.eq_defn_of_toPattern_varN
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 4, cone 123
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.Params.not_pat_ctorSpine_of_pos
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 6, cone 1108
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.SetModel.eq_singleton_of_recProp
            module Lean4Lean.Theory.Typing.StructEtaPrice, arity 8, cone 5826
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
NOT FOUND   Lean4Lean.VEnv.structEta_of_extra
            (the brief's name; the real one carries no VEnv namespace -- see next line)
FOUND       Lean4Lean.structEta_of_extra
            module Lean4Lean.Theory.Typing.StructEtaPrice, arity 9, cone 645
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.descendSE_uniq_sortUniq_not_all
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 0, cone 6800
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 22, cone 674
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.IsDefEq.church_rosser
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 7, cone 4383
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.weakN_iff, Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS, Lean4Lean.VEnv.NormalEq.descend]
            *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
FOUND       Lean4Lean.VEnv.NormalEq.parRed
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 8, cone 4135
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.weakN_iff, Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS, Lean4Lean.VEnv.NormalEq.descend]
            *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
FOUND       Lean4Lean.VEnv.Params.extra_pat
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 8, cone 678
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.WF.ruleShape
            module Lean4Lean.Theory.Typing.PatternRules, arity 4, cone 3292
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.Pat.extra
            module Lean4Lean.Theory.Typing.PatternRules, arity 9, cone 4517
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6

NOTES.
* Orchestrator's cone figures confirmed to the digit: structEta_of_extra 645;
  descendSE_uniq_sortUniq_not_all arity 0 cone 6800; not_parRedStatementSE_of_propMajor arity 22 cone 674.
* NAME CORRECTION: the brief wrote 'Lean4Lean.VEnv.structEta_of_extra'. NOT FOUND.
  Correct fully-qualified name: Lean4Lean.structEta_of_extra (root namespace, no VEnv).
* (d) CONFIRMED hole-free: Lean4Lean.SetModel.eq_singleton_of_recProp, cone 5826, no sorryAx.
* church_rosser / NormalEq.parRed carry FOUR holes each AND the two WATCHED statements
  Lean4Lean.VEnv.IsDefEq.uniq and Lean4Lean.VEnv.IsDefEq.uniqU in cone. Both lines reported.
```

### M18 [2026-09-04T02:15:12Z] (c) do the 4 downstream refutation modules mention NormalEq/ParRed DIRECTLY, or only via the *Statement defs?
```
-- where DescendStatement / ParRedStatement are defined
Lean4Lean/Theory/Typing/DescendRestate.lean:94:def DescendStatementV (I : VEnv.Params) : Prop :=
Lean4Lean/Theory/Typing/DescendRefute.lean:420:def DescendStatement (I : VEnv.Params) : Prop :=
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:137:def DescentLamP (N RS H : List VExpr → VExpr → VExpr → Prop) (univs : Nat) :
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:161:def DescendStatementP (N RS H : List VExpr → VExpr → VExpr → Prop) (univs : Nat)
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:579:def DescendStatementSE (I : VEnv.Params) : Prop :=
Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:618:def ParRedStatementSE : Prop :=
Lean4Lean/Theory/Typing/KCanonical.lean:459:def ParRedStatement : Prop :=

== DescendRefute.lean (589 lines)
   NormalEq occurrences (code+prose): 31
   ParRed   occurrences: 31
   theorem/def count:    91
   -- top-level decls mentioning NormalEq or ParRed in their SIGNATURE line:
185:theorem refNormalEq : @VEnv.NormalEq refParams refCtx refG refG' := by
198:theorem refParRed_const {Γ c ls e} (H : @VEnv.ParRed refParams Γ (.const c ls) e) :
204:theorem refParRed_bvar {Γ i e} (H : @VEnv.ParRed refParams Γ (.bvar i) e) :
210:theorem refParRed_constBvar {Γ c ls i e}
211:    (H : @VEnv.ParRed refParams Γ (.app (.const c ls) (.bvar i)) e) :
214:  | app hf ha => rw [refParRed_const hf, refParRed_bvar ha]
217:theorem refParRed_G {e} (H : @VEnv.ParRed refParams refCtx refG e) : e = refG :=
218:  refParRed_constBvar H
220:theorem refParRedS_G {e} (H : @VEnv.ParRedS refParams refCtx refG e) : e = refG := by
223:  | tail _ h ih => cases ih; exact refParRed_G h
231:      cases refParRedS_G hred
234:  | _+1, _, _, ⟨_, _, _, hred, _⟩ => by cases refParRedS_G hred
== KDescend.lean (415 lines)
   NormalEq occurrences (code+prose): 26
   ParRed   occurrences: 16
   theorem/def count:    11
   -- top-level decls mentioning NormalEq or ParRed in their SIGNATURE line:
87:local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
88:local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
89:local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2
133:theorem NormalEq.descendV :
144:    obtain ⟨u1, u2, hmt, hlv, hwa, hwb, hn⟩ := NormalEq.descent_refl hΓ hm h
178:        refine .inl ⟨0, .app t a₁, u1, (·.elim a₁ u2), ParRedS.app hred .rfl, .var hmt,
186:          (.trans (ParRedS.app hred .rfl) (.tail .rfl (.beta .rfl .rfl)))
190:        exact .inr (NormalEq.appDF_proof_escape_of_sortUniq Params.sortUniq hΓ l1 l2 l3 l4 l6 hP hp1)
209:theorem NormalEq.appDF_extra_of_descendV
315:              have hins := NormalEq.apply_instL (p := q₁.app q₂) (r := w) hΓ' hwB hwAS hlvS' hw
332:        exact NormalEq.apply_congr (p := q₁.app q₂) (r := r.fst) hΓ' hwAS hwB hlvS
334:    match NormalEq.descendV _ (Nat.le_refl _)
== KSite7App.lean (535 lines)
   NormalEq occurrences (code+prose): 40
   ParRed   occurrences: 87
   theorem/def count:    12
   -- top-level decls mentioning NormalEq or ParRed in their SIGNATURE line:
65:local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
66:local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
67:local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2
110:    (hm : q.Matches g m1 m2) (hr : ∀ x, ParRedK Γ (m2 x) (m2' x)) :
111:    ∃ g', ParRedK Γ g g' ∧ q.Matches g' m1 m2' :=
112:  develop_of_matches (R := ParRedK Γ) .const .app hm hr
119:    ∃ t n1' n, ParRedKS Γ g t ∧ q.Matches t n1' n ∧
123:      (∀ x, NormalEq Γ (n x) (n2 x))
125:    ∃ A e B, ParRedKS Γ g (.lam A e) ∧ HasType env univs Γ g' (.forallE A B) ∧
141:    (hred : ParRedKS Γ g g₀) (H : DescentLamK k Γ q g₀ g' n1 n2) :
169:      ∃ s, ParRedKS Γ' t s ∧ Γ' ⊢ s ≡ₚ S.liftN n) →
171:    ∃ t, ParRedKS Γ g t ∧ Γ ⊢ t ≡ₚ S := by
== ParRedPropRefute.lean (222 lines)
   NormalEq occurrences (code+prose): 22
   ParRed   occurrences: 40
   theorem/def count:    6
   -- top-level decls mentioning NormalEq or ParRed in their SIGNATURE line:
94:    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
95:    (hne : ¬ NormalEq Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) :
96:    ¬ ParRedStatement := by
98:  have h1 : NormalEq Γ (.app f a) (.app f b) :=
100:  have h2 : ParRed Γ (.app f b) (Pattern.RHS.apply m1 m2 r.1) :=
128:    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
130:    ¬ (∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → ParRed Δ e e') := by
151:    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
190:theorem ParRedK.propMajor_fires
200:    ParRedK Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1) :=
201:  ParRedK.hK (.mk r1 r2 r3 hf (.proofIrrel hA ha hb))
207:theorem ParRedK.propMajor_joins

-- Params class: which of the 10 fields mention the judgment (IsDefEq/HasType/IsType/IsDefEqU)?
   2:  env : VEnv
   3:  henv : env.WF
   4:  univs : Nat
   6:  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
   7:  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
   8:    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
   12:  argument well-typed at the *declared* domain -- so the typing of `e` has to be inverted.
   16:  still *true* -- an ill-formed `Γ` only lets `bvar` carry junk types, while the application
   17:  rules still pin the recursor's arguments -- but it is not provable by any route in the
   19:  scope and passes it to `.trans_l henv hΓ` in the same expression, so this costs nothing.
   23:  should be treated as suspect by default.
   25:  pat_wf : Pat p r → p.Matches e m1 m2 → OnCtx Γ (IsType env univs) →
   26:    HasType env univs Γ e A →
   27:    r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
   28:  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
   29:    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
   30:  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
   31:    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
   37:  while `Pattern.Matches` only walks `const`/`app` spines. Without peeling this field is
   38:  satisfiable only by environments whose every defeq is a bare δ-rule, which is why nothing
   39:  instantiates `Params`. Peeling leaves `IsDefEq`, `VDefEq`, `Matches`, the `vdefeq`
   40:  elaborator and `Theory/Quot.lean` untouched; the rejected alternative — storing `VDefEq`
   41:  in applied form — would force `quotDefEq`, the elaborator and `QuotLemmas.lean` to be
   45:  which is exactly where the `ParRed.extra` step fires once `ParRed.lams` has wrapped it in
   49:  discharged by β-reducing `mkLams tel a` applied to the matched constructor arguments;
   53:  nothing — but `OnCtx` quantifies over every entry.  The sole consumer already holds the
   54:  fact: `NormalEq.parRed`'s `extra` case (below) sits inside `IsDefEq.church_rosser`, whose
   56:  case — which is why the sibling cases use it freely.  So this costs one argument at one
   57:  call site.
   60:  which was under-hypothesised for it.  Three for three: on this development a rule stated
   61:  about an arbitrary `Γ` with no well-formedness hypothesis is suspect by default.
   65:  universally quantified `Nat`, unrelated to `Params.univs`.  (`uvars` is the section
   66:  variable of `Theory/Typing/Basic.lean`, where `IsDefEq.extra` states the same hypothesis
   68:  for the conclusion at level lists that are *not* well-formed for the judgment, which
   73:  extra_pat : OnCtx Γ (IsType env univs) →
   74:    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
   75:    ∃ Δ L R p r m1 m2,
   76:      df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
   77:      Pat p r ∧ p.Matches L m1 m2 ∧
   78:      r.2.OK (IsDefEqU env univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2
```

### M19 [2026-09-04T02:15:47Z] (d) residual: the two steps StructEtaPrice §8 says the model still owes
```
-- step 1: the interp(recType) peel at a GENERAL block. Does a general peel exist?
Lean4Lean/Theory/SetModel/IffConsts.lean:215:  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun p hp ↦ ?_)
Lean4Lean/Theory/SetModel/IffConsts.lean:219:  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun q _ ↦ ?_)
Lean4Lean/Theory/SetModel/EqOracle.lean:535:`UnitOracleLarge.pt_not_mem_interpL_recType_of_ne`, which needs an inhabitant of the *motive*
Lean4Lean/Theory/SetModel/EqOracle.lean:542:    (pt : V) ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
Lean4Lean/Theory/SetModel/EqOracle.lean:555:    (hw : w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅) : w = pt := by
Lean4Lean/Theory/SetModel/EqOracle.lean:577:    (hw₀ : w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅) :
Lean4Lean/Theory/SetModel/EqOracle.lean:578:    w ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u₁, v])).toFun ∅ := by
Lean4Lean/Theory/SetModel/EqOracle.lean:653:    (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
Lean4Lean/Theory/SetModel/EqOracle.lean:743:    ¬ ∃ w : V, w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅ ∧
Lean4Lean/Theory/SetModel/EqOracle.lean:744:        w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₁, v])).toFun ∅ := by
Lean4Lean/Theory/SetModel/EqOracle.lean:762:    (∃ w : V, w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅) ↔
Lean4Lean/Theory/SetModel/EqOracle.lean:763:      (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅ := by
Lean4Lean/Theory/SetModel/IffRecLarge.lean:476:Five applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`, one per binder, and one hypothesis:
Lean4Lean/Theory/SetModel/IffRecLarge.lean:498:      (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
Lean4Lean/Theory/SetModel/IffRecLarge.lean:501:  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]; rfl) (fun a ha ↦ ?_)
Lean4Lean/Theory/SetModel/IffRecLarge.lean:506:  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]; rfl) (fun b hb ↦ ?_)
Lean4Lean/Theory/SetModel/IffRecLarge.lean:511:  refine UnitAudit.mkLam_mem_mkForallType_of_dom
Lean4Lean/Theory/SetModel/IffRecLarge.lean:516:  refine UnitAudit.mkLam_mem_mkForallType_of_dom
Lean4Lean/Theory/SetModel/IffRecLarge.lean:522:  refine UnitAudit.mkLam_mem_mkForallType_of_dom
Lean4Lean/Theory/SetModel/IffRecLarge.lean:611:    (pt : V) ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by

-- step 2: PropSplit agreement with typing, in the form 'a motive is not a proof'
Lean4Lean/Theory/SemanticRouteClosed.lean
Lean4Lean/Verify/Typing/ProjInhab.lean
Lean4Lean/Theory/Typing/AppCase.lean
Lean4Lean/Theory/Equiconsistency.lean
Lean4Lean/Theory/Typing/InjCorner.lean
Lean4Lean/Theory/Typing/StructEtaPrice.lean
Lean4Lean/Theory/Typing/InjSortPiModel.lean
Lean4Lean/Theory/Typing/SortUniq.lean
Lean4Lean/Theory/Typing/SortInvIndep.lean
Lean4Lean/Theory/SetModel/EqOracle.lean
  decls whose name mentions PropSplit and motive/notProof:
Lean4Lean/Theory/SetModel/PropSplitAudit.lean:127:Moved here from `SetModel/NotProofNoModel.lean` on 2026-09-02, when `PropSplit`'s two fields
Lean4Lean/Theory/SetModel/FalseProp.lean:54:Moved here from `SetModel/NotProofNoModel.lean` on 2026-09-02: with `PropSplit`'s fields
Lean4Lean/Theory/SetModel/FalseProp.lean:64:`sort_not_proof` supplies, and (since 2026-09-02) the one `PropSplit`'s fields want at the
Lean4Lean/Theory/SetModel/StablePrelude.lean:29:`PropSplitUp.isPropUp_liftN` / `isProofUp_liftN` that `propSplitUp_stable` already uses for those
Lean4Lean/Theory/SetModel/AboveAudit.lean:401:and for `PropSplitAudit.propSplitOf` — whose `IsPropAt`/`IsProofAt` *contain* their own
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:27:`SetModel/PropSplitAudit.lean` already contains the statement that `sort_not_proof` is an
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:47:`SetModel/Interp.lean`'s `PropSplit` is the parameter that every model statement in the tree
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:49:them take `L : PropSplit envF nv`.  Its `proof_sound` field is a **biconditional** between a
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:54:    propTypeAgree_of_propSplit :  PropSplit env nv  →  env.PropTypeAgree nv
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:55:    propUniq_of_propSplit     :  PropSplit env nv  →  env.PropUniq nv

-- is there ANY lemma stating the model validates StructEtaG / UnitEta?
Lean4Lean/Theory/SetModel/UnitEtaPairing.lean:6:`docs/vacuity-ledger.md` row 102a: `VEnv.UnitEta`
Lean4Lean/Theory/SetModel/UnitEtaPairing.lean:172:/-- **What `UnitEta` needs of the model, at the set level**: any two inhabitants
Lean4Lean/Theory/SetModel/UnitEtaPairing.lean:734:  worthless on its own for `UnitEta`.  Every one of them is instantiated at

-- soundAbove: the single model induction site on the strong relation
Lean4Lean/Theory/Typing/StructEtaPrice.lean:42:`SetModel/Consts` (`constsIn`).  `SetModel/SoundInduction`'s `soundAbove` is on the
Lean4Lean/Theory/Typing/StructEtaPrice.lean:62:* **1 site is the model** (`SetModel/soundAbove`), §8 below.
Lean4Lean/Theory/Typing/EnlargedModel.lean:49:theorem retype_soundAbove {Γ : List VExpr} {e₁ e₂ A B : VExpr}
Lean4Lean/Theory/SetModel/LevelAssignUnsat.lean:148:was vacuous**, including `soundAbove` and everything downstream of it.
Lean4Lean/Theory/SetModel/PropSplitUp.lean:15:`PropSplit.Stable`, or `soundAbove`.  Replacing
Lean4Lean/Theory/SetModel/NotProofNoModel.lean:48:is quantified over: `interp`, `Sound`, `soundAbove`, `sound_nil`, `interp_falseProp`, all of
```

### M20 [2026-09-04T02:16:11Z] (d)+(c) exists.lean pass 2
```

population: 443 built modules
watching 6 declarations for cone membership

FOUND       Lean4Lean.SetModel.soundAbove
            module Lean4Lean.Theory.SetModel.SoundInduction, arity 23, cone 7163
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.StructEtaG
            module Lean4Lean.Verify.TypeChecker.EtaStructG, arity 1, cone 723
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.UnitEta
            module Lean4Lean.Theory.Inductive.StructureEta, arity 1, cone 600
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.SetModel.UnitAudit.mkLam_mem_mkForallType_of_dom
            module Lean4Lean.Theory.SetModel.UnitOracleLarge, arity 16, cone 5785
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
NOT FOUND   Lean4Lean.SetModel.sort_not_proof
            (before writing "absent", also query by conclusion shape — a different name for the same content is the failure mode that bites)
FOUND       Lean4Lean.VEnv.NormalEq.descend
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 12, cone 3874
            own value is a hole: true; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS, Lean4Lean.VEnv.NormalEq.descend]
            *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
            (these are forbidden or load-bearing by policy, NOT holes --
             a clean sorryAx line does not clear them)
FOUND       Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified
            module Lean4Lean.Theory.Typing.Injectivity, arity 16, cone 48
            own value is a hole: true; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified]
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.ParRedStatement
            module Lean4Lean.Theory.Typing.KCanonical, arity 1, cone 36
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.DescendStatement
            module Lean4Lean.Theory.Typing.DescendRefute, arity 1, cone 677
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.ParRedStatementSE
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 1, cone 37
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.DescendStatementSE
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 1, cone 678
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.crSchema_eq_parRedStatement
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 1, cone 41
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.crSchema_congr
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 12, cone 16
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.not_crSchema_of_inert
            module Lean4Lean.Theory.Typing.ConfluenceRebuildPrice, arity 13, cone 19
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
```

---

## 2. Analysis and verdicts

### 2.1 (b) The `VDefEq`-route verdict: **it does NOT avoid the re-erection.** MACHINE-CHECKED.

This is the round's main result and it **corrects a row of `StructEtaPrice.lean` §7's price table**.

§7's table has two rows about the closed-`VDefEq` route:

| | closed `VDefEq` (§7) | this round |
|---|---|---|
| induction cases added | **0** | **CONFIRMED** |
| `church_rosser` | `extra` case, already written | **REFUTED** |

**Why row 1 is right.**  `VEnv.ParRed.extra` and `VEnv.CParRed.extra` (`ChurchRosser.lean:761`,
`:795`) are quantified over `Params.Pat p r` — an abstract rule.  A new rule therefore adds no
constructor to `ParRed`/`CParRed`/`NormalEq` and no case to any induction over them.  `NormalEq`
has no `extra` constructor at all (its nine are `refl sortDF constDF appDF lamDF forallEDF etaL
etaR proofIrrel`); rules reach it only through the theorem `NormalEq.parRed`.  So on the *case*
axis the §7 table is correct.

**Why row 2 is wrong.**  A new rule does not reach `ParRed` as a case.  It reaches
`VEnv.Params` — a **ten-field interface**, of which four fields pin the rule set to two shapes and
assert they do not overlap — as an *obligation*.  `Params` is the hypothesis of every theorem in
`ChurchRosser.lean`, `church_rosser` and `NormalEq.parRed` included.  The obligation cannot be
discharged, in either orientation, at any structure:

* **Orientation 1** — the rule as §7 actually writes and machine-checks it
  (`Lean4Lean.etaDfZ`: `(fun x : S => x) ≡ (fun x : S => mk)`).
  `Lean4Lean.VEnv.Params.not_defeqs_etaDfZ` (cone 733, hole-free): **no `Params` instance may have
  this rule in `env.defeqs`.**  `Params.extra_pat` demands the rule λ-peel to a body matchable by
  `Pattern.Matches`, with the two sides sharing a telescope.  There are exactly two peels —
  `Δ = []` leaves a `lam`, `Δ = [S]` leaves `.bvar 0` — and `Pattern.Matches` walks `const`/`app`
  spines only (`Lean4Lean.Pattern.not_matches_bvar`, `Lean4Lean.Pattern.not_matches_lam`, both
  cone 92, axiom-free).  **This is route-independent inside the pattern language**: the theorem
  never mentions `Pat`, so adding constructors to `Pat`, to `SimplePattern`, or to
  `VEnv.RuleShape` does not repair it.  Only changing `Pattern.Matches` itself would — and
  `Matches` is what `ParRed.extra`, `CParRed.extra`, `Pattern.matches_inter` and the whole diamond
  argument are written against.

* **Orientation 2, zero parameters and zero fields** — flip the rule so the left-hand side is the
  constructor spine and the peeled head *is* a `const`.
  `Lean4Lean.VEnv.Params.not_pat_ctorSpine` (cone 679, hole-free): the pattern is then
  `(Pattern.const C.name).varN (D.np + C.fields.length)`, which is **letter for letter the right
  half of `Lean4Lean.VInductDecl'.iotaPat`** — the block the constructor's own ι-rule already
  registers as its major-premise position.  `Params.pat_uniq` (two registered patterns meeting a
  subpattern of one of them must be *the same pattern*) is contradicted, via
  `Pattern.inter_self` and `Subpattern.appR .refl`.  Nothing in this theorem is eta-specific: it
  prices *any* rewrite rule whose left-hand side is a saturated constructor application, which is
  precisely what surjective pairing is.

* **Orientation 2, positive parameters or fields** — `pat_simple` rejects it before `pat_uniq`
  gets to.  `Lean4Lean.SimplePattern.eq_defn_of_toPattern_varN` (cone 123, `[propext]`):
  `SimplePattern` has exactly two constructors, `.defn c` (bare `const`, arity 0) and
  `.iota r m c n` (`rec`-spine applied to `ctor`-spine), so `(const c).varN n` is a
  `SimplePattern` only at `n = 0`.  Corollary
  `Lean4Lean.VEnv.Params.not_pat_ctorSpine_of_pos` (cone 1108, hole-free).

The two obstacles bite at **complementary arities**, so between them no orientation survives at
any structure.  And the chain closes at the top: `Lean4Lean.VEnv.WF.ruleShape`
(`PatternRules.lean:578`, cone 3292, hole-free) says every rule of a well-formed environment is a
δ-, quotient- or ι-rule, and `Lean4Lean.Pat.extra` (cone 4517, hole-free) is what discharges
`extra_pat` by dispatching on it.  Making eta a legal `VDefEq` means a fourth `RuleShape`
constructor, at which point `Pat.extra` must produce a `Pat` for it — which the three theorems
above say is impossible.

**So the `VDefEq` route's cost is not "0 against 136".**  It is: extend `Pattern` and
`Pattern.Matches`; re-prove `pat_simple`, `pat_uniq`, `pat_app_l_uniq`, `pat_app_uniq` with the
new shape in the mix (these are the diamond's non-overlap conditions, and eta *does* overlap with
ι at the constructor); extend `RuleShape`, `Pat`, `Pat.extra`, `paramsOfWF`; and then re-check
`ChurchRosser.lean` in full, because `Pattern.lean` is **upstream** of it (M13: `Pattern` is in
ChurchRosser's 44-module import closure).  That is strictly worse in *kind* than a new
constructor: a missing case is work, an uninhabitable interface is vacuity — `church_rosser` is a
theorem *about* `Params.env`, so at an environment carrying the rule it would say nothing.

**Recommendation follows from this: the 14th-constructor route is the live one.**  The 136-vs-0
comparison on record should be read as 136-vs-(rebuild the pattern language), not 136-vs-0.

### 2.2 (c) The layering: **the obstacle is confirmed, and it does not block.**

The orchestrator's claim is **correct** — all four modules are downstream of `ChurchRosser` — and
I recovered the exact chains (M13).  Every one routes through `ParamsBuild`:

    DescendRefute    -> ParamsBuild -> ChurchRosser                                    (closure 54)
    KDescend         -> DescendRefute -> ParamsBuild -> ChurchRosser                   (closure 58)
    KSite7App        -> KSite7 -> KMeasure -> KEta -> KCanonical -> KDescend
                        -> DescendRefute -> ParamsBuild -> ChurchRosser                (closure 63)
    ParRedPropRefute -> KEta -> KCanonical -> KDescend -> DescendRefute
                        -> ParamsBuild -> ChurchRosser                                 (closure 61)

`ChurchRosser`'s own closure is 44 modules; none of the four is in it, so there is no cycle, only
a direction.  `KSite7App` and `ParRedPropRefute` are *transitively* downstream (7 and 6 hops), not
direct importers; the nine direct importers of `ChurchRosser` are `Theory`, `CRBetaGen`,
`CRPiDescend`, `HeadReduction`, `NormalEqStrengthen`, `ParRedKWeakN`, `ParamsBuild`,
`ParamsWitness`, `PatKHead`.

**But "no in-place rewiring is possible" does not follow, and I believe it is wrong.**  The reason
is structural: `ChurchRosser.lean` is *already parametric*, over `VEnv.Params`.  Of `Params`' ten
fields, exactly **two mention the judgment** — `pat_wf` and `extra_pat` — and the other eight
(`env`, `henv`, `univs`, `Pat`, `pat_simple`, `pat_uniq`, `pat_app_l_uniq`, `pat_app_uniq`) are
purely syntactic and transport verbatim.  So the re-erection is not a copy of a 2525-line file; it
is a *generalisation added below* `ChurchRosser` plus an *in-place* rewrite of `ChurchRosser`.

A layering that works, concretely, with nothing deleted and nothing moved downstream:

1. **New module `Theory/Typing/PatSig.lean`, below `ChurchRosser`** (its only imports would be
   `Theory/Typing/Pattern`, closure 10).  Holds the eight relation-free `Params` fields as a class
   `PatSig`.  Zero re-erection: they are syntactic.  `PatternRules.lean` (closure 44, and it does
   **not** import `ChurchRosser`) already proves all eight for `Pat env` at an arbitrary
   `VEnv.WF` — `Pat.simple`, `Pat.uniq`, `Pat.app_l_uniq`, `Pat.app_uniq` — so this module needs no
   new proof at all.
2. **`Params` becomes `PatSig` plus the two judgment fields, with the judgment a parameter.**  The
   right abstraction is already machine-checked: `ConfluenceRebuildPrice.lean` §1–§2 found the
   layer has exactly **three ingredients** — a conversion, a multi-step reduction, and a typing
   judgment — and checked its abstracted statements equal the real ones by `rfl`
   (`Lean4Lean.VEnv.crSchema_eq_parRedStatement`, cone 41, hole-free).  What exists on the
   *statement* side has to be redone on the *proof* side; that is the actual job.
3. **`ChurchRosser.lean` rewritten in place**, `NormalEq`/`ParRed`/`CParRed` taking the judgment
   as a parameter, with `abbrev NormalEq := NormalEqP (HasType env univs)` so the old names still
   resolve.
4. **The four refutation modules are not deleted and do not move.**  The transport lemmas they
   need are already written and hole-free: `Lean4Lean.crSchema_congr` (cone 16) and
   `Lean4Lean.not_crSchema_of_inert` (cone 19) — pointwise-equal ingredients give the *same*
   proposition, and a refuted statement stays refuted under an inert change of ingredients.
   `Lean4Lean.DescendStatementSE` (cone 678) against `Lean4Lean.DescendStatement` (cone 677), and
   `Lean4Lean.VEnv.ParRedStatementSE` (cone 37) against `Lean4Lean.VEnv.ParRedStatement`
   (cone 36), differ by one constant each — consistent with "same proposition, transported".

   **Residual cost, measured, and it is real:** the four modules reference the inductives
   *directly*, not only through the `*Statement` defs — e.g.
   `Lean4Lean.DescendRefute`'s `refNormalEq : @VEnv.NormalEq refParams refCtx refG refG'` and
   `refParRed_const {Γ c ls e} (H : @VEnv.ParRed refParams Γ (.const c ls) e)`.  An `abbrev`
   keeps the *type* resolving but not `NormalEq.refl` / `ParRed.app` as constructor names, so
   every `induction`/`cases` in those files needs its case names re-pointed.  Sizes:
   `DescendRefute` 589 lines / 91 decls, `KDescend` 415 / 11, `KSite7App` 535 / 12,
   `ParRedPropRefute` 222 / 6.  Mechanical, but it is four files plus `ChurchRosser`'s 2525 lines.

### 2.3 (d) The model: **verified, and it owes confluence nothing.**

* `Lean4Lean.SetModel.eq_singleton_of_recProp` — **FOUND, cone 5826, hole-free, no `sorryAx`**
  (`Theory/Typing/StructEtaPrice.lean`).  Confirmed exactly as claimed.  So the model *does*
  validate zero-field surjective pairing, and the argument for it is the recursor's own
  `OracleOK.type` obligation against the full function space — i.e. **forced, not chosen**.  Its
  supporting lemmas are hole-free too: `SetModel.mkForallType_const_eq_pow`,
  `SetModel.charFam_mem_pow`, `SetModel.recProp_at_singleton`.
* `Lean4Lean.SetModel.soundAbove` (`Theory/SetModel/SoundInduction.lean`) — **cone 7163,
  hole-free, no `sorryAx`**.  This is the single model induction site, and it runs on
  `IsDefEqStrong`, not `IsDefEq`.  A 14th constructor adds one case here.
* **Does confluence over the extended relation need anything further from `Theory/SetModel/`?
  No.**  Measured (M16): `ChurchRosser`'s 44-module import closure contains **zero**
  `Theory/SetModel/` modules, and so do the closures of `Injectivity` (40), `ParamsBuild` (52),
  `PatternRules` (44) and `Pattern` (10).  The confluence layer is purely syntactic.  The model's
  debt is to `kernel_sound`, not to `church_rosser`.
* **What the model still owes, and it is unchanged from §8's account** — I checked both steps and
  neither is done:
  1. *The `interp (D.recType j)` peel at a **general** block.*  Every peel in the tree is at a
     *specific* declaration, hand-written one binder at a time with
     `Lean4Lean.SetModel.UnitAudit.mkLam_mem_mkForallType_of_dom` (cone 5785, hole-free):
     `eqIndDecl` in `SetModel/EqOracle.lean`, `iffIndDecl` in `SetModel/IffRecLarge.lean` (five
     applications, one per binder), `unitDeclLE` in `SetModel/UnitOracleLarge.lean` (six).  There
     is **no** general-telescope version.  One file of work.
  2. *The `PropSplit` side condition* — "a motive is not classified as a proof".  Related
     machinery exists (`SetModel/PropSplitAudit.lean`, `SetModel/FalseProp.lean`,
     `SetModel/NotProofNoModel.lean`) but the name §8 gestures at,
     `Lean4Lean.SetModel.sort_not_proof`, is **NOT FOUND** in the 443-module population.  Report
     it as owed.
* **One flag, not investigated further because it is another stream's ground:**
  `Theory/SetModel/LevelAssignUnsat.lean:148` records that something "was vacuous, including
  `soundAbove` and everything downstream of it".  `soundAbove` is hole-free *today*, so this reads
  as a historical note, but anyone costing the model line should read that file first.  I did not
  touch `docs/vacuity-ledger.md`.

### 2.4 The two prior claims I was asked to verify, verified

* **The two false confluence statements transport, and the re-erection is not their repair.**
  `Lean4Lean.descendSE_uniq_sortUniq_not_all` — arity **0**, cone **6800**, hole-free.
  `Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor` — arity **22**, cone **674**, hole-free.
  Both figures match the brief to the digit.
* **`Lean4Lean.structEta_of_extra`** — cone **645**, hole-free.  Figure matches.
  **NAME CORRECTION:** the brief called it `Lean4Lean.VEnv.structEta_of_extra`; that is
  **NOT FOUND**.  It lives in the root namespace.
* **`church_rosser`'s and `NormalEq.parRed`'s standing debt, both lines as the brief requires:**
  - `Lean4Lean.VEnv.IsDefEq.church_rosser` — cone 4383, `sorryAx` **true**, holes in cone
    `[Lean4Lean.VEnv.IsDefEqU.weakN_iff, Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    Lean4Lean.VEnv.WF.rigidShapeUniqNS, Lean4Lean.VEnv.NormalEq.descend]`;
    *** WATCHED IN CONE: `[Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]` ***
  - `Lean4Lean.VEnv.NormalEq.parRed` — cone 4135, `sorryAx` **true**, same four holes;
    *** WATCHED IN CONE: `[Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]` ***
  - `Lean4Lean.VEnv.NormalEq.descend` — cone 3874, **own value is a hole**;
    *** WATCHED IN CONE: `[Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]` ***
  A clean `sorryAx` line would not have cleared these, and it is not clean either.

### 2.5 Priors, scored

| | prior | outcome |
|---|---|---|
| P1 | 60–150 relation-mentioning decls; 80–200 induction sites; grep undercounts | see §3 (proof-term walk) |
| P2 | **NO, the `VDefEq` route does not avoid the re-erection** (conf. 0.75) | **RIGHT** — and machine-checked, four theorems.  My *mechanism* was wrong: I predicted a critical-pair/joinability failure inside the diamond.  The real mechanism is one layer lower and cleaner — the rule cannot be *expressed* in `Pattern`, so it never reaches the diamond.  The counter-scenario I flagged as most plan-changing ("`ParRed` may quantify over the rule set abstractly and already prove confluence for any rule set satisfying a side condition") turned out to be **half true and decisive**: `ParRed.extra` *is* abstract over the rule set, which is why the case count is 0 — but the "side condition" is `Params`' four non-overlap fields, and eta fails them. |
| P3 | direction right, ≥1 of the four mis-attributed; a `ChurchRosserCore` split exists | **HALF RIGHT.**  Direction right, and **no** mis-attribution — all four are downstream, chains recovered.  I was wrong to expect an error; the calibration note ("attributions unreliable") led me to over-hedge a correct claim.  The split does exist, and it is cheaper than I guessed: parametricity added *below* `ChurchRosser`, not a core/instantiation copy. |
| P4 | `eq_singleton_of_recProp` hole-free; "forced" is the weak link; ≥1 further obligation from `SetModel/` for confluence | **HALF WRONG.**  Hole-free: right.  "Forced": I doubted it and it holds up — the argument is the recursor's own `OracleOK.type` obligation, and `soundAbove` is hole-free.  "Further obligation for confluence": **wrong** — measured zero `SetModel/` modules in the confluence closure.  The two owed steps are owed to `kernel_sound`, not to confluence. |
| P5 | "large independent project", several hundred lines, multi-round; cheapest win is a parametric restatement | **RIGHT on both.**  §2.2's layering is exactly the parametric restatement, and the statement-side half of it is already written and hole-free. |
| P6 | instrument risk; append-only log | held — 20 measurements, none batched. |

Net: the priors practice earned its keep on P2 (it forced me to name the counter-scenario I then
found) and cost me on P3 (calibration-driven hedging against a claim that was simply correct).

### 2.6 (e) Recommended order of work, with costs

**Do not narrow `kernel_sound`.**  Nothing below does.

**Step 0 — retire the `VDefEq` route (done, this round).**  It is not a cheaper alternative; it is
a rebuild of the pattern language.  The 136-vs-0 comparison on record should be restated as
136-vs-(rebuild `Pattern`, `Matches`, the four non-overlap fields, `RuleShape`, `Pat`, `Pat.extra`,
`paramsOfWF`, then re-check `ChurchRosser` because `Pattern` is upstream of it).  Cost: 0 — the
four theorems in `Theory/Typing/SEReerectionScope.lean` are written and hole-free.

**Step 1 — the parametric restatement of the layer, proof side.  This is the blocking step and it
is the whole job.**  `ConfluenceRebuildPrice.lean` already did it on the statement side (three
ingredients, `rfl`-checked).  Doing it on the proof side means: `PatSig` below `ChurchRosser`
(eight fields, zero new proofs — `PatternRules.lean` already proves all eight); `Params` = `PatSig`
+ two judgment fields with the judgment a parameter; `ChurchRosser.lean` rewritten in place
(2525 lines) with `NormalEq`/`ParRed`/`CParRed` parametric; `abbrev`s for the old names; case-name
re-pointing in the four downstream refutation modules (589 + 415 + 535 + 222 lines, 120 decls).
**Cost: this is a large independent project — multiple rounds, and the honest unit is "rewrite
`ChurchRosser.lean`", not "add N cases".**  Its payoff is that it is done *once* and then the
14th constructor is a parameter change rather than a 136-site edit.

**Step 2 — the fourteenth constructor, over the parametric layer.**  Only after Step 1.  The
136 sites do not go away, but they change character: over a parametric layer most of the ~40
congruence/stability sites become instances rather than edits.  The five missing commutation
lemmas §1 names (`projTermG_weakN`, `projTerm_weakN`, `etaExpansion_weakN`,
`etaExpansionG_weakN`, `etaExpansionG_instL`) are unavoidable either way and are independent of
Step 1 — **they can be done now, in parallel, by a separate stream.**  Cheapest real work
available this week.

**Step 3 — the three-file syntax/`WF` split** `StructEtaPrice.lean` §3 names (`Decl.lean`,
`Structure.lean`, `ProjGen.lean` splitting into a syntax half below `Basic.lean` and a `WF` half
above).  Independent of Steps 1–2 and also parallelisable now.

**Step 4 — the model's two owed steps** (§2.3): the general `interp (D.recType j)` telescope peel
(one file; the three existing peels are per-declaration and give the pattern), and the `PropSplit`
"a motive is not a proof" lemma (`Lean4Lean.SetModel.sort_not_proof` is NOT FOUND — it must be
written).  Independent of Steps 1–3.  Needed for `kernel_sound`, **not** for confluence.

**Not on the critical path for eta, and should not be conflated with it:** the four holes in
`church_rosser`'s cone (`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`,
`WF.rigidShapeUniqNS`, `NormalEq.descend`) and the two watched statements (`IsDefEq.uniq`,
`IsDefEq.uniqU`).  Those are the *existing* confluence debt; re-erection neither pays nor
increases it — `ConfluenceRebuildPrice.lean` §5 already showed the refutations transport verbatim.

**Parallelisable now (no dependency on Step 1):** Step 2's five commutation lemmas, Step 3's file
split, Step 4's two model steps.  **Serial:** Step 1 then the rest of Step 2.
### M21 [2026-09-04T02:20:41Z] §5 added: the mk-headed-iota encoding also collides. Build OK, hole-free.
```

population: 443 built modules
watching 6 declarations for cone membership

FOUND       Lean4Lean.Pattern.const_varN_inj
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 5, cone 121
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
FOUND       Lean4Lean.VEnv.Params.not_pat_ctorHeadedIota
            module Lean4Lean.Theory.Typing.SEReerectionScope, arity 13, cone 697
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
NOT FOUND   Lean4Lean.Pat.rec_ne_ctor
            (before writing "absent", also query by conclusion shape — a different name for the same content is the failure mode that bites)

Full axiom bar of Lean4Lean/Theory/Typing/SEReerectionScope.lean (7 theorems, all hole-free):
'Lean4Lean.Pattern.not_matches_bvar' does not depend on any axioms
'Lean4Lean.Pattern.not_matches_lam' does not depend on any axioms
'Lean4Lean.VEnv.Params.not_defeqs_etaDfZ' depends on axioms: [propext, Quot.sound]
'Lean4Lean.VEnv.Params.not_pat_ctorSpine' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SimplePattern.eq_defn_of_toPattern_varN' depends on axioms: [propext]
'Lean4Lean.VEnv.Params.not_pat_ctorSpine_of_pos' depends on axioms: [propext, Quot.sound]
'Lean4Lean.VEnv.Params.not_pat_ctorHeadedIota' depends on axioms: [propext, Quot.sound]

GAP I FOUND IN MY OWN §2-§4 AND CLOSED:
  §4 rules out the BARE constructor spine (Pattern.const C.name).varN n only.
  At positive fields the eta LHS 'S.mk ps (proj0 ps x) ... (projk-1 ps x)' IS expressible
  as SimplePattern.iota with the roles SWAPPED: r := C.name, m := np+k-1,
  c := the head of the last projection term (a recursor), n := its arity.
  So §4 alone did NOT close the route.  §5's not_pat_ctorHeadedIota closes it:
  the iota-rule's own constructor block (const C.name).varN (np+|fields|) is Pattern.var of
  (const C.name).varN (np+k-1) -- exactly the LEFT half of the sneaky pattern -- so
  Pattern.inter succeeds through 'inter (.app f a) (.var f')' and pat_uniq fires again.
  Residue taken as a hypothesis: mkRecName T.name != C.name, which is what
  Lean4Lean.Pat.rec_ne_ctor establishes (PatternRules.lean:362).
```

### M22 [2026-09-04T02:21:17Z] §5's residual hypothesis IS discharged by an existing hole-free lemma
```
NOT FOUND   Lean4Lean.Pat.rec_ne_ctor
FOUND       Lean4Lean.rec_ne_ctor
            module Lean4Lean.Theory.Typing.PatternRules, arity 10, cone 740
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6

Its statement, verbatim (PatternRules.lean:362):
theorem rec_ne_ctor {env : VEnv} {D D' : VInductDecl'} {j j' : Nat} {T : VIndType}
    {C : VIndCtor} (hT : D.types[j]? = some T)
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hctor : env.constants C.name = some ⟨D'.uvars, C.type D' j'⟩) :
    Lean.mkRecName T.name ≠ C.name := fun h => by
  rw [h, hctor, Option.some_inj] at hrec
  exact recType_ne_ctorType hT (congrArg VConstant.type hrec).symm


-> exactly the hypothesis §5 takes, and Pat.iota already carries both env.constants facts
   it needs.  So not_pat_ctorHeadedIota's hypothesis is not an extra assumption; it is
   available in the tree, hole-free.

DOC BUG (in an existing file, NOT edited by me): PatternRules.lean's own docstrings refer to
this lemma twice as 'Pat.rec_ne_ctor' (e.g. around line 278, 'Not decoration: see
Pat.rec_ne_ctor').  That name does not exist; the lemma is Lean4Lean.rec_ne_ctor, root
namespace.  Reported, not fixed -- this round owns no existing file.
```


---

## 3. (a) The enumeration — timestamped, from proof terms

Delegated proof-term walk. Build warm; **population 443 built modules** (whole default target;
`Lean4Lean.Experimental` excluded as it is not in `defaultTargets`; `Lean4Lean.Replay` +
reverse-closure dropped for an `ImportGraph` name collision). Windows, UTC 2026-09-04:
warm-build check 02:09:28–02:09:42; parts 1/2/3 run 1 02:11:40–02:13:28 (population 442);
`church_rosser` consumers 02:15:15–02:15:43; run 2 for reproducibility 02:16:23–02:18:10
(population 443, byte-identical output). The extra module in run 2 is my own
`Lean4Lean.Theory.Typing.SEReerectionScope`, built 02:12:35 mid-measurement; it contributes zero
hits. Reproduce with `lake env lean --run /tmp/relcount.lean` / `/tmp/cr.lean` (scratch, `/tmp`
only; no repo file was created or modified by the walk).

### 3.1 Induction sites — raw

| relation | raw eliminator-applying declarations |
|---|---|
| `Lean4Lean.VEnv.NormalEq` | **34** |
| `Lean4Lean.VEnv.ParRed` | **28** |
| `Lean4Lean.VEnv.CParRed` | **3** |
| `Lean4Lean.VEnv.ParRedK` | **24** |
| `Lean4Lean.VEnv.ParRedKn` | **9** |
| sum | **98** |

Eliminators seen: `.rec`, `.recOn`, `.casesOn`, `.brecOn`, `.below`. Exactly three per relation
(`recOn`, `casesOn`, `brecOn`) were netted out by the own-name rule; exactly one per relation, the
auto-generated `‹Rel›.below.casesOn`, survives it and is **still auto-generated**.

`ParRedS` is a `def` (`ChurchRosser.lean:1231`, `ReflTransGen (ParRed Γ)`), not an inductive: 0
induction sites, but see §3.3.

**Comparison to the figure on record.** `StructEtaPrice.lean` §1 (measured 2026-09-03, population
**421**) reported NormalEq **31**, ParRed **26**, ParRedK **23**. Today, population **443**:
**34 / 28 / 24**. The tree grew 22 modules in between; the earlier figures are not wrong, they are
stale. `CParRed` and `ParRedKn` were not in §1's table at all.

### 3.2 Induction sites — hand-written declarations, and a CORRECTION to the walk's own total

Collapsing compiler-generated pieces (`.below.casesOn`, `.match_N_M`, `._unary`) onto the one
hand-written declaration they belong to:

| relation | distinct hand-written source declarations |
|---|---|
| `Lean4Lean.VEnv.NormalEq` | 32 |
| `Lean4Lean.VEnv.ParRed` | 27 |
| `Lean4Lean.VEnv.CParRed` | 2 |
| `Lean4Lean.VEnv.ParRedK` | 23 |
| `Lean4Lean.VEnv.ParRedKn` | 8 |
| sum (double-counts overlaps) | 92 |

The walk reported the **union** as **93**. That cannot be right — a union cannot exceed the sum of
its parts — and the walk flagged its own arithmetic as unresolved. **I recounted it by hand from
the walk's own name lists.** Four declarations induct on two relations each:

* `Lean4Lean.VEnv.NormalEq.parRed` — on `NormalEq` and on `ParRed`
* `Lean4Lean.VEnv.ParRed.triangle` — on `ParRed` and on `CParRed`
* `Lean4Lean.VEnv.parRedKStatement_of_rows` — on `NormalEq` and on `ParRedK`
* `Lean4Lean.VEnv.parRedKStatementN_succ` — on `NormalEq` and on `ParRedKn`

so the union is 92 − 4 = **88**.

**THE RE-ERECTION FIGURE IS 88 DISTINCT HAND-WRITTEN DECLARATIONS.**

The 93 is explained exactly: it is 88 plus the **five** auto-generated `‹Rel›.below.casesOn`
entries, one per relation, which the walk's per-module union table left in. Independent check on
the same discrepancy: the union table gives `ChurchRosser` **21**, but recounting from the name
lists gives 11 (`NormalEq`) + 6 new (`ParRed`) + 1 new (`CParRed`) = **18**, and 21 − 18 = the
three `below.casesOn` entries that live in that module. 93 − 5 = 88 on both routes.

### 3.3 Statement-mention count — declarations whose TYPE references the relation

| relation | total mentioning it in type | compiler-generated | hand-written statements to restate |
|---|---|---|---|
| `Lean4Lean.VEnv.NormalEq` | 272 | 143 | **129** |
| `Lean4Lean.VEnv.ParRed` | 118 | 55 | **63** |
| `Lean4Lean.VEnv.CParRed` | 30 | 27 | **3** |
| `Lean4Lean.VEnv.ParRedS` | 110 | 64 | **46** |
| `Lean4Lean.VEnv.ParRedK` | 95 | 27 | **68** |
| sum | 625 | 316 | **309** |

309 is an **upper bound, loose by 4**: `KTable.mk.inj`, `KTable.mk.injEq`,
`KTable.mk.sizeOf_spec` and `DescentLam.eq_def` are auto-generated but sit in the hand-written
column because the walk's predicate does not catch them. So **305–309**. This figure double-counts
declarations mentioning two relations; it was not de-duplicated, so treat it as an upper bound on a
union that is smaller.

Per-module, hand-written:

* **NormalEq (129)** — ChurchRosser 33, KCanonical 9, KMeasure 9, ParRedKGraded 7,
  ConfluenceRebuildPrice 6, KSite7 6, KSite7App 6, Verify.QuotAppParams 6, KKetaRow 5,
  PatAppParams 5, CRBetaGen 4, DescendRefute 4, KDiamondJoin 4, NormalEqStrengthen 4,
  Verify.Typing.ConstSpine 4, CRPiDescend 3, KEtaDiamond 3, KSite7Rows 3, KDescend 2, KEta 2,
  ParRedCycle 2, ParRedPropRefute 2.
* **ParRed (63)** — ChurchRosser 15, DescendRefute 8, Verify.QuotAppParams 8, KEta 6, KCanonical 4,
  PatAppParams 5, ParRedPropRefute 3, Verify.Typing.ConstSpine 3, ConfluenceRebuildPrice 2,
  HeadReduction 2, KDescend 2, ParamsWitness 2, ParRedCycle 1, ParRedMissing 1,
  Verify.Typing.Rigidity 1.
* **CParRed (3)** — all in ChurchRosser: `Lean4Lean.VEnv.CParRed.exists`,
  `Lean4Lean.VEnv.CParRed.toParRed`, `Lean4Lean.VEnv.ParRed.triangle`.
* **ParRedS (46)** — ChurchRosser 16, ConfluenceRebuildPrice 6, HeadReduction 4,
  Verify.Typing.ConstSpine 4, CRBetaGen 3, DescendRefute 3, KCanonical 3, CRPiDescend 2,
  KMeasure 2, KDescend 1, KEta 1, KSite7 1.
* **ParRedK (68)** — KEta 18, KMeasure 12, QuotKAppEta 7, KSite7 6, KSite7App 6,
  Verify.Typing.QuotKEta 4, DescendRestate 3, KDiamondJoin 3, KSite7Rows 3, DescendConstSpineK 2,
  KKetaRow 2, ParRedMissing 1, ParRedPropRefute 1.

### 3.4 Induction sites by module — the union of 88, with the autos removed

Walk's table minus the five `below.casesOn` entries (ChurchRosser held three of them: `NormalEq`'s,
`ParRed`'s and `CParRed`'s; `KEta` held `ParRedK`'s; `KKetaRow` held `ParRedKn`'s):

    ChurchRosser 18, KEta 10, DescendRefute 7, Verify.QuotAppParams 7,
    Verify.Typing.ConstSpine 7, KKetaRow 5, KSite7 4, ParRedKGraded 4,
    DescendRestate 3, HeadReduction 3, KCanonical 3, PatAppParams 3,
    ConfluenceRebuildPrice 2, KMeasure 2, KSite7App 2,
    and 1 each in CRBetaGen, CRPiDescend, DescendConstSpineK, KDescend,
    KDiamondJoin, KSite7Rows, NormalEqStrengthen, QuotKAppEta
    -- 22 modules, 88 declarations, minus the 4 cross-relation duplicates already netted.

### 3.5 `church_rosser`'s consumers

Three variants, all in `ChurchRosser.lean`: `Lean4Lean.VEnv.ParRed.church_rosser` (:1223),
`Lean4Lean.VEnv.ParRedS.church_rosser` (:2435), `Lean4Lean.VEnv.IsDefEq.church_rosser` (:2480).
`IsDefEq.church_rosser` inducts on `VEnv.IsDefEq`, not on any of the five relations, so it appears
in none of §3.1's lists — it is on the `IsDefEq` line of `StructEtaPrice` §1's 22.

* `Lean4Lean.VEnv.IsDefEq.church_rosser` — **9 consumers**:
  `Lean4Lean.VEnv.IsDefEq.reduce_forallE`, `Lean4Lean.VEnv.IsDefEq.reduce_sort` (HeadReduction);
  `Lean4Lean.VEnv.crStatement_holds` (KCanonical); `Lean4Lean.VEnv.church_rosser_of_patWF`
  (ParamsBuild); `Lean4Lean.VEnv.propLoopEnv_church_rosser_fires` (ParamsWitness);
  `Lean4Lean.VEnv.IsDefEq.constApp_inv`, `Lean4Lean.VEnv.IsDefEqU.constApp_forallE_false`,
  `Lean4Lean.VEnv.IsDefEqU.constApp_sort_false`, `Lean4Lean.VEnv.constRigid_of_weakNorm`
  (Verify.Typing.ConstSpine).
* `Lean4Lean.VEnv.ParRed.church_rosser` — 1: `Lean4Lean.VEnv.ParRedS.church_rosser`.
* `Lean4Lean.VEnv.ParRedS.church_rosser` — 1: `Lean4Lean.VEnv.CRDefEq.trans`.

### 3.6 Sizes

**30 modules** appear in at least one breakdown; **17 547 lines** total. Largest:
`ChurchRosser.lean` 2525, `KSite7.lean` 1264, `KMeasure.lean` 1160, `KEta.lean` 1031,
`ConfluenceRebuildPrice.lean` 769, `HeadReduction.lean` 696, `Verify/QuotAppParams.lean` 667,
`Verify/Typing/ConstSpine.lean` 665, `KDiamondJoin.lean` 619, `KCanonical.lean` 617,
`KKetaRow.lean` 603, `DescendRefute.lean` 589, `KSite7App.lean` 535.

Declarations in `ChurchRosser.lean`: **509** constants in the environment, **126** after filtering
internal-detail / constructor / recursor / aux names; a grep of line-start declaration headers
finds **95**. So 95 and 126 bracket the source-level declaration count.

**Caveat carried forward from the walk:** `ChurchRosser.lean:2011` carries a `sorry` (build
warning) — that is `NormalEq.descend`, already accounted for in §2.4.

### 3.7 So: what exactly must be re-erected

**88 hand-written declarations carry an induction/`cases` site on one of the five relations, and
305–309 hand-written statements mention one of them in their type.** Add `Params`' two
judgment-bearing fields (`pat_wf`, `extra_pat`) — the other eight transport verbatim — and
`ChurchRosser.lean`'s own 95–126 declarations across 2525 lines. The work spans **22 modules for
the induction sites and 30 modules in total, 17 547 lines**, and it reaches outside `Theory/` into
`Verify/QuotAppParams.lean` (7 sites), `Verify/Typing/ConstSpine.lean` (7) and
`Verify/Typing/{Rigidity,QuotKEta}.lean`.

**That is the honest answer to (e)'s implicit question: this is a large independent project.** It
is not 136 and it is not 0; on the live route it is **88 induction sites + ~305 statements across
30 modules**, and the 136-vs-0 comparison on record compares two figures that measure different
things (136 counted eight relations including `IsDefEq`/`IsDefEqStrong`; 0 counted only cases added
to `ParRed`/`NormalEq`, which §2.1 shows is the wrong axis).

---

## 4. Bottom line for the next reader

1. **The `VDefEq` route is dead as a shortcut.** Seven hole-free theorems in
   `Lean4Lean/Theory/Typing/SEReerectionScope.lean` say the closed-`VDefEq` rule cannot be a
   `VEnv.Params` rule in any orientation at any structure. `StructEtaPrice.lean` §7's table row
   "`church_rosser` | `extra` case, already written" should be struck; its "induction cases added:
   0" row is correct but measures the wrong axis. **This is the one substantive correction of the
   round.** Do not edit `StructEtaPrice.lean` on my account — it is not mine and the correction
   lives here and in the new file's docstring.
2. **The live route is the fourteenth constructor**, and its blocking step is the parametric
   restatement of the confluence layer (§2.6 Step 1). `ConfluenceRebuildPrice.lean` already did
   that restatement on the *statement* side, hole-free; the job is the *proof* side.
3. **The price is 88 induction sites + 305–309 statements across 30 modules / 17 547 lines**, not
   136 and not 0. It reaches into `Verify/`.
4. **The model owes confluence nothing** (zero `SetModel/` modules in the confluence import
   closure) and owes `kernel_sound` two named, parallelisable steps.
5. **Parallelisable right now, no dependency on the big rewrite:** the five missing commutation
   lemmas; the three-file syntax/`WF` split; the model's general `interp (recType)` peel; the
   `PropSplit` motive-not-a-proof lemma.
6. **Two name corrections for future briefs.** `Lean4Lean.VEnv.structEta_of_extra` → NOT FOUND, it
   is `Lean4Lean.structEta_of_extra`. `Lean4Lean.Pat.rec_ne_ctor` → NOT FOUND, it is
   `Lean4Lean.rec_ne_ctor`, and `PatternRules.lean`'s own docstrings misname it.
