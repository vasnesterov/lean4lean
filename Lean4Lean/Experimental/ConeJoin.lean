import Lean4Lean.Verify.Typing.ProjLvlCongr  -- added 2026-08-31: EqUpToLevels kit for TrProj.uniq
import Lean4Lean.Theory.Typing.ParRedKWeakN  -- added 2026-08-31: entry (2) = the hole restated
import Lean4Lean.Verify.SoundnessAssembly  -- added 2026-08-31: the kernel_sound assembly
import Lean4Lean.Theory.SemanticRouteClosed  -- added 2026-08-31: injectivity-stream semantic route
import Lean4Lean.Verify.PreludeVacuity  -- added 2026-08-31: where the Bridge chain is false
import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Theory.Typing.ParamsBuild
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Soundness
-- Leaf modules that nothing else imports. They are here so that
-- `scripts/dup-names.lean` and `scripts/sorry-census.lean`, which measure this
-- file's closure, actually see them: a leaf outside the closure is invisible to
-- both, so a duplicate name in one would be reported as "no duplicates" and a
-- hole in one would be missing from the census. A stream caught exactly that on
-- 2026-08-30 -- the dup-names clean line was not evidence about its own new
-- files. Add every new leaf here.
import Lean4Lean.Verify.Typing.ProjClosedGWitness
import Lean4Lean.Verify.Typing.ProjGenLiftWitness
import Lean4Lean.Verify.Typing.ProjGenInstWitness
import Lean4Lean.Verify.Typing.ProjGenMinorWitness
import Lean4Lean.Verify.Typing.ProjGenMinorNarrow
import Lean4Lean.Verify.Typing.ProjGenMotiveWitness
import Lean4Lean.Verify.Typing.ProjGenSwapNarrow
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.ProjWfWitness
import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.InductFlip
import Lean4Lean.Verify.QuotConsts
import Lean4Lean.Verify.QuotReach
import Lean4Lean.Verify.EqSafety
import Lean4Lean.Verify.SafeFragment
import Lean4Lean.Verify.Inductive.AddDeclWF
import Lean4Lean.Verify.Inductive.AddInductiveStep
import Lean4Lean.Verify.Inductive.RunIdentity  -- 2026-09-01: run_types_eq, and the loose-bvar refutation of AddInductiveStepWF
import Lean4Lean.Verify.ClosednessPropagation  -- 2026-09-01: the closedness measurement, and the guard's consequences
import Lean4Lean.Theory.Typing.KMeasure
import Lean4Lean.Theory.Typing.KSite7
import Lean4Lean.Theory.Typing.KDescend
import Lean4Lean.Theory.Typing.KCanonical
import Lean4Lean.Theory.Typing.RetypeCase
import Lean4Lean.Theory.Typing.ProofRetypeHeads
import Lean4Lean.Theory.Typing.BaseUniqTerm
import Lean4Lean.Theory.Typing.StrengthenAxiom
import Lean4Lean.Theory.Typing.StrengthenWitness
import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Theory.Typing.SortClauses
import Lean4Lean.Theory.Typing.AppCase
import Lean4Lean.Theory.Typing.SortRedApp
import Lean4Lean.Theory.Typing.DefInvRefute
import Lean4Lean.Theory.Typing.RegPiSat
import Lean4Lean.Theory.Typing.PatWFIota
-- Imports `PiLevelPin`, which was itself outside this closure until 2026-08-31.
import Lean4Lean.Theory.Typing.RigidNodeCircle
import Lean4Lean.Theory.Typing.ConstSubstNested
import Lean4Lean.Theory.Inductive.NestedKeys
import Lean4Lean.Theory.Inductive.NestedPositivity
import Lean4Lean.Theory.Inductive.StructureExamples
-- `SetModel/` was invisible to both instruments until 2026-08-30: `VEnv.PropTypeAgree`
-- was declared with two DIFFERENT statements, in `Theory/Typing/UniqueTypingN.lean`
-- and `Theory/SetModel/PropSplitAudit.lean`, so no `SetModel/` module could enter this
-- cone at all. The `Theory/Typing/` one is now `PropTypeAgreeN`, matching that file's
-- own `IsPropN`/`HasTypeN`/`SortInvN` convention.
import Lean4Lean.Theory.SetModel.StableAudit
import Lean4Lean.Theory.SetModel.PropSplitAudit
import Lean4Lean.Theory.SetModel.PropUniqFromFalse
import Lean4Lean.Theory.SetModel.PropReduce
import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.SetModel.CoherentWitness
import Lean4Lean.Theory.SetModel.CtorTransExamples
import Lean4Lean.Theory.SetModel.LevelAssignUnsat
import Lean4Lean.Theory.SetModel.FalseProp
-- Added 2026-08-31 after a sweep found 59 of 265 modules outside this closure, 26 of them
-- mentioning `sorry`.  The worst was `Theory/Equiconsistency.lean`: the single statement
-- `kernel_sound` most needs (`Consistent ZFC+Inacc -> leanTTConsistent`) was a `sorry` that
-- NOTHING imported, so the census had never counted it.  `scripts/cone-orphans.py` is now a
-- standing check that fails if any non-Experimental, non-Tests module is missing here.
import Lean4Lean.Theory.Equiconsistency
import Lean4Lean.Theory.LevelSat
import Lean4Lean.Theory.SetModel.NotProofNoModel
import Lean4Lean.Theory.SetModel.PropSplitUp
import Lean4Lean.Theory.SetModel.QuotInterp
import Lean4Lean.Theory.SetModel.CnstRecursion
import Lean4Lean.Theory.SetModel.InductOracleAudit
import Lean4Lean.Theory.SetModel.AxiomsValidatedAudit
import Lean4Lean.Theory.Typing.ConstInvWitness
import Lean4Lean.Theory.Typing.ConstVar
import Lean4Lean.Theory.Typing.CtxConvIndex
import Lean4Lean.Theory.Typing.Enlarged
import Lean4Lean.Theory.Typing.EnlargedModel
import Lean4Lean.Theory.Typing.KSite7Rows  -- 2026-08-31: imports KSite7App; carries the ParRedK restatement
import Lean4Lean.Theory.Typing.ParRedPropRefute
import Lean4Lean.Theory.Typing.SortUniqDown
import Lean4Lean.Theory.Typing.StrengthenCanon
import Lean4Lean.Theory.Typing.StrengthenVerdict
import Lean4Lean.Theory.Typing.StructureRuleFree
import Lean4Lean.Theory.Typing.SubstTRefute
import Lean4Lean.Theory.Typing.UniqSort
import Lean4Lean.Verify.Typing.RecTypePeel
import Lean4Lean.Verify.Typing.StructureUniq
import Lean4Lean.Theory.Typing.NormalEqStrengthen
import Lean4Lean.Theory.Typing.StrengthenPiProp  -- added 2026-08-31: round 7 Prop/Pi slices of the weakN_iff trans residual
import Lean4Lean.Verify.Typing.ProjSpineInv
import Lean4Lean.Verify.Typing.WeakNormRefute
import Lean4Lean.Theory.Typing.InjSortPiModel  -- added 2026-08-31: sort/Pi separation, and the vacuity of the packaged part-4 supply
import Lean4Lean.Theory.Inductive.RestoreBridge  -- 2026-08-31: addIndRulesR substitutes; the dirty witness refutes NOTHING; (A) closed for np = 0
import Lean4Lean.Theory.SetModel.CoherentConstShape  -- added 2026-08-31: CoherentOn cannot separate a constant from a universe or a Pi
import Lean4Lean.Theory.Typing.InjChainStep  -- added 2026-08-31: SortUniq splits over PiInv into a bridge entry plus ConvStep2
import Lean4Lean.Theory.Typing.StrengthenAudit  -- added 2026-08-31: the neutral residual bounded three ways, and no syntactic slice of b can help
import Lean4Lean.Theory.Typing.InjSpineTransport  -- added 2026-08-31: hole B's ProofTransport tax is only ConvStep2, not all of hole A
import Lean4Lean.Verify.Typing.ProjWeakInv  -- added 2026-08-31: TrProj.weak'_inv's residual, reduced and bounded
import Lean4Lean.Theory.SetModel.InaccChainOmega  -- 2026-09-01: the hκ gap, one κ for every finite length
import Lean4Lean.Theory.Inductive.NestedRules  -- 2026-09-01: the (B)/(C) bridges
import Lean4Lean.Theory.SetModel.ModelFitsVacuous  -- 2026-09-01: ModelFitsInput is FALSE; the repair narrows to PureOverPrelude
import Lean4Lean.Theory.Typing.InjMidpoint  -- 2026-09-01: ConvStep2 localised at its midpoint; three of six heads free; the sortDF reading refuted
import Lean4Lean.Theory.Typing.KKetaRow  -- 2026-09-01: ParRedK graded by redex height; AppKetaRow's hard half free; one weakN_iff entry removed from site 7
import Lean4Lean.Verify.Typing.ProjInhab  -- 2026-09-01: uninhabited-prop existence IS VEnv.Consistent; first positive instance of the residual
import Lean4Lean.Theory.Typing.ParRedKGraded  -- 2026-09-01: eight non-keta rows graded; AppKetaRow DISCHARGED -- site 7 for ParRedK from WeakNInvDS alone
import Lean4Lean.Theory.Typing.InjMidLocal  -- 2026-09-01: the two costly midpoint heads re-priced at localised residuals
import Lean4Lean.Theory.SetModel.ModelExists  -- 2026-09-01: Input A DISCHARGED -- ModelExistsInput is a theorem
import Lean4Lean.Theory.SetModel.InductOracleWitness  -- 2026-09-01: the .induct residual satisfied at a WF, reachable block
import Lean4Lean.Theory.SetModel.AboveAudit  -- 2026-09-01: the Above wrapper weakens nothing at or below ModelFits; CtxAgree is the greatest CtxInvariant
import Lean4Lean.Theory.Typing.InjChainLower  -- 2026-09-01: SortChainAt at .bvar 0 IS ConvSortInv; the sort-side localisation collapses
import Lean4Lean.Verify.Inductive.NestedRestore  -- 2026-09-01: VIndRestore from checker data + the _nested name barrier
import Lean4Lean.Theory.Typing.CRBetaGen  -- 2026-09-01: parRed_beta with the argument mismatch absorbed; ChurchRosser:1438's NormalEq.trans removed
import Lean4Lean.Theory.SetModel.PropUpFits  -- 2026-09-01: ModelFits from InstDescendUp; the relation slot discharged for the lift-closed split
import Lean4Lean.Theory.Typing.InjPiInhab  -- 2026-09-01: ConvCStrengthen retired as unnecessary; ConvStep2 from the two .bvar 0 residuals alone
import Lean4Lean.Theory.Typing.CRPiDescend  -- 2026-09-01: hasType_app_bvar0 from TypingStrengthening alone; site 7's appDF x beta row is weakN_iff-free
import Lean4Lean.Theory.Inductive.NestedTele  -- 2026-09-01: the motive-entry vacuity above np=0 and its general-Gamma repair
import Lean4Lean.Verify.Inductive.NestedRestoreWit  -- 2026-09-01: RestoreData satisfied; AddNested + InductStepNested at mkRestore
import Lean4Lean.Theory.Typing.StrengthenInhabGate  -- 2026-09-01: the typing half's obstruction IS its uninhabited stripped entries -- closes the handed-over-inhabitant route
import Lean4Lean.Verify.Inductive.NestedOccData      -- 2026-09-01: OccResidue reduced to member+occurs; head and ctorName_inv closed in general
import Lean4Lean.Verify.Inductive.NestedRunInvariant -- 2026-09-01: MWF, the nested-branch M calculus with the state invariant a parameter
import Lean4Lean.Theory.Typing.InjPiRogue  -- 2026-09-01: Pi-side rogue Ordered env; ConvPiFromEntry is FALSE at Ordered strength, so the localisation program must consume VEnv.WF
import Lean4Lean.Theory.Typing.InjOneFact  -- 2026-09-01: the one fact stated once (ShapeLinkAgree = 3 consumers, both ways); betaMid COLLAPSES SortMidNonSort and PiMidNonPi into their targets
import Lean4Lean.Theory.SetModel.UnitOracleWitness  -- 2026-09-01: the .induct residual at a WF block with NO empty domain; the frontier is isLE, not Prop
import Lean4Lean.Theory.SetModel.UnitOracleLarge  -- 2026-09-01: the .induct residual at the LARGE eliminator; the oracle's level branch is FORCED; IndInterp was not needed
import Lean4Lean.Theory.SetModel.InstDescendAudit  -- 2026-09-01: sort_inst's recorded refutation is SYMMETRIC; the level condition is free; the shared residual is UniqueTyping + sort-inversion
import Lean4Lean.Theory.SetModel.UnitEtaPairing  -- 2026-09-01: zero-field surjective pairing at a MUTUAL block; IsSubsingletonSignature3.single is the singleton-block assumption in the model's own language
import Lean4Lean.Theory.Typing.DescendRestate  -- 2026-09-01: descend's restatement bounded both ways; the ParRedKn route closed for it
import Lean4Lean.Theory.Typing.ParRedMissing  -- 2026-09-01: what ParRed lacks, as CONSTRUCTORS of an extension; all three descend witnesses repaired, and the extension is cyclic
import Lean4Lean.Theory.Typing.ParRedCycle  -- 2026-09-01: the cycle is essential, no grading helps, and the confluence layer reduces to M3 (PatMajorCanonical)
import Lean4Lean.Theory.Typing.PatAppParams  -- 2026-09-01: first Params instance registering .app patterns (appParams); PatMajorCanonical true and non-vacuous there; KStep.stuck_fires closed
import Lean4Lean.Verify.Inductive.TrIndDeclNCtorOwn  -- 2026-09-01: TrIndDeclN.ctorName_own -- producer side for all three paths, six-consumer audit, RestoreData.ctor's prefix half
import Lean4Lean.Verify.QuotAppParams  -- 2026-09-01: canonical .app-pattern instance (quotParams, one PiInv away); M3 and KDiamond FALSE there; parRed/church_rosser refutations reachable
import Lean4Lean.Verify.TypeChecker.UnitEta  -- 2026-09-01: zero-field eta over IsStructureG; UnitLikeBridgeG satisfiable at a two-type mutual block
import Lean4Lean.Verify.TypeChecker.EtaStructG  -- 2026-09-01: StructEtaG over IsStructureG with projTermG -- projCore_arity_wrong INERT; the wall is TrProj carrying IsStructure
import Lean4Lean.Verify.TypeChecker.FiringWitness  -- 2026-09-01: the three "never fires" gates, fired
import Lean4Lean.Theory.Typing.KEtaDiamond  -- 2026-09-01: the lambda-congruence induction; the eta-half reduces to injectivity, not the rule table
import Lean4Lean.Theory.Typing.KDiamondJoin  -- 2026-09-01: KDiamond/M3 as joinability, and its CR price -- the repair works and lands back on confluence

/-!
# Acceptance test: the `PatternRules` cone and the `Verify/` cone join

Until 2026-08 these two import cones could not appear in one file: seven declarations were
declared twice under the same name, and Lean rejects an import that re-declares a name.  The
wall sat directly on goal 2's critical path — nothing proved through
`Theory/Typing/ParamsBuild.lean` (`VEnv.paramsOfWF`, Church–Rosser, head reduction) could
reach the proof of `Lean4Lean.kernel_sound`, which lives in `Verify/`.

The duplicates are gone: `VEnv.addConst_defeqs`, `VEnv.addConstList_defeqs`,
`VEnv.addConsts_defeqs`, `VEnv.addDefEqs_le` and `VEnv.addDefEqs_defeqs` now have a single
copy each, in `Theory/Typing/EnvLemmas.lean`, which every side already imports.

This file is the standing regression test: **if it compiles, the wall is down.**  It is not
in `defaultTargets`; build it with `lake build Lean4Lean.Experimental.ConeJoin`.  See
`docs/handoff-collisions.md`.
-/

open Lean4Lean

-- from the `PatternRules` cone
#check @Lean4Lean.VEnv.HasArgs.defeqDFC
#check @Lean4Lean.VEnv.RuleShape

-- from `ParamsBuild`, the payload the wall was blocking
#check @Lean4Lean.VEnv.paramsOfWF
#check @Lean4Lean.VEnv.IsDefEq.church_rosser

-- from `Verify/`
#check @Lean4Lean.kernel_sound
#check @Lean4Lean.TrEnv

-- the deduplicated lemmas, one copy, visible to both sides
#check @Lean4Lean.VEnv.addConst_defeqs
#check @Lean4Lean.VEnv.addConstList_defeqs
#check @Lean4Lean.VEnv.addConsts_defeqs
#check @Lean4Lean.VEnv.addDefEqs_le
#check @Lean4Lean.VEnv.addDefEqs_defeqs
