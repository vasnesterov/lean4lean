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
