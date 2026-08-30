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
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.ProjWfWitness
import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.InductFlip
import Lean4Lean.Verify.QuotConsts
import Lean4Lean.Verify.EqSafety
import Lean4Lean.Verify.SafeFragment
import Lean4Lean.Verify.Inductive.AddDeclWF
import Lean4Lean.Theory.Typing.KMeasure
import Lean4Lean.Theory.Typing.KDescend
import Lean4Lean.Theory.Typing.KCanonical
import Lean4Lean.Theory.Typing.RetypeCase
import Lean4Lean.Theory.Typing.StrengthenAxiom
import Lean4Lean.Theory.Typing.StrengthenWitness
import Lean4Lean.Theory.Typing.SortClauses
import Lean4Lean.Theory.Typing.AppCase
import Lean4Lean.Theory.Typing.SortRedApp
import Lean4Lean.Theory.Typing.DefInvRefute
import Lean4Lean.Theory.Typing.RegPiSat
import Lean4Lean.Theory.Typing.PatWFIota
import Lean4Lean.Theory.Typing.ConstSubstNested
import Lean4Lean.Theory.Inductive.NestedKeys
import Lean4Lean.Theory.Inductive.NestedPositivity
import Lean4Lean.Theory.Inductive.StructureExamples

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
