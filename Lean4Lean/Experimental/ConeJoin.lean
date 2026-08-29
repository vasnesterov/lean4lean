import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Theory.Typing.ParamsBuild
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Soundness

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
