/-
The real hole census: declarations whose VALUE contains `sorryAx`.

Why this exists. On 2026-08-29 the orchestrator reported "89 sorries remaining"
from `grep -rn sorry --include=*.lean`. The true number was 21. The grep counted
docstrings, module comments, prose discussing sorries, and the word inside
identifiers -- and it counted eight files as holding nine holes when they held
none at all. That is the same name-based-count failure this project keeps
telling streams not to commit, made by the orchestrator.

Run:  lake env lean scripts/sorry-census.lean

It imports `Experimental.ConeJoin` so that BOTH the Theory and Verify cones are
in the environment; importing only one silently under-reports. Internal names
are skipped (they mirror their parents), and theorem values are read by an
explicit match because `ConstantInfo.value?` returns `none` for `.thmInfo` --
the scan trap that silently reports a cone of size 0.
-/
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    -- a declaration whose VALUE literally contains sorryAx = a real hole
    let hasSorry := match ci with
      | .thmInfo v => v.value.hasSorry
      | _ => match ci.value? (allowOpaque := true) with
             | some v => v.hasSorry
             | none => false
    if hasSorry then
      let m := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames.getD i.toNat default)
        | none => `_current
      byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mut total := 0
  for (m, ns) in byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    total := total + ns.size
    logInfo s!"{m}: {ns.size}  {ns.toList.take 4}"
  logInfo s!"TOTAL declarations directly containing sorryAx: {total}"
