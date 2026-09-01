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
in the environment; importing only one silently under-reports.

It also reports each hole's **transitive user count** across `Lean4Lean.*`. That
number reorders the work: on 2026-08-30 a reverse-cone measurement found four of
`Injectivity.lean`'s six holes had **zero** users while `weakN_iff` had 169 --
the file had been treated as six equally-weighted obstructions. A hole with 0
transitive users blocks nothing that exists today. Internal names
are skipped (they mirror their parents), and theorem values are read by an
explicit match because `ConstantInfo.value?` returns `none` for `.thmInfo` --
the scan trap that silently reports a cone of size 0.
-/
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
open Lean Elab Command

/-- Transitive constants of a declaration, theorem values read explicitly. -/
private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs

run_cmd do
  let env ← getEnv
  -- pass 1: the holes
  let mut holes : Array Name := #[]
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    let hasSorry := match ci with
      | .thmInfo v => v.value.hasSorry
      | _ => match ci.value? (allowOpaque := true) with
             | some v => v.hasSorry
             | none => false
    if hasSorry then
      holes := holes.push n
      let m := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames.getD i.toNat default)
        | none => `_current
      byMod := byMod.insert m ((byMod.getD m #[]).push n)
  -- pass 2: transitive reverse reachability, by fixpoint over direct deps
  -- reaches n = set of Lean4Lean decls whose transitive deps include n
  -- The graph must include INTERNAL names as pass-through nodes.  Excluding them was a real
  -- bug: a declaration compiled by well-founded recursion routes its recursive calls through
  -- an internal companion (`NormalEq.trans._unary`), so that node got no outgoing edges and
  -- every walk truncated there.  One such companion sits on a live path --
  -- `NormalEq.trans -> ._unary -> NormalEq.weakN_iff -> weakN_inv_DFC -> IsDefEqU.weakN_iff` --
  -- and `NormalEq.weakN_iff`'s ONLY user is that companion, so `NormalEq.trans` was scored as
  -- not reaching the hole while `#print axioms` on it reports `sorryAx`.  Measured effect on
  -- `IsDefEqU.weakN_iff`: 211 users become 293.  Fixed 2026-09-01; the same bug was fixed in
  -- `scripts/hole-rank.lean` earlier and this script was not checked at the time.
  -- `names` (what is counted and printed) stays non-internal.
  let mut direct : Std.HashMap Name NameSet := {}
  let mut names : Array Name := #[]
  let mut graphNames : Array Name := #[]
  for (n, _) in env.constants.toList do
    unless (`Lean4Lean).isPrefixOf n do continue
    graphNames := graphNames.push n
    direct := direct.insert n (depsOf env n)
    unless n.isInternal do names := names.push n
  let mut users : Std.HashMap Name Nat := {}
  for h in holes do
    -- BFS backwards: repeatedly add any decl whose deps meet the frontier
    let mut hit : NameSet := ({} : NameSet).insert h
    let mut changed := true
    while changed do
      changed := false
      for n in graphNames do
        if hit.contains n then continue
        let ds := direct.getD n {}
        if ds.any (fun d => hit.contains d) then
          hit := hit.insert n
          changed := true
    -- count only non-internal reachers
    let mut cnt := 0
    for n in names do
      if n != h && hit.contains n then cnt := cnt + 1
    users := users.insert h cnt
  -- report
  let mut total := 0
  for (m, ns) in byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    total := total + ns.size
    logInfo s!"{m}: {ns.size}"
    for n in ns do
      logInfo s!"    {n}   [{users.getD n 0} transitive users]"
  logInfo s!"TOTAL declarations directly containing sorryAx: {total}"
  logInfo "A hole with 0 transitive users blocks nothing that exists today."
