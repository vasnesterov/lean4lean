/-
Which of `VEnv.IsDefEqU.weakN_iff`'s transitive users need the **conversion** half of it,
and which need only the **typing** half?

Why this exists. `Theory/Typing/Strengthen.lean` §7/§9 and
`Theory/Typing/StrengthenNarrow.lean` §3 split the hole at
`Theory/Typing/UniqueTyping.lean:174` into two independent statements:

  * `TypingStrengthening` (equivalently `PiDescend`) -- shape descent, no `trans` case; and
  * `TransStrengtheningNarrow` -- the `trans` case with a middle term that genuinely mentions
    a stripped variable.

`StrengthenNarrow.lean` §5 proves that nine of `UniqueTyping.lean`'s downstream wrappers --
`HasType.weakN_iff`, `IsType.weakN_iff`, `VExpr.WF.weakN_iff`, `OnCtx.weakN_inv`,
`OnCtx.weak'_inv`, `HasType.weak'_iff`, `IsType.weak'_iff`, `VExpr.WF.weak'_iff` and
`HasType.skips` -- follow from `TypingStrengthening` **alone**.  So a proof of the typing half
would unblock every user that reaches the hole only through those nine.

This script measures that set.  It walks the reverse dependency graph twice: once normally
(the hole's transitive users, matching `scripts/sorry-census.lean`), and once with the nine
gates treated as leaves that do not propagate reachability.  The difference is the population
that shape descent alone would free.

Run:  lake env lean scripts/weakn-gate-split.lean

It imports `Experimental.ConeJoin` for the same reason the census does: a module outside that
closure is invisible here and would be silently counted as zero.
-/
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
import Lean4Lean.Theory.Typing.StrengthenNarrow
open Lean Elab Command

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

/-- The nine wrappers proved from `TypingStrengthening` alone in
`Theory/Typing/StrengthenNarrow.lean` §5. -/
private def typingGates : List Name :=
  [``Lean4Lean.VEnv.HasType.weakN_iff,
   ``Lean4Lean.VEnv.IsType.weakN_iff,
   ``Lean4Lean.VExpr.WF.weakN_iff,
   ``Lean4Lean.OnCtx.weakN_inv,
   ``Lean4Lean.OnCtx.weak'_inv,
   ``Lean4Lean.VEnv.HasType.weak'_iff,
   ``Lean4Lean.VEnv.IsType.weak'_iff,
   ``Lean4Lean.VExpr.WF.weak'_iff,
   ``Lean4Lean.VEnv.HasType.skips]

/-- The wrappers that are genuine conversions, kept for the report. -/
private def convGates : List Name :=
  [``Lean4Lean.VEnv.IsDefEq.weakN_iff,
   ``Lean4Lean.VEnv.IsDefEq.weakN_iff',
   ``Lean4Lean.VEnv.IsDefEqU.weak'_iff,
   ``Lean4Lean.VEnv.IsDefEq.weak'_iff,
   ``Lean4Lean.VEnv.IsDefEq.skips]

run_cmd do
  let env ← getEnv
  let hole := ``Lean4Lean.VEnv.IsDefEqU.weakN_iff
  -- INTERNAL names are pass-through nodes in the graph; excluding them truncated every walk at
  -- an equation-compiler companion, and one (`NormalEq.trans._unary`) sits on a live path to
  -- this very hole.  See the long note in `scripts/sorry-census.lean`.  Fixed 2026-09-01.
  -- `names` (counted and printed) stays non-internal.
  let mut names : Array Name := #[]
  let mut graphNames : Array Name := #[]
  let mut direct : Std.HashMap Name NameSet := {}
  for (n, _) in env.constants.toList do
    unless (`Lean4Lean).isPrefixOf n do continue
    graphNames := graphNames.push n
    direct := direct.insert n (depsOf env n)
    unless n.isInternal do names := names.push n
  -- reverse reachability, optionally with a set of nodes that do not propagate
  let reach (cut : NameSet) : NameSet := Id.run do
    let mut hit : NameSet := ({} : NameSet).insert hole
    let mut changed := true
    while changed do
      changed := false
      for n in graphNames do
        if hit.contains n then continue
        if (direct.getD n {}).any fun d => hit.contains d && !cut.contains d then
          hit := hit.insert n
          changed := true
    -- report only non-internal reachers
    return names.foldl (fun acc n => if hit.contains n then acc.insert n else acc)
      (({} : NameSet).insert hole)
  let gateSet : NameSet := typingGates.foldl (fun s n => s.insert n) {}
  let all := reach {}
  let conv := reach gateSet
  logInfo s!"hole: {hole}"
  logInfo s!"  transitive users (all)                : {all.size - 1}"
  logInfo s!"  still reach it with the typing gates cut: {conv.size - 1}"
  logInfo s!"  freed by the typing half alone         : {all.size - conv.size}"
  logInfo "typing gates (provable from TypingStrengthening alone, StrengthenNarrow §5):"
  for g in typingGates do
    logInfo s!"    {g}  [in cone: {all.contains g}]"
  logInfo "conversion gates (need the narrow trans residual):"
  for g in convGates do
    let n := (reach (gateSet.insert g)).size
    logInfo s!"    {g}  [users lost if also cut: {conv.size - n}]"
