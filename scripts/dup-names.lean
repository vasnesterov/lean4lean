/-
Duplicate-declaration check across the whole package.

Why this exists. Two modules can each declare the same name and both compile:
`lake build` never imports them together, so nothing complains. The pair is then
**un-importable** — any file needing both fails with "environment already
contains …", and it surfaces at the worst moment, usually when a measurement
script or a bridging proof first needs the two halves in one place.

This has happened three times here:
  * `VEnv.addDefEqs_le` and four siblings, walling `Theory/Typing/PatternRules`
    off from all of `Verify/` — nothing proved through one could reach the other
    (fixed, `3e13a0f`);
  * `VEnv.PropUniq` / `VEnv.PropTypeAgree`, declared twice with DIFFERENT
    statements, making any name-based claim spanning the two trees ambiguous;
  * `VEnv.addDefEqList_defeqs_inv` and `addIndRules_defeqs_inv` (fixed, `5259ae6`).

Run:  lake env lean scripts/dup-names.lean

It imports `Experimental.ConeJoin`, which pulls both the Theory and Verify cones
into one environment — so a collision between those two halves shows up as an
import error here rather than as a silent wall. Names reported below are ones
declared in more than one *source module* within that closure.
-/
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut seen : Std.HashMap Name (Array Name) := {}
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    let m := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames.getD i.toNat default)
      | none => `_current
    seen := seen.insert n ((seen.getD n #[]).push m)
  let mut dups := 0
  for (n, ms) in seen.toList do
    if ms.size > 1 then
      dups := dups + 1
      logInfo s!"DUPLICATE {n}\n    in {ms.toList}"
  if dups == 0 then
    logInfo "no duplicate Lean4Lean declarations across the joined cone"
  else
    logInfo s!"{dups} duplicated name(s) -- each makes its two modules un-importable together"
