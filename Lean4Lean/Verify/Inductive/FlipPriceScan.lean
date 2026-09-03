/-
# `FlipPriceScan`: a structural query over the compiled environment

`docs/handoff-flipprice.md`'s ABSENCE claims rest on this file, not on grep.  A source-text
search for `addInductR_ordered` cannot see a theorem that reaches the same conclusion under
another name, and this repo has twice recorded a round whose conclusion was inverted because a
grep missed one.  So the question "is `Ordered` after a nested step already available in
general, without the three obligations?" is asked here of the *environment*: every declaration
whose TYPE mentions both `VEnv.addInductR` and `VEnv.Ordered` is enumerated with its arity, so
a general result cannot hide behind a name.
-/
-- 2026-09-03: `ParamRedex` added after blocker (B)'s stream found this scan's population
-- INCOMPLETE.  Without it the scan reported "exactly five declarations mention both
-- `VEnv.addInductR` and `VEnv.Ordered`, and the only arity-0 ones are the two witnesses"; with it
-- the counts are SIX and THREE.  The third is `MRedex.MPWit.mpAuxB_addInductR_ordered`, arity 0,
-- at a **non-canonical parameterised** block -- so there are two independent end-to-end
-- parameterised confirmations, not one, and `mpAuxB_hdata` (arity 9) is an `IotaHargs` at a
-- parameterised block, which `docs/handoff-flipprice.md` §5b records as having no witness.
--
-- This is the fixed-import-list failure of `scripts/sorry-census.lean` (ledger rows 175, 187)
-- recurring one level down, in the very instrument the briefs point streams at for ABSENCE
-- claims.  A structural query over the compiled environment is only as complete as the modules
-- imported into it, and nothing in the query itself reveals the gap.
import Lean4Lean.Theory.Inductive.ParamRedex
import Lean4Lean.Theory.Inductive.RestoreBridge
import Lean4Lean.Theory.Inductive.NestedTele
import Lean4Lean.Theory.Inductive.NestedOrdered
import Lean4Lean.Theory.Inductive.NestedKeys
import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Typing.PatternRules

open Lean Elab Meta

/-- Names mentioned in a type. -/
private def constsOfType (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

private def arity (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => 1 + arity b
  | _ => 0

run_cmd do
  let env ← getEnv
  let mut hitsOrdered : Array (Name × Nat) := #[]
  let mut hitsRS : Array (Name × Nat) := #[]
  let mut hitsCtorCR : Array (Name × Nat) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    let cs := constsOfType ci.type
    let has (m : Name) := cs.contains m
    if has ``Lean4Lean.VEnv.addInductR && has ``Lean4Lean.VEnv.Ordered then
      hitsOrdered := hitsOrdered.push (n, arity ci.type)
    if has ``Lean4Lean.VInductDecl'.iotaRulesRS then
      hitsRS := hitsRS.push (n, arity ci.type)
    if has ``Lean4Lean.VInductDecl'.ctorConstsCR && has ``Lean4Lean.VConstant.WF then
      hitsCtorCR := hitsCtorCR.push (n, arity ci.type)
  logInfo m!"=== type mentions BOTH VEnv.addInductR and VEnv.Ordered ({hitsOrdered.size}) ==="
  for (n, a) in hitsOrdered do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== type mentions iotaRulesRS ({hitsRS.size}) ==="
  for (n, a) in hitsRS do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== type mentions ctorConstsCR and VConstant.WF ({hitsCtorCR.size}) ==="
  for (n, a) in hitsCtorCR do logInfo m!"  {n}   arity {a}"
