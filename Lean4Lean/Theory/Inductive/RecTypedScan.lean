/-
# `RecTypedScan`: a structural query over the compiled environment, for obligation (B)

Companion instrument to `Verify/Inductive/FlipPriceScan.lean`, restricted to the (B) corner and
kept under `Theory/` so that it can be imported by `RecTyped.lean` without breaking layering.
It exists because `docs/handoff-rectyped.md`'s ABSENCE claims must not rest on grep: this repo
has twice recorded a round whose conclusion was inverted because a source search missed a
theorem reaching the same conclusion under another name.

Nothing here proves anything.  It enumerates, with arities, every declaration whose TYPE
mentions the (B) conclusion (`recConstsR` together with `VConstant.WF`) and every declaration
whose type mentions the two moving entry families (`motiveTypeR`, `minorTypeR`), so that
"nobody has composed (B) down to `hargs`" is an environment fact.
-/
import Lean4Lean.Theory.Inductive.RestoreBridge
import Lean4Lean.Theory.Inductive.NestedTele
import Lean4Lean.Theory.Inductive.NestedOrdered
import Lean4Lean.Theory.Inductive.NestedKeys
import Lean4Lean.Theory.Inductive.ParamRedex
import Lean4Lean.Theory.Typing.ConstSubstNested

open Lean Elab Meta

private def constsOfType (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

private def arity (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => 1 + arity b
  | _ => 0

run_cmd do
  let env ← getEnv
  let mut hitsB : Array (Name × Nat) := #[]
  let mut hitsMot : Array (Name × Nat) := #[]
  let mut hitsMin : Array (Name × Nat) := #[]
  let mut hitsHargs : Array (Name × Nat) := #[]
  let mut hitsOrd : Array (Name × Nat) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    let cs := constsOfType ci.type
    let has (m : Name) := cs.contains m
    if has ``Lean4Lean.VInductDecl'.recConstsR && has ``Lean4Lean.VConstant.WF then
      hitsB := hitsB.push (n, arity ci.type)
    if has ``Lean4Lean.VInductDecl'.motiveTypeR then
      hitsMot := hitsMot.push (n, arity ci.type)
    if has ``Lean4Lean.VInductDecl'.minorTypeR then
      hitsMin := hitsMin.push (n, arity ci.type)
    if has ``Lean4Lean.VIndRestore.IotaHargs then
      hitsHargs := hitsHargs.push (n, arity ci.type)
    if has ``Lean4Lean.VEnv.addInductR && has ``Lean4Lean.VEnv.Ordered then
      hitsOrd := hitsOrd.push (n, arity ci.type)
  logInfo m!"=== (B)'s conclusion: recConstsR + VConstant.WF ({hitsB.size}) ==="
  for (n, a) in hitsB do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== type mentions motiveTypeR ({hitsMot.size}) ==="
  for (n, a) in hitsMot do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== type mentions minorTypeR ({hitsMin.size}) ==="
  for (n, a) in hitsMin do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== type mentions IotaHargs -- (C)'s bundle, for comparison ({hitsHargs.size}) ==="
  for (n, a) in hitsHargs do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== addInductR AND Ordered -- FlipPriceScan's query, over a LARGER environment: it \
does not import ParamRedex.lean ({hitsOrd.size}) ==="
  for (n, a) in hitsOrd do logInfo m!"  {n}   arity {a}"
