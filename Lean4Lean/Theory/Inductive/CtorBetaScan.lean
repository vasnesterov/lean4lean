/-
# `CtorBetaScan`: a structural query over the compiled environment, for obligation (A)

This file *measures*; it proves nothing.  Its job is to make the ABSENCE claims of
`docs/handoff-ctorbeta.md` claims about the **compiled environment** rather than about grep:
the question "is there already a defeq-level bridge between `VIndRestore.restore` and
`VExpr.substC`, or a general parameterful obligation (A)?" is asked of every declaration whose
*type* mentions the relevant heads, so a theorem cannot hide behind an unexpected name.

Precedent for doing it this way: `Lean4Lean/Verify/Inductive/FlipPriceScan.lean`, and the two
occasions recorded in `docs/handoff-flipprice.md` §7 where a grep inverted a conclusion.
-/
import Lean4Lean.Theory.Inductive.IndexedNested
import Lean4Lean.Theory.Inductive.FieldsNoK
import Lean4Lean.Theory.Inductive.RestoreOpWit
import Lean4Lean.Theory.Inductive.RecArgIndep
import Lean4Lean.Theory.Inductive.NestedKeys
import Lean4Lean.Theory.Inductive.StructureEta
import Lean4Lean.Theory.Inductive.IotaGen
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.PatternRules

open Lean Elab Meta

private def constsOfType (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

private def arity (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => 1 + arity b
  | _ => 0

run_cmd do
  let env ← getEnv
  let mut q1 : Array (Name × Nat) := #[]   -- restore + IsDefEq
  let mut q2 : Array (Name × Nat) := #[]   -- restore + substC
  let mut q3 : Array (Name × Nat) := #[]   -- ctorConstsCR + VConstant.WF
  let mut q4 : Array (Name × Nat) := #[]   -- TeleDefEq + fieldTypesR
  let mut q5 : Array (Name × Nat) := #[]   -- typeR + (IsDefEq or TeleDefEq)
  let mut q6 : Array (Name × Nat) := #[]   -- restore, any
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    let cs := constsOfType ci.type
    let has (m : Name) := cs.contains m
    let a := arity ci.type
    if has ``Lean4Lean.VIndRestore.restore then
      q6 := q6.push (n, a)
      if has ``Lean4Lean.VEnv.IsDefEq || has ``Lean4Lean.VEnv.IsDefEqU
          || has ``Lean4Lean.VEnv.TeleDefEq then q1 := q1.push (n, a)
      if has ``Lean4Lean.VExpr.substC then q2 := q2.push (n, a)
    if has ``Lean4Lean.VInductDecl'.ctorConstsCR && has ``Lean4Lean.VConstant.WF then
      q3 := q3.push (n, a)
    if has ``Lean4Lean.VEnv.TeleDefEq && has ``Lean4Lean.VIndCtor.fieldTypesR then
      q4 := q4.push (n, a)
    if has ``Lean4Lean.VIndCtor.typeR
        && (has ``Lean4Lean.VEnv.IsDefEq || has ``Lean4Lean.VEnv.TeleDefEq
            || has ``Lean4Lean.VEnv.IsDefEqU) then
      q5 := q5.push (n, a)
  logInfo m!"=== Q1 restore + (IsDefEq|IsDefEqU|TeleDefEq) ({q1.size}) ==="
  for (n, a) in q1 do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== Q2 restore + substC ({q2.size}) ==="
  for (n, a) in q2 do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== Q3 ctorConstsCR + VConstant.WF ({q3.size}) ==="
  for (n, a) in q3 do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== Q4 TeleDefEq + fieldTypesR ({q4.size}) ==="
  for (n, a) in q4 do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== Q5 VIndCtor.typeR + defeq ({q5.size}) ==="
  for (n, a) in q5 do logInfo m!"  {n}   arity {a}"
  logInfo m!"=== Q6 mentions VIndRestore.restore, total {q6.size} ==="
