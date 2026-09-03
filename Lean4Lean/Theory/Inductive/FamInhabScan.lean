/-
# `FamInhabScan`: the conclusion-shape query behind this round's ABSENCE claim

`docs/handoff-faminhab.md` claims that before `Theory/Inductive/FamInhabNTree.lean` **no
declaration in the tree inhabited any of obligation (B)'s four data families at a block with
`D.np > 0`** — that is, that `docs/handoff-rectyped.md` §3b and `docs/handoff-htele.md` §4b were
accurate when written.  `scripts/exists.lean` can only say `NOT FOUND` for a *name*; this file is
the shape query the standing rules require alongside it.

It enumerates every `Lean4Lean` declaration whose TYPE mentions each of the four families, with
arities, so that "the only hypothesis-free inhabitations are `FamInhab*`'s" is an environment fact
rather than a grep.

**Import list, stated because a scan is only as complete as its population** (the failure
`docs/handoff-rectyped.md` §5 item 1 records): this file imports `FamInhabC.lean`, which imports
`FamInhabNTree.lean` → `RecTyped.lean` and `HTeleRecB.lean` → `HTeleGen.lean` → `HTeleNTree.lean`
→ `OwnRule.lean`, plus `ParamRedex.lean` and `IotaWit.lean` for the second parameterised block
(`MRedex.MPWit`), which is where a competing witness would live if there were one.  Every module
that mentions any of the four families is therefore in the population; the families are *defined*
in `RecTyped.lean`, so any user of them is downstream of it and cannot escape a scan rooted here
unless it is in a module this one does not reach — hence `ParamRedex`/`IotaWit` are named
explicitly.

Nothing here proves anything.
-/
import Lean4Lean.Theory.Inductive.FamInhabC
import Lean4Lean.Theory.Inductive.ParamRedex
import Lean4Lean.Theory.Inductive.IotaWit

open Lean Elab Meta

private def constsOfType (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

private def arity (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => 1 + arity b
  | _ => 0

run_cmd do
  let env ← getEnv
  let fams : Array Name :=
    #[``Lean4Lean.VIndRestore.MotiveHargs, ``Lean4Lean.VIndRestore.MinorFldDefEq,
      ``Lean4Lean.VIndRestore.MinorCtorHargs, ``Lean4Lean.VIndRestore.RecBodyHargs]
  for fam in fams do
    let mut hits : Array (Name × Nat) := #[]
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      unless (`Lean4Lean).isPrefixOf n do continue
      if (constsOfType ci.type).contains fam then
        hits := hits.push (n, arity ci.type)
    logInfo m!"=== type mentions {fam} ({hits.size}) ==="
    for (n, a) in hits.qsort (fun a b => a.1.toString < b.1.toString) do
      logInfo m!"  {n}   arity {a}"
