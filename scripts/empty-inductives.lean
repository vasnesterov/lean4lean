/-
Empty-inductive detector: the third instrument.

Why this exists.  The repo has two automated measurements of incompleteness and
both are blind to the same thing.

  * `scripts/sorry-census.lean` counts declarations whose value mentions
    `sorryAx`.  A hole that is *not* a `sorry` is invisible to it.
  * guard 3 in `Verify/Guard.lean` counts implementation markers (`partial`,
    `@[extern]`, `@[implemented_by]`) reachable from `addDecl`.  A hole in the
    *specification* is invisible to it.

An `inductive P ... : Prop` with **no constructors** is a hole of exactly that
invisible kind.  It elaborates, it is a perfectly good `Prop`, and every lemma
whose hypotheses mention it becomes VACUOUSLY TRUE.  Nothing goes red.  The
census stays flat.  Guard 3 stays flat.  Guard 2 can even reach
"proof COMPLETE" over a chain of such lemmas, having proved nothing at all.

This is not hypothetical.  `Lean4Lean.AddInduct` (`Verify/Environment/Basic.lean`)
is declared with no constructors and a `-- TODO`, and it is the root cause of
every entry in `docs/vacuity-ledger.md`.  It went unmeasured for the whole
project because no instrument was looking.

What is reported, for each empty inductive in the `Lean4Lean` namespace:

  * `reach` — how many loaded declarations mention it DIRECTLY in their own type
    or value.  Direct mention is the right measure here: a statement is vacuous
    when its OWN hypotheses name the empty `Prop`, so each of these is a
    candidate vacuous statement to be accounted for in the ledger.
  * whether it is a `Prop` (the dangerous case; an empty *data* type is usually
    deliberate, e.g. `Empty`).

An empty inductive is not automatically wrong — `False` is empty on purpose, and
so is a deliberately-uninhabited index type.  The point of the instrument is
that the tree should contain no empty inductive that anyone *believes* is
inhabited.  Every entry this prints must be accounted for in the ledger.

Run:  ~/.elan/bin/lake env lean scripts/empty-inductives.lean
-/
import Lean4Lean.Experimental.ConeJoin

open Lean

/-- Constants named by a declaration's type and value (same walker as `hole-cone.lean`). -/
def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

def isOurs (n : Name) : Bool :=
  (`Lean4Lean).isPrefixOf n && !n.isInternal

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Experimental.ConeJoin}] {}
  -- collect the empty inductives
  let mut empties : Array (Name × Bool) := #[]
  for (n, ci) in env.constants.toList do
    if isOurs n then
      match ci with
      | .inductInfo iv =>
        if iv.ctors.isEmpty then
          let isProp := (← do pure (iv.type.getForallBody == .sort .zero))
          empties := empties.push (n, isProp)
      | _ => pure ()
  if empties.isEmpty then
    IO.println "empty-inductives: none in the Lean4Lean namespace"
    return
  -- one pass over the environment, counting who mentions each
  let names := empties.map (·.1)
  let mut reach : Std.HashMap Name Nat := {}
  for n in names do reach := reach.insert n 0
  for (_, ci) in env.constants.toList do
    let d := deps ci
    for n in names do
      if d.contains n then
        reach := reach.insert n ((reach.getD n 0) + 1)
  IO.println s!"empty-inductives: {empties.size} in the Lean4Lean namespace"
  IO.println "  (an empty `Prop` makes every hypothesis mentioning it vacuous)"
  let sorted := empties.qsort fun a b => reach.getD a.1 0 > reach.getD b.1 0
  for (n, isProp) in sorted do
    let kind := if isProp then "Prop  <-- VACUITY SOURCE" else "data"
    IO.println s!"  {n}: reach {reach.getD n 0}, {kind}"

#eval! main
