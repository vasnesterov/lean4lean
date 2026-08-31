/-
Standing hole-ranking instrument.

    ~/.elan/bin/lake env lean scripts/hole-rank.lean

Why this exists.  Prioritising a round means knowing which hole carries the most
weight, and that number ("131 users", "449 users") had been recomputed ad hoc
each time from throwaway scripts.  Two consequences, both of which have bitten:
a stale count outlives the tree it described, and an ad-hoc walker gets the
`allowOpaque` trap wrong and reports a clean cone for a tainted proof.

So: the holes are **discovered**, never listed.  A hole is any declaration whose
own type-or-value mentions `sorryAx` -- the same rule `scripts/sorry-census.lean`
uses -- so this file cannot disagree with the census, and adding or closing a
hole needs no edit here.

**The scan trap.**  `ConstantInfo.value?` returns `none` for `.thmInfo` unless
`allowOpaque := true` is passed.  Without it a dependency walk sees *types only*,
every theorem's cone reads clean, and a `sorry`-tainted proof measures
`sorry`-free.  `deps` below passes it; see `docs/audit-classes.md` incidental
finding 4 for the round this cost.

Columns:
* `users`      -- transitive reverse-reachable declarations (the blast radius).
* `sole`       -- users that reach *this* hole with every **other** hole cut.
  These are the ones closing this hole alone would free; `users - sole` is shared
  with at least one other hole, so the two numbers together say whether a hole is
  worth attacking on its own or only as part of a group.
* `cone`       -- other holes appearing in this hole's own forward cone.  A
  non-empty entry means this hole's would-be proof currently routes through
  another one, i.e. a dependency between holes, and a cycle here is why some
  routes are closed.
-/
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin

open Lean

/-- Constants referenced by `ci`, from its type *and* its value -- theorems included. -/
def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

def inScope (n : Name) : Bool := (`Lean4Lean).isPrefixOf n && !n.isInternal

/-- **Graph membership is deliberately wider than `inScope`.**

`inScope` excludes internal names, and using it to *build* the graph was a real bug: a
declaration compiled by well-founded recursion routes its recursive calls through an internal
companion (`NormalEq.trans._unary`), so that node got no outgoing edges and every walk truncated
there.  The instrument then reported `NormalEq.descend`'s cone as
`[forallE_inv_stratified, rigidShapeUniqNS]` while `IsDefEqU.weakN_iff` was in fact reachable in
seven hops through exactly such a companion — i.e. it printed "no cycle" at the one place a cycle
existed, and every `users`/`sole` count it produced was an undercount (`weakN_iff` 60 → 69,
`rigidShapeUniqNS` 136 → 139, `forallE_inv_stratified` 232 → 233 in the Guard+K closure).

So internal names are **pass-through nodes** in the graph, and `inScope` remains the filter on
what is *counted and printed*.  Found by the `descend` stream, 2026-08-31. -/
def inGraph (n : Name) : Bool := (`Lean4Lean).isPrefixOf n

structure Graph where
  rev : Std.HashMap Name (Array Name)
  fwd : Std.HashMap Name (Array Name)

def buildGraph (env : Environment) : Graph := Id.run do
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut fwd : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    unless inGraph n do continue
    let ds := (deps ci).toList.toArray
    fwd := fwd.insert n ds
    for d in ds do rev := rev.insert d ((rev.getD d #[]).push n)
  return ⟨rev, fwd⟩

/-- Transitive reverse-reachable set of `seed`, skipping anything in `cut`. -/
def transUsersCut (g : Graph) (seed : Name) (cut : NameSet) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [seed]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      for u in g.rev.getD n #[] do
        if cut.contains u then continue
        unless seen.contains u do seen := seen.insert u; stack := u :: stack
  return seen

/-- Forward cone of `seed`, restricted to `Lean4Lean` names. -/
def fwdCone (g : Graph) (seed : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [seed]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      for d in g.fwd.getD n #[] do stack := d :: stack
  return seen

open Elab Command in
run_cmd do
  let env ← getEnv
  -- Discover the holes: same rule as scripts/sorry-census.lean.
  let mut holes : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless inScope n do continue
    if (deps ci).contains ``sorryAx then holes := holes.push n
  let holeSet : NameSet := holes.foldl (·.insert ·) {}
  let g := buildGraph env
  let mut rows : Array (Nat × Nat × Name × List Name) := #[]
  let mut tainted : NameSet := {}
  for h in holes do
    let us := transUsersCut g h {}
    for u in us.toList do tainted := tainted.insert u
    let others : NameSet := holes.foldl (fun s x => if x == h then s else s.insert x) {}
    let sole := transUsersCut g h others
    let inCone := (fwdCone g h).toList.filter fun x => x != h && holeSet.contains x
    rows := rows.push (us.toList.length, sole.toList.length, h, inCone)
  let sorted := rows.qsort fun a b => a.1 > b.1
  let mut out := s!"{holes.size} holes, ranked by blast radius\n"
  out := out ++ s!"{"".pushn ' ' 6}users   sole  hole\n"
  for (u, s, n, c) in sorted do
    out := out ++ s!"      {u}\t{s}\t{n}"
    unless c.isEmpty do out := out ++ s!"\n              cone: {c}"
    out := out ++ "\n"
  out := out ++ s!"\nunion of all blast radii: {tainted.toList.length} declarations tainted"
  logInfo out
