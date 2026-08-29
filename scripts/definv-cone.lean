import Lean4Lean.Theory.Typing.AppCase
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.ConstInvWitness
import Lean4Lean.Theory.Typing.CycleConv
import Lean4Lean.Theory.Typing.DeclRules
import Lean4Lean.Theory.Typing.DefInvRefute
import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.HeadReduction
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.LogRelRowZero
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.PatternDecode
import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Theory.Typing.PropConv
import Lean4Lean.Theory.Typing.PropShadow
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.RawDefEq
import Lean4Lean.Theory.Typing.RegPiSat
import Lean4Lean.Theory.Typing.ShapeSpine
import Lean4Lean.Theory.Typing.SortUniqFacts
import Lean4Lean.Theory.Typing.Strengthen
import Lean4Lean.Theory.Typing.SubstTRefute
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.UnivDiscrim
import Lean4Lean.Theory.Typing.SortClauses

/-!
# `DefInv` vacuity cone

Reverse-dependency measurement seeded at `Lean4Lean.VEnv.DefInv` and at each of its three
field projections.  Run from the repo root:

    ~/.elan/bin/lake env lean scripts/definv-cone.lean

Same scan trap as `scripts/cone-measure.lean`: `ConstantInfo.value?` returns `none` for
`.thmInfo` unless `allowOpaque := true`, so the sweep would report an empty cone otherwise.
-/

open Lean

def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

structure Graph where
  fwd : Std.HashMap Name (Array Name)
  rev : Std.HashMap Name (Array Name)

def buildGraph (env : Environment) (inScope : Name → Bool) : Graph := Id.run do
  let mut fwd : Std.HashMap Name (Array Name) := {}
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    unless inScope n do continue
    let ds := (deps ci).toList.toArray
    fwd := fwd.insert n ds
    for d in ds do rev := rev.insert d ((rev.getD d #[]).push n)
  return ⟨fwd, rev⟩

def transUsers (g : Graph) (seed : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [seed]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      for u in g.rev.getD n #[] do
        unless seen.contains u do seen := seen.insert u; stack := u :: stack
  return seen

def modOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def sortNames (s : List Name) : Array Name := s.toArray.qsort (·.toString < ·.toString)

open Lean4Lean VEnv in
#eval show CoreM Unit from do
  let env ← getEnv
  let inScope : Name → Bool := fun n =>
    (`Lean4Lean).isPrefixOf n && !(`Lean4Lean.Experimental).isPrefixOf n
  let g := buildGraph env inScope
  IO.println s!"=== {g.fwd.size} Lean4Lean source declarations in scope"
  let seeds : List Name :=
    [``DefInv, ``DefInv.sort, ``DefInv.forallE, ``DefInv.sort_forallE, ``DefInv.zero,
     ``SortInvN, ``SortForallEDisjN, ``ForallEInvN]
  let mut cones : Std.HashMap Name NameSet := {}
  for s in seeds do
    let t := transUsers g s
    cones := cones.insert s t
    IO.println s!"\n--- transitive users of {s}: {t.toList.length}"
  -- the interesting classification: users of DefInv, split by whether the *transitive*
  -- cone reaches clause (2)'s projection.
  let dAll := cones.getD ``DefInv {}
  IO.println "\n=== every transitive user of `DefInv` whose TYPE mentions it"
  IO.println "    columns: 1 = reaches DefInv.sort, 2 = DefInv.forallE, 3 = DefInv.sort_forallE"
  IO.println "    R = reaches DefInv.rec/.casesOn (destructs all three)"
  let close (seed : Name) : NameSet := (cones.getD seed {}).insert seed
  let c1 := close ``DefInv.sort
  let c2 := close ``DefInv.forallE
  let c3 := close ``DefInv.sort_forallE
  let cR := (close ``DefInv.rec).union (close ``DefInv.casesOn)
  for n in sortNames dAll.toList do
    let ci := (env.find? n).get!
    unless ci.type.getUsedConstantsAsSet.contains ``DefInv do continue
    let ds := (deps ci).toList
    let hit (c : NameSet) := ds.any (fun d => c.contains d)
    let tag := (if hit c1 then "1" else "-") ++ (if hit c2 then "2" else "-")
      ++ (if hit c3 then "3" else "-") ++ (if hit cR then "R" else "-")
    let m := (modOf env n).getD Name.anonymous
    IO.println s!"  [{tag}] {n}   ({m})"
