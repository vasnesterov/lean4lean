/-
# `exists.lean` — does this declaration exist, and what does it cost?

**Why this exists.** The orchestrator's briefs asserted six times in two days that something
was absent, unproved, or needed, when it was already in the tree — twice contradicted by prose
in a file committed hours earlier, once by a docstring naming the very thing as present, once
by a lemma pair that was already proved with bodies. Every brief tells streams to make absence
claims against the *compiled environment* rather than by grep. This is the orchestrator doing
the same thing before writing the claim down.

Run:  lake env lean --run scripts/exists.lean Name.One Name.Two …
  or: NAMES="a b c" lake env lean --run scripts/exists.lean

For each name it reports: found or NOT FOUND, arity, whether the value is a `sorry` hole,
whether the axiom set is tainted, and the axiom set itself. `NOT FOUND` is the only output that
licenses the word "absent" in a brief — and even then, a *different name* for the same content
is the failure mode that has actually bitten, so pair this with a conclusion-shape query
(`Verify/Inductive/FlipPriceScan.lean` is the template) when the claim is "nothing proves X".

**Population caveat, learned the hard way.** A structural query is only as complete as the
modules imported into it, and nothing in its output reveals a gap — a scan here once reported
five declarations where there were six because it omitted one import. This script imports the
whole default-target population via the same filesystem walk as `sorry-census-all.lean`, so the
population is the build's, not a hand-maintained list.
-/
import Lean
open Lean

private def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

private partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then cone env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some ci => cone env ((deps ci).toList ++ rest) seen
    | none => cone env rest seen

private def arity : Expr → Nat
  | .forallE _ _ b _ => 1 + arity b
  | _ => 0

partial def walk (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if (← e.path.isDir) then out := out ++ (← walk e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  return out

def toModule (p : System.FilePath) : Option Name := do
  let s : String := p.toString
  guard (s.endsWith ".lean")
  let s : String := s.dropEnd 5 |>.toString
  let parts : List String := s.splitOn "/"
  guard (parts.head? == some "Lean4Lean")
  return parts.foldl (fun acc c => Name.mkStr acc c) Name.anonymous

def main (argv : List String) : IO Unit := do
  let envNames := (← IO.getEnv "NAMES").getD ""
  let names := if argv.isEmpty then envNames.splitOn " " else argv
  let names := names.filter (· != "")
  if names.isEmpty then
    IO.println "usage: lake env lean --run scripts/exists.lean Name.One Name.Two …"
    return
  initSearchPath (← findSysroot)
  let files ← walk ("Lean4Lean" : System.FilePath)
  let onDisk := (files.filterMap toModule) ++ #[`Lean4Lean]
  let oleanOf (m : Name) : System.FilePath :=
    (m.components.foldl (fun (acc : System.FilePath) c => acc / c.toString)
      (".lake/build/lib/lean" : System.FilePath)).withExtension "olean"
  -- default-target population only; `Experimental` is not in `defaultTargets`
  let cand := onDisk.filter (fun m => !(`Lean4Lean.Experimental).isPrefixOf m)
  let mut built := #[]
  for m in cand do if ← (oleanOf m).pathExists then built := built.push m
  -- Drop `Replay` AND EVERYTHING THAT IMPORTS IT: it collides with a dependency's `ImportGraph`
  -- on `Environment.importsOf`, so importing any of its reverse closure throws.  Dropping only
  -- the module itself is not enough -- a transitive importer pulls it back in, which is how the
  -- first version of this script failed.
  let importsOfFile (m : Name) : IO (Array Name) := do
    let path := (m.components.foldl
      (fun (acc : System.FilePath) c => acc / c.toString) ("." : System.FilePath)).withExtension "lean"
    if !(← path.pathExists) then return #[]
    let txt ← IO.FS.readFile path
    let mut out := #[]
    for line in txt.splitOn "\n" do
      let line := line.trim
      if line.startsWith "import " then
        let rest := (line.drop 7).trim.toString
        let nm := (rest.splitOn " ").headD rest
        if nm.startsWith "Lean4Lean" then
          out := out.push (nm.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous)
    return out
  let mut imps : Std.HashMap Name (Array Name) := {}
  for m in built do imps := imps.insert m (← importsOfFile m)
  let mut bad : NameSet := (∅ : NameSet).insert `Lean4Lean.Replay
  let mut grew := true
  while grew do
    grew := false
    for m in built do
      unless bad.contains m do
        if (imps.getD m #[]).any (bad.contains ·) then bad := bad.insert m; grew := true
  let mods := built.filter (!bad.contains ·)
  let env ← importModules (mods.map fun m => {module := m}) {}
  IO.println s!"population: {mods.size} built modules\n"
  for s in names do
    let n := s.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    match env.find? n with
    | none => IO.println s!"NOT FOUND   {s}\n            (before writing \"absent\", also query by conclusion shape — a different name for the same content is the failure mode that bites)"
    | some ci =>
      let m := match env.getModuleIdxFor? n with
        | some i => toString env.header.moduleNames[i.toNat]!
        | none => "?"
      let hasBody := (ci.value? (allowOpaque := true)).isSome
      let isHole := match ci.value? (allowOpaque := true) with
        | some v => v.hasSorry | none => false
      -- A declaration with no proof term (structure, inductive, axiom, opaque) has a cone
      -- consisting of its TYPE's constants only.  That number says nothing about how hard the
      -- statement is to satisfy, and I once read `cone 5` on a `structure` as evidence a route
      -- was short -- the predicate turned out to be FALSE at every witness on that path.  The
      -- price of such a thing lives in its witnesses, never in its definition.
      let kindNote :=
        if hasBody then "" else
          "  [NO PROOF TERM: cone is type-constants only; it says NOTHING about satisfiability -- price the witnesses]"
      let c := cone env [n] {}
      let tainted := c.contains ``sorryAx
      IO.println s!"FOUND       {s}"
      IO.println s!"            module {m}, arity {arity ci.type}, cone {c.size}{kindNote}"
      IO.println s!"            own value is a hole: {isHole}; cone reaches sorryAx: {tainted}"
      if tainted then
        let holes := c.toList.filter fun h =>
          h != ``sorryAx && (match env.find? h with
            | some hi => (deps hi).contains ``sorryAx | none => false)
        IO.println s!"            holes in cone: {holes}"
