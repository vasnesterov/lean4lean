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
  IO.println s!"population: {mods.size} built modules"
  -- WATCHED DECLARATIONS.  `sorryAx` reachability is NOT enough to police a ban: several
  -- statements this project forbids are themselves `sorryAx`-free, so a cone can route straight
  -- through one and still report "hole-free".  `AxiomConservativityWF` is the case that exposed
  -- it -- a `Prop` definition with a clean cone.  Every "hole-free, therefore clean" verdict I
  -- issued before this was enforced by stream honesty rather than by measurement.
  let watchStr := (← IO.getEnv "WATCH").getD (String.intercalate " " [
    "Lean4Lean.VEnv.HasArgs.of_mkApp", "Lean4Lean.VEnv.IsDefEq.uniq",
    "Lean4Lean.VEnv.IsDefEq.uniqU", "Lean4Lean.VEnv.AxiomConservativityWF",
    "Lean4Lean.VEnv.StrengtheningTarget", "Lean4Lean.VEnv.SortWitness"])
  let watch := (watchStr.splitOn " ").filter (· != "") |>.map fun w =>
    w.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
  let (watchOk, watchBad) := watch.partition env.contains
  if !watchBad.isEmpty then
    IO.println s!"WATCH NAMES THAT DO NOT RESOLVE (they can never be reported): {watchBad}"
  IO.println s!"watching {watchOk.length} declarations for cone membership\n"
  let coneIn : Option String := match (← IO.getEnv "CONE_IN") with
    | some v => if v.trim.isEmpty then none else some v.trim
    | none => none
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
      let hits := watchOk.filter c.contains
      if hits.isEmpty then
        IO.println s!"            watched declarations in cone: none of {watchOk.length}"
      else
        IO.println s!"            *** WATCHED IN CONE: {hits} ***"
        IO.println s!"            (these are forbidden or load-bearing by policy, NOT holes --"
        IO.println s!"             a clean sorryAx line does not clear them)"
      -- CONE MEMBERS, restricted to one module.  Added 2026-09-04 because the absence of this
      -- hid `Lean4Lean.TrProj.instN` from FOUR successive rounds attacking census hole #1.  That
      -- lemma substitutes a whole `TrProj` derivation and lives in the hole's OWN module; the
      -- rounds instead ran the move on the major premise's type only, which forced them to discard
      -- two `HasArgs` fields and rebuild them via `VEnv.HasArgs.of_mkApp` -- and THAT is where
      -- three census holes and three watched names entered.  Routing through `instN` discards
      -- nothing and the route is hole-free (3412/0/0 against 3698/3/3).
      --
      -- The question none of my instruments could answer was "which of my dependencies are already
      -- declared next door?"  Cone SIZE cannot answer it and neither can a name search, because you
      -- have to know the name to search for it.  `CONE_IN=<module>` answers it directly: it lists
      -- the cone members declared in that module, which is the set of tools a proof in that file
      -- may reach for without adding an import.
      --
      --   CONE_IN="Lean4Lean.Verify.Typing.Lemmas" NAMES="…" lake env lean --run scripts/exists.lean
      --
      -- Pass CONE_IN=SELF for the target's own module, which is the common case: "what is already
      -- in the file holding the hole I am attacking?"
      match coneIn with
      | none => pure ()
      | some want =>
        let target := if want == "SELF" then m else want
        let modOf := fun (d : Name) => match env.getModuleIdxFor? d with
          | some i => toString env.header.moduleNames[i.toNat]!
          | none => "?"
        let local' := c.toList.filter fun d => modOf d == target && d != n
        if local'.isEmpty then
          IO.println s!"            cone ∩ {target}: none"
        else
          IO.println s!"            cone ∩ {target} ({local'.length}) -- reachable with no new import:"
          for d in local'.toArray.qsort (·.toString < ·.toString) do
            IO.println s!"              {d}"
