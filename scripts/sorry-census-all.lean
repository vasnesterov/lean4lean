/-
The hole census over **every** built module, not a fixed import closure.

Why this exists.  `scripts/sorry-census.lean` imports `Lean4Lean.Verify.Guard` +
`Lean4Lean.Experimental.ConeJoin` -- a *fixed* list -- and therefore measures only
what those two reach.  On 2026-09-03 a stream landed
`Verify/Typing/ProjGenTerm.lean` (782 lines, the wall-2 proof) and
`Verify/TypeChecker/ProjGenTermWitness.lean`.  Both build, via the
`Lean4Lean.Verify.*` glob in `lakefile.toml`.  **Nothing imports either** except
the witness importing the proof, and nothing imports the witness -- so both were
invisible to `sorry-census.lean`, to `scripts/cone-measure.lean`, and to
`Experimental/ConeJoin.lean`, all three of which are fixed-import-list
instruments.  Nothing was at risk that day, because neither module holds a
`sorry`; the gap is that **a leaf carrying a hole would have been invisible to
every census in the repo while `lake build` stayed green.**  Vacuity-ledger row
174d records it as the tenth instrument blindness.

The fix is to take the population from the *filesystem*, exactly as the lakefile
globs do, rather than from an import list a human maintains.  This script walks
`Lean4Lean/` for `.lean` files, converts each path to a module name, imports them
all, and reports every declaration whose VALUE contains `sorryAx`, plus which
modules are *orphans* (nothing else in the tree imports them) so the difference
between the two populations is itself visible.

Run:  lake env lean scripts/sorry-census-all.lean

Traps this script is written to avoid, all previously paid for in this repo:
* `ConstantInfo.value?` returns `none` for `.thmInfo` unless `allowOpaque := true`,
  which silently reports a cone of size 0 for anything used only in proofs.
* A `grep -c sorry` counts prose, docstrings and identifiers.  On 2026-08-29 that
  turned 21 holes into a reported 89.
* `Experimental` is globbed with `.+` (strictly below), the others with `.*`, so
  the root modules `Lean4Lean/Theory.lean` etc. are in-population and
  `Lean4Lean/Experimental.lean` -- if it exists -- is not.  Mirroring the lakefile
  matters: a population that differs from what `lake build` builds is a third
  population, not a fix.
-/
import Lean
open Lean

/-- Transitive constants of a declaration; theorem values read explicitly. -/
private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs

/-- Every `.lean` file under `dir`, recursively, as repo-relative paths. -/
partial def walk (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if (← e.path.isDir) then
      out := out ++ (← walk e.path)
    else if e.path.extension == some "lean" then
      out := out.push e.path
  return out

/-- `Lean4Lean/Verify/Typing/ProjGenTerm.lean` -> `Lean4Lean.Verify.Typing.ProjGenTerm`. -/
def toModule (p : System.FilePath) : Option Name := do
  let s := p.toString
  let s : String := if s.startsWith "./" then (s.drop 2).toString else s
  guard (s.endsWith ".lean")
  let s : String := s.dropEnd 5 |>.toString
  let parts : List String := s.splitOn "/"
  guard (parts.head? == some "Lean4Lean")
  return parts.foldl (fun acc c => Name.mkStr acc c) Name.anonymous

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let files ← walk ("Lean4Lean" : System.FilePath)
  let roots : Array Name := #[`Lean4Lean]
  let onDisk := (files.filterMap toModule) ++ roots
  -- A module is in the *built* population only if its `.olean` exists.  This is not
  -- a defensive nicety: `Lean4Lean.Experimental` is absent from `defaultTargets` in
  -- `lakefile.toml`, so `lake build` does not build any `Experimental/` module unless
  -- something in a default target imports it.  Those files are therefore invisible to
  -- *every* instrument in this repo, this one included, and the honest thing is to
  -- name them rather than to import-error on the first one.
  let oleanOf (m : Name) : System.FilePath :=
    (m.components.foldl (fun (acc : System.FilePath) c => acc / c.toString)
      (".lake/build/lib/lean" : System.FilePath)).withExtension "olean"
  -- `Lean4Lean.Experimental.*` is OUT of population, and this is the lakefile's own
  -- verdict, not a convenience: `defaultTargets` lists Lean4Lean, lean4lean,
  -- Lean4Lean.Theory, Lean4Lean.Verify, Lean4Lean.Tests -- and not Experimental.  So
  -- `lake build` does not build it, it is not part of the verified artifact, and a
  -- `sorry` there blocks nothing.  Measuring it would report a third population,
  -- larger than what `lake build` checks, which is a different error from the one
  -- this script fixes.
  let inPop (m : Name) : Bool := !(`Lean4Lean.Experimental).isPrefixOf m
  let cand := onDisk.filter inPop
  let expl := onDisk.filter (!inPop ·)
  let mut mods : Array Name := #[]
  let mut unbuilt : Array Name := #[]
  for m in cand do
    if ← (oleanOf m).pathExists then mods := mods.push m else unbuilt := unbuilt.push m
  IO.println s!"on disk: {onDisk.size}; in default-target population: {cand.size}; \
    Experimental (out of population, not in defaultTargets): {expl.size}"
  IO.println s!"BUILT: {mods.size}; in population but NOT BUILT: {unbuilt.size}"
  if unbuilt.size > 0 then
    IO.println "NOT BUILT -- in a default target, on disk, no .olean.  These are invisible to \
      every census in this repo, this one included, while `lake build` may still say green:"
    for u in unbuilt.qsort (·.toString < ·.toString) do
      IO.println s!"  {u}"
  -- TWO PASSES, and the reason is a fact about this tree that no document recorded:
  -- `Lean4Lean/Replay.lean:17` defines `Lean.Environment.importsOf`, and a dependency's
  -- `ImportGraph.Imports.ImportGraph` defines the same name.  Loading both into one
  -- environment throws `environment already contains ...`.  So **the whole tree cannot be
  -- imported at once**, and every existing census avoided this only by accident of which
  -- import list it happened to carry.  A whole-population census must therefore run in
  -- disjoint groups and union the results, which is what this does: group B is
  -- `Replay` and everything that (transitively, textually) imports it; group A is the rest.
  let importsOfFile (m : Name) : IO (Array Name) := do
    let path := (m.components.foldl
      (fun (acc : System.FilePath) c => acc / c.toString) ("." : System.FilePath)).withExtension "lean"
    if !(← path.pathExists) then return #[]
    let txt ← IO.FS.readFile path
    let mut out := #[]
    -- Scan the WHOLE file for `import` lines.  The previous version stopped at the first
    -- line beginning `/-`, `namespace` or `open`, which is WRONG in this repo: several modules
    -- carry a `/-! … -/` block *between* import lines, so every import after it was silently
    -- dropped and the resulting graph was a subgraph.  A concurrent stream found this while
    -- working around a crash of this script (2026-09-03).  Over-collecting is impossible in
    -- practice: `import` cannot begin a line except as a command.
    for line in txt.splitOn "\n" do
      let line := line.trim
      if line.startsWith "import " then
        -- keep only the module name; a trailing `-- …` note is common here
        let rest := (line.drop 7).trim.toString
        let nm := (rest.splitOn " ").headD rest
        if nm.startsWith "Lean4Lean" then
          out := out.push (nm.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous)
    return out
  let mut imps : Std.HashMap Name (Array Name) := {}
  for m in mods do imps := imps.insert m (← importsOfFile m)
  -- reverse-transitive closure of `Lean4Lean.Replay`
  let mut groupB : NameSet := (∅ : NameSet).insert `Lean4Lean.Replay
  let mut changed := true
  while changed do
    changed := false
    for m in mods do
      unless groupB.contains m do
        if (imps.getD m #[]).any (groupB.contains ·) then
          groupB := groupB.insert m; changed := true
  let gB := mods.filter (groupB.contains ·)
  let gA := mods.filter (!groupB.contains ·)
  -- Exclude the REVERSE closure of anything unbuilt.  Importing a module whose own import is
  -- missing throws, so a single broken module used to abort the whole census -- which is exactly
  -- when it is most wanted.  Reported by a stream on 2026-09-03 after `RecTyped.lean` broke.
  let unbuiltSet := unbuilt.foldl (fun (s : NameSet) m => s.insert m) {}
  let mut poisoned : NameSet := unbuiltSet
  let mut changed2 := true
  while changed2 do
    changed2 := false
    for m in mods do
      unless poisoned.contains m do
        if (imps.getD m #[]).any (poisoned.contains ·) then
          poisoned := poisoned.insert m; changed2 := true
  let gA := gA.filter (!poisoned.contains ·)
  let gB := gB.filter (!poisoned.contains ·)
  let skipped := poisoned.toList.length - unbuilt.size
  if skipped > 0 then
    IO.println s!"SKIPPED {skipped} module(s) importing something unbuilt -- census is over the \
      remainder, not the whole population.  Fix the unbuilt module and re-run."
  IO.println s!"pass A: {gA.size} modules; pass B (the `Replay` reverse closure): {gB.size}"

  -- The hole scan, run once per group.  `holesIn` returns the declarations whose own
  -- VALUE contains `sorryAx` directly -- the holes themselves, not their consumers.
  let holesIn (env : Environment) : Array (Name × Name) := Id.run do
    let mut out := #[]
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      unless (`Lean4Lean).isPrefixOf n do continue
      let hasSorry := match ci with
        | .thmInfo v => v.value.hasSorry
        | _ => match ci.value? (allowOpaque := true) with
               | some v => v.hasSorry
               | none => false
      if hasSorry && (depsOf env n).contains ``sorryAx then
        let m := match env.getModuleIdxFor? n with
          | some i => env.header.moduleNames[i.toNat]!
          | none => `«?»
        out := out.push (n, m)
    return out

  let envA ← importModules (gA.map fun m => {module := m}) {}
  let hA := holesIn envA
  -- pass 2's orphan report needs pass A's header, which carries the bulk of the tree
  let mut imported : NameSet := {}
  for mi in envA.header.moduleData do
    for i in mi.imports do
      imported := imported.insert i.module

  let envB ← importModules (gB.map fun m => {module := m}) {}
  let hB := holesIn envB
  for mi in envB.header.moduleData do
    for i in mi.imports do
      imported := imported.insert i.module

  -- union, so a hole visible in only one group is still counted
  let mut seen : NameSet := {}
  let mut all : Array (Name × Name) := #[]
  for (n, m) in hA ++ hB do
    unless seen.contains n do
      seen := seen.insert n; all := all.push (n, m)
  IO.println s!"\nHOLES over the WHOLE built population, unioned across both passes: {all.size}"
  IO.println s!"  (pass A found {hA.size}, pass B found {hB.size})"
  for (h, m) in all.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"  {h}   [{m}]"

  let orphans := mods.filter fun m => !imported.contains m && m != `Lean4Lean
  IO.println s!"\nORPHAN modules ({orphans.size}) -- in a default target, built, imported by nothing."
  IO.println "A fixed-import-list census cannot reach these at all; that is the blindness this"
  IO.println "script exists to remove.  A hole in one of them would block nothing TODAY, but it"
  IO.println "would also be invisible to every other instrument in the repo."
  for o in orphans.qsort (·.toString < ·.toString) do
    IO.println s!"  {o}"
