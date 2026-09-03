/-
# `users.lean` — how many declarations ACTUALLY depend on this one?

**Why this exists.** The prose in this repo describes one hole as a 534-, 736-, 714-, 449-,
515- and 468-user hole, in six different places, and another as 176- and 460-. Those cannot all
be right; they are mutually inconsistent by 1.6x. The direct reference counts are small (the two
injectivity holes have 2 and 3 uses), so every large figure is a *transitive* count that nobody
has recomputed since it was written. A stream asked for this instrument after two attempts at the
measurement exceeded its budget.

This walks the reverse dependency graph over the whole built population and reports, for each
name: direct dependants, transitive dependants, and how many files and modules they span. A
declaration counts as depending on X if X appears in its type or its value.

Run:  NAMES="Lean4Lean.VEnv.WF.rigidShapeUniqNS" lake env lean --run scripts/users.lean
  or: lake env lean --run scripts/users.lean Name.One Name.Two

Read the two numbers as different facts. **Direct** is how many places would break if you changed
the statement. **Transitive** is how much of the tree stands on it — and it is the number that
belongs in a sentence like "an N-user hole". Quoting a transitive figure as though it were direct,
or vice versa, is how the six inconsistent numbers happened.

Caveat kept from `exists.lean`: a structural query is only as complete as its population, and
nothing in the output reveals a gap. This imports the build's own default-target population.
-/
import Lean
open Lean

private def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

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
    IO.println "usage: NAMES=\"Lean4Lean.Some.Decl\" lake env lean --run scripts/users.lean"
    return
  initSearchPath (← findSysroot)
  let files ← walk ("Lean4Lean" : System.FilePath)
  let onDisk := (files.filterMap toModule) ++ #[`Lean4Lean]
  let oleanOf (m : Name) : System.FilePath :=
    (m.components.foldl (fun (acc : System.FilePath) c => acc / c.toString)
      (".lake/build/lib/lean" : System.FilePath)).withExtension "olean"
  let cand := onDisk.filter (fun m => !(`Lean4Lean.Experimental).isPrefixOf m)
  let mut built := #[]
  for m in cand do if ← (oleanOf m).pathExists then built := built.push m
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
  -- Reverse edges, restricted to dependants declared in OUR tree: a toolchain lemma that happens
  -- to mention one of our constants is not a user of it in any sense the prose means.
  let ourModule (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => (toString env.header.moduleNames[i.toNat]!).startsWith "Lean4Lean"
    | none => false
  --
  -- INTERNAL DECLARATIONS MUST STAY IN THE GRAPH. The first version of this script skipped them
  -- (`if n.isInternal then continue`) and under-counted by ~20%: if theorem `T`'s proof reaches the
  -- hole only through `T.match_1` or a `_proof_` term, dropping that node severs BOTH edges and `T`
  -- vanishes from the count. Caught because a stream implemented the same measurement
  -- independently and got 540/888 where this got 435/761 — a disagreement is the only reason the
  -- bug surfaced. Traverse everything; filter only when COUNTING.
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut ours := 0
  for (n, ci) in env.constants.toList do
    if !ourModule n then continue
    if !n.isInternal then ours := ours + 1
    for d in (deps ci).toList do
      rev := rev.insert d ((rev.getD d #[]).push n)
  IO.println s!"population: {mods.size} built modules, {ours} non-internal declarations in Lean4Lean\n"
  for sName in names do
    let target := sName.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    if !env.contains target then
      IO.println s!"NOT FOUND   {sName}   (0 users is NOT evidence here -- fix the name and rerun)\n"
      continue
    let direct := (rev.getD target #[]).filter (fun n => !n.isInternal)
    -- BFS over reverse edges
    let mut seen : NameSet := ∅
    -- SEED UNFILTERED. Fixing the graph (above) but seeding from the *filtered* direct set is the
    -- same bug one line later: if a hole's only direct user is internal — `inferProj.WF`'s is
    -- `inferType'.WF._unary` — the frontier starts empty and the transitive count reads 0 when the
    -- truth is 70. It also silently under-counts any hole that has *some* internal direct user, by
    -- losing everything reachable only through it. Found by a stream, not by me, after I had already
    -- fixed the graph-building half and reported numbers from the broken seed.
    let mut frontier := rev.getD target #[]
    while !frontier.isEmpty do
      let mut next := #[]
      for n in frontier do
        unless seen.contains n do
          seen := seen.insert n
          next := next ++ rev.getD n #[]
      frontier := next
    -- traversal kept internals; the reported figure counts only real declarations
    let trans := seen.toList.filter (fun n => !n.isInternal)
    let modOf (n : Name) : String :=
      match env.getModuleIdxFor? n with
      | some i => toString env.header.moduleNames[i.toNat]!
      | none => "?"
    let dmods := (direct.map modOf).toList.eraseDups
    let tmods := (trans.map modOf).eraseDups
    IO.println s!"{sName}"
    IO.println s!"  DIRECT     {direct.size} declarations in {dmods.length} modules"
    IO.println s!"  TRANSITIVE {trans.length} declarations in {tmods.length} modules"
    IO.println s!"  (direct = what breaks if the statement changes; transitive = what stands on it,"
    IO.println s!"   and transitive is the number a sentence like \"an N-user hole\" means)"
    for m in dmods.take 6 do IO.println s!"    direct in: {m}"
    if dmods.length > 6 then IO.println s!"    … and {dmods.length - 6} more modules"
    IO.println ""
