/-
# `shape.lean` — what in the tree already CONCLUDES this?

**Why this exists, and it is a different failure from `exists.lean`'s.** `exists.lean` answers
"does this NAME exist". Ten times now a brief has claimed a premise was open, unproved, or had
to be carried, when the tree already concluded it under a name nobody would guess. The tenth was
the sharpest: the "one open premise" was `VInductDecl'.WF.params` — a **field of a structure that
was already in scope at the claim site**. No name search finds that, and neither does grepping
the source, because a structure field's statement never appears as source text at all: it is
generated. My searches were over source text; structure projections are constants in the
*environment*.

So this searches the compiled environment structurally: every constant whose TYPE mentions all
of the given head constants, **projections and auto-generated fields included**, sorted cheapest
first (fewest binders), because the cheapest match is usually the one you wanted.

Run:  HEADS="OnCtx VEnv.IsType" lake env lean --run scripts/shape.lean
  or: lake env lean --run scripts/shape.lean OnCtx VEnv.IsType

Give it the head constants of the premise's CONCLUSION, not its rendered text and not an
instantiated form — `env₃` and `1` are not searchable, `OnCtx` and `VEnv.IsType` are. A hit whose
name ends in a structure field is flagged `[FIELD of S]`: that means it is free wherever you have
an `S`, so it is not a premise to carry.
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
  let envHeads := (← IO.getEnv "HEADS").getD ""
  let heads := if argv.isEmpty then envHeads.splitOn " " else argv
  let heads := heads.filter (· != "")
  if heads.isEmpty then
    IO.println "usage: HEADS=\"OnCtx VEnv.IsType\" lake env lean --run scripts/shape.lean"
    IO.println "  give the head constants of the premise's CONCLUSION, not its rendered text"
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
  -- resolve each head to a real constant: an unresolvable head silently matches nothing, which
  -- would print "0 hits" and read as evidence of absence.  That is the exact error this script
  -- exists to prevent, so it is a hard failure instead.
  let mut wanted : Array Name := #[]
  for h in heads do
    let n := h.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    let cands := (#[n, `Lean4Lean ++ n] : Array Name).filter (env.contains ·)
    match cands[0]? with
    | some c => wanted := wanted.push c
    | none =>
      IO.println s!"HEAD NOT A CONSTANT: {h}"
      IO.println "  0 hits from an unresolvable head is NOT evidence of absence -- fix the head and rerun."
      IO.println "  (try the fully qualified name, or with the Lean4Lean prefix)"
      return
  IO.println s!"population: {mods.size} built modules"
  IO.println s!"heads (all must appear in the type): {wanted.toList}\n"
  let mut hits : Array (Nat × Name × String × Bool × Option Name) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let used := ci.type.getUsedConstantsAsSet
    if wanted.all (used.contains ·) then
      let m := match env.getModuleIdxFor? n with
        | some i => toString env.header.moduleNames[i.toNat]!
        | none => "?"
      -- only report our own tree, not the toolchain's
      if !m.startsWith "Lean4Lean" then continue
      let isHole := match ci.value? (allowOpaque := true) with
        | some v => v.hasSorry | none => false
      -- A real projection, not merely a declaration sitting in a structure's NAMESPACE.
      -- The first version of this script used `isStructure env n.getPrefix`, which flags every
      -- theorem in the `VEnv` namespace as a field of `VEnv` -- inventing exactly the kind of
      -- false statement the script exists to prevent.
      let parent := n.getPrefix
      let fieldOf :=
        if (env.getProjectionFnInfo? n).isSome then some parent
        else if !parent.isAnonymous && isStructure env parent
             && (getStructureFields env parent).contains n.getString!.toName then some parent
        else none
      hits := hits.push (arity ci.type, n, m, isHole, fieldOf)
  let sorted := hits.qsort (fun a b => a.1 < b.1)
  -- Structure FIELDS first and always, however many plain hits there are.  A field is free
  -- wherever you hold the structure, so it can retire a premise outright rather than discharge
  -- it -- and it is the one kind of hit that neither a name search nor a source grep can find,
  -- since a field's statement is generated and appears nowhere as text.
  let fields := sorted.filter (fun h => h.2.2.2.2.isSome)
  IO.println s!"{sorted.size} constants in Lean4Lean conclude something mentioning all heads"
  IO.println s!"of which {fields.size} are STRUCTURE FIELDS -- reported first, because a field is not a premise\n"
  for (ar, n, m, isHole, fieldOf) in fields.toList.take 25 do
    let s := match fieldOf with | some s => toString s | none => "?"
    let h := if isHole then "  [HOLE]" else ""
    IO.println s!"  FIELD  arity {ar}  {n}\n            of {s}, module {m}{h}"
    IO.println s!"            free wherever you have a {s} -- do NOT carry this as a hypothesis"
  if fields.size > 25 then IO.println s!"  … {fields.size - 25} more fields"
  IO.println "\n-- plain declarations, sorted by binder count, cheapest first --\n"
  let cap := 40
  for (ar, n, m, isHole, fieldOf) in (sorted.filter (fun h => h.2.2.2.2.isNone)).toList.take cap do
    let flag := match fieldOf with
      | some s => s!"  [FIELD of {s} -- free wherever you have one; NOT a premise to carry]"
      | none => ""
    let h := if isHole then "  [HOLE: its own value is a sorry]" else ""
    IO.println s!"  arity {ar}  {n}\n            module {m}{flag}{h}"
  if sorted.size > cap then
    IO.println s!"\n  … {sorted.size - cap} more (raise the cap or add another head to narrow)"
  if sorted.isEmpty then
    IO.println "  NOTHING -- and this IS meaningful, because heads were resolved to real constants."
    IO.println "  Still pair it with a check that you named the right heads: a premise stated via a"
    IO.println "  DEFINITION that unfolds to your shape will not mention your heads at all."
