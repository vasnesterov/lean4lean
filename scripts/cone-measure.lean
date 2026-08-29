import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.SafeFragment
import Lean4Lean.Verify.Bridge
import Lean4Lean.Verify.Inductive.Add
import Lean4Lean.Verify.Environment.Induct
import Lean4Lean.Verify.Typing.DefEqCtx
import Lean4Lean.Verify.Primitive
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.NormLt
import Lean4Lean.Verify.LevelStd

/-!
# Cone measurement instrument

Reverse-dependency measurement over this package's declarations.  Run from the repo root:

    ~/.elan/bin/lake env lean scripts/cone-measure.lean

It is deliberately *not* part of any `lean_lib` glob, so `lake build` ignores it.

**The scan trap this file exists to avoid.**  `ConstantInfo.value?` returns `none` for
`.thmInfo` unless `allowOpaque := true` is passed (see `Lean/Declaration.lean`), so a naive
`getUsedConstantsAsSet` sweep silently reports a cone of size 0 for anything used only inside
theorem proofs.  `deps` below passes it.

Two scopes are reported:
* **A** — declarations whose defining module is in the import closure of
  `Verify/TypeChecker.lean` + `Verify/Typing/Lemmas.lean` (the closure `Verify/SafeFragment.lean`
  §4 measured).
* **B** — declarations from every `Lean4Lean.*` module reachable from the imports below, i.e.
  all of `Verify/` including `Verify/Primitive.lean`, which scope A does **not** contain.
-/

open Lean

/-- Constants referenced by `ci`, from its type *and* its value -- theorems included. -/
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

/-- Transitive users of `seed`, with every name in `cut` treated as absent (its own edges do
not propagate).  `cut = {}` is the plain transitive user set. -/
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

def transUsers (g : Graph) (seed : Name) : NameSet := transUsersCut g seed {}

def importClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:names.size] do idx := idx.insert names[i] i
  let mut seen : NameSet := {}
  let mut stack := roots
  while true do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if seen.contains m then continue
      seen := seen.insert m
      if let some i := idx[m]? then
        for imp in env.header.moduleData[i]!.imports do stack := imp.module :: stack
  return seen

def modOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def mkScope (env : Environment) (mods : NameSet) : Name → Bool := fun n =>
  match modOf env n with | some m => mods.contains m | none => false

def l4l (s : NameSet) : NameSet := Id.run do
  let mut o : NameSet := {}
  for m in s.toList do if (`Lean4Lean).isPrefixOf m then o := o.insert m
  return o

def allMods (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames do s := s.insert m
  return s

open Lean4Lean VEnv in
#eval show CoreM Unit from do
  let env ← getEnv
  let scopeA := l4l (importClosure env
    [`Lean4Lean.Verify.TypeChecker, `Lean4Lean.Verify.Typing.Lemmas])
  let scopeB := l4l (allMods env)
  let mkCut (l : List Name) : NameSet := l.foldl (·.insert ·) ({} : NameSet)
  /- The twelve declarations that enlargement (E) of `docs/backward-analysis.md` would turn
  into rules; `Verify/SafeFragment.lean` §4's table cuts these in stages. -/
  let E := [``IsDefEqU.trans, ``IsDefEqU.defeqDF, ``IsDefEqU.of_l, ``IsDefEqU.of_r,
    ``HasType.defeqU_l, ``HasType.defeqU_r, ``IsType.defeqU_l, ``IsDefEq.trans_l,
    ``IsDefEq.trans_r, ``IsDefEq.transU_l, ``IsDefEq.transU_r, ``isDefEq_iff]
  for (lbl, mods) in [("A (TypeChecker + Typing/Lemmas closure)", scopeA),
                      ("B (all Lean4Lean modules)", scopeB)] do
    let g := buildGraph env (mkScope env mods)
    IO.println s!"=== scope {lbl}: {g.fwd.size} source declarations"
    for t in [``IsDefEqU.sort_inv, ``IsDefEq.uniq, ``IsDefEq.uniqU, ``HasType.piUniq] do
      let direct := (g.rev.getD t #[]).toList.eraseDups
      IO.println s!"  {t}: direct={direct.length} transitive={(transUsers g t).toList.length}"
      for d in direct.toArray.qsort (·.toString < ·.toString) do IO.println s!"      {d}"
    let count (l : List Name) := (transUsersCut g ``IsDefEqU.sort_inv (mkCut l)).toList.length
    IO.println s!"  sort_inv users: none cut {count []}, under (E) {count E}, \
      (E)+piUniq {count (E ++ [``HasType.piUniq])}, \
      (E)+piUniq+weakN_iff' {count (E ++ [``HasType.piUniq, ``IsDefEq.weakN_iff'])}"
