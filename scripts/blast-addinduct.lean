import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.SafeFragment
import Lean4Lean.Verify.EqSafety
import Lean4Lean.Verify.Bridge
import Lean4Lean.Verify.Inductive.Add
import Lean4Lean.Verify.Environment.Induct
import Lean4Lean.Verify.Typing.DefEqCtx
import Lean4Lean.Verify.Primitive
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.NormLt
import Lean4Lean.Verify.LevelStd

/-!
# Blast-radius measurement for `AddInduct`'s emptiness

Same instrument as `scripts/cone-measure.lean` -- the same `deps`, with the
`value? (allowOpaque := true)` fix for the `.thmInfo` scan trap.  Run from the repo root:

    ~/.elan/bin/lake env lean scripts/blast-addinduct.lean

Not in any `lean_lib` glob, so `lake build` ignores it.

Two seed sets:

* **tier 1** -- the seven lemmas whose *proofs* case on the empty `AddInduct`.  Their
  statements stay true after the flip (except `no_inductInfo`); the arms are proved.
* **tier 2** -- the statements that become *false* after the flip.

The second `#eval` splits each cone by whether the declaration is already `sorryAx`-tainted:
that is the measurement that says how much *proved content* the flip actually costs.
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

def transUsersMany (g : Graph) (seeds : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := seeds
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      for u in g.rev.getD n #[] do
        unless seen.contains u do seen := seen.insert u; stack := u :: stack
  return seen

def l4l (s : NameSet) : NameSet := Id.run do
  let mut o : NameSet := {}
  for m in s.toList do if (`Lean4Lean).isPrefixOf m then o := o.insert m
  return o

def allMods (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames do s := s.insert m
  return s

def modOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def mkScope (env : Environment) (mods : NameSet) : Name → Bool := fun n =>
  match modOf env n with | some m => mods.contains m | none => false

open Lean4Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let scope := l4l (allMods env)
  let g := buildGraph env (mkScope env scope)
  IO.println s!"scope: {g.fwd.size} Lean4Lean source declarations"
  -- tier 1: proofs that literally case on the empty `AddInduct`
  let tier1 : List Name := [``AddInduct.to_addInduct, ``Aligned.addInduct, ``AddInduct.le,
    ``TrEnv'.of_value, ``TrEnv'.find?_shape, ``TrEnv'.defeqs_shape, ``TrEnv'.no_inductInfo]
  -- tier 2: statements that become FALSE on the flip
  let tier2 : List Name := [``TrEnv'.no_inductInfo, ``TrEnv.not_inductInfo,
    ``TrEnv.not_ctorInfo, ``TrEnv.not_recInfo, ``TypeChecker.VContext.not_inductInfo,
    ``TypeChecker.Inner.inductiveReduceRec_eq_none, ``checkEqType.WF, ``TrEnv'.find?_shape,
    ``TrEnv.find?_shape]
  for (lbl, seeds) in [("tier1 (proofs casing on empty AddInduct)", tier1),
                       ("tier2 (statements false after the flip)", tier2)] do
    IO.println s!"=== {lbl}"
    for t in seeds do
      let direct := (g.rev.getD t #[]).toList.eraseDups
      IO.println s!"  {t}: direct={direct.length} transitive={(transUsersMany g [t]).toList.length}"
      for d in direct.toArray.qsort (·.toString < ·.toString) do
        IO.println s!"      {d}   [{(modOf env d).getD `unknown}]"
    let u := transUsersMany g seeds
    IO.println s!"  UNION transitive users: {u.toList.length}"
    let mut bymod : Std.HashMap Name Nat := {}
    for n in u.toList do
      let m := (modOf env n).getD `unknown
      bymod := bymod.insert m ((bymod.getD m 0) + 1)
    for (m, c) in bymod.toList.toArray.qsort (·.1.toString < ·.1.toString) do
      IO.println s!"      {c}  {m}"

open Lean4Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let scope := l4l (allMods env)
  let g := buildGraph env (mkScope env scope)
  let tier2 : List Name := [``TrEnv'.no_inductInfo, ``TrEnv.not_inductInfo,
    ``TrEnv.not_ctorInfo, ``TrEnv.not_recInfo, ``TypeChecker.VContext.not_inductInfo,
    ``TypeChecker.Inner.inductiveReduceRec_eq_none, ``checkEqType.WF, ``TrEnv'.find?_shape,
    ``TrEnv.find?_shape]
  let tier1 : List Name := [``AddInduct.to_addInduct, ``Aligned.addInduct, ``AddInduct.le,
    ``TrEnv'.of_value, ``TrEnv'.find?_shape, ``TrEnv'.defeqs_shape, ``TrEnv'.no_inductInfo]
  for (lbl, seeds) in [("tier1", tier1), ("tier2", tier2)] do
    let u := (transUsersMany g seeds).toList
    let mut clean : List Name := []
    let mut tainted := 0
    for n in u do
      let ax ← collectAxioms n
      if ax.contains ``sorryAx then tainted := tainted + 1 else clean := n :: clean
    IO.println s!"=== {lbl}: {u.length} users; already sorryAx-tainted {tainted}; \
      currently sorry-FREE {clean.length}"
    for n in clean.toArray.qsort (·.toString < ·.toString) do
      IO.println s!"      {n}   [{(modOf env n).getD `unknown}]"
