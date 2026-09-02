import Lean4Lean.Theory.Typing.AppCodConvSort
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Hole-cone measurement for `Theory/Typing/AppCodConvSort.lean`

Same instrument as `scripts/appcodlevelwf-cone.lean`: for each seed, walk the transitive closure
of the constants its **type and value** reference (`allowOpaque := true`, so `.thmInfo` values are
not silently empty) and report which of the four big holes it contains.

`UniqueTyping` and `ChurchRosser` are imported *only* so that `IsDefEqU.weakN_iff` and
`NormalEq.descend` are present in the measuring environment — the round-4/5 trap, where a name
absent from the environment measures as `present = false` and every cone then looks clean.
`Injectivity` supplies the other two holes and both tainted controls.

    ~/.elan/bin/lake env lean scripts/appcodconvsort-cone.lean
-/
open Lean

def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

partial def go (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then go env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some ci => go env ((deps ci).toList ++ rest) seen
    | none => go env rest seen

def cone (env : Environment) (seed : Name) : NameSet := go env [seed] {}

def holes : List Name :=
  [``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
   ``Lean4Lean.VEnv.WF.rigidShapeUniqNS,
   ``Lean4Lean.VEnv.IsDefEqU.weakN_iff,
   ``Lean4Lean.VEnv.NormalEq.descend]

def controls : List Name :=
  [``Lean4Lean.VEnv.piInv_axiom, ``Lean4Lean.VEnv.WF.sortUniq']

def seeds : List Name :=
  [``Lean4Lean.VEnv.CodType0Refute.lhs_defeq_a,
   ``Lean4Lean.VEnv.CodType0Refute.lhs_defeq_sort,
   ``Lean4Lean.VEnv.CodType0Refute.cond₀,
   ``Lean4Lean.VEnv.CodType0Refute.cond₁,
   ``Lean4Lean.VEnv.CodType0Refute.a_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.lam_hasType_nil,
   ``Lean4Lean.VEnv.CodType0Refute.lhs_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.betaRule_wf,
   ``Lean4Lean.VEnv.CodType0Refute.betaEnv_ordered,
   ``Lean4Lean.VEnv.CodType0Refute.betaEnv_defeqs,
   ``Lean4Lean.VEnv.CodType0Refute.betaEnv_lhs_defeq_sort,
   ``Lean4Lean.VEnv.CodType0Refute.betaEnv_cond₀,
   ``Lean4Lean.VEnv.AppCodHasType0On,
   ``Lean4Lean.VEnv.AppCodType0OnC.hasType0,
   ``Lean4Lean.VEnv.AppCodShareOn.hasType0,
   ``Lean4Lean.VEnv.appCodHasType0On_false,
   ``Lean4Lean.VEnv.appCodType0OnC_false,
   ``Lean4Lean.VEnv.appCodShareOn_false,
   ``Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0OnC_vacuous,
   ``Lean4Lean.VEnv.AppData.mono_index,
   ``Lean4Lean.VEnv.AppCodHasType0On.mono_index,
   ``Lean4Lean.VEnv.AppCodType0OnC.mono_index,
   ``Lean4Lean.VEnv.AppCodShareOn.mono_index,
   ``Lean4Lean.VEnv.appCodType0OnC_false_of_two_le,
   ``Lean4Lean.VEnv.appCodShareOn_false_of_two_le,
   ``Lean4Lean.VEnv.appCodHasType0On_false_of_two_le,
   ``Lean4Lean.VEnv.appCodType0OnC_zero,
   ``Lean4Lean.VEnv.appCodShareOn_zero,
   ``Lean4Lean.VEnv.appCodHasType0On_zero,
   ``Lean4Lean.VEnv.appCodHasType0On_one_false_ordered,
   ``Lean4Lean.VEnv.appCodType0OnC_one_false_ordered,
   ``Lean4Lean.VEnv.appCodShareOn_one_false_ordered,
   ``Lean4Lean.VEnv.codType0OnC_false_somewhere_ordered,
   ``Lean4Lean.VEnv.betaRule_lhs_shape,
   ``Lean4Lean.VEnv.betaRule_lhs_ne_sort,
   ``Lean4Lean.VEnv.betaRule_lhs_ne_forallE]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Theory.Typing.AppCodConvSort},
                            {module := `Lean4Lean.Theory.Typing.Injectivity},
                            {module := `Lean4Lean.Theory.Typing.UniqueTyping},
                            {module := `Lean4Lean.Theory.Typing.ChurchRosser}] {}
  IO.println "-- presence check (a false `present = false` makes every cone below meaningless)"
  for h in holes ++ controls do
    IO.println s!"present {h}: {(env.find? h).isSome}"
  IO.println "-- controls: the instrument must fire on these"
  for c in controls do
    let k := cone env c
    IO.println s!"{c}: cone {k.size}, holes {holes.filter k.contains}"
  IO.println "-- seeds"
  let mut dirty := 0
  for s in seeds do
    let k := cone env s
    let hs := holes.filter k.contains
    if !hs.isEmpty then dirty := dirty + 1
    let sorryish := k.contains ``sorryAx
    IO.println s!"{s}: cone {k.size}, holes {hs}, sorryAx {sorryish}"
  IO.println s!"-- seeds with a hole in cone: {dirty} / {seeds.length}"

#eval! main
