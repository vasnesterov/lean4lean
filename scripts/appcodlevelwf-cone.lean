import Lean4Lean.Theory.Typing.AppCodLevelWF
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Hole-cone measurement for `Theory/Typing/StratLevelWF.lean` and `Theory/Typing/AppCodLevelWF.lean`

Same instrument as `scripts/hole-cone.lean`: for each seed, walk the transitive closure of the
constants its **type and value** reference (`allowOpaque := true`, so `.thmInfo` values are not
silently empty) and report which of the four big holes it contains.

`UniqueTyping` and `ChurchRosser` are imported *only* so that `IsDefEqU.weakN_iff` and
`NormalEq.descend` are present in the measuring environment — the round-4/5 trap, where a name
absent from the environment measures as `present = false` and every cone then looks clean.
`Injectivity` supplies the other two holes and both tainted controls.

    ~/.elan/bin/lake env lean scripts/appcodlevelwf-cone.lean
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
  [``Lean4Lean.VEnv.Stratified.levelWF,
   ``Lean4Lean.VEnv.HasTypeN.levelWF,
   ``Lean4Lean.VEnv.IsDefEqN.levelWF,
   ``Lean4Lean.VEnv.isDefEqN_levelWF_conj_false,
   ``Lean4Lean.VEnv.isDefEqN_levelWF_iff_needs_ctx,
   ``Lean4Lean.VEnv.Stratified.levelWF_subject,
   ``Lean4Lean.VEnv.HasTypeN.levelWF_subject,
   ``Lean4Lean.VEnv.hasTypeN_levelWF_type_needs_ctx,
   ``Lean4Lean.VEnv.forallE_wf_free,
   ``Lean4Lean.VEnv.AppData.levelWF,
   ``Lean4Lean.VEnv.AppData.sort_levelWF,
   ``Lean4Lean.VEnv.HasTypeN.sort_levelWF,
   ``Lean4Lean.VEnv.codType0OnC_sortCase_iff_agree',
   ``Lean4Lean.VEnv.codShareOn_sortCase_forces_syntactic_eq',
   ``Lean4Lean.VEnv.codType0OnC_sortCase_of_agree',
   ``Lean4Lean.VEnv.forallE_wf_of_guard,
   ``Lean4Lean.VEnv.no_badLevel_sortCase,
   ``Lean4Lean.VEnv.badLevel_sortCase_without_guard]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Theory.Typing.AppCodLevelWF},
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
