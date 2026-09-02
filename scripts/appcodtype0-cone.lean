import Lean4Lean.Theory.Typing.AppCodType0
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Hole-cone measurement for `Theory/Typing/AppCodType0.lean`

Same instrument as `scripts/hole-cone.lean`: for each seed, walk the transitive closure of the
constants its **type and value** reference (`allowOpaque := true`, so `.thmInfo` values are not
silently empty) and report which of the four big holes it contains.

`UniqueTyping` and `ChurchRosser` are imported *only* so that `IsDefEqU.weakN_iff` and
`NormalEq.descend` are present in the measuring environment — the round-4/5 trap, where a name
absent from the environment measures as `present = false` and every cone then looks clean.
`Injectivity` supplies the other two holes and both tainted controls.

    ~/.elan/bin/lake env lean scripts/appcodtype0-cone.lean
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
  [``Lean4Lean.VEnv.CodType0Refute.q,
   ``Lean4Lean.VEnv.CodType0Refute.a,
   ``Lean4Lean.VEnv.CodType0Refute.A,
   ``Lean4Lean.VEnv.CodType0Refute.D,
   ``Lean4Lean.VEnv.CodType0Refute.P,
   ``Lean4Lean.VEnv.CodType0Refute.lhs,
   ``Lean4Lean.VEnv.CodType0Refute.P_lift,
   ``Lean4Lean.VEnv.CodType0Refute.D_inst,
   ``Lean4Lean.VEnv.CodType0Refute.q_wf,
   ``Lean4Lean.VEnv.CodType0Refute.succ_q_equiv,
   ``Lean4Lean.VEnv.CodType0Refute.a_hasType1,
   ``Lean4Lean.VEnv.CodType0Refute.a_hasTypeN,
   ``Lean4Lean.VEnv.CodType0Refute.a_not_hasType0,
   ``Lean4Lean.VEnv.CodType0Refute.lhs_not_hasType0,
   ``Lean4Lean.VEnv.CodType0Refute.A_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.lam_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.D_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.P_hasType,
   ``Lean4Lean.VEnv.CodType0Refute.P_isType,
   ``Lean4Lean.VEnv.CodType0Refute.onCtx,
   ``Lean4Lean.VEnv.CodType0Refute.hx,
   ``Lean4Lean.VEnv.CodType0Refute.hbeta,
   ``Lean4Lean.VEnv.CodType0Refute.hpi,
   ``Lean4Lean.VEnv.CodType0Refute.hx2,
   ``Lean4Lean.VEnv.CodType0Refute.witness,
   ``Lean4Lean.VEnv.CodType0Refute.stuck,
   ``Lean4Lean.VEnv.CodType0Refute.lhs_not_defeq_sort,
   ``Lean4Lean.VEnv.CodType0Refute.witness_outside_conditioned,
   ``Lean4Lean.VEnv.CodType0Refute.witness_snd_is_sort,
   ``Lean4Lean.VEnv.appCodType0On_false,
   ``Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0On_vacuous,
   ``Lean4Lean.VEnv.AppCodType0On.premise_mono,
   ``Lean4Lean.VEnv.AppCodType0OnC,
   ``Lean4Lean.VEnv.AppLvlAgreeOn,
   ``Lean4Lean.VEnv.AppCodType0On.conditioned,
   ``Lean4Lean.VEnv.lvlAgree_strictly_stronger,
   ``Lean4Lean.VEnv.appUniqLvlOn_of_appLvlAgreeOn,
   ``Lean4Lean.VEnv.appLvlAgreeOn_of_sortRedInv_codType0OnC,
   ``Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0OnC,
   ``Lean4Lean.VEnv.codType0OnC_sortCase_iff_agree,
   ``Lean4Lean.VEnv.codType0OnC_sortCase_of_agree,
   ``Lean4Lean.VEnv.sortInvN_of_route,
   ``Lean4Lean.VEnv.SortRed.type0_pin_any,
   ``Lean4Lean.VEnv.AppCodShareOn,
   ``Lean4Lean.VEnv.AppCodType0OnC.share,
   ``Lean4Lean.VEnv.appLvlAgreeOn_of_sortRedInv_codShareOn,
   ``Lean4Lean.VEnv.codShareOn_sortCase_forces_syntactic_eq,
   -- the statements this file refutes / prices, measured too
   ``Lean4Lean.VEnv.AppCodType0On,
   ``Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0On,
   ``Lean4Lean.VEnv.appCodType0_false_everywhere]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Theory.Typing.AppCodType0},
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
