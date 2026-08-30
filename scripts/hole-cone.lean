import Lean4Lean.Verify.Typing.ProjGen
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.Rigidity
import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Theory.Typing.KCanonical
import Lean4Lean.Theory.Typing.PatWFIota

/-!
# Forward hole-cone measurement

For each seed name given below, walk the transitive closure of the constants its **type and
value** reference (`allowOpaque := true`, so `.thmInfo` values are not silently empty) and
report every declaration in it that itself mentions `sorryAx`.

    ~/.elan/bin/lake env lean scripts/hole-cone.lean
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

def seeds : List Name :=
  [``Lean4Lean.VInductDecl'.minorBody_instAll_spine,
   ``Lean4Lean.VInductDecl'.padMotive_liftN,
   ``Lean4Lean.padMotive_body_hasType,
   ``Lean4Lean.padMotive_hasType,
   ``Lean4Lean.padMotive_app_beta,
   ``Lean4Lean.padMinor_beta,
   ``Lean4Lean.padMinor_hasType,
   ``Lean4Lean.padMinor_hasType',
   ``Lean4Lean.VInductDecl'.minorTele_norec,
   ``Lean4Lean.VInductDecl'.minorBodyArgs_norec,
   ``Lean4Lean.ctorArgs_hasArgs_gen,
   ``Lean4Lean.ctorApp_hasType_gen,
   ``Lean4Lean.tyBinder_instAll,
   ``Lean4Lean.padMinor_hbs_norec,
   ``Lean4Lean.padMinor_hasType_norec,
   ``Lean4Lean.MutNonRec.minorBody_head_at_decl2,
   ``Lean4Lean.MutNonRec.padMotives_at_decl2,
   ``Lean4Lean.VEnv.IsDefEq.church_rosser,
   ``Lean4Lean.VEnv.crStatement_holds,
   ``Lean4Lean.VEnv.not_crStatement_of_kstep,
   ``Lean4Lean.VEnv.const_app_inv_of_patWF,
   ``Lean4Lean.VEnv.constNoConf_of_patWF,
   ``Lean4Lean.VEnv.constRigid_of_weakNorm,
   ``Lean4Lean.VEnv.patWF,
   ``Lean4Lean.VEnv.paramsOfPiInv,
   ``Lean4Lean.VEnv.piInv_axiom,
   ``Lean4Lean.TrProj.wf,
   ``Lean4Lean.VEnv.patWF_of_wf,
   ``Lean4Lean.VEnv.const_app_inv_of_wf,
   ``Lean4Lean.VEnv.const_forallE_inv_of_wf,
   ``Lean4Lean.VEnv.const_sort_inv_of_wf,
   ``Lean4Lean.VEnv.constNoConf_of_wf,
   ``Lean4Lean.VEnv.propLoopEnv2_A_ne_B',
   ``Lean4Lean.VEnv.propLoopEnv2_A_ne_sort']

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Verify.Typing.ProjGen},
                            {module := `Lean4Lean.Verify.Typing.ProjGenWitness},
                            {module := `Lean4Lean.Verify.Typing.Lemmas},
                            {module := `Lean4Lean.Verify.Typing.Rigidity},
                            {module := `Lean4Lean.Verify.Typing.ConstSpineWF},
                            {module := `Lean4Lean.Theory.Typing.KCanonical},
                            {module := `Lean4Lean.Theory.Typing.PatWFIota}] {}
  for s in seeds do
    let c := cone env s
    let holes := c.toList.filter fun n =>
      match env.find? n with
      | some ci => (deps ci).contains ``sorryAx || n == ``sorryAx
      | none => false
    IO.println s!"{s}: cone {c.size}, holes {holes.filter (· != ``sorryAx)}"

#eval! main
