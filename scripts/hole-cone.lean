import Lean4Lean.Verify.Typing.ProjGen
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.ProjGenLiftWitness
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
   ``Lean4Lean.VExpr.instAll_liftN_below,
   ``Lean4Lean.VInductDecl'.minorTele_gen,
   ``Lean4Lean.VInductDecl'.minorBodyArgs_gen,
   ``Lean4Lean.VInductDecl'.minorTele_norec,
   ``Lean4Lean.VInductDecl'.minorBodyArgs_norec,
   ``Lean4Lean.ctorArgs_hasArgs_gen,
   ``Lean4Lean.ctorApp_hasType_gen,
   ``Lean4Lean.tyBinder_instAll,
   ``Lean4Lean.padMinor_hbs_gen,
   ``Lean4Lean.padMinor_hasType_gen,
   ``Lean4Lean.padMinor_hbs_norec,
   ``Lean4Lean.padMinor_hasType_norec,
   ``Lean4Lean.ProjClosedGap.projClosedG_needs_recArgs,
   ``Lean4Lean.ProjClosedGap.projClosed_ok_without_recArgs,
   ``Lean4Lean.MutRec.ihTypes_at_rmk,
   ``Lean4Lean.MutRec.minorTele_at_rmk,
   ``Lean4Lean.MutRec.minorBodyArgs_at_rmk,
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
   ``Lean4Lean.VEnv.propLoopEnv2_A_ne_sort',
   -- ProjClosedG: the predicate, its derivation, its consumer, its witnesses
   ``Lean4Lean.VInductDecl'.projClosedG_of_wf,
   ``Lean4Lean.VEnv.IsStructureG.projClosedG,
   ``Lean4Lean.VInductDecl'.closedN_ihType,
   ``Lean4Lean.VInductDecl'.closedTele_minorBinders,
   ``Lean4Lean.ProjClosedGap.badCtor_not_projClosedG,
   ``Lean4Lean.ProjClosedGap.argsCtor_not_projClosedG,
   ``Lean4Lean.Rich.richBlock_projClosedG,
   ``Lean4Lean.Rich.minorBinders_closed,
   -- block A, the `lift'` family
   ``Lean4Lean.VInductDecl'.padMinor_lift',
   ``Lean4Lean.VInductDecl'.realMinor_lift',
   ``Lean4Lean.VInductDecl'.padMotive_lift',
   ``Lean4Lean.VIndType.projMotive_lift',
   ``Lean4Lean.VIndType.projMotive_liftN,
   ``Lean4Lean.VInductDecl'.padMotives_lift',
   ``Lean4Lean.VInductDecl'.padMinorsAux_lift',
   ``Lean4Lean.VInductDecl'.padMinors_lift',
   ``Lean4Lean.VInductDecl'.projCoreG_lift',
   ``Lean4Lean.VInductDecl'.projArgsG_lift',
   ``Lean4Lean.VInductDecl'.projTermG_lift',
   ``Lean4Lean.Rich.projCoreG_lift'_fires,
   ``Lean4Lean.Rich.projTermG_lift'_fires,
   ``Lean4Lean.Rich.padMinor_lift_moves]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Verify.Typing.ProjGen},
                            {module := `Lean4Lean.Verify.Typing.ProjGenWitness},
                            {module := `Lean4Lean.Verify.Typing.ProjGenLiftWitness},
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
