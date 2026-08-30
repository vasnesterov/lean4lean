import Lean4Lean.Theory.Inductive.StructureExamples
import Lean4Lean.Theory.Inductive.StructureEta
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.ProjGenLiftWitness
import Lean4Lean.Verify.Typing.ProjGenInstWitness
import Lean4Lean.Verify.Typing.ProjGenMinorWitness
import Lean4Lean.Verify.Typing.ProjGenMinorNarrow
import Lean4Lean.Verify.Typing.ProjGenMotiveWitness
import Lean4Lean.Verify.Typing.ProjGenSwapNarrow
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# The projection cluster's standing checks, re-run

Every name below is a check that must keep firing after any change to the projection
cluster.  `#print axioms` on each is the instrument: a check that stopped existing, or
acquired `sorryAx`, shows up here rather than in a build log.
-/
open Lean4Lean

-- The five `rfl` validations of `etaExpansion` against Lean's own elaborator
-- (`Prod`, `Sigma`, `And`, `Subtype`) and the F17 clause at `And` are anonymous `example`s
-- in `Theory/Inductive/StructureExamples.lean`, so they have no names to print here: the
-- instrument for them is that that module elaborates, i.e.
--     lake build Lean4Lean.Theory.Inductive.StructureExamples
-- Recorded so nobody looks for names that do not exist.

-- structure-eta non-vacuity, both directions
#print axioms Lean4Lean.VEnv.empty_structEta
#print axioms Lean4Lean.bazEnv_structEta
#print axioms Lean4Lean.bazEnv_etaExpansion_eq
#print axioms Lean4Lean.bazEnv_projMinors_distinct
#print axioms Lean4Lean.bazEnv_structEta_premises

-- the refutation, and its inertness against the generalisation
#print axioms Lean4Lean.MutNonRec.kernelProjChecks
#print axioms Lean4Lean.MutNonRec.projCore_arity_wrong
#print axioms Lean4Lean.MutNonRec.projCoreG_arity_right
#print axioms Lean4Lean.MutNonRec.projCoreG_arity_right'

-- the compatibility bridge, and `TrProj.wf`
#print axioms Lean4Lean.VInductDecl'.projTermG_eq_projTerm
#print axioms Lean4Lean.VInductDecl'.recArity_eq_projCoreG
#print axioms Lean4Lean.VInductDecl'.projCoreG_eq_projCore
#print axioms Lean4Lean.TrProj.wf

-- the two eta bridges in the checker
#print axioms Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF_of_structEta
#print axioms Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF_of_structEta

-- this round: the residual
#print axioms Lean4Lean.VInductDecl'.minorBody_instAll_spine
#print axioms Lean4Lean.padMotive_app_beta
#print axioms Lean4Lean.padMinor_beta
#print axioms Lean4Lean.padMinor_hasType'
#print axioms Lean4Lean.padMinor_hasType_norec
#print axioms Lean4Lean.padMinor_hbs_norec
#print axioms Lean4Lean.MutNonRec.minorBody_head_at_decl2
#print axioms Lean4Lean.MutNonRec.padMotives_at_decl2

-- this round: the recursive constructor
#print axioms Lean4Lean.VInductDecl'.minorTele_gen
#print axioms Lean4Lean.VInductDecl'.minorBodyArgs_gen
#print axioms Lean4Lean.padMinor_hbs_gen
#print axioms Lean4Lean.padMinor_hasType_gen
#print axioms Lean4Lean.MutRec.ihTypes_at_rmk
#print axioms Lean4Lean.MutRec.minorTele_at_rmk
#print axioms Lean4Lean.MutRec.minorBodyArgs_at_rmk
#print axioms Lean4Lean.ProjClosedGap.minorBinders_bad
#print axioms Lean4Lean.ProjClosedGap.projClosedG_needs_recArgs
#print axioms Lean4Lean.ProjClosedGap.projClosed_ok_without_recArgs

-- this round: `ProjClosedG`, derived, and its one real consumer
#print axioms Lean4Lean.VInductDecl'.projClosedG_of_wf
#print axioms Lean4Lean.VEnv.IsStructureG.projClosedG
#print axioms Lean4Lean.VEnv.IsStructure.projClosedG
#print axioms Lean4Lean.VInductDecl'.ProjClosedG.toProjClosed
#print axioms Lean4Lean.VInductDecl'.closedN_ihType
#print axioms Lean4Lean.VInductDecl'.closedTele_minorBinders
-- …the refutation re-run against it, and the second conjunct's own witness
#print axioms Lean4Lean.ProjClosedGap.badCtor_not_projClosedG
#print axioms Lean4Lean.ProjClosedGap.minorBinders_args
#print axioms Lean4Lean.ProjClosedGap.projClosedG_needs_recArgs_args
#print axioms Lean4Lean.ProjClosedGap.argsCtor_not_projClosedG
-- …and the block where it carries real data
#print axioms Lean4Lean.Rich.richBlock_projClosedG
#print axioms Lean4Lean.Rich.minorBinders_rich
#print axioms Lean4Lean.Rich.ihType_closed
#print axioms Lean4Lean.Rich.minorBinders_closed
#print axioms Lean4Lean.Rich.minorBinders_not_closed_at_1
#print axioms Lean4Lean.Rich.ihEntry_not_closed_at_3

-- this round: block A's `lift'` family
#print axioms Lean4Lean.VInductDecl'.padMinor_lift'
#print axioms Lean4Lean.VInductDecl'.realMinor_lift'
#print axioms Lean4Lean.VInductDecl'.padMotive_lift'
#print axioms Lean4Lean.VIndType.projMotive_lift'
#print axioms Lean4Lean.VIndType.projMotive_liftN
#print axioms Lean4Lean.VInductDecl'.padMotives_lift'
#print axioms Lean4Lean.VInductDecl'.padMinorsAux_lift'
#print axioms Lean4Lean.VInductDecl'.padMinors_lift'
#print axioms Lean4Lean.VInductDecl'.projCoreG_lift'
#print axioms Lean4Lean.VInductDecl'.projArgsG_lift'
#print axioms Lean4Lean.VInductDecl'.projTermG_lift'
#print axioms Lean4Lean.Rich.projCoreG_lift'_fires
#print axioms Lean4Lean.Rich.projTermG_lift'_fires
#print axioms Lean4Lean.Rich.padMinor_lift_moves

-- this round: block A's `inst` and `instL` families
#print axioms Lean4Lean.VExpr.inst_liftN_add
#print axioms Lean4Lean.VInductDecl'.padMinor_instN
#print axioms Lean4Lean.VInductDecl'.realMinor_instN
#print axioms Lean4Lean.VInductDecl'.padMotive_instN
#print axioms Lean4Lean.VIndType.projMotive_instN
#print axioms Lean4Lean.VInductDecl'.padMotives_instN
#print axioms Lean4Lean.VInductDecl'.padMinorsAux_instN
#print axioms Lean4Lean.VInductDecl'.padMinors_instN
#print axioms Lean4Lean.VInductDecl'.projCoreG_instN
#print axioms Lean4Lean.VInductDecl'.projArgsG_instN
#print axioms Lean4Lean.VInductDecl'.projTermG_instN
#print axioms Lean4Lean.VInductDecl'.projLvls_inst
#print axioms Lean4Lean.VInductDecl'.padMinor_instL
#print axioms Lean4Lean.VInductDecl'.realMinor_instL
#print axioms Lean4Lean.VInductDecl'.padMotive_instL
#print axioms Lean4Lean.VIndType.projMotive_instL
#print axioms Lean4Lean.VInductDecl'.padMotives_instL
#print axioms Lean4Lean.VInductDecl'.padMinorsAux_instL
#print axioms Lean4Lean.VInductDecl'.padMinors_instL
#print axioms Lean4Lean.VInductDecl'.projCoreG_instL
#print axioms Lean4Lean.VInductDecl'.projArgsG_instL
#print axioms Lean4Lean.VInductDecl'.projTermG_instL
-- …the refutation re-run at the *conclusion*, and the passenger check
#print axioms Lean4Lean.ProjClosedGap.padMinor_instN_false_at_badCtor
#print axioms Lean4Lean.ProjClosedGap.padMinor_instN_false_at_argsCtor
-- …fired at the exactly-saturated bound, and not an identity there
#print axioms Lean4Lean.Rich.padMinor_instN_fires
#print axioms Lean4Lean.Rich.projCoreG_instN_fires
#print axioms Lean4Lean.Rich.projTermG_instN_fires
#print axioms Lean4Lean.Rich.padMinor_inst_moves
-- …the `instL` family at a block whose levels actually move
#print axioms Lean4Lean.Poly.projLvls_inst_fires
#print axioms Lean4Lean.Poly.projLvls_moves
#print axioms Lean4Lean.Poly.projMotive_instL_moves
#print axioms Lean4Lean.Poly.projTermG_instL_fires
-- …two negative controls, neither an arity error
#print axioms Lean4Lean.InstControls.realMinor_instN_false_without_hi
#print axioms Lean4Lean.InstControls.projArgsG_instN_false_at_zero
#print axioms Lean4Lean.InstControls.projArgsG_one_at_rich

-- this round: ingredient (b) of `realMinor_hasType_gen`
#print axioms Lean4Lean.VInductDecl'.ProjClosedG.ftype_closedN
#print axioms Lean4Lean.VInductDecl'.projTermG_instAll
#print axioms Lean4Lean.VInductDecl'.projArgsG_eq_map
#print axioms Lean4Lean.VInductDecl'.projMotiveBodyG_instAll
#print axioms Lean4Lean.Rich.projArgsG_eq_map_fires
#print axioms Lean4Lean.Rich.projTermG_instAll_fires
#print axioms Lean4Lean.Rich.projMotiveBodyG_instAll_fires
#print axioms Lean4Lean.DepPair.depBlock_projClosedG
#print axioms Lean4Lean.DepPair.projMotiveBodyG_instAll_fires
#print axioms Lean4Lean.DepPair.rhs_moves
#print axioms Lean4Lean.InstControls.projMotiveBodyG_instAll_false_without_hps

-- this round: ingredient (c), the real minor through the ih block
#print axioms Lean4Lean.VInductDecl'.realMinor_field_hasType
#print axioms Lean4Lean.VInductDecl'.realMinor_hasType_gen
#print axioms Lean4Lean.VInductDecl'.realMinor_hasType_gen'
#print axioms Lean4Lean.VInductDecl'.realMinor_norec
#print axioms Lean4Lean.VInductDecl'.realMinor_hasType_atPadMotives
#print axioms Lean4Lean.RecDep.shape
#print axioms Lean4Lean.RecDep.ihTypes_at_rpmk
#print axioms Lean4Lean.RecDep.minorTele_at_rpmk
#print axioms Lean4Lean.RecDep.realMinor_at_rpmk
#print axioms Lean4Lean.RecDep.realMinor_norec_reading_false
#print axioms Lean4Lean.RecDep.realMinor_ne_projMinor
#print axioms Lean4Lean.RecDep.realMinor_norec_fires
#print axioms Lean4Lean.RecDep.bvar_index_saturated
#print axioms Lean4Lean.RecDep.minorBody_head_at_rpmk
#print axioms Lean4Lean.RecDep.closedTele_ramk
#print axioms Lean4Lean.RecDep.closedTele_rpmk
#print axioms Lean4Lean.RecDep.projClosedG
#print axioms Lean4Lean.RecDep.field_hasType_fires
#print axioms Lean4Lean.RecDep.field_hasType_moves
#print axioms Lean4Lean.RecDep.field_hasType_fires_at_0
#print axioms Lean4Lean.RecDep.field_hasType_fires_at_2
-- …and the collapse test, which inherits the narrow theorem's `sorryAx` by design
#print axioms Lean4Lean.realMinor_hasType_narrow

-- this round: ingredient (d), the motive half of the ι-law chain.  Swap-free part first —
-- every one of these must stay `sorryAx`-free.
#print axioms Lean4Lean.projMotiveTermG
#print axioms Lean4Lean.VIndType.projMotiveG_eq'
#print axioms Lean4Lean.projMotiveTermG_eq_projMotiveTerm
#print axioms Lean4Lean.projMotiveG_liftN
#print axioms Lean4Lean.ProjHasTypeG
#print axioms Lean4Lean.projHasTypeG_eq
#print axioms Lean4Lean.ftype_hasTypeG
#print axioms Lean4Lean.motiveCtxG_wf
#print axioms Lean4Lean.RecDep.padMotive_at_recdep_0
#print axioms Lean4Lean.RecDep.projMotive_at_recdep
#print axioms Lean4Lean.RecDep.padMotives_at_recdep
#print axioms Lean4Lean.RecDep.ctorsAll_at_recdep
#print axioms Lean4Lean.RecDep.padMotives_j_moves
#print axioms Lean4Lean.RecDep.projCoreG_j_moves
#print axioms Lean4Lean.RecDep.projMotiveTermG_at_recdep
#print axioms Lean4Lean.RecDep.projMotiveTermG_j_moves
#print axioms Lean4Lean.RecDep.projMotiveTermG_j_invisible_at_0
#print axioms Lean4Lean.RecDep.motiveTypeG_at_recdep
#print axioms Lean4Lean.RecDep.motiveTypeG_j_moves
#print axioms Lean4Lean.Rich.projMotiveG_liftN_fires
#print axioms Lean4Lean.Rich.projMotiveG_liftN_moves

-- …and the swap half, which routes through `VEnv.HasType.swapCtx` and therefore inherits
-- `weakN_iff` — the narrow chain's own hole, not a new one.  `projArgsG_hasArgs_swapped` and
-- `projMotiveBodyG_hasType_swapped` take the swap data as premises and are clean.
#print axioms Lean4Lean.onCtxFields_instLG
#print axioms Lean4Lean.ftype_hasType_swappedG
#print axioms Lean4Lean.VIndCtor.swapDataG
#print axioms Lean4Lean.projArgsG_hasArgs_swapped
#print axioms Lean4Lean.projMotiveBodyG_hasType_swapped
#print axioms Lean4Lean.projMotiveBodyG_hasType_guarded
#print axioms Lean4Lean.projMotiveTermG_hasType_swapped
#print axioms Lean4Lean.VEnv.IsStructureG.projMotiveTermG_hasType_swapped
#print axioms Lean4Lean.projMotiveTermG_hasType_swapped_narrow
#print axioms Lean4Lean.projMotiveBodyG_hasType_guarded_narrow
