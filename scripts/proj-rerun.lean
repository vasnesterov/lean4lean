import Lean4Lean.Theory.Inductive.StructureExamples
import Lean4Lean.Theory.Inductive.StructureEta
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.Typing.ProjGenWitness
import Lean4Lean.Verify.Typing.ProjGenLiftWitness
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
