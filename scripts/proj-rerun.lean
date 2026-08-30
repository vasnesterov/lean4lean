import Lean4Lean.Theory.Inductive.StructureExamples
import Lean4Lean.Theory.Inductive.StructureEta
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.Typing.ProjGenWitness
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
