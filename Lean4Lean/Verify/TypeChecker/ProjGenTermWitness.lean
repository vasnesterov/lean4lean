import Lean4Lean.Verify.Typing.ProjGenTerm
import Lean4Lean.Verify.TypeChecker.EtaStructG

/-!
# Firing witness for wall 2, at a genuinely mutual block

`VEnv.IsStructureG.projTermG_hasType` (`Verify/Typing/ProjGenTerm.lean`) is the block-index
generalisation of `projTerm_hasType`.  The question a generalisation always has to answer is
whether it *reaches* anything the narrow statement cannot state, and the answer here is
machine-checked rather than argued: every premise but one is discharged at
`MutField.declEnv` — the **two-type** mutual block of `Verify/TypeChecker/EtaStructG.lean`,
projected member at index **1**, one field — where `VEnv.IsStructure` is outright false
(`MutField.decl_not_isStructure`).

**The one premise left open is `VEnv.WF declEnv`, and it is open for everybody.**  Nothing in
this tree proves `VEnv.WF` of an environment produced by `addInduct'`; that is the keystone
(`addDecl.WF`).  The narrow `projTerm_hasType` is in exactly the same position at *its*
witnesses, so this is not a defect of the generalisation.  Stated as a hypothesis so the
firing is a real implication rather than a claim.
-/

namespace Lean4Lean
namespace MutField

open VExpr

/-- **Wall 2, fired at the second member of a two-type mutual block**, conditional on the
block's environment being well-formed.  `VEnv.IsStructure` cannot state this instance at all. -/
theorem projTermG_hasType_at_mutual (hwf : VEnv.WF declEnv) :
    ProjHasTypeG declEnv 0 `MutField.B decl bTy bCtor [] 1 0 :=
  declEnv_IsStructureG.projTermG_hasType hwf rfl rfl (by simp) 0
    (by rw [bCtor_fields_length]; omega)
    (projLvls_elim_of_F17 (.inr fun k hk _ =>
      bCtor_field_prop k (by rw [bCtor_fields_length]; omega)))

end MutField
end Lean4Lean
