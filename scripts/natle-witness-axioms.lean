/-
Axiom audit for the `Condition.natLE` witness-producer chain added while attacking the
`Nat.gcd` / `Nat.bitwise` fuel bound (`docs/handoff-primitive-natle.md` §5).

Run: `lake env lean scripts/natle-witness-axioms.lean`
-/
import Lean4Lean.Verify.PrimitiveWF

open Lean4Lean

-- new
#print axioms Lean4Lean.trExprS_ofTrueType_inv'
#print axioms Lean4Lean.VExpr.gcdCtxWF
#print axioms Lean4Lean.VEnv.IsDefEqU.instGcdWF
-- materially changed (conclusion strengthened / hypothesis dropped)
#print axioms Lean4Lean.TypeChecker.Reflection.checkNatDITE.WF
#print axioms Lean4Lean.TypeChecker.Condition.check.WF
#print axioms Lean4Lean.TypeChecker.Condition.check.WF_natLE
#print axioms Lean4Lean.TypeChecker.Condition.check.WF_natEq
#print axioms Lean4Lean.TypeChecker.Condition.check.WF_natLE_pinned
#print axioms Lean4Lean.VEnv.reflects_fuel_gcd
-- the two consumers, unchanged in statement, for comparison
#print axioms Lean4Lean.VEnv.reflects_gcd_of_equations
#print axioms Lean4Lean.VEnv.reflects_bitwise_of_equations
