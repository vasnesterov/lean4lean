import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Environment

/-!
This module contains the front-end-specific trust boundary for declaration verification.
The checker, extension, and declaration modules introduce no additional `sorry`-backed
assumptions. The imported type-checker and theory layers retain their own explicit
verification gaps.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- What the primitive-definition recognizer must establish beyond ordinary type checking.
This is kept separate from declaration checking so that the remaining metatheory does not
depend on the recognizer's syntactic implementation. Primitive semantics are claimed only
in well-formed extensions of the environment in which recognition ran. -/
structure PrimitiveResult (checked : VEnv) (v : DefinitionVal) (allow : Bool) : Prop where
  safe : allow = true → v.safety = .safe
  no_level_params : allow = true → v.levelParams = []
  preserves : allow = true → ∀ {safety : DefinitionSafety} {venv env' : VEnv} {ci' : VDefVal},
    checked ≤ venv → venv.WF →
    venv.HasPrimitives →
    TrDefVal safety venv (.defnInfo v) ci' → ci'.WF venv →
    venv.addConst v.name ci'.toVConstant = some env' →
    (env'.addDefEq ci'.toDefEq).HasPrimitives

/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer.

Two earlier refutations of this statement have been closed on the implementation side
(`Lean4Lean/Primitive.lean`):

* the `Char.ofNat` and `String.ofList` branches now compare `v.type` with `==` (`Expr.eqv`,
  structural up to binder names and binder info) rather than `isDefEq`, so the `VConstant`
  that `TrConstant` reads off structurally is forced to be the one `VEnv.HasPrimitives`
  demands; and
* the `Nat` branches compare open terms under `withLocalDecl`-bound free variables instead of
  wrapping them in the ill-typed pseudo-type `∀ _ : Nat, e`, which had no `TrExprS` witness and
  therefore made every `isDefEq` spec vacuous.

The remaining mathematical content is the 16 reflection theorems relating the primitive `Nat`
operations to their Lean definitions (`VEnv.ReflectsNatNat`, `…NatNat`, `…NatNatBool`,
`ReflectsNatBitwise`), including the fuel recursion of `Nat.div`/`Nat.mod` and the
`WellFounded.Nat.fix`/`Acc.rec` unfolding used by `Nat.gcd`/`Nat.bitwise`.  Nine of them --
`Nat.add`, `Nat.pred`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.shiftLeft`,
`Nat.shiftRight` -- are proved in `Lean4Lean/Verify/Primitive.lean`, together with the whole
environment side (`VEnv.PrimField`, `VEnv.HasPrimitives.addDef`, `VEnv.const_defeq_value`).

**This statement is nevertheless false as it stands, for a third reason, and the `sorry` below
cannot be narrowed until `Lean4Lean/Primitive.lean` changes again.**

`checkPrimitiveDef` runs *before* `checkConstantVal`, so when it is called neither `v.type` nor
`v.value` has been type-checked.  Every `Nat` branch nonetheless calls `TypeChecker.isDefEq` on
them (`isDefEq v.type q(Nat → Nat → Nat)`, and `defeq1`/`defeq2` on terms built from
`v.value`).  `TypeChecker.isDefEq` records a successful comparison in the `EquivManager`
(`Lean4Lean/TypeChecker.lean`, `st.eqvManager.addEquiv t s`), and `TypeChecker.VState.WF`'s
`ectx` field demands `EquivManager.WF`, whose `defeq` field demands
`EquivManager.IsDefEqE venv lparams Δ' t s`.  Since `M.WF` requires the final state to satisfy
`VState.WF`, a proof would have to produce that `IsDefEqE`, and `IsDefEqE` can relate terms of
different head shape only through its `defeq` constructor, which needs `TrExprS` witnesses on
both sides.  Untyped input has none.

Concretely: in a kernel environment holding only `Nat` and `Nat.zero` as axioms and
`Nat.succ := fun n => n` as a definition -- an environment with no inductive types, hence one
that `TrEnv` models today -- the declaration

    Nat.pred : (fun _ : NoSuchType => Nat → Nat) NoSuchValue := fun n => n

is accepted by `checkPrimitiveDef` (it returns `.ok true`), and its final `eqvManager` has the
declared type and `Nat → Nat` in one equivalence class.  `NoSuchType` and `NoSuchValue` are
absent from the environment, so by `TrExprS.const` the declared type has no `TrExprS` witness in
any model, and no `IsDefEqE` can relate it to `Nat → Nat`: `IsDefEqE`'s congruence constructors
preserve which constants a term mentions, and its `defeq` constructor is unavailable.  So
`VState.WF` fails for the final state and this theorem is false.  The same happens through
`v.value` (5 `eqvManager` keys mentioning the absent constant, with the real `Nat.add` body
wrapped in the same redex).

The fix belongs in `Lean4Lean/Primitive.lean`: each branch must obtain `TrExprS` witnesses
before comparing, e.g. by guarding with `Environment.checkNoMVarNoFVar` and replacing
`isDefEq v.type q(Nat → Nat → Nat)` with `isDefEq (← checkType v.value) q(Nat → Nat → Nat)`,
which both supplies the `TrExprS` for `v.value` that `defeq1`/`defeq2` need and pins the
value's type.  Note that comparing `v.type` syntactically with `==`, as the `Char.ofNat` branch
does, is *not* available here: the declared types of the `Nat` primitives carry `@&` borrow
annotations (`.mdata { borrowed := true }` around each `Nat` domain), so `==` would reject
them.  Once the recognizer produces those witnesses, the nine branches above are drop-in. -/
theorem checkPrimitiveDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig := {}) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams fuel) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := by
  sorry
