import Lean4Lean.Environment
import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.TypeChecker.InferType

/-!
# The three "never fires" gates, fired

`docs/vacuity-ledger.md` row 13 records that `inferProj`, `tryEtaStructCore` and
`isDefEqUnitLike` "never fire", and cites `inferProj_always_throws`,
`tryEtaStructCore_never_true` and `isDefEqUnitLike_never_true` for it.  Those three theorems
are true and this file does not contradict them — but the sentence they get compressed into
is misleading in a way that has cost planning time, so it is worth pinning down by
measurement.

**What is dead is a proof-side branch, not a code path.**  All three vacuity lemmas kill the
`.inductInfo`/`.ctorInfo` arm of a `TrEnv`-guarded lookup, via `TrEnv.not_inductInfo` /
`.not_ctorInfo` (`Verify/TypeChecker/Reduce.lean`), which hold *only* because
`Lean4Lean.AddInduct` (`Verify/Environment/Basic.lean`) has no constructors.  Their hypothesis
`c.TrExprS …` is what carries that emptiness in.  The **executable** checker has no such
hypothesis, and it fires all three gates and returns the affirmative answer at each.

So there is no implementation work in "making the three functions fire": they already do.  The
work is the `AddInduct` flip plus the abstract-side content (`VEnv.StructEta`, and the
`IsStructure` bridges `UnitLikeBridge` / `EtaStructSpine`).

The two `#eval`s below fail the build if any verdict changes.

## What each check establishes

1. **`inferProj` returns a type** at a one-field structure, and *also* at a **recursive**
   one-constructor inductive, both fields — the configuration `VEnv.IsStructure.noRec`
   (`Theory/Inductive/Structure.lean`) cannot describe.  This is `bugs-found.md` item 10
   measured against lean4lean's own `inferProj`, not only against `Lean4Lean.addDecl`; C++
   agrees (`~/lean4/src/kernel/type_checker.cpp`, `type_checker::infer_proj` reads
   `I_val.get_cnstrs()` and the arity and never `InductiveVal.isRec`).
2. **`tryEtaStructCore` returns `true`** relating a variable to its own η-expansion.
3. **`isDefEqUnitLike` returns `true`** on two *distinct free variables* of a zero-field
   structure in `Type`.  `Type`, so `isDefEqProofIrrel` cannot be doing the work; distinct
   fvars, so neither side is a constructor application and `tryEtaStruct` returns `false`
   both ways (`isDefEqCore'` runs `isDefEqUnitLike` last, after `isDefEqApp`,
   `tryEtaExpansion`, `tryEtaStruct` and `tryStringLitExpansion`).
4. `Lean4Lean.addDecl` accepts hand-built declarations whose *only* route to acceptance is
   each of those three answers, so the gates are live in the shipped checker and not merely
   in a direct call.
5. **`isDefEqUnitLike` fires at a member of a two-type mutual block** (`FM1`, whose
   `InductiveVal.all` is `[FM1, FM2]`).  This is the load-bearing consequence for
   `isDefEqUnitLike.WF`: its residual hypothesis `UnitLikeBridge c`
   (`Verify/TypeChecker/IsDefEq.lean`) concludes `c.venv.IsStructure I D T C`, whose `types`
   field is `D.types = [T]`; names are unique in a `VEnv`, so no singleton block can witness
   `FM1`, and `UnitLikeBridge` is therefore **false at this instance** the moment `AddInduct`
   stops being empty.  It is not merely unproved.  The same gap is already recorded for the
   projection and eta paths (`VEnv.IsStructure.types`' docstring,
   `MutNonRec.kernelProjChecks` in `Verify/StructureBridge.lean`); this is the third path, and
   the cheapest, because at **zero fields** no recursor is built at all —
   `VEnv.StructEta.unitLike` goes through `etaExpansion_of_no_fields`, i.e. `C.mk ps`, so
   `types = [T]` is inessential to the *content* and only bundled in by `IsStructure`.
   `VEnv.IsStructureG` (`Verify/Typing/ProjGen.lean`) is the widened predicate that already
   drops it.
-/

namespace Lean4Lean.TypeChecker.FiringWitness
open Lean

/-- A one-field non-recursive structure: `isNonRecStructure` says `true`. -/
structure FS1 where f : Nat
/-- A zero-field non-recursive structure in `Type` — `isDefEqUnitLike`'s gate exactly. -/
structure FS0 where
/-- A *recursive* one-constructor inductive: `isNonRecStructure` says `false`, `inferProj`
does not care. -/
inductive FRec where | mk : Nat → FRec → FRec

/-! `FM1`/`FM2`: a **two-type mutual block** whose first member is zero-field.  This is the
configuration `UnitLikeBridge`'s conclusion cannot describe — `VEnv.IsStructure.types` demands
`D.types = [T]`, names are unique in a `VEnv`, so no singleton block witnesses `FM1`. -/
mutual
/-- The projected member: zero fields, so `isDefEqUnitLike`'s gate passes. -/
inductive FM1 where | mk : FM1
/-- The other half of the block. -/
inductive FM2 where | mk : FM2
end

/-- The `InductiveVal` shapes the checks below rely on, so a change upstream is a failure here
rather than a silently different measurement. -/
def shapeChecks : CoreM Unit := do
  let env ← Lean.getEnv
  let some (.inductInfo v0) := env.find? ``FS0 | throwError "FS0 is not an inductive"
  unless v0.isRec = false && v0.numIndices = 0 && v0.ctors = [``FS0.mk] && v0.all = [``FS0] do
    throwError "FS0's InductiveVal moved"
  unless env.find? ``FS0.mk matches some (.ctorInfo { numFields := 0, .. }) do
    throwError "FS0.mk is no longer a zero-field constructor"
  -- `FS0 : Type`, so proof irrelevance cannot be what relates two of its inhabitants.
  unless v0.type == .sort (.succ .zero) do throwError "FS0 is no longer `Type`"
  let some (.inductInfo v1) := env.find? ``FS1 | throwError "FS1 is not an inductive"
  unless v1.isRec = false && v1.numIndices = 0 && v1.ctors = [``FS1.mk] do
    throwError "FS1's InductiveVal moved"
  unless Lean.isNonRecStructure env ``FS1 do throwError "isNonRecStructure rejects FS1"
  let some (.inductInfo vr) := env.find? ``FRec | throwError "FRec is not an inductive"
  unless vr.isRec = true && vr.numIndices = 0 && vr.ctors = [``FRec.mk] do
    throwError "FRec's InductiveVal moved"
  let some (.inductInfo vm) := env.find? ``FM1 | throwError "FM1 is not an inductive"
  unless vm.isRec = false && vm.numIndices = 0 && vm.ctors = [``FM1.mk]
      && vm.all = [``FM1, ``FM2] do
    throwError "FM1's InductiveVal moved -- the two-type block is what this check is about"

/-- **The direct calls.**  Each of the three functions, invoked on a local context the way the
checker invokes it, with the answer asserted. -/
def gateChecks : Elab.Term.TermElabM Unit := do
  Meta.withLocalDeclD `a (.const ``FS0 []) fun a =>
  Meta.withLocalDeclD `b (.const ``FS0 []) fun b => do
    unless ← (Inner.isDefEqUnitLike a b).run do
      throwError "isDefEqUnitLike no longer relates two distinct inhabitants of FS0"
  Meta.withLocalDeclD `x (.const ``FS1 []) fun x => do
    unless ← (Inner.tryEtaStructCore x (.app (.const ``FS1.mk []) (.proj ``FS1 0 x))).run do
      throwError "tryEtaStructCore no longer relates x to FS1.mk x.0"
    unless (← (Inner.inferProj ``FS1 0 x (.const ``FS1 [])).run) == .const ``Nat [] do
      throwError "inferProj FS1 0 no longer returns Nat"
  -- The gate passes at a member of a two-type mutual block: neither lean4lean nor C++
  -- (`is_non_rec_structure`, `~/lean4/src/kernel/inductive.cpp`) tests block singleton-ness.
  Meta.withLocalDeclD `p (.const ``FM1 []) fun p =>
  Meta.withLocalDeclD `q (.const ``FM1 []) fun q => do
    unless ← (Inner.isDefEqUnitLike p q).run do
      throwError "isDefEqUnitLike no longer fires at a member of a two-type mutual block"
  Meta.withLocalDeclD `y (.const ``FRec []) fun y => do
    -- item 10: both fields, the recursive one included
    unless (← (Inner.inferProj ``FRec 0 y (.const ``FRec [])).run) == .const ``Nat [] do
      throwError "inferProj FRec 0 no longer returns Nat"
    unless (← (Inner.inferProj ``FRec 1 y (.const ``FRec [])).run) == .const ``FRec [] do
      throwError "inferProj FRec 1 no longer returns FRec"

open Elab.Command in
#eval show CommandElabM Unit from do liftCoreM shapeChecks; liftTermElabM gateChecks

/-! ### The same three answers, through `Lean4Lean.addDecl`

Each declaration below is accepted *only if* the corresponding gate answers affirmatively:
`projTest` needs `inferProj` to return a type, `etaTest` needs `tryEtaStructCore x (FS1.mk x.0)`
(nothing else in `isDefEqCore'` relates a variable to a constructor application), and
`unitTest` needs `isDefEqUnitLike` on two distinct variables of `FS0`. -/

private def eqTy (α a b : Expr) : Expr := mkApp3 (.const ``Eq [.succ .zero]) α a b
private def rflOf (α a : Expr) : Expr := mkApp2 (.const ``rfl [.succ .zero]) α a
private def fs1 : Expr := .const ``FS1 []
private def fs0 : Expr := .const ``FS0 []
private def frec : Expr := .const ``FRec []

/-- `fun a : FS1 => a.0` — forces `inferProj`. -/
def projTest : Declaration := .defnDecl
  { name := `Lean4Lean.TypeChecker.FiringWitness.projTest_out, levelParams := [],
    hints := .abbrev, safety := .safe,
    type := .forallE `a fs1 (.const ``Nat []) .default,
    value := .lam `a fs1 (.proj ``FS1 0 (.bvar 0)) .default }

/-- `fun a : FS1 => rfl : ∀ a : FS1, a = FS1.mk a.0` — forces `tryEtaStructCore`. -/
def etaTest : Declaration := .thmDecl
  { name := `Lean4Lean.TypeChecker.FiringWitness.etaTest_out, levelParams := [],
    type := .forallE `a fs1
      (eqTy fs1 (.bvar 0) (.app (.const ``FS1.mk []) (.proj ``FS1 0 (.bvar 0)))) .default,
    value := .lam `a fs1 (rflOf fs1 (.bvar 0)) .default }

/-- `fun a b : FS0 => rfl : ∀ a b : FS0, a = b` — forces `isDefEqUnitLike`. -/
def unitTest : Declaration := .thmDecl
  { name := `Lean4Lean.TypeChecker.FiringWitness.unitTest_out, levelParams := [],
    type := .forallE `a fs0 (.forallE `b fs0 (eqTy fs0 (.bvar 1) (.bvar 0)) .default) .default,
    value := .lam `a fs0 (.lam `b fs0 (rflOf fs0 (.bvar 1)) .default) .default }

/-- `fun a : FRec => a.0` — `inferProj` on a recursive one-constructor inductive. -/
def recProjTest : Declaration := .defnDecl
  { name := `Lean4Lean.TypeChecker.FiringWitness.recProjTest_out, levelParams := [],
    hints := .abbrev, safety := .safe,
    type := .forallE `a frec (.const ``Nat []) .default,
    value := .lam `a frec (.proj ``FRec 0 (.bvar 0)) .default }

#eval show CoreM Unit from do
  let kenv := (← Lean.getEnv).toKernelEnv
  for (nm, d) in [("projTest", projTest), ("etaTest", etaTest), ("unitTest", unitTest),
      ("recProjTest", recProjTest)] do
    match Lean4Lean.addDecl kenv d (check := true) with
    | .ok _ => pure ()
    | .error e => throwError "Lean4Lean.addDecl rejected {nm}: {e.toMessageData {}}"

end Lean4Lean.TypeChecker.FiringWitness
