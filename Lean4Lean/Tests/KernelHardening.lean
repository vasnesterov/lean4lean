import Lean4Lean.Environment

/-!
Executable regressions for the kernel hardening merged between Lean v4.32.2 and
v4.33.0-rc2.  The declarations are assembled manually so they exercise
`Lean4Lean.addDecl` and `Lean4Lean.TypeChecker` directly.

## Reaching the C++ kernel: use `addDeclCore`, never `Lean.addDecl`

The *differential* probes at the bottom of this file compare the two kernels' verdicts, and
the C++ side must be reached through `Lean.Kernel.Environment.addDeclCore`
(`@[extern "lean_add_decl"]`), which type-checks synchronously and returns
`Except Kernel.Exception _`.

**`Lean.addDecl` is not usable for this and will give a silently wrong answer.**  Declaration
checking is asynchronous: `Lean.addDecl` returns before the kernel has run, so a harness that
adds a declaration, catches nothing, and restores the environment reports ACCEPT for a
declaration the kernel in fact rejects.  This was hit while writing the positivity probes
below — the first version reported that Lean accepted a projection out of a zero-field
structure — and it was caught only because lean4lean disagreed and the disagreement was
chased instead of the conclusion.  It is the project's recurring failure mode in a new
costume: *absence of an error is not acceptance*.

Anything asserting "the C++ kernel accepts/rejects X" belongs on `addDeclCore`.
-/

namespace Lean4Lean.Tests.KernelHardening

open Lean Lean4Lean TypeChecker

private def errorOf (r : Except Kernel.Exception α) : MetaM (Option String) := do
  match r with
  | .ok _ => return none
  | .error e => return some (← (e.toMessageData {}).toString)

private def mentions (pat s : String) : Bool := (s.splitOn pat).length > 1

private def expectError (label pat : String) (r : Except Kernel.Exception α) : MetaM Unit := do
  match ← errorOf r with
  | none => throwError "{label} was accepted"
  | some msg => unless mentions pat msg do throwError "{label} failed for the wrong reason: {msg}"

private def runM (r : Except Kernel.Exception α) : MetaM α := do
  match r with
  | .ok a => pure a
  | .error e => throwError "kernel operation failed: {← (e.toMessageData {}).toString}"

private def mkPartial (n : Name) (lparams : List Name) (type value : Expr) : DefinitionVal :=
  { name := n, levelParams := lparams, type, value, hints := .opaque, safety := .partial }

private def universeTy : Expr :=
  .forallE `x (.sort (.param `u)) (.sort (.param `u)) .default

private def universeVal : Expr :=
  .lam `x (.sort (.param `u)) (.bvar 0) .default

private def imaxProp : Expr := .sort (.imax (.succ .zero) .zero)

private def imaxDataDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKIPData
    type := imaxProp
    ctors := [{
      name := `L4LKIPData.mk
      type := .forallE `b (.const ``Bool []) (.const `L4LKIPData []) .default }]
  }] false

/-- The auxiliary name the kernel generates for a nested `List` occurrence. -/
private def auxListName : Name := (`_nested ++ `List).appendIndexAfter 1

/-- lean4#14616.  `mk` nests `List L4LKNReal`, so eliminating it makes the kernel generate
`_nested.List_1`; `bad` then names that auxiliary.  This is the form that *discriminates*:
without the check the declaration is accepted, and `restoreNested` rewrites the stored type of
`bad` to `List L4LKNReal → L4LKNReal`, which the kernel never checked.  A declaration naming an
auxiliary that never exists is instead rejected as an unknown constant either way. -/
private def nestedAuxRealDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNReal
    type := .sort 1
    ctors := [
      { name := `L4LKNReal.mk
        type := .forallE `xs (.app (.const ``List [.zero]) (.const `L4LKNReal []))
          (.const `L4LKNReal []) .default },
      { name := `L4LKNReal.bad
        type := .forallE `y (.const auxListName []) (.const `L4LKNReal []) .default }]
  }] false

private def nestedAuxProjDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNProj
    type := .sort .zero
    ctors := [{
      name := `L4LKNProj.mk
      type := .forallE `x (.const ``Nat [])
        (.forallE `y (.proj `_nested.L4LHost_1 0 (.bvar 0))
          (.const `L4LKNProj []) .default) .default }]
  }] false

private def nestedBadDecl (bad : Expr) (name : Name) : Declaration :=
  let ind := fun a => .app (.const name []) a
  .inductDecl [] 1 [{
    name
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [{
      name := name ++ `mk
      type := .forallE `α (.sort 1)
        (.forallE `xs (.app (.const ``Array [.zero]) (ind bad))
          (ind (.bvar 1)) .default) .default }]
  }] false

/-- lean4#14613: projecting the field back out of a `Sort (imax 1 0)` proof would break proof
irrelevance, so `inferProj` must reject it. -/
private def imaxLeakDecl : Declaration :=
  .defnDecl {
    name := `L4LKIPLeak
    levelParams := []
    type := .forallE `proof (.const `L4LKIPData []) (.const ``Bool []) .default
    value := .lam `proof (.const `L4LKIPData []) (.proj `L4LKIPData 0 (.bvar 0)) .default
    hints := .abbrev, safety := .safe }

structure L4LKC where b : Bool
inductive L4LKW : Type where | mk (p : Bool)
inductive L4LKL (α : Type) (b : Bool) : Type where | mk

/-- lean4#14576/#14577: the parametric arguments of a nested occurrence are dropped from the
auxiliary declaration, so they escape checking unless they are checked against the environment
that results from the declaration. Here `w.1.1` is ill typed. -/
private def nestedIllTypedParams : Declaration :=
  let w : Expr := .bvar 0
  let Ew : Expr := .app (.const `L4LKE []) w
  let b : Expr := .proj ``L4LKC 0 (.proj ``L4LKC 0 w)
  let l : Expr := mkApp2 (.const ``L4LKL []) Ew b
  .inductDecl [] 1 [{
    name := `L4LKE
    type := .forallE `w (.const ``L4LKW []) (.sort 1) .default
    ctors := [{
      name := `L4LKE.mk
      type := .forallE `w (.const ``L4LKW [])
        (.forallE `l l (.app (.const `L4LKE []) (.bvar 1)) .default) .default }]
  }] false

private partial def deepNat : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (deepNat n)

structure ProjB where b : Nat

run_meta do
  let env := (← getEnv).toKernelEnv

  -- lean4#14608 and lean4#14632: mutual blocks share level parameters and names.
  expectError "mutual block with mismatched universe parameters"
    "same universe level parameters" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutA [`u] universeTy universeVal,
      mkPartial `L4LMutB [] universeTy universeVal]
  expectError "mutual block with a duplicate name" "duplicate declaration name" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutDup [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutDup [] (.const ``Bool []) (.const ``Bool.true [])]
  match Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutGoodA [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutGoodB [] (.const ``Bool []) (.const ``Bool.true [])] with
  | .error e => throwError "valid mutual block was rejected: {← (e.toMessageData {}).toString}"
  | .ok _ => pure ()

  -- lean4#14613/#14615: normalized `Prop` controls inductive classification and recursor levels.
  let env' ← match Lean4Lean.addDecl env imaxDataDecl with
    | .ok env' => pure env'
    | .error e => throwError "imax-Prop inductive was rejected: {← (e.toMessageData {}).toString}"
  let some (.recInfo recInfo) := env'.find? `L4LKIPData.rec
    | throwError "imax-Prop recursor was not generated"
  unless recInfo.levelParams.isEmpty do
    throwError "imax-Prop inductive received a large-elimination universe"
  -- ... but its field must not be projectable back out, or proof irrelevance equates
  -- `mk false` and `mk true`.
  expectError "projection out of an `imax`-`Prop` proof" "invalid projection" <|
    Lean4Lean.addDecl env' imaxLeakDecl

  -- lean4#14616: a constructor naming a `_nested` auxiliary the kernel really generated.
  expectError "constructor naming a generated nested auxiliary" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxRealDecl
  -- The `Expr.proj` form of the same scan.  Note this one names an auxiliary that never exists,
  -- so it pins the branch rather than the hole: without the check it is still rejected, as an
  -- unknown constant.
  expectError "constructor naming a nested auxiliary in a projection" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxProjDecl

  -- lean4#14576/#14577: parametric arguments dropped from the auxiliary declaration.
  expectError "nested inductive with ill-typed dropped parameters" "invalid projection" <|
    Lean4Lean.addDecl env nestedIllTypedParams

  -- lean4#14607: validate original nested constructor types before elimination can hide them.
  expectError "nested inductive containing a free variable" "free variables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.fvar { name := `l4lBadFVar }) `L4LNestedFVar
  expectError "nested inductive containing a metavariable" "metavariables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.mvar { name := `l4lBadMVar }) `L4LNestedMVar

  -- lean4#14632: projection indices are `Nat` throughout lean4lean, so an index past `2^32`
  -- is stuck rather than truncated.  The structure *name* is deliberately not compared here;
  -- see the projection entry in `divergences.md`.
  let b : Expr := .app (.const ``ProjB.mk []) (mkRawNatLit 7)
  let good : Expr := .proj ``ProjB 0 b
  let huge : Expr := .proj ``ProjB 4294967296 b
  let goodWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf good)
  unless goodWhnf == mkRawNatLit 7 do throwError "valid projection did not reduce"
  let hugeWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf huge)
  unless hugeWhnf == huge do throwError "large projection index was truncated during reduction"
  let same ← runM <| TypeChecker.M.run env (x := TypeChecker.isDefEq good good)
  unless same do throwError "identical projections were not definitionally equal"
  expectError "out-of-range large projection" "invalid projection" <|
    TypeChecker.M.run env (x := TypeChecker.checkType huge)

  -- lean4#13956: lean4lean's explicit fuel remains deterministic and configurable.
  expectError "deep term with low recursion fuel" "deep recursion" <|
    TypeChecker.M.run env (fuel := { recDepth := 1 }) (x := TypeChecker.checkType (deepNat 100))
  match TypeChecker.M.run env (fuel := { recDepth := 1000 })
      (x := TypeChecker.checkType (deepNat 100)) with
  | .error e => throwError "deep term with sufficient recursion fuel failed: {← (e.toMessageData {}).toString}"
  | .ok ty => unless ty.isConstOf ``Nat do throwError "deep term inferred an unexpected type"

/-! ## The positivity scope invariant, probed differentially

`checkPositivity` rejects on `hasIndOcc`, a purely *syntactic* scan of a constructor field's
type.  The abstract counterpart `VIndField.WF.pos` is about the field's *translation*, and
`TrProj` translates `.proj S i e` by splicing in the parameter and index arguments read off
the **type of `e`** — arguments that appear nowhere in `.proj S i e` itself.  So the question
is whether a block constant can ride into those spliced arguments while `hasIndOcc` returns
`false`.  In a strict-positivity check, an occurrence the check cannot see is the shape of a
real defect, which is why this is a permanent regression rather than a one-off experiment.

**It cannot**, and the reason is an invariant load-bearing in both kernels and stated in
neither (`Lean4Lean/Verify/Inductive/Add.lean`, "The positivity scope invariant"):

> At the point `checkConstructors` checks field `i`, every free variable in scope has a type
> that is either definitionally free of the block's constants, or of the form `∀ ξ, I_j p args`.

`checkPositivity`'s two `throw`s maintain it, and the second alternative is a **pi**, which is
never the type of a projectable term.  Two facts finish it: **block-name freshness** (no
existing constant mentions a block name, so δ-unfolding cannot *introduce* one — every block
constant in `whnf t` came from `t`), and **`whnf` is head-only** (an occurrence either survives
into an argument of the head-normal form, where `hasIndOcc` sees it, or is erased and is then
absent from the spliced arguments too).

`Kpos1` versus `Kpos4` is the pair that makes it convincing, and it is why an accepting
control is not enough: a β-redex hiding the occurrence *inside* an index is **rejected**, one
erasing the whole field type is **accepted**, and the difference is exactly whether the
occurrence survives head-normalisation.

Two structural facts the probes depend on, both easy to get wrong:

* `Expr.proj` out of a **one-constructor type with indices** is legal in both kernels —
  `infer_proj` checks `args.size = nparams + nindices` and never demands `nindices = 0`
  (`~/lean4/src/kernel/type_checker.cpp:263`).  So `TrProj`'s index arguments are not vacuous,
  and `KPosBox` below has to be declared by hand with `nparams := 0`, because the `inductive`
  command would promote its index to a parameter.
* `ElimNestedInductive.isNestedInductiveApp?` scans only `[0:numParams]`.  An occurrence in a
  structure *parameter* is therefore consumed by nested-inductive elimination before
  positivity ever sees it (`Ppos1`/`Ppos2`), so only an occurrence in an **index** reaches the
  plain positivity check.  The parameter route and the index route must be probed separately. -/

private structure KPosBox₀ (α : Type) : Type where
  val : α

/-- `KPosBox : Type → Type 1`, `mk : (a : Type) → KPosBox a`, with **`nparams = 0`** so `a` is
an *index*.  One constructor, one field, hence projectable. -/
private def kposBoxDecl : Declaration :=
  let ctor : Constructor :=
    { name := `KPosBox.mk
      type := .forallE `a (.sort 1) (.app (.const `KPosBox []) (.bvar 0)) .default }
  let ty : Expr := .forallE `_ (.sort 1) (.sort 2) .default
  let it : InductiveType := { name := `KPosBox, type := ty, ctors := [ctor] }
  .inductDecl [] 0 [it] false

/-- Run one declaration through **both** kernels and require them to agree, and to agree with
`expect`.  See the module docstring for why the C++ side is `addDeclCore`. -/
private def bothKernels (label : String) (env : Kernel.Environment) (expect : Bool)
    (d : Declaration) : MetaM Unit := do
  let l4l := (Lean4Lean.addDecl env d).toOption.isSome
  let cpp := (Lean.Kernel.Environment.addDeclCore env 0 512 d none).toOption.isSome
  let say := fun b => if b then "accepted" else "rejected"
  unless l4l == cpp do
    throwError "{label}: the kernels disagree — lean4lean {say l4l}, C++ {say cpp}"
  unless l4l == expect do
    throwError "{label}: both kernels {say l4l} it; expected {say expect}"

private def posArrow (a b : Expr) : Expr := .forallE `_ a b .default
private def kboxE (a : Expr) : Expr := .app (.const `KPosBox []) a
private def pboxE (a : Expr) : Expr := .app (.const ``KPosBox₀ []) a

/-- A `Prop`-valued block, so the impredicative F6 level check admits fields of any universe
and the probes are not derailed by universe arithmetic. -/
private def mkPosProp (n : Name) (ctorTy : Expr) : Declaration :=
  let ctor : Constructor := { name := n ++ `mk, type := ctorTy }
  .inductDecl [] 0 [{ name := n, type := .sort .zero, ctors := [ctor] }] false

private def mkPosTy (n : Name) (ctorTy : Expr) : Declaration :=
  let ctor : Constructor := { name := n ++ `mk, type := ctorTy }
  .inductDecl [] 0 [{ name := n, type := .sort 1, ctors := [ctor] }] false

run_meta do
  let env0 := (← getEnv).toKernelEnv
  let C : Name → Expr := fun n => .const n []
  let falseE : Expr := .const ``False []
  let natE : Expr := .const ``Nat []
  -- The indexed carrier itself must be declarable, and by both kernels.
  bothKernels "indexed one-constructor carrier" env0 true kposBoxDecl
  let env ← runM <| Lean4Lean.addDecl env0 kposBoxDecl

  -- === parameter route: nested-inductive elimination takes it before positivity ===
  bothKernels "Ppos1 mk : Box (P -> False) -> P" env false <|
    mkPosTy `L4LPpos1 (posArrow (pboxE (posArrow (C `L4LPpos1) falseE)) (C `L4LPpos1))
  bothKernels "Ppos2 mk : (b : Box (P -> False)) -> b.val -> P" env false <|
    mkPosTy `L4LPpos2 (.forallE `b (pboxE (posArrow (C `L4LPpos2) falseE))
      (posArrow (.proj ``KPosBox₀ 0 (.bvar 0)) (C `L4LPpos2)) .default)

  -- === index route: nesting cannot fire, so this is the probe that matters ===
  -- CONTROL: a projection out of an indexed one-constructor type is legal.
  bothKernels "Kpos0 mk : (b : KPosBox Nat) -> b.0 -> K   [control]" env true <|
    mkPosProp `L4LKpos0 (.forallE `b (kboxE natE)
      (posArrow (.proj `KPosBox 0 (.bvar 0)) (C `L4LKpos0)) .default)
  -- TARGET: the block occurs only in the *index* of `b`'s type.  The field type
  -- `.proj KPosBox 0 b` contains no block constant at all, yet the declaration is rejected —
  -- at the earlier field `b`, by `checkPositivity`'s `isValidIndApp?` branch.
  bothKernels "Kpos1 mk : (b : KPosBox (K -> Nat)) -> b.0 -> K   [target]" env false <|
    mkPosProp `L4LKpos1 (.forallE `b (kboxE (posArrow (C `L4LKpos1) natE))
      (posArrow (.proj `KPosBox 0 (.bvar 0)) (C `L4LKpos1)) .default)
  -- A beta redex hiding the occurrence *inside* the index does not help: `whnf` is head-only,
  -- so `KPosBox ((fun _ => Nat) K)` is already in weak-head normal form.
  bothKernels "Kpos3 redex inside the index" env false <|
    mkPosProp `L4LKpos3 (.forallE `b
      (kboxE (.app (.lam `x (.sort .zero) natE .default) (C `L4LKpos3)))
      (posArrow (.proj `KPosBox 0 (.bvar 0)) (C `L4LKpos3)) .default)
  -- ... whereas a redex over the *whole* field type is ACCEPTED, because the occurrence is
  -- erased outright: the index is then `Nat`, so nothing reaches the spliced arguments either.
  -- This is the other half of the dichotomy; without it the block above proves only that the
  -- checker is conservative.
  bothKernels "Kpos4 redex over the whole field type   [accepted: occurrence erased]" env true <|
    mkPosProp `L4LKpos4 (.forallE `b
      (.app (.lam `x (.sort .zero) (kboxE natE) .default) (C `L4LKpos4))
      (posArrow (.proj `KPosBox 0 (.bvar 0)) (C `L4LKpos4)) .default)
  -- The subject need not be a variable: an application of an earlier field is rejected at
  -- that field, since its type is a pi whose codomain mentions the block.
  bothKernels "Kpos5 subject is `f 0` for f : Nat -> KPosBox (K -> Nat)" env false <|
    mkPosProp `L4LKpos5 (.forallE `f (posArrow natE (kboxE (posArrow (C `L4LKpos5) natE)))
      (posArrow (.proj `KPosBox 0 (.app (.bvar 0) (mkRawNatLit 0))) (C `L4LKpos5)) .default)
  -- Nor can a `let` hide it: the let *value* is a subterm, so the syntactic scan sees it.
  bothKernels "Kpos6 subject is let-bound" env false <|
    mkPosProp `L4LKpos6 (.forallE `b (kboxE (posArrow (C `L4LKpos6) natE))
      (posArrow (.letE `y (kboxE (posArrow (C `L4LKpos6) natE)) (.bvar 0)
        (.proj `KPosBox 0 (.bvar 0)) false) (C `L4LKpos6)) .default)
  -- An occurrence only under a ξ binder of a recursive field takes the *other* throw branch.
  bothKernels "Kpos7 occurrence under a xi binder   [non positive branch]" env false <|
    mkPosProp `L4LKpos7 (.forallE `g
      (.forallE `b (kboxE (posArrow (C `L4LKpos7) natE)) (C `L4LKpos7) .default)
      (C `L4LKpos7) .default)
  -- CONTROL for the previous one: the same shape with a block-free ξ domain is a legitimate
  -- recursive field, so `Kpos7` is not rejected merely for being higher-order.
  bothKernels "Kpos8 same with a block-free xi domain   [control]" env true <|
    mkPosProp `L4LKpos8 (.forallE `g (.forallE `b (kboxE natE) (C `L4LKpos8) .default)
      (C `L4LKpos8) .default)

/-! ## `consumeTypeAnnotations` really fires

Both kernels record `consume_type_annotations(dom)` as a constructor binder's local-context
type, not `dom` itself (`~/lean4/src/kernel/inductive.cpp:222,227`;
`Lean4Lean/Inductive/Add.lean`, the 13 `withLocalDecl` sites).  So the abstract context of the
fvar walk is the *stripped* telescope, only definitionally the constructor's stored one — which
makes `M.WF.elim_loop`'s `hcta` hypothesis false (`Verify/Inductive/Add.lean`, "The one
obligation this cannot discharge").

The temptation is to read that as a technicality that never bites. It bites: the check below
fails the build unless the stripping is a genuine non-identity on a real environment. It exists
so the measurement cannot quietly decay into "in principle only" — an assumption nobody
re-tests is exactly how a false hypothesis becomes invisible.

Deliberately **not** an exact count: the number moves with the prelude. The assertion is that
it is non-zero, plus one named witness whose annotation is `outParam`. -/

/-- `(binder domains, those the stripping changes)` over a pi spine. -/
private partial def annotatedBinders : Expr → Nat × Nat
  | .forallE _ d b _ =>
    let (n, h) := annotatedBinders b
    (n + 1, h + if d.consumeTypeAnnotations == d then 0 else 1)
  | _ => (0, 0)

/-- The first binder domain the stripping changes, if any. -/
private partial def firstAnnotated : Expr → Option Expr
  | .forallE _ d b _ => if d.consumeTypeAnnotations == d then firstAnnotated b else some d
  | _ => none

run_meta do
  let env ← getEnv
  let mut ctors : Nat := 0
  let mut binders : Nat := 0
  let mut hits : Nat := 0
  for (_, ci) in env.constants.toList do
    if let .ctorInfo v := ci then
      let (n, h) := annotatedBinders v.type
      ctors := ctors + 1
      binders := binders + n
      hits := hits + h
  if hits == 0 then
    throwError "`consumeTypeAnnotations` is the identity on every constructor binder domain \
      of this environment ({ctors} constructors, {binders} binders). Either the prelude \
      changed or the function did; `M.WF.elim_loop`'s `hcta` note claims the opposite and \
      must be re-measured."
  logInfo m!"consumeTypeAnnotations fires on {hits}/{binders} constructor binder domains \
    ({ctors} constructors)"
  -- A named witness, so the *shape* is pinned and not just the count.
  let some (.ctorInfo w) := env.find? ``Std.Roc.Sliceable.mk
    | logInfo "witness Std.Roc.Sliceable.mk absent; count assertion above still stands"
  let some dom := firstAnnotated w.type
    | throwError "witness Std.Roc.Sliceable.mk no longer carries a stripped binder domain"
  unless dom.getAppFn.isConstOf ``outParam do
    throwError "witness's annotation is no longer `outParam`: {dom.getAppFn}"

end Lean4Lean.Tests.KernelHardening
