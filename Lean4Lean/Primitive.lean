import Lean4Lean.TypeChecker
import Lean4Lean.Environment.Basic
import Lean4Lean.Inductive.Add

namespace Lean4Lean
namespace Environment
open Lean hiding Environment Exception
open Kernel TypeChecker

deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for MVarId
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax
deriving instance ToExpr for DataValue
deriving instance ToExpr for KVMap
deriving instance ToExpr for Expr

elab (name := microQq) "q(" e:term ")" : term =>
  return toExpr (← instantiateMVars (← Elab.Term.elabTerm e none))

/-- Type-check a primitive definition's value, and compare its inferred type with `ty`.

`checkPrimitiveDef` runs *before* `checkConstantVal`, so when the recognizer looks at them
neither `v.type` nor `v.value` has been type-checked. Handing either to `isDefEq` compares terms
that may have no translation into the abstract syntax at all, so the comparison carries no
semantic content -- and worse, `isDefEq` records its verdict in the `EquivManager`, whose
well-formedness invariant demands that both sides be translatable. A `Nat.pred` declared with
type `(fun _ : NoSuchType => Nat → Nat) NoSuchValue` used to be accepted here, leaving that redex
in the `EquivManager` (see `bugs-found.md`). `checkConstantVal` rejected the declaration a moment
later, so nothing unsound was ever admitted, but the recognizer's postcondition was false.

Both sides are therefore type-checked before anything is compared. The comparison is against the
*inferred* type of the value rather than the declared `v.type`; `checkConstantVal` separately
forces `v.type` to agree with that inferred type, so the set of declarations `addDecl` accepts
does not change -- only which check rejects a bad one first, and hence the error message.

Cost: measured over the work `addDefinition` actually runs (this recognizer followed by the body
check, in one `M.run`, best of 5 x 40 iterations, all 18 primitives), 65.2 ms here against
63.4 ms before the change -- within noise, because the body check `addDefinition` performs
afterwards shares this one's `inferTypeC` entries. The whole recognizer is ~0.08% of the 83 s
the Kernel Arena's `init` test spends on 53090 declarations. -/
def checkPrimValue (v : DefinitionVal) (ty : Expr) (fail : ∀ {α}, M α) : M Unit := do
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar (← getEnv) v.name v.value
  _ ← checkType ty
  unless ← isDefEq (← checkType v.value) ty do fail

/-- `ensureType` with the *checking* type inference. Same reason as `checkPrimValue`: the
recognizer must not run `inferType`, which assumes its argument is already well-typed, on a term
it has not checked. -/
def checkIsType (e : Expr) : M Expr := do ensureSort (← checkType e) e

/-- `withLocalDecl` with the binder's type checked first.

Every free variable the recognizer introduces has to carry a translation into the abstract
syntax, because every comparison made under it does: the verification's `M.WF.withLocalDecl0`
takes a `TrExprS` and an `IsType` for the domain, and neither exists for a domain the
recognizer has not checked. The domains the four fuel/well-founded branches bind (`1 ≤ y`,
`Nat.succ x ≤ Nat.succ fuel`, `r.type p Bool.true`, the inferred type of a subterm recovered
from a `whnf`) are built from constants the recognizer only requires to be *present*, so this
is the same remedy as `checkedIsDefEq`, applied to binders instead of comparisons. -/
def withCheckedLocalDecl (name : Name) (bi : BinderInfo) (ty : Expr) (k : Expr → M α) : M α := do
  _ ← checkIsType ty
  withLocalDecl name bi ty k

/-- `isDefEq`, with both sides type-checked first.

The recognizer's equations are built from the definition's value *and* from other primitives
that are merely required to be present (`Nat.pred` in the `Nat.sub` branch, `Nat.add` in
`Nat.mul`, and so on). `VEnv.HasPrimitives` pins those primitives' behaviour at numerals but not
their types, so a term like `Nat.add (mul y x) y` need not be well-typed at all; comparing it
with `isDefEq` would again record an untranslatable term in the `EquivManager` (see
`checkPrimValue`). Type-checking both sides first is the uniform remedy, and it is what lets the
verification read a `TrExprS` witness off each comparison instead of having to reconstruct one
from typing facts the recognizer never checks. -/
def checkedIsDefEq (a b : Expr) : M Bool := do
  _ ← checkType a
  _ ← checkType b
  isDefEq a b

/-- Check that `e`'s inferred type is `ty`, with `ty` itself type-checked first -- again so that
both sides of the `isDefEq` have translations. -/
def checkedTypeIs (e ty : Expr) : M Bool := do
  let t ← checkType e
  _ ← checkType ty
  isDefEq t ty

structure Reflection where
  type : Expr
  ofTrue : Expr
  ofFalse : Expr
  toDec : Expr

def Reflection.defn₁ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (¬true = true → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (¬false = true → ¬p) → q) → q) =>
    H fun _ h => h Bool.noConfusion)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q) =>
    if h : b = true then isTrue (H fun h' _ => h' h) else isFalse (H fun _ h' => h' h))

def Reflection.defn₂ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (true = false → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (false = false → ¬p) → q) → q) =>
    H fun _ h => h rfl)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q) =>
    b.casesOn (motive := fun b' => b = b' → Decidable p)
      (fun h => isFalse (H fun _ h' => h' h)) (fun h => isTrue (H fun h' _ => h' h)) rfl)

def Reflection.check (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← checkedTypeIs r.type q(Prop → Bool → Prop) do fail
  -- Accept-set neutral: `toDec` is a subterm of every term `Reflection.checkITE` and
  -- `Condition.check` hand to `checkType`, so a `toDec` that fails to type-check already made
  -- this recognizer branch fail.  Running the check *here* is what gives the verification a
  -- translation of `toDec` at the **base** context; the ones it can read off `checkITE` and
  -- off `Condition.check`'s decision term live under binders of different depths, and
  -- identifying those with one another needs `IsDefEqU.weakN_iff`, which is open.
  _ ← checkType r.toDec

inductive ConditionImpl where
  | bool
  | reflectNatNat (asBool : Expr) (reflect : Reflection) (proof : Expr)

structure Condition where
  prop : Expr
  dec : Expr
  impl : ConditionImpl

def Condition.natLE : Condition where
  prop := q(@LE.le Nat _)
  dec := q(Nat.decLe)
  impl := .reflectNatNat
    (asBool := q(Nat.ble))
    (reflect := .defn₁)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m)))

def Condition.natEq : Condition where
  prop := q(@Eq Nat)
  dec := q(Nat.decEq)
  impl := .reflectNatNat
    (asBool := q(Nat.beq))
    (reflect := .defn₂)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)))

def Condition.bool : Condition where
  prop := q(fun x : Bool => x = true)
  dec := q(fun x => Bool.decEq x true)
  impl := .bool

/-- **One half of `Reflection.checkITE`**: the selection equation at a single boolean literal
`b`, with `sel` picking the branch that literal selects.

This is a separate definition, not two blocks inside `checkITE`, because as two blocks it was
**not** two blocks: `fun t => do` opens its `do` at the same column as the following
`withCheckedLocalDecl`, so the `false` half was nested *inside* the `true` half's `p`, `H` and
`t` binders and ran at binder depth 3 rather than at the base context.  Behaviourally that is
inert -- the three extra local declarations are checked, unused, and mentioned by neither side
of the comparison -- but the verification cannot state the `false` half's conclusion in the
same four-entry context as the `true` half's, and identifying the two across three stale
binders would need `VEnv.IsDefEqU.weakN_iff`, which is open.  Factoring the half out makes the
two calls siblings by construction. -/
def Reflection.checkITEHalf (r : Reflection) (α b : Expr) (sel : Expr → Expr → Expr)
    (fail : ∀ {β}, M β) : M Unit :=
  withCheckedLocalDecl `p .default q(Prop) fun p =>
  withCheckedLocalDecl `H .default (mkApp2 r.type p b) fun H =>
  withCheckedLocalDecl `t .default α fun t =>
  withCheckedLocalDecl `e .default α fun e => do
    unless ← checkedIsDefEq
      (mkApp5 q(@_root_.ite.{1}) α p (mkApp3 r.toDec p b H) t e) (sel t e) do fail

/-- The `@ite` selection rule at result type `α`, checked in exactly the shape the
verification consumes.

The comparison is made on the conditional *application itself* -- `@ite α p (r.toDec p b H) t e`
against the branch it must select -- rather than on the partially applied
`fun p b H α => @ite α p (r.toDec p b H)` compared with `fun α a _ => a`.  The two accept the
same declarations: `isDefEq` descends under λ and is η-complete, so the equation between the
two λ-abstractions holds exactly when all its instances under the binders do, and the instances
are what is checked here.  What changes is the verification: `VEnv.ReflectsCondApp` is stated
over the applied form, so its hypothesis is now read off the check by inverting an application
spine, instead of inverting the translation of a four-fold λ and β-reducing through it.  See
`docs/handoff-primitive.md` §5(a). -/
def Reflection.checkITE (r : Reflection) (α : Expr) (fail : ∀ {β}, M β) : M Unit := do
  _ ← checkIsType α
  -- **The conditional head's own type, at this result type.**  Without it the verification
  -- cannot type the four arguments of the conditional application: `VExpr.WF.app_inv` invents
  -- an existential domain per argument, and `VEnv.condApp_typed` -- the step that hands
  -- `VEnv.reflects_condApp`'s `hsel` its typing hypotheses -- needs the *declared* ones.
  --
  -- The check is on `@ite.{1} α`, not on `@ite.{1}`, and that is load-bearing rather than
  -- cosmetic: `VEnv.condApp_typed` wants `HasType F (∀ (c : Prop), Dc c → α → α → α)` with `F`
  -- the head *already applied to the result type*, and recovering that from
  -- `HasType ite (∀ (α : Type) …)` needs `HasType α (.sort 1)` at the base context, which
  -- `checkIsType α` does not give (it gives `α : Sort u` for an existential `u`).  Checking the
  -- applied form hands the verification exactly the Pi-type it consumes.  Same shape as
  -- `Reflection.checkNatDITE`'s `@dite Nat` check.  See `divergences.md`.
  unless ← checkedTypeIs (mkApp q(@_root_.ite.{1}) α)
    (.forallE `c q(Prop) (.arrow (mkApp q(Decidable) (.bvar 0))
      (.arrow α (.arrow α α))) .default) do fail
  r.checkITEHalf α q(true) (fun t _ => t) fail
  r.checkITEHalf α q(false) (fun _ e => e) fail

/-- **One half of `Reflection.checkNatDITE`**, factored out for the same reason as
`Reflection.checkITEHalf`: as two blocks inside one `do`, the `false` half was nested inside the
`true` half's `p`, `H` and `a` binders. -/
def Reflection.checkNatDITEHalf (r : Reflection) (bl : Expr)
    (sel : Expr → Expr → Expr → Expr → Expr) (fail : ∀ {β}, M β) : M Unit :=
  withCheckedLocalDecl `p .default q(Prop) fun p =>
  withCheckedLocalDecl `H .default (mkApp2 r.type p bl) fun H =>
  withCheckedLocalDecl `a .default (.arrow p q(Nat)) fun a =>
  withCheckedLocalDecl `b .default (.arrow (mkApp q(Not) p) q(Nat)) fun b => do
    unless ← checkedIsDefEq (mkApp4 q(@dite Nat) p (mkApp3 r.toDec p bl H) a b)
      (sel p H a b) do fail

/-- The `@dite` selection rule at result type `Nat`, in the same applied shape as
`Reflection.checkITE` and for the same reason.  The binders are ordered `p`, `H`, `a`, `b` so
that the only one the others depend on is outermost, which is what lets the verification
instantiate them by one `IsDefEqU.instN` followed by three `IsDefEqU.inst0`s. -/
def Reflection.checkNatDITE (r : Reflection) (fail : ∀ {β}, M β) : M Unit := do
  unless ← checkedTypeIs q(Not) q(Prop → Prop) do fail
  -- Same reason as `Reflection.checkITE`'s `@ite` check; note the two branch domains here are
  -- `c → Nat` and `¬c → Nat`, so `dite` needs its own typing lemma, not `VEnv.condApp_typed`.
  unless ← checkedTypeIs q(@dite Nat)
    q(∀ (c : Prop), Decidable c → (c → Nat) → (¬c → Nat) → Nat) do fail
  unless ← checkedTypeIs r.ofTrue (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) do fail
  unless ← checkedTypeIs r.ofFalse (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) do fail
  r.checkNatDITEHalf q(true) (fun p H a _ => mkApp a (mkApp2 r.ofTrue p H)) fail
  r.checkNatDITEHalf q(false) (fun p H _ b => mkApp b (mkApp2 r.ofFalse p H)) fail

/-- **One half of `Condition.check`'s `.bool` selection rule**, factored out for the same reason
as `Reflection.checkITEHalf`: as two blocks inside one `do`, the `false` half was nested inside
the `true` half's `t` binder. -/
def Condition.checkBoolITEHalf (cond : Condition) (α b : Expr) (sel : Expr → Expr → Expr)
    (fail : ∀ {β}, M β) : M Unit :=
  withCheckedLocalDecl `t .default α fun t =>
  withCheckedLocalDecl `e .default α fun e => do
    unless ← checkedIsDefEq (mkApp5 q(@_root_.ite.{1}) α
      (mkApp cond.prop b) (mkApp cond.dec b) t e) (sel t e) do fail

/-- `iteTypes` lists the result types at which the conditional's selection rule is needed:
`Nat` for a `Condition.ite Nat`, `Bool` for a `Condition.decide`.  It replaces the old boolean
`ite` flag, which hard-wired the rule to a single universally quantified `α : Type`; the
verification consumes one `VEnv.ReflectsCondApp` per result type, so the check is now made per
result type as well. -/
def Condition.check (cond : Condition) (fail : ∀ {α}, M α)
    (iteTypes : List Expr := []) (dite := false) : M Unit := do
  _ ← checkType cond.dec
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    unless ← checkedTypeIs cond.prop q(Nat → Nat → Prop) do fail
    reflect.check fail
    for α in iteTypes do reflect.checkITE α fail
    let y := .bvar 0; let x := .bvar 1
    let e := .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
      (mkApp2 cond.prop x y) (mkApp2 asBool x y) (mkApp2 proof x y)
    unless ← checkedTypeIs asBool q(Nat → Nat → Bool) do fail
    unless ← isProp (← checkType proof) do fail
    -- **The reflection proof's own type.**  Without this the verification cannot type
    -- `proof x y` at all: `TrExprS.app` hands back the *existential* domain the application
    -- invented, and pinning it to `reflect.type (prop x y) (asBool x y)` would need
    -- `toDec`'s declared Pi-telescope, which nothing checks.  `Condition.check`'s consumer
    -- (`VEnv.reflects_condApp`) needs exactly this typing to instantiate the selection
    -- equation `Reflection.checkITE` proves under its `p`/`H` binders.  See
    -- `docs/handoff-primitive.md` and `divergences.md`.
    unless ← checkedTypeIs proof
      (.forallE `n q(Nat) (.forallE `m q(Nat) (mkApp2 reflect.type
        (mkApp2 cond.prop x y) (mkApp2 asBool x y)) .default) .default) do fail
    -- `checkType e` is here rather than above the `proof` checks, and the `dite` check is the
    -- arm's last statement, purely so that the verification meets them in a usable order: every
    -- statement in this arm must succeed for the recognizer to accept, so their order is
    -- accept-set neutral, but `checkType e`'s output can only be *read* once `proof`'s own
    -- translation is in hand (`trExprS_decisionTerm_inv'` identifies the `proof x y` subterm
    -- with it), and a trailing `if` needs no `do`-block join point, so the tail of the arm is
    -- traversed once instead of twice.  See `docs/handoff-primitive.md`.
    _ ← checkType e
    unless ← isDefEq e cond.dec do fail
    if dite then reflect.checkNatDITE fail
  | .bool =>
    unless ← checkedTypeIs cond.prop q(Bool → Prop) do fail
    for α in iteTypes do
      _ ← checkIsType α
      -- Same applied form, and for the same reason, as `Reflection.checkITE`'s check.
      unless ← checkedTypeIs (mkApp q(@_root_.ite.{1}) α)
        (.forallE `c q(Prop) (.arrow (mkApp q(Decidable) (.bvar 0))
          (.arrow α (.arrow α α))) .default) do fail
      cond.checkBoolITEHalf α q(true) (fun t _ => t) fail
      cond.checkBoolITEHalf α q(false) (fun _ e => e) fail
    if dite then throw <| .other "unsupported"

protected def Condition.ite (cond : Condition) (α : Expr) (args : Array Expr) (t e : Expr) : Expr :=
  mkApp5 q(@ite.{1}) α (mkAppN cond.prop args) (mkAppN cond.dec args) t e

protected def Condition.dite (cond : Condition) (args: Array Expr) (t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkAppN cond.prop args) (mkAppN cond.dec args)
    (.lam0 (mkAppN cond.prop args) t)
    (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)

protected def Condition.decide (cond : Condition) (args : Array Expr) : Expr :=
  cond.ite q(Bool) args q(true) q(false)

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .lam x dom body bi =>
    let d := dom.instantiateRev fvars
    withCheckedLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

def forallTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .forallE x dom body bi =>
    let d := dom.instantiateRev fvars
    withCheckedLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

/-- **No `Expr.proj` anywhere.**  This is the decidable content of `TrExprS.IsUnique`, the
condition under which a term's translation into the abstract syntax is determined by its
context (`TrExprS.unique`).  Everything else in the recognizer compares constants and
`withCheckedLocalDecl` variables, whose translations are pinned outright; the terms
`unfoldNatWellFounded` recovers are arbitrary, so for those it has to be checked.

`WellFounded.Nat.fix`'s compiled output satisfies it: the packing and unpacking go through
`PSigma.casesOn`, not through projections.

The traversal is `Lean4Lean.anySubterm` rather than a fresh recursion, for the reason that
function's own doc-comment records: every recursive definition, structural or not, gets an
`f._unsafe_rec` companion for code generation, and `Verify/Guard.lean`'s check 3 counts those,
so a new walk would enlarge the frozen implementation-gap list. -/
def isProjNode : Expr → Bool
  | .proj .. => true
  | _ => false

def noProj (e : Expr) : Bool := !Lean4Lean.anySubterm isProjNode e

/-- What `unfoldNatWellFounded` hands its caller.

The unfolder is **search, not verification**: nothing it returns is trusted, and every fact the
verification uses is re-established by a check the *caller* makes on this data.  Three of those
checks were missing, and two of the three made `checkPrimitiveDef.WF.rest`'s `Nat.gcd` and
`Nat.bitwise` branches unprovable rather than merely open:

* **The measure.**  `WellFounded.Nat.fix h F x` reduces to `fix.go h F (Nat.eager (h x + 1)) x _`,
  and `Nat.eager` is a gadget whose whole purpose is to block reduction until its argument is a
  numeral -- so unless `h x` is *known* to reduce to a numeral, the fuel `Nat.rec` never fires
  and the definition does not reduce at literals at all.  A `Nat.gcd` whose measure is
  `fun x => x.1 + 0 * c` for a kernel-opaque `c` passed every check the recognizer made, while
  the Lean kernel refutes `gcd 4 6 = 2` by `rfl` on it
  (`scripts/primitive-wf-refutation.lean`).  The caller now checks `h (pack fvs)` against the
  intended measure.
* **`go`'s own type.**  The fuel induction has to know that the third argument of
  `fix.go α motive h F fuel x` is a proof of `h x < fuel`; without it the recursive call's fuel
  bound has no type at all -- `VExpr.WF.app_inv` invents an existential domain, and the
  induction's step hypothesis is then underivable.  This is exactly what
  `checkedTypeIs q(Nat.modCore.go) q(...)` supplies in the (proved) `Nat.mod` branch.
  `NatWFUnfold.goType` is the type the caller checks.
* **Independence from the recursion variables.**  The induction steps `go` and `pack` to
  *different* arguments, so both must be the same closed terms at every level of the recursion.
  Nothing forced that: `whnfCore` of `e m n` may perfectly well return a `fix α motive h F a₀`
  whose `α`, `motive`, `h` or `F` mention `m` or `n`.  Everything below is therefore returned
  abstracted over the leading `nOuter` variables (none for `Nat.gcd`, the combinator for
  `Nat.bitwise`) and checked to contain no free variables at all.

The fixpoint equation `rhs ≡ F a₀ ih` that this used to check is **gone**.  It was checked at
exactly one `ih`, namely `fun y _ => fix h F y`, and an `IsDefEqU` at one argument says nothing
about another, so a fuel induction -- which needs `F a₀` at `fun y _ => go h F fuel y _` --
could never use it.  What replaces it is the caller's check of `go`'s own fuel recurrence, in
the same shape as the `Nat.mod` and `Nat.div` branches.  See `docs/handoff-primitive.md` and
`divergences.md`. -/
structure NatWFUnfold where
  /-- `fun outer => WellFounded.Nat.fix.go α motive h F`: the fuel recursion, applied to
  everything except the fuel, the argument, and the fuel bound, and abstracted over the leading
  `nOuter` free variables. -/
  go : Expr
  /-- `fun fvs => a₀`: how the unary-ized definition packs its arguments. -/
  pack : Expr
  /-- the measure `h`. -/
  measure : Expr
  /-- the fixpoint's carrier. -/
  alpha : Expr
  /-- the fixpoint's motive. -/
  motive : Expr
  /-- `fun fvs => prf`: the fuel bound the entry point passes. -/
  prfA : Expr

/-- `∀ (fuel : Nat) (x : α), Nat.succ (h x) ≤ fuel → motive x`, i.e. `WellFounded.Nat.fix.go`'s
own type with `α`, `motive` and `h` filled in.  `h x < fuel` is spelled as
`Nat.succ (h x) ≤ fuel` so that the verification meets `VExpr.natLE`, the relation the proved
`Nat.mod` / `Nat.div` fuel telescope is stated with. -/
def NatWFUnfold.goType (u : NatWFUnfold) : Expr :=
  .forallE `fuel q(Nat)
    (.forallE `x u.alpha
      (.forallE `hlt
        (mkApp2 q(@LE.le Nat instLENat)
          (mkApp q(Nat.succ) (.app u.measure (.bvar 0))) (.bvar 1))
        (.app u.motive (.bvar 1)) .default)
      .default)
    .default

/-- Recover `WellFounded.Nat.fix.go α motive h F` and the packing function from a definition
compiled by well-founded recursion on a `Nat`-valued measure.

Nothing here is checked; the caller checks all of it (see `NatWFUnfold`).  The only checks made
are the ones that make the *result* usable at all: that the pieces contain no free variables
beyond the `nOuter` leading ones they are abstracted over. -/
def unfoldNatWellFounded (e : Expr) (fvs : Array Expr) (nOuter : Nat) (fail : ∀ {α}, M α) :
    M NatWFUnfold := do
  let e1 ← whnfCore (mkAppN e fvs) -- get _unary
  let e1 ← unfoldDefinition e1 -- get fix
  let e1 ← whnfCore e1
  -- The application spine is matched out explicitly rather than through `Expr.withApp`, so that
  -- the verification meets one `split` instead of having to reason about `withAppAux`.
  let .app (.app (.app (.app (.app (.const ``WellFounded.Nat.fix [_, _]) α) motive) f) F) a₀ :=
    e1 | fail
  let lctx ← getLCtx
  let e2 ← unfoldDefinition e1 -- get fix.go
  let e2 ← whnfCore e2
  let .app (.app (.app (.app (.app (.app
    (.app (.const ``WellFounded.Nat.fix.go [v₁, v₂]) α') motive') f') F') _fuel) a') prfA :=
    e2 | fail
  unless (α, motive, f, F, a₀) == (α', motive', f', F', a') do fail
  let u : NatWFUnfold :=
    { go := lctx.mkLambda (fvs.extract 0 nOuter)
        (mkAppN (.const ``WellFounded.Nat.fix.go [v₁, v₂]) #[α,motive,f,F])
      pack := lctx.mkLambda fvs a₀
      measure := f
      alpha := α
      motive := motive
      prfA := lctx.mkLambda fvs prfA }
  unless noProj u.go && noProj u.pack && noProj u.measure && noProj u.alpha do fail
  let env ← getEnv
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.go
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.pack
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.measure
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.alpha
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.motive
  _root_.Lean.Kernel.Environment.checkNoMVarNoFVar env ``WellFounded.Nat.fix u.prfA
  return u


def checkPrimitiveDef (v : DefinitionVal) : M Bool := do
  unless v.safety == .safe do return false
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let tru := q(true)
  let fal := q(false)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let pred := mkApp q(Nat.pred)
  let add := mkApp2 q(Nat.add)
  let sub := mkApp2 q(Nat.sub)
  let mul := mkApp2 q(Nat.mul)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let one := succ zero
  let two := succ one
  -- Compare two open terms under genuinely bound free variables. Writing
  -- `isDefEq (.arrow q(Nat) a) (.arrow q(Nat) b)` to get under a binder would instead build the
  -- ill-typed pseudo-type `∀ _ : Nat, a`, whose body is a `Nat` rather than a sort; such a term
  -- has no translation into the abstract syntax, so the comparison would carry no semantic
  -- content. `withLocalDecl` performs exactly the comparison `isDefEqForall` would have made,
  -- but on well-typed terms.
  let defeqT1 (ty : Expr) (f g : Expr → Expr) : M Bool :=
    withLocalDecl `x .default ty fun x => checkedIsDefEq (f x) (g x)
  let defeq1 := defeqT1 q(Nat)
  let defeq2 (f g : Expr → Expr → Expr) : M Bool :=
    withLocalDecl `y .default q(Nat) fun y =>
    withLocalDecl `x .default q(Nat) fun x => checkedIsDefEq (f y x) (g y x)
  let env ← getEnv
  match v.name with
  | ``Nat.add =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- add : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let add := mkApp2 v.value
    -- add x 0 ≡ x
    unless ← defeq1 (fun x => add x zero) (fun x => x) do fail
    -- add y (succ x) ≡ succ (add y x)
    unless ← defeq2 (fun y x => add y (succ x)) (fun y x => succ (add y x)) do fail
  | ``Nat.pred =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- pred : Nat → Nat
    checkPrimValue v q(Nat → Nat) fail
    let pred := mkApp v.value
    unless ← checkedIsDefEq (pred zero) zero do fail
    unless ← defeq1 (fun x => pred (succ x)) (fun x => x) do fail
  | ``Nat.sub =>
    unless env.contains ``Nat && env.contains ``Nat.pred && v.levelParams.isEmpty do fail
    -- sub : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let sub := mkApp2 v.value
    unless ← defeq1 (fun x => sub x zero) (fun x => x) do fail
    unless ← defeq2 (fun y x => sub y (succ x)) (fun y x => pred (sub y x)) do fail
  | ``Nat.mul =>
    unless env.contains ``Nat && env.contains ``Nat.add && v.levelParams.isEmpty do fail
    -- mul : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let mul := mkApp2 v.value
    unless ← defeq1 (fun x => mul x zero) (fun _ => zero) do fail
    unless ← defeq2 (fun y x => mul y (succ x)) (fun y x => add (mul y x) y) do fail
  | ``Nat.pow =>
    unless env.contains ``Nat && env.contains ``Nat.mul && v.levelParams.isEmpty do fail
    -- pow : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let pow := mkApp2 v.value
    unless ← defeq1 (fun x => pow x zero) (fun _ => one) do fail
    unless ← defeq2 (fun y x => pow y (succ x)) (fun y x => mul (pow y x) y) do fail
  | ``Nat.mod =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.sub && env.contains ``Nat.ble && v.levelParams.isEmpty do fail
    -- mod : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let mod := mkApp2 v.value
    unless ← defeq1 (fun x => mod zero x) (fun _ => zero) do fail
    unless ← checkedTypeIs q(@LE.le Nat _) q(Nat → Nat → Prop) do fail
    let le := mkApp2 q(@LE.le Nat _)
    unless ← checkedTypeIs q(Nat.modCore.go)
      q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let go := mkApp5 q(Nat.modCore.go)
    let c := Condition.natLE; c.check fail (iteTypes := [q(Nat)]) (dite := true)
    withCheckedLocalDecl `x .default q(Nat) fun x => do
    withCheckedLocalDecl `y .default q(Nat) fun y => do
    let sx := succ x
    let e := c.ite q(Nat) #[y, sx] (c.dite #[one, y]
      (go y (.bvar 0) (succ sx) sx (mkApp q(Nat.lt_succ_self) sx)) sx) sx
    unless ← checkedIsDefEq (mod sx y) e do fail
    withCheckedLocalDecl `hy .default (le one y) fun hy => do
    withCheckedLocalDecl `fuel .default q(Nat) fun fuel => do
    withCheckedLocalDecl `h .default (le (succ x) (succ fuel)) fun h => do
    let e := c.dite #[y, x] (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x
    unless ← checkedIsDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.div =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.sub && env.contains ``Nat.ble && v.levelParams.isEmpty do fail
    -- div : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let div := mkApp2 v.value
    let c := Condition.natLE; c.check fail (dite := true)
    unless ← checkedTypeIs q(@LE.le Nat _) q(Nat → Nat → Prop) do fail
    let le := mkApp2 q(@LE.le Nat _)
    unless ← checkedTypeIs q(Nat.div.go)
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let go := mkApp5 q(Nat.div.go)
    withCheckedLocalDecl `x .default q(Nat) fun x => do
    withCheckedLocalDecl `y .default q(Nat) fun y => do
    let e := c.dite #[one, y] (go y (.bvar 0) (succ x) x (mkApp q(Nat.lt_succ_self) x)) zero
    unless ← checkedIsDefEq (div x y) e do fail
    withCheckedLocalDecl `hy .default (le one y) fun hy => do
    withCheckedLocalDecl `fuel .default q(Nat) fun fuel => do
    withCheckedLocalDecl `h .default (le (succ x) (succ fuel)) fun h => do
    let e := c.dite #[y, x] (succ (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) zero
    unless ← checkedIsDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.gcd =>
    unless env.contains ``Nat && env.contains ``Bool && env.contains ``Nat.mod
      && env.contains ``Nat.beq && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    -- `Condition.natEq` and `Condition.bool` are closed, and so are their `iteTypes`, so
    -- running their checks *above* the binders is accept-set neutral and puts the facts they
    -- establish at the base context, where `VEnv.ReflectsCondAppD` / `ReflectsCondApp1` want
    -- them.  `Condition.bool` is what unfolds the `Nat.eager` gadget guarding the fuel.
    let c := Condition.natEq; c.check fail (dite := true)
    let bc := Condition.bool; bc.check fail (iteTypes := [q(Nat)])
    -- **Search.**  Nothing `unfoldNatWellFounded` returns is trusted; the checks below are what
    -- the verification reads.  It runs under its own copy of the binders so that the facts the
    -- caller needs at the *base* context -- `go`'s type -- are established there.
    let u ← withCheckedLocalDecl `m .default q(Nat) fun m =>
            withCheckedLocalDecl `n .default q(Nat) fun n =>
              unfoldNatWellFounded v.value #[m, n] 0 fail
    -- **`go`'s own type.**  See `NatWFUnfold`; this is the analogue of the `Nat.mod` branch's
    -- `checkedTypeIs q(Nat.modCore.go) q(...)`, and it is what types the recursive call's fuel
    -- bound.
    unless ← checkedTypeIs u.go u.goType do fail
    -- The carrier, the measure and the packing function, at the base context.  These pin the
    -- three translations the equations below are stated over, and -- because they are checked
    -- where the local context is empty -- give them the closedness the fuel induction needs.
    unless ← checkedTypeIs u.measure (.forallE `x u.alpha q(Nat) .default) do fail
    unless ← checkedTypeIs u.pack
      (.forallE `m q(Nat) (.forallE `n q(Nat) u.alpha .default) .default) do fail
    let pk := mkApp2 u.pack
    withCheckedLocalDecl `m .default q(Nat) fun m => do
    withCheckedLocalDecl `n .default q(Nat) fun n => do
    -- **The measure.**  Without this the fuel never becomes a numeral and the definition does
    -- not reduce at literals at all; see `NatWFUnfold` and
    -- `scripts/primitive-wf-refutation.lean`.
    unless ← checkedIsDefEq (mkApp u.measure (pk m n)) m do fail
    -- **The entry point.**  `gcd m n ≡ go (Nat.eager (h ⟨m,n⟩ + 1)) ⟨m,n⟩ _`, with `Nat.eager`
    -- written out as the conditional `Condition.bool` reflects: at a pair of numerals the
    -- measure check turns the scrutinee into `Nat.beq (m+1) (m+1)`, which `Nat.beq`'s
    -- reflection sends to `true`, and the fuel becomes the numeral `m+1`.
    let X := succ (mkApp u.measure (pk m n))
    unless ← checkedIsDefEq (mkApp2 v.value m n)
      (mkApp3 u.go (bc.ite q(Nat) #[mkApp2 (.const ``Nat.beq []) X X] X X) (pk m n)
        (mkApp2 u.prfA m n)) do fail
    -- **The fuel recurrence**, in the shape the (proved) `Nat.mod` and `Nat.div` branches use.
    -- The fuel bound's domain is written out rather than read off a `whnf`: it is exactly
    -- `go (succ fuel)`'s third argument type at `⟨m,n⟩`, `h ⟨m,n⟩ < succ fuel`, which the
    -- measure check above makes definitionally `Nat.succ m ≤ Nat.succ fuel`.
    withCheckedLocalDecl `fuel .default q(Nat) fun fuel => do
    withCheckedLocalDecl `h .default
      (mkApp2 q(@LE.le Nat instLENat) X (succ fuel)) fun h => do
    -- `.bvar 0` is the `¬(m = 0)` that `Condition.dite`'s else-branch `lam0` binds.
    let hpos := mkApp2 q(@Nat.zero_lt_of_ne_zero) m (.bvar 0)
    let prf := mkApp5 q(@Nat.lt_of_lt_of_le) (mod n m) m fuel
      (mkApp3 q(@Nat.mod_lt) n m hpos) (mkApp3 q(@Nat.le_of_lt_succ) m fuel h)
    unless ← checkedIsDefEq (mkApp3 u.go (succ fuel) (pk m n) h)
      (c.dite #[m, zero] n (mkApp3 u.go fuel (pk (mod n m) m) prf)) do fail
  | ``Nat.beq =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- beq : Nat → Nat → Bool
    checkPrimValue v q(Nat → Nat → Bool) fail
    let beq := mkApp2 v.value
    unless ← checkedIsDefEq (beq zero zero) tru do fail
    unless ← defeq1 (fun x => beq zero (succ x)) (fun _ => fal) do fail
    unless ← defeq1 (fun x => beq (succ x) zero) (fun _ => fal) do fail
    unless ← defeq2 (fun y x => beq (succ y) (succ x)) (fun y x => beq y x) do fail
  | ``Nat.ble =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- ble : Nat → Nat → Bool
    checkPrimValue v q(Nat → Nat → Bool) fail
    let ble := mkApp2 v.value
    unless ← checkedIsDefEq (ble zero zero) tru do fail
    unless ← defeq1 (fun x => ble zero (succ x)) (fun _ => tru) do fail
    unless ← defeq1 (fun x => ble (succ x) zero) (fun _ => fal) do fail
    unless ← defeq2 (fun y x => ble (succ y) (succ x)) (fun y x => ble y x) do fail
  | ``Nat.bitwise =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.add && env.contains ``Nat.div && env.contains ``Nat.mod
      && env.contains ``Nat.beq && v.levelParams.isEmpty do fail
    -- bitwise : Nat → Nat → Nat
    checkPrimValue v q((Bool → Bool → Bool) → Nat → Nat → Nat) fail
    -- `Condition.natEq` and `Condition.bool` are closed, and so are the `iteTypes`, so these
    -- two checks neither read nor bind `f`, `n`, `m`.  Running them *above* the three binders
    -- is accept-set neutral and puts the facts they establish at the base context, where
    -- `VEnv.ReflectsCondApp` wants them; leaving them inside would have needed
    -- `IsDefEqU.weakN_iff` (open) or an instantiation at closed inhabitants.
    let c := Condition.natEq; c.check fail (iteTypes := [q(Nat), q(Bool)]) (dite := true)
    let bc := Condition.bool; bc.check fail (iteTypes := [q(Nat)])
    -- **Search.**  See `NatWFUnfold`; `go` is abstracted over the combinator, which is the one
    -- free variable the fixpoint's `F` legitimately mentions.
    let u ← withCheckedLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
            withCheckedLocalDecl `n .default q(Nat) fun n =>
            withCheckedLocalDecl `m .default q(Nat) fun m =>
              unfoldNatWellFounded v.value #[f, n, m] 1 fail
    unless ← checkedTypeIs u.go (.forallE `f q(Bool → Bool → Bool) u.goType .default) do fail
    unless ← checkedTypeIs u.measure (.forallE `x u.alpha q(Nat) .default) do fail
    unless ← checkedTypeIs u.pack
      (.forallE `f q(Bool → Bool → Bool)
        (.forallE `n q(Nat) (.forallE `m q(Nat) u.alpha .default) .default) .default) do fail
    let pk := mkApp3 u.pack
    withCheckedLocalDecl `f .default q(Bool → Bool → Bool) fun f => do
    let go := mkApp u.go f
    withCheckedLocalDecl `n .default q(Nat) fun n => do
    withCheckedLocalDecl `m .default q(Nat) fun m => do
    -- **The measure**, and **the entry point**: same two checks as the `Nat.gcd` branch.
    unless ← checkedIsDefEq (mkApp u.measure (pk f n m)) n do fail
    let X := succ (mkApp u.measure (pk f n m))
    unless ← checkedIsDefEq (mkApp3 v.value f n m)
      (mkApp3 go (bc.ite q(Nat) #[mkApp2 (.const ``Nat.beq []) X X] X X) (pk f n m)
        (mkApp3 u.prfA f n m)) do fail
    -- **The fuel recurrence.**  The `n = 0` test is a `dite` (the `Nat.bitwise` equation states
    -- it as an `ite`) purely so that the recursive call's fuel bound, which needs `n ≠ 0`, has
    -- a proof of it in scope.
    withCheckedLocalDecl `fuel .default q(Nat) fun fuel => do
    withCheckedLocalDecl `h .default
      (mkApp2 q(@LE.le Nat instLENat) X (succ fuel)) fun h => do
    let n' := div n two
    let m' := div m two
    let b₁ := c.decide #[mod n two, one]
    let b₂ := c.decide #[mod m two, one]
    -- `.bvar 0` is the `¬(n = 0)` the `dite`'s else-branch binds.
    let prf := mkApp5 q(@Nat.lt_of_lt_of_le) n' n fuel
      (mkApp4 q(@Nat.div_lt_self) n two (mkApp2 q(@Nat.zero_lt_of_ne_zero) n (.bvar 0))
        (mkApp q(@Nat.le.refl) two))
      (mkApp3 q(@Nat.le_of_lt_succ) n fuel h)
    let r := mkApp3 go fuel (pk f n' m') prf
    let e := c.dite #[n, zero]
      (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
      c.ite q(Nat) #[m, zero] (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
      bc.ite q(Nat) #[mkApp2 f b₁ b₂] (add (add r r) one) (add r r)
    unless ← checkedIsDefEq (mkApp3 go (succ fuel) (pk f n m) h) e do fail
  | ``Nat.land =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- land : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let .app (.const ``Nat.bitwise []) and := v.value | fail
    -- The combinator's own type. `VEnv.ReflectsBoolBoolBool` carries this alongside the truth
    -- table because `VEnv.ReflectsNatBitwise`'s conclusion is an `IsDefEqU` at
    -- `Nat.bitwise and a b`, which asserts it; the truth table alone does not imply it.
    -- See `docs/handoff-primitive.md` §3.
    unless ← checkedTypeIs and q(Bool → Bool → Bool) do fail
    let and := mkApp2 and
    -- `and : Bool → Bool → Bool`, so the free variable here is a `Bool`
    unless ← defeqT1 q(Bool) (fun x => and fal x) (fun _ => fal) do fail
    unless ← defeqT1 q(Bool) (fun x => and tru x) (fun x => x) do fail
  | ``Nat.lor =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- lor : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let .app (.const ``Nat.bitwise []) or := v.value | fail
    -- The combinator's own type. `VEnv.ReflectsBoolBoolBool` carries this alongside the truth
    -- table because `VEnv.ReflectsNatBitwise`'s conclusion is an `IsDefEqU` at
    -- `Nat.bitwise or a b`, which asserts it; the truth table alone does not imply it.
    -- See `docs/handoff-primitive.md` §3.
    unless ← checkedTypeIs or q(Bool → Bool → Bool) do fail
    let or := mkApp2 or
    -- `or : Bool → Bool → Bool`, so the free variable here is a `Bool`
    unless ← defeqT1 q(Bool) (fun x => or fal x) (fun x => x) do fail
    unless ← defeqT1 q(Bool) (fun x => or tru x) (fun _ => tru) do fail
  | ``Nat.xor =>
    unless env.contains ``Nat && env.contains ``Bool
      && env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- xor : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let .app (.const ``Nat.bitwise []) xor := v.value | fail
    -- The combinator's own type. `VEnv.ReflectsBoolBoolBool` carries this alongside the truth
    -- table because `VEnv.ReflectsNatBitwise`'s conclusion is an `IsDefEqU` at
    -- `Nat.bitwise xor a b`, which asserts it; the truth table alone does not imply it.
    -- See `docs/handoff-primitive.md` §3.
    unless ← checkedTypeIs xor q(Bool → Bool → Bool) do fail
    let xor := mkApp2 xor
    unless ← checkedIsDefEq (xor fal fal) fal do fail
    unless ← checkedIsDefEq (xor tru fal) tru do fail
    unless ← checkedIsDefEq (xor fal tru) tru do fail
    unless ← checkedIsDefEq (xor tru tru) fal do fail
  | ``Nat.shiftLeft =>
    unless env.contains ``Nat && env.contains ``Nat.mul && v.levelParams.isEmpty do fail
    -- shiftLeft : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let shl := mkApp2 v.value
    unless ← defeq1 (fun x => shl x zero) (fun x => x) do fail
    unless ← defeq2 (fun y x => shl x (succ y)) (fun y x => shl (mul two x) y) do fail
  | ``Nat.shiftRight =>
    unless env.contains ``Nat && env.contains ``Nat.div && v.levelParams.isEmpty do fail
    -- shiftRight : Nat → Nat → Nat
    checkPrimValue v q(Nat → Nat → Nat) fail
    let shr := mkApp2 v.value
    unless ← defeq1 (fun x => shr x zero) (fun x => x) do fail
    unless ← defeq2 (fun y x => shr x (succ y)) (fun y x => div (shr x y) two) do fail
  | ``Char.ofNat =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- Char : Type
    _ ← checkIsType q(Char)
    -- @Char.ofNat : Nat → Char, compared *syntactically*.
    -- The declared type of a primitive is what pins down the constant's meaning, and it is read
    -- off structurally rather than up to defeq, so a defeq-but-differently-shaped type such as
    -- `(fun _ : Nat => Nat → Char) Nat.zero` must be rejected here. `==` is `Expr.eqv`, which is
    -- structural equality ignoring binder names and binder info — exactly the identifications
    -- the structural reading makes.
    unless v.type == q(Nat → Char) do fail
  | ``String.ofList =>
    unless env.contains ``String && env.contains ``Char
      && env.contains ``List.nil && env.contains ``List.cons
      && v.levelParams.isEmpty do fail
    -- Char : Type
    _ ← checkIsType q(Char)
    -- List Char : Type
    _ ← checkIsType q(List Char)
    -- @List.nil.{0} Char : List Char
    unless ← checkedTypeIs q(List.nil (α := Char)) q(List Char) do fail
    -- @List.cons.{0} Char : Char → List Char → List Char
    unless ← checkedTypeIs q(List.cons (α := Char)) q(Char → List Char → List Char) do fail
    -- String.ofList : List Char → String, compared syntactically as for `Char.ofNat` above
    unless v.type == q(List Char → String) do fail
  | _ => return false
  return true

def checkPrimitiveInductive (_env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Except Exception Bool := do
  unless !isUnsafe && lparams.isEmpty && nparams == 0 do return false
  let [type] := types | return false
  unless type.type == .sort (.succ .zero) do return false
  let fail {α} : Except Exception α :=
    throw <| .other s!"invalid form for primitive inductive {type.name}"
  match type.name with
  | ``Bool =>
    let [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] := type.ctors | fail
  | ``Nat =>
    let [
      ⟨``Nat.zero, .const ``Nat []⟩,
      ⟨``Nat.succ, .forallE _ (.const ``Nat []) (.const ``Nat []) _⟩
    ] := type.ctors | fail
  | _ => return false
  return true

-- Self-test to ensure that the primitives check at compile time
run_meta
  let env ← Lean.getEnv
  for c in Environment.primitives do
    match env.find? c with
    | some (.defnInfo v) =>
      let (.true, _) ← Elab.Term.TermElabM.run (checkPrimitiveDef v)
        | throwError "{v.name}"
    | some (.inductInfo _) | some (.ctorInfo _) => pure ()
    | r => throwError "unexpected primitive: {r.map (·.name)}"
