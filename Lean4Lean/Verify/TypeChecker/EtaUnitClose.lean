import Lean4Lean.Verify.TypeChecker.EtaUnitRefute
import Lean4Lean.Verify.TypeChecker.EtaResidual
import Lean4Lean.Verify.TypeChecker

/-!
# The two eta holes: **true today, vacuously; false the day `AddInduct` lands**

`Verify/TypeChecker/IsDefEq.lean` carries two `sorry`s:

```
:556  tryEtaStructCore.WF : RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂'
:1052 isDefEqUnitLike.WF  : RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → …
```

`EtaResidual.lean` reduces both to the single abstract hypothesis `c.venv.StructEtaG`, and
`EtaUnitRefute.lean` proves that hypothesis **false** at `MutField.unitEnv`, a `VEnv` whose
`VEnv.WF` is proved.  What that leaves open is the step from "the residual is refuted" to "the
hole is false": the holes quantify over `VContext`, and no `VContext` has `venv = unitEnv`
today, because `Lean4Lean.AddInduct` has no constructors.

This file closes that step **conditionally**, and measures the two directions of vacuity.

* §1 the abstract contradiction, isolated: `MutField.unitEnv_foo_ne_Amk`.
* §2 the two holes are **false** at any `VContext` over `unitEnv` at which the checker answers
  affirmatively — `isDefEqUnitLike_WF_false_of_flip`, `tryEtaStructCore_WF_false_of_flip`, and
  the pair `etaHoles_false_of_flip`.  The one ingredient neither of them can supply today is
  `TrEnv safety env unitEnv`, i.e. the `AddInduct` flip; everything else is discharged here.
* §3 the *other* direction of vacuity: both holes are true today, in one line each, hole-free
  (`tryEtaStructCore.WF_today`, `isDefEqUnitLike.WF_today`).  So the pair
  {§2, §3} is exactly "vacuously true now, false later", which is what a `sorry` that must not
  be closed looks like.
* §4 the firing witness at the *refutation's own shape* — an **axiom** inhabitant of a
  zero-field structure in `Type` — run through `M.run`/`RecM.run`, the same call the §2
  hypothesis names.  `FiringWitness.lean` fires the same gates at *free variables*; a free
  variable cannot carry the refutation (there is no bvar-vs-constructor no-confusion in this
  tree), so the axiom version is the one that matters here.
-/

namespace Lean4Lean

/-! ## 1. The abstract contradiction, isolated

`EtaUnitRefute.lean` derives `¬ unitEnv.UnitEta` from `VEnv.constNoConf_of_notIsProof` applied
to the eta *rule's* output.  The same application, with the rule's output replaced by a bare
`IsDefEqU` assumption, is the statement §2 needs: the two constant inhabitants of the
zero-field member are not related by the thirteen-constructor `VEnv.IsDefEq`. -/

namespace MutField

/-- **`foo` and `A.mk` are not definitionally equal in `unitEnv`.**  Both inhabit the zero-field
member `A : Type` of a two-type mutual block; `foo` is an axiom, so it is not a proof, and
no-confusion at a non-proof constant head separates them. -/
theorem unitEnv_foo_ne_Amk :
    ¬ unitEnv.IsDefEqU 0 [] (.const `MutField.foo []) (.const `MutField.A.mk []) := fun h =>
  absurd (VEnv.constNoConf_of_notIsProof unitEnv_wf 0 (VEnv.patWF_of_wf unitEnv_wf 0)
    (Γ := []) trivial (as := []) (as' := [])
    (unitEnv_ruleFreeHead (by decide) (by decide))
    (unitEnv_ruleFreeHead (by decide) (by decide))
    unitEnv_not_isProof_foo h) (by decide)

/-! ### `unitEnv` satisfies two of `VEnvAt`'s three fields outright

`VEnvAt env safety venv` (`Verify/TypeChecker.lean`) has three fields: `tr`, `hasPrimitives`
and `safePrimitives`.  The second is proved here, so the `AddInduct`-blocked premise of §2 is
**exactly** `TrEnv safety env unitEnv` plus a condition on `env` alone.  Every one of
`HasPrimitives`' 24 fields is guarded by `env.contains …` or by a `constants … = some ci`
hypothesis, and `unitEnv` contains only the six names of `MutField.decl` plus `foo`; so all 24
are vacuous. -/

theorem declEnv_addInduct : VEnv.empty.addInduct' decl = some declEnv := declEnv_eq.choose_spec

/-- `unitEnv` knows only `MutField.foo` and the six names of the block. -/
theorem unitEnv_constants_eq_none {n : Lean.Name}
    (h1 : `MutField.foo ≠ n) (h2 : n ∉ decl.allNames) : unitEnv.constants n = none := by
  rw [VEnv.addConst_eq_of_ne declEnv_addConst h1,
    VEnv.addInduct'_constants_of_not_mem declEnv_addInduct h2]
  rfl

/-- Any containment claim at a name outside those seven is absurd.  The two side conditions are
`autoParam`s so that callers write `unitEnv_absurd h` and the name is fixed by `h`. -/
theorem unitEnv_absurd {α : Prop} {n : Lean.Name} (h : unitEnv.contains n)
    (h1 : `MutField.foo ≠ n := by decide) (h2 : n ∉ decl.allNames := by decide) : α := by
  obtain ⟨_, h⟩ := h
  rw [unitEnv_constants_eq_none h1 h2] at h
  exact absurd h nofun

@[inherit_doc unitEnv_absurd]
theorem unitEnv_absurd' {α : Prop} {n : Lean.Name} {ci : VConstant}
    (h : unitEnv.constants n = some ci)
    (h1 : `MutField.foo ≠ n := by decide) (h2 : n ∉ decl.allNames := by decide) : α :=
  unitEnv_absurd ⟨_, h⟩ h1 h2

/-- **`VEnv.HasPrimitives` is free at `unitEnv`.** -/
theorem unitEnv_hasPrimitives : VEnv.HasPrimitives unitEnv where
  bool h := unitEnv_absurd h
  boolFalse h := unitEnv_absurd' h
  boolTrue h := unitEnv_absurd' h
  nat h := unitEnv_absurd h
  natZero h := unitEnv_absurd' h
  natSucc h := unitEnv_absurd' h
  natAdd h := unitEnv_absurd h
  natPred h := unitEnv_absurd h
  natSub h := unitEnv_absurd h
  natMul h := unitEnv_absurd h
  natPow h := unitEnv_absurd h
  natGcd h := unitEnv_absurd h
  natMod h := unitEnv_absurd h
  natDiv h := unitEnv_absurd h
  natBEq h := unitEnv_absurd h
  natBLE h := unitEnv_absurd h
  natBitwise h := unitEnv_absurd h
  natLAnd h := unitEnv_absurd h
  natLOr h := unitEnv_absurd h
  natXor h := unitEnv_absurd h
  natShiftLeft h := unitEnv_absurd h
  natShiftRight h := unitEnv_absurd h
  charOfNat h := unitEnv_absurd' h
  stringOfList h := unitEnv_absurd' h

end MutField

end Lean4Lean

/-! ## 2. Both holes are false at a post-flip context -/

namespace Lean4Lean
namespace TypeChecker

open Lean hiding Environment Exception
open Kernel

/-- **The `AddInduct`-blocked premise of §2, isolated.**  `VEnvAt`'s `hasPrimitives` field is
free at `unitEnv` (`MutField.unitEnv_hasPrimitives`) and `safePrimitives` constrains `env`, not
`venv`; so the whole of §2's environment hypothesis is `TrEnv safety env MutField.unitEnv`. -/
theorem MutField.venvAt_of_trEnv {env : Environment} {safety : DefinitionSafety}
    (htr : TrEnv safety env MutField.unitEnv)
    (hsafe : ∀ {n : Name} {ci : ConstantInfo}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []) :
    VEnvAt env safety MutField.unitEnv where
  tr := htr
  hasPrimitives := MutField.unitEnv_hasPrimitives
  safePrimitives := hsafe

theorem isDefEqUnitLike_WF_false_of_flip
    {env : Environment} {safety : DefinitionSafety}
    (hva : VEnvAt env safety MutField.unitEnv)
    {m : Methods} (hm : m.WF) {st : State}
    (hfire : Inner.isDefEqUnitLike (.const `MutField.foo []) (.const `MutField.A.mk []) m
        (VContext.mk1 hva).toContext {} = .ok (true, st))
    (H : ∀ {e₁ e₂ : Expr} {e₁' e₂' : VExpr} {c : VContext} {s : VState},
      c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
      RecM.WF c s (Inner.isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂') :
    False := by
  have htr₁ : (VContext.mk1 hva).TrExprS (.const `MutField.foo []) (.const `MutField.foo []) :=
    .const MutField.unitEnv_foo rfl rfl
  have htr₂ : (VContext.mk1 hva).TrExprS (.const `MutField.A.mk []) (.const `MutField.A.mk []) :=
    .const MutField.unitEnv_Amk rfl rfl
  obtain ⟨vs', -, -, -, hQ⟩ := H htr₁ htr₂ (s := {}) m hm VState.WF.empty1 _ _ hfire
  exact MutField.unitEnv_foo_ne_Amk (hQ rfl)

theorem tryEtaStructCore_WF_false_of_flip
    {env : Environment} {safety : DefinitionSafety}
    (hva : VEnvAt env safety MutField.unitEnv)
    {m : Methods} (hm : m.WF) {st : State}
    (hfire : Inner.tryEtaStructCore (.const `MutField.foo []) (.const `MutField.A.mk []) m
        (VContext.mk1 hva).toContext {} = .ok (true, st))
    (H : ∀ {e₁ e₂ : Expr} {e₁' e₂' : VExpr} {c : VContext} {s : VState},
      c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
      RecM.WF c s (Inner.tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂') :
    False := by
  have htr₁ : (VContext.mk1 hva).TrExprS (.const `MutField.foo []) (.const `MutField.foo []) :=
    .const MutField.unitEnv_foo rfl rfl
  have htr₂ : (VContext.mk1 hva).TrExprS (.const `MutField.A.mk []) (.const `MutField.A.mk []) :=
    .const MutField.unitEnv_Amk rfl rfl
  obtain ⟨vs', -, -, -, hQ⟩ := H htr₁ htr₂ (s := {}) m hm VState.WF.empty1 _ _ hfire
  exact MutField.unitEnv_foo_ne_Amk (hQ rfl)

/-! ## 3. The other direction of vacuity: both holes are TRUE today, in one line each -/

/-- **`tryEtaStructCore.WF` as stated, proved.**  `tryEtaStructCore_never_true` says the
answer is `false` whenever `e₂` translates, so the implication `b → …` is vacuous.  `he₁` is
not needed, which is itself the measurement: the hole's own hypothesis about `e₁` is dead
weight while `AddInduct` is empty. -/
theorem tryEtaStructCore.WF_today {c : VContext} {s : VState} {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (_he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (Inner.tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  (Inner.tryEtaStructCore_never_true he₂).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun

/-- **`isDefEqUnitLike.WF` as stated, proved.**  Dual to the above; here it is `he₂` that is
dead weight. -/
theorem isDefEqUnitLike.WF_today {c : VContext} {s : VState} {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (he₁ : c.TrExprS e₁ e₁') (_he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (Inner.isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
  (Inner.isDefEqUnitLike_never_true he₁).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun

/-- **Both statements, and the fact that they are simultaneously refutable at a post-flip
context.**  Read as one theorem, this is the shape of a `sorry` that must not be closed: the
left conjuncts are the two holes, proved; the right conjunct says the same two statements are
false at any `VContext` over `MutField.unitEnv` at which the checker answers affirmatively. -/
theorem etaHoles_true_today_false_of_flip {c : VContext} {s : VState}
    {e₁ e₂ : Expr} {e₁' e₂' : VExpr}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    {env : Environment} {safety : DefinitionSafety} (hva : VEnvAt env safety MutField.unitEnv)
    {m : Methods} (hm : m.WF) {st₁ st₂ : State}
    (hfire₁ : Inner.tryEtaStructCore (.const `MutField.foo []) (.const `MutField.A.mk []) m
        (VContext.mk1 hva).toContext {} = .ok (true, st₁))
    (hfire₂ : Inner.isDefEqUnitLike (.const `MutField.foo []) (.const `MutField.A.mk []) m
        (VContext.mk1 hva).toContext {} = .ok (true, st₂)) :
    RecM.WF c s (Inner.tryEtaStructCore e₁ e₂) (fun b _ => b → c.IsDefEqU e₁' e₂') ∧
    RecM.WF c s (Inner.isDefEqUnitLike e₁ e₂) (fun b _ => b = .true → c.IsDefEqU e₁' e₂') ∧
    ¬ (∀ {e₁ e₂ : Expr} {e₁' e₂' : VExpr} {c : VContext} {s : VState},
        c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
        RecM.WF c s (Inner.tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂') ∧
    ¬ (∀ {e₁ e₂ : Expr} {e₁' e₂' : VExpr} {c : VContext} {s : VState},
        c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
        RecM.WF c s (Inner.isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂') :=
  ⟨tryEtaStructCore.WF_today he₁ he₂, isDefEqUnitLike.WF_today he₁ he₂,
   tryEtaStructCore_WF_false_of_flip hva hm hfire₁,
   isDefEqUnitLike_WF_false_of_flip hva hm hfire₂⟩

end TypeChecker

/-! ## 4. `hfire` measured, at the refutation's own shape

`FiringWitness.lean` fires these two gates at **free variables** of a zero-field structure.
That is the right measurement for "the code path is live", but it cannot carry §2's
refutation: the abstract side needs no-confusion, and no-confusion in this tree is available
only at a **constant** head (`VEnv.constNoConf_of_notIsProof`; there is no
bvar-vs-constructor no-confusion anywhere, see `docs/handoff-etaunit.md` §2).  So the shape
that matters here is an **axiom** inhabitant, which is exactly what `MutField.foo` is.

The axiom is added to a *kernel environment value* by `Lean4Lean.addDecl`, not to this module's
environment, so this file declares no axiom.  The two `M.run` calls below are syntactically the
call named by §2's `hfire`, with `m = Methods.withFuel …` supplied by `RecM.run`.
-/

namespace EtaUnitClose
open Lean

/-- A zero-field structure in `Type` — `isNonRecStructure` says `true`, and `Type` (not `Prop`)
so `isDefEqProofIrrel` cannot be what relates its inhabitants. -/
structure Z : Type where

private def zTy : Expr := .const ``Z []
private def fooName : Name := `Lean4Lean.EtaUnitClose.fooAx
private def fooE : Expr := .const fooName []
private def mkE : Expr := .const ``Z.mk []

/-- `axiom fooAx : Z` — a *second* constant inhabiting `Z`, the shape `MutField.foo` abstracts. -/
def fooAxDecl : Declaration := .axiomDecl
  { name := fooName, levelParams := [], type := zTy, isUnsafe := false }

/-- `theorem : fooAx = Z.mk := rfl` — accepted only if a gate identifies an axiom with the
constructor of a zero-field `Type`-valued structure. -/
def eqTest : Declaration := .thmDecl
  { name := `Lean4Lean.EtaUnitClose.eqTest_out, levelParams := [],
    type := mkApp3 (.const ``Eq [.succ .zero]) zTy fooE mkE,
    value := mkApp2 (.const ``rfl [.succ .zero]) zTy fooE }

open TypeChecker in
#eval show CoreM Unit from do
  let some (.inductInfo v) := (← getEnv).find? ``Z | throwError "Z is not an inductive"
  unless v.isRec = false && v.numIndices = 0 && v.ctors = [``Z.mk]
      && v.type == .sort (.succ .zero) do
    throwError "Z is no longer a zero-field non-recursive structure in Type"
  let .ok kenv := Lean4Lean.addDecl (← getEnv).toKernelEnv fooAxDecl
    | throwError "Lean4Lean.addDecl rejected the axiom inhabitant of Z"
  unless M.run kenv .safe {} [] {} (RecM.run (Inner.isDefEqUnitLike fooE mkE)) matches .ok true do
    throwError "isDefEqUnitLike no longer answers true at (fooAx, Z.mk)"
  unless M.run kenv .safe {} [] {} (RecM.run (Inner.tryEtaStructCore fooE mkE)) matches .ok true do
    throwError "tryEtaStructCore no longer answers true at (fooAx, Z.mk)"
  match Lean4Lean.addDecl kenv eqTest with
  | .ok _ => pure ()
  | .error e => throwError "Lean4Lean.addDecl rejected `fooAx = Z.mk`: {e.toMessageData {}}"

end EtaUnitClose

/-! ## 5. The two edits to `IsDefEq.lean` that this round makes available — and the one it
recommends

`IsDefEq.lean` is not mine.  Two edits are *available*:

```lean
-- IsDefEq.lean:556-558, and note the binder must become `_he₁` or the
-- `linter.unusedVariables` warning fires (measured):
theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (_he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  (tryEtaStructCore_never_true he₂).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun

-- IsDefEq.lean:1052-1054, likewise `_he₂`:
theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (_he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
  (isDefEqUnitLike_never_true he₁).mono fun _ _ _ h hb => absurd (h ▸ hb) nofun
```

Both are `sorryAx`-free (`WF_today` above is each of them, verbatim).  **Neither should be
made.**  §2 is the reason, now as a theorem rather than as a docstring's warning: each edit
would install a proof of a statement that `tryEtaStructCore_WF_false_of_flip` /
`isDefEqUnitLike_WF_false_of_flip` show to be *false* at a post-flip context, so the two `sorry`s
would be replaced by two theorems that must be deleted again, and in the interval the refinement
layer would report structure eta as done.  The repair is on the abstract side: give
`VEnv.IsDefEq` the structure-eta rule, at which point `EtaResidual.lean`'s
`tryEtaStructCore.WF_of_structEtaG'` and `isDefEqUnitLike.WF_of_structEtaG` close both holes
with content. -/

end Lean4Lean

#print axioms Lean4Lean.MutField.unitEnv_constants_eq_none
#print axioms Lean4Lean.MutField.unitEnv_hasPrimitives
#print axioms Lean4Lean.MutField.unitEnv_foo_ne_Amk
#print axioms Lean4Lean.TypeChecker.MutField.venvAt_of_trEnv
#print axioms Lean4Lean.TypeChecker.tryEtaStructCore.WF_today
#print axioms Lean4Lean.TypeChecker.isDefEqUnitLike.WF_today
#print axioms Lean4Lean.TypeChecker.tryEtaStructCore_WF_false_of_flip
#print axioms Lean4Lean.TypeChecker.isDefEqUnitLike_WF_false_of_flip
#print axioms Lean4Lean.TypeChecker.etaHoles_true_today_false_of_flip
