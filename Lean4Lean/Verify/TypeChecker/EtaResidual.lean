import Lean4Lean.Verify.TypeChecker.UnitEta
import Lean4Lean.Verify.TypeChecker.EtaStructG

/-!
# The two eta holes, reduced to **one** abstract rule

`Verify/TypeChecker/IsDefEq.lean` carries two `sorry`s, `tryEtaStructCore.WF` and
`isDefEqUnitLike.WF`.  Two rounds of work turned each into a conditional theorem with **two**
hypotheses — an abstract eta rule and a kernel→abstract bridge:

| hole | conditional theorem | hypotheses |
|---|---|---|
| `tryEtaStructCore.WF` | `WF_of_structEtaGC` (`EtaStructG.lean`) | `c.venv.StructEtaG`, `EtaStructSpineGC c e₁ e₂ e₁' e₂'` |
| `isDefEqUnitLike.WF` | `WF_of_unitEta` (`UnitEta.lean`) | `c.venv.UnitEta`, `UnitLikeBridgeG c` |

This file removes three of those four, leaving **one**:

1. `EtaStructSpineGC.today` (`EtaStructG.lean`) already discharges the first bridge from the
   theorem's own `he₂`.  The zero-field bridge had no counterpart, so
   `UnitLikeBridgeG.today` below supplies it — same route, `TrEnv.not_inductInfo` in place of
   `TrEnv.not_ctorInfo`, hole-free.
2. `VEnv.StructEtaG.toUnitEta` discharges `UnitEta` from `StructEtaG`.  `StructEtaG.unitLike`'s
   docstring already claims the subsumption ("the two widenings are one rule, not two competing
   ones"); this is that claim as a theorem, and it is what lets **one** rule serve both holes.

The result is `isDefEqUnitLike.WF_of_structEtaG` and `tryEtaStructCore.WF_of_structEtaG'`:
**both holes follow, today, from the single hypothesis `c.venv.StructEtaG` and nothing else.**

**What that is and is not.**  It is not a close: `StructEtaG` is an addition to the abstract
theory (surjective pairing, which no combination of `VEnv.IsDefEq`'s 13 constructors gives — see
`docs/research-structeta.md` §2), and nothing in this tree discharges it for a translated
`venv`.  It *is* a statement of the residual with no slack left in it: one predicate, whose
premises are satisfiable at exactly the block shape the checker fires at
(`MutField.declEnv_structEtaG_premises`), for two holes with 70 and 71 transitive users.

**Anti-vacuity, for the new implication specifically.**  `toUnitEta` would be worthless if the
`UnitEta` it produces were only ever instantiated at premises nothing satisfies.  The last
section instantiates it at `MutField.declEnv` — a **two-type mutual block in `Type`**, at its
zero-field member — and fires it: `declEnv_unitEta_of_structEtaG` and
`declEnv_unitLike_of_structEtaG` produce specific `IsDefEq`s between syntactically distinct
terms, from `declEnv.StructEtaG` alone.  `MutField.decl_not_isStructure` is the matching
negative: the *narrow* rule `VEnv.StructEta` cannot even be stated there.
-/

namespace Lean4Lean

open VExpr

/-! ## One rule for both holes -/

namespace VEnv.StructEtaG

variable {env : VEnv}

/-- **`StructEtaG` subsumes `UnitEta`.**

At `C.fields = []` the two rules' right-hand sides are the same term
(`etaExpansionG_of_no_fields`), `C.recFields = []` comes free
(`VIndCtor.recFields_of_fields_nil`), and the F17 clause is vacuous.  So the zero-field rule is
an instance of the positive-field one and the two widenings are a single abstract addition.

Together with `StructEtaG.toStructEta` this makes `StructEtaG` the top of the three:
`StructEtaG → StructEta` and `StructEtaG → UnitEta`, both by dropping to a special case with no
side condition left over. -/
theorem toUnitEta (H : env.StructEtaG) : env.UnitEta := by
  intro U Γ S D j T C us ps e hS hidx hnf hus husWF hps hpsA he
  have h := H hS hidx (VIndCtor.recFields_of_fields_nil hnf) hus husWF hps hpsA he
    (.inr (by simp [hnf]))
  rwa [D.etaExpansionG_of_no_fields T C us hnf] at h

end VEnv.StructEtaG

namespace TypeChecker.Inner
open Lean hiding Environment Exception

variable {e₁ e₂ : Expr} {e₁' e₂' : VExpr}

/-- **The zero-field bridge is satisfiable today, vacuously** — the counterpart of
`EtaStructSpineGC.today`, and established rather than asserted (`docs/vacuity-ledger.md` §0,
blindness 4: an unproved claim of vacuity is worth nothing).

The route is `isDefEqUnitLike_never_true`'s: the bridge's own first premise translates `tType`,
whose head is `.const I ls`, so `c.venv.constants I` is populated, and `TrEnv.not_inductInfo`
then forbids `c.env.find? I` from answering `.inductInfo` while `AddInduct` is empty.  So the
bridge's third premise is refuted and every instance is vacuous.

**Read the polarity.**  `UnitLikeBridgeG` is a *hypothesis* of
`isDefEqUnitLike.WF_of_unitEta`, so proving it here removes it from the residual outright — and
what remains, `c.venv.UnitEta`, is not vacuous in the same way: it is an abstract rule with
satisfiable premises (`MutNonRec.decl2Env_unitEta_premises`) that nothing discharges.  When
`AddInduct` gains constructors this theorem goes red, exactly as
`isDefEqUnitLike_never_true` and `EtaStructSpineGC.today` do, and the bridge becomes real work
again.  That is why `WF_of_unitEta` is kept as the theorem with the bridge explicit: it survives
the flip, this does not. -/
theorem UnitLikeBridgeG.today {c : VContext} : UnitLikeBridgeG c := by
  intro _ _ _ _ _ _ _ htT hhead hci _ _ _ _ _
  obtain ⟨f', hf⟩ := head_tr htT
  rw [hhead] at hf
  let .const hc _ _ := hf
  exact absurd hci fun hh => c.trenv.not_inductInfo ⟨_, hc⟩ hh

/-- **`isDefEqUnitLike.WF` from `c.venv.StructEtaG` alone.**

`WF_of_unitEta` (`UnitEta.lean`) with both of its hypotheses reduced: `UnitEta` by
`StructEtaG.toUnitEta`, the bridge by `UnitLikeBridgeG.today`.  So the entire distance between
`isDefEqUnitLike.WF` and a proof is the abstract rule.

Its axiom set and hole cone are `WF_of_unitEta`'s — the four borrowed holes of `inferType.WF`
(`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend`) and no others;
neither ingredient adds one. -/
theorem isDefEqUnitLike.WF_of_structEtaG {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') (hSE : c.venv.StructEtaG) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
  isDefEqUnitLike.WF_of_unitEta he₁ he₂ hSE.toUnitEta UnitLikeBridgeG.today

/-- **`tryEtaStructCore.WF` from `c.venv.StructEtaG` alone.**

`WF_of_structEtaGC` (`EtaStructG.lean`) with its bridge discharged by `EtaStructSpineGC.today`,
which needs exactly the `he₂` this statement already has.

Same warning as `EtaStructSpineGC.today` carries: the bridge is discharged *vacuously*, so this
theorem is the one that goes red at the `AddInduct` flip while `WF_of_structEtaGC` survives it.
What the pair establishes is that the residual today is one hypothesis, not two — not that the
bridge is free in general. -/
theorem tryEtaStructCore.WF_of_structEtaG' {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') (hSE : c.venv.StructEtaG) :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  tryEtaStructCore.WF_of_structEtaGC he₁ he₂ hSE (EtaStructSpineGC.today he₂)

/-- **Both holes, from one hypothesis, side by side.**  Stated as a conjunction so that the
"one rule closes both" claim is a single theorem rather than a reading of two.  `tryEtaStruct`
is included because it is `tryEtaStructCore`'s only consumer and needs the rule at both argument
orders. -/
theorem etaHoles_of_structEtaG {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') (hSE : c.venv.StructEtaG) :
    RecM.WF c s (tryEtaStructCore e₁ e₂) (fun b _ => b → c.IsDefEqU e₁' e₂') ∧
    RecM.WF c s (tryEtaStruct e₁ e₂) (fun b _ => b → c.IsDefEqU e₁' e₂') ∧
    RecM.WF c s (isDefEqUnitLike e₁ e₂) (fun b _ => b = .true → c.IsDefEqU e₁' e₂') :=
  ⟨tryEtaStructCore.WF_of_structEtaG' he₁ he₂ hSE,
   by
     simp [tryEtaStruct, orM, toBool]
     refine (tryEtaStructCore.WF_of_structEtaG' he₁ he₂ hSE).bind fun _ _ _ h => ?_
     split <;> [exact .pure fun _ => h rfl; skip]
     exact (tryEtaStructCore.WF_of_structEtaG' he₂ he₁ hSE).mono fun _ _ _ h hb => (h hb).symm,
   isDefEqUnitLike.WF_of_structEtaG he₁ he₂ hSE⟩

end TypeChecker.Inner

/-! ## Anti-vacuity for `toUnitEta`: the derived rule fires at a two-type mutual block

`StructEtaG.toUnitEta` is an implication between two predicates, so it is green whether or not
either side is ever satisfiable.  This section instantiates the conclusion at
`MutField.declEnv` — the two-type mutual block in `Type` of `EtaStructG.lean`, whose narrow
`VEnv.IsStructure` is refuted (`MutField.decl_not_isStructure`) — at its **zero-field** member
`A`, and fires the derived rule there.

`MutField.decl` is the right witness for this and `MutNonRec.decl2` is not: `decl` carries a
field on its *other* member, so a single `StructEtaG` assumption is being used at both arities
of the same block. -/

namespace MutField

/-- `IsStructureG` at the **zero-field** member of the block.  `declEnv_IsStructureG`
(`EtaStructG.lean`) is the same at index `1`, the member with the field. -/
theorem declEnv_IsStructureG_0 : declEnv.IsStructureG `MutField.A decl 0 aTy aCtor where
  types := rfl
  name := rfl
  ctors := rfl
  decl := ⟨.empty, declEnv, decl_WF, declEnv_eq.choose_spec, VEnv.LE.rfl⟩

/-- The context `(x : A)`. -/
def aCtx : List VExpr := [.const `MutField.A []]

theorem declEnv_A : declEnv.constants `MutField.A = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addInduct'_types (T := aTy) declEnv_eq.choose_spec (by simp [decl])

/-- **Every premise of `VEnv.UnitEta`, satisfied at once, at the zero-field member of the
two-type block** — the audit `MutNonRec.decl2Env_unitEta_premises` performs at a block with no
fields anywhere, performed here at a block that *does* have one. -/
theorem declEnv_unitEta_premises :
    declEnv.IsStructureG `MutField.A decl 0 aTy aCtor ∧
    aTy.indices = [] ∧
    aCtor.fields = [] ∧
    ([] : List VLevel).length = decl.uvars ∧
    (∀ l ∈ ([] : List VLevel), l.WF 0) ∧
    ([] : List VExpr).length = decl.np ∧
    declEnv.HasArgs 0 aCtx (decl.params.map (VExpr.instL [])) [] ∧
    declEnv.HasType 0 aCtx (.bvar 0) ((VExpr.const `MutField.A []).mkApp []) ∧
    decl.types.length = 2 ∧ bCtor.fields.length = 1 :=
  ⟨declEnv_IsStructureG_0, rfl, rfl, rfl, nofun, rfl, .nil, .bvar (.zero ..), rfl, rfl⟩

/-- **The derived zero-field rule, fired from the positive-field one**: `x ≡ A.mk` for `x : A`,
`A` the zero-field member of a two-type mutual block, from `declEnv.StructEtaG` alone.

This is the check that `toUnitEta` lands somewhere: had the derivation needed a premise the
zero-field case cannot supply, this would not typecheck. -/
theorem declEnv_unitEta_of_structEtaG (H : declEnv.StructEtaG) :
    declEnv.IsDefEq 0 aCtx (.bvar 0) (.const `MutField.A.mk []) (.const `MutField.A []) :=
  H.toUnitEta (us := []) (ps := []) declEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil
    (.bvar (.zero ..))

/-- …and the consequence `isDefEqUnitLike` reports: any two inhabitants of `A` are
definitionally equal, from the same single assumption. -/
theorem declEnv_unitLike_of_structEtaG (H : declEnv.StructEtaG) :
    declEnv.IsDefEq 0 (.const `MutField.A [] :: aCtx) (.bvar 0) (.bvar 1)
      (.const `MutField.A []) :=
  VEnv.UnitEta.unitLike H.toUnitEta (us := []) (ps := []) declEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil
    (.bvar (.zero ..)) (.bvar (.succ (.zero ..)))

theorem declEnv_Amk : declEnv.constants `MutField.A.mk = some ⟨0, .const `MutField.A []⟩ :=
  VEnv.addInduct'_ctors (C := aCtor) (j := 0) declEnv_eq.choose_spec
    (by simp [VInductDecl'.ctorsAll, decl, aTy, aCtor, bTy])

/-- The right-hand side is well typed at the witness, so the fired instance is not satisfied by
an ill-typed conclusion (`VEnv.IsDefEq` implies both sides typed, so an ill-typed right-hand
side would make the rule *false* there rather than merely useless). -/
theorem declEnv_Amk_hasType :
    declEnv.HasType 0 aCtx ((VExpr.const `MutField.A.mk []).mkApp [])
      ((VExpr.const `MutField.A []).mkApp []) :=
  .constDF declEnv_Amk nofun nofun rfl .nil

end MutField

end Lean4Lean
