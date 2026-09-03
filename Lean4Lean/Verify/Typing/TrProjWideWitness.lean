import Lean4Lean.Verify.Typing.TrProjWide
import Lean4Lean.Verify.TypeChecker.EtaStructG
import Lean4Lean.Verify.Typing.ProjWfWitness

/-!
# Firing witness for the `TrProj` widening, at a genuinely mutual block

A widening needs a **firing** test, not only a collapse test: an instance the old predicate
cannot express and the new one can, with every premise discharged except ones named.  This is
that test for `TrProjG` (`Verify/Typing/TrProjWide.lean`).

The block is `MutField.decl` (`Verify/TypeChecker/EtaStructG.lean`) — `mutual inductive A | mk :
A; inductive B | mk : (f : ∀ p : Prop, p) → B end`, two types, in `Type`, the projected member
`B` at index **`j = 1`**, one field.  At this block:

* `VEnv.IsStructure` is **false for every `T`, `C`** (`MutField.decl_not_isStructure`), so
  `TrProj`'s first field cannot be supplied from `decl` at all, and any `TrProj` derivation for
  the name `MutField.B` would have to certify a *different* block
  (`trProj_at_MutField_needs_other_block`, same file);
* `TrProjG` fires, **with its eleventh field discharged** rather than assumed, through
  `TrProjG.mk'` — i.e. through `VEnv.IsStructureG.projTermG_hasType`
  (`Verify/Typing/ProjGenTerm.lean`).

**The one open premise is `VEnv.WF declEnv`, and it is open for everybody**: nothing in this tree
proves `VEnv.WF` of an environment built by `addInduct'` (that is the keystone, `addDecl.WF`).
The narrow `TrProj.wf`'s own witness `barEnv_TrProj_wf` (`Verify/Typing/ProjWfWitness.lean`)
takes the same hypothesis, so this is not a defect of the widening.  Everything else —
`IsStructureG`, `noRec`, the major premise's typing, the two `HasArgs` spines, the lengths, F17
in its small-elimination branch — is discharged outright.
-/

namespace Lean4Lean
namespace MutField

open VExpr

/-- `B` is a type in `declEnv`. -/
theorem declEnv_B_hasType :
    declEnv.HasType 0 [] (.const `MutField.B []) (.sort (.succ .zero)) :=
  .constDF declEnv_B nofun nofun rfl .nil

/-- The context `(x : B)` is well formed. -/
theorem bCtx_onCtx : OnCtx bCtx (declEnv.IsType 0) :=
  ⟨trivial, _, declEnv_B_hasType⟩

/-- **F17 in the guarded form `TrProjG` records**, at field `0` of `B`'s constructor. -/
theorem bCtor_F17 : decl.isLE = true ∨ ∀ k, k ≤ 0 → (k = 0 ∨ bCtor.FieldUsed decl 0 k) →
    (bCtor.fields.getD k default).lvl.inst [] ≈ .zero :=
  .inr fun k hk _ => bCtor_field_prop k (by rw [bCtor_fields_length]; omega)

/-- **The ten fields, discharged unconditionally**, at the same block.

This is the measurement that prices option (d) exactly: `TrProjG`'s first ten fields — the ones
`TrProj.mk` already has, with `IsStructure` widened and `noRec` re-added — hold at
`MutField.decl` with **no hypothesis at all**, hole-free.  It is the eleventh field, and only the
eleventh, that brings `VEnv.WF declEnv` into `declEnv_trProjG` below.

(Every conjunct is `declEnv_structEtaG_premises`' own, re-associated to `TrProjG.mk`'s order and
with F17 in the `≤ i` form the relation records.) -/
theorem declEnv_trProjG_ten_fields :
    declEnv.IsStructureG `MutField.B decl 1 bTy bCtor ∧
    bCtor.recFields = [] ∧
    declEnv.HasType 0 bCtx (.bvar 0) ((VExpr.const `MutField.B []).mkApp ([] ++ [])) ∧
    ([] : List VLevel).length = decl.uvars ∧
    ([] : List VExpr).length = decl.np ∧
    ([] : List VExpr).length = bTy.indices.length ∧
    0 < bCtor.fields.length ∧
    (∀ l ∈ ([] : List VLevel), l.WF 0) ∧
    declEnv.HasArgs 0 bCtx (decl.params.map (VExpr.instL [])) [] ∧
    declEnv.HasArgs 0 bCtx (VExpr.instAllTele (bTy.indices.map (VExpr.instL [])) []) [] ∧
    (decl.isLE = true ∨ ∀ k, k ≤ 0 → (k = 0 ∨ bCtor.FieldUsed decl 0 k) →
      (bCtor.fields.getD k default).lvl.inst [] ≈ .zero) :=
  ⟨declEnv_IsStructureG, rfl, .bvar (.zero ..), rfl, rfl, rfl,
    by rw [bCtor_fields_length]; omega, nofun, .nil, .nil, bCtor_F17⟩

/-- **The widened relation fires at the second member of a two-type mutual block**, projecting
its one field, with the eleventh field *discharged* by wall 2.

Every premise is discharged except `VEnv.WF declEnv`, which is this tree's keystone. -/
theorem declEnv_trProjG (hwf : VEnv.WF declEnv) :
    TrProjG declEnv 0 bCtx `MutField.B 0 (.bvar 0)
      (decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)) :=
  .mk' hwf bCtx_onCtx declEnv_IsStructureG rfl (.bvar (.zero ..)) rfl rfl rfl
    (by rw [bCtor_fields_length]; omega) nofun .nil .nil bCtor_F17

/-- **The firing, against the old relation, in one statement.**

Conjunct 1: the widened relation holds at `MutField.decl`.
Conjunct 2: the narrow relation's `IsStructure` field is unavailable at that block, for every
`T` and `C` — so conjunct 1 is *not* an instance `TrProj` could have stated with the same data.
Conjunct 3: consequently any `TrProj` derivation for this name would have to certify some other
block (`trProj_at_MutField_needs_other_block`, quoted so the comparison is in one place).

Conjunct 3 is the honest limit of the comparison: `TrProj` at the *name* `MutField.B` is not
refuted outright, because `VEnv.IsStructure` carries no claim that a name belongs to at most one
block — that is ledger G4, and it has no statement in the tree. -/
theorem trProjG_fires_where_trProj_cannot (hwf : VEnv.WF declEnv) :
    TrProjG declEnv 0 bCtx `MutField.B 0 (.bvar 0)
      (decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)) ∧
    (∀ T C, ¬ declEnv.IsStructure `MutField.B decl T C) ∧
    (∀ {U : Nat} {Γ : List VExpr} {i : Nat} {e e' : VExpr},
      TrProj declEnv U Γ `MutField.B i e e' →
        ∃ D T C, declEnv.IsStructure `MutField.B D T C ∧ D ≠ decl) :=
  ⟨declEnv_trProjG hwf, fun _ _ => decl_not_isStructure,
    fun h => trProj_at_MutField_needs_other_block h⟩

/-- …and the term the widening relates `x` to at this block is a genuine `projTermG` at motive
slot `1`, not the degenerate narrow term: it is the entry of the η-expansion
`declEnv_etaExpansionG_eq` already exhibits. -/
theorem declEnv_trProjG_target :
    decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)
      = (VExpr.const `MutField.B.mk []).mkApp
          [decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)] := rfl

end MutField

/-! ## The collapse test, fired at a concrete narrow instance

`TrProj.toG` says every narrow derivation is a wide one.  Here it is at the *only* concrete
`TrProj` derivation in the tree — `barEnv_TrProj` (`Verify/Typing/ProjWfWitness.lean`), the
two-field `structure Bar : Prop` witness, projecting the used field `1` over the unused field
`0`.  The target is the **narrow** term `barDecl.projTerm …`, unchanged: `projTermG … 0` is
`projTerm` on the nose, so the widening does not relabel the object being related.

`VEnv.WF barEnv` is a hypothesis for the reason `barEnv_TrProj_wf` gives: `barEnv` is built by
`addInduct'`, and no lemma in this tree proves `VEnv.WF` of such an environment. -/
theorem barEnv_trProjG (henv : VEnv.WF barEnv) :
    TrProjG barEnv 0 barCtx `Bar 1 (.bvar 0)
      (barDecl.projTerm barType barCtor [] [] [] 1 (.bvar 0)) :=
  TrProj.toG henv barCtx_onCtx barEnv_TrProj

/-- …and `TrProjG.wf` fired on it gives back exactly what `TrProj.wf` gave — with **no**
`VEnv.WF`, **no** `OnCtx` and **no** `VExpr.WF` of the major premise at the `wf` call itself
(they are consumed once, when the derivation is built).  Compare `barEnv_TrProj_wf`. -/
theorem barEnv_trProjG_wf (henv : VEnv.WF barEnv) :
    VExpr.WF barEnv 0 barCtx (barDecl.projTerm barType barCtor [] [] [] 1 (.bvar 0)) :=
  (barEnv_trProjG henv).wf

end Lean4Lean
