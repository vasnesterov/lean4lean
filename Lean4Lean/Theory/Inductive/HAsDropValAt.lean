/-
# `HAsDropValAt`: the `ValAt` clause, stated and supplied at the **Theory** layer

`docs/handoff-restrict.md` §5 item 1 makes `VIndRestore.ValAt D K e₂ e` the entire residual of the
nested transport — *one closed typing per companion member, subject and type companion-free, no
context, no spine, no telescope* — and recommends restating
`docs/handoff-argstyped.md`'s `TrIndDeclN` clause in that weaker form.

Two things block doing that here, and both are recorded in `docs/handoff-hasdrop.md` §3 rather than
worked around:

1. **`ValAt` is defined in the wrong layer.**  It sits at `Verify/Inductive/RestrictCompanion.lean`,
   yet every name in it — `VIndRestore`, `VInductDecl'`, `csubstTy` (`Theory/Inductive/Restore.lean`),
   `VEnv.constants`, `VEnv.HasType` — is `Theory` vocabulary.  `Theory/` may not import `Verify/`,
   so nothing here can *name* `ValAt`.
2. **The clause itself goes on `structure TrIndDeclN`** (`Verify/Environment/InductR.lean`), which
   is neither mine nor `Theory`.

What *can* be done in one file, and is done here: state `ValAt`'s **body** — the identical `∀`, so a
`ValAt` goal is closed by `exact` on delta-unfolding — and supply it from the datum
`Theory/Inductive/HargsShared.lean` §6 already reduces the four consumption sites to.  So the answer
to "does the weaker form actually supply the consumers" is *yes at the Theory layer, from `hargs` in
`HasArgs` form*, and the two edits above are the whole remaining distance.

**The boundary, measured**: this cannot be run hypothesis-free at `ntreeAux`.  The datum is
inhabited there only in *applied* form (`HargsShared.lean` §7's `ntree_spineTypedAt_ty_inhabited`),
and getting from applied form back to `HasArgs` is `VEnv.HasArgs.of_mkApp`, which this corner is
deliberately without.  That is the same wall `tyVal_hasType_of_spineTyped` pays for, and it is why
§2 below is arity-`hargs` rather than arity 0.
-/
import Lean4Lean.Theory.Inductive.HargsShared

namespace Lean4Lean

open Lean (Name)

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-! ## §1 `ValAt`'s body, from the `HasArgs` datum

`HargsShared.lean` §6's `tyVal_hasType_of_hargs` gives one member's typing; this is the
bookkeeping that turns "one per member" into the substitution-indexed form
`VEnv.CSubst.WF`'s `val` field — and therefore `VIndRestore.ValAt` — is stated in:
`csubstTy_dom` names the member behind a domain entry, and `addConstList_constants` pins the
declared constant the lookup returns.

Note which environment each hypothesis lives at: `hfa`/`hargs` at `env` (the pre-block
environment `Faithful` is about), the lookup at `E₂ = env.addIndTypes D`, and the conclusion at
any `F ≥ env` where the parameters are types. -/

/-- **`VIndRestore.ValAt D K E₂ F`, spelled out.**  Definitionally the `ValAt` of
`Verify/Inductive/RestrictCompanion.lean`, which `Theory/` cannot name; `exact` closes a `ValAt`
goal with it. -/
theorem valAt_of_hargs {env E₂ F : VEnv} {npJ : Nat → Nat}
    (hfa : R.Faithful D env K npJ) (hle : env ≤ F)
    (hparams : OnCtx D.params.reverse (F.IsType D.uvars))
    (h₂ : env.addIndTypes D = some E₂)
    (hlvl : ∀ j : Nat, ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hargs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        F.HasArgs D.uvars D.params.reverse (R.declTele ci (npJ j) j) (R.tyArgs j)) :
    ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = some t →
      E₂.constants c = some ci → F.HasType ci.uvars [] t ci.type := by
  intro c t ci hd hc
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := VIndRestore.csubstTy_dom hd
  have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConsts :=
    List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩
  rw [VEnv.addIndTypes] at h₂
  rw [VEnv.addConstList_constants h₂ _ hmem] at hc
  cases hc
  exact tyVal_hasType_of_hargs hfa hle hparams hT hK (hlvl j) (hargs j T hT hK)

/-! ## §2 The collapse test

At `K = []` the body is vacuous — `csubstTy` is the identity substitution and its domain is empty
(`Verify/Inductive/RestrictCompanion.lean`'s `valAt_nil` says the same one layer up).  So all of
§1's content lives at `K ≠ []`, which is where both of the tree's nested witnesses are.  Recorded
because a supplier that also holds at `K = []` for the trivial reason would grade itself against a
criterion that cannot fail. -/

theorem valAt_body_nil {E₂ F : VEnv} :
    ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D [] c = some t →
      E₂.constants c = some ci → F.HasType ci.uvars [] t ci.type := by
  intro c t ci hd _
  rw [VIndRestore.csubstTy_nil] at hd
  exact absurd hd (by simp [CSubst.id])

/-! ## §3 …and the non-degenerate side: at `ntreeK` the domain is NOT empty

The complement of §2 at the canonical parameterised nested block: the substitution really does
replace a constant, so §1 at `ntreeAux` is not the vacuous statement §2 is. -/

end VIndRestore

namespace InductiveDeclExamples

/-- `ntreeK ≠ []`, so §2's collapse does not apply at the canonical block. -/
theorem ntreeK_ne_nil : ntreeK ≠ [] := by decide

/-- …and the companion member really is in `csubstTy`'s domain, at index `1`. -/
theorem ntree_csubstTy_dom_ne_none :
    ntreeRestore.csubstTy ntreeAux ntreeK (ntreeAux.types.getD 1 default).name ≠ none := by
  decide

end InductiveDeclExamples

/-! ## §4 Axiom audit — hole-freeness only.  Inhabitation is the header's boundary note. -/

#print axioms Lean4Lean.VIndRestore.valAt_of_hargs
#print axioms Lean4Lean.VIndRestore.valAt_body_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntreeK_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_csubstTy_dom_ne_none

end Lean4Lean
