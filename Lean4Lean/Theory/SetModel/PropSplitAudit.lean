import Lean4Lean.Theory.SetModel.Interp

/-!
# The satisfiability audit for `PropSplit`

**Run before anything is built on the new parameter, not after.**
`SetModel/LevelAssignUnsat.lean` machine-checks that the unguarded analogue of
`LevelAssign`'s condition is unsatisfiable *for every environment*, for a
junk-context reason having nothing to do with the mathematics — and a structure
refuted that way makes everything above it vacuous while every proof stays
green.  `PropSplit` is a new structure over the same syntax, so it gets the same
audit.

Three checks, in the order they answer the question.

## 1. Upper bound — it asks for nothing new

`LevelAssign.toPropSplit` (`SetModel/Interp.lean`) builds a `PropSplit` from a
`LevelAssign`.  So the re-parameterisation cannot have strengthened the model's
hypothesis; whatever was true of the old parameter is available for the new one.
There is deliberately **no converse**: a propositionhood predicate does not
determine a level, and that is the whole content of the weakening.

## 2. The fields do real work — no constant predicate satisfies them

`prop_forces_false` and `prop_forces_true` exhibit one instance of each branch,
from `prop_sound` alone.  Together they rule out the degenerate assignments
(`fun _ _ _ ↦ True`, `fun _ _ _ ↦ False`) — a structure both of those satisfy is
not saying anything, and this is the check `PreludeSpec.lean` runs on its own
witnesses for the same reason.

## 3. Lower bound — satisfiability reduces to two named syntactic statements

`propSplitOf` constructs a `PropSplit` from

* `PropUniq` — the sorts of a **type** agree on being zero, and
* `PropTypeAgree` — the types of a **term** agree on being propositions,

by the obvious assignment: a type is a proposition when *some* sort of it
evaluates to `0`.  So `PropSplit` is satisfiable exactly when those hold; it
cannot be vacuous for a structural reason, and any remaining doubt is about a
statement of the *judgement*, which is where it belongs.

**Why these two and not `SortUniq`.**  `Theory/Typing/SortUniq.lean` shows
`SortUniq` is not a semantic consequence: add cumulativity, which every
nested-universe model validates, and it fails.  That check reaches `PropUniq`
too — a proposition then has sorts `0` and `1`.  It does **not** reach
`PropTypeAgree`: cumulativity retypes at *sorts*, and never gives a proof a
second type.  So of the two hypotheses here, one is a casualty of the same check
and one is not — which is exactly the split `docs/model-interface.md` §5 uses to
say that the minimum convention (a type is a proposition when *some* sort of it
is zero, with `U_mono` absorbing the difference) would leave `PropTypeAgree` as
the sole syntactic import.  **That weakening is measured, not built**; this file
audits the `↔`-form that is in the tree.
-/

namespace Lean4Lean

namespace VEnv

/-- **The sorts of a type agree on being zero.**  Strictly weaker than
`SortUniq` (which forces the levels equivalent), and strictly stronger than
nothing: it is what the `↔` form of `PropSplit.prop_sound` needs.

Refuted by the cumulativity check of `Theory/Typing/SortUniq.lean`, and that is
why the minimum convention exists. -/
def PropUniq (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u v : VLevel} {ls : List ℕ}, u.WF nv → v.WF nv →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A (.sort v) →
    (u.eval ls = 0 ↔ v.eval ls = 0)

/-- **The types of a term agree on being propositions.**

This is the model's irreducible syntactic import: if a term had a `Prop` type
and a non-`Prop` type, its denotation would have to be `•` and to lie in a
non-`Prop` denotation — a different set, not a bigger universe, so nothing
absorbs it.

`Theory/Typing/SortUniq.lean`'s `sort_not_proof` is this statement at
`e = .sort u`, its two types being `.sort (u+1)` and the proposition `p`. -/
def PropTypeAgree (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} {ls : List ℕ}, u.WF nv → u'.WF nv →
    env.HasType nv Γ e A → env.HasType nv Γ e A' →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

end VEnv

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 2. Both branches fire -/

section RealWork

variable {env : VEnv} {nv : ℕ} (L : PropSplit env nv) (ls : List ℕ)

include L in
/-- `Prop` itself is **not** a proposition, in any `PropSplit`. -/
theorem prop_forces_false : ¬ L.IsPropAt ls [] (.sort .zero) := by
  have h : env.HasType nv [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF (by trivial) (by trivial) rfl
  rw [L.prop_sound (u := .succ .zero) (by trivial) h]
  simp [VLevel.eval]

include L in
/-- A variable of type `Prop` **is** a proposition, in any `PropSplit`.  Note
this is a genuine `bvar` instance — the shape that refuted the unguarded
`LevelAssign`. -/
theorem prop_forces_true : L.IsPropAt ls [.sort .zero] (.bvar 0) := by
  have h : env.HasType nv [.sort .zero] (.bvar 0) (.sort .zero) :=
    VEnv.IsDefEq.bvar .zero
  rw [L.prop_sound (u := .zero) (by trivial) h]
  simp [VLevel.eval]

include L in
/-- Consequently no constant predicate is a `PropSplit`: the two instances above
disagree.  This is the check that keeps the parameter from being satisfied by
saying nothing. -/
theorem propSplit_not_constant :
    ¬ ∀ (Γ : List VExpr) (A : VExpr) (Γ' : List VExpr) (A' : VExpr),
        L.IsPropAt ls Γ A ↔ L.IsPropAt ls Γ' A' :=
  fun h ↦ prop_forces_false L ls ((h _ _ _ _).mpr (prop_forces_true L ls))

end RealWork

/-! ## 3. Satisfiability, reduced -/

/-- **The natural assignment**: a type is a proposition when *some* sort of it
evaluates to `0`, and a term is a proof when *some* type of it is one.  Total,
and classically decidable; no choice of levels is involved. -/
noncomputable def propSplitOf (env : VEnv) (nv : ℕ)
    (hU : env.PropUniq nv) (hT : env.PropTypeAgree nv) : PropSplit env nv where
  IsPropAt ls Γ A := ∃ u : VLevel, u.WF nv ∧ env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0
  IsProofAt ls Γ e := ∃ (A : VExpr) (u : VLevel), u.WF nv ∧ env.HasType nv Γ e A ∧
    env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0
  decProp _ _ _ := Classical.propDecidable _
  decProof _ _ _ := Classical.propDecidable _
  prop_sound hw ht :=
    ⟨fun ⟨_, hw', ht', h0⟩ ↦ (hU hw' hw ht' ht).mp h0, fun h0 ↦ ⟨_, hw, ht, h0⟩⟩
  proof_sound hw he hA :=
    ⟨fun ⟨_, _, hw', he', hA', h0⟩ ↦ (hT hw' hw he' he hA' hA).mp h0,
      fun h0 ↦ ⟨_, _, hw, he, hA, h0⟩⟩

/-- **The audit's conclusion.**  `PropSplit` is satisfiable for every
environment whose judgement satisfies the two agreement statements — so it is
not unsatisfiable for a structural reason, and what remains to be established is
a fact about the typing relation rather than about this structure. -/
theorem exists_propSplit {env : VEnv} {nv : ℕ}
    (hU : env.PropUniq nv) (hT : env.PropTypeAgree nv) : Nonempty (PropSplit env nv) :=
  ⟨propSplitOf env nv hU hT⟩

end SetModel

end Lean4Lean
