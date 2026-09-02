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
second type.

## 4. The minimum convention does not work — and the obstruction is one goal

The weakening this file was expected to enable — replace the `↔` by "*some*
sort of `A` evaluates to `0`", and let `U_mono` absorb a `Prop` branch taken
against a non-zero sort — **fails**, and the reason is worth stating precisely
because the first two thirds of the argument are right.

`U_mono` does absorb the **formation** obligation: the `Prop` branch produces
`piProp ∈ U κ 0`, and `U κ 0 ⊆ U κ k` gives membership at whatever index the
rule names.  That much of the analysis holds.

What it cannot absorb is **parts 1 and 2**.  `propSound_of_mem_sort`
(`SetModel/InterpSound.lean`) turns `⟦e⟧ρ ∈ ⟦.sort u⟧ρ` into `⟦e⟧ρ ⊆ {•}` and
its hypothesis `u.eval M.ls = 0` is load-bearing — dropping it leaves exactly

```
h : ⟦e⟧ρ ∈ U M.κ (u.eval M.ls)
⊢ ⟦e⟧ρ ⊆ {pt}
```

which is the **downward** inclusion.  `U_mono` moves memberships *up*; nothing
moves them down.  And `Sound.proof` — part 2, consumed by `appDF`, `lamDF`,
`beta` and `eta` — takes `Sound M L Γ A A' (.sort u)` together with
`u.eval M.ls = 0`, where the `Sound` for the type is the induction hypothesis
**at the sort the premise names**.  If the split says "proof" while that sort is
non-zero, the witness sort's soundness is simply not in scope: the induction
supplies one `Sound` per premise, not one per sort the type happens to have.

So the `⇒` direction of `prop_sound`/`proof_sound` is not decoration, and
`PropSplit`'s `↔`-form is the weakest form the present soundness induction can
run on.  **The model's syntactic import is therefore both statements above, not
`PropTypeAgree` alone.**  Both remain strictly weaker than `SortUniq`, which is
what step 1 bought; `PropUniq` is reached by the cumulativity check and so, like
`SortUniq`, needs a syntactic proof.

*What would remove `PropUniq`*, for whoever prices it: strengthening `Sound` to
quantify over **all** types of a term rather than the one its premise names —
which is close to assuming the uniqueness it is trying to avoid — or deciding
the `forallE` branch semantically (`⟦B⟧ρ ⊆ {•}` pointwise, a definable test).
The second is a real option for `forallE` congruence but does **not** help parts
1 and 2, which are about `lam`/`app` terms whose *type* is a proposition.  It is
not a small change and it is not scoped here.
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

/-! ### The `OnCtx`-guarded companions

Moved here from `SetModel/NotProofNoModel.lean` on 2026-09-02, when `PropSplit`'s two fields
acquired the same guard: these are now the *inputs* of `propSplitOfOnCtx` below, so they have
to be in scope where the structure is built rather than three files later.  Their producers
(`VEnv.WF.propTypeAgreeOn`, `WF.propUniqOn`, and the stratified route
`PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`) stay where they are. -/

/-- **`PropTypeAgree`, guarded by `OnCtx`.**  The form every unique-typing result in the
tree can supply — every one of them carries `OnCtx Γ (env.IsType U)`, because
`IsDefEq.strong`'s `CtxStrong` *is* "every entry is a type" — and, since 2026-09-02, the
form `PropSplit.proof_sound` asks for. -/
def PropTypeAgreeOnCtx (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} {ls : List ℕ},
    OnCtx Γ (env.IsType nv) → u.WF nv → u'.WF nv →
    env.HasType nv Γ e A → env.HasType nv Γ e A' →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

/-- **`PropUniq`, guarded by `OnCtx`** — the companion import, and what
`PropSplit.prop_sound` asks for. -/
def PropUniqOnCtx (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u v : VLevel} {ls : List ℕ},
    OnCtx Γ (env.IsType nv) → u.WF nv → v.WF nv →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A (.sort v) →
    (u.eval ls = 0 ↔ v.eval ls = 0)

/-- The unguarded statements are stronger: forget the guard. -/
theorem PropTypeAgree.onCtx {env : VEnv} {nv : ℕ} (h : env.PropTypeAgree nv) :
    env.PropTypeAgreeOnCtx nv := fun _ => h

/-- The unguarded statements are stronger: forget the guard. -/
theorem PropUniq.onCtx {env : VEnv} {nv : ℕ} (h : env.PropUniq nv) :
    env.PropUniqOnCtx nv := fun _ => h

end VEnv

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 2. Both branches fire

Both instances now have to exhibit the `OnCtx` guard `PropSplit`'s fields carry.  `[]` is
`trivial`; `[.sort .zero]` is the one-line lemma below, and it is worth noting that this is
the *`bvar` instance* — the shape that refuted the unguarded `LevelAssign` — so the guard has
not made the "both branches fire" check vacuous. -/

/-- `[Prop]` is an `OnCtx`-well-formed context, at every environment. -/
theorem onCtx_sortZero {env : VEnv} {nv : ℕ} :
    OnCtx [(VExpr.sort .zero)] (env.IsType nv) :=
  ⟨trivial, .succ .zero, VEnv.HasType.sort trivial⟩

section RealWork

variable {env : VEnv} {nv : ℕ} (L : PropSplit env nv) (ls : List ℕ)

include L in
/-- `Prop` itself is **not** a proposition, in any `PropSplit`. -/
theorem prop_forces_false : ¬ L.IsPropAt ls [] (.sort .zero) := by
  have h : env.HasType nv [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF (by trivial) (by trivial) rfl
  rw [L.prop_sound (Γ := []) (u := .succ .zero) trivial (by trivial) h]
  simp [VLevel.eval]

include L in
/-- A variable of type `Prop` **is** a proposition, in any `PropSplit`.  Note
this is a genuine `bvar` instance — the shape that refuted the unguarded
`LevelAssign`. -/
theorem prop_forces_true : L.IsPropAt ls [.sort .zero] (.bvar 0) := by
  have h : env.HasType nv [.sort .zero] (.bvar 0) (.sort .zero) :=
    VEnv.IsDefEq.bvar .zero
  rw [L.prop_sound (u := .zero) onCtx_sortZero (by trivial) h]
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
  prop_sound _ hw ht :=
    ⟨fun ⟨_, hw', ht', h0⟩ ↦ (hU hw' hw ht' ht).mp h0, fun h0 ↦ ⟨_, hw, ht, h0⟩⟩
  proof_sound _ hw he hA :=
    ⟨fun ⟨_, _, hw', he', hA', h0⟩ ↦ (hT hw' hw he' he hA' hA).mp h0,
      fun h0 ↦ ⟨_, _, hw, he, hA, h0⟩⟩

/-! ### The unguarded instance keeps its unguarded soundness

`propSplitOf`'s two predicates are pinned by `hU`/`hT` at **every** `Γ`, so the instance it
builds satisfies the *pre-2026-09-02* (unguarded) form of the two fields as well.  Stated
separately because the fields themselves no longer say so, and `SetModel/PropSplitUp.lean`'s
comparison lemmas are about this instance rather than about an arbitrary `PropSplit`. -/

theorem propSplitOf_isPropAt_iff {env : VEnv} {nv : ℕ} {hU : env.PropUniq nv}
    {hT : env.PropTypeAgree nv} {ls : List ℕ} {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hw : u.WF nv) (ht : env.HasType nv Γ A (.sort u)) :
    (propSplitOf env nv hU hT).IsPropAt ls Γ A ↔ u.eval ls = 0 :=
  ⟨fun ⟨_, hw', ht', h0⟩ ↦ (hU hw' hw ht' ht).mp h0, fun h0 ↦ ⟨_, hw, ht, h0⟩⟩

theorem propSplitOf_isProofAt_iff {env : VEnv} {nv : ℕ} {hU : env.PropUniq nv}
    {hT : env.PropTypeAgree nv} {ls : List ℕ} {Γ : List VExpr} {e A : VExpr} {u : VLevel}
    (hw : u.WF nv) (he : env.HasType nv Γ e A) (hA : env.HasType nv Γ A (.sort u)) :
    (propSplitOf env nv hU hT).IsProofAt ls Γ e ↔ u.eval ls = 0 :=
  ⟨fun ⟨_, _, hw', he', hA', h0⟩ ↦ (hT hw' hw he' he hA' hA).mp h0,
    fun h0 ↦ ⟨_, _, hw, he, hA, h0⟩⟩

/-- **The audit's conclusion.**  `PropSplit` is satisfiable for every
environment whose judgement satisfies the two agreement statements — so it is
not unsatisfiable for a structural reason, and what remains to be established is
a fact about the typing relation rather than about this structure. -/
theorem exists_propSplit {env : VEnv} {nv : ℕ}
    (hU : env.PropUniq nv) (hT : env.PropTypeAgree nv) : Nonempty (PropSplit env nv) :=
  ⟨propSplitOf env nv hU hT⟩

/-! ## 3′. The **guarded** lower bound — the one that is discharged at a named environment

Added 2026-09-02 together with the `OnCtx` guard on `PropSplit`'s fields.  This is the
version that matters: `propSplitOf` above takes the *unguarded* statements, and
`docs/vacuity-ledger.md` rows 130b/131 record that those are nobody's target — the whole
syntactic development produces the guarded forms, because `IsDefEq.strong` needs the
context's entries to be types.  With the guard on the fields, the same construction runs on
the guarded inputs verbatim: the predicates are unchanged, and every use of `hU`/`hT` inside
`propSplitOf` happens at the `Γ` the field was handed, whose guard the field now supplies. -/

/-- **The natural assignment, from the guarded statements.**  Same predicates as
`propSplitOf`; the `OnCtx` the fields now carry is exactly what feeds `hU`/`hT`. -/
noncomputable def propSplitOfOnCtx (env : VEnv) (nv : ℕ)
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv) : PropSplit env nv where
  IsPropAt ls Γ A := ∃ u : VLevel, u.WF nv ∧ env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0
  IsProofAt ls Γ e := ∃ (A : VExpr) (u : VLevel), u.WF nv ∧ env.HasType nv Γ e A ∧
    env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0
  decProp _ _ _ := Classical.propDecidable _
  decProof _ _ _ := Classical.propDecidable _
  prop_sound hΓ hw ht :=
    ⟨fun ⟨_, hw', ht', h0⟩ ↦ (hU hΓ hw' hw ht' ht).mp h0, fun h0 ↦ ⟨_, hw, ht, h0⟩⟩
  proof_sound hΓ hw he hA :=
    ⟨fun ⟨_, _, hw', he', hA', h0⟩ ↦ (hT hΓ hw' hw he' he hA' hA).mp h0,
      fun h0 ↦ ⟨_, _, hw, he, hA, h0⟩⟩

/-- **The audit's conclusion, guarded.**  `PropSplit` is inhabited at every environment
satisfying the two *guarded* agreement statements — which, unlike the unguarded ones, the
tree proves (`VEnv.WF.propTypeAgreeOn`, `WF.propUniqOn`, and hole-free from the stratified
side by `PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`). -/
theorem exists_propSplit_onCtx {env : VEnv} {nv : ℕ}
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv) :
    Nonempty (PropSplit env nv) :=
  ⟨propSplitOfOnCtx env nv hU hT⟩

end SetModel

end Lean4Lean
