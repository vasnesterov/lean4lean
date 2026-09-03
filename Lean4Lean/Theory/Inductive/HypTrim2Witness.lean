import Lean4Lean.Theory.Inductive.NestedHead
import Lean4Lean.Theory.Typing.ConstSubstNested

/-!
# The second round of `include`-group trims, instantiated

Three `Theory`-side theorems carried a hypothesis their proofs never use:

| theorem | file | removed |
| --- | --- | --- |
| `ntree_const_staged` | `Theory/Inductive/NestedHead.lean` | `h : VEnv.empty.addInduct' listDecl = some env₁` |
| `nlist_const_staged` | same | same |
| `nfnF₂_ordered` | `Theory/Typing/ConstSubstNested.lean` | `hE₂ : E₁.addIndCtors nfnAux = some E₂` |

**Correcting the previous round's account of the mechanism.**  `docs/handoff-hyptrim.md` says
Lean's `linter.unusedSectionVars` "fires only for *automatically* included variables" and that
"an explicit `include` suppresses it".  That is **false**: the linter fires under a bare
`include` and under `include … in` alike, it fired on all three theorems above, and it had
already fired on `VIndRestore.substC_tyAppR` — the previous round's own headline instance —
inside `lake build`'s ordinary output before that round began.  The defect class was never
invisible; the *warning stream* was unread.  See `docs/handoff-hyptrim2.md` §1.

Removing a `Prop` hypothesis cannot turn a true statement false, so the risk of a trim is that
what remains is **vacuous**.  Below, each trim gets a witness, and the two `NestedHead` ones get
the strong form: an instance at a point where the **removed** hypothesis is provably refuted, so
the untrimmed lemma had no instance there at all.

For `nfnF₂_ordered` the strong form is **unavailable**, and §2 says why and proves the
substitute: the removed hypothesis's existential witness `E₂` leaves the signature entirely, and
at the unique `E₁` that `hE₁` pins the ctor stage does succeed, so that trim is *incidental*
rather than route-opening.  Recording the difference is the point of stating it.
-/

namespace Lean4Lean
namespace HypTrim2Witness

open InductiveDeclExamples
open Lean (Name)

/-! ## 1  `ntree_const_staged` / `nlist_const_staged`: the removed hypothesis is FALSE -/

/-- `VEnv.empty` is not the environment `listDecl` builds — `addInduct'` declares `List`, and
`VEnv.empty` holds nothing.  So at `env₁ := VEnv.empty` the removed hypothesis
`h : VEnv.empty.addInduct' listDecl = some env₁` is **refuted**, and the untrimmed
`ntree_const_staged` had no instance whatsoever at that `env₁`. -/
theorem listEnv_ne_empty : ¬ VEnv.empty.addInduct' listDecl = some VEnv.empty := by
  intro h
  have := list_const h
  exact absurd this nofun

/-- The surviving hypothesis is inhabited at that same point: the type stage of `ntreeAux` runs
over `VEnv.empty`, because both its names are fresh there and the pair is `Nodup`. -/
theorem ntreeAux_staged_over_empty : ∃ e : VEnv, VEnv.empty.addIndTypes ntreeAux = some e :=
  VEnv.addConstList_eq_some_iff.2 ⟨fun _ _ => rfl, by decide⟩

/-- **The two trimmed lemmas, applied where `h` is false.**  Arity 0. -/
theorem staged_consts_over_empty : ∃ e : VEnv,
    VEnv.empty.addIndTypes ntreeAux = some e ∧
    e.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ ∧
    e.constants `_nested.List_1
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := by
  obtain ⟨e, he⟩ := ntreeAux_staged_over_empty
  exact ⟨e, he, ntree_const_staged he, nlist_const_staged he⟩

/-- …and the instance is not the degenerate one: the two constants are **distinct**, so the
conclusion is two facts and not one repeated. -/
theorem staged_names_distinct : (``NTree : Name) ≠ `_nested.List_1 := by decide

/-! ## 2  `nfnF₂_ordered`: inhabited, and honestly incidental

`hE₂ : E₁.addIndCtors nfnAux = some E₂` was the removed hypothesis, and `E₂` occurs nowhere else
in the statement, so it left the signature with it.  There is therefore no `E₂` left to refute
the hypothesis *at* — the strong form of the check is not available here, and pretending
otherwise would be the vacuous move this file exists to avoid.

What *is* available: (a) the trimmed conclusion at a concrete four-environment chain that never
constructs a ctor stage at all (`nfnF₂_ordered_no_ctor_stage`), and (b) the measurement that
makes the verdict "incidental": the ctor stage **does** succeed at the unique `E₁` that `hE₁`
pins (`nfn_ctor_stage_exists`), so this trim removes a discharge-able obligation rather than an
impossible one.
-/

/-- Freshness of all four `NFn`-block names in the `PFn` environment.  `nfn_fresh'`
(`ConstSubstNested.lean`) covers only the two *type* names; the ctor stages need the
constructor names too. -/
theorem nfn_fresh {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
    (n : Name) (hn : n ∈ [``NFn, `_nested.PFn_1, ``NFn.node, `_nested.PFn_1.mk]) :
    env₂.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

/-- **The trimmed lemma at a concrete chain, with no ctor stage anywhere in it.**  Four
environments, not five: `E₂` is absent from the statement and from the proof. -/
theorem nfnF₂_ordered_no_ctor_stage : ∃ env₂ E₁ F₁ F₂ : VEnv,
    VEnv.empty.addInduct' pfnDecl = some env₂ ∧
    env₂.addIndTypes nfnAux = some E₁ ∧
    env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁ ∧
    F₁.addConstList (nfnAux.ctorConstsCR nfnRestore nfnK) = some F₂ ∧
    F₂.Ordered := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ := nfnAux_staged_exists h
  obtain ⟨F₁, hF₁⟩ := nfnAux_declared_exists h
  obtain ⟨F₂, hF₂⟩ : ∃ e, F₁.addConstList (nfnAux.ctorConstsCR nfnRestore nfnK) = some e := by
    refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
    rw [VEnv.addConstList_constants_of_not_mem hF₁ (by revert hn; revert n; decide)]
    exact nfn_fresh h n (by revert hn; revert n; decide)
  exact ⟨env₂, E₁, F₁, F₂, h, hE₁, hF₁, hF₂, nfnF₂_ordered h hE₁ hF₁ hF₂⟩

/-- **Why the trim is incidental, not route-opening.**  The removed hypothesis was satisfiable at
the very `E₁` its companion `hE₁` pins, so no caller was ever blocked by it — unlike
`hp : D.params = []` in the previous round, which was *false* at the block that needed the
lemma. -/
theorem nfn_ctor_stage_exists {env₂ E₁ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂)
    (hE₁ : env₂.addIndTypes nfnAux = some E₁) :
    ∃ E₂, E₁.addIndCtors nfnAux = some E₂ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  rw [VEnv.addConstList_constants_of_not_mem hE₁ (by revert hn; revert n; decide)]
  exact nfn_fresh h n (by revert hn; revert n; decide)

end HypTrim2Witness
end Lean4Lean
