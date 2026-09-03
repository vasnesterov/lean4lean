import Lean4Lean.Verify.Inductive.FlipRemainder
import Lean4Lean.Verify.Inductive.FlipConstruct
import Lean4Lean.Verify.Inductive.NestedRestore

/-!
# A general producer for `TrIndDeclN`, and the exact list of what is still open

`Verify/Environment/InductR.lean`'s `TrIndDeclN` has **twelve** fields.  Before this file the
only things concluding the whole relation were `TrIndDecl.toN` (the `numNested = 0` bridge) and
the two concrete nested witnesses `NestedWit.trIndDeclN_wit` / `trIndDeclN_wit'`, both at the
degenerate `nfnAux` block (`uvars = 0`, `params = []`).

§1 is the producer.  Its hypotheses are, deliberately, of two kinds:

* the ones a *general* theorem discharges — and those are **not** hypotheses of §1 at all,
  they are proved in its body: `ctorName_own` and `recName_own`;
* the ones nothing in the tree concludes in general, carried as explicitly named hypotheses:
  `trType`, `trCtorsLen`, `trCtors`.

So §1's shape *is* the checklist: **three open fields**, plus the block's own data
(`safe`/`uvars`/`np`/`length`/`companions`), plus `recName_aux`, plus the spine clause — the
last three all discharged in general downstream (§2 for `recName_aux` at `mkRestore`,
`TrSpineProducer.lean`/`FlipRemainder.lean` for the spine).

§3 is the vacuity guard the assembly needs: an arity-0, existentially-closed instance at
`InductiveDeclExamples.ntreeAux` — `uvars = 1`, `params = [.sort (.succ (.param 0))]`, the
parameterised nested block, **not** the degenerate `nfnAux`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The producer

Two fields are discharged here from data the site already has, and it is worth saying exactly
how, because both were on the brief's list of open obligations:

* **`ctorName_own`** (`c.name = C.name`) comes from `trCtors` (`c.name = R.ctorName C.name`)
  composed with `OwnId.ctorName` (`R.ctorName C.name = C.name` off `K`).  `trCtors` is staged,
  so this costs the same `∃ env₁, env.addIndTypesC D K = some env₁` premise that
  `TrIndDecl.toN` already pays; no new obligation.
* **`recName_own`** comes from `OwnId.recName` composed with `trType`'s *name* half
  (`t.name = T.name`), the guard `T.name ∉ K` coming from `companions` and `j < types.length`.

`OwnId` is the general interface here rather than `mkRestore`: it is available both at the
computed restoration (`RestoreData.mkRestore_ownId`) and at a hand-written one
(`ntreeRestore_ownId`), which is what lets §3 exist at all. -/

/-- **THE GENERAL NESTED PRODUCER.**  Every field of `TrIndDeclN` except `trType`,
`trCtorsLen` and `trCtors` is either the block's own data or discharged here. -/
theorem trIndDeclN_of_ownId {env : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List InductiveType} {isUnsafe : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore}
    (hown : R.OwnId D K)
    (hsafe : isUnsafe = false) (huv : Us.length = D.uvars) (hnp : nparams = D.np)
    (hlen : D.types.length = types.length + numNested)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j))
    (hrax : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      R.recName (Lean.mkRecName T.name) = auxRecName types (j - types.length))
    (hst : ∃ env₁, env.addIndTypesC D K = some env₁)
    (hspine : R.SpineHargsN D K env types)
    -- the three open fields, named
    (hty : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T)
    (hclen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.ctors.length = T.ctors.length)
    (hctors : ∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D R j c C) :
    TrIndDeclN env Us nparams types isUnsafe numNested D K R where
  safe := hsafe
  uvars := huv
  np := hnp
  length := hlen
  companions := hcomp
  trType := hty
  trCtorsLen := hclen
  trCtors := hctors
  trSpine := hspine
  ctorName_own := by
    intro j t T ht hT q c C hc hC
    obtain ⟨env₁, hst⟩ := hst
    have hK : T.name ∉ K := fun hm =>
      absurd ((hcomp j T hT).1 hm) (Nat.not_le.2 (List.getElem?_eq_some_iff.1 ht).1)
    rw [(hctors env₁ hst j t T ht hT q c C hc hC).1]
    exact hown.ctorName j T hT hK C (List.mem_of_getElem? hC)
  recName_own := by
    intro j t T ht hT
    have hK : T.name ∉ K := fun hm =>
      absurd ((hcomp j T hT).1 hm) (Nat.not_le.2 (List.getElem?_eq_some_iff.1 ht).1)
    rw [hown.recName j T hT hK, (hty j t T ht hT).1]
  recName_aux := hrax

/-! ## §2 …at the restoration the checker's data determines

`RestoreData` discharges two more of §1's inputs — `companions` and `recName_aux` — and supplies
the `OwnId`.  So at `mkRestore` the producer's *only* remaining hypotheses beyond the block's
own arithmetic and the spine clause are the **three** open fields. -/

open ElimNestedInductive in
/-- **THE PRODUCER AT `mkRestore`.**  `hown`/`hcomp`/`hrax` of §1 are gone: `RestoreData` gives
all three (`mkRestore_ownId`, `RestoreData.companions`, `mkRestore_recName_aux`). -/
theorem trIndDeclN_of_restoreData {env : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List InductiveType} {isUnsafe : Bool} {D : VInductDecl'} {K : List Name}
    {r : Result} {ls : Nat → List VLevel} {as : Nat → List VExpr}
    (hRD : r.RestoreData types D K as)
    (hsafe : isUnsafe = false) (huv : Us.length = D.uvars) (hnp : nparams = D.np)
    (hlen : D.types.length = types.length + numNested)
    (hst : ∃ env₁, env.addIndTypesC D K = some env₁)
    (hspine : (r.mkRestore types D.uvars D.np ls as).SpineHargsN D K env types)
    (hty : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T)
    (hclen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.ctors.length = T.ctors.length)
    (hctors : ∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D (r.mkRestore types D.uvars D.np ls as) j c C) :
    TrIndDeclN env Us nparams types isUnsafe numNested D K
      (r.mkRestore types D.uvars D.np ls as) :=
  trIndDeclN_of_ownId (hRD.mkRestore_ownId (ls := ls) (as := as)) hsafe huv hnp hlen
    hRD.companions (fun _ _ hT hle => hRD.mkRestore_recName_aux hT hle) hst hspine
    hty hclen hctors

/-! ## §3 Vacuity: the arity-0 witness at the **parameterised** nested block

`InductiveDeclExamples.ntreeAux` is `inductive NTree (α : Type u) | node : α → List (NTree α) →
NTree α` with its `_nested.List_1` companion: `uvars = 1`, `params = [.sort (.succ (.param 0))]`,
`np = 1`, `numNested = 1`.  Deliberately **not** `nfnAux`, which is degenerate (`uvars = 0`,
`params = []`) — §3.2 asserts the two numbers inside the statement so the witness cannot silently
become the degenerate one.

**Route.**  Every field goes through §1.  The three open fields are supplied by
`FlipConstruct.lean`'s `TrExprS` bridges (`tr_ntreeType` needs *no* hypotheses; `tr_ntreeNodeType`
needs `List` and `NTree` declared, which `list_const₃`/`ntree_const₃` give at the staged
environment), the spine clause by `FlipRemainder.lean`'s general index-free route, and the
`OwnId` by `ntreeRestore_ownId`.  Nothing here is a `TrIndDeclN`-specific block lemma, and in
particular **nothing borrows from `NestedWit.trIndDeclN_wit`**, which is the `nfnAux` witness. -/

namespace InductiveDeclExamples

/-- **THE NESTED TRANSLATION RELATION AT `ntreeAux`, THROUGH THE GENERAL PRODUCER, ARITY 0.**

Existentially closed over the pre-block environment.  The two numeric conjuncts are the
degeneracy guard: `nfnAux` has `uvars = 0` and `params = []`, so a witness that drifted to it
would fail them. -/
theorem ntreeAux_trIndDeclN :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      TrIndDeclN env₁ [`u] 1 [ntreeIndType] false 1 ntreeAux ntreeK ntreeRestore := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  refine ⟨env₁, h, rfl, rfl, trIndDeclN_of_ownId ntreeRestore_ownId rfl rfl rfl rfl
    ntreeAux_companions ?_ ⟨env₃, h₃⟩
    (VIndRestore.spineHargsN_of_head_indexFree (ntreeAux_restrictStepCfg h h₂ h₃)
      (ntreeAux_argsTypedK_of_wf h₂) (T₀ := ntreeAux.types.getD 0 default) rfl (by decide)
      (by decide) ntreeAux_companions)
    ?_ ?_ ?_⟩
  · -- `recName_aux`: `mkAuxRecNameMap` renames `_nested.List_1.rec` to `NTree.rec_1`
    rintro (_ | _ | j) T hT hle
    · simp at hle
    · cases hT; rfl
    · simp [ntreeAux] at hT
  · -- `trType`: `tr_ntreeType`, no hypotheses at all
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; exact ⟨rfl, tr_ntreeType⟩
    · simp at ht
  · -- `trCtorsLen`
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  · -- `trCtors`: `tr_ntreeNodeType` at the staged environment
    rintro env₁' hst (_ | j) t T ht hT (_ | q) c C hc hC
    · cases ht; cases hT; cases hc; cases hC
      cases Option.some.inj (hst.symm.trans h₃)
      exact ⟨rfl, tr_ntreeNodeType (list_const₃ h h₃) (ntree_const₃ h₃)⟩
    · cases ht; cases hT; simp [ntreeIndType] at hc
    · simp at ht
    · simp at ht

/-- …and the contrast with the degenerate block, so §3's non-degeneracy is machine-checked
rather than asserted: `nfnAux` fails both numeric conjuncts. -/
theorem nfnAux_is_degenerate : nfnAux.uvars = 0 ∧ nfnAux.params = [] :=
  ⟨rfl, rfl⟩

end InductiveDeclExamples

end Lean4Lean
