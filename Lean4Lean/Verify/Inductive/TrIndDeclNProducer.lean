import Lean4Lean.Verify.Inductive.FlipRemainder
import Lean4Lean.Verify.Inductive.FlipWiring
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
* the ones nothing in the tree concludes in general, carried as explicitly named hypotheses.

**`trCtors` is now wired, not carried.**  Before this revision §1 took the whole field
`trCtors` as a hypothesis.  It now takes `TrExprSGeneral.lean`'s two:
`hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁` — a lookup table agreeing
with the staged environment, discharged in general by `FlipWiring.lean` §1 — and `hctr`, an
`Option` computation of the inferencer `ctorTr?` at each constructor.  `trCtors_of_ctorTr`
concludes the field's text verbatim, so the substitution is a drop-in.

**And it removed a premise.**  `∃ env₁, env.addIndTypesC D K = some env₁` was carried only so
that `ctorName_own` could instantiate the *staged* `trCtors` hypothesis and read off
`c.name = R.ctorName C.name`.  `hctr`'s first conjunct is unstaged, so the premise is gone: §1
no longer requires the type stage to succeed at all.

So §1's shape *is* the checklist.  What remains as a hypothesis and is **not** general is
**`trCtorsLen`** — and only that.  `trType` is general via `trType_of_sortPiTr`
(`TrTypeProducer.lean`) and, for a sort-telescope member, via `ctorTr?` with the *empty* table;
`trCtors` is general via the wiring above; `companions`/`recName_aux` are `RestoreData`'s (§2);
the spine clause is `TrSpineProducer.lean`/`FlipRemainder.lean`'s.  `trCtorsLen` has no general
producer anywhere in the tree, and `Verify/Inductive/CtorPointwise.lean` §3 proves the obvious
supplier cannot exist (`trCtorsLen_not_of_restoreData`): `RestoreData` never mentions
`types[j].ctors`.  Both remaining hypotheses of §1 are therefore *carried on purpose*, and §1's
arity is the honest measure of what is left.

§3 is the vacuity guard the assembly needs: an arity-0, existentially-closed instance at
`InductiveDeclExamples.ntreeAux` — `uvars = 1`, `params = [.sort (.succ (.param 0))]`, the
parameterised nested block, **not** the degenerate `nfnAux`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The producer

Two fields are discharged here from data the site already has, and it is worth saying exactly
how, because both were on the brief's list of open obligations:

* **`ctorName_own`** (`c.name = C.name`) comes from `hctr`'s name conjunct
  (`c.name = R.ctorName C.name`) composed with `OwnId.ctorName` (`R.ctorName C.name = C.name`
  off `K`).  `hctr` is **unstaged**, which is why this no longer costs a
  `∃ env₁, env.addIndTypesC D K = some env₁` premise — the earlier version had to carry one
  because it read the same equation off the staged `trCtors` field.
* **`recName_own`** comes from `OwnId.recName` composed with `trType`'s *name* half
  (`t.name = T.name`), the guard `T.name ∉ K` coming from `companions` and `j < types.length`.

`OwnId` is the general interface here rather than `mkRestore`: it is available both at the
computed restoration (`RestoreData.mkRestore_ownId`) and at a hand-written one
(`ntreeRestore_ownId`), which is what lets §3 exist at all. -/

/-- **THE GENERAL NESTED PRODUCER.**  Every field of `TrIndDeclN` except `trType` and
`trCtorsLen` is either the block's own data, discharged here, or — for `trCtors` — reduced to a
lookup table plus an `Option` computation. -/
theorem trIndDeclN_of_ownId {env : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List InductiveType} {isUnsafe : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} {Γc : Name → Option VConstant}
    (hown : R.OwnId D K)
    (hsafe : isUnsafe = false) (huv : Us.length = D.uvars) (hnp : nparams = D.np)
    (hlen : D.types.length = types.length + numNested)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j))
    (hrax : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      R.recName (Lean.mkRecName T.name) = auxRecName types (j - types.length))
    (hspine : R.SpineHargsN D K env types)
    -- `trCtors`, through the inferencer: a lookup table plus a computation
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (hctr : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t'))
    -- `trType`: general via `trType_of_ctorTr` / `trType_of_sortPiTr`, carried here.
    -- `trCtorsLen`: THE ONE FIELD WITH NO GENERAL PRODUCER (`CtorPointwise.lean` §3 refutes
    -- the `RestoreData` route outright), so it is carried on purpose.
    (hty : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T)
    (hclen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.ctors.length = T.ctors.length) :
    TrIndDeclN env Us nparams types isUnsafe numNested D K R where
  safe := hsafe
  uvars := huv
  np := hnp
  length := hlen
  companions := hcomp
  trType := hty
  trCtorsLen := hclen
  trCtors := trCtors_of_ctorTr hΓc hctr
  trSpine := hspine
  ctorName_own := by
    intro j t T ht hT q c C hc hC
    have hK : T.name ∉ K := fun hm =>
      absurd ((hcomp j T hT).1 hm) (Nat.not_le.2 (List.getElem?_eq_some_iff.1 ht).1)
    rw [(hctr j t T ht hT q c C hc hC).1]
    exact hown.ctorName j T hT hK C (List.mem_of_getElem? hC)
  recName_own := by
    intro j t T ht hT
    have hK : T.name ∉ K := fun hm =>
      absurd ((hcomp j T hT).1 hm) (Nat.not_le.2 (List.getElem?_eq_some_iff.1 ht).1)
    rw [hown.recName j T hT hK, (hty j t T ht hT).1]
  recName_aux := hrax

/-! ## §2 …at the restoration the checker's data determines

`RestoreData` discharges two more of §1's inputs — `companions` and `recName_aux` — and supplies
the `OwnId`.  So at `mkRestore` the producer's remaining hypotheses beyond the block's own
arithmetic and the spine clause are the constructor table/computation pair and the **two**
fields with no general producer, `trType` and `trCtorsLen`. -/

open ElimNestedInductive in
/-- **THE PRODUCER AT `mkRestore`.**  `hown`/`hcomp`/`hrax` of §1 are gone: `RestoreData` gives
all three (`mkRestore_ownId`, `RestoreData.companions`, `mkRestore_recName_aux`). -/
theorem trIndDeclN_of_restoreData {env : VEnv} {Us : List Name} {nparams numNested : Nat}
    {types : List InductiveType} {isUnsafe : Bool} {D : VInductDecl'} {K : List Name}
    {r : Result} {ls : Nat → List VLevel} {as : Nat → List VExpr}
    {Γc : Name → Option VConstant}
    (hRD : r.RestoreData types D K as)
    (hsafe : isUnsafe = false) (huv : Us.length = D.uvars) (hnp : nparams = D.np)
    (hlen : D.types.length = types.length + numNested)
    (hspine : (r.mkRestore types D.uvars D.np ls as).SpineHargsN D K env types)
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (hctr : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = (r.mkRestore types D.uvars D.np ls as).ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type []
          = some (C.typeR D (r.mkRestore types D.uvars D.np ls as) j, t'))
    (hty : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T)
    (hclen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.ctors.length = T.ctors.length) :
    TrIndDeclN env Us nparams types isUnsafe numNested D K
      (r.mkRestore types D.uvars D.np ls as) :=
  trIndDeclN_of_ownId (hRD.mkRestore_ownId (ls := ls) (as := as)) hsafe huv hnp hlen
    hRD.companions (fun _ _ hT hle => hRD.mkRestore_recName_aux hT hle) hspine
    hΓc hctr hty hclen

/-! ## §3 Vacuity: the arity-0 witness at the **parameterised** nested block

`InductiveDeclExamples.ntreeAux` is `inductive NTree (α : Type u) | node : α → List (NTree α) →
NTree α` with its `_nested.List_1` companion: `uvars = 1`, `params = [.sort (.succ (.param 0))]`,
`np = 1`, `numNested = 1`.  Deliberately **not** `nfnAux`, which is degenerate (`uvars = 0`,
`params = []`) — the two numbers are asserted inside the statement so the witness cannot silently
become the degenerate one, and `nfnAux_is_degenerate` next to it is the contrast.

**Route, and it is now free of every hand-built bridge.**  Every field goes through §1.

* `trCtors` is the **wired** route: the table is `ntreeGc` (`TrExprSGeneral.lean` §5, the two
  constants `NTree.node`'s stored type mentions), its `ConstLookup` comes from
  `FlipWiring.lean`'s `constLookup_staged_of_split` — `List` is a pre-block constant, `NTree` is
  one of `ntreeAux.typeConstsC ntreeK` — and the per-constructor content is `ntreeNode_ctorTr`,
  an `rfl`.
* `trType` goes through `FlipWiring.lean`'s general producer `trType_of_ctorTr` and costs
  **nothing about the environment**: `ntreeIndType.type` is `Type u → Type u`, a sort telescope
  with no `.const` leaf, so `ctorTr?` reads it off with the *empty* table (`constLookup_none`).
  `tr_ntreeType_of_ctorTr` below is `FlipConstruct.lean`'s `tr_ntreeType` re-derived that way,
  kept as the standalone contrast with the `trS_tac` version.
* the spine clause is `FlipRemainder.lean`'s general index-free route, the `OwnId` is
  `ntreeRestore_ownId`, and `trCtorsLen` is `rfl`.

**Structural non-borrowing.**  This module **no longer imports
`Verify/Inductive/FlipConstruct.lean`**, and that was its only path into the closure, so
`tr_ntreeType` and `tr_ntreeNodeType` — the two `trS_tac` bridges — are not in scope here at all
and cannot be borrowed by accident.  Nothing below uses `trS_tac` or `type_tac`, and
`NestedWit.trIndDeclN_wit` (the `nfnAux` witness) is not in scope either. -/

namespace InductiveDeclExamples

/-- **`tr_ntreeType` re-derived through the inferencer**, from no hypotheses and an *empty* table:
the member's own stored type is a sort telescope, so it has no `.const` leaf to look up.  This is
`Verify/Inductive/FlipConstruct.lean:121`'s bridge, which this module does not import. -/
theorem tr_ntreeType_of_ctorTr {env : VEnv} : TrExprS env [`u] []
    (exprOf% NTree) (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
  trExprS_of_ctorTr (Γc := fun _ => none) constLookup_none rfl

/-- The table's `ConstLookup`, through `FlipWiring.lean` §1 rather than by hand: `List` is a
pre-block constant, `NTree` is one of the block's own non-companion type constants. -/
theorem ntreeGc_constLookup {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∀ F, env₁.addIndTypesC ntreeAux ntreeK = some F → ConstLookup ntreeGc F := by
  refine constLookup_staged_of_split fun c ci hc => ?_
  rw [ntreeGc] at hc
  split at hc
  · next hL => cases hc; subst hL; exact .inr (list_const h)
  · split at hc
    · next hN =>
      cases hc; subst hN
      exact .inl (by rw [ntree_typeConstsC]; exact List.Mem.head _)
    · exact absurd hc nofun

/-- **THE NESTED TRANSLATION RELATION AT `ntreeAux`, THROUGH THE WIRED PRODUCER, ARITY 0.**

Existentially closed over the pre-block environment.  The two numeric conjuncts are the
degeneracy guard: `nfnAux` has `uvars = 0` and `params = []`, so a witness that drifted to it
would fail them. -/
theorem ntreeAux_trIndDeclN :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      TrIndDeclN env₁ [`u] 1 [ntreeIndType] false 1 ntreeAux ntreeK ntreeRestore := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  refine ⟨env₁, h, rfl, rfl, trIndDeclN_of_ownId ntreeRestore_ownId rfl rfl rfl rfl
    ntreeAux_companions ?_
    (VIndRestore.spineHargsN_of_head_indexFree (ntreeAux_restrictStepCfg h h₂ h₃)
      (ntreeAux_argsTypedK_of_wf h₂) (T₀ := ntreeAux.types.getD 0 default) rfl (by decide)
      (by decide) ntreeAux_companions)
    (ntreeGc_constLookup h) ?_ ?_ ?_⟩
  · -- `recName_aux`: `mkAuxRecNameMap` renames `_nested.List_1.rec` to `NTree.rec_1`
    rintro (_ | _ | j) T hT hle
    · simp at hle
    · cases hT; rfl
    · simp [ntreeAux] at hT
  · -- `trCtors`, wired: the name equation and the inferencer's computation, both `rfl`
    rintro (_ | j) t T ht hT (_ | q) c C hc hC
    · cases ht; cases hT; cases hc; cases hC
      exact ⟨rfl, _, ntreeNode_ctorTr⟩
    · cases ht; cases hT; simp [ntreeIndType] at hc
    · simp at ht
    · simp at ht
  · -- `trType`: through the general `ctorTr?` producer, with the **empty** table
    refine trType_of_ctorTr (Γc := fun _ => none) constLookup_none ?_
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; exact ⟨rfl, _, rfl⟩
    · simp at ht
  · -- `trCtorsLen`
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht

/-- …and the contrast with the degenerate block, so §3's non-degeneracy is machine-checked
rather than asserted: `nfnAux` fails both numeric conjuncts. -/
theorem nfnAux_is_degenerate : nfnAux.uvars = 0 ∧ nfnAux.params = [] :=
  ⟨rfl, rfl⟩

end InductiveDeclExamples

end Lean4Lean
