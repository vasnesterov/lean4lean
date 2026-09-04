import Lean4Lean.Verify.Inductive.ValAtParam
import Lean4Lean.Theory.Typing.ConstSubstNested

/-!
# `TrIndDeclN.trCtors`, in general: the fragment trick, extended past constants

`Verify/Inductive/TrTypeProducer.lean` settled `TrIndDeclN.trType` on a fragment
(`sortPiTr?`, §1 there) whose defining virtue is that it needs **no** environment: `TrExprS.const`
is the only constructor that reads `env.constants`, and a sort-and-pi arity has no `.const` leaf.
A **constructor** type is not like that -- `NTree.node : ∀ α, α → List (NTree α) → NTree α`
mentions the block's own member and the companion's head -- so the received view was that the
fragment trick cannot transfer and the translation must come from the checker
(`TypeChecker.checkType.WF`, cone 18795, 8 holes, and both watched `VEnv.IsDefEq.uniq` /
`uniqU`).

That is wrong, and this file is the counter-construction.  The fragment trick transfers if you
give up the *wrong* virtue.  What made `sortPiTr?` work was not that it ignored the environment;
it was that it was a **function**, so the field's obligation became an equation between computed
data.  A function may read the environment perfectly well -- `VEnv.constants` is a plain
`Name → Option VConstant` field -- and the price of the extension is not the constants at all.
It is that `TrExprS.app` carries two `VEnv.HasType` premises, so a translator that admits
applications has to be a *type inferencer*, not just a translator.

`ctorTr?` (§2) is that inferencer, on the fragment `.sort | .bvar | .const | .app | .forallE |
.mdata` -- exactly the cases `trS_tac` (`Verify/Environment/InductR.lean:779`) handles by
reflection, and exactly the cases a non-indexed constructor type uses.  It returns the translation
**and its type**, which is what lets the `.app` case discharge `HasType f' (.forallE A B)` and
`HasType a' A` without any definitional unfolding: on this fragment the function's inferred type is
*syntactically* a `∀`, so no whnf, no `IsDefEq`, and therefore no contact with the checker.

Three deliberate choices, each of which keeps the cone clean:

* **The environment enters as a `Name → Option VConstant` argument**, not as the `VEnv` itself,
  with the soundness side condition `∀ c ci, Γc c = some ci → env.constants c = some ci`.  So the
  function still *computes* at a concrete block (§5's witness is `rfl`), and the environment
  content appears as the same kind of hypothesis the hand-built witnesses already take
  (`tr_ntreeNodeType` has arity 3: `{env}` plus two lookups).
* **The local context is an all-`vlam` one built from a `List VExpr`** (`bvarCtx`, §1).  For such a
  context `VLCtx.find?` computes and `Lookup` follows by a four-line induction, so the bvar case
  needs neither `VLCtx.WF.find?_wf` nor `HasType.weakN` -- both of which sit behind
  `VEnv.Ordered`, which `ntree_stage₂_exists` does not hand out.  A constructor type's telescope
  from the empty base context is exactly this shape.
* **No `.lam`, `.letE`, `.proj`, `.lit`, `.fvar` case.**  `trS_tac` has none either.  §6 records
  the boundary.

§3 is the member-level statement, §4 the `TrIndDeclN.trCtors` field producer, §5 the arity-0
vacuity witness at the **parameterised** nested block `ntreeAux` (`uvars = 1`,
`params = [Type u]`), reached through §4 with no block lemma: this file does **not** import
`Verify/Inductive/FlipConstruct` or `Verify/Inductive/TrIndDeclNProducer`, so neither
`tr_ntreeNodeType` nor `ntreeAux_trIndDeclN` is in scope.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The all-`vlam` context, and why its lookups are free -/

/-- The `VLCtx` a `∀`-telescope builds from the empty base context: every entry a `vlam`, no
free variables. -/
def bvarCtx : List VExpr → VLCtx
  | [] => []
  | A :: Γ => (none, .vlam A) :: bvarCtx Γ

@[simp] theorem bvarCtx_toCtx : ∀ Γ : List VExpr, (bvarCtx Γ).toCtx = Γ
  | [] => rfl
  | _ :: Γ => by rw [bvarCtx, VLCtx.toCtx, bvarCtx_toCtx Γ]

@[simp] theorem bvarCtx_cons (A : VExpr) (Γ : List VExpr) :
    bvarCtx (A :: Γ) = (none, .vlam A) :: bvarCtx Γ := rfl

/-- `find?` at the head of an all-`vlam` context. -/
theorem bvarCtx_find?_zero (B : VExpr) (Γ : List VExpr) :
    (bvarCtx (B :: Γ)).find? (.inl 0) = some (.bvar 0, B.lift) := rfl

/-- …and past it, lifting by one. -/
theorem bvarCtx_find?_succ (B : VExpr) (Γ : List VExpr) (i : Nat) :
    (bvarCtx (B :: Γ)).find? (.inl (i+1))
      = ((bvarCtx Γ).find? (.inl i)).bind fun p => some (p.1.liftN 1, p.2.liftN 1) := rfl

/-- **The bvar case, with no `VLCtx.WF` and no `Ordered env`.**  On an all-`vlam` context
`VLCtx.find?` returns the de Bruijn variable itself together with a type that `Lookup` names. -/
theorem bvarCtx_find? : ∀ {Γ : List VExpr} {i : Nat} {e A : VExpr},
    (bvarCtx Γ).find? (.inl i) = some (e, A) → e = .bvar i ∧ Lookup Γ i A
  | [], _, _, _, h => by simp [bvarCtx, VLCtx.find?] at h
  | B :: Γ, 0, e, A, h => by
    rw [bvarCtx_find?_zero] at h; cases h; exact ⟨rfl, .zero⟩
  | B :: Γ, i+1, e, A, h => by
    rw [bvarCtx_find?_succ, Option.bind_eq_some_iff] at h
    obtain ⟨⟨e₀, A₀⟩, h₀, he⟩ := h
    obtain ⟨rfl, hl⟩ := bvarCtx_find? h₀
    cases he
    exact ⟨by simp [VExpr.liftN, liftVar, Nat.add_comm], .succ hl⟩
