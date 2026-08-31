import Lean4Lean.Theory.SemanticRouteClosed
import Lean4Lean.Theory.Typing.RigidNodeCircle

/-!
# The semantic route into the injectivity corner, part 2: the **negative** conjuncts

`Theory/SemanticRouteClosed.lean` measured the set model against the injectivity corner and
found: `SortInv` closed and exact; `SortUniq` **dead** (`hasChains_refutes_levelSeparating`);
`PiInv`'s domain conjunct **dead** (`not_forallPropDomInj`), with a second, unresidualised
faithfulness gap behind it.  That file's own summary is that the model "helps precisely as far
as `SortInv` and no further".

This file shows that summary is one conjunct short, and names the structural reason.

## The principle

Look at what the three measured statements *ask for*:

| statement | asks for | model needs |
|---|---|---|
| `SortUniq` | a level equation, from two **memberships** | stages disjoint — **false** (`U_mono`) |
| `PiInv` | a **derivation** `Γ ⊢ A ≡ A'` | faithfulness — absent from any soundness model |
| `SortInv` | a level equation, from one **equality** | `U` injective — **true** (`U_injOn`) |

The faithfulness gap is what kills `PiInv`, and it kills every *positive* conjunct: soundness
maps derivations to denotational facts, never back.  But a **disjointness** conjunct is
negative: it says a conversion does *not* exist.  For those, soundness alone is the right tool
— assume the conversion, push it through part 4, and contradict a set-theoretic fact.  No
faithfulness is involved, because the derivation is a *hypothesis*, not a conclusion.

`Theory/Typing/RigidNodeCircle.lean`'s `rigidShapeUniqNS_iff_family` decomposes the second open
hole, `Injectivity.WF.rigidShapeUniqNS`, into exactly five conjuncts.  **Three of them are
negative**: `RigidSortPiDisj`, `RigidConstPiDisj`, `RigidConstSortDisj`.  So the model route was
never measured against the majority of that hole.

## What is proved here

1. **`RigidSortPiDisj` — `IsDefEqU.sort_forallE_inv` — has a semantic residual that is a
   THEOREM, not a refuted statement.**  `interp_sort_ne_interp_forallE`: a universe stage is
   never the denotation of a `∀`, on *either* branch of the proof split, under no hypothesis
   beyond the chain the model already assumes.  The separating element is `{•}`: it is in every
   stage (`true_mem_U`) and in no `∀` node — impredicatively because every element of `piProp`
   *is* `•`, predicatively because `•` is not a Kuratowski pair, so `{•}` is not a function.
   Contrast the two measured dead routes, whose residuals (`LevelSeparating`,
   `ForallPropDomInj`) are **refuted**.  This is the first conjunct other than `SortInv` for
   which the model layer supplies a usable fact.

2. **The packaging COLLAPSES, and that is stated as a theorem** (`sortPiSupplyAll_iff`): the
   per-conversion supply `SortPiSupplyAll` is *equivalent* to `RigidSortPiDisj`, so
   `semantic_rigidSortPiDisj` and `rigidShapeUniqNS_of_four` are restatements, not reductions,
   and no residual and no census number moves today.  The reason the shape is forced is
   `Above`: `SetModel.sound`'s threshold is produced *by the derivation*, so a chain long enough
   to use it can only be picked after the derivation is in hand.  The content is entirely in
   item 1, which takes no supply.

3. **The other two negative conjuncts are DEAD, and `Coherent` does not rescue them.**
   `interp M L Γ (.const c us) = M.cnst c us` and `M.cnst` is a free field of `ModelData`:
   `const_denot_arbitrary` makes every constant denote whatever one likes, and the residual
   `ConstNotUniv` is **false unguarded** (`not_constNotUniv`) — the same idiom as
   `not_levelSeparating`.  So `RigidConstPiDisj` and `RigidConstSortDisj` are unreachable from
   `interp` alone.

   **CORRECTION (2026-08-31, later).**  This item used to end "they become reachable only under
   `Coherent`, which `Theory/SetModel/` does not yet construct".  **Both halves of that were
   wrong.**  `CoherentOn` *is* constructed, in two places — `SetModel/CoherentWitness.lean`'s
   `coherentOn_witness` and `SetModel/CnstRecursion.lean`'s `coherentOn_cnstOf` — and the
   `CoherentOn`-guarded strengthening of the residual is **refuted**:
   `SetModel/CoherentConstShape.lean`'s `not_coherentConstNotUniv`,
   `not_coherentConstNotUniv_chain` and `not_coherentConstNotPi`, with
   `coherent_const_denot_eq_sort` / `coherent_const_denot_eq_forallE` exhibiting a `CoherentOn`
   model over a `VEnv.WF` environment with **no defeqs at all** in which `.const cShape us` and
   `.sort .zero` have the same denotation in every context at every valuation, and
   `oracleOK_univ` showing `Cnst.OracleOK` does not exclude it one level down.  The reason is
   structural: **`CoherentOn.const_type` constrains `M.cnst c us` by *membership* in
   `⟦ci.type⟧` and by nothing else**, and both target shapes live inside a declared type.  The
   refuted guard is moreover *stronger* than what these conjuncts supply — whole-environment
   rule-freeness (`∀ df, ¬ env.defeqs df`) versus `RuleFreeHead c` — so no weakening of it
   rescues them.  **The semantic tally for the second hole is therefore 1 usable conjunct of 5,
   permanently**, not 1 plus 2 pending.

4. **A limit on every semantic route into this corner, and a correction upstream.**  Both this
   file's supply and `SemanticRoute.SortEqSupply` demand `ρ ∈ interpCtx M L Γ`, because that is
   what `Sound.eq` quantifies over.  `interpCtx_vFalse`: for `Γ = [∀ p : Prop, p]` — a
   legitimate context over every environment (`onCtx_vFalse`) — the interpretation is **empty**,
   in every model and on both branches (`interp_vFalse`).  Hence `not_sortEqSupply`, and hence
   `sortInvSupply_vacuous`: the hypothesis of `SemanticRoute.semantic_sortInv_packaged` is
   **false for every `env` and every `nv`**, because reflexivity of `.sort .zero` supplies the
   conversion that the model cannot see.  `SemanticRouteClosed.lean`'s table records that route
   as "CLOSED, and exact"; the exactness check there (`sortEqRaw_iff`) is about `SortEqRaw`,
   which has no context and no `ρ`, and does not certify `SortEqSupply`.  The *content* of the
   upstream route survives — `U_injOn` and `semantic_sortInv` are untouched — but the packaged
   form does not, and anything that wants to use the model on a judgement in an arbitrary
   context owes a valuation for that context.

So the classification of the second hole's five conjuncts by *semantic* reachability is:

| conjunct | polarity | semantic status |
|---|---|---|
| `PiInv` | positive | dead (faithfulness; domain half also refuted upstream) |
| `RigidConstAppInv` | positive | dead (faithfulness) |
| `RigidSortPiDisj` | negative | residual **proved** here; packaging collapses (item 2) |
| `RigidConstPiDisj` | negative | **dead** — `CoherentOn` constrains `cnst` by membership only (`not_constNotUniv`; `SetModel/CoherentConstShape.lean`'s `not_coherentConstNotPi`) |
| `RigidConstSortDisj` | negative | **dead** — `CoherentOn` constrains `cnst` by membership only (`not_constNotUniv`; `SetModel/CoherentConstShape.lean`'s `not_coherentConstNotUniv`) |

and over all of them sits item 4's valuation obligation.

## What is NOT claimed

* **No hole is closed and no census number moves.**  `Injectivity.WF.rigidShapeUniqNS` still
  carries its `sorry`, and `sortPiSupplyAll_iff` is the receipt that today's packaging is a
  restatement rather than a narrowing.
* **Nothing here touches the *first* hole**, `IsDefEqU.forallE_inv_stratified`.  That one is
  `SortUniq` given `PiInv` (`Injectivity.sortUniq_iff_piInvStratApp`); both are positive, and
  both are measured semantically dead upstream.
* **No claim that `RigidSortPiDisj` is unprovable syntactically**, and no claim that the
  valuation obligation of item 4 is unsatisfiable — only that it is not satisfied at
  `[∀ p : Prop, p]` by *this* interpretation, which is the only one the tree has.
* Every declaration here is `sorryAx`-free (`#print axioms` block at the end) and the forward
  cone of every result reaches **no** sorry-carrying declaration — checked with
  `scripts/hole-cone.lean`'s walker, so the route is not circular through the corner it
  measures.
-/

namespace Lean4Lean.InjSortPi

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel Lean4Lean.SemanticRoute

variable {V : Type*} [SetStructure V] [Nonempty V]

section Z
variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- `{•} ≠ •`: the true proposition is not the point.  One line, but it is the entire
separating fact below. -/
theorem singleton_pt_ne_pt : ({pt} : V) ≠ (pt : V) := by
  intro h
  have hm : (pt : V) ∈ ({pt} : V) := by simp
  rw [h, pt_def] at hm
  exact not_mem_empty hm

/-- `{•}` is never an element of an impredicative `∀`. -/
theorem true_not_mem_piProp {A : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    ({pt} : V) ∉ piProp A B hB := fun h => singleton_pt_ne_pt (mem_piProp_iff.mp h).1

/-- `{•}` is not a function: `•` is not a Kuratowski pair. -/
theorem true_not_mem_function {X Y : V} : ({pt} : V) ∉ (Y ^ X : V) := by
  intro h
  have hp : (pt : V) ∈ (X ×ˢ Y : V) := subset_prod_of_mem_function h _ (by simp)
  obtain ⟨x, _, y, _, he⟩ := mem_prod_iff.mp hp
  have hx : ({x} : V) ∈ (pt : V) := by rw [he, kpair]; simp
  rw [pt_def] at hx
  exact not_mem_empty hx

end Z

section ZF
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `{•}` is never an element of a dependent product. -/
theorem true_not_mem_mkForallType {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ : V} : ({pt} : V) ∉ mkForallType G hG F hF ρ :=
  fun h => true_not_mem_function (mem_mkForallType_iff.mp h).1

/-- `{•}` is never an element of an impredicative `∀` node. -/
theorem true_not_mem_mkForallProp {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ : V} : ({pt} : V) ∉ mkForallProp G hG F hF ρ :=
  fun h => true_not_mem_piProp (by rwa [mkForallProp] at h)

/-- `{•}` is an element of every universe stage. -/
theorem true_mem_U {n i : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (hi : i ≤ n) :
    ({pt} : V) ∈ U κ i :=
  U_mono hκ (Nat.zero_le i) hi _ (by rw [U_zero]; exact true_mem_UProp)

end ZF

section Interp
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ}

/-- `{•}` is not in the denotation of a `∀`, on either branch of the proof split. -/
theorem true_not_mem_interp_forallE (M : ModelData V) (L : PropSplit env nv)
    {Γ : List VExpr} {A B : VExpr} (ρ : V) :
    ({pt} : V) ∉ (interp M L Γ (.forallE A B)).toFun ρ := by
  by_cases h : L.IsProp M (A :: Γ) B
  · rw [interp_forallE_prop M L h]; exact true_not_mem_mkForallProp
  · rw [interp_forallE_type M L h]; exact true_not_mem_mkForallType

/-- **The separation, at the interpretation.** -/
theorem interp_sort_ne_interp_forallE {n : ℕ} {M : ModelData V} {L : PropSplit env nv}
    (hκ : IsInaccessibleChain n M.κ) {Γ : List VExpr} {u : VLevel} {A B : VExpr}
    (hu : u.eval M.ls ≤ n) (ρ : V) :
    (interp M L Γ (.sort u)).toFun ρ ≠ (interp M L Γ (.forallE A B)).toFun ρ := by
  rw [interp_sort]
  intro h
  exact true_not_mem_interp_forallE M L ρ (h ▸ true_mem_U hκ hu)

end Interp

/-! ## §3 The supply, packaged the way `SemanticRoute.SortEqSupply` is -/

section Supply
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ}

/-- **Part 4 at a sort/Π pair**, in exactly the shape `SemanticRoute.SortEqSupply` has, so the
two can be compared line by line: for every universe valuation there is a model at that
valuation, with a chain long enough for the level, in which `.sort u` and `.forallE A B` get
equal denotations.  This is what `SetModel.sound`'s `eq` field delivers for a derivation of
`Γ ⊢ .sort u ≡ .forallE A B : T`. -/
def SortPiEqSupply (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (env : VEnv) (nv : ℕ) (Γ : List VExpr) (u : VLevel) (A B : VExpr) : Prop :=
  ∀ ls : List ℕ, ∃ (n : ℕ) (M : ModelData V) (L : PropSplit env nv) (ρ : V),
    M.ls = ls ∧ IsInaccessibleChain n M.κ ∧ ρ ∈ interpCtx M L Γ ∧
    u.eval ls ≤ n ∧
    (interp M L Γ (.sort u)).toFun ρ = (interp M L Γ (.forallE A B)).toFun ρ

/-- **The demand actually consumed**, and it is strictly less than `SortPiEqSupply` in three
independent ways: *one* valuation instead of all of them, *no* `ρ ∈ interpCtx` guard, and no
`M.ls = ls` tie.  Recording it separately is the point — the route does not need part 4 in
full, and a future supplier only has to hit this. -/
def SortPiEqSupplyAt (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (env : VEnv) (nv : ℕ) (Γ : List VExpr) (u : VLevel) (A B : VExpr) : Prop :=
  ∃ (n : ℕ) (M : ModelData V) (L : PropSplit env nv) (ρ : V),
    IsInaccessibleChain n M.κ ∧ u.eval M.ls ≤ n ∧
    (interp M L Γ (.sort u)).toFun ρ = (interp M L Γ (.forallE A B)).toFun ρ

theorem sortPiEqSupplyAt_of_supply {Γ : List VExpr} {u : VLevel} {A B : VExpr}
    (h : SortPiEqSupply V env nv Γ u A B) : SortPiEqSupplyAt V env nv Γ u A B := by
  obtain ⟨n, M, L, ρ, hls, hκ, _, hu, heq⟩ := h []
  exact ⟨n, M, L, ρ, hκ, by rw [hls]; exact hu, heq⟩

/-- **The semantic route to sort/Π disjointness works, and there is no residual.**

Contrast `SemanticRoute.sortUniq_of_levelSeparating`, whose residual `LevelSeparating` is
*refuted*, and `SemanticRoute.interp_dom_eq_of_forallPropDomInj`, whose residual
`ForallPropDomInj` is *refuted*.  Here the corresponding residual is
`interp_sort_ne_interp_forallE`, and it is a **theorem**: no hypothesis on `env`, no hypothesis
on the chain beyond the one the model already assumes, no injectivity input. -/
theorem semantic_sortPiDisj {Γ : List VExpr} {u : VLevel} {A B : VExpr}
    (h : SortPiEqSupplyAt V env nv Γ u A B) : False := by
  obtain ⟨n, M, L, ρ, hκ, hu, heq⟩ := h
  exact interp_sort_ne_interp_forallE hκ hu ρ heq

/-- The per-conversion supply, quantified over all instances — the shape
`SemanticRoute.semantic_sortInv_packaged` takes.  The `Above`-wrapping of `SetModel.sound`
forces this shape: the threshold `m` is produced *by the derivation*, so a chain long enough to
use it can only be chosen after the derivation is in hand. -/
def SortPiSupplyAll (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr},
    OnCtx Γ (env.IsType nv) → env.IsDefEqU nv Γ (.sort u) (.forallE A B) →
      SortPiEqSupplyAt V env nv Γ u A B

/-- `VEnv.RigidSortPiDisj` — one of the five conjuncts of `WF.rigidShapeUniqNS`
(`RigidNodeCircle.rigidShapeUniqNS_iff_family`) — from the model.

The `OnCtx` guard and the conversion are *discarded*, exactly as in
`SemanticRoute.semantic_sortInv_packaged`: the semantic argument never inspects the
derivation.

**Read `sortPiSupplyAll_iff` before quoting this as a reduction.**  It is not one: the
hypothesis is *equivalent* to the conclusion. -/
theorem semantic_rigidSortPiDisj (h : SortPiSupplyAll V env nv) :
    env.RigidSortPiDisj nv := fun hΓ hD => semantic_sortPiDisj (h hΓ hD)

/-- **COLLAPSE TEST, and it FAILS — stated as a theorem rather than left for a reader.**

`SortPiSupplyAll` is equivalent to `RigidSortPiDisj`, so `semantic_rigidSortPiDisj` and
`rigidShapeUniqNS_of_four` are **restatements**, not reductions: once `SortPiEqSupplyAt` is
refuted, "the supply exists for every such conversion" says only "there is no such conversion".

This is exactly the trap `ORCHESTRATOR.md` rule 5 is about, and it is worth spelling out how it
differs from the upstream case it imitates.  `SemanticRoute.semantic_sortInv_packaged` has the
same *shape*, and does **not** collapse, because its supply `SortEqSupply` is satisfiable —
`SemanticRoute.sortEqRaw_iff`'s `←` direction is precisely the check that every true instance of
`u ≈ v` produces the datum.  Here the supply is refuted, so the packaging carries no content.

**Where the content actually is: `interp_sort_ne_interp_forallE`**, which takes no supply, no
`env`, no conversion, and is not equivalent to anything in the corner.  What it says is that the
model can never *witness* sort/Π confusion — so when the deferred inputs of `SetModel.sound`
(`hle`, `henv`, `hS`, `hC : CoherentOn`, `hR`, `hRd`) are discharged, `RigidSortPiDisj` follows
from them and this theorem, with no further residual.  Until then the honest statement is the
unconditional one, and this `iff` is the receipt. -/
theorem sortPiSupplyAll_iff : SortPiSupplyAll V env nv ↔ env.RigidSortPiDisj nv := by
  refine ⟨semantic_rigidSortPiDisj, fun h => ?_⟩
  intro Γ u A B hΓ hD
  exact absurd hD (h hΓ)

/-- **The narrowing, written out.**  `RigidNodeCircle.rigidShapeUniqNS_of_family` takes five
conjuncts; with the model supplying the sort/Π one, the open bridge
`Injectivity.WF.rigidShapeUniqNS` has a **four**-conjunct residual. -/
theorem rigidShapeUniqNS_of_four (hord : VEnv.Ordered env) (htr : env.ProofTransport nv)
    (hsup : SortPiSupplyAll V env nv)
    (hpi : env.PiInv nv) (hca : env.RigidConstAppInv nv)
    (hcp : env.RigidConstPiDisj nv) (hcs : env.RigidConstSortDisj nv) :
    env.RigidShapeUniqNS nv :=
  VEnv.rigidShapeUniqNS_of_family hord htr hpi (semantic_rigidSortPiDisj (V := V) hsup) hca hcp hcs

end Supply

/-! ## §4 Non-vacuity and the boundary controls

Three checks, in the order `ORCHESTRATOR.md` asks for them: the separating element is not the
obvious one; the neighbouring *strengthening* is false; and the technique demonstrably stops
where the file says it stops.
-/

section Controls
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **CONTROL 1: the obvious separating element does not work.**  `•` itself is in every
universe stage *and* in a `∀` node — take the empty domain, where the impredicative `∀` is
`True = {•}`.  So the argument cannot be run with `pt`; it has to be run with `{pt}`, and the
one-element difference between the two is the whole proof. -/
theorem pt_mem_U {n i : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (hi : i ≤ n) :
    (pt : V) ∈ U κ i :=
  U_mono hκ (Nat.zero_le i) hi _ (by rw [U_zero]; exact empty_mem_UProp)

theorem pt_mem_piProp_empty {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    (pt : V) ∈ piProp (∅ : V) B hB := by rw [piProp_empty]; simp

/-- **CONTROL 2: the neighbouring strengthening is FALSE.**  "A universe stage and a `∀` node
are *disjoint*" — which is what one would write down first, and which would make the argument
uniform in the choice of element — fails at the same witness: `•` lies in both.  So the
separation really is by one distinguished element and not by any structural incompatibility
between the two kinds of set. -/
theorem U_piProp_not_disjoint {n i : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (hi : i ≤ n)
    {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    ∃ z : V, z ∈ U κ i ∧ z ∈ piProp (∅ : V) B hB :=
  ⟨pt, pt_mem_U hκ hi, pt_mem_piProp_empty⟩

end Controls

section ConstBoundary
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ}

/-- **CONTROL 3 — the boundary, and it is why this file closes ONE conjunct and not three.**

`RigidConstSortDisj` and `RigidConstPiDisj` are negative statements too, so the *shape* of the
argument above applies to them.  It nevertheless delivers nothing, because
`interp M L Γ (.const c us) = M.cnst c us` and `M.cnst` is a **free parameter** of
`ModelData`: for *any* target set `t` there is a model in which every constant denotes `t`.
Take `t := U κ i` and the const/sort route dies; take `t := ` a `∀` node's denotation and the
const/Π route dies.

This file once said that closing those two semantically "needs `Coherent` — the constraint
linking `M.cnst` to the declarations, which `Theory/SetModel/` does not yet construct".
**CORRECTED 2026-08-31:** `CoherentOn` *is* constructed (`SetModel/CoherentWitness.lean`'s
`coherentOn_witness`, `SetModel/CnstRecursion.lean`'s `coherentOn_cnstOf`), and the
`CoherentOn`-guarded residual is **false** — `SetModel/CoherentConstShape.lean`'s
`not_coherentConstNotUniv` and `not_coherentConstNotPi`.  `CoherentOn.const_type` pins
`M.cnst c us` only by *membership* in `⟦ci.type⟧`, which both target shapes satisfy.  So the
count is 5 → 4 **permanently**, and the two constant-spine conjuncts have no semantic route at
all rather than one waiting on a construction. -/
theorem const_denot_arbitrary (κ : ℕ → V) (ls : List ℕ) (t : V) :
    ∃ M : ModelData V, M.κ = κ ∧ M.ls = ls ∧
      ∀ (L : PropSplit env nv) (Γ : List VExpr) (c : Lean.Name) (us : List VLevel) (ρ : V),
        (interp M L Γ (.const c us)).toFun ρ = t :=
  ⟨⟨κ, ls, fun _ _ => t⟩, rfl, rfl, fun L Γ c us ρ => interp_const _ L Γ c us ρ⟩

/-- **CONTROL 4: in the empty context the supply's `ρ ∈ interpCtx` guard costs nothing.**

`SortPiEqSupply` inherits that guard from `SemanticRoute.SortEqSupply`, and in a context whose
interpretation is empty the guard makes the supply unsatisfiable — so the packaged route
delivers `RigidSortPiDisj` only where the context has a valuation.  The caveat is *inherited,
not introduced*: `semantic_sortInv_packaged` carries exactly the same one.  And
`SortPiEqSupplyAt` drops the guard altogether, so the route this file actually runs on does not
have it. -/
theorem empty_ctx_has_valuation (M : ModelData V) (L : PropSplit env nv) :
    (∅ : V) ∈ interpCtx M L [] := by rw [interpCtx_nil]; simp

end ConstBoundary

/-! ## §4b The two constant-spine conjuncts: their semantic residual, named and refuted

`RigidConstSortDisj` and `RigidConstPiDisj` are negative statements, so §1's principle applies
to them in shape.  This section says exactly what it would take and why it is not available:
the residual is a statement about `M.cnst`, and *unguarded* it is false, in the same idiom as
`SemanticRoute.not_levelSeparating`.
-/

section ConstResidual
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ}

/-- **The residual of the part-4 route to `RigidConstSortDisj`**, at the simplest instance (a
bare constant, empty spine): a constant never denotes a universe stage. -/
def ConstNotUniv (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ (M : ModelData V) (c : Lean.Name) (us : List VLevel) (i : ℕ), M.cnst c us ≠ U M.κ i

/-- **The residual is exactly the part-4 datum**: at a bare constant the interpretation carries
nothing but `M.cnst`, so "the denotations coincide" and "the assignment coincides" are the same
statement.  One rewrite, and it is what makes the refutation below relevant rather than a fact
about an unrelated function. -/
theorem interp_const_eq_U_iff (M : ModelData V) (L : PropSplit env nv) (Γ : List VExpr)
    (c : Lean.Name) (us : List VLevel) (ρ : V) (i : ℕ) :
    (interp M L Γ (.const c us)).toFun ρ = U M.κ i ↔ M.cnst c us = U M.κ i := by
  rw [interp_const]

/-- **BOUNDARY CONTROL: the residual is FALSE unguarded**, exactly as
`SemanticRoute.not_levelSeparating` is for the part-3 route to `SortUniq`.  `ModelData.cnst` is
a free field, so a model may assign a universe stage to a constant.

Consequence, and it is the reason this file closes **one** conjunct and not three: the two
constant-spine conjuncts are unreachable from `interp` alone.

**CORRECTED 2026-08-31.**  This docstring used to continue "they become reachable only under
`Coherent` — the constraint tying `M.cnst` to the declarations — which `Theory/SetModel/` does
not yet construct".  `CoherentOn` is constructed twice (`coherentOn_witness`,
`coherentOn_cnstOf`), and `SetModel/CoherentConstShape.lean` **refutes the guarded residual**:
`not_coherentConstNotUniv`, `not_coherentConstNotUniv_chain`, `not_coherentConstNotPi`, with
`coherent_const_denot_eq_sort` / `_eq_forallE` as the witnesses and `oracleOK_univ` closing the
`Cnst.OracleOK` escape.  `CoherentOn.const_type` constrains `M.cnst c us` by *membership* in
`⟦ci.type⟧` and nothing else, and the refuted guard (whole-environment rule-freeness) is
*stronger* than the `RuleFreeHead c` these conjuncts supply, so weakening it cannot help.

So the classification of `WF.rigidShapeUniqNS`'s five conjuncts by semantic reachability is:
`PiInv` and `RigidConstAppInv` are *positive* and need faithfulness (absent from any soundness
model); `RigidSortPiDisj` is *negative* and needs nothing further (§3); `RigidConstPiDisj` and
`RigidConstSortDisj` are *negative* and **dead under `Coherent` too**.  One usable conjunct of
five, permanently. -/
theorem not_constNotUniv : ¬ ConstNotUniv V := by
  intro h
  exact h ⟨fun _ => (∅ : V), [], fun _ _ => U (fun _ => (∅ : V)) 0⟩ .anonymous [] 0 rfl

end ConstResidual

/-! ## §4c The model is BLIND in an uninhabited context — a limit on every semantic route

Both `SortPiEqSupply` here and `SemanticRoute.SortEqSupply` upstream demand
`ρ ∈ interpCtx M L Γ`, because that is what `Sound.eq` quantifies over.  In a context whose
interpretation is empty there is no such `ρ`, and the supply is **refuted** — not deferred.

`Γ = [∀ p : Prop, p]` is such a context, in *every* model and on *both* branches of the proof
split, and it is a legitimate one: `OnCtx [vFalse] (env.IsType nv)` holds over every `env`.

This is a correction to `Theory/SemanticRouteClosed.lean`, whose table records the part-4 route
to `SortInv` as "CLOSED, and exact".  The exactness check there
(`sortEqRaw_iff`) is about `SortEqRaw`, which has no context and no `ρ`; it does not certify
`SortEqSupply`, and `not_sortEqSupply` below shows `SortEqSupply` is false at this `Γ` for
*every* pair of levels — including equivalent ones.  So the semantic route to `SortInv`,
like the one to `RigidSortPiDisj`, is available only where the context has a valuation.
-/

section Blind
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ}

/-- `∀ p : Prop, p` — the canonical empty type. -/
def vFalse : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- It is a legitimate context entry: a type, over every environment. -/
theorem onCtx_vFalse : OnCtx [vFalse] (env.IsType nv) :=
  ⟨trivial, _, VEnv.HasType.forallE (VEnv.HasType.sort trivial) (VEnv.HasType.bvar .zero)⟩

/-- **`⟦∀ p : Prop, p⟧ = ∅`, on both branches.**  Impredicatively because `False ∈ Prop` and
no `z` is in it; predicatively because a function on `Prop` would have to take a value in
`False`. -/
theorem interp_vFalse (M : ModelData V) (L : PropSplit env nv) :
    (interp M L [] vFalse).toFun (∅ : V) = (∅ : V) := by
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have hdom : (interp M L [] (VExpr.sort .zero)).toFun (∅ : V) = (UProp : V) := by
    rw [interp_sort]; rfl
  have hbody : ∀ v : V,
      (interp M L [VExpr.sort .zero] (VExpr.bvar 0)).toFun (snoc (∅ : V) v) = v := by
    intro v
    rw [interp_bvar]
    simpa using snoc_value_at_len (Γ := ([] : List VExpr)) M L hnil (v := v)
  have hempty : (∅ : V) ∈ (interp M L [] (VExpr.sort .zero)).toFun (∅ : V) := by
    rw [hdom]; exact empty_mem_UProp
  refine subset_empty_iff_eq_empty.mp fun z hz => ?_
  simp only [vFalse] at hz
  by_cases h : L.IsProp M ([VExpr.sort .zero]) (VExpr.bvar 0)
  · obtain ⟨rfl, hz2⟩ := (mem_interp_forallE_prop_iff M L h).mp hz
    have := hz2 _ hempty
    rw [hbody] at this
    exact absurd this not_mem_empty
  · rw [interp_forallE_type M L h] at hz
    obtain ⟨hfun, hsep⟩ := mem_mkForallType_iff.mp hz
    obtain ⟨y, _, hmem⟩ := exists_of_mem_function hfun _ hempty
    have := hsep _ hempty y hmem
    rw [hbody] at this
    exact absurd this not_mem_empty

/-- The context has no valuation. -/
theorem interpCtx_vFalse (M : ModelData V) (L : PropSplit env nv) :
    interpCtx M L [vFalse] = (∅ : V) := by
  refine subset_empty_iff_eq_empty.mp fun r hr => ?_
  obtain ⟨ρ, hρ, v, hv, rfl⟩ := (mem_interpCtx_cons M L).mp hr
  rw [interpCtx_nil] at hρ
  rcases mem_singleton_iff.mp hρ with rfl
  rw [interp_vFalse M L] at hv
  exact absurd hv not_mem_empty

/-- **This file's supply is refuted at that context.** -/
theorem not_sortPiEqSupply {u : VLevel} {A B : VExpr} :
    ¬ SortPiEqSupply V env nv [vFalse] u A B := by
  intro h
  obtain ⟨_, M, L, ρ, _, _, hρ, _, _⟩ := h []
  rw [interpCtx_vFalse] at hρ
  exact absurd hρ not_mem_empty

/-- **And so is `SemanticRoute.SortEqSupply`, for every pair of levels** — the correction to the
"CLOSED, and exact" row described in this section's header. -/
theorem not_sortEqSupply {u v : VLevel} :
    ¬ SemanticRoute.SortEqSupply V env nv [vFalse] u v := by
  intro h
  obtain ⟨_, M, L, ρ, _, _, hρ, _, _, _⟩ := h []
  rw [interpCtx_vFalse] at hρ
  exact absurd hρ not_mem_empty

/-- **The consequence for the upstream "CLOSED" row, machine-checked: the *packaged* form of the
part-4 route to `SortInv` is VACUOUS.**

`SemanticRoute.semantic_sortInv_packaged` takes exactly the hypothesis negated here, and that
hypothesis is false over **every** environment and every `nv` — no `env` is exempt, because the
instance that kills it is reflexivity of `.sort .zero` in the context `[∀ p : Prop, p]`, which
every environment admits.

Read the verdict precisely, because it is not "the route is wrong":

* `SemanticRoute.semantic_sortInv` — the *unpackaged* implication `SortEqSupply → u ≈ v` — is
  fine, and so is `sortEqRaw_iff`.  What they say is that *where the model can see the
  conversion*, it delivers the level equation exactly.
* What is vacuous is the ∀-over-all-contexts packaging, and the reason has nothing to do with
  levels: the model has no valuation for a context containing an empty type, so part 4 supplies
  nothing there.
* The same defect afflicts this file's packaging, in the weaker form
  `sortPiSupplyAll_iff` records: `SortPiSupplyAll` is not *false* (there is no sort/Π conversion
  to supply for, so the empty-context instance is vacuously satisfied) but it is equivalent to
  its own conclusion.

Either way the operative statement is the unconditional one -- `U_injOn` there,
`interp_sort_ne_interp_forallE` here -- and any route that wants to *use* the model on a
judgement in an arbitrary context owes a valuation for that context. -/
theorem sortInvSupply_vacuous :
    ¬ (∀ {Γ : List VExpr} {u v : VLevel}, OnCtx Γ (env.IsType nv) →
        env.IsDefEqU nv Γ (.sort u) (.sort v) → SemanticRoute.SortEqSupply V env nv Γ u v) := by
  intro h
  exact not_sortEqSupply (V := V)
    (h (Γ := [vFalse]) (u := .zero) (v := .zero) onCtx_vFalse ⟨_, VEnv.HasType.sort trivial⟩)

end Blind

section Audit
/-! ## §5 Axiom check -/

#print axioms Lean4Lean.InjSortPi.singleton_pt_ne_pt
#print axioms Lean4Lean.InjSortPi.true_not_mem_piProp
#print axioms Lean4Lean.InjSortPi.true_not_mem_function
#print axioms Lean4Lean.InjSortPi.true_not_mem_mkForallType
#print axioms Lean4Lean.InjSortPi.true_not_mem_mkForallProp
#print axioms Lean4Lean.InjSortPi.true_mem_U
#print axioms Lean4Lean.InjSortPi.true_not_mem_interp_forallE
#print axioms Lean4Lean.InjSortPi.interp_sort_ne_interp_forallE
#print axioms Lean4Lean.InjSortPi.sortPiEqSupplyAt_of_supply
#print axioms Lean4Lean.InjSortPi.semantic_sortPiDisj
#print axioms Lean4Lean.InjSortPi.semantic_rigidSortPiDisj
#print axioms Lean4Lean.InjSortPi.sortPiSupplyAll_iff
#print axioms Lean4Lean.InjSortPi.rigidShapeUniqNS_of_four
#print axioms Lean4Lean.InjSortPi.pt_mem_U
#print axioms Lean4Lean.InjSortPi.pt_mem_piProp_empty
#print axioms Lean4Lean.InjSortPi.U_piProp_not_disjoint
#print axioms Lean4Lean.InjSortPi.const_denot_arbitrary
#print axioms Lean4Lean.InjSortPi.empty_ctx_has_valuation
#print axioms Lean4Lean.InjSortPi.interp_const_eq_U_iff
#print axioms Lean4Lean.InjSortPi.not_constNotUniv
#print axioms Lean4Lean.InjSortPi.not_sortEqSupply
#print axioms Lean4Lean.InjSortPi.sortInvSupply_vacuous
#print axioms Lean4Lean.InjSortPi.not_sortPiEqSupply
#print axioms Lean4Lean.InjSortPi.interpCtx_vFalse
#print axioms Lean4Lean.InjSortPi.interp_vFalse
#print axioms Lean4Lean.InjSortPi.onCtx_vFalse

end Audit

end Lean4Lean.InjSortPi
