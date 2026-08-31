import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.Typing.SortUniqDown
import Lean4Lean.Theory.Typing.Injectivity

/-!
# The semantic route into the injectivity corner: what it delivers, and where it stops

`docs/critical-path.md` puts two unowned holes at the top of `kernel_sound`'s dependency tree,
and `Theory/Typing/RigidNodeCircle.lean` shows they decompose into **two** independent
statements, `VEnv.SortUniq` and `VEnv.PiInv`.  Every *syntactic* route to either is measured
circular (constant-application injectivity is proved via Church-Rosser, hence reaches
`IsDefEqU.weakN_iff`).  The remaining candidate is the **set model**: prove the injectivity
facts about denotations instead of about reduction.

This file measures that route.

## Step 0: the model layer is not circular, and the cone is not the whole answer

Measured with `scripts/hole-cone.lean`'s walker verbatim (`allowOpaque := true`, type *and*
value), over the union cone of **every** declaration in `SetModel/SoundInduction.lean` (50
decls, union cone 7578), `SetModel/Interp.lean` (191, 6452) and `SetModel/InterpSound.lean`
(112, 7147):

* `sorryAx`: **not reached** by any of the three.
* `VEnv.SortUniq`, `VEnv.PiInv`, `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
  `IsDefEqU.weakN_iff`, `WF.sortUniq'`, `piInvStratApp_axiom`: **none reached** by any of the
  three.

A cone can never see a hypothesis (`docs/critical-path.md` makes the same point about H1/H2),
so the cone reading alone would be worthless here -- the model layer is *parameterised*, and
the interesting question is what the parameter contains.  That is measured too, by reading the
structures rather than the cone:

* the **old** parameter `LevelAssign` did contain `SortUniq`: `LevelAssign.srt_sound` demands
  one canonical level agree with every type of a term, and `LevelAssign.srt_uniq` derives
  universe uniqueness for terms from it.  Against `LevelAssign` the model route **was**
  circular through its parameter.
* the **current** parameter is `PropSplit`, and it is not.  `PropSplit.prop_sound` /
  `proof_sound` test only `u.eval ls = 0`; they constrain levels only up to "is zero", so they
  do not imply `SortUniq`, and nothing in `PropSplit` mentions `PiInv`.

So: **the model route is not circular.**  The re-parameterisation from `LevelAssign` to
`PropSplit` is what made that true, and it is recent (`docs/model-interface.md`'s own
correction header).  `Theory/Typing/SortUniq.lean` still says "the model is parameterised on
it", which was accurate for `LevelAssign` and is now stale.

## Step 1: what the route actually delivers

The route is open, so it can be walked.  Doing so gives a finer answer than the paragraph
"There is no model route to `SortUniq`" in `Theory/Typing/SortUniq.lean` -- which is flagged
there as *analysis, not a Lean proof*, "the one claim in this file that is not machine-checked".
Everything below is machine-checked.

| Target | Route | Status |
|---|---|---|
| `SortInv` (`IsDefEqU.sort_inv`) | part 4 (`EqSound`) + `U` injective | **CLOSED, and exact** (`semantic_sortInv`, `sortEqRaw_iff`) |
| `SortUniq` | part 3 (`TypeSound`) + universes disjoint | **DEAD**: residual refuted (`hasChains_refutes_levelSeparating`) |
| `PiInv`, domain conjunct | part 4 + `forallE` domain-injective | **DEAD**: residual refuted (`not_forallPropDomInj`), *and* a second gap with no residual at all |

The asymmetry is exactly the difference between *equality* and *membership* of denotations.
Part 4 says two denotations are **equal**; the universe sequence is injective (`U_injOn`), so
`U κ i = U κ j` pins `i = j`.  Part 3 says a denotation is a **member**; the universe sequence
is *nested* (`U_mono`), so membership pins nothing.  One fact about `U` separates the statement
the model can supply from the one it cannot.

`Theory/Typing/SortUniqDown.lean` gives the sandwich `UniqTy ∧ SortInv → SortUniq → SortInv`.
The model supplies the `SortInv` end of it.  The gap it leaves is therefore **exactly unique
typing** (`UniqTy`), which is syntactic.  That is a sharper statement of the corner than
"no model route to `SortUniq`": the model does not fail to help, it helps precisely as far as
`SortInv` and no further.

## Reading guide: closure vs. reduction vs. deferral

* `semantic_sortInv` is a **closure**: `SortInv` follows from the model's part-4 conclusion with
  no residual, no hypothesis on the environment, no `sorryAx`.  `sortEqRaw_iff` shows the
  implication is an **equivalence**, so it is neither vacuous nor lossy.
* What is **deferred** is the *supply* of that conclusion (`SortEqSupply`).  `SetModel.sound`
  needs `hle`, `henv`, `hS`, `hC : CoherentOn`, `hR`, `hRd`, and nothing in `Theory/SetModel/`
  yet constructs a `ModelData.cnst` with `Coherent` -- that is the outer-recursion
  workstream's obligation (`docs/soundness-ledger.md`, H2 of `docs/critical-path.md`).  A
  deferral is not a closure and this file does not claim `SortInv`.
* `sortUniq_of_levelSeparating` is a **reduction with a refuted residual**, i.e. a dead end that
  is now measured rather than argued.
* `interp_dom_eq_of_forallPropDomInj` is the same shape for `PiInv`'s domain conjunct, with the
  extra honesty that even *granting* its residual the conclusion is an equality of denotations,
  not a derivation -- so a second, unresidualised gap (faithfulness) remains behind it.

## What this does *not* say

It does not say `SortUniq` is false -- it is true, and `Theory/Typing/UniqSort.lean` proves it
relative to `forallE_inv_stratified`.  It says the *model* cannot see it, because the model
validates a system in which it fails.  `Theory/Typing/SortUniq.lean` names that system: Lean
plus cumulativity.  `U_mono` is the machine-checked reason every nested-universe model
validates cumulativity, and `not_levelSeparating` is that observation in the form a proof
attempt actually collides with.

It also does not claim these are the *only* semantic routes.  What is proved is that the two
conclusions the model layer exposes -- `TypeSound` (part 3) and `EqSound` (part 4) -- yield
`SortInv` and nothing more.  A different semantic route would have to expose a different
conclusion; `interp` has no others.
-/

namespace Lean4Lean.SemanticRoute

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 0. The parameter measurement: the *old* parameterisation really was circular

The cone measurement in the header cannot see the model's parameter.  This section supplies the
half of the parameter measurement that *is* a Lean proof.
-/

/-- **`LevelAssign` contains `SortUniq`.**  So against the *old* parameterisation the model
route was circular through its own parameter -- and a cone measurement would never have shown
it, because a parameter is a hypothesis.

`LevelAssign.srt_uniq` (`SetModel/Interp.lean`) already records "a `LevelAssign` forces the
sorts of a term's two *different* types to agree"; this spells out that the forced statement is
literally `VEnv.SortUniq`, the 515-user hole's companion.  It is the machine-checked reason the
re-parameterisation to `PropSplit` (`docs/model-interface.md`) was not a cosmetic weakening: it
is what makes the semantic route worth walking at all.

The converse fails -- `PropSplit`'s two conditions constrain a level only up to `= 0`, so they
cannot force two levels equal -- but that direction is a reading of the structure, not a theorem
here, and is labelled as such in the header. -/
theorem levelAssign_gives_sortUniq {env : VEnv} {nv : ℕ} (L : LevelAssign env nv) :
    env.SortUniq nv := by
  intro Γ e u v _ hu hv h1 h2
  exact VLevel.succ_congr_iff.1
    (L.srt_uniq (by exact hu) (by exact hv) h1 h2 (VEnv.HasType.sort hu) (VEnv.HasType.sort hv))

/-! ## 1. The two facts about the universe sequence

Both are about `U` alone; neither mentions syntax.  They are the engine of everything below.
-/

section Universes
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **The residual of the part-3 route**: distinct universe stages are disjoint.

This is exactly what a derivation of `SortUniq` from part 3 of soundness needs.  Part 3 gives
`⟦e⟧ρ ∈ U κ (u.eval ls)` and `⟦e⟧ρ ∈ U κ (v.eval ls)`; the only way to conclude
`u.eval ls = v.eval ls` from two membership facts is for the stages to be pairwise disjoint. -/
def LevelSeparating (κ : ℕ → V) (n : ℕ) : Prop :=
  ∀ {x : V} {i j : ℕ}, i ≤ n → j ≤ n → x ∈ U κ i → x ∈ U κ j → i = j

/-- **BOUNDARY CONTROL for the part-3 route.**  `LevelSeparating` is false, and false under
exactly the hypothesis the model development already assumes -- a chain of `n` inaccessibles,
`n ≥ 1`.  So there is no chain to choose that rescues the reduction.

The witness is `∅`, which is `False` in `U κ 0 = ℘{•}` and also an element of `U κ 1`; the
inclusion is `U_mono`, i.e. the transitivity of `Vset`.  Semantically this *is* cumulativity:
`Prop`'s elements are `Sort 1`'s elements. -/
theorem not_levelSeparating {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (hn : 1 ≤ n) : ¬ LevelSeparating κ n := by
  intro h
  have h0 : (∅ : V) ∈ U κ 0 := by simp [U]
  have h1 : (∅ : V) ∈ U κ 1 := U_mono hκ (by omega) hn _ h0
  exact absurd (h (by omega) hn h0 h1) (by omega)

/-- **The engine of the part-4 route**: `U` is injective on `{0, …, n}`.

Unlike disjointness this is *true*, and it is what makes `SortInv` semantically available.
The proof is `U κ i ∈ U κ j` for `i < j` (`U_mem_of_lt`) plus foundation. -/
theorem U_injOn {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (h : U κ i = U κ j) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | rfl | hlt
  · exact absurd (h ▸ U_mem_of_lt hκ hlt hj) (by simp)
  · rfl
  · exact absurd (h ▸ U_mem_of_lt hκ hlt hi) (by simp)


/-! ### The model's standing assumption, named

`SetModel/Inaccessible.lean` builds the universe sequence from a chain; the equiconsistency
theorem supplies one of every finite length (`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`).  Naming it lets the two results
below be stated under the *same* hypothesis, which is what makes them a joint measurement
rather than two unrelated facts: the model's own assumption simultaneously makes the part-4
datum **exactly** level equivalence and makes the part-3 residual **false**. -/
def HasChains (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ n : ℕ, ∃ κ : ℕ → V, IsInaccessibleChain n κ

/-- **The part-4 datum at a sort, with `interp` unfolded away.**

`interp_sort` says the `sort` clause of the interpretation ignores everything but `M.κ` and
`M.ls`, so part 4 at a pair of sorts is exactly this statement about `U`.  Isolating it is what
makes the exactness result below possible: no `env`, no `PropSplit`, no context. -/
def SortEqRaw (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (u v : VLevel) : Prop :=
  ∀ ls : List ℕ, ∃ (n : ℕ) (κ : ℕ → V), IsInaccessibleChain n κ ∧
    u.eval ls ≤ n ∧ v.eval ls ≤ n ∧ U κ (u.eval ls) = U κ (v.eval ls)

/-- **NON-VACUITY / EXACTNESS CONTROL for the part-4 route.**

Under the model's own standing assumption the semantic datum at a pair of sorts is *equivalent*
to level equivalence -- not merely sufficient for it.  Both directions matter:

* `→` is the route working (`U_injOn`), and
* `←` is the proof that the hypothesis of `semantic_sortInv` is **not vacuous**: every true
  instance of `u ≈ v` really does produce the datum.  Without this half, `semantic_sortInv`
  could have been an argument from an empty premise -- the failure mode
  `sortConv_encoding_vacuous` (`Theory/Typing/NormalEqStrengthen.lean`) records elsewhere in
  this tree.

So the part-4 route loses nothing and invents nothing: it transports exactly `SortInv`. -/
theorem sortEqRaw_iff (hc : HasChains V) {u v : VLevel} :
    SortEqRaw V u v ↔ u ≈ v := by
  constructor
  · intro h
    rw [VLevel.equiv_def]
    intro ls
    obtain ⟨n, κ, hκ, hu, hv, heq⟩ := h ls
    exact U_injOn hκ hu hv heq
  · intro h ls
    obtain ⟨κ, hκ⟩ := hc (max (u.eval ls) (v.eval ls))
    exact ⟨_, κ, hκ, Nat.le_max_left .., Nat.le_max_right .., by
      rw [VLevel.equiv_def.mp h ls]⟩

/-- **BOUNDARY CONTROL, stated under the same hypothesis.**  `HasChains` -- the assumption that
makes the part-4 route exact -- simultaneously refutes the part-3 route's residual.  The two
halves of the measurement are therefore *jointly* satisfiable, in the sense of
`SetModel/PreludeSpec.lean`'s `preludeSpec_satisfiable`: there is no reading of the model's
hypotheses on which the part-3 route survives. -/
theorem hasChains_refutes_levelSeparating (hc : HasChains V) :
    ¬ (∀ (n : ℕ) (κ : ℕ → V), IsInaccessibleChain n κ → LevelSeparating κ n) := by
  intro h
  obtain ⟨κ, hκ⟩ := hc 1
  exact not_levelSeparating hκ le_rfl (h 1 κ hκ)

end Universes

/-! ## 2. What the model layer supplies, packaged over valuations

`VLevel`-equivalence `u ≈ v` is `∀ ls, u.eval ls = v.eval ls`, while one `ModelData` fixes one
valuation `M.ls`.  So a semantic proof of any `≈` statement needs a model *per valuation*, and
each comes with its own threshold `n` -- the `SoundAbove` shape (`SetModel/SoundInduction.lean`:
"there is a threshold `m`, produced by the induction from the derivation").  The two supply
predicates below are that shape, spelled out.

**These are hypotheses, deliberately.**  Discharging them is the outer-recursion workstream's
job: `SetModel.sound` needs `hle`, `henv`, `hS`, `hC` (`CoherentOn`), `hR`, `hRd`, and nothing
in `Theory/SetModel/` yet constructs a `ModelData.cnst` with `Coherent`.  Stating the supply
separately is what lets the *rest* of the route be measured now.
-/

section Supply
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **Part 4, packaged**: for every universe valuation there is a model at that valuation,
with a chain long enough for both levels, in which `.sort u` and `.sort v` get equal
denotations.  This is what `SetModel.sound`'s `eq` field delivers for a derivation of
`Γ ⊢ .sort u ≡ .sort v : A`. -/
def SortEqSupply (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (env : VEnv) (nv : ℕ) (Γ : List VExpr) (u v : VLevel) : Prop :=
  ∀ ls : List ℕ, ∃ (n : ℕ) (M : ModelData V) (L : PropSplit env nv) (ρ : V),
    M.ls = ls ∧ IsInaccessibleChain n M.κ ∧ ρ ∈ interpCtx M L Γ ∧
    u.eval ls ≤ n ∧ v.eval ls ≤ n ∧
    (interp M L Γ (.sort u)).toFun ρ = (interp M L Γ (.sort v)).toFun ρ

/-- **Part 3, packaged**, for a single term at two sorts.  Both typings must be seen by the
*same* model -- two separate applications of part 3 give two models and the argument does not
join up -- so they are packaged together.  `SoundAbove` supplies this: two thresholds combine
by `Above.and`. -/
def SortTypeSupply (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (env : VEnv) (nv : ℕ) (Γ : List VExpr) (e : VExpr) (u v : VLevel) : Prop :=
  ∀ ls : List ℕ, ∃ (n : ℕ) (M : ModelData V) (L : PropSplit env nv) (ρ : V),
    M.ls = ls ∧ IsInaccessibleChain n M.κ ∧ ρ ∈ interpCtx M L Γ ∧
    u.eval ls ≤ n ∧ v.eval ls ≤ n ∧
    (interp M L Γ e).toFun ρ ∈ (interp M L Γ (.sort u)).toFun ρ ∧
    (interp M L Γ e).toFun ρ ∈ (interp M L Γ (.sort v)).toFun ρ

/-! ### 2a. The part-4 route CLOSES `SortInv` -/

/-- **The bridge**: the `interp`-phrased supply is the raw one.  `interp_sort` is the whole
proof -- which is the precise sense in which the `sort` clause of the interpretation carries no
information beyond the universe index. -/
theorem sortEqRaw_of_supply {env : VEnv} {nv : ℕ} {Γ : List VExpr} {u v : VLevel}
    (h : SortEqSupply V env nv Γ u v) : SortEqRaw V u v := by
  intro ls
  obtain ⟨n, M, L, ρ, hls, hκ, _, hu, hv, heq⟩ := h ls
  rw [interp_sort, interp_sort] at heq
  subst hls
  exact ⟨n, M.κ, hκ, hu, hv, heq⟩

/-- **The semantic route to sort injectivity works, unconditionally.**

No residual, no hypothesis on `env`, no injectivity input: given the model's part-4
conclusion at every valuation, the levels are equivalent.  The only ingredient is `U_injOn`.

This is the *positive* half of the measurement, and it is new: `docs/soundness-ledger.md`
records that the model *consumes* `sort_inv` (as `LevelAssign.lvl_sound`, now weakened away to
`PropSplit`), and reads as though the model can only ever be a consumer.  It can also be a
producer, for this one statement. -/
theorem semantic_sortInv {env : VEnv} {nv : ℕ} {Γ : List VExpr} {u v : VLevel}
    (h : SortEqSupply V env nv Γ u v) : u ≈ v := by
  rw [VLevel.equiv_def]
  intro ls
  obtain ⟨n, M, L, ρ, hls, hκ, _, hu, hv, heq⟩ := h ls
  rw [interp_sort, interp_sort] at heq
  subst hls
  exact U_injOn hκ hu hv heq

/-- `SortInv` in its packaged form (`Theory/Typing/SortUniqDown.lean`), from the model.

The `OnCtx` guard and the conversion `env.IsDefEqU U Γ (.sort u) (.sort v)` are *discarded*:
the semantic argument never inspects the derivation, only its denotational consequence.  That
is the whole point -- and it is why the route escapes the Church-Rosser circle. -/
theorem semantic_sortInv_packaged {env : VEnv} {nv : ℕ}
    (h : ∀ {Γ : List VExpr} {u v : VLevel},
      OnCtx Γ (env.IsType nv) → env.IsDefEqU nv Γ (.sort u) (.sort v) →
        SortEqSupply V env nv Γ u v) :
    env.SortInv nv := fun hΓ hD => semantic_sortInv (h hΓ hD)

/-! ### 2b. The part-3 route to `SortUniq` is DEAD -/

/-- **The reduction.**  If the universe stages were disjoint, the part-3 conclusion would give
`SortUniq` at every valuation.  Stated so that the residual is isolated as a hypothesis and
nothing else is assumed. -/
theorem sortUniq_of_levelSeparating {env : VEnv} {nv : ℕ} {Γ : List VExpr} {e : VExpr}
    {u v : VLevel} (hsep : ∀ (n : ℕ) (κ : ℕ → V), IsInaccessibleChain n κ → LevelSeparating κ n)
    (h : SortTypeSupply V env nv Γ e u v) : u ≈ v := by
  rw [VLevel.equiv_def]
  intro ls
  obtain ⟨n, M, L, ρ, hls, hκ, _, hu, hv, h1, h2⟩ := h ls
  rw [interp_sort] at h1 h2
  subst hls
  exact hsep n M.κ hκ hu hv h1 h2

/-- **BOUNDARY CONTROL: the residual of the reduction above is refuted.**

`sortUniq_of_levelSeparating`'s hypothesis is unsatisfiable as soon as *one* chain of at least
one inaccessible exists in `V` -- and the existence of such chains is precisely what
`SetModel/Inaccessible.lean` assumes in order to build the model at all.  So the reduction is
not a lead: the part-3 route to `SortUniq` is closed. -/
theorem not_univ_levelSeparating {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (hn : 1 ≤ n) :
    ¬ (∀ (n : ℕ) (κ : ℕ → V), IsInaccessibleChain n κ → LevelSeparating κ n) :=
  fun h => not_levelSeparating hκ hn (h n κ hκ)

end Supply

/-! ## 3. `PiInv`'s domain conjunct: the part-4 route is DEAD too

`VEnv.PiInv` (`Theory/Typing/Injectivity.lean`) asks, from
`Γ ⊢ ∀A.B ≡ ∀A'.B'`, for `∃ u, Γ ⊢ A ≡ A' : .sort u` and a codomain conjunct.  The only
semantic input available is part 4: `⟦∀A.B⟧ρ = ⟦∀A'.B'⟧ρ`.  For that to say anything about the
domains, the `forallE` node of the interpretation would have to be injective in its domain
argument.  At the `Prop` branch that node is `mkForallProp = piProp`, and it is not.
-/

section Pi
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **The residual of the part-4 route to `PiInv`'s domain conjunct**: the impredicative
`forallE` node is injective in its domain. -/
def ForallPropDomInj (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] : Prop :=
  ∀ (A A' : V) (B B' : V → V) (hB : ℒₛₑₜ-function₁ B) (hB' : ℒₛₑₜ-function₁ B'),
    piProp A B hB = piProp A' B' hB' → A = A'

/-- **The reduction, at the interpretation.**  Domain-injectivity of the impredicative
`forallE` node is *exactly* what turns part 4 at a pair of `∀`s into information about their
domains.  `mkForallProp` is `piProp` by definition, so this is one rewrite.

Note what the conclusion is -- and is not.  It is an equality of **denotations**.  `VEnv.PiInv`
asks for `∃ u, env.IsDefEq U Γ A A' (.sort u)`, a *derivation*.  Getting from one to the other
needs the converse of soundness (denotational equality implies definitional equality), which
this model does not have and which no soundness model provides.  So the part-4 route to `PiInv`
has **two** gaps, and they are of different kinds: this one, refuted below, and a faithfulness
statement that is simply absent from the model layer.  Recording both is the point; closing the
first would still leave the second. -/
theorem interp_dom_eq_of_forallPropDomInj [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] (hinj : ForallPropDomInj V)
    {env : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit env nv}
    {Γ : List VExpr} {A B A' B' : VExpr}
    (h : L.IsProp M (A :: Γ) B) (h' : L.IsProp M (A' :: Γ) B') (ρ : V)
    (heq : (interp M L Γ (.forallE A B)).toFun ρ = (interp M L Γ (.forallE A' B')).toFun ρ) :
    (interp M L Γ A).toFun ρ = (interp M L Γ A').toFun ρ := by
  rw [interp_forallE_prop M L h, interp_forallE_prop M L h', mkForallProp, mkForallProp] at heq
  exact hinj _ _ _ _ _ _ heq

/-- **BOUNDARY CONTROL for `PiInv`.**  The impredicative `forallE` node is not
domain-injective -- and the counterexample is not pathological.  Both domains are `U κ i` for
distinct `i`, i.e. the denotations of the honest closed types `Prop` and `Sort 1`; both are
*distinct* sets (`U_injOn`); and the common codomain is the constant `True`.  So
`⟦∀ p : Prop, True⟧ = ⟦∀ x : Sort 1, True⟧`, both being `{•}`.

Consequence: part 4 carries **no** information at all about a `forallE` node's domain, not
merely insufficient information.  Any semantic derivation of `PiInv`'s domain conjunct is
therefore impossible from the model's conclusion, however the rest of the argument is
arranged. -/
theorem not_forallPropDomInj {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (hn : 1 ≤ n) : ¬ ForallPropDomInj V := by
  intro h
  have key : ∀ A : V, piProp A (fun _ => ({pt} : V)) (by definability) = ({pt} : V) := by
    intro A; ext z; simp only [mem_piProp_iff, mem_singleton_iff]
    exact ⟨And.left, fun h => ⟨h, fun _ _ => by simpa using h⟩⟩
  have := h (U κ 0) (U κ 1) _ _ (by definability) (by definability)
    ((key _).trans (key _).symm)
  exact absurd (U_injOn hκ (by omega) hn this) (by omega)

end Pi

end Lean4Lean.SemanticRoute
