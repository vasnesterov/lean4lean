import Lean4Lean.Theory.Typing.PiInvWF
import Lean4Lean.Theory.Typing.SortInvIndep

/-!
# `PiInv` at `∅`, and whether `ForallEProofPair` is vacuous

Two probes handed over by `Theory/Typing/PiInvWF.lean`, whose §2 established that at `VEnv.WF` the
**only** open refutation route for `VEnv.PiInv` is `proofIrrel`, entered by `ForallEProofPair` (two
Π's with non-convertible domains inhabiting one `Prop`) or by the weaker `SortZeroConvProp`.

**Probe 1** — `PiInv ∅ U`, which that file flagged as unrun.  `∅` *is* `VEnv.WF`, so the two
directions are wildly asymmetric: a refutation at `∅` collapses the whole corner
(`not_piInv_empty_collapses`), while a proof at `∅` generalises nothing.  §1 runs it.

**Probe 2** — the claim that `ForallEProofPair` is **vacuous**, because a Π's type is a sort and
`Sort u : Sort (u+1)` cannot be a `Prop`.  The claim came with a flagged hole: deducing "the type
of a Π is a sort" might itself need the inversion machinery under investigation, i.e. be circular.

## The answers

**§2, and it is the round's finding: the sort-hood step is NOT circular, and the vacuity of
`ForallEProofPair` is available from a hypothesis that is not `SortUniq`.**

`Theory/Typing/SortInvIndep.lean` — which `PiInvWF.lean` does not import — already proves
`forallENotProof_of_propAgreeOn`: *a Π is not a proof*, from `Ordered` plus `PropAgreeOn` (the
types of a term agree on being propositions), `sorryAx`-free and with **no `SortUniq`**.  Two
things follow, and both are new here:

| statement | content |
| --- | --- |
| `not_forallEProofPair_of_propAgreeOn` | the route's **entry** dies from `PropAgreeOn` |
| `not_propConv_of_propAgreeOn` | so does its weaker entry `SortZeroConvProp` |

So `PiInvWF.lean`'s trilemma is superseded on the entry side: a `proofIrrel` refutation of `PiInv`
now needs **`SortUniq` *and* `PropAgreeOn` to fail** (two hypotheses that this file measures to be
not related by the obvious routes — `propAgreeOn_trivial_at_sort_types` shows `PropAgreeOn`'s
conclusion is trivial at `SortUniq`'s premise shape, and that is *all* that is proved here: no
incomparability theorem is claimed, per method rule 4), while still needing a `SortUniq`-strength
discrimination at the exit.  The route is *more* closed than `PiInvWF` priced it.

And the brief's worry is answered precisely: the step is **`HasType.forallE_inv`**, which recovers
the domain and codomain typings from the Π's *own* typing at `Ordered` strength, hole-free
(`forallE_second_type` below).  One never needs "the Π's type `T` is a sort"; one needs the Π's
**second** typing `.sort (.imax u v)`, and then a level-comparison step.  The comparison is where
the cost is, and the weakest node in the tree that performs it is `PropAgreeOn`, not `SortUniq`.

**What is *not* proved: `ForallEProofPair` is not vacuous outright.**  `PropAgreeOn` is a hypothesis
with no hole-free unconditional supplier (`SortInvIndep.lean` §5: route A goes through
`IsDefEqU.forallE_inv_stratified` — the hole `PiInv` is part of — and route B is open at every index
above 0 and fixed at `nv = 0`).  So the honest statement is a **reduction**: the last refutation
route for `PiInv` is closed at every `Ordered ∧ PropAgreeOn` environment.

**§1: `PiInv ∅ U` is open, and the round did not settle it.**  What §1 does establish is the price
list, machine-checked rather than confessed:

* `∅` is `VEnv.WF` and `Ordered`, and has **no** δ-rules, so `IsDefEq.extra` is dead there
  (`empty_no_defeqs`) — this is why a refutation at `∅` would have to run through `proofIrrel`, and
  is the sense in which a *proof* at `∅` transfers to no environment carrying a rule;
* `PiInv ∅ U` follows from `PropAgreeOn ∅ U` together with `RigidShapeUniqNS ∅ U`
  (`piInv_empty_of_propAgreeOn`), both open at `∅`;
* and the refutation route at `∅` is in a **worse** position than the brief expected, not a better
  one: `∅ ≤ env` for every `env`, so a Π-in-`Prop` witness at `∅` is a witness at *every*
  environment (`isProof_forallE_empty_mono`), and therefore **one** `PropAgreeOn` instance anywhere
  in the class refutes `ForallEProofPair ∅ U` (`not_forallEProofPair_empty_of_any_propAgreeOn`).
  `∅` is the cheapest place to look for the witness and the hardest place for it to survive.

## Anti-vacuity, in the direction that matters here

Every §2 statement concludes a **negative**, so the check inverts (`SortInvIndep.lean` §7 makes the
same point about `ShapeNotProofC`): an uninhabited hypothesis set would make them true and useless.
The honest status is therefore recorded, not glossed: **`Ordered ∧ PropAgreeOn` has no hole-free
inhabitant in the tree.**  `SetModel/PropAgreeWall.preludeEnv_propTypeAgreeOnCtx` inhabits it at
`preludeEnv` *modulo* `IsDefEqU.forallE_inv_stratified`, and `PropAgreeGuarded.propAgreeOn_of_stratifiedN`
inhabits it from `PropTypeAgreeN`/`PropUniqN` at every index, discharged only at `n = 0`.  What is
*not* vacuous is the premise side: `SortInvIndep.propAgreeOn_premises_fire` shows all of
`PropAgreeOn`'s slots fire simultaneously, at `∅`, with the two types syntactically different.  And
`PiInvWF.lean`'s `SortUniq`-based negatives sit at exactly the same status (`WF.sortUniq'` is
hole-tainted), so this file's hypothesis is no worse than the one it replaces — it is a different
one, which is the point: the refuter has to defeat both.

`docs/handoff-proofirrel-vac.md` has the scorecard, the four cold questions and their predictions,
and the measured verdicts including the two predictions this round got wrong.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 Probe 1 — `PiInv ∅ U`

The environment facts first, then the two asymmetric transfer statements. -/

/-- `∅` is below every environment: it has no constants and no rules.

Named with the suffix because `Verify/Typing/ProjInhab.lean` already has `VEnv.empty_le` with this
statement, and a `Theory/` file cannot import `Verify/` without inverting the layer — measured, by
`scripts/exists.lean` refusing to load a population containing both. -/
theorem empty_le_all (env : VEnv) : (∅ : VEnv) ≤ env := ⟨nofun, nofun⟩

/-- **`∅` has no δ-rules**, so `IsDefEq.extra` cannot fire there.  This is the whole content of
"a proof of `PiInv` at `∅` generalises nothing": the `extra` rule, which is the only clause of
`IsDefEq` that mentions the environment's `defeqs`, is unreachable at `∅`. -/
theorem empty_no_defeqs (df : VDefEq) : ¬ (∅ : VEnv).defeqs df := id

/-- …and no constants, so `constDF` cannot fire either. -/
theorem empty_no_constants (n : Name) : (∅ : VEnv).constants n = none := rfl

theorem empty_ordered : Ordered (∅ : VEnv) := .empty

/-- `∅` is `VEnv.WF` — which is what makes Probe 1 worth running at all.  Already in the tree as
`InjPiRogue.empty_wf`; re-derived here only to record that the fact was measured, not assumed
(the name clash is itself the measurement, and this file cites the existing one below). -/
theorem empty_wf' : (∅ : VEnv).WF := ⟨[], .empty⟩

/-- **The asymmetry, one direction: a refutation at `∅` collapses the corner.**  Every consumer
takes `PiInv` in the form `∀ env, env.WF → PiInv env U`, and `∅` is one of those environments. -/
theorem not_piInv_empty_collapses (h : ¬ PiInv (∅ : VEnv) U) :
    ¬ ∀ env : VEnv, env.WF → PiInv env U := fun H => h (H _ empty_wf)

/-- **The asymmetry, the other direction: `PiInv ∅ U` is a *necessary* condition and nothing
more.**  It is implied by the real obligation, so proving it refutes nothing and proves nothing
about any other environment. -/
theorem piInv_empty_of_all (H : ∀ env : VEnv, env.WF → PiInv env U) : PiInv (∅ : VEnv) U :=
  H _ empty_wf

/-- **What would suffice at `∅`.**  `SortInvIndep.piInv_of_propAgreeOn` instantiated at `∅`: the
two inputs are `PropAgreeOn ∅ U` and `RigidShapeUniqNS ∅ U`, and both are open there.  Recorded so
that "Probe 1 is open" comes with the two named statements that would close it. -/
theorem piInv_empty_of_propAgreeOn (hT : PropAgreeOn (∅ : VEnv) U)
    (h : (∅ : VEnv).RigidShapeUniqNS U) : PiInv (∅ : VEnv) U :=
  piInv_of_propAgreeOn empty_wf hT h

/-- **A Π-in-`Prop` witness at `∅` is a witness at every environment.**  `∅ ≤ env` always, and
`HasType.mono` climbs.  So the positive half of `ForallEProofPair` is *hardest* to satisfy at `∅`,
not easiest — the opposite of the usual reading of "`∅` is the cheapest witness to try". -/
theorem isProof_forallE_empty_mono (env : VEnv) {Γ : List VExpr} {p A B : VExpr}
    (hp : (∅ : VEnv).HasType U Γ p (.sort .zero))
    (hf : (∅ : VEnv).HasType U Γ (.forallE A B) p) :
    env.HasType U Γ p (.sort .zero) ∧ env.HasType U Γ (.forallE A B) p :=
  ⟨hp.mono (empty_le_all env), hf.mono (empty_le_all env)⟩

/-! ## §2 Probe 2 — the vacuity claim

The sort-hood step first, because the brief's flagged hole was about it. -/

/-- **The step the brief feared was circular, and it is not.**  From a Π typed at *anything*, at
`Ordered` strength alone, one recovers its **second** typing `.sort (.imax u v)`: `forallE_inv`
gives the domain and codomain typings back out of the Π's own typing, and `forallEDF` reassembles
them.  No `SortUniq`, no `HasTypeStrong`, no `forallE_inv_stratified` — and no need for the
statement "the type of a Π is a sort" that the brief was trying to justify.

Compare `NotProof.HasTypeStrong.forallE_type`, which *does* take `SortUniq`: it proves the stronger
"`p` is convertible to a sort", which is not what the argument needs. -/
theorem forallE_second_type (hord : Ordered env) {Γ : List VExpr} {A B p : VExpr}
    (hf : env.HasType U Γ (.forallE A B) p) :
    ∃ u v, env.HasType U Γ (.forallE A B) (.sort (.imax u v)) :=
  let ⟨⟨u, hA⟩, v, hB⟩ := hf.forallE_inv hord
  ⟨u, v, IsDefEq.forallEDF hA hB⟩

/-- **The route's entry dies from `PropAgreeOn`.**  `PiInvWF.not_forallEProofPair_of_sortUniq` with
`SortUniq` replaced by the independent source; `sorryAx`-free. -/
theorem not_forallEProofPair_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U) :
    ¬ ForallEProofPair env U := by
  rintro ⟨Γ, p, A, B, _, _, hΓ, hp, h1, -, -⟩
  exact forallENotProof_of_propAgreeOn hord hT hΓ hp h1

/-- **And so does its weaker entry.**  If `.sort .zero` is convertible to a proposition then
`hasType_falseProp` retypes `∀ p : Prop, p` at that proposition, producing a Π that is a proof —
which `PropAgreeOn` forbids.  `PiInvWF.not_propConv_of_sortUniq` at the weaker hypothesis. -/
theorem not_propConv_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U) :
    ¬ SortZeroConvProp env U := by
  rintro ⟨Γ, p, z, hΓ, hp, hcv⟩
  exact forallENotProof_of_propAgreeOn hord hT hΓ hp (.defeqDF hcv hasType_falseProp)

/-- **Both entries at once** — the analogue of `PiInvWF.proofIrrel_route_self_defeating`, with
`SortUniq` replaced throughout.  Note what is *missing* relative to that theorem: the exit residual
`SortZeroOneConv`, which `PropAgreeOn` cannot touch (see `propAgreeOn_trivial_at_sort_types`). -/
theorem proofIrrel_route_entry_closed_of_propAgreeOn (hord : Ordered env)
    (hT : PropAgreeOn env U) :
    (¬ ForallEProofPair env U) ∧ (¬ SortZeroConvProp env U) :=
  ⟨not_forallEProofPair_of_propAgreeOn hord hT, not_propConv_of_propAgreeOn hord hT⟩

/-- **The dichotomy, at the new hypothesis.**  At any `Ordered` environment: either `PropAgreeOn`
fails, or the `proofIrrel` route into `PiInv` is empty.  Read against
`PiInvWF.sortUniq_of_route_open`, which says the same with `SortUniq`: **the refuter now has to
defeat both.** -/
theorem not_propAgreeOn_of_route_open (hord : Ordered env)
    (h : ForallEProofPair env U ∨ SortZeroConvProp env U) : ¬ PropAgreeOn env U :=
  fun hT => h.elim (not_forallEProofPair_of_propAgreeOn hord hT)
    (not_propConv_of_propAgreeOn hord hT)

/-- **`ForallEProofPair ∅ U` is refuted by a single `PropAgreeOn` instance anywhere.**  Probe 1's
refutation route, priced: since `∅`'s conversions hold at every environment, the witness would have
to survive at *every* environment, so it is enough that one environment in the whole class agrees
that the types of a term agree on propositionhood.

This is the strongest statement this round has about `PiInv ∅ U`, and it is a statement about the
route rather than about the conclusion: it does not prove `PiInv ∅ U`, because closing the
`proofIrrel` entry is not the same as inverting a Π-conversion. -/
theorem not_forallEProofPair_empty_of_any_propAgreeOn {env : VEnv} (hord : Ordered env)
    (hT : PropAgreeOn env U) : ¬ ForallEProofPair (∅ : VEnv) U := by
  rintro ⟨Γ, p, A, B, _, _, hΓ, hp, h1, -, -⟩
  exact forallENotProof_of_propAgreeOn hord hT
    (hΓ.mono fun h => h.mono (empty_le_all env)) (hp.mono (empty_le_all env)) (h1.mono (empty_le_all env))

/-- **The citable form: one supplier anywhere in the class is enough.**  Repackaging of the
previous theorem as the statement a client can use without naming an environment.

Two suppliers exist in the tree and **neither licenses dropping the hypothesis**, so this stays a
conditional (method rule 3): `SetModel/PropAgreeWall.preludeEnv_propTypeAgreeOnCtx` is
unconditional at `preludeEnv` but its hole cone is exactly `IsDefEqU.forallE_inv_stratified` — the
hole `PiInv` is part of — and `propAgreeOn_of_stratifiedN`
(`Theory/Typing/PropAgreeGuarded.lean`) is `sorryAx`-free but takes `PropTypeAgreeN`/`PropUniqN`
at *every* index, discharged only at `n = 0`, and is fixed at `nv = 0`.

Consequence, stated as the conditional it is: **if `forallE_inv_stratified` is true then
`ForallEProofPair ∅ U` is false**, so the `proofIrrel` refutation of `PiInv` at `∅` cannot be the
thing that refutes the corner — it could only be walked in a world where the corner's own hole
fails. -/
theorem not_forallEProofPair_empty_of_exists_propAgreeOn
    (h : ∃ env : VEnv, Ordered env ∧ PropAgreeOn env U) : ¬ ForallEProofPair (∅ : VEnv) U :=
  let ⟨_, hord, hT⟩ := h; not_forallEProofPair_empty_of_any_propAgreeOn hord hT

/-! ### The level side of the brief's argument, and the limits of `PropAgreeOn`

The brief asked for two `VLevel` facts to be checked rather than assumed.  Both hold, so the
*level* half of its vacuity argument is sound; what was wrong was the claim that sort-hood plus
levels is the whole argument. -/

/-- `succ u ≈ zero` is refutable outright, at every level and every valuation. -/
theorem not_succ_equiv_zero (u : VLevel) : ¬ (VLevel.succ u ≈ (VLevel.zero : VLevel)) :=
  fun h => absurd (congrFun h []) (by simp [VLevel.eval])

/-- **`imax` cannot launder a `succ` into `zero` from the *domain* side**: `imax u v ≈ zero`
forces `v ≈ zero`.  `VLevel.imax_eq_zero` is the fact; it is restated here because the brief's
argument uses it in the contrapositive direction, and because the *other* direction
(`VLevel.imax_zero`: `imax u zero ≈ zero`) is what makes `hasType_falseProp` work and is the
asymmetry the argument must not confuse with "a Π inhabits a `Prop`". -/
theorem imax_zero_cod {u v : VLevel} (h : VLevel.imax u v ≈ (VLevel.zero : VLevel)) :
    v ≈ (VLevel.zero : VLevel) := VLevel.imax_eq_zero.1 h

/-- **Why `PropAgreeOn` fires on the entry but not on the exit.**  Its conclusion is the
propositionhood *bit* of the two types' own levels.  When both types are **sorts** — which is the
exit residual `SortZeroOneConv`'s configuration, and also `SortUniq`'s premise shape — both levels
are `succ`s, both bits are `false`, and the conclusion is trivially true: the instrument cannot
fire.  Method rule 4 applies to `SortInvIndep.lean`'s docstring claim that `PropAgreeOn` is
"strictly weaker than `SortUniq`": what is machine-checked here is only that this *route* from it
to a sort/sort discrimination yields nothing. -/
theorem propAgreeOn_trivial_at_sort_types (u v : VLevel) (ls : List Nat) :
    ((VLevel.succ u).eval ls = 0 ↔ (VLevel.succ v).eval ls = 0) := by simp [VLevel.eval]

/-- …and the converse non-comparison, for the same reason in the other direction: `SortUniq`'s
conclusion `u ≈ v` says nothing when the two types compared are a `Prop` and a sort, because
`SortUniq` never applies to a term whose two types are `p` and `.sort (.imax u v)` — it requires
both types to be syntactic sorts.  So the entry is closed by `PropAgreeOn` for a reason `SortUniq`
does not supply, and vice versa at the exit. -/
theorem propBit_splits_entry (w : VLevel) (ls : List Nat) :
    (VLevel.zero).eval ls = 0 ∧ ¬ (VLevel.succ w).eval ls = 0 := by simp [VLevel.eval]

/-- **The distinction the brief's argument turns on, as one statement.**  `∀ p : Prop, p` is a
Π-headed term whose **type** is `.sort .zero`, in every environment and every context — so "a Π is
a `Prop`" is *free*.  `ForallEProofPair` needs the other thing: a Π that **inhabits** a
proposition.  `hasType_falseProp` supplies the first; §2 shows the second dies at
`Ordered ∧ PropAgreeOn`. -/
theorem forallE_isType_free {Γ : List VExpr} : env.IsType U Γ (.forallE (.sort .zero) (.bvar 0)) :=
  ⟨.zero, hasType_falseProp⟩

end VEnv
end Lean4Lean
