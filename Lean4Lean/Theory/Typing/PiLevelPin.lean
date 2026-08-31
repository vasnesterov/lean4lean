import Lean4Lean.Theory.Typing.Injectivity

/-!
# Pinning the levels of a Π type from `IsDefEq.uniq`'s own invariant

`Theory/Typing/Injectivity.lean`'s `IsDefEqU.forallE_inv_stratified` (the file's largest
hole, by transitive users) has exactly one consumer: the `app` case of `uniqQ`, which is
`IsDefEq.uniq`'s induction body.  This file measures that call site: it separates the part
of the demand that the induction can already pay for from the part that it cannot, and
machine-checks that the residue is not reachable by level arithmetic.

## What the invariant already buys

`UniqAux env U n` (`Injectivity.lean`) carries the clause `A = .sort s₁ → B = .sort s₂ →
s₁ ≈ s₂`, and `sortType_level` reads the level of a *sort's* type off it.  The reason that
works is an index accident: `HasTypeStratified.sort'` concludes at **every** index, so the
canonical typing `Γ ⊢ .sort s : .sort (.succ s) !! n` is free at whatever index the
invariant is available.  `HasTypeStratified.forallE` concludes at `n+1` from premises at
`n`, so the canonical typing of a Π costs `+1` and the same move does not go through
directly.

`forallEType_level` below recovers it anyway, by first *descending* with
`HasTypeStratified.forallE_inv'` (premises at `k-1`) and then rebuilding at `(k-1)+1 = k`.
So the level of a Π type is pinned by the invariant at the *same* index, just like a sort's:

    Γ ⊢ .forallE A B : .sort w !! k    ⟹    w ≈ .imax u v

for the domain/codomain levels the derivation itself supplies.

`app_domain_level` is the second free ingredient, and it comes from a premise that `uniqQ`'s
`app` case currently discards.  `HasTypeStratified.app`'s sixth premise types the *argument*
at the domain: both derivations of `.app f a` give `Γ ⊢ a : A !! n` and `Γ ⊢ a : A' !! n`,
so the invariant applied to *those* two typings yields `u ≈ u'` — the **domain** levels of
the two Π types of `f` agree, with no appeal to Π-injectivity at all.

Putting the two together (`app_pi_levels_free`), the `app` case gets, for free:

    u ≈ u'   and   .imax u v ≈ .imax u' v'

and what it still needs in order to close is `v ≈ v'` together with the codomain conversion.

## Why that residue is not an arithmetic consequence

`imax_cod_not_pinned` machine-checks that `u ≈ u'` and `.imax u v ≈ .imax u' v'` do **not**
entail `v ≈ v'`: at `u = u' = 2`, `v = 1`, `v' = 2` both hypotheses hold and `1 ≉ 2`.  So no
amount of level bookkeeping can finish the `app` case; the codomain levels have to come from
inverting the conversion between the two Π types, which is the hole.

`imax_cod_prop_iff` records what *is* extractable: the pinning decides whether the codomain
is a `Prop`, and nothing finer.  This is the exact strength of the free half.

Nothing in this file is an axiom or a `sorry`; all four statements are proved outright, and
`forallEType_level`/`app_domain_level` are stated so that `uniqQ` can use them verbatim
(their `UniqAux env U k` hypothesis is what `uniqQ`'s `IH` delivers for every `k < n`).
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- **The level of a Π type is pinned by `IsDefEq.uniq`'s invariant, at the same index.**

The Π analogue of `Injectivity.lean`'s `sortType_level`.  The `+1` that
`HasTypeStratified.forallE` costs is paid by first descending with `forallE_inv'`: its
premises land at `k-1`, and rebuilding puts the canonical typing back at `(k-1)+1 = k`,
which is where the invariant is available. -/
theorem forallEType_level (henv : VEnv.WF env) {Γ : List VExpr} {A B : VExpr} {w : VLevel}
    {k : Nat} (hU : UniqAux env U k) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.HasTypeStratified U Γ (.forallE A B) (.sort w) true k) :
    ∃ u v, u.WF U ∧ v.WF U ∧ w ≈ .imax u v ∧
      env.HasTypeStratified U Γ A (.sort u) true (k-1) ∧
      env.HasTypeStratified U (A::Γ) B (.sort v) true (k-1) := by
  obtain ⟨hk, u, v, hA, hB⟩ := h.forallE_inv'
  have hΓ' : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA.hasType⟩
  have hu : u.WF U := have ⟨_, t⟩ := hA.hasType.isType henv hΓ; t.sort_inv henv
  have hv : v.WF U := have ⟨_, t⟩ := hB.hasType.isType henv hΓ'; t.sort_inv henv
  have hcanon : env.HasTypeStratified U Γ (.forallE A B) (.sort (.imax u v)) true k := by
    have := HasTypeStratified.base (HasTypeStratified.forallE hu hv hA hB)
    rwa [Nat.sub_add_cancel hk] at this
  have ⟨_, _, _, _, _, _, hc⟩ := hU hΓ (Nat.le_refl k) (Nat.le_refl k) h hcanon
  exact ⟨u, v, hu, hv, hc _ _ rfl rfl, hA, hB⟩

/-- **The domain levels of two Π types of one function agree — for free.**

`HasTypeStratified.app`'s sixth premise types the argument at the domain, so the two
derivations of `.app f a` hand over `Γ ⊢ a : A !! n` and `Γ ⊢ a : A' !! n`.  Feeding *those*
to the invariant produces a conversion `A ≡ A'` and, through the sort clause, the level
agreement.  No Π-injectivity is used; `uniqQ`'s `app` case currently discards this premise
(it appears as `_` in the pattern `.app _ _ b3 b4 b5 _ b7`). -/
theorem app_domain_level {Γ : List VExpr} {a A A' : VExpr} {u u' : VLevel} {n₁ n₂ k : Nat}
    (hU : UniqAux env U k) (hΓ : OnCtx Γ (env.IsType U)) (le₁ : n₁ ≤ k) (le₂ : n₂ ≤ k)
    (hA : env.HasTypeStratified U Γ A (.sort u) true n₁)
    (hA' : env.HasTypeStratified U Γ A' (.sort u') true n₂)
    (ha : env.HasTypeStratified U Γ a A true n₁)
    (ha' : env.HasTypeStratified U Γ a A' true n₂) : u ≈ u' := by
  obtain ⟨_, _, _, hzz', hz, hz', -⟩ := hU hΓ le₁ le₂ ha ha'
  have ⟨_, _, _, _, _, _, c1⟩ :=
    hU hΓ le₁ (Nat.le_trans (Nat.sub_le ..) (Nat.le_refl k)) hA hz
  have ⟨_, _, _, _, _, _, c2⟩ :=
    hU hΓ le₂ (Nat.le_trans (Nat.sub_le ..) (Nat.le_refl k)) hA' hz'
  exact (c1 _ _ rfl rfl).trans (hzz'.trans (c2 _ _ rfl rfl).symm)

/-- **Everything `uniqQ`'s `app` case gets for free.**

The configuration is the one produced by two `HasTypeStratified.app` derivations of the same
`.app f a`, plus the invariant one index down (which `uniqQ`'s `IH` supplies).  The output is
the whole level-side content that does *not* need Π-injectivity. -/
theorem app_pi_levels_free (henv : VEnv.WF env) {Γ : List VExpr} {a A B A' B' : VExpr}
    {u v u' v' w w' : VLevel} {k : Nat}
    (hU : UniqAux env U k) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasTypeStratified U Γ A (.sort u) true k)
    (hB : env.HasTypeStratified U (A::Γ) B (.sort v) true k)
    (hA' : env.HasTypeStratified U Γ A' (.sort u') true k)
    (hB' : env.HasTypeStratified U (A'::Γ) B' (.sort v') true k)
    (ha : env.HasTypeStratified U Γ a A true k)
    (ha' : env.HasTypeStratified U Γ a A' true k)
    (hpi : env.HasTypeStratified U Γ (.forallE A B) (.sort w) true k)
    (hpi' : env.HasTypeStratified U Γ (.forallE A' B') (.sort w') true k)
    (hww' : w ≈ w') : u ≈ u' ∧ VLevel.imax u v ≈ VLevel.imax u' v' := by
  refine ⟨app_domain_level hU hΓ (Nat.le_refl k) (Nat.le_refl k) hA hA' ha ha', ?_⟩
  obtain ⟨u₁, v₁, _, _, e1, hA₁, hB₁⟩ := forallEType_level henv hU hΓ hpi
  obtain ⟨u₂, v₂, _, _, e2, hA₂, hB₂⟩ := forallEType_level henv hU hΓ hpi'
  have le' : k - 1 ≤ k := Nat.sub_le ..
  have hΓ₁ : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA.hasType⟩
  have hΓ₂ : OnCtx (A'::Γ) (env.IsType U) := ⟨hΓ, _, hA'.hasType⟩
  have ⟨_, _, _, _, _, _, c1⟩ := hU hΓ (Nat.le_refl k) le' hA hA₁
  have ⟨_, _, _, _, _, _, c2⟩ := hU hΓ₁ (Nat.le_refl k) le' hB hB₁
  have ⟨_, _, _, _, _, _, c3⟩ := hU hΓ (Nat.le_refl k) le' hA' hA₂
  have ⟨_, _, _, _, _, _, c4⟩ := hU hΓ₂ (Nat.le_refl k) le' hB' hB₂
  -- `w ≈ imax u v` and `w' ≈ imax u' v'`, then transport along `w ≈ w'`.
  have f1 : w ≈ VLevel.imax u v :=
    e1.trans (VLevel.imax_congr (c1 _ _ rfl rfl).symm (c2 _ _ rfl rfl).symm)
  have f2 : w' ≈ VLevel.imax u' v' :=
    e2.trans (VLevel.imax_congr (c3 _ _ rfl rfl).symm (c4 _ _ rfl rfl).symm)
  exact f1.symm.trans (hww'.trans f2)

/-! ## The residue is not an arithmetic consequence -/

/-- **The free half does not pin the codomain level.**

`u ≈ u'` and `.imax u v ≈ .imax u' v'` — everything `app_pi_levels_free` delivers — leave
`v ≈ v'` undetermined.  Witness: `u = u' = 2`, `v = 1`, `v' = 2`, where
`imax 2 1 = 2 = imax 2 2` and `1 ≉ 2`.

Consequence: `uniqQ`'s `app` case cannot be closed by level bookkeeping.  Its residual
demand is genuinely the *conversion*-side inversion of `Γ ⊢ .forallE A B ≡ .forallE A' B'`,
i.e. `IsDefEqU.forallE_inv_stratified` itself. -/
theorem imax_cod_not_pinned :
    ∃ u u' v v' : VLevel, u ≈ u' ∧ VLevel.imax u v ≈ VLevel.imax u' v' ∧ ¬ v ≈ v' := by
  refine ⟨.succ (.succ .zero), .succ (.succ .zero), .succ .zero, .succ (.succ .zero),
    rfl, ?_, ?_⟩
  · simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
  · intro h; exact absurd (congrFun h []) (by simp [VLevel.eval])

/-- **What the pinning does decide: whether the codomain is a `Prop`.**

`.imax u v ≈ .imax u' v'` is equivalent to no more than this about `v, v'` (given the
counterexample above), so this is the exact strength of the free half. -/
theorem imax_cod_prop_iff {u v u' v' : VLevel}
    (h : VLevel.imax u v ≈ VLevel.imax u' v') : v ≈ .zero ↔ v' ≈ .zero :=
  VLevel.imax_eq_zero.symm.trans <| (VLevel.equiv_congr_left h).trans VLevel.imax_eq_zero

/-! ## The narrowing does not dodge unstratified Π-injectivity -/

/-- The **codomain half** of `PiInv`: the part of unstratified Π-injectivity that
`PiInvStratApp` actually talks about (`PiInvStratApp` has no domain conjunct at all). -/
def PiInvCod (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u)

/-- **`PiInvStratApp` implies the unstratified codomain injectivity.**

The stratified hypotheses are not a restriction: over a `VEnv.WF` environment every typed
term has *some* stratified derivation (`HasTypeStrong.stratify`), and `.mono` aligns the two
indices, so `PiInvStratApp` can always be instantiated.

Read together with `Injectivity.piInvStratApp_of` (`SortUniq ∧ PiInv → PiInvStratApp`) and
`Injectivity.sortUniq_of_piInvStratApp` (`PiInvStratApp → SortUniq`) this brackets the hole:

    SortUniq ∧ PiInv  →  PiInvStratApp  →  SortUniq ∧ PiInvCod

The only slack is the *domain* half of `PiInv`, which `PiInvStratApp` does not mention (and
cannot recover: take `B = B' = .sort .zero`, where the conclusion says nothing about `A`,
`A'`).  So **`forallE_inv_stratified` is not a weakening of the unstratified statement**: any
route that closes it also closes unstratified Π-injectivity for codomains *and* universe
uniqueness.  Attempts to make the stratified form easier by reshaping the index or the flag
cannot help; the content has to come from normalisation. -/
theorem piInvCod_of_piInvStratApp (henv : VEnv.WF env) (hpi : PiInvStratApp env U) :
    PiInvCod env U := by
  intro Γ A B A' B' hΓ h1
  obtain ⟨V, H⟩ := h1
  obtain ⟨n₁, s1⟩ := ((H.hasType.1.strong henv hΓ).hasType'.1).stratify
  obtain ⟨n₂, s2⟩ := ((H.hasType.2.strong henv hΓ).hasType'.1).stratify
  obtain ⟨u, hu, -⟩ := hpi hΓ ⟨_, H⟩
    (s1.mono (Nat.le_max_left n₁ n₂)) (s2.mono (Nat.le_max_right n₁ n₂))
  exact ⟨u, hu⟩

/-! ## The hole is now *exactly* universe uniqueness

Since `IsDefEqU.forallE_inv` became a theorem modulo the single bridge
`VEnv.WF.rigidShapeUniq`, `PiInv` is no longer an open hypothesis, and the two implications
already in `Injectivity.lean` collapse to a biconditional with nothing left over. -/

/-- **`forallE_inv_stratified` is exactly `VEnv.SortUniq`.**

`Injectivity.piInvStratApp_of` gives `SortUniq ∧ PiInv → PiInvStratApp` and
`Injectivity.sortUniq_of_piInvStratApp` gives the converse.  `Injectivity.piInv_axiom`
(`IsDefEqU.forallE_inv`, a theorem since the `RigidShapeBridge` consolidation) removes the
remaining side hypothesis `PiInv`, which every earlier statement of the equivalence had to
carry.  So the 446-user hole carries **no content beyond universe uniqueness** —
every other ingredient it was thought to need (Π-injectivity, the level bookkeeping of §1–2)
is either a theorem or free.

This is sorry-backed *through `WF.rigidShapeUniq`*, i.e. through the other, smaller hole in
`Injectivity.lean` — not through `forallE_inv_stratified` itself, and it adds no new `sorry`
of its own. -/
theorem piInvStratApp_iff_sortUniq (henv : VEnv.WF env) :
    PiInvStratApp env U ↔ env.SortUniq U :=
  (sortUniq_iff_piInvStratApp henv (piInv_axiom henv)).symm

/-- **The refutation direction needs no other hole.**  `sortUniq_of_piInvStratApp` is
`sorryAx`-free (checked: `[propext, Classical.choice, Quot.sound]`), so its contrapositive is
unconditional — unlike `piInvStratApp_iff_sortUniq`, which passes through
`WF.rigidShapeUniq` in the other direction.

Consequence: a counterexample to `SortUniq` at *any* well-formed environment refutes
`forallE_inv_stratified` outright, and with it the whole Π/sort inversion family, without
anyone having to settle `rigidShapeUniq` first.  Anyone hoping to rescue a statement by
refuting universe uniqueness at a small environment should know that this is the price. -/
theorem not_piInvStratApp_of_not_sortUniq (henv : VEnv.WF env) (h : ¬ env.SortUniq U) :
    ¬ PiInvStratApp env U := fun hpi => h (sortUniq_of_piInvStratApp henv hpi)

/-!
## The one finite instance of the circle

`DescendRefute.lean`'s witness environment `refEnv` — six axioms and `refEnv_no_defeqs` —
kills the `extra` constructor outright: no δ, no ι, no quotient rules.  So `SortUniq refEnv 0`
reduces to beta/eta/proofIrrel/trans confluence over a pure calculus with no rewrite rules,
which is the only *finite, self-contained* instance of this circle anywhere in the tree.
Proved outright it would be the first non-vacuity witness for `SortUniq`, and by
`piInvStratApp_iff_sortUniq` it would make `PiInvStratApp refEnv 0` a theorem at the same
stroke.  Not attempted here: `proofIrrel` and `trans` are still the hard cases.

Caution for anyone using `refEnv` as *satisfiability* evidence for a `SortUniq` side
hypothesis: "the `sortUniq_badEnv` failure route is closed at `refEnv`" is **not**
`refEnv`-specific.  `VEnv.WF.instL_lhs_ne_sort` (`DeclRules.lean:234`) is proved for every
`env.WF`, with no hypothesis on the environment's rule set, and `badEnv_not_wf` is exactly
that lemma applied to `badEnv`.  Reduced to its content the observation is "the general fact
holds", which is what is open; `refEnv_no_defeqs` adds nothing to it.  What `refEnv_no_defeqs`
does add is the dead `extra` case above.

## Where the demand actually comes from: `uniq`'s `defeq` case, not its `app` case

`UniqueTyping.lean`'s `IsDefEq.uniq` has an *unstratified* statement
(`∃ u, Γ ⊢ A ≡ B : .sort u`); the stratified conjuncts live only inside its `suffices`.  They
are forced by the **`defeq`** case (`UniqueTyping.lean:102`), which re-applies the invariant to
the invariant's *own output* `c3 : Γ ⊢ A' : .sort u₁ !! n-1` — not a subderivation of anything,
so it has to arrive with an index bound.  The `app` case is only a *supplier*: it must hand
back what the invariant promises, and `forallE_inv_stratified` is how it does that.

Consequence for anyone attacking this hole: run the same induction with `sort_inv` and `PiInv`
as *external* inputs and the `app` case becomes `⟨_, d3.instN henv a6.hasType .zero⟩` with no
level alignment at all, while `lam`/`forallE`/`const`/`bvar`/`sort'` need only `sort_inv`.  The
entire stratification apparatus is bookkeeping for the `defeq` case, whose demand is a
`SortUniq` instance at an unbounded index.  So the productive target is not a cleverer `app`
case (this file shows the level side of that is exhausted) but either

* a height-preserving `uniq`, so the `SortUniq` instance the `defeq` case needs is *bounded*,
  turning the circle into a chain; or
* `sort_not_proof` from an independent source.  `SortUniq.lean` notes that `sort_not_proof`
  survives cumulativity, so unlike `SortUniq` itself it is not blocked for the n-inaccessible
  model; with it, `sort_inv` follows from `WF.rigidShapeUniq` alone.

## Axiom check

    #print axioms Lean4Lean.VEnv.forallEType_level
    #print axioms Lean4Lean.VEnv.app_domain_level
    #print axioms Lean4Lean.VEnv.app_pi_levels_free
    #print axioms Lean4Lean.VEnv.imax_cod_not_pinned
    #print axioms Lean4Lean.VEnv.imax_cod_prop_iff
    #print axioms Lean4Lean.VEnv.piInvCod_of_piInvStratApp

all report `[propext, Classical.choice, Quot.sound]`.  **No `sorryAx`**, despite the import of
`Injectivity.lean`: nothing in §1–§3 consumes `forallE_inv_stratified` or anything downstream
of it.

The last one, `piInvStratApp_iff_sortUniq`, does report `sorryAx` — through
`VEnv.WF.rigidShapeUniq`, the *other* hole in `Injectivity.lean`, and not through
`forallE_inv_stratified`.  It adds no `sorry` of its own, so the census is unchanged.
-/

end VEnv
end Lean4Lean
