import Lean4Lean.Theory.Typing.BaseUniqChain
import Lean4Lean.Theory.Typing.SortUniqDown

/-!
# The chain-composition step, isolated — and the one place it is weaker than `SortUniq`

`Theory/Typing/BaseUniqChain.lean` establishes that the whole term-recursion route to unique
typing is free *except* for two chain-shaped hypotheses, `ConvSortInv` and `ConvPiInv`, and
that `SortUniq` is interderivable with the first given the second
(`sortUniq_iff_convSortInv`).  `HasTypeStrong.peelChain` and `uniqStrongCAt_of_baseUniqCAt`
take no hypothesis at all; **the only step that costs anything is `ConvC.collapse`**, which
composes two adjacent links of a chain and needs `SortUniq` to do it.

This file isolates that step as a `Prop` and measures it.  The finding is a genuine
narrowing, and it turns on one existential quantifier:

* `ConvStep2Level` — the composition step with the two link levels **identified** in the
  conclusion — is *equivalent* to `VEnv.SortUniq` (`convStep2Level_iff_sortUniq`, both
  directions, `sorryAx`-free).  So the level form is a restatement, not a reduction.
* `ConvStep2` — the same step with the composed conversion at an **existentially quantified**
  sort — is implied by `SortUniq` (`convStep2_of_sortUniq`) and, together with plain sort
  injectivity `SortInv` and plain Π-injectivity `PiInv`, implies it back
  (`sortUniq_of_convStep2`).  But **no route in this tree gets `SortUniq` from `ConvStep2`
  alone**: instantiating it at `X = Y = Z` returns `∃ w, … (.sort w)` and the two input levels
  are discarded, which is exactly the difference from the level form.

So, **over `PiInv`, the 534-user hole splits in two**:

    PiInvStratApp  ⟺  SortUniq  ⟺  ConvStep2 ∧ SortInv        (given PiInv)

with `SortInv` — the `sort`/`sort` entry of `Injectivity.lean`'s `RigidShapeUniq` bridge, i.e.
the same *kind* of conversion-inversion fact as every conjunct of the second hole
(`RigidNodeCircle.rigidShapeUniqNS_iff_family`) — carrying the sort-injectivity half, and
`ConvStep2` carrying the rest.  That is the first decomposition of `SortUniq` in this tree into
a part that is a bridge entry and a part that is not.  §6 states the limit of the result: it
narrows the *statement*, and there is no evidence that it narrows the *work* — the only route
to `ConvStep2` here still factors through the level form.

## What is new here and what is not

**Not new.**  `sortUniq_of_convInv`, `ConvC.collapse`, `sortUniq_iff_convSortInv`
(`BaseUniqChain.lean`); `sortUniq_of` and `SortInv.of_sortUniq` (`SortUniqDown.lean`);
`piInvStratApp_of` and `sortUniq_of_piInvStratApp` (`Injectivity.lean`).  Everything below is
built out of those.

**New.**  The two `Prop`s, the `∃`-form collapse `ConvC.collapseE` (which takes `ConvStep2`
instead of `SortUniq`), the two chain-inversion suppliers `convSortInv_of_convStep2` /
`convPiInv_of_convStep2`, the four-way bracket `sortUniq_iff_convStep2_sortInv`, and the
collapse test `convStep2Level_iff_sortUniq` that separates the two forms.

## Two corrections to the surrounding documents

**1. `PiLevelPin.lean`'s advice is right about the `app` case and does not deliver `UniqTy`.**
Its docstring says: *"run the same induction with `sort_inv` and `PiInv` as external inputs and
the `app` case becomes `⟨_, d3.instN henv a6.hasType .zero⟩` with no level alignment at all,
while `lam`/`forallE`/`const`/`bvar`/`sort'` need only `sort_inv`."*  That is accurate for the
*structural* cases, and it is **not** a route to `SortUniq`, for the reason the same docstring
gives two sentences later: the `defeq` case's demand is a `SortUniq` instance at an unbounded
index.  Written out, the failure is sharper than "unbounded": the invariant of `uniqQ` couples
the level of its output *conversion* to the level of its output *stratified* typing (the
conjunct `∃ v, u ≈ v ∧ …`), and **that coupling is load-bearing**.  Decoupling it — which is
what would let plain `PiInv` replace `PiInvStratApp` in the `app` case, since `PiInv`'s output
level is existential — breaks the `base`/`defeq` cases, where the recovered level `u₁` of the
conversion must be matched against the level `u` of the derivation's own `defeq` premise, and
the only handle on that pair is two *plain* sort-typings of the intermediate type, i.e.
`SortUniq` again and not `SortInv`.  Checked by writing the decoupled invariant out; the reason
`Injectivity.uniqQ` carries `∃ v, u ≈ v` is this and not bookkeeping. **[analysis]**

**2. `BaseUniqChain.lean`'s "next thing to try" is answered in the negative.**  Its §8-item-1
bullet asks whether the *shape* of the chains `ConvSortInv` is applied to can be exploited —
"every chain it is applied to has both endpoints syntactic sorts and arises from
`UniqStrongCAt` at a proper subterm".  It cannot be exploited *at the endpoints*: the endpoint
shape is already in `ConvSortInv`'s statement, and the obstruction is at the **interior**
links, whose midpoints are arbitrary terms carrying two unrelated sort types.  What the shape
question does yield is the split this file records: the endpoint shape is exactly what lets
`SortInv` (a single conversion between two syntactic sorts) discharge the *outer* level
comparison once the chain is collapsed, leaving `ConvStep2` — a statement with no sort
endpoints at all — as the interior residual. **[machine, for the split; analysis, for the
negative]**
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The two forms of the composition step -/

/-- **The chain-composition step, existential form.**  Two conversions at syntactic sorts
sharing an endpoint compose to a conversion at *some* syntactic sort.

This is precisely what `ConvC.collapse` (`BaseUniqChain.lean`) does with `SortUniq` in hand,
with the level of the result left free.  `ConvC.collapseE` below shows the existential form is
enough to collapse a whole chain. -/
def ConvStep2 (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X Y Z : VExpr} {a b : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ X Y (.sort a) → env.IsDefEqStrong U Γ Y Z (.sort b) →
    ∃ u, env.IsDefEqStrong U Γ X Z (.sort u)

/-- **The same step with the two link levels identified.**  The form one writes down first, and
`convStep2Level_iff_sortUniq` shows it is `VEnv.SortUniq` on the nose — so it is a restatement
and not a reduction.  Kept as the negative control for `ConvStep2`. -/
def ConvStep2Level (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X Y Z : VExpr} {a b : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ X Y (.sort a) → env.IsDefEqStrong U Γ Y Z (.sort b) → a ≈ b

/-! ## §2 The level form is exactly `SortUniq` — the collapse test that FAILS -/

/-- `SortUniq` gives the level form: the shared midpoint `Y` inhabits both sorts. -/
theorem convStep2Level_of_sortUniq (henv : Ordered env) (hsu : env.SortUniq U) :
    ConvStep2Level env U := by
  intro Γ X Y Z a b hΓ h1 h2
  exact hsu hΓ.defeq (h1.defeq.sort_r henv hΓ.defeq) (h2.defeq.sort_r henv hΓ.defeq)
    h1.hasType.2.defeq h2.hasType.1.defeq

/-- …and the level form gives `SortUniq` back, by taking `X = Y = Z`.  So the level form
carries **no content beyond universe uniqueness**. -/
theorem sortUniq_of_convStep2Level (henv : Ordered env) (h : ConvStep2Level env U) :
    env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := CtxStrong.strong henv hΓ
  exact h hΓ' (h1.strong henv hΓ) (h2.strong henv hΓ)

/-- **The collapse test, FAILING for the level form.**  `ConvStep2Level` is `VEnv.SortUniq`,
both directions, `sorryAx`-free.  This is why the existential in `ConvStep2` is not cosmetic:
it is the whole difference between a restatement and a reduction. -/
theorem convStep2Level_iff_sortUniq (henv : Ordered env) :
    ConvStep2Level env U ↔ env.SortUniq U :=
  ⟨sortUniq_of_convStep2Level henv, convStep2Level_of_sortUniq henv⟩

/-- The existential form is weaker than the level form on its face — one `atSort`. -/
theorem convStep2_of_convStep2Level (henv : Ordered env) (h : ConvStep2Level env U) :
    ConvStep2 env U := by
  intro Γ X Y Z a b hΓ h1 h2
  have ha := h1.defeq.sort_r henv hΓ.defeq
  have hb := h2.defeq.sort_r henv hΓ.defeq
  exact ⟨a, h1.trans (h2.atSort hb ha (h hΓ h1 h2).symm)⟩

/-- **Upper bound: `ConvStep2` is no stronger than `SortUniq`.**  So assuming it assumes
nothing beyond the statement it is used to attack. -/
theorem convStep2_of_sortUniq (henv : Ordered env) (hsu : env.SortUniq U) : ConvStep2 env U :=
  convStep2_of_convStep2Level henv (convStep2Level_of_sortUniq henv hsu)

/-! ## §3 The existential form collapses a whole chain -/

/-- **`ConvC.collapse` with `SortUniq` replaced by `ConvStep2`.**

`BaseUniqChain.ConvC.collapse` needs a reflexivity witness `IsDefEqStrong Γ A A (.sort u)` for
the left endpoint, which is where it also needs the level; the existential form needs no such
witness, at the price of returning the `refl` case as a syntactic equation.  Both callers below
have the endpoint shape that makes that free. -/
theorem ConvC.collapseE (hcs : ConvStep2 env U) {Γ : List VExpr} (hΓ : CtxStrong env U Γ) :
    ∀ {A B : VExpr}, ConvC env U Γ A B →
      A = B ∨ ∃ u, env.IsDefEqStrong U Γ A B (.sort u) := by
  intro A B h
  induction h with
  | refl => exact .inl rfl
  | @step A B C u hl _ ih =>
    match ih with
    | .inl eq => exact .inr ⟨u, eq ▸ hl⟩
    | .inr ⟨v, hr⟩ => exact .inr (hcs hΓ hl hr)

/-! ## §4 The two chain-inversion hypotheses, supplied -/

/-- **`ConvSortInv` from `ConvStep2` and plain sort injectivity.**

The chain's endpoints are syntactic sorts, so the `refl` case is a syntactic equation and the
collapsed case hands `SortInv` exactly its own premise — one `IsDefEqU` between two sorts. -/
theorem convSortInv_of_convStep2 (hcs : ConvStep2 env U) (hsi : env.SortInv U) :
    ConvSortInv env U := by
  intro Γ u v hΓ h
  match h.collapseE hcs hΓ with
  | .inl eq => cases eq; rfl
  | .inr ⟨_, hw⟩ => exact hsi hΓ.defeq ⟨_, hw.defeq⟩

/-- **`ConvPiInv` from `ConvStep2` and plain Π-injectivity.**

`BaseUniqChain.convPiInv_of_sortUniq_piInv` needs `SortUniq` for the same collapse; here the
collapse is `ConvStep2`'s job and `PiInv` is applied to the single conversion that comes out. -/
theorem convPiInv_of_convStep2 (henv : Ordered env) (hcs : ConvStep2 env U)
    (hpi : PiInv env U) : ConvPiInv env U := by
  intro Γ A B A' B' hΓ h
  match h.collapseE hcs hΓ with
  | .inl eq => cases eq; exact ⟨.refl, .refl⟩
  | .inr ⟨_, hw⟩ =>
    obtain ⟨⟨_, ha⟩, _, hb⟩ := hpi hΓ.defeq ⟨_, hw.defeq⟩
    have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ.defeq, _, ha.hasType.1⟩
    exact ⟨.one (ha.strong henv hΓ.defeq), .one (hb.strong henv hΓA)⟩

/-! ## §5 The bracket -/

/-- **`SortUniq` from `ConvStep2`, `SortInv` and `PiInv`.**

Composes §4 with `BaseUniqChain.sortUniq_of_convInv`, whose own hypotheses are exactly the two
chain-inversion facts and `Ordered env`.  `sorryAx`-free. -/
theorem sortUniq_of_convStep2 (henv : Ordered env) (hcs : ConvStep2 env U)
    (hsi : env.SortInv U) (hpi : PiInv env U) : env.SortUniq U :=
  sortUniq_of_convInv henv (convSortInv_of_convStep2 hcs hsi)
    (convPiInv_of_convStep2 henv hcs hpi)

/-- **The split, both directions.**  Over `PiInv`, universe uniqueness is exactly the
conjunction of the chain-composition step and plain sort injectivity.

`←` is §5; `→` is `convStep2_of_sortUniq` together with `SortInv.of_sortUniq`
(`SortUniqDown.lean`).  `sorryAx`-free in both directions.

`SortInv` is the `sort`/`sort` entry of `Injectivity.RigidShapeUniq`, which
`rigidShapeUniq_of_sortUniq` removes from the second hole; so this says the second hole's
*discarded* entry is one of the two halves of the first hole. -/
theorem sortUniq_iff_convStep2_sortInv (henv : Ordered env) (hpi : PiInv env U) :
    env.SortUniq U ↔ (ConvStep2 env U ∧ env.SortInv U) :=
  ⟨fun hsu => ⟨convStep2_of_sortUniq henv hsu, SortInv.of_sortUniq hsu henv⟩,
   fun ⟨hcs, hsi⟩ => sortUniq_of_convStep2 henv hcs hsi hpi⟩

/-- **…and therefore the 534-user hole itself.**  `PiInvStratApp` is the single instance of
`IsDefEqU.forallE_inv_stratified` that `uniqQ` consumes (`Injectivity.lean`), and
`sortUniq_iff_piInvStratApp` identifies it with `SortUniq` over `PiInv`.  Chaining:

    ConvStep2 ∧ SortInv ∧ PiInv  →  PiInvStratApp

`sorryAx`-free; the `sorry` stays in the *inhabitant* `piInvStratApp_axiom`. -/
theorem piInvStratApp_of_convStep2 (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (hsi : env.SortInv U) (hpi : PiInv env U) : PiInvStratApp env U :=
  piInvStratApp_of henv (sortUniq_of_convStep2 henv.ordered hcs hsi hpi) hpi

/-- The four-way bracket, packaged.  `sorryAx`-free. -/
theorem piInvStratApp_iff_convStep2_sortInv (henv : VEnv.WF env) (hpi : PiInv env U) :
    PiInvStratApp env U ↔ (ConvStep2 env U ∧ env.SortInv U) :=
  (sortUniq_iff_piInvStratApp henv hpi).symm.trans (sortUniq_iff_convStep2_sortInv henv.ordered hpi)

/-! ## §6 Non-vacuity, and the two bounds on the residual

The ledger's discipline (`docs/vacuity-ledger.md` §5): a reduction to an unmeasured residual is
relocation, not progress.  `ConvStep2` is bounded on both sides —

* **above** by `convStep2_of_sortUniq`: it follows from the statement it is used to prove, so it
  is not a smuggled strengthening;
* **below** by `sortUniq_of_convStep2`: together with `SortInv` and `PiInv` it gives that
  statement back, so it is not a weakening that loses the content.

What separates it from a restatement is `convStep2Level_iff_sortUniq` in the other direction:
the level form *is* `SortUniq`, and `SortUniq` is **not** reachable from `ConvStep2` by the
`X = Y = Z` instantiation that settles the level form, because the conclusion's `∃ u` discards
both input levels.  That is a statement about the routes this tree has, not an unprovability
claim.

### The limit of this result, stated plainly

**This is a narrowing of the *statement*, not yet a reduction of the *work*.**  The only route
to `ConvStep2` in this file is `convStep2_of_convStep2Level`, and `ConvStep2Level` is
`SortUniq` on the nose.  Anyone proving `ConvStep2` therefore has to find an argument that does
**not** factor through aligning the two link levels — and aligning them is universe uniqueness
at the midpoint `Y`, which is a *type* (both `.sort a` and `.sort b` are its types), i.e. it is
`SortUniq` in its full stated generality, since `SortUniq` is itself stated for types only.
Every attempt to build the composed conversion in this tree's calculus goes through
`IsDefEqStrong.defeqDF`, whose type premise at a sort is `sortDF`, whose side condition is
`a ≈ b`.

**Correction, 2026-09-01 (`Theory/Typing/InjMidpoint.lean`).**  The last sentence is false as a
claim about the tree, and only the sentence before it survives.  `BaseUniqChain.ConvC.transport`
builds one `defeqDF` per chain link at an **arbitrary** type — never at a pair of syntactic
sorts — so `convStep2At_of_baseUniqCAt` composes the two conversions with no `sortDF` and no
level comparison at all, from `BaseUniqCAt` at the single midpoint `Y`.  Consequences: three of
`VExpr`'s six midpoint heads (`.bvar`, `.sort`, `.const`) discharge `ConvStep2` outright from
`Ordered env` alone, and the instance `convStep2_fires` below advertises as a *firing test* is a
*theorem* (`convStep2At_sort_discharges`).  The circle is not cut — `baseUniqC_iff_convStep2`
shows `BaseUniqC` is `ConvStep2` over `SortInv ∧ PiInv` — but the residual is not a level
alignment.  So the honest reading is:

* **gained** — `SortInv` is now a *separable half* of the first hole.  Over `PiInv` the
  534-user hole is `ConvStep2 ∧ SortInv`, and `SortInv` is the `sort`/`sort` entry of the
  second hole's bridge, so whatever closes the nine-entry bridge closes half of the first hole
  as well.  Before this file the accounting ran only the other way (`SortUniq` buys one of the
  bridge's nine entries, `rigidShapeUniq_of_sortUniq`); nothing said the bridge buys any part
  of `SortUniq`.
* **gained** — `ConvC.collapseE` is a strictly cheaper collapse than
  `BaseUniqChain.ConvC.collapse`: `[propext]` alone, no `SortUniq`, and no reflexivity witness
  for the left endpoint.
* **gained** — a sharp negative: the *obvious* formulation of the composition step, the one
  with the levels identified, is provably `SortUniq` (`convStep2Level_iff_sortUniq`), so the
  `∃` is the only place slack exists and any attack has to live there.
* **not gained** — no census movement, no cone movement, and no evidence that `ConvStep2` is
  easier to prove than `SortUniq`.  It is only formally weaker.
-/

/-- **The hypothesis fires, non-degenerately.**  Over *every* environment, at `Γ = []`, with
`X`, `Y`, `Z` pairwise distinct as expressions and the two link levels **syntactically
different** (`.succ (.imax .zero .zero)` versus `.succ .zero`, equivalent but not equal).  So
neither the premise nor the level pair is degenerate; no constant, no rule, no `VEnv.WF`. -/
theorem convStep2_fires :
    (VLevel.succ (.imax .zero .zero) : VLevel) ≠ .succ .zero ∧
    CtxStrong env 0 [] ∧
    env.IsDefEqStrong 0 [] (.sort (.imax .zero .zero)) (.sort .zero)
      (.sort (.succ (.imax .zero .zero))) ∧
    env.IsDefEqStrong 0 [] (.sort .zero) (.sort (.max .zero .zero))
      (.sort (.succ .zero)) := by
  refine ⟨by intro h; exact absurd h (by simp), trivial, ?_, ?_⟩
  · exact .sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero
  · exact .sortDF trivial ⟨trivial, trivial⟩ (by rfl)

/-! ## §7 Axiom check

    #print axioms Lean4Lean.VEnv.convStep2Level_iff_sortUniq
    #print axioms Lean4Lean.VEnv.ConvC.collapseE
    #print axioms Lean4Lean.VEnv.convSortInv_of_convStep2
    #print axioms Lean4Lean.VEnv.convPiInv_of_convStep2
    #print axioms Lean4Lean.VEnv.sortUniq_of_convStep2
    #print axioms Lean4Lean.VEnv.sortUniq_iff_convStep2_sortInv
    #print axioms Lean4Lean.VEnv.piInvStratApp_of_convStep2
    #print axioms Lean4Lean.VEnv.convStep2_fires

None mentions `sorryAx`, despite the import of `Injectivity.lean` through both parents:
nothing here consumes `piInvStratApp_axiom`, `WF.sortUniq'`, `WF.rigidShapeUniqNS`,
`IsProof.defeqU` or `WF.uniq'`.  Every `SortUniq`, `SortInv`, `PiInv` and `ConvStep2` is a
hypothesis. -/

end VEnv
end Lean4Lean
