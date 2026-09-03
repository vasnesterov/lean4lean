# Handoff: `IsDefEqU.forallE_inv_stratified` (hole A) — the price is now exact

*Written 2026-09-03. Every claim below is machine-checked in
`Lean4Lean/Theory/Typing/ForallInvPrice.lean` (14 declarations, builds green, **every headline
`sorryAx`-free**) unless it is marked `[analysis]` or `[read off]`.*

## 0. Corrections to the brief I was given

* **The `sorry` is not in `UniqueTyping.lean`.** It is `Lean4Lean/Theory/Typing/Injectivity.lean:261`.
  `UniqueTyping.lean:43` is one of its two *consumers*. (The brief flagged this as a guess; the
  guess was wrong.)
* **"~736 reverse-dependents, largest of the 13 standing holes" is exact, and I measured it**
  rather than reading it off: `lake env lean scripts/sorry-census.lean` at `cc6ba3b` gives
  `IsDefEqU.forallE_inv_stratified [736 transitive users]`, `WF.rigidShapeUniqNS [460]`,
  `IsDefEqU.weakN_iff [312]`, `NormalEq.descend [200]`, TOTAL 13. Ledger row 69c's 650 is stale.
* **"one of exactly two holes in the cone of ... `TrProj.wf`"** — consistent with
  `Verify/Typing/ProjWeakInv.lean:53`. `[read off]`, not re-measured.
* **`docs/vacuity-ledger.md`'s corner table is stale in its hole-A row.** It reads
  "hole A, over `PiInv` | `ConvStep2 ∧ SortInv`". After `PiInvResidual.lean` (2026-09-02) `PiInv`
  is no longer an assumption for hole A — it is free from the same hypothesis. The row should read
  **"hole A | `ConvStep2 ∧ ShapeLinkAgree`"**, which is also exactly hole B's row minus the three
  constant-spine conjuncts.

## 1. The result

`VEnv.piInvStrat_of_shapeLinkAgree` (§1 of the file):

    VEnv.WF env  →  ConvStep2 env U  →  ShapeLinkAgree env U  →  PiInvStrat env U

`PiInvStrat` is `Injectivity.lean`'s packaging of the `sorry`'s exact statement;
`IsDefEqU.forallE_inv_stratified_of_shapeLinkAgree` (§6) restates it verbatim in the `sorry`'s own
binder shape, so no reading is required to check that it is the same proposition.

It is a **composition of three existing theorems** — `Injectivity.piInvStrat_of`
(`SortUniq ∧ PiInv → PiInvStrat`, line 580) and `PiInvResidual.{sortUniq,piInv}_of_shapeLinkAgree`
(landed 2026-09-02) — that had not been composed: `PiInvResidual.lean` never mentions `PiInvStrat`.
There is no new mathematics in §1.

## 2. The price is exact (this is the part that changes planning)

`VEnv.convStep2_shapeLinkAgree_iff`, over `VEnv.WF env`:

    ConvStep2 ∧ ShapeLinkAgree   ↔   PiInvStrat ∧ SortPiDisjUC

The `←` direction is new content, §2 of the file:

| coordinate of the price | comes back from hole A? | how |
| --- | --- | --- |
| `ConvStep2` | yes | `SortUniq` then `convStep2_of_sortUniq` |
| `SortLinkInvUC` | yes | `SortUniq` then `sortLinkInvUC_of_sortUniq` |
| `PiLinkInvUC` | **yes** | `piLinkInvUC_of_piInvStrat` — new |
| `SortPiDisjUC` | **not proved either way** | see §4 below |

`piLinkInvUC_of_piInvStrat` **corrects a note written the day before**. `PiInvResidual.lean` §5
records that `PiLinkInvUC` "is not recovered from `PiInv`… because moving an arbitrary index `T` to
a syntactic sort is uniqueness of typing", and concludes that §3's reduction is "into something
*possibly strictly stronger*". That is right about `PiInv` and wrong about the *target*: hole A's own
hypothesis is an `IsDefEqU` at an **arbitrary** index, and `HasTypeStrong.stratify` (`Strong.lean:1005`)
manufactures the two stratified premises from `IsDefEqStrong.hasType'`. So hole A supplies exactly the
uniqueness-of-typing that §5 named as missing, and the corner's normal form is *not* strictly stronger
than hole A in that coordinate.

**Consequence for anti-vacuity** (`hyp_inhabited_iff`, §7, stated in the `∃` form the ledger asks
for):

    (∃ env U, WF env ∧ ConvStep2 ∧ ShapeLinkAgree)  ↔  (∃ env U, WF env ∧ PiInvStrat ∧ SortPiDisjUC)

This is the strongest inhabitation statement obtainable for a hypothesis that is an *equivalent* of
an open target: the hypothesis of §1 cannot be vacuous unless hole A itself is unsatisfiable over
well-formed environments. **An absolute witness is not offered, and by the `iff` it cannot be
offered without closing the corner** — that is a theorem here, not an excuse. Anyone who asks a
future stream for "a concrete `env` satisfying `ConvStep2 ∧ ShapeLinkAgree`" is asking it to close
hole A.

## 3. Negative control (§4–§5)

`sortPiEnv` := `InjPiRogue.rogueEnv1` with **two** δ-rules for its single constant
`rogueC : Sort 1` — `rogueC ≡ ∀ (_ : Prop), Prop` and `rogueC ≡ Prop`.

* `ordered_sortPiEnv : Ordered sortPiEnv`
* `sortPi_link : sortPiEnv.IsDefEqStrong 0 [] (.sort .zero) roguePi1 (.sort (.succ .zero))`
* `not_shapeLinkAgree_sortPiEnv : ¬ ShapeLinkAgree sortPiEnv 0` — via `SPShape.Agree (.sort _) (.pi _ _) = False`
* `not_sortPiDisjUC_sortPiEnv : ¬ SortPiDisjUC sortPiEnv 0`

So §1 is not a tautology of the definitions and `VEnv.WF` is load-bearing in it. **And the control
is a control, not a refutation:** `not_wf_sortPiEnv : ¬ VEnv.WF sortPiEnv`, because the two rules
share an lhs and `DeltaUnique.WF.defEqHeadsUnique` forbids that — the same discipline
`InjPiRogue.not_wf_roguePiEnv` observes for its own witness, and the same clause row 69 identifies
as what saves the corner from `roguePiEnv`.

The control for the *conclusion* already existed and I did not duplicate it:
`Injectivity.piInvStratApp_fires` instantiates hole A's premises non-degenerately (two
syntactically distinct domains, hence two distinct codomain contexts) over every environment. So
neither side of §1 is degenerate.

## 4. What I did NOT establish, as negatives

* **`PiInvStrat → SortPiDisjUC`: not proved, and not refuted.** The natural route,
  `Injectivity.IsDefEqU.sort_forallE_inv`, is unavailable: its `trans` case consumes hole B
  (ledger row 41). Nor did I exhibit a `VEnv.WF` environment satisfying hole A and refuting
  `SortPiDisjUC`, which is what a separation needs. **This is the one open coordinate of the price**
  and it is a good target: it is the corner's *only* semantically-settled conjunct
  (`interp_sort_ne_interp_forallE`, per the ledger's corner table).
* **`ConvStep2` from `ShapeLinkAgree` alone: not attempted beyond analysis.** `ConvStep2` composes
  two sort-*indexed* links and needs the two index levels reconciled at an arbitrary midpoint;
  `ShapeLinkAgree` constrains only terms that *are* shapes. I see no route and did not look for a
  refutation. `[analysis]`
* **No claim that any of this reduces the work.** Per `InjOneFact.shapeMidShapeless_iff` and
  `shapeLinkAgree_iff`, everything here lands in a normal form known to be at least as strong as
  its own target. What is new is that the normal form is now known to be *exactly* as strong,
  modulo one named coordinate.

## 5. The blocker for actually cashing §1 — read this before planning a substitution

**The substitution at the `sorry` site is not available, and no amount of proof will make it so
without a refactor.** Measured (BFS over `^import` in `Lean4Lean/`):

    Injectivity ← PiLevelPin ← RigidNodeCircle ← InjSpineTransport ← InjPiInhab
                ← InjPiRogue ← InjOneFact ← SortInvIndep ← PiInvResidual

`Injectivity.lean` is **eight imports upstream** of `PiInvResidual.lean`, and even inside
`Injectivity.lean` the ingredient `piInvStrat_of` is at line 580, *after* the `sorry` at 261. So
§1 is a strictly *downstream* discharge.

Two ways to cash it, and I recommend neither without a human call:

* **(a) Thread the hypothesis.** `Injectivity.uniqQ`/`uniqAux` already take `PiInvStratApp`, and the
  `sorry` has **exactly two application sites** in the whole tree — `UniqueTyping.lean:43` (inside
  `IsDefEq.uniq`) and `Injectivity.lean:546` (`piInvStrat_axiom`); everything else that names it is
  prose (checked by grep over `Lean4Lean/`, excluding backticked and `--` lines). So the tree is
  90% set up for it. **But this trade is bad on its own terms:** it converts a `sorry` that
  `scripts/sorry-census.lean` counts into a *hypothesis*, which the census and `hole-cone` are
  blind to by construction (ledger §0). Census 13 → 12 with nothing discharged is the exact
  overstatement the ledger exists to prevent.
* **(b) Hoist.** `ConvC`, `SPShape`, `ConvStep2` and `ShapeLinkAgree` mention only `Strong.lean`
  material and could be *defined* upstream of `Injectivity.lean`; their *proofs* could not be, since
  `BaseUniqChain`'s development is what supplies `sortUniq_of_convInv`. A real refactor, not a
  file move. `[analysis]`

**So the value of this round is the price, not a discharge.** Leave the `sorry` where it is.

## 6. What to pick up first

1. **`SortPiDisjUC`** — the one coordinate of the price that hole A does not give back. Either
   derive it from hole A (making `convStep2_shapeLinkAgree_iff` an unconditional identification of
   hole A with the corner's normal form), or separate it. Both outcomes are publishable rows.
2. **`ConvStep2`** — unchanged as the shared node, and now provably shared: it is a coordinate of
   hole A's price *and* of hole B's. Ledger §0's "effort on it pays twice" is now a theorem
   (`piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree`), not an observation.
3. **Do not** commission a hypothesis-threading refactor to make the census read 12.
4. Update the ledger's corner table row for hole A (see §0).

## 7. Inventory of `Lean4Lean/Theory/Typing/ForallInvPrice.lean`

All in namespace `Lean4Lean.VEnv` (read off the file's own `namespace` lines; names confirmed by
the build's own `#print axioms` output, not composed from the path).

| § | declaration | axioms |
| --- | --- | --- |
| 1 | `piInvStrat_of_shapeLinkAgree` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `piInvStrat_of_propAgreeOn` | same |
| 2 | `convStep2_of_piInvStrat` | same |
| 2 | `sortLinkInvUC_of_piInvStrat` | same |
| 2 | `piLinkInvUC_of_piInvStrat` | same |
| 3 | `sortPiDisjUC_of_shapeLinkAgree`, `shapeLinkAgree_of_piInvStrat` | same |
| 3 | `convStep2_shapeLinkAgree_iff` | same |
| 4 | `ordered_sortPiEnv`, `sortPi_link`, `not_shapeLinkAgree_sortPiEnv`, `not_sortPiDisjUC_sortPiEnv` | `[propext, Quot.sound]` |
| 5 | `not_defEqHeadsUnique_sortPiEnv`, `not_wf_sortPiEnv` | `[propext, (Classical.choice,) Quot.sound]` |
| 6 | `IsDefEqU.forallE_inv_stratified_of_shapeLinkAgree` | `[propext, Classical.choice, Quot.sound]` |
| 7 | `hyp_inhabited_iff` | same |
| 8 | `convStep2_shapeMidShapeless_iff` | same |
| 8 | `piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` | same |

**No `sorryAx` anywhere in the file.** Nothing in the tree imports it, by design: it is a
measurement, and importing it would put `sortPiEnv` in other cones for no benefit.
