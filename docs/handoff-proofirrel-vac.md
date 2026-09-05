# handoff-proofirrel-vac — `PiInv ∅ U`, and is `ForallEProofPair` vacuous?

Stream: ProofIrrelVac. Opened 2026-09-05, HEAD `8826327` (bare build green 1673 jobs, guards
1/2/3 ✓, census 13).

Owned: `Lean4Lean/Theory/Typing/PiInvVac.lean` (new), `docs/handoff-proofirrel-vac.md` (this file).
Read-only, explicitly: `Lean4Lean/Theory/Typing/Injectivity.lean` and
`Lean4Lean/Theory/Typing/PiInvWF.lean` (may **not** be edited).
Frozen: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

Two probes handed over by the PiInvWF round:

* **Probe 1** — its own flagged omission: `VEnv.PiInv ∅ U`. `∅` is `VEnv.WF`, so a *refutation*
  there collapses the whole corner; a *proof* there generalises nothing (no `defeqs`, so no
  `extra`). Asymmetric, and unrun.
* **Probe 2** — an orchestrator *claim to test, not a fact*: `ForallEProofPair` is **vacuous**
  because `proofIrrel` needs two Π's inhabiting a common `T : Prop`, a Π's type is a sort, and
  `Sort u : Sort (u+1)` would need `succ u ≈ zero`. The orchestrator's own flagged hole: deducing
  "`T` is a sort" from `⊢ ∀A.B : T` may itself route through the inversion machinery under
  investigation, i.e. be **circular**.

---

## §1 — Questions asked cold

**The four shape questions below were written and committed to this file before running any
tool against `PiInvVac.lean`, before instantiating `PiInv` at `∅`, and before reading
`UniqSort.lean`, `SortUniq.lean`'s corrections, `InjCensus.lean`, `InjMethod.lean`,
`InjPiRogue.lean`, or `docs/handoff-injcensus.md`.** (Read before writing: `CLAUDE.md`,
`PiInvWF.lean` in full, `NotProof.lean` in full, `Injectivity.lean` §§`PiInv`/`IsProof`,
`docs/handoff-piinv.md` §1, `docs/vacuity-ledger.md` head.) Predictions are filled in
immediately below each question, before the corresponding measurement. **A filled answer is
never edited**; corrections go in §2 with a date.

### Q1. Does the target exist — judged on the *conclusion head*, not the name?

(a) `VEnv.PiInv` — a `def … : Prop` I can instantiate at `env := ∅`, and its **full arity
including invisible section binders** (`variable {env : VEnv} {U : Nat}` is in scope at
`Injectivity.lean:327`, so the printed arity may be 2, not 0). (b) `VEnv.ForallEProofPair` and
`VEnv.SortZeroConvProp` — same test: `def`s, arity, and are they in namespace `Lean4Lean.VEnv`
as `PiInvWF.lean`'s `namespace` lines imply? (c) Is `∅ : VEnv` a real `EmptyCollection`
instance with `constants := fun _ => none` and `defeqs := fun _ => False`, or is `∅`
notation for something else — and is `(∅ : VEnv).WF` actually derivable (`VEnv.WF'.empty`
exists? `⟨_, .empty⟩`?) rather than merely assumed by the brief? (d) `VEnv.imax_dom_not_pinned`
(`RigidNodeCircle.lean`) — brief says arity 0, cone 591, hole-free; measure all three before
citing, and decide whether it is relevant *at all* to either probe.

**Prediction (recorded before measurement):** (a) `VEnv.PiInv` exists as `def PiInv (env : VEnv)
(U : Nat) : Prop` — the two section variables are *re-bound explicitly* in the `def`, so I predict
`scripts/exists.lean` prints **arity 2**, not 0, and I predict no invisible extra binder beyond
those two. (b) `ForallEProofPair`, `SortZeroConvProp`, `SortZeroOneConv` likewise arity 2, all in
`Lean4Lean.VEnv`. (c) `∅ : VEnv` is a real instance with `defeqs := fun _ => False`; `(∅ : VEnv).WF`
is derivable in one line as `⟨[], .empty⟩` or `⟨_, .empty⟩` — I have already seen `.empty` used as
the tail of `PiInvWF.wf_permits_inconsistent`'s chain, so this is near-certain. (d) I predict
`imax_dom_not_pinned` is **irrelevant to both probes**: it is about no *level* conjunct being
smuggled into the Π-inversion conclusion, whereas both probes are about the *type* of a Π-headed
term. Confidence 0.8 irrelevant.

### Q2. Is the work in the direction I think?

(i) `PiInv ∅ U`'s *hard* direction: its premise is `IsDefEqU ∅ U Γ (∀A.B) (∀A'.B')` and its
conclusion is a positive conversion. At `∅` the premise is the whole content: **which
`IsDefEq` rules can relate two Π's over an environment with no constants and no rules?**
Prediction to record: `extra` is dead (`defeqs = fun _ => False`), `proofIrrel` is the one
non-structural survivor, `beta`/`eta`/`appDF` need a redex, `trans`/`symm` need a middle term.
So Probe 1 reduces to: *does `proofIrrel` fire at `∅`?* — i.e. **Probe 1 and Probe 2 are the
same question at `∅`**, and Probe 2 answered negatively proves Probe 1 positively. Check that
identification rather than assume it.
(ii) Is a **proof** of `PiInv ∅ U` worth anything? Brief says no. State the limit as a
theorem if possible (e.g. `∅` has no `extra` step at all), not as a confession.
(iii) Vacuity risk on the *premise* side: if `IsDefEqU ∅ U Γ (∀A.B) (∀A'.B')` is only ever
derivable with `A ≡ A'` structurally, `PiInv ∅ U` is true and hollow — and that must be
reported as hollow, per `docs/vacuity-ledger.md`'s kind-4 guard.

**Prediction (recorded before measurement):** (i) `extra` is dead at `∅` — near-certain. But I
predict the reduction "Probe 1 = Probe 2 at `∅`" is **wrong**, and this is the prediction I most
expect to be graded on: `beta`, `eta`, `appDF` and above all `trans` survive at `∅` with no
constants at all (`(fun x => ∀A.B) c ≡ ∀A.B` needs no environment), so a Π at `∅` can be related to
a non-Π-headed term and `trans` can route through it. That is the *whole* `RigidShapeUniq`
difficulty, and it is δ-free. So I predict `PiInv ∅ U` is **true but not cheaply provable** — the
pure-fragment Church–Rosser problem — and I put ≤0.25 on a cheap decision existing, ~0.05 on
refutable. (ii) Yes: I predict I can prove the limit rather than confess it — `∅` admits no `extra`
step, so a proof at `∅` transfers to no environment with a δ-rule. (iii) The premise is *not*
vacuous at `∅` (`refl`/`forallEDF` supply premises with `A ≡ A'` already), but every *easy* premise
has a convertible domain, so the honest risk is that a proof of `PiInv ∅ U` is hollow in the second
sense: true for the same reason `refl` is.

### Q3. Measurement or docstring?

Each of these is *prose in my brief* until measured here, with `#print axioms` and
`scripts/exists.lean`: (i) "`ForallEProofPair` has no non-vacuity witness at any environment" —
a **negative**, therefore per the ledger's kind-4 guard the *most* suspect claim in the brief;
(ii) "`IsProof.forallE_fires` shows a Π-*typed* term can be a proof" — read its statement, not
its docstring, and check whether the term is Π-*typed* or Π-*headed* (the brief distinguishes
them and the distinction is the whole probe); (iii) `PiInvWF.hasType_falseProp` /
`hasType_piOne` — these type a **Π-headed term at `.sort .zero`**, which is *superficially* the
thing Probe 2 says is impossible; classify the difference (type-is-`Prop` vs
inhabits-a-`Prop`) before believing either side; (iv) `forallE_not_proof`'s hypothesis list —
does it take `SortUniq`, and does `HasTypeStrong.forallE_type` take it too, and *where*;
(v) `WF.sortUniq'`'s cone — if it is `PiInvStratApp`-conditional or `sorryAx`-tainted then
"`ForallEProofPair` is refuted at `VEnv.WF`" is already known-modulo-the-hole and Probe 2's
only value is a **hole-free** version.

**Prediction (recorded before measurement):** (i) I predict "no non-vacuity witness at any
environment" is **not a measured fact anywhere in the tree** and is unproved even at `Ordered`;
predicted status: plausible, unproved, and *unprovable hole-free by the argument as given*.
(ii) I predict `IsProof.forallE_fires` exhibits a term whose **type is Π-headed** (`.bvar 0` at
`.forallE (.sort .zero) (.bvar 2)`) with `p` a **context variable** — so it is Π-*typed*, not
Π-*headed*, and it therefore says nothing about Probe 2. The brief's distinction survives.
(iii) I predict the difference is exactly *being a proposition* vs *inhabiting one*:
`hasType_falseProp` gives `∀p:Prop,p : Sort 0` (its **type is** `Prop`); `ForallEProofPair` needs
`∀A.B : p` with `p : Sort 0` (it **inhabits** a `Prop`). `VLevel.imax_zero` supplies the first for
free and is *irrelevant* to the second — and I predict the orchestrator's argument silently trades
on the first. (iv) `forallE_not_proof` takes `SortUniq` (`huniq`), and so does
`HasTypeStrong.forallE_type`, at its **`defeq` case** — I have read both, so this is near-certain;
the prediction is that this is the *only* route in the tree to "the type of a Π is a sort".
(v) I predict `WF.sortUniq'` is `PiInvStratApp`-conditional / `sorryAx`-tainted, hence **the
orchestrator's sort-hood step is circular**: it is `forallE_type`'s `huniq`, and at `VEnv.WF` that
`huniq` comes from the very hole under investigation. Confidence 0.85 circular.

### Q4. What does the structure branch on, and where are its extremes — i.e. what do
`ForallEProofPair`'s **side conditions** permit that I am assuming they forbid?

Method rule 2, current form: *for a structure with a side condition the extremes are what the
condition permits and you assumed it forbade.* `ForallEProofPair`'s conditions are
`OnCtx Γ (IsType U)`, `⊢ p : Sort 0`, `⊢ ∀A.B : p`, `⊢ ∀A'.B' : p`, `¬∃u, A ≡ A' : Sort u`.
Extremes to instantiate:
- `p` at its extremes: `p` a **sort** (`.sort .zero` — forbidden? that needs `Sort 0 : Sort 0`),
  `p` a **bvar** from `Γ` (the `IsProof_fires` trick — `Γ = [.bvar 0, .sort .zero]` puts an
  arbitrary `p : Prop` in scope with an *inhabitant*, and **that is the extreme I expect the
  vacuity argument to have assumed away**), `p` a Π, `p` a constant.
- `Γ` at its extremes: `[]` (nothing to hypothesise) vs a context that *assumes* `p`'s
  inhabitedness. `OnCtx` only demands each entry be a **type**, so a context entry may be an
  arbitrary `.bvar`-typed hypothesis — including one whose type is a Π that is a `Prop`.
- `A`, `A'` at their extremes: equal (then the last conjunct fails), one closed one open, and
  the pair `(.sort .zero, .sort (.succ .zero))` that `PiInvWF` already builds.
- `env` at its extremes: `∅` (Probe 1) and the `Ordered`-only rogue envs.
- `U` at its extremes: `U = 0` and `U` large.
The deliverable per probe: which side-condition-legal state makes `ForallEProofPair` fire, and
**is the orchestrator's sort-hood step available from anything weaker than `SortUniq`** — where
"weaker" is measured as: not routing through `forallE_inv_stratified` or `rigidShapeUniqNS`.
`VLevel` sub-questions to measure, not assume: is `succ u ≈ zero` refutable outright (all
valuations), and can `imax`/`max` produce `zero` from a `succ` argument (`VLevel.imax_zero`
says `imax _ zero ≈ zero` — so the **codomain** is the zero-maker, and the *domain* is free;
that is the asymmetry Probe 2 must not confuse with "the Π's type is a `Prop`").

**Prediction (recorded before measurement):** I predict the side condition that decides Probe 2
is `⊢ ∀A.B : p` together with `⊢ p : Sort 0`, and that the extreme I would have assumed away is
`p` a **context variable or constant** rather than a sort. My predicted obstruction, and it is the
*same* self-defeat `PiInvWF` found one level up: to get a Π-headed term to inhabit `p` you must
retype `.sort (imax u v)` at `p` via `defeqDF`, i.e. you need `.sort _ ≡ p` at a common sort, and
then `p : Sort 0` plus `.sort _ : .sort (succ _)` demands `succ _ ≈ 0` **at that common type** —
which is exactly the step that needs `SortUniq` to compare the two types. So I predict: not
witnessable by any construction I can build, and not refutable hole-free; the deliverable is a
*conditional* vacuity plus a proof that the condition is the same `SortUniq` node, i.e. **the probe
fails honestly and the circularity is the finding**. Secondary prediction: what I *can* get
hole-free is that `ForallEProofPair` forces a conversion between a **sort and a non-sort** (a
`SortForallConv`-shaped residual), which is strictly weaker than `¬SortUniq` and may already be
named in the tree. `VLevel`: `succ u ≈ zero` refutable outright at every valuation (near-certain,
`VLevel.eval` sends `succ` to `+1`); `imax`/`max` produce `zero` only from `zero` arguments
(`VLevel.imax_eq_zero` exists and I predict a `max_eq_zero` analogue does too), so no `succ` can be
laundered to `zero` — meaning the level side of the vacuity argument is **sound**, and only its
sort-hood side is circular.

---

## §2 — Verdicts, as measured

_(appended per verdict, before the next tool call)_

### V1 (2026-09-05) — Q1: everything exists, arities as predicted, and `imax_dom_not_pinned` is irrelevant

`scripts/exists.lean` (population 487 built modules):

| name | module | arity | hole in own value | cone reaches `sorryAx` |
| --- | --- | --- | --- | --- |
| `Lean4Lean.VEnv.PiInv` | `Theory.Typing.Injectivity` | 2 | no | no (cone 31) |
| `Lean4Lean.VEnv.ForallEProofPair` | `Theory.Typing.PiInvWF` | 2 | no | no (cone 33) |
| `Lean4Lean.VEnv.SortZeroConvProp` | `Theory.Typing.PiInvWF` | 2 | no | no (cone 30) |
| `Lean4Lean.VEnv.SortZeroOneConv` | `Theory.Typing.PiInvWF` | 2 | no | no (cone 31) |
| `Lean4Lean.VEnv.imax_dom_not_pinned` | `Theory.Typing.RigidNodeCircle` | 0 | no | no (cone 591) |
| `Lean4Lean.VEnv.forallE_not_proof` | `Theory.Typing.NotProof` | **11** | no | no (cone 2378) |
| `Lean4Lean.VEnv.HasTypeStrong.forallE_type` | `Theory.Typing.NotProof` | **10** | no | no (cone 742) |
| `Lean4Lean.VEnv.IsProof.forallE_fires` | `Theory.Typing.Injectivity` | 2 | no | no (cone 619) |
| `Lean4Lean.VEnv.hasType_falseProp` | `Theory.Typing.PiInvWF` | 3 | no | no (cone 617) |
| `Lean4Lean.VEnv.not_forallEProofPair_of_sortUniq` | `Theory.Typing.PiInvWF` | 4 | no | no (cone 2380) |

Q1 prediction **correct** on all four parts, including that `imax_dom_not_pinned` (arity 0, cone
591, hole-free — the brief's three numbers all confirmed) is irrelevant here: it is a level-conjunct
statement and both probes are about the *type* of a Π-headed term. It is cited nowhere below.

### V2 (2026-09-05) — Q3(v): the circularity the brief feared is REAL at `WF.sortUniq'`, and measured

`VEnv.WF.sortUniq` (`Theory.Typing.SortUniqFacts`, arity 3, cone 3475): **cone reaches `sorryAx`:
true**, holes in cone `[Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified]`, and it is additionally
flagged `*** WATCHED IN CONE: [IsDefEq.uniq, IsDefEq.uniqU] ***`. Same for
`VEnv.propLoop_sortUniq` (cone 3458, same single hole). So at `VEnv.WF` the tree's only supplier of
`SortUniq` runs through the hole `PiInv` is part of — *if* the vacuity argument needs `SortUniq`,
it is circular. Q3(v) prediction **correct**.

Census confirmed 13 (`scripts/sorry-census.lean`), `forallE_inv_stratified` 742 users,
`rigidShapeUniqNS` 461, `NormalEq.descend` 200.

### V3 (2026-09-05) — Q3(i)/Q4: the brief's negative is FALSE as stated, and the sort-hood step is NOT circular

**This is the round's finding, and it overturns the premise of Probe 2 rather than answering it as
posed.** `Theory/Typing/SortInvIndep.lean` (which `PiInvWF.lean` does not import) already contains

* `VEnv.PropAgreeOn` (`SortInvIndep.lean:80`) — *the types of a term agree on being propositions*;
* `VEnv.forallENotProof_of_propAgreeOn` — **a Π is not a proof, from `Ordered` + `PropAgreeOn`,
  with no `SortUniq`**, `sorryAx`-free;
* and its own docstring records why: `HasType.forallE_inv` recovers the domain/codomain typings
  **from the Π's own typing**, from `Ordered` alone.

So the sort-hood step the brief feared was circular is *not* circular and does not need the
inversion machinery: one does not need "`T` is a sort", only the Π's **second** typing
`.sort (.imax u v)`, which `HasType.forallE_inv` + `forallEDF` deliver hole-free at `Ordered`.
What the argument needs beyond that is a **level-comparison** step, and the weakest node in the
tree that performs it is `PropAgreeOn`, not `SortUniq`. Q4's predicted obstruction ("the same
self-defeat one level up") was therefore **wrong**, and Q3(i)'s prediction that the brief's
negative is unproved is **right but for the wrong reason**: it is not merely unproved, its
strongest available form is *already false as a universal claim about hypotheses* — `Ordered` +
`PropAgreeOn` suffices.

### V4 (2026-09-05) — Probe 2, the measured result: `ForallEProofPair` is vacuous at `Ordered ∧ PropAgreeOn`, and that is weaker than `SortUniq`

All in `Lean4Lean/Theory/Typing/PiInvVac.lean`, all `sorryAx`-free (`scripts/exists.lean`,
population 488):

| declaration | arity | cone | hole-free |
| --- | --- | --- | --- |
| `Lean4Lean.VEnv.forallE_second_type` | 8 | 2082 | ✓ |
| `Lean4Lean.VEnv.not_forallEProofPair_of_propAgreeOn` | 4 | 2117 | ✓ |
| `Lean4Lean.VEnv.not_propConv_of_propAgreeOn` | 4 | 2120 | ✓ |
| `Lean4Lean.VEnv.not_forallEProofPair_empty_of_any_propAgreeOn` | 4 | 2123 | ✓ |
| `Lean4Lean.VEnv.piInv_empty_of_propAgreeOn` | 3 | 3455 | ✓ |
| `Lean4Lean.VEnv.not_piInv_empty_collapses` | 2 | 51 | ✓ |

Inputs, measured the same way: `Lean4Lean.VEnv.forallENotProof_of_propAgreeOn`
(`SortInvIndep`, arity 11, cone 2115, hole-free), `Lean4Lean.VEnv.HasType.forallE_inv`
(`Lemmas`, arity 8, cone 2080, hole-free), `Lean4Lean.VEnv.piInv_of_propAgreeOn`
(`SortInvIndep`, arity 5, cone 3453, hole-free).

**Answer to the brief's question — is the sort-hood argument circular? NO, and the argument does
not need sort-hood.** `HasType.forallE_inv` (`Ordered`, hole-free, cone 2080) recovers the domain
and codomain typings from the Π's own typing, and `forallEDF` rebuilds the Π at
`.sort (.imax u v)`. So the Π has a *second* typing, obtained without any inversion of a
*conversion*; "`T` is a sort" is never needed. What is needed is a **level comparison** between the
two typings, and the weakest node performing it is `PropAgreeOn`, not `SortUniq`.

**And the limits, proved rather than confessed:**
* `propAgreeOn_trivial_at_sort_types` — when both types are sorts, both propositionhood bits are
  `false` and `PropAgreeOn`'s conclusion is trivially true. So `PropAgreeOn` **cannot** kill the
  route's *exit* residual `SortZeroOneConv`, which `SortUniq` does kill; and per method rule 4 this
  is all that is machine-checked about `SortInvIndep.lean`'s docstring claim that `PropAgreeOn` is
  "strictly weaker than `SortUniq`" — what is checked is that this route from it to a sort/sort
  discrimination yields nothing, **not** an incomparability theorem.
* `propBit_splits_entry` — the entry dies precisely because one of the two types is a `Prop`
  (bit `0`) and the other is a sort (bit `succ`). That asymmetry is the whole mechanism.
* `not_succ_equiv_zero`, `imax_zero_cod` — the brief's two `VLevel` questions: `succ u ≈ zero` is
  refutable at every valuation, and `imax u v ≈ zero` forces `v ≈ zero`, so no `succ` can be
  laundered into `zero`. The **level** half of the brief's argument is sound; the half that was
  wrong is "sort-hood + levels is the whole argument".
* `forallE_isType_free` — `∀ p : Prop, p` is a Π whose **type** is `.sort .zero` in every
  environment. Being a `Prop` is free; **inhabiting** one is what dies. Q3(iii) prediction correct.
* `PropAgreeOn` itself has **no hole-free unconditional supplier**: route A
  (`SetModel/PropAgreeWall.preludeEnv_propTypeAgreeOnCtx`, unconditional at `preludeEnv`) has hole
  cone exactly `IsDefEqU.forallE_inv_stratified`; route B
  (`PropAgreeGuarded.propAgreeOn_of_stratifiedN`, hole-free) takes `PropTypeAgreeN`/`PropUniqN` at
  every index (discharged only at `n = 0`) and is fixed at `nv = 0`. **So §2 is a reduction, not a
  closure, and `ForallEProofPair` is NOT proved vacuous outright.**

### V5 (2026-09-05) — Probe 1: `PiInv ∅ U` is OPEN, and the refutation route at `∅` is worse off than the brief expected

Neither proved nor refuted. What was measured:

* `∅` is `VEnv.WF` (already in the tree as `InjPiRogue.empty_wf` — the brief's assumption was
  right, and my duplicate is renamed `empty_wf'`), `Ordered`, has no constants
  (`empty_no_constants`) and **no δ-rules** (`empty_no_defeqs`), so `IsDefEq.extra` is dead at `∅`.
* The asymmetry is machine-checked in both directions: `not_piInv_empty_collapses` (a refutation
  at `∅` kills `∀ env, env.WF → PiInv env U`) and `piInv_empty_of_all` (a proof at `∅` is only a
  *necessary* condition — **it generalises nothing**, and the reason is `empty_no_defeqs`: the one
  clause of `IsDefEq` that reads the environment cannot fire there).
* `piInv_empty_of_propAgreeOn` — what *would* close it at `∅`: `PropAgreeOn ∅ U` together with
  `RigidShapeUniqNS ∅ U`. Both open at `∅`.
* **The reversal, and the round's second finding:** `∅ ≤ env` for every `env`
  (`empty_le_all`), so by `HasType.mono` a Π-in-`Prop` witness at `∅` is a witness at **every**
  environment (`isProof_forallE_empty_mono`). Hence **one** `PropAgreeOn` instance anywhere in the
  class refutes `ForallEProofPair ∅ U` (`not_forallEProofPair_empty_of_any_propAgreeOn`, and the
  citable `∃`-form `not_forallEProofPair_empty_of_exists_propAgreeOn`). `∅` is the *cheapest* place
  to look for the witness and the *hardest* place for it to survive — the opposite of the reading
  that made it "the cheapest unexplored witness left on this row".
* Conditional consequence, flagged as conditional per method rule 3: **if
  `forallE_inv_stratified` is true, `ForallEProofPair ∅ U` is false** (route A supplies
  `PropAgreeOn` at `preludeEnv` under exactly that hole). So the `proofIrrel` refutation at `∅`
  could only be walked in a world where the corner's own hole fails.
* Q2 prediction: **correct** that `extra` is dead and that the reduction "Probe 1 = Probe 2 at `∅`"
  is not available (closing the `proofIrrel` entry is not inverting a Π-conversion); correct that no
  cheap decision exists. Wrong in its emphasis: I predicted the obstruction would be β/`trans`
  regress and said nothing about the *monotonicity* argument, which is what actually prices the
  route.

### V6 (2026-09-05) — scorecard, and the two collisions found on the way

* **Q1: 4/4 correct.** Arities 2/2/2/0 as predicted; `imax_dom_not_pinned` irrelevant, as predicted.
* **Q2: partly correct** (see V5). The prediction that `PiInv ∅ U` is "true but not cheaply
  provable" is **unresolved** — this round did not prove it either way and says so.
* **Q3: 4/5 correct, one wrong in a way that mattered.** (i) right that the brief's negative was
  unmeasured, wrong that it was merely unproved — a stronger hypothesis-relative form was already
  reachable; (ii) `IsProof.forallE_fires` is Π-*typed*, not Π-*headed*, as predicted; (iii) the
  type-is-`Prop` vs inhabits-a-`Prop` distinction, as predicted, and it *is* what the brief's
  argument traded on; (iv) `forallE_not_proof`/`forallE_type` do take `SortUniq`, as predicted —
  but they are **not the only route**, which is where prediction (iv)'s framing was wrong;
  (v) `WF.sortUniq'` circular, as predicted.
* **Q4: wrong on its central prediction.** I predicted the obstruction would be "the same
  self-defeat one level up" and that no hole-free route existed; `forallENotProof_of_propAgreeOn`
  already existed one import away. The method rule that would have caught it is rule 5's spirit
  (query the compiled environment for the *conclusion shape*, not the name): I searched for
  `ForallEProofPair` consumers and for `SortUniq` refutations, and did not search for "a Π is not a
  proof" by conclusion until late.
* **Two name collisions were found by tooling, not by grep**, and both are recorded in the file:
  `VEnv.empty_wf` already exists (`InjPiRogue.lean:721`) and `VEnv.empty_le` already exists
  (`Verify/Typing/ProjInhab.lean:212`) — the second only surfaced when `scripts/exists.lean` refused
  to load a population containing both, since `Theory/` cannot import `Verify/`. Mine are
  `empty_wf'` and `empty_le_all`; `scripts/dup-names.lean` now reports no duplicates.

### V7 (2026-09-05) — build state

Bare `lake build`: **green, 1674 jobs** (1673 before this file). `scripts/sorry-census.lean`:
**13**, unchanged. `scripts/dup-names.lean`: no duplicates. LSP diagnostics on
`PiInvVac.lean`: **empty** — no errors, no warnings. Guard status re-checked below in V8.

### V8 (2026-09-05) — guards, and the anti-vacuity check in the inverted direction

`lake build Lean4Lean.Verify.Guard`:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

**Anti-vacuity, inverted.** Every §2 statement concludes a negative, so an *uninhabited* hypothesis
set would make them true and useless. Recorded in the file's docstring and here:
`Ordered ∧ PropAgreeOn` has **no hole-free inhabitant in the tree** (route A tainted by
`forallE_inv_stratified`; route B conditional). `SortInvIndep.propAgreeOn_premises_fire` does show
`PropAgreeOn`'s own premise slots all fire at `∅` with the two types syntactically different, so the
hypothesis is not a statement about an empty class. `PiInvWF.lean`'s `SortUniq`-based negatives have
exactly the same status, since `WF.sortUniq'` is hole-tainted — so this round's hypothesis is not
weaker in provability, it is **different**, which is precisely why the entry is now doubly closed.

### V9 (2026-09-05) — method gaps this round exposed

1. **Rule 5 needs a conclusion-shape clause, and this round is the evidence.** Both probes were
   framed around named statements (`ForallEProofPair`, `PiInv ∅`), and the thing that settled Probe 2
   was a theorem named after *neither* — `forallENotProof_of_propAgreeOn`, one import away, whose
   conclusion is `False` and whose subject is "a Π is not a proof". `scripts/exists.lean` warns about
   exactly this ("a residual whose type is literally `Prop` is INVISIBLE to shape search"), and the
   warning fired for me in reverse: I queried names, not conclusions, for the first half of the
   round. A brief that says "no witness at any environment" should be answered by searching for
   *refutations of the shape*, not for consumers of the definition.
2. **A hypothesis-relative negative can be *strengthened* by weakening its hypothesis, and the
   census cannot see it.** `not_forallEProofPair_of_sortUniq` and
   `not_forallEProofPair_of_propAgreeOn` have the same conclusion and unrelated hypotheses; nothing
   in the sorry census, the cone walker, or guard 3 registers that the second exists or that it
   makes the route harder to walk. The vacuity ledger's instruments are blind here in the same way
   `hole-cone.lean` is blind to hypotheses (its §0 table).
3. **"Cheapest witness" needs a monotonicity check before it is believed.** The brief called
   `PiInv ∅ U` "the cheapest unexplored witness left on this row". `∅` is the *cheapest to state*
   and the *hardest to witness*, because `∅ ≤ env` makes every `∅`-conversion universal. Any future
   "try it at `∅`" should run `empty_le_all` + `mono` first and ask which direction the cheapness
   points in.
4. **What this round did not do:** it did not decide `PiInv ∅ U`, and it did not try to build a
   `ForallEProofPair` witness at an `Ordered` non-`WF` environment. The construction attempt was
   worked through on paper (every route needs a common type inhabited by both a sort and a
   proposition, and each rogue rule needs its two sides typed in the *empty* context at the
   *preceding* environment, which regresses) but **no `¬ Ordered badEnv` or similar was proved**, so
   that paragraph is a conjecture and is marked as one here rather than written into the Lean file.
