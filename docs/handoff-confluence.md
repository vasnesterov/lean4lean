# Handoff: the confluence layer

*Written 2026-09-01 by the `descend` stream, at `1109bab`, on being told to stop. Everything
below is either **[measured]** (an instrument was run, this session, and the output is quoted),
**[read]** (read off source, not run), or **[not run]** (believed but unverified). Those three
registers are kept apart deliberately; conflating them is how this project has repeatedly sent
work in the wrong direction.*

---

## 0. STALE — read this before §1, §9 or §10 (2026-09-01, later)

**Three sections of this file are superseded, and §9's "what I would pick up first" is dead work.**

* §1 item (3), §9 and §10 say `PatMajorCanonical` is untested for want of a `Params` instance
  registering an `.app` pattern, and that `PatWFIota.lean` would supply it. **An instance exists** —
  `Theory/Typing/PatAppParams.lean`'s `appParams` — and M3 is **non-vacuous and true** there, though
  with its **typing premises never used** (both right-hand sides closed and mutually `NormalEq`), so
  the test is weak. And `PatWFIota.lean` is not where the *canonical* instance can come from: its
  `paramsOfPiInv` is parametrised, and the concrete environment already exists in
  `Verify/QuotConsts.lean`, which `Theory/` cannot import — so the canonical instance must live
  **outside `Theory/`**. Ledger rows 96–96e.
* The reason this file and three `K*` files gave for there being no such instance — that
  `paramsOfWF`'s `PatWF` is open — was a **wrong reason**, not a gap: `ParamsWitness.lean` builds a
  `Params` by hand. Four items looked blocked on it. Ledger row 96a, and row 100c on the two copies
  that survived the first repair.
* **`KDiamond` does not suffice**, which this file's §1 correctly declined to claim. The
  λ-congruence induction is now run (`Theory/Typing/KEtaDiamond.lean`), and the η-half reduces to
  **injectivity** — `{forallE_inv_stratified, rigidShapeUniqNS}` — not to the rule table. A pinned
  variant (`EtaKD`) needs `KDiamond` and nothing else, with its own stated, undischarged obligation.
  Ledger rows 100–100b.

* **And after the joinability repair, §1(1) and §1(2) are superseded too.** §1(1) calls
  `PatMajorCanonical → KDiamond` "the deliverable"; its conclusion is now **false** at a concrete
  instance. §1(2)'s "next proof obligation" should be the **joinability** form. The repair itself is
  in `Theory/Typing/KDiamondJoin.lean` — and it lands back on Church–Rosser: `KDiamondJ` is
  sandwiched between `kDiamondJ_of_crK` above and the hole-free
  `quotPat_argJoin_of_kDiamondJ` below, so proving it is proving confluence. Ledger rows 103–103c.

§2–§8 stand.


## 1. The state, unhedged

Three sentences, and none of them should be softened when quoted upward.

1. **`PatMajorCanonical → KDiamond` is proved and clean.** `VEnv.kDiamond_of_patMajorCanonical`
   (`Theory/Typing/ParRedCycle.lean`). **[measured]** `#print axioms` gives
   `[propext, Quot.sound]` — no `sorryAx`, no `Classical.choice`.
2. **`KDiamond` is *not* shown to suffice for `ParRedK` confluence.** `EtaKDiamond`
   (`Theory/Typing/KEta.lean`) reduces by `KMeasure.etaKDiamond_of_at` to an *equal-height*
   diamond plus a λ-congruence induction whose base is `KDiamond`-shaped — and **that induction
   is open**. **[read]** Nobody has written it. So "the confluence layer reduces to M3" is a
   statement about where the *residual* sits, not a claim that M3 finishes it.
3. **`PatMajorCanonical` is *not* shown satisfiable.** At `cycParams` it is **vacuous**, because
   `cycNoPat` says the environment registers no rule at all. Non-vacuity needs a `Params`
   instance registering an `.app` pattern, which is what `Theory/Typing/PatWFIota.lean` would
   supply and which **no instance in this tree has**. **[read]**, from
   `ParRedPropRefute.lean`'s own §Satisfiability.

A newcomer should read (1) as the deliverable, (2) as the next proof obligation, and (3) as the
reason the whole thing is currently untested against a real rule table.

---

## 2. Why the add-steps-to-`ParRed` route is closed for good

`NormalEq` has nine constructors; `ParRed` has eight; two of `NormalEq`'s — `proofIrrel` and
`etaL`/`etaR` — have no `ParRed` counterpart. `descend`'s conclusion asks a `NormalEq` to be
pushed through *to a reduct*, so at exactly those two it asks for a step the relation does not
contain. The obvious repair is to add the two steps. That route is dead, and this is the part a
newcomer cannot cheaply reconstruct, because each negative needs a different argument.

`Theory/Typing/ParRedMissing.lean` defines the extension `ParRedP` (all of `ParRed` via `of`,
plus `app` congruence, plus `proofRepl` and `etaContract`) — deliberately a **sub**relation of
the intended extension, so that a reduction exhibited in it is a reduction in the real one, and
the repairs below are conservative. **[measured]** all of §2–§3 there is `sorryAx`-free.

### 2.1 The obligation demands both directions, before any constructor exists

`Theory/Typing/ParRedCycle.lean` builds `cycEnv`: `P : Prop`, `D : P`, **`D2 : P`**, `T : Type`,
`C : P → T`. The second constant proof is the whole point (§6.1). Then:

> `descend` is called at `C D` against the pattern naming `D2`, **and** at `C D2` against the
> pattern naming `D`. Both are legitimate `Params.pat_simple` shapes — `.app` of two `.var`-chains
> over `.const` leaves — and `descend` quantifies over both.

`cyc_of_answers` proves, for an **arbitrary** relation `R`, that meeting the requirement at both
witnesses forces `C D →* C D2` **and** `C D2 →* C D`. **[measured]** axioms `[propext]`.

Two things make this not a strawman, and both matter:

* `answersAt_of_descentLam` checks that `AnswersAt` is *literally the first three conjuncts* of
  `DescentLam 0`. It is a **weakening** of `descend`'s obligation — it drops the `NormalEq` clause
  on matched arguments, both WF clauses, and the eta tower. So refuting it refutes `descend`.
* The **level clause is kept**, and that is what pins the reduct to `C D2` *on the nose*.
  `Pattern.Matches (.const c) (.const c ls)` accepts any `ls`, so without the level clause one
  gets `C D →* C[ls₁] D2[ls₂]` with junk levels and no exact cycle — only non-termination.
  `List.Forall₂` forces equal length, so `≈ []` forces `= []`. Anyone weakening `AnswersAt`
  further should check they have not lost this.

### 2.2 No well-founded strict order orients it

* `no_decreasing_measure` — no `Nat`-valued measure decreasing along `R`.
* `no_wf_orientation` — no well-founded **strict order** orienting `R` at all. This is the general
  form of "try orienting it". Transitivity is assumed because a *chain* of steps must compose
  into one `lt`, which is exactly what an orientation by a strict order provides.
* `parRedP_no_decreasing_measure` — and it applies to the real extension, **unconditionally**
  (no hypothesis at all).

**[measured]** `no_wf_orientation` axioms `[propext, Classical.choice, Quot.sound]`.

The reason is not technical: proof irrelevance has no preferred direction, and any relation
strong enough for `descend` inherits that. A selector-oriented proof replacement (every proof
reduces toward a canonical one) is acyclic by construction and therefore **cannot** meet the
requirement — orientability and sufficiency are incompatible. There is nothing to trade off.

### 2.3 No grading of any kind removes a two-cycle

`no_grading_removes_cycle`: a *grading* is a monotone family whose union is the relation; a
two-cycle is **two steps**; a grading bounds structure **within** a step and never the length of
a chain. So the cycle already lives at a finite grade. **[measured]** axioms `[propext]`.
`parRedP_cycle_survives_grading` instantiates it at `ParRedP`.

This closes the route for **every** grading, not only `ParRedKn`. See §6.2 for why it had to be
proved rather than inherited.

---

## 3. Why the rewiring is blocked

The tempting move is: delete `descend`, land `NormalEq.parRed` and `IsDefEq.church_rosser` on the
`descendV` / `appDF_extra_of_descendVK` route, census 13 → 12. It does not work, for three
independent reasons.

1. **Over `ParRed`, the target statement is false.** `KCanonical.lean`'s
   `not_crStatement_of_kstep` refutes `CRStatement` — `IsDefEq.church_rosser`'s statement
   **verbatim** (`crStatement_holds` is the anti-strawman check) — from a registered K-redex under
   an `eta`, using **no `hK`**, only `KStep.defeq`, i.e. only that the rule is admissible.
   `ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor` does the same for `parRed`.
   **[read]**
2. **The replacement is downstream of its caller.** **[measured]** import chain:
   `ChurchRosser → HeadReduction → HeadRedStuck → KRule → KDescend → KEta → KMeasure → KSite7 →
   KSite7App`. `NormalEq.appDF_extra_of_descendVK` lives at the far end, so `NormalEq.parRed`
   cannot call it without an import cycle. The rewiring is **not** a local edit to `parRed`'s
   `extra` case, and anyone who prices it as one will be wrong by a whole file reorganisation.
3. **Moving the conclusion to `ParRedK` needs `KDiamond`** — which is §1's item (2).

### The sentence that cost a mis-priced brief

Both refutations in (1) need a `Params` instance registering an `.app` pattern, and **no instance
in this tree has one**. That is a *weaker* grade of refutation than `descend`'s (ledger row 33 vs
row 32). It is tempting to conclude the statements are therefore safe to prove.

> **"Not reachable today" is not "safe to prove."**

There is no instance-uniform theorem behind either statement. Deleting `descend` and carrying its
obligation as a hypothesis on `parRed`/`church_rosser` would push a hypothesis onto all 193 users
with nothing behind it — and, by §5, a hypothesis of exactly that shape is *false* at the one
witness instance available, so its consequences would be vacuous. That is a vacuity transfer, not
a repair. Do not do it, and do not weaken either statement to make wiring go through: both are
refuted as stated and the fix is upstream.

---

## 4. What was tried and failed, with the failing step

Four dead ends. Each is cheap to re-attempt and each wastes a round.

| attempt | fails at |
|---|---|
| `ParRedKn` grading applied to `descend` | The term does not **move**. `refG` is `ParRedK`-normal at every grade (`refParRedK_G`, `refParRedKn_G`), so no grading can produce the reduct the descent needs. Ledger row 71a. |
| Orienting the proof-replacement step | §2.2. The obligation is symmetric because proof irrelevance is; orientability and sufficiency are incompatible. |
| Any grading applied to the **cycle** | §2.3. A grading bounds structure within a step, never chain length. |
| `PatMajorCanonical` stated with a **composed** `IsDefEqU Γ c c'` hypothesis | Composing the two major-premise conversions through the shared redex needs `IsDefEqU.trans`, which reconciles `A₀` with `A₀'` and therefore **carries `sorryAx`**. **[measured]** `IsDefEqU.trans` depends on `[propext, sorryAx, Classical.choice, Quot.sound]`. |

On the last one: the fix was to pass the two conversions **un-composed** — `HasType f (forallE A₀ B₀)`, `HasType f (forallE A₀' B₀')`, `IsDefEq h c A₀`, `IsDefEq h c' A₀'`. That is *weaker as a
hypothesis*, hence a **tighter** request, and it keeps the reduction free of the injectivity
holes. This is ledger row 64a's split applied deliberately: the direction that **guides work**
stays clean. The composed version measured tainted in the axiom sweep, not in review — see §6.3.

---

## 5. The eighth instrument blindness: a missing step is not a property of the relation

This gets a section because it is structural, it generalises past this corner, and it was caught
in a draft rather than in review.

The obvious way to say "`ParRed` is missing proof replacement" is a hypothesis:

```lean
def ParRedProofRepl : Prop :=
  ∀ {Γ P h h'}, Γ ⊢ P : .sort 0 → Γ ⊢ h : P → Γ ⊢ h' : P → Γ ⊢ h ≫ h'
```

**Every consequence of that hypothesis is vacuous at the only witness instance in the tree.**
`ParRed` is a fixed inductive with eight constructors, so the `Prop` is a claim *about that
inductive*, and it is **false** at `refParams`: `not_parRedProofRepl` derives
`ParRed refCtx (.bvar 0) (.const D [])` from it and contradicts `refParRed_bvar`. Likewise
`not_parRedEtaContract`, against `refParRed_id`. **[measured]** both are theorems in
`ParRedMissing.lean`, `sorryAx`-free.

The first draft of `ParRedMissing.lean` proved three "witness repaired" theorems under those
hypotheses. All three compiled. All three were vacuous — *exactly at the instance they were
about*. Nothing in a build, a census, a cone measurement or a `#print axioms` sweep flags this:
the falsity is in the **hypothesis**, and the standard instruments all look at conclusions.

**The rule.** A missing reduction step must be stated as a **constructor of an extension**, never
as a property of the relation being extended. `ParRedP` is the corrected form, and everything in
`ParRedMissing.lean` §2–§4 is unconditional as a result.

**The general shape**, worth carrying past reductions: *any* hypothesis asserting that a fixed
inductive contains a rule it does not have is refutable, so anything proved from it is vacuous.
The guard is to ask, of every hypothesis in a new statement: **is this satisfiable at the witness
this statement is about?** — and to prove the answer, not assume it.

---

## 6. Three things about method, kept because the results do not show them

### 6.1 The second constant proof, and why needing it was itself informative

`refEnv` (`DescendRefute.lean`) has exactly **one** constant proof of `P`. So its cycle
(`refParRedP_cycle`) runs between `.bvar 0` and `.const D []` — one endpoint a **context
variable**. That leaves a live reading: "orient toward closed terms." The cycle looked essential
and was not yet shown to be.

Noticing that the *need* for a new environment was itself the informative part is what produced
`cycEnv`, whose cycle runs between two **closed** terms `C D` and `C D2` in the **empty context**
(`cycCtx = []`). There is nothing left to orient by. **[measured]** `cycEnv_wf` is `sorryAx`-free
and `Classical.choice`-free.

Generalisable: when a witness *almost* refutes something, the gap between "almost" and "does" is
usually a missing piece of the witness, not a missing piece of the argument.

### 6.2 Checking grading separately rather than inheriting the earlier verdict

Row 71a already said grading cannot rescue `descend`. It would have been natural to inherit that
for the cycle. **The mechanisms differ**: there the term does not *move*, here the terms move in a
**circle**. Same verdict, different proof — and the second proof turned out to be *more* general
(it closes every grading, not just `ParRedKn`). An inherited verdict would have been correct and
would have been worth strictly less.

Generalisable: two negatives with the same conclusion are not the same negative. Re-deriving one
sometimes buys generality.

### 6.3 The axiom sweep is a design instrument, not a formality

The composed-`IsDefEqU` version of `PatMajorCanonical` (§4) looked right, compiled, and read
correctly. It measured `sorryAx`-tainted. Running `#print axioms` on *every* new declaration —
not just the headline — is what turned a tainted request into a clean one, and the redesign it
forced (un-composed conversions) also made the request **tighter**. The sweep found a design
improvement, not just a defect.

---

## 7. Citations drift; cite declarations, not lines

This is a live, twice-burned problem and it deserves a standing habit.

`DescendRefute.lean`'s table of `descend`'s three `sorry`s has been stale **twice**:
`:1799`/`:1784`/`:1779` (off by ~290 lines), corrected to `:2074`/`:2079`/`:2094` on 2026-09-01,
and **those went stale within one commit** when prose was inserted higher up `ChurchRosser.lean`.
It now carries no line numbers at all and names the *branch* instead — all three are in
`NormalEq.descend`'s `.app`-node case, in the `cases hm` / `app` branch, distinguished by which
recursive call returns `.inr`.

**[measured] at `1109bab`**, for orientation only — expect these to move:

| declaration | `ChurchRosser.lean` |
|---|---|
| `inductive ParRed` | 752 |
| `ParRed.triangle` | 1073 |
| `def ParRedS` | 1231 |
| `ParRedExt.parRed_beta` | 1352 |
| `def DescentLam` | 1906 |
| `def DescentOut` | 1923 |
| `NormalEq.descend` | 2011 |
| its three `sorry`s | 2085, 2090, 2105 |
| `NormalEq.appDF_extra_of_descend` | 2201 |
| `NormalEq.parRed` | 2297 |
| `ParRedS.church_rosser` | 2435 |
| `IsDefEq.church_rosser` | 2480 |

Prefer `grep -n "^theorem NormalEq.descend"` to any number in this table.

---

## 8. Measurements

**[measured] this session.** Run from a private `ConeJoin`-importing file, per the standing
instruction that the `ConeJoin` import *is* the duplicate-name check — a `dup-names` pass and a
measurement run are **not** interchangeable in time. Mine passed twenty minutes before a
concurrent stream briefly landed a duplicate `VEnv.SortNotProp` (`InjPiRogue` vs `PropConv`) that
made `ConeJoin` un-importable and silently shrank my closure from 193/296 users to 19/68. That
stream renamed it to `SortNotPropStrong` and the figures below are post-fix.

### Cones

| seed | cone | `descend` in cone | holes |
|---|---|---|---|
| `NormalEq.descend` | 3837 | — | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `NormalEq.descendV` | 3839 | no | the same two |
| `NormalEq.appDF_extra_of_descend` | 3942 | **yes** | the two **+ `descend`** |
| `NormalEq.appDF_extra_of_descendVK` | 3989 | no | the same two |
| `parRedKStatement_of_rows` | 4261 | no | the two **+ `IsDefEqU.weakN_iff`** |
| `parRedKStatementN_zero` | 683 | no | **none** |

### The two-sided trade, and it is clean

`descend` has exactly **one** direct user, `NormalEq.appDF_extra_of_descend`, feeding
`NormalEq.parRed`. So all 193 users pass through one chokepoint and the restatement serves all
of them or none.

| | |
|---|---|
| `descend` users (would leave) | **193** |
| `IsDefEqU.weakN_iff` users (would arrive) | **296** |
| descend users **already** on `weakN_iff` | **191** |
| descend users that would **newly** acquire it | **2** |

And the two are named: `descendStatement_holds` and `NormalEq.appDF_extra_of_descend` — **both
deleted by the rewiring itself**. So the true concentration is **zero**. If §1's items (2) and (3)
are cleared, the trade is free and the census drops 13 → 12 outright. This is the first clean
two-sided trade in the ledger; state it two-sided, never netted.

### Stale figures corrected this session

| where | was | is |
|---|---|---|
| `ChurchRosser.lean` | `descend` has "145" transitive users | **193** (census) / 206 users, 196 sole (`hole-rank`) |
| `ChurchRosser.lean` | rewiring "is not a hole-count improvement" because it trades for a refuted hypothesis | that hypothesis was `hK`, now discharged unconditionally by `ParRedK.hK` |
| `ChurchRosser.lean` | `forallE_inv_stratified` has "446" users | **650** |
| `KDescend.lean` | **"`sorry`-free", three times**, of `NormalEq.descendV` | it carries `sorryAx`: **[measured]** `[propext, sorryAx, Classical.choice, Quot.sound]`, via `Params.sortUniq` / `IsDefEq.uniq`. The axiom list is now printed **inline** so the error cannot recur. |
| `DescendRefute.lean` | three `sorry` line citations | §7 |
| `ParRedKGraded.lean` | typing half "sufficient for 18 of the hole's users" | **43** of 296, **46** with the tenth gate (`handoff-weakn.md` §5.3) |
| `ParRedKGraded.lean` | "that one composition is the whole obstruction" (self-flagged inspection-only) | refuted by `CRBetaGen`'s `parRed_beta_gen`; ledger row 59 |

The `KDescend.lean` one is worth dwelling on: **"no local `sorry`" and "no `sorryAx`" are
different claims**, and the file whose entire subject is a refuted lemma asserted the wrong one
three times. `#print axioms`, always.

---

## 9. What I would pick up first

**I agree with the coordinator: `PatWFIota.lean`'s `.app`-pattern instance.** It is the single
item that unblocks the most, and the reason is that four separate things are waiting on the *same*
missing object:

1. `PatMajorCanonical` is vacuous without it (§1 item 3) — so M3 currently cannot be tested at
   all, and a "proof" of it today would be a proof about an empty quantifier.
2. `not_crStatement_of_kstep` needs it to become a *reachable* refutation rather than a
   conditional one (§3).
3. `not_parRedStatement_of_propMajor` needs the same instance.
4. `KStep.stuck_fires` — the non-vacuity witness for the K-rule itself — needs a registered rule.

So one construction converts three conditional results into reachable ones **and** makes the
session's main deliverable non-vacuous. Nothing else in this corner has that fan-out. And per the
coordinator, the injectivity corner's three residuals were independently priced as three
instances of one fact plus Church–Rosser, so both corners point at the rule table
(`docs/critical-path.md`, "The convergence").

**One caution I would attach.** Building that instance will make `PatMajorCanonical` non-vacuous —
and it may make it **false**. That is a real possibility, not a formality: the same instance is
what refutes `church_rosser`'s and `parRed`'s statements. Whoever builds it should be prepared for
the outcome "M3 is false at the first real rule table", and should treat that as the *result*
rather than as a failure — it would relocate the confluence layer again, and it would do so with a
reachable witness, which is the strongest kind of finding this corner produces.

**Where I would not start.** Not on `ParRed.triangle`. §2 says every route through a
measure or a grading over an extended `ParRed` is closed, and the theorems are unconditional. A
newcomer's instinct will be to look for a cleverer measure; there isn't one, and the three
theorems in `ParRedCycle.lean` §1–§4 are there to save that round.

---

## 10. Files

| file | what it holds |
|---|---|
| `Theory/Typing/DescendRefute.lean` | `refEnv`, `refParams`, the three witnesses, `DescendStatement` and its three refutations, `descend_uniq_sortUniq_not_all` |
| `Theory/Typing/KDescend.lean` | `Pattern.NoApp`, `Params.pat_app_noApp`, `NormalEq.descendV`, `appDF_extra_of_descendV`, `KDiamond`, `KStep.uniq_defeq` |
| `Theory/Typing/DescendRestate.lean` | `DescendStatementV` and both bounds; `refDescentOutV`; `descendV_dodges_witnessA`; `refParRedK_G` / `refParRedKn_G` |
| `Theory/Typing/ParRedMissing.lean` | the two missing constructors; `ParRedP`; all three witnesses repaired unconditionally; `refParRedP_cycle`; §5's blindness |
| `Theory/Typing/ParRedCycle.lean` | `cycEnv`; `AnswersAt` + `answersAt_of_descentLam`; `cyc_of_answers`; `no_decreasing_measure`; `no_wf_orientation`; `no_grading_removes_cycle`; `PatMajorCanonical`; `kDiamond_of_patMajorCanonical` |

**[measured] at `1109bab`**: census `13`; guard 1 `exactly the 24 frozen axioms ✓`; guard 2
`within whitelist ✓ (proof INCOMPLETE: sorryAx present)`; guard 3 `(2/2 remaining) ✓`;
`ConeJoin`-importing file imports clean; `descend` still present with 193 users.

**[not run]**: the Kernel Arena suite. Nothing in this session touched the checker, only
`Theory/`, so no behavioural change is expected — but expected is not measured.
