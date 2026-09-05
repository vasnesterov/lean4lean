# handoff-injcensus — censusing the parts of `RigidShapeUniqNS` instead of attacking the conjunction

Stream: InjCensus. Opened 2026-09-05, HEAD `9165203` (bare build green 1670 jobs, guards 1/2/3 ✓, census 13).

Owned: `Lean4Lean/Theory/Typing/InjCensus.lean` (new), `docs/handoff-injcensus.md` (this file).
Read-only, explicitly: `Lean4Lean/Theory/Typing/Injectivity.lean` (holds both target holes).
Frozen: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

Target: `Lean4Lean.VEnv.WF.rigidShapeUniqNS` (`Injectivity.lean:1046`), a `sorry`. Four rounds have
attacked the conjunction. This round does not attack it: it **censuses the family**, asking for each
member what environment hypothesis it actually needs (`Ordered`, `Ordered` + a named clause,
`VEnv.WF`, or unknown), and whether the members are independent.

Deliverable: one row per family member — weakest sufficient environment hypothesis, a proof or a
witness-refutation at that strength, independence. Headline: one problem or several, and which
member is load-bearing.

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `Injectivity.lean`, `InjMethod.lean`, `InjPiRogue.lean`, or any
`docs/handoff-inj*.md` in this session.** Answers are appended below the questions once measured.
**A filled answer is never edited**; corrections go in §2 with a timestamp.

### The four shape questions, instantiated to the census

**Q1. Does the target exist — judged on the *conclusion head*, not the obligation's name?**
My target is not a theorem, it is a *decomposition*. So the existence question is two-layered:
(a) Does `rigidShapeUniqNS_iff_family` exist under that name, and is it really `sorryAx`-free **in
both directions** as `Injectivity.lean:208` says, or is one direction conditional / a different
statement? (b) Does each *member* of the family exist as a **standalone named `Prop`** whose
conclusion head is the family member itself — so that "census the members" is reading off existing
definitions — or does the family exist only as an unnamed conjunction inside one `iff`, in which
case the census's first cost is *naming* the members in `InjCensus.lean`? And: how many members are
there? `:208` says **three** constant-spine facts; `RigidShape` has three constructors, so the
`Compat` table has 3×3 = 9 entries, of which `sort`/`sort` is excised by `¬ BothSort`. Three ≠ eight,
so either the family is coarser than the table or the table's entries are not the members. Which?

**Q2. Is the work in the direction I think?**
I am briefed that this is "one problem or five". The direction-check is whether the `iff` is a
**genuine decomposition** — members provable/refutable *separately* — or whether it is an `iff` into
a conjunction whose parts are **mutually entangled**, so that the census's per-row answers cannot be
combined. Concretely: does any member's *statement* mention another member, or quantify over the
same environment in a way that forces a simultaneous induction? And is the direction I need
(family → `RigidShapeUniqNS`) the direction that is actually `sorryAx`-free? A census that measures
each row at its own strength is worthless if the assembly step needs all rows at `VEnv.WF`.

**Q3. Measurement or docstring?**
Every fact in my brief must be classified as *measured in this repo* or *prose*. The specific ones:
(i) "`rigidShapeUniqNS_iff_family` is `sorryAx`-free in both directions" — measured or docstring?
(ii) "`rigidPiUniq_iff_piInv` shows `RigidPiUniq` **is** `VEnv.PiInv`, neither weaker nor stronger" —
measured both ways, or one way plus prose? (iii) `not_sortForallEDisjN_of_ordered` "hole-free" and
`not_wf_injEnv` — measured (I must `#print axioms` each). (iv) `propAgree_conclusion_not_sortUniq`,
`SubstCRefute`, `DefInvRefute.defInv_all_false` — measured, and **at what generality**; my brief was
burned once by quoting a *conditional* refutation flat (`quotParams_not_crStatement`), so any
refutation I cite gets its hypotheses read off the actual statement, not the name.

**Q4. What does the structure branch on, and where are its extremes — i.e. what does `WF` fail to forbid?**
The cheapest instrument here is instantiating each universally quantified *argument* at its extremes.
The arguments of a family member are: the **environment** (`env`), the **universe bound** (`U`), the
**context** (`Γ`), the **shapes** (`s₁ s₂`), and the **term** (`e`). For the environment the extremes
are not "small" and "large" but **the states the side condition fails to forbid**: for `Ordered`,
what does it *not* say about `defeqs` (a `VDefEq` whose lhs is not `const`-headed — `injEnv`; two
δ-rules on one constant — `InjPiRogue`); for `VEnv.WF`, likewise. So per member I must ask: *which
`Ordered`-legal environment state does this member's truth depend on, and does `VEnv.WF` forbid it,
and by which named clause?* Extremes for the other arguments: `U = 0`; `Γ = []`; `e` a `bvar`/`sort`
(no `defeq` can fire) versus `e` a `const` (every `defeq` can); shapes at equal vs distinct
constructors. The named-clause question is the whole deliverable, because "needs `VEnv.WF`" is not an
answer — **which clause of `VEnv.WF`** is.

### Numbered predictions, made cold (blank — to be filled only from measurement)

- **P1.** Number of family members in `rigidShapeUniqNS_iff_family`. Prediction: **3**, and they are
  *not* the `Compat` table entries but coarser groupings (a spine/`app` fact, a `pi` fact, a
  cross-shape disjointness fact). Prediction that the 8 surviving table entries map onto them
  many-to-one. Falsifier: reading the `iff`'s RHS.
- **P2.** How many members are **refutable from `Ordered` alone** (a witness environment that is
  `Ordered`, outside `VEnv.WF`, and falsifies the member). Prediction: **at least 2** — the
  cross-shape sort/Π entry (already known, `injEnv`) and the `pi`/`pi` member (via `InjPiRogue`'s
  two-δ-rules-on-one-constant rogue). Prediction that the `app`/`app` member is **also** refutable
  from `Ordered` (the `ConstInvWitness` rogue), making it 3 of 3 and the corner *one* problem, not
  five. Confidence: medium.
- **P3.** The load-bearing member. Prediction: **the `pi`/`pi` member (`RigidPiUniq` = `VEnv.PiInv`)**,
  because it is the only *positive* member that must produce a conversion derivation, and because
  `PiInv` is what the rest of the file's clients consume. The cross-shape members I predict are
  **cheaper**: refutable-from-`Ordered` but *provable* from `VEnv.WF` by a type-level argument that
  never needs confluence (a sort and a Π cannot share a type). Falsifier: finding a cross-shape entry
  whose `VEnv.WF` proof needs Π-inversion, which would collapse the census to a single problem.
- **P4.** Independence. Prediction: **not independent** — I predict the cross-shape members *reduce*
  to the positive ones (you refute `e : sort` vs `e : pi` by inverting one side), so the dependency
  graph has `pi`/`pi` at the bottom. Prediction: exactly **one** member is at the bottom.
- **P5.** Which named `VEnv.WF` clause each refutation is separated by. Prediction: the two clauses
  named in my brief — `VEnv.RuleShape.delta` (logically prior; pins "every `defeq` lhs is
  `const`-headed") and `DefEqHeadsUnique` (pins "at most one δ-rule per constant") — **suffice for
  all cross-shape members**, i.e. `Ordered` + those two clauses is enough and full `VEnv.WF` is not
  needed for any member except possibly `pi`/`pi`. Confidence: low-medium; this is the prediction I
  most expect to be wrong, because a `defeq` whose lhs *is* `const`-headed and unique can still be
  ill-typed unless `Ordered` already types it.
- **P6.** Cost/outcome. Prediction: **the census completes as a table but at most one row gets a new
  machine-checked *proof*.** I predict I land with: 2–3 rows carrying real witnesses (some pre-existing,
  at least one new), 1 row at `unknown`, and the headline answer delivered. I predict I do **not**
  close `WF.rigidShapeUniqNS`, and I predict the honest limit of this round is that "weakest
  hypothesis" is measured as *"this strength is insufficient (witness)"* + *"that strength suffices
  (proof)"* only for the rows where both exist; elsewhere it is a one-sided bound and must be
  reported as such.

---

## §2 — Verdicts, appended as measured (append-only; each entry dated)

### V1 (2026-09-05) — Q1 answered: the family exists, has **five** members, and the brief's count is a doc defect

`Lean4Lean/Theory/Typing/RigidNodeCircle.lean:245` — `VEnv.rigidShapeUniqNS_iff_family`, arity
(explicit) 3: `(henv : VEnv.WF env) (hsu : env.SortUniq U) (htr : env.ProofTransport U)`, plus the
section variables `{env : VEnv} {U : Nat}` (invisible in the statement — method rule 4).  Both
directions are present in the term: `⟨fun h => ⟨…⟩, fun ⟨…⟩ => rigidShapeUniqNS_of_family …⟩`.

**Members, named as standalone `Prop`s** (so the census is reading off definitions, not naming them):

| # | member | def site | shape entry |
|---|--------|----------|-------------|
| 1 | `VEnv.PiInv` | elsewhere (see V2) | `pi`/`pi` |
| 2 | `VEnv.RigidSortPiDisj` | RigidNodeCircle.lean:125 | `sort`/`pi` (+ `pi`/`sort`) |
| 3 | `VEnv.RigidConstAppInv` | RigidNodeCircle.lean:132 | `app`/`app` |
| 4 | `VEnv.RigidConstPiDisj` | RigidNodeCircle.lean:139 | `app`/`pi` (+ `pi`/`app`) |
| 5 | `VEnv.RigidConstSortDisj` | RigidNodeCircle.lean:144 | `app`/`sort` (+ `sort`/`app`) |

So the 8 surviving `Compat` entries map **8 → 5** onto members, two-to-one on the three off-diagonal
pairs (the `⟸` proof `rigidShapeUniqNS_of_family` uses `hs.symm` for the mirrored entry).
**P1 is WRONG**: predicted 3, actual **5**.

**Doc defect found, and it is the one my brief inherited.** `Injectivity.lean:208` says the bridge
"is exactly `PiInv` together with **three constant-spine facts**" — that is 4, and it silently drops
`RigidSortPiDisj`, which is *not* a constant-spine fact (no `c`, no `RuleFreeHead`).
`RigidNodeCircle.lean:12` says "**five** properties" and the theorem confirms five.  My brief quoted
the Injectivity prose.  Anyone budgeting rows from `:208` budgets one row too few, and the dropped
row is the sort/Π one — the very entry that `InjMethod.injEnv` refutes.  Recorded as a prose-vs-source
discrepancy, not a soundness issue.

### V2 (2026-09-05) — Q2 answered: the decomposition is genuine, and the **assembly step is cheap**

Statement-level independence: **yes**, no member's statement mentions another.  All five are
`Prop`-valued predicates of `(env, U)` alone.  `PiInv` is `Injectivity.lean:347`, arity 0 explicit
(`{Γ A B A' B'}` implicit, section `{env} {U}`).

The direction I need is `⟸`, `rigidShapeUniqNS_of_family` (RigidNodeCircle.lean:169), and its
hypotheses are **`Ordered env` + `env.ProofTransport U` + the five members** — *not* `VEnv.WF`.
The `⟹` direction is the one that costs `VEnv.WF ∧ SortUniq ∧ ProofTransport`.  So:

> **The assembly is not the problem.**  A census that discharges the five members at any strength
> ≥ `Ordered` + `ProofTransport` closes `RigidShapeUniqNS` at that strength.  There is no
> simultaneous induction and no mutual entanglement in the assembly; the branch structure is a
> 9-way `cases` on `s₁ × s₂` with one member consumed per branch (`htr`/`hnp` in `app`/`app` only).

Consequence for the census's shape: **per-row answers *do* compose.**  The "one problem or five"
question is therefore entirely about the rows, not about the glue.

### V3 (2026-09-05) — Q3 answered: what was measured, what was prose

`#print axioms` run from `lake env lean` **after** a green `lake build` (RigidNodeCircle §4's
instrument caution honoured):

| cited fact | name as the compiled environment has it | verdict |
|---|---|---|
| decomposition, both directions | `Lean4Lean.VEnv.rigidShapeUniqNS_iff_family` | `[propext, Classical.choice, Quot.sound]` — **measured**, `sorryAx`-free ✓ |
| `pi`/`pi` entry **is** `PiInv` | `Lean4Lean.VEnv.rigidPiUniq_iff_piInv` | `[propext, Classical.choice, Quot.sound]` ✓ |
| 3 const members ↔ hole B over the base | `Lean4Lean.VEnv.constFamily_iff_rigidShapeUniqNS` | `[propext, Classical.choice, Quot.sound]` ✓ |
| member 2's UC form ↔ hole B over the base | `Lean4Lean.VEnv.sortPiDisjUC_iff_rigidShapeUniqNS` | `[propext, Classical.choice, Quot.sound]` ✓ |
| "`three` constant-spine facts" | `Injectivity.lean:208` prose | **PROSE, and undercounts** — see V1 |
| "cross-shape members are provable from `VEnv.WF` by a type-level argument" | *my own P3, second half* | **FALSE, and already refuted in-tree**: `UnivDiscrim.lean` shows `.sort u` and `.forallE (.sort u) (.sort u)` are both types at `.succ u`; my own `censusEnv` types `Prop`, `∀(_:Prop),Prop` and `C.{0}` all at `Sort 1`. There is no type-level discriminant. |

Also measured, and it changes how row 1 must be read: `InjPiRogue.lean`'s §"Why no refutation is
constructible" is not rhetoric — it enumerates the tree's **two** techniques for proving a
conversion absent (`IsDefEq.closedN`; inversion at a bounded index) and shows both fail on this
shape.  Rules relate **closed** terms, so `closedN` is vacuous at every rogue witness, and an
`extra` link carries no index bound.  This is the reason rows 1 and 3 behave differently from
2/4/5, and it is a property of the *tree*, not of my effort.

### V4 (2026-09-05) — Q4 answered, and it is the census: `Lean4Lean/Theory/Typing/InjCensus.lean`

One `Ordered` environment, `censusEnv`: one constant `C : Sort 1` carrying **one universe
parameter its type does not mention**, and **three** rules, none `const`-headed —

    dfPi    : ∀ (_ : Prop), Prop ≡ C.{0}   at Sort 1
    dfSort  : Prop               ≡ C.{0}   at Sort 1
    dfSort1 : Prop               ≡ C.{1}   at Sort 1

`ordered_censusEnv` ✓, `ruleFreeHead_cName` ✓ (so the `RigidShape.RuleFree` side condition is
*satisfied*, not dodged), `not_wf_censusEnv` ✓ — all `[propext, Quot.sound]` except
`not_wf_censusEnv` which adds `Classical.choice` through `WF.choose_spec`.  No `sorryAx` anywhere.

**The extremes that mattered were exactly the ones `WF` fails to forbid**, as the method rule
predicted: not "small `env`" but "a rule whose lhs is not `const`-headed" (`RuleShape.delta`) and
"one constant, two level instantiations" (which `Ordered` never relates).  The second is new here;
`InjMethod.injEnv` has no constants at all and `InjPiRogue.roguePiEnv`'s constant has no universe
parameters, so neither could reach the spine members or the level conjunct.

**Verdicts, one row per member** (`Ordered` column = is `Ordered` demonstrably insufficient):

| # | member | polarity | `Ordered` insufficient? | witness (all in `InjCensus.lean`) |
|---|---|---|---|---|
| 1 | `PiInv` | positive | **only conditionally** | `not_piInv_of_rigidSortPiDisj`, `ordered_not_enough_for_piInv` — at `roguePiEnv`, antecedent = member 2 there |
| 2 | `RigidSortPiDisj` | negative | **YES, outright** | `not_rigidSortPiDisj` |
| 3 | `RigidConstAppInv` | positive | **YES modulo one `¬ IsProof`** | `not_rigidConstAppInv_of_not_isProof`; `not_rigidConstAppInvNP` is unconditional |
| 4 | `RigidConstPiDisj` | negative | **YES, outright** | `not_rigidConstPiDisj` |
| 5 | `RigidConstSortDisj` | negative | **YES, outright** | `not_rigidConstSortDisj` |

Separating clause, for rows 2/3/4/5: **`VEnv.RuleShape.delta` alone** — one rule with a
non-`const`-headed lhs.  `DeltaUnique.DefEqHeadsUnique` is *not* needed (my rules have no head at
all), so this is one clause cheaper than `InjPiRogue`'s two-rule separation, and it covers three
members that no witness in the tree had reached: members 4 and 5 need a **declared** constant for
the spine, and `InjMethod.injEnv` has none.

**Independence, measured on this axis:** rows 2, 4 and 5 fall at *one* witness under *one* clause
— they are not three separate environment problems.  Row 3 falls at the same witness plus exactly
one `¬ IsProof` instance.  Row 1 **cannot** share that witness: refuting it needs member 2 to
*hold* at the environment, and `censusEnv` refutes member 2.  So rows 1 and {2,3,4,5} are not
co-witnessable, and the dependency runs **row 2 below row 1** — the opposite orientation from P4's
guess.

### V5 (2026-09-05) — the honest limit: every bound here is one-sided

The deliverable asked for "the weakest environment hypothesis that **suffices**".  For all five
members that column is **unknown**, and no round can fill it without closing the hole: an upper
bound below `VEnv.WF` would *be* a proof of the member.  What this round produced is the other
side — insufficiency, with a named clause — for four rows out of five.  The table above should be
read as lower bounds, and any future brief quoting it must keep the word "insufficient" in it.

Two further limits, both provable rather than confessed:

* **Row 3's residue is exactly one `¬ IsProof`**, and it is not dischargeable cheaply: the clean
  supplier is `not_isProof_of_sort'`, whose hypotheses are `SortUniq ∧ Ordered ∧ ProofTransport`
  (`not_rigidConstAppInv_of_sortUniq` states the routed form), and `SortUniq` at `censusEnv` is as
  unavailable as `SortUniq` anywhere in this corner.  The `sorryAx`-free-looking alternative,
  `Injectivity.not_isProof_of_defeqU_sort`, is `sorryAx`-**backed**.
* **Row 1 cannot be improved by a cleverer witness in this tree**, for the reason in V3: every
  refutation of a positive member needs a ¬conversion fact, and the tree has none that reaches an
  unbounded, closed-term conversion.  Row 3 escapes only because its conclusion carries a *level*
  list, which is decidably refutable; `PiInv` has no level conjunct at all, and
  `RigidNodeCircle.imax_dom_not_pinned` is the machine-checked reason level data cannot be
  smuggled into its domain half.

### V6 (2026-09-05) — the headline

**Not five, and not one: two.**  On the environment axis the corner has one problem shared by four
members — *`Ordered` permits a rule whose left-hand side is not `const`-headed*, one witness, one
clause (`RuleShape.delta`) — and one member left over, **`PiInv`**, which is the load-bearing one.

`PiInv` is load-bearing on three independent counts, of which only the first is mine:

1. it is the only member with **no** `Ordered`-level insufficiency witness, and the reason is
   structural (V3/V5) rather than unfinished work — so it is the only row whose environment
   requirement is genuinely unmeasured, and the only one that could conceivably need far less
   than `VEnv.WF`;
2. `RigidNodeCircle.lean` already names it as the corner's second node, with `SortUniq → PiInv`
   blocked in both level coordinates;
3. it also pays part of the **assembly**: `rigidShapeUniqNS_of_family`'s `htr`
   (`ProofTransport`) is supplied from `ConvStep2 ∧ PiInv` (`InjChainStep.convPiInv_of_convStep2`
   + `InjSpineTransport.proofTransportSpine_of`), so `PiInv` is upstream of the glue as well as of
   its own row.

Where the next round should go: **not** at rows 2/4/5 — their `Ordered`-level failure is now fully
understood and their positive content is `ShapeLinkAgree`/`ConvStep2`, already priced in
`InjOneFact.lean` and `RigidConstPrice.lean`.  Row 1, and specifically the *only* thing that would
turn row 1's conditional bound into a real measurement: a ¬conversion technique that survives
`IsDefEqStrong.beta` at an unbounded index.  That is the same missing primitive `InjPiRogue`
names, and this census is now the third file to arrive at it from a different direction.

### V7 (2026-09-05) — scorecard on §1's cold predictions

| pred | verdict |
|---|---|
| **P1** (3 members) | **WRONG** — 5.  The `:208` prose that misled me is itself wrong (V1). |
| **P2** (≥2 refutable from `Ordered`; `app`/`app` too; "one problem not five") | **MOSTLY RIGHT** — 3 outright + 1 modulo `¬IsProof`.  "app/app too" right only for the `¬IsProof`-free form.  "one problem" too coarse: it is two. |
| **P3** (PiInv load-bearing; cross-shape members provable from `WF` by a type-level argument) | **SPLIT** — first half **confirmed** (V6); second half **FALSE and already refuted in-tree** (V3). |
| **P4** (not independent; exactly one at the bottom) | **RIGHT, WRONG ORIENTATION** — one at the bottom, but it is member 2 as the *antecedent* of row 1's bound, not the positive members below the negative ones. |
| **P5** (`Ordered` + `RuleShape.delta` + `DefEqHeadsUnique` suffices for the cross-shape members) | **UNSUPPORTED, and one clause too many** — no sufficiency was measured for any row (V5); the *separation* needs `RuleShape.delta` only. |
| **P6** (table completes; ≤1 new proof; 1 row unknown; one-sided bounds; hole not closed) | **RIGHT** — 0 new proofs of members, 4 rows witnessed, 1 row conditional-only, all bounds one-sided, hole untouched (census still 13). |

Build state at close: bare `lake build` green, **1672 jobs** (baseline 1670 + this module),
guard 1 ✓ (24 frozen axioms), guard 2 ✓ (`INCOMPLETE: sorryAx present`, unchanged), guard 3 ✓
(2/2), hole census **13** (unchanged).  `InjCensus.lean` warnings: none.  `InjCensus` is listed by
`scripts/sorry-census-all.lean` among modules a fixed-import census cannot reach — exactly as
`InjMethod` is, which is the precedent for a witness-only module.

### V8 (2026-09-05) — names as `scripts/exists.lean` prints them (arity + cone), and one arity correction

Population: 486 built modules.  Every row: *own value is a hole: false; cone reaches sorryAx: false*.

| name | module | arity | cone |
|---|---|---|---|
| `Lean4Lean.VEnv.InjCensus.not_rigidSortPiDisj` | `Theory.Typing.InjCensus` | 0 | 789 |
| `Lean4Lean.VEnv.InjCensus.not_rigidConstPiDisj` | ″ | 0 | 804 |
| `Lean4Lean.VEnv.InjCensus.not_rigidConstSortDisj` | ″ | 0 | 804 |
| `Lean4Lean.VEnv.InjCensus.not_rigidConstAppInvNP` | ″ | 0 | 832 |
| `Lean4Lean.VEnv.InjCensus.not_rigidConstAppInv_of_not_isProof` | ″ | 1 | 833 |
| `Lean4Lean.VEnv.InjCensus.not_piInv_of_rigidSortPiDisj` | ″ | 1 | 810 |
| `Lean4Lean.VEnv.InjCensus.ordered_not_enough_for_piInv` | ″ | 1 | 1680 |
| `Lean4Lean.VEnv.InjCensus.not_wf_censusEnv` | ″ | 0 | 5015 |
| `Lean4Lean.VEnv.rigidShapeUniqNS_iff_family` | `Theory.Typing.RigidNodeCircle` | **5** | 3500 |

**Correction to V1** (which is left as written, per the append-only rule): I recorded
`rigidShapeUniqNS_iff_family`'s arity as "(explicit) 3".  `exists.lean` reports **5** — the two
section binders `{env} {U}` are counted and are invisible in the statement, which is precisely the
defect method rule 4 warns about.  V1's *content* (three explicit hypotheses `henv`/`hsu`/`htr`) is
unchanged; the number 3 was mine, not the environment's.

## §3 — Gaps in my own method

1. **No sufficiency was measured for any row.**  The census is one-sided by construction (V5), and
   I did not find a way to make it two-sided that was not "prove the hole".
2. **Rows 2/4/5 are shown non-independent only in the sense of sharing a witness.**  I did *not*
   show that no `Ordered` witness separates them, and I cannot: separating them would need a
   ¬conversion fact at a sub-environment, the same missing primitive as row 1.  So "one problem for
   four members" is a statement about the *witness and clause*, not a proof of equivalence.
3. **Row 3's `¬ IsProof` residue is believed true and unproved.**  If it were *false* at
   `censusEnv` — i.e. if some `Ordered` environment can make a `Sort 1`-typed constant a proof —
   then row 3's `Ordered`-insufficiency is unmeasured too, and the census's "4 of 5" becomes
   "3 of 5".  I could not settle it either way, and it should not be quoted as settled.
4. **The two-versus-five headline is on the environment axis only.**  Over the `VEnv.WF` base the
   existing prices (`RigidConstPrice.constFamily_iff_rigidShapeUniqNS`,
   `SortPiDisjPrice.sortPiDisjUC_iff_rigidShapeUniqNS`) already make every subfamily equivalent to
   the whole, i.e. **one** problem on that axis.  The two axes disagree, and neither supersedes the
   other; a brief that quotes one must name which.
