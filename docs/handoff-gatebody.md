# Handoff: `docs/handoff-pidescend.md` §3.3's gate-body edit — **refuted as stated**, and the half of it that is now landed

Stream: `GateBody`.  Owned files: `Theory/Typing/UniqueTyping.lean`, `Theory/Typing/Strengthen.lean`,
new `Theory/Typing/GateBody*.lean`, this document.

---

## 0. Verdict, up front

**§3.3's edit cannot be applied, and the reason is not the one §3.3 anticipated.**  §3.3 named
import order as the only obstruction and measured it false.  Import order *was* false, and it is
now removed for good.  The real obstruction is one §3.3 states in its own step 3 but the brief I
was handed dropped: **`VEnv.TypingStrengthening` has no unconditional inhabitant.**  Every
producer of it in the built environment takes either an open statement or the hole itself as a
hypothesis (§2, measured).  So the gate bodies cannot route through it today; routing them
through a fresh `sorry` would move the hole, not remove it, and would leave the same 319
declarations tainted.

**Three further claims in the brief I was handed do not reproduce.**  Named in §5; the important
one is that the replacements are **not** all hole-free.  Only the `IsType`/`OnCtx`/`VExpr.WF`
gates are; the three `HasType`-shaped gates — including `HasType.weakN_iff`, which is the
projection corner's *principal* route — have no known hole-free proof from
`TypingStrengthening`, and the one that exists trades this hole for `WF.rigidShapeUniqNS`, which
for 26 of the corner's 31 seeds is a **new** hole (§3, measured).

**What is landed** (all hole-free, `#print axioms` in §4):

1. **Blocker 1 removed, permanently.**  `TypingStrengthening`, `SortDescend`, `PiDescend`,
   `TypingStrengthening.of` / `.sortDescend` / `.piDescend`, `Lookup.weakN_inv` and the six
   `VExpr.liftN_eq_*` inversions moved out of `Strengthen.lean` (which imports
   `UniqueTyping.lean`) into the new `Theory/Typing/GateBodyDescend.lean`, whose 38-module import
   closure is a strict subset of `UniqueTyping.lean`'s 43.  `UniqueTyping.lean` now imports it.
   **Zero names changed, zero call sites changed** (measured: full build green, §4).
2. **Six of the fourteen gate bodies written and machine-checked**, hole-free, in
   `GateBodyDescend.lean` §2 — the statements are *verbatim* the gate's plus one hypothesis `HT`.
   Before this round only two of the six existed anywhere (`WeakNProjGate.onCtx_inv'`,
   `.isType_weakN_iff'`); the four `weak'`/`VExpr.WF` ones are new.
3. **The drop-in property is checked inside `UniqueTyping.lean` itself**, as six `example`s whose
   type is the gate's statement plus `HT` and whose proof is the proposed replacement.  §3.3's
   step 2 was marked `[read]`; it is now `[measured]` for those six, at the position that matters.
4. **Anti-vacuity discharged**: `GateBodyWitness.exists_env_gates_unconditional` — a concrete
   `VEnv.WF` environment at which all six fire with no hypotheses left (with the inconsistency
   caveat carried, §6).

**What is not landed**: no gate body was replaced, because none can be today.  The hole count is
**13 before and 13 after** (§4).

---

## 1. The global and corner measurements, reproduced and corrected

Instrument: `/tmp/gatebody/scan.lean` and `/tmp/gatebody/scan2.lean`, reproduced in §7, with the
two disclosures `docs/vacuity-ledger.md` row 180d demands plus a positive control on the hole.
Import closure: `Verify.Guard`, `Experimental.ConeJoin`, `Theory.Typing.StrengthenNarrow`,
`Theory.Typing.PiDescendSplit`, `Theory.Typing.GateBodyWitness`, `Verify.Typing.ProjGenTerm`,
`Verify.TypeChecker.ProjGenTermWitness`, `Verify.Typing.ProjWeakInvSplit`.

### 1.1 Global reverse reachability from the hole [measured]

```
hole Lean4Lean.VEnv.IsDefEqU.weakN_iff
  transitive users, non-internal, hole included in the count : 319
  with the 9 in-file TYPING gates cut                        : 264   freed 55
  with those 9 + hasType_app_bvar0 cut                       : 261   freed 58
  with ALL 14 post-hole UniqueTyping declarations cut         : 248   freed 71
```

**The brief said 312 reverse-dependents and "frees 59 users globally".**  Measured: **318**
reverse-dependents (319 including the hole), and cutting the nine typing gates *this file
defines* frees **55**, not 59.  58 requires also cutting `hasType_app_bvar0`, which lives in
`ChurchRosser.lean` and is therefore not part of §3.3's edit at all.  I could not reproduce 59 by
any subset of the fourteen; the closest are 55 (9 gates), 58 (9 + `hasType_app_bvar0`) and 71
(all 14).  The gap is small and probably a commit drift — the corner numbers below reproduce
exactly — but the figure to quote for §3.3's edit is **55**.

### 1.2 The projection corner [measured]

Seeds: the 31 names `docs/handoff-pidescend.md` §8.3 lists.  All 31 resolve; none was silently
zero.

```
CORNER (31 seeds)
  reach IsDefEqU.weakN_iff                        : 31
  still reach it, the 9 typing gates cut          :  3   freed 28
  still reach it, all 14 cut                      :  0   freed 31
  reach IsDefEqU.forallE_inv_stratified           : 31
  reach WF.rigidShapeUniqNS                       :  5
```

**"28 of the corner's 31" reproduces exactly**, and the three that survive are exactly the
`constRigid` line §3.3 names: `constAppDefeqStrengthenRF_of_constRigid`,
`constAppDefeqStrengthenInh_of_constRigid`, `TrProj.weak'_inv_of_constRigid`.

**But the count is not what it sounds like, and the brief told me to say so plainly.**  All 31
corner seeds also reach `VEnv.IsDefEqU.forallE_inv_stratified`, a *different* standing hole that
this edit does not touch.  So "28 of 31 freed" means **freed of one of their two holes**.  After
the (hypothetical, post-`PiDescend`) edit, 28 corner declarations would still carry `sorryAx`,
through `forallE_inv_stratified`.  Zero corner declarations become sorry-free by this edit, now or
later.

---

## 2. Why the edit cannot be made: `TypingStrengthening` has no unconditional inhabitant [measured]

This is the decisive measurement, and it is a structural query over the compiled environment, not
a grep.  I walked every non-internal `Lean4Lean` constant, stripped its binders, and reported
every declaration whose **conclusion** is `TypingStrengthening _ _`, `PiDescend _ _`,
`SortDescend _ _`, `Strengthening _ _` or `StrengtheningTarget _ _`: **27 declarations**.  Their
full types are in `/tmp/gatebody/ts2-out.txt`.  Every one of them takes at least one hypothesis
beyond `VEnv.WF`, and that hypothesis is in every case one of

* another open shape-descent statement (`SortDescend`, `PiDescend`, `Strengthening`,
  `TypingStrengthening1`, `TransStrengthening`, `TransStrengtheningNarrow`, …);
* an **inhabitedness** assumption on the environment or its contexts
  (`typingStrengthening_of_allInhabited`, `strengtheningTarget_of_allClosedInhabited`,
  `AllTypesInhabited.strengtheningTarget`, `AxiomConservativity*.target`) — `Strengthen.lean` §1's
  proved route, which by construction says nothing about uninhabited entries, i.e. about the only
  case that is open;
* a **specific** environment (`strengtheningTarget_of_univInhab`, which requires
  `env.constants \`univInhab = some …`);
* or the hole itself: `VEnv.typingStrengthening_of_weakN_iff` (`CRPiDescend.lean:351`) has type
  `∀ [Params], Params.env.TypingStrengthening Params.univs` — no explicit hypothesis, and its cone
  contains `IsDefEqU.weakN_iff`.  That is the circle §3.2 of the previous handoff already names.

So the two ways to write §3.3's edit today are:

* **add `(HT : TypingStrengthening env U)` to the nine gates.**  That changes their *statements*,
  so it is not a body replacement: all 318 users must supply or acquire `HT`.  This is the same
  flag day §3.2 priced at 189 for sites 2–4, only larger.  "**Touches zero call sites**" is true
  only of the version that keeps the statements, and that version needs an unconditional `HT`.
* **`sorry` `TypingStrengthening` inside `UniqueTyping.lean`** and route the gates through it.
  The nine gates then reach the new `sorry` instead of the old one; the 55 "freed" users are freed
  of `weakN_iff` and immediately tainted by the replacement, the union of tainted declarations is
  unchanged, and `scripts/sorry-census-all.lean` goes 13 → 14.  This is exactly the relabelling
  that `docs/vacuity-ledger.md` §0 (third row: "a cone walks `deps`, and a hypothesis is not a
  dependency") exists to catch.

`docs/handoff-pidescend.md` itself is right about this — §6 item 3 says "do it only once
`PiDescend` is a theorem".  **The brief I was handed dropped that condition** and presented the
edit as available now because "the replacements exist and are hole-free".  The replacements do
exist and three of them are hole-free; they are *conditional*, and the condition is the open
statement.

---

## 3. The per-gate table: which of the fourteen have a replacement, and at what price [measured]

`UniqueTyping.lean` states **fourteen** declarations after the hole, not ten.  §3.3 says "ten
typing gates … **defined** at `UniqueTyping.lean:200–260`"; both halves of that are off.  The
fourteen are at `:196, 199, 209, 217, 230, 235, 240, 245, 250, 263, 276, 281, 286, 290` (line
numbers after this round's one added import); lines 200–260 contain seven of them.  And the ten
names §3.3 lists are **not** the ten `typingGates` of `scripts/weakn-gate-split.lean`: §3.3's list
includes `IsDefEq.skips`, `IsDefEq.weakN_iff'` and `IsDefEq.weakN_iff`, which that script
deliberately classifies as *conversion* gates because their two endpoints differ.  The script's
tenth gate, `hasType_app_bvar0`, is in `ChurchRosser.lean`, not here.

Hole sets below are cones of the compiled declarations, holes = the four standing `Theory`-side
ones (`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
`NormalEq.descend`).

| # | gate (`UniqueTyping.lean`) | replacement from `TypingStrengthening` | its hole set |
|---|---|---|---|
| 1 | `VExpr.WF.weakN_iff` `:196` | **`GateBody.wf_weakN_iff`** (new) | **{} hole-free** |
| 2 | `OnCtx.weakN_inv` `:217` | **`GateBody.onCtx_weakN_inv`** (= `WeakNProjGate.onCtx_inv'`) | **{}** |
| 3 | `IsType.weakN_iff` `:240` | **`GateBody.isType_weakN_iff`** (= `.isType_weakN_iff'`) | **{}** |
| 4 | `OnCtx.weak'_inv` `:290` | **`GateBody.onCtx_weak'_inv`** (new) | **{}** |
| 5 | `IsType.weak'_iff` `:281` | **`GateBody.isType_weak'_iff`** (new) | **{}** |
| 6 | `VExpr.WF.weak'_iff` `:286` | **`GateBody.wf_weak'_iff`** (new) | **{}** |
| 7 | `HasType.weakN_iff` `:235` | `StrengthenNarrow.TypingStrengthening.hasType_weakN_iff` | `{forallE_inv_stratified, rigidShapeUniqNS}` |
| 8 | `HasType.weak'_iff` `:276` | `…hasType_weak'_iff` | `{forallE_inv_stratified, rigidShapeUniqNS}` |
| 9 | `HasType.skips` `:245` | `…hasType_skips` | `{forallE_inv_stratified, rigidShapeUniqNS}` |
| 10 | `IsDefEq.skips` `:199` | **none** — two distinct endpoints | — |
| 11 | `IsDefEq.weakN_iff'` `:209` | **none** | — |
| 12 | `IsDefEq.weakN_iff` `:230` | **none** | — |
| 13 | `IsDefEqU.weak'_iff` `:250` | **none** | — |
| 14 | `IsDefEq.weak'_iff` `:263` | **none** | — |

Rows 1–6 are the six this round wrote and machine-checked (`GateBodyDescend.lean` §2).  Before
this round the tree contained only rows 2 and 3 hole-free (`WeakNProjGate.lean` §1's
`onCtx_inv'` / `isType_inv'` / `isType_weakN_iff'`, which are three lemmas covering two gates);
rows 1, 4, 5, 6 are new, and the existing `StrengthenNarrow.lean` §5 versions of rows 4–6
(`onCtx_weak'_inv`, `isType_weak'_iff`, `wf_weak'_iff`, `wf_inv`) all route through
`TypingStrengthening.typed` and therefore carry both extra holes — measured, all ten of
`StrengthenNarrow.lean` §5's gate re-proofs have hole set
`{forallE_inv_stratified, rigidShapeUniqNS}`.

### 3.1 Where the brief is most wrong: the corner's principal gate is row 7

The brief says the replacement route is hole-free "so they route through `SortDescend` rather than
`TypingStrengthening.typed`, where `IsDefEqU.forallE_inv` and hence the hole enters".  That is
true of rows 1–6 and **false of rows 7–9**, and rows 7–9 are the ones the projection corner runs
on: `Verify/Typing/ProjSkip.lean`'s `VEnv.HasType.swapSkipped` is literally
`((HasType.weakN_iff henv hΓ W).1 H).weakN henv.ordered W'`.

`SortDescend` produces *a* sort downstairs, which is all `IsType` (level existential), `OnCtx`
(a conjunction of `IsType`s) and `VExpr.WF` (type existential) ever need.  Row 7 needs the
**given** type `A` downstairs; recovering it is `TypingStrengthening.typed`'s ascription-redex
trick, which consumes `IsDefEqU.forallE_inv` and so `WF.rigidShapeUniqNS`.
`WeakNProjGate.lean` §2's `hasType_sort_inv` avoids `rigidShapeUniqNS` — measured hole set
`{forallE_inv_stratified}` only — but *only for sort-typed judgements*, which is not general
enough to be row 7's body.

**Consequence, measured, and this is the number that matters:** cut *only* the six hole-free-
replaceable gates (rows 1–6) and the hole loses **4** of its 319 users globally and **2** of the
corner's 31:

```
GLOBAL, non-internal transitive users of IsDefEqU.weakN_iff (hole included in the count)
  none cut                                    : 319
  (a) the 6 hole-free-replaceable gates cut   : 315   freed  4
  (a)+(b) the 9 in-file typing gates cut      : 264   freed 55
  (a)+(b)+hasType_app_bvar0 cut               : 261   freed 58
  all 14 post-hole declarations cut           : 248   freed 71

CORNER (31 seeds)
  none cut                                    : 31
  (a) cut                                     : 29   freed  2   (OnCtx.swapCtx,
                                                                 TrProj.weak'_inv_of_strengthen)
  (a)+(b) cut                                 :  3   freed 28
```

So **the 55/28 belongs almost entirely to rows 7–9**, whose only known replacement carries
`WF.rigidShapeUniqNS`.  5 of the corner's 31 seeds reach `rigidShapeUniqNS` today; replacing row 7
via `hasType_weakN_iff` would give it to the other 26.  The honest statement of §3.3's edit, even
after `PiDescend` lands, is therefore:

> Rows 1–6: **4 users globally, 2 in the corner, at no cost.**  Rows 7–9: the remaining 51
> globally / 26 in the corner, **by exchanging `weakN_iff` for `rigidShapeUniqNS`** — a hole those
> 26 do not currently carry.

`WeakNProjGate.lean`'s own module docstring makes exactly this point about `StrengthenNarrow.lean`
§5 ("substituting them into the corner would trade the hole `weakN_iff` for the hole
`rigidShapeUniqNS`"); §3.3 does not carry the warning forward, and the brief I was handed inverted
it into "the replacements … are hole-free".

---

## 4. What landed, and the verification

### 4.1 The import move — §3.3 step 1, executed [measured]

Moved out of `Theory/Typing/Strengthen.lean` into the new
`Theory/Typing/GateBodyDescend.lean`, verbatim, with no name changes:

* `VEnv.TypingStrengthening` (was `Strengthen.lean` §2);
* `VExpr.liftVar_eq_zero`, `VExpr.liftN_eq_{bvar,sort,const,app,lam,forallE}` (was its §4);
* `VEnv.SortDescend`, `VEnv.PiDescend`, `Lookup.weakN_inv`, `VEnv.TypingStrengthening.of`,
  `.sortDescend`, `.piDescend` (was its §7).

The move set was chosen by measurement, not by reading: the joint cone of the three statements and
the three theorems contains exactly **18** constants declared in `Strengthen.lean`, and they are
the ones above plus four `match_1_*`/`_proof_*` companions of `of` and `sortDescend`, which move
with their parents.  `Strengthen.lean` now `import`s the new module and keeps everything else
(`Strengthening`, `TransStrengthening`, `.typed`, `.of_typing`, `iff_descend`,
`PiDescend.sortDescend`, `iff_piDescend`, the whole of §§1, 3, 5, 6, 8–13) unchanged.

* `GateBodyDescend.lean` import closure: **38** modules; `UniqueTyping.lean`'s: **43**.
  `GateBodyDescend`'s closure minus `UniqueTyping`'s is exactly `{GateBodyDescend}` — a strict
  subset, so no cycle [measured, by walking the `import` headers of all 393 modules on disk].
* `UniqueTyping.lean` now imports it, and builds.  `PiDescend.sortDescend` was **not** moved: its
  cone contains `UniqueTyping` constants, so it cannot go above it — §3.3 did not list it, which
  is correct.
* `TypingStrengthening.of` / `.sortDescend` / `.piDescend` cone-module counts: **18 / 17 / 18**,
  with `Strengthen.lean` the only illegal module.  This reproduces §3.3's "18, 17, 18" exactly.

### 4.2 The six gate bodies — §3.3 step 2, `[read]` → `[measured]` for six of fourteen

`GateBodyDescend.lean` §2, namespace `Lean4Lean.VEnv.GateBody` (names read off the file's own
`namespace` lines and confirmed by `#print axioms`, not composed from the path):

```
'Lean4Lean.VEnv.GateBody.onCtx_of_appendL' does not depend on any axioms
'Lean4Lean.VEnv.GateBody.onCtx_isType_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.onCtx_weakN_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.isType_weakN_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.wf_weakN_iff'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.onCtx_weak'_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.isType_weak'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.GateBody.wf_weak'_iff'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.TypingStrengthening.of'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.TypingStrengthening.sortDescend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.VEnv.TypingStrengthening.piDescend'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Lean4Lean.Lookup.weakN_inv'              depends on axioms: [propext, Quot.sound]
```

No `sorryAx` anywhere in that list.  **Before** the move the same declarations had the same axiom
sets (`TypingStrengthening.of` etc. were already hole-free in `Strengthen.lean`); the move changed
nothing about them, which is the point.

All fourteen gates were `#print axioms`-checked **before and after** this round; all fourteen read
`[propext, sorryAx, Classical.choice, Quot.sound]` in both, unchanged — as they must, since no body
was replaced.  (This is the "before and after" the brief asked for; the answer is "identical", and
that is the honest report.)

`UniqueTyping.lean` ends with six `example`s, each stating a gate's statement verbatim plus
`(HT : TypingStrengthening env U)` and proving it by the corresponding `GateBody` lemma.  They
elaborate.  That is the drop-in property, checked at the position where the edit will happen; it
was §3.3 step 2's `[read]` mark.  `example`s introduce no names and no axiom obligations.

### 4.3 Anti-vacuity

`Theory/Typing/GateBodyWitness.lean`:
`Lean4Lean.VEnv.GateBody.exists_env_gates_unconditional : ∃ env, VEnv.WF env ∧ ∀ U, (all six
gates hold, quantified over lifts, contexts and subject)` — `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`.  Built on `WeakNProjGate.exists_typingStrengthening_env`, which the
brief flagged as available and which is indeed hole-free.

**Carry the scope statement with it.**  The witness environment declares
`univInhab : ∀ (α : Sort u), α` and is therefore inconsistent; `univInhab_no_uninhabited_entry`
says its contexts have no uninhabited entry, which is precisely the case `Strengthen.lean` §1
already settles.  So this is a *satisfiability* witness — the hypothesis is not contradictory —
and it is **not** evidence that the hypothesis is easy or that the conclusions have content there.
The file says so in its docstring.

---

## 5. Where the brief and its input are wrong

Everything relayed to me was flagged as unverified, and it needed to be.  In descending order of
consequence:

1. **"The replacements exist and are hole-free: `WeakNProjGate`'s `onCtx_inv'` / `isType_inv'` /
   `isType_weakN_iff'`" placed in the same sentence as "frees 59 users globally, 28 of the
   corner's 31".**  Those three lemmas are hole-free, and they cover two of the fourteen gates.
   Together with the four I added this round they free **4 globally and 2 in the corner**.  The
   55/28 needs the three `HasType` gates, whose replacements carry two other holes.  This is ledger
   row 180's juxtaposition error again — an unconditional win (hole-free, 4 users) reported beside
   a conditional total (55 users, needs a hole trade) so that the total reads as delivered by the
   win.  §3.4 of the previous handoff flagged that exact failure mode; the brief reproduced it.
2. **"Frees 59 users globally."**  Measured **55** for the nine gates this file defines, 58 if you
   also cut `hasType_app_bvar0` (which is in `ChurchRosser.lean` and not part of the edit), 71 for
   all fourteen.  I could not produce 59 from any subset.
3. **"312 reverse-dependents."**  Measured **318** (319 with the hole itself).
4. **"Ten typing gates … defined at `UniqueTyping.lean:200–260`."**  There are **fourteen**
   post-hole declarations; lines 200–260 hold seven of them; and the ten names §3.3 lists are not
   the ten `typingGates` of `scripts/weakn-gate-split.lean` — §3.3's list contains three
   *conversion* gates (`IsDefEq.skips`, `IsDefEq.weakN_iff'`, `IsDefEq.weakN_iff`) and omits
   `hasType_app_bvar0`, `OnCtx.weak'_inv`, `HasType.weak'_iff`, `IsType.weak'_iff`,
   `VExpr.WF.weak'_iff`.  A stream told to "replace the ten gate bodies" would have replaced three
   that cannot be replaced.
5. **"Replacing the gate bodies … touches zero call sites and frees 59 users."**  The two halves
   are not simultaneously satisfiable today: zero call sites requires the statements to stay
   unconditional, which requires an unconditional `TypingStrengthening`, which is the open
   statement (§2).  §3.3's own step 3 and §6 item 3 carry that condition; the brief dropped it.
6. **The brief's framing "one of 13 standing holes … 312 reverse-dependents" invites reading the
   edit as progress on the hole count.**  It is not, and cannot be: the edit removes no `sorry`.
   `scripts/sorry-census-all.lean` reads **13 before and 13 after** this round.
7. **§3.3's import-order measurement is correct** — this is the one claim that reproduced exactly
   (43-module closure; 18/17/18 cone modules; `Strengthen.lean` the only illegal one), and it is
   now executed rather than available.

### 5.1 A repo-level hazard, not a document error, found twice this round

`lake build` reported **green** while `Lean4Lean/Verify/Environment/Boundaries.olean` was **absent**
from `.lake/build` — Lake's `.trace`/`.hash` for that module were present and current, so it was
never rebuilt, and `Verify/Environment/Checker.lean`, which imports it, was replayed from cache.
`scripts/sorry-census-all.lean` caught it (it is the only instrument that enumerates the
default-target population from disk) and then *crashed* on the missing `.olean`, which is how I
found it.  I repaired it by deleting that module's `.trace`/`.olean.hash`/`.ilean.hash` and
rebuilding the single module; nothing in the repo changed.

A second instance appeared at the end of the round for a different reason:
`Lean4Lean.Theory.Inductive.RecArgIndep` is on disk and in a default target but has no `.olean`,
because a concurrent stream created it after my `lake build` started.  That one is not mine and not
a defect.

**The lesson for the orchestrator**: "full `lake build` green" is not by itself evidence that every
module in the tree was built, and a stale-`.olean` probe is not the only failure mode — a *missing*
one also passes.  Run `scripts/sorry-census-all.lean` and read its `NOT BUILT` line, which is why
that line exists.

---

## 6. Verification

* **`lake build`: green, 1554 jobs [measured]** (`/tmp/gatebody/build-full.log`; 0 lines matching
  `error`).  Baseline at the start of the round was green at 1549 jobs; the delta is my three new
  modules plus two created by concurrent streams.
* **Guards, verbatim [measured]:**
  ```
  guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
  guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
  guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
  ```
* **`scripts/sorry-census-all.lean`: 13 before, 13 after [measured]**, same thirteen names.  Run at
  the start of the round (after repairing the missing `.olean`, §5.1) and at the end.
* **`scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone"**
  [measured].
* **Layering**: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty** [measured].
* **Frozen files**: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are not in
  `git status` and not in `git diff`; they were not read-modified, not `touch`ed, and this document
  requests no edit to them.
* **Files changed / added**:
  * `Lean4Lean/Theory/Typing/GateBodyDescend.lean` (new, 301 lines) — the move plus §2's six gate
    bodies;
  * `Lean4Lean/Theory/Typing/GateBodyWitness.lean` (new) — anti-vacuity;
  * `Lean4Lean/Theory/Typing/Strengthen.lean` — the moved declarations deleted, one import added,
    three pointer comments left where they were (133 lines touched, net −120);
  * `Lean4Lean/Theory/Typing/UniqueTyping.lean` — one import added, plus a documentation block and
    six `example`s at the end (+76);
  * `docs/handoff-gatebody.md` (this file).
  Nothing else.  I did not touch `WeakNProjGate.lean`, `Descend*`, `FieldsNoK*`, `RecArgIndep*` or
  `PiDescendFst*`.
* **Probe hygiene**: every `#print axioms` and every scan in this document was run *after* the
  module it probes had been rebuilt; `scan2.lean` was run against the post-move tree and reproduces
  the pre-move global count of 319 exactly, which is the control for "the move changed no name".

---

## 7. The instrument

`/tmp/gatebody/{scan,scan2,ts,ts2,cones,cones2,movelist,ax,ax2}.lean` and
`/tmp/gatebody/imports.py`.  All Lean walkers share this core, with the two disclosures
`docs/vacuity-ledger.md` row 180d requires:

```lean
-- INSTRUMENT DISCLOSURES:
--  * VALUES ARE READ: `.thmInfo` constants via `v.value`; everything else via
--    `ci.value? (allowOpaque := true)`.  Types are always read.
--  * INTERNAL NAMES ARE KEPT as graph nodes and are never skipped while traversing; they are
--    filtered only when a count or a seed list is reported.
private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs
```

Positive controls: the hole must be found by `env.find?` **and** must appear in its own reach set;
every seed and gate name is `env.find?`-checked and an unresolved one is `logError`, never a silent
zero.  All 31 corner seeds, all 14 gates and `hasType_app_bvar0` resolved.

§2's query is deliberately **structural, not textual**: it strips the binders of every non-internal
`Lean4Lean` constant and matches the head of the conclusion against
`{TypingStrengthening, PiDescend, SortDescend, Strengthening, StrengtheningTarget}`, then prints the
whole type.  A grep for "unconditional `TypingStrengthening`" would have found nothing and proved
nothing; this enumerates the 27 producers and shows what each needs.

The import graph in §4.1 is computed from the `import` headers of all modules on disk
(`/tmp/gatebody/imports.py`), not from the loaded environment, so that a module that fails to build
still appears.

---

## 8. What to pick up first

1. **`PiDescendFst` is still the whole residual** — `docs/handoff-pidescend.md` §2.1 and §6 items
   1–2 are unaffected by anything here, and its `.const` case is still the sharpest untouched
   target.  Nothing in this round is a substitute for that; §3.3's edit is downstream of it.
2. **When `PiDescend` lands, the edit is now six one-line body swaps**, listed in the table in §3
   with the `GateBody` lemma name for each, and machine-checked as `example`s at the bottom of
   `UniqueTyping.lean`.  Expect **4 users globally / 2 in the corner** from those six, and price
   rows 7–9 separately (§3.1) rather than as part of the same total.
3. **Rows 7–9 need a hole-free `HasType` descent, and that is a real open question**, not a
   transcription.  The concrete shape: `TypingStrengthening.typed` recovers the *given* type by the
   ascription redex `(fun _ : A => #0) e` and then needs `IsDefEqU.forallE_inv` to read the domain
   off the lambda's type — that is where `rigidShapeUniqNS` enters.  `WeakNProjGate.lean` §2 shows
   the sort-typed case escapes with only `forallE_inv_stratified`.  **The open question is whether
   the general case can be got from `SortDescend` plus `PiDescend` directly** (both of which are
   `TypingStrengthening`'s own equivalents) without the redex.  If it can, §3.3's edit becomes what
   the brief claimed it already was.  I did not attempt it.
4. **Do not** re-attempt: adding `(HT : …)` to the gates (§2, second bullet: it is the 318-call-site
   flag day); `sorry`ing `TypingStrengthening` in `UniqueTyping.lean` (§2, third bullet: pure
   relabelling, census 13 → 14); replacing rows 10–14 from `TypingStrengthening` (their endpoints
   differ — they are not instances of it); moving `PiDescend.sortDescend` above `UniqueTyping.lean`
   (its cone contains `UniqueTyping` constants).
5. **Dedup opportunity for whoever owns `WeakNProjGate.lean`**: its §1 (`onCtx_of_appendL`,
   `onCtx_isType_inv`, `onCtx_inv'`, `isType_inv'`, `isType_weakN_iff'`) is now duplicated, by
   necessity, as `GateBodyDescend.lean` §2's `onCtx_of_appendL` / `onCtx_isType_inv` /
   `onCtx_weakN_inv` / `isType_weakN_iff`.  `WeakNProjGate.lean` is downstream of
   `GateBodyDescend.lean`, so it can delete its copies and re-export.  I did not do this because
   that file is not mine.

---

## 9. Verdict

* **Outcome 1 (gate bodies replaced): not achieved, and not achievable.**  Blocked on
  `TypingStrengthening` having no unconditional inhabitant (§2, measured over the compiled
  environment).
* **Outcome 2 (some gates replaced, the rest with the obstruction named per gate): the per-gate
  table is in §3**, but *zero* gates could be replaced, for the single reason in §2, which is
  common to all fourteen rather than per-gate.
* **Outcome 3 (a measurement showing §3.3's edit is wrong, or its numbers don't reproduce):
  achieved, on both counts.**  The edit is not applicable today (§2); of its numbers, the corner's
  28/31 reproduces exactly, "59 globally" does not (55), "312 reverse-dependents" does not (318),
  "ten gates at `:200–260`" does not (fourteen, and a different ten), and the crucial one — that
  the replacements are hole-free — is true of only 4 users globally and 2 in the corner (§3.1).
* **Landed anyway, all hole-free and full-tree green**: the import move (§3.3 step 1, executed),
  four new gate bodies that did not exist in the tree, the six-way drop-in check inside
  `UniqueTyping.lean` (§3.3 step 2, `[read]` → `[measured]`), and the anti-vacuity witness.
* **The corner's hole-reaching count, before and after this round: 31 and 31.**  Nothing was
  replaced, so nothing moved.  The 29 / 3 / 0 figures in §1.2 and §3.1 are *counterfactual* — what
  the counts would be if the named gates stopped propagating — not the state of the tree.
* **Hole count: 13 before, 13 after.**  No `sorry` was removed and none was added.
