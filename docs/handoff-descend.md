# Handoff: `NormalEq.descend` — round of 2026-09-03

> **Read this section first; everything below it is the 2026-08-31 round and is still
> accurate on its own subject.**  This round did **not** attempt to prove `descend`, because
> `descend` is already machine-checked **false** and had been for two rounds.  What it did was
> take the one link on `descend`'s critical-path chain that the K-repair had left **[analysis]**
> and machine-check it.  New file: `Lean4Lean/Theory/Typing/DescendConstSpineK.lean`
> (263 lines, no `sorry`, 80 jobs, `lake build` green).

Marks as in the old round: **[machine-checked]** = a named `sorry`-free Lean declaration;
**[measured]** = a run whose output is reproduced; **[read]** = read off source; **[analysis]**
= neither.

## 1. Verdict on the target: outcome 1 is not available, and outcome 4 was already taken

`Lean4Lean.VEnv.NormalEq.descend` (`Theory/Typing/ChurchRosser.lean:2011`, three `sorry`s at
`:2085/:2090/:2105`, all in the `.app`-node case) cannot be proved.  All three goals are
**false**, machine-checked in `Theory/Typing/DescendRefute.lean`
(`not_descendStatement`, `not_descendStatement_etaArg`, `not_descendStatement_etaFun`, and the
unconditional corollary `not_descendStatement_of_wf`).  The restatement exists
(`KDescend.lean`'s `descendV`), it is bounded both ways (`DescendRestate.lean`), the grading
route is closed (`DescendRestate.lean` §3), and the reduction-side repair is priced and
**cyclic** (`ParRedMissing.lean` §3).  Nothing in this corner is waiting for someone to try
harder.

So this round went after outcome 5.  **Its one new theorem is a necessary link on the only
live repair route, and it was the last of that route's three consumer ports still unproved.**

### What the brief relayed to me, corrected

| relayed | correction |
| --- | --- |
| "a `sorry` in `ChurchRosser.lean`" | **three**, all in the `.app`-node case, all with refuted goals **[read + machine-checked]** |
| "~200 reverse-dependents" | three figures live in the tree and I re-measured none: **193** (`sorry-census` at `f4b32ea`, quoted in `ChurchRosser.lean:1815`), **206 users / 196 sole** (`hole-rank`), **200** (`docs/critical-path.md`'s 2026-09-02 column).  Treat all three as inherited |
| "prove it, or refute it as stated" | refutation was landed on 2026-08-31; outcome 4 was not available |
| the midpoint warning (ledger rows 94/94a, 100–103) | **correctly relayed and it does not bind here.**  My route constrains no midpoint: `NormalEq` has no `trans` constructor (that is `handoff-descend.md` §1's own observation from the earlier round), and `ParRedK.constApp_inv` is an induction over a reduction relation, not a localisation of a conversion node.  I am not the next collapse, and I am saying why rather than only that |
| "compose two things already in the tree that nobody had composed" | **this was the productive move again.**  §2 |

## 2. What was proved: the third `ConstSpine` port

### 2.1 Why this link and not another

`docs/critical-path.md` records that `descend` is on `Bridge.kernel_sound_of`'s cone and enters
through **exactly one** chain **[read, that document's 2026-09-01 correction]**:

    addAxiom.WF ← … ← constApp_inv_of_patWF ← IsDefEq.constApp_inv ← IsDefEq.church_rosser
                ← CRDefEq.trans ← NormalEq.parRedS ← NormalEq.parRed
                ← appDF_extra_of_descend ← descend

The reduction lemma that chain rests on is `Verify/Typing/ConstSpine.lean`'s
`ParRedS.constApp_inv`: *a rule-free constant spine parallel-reduces only to constant spines
with the same head, levels and arity.*  It is an induction over `ParRed`'s **eight**
constructors.

The only live repair of the layer above it moves everything to **`ParRedK`** = `ParRed` + the
η-guarded K step `keta` (`KEta.lean`), because `ParRedPropRefute.lean`'s
`not_parRedStatement_of_propMajor` refutes `NormalEq.parRed`'s statement over plain `ParRed`.
`ParRedK` has a **ninth** constructor, and `ConstSpine.lean`'s induction acquires a ninth case.

`KEta.lean:441-447` states the situation exactly: `ConstSpine.lean` holds the only three
declarations outside the K stream that case on `ParRed`; **two** were ported there
(`ParRedK.forallE_inv`, `ParRedK.sort_inv`), and the third — `ParRed.constApp_inv`, *the one on
the critical-path chain* — was left, because `PatFreeHead` and `Pattern.headConst` are defined
in `Verify/`, which `Theory/` may not import.  `docs/handoff-krule.md` §T5 marks that edit
**[analysis]** and says so in its own evidence column.

### 2.2 The composition

Both halves were already in the tree and had never been put together:

* `KEta.lean`'s `EtaK.matches_head`, whose docstring says it is "the fact
  `Verify/Typing/ConstSpine.lean`'s `ParRed.constApp_inv` needs" — written **for** this use;
* `ConstSpine.lean`'s `ParRed.constApp_inv` proof.

**ABSENCE claim, made against the compiled environment, not the source text:** before this
round `EtaK.matches_head` had **zero** users.  Instrument: LSP `references` at its definition
site `Theory/Typing/KEta.lean:172`, over the whole indexed project — 3 hits, being the
declaration itself and this round's two uses. **[measured]**

### 2.3 The results

`Lean4Lean/Theory/Typing/DescendConstSpineK.lean`, all `sorry`-free, axioms `[propext,
Quot.sound]` **[measured, `#print axioms`, names read off the file's own `namespace` lines]**:

| name | content |
| --- | --- |
| `Lean4Lean.VEnv.EtaK.constApp_free` | **the ninth case.**  An `EtaK` step cannot fire at a rule-free constant spine |
| `Lean4Lean.VEnv.ParRedK.constApp_inv` | `ConstSpine.lean`'s `ParRed.constApp_inv`, ported constructor-for-constructor with the `keta` case added |
| `Lean4Lean.VEnv.ParRedKS.constApp_inv` | the reflexive-transitive form — the statement a `constApp_inv` over the K-route consumes, since `CRDefEq`'s K analogue concludes in `ParRedKS` (`KMeasure.lean:358`) |

The ninth case is discharged by the *same* hypothesis as the `extra` case, because
`patHeadConst (p₁.app p₂) = patHeadConst p₁` and `EtaK.matches_head` hands back a registered
`.app`-pattern whose function side matches at the same head constant.  Three lines, exactly as
§T5 predicted — the value is not the difficulty, it is that the prediction is now checked and
the layering excuse is gone.

### 2.4 Two claims this upgrades from [analysis] to [machine-checked]

1. `docs/handoff-krule.md` §T5's row for `ParRed.constApp_inv` — "the same three lines as the
   existing `extra` case", marked **[analysis]**.  It is right.
2. `docs/handoff-krule.md` §T1's design argument that `EtaK` **must** be guarded, because plain
   η-expansion "makes `ParRed.constApp_inv` false".  That was **[analysis]**; my proof consumes
   the guard (`EtaK.matches_head` exists only because `here` bottoms out in a `KStep`), so the
   guard is now known to be *sufficient* for this lemma, not merely believed necessary.

### 2.5 The layering blocker was a four-line `def`

`Pattern.headConst`, `Pattern.Matches.headConst`, `PatFreeHead`, `List.Forall₂.trans'`,
`List.forall₂_refl'` and the four `VExpr.constApp_ne_*` lemmas are all statements about
`Pattern` and `VExpr` alone — **no `Verify` dependency of any kind** **[read, definition sites
`Verify/Typing/ConstSpine.lean:98,104,156,166,180` and `:110-148`]**.  The right repair is to
move them into `Theory/`.  Until someone does, my file carries copies under distinct names
(`patHeadConst`, `matches_patHeadConst`, `PatFreeHeadK`, `constAppK_ne_*`,
`List.Forall₂.transK`, `List.forall₂_reflK`) so nothing clashes if a module later imports both.
`scripts/dup-names.lean`: **no duplicate `Lean4Lean` declarations across the joined cone**
**[measured]**.

## 3. Anti-vacuity

`PatFreeHeadK c` quantifies over the registered pattern table, so the degenerate way to satisfy
it is an **empty** table — which is what `refParams` (`refNoPat`) and `cycParams` (`cycNoPat`)
have.  A check only there would be a check about a relation that never moves.

The non-degenerate instance is `ParamsWitness.lean`'s `propLoopParams`: `VEnv.WF`, two
registered δ-patterns, and a `ParRed.extra` step that really fires.  All four results are at
that instance, all `sorry`-free (`[propext, Classical.choice, Quot.sound]`):

| name | role |
| --- | --- |
| `propLoop_patFreeHeadK` | `PatFreeHeadK c` holds for every `c ∉ {A, B}` — **inhabitation** |
| `propLoop_pat_nonempty` | the table it is satisfied against is **not empty** (`A` is a registered head) — so the inhabitation is not the degenerate one |
| `propLoop_not_patFreeHeadK` + `propLoop_constApp_inv_needs_hyp` | **negative control**: at the same instance the head that *does* front a rule has `ParRedK [] (.const A []) (.const B [])` while `B` is no `A`-headed spine, so dropping the hypothesis makes the conclusion false |
| `propLoop_no_etaK` | **the honest limit** — see below |

**The control is a control, per `ForallInvPrice`'s discipline.**  `ForallInvPrice`'s
`rogueSortPiEnv` needs `not_wf_sortPiEnv` beside it so the control is not mistaken for a
refutation of the target.  Here the analogous second half is the opposite fact and it is
already proved elsewhere: `propLoopEnv_wf : propLoopEnv.WF` **[machine-checked,
`ParamsWitness.lean`]**.  The control environment is *legitimate*; what fails there is
`PatFreeHeadK A`, not the theorem.  So the control bounds the hypothesis and refutes nothing.

### 3.1 The honest limit, stated as a theorem rather than a caveat

`propLoop_no_etaK : ¬ EtaK Γ e e'` at `propLoopParams`.  `EtaK` fires only where an `.app`
pattern is registered (`EtaK.matches_head`), and **every `Params` instance in `Theory/` has a
δ-only table** — `refNoPat`, `cycNoPat`, and `propLoopParams`' explicit table, whose `.app` and
`.var` rows are literally `False`.  So:

* `ParRedK.constApp_inv`'s **proof** is instance-independent and complete;
* its `keta` case's **content** is untested, because no Theory-side instance can reach it;
* the first instance that would test it is `Verify/QuotAppParams.lean`'s `quotParams` (ledger
  row 101), which `Theory/` may not import **[read]**.

That is a bounded gap and I am not dressing it up: what is machine-checked is that the head
condition *discharges* the ninth case, not that the ninth case ever arises at an instance this
layer can name.  Anyone who moves `PatFreeHead` down into `Theory/` gets the `quotParams`
check for free and should take it.

## 4. What this does and does not buy

**Does.**  The K-route is now known to be **compatible** with the consumer that puts `descend`
on the soundness cone.  Had the ninth case failed, the whole `KDescend`/`KSite7`/`KEta`/
`ParRedKGraded` programme would have been unable to reach `IsDefEq.constApp_inv` — i.e. unable
to serve the one chain that makes `descend` matter — and that would have been discovered only
after `church_rosser`-over-`ParRedK` was attempted.  The risk is retired, not assumed away.

**Does not.**  It delivers no confluence.  Still owed, unchanged by this round:

1. `ParRed.triangle`'s analogue over `ParRedK` (`ParRedCycle.lean`, `ParRedMissing.lean` §3);
2. `parRedKStatement_of_rows`, which costs `IsDefEqU.weakN_iff` (`DescendRestate.lean`'s cone
   table);
3. the two ambient injectivity holes, which every route here pays.

Hole count is **unchanged at 13** **[measured, `scripts/sorry-census-all.lean`: 391 files on
disk, 367 in the default-target population, 367 built, 0 unbuilt, 13 holes, pass A 13 / pass B
0]**.  My module is an **orphan** (nothing imports it), which that script reports by name — a
deliberate consequence of the ownership rule for this round, not an oversight.

## 5. Where the tree is wrong

1. **`docs/handoff-krule.md` §T1's `EtaK` code block is stale.**  It shows
   `here {Γ e t t'} : KStep Γ e t → ParRed Γ t t' → EtaK Γ e t'`.  The landed inductive
   (`KEta.lean:137-142`) has `here : KStep Γ e t → EtaK Γ e t`, one premise — the `ParRed`
   premise moved into `ParRed`'s `keta` constructor, which that file's own docstring calls
   "Shape C" and explains.  §T1's *argument* is unaffected; only its transcription is wrong.
   **[read, both sites]**
2. **`ChurchRosser.lean:1815`'s "one direct user" is right, but "the restatement serves all of
   them" reads as if the chokepoint substitution were a drop-in.  It is not.**
   `appDF_extra_of_descend` concludes in `ParRedS`; `appDF_extra_of_descendVK` concludes in
   `ParRedKS` **[read, both signatures]**.  So there is no one-line edit at the chokepoint:
   `parRed`, `parRedS`, `CRDefEq` and `church_rosser` all move to `ParRedK` together, and every
   consumer that cases on `ParRed` moves with them.  `DescendRestate.lean`'s "serves all of
   them" and `ParRedMissing.lean`'s "not reachable today" are consistent once that is said out
   loud; read alone, the first is easy to over-read.  **My §2 is one of the consumer ports that
   move.**
3. **`docs/critical-path.md`'s three different user counts for `descend`** (193 / 206 / 200) are
   all live in the tree with no note saying they are the same quantity under three instruments.
   I did not re-measure and I am not claiming which is right.

## 6. Sequencing: what to pick up first

1. **Move `Pattern.headConst`, `Pattern.Matches.headConst`, `PatFreeHead`, `List.Forall₂.trans'`,
   `List.forall₂_refl'` and the four `VExpr.constApp_ne_*` lemmas from
   `Verify/Typing/ConstSpine.lean` into `Theory/`** (they belong beside
   `Theory/Typing/Injectivity.lean`'s `VExpr.headConst?`).  Then delete my copies, restate my
   three theorems against the moved definitions, and run the `quotParams` check §3.1 cannot
   reach.  That is the cheapest thing on this list and it unblocks the only untested case.
2. **Do not attempt `descend` again, and do not attempt a syntactic weakening of it.**  Its
   three goals are false, the restatement exists, and the grading route is closed.
3. The next real obstruction on this route is item 1 of §4 — the triangle over `ParRedK` — and
   `ParRedMissing.lean` §3 has already priced why it is hard.  Nothing I did makes it easier.
4. **Not touched, and not to be inferred from anything above:** `ChurchRosser.lean` is
   unchanged; no frozen file was read for edit, opened for edit, or touched.

## 7. Build state at hand-off, including one thing that is not mine

* `lake build Lean4Lean.Theory.Typing.DescendConstSpineK` — **green, 81 jobs** **[measured]**.
* A **full** `lake build` was green (`EXIT=0`) at the *start* of this round and is **red at the
  end**, at `Lean4Lean/Theory/Inductive/FieldsNoK.lean:199/220/234/264/276-281/345` — an
  untracked file belonging to the concurrent `FieldsNoK*` stream, with in-flight edits.  My
  module does not import it and is unaffected **[measured]**.  Recorded because "the tree is
  red" will otherwise be attributed to this round.
* `scripts/sorry-census-all.lean` was run **before** that breakage arrived: 367 in population,
  367 built, 0 unbuilt, 13 holes.  A re-run now would report unbuilt modules, so the figure
  above is the valid one and its timestamp matters.
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — **empty** **[measured]**.

## 8. Files

* `Lean4Lean/Theory/Typing/DescendConstSpineK.lean` — **new**, 263 lines, no `sorry`, 81 jobs.
  Nine declarations named above plus six marked copies.
* `docs/handoff-descend.md` — this section prepended; the 2026-08-31 round preserved verbatim
  below.
* Nothing else changed.

---
---

> **CORRECTION (later round, machine-checked elsewhere).** §4's conclusion *"there is no right
> guard"* is **wrong**, and the error matters: it reads as *"`church_rosser` is false for real
> environments"* when the true statement is *"this repo's `Theory/` is missing a rule."*
>
> `Theory/` registers only **constructor-matching** ι/quot rules (`Pattern.lean:293`), so it has
> **no K-like reduction**. Carneiro's κ has one (`unique.tex:103`, `K⁺`, firing at an *arbitrary*
> major premise); the C++ kernel has one (`inductive.cpp:595`); **this repo's own implementation
> has one** (`Inductive/Reduce.lean`, `toCtorWhenK`). And `unique.tex:66` states outright that
> without such a device Church–Rosser *"is not true … because of proof irrelevance"*. So the
> ι-flavoured failure is a **missing rule — fixable**, not an inherent falsity.
>
> **What stands unaffected:** `descend`'s three machine-checked refutations. Those are a *scope*
> defect (quantification over an unregistered `q`) and are independent of this correction.
>
> See `docs/handoff-headreduction.md` and `Theory/Typing/HeadRedStuck.lean`.

# Handoff: `NormalEq.descend` is FALSE, and what that does to the two targets

**Session targets:** `Lean4Lean.VEnv.NormalEq.descend` (`Theory/Typing/ChurchRosser.lean:1706`)
and `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:174`).  Both are
among the tree's 21 `sorryAx` declarations (census re-run this session: **21**, unchanged).

**Headline: three of `descend`'s five `sorry`s are goals that are *false*, not open.**  The
file's own inventory (`ChurchRosser.lean:1541`) says "None of their goals is known false".
That sentence is now wrong, and `Theory/Typing/DescendRefute.lean` carries a machine-checked
witness for each of the three.

Marks used throughout: **[machine-checked]** = a named `sorry`-free Lean declaration in this
tree; **[measured]** = a machine run whose output is reproduced; **[read]** = read off
source; **[analysis]** = neither.

---

## 0. The four things to know before touching either target

0. **`descend` quantifies over an arbitrary `q : Pattern`** — no hypothesis that `q` is a
   rule the environment registers, not even that it is a subpattern of one. **[read,
   `#check` reproduced in §6]**  Its three "E5" branches all assert something about the
   *argument position* of an `.app` pattern node, and at an unregistered `q` each of them is
   refutable.  **[machine-checked: `not_descendStatement`, `not_descendStatement_etaArg`,
   `not_descendStatement_etaFun`.]**
1. **The refutation costs exactly two open hypotheses, and they are the *targets* of the
   development it refutes.**  Each witness needs "this node is not a proof", which needs
   unique typing (`IsDefEq.uniq`) and universe uniqueness (`VEnv.SortUniq`).  Both are
   carried as explicit hypotheses, so the refutation itself is `sorry`-free.  The headline
   is therefore `descend_uniq_sortUniq_not_all`: **`descend`, unique typing and universe
   uniqueness cannot all three hold.**  The latter two are theorems of Lean's type theory,
   so the one that fails is `descend`.  **[machine-checked]**
   *Concurrent-work check:* `Theory/Typing/SortUniqDown.lean`'s `sortUniq_badEnv` (landed
   this session by the `SortUniq` stream) refutes `VEnv.SortUniq` **unqualified over
   `env`** — its witness `badEnv` is not `VEnv.WF` (`badEnv_not_wf`).  The instance used
   here is at `refEnv`, which **is** `VEnv.WF` (`refEnv_wf`), i.e. the
   `∀ env, env.WF → env.SortUniq U` form that remains open.  So the hypothesis is not the
   refuted one.  **[read, from that file]**
2. **Restricting `q` to registered patterns does not save it** — see §3.  It saves the δ
   fragment trivially (a δ-pattern is a bare `.const`, so `descend`'s `.app` cases never
   arise), and it fails for ι and quotient rules, where the argument position is the major
   premise and a large-eliminating `Prop` inductive (`Eq`, `HEq`, `Acc`, `Quot` at
   `Sort 0`) makes that premise a *proof* — which is witness A's shape at a registered
   pattern.  **[analysis]**  §3 says exactly what would have to be built to machine-check it.
3. **`docs/handoff-weakn.md` §4.1 is superseded.**  It calls "`Params` has no instance" the
   *fatal* blocker on the Church–Rosser route.  `docs/handoff-params.md` (later) built
   `paramsOfWF` and `paramsOfDelta`; this session **used** `paramsOfDelta` to get the
   instance the refutation needs, so that blocker is gone. **[machine-checked:
   `Lean4Lean.refParams`]**  The route is still dead, for the stronger reason above.

---

## 1. The criterion, applied to both targets

§5 of `docs/handoff-stratified.md`: *does the induction ever have to look at a conversion
derivation?*  Companion: *is the IH non-vacuous at each recursive position?*

| statement | induction sees a conversion? | conclusion | `trans` | verdict | outcome this session |
|---|---|---|---|---|---|
| `IsDefEqU.weakN_iff` | yes, in the core judgment (`HasType e A := IsDefEq e e A`) | endpoint-asserted | **is the statement** (`Strengthening.iff_trans`) | needs a deterministic reduction relation | not attempted; §5 |
| `NormalEq.descend` | **no** — induction is on `sizeOf g` with a case split on the `NormalEq` *constructor*, and `NormalEq` has no `trans` constructor | — | never arises | tractable | attacked; **three cases refuted, two closable** |

The criterion's verdict on `descend` was right in the sense it is usually used — the
induction is tractable, and 90 % of `descend` is in fact proved.  **What it does not see is
whether the statement is true.**  That is the lesson worth carrying: the criterion predicts
whether an induction *can be run*, not whether its conclusion holds.  `descend`'s induction
runs fine; three of its leaves are simply false.

Companion check ("is the IH non-vacuous"): yes at every recursive position — the recursion is
on strict subterms of `g` and on the lam body in the `etaL` case.  That check also passes,
and also does not see the falsity.

---

## 2. Inventory of `descend`'s five `sorry`s

Line numbers are `Theory/Typing/ChurchRosser.lean` as of this session.  "Branch" names the
`cases`/`rcases` path that reaches it.

| # | line | branch | what the goal asks | status |
|---|---|---|---|---|
| 1 | 1769 | `hm = .var q₁`, function child returned the proof escape | the whole node `.app f₁ a₁` is a proof | **closable** — `NormalEq.appDF_proof_escape`, from `SortUniq` alone **[machine-checked]** |
| 2 | 1779 | `hm = .app q₁ q₂`, function child answered at `kf+1` eta layers | after the β-step, the contractum's argument position matches `q₂` | **FALSE** — `not_descendStatement_etaFun` **[machine-checked]** |
| 3 | 1784 | `hm = .app q₁ q₂`, `kf = 0`, argument child answered at `ka+1` layers | an eta-expanded argument reduces to something matching `q₂` | **FALSE** — `not_descendStatement_etaArg` **[machine-checked]** |
| 4 | 1799 | `hm = .app q₁ q₂`, argument child returned the proof escape | an argument that is a proof reduces to something matching `q₂` | **FALSE** — `not_descendStatement` **[machine-checked]** |
| 5 | 1801 | `hm = .app q₁ q₂`, function child returned the proof escape | the whole node is a proof | **closable** — same lemma as #1 **[machine-checked]** |

So the file's grouping ("E3" = #1 and #5, "E5" = #2, #3, #4) is exactly the true/false split:
**E3 is closable, E5 is refuted.**

### 2.1 `appDF_proof_escape` — what closes #1 and #5

`VEnv.NormalEq.appDF_proof_escape` (`Theory/Typing/DescendRefute.lean`): given
`Γ ⊢ f₁ : ∀ A, B`, `Γ ⊢ f₂ : ∀ A, B`, `Γ ⊢ a₁ : A`, `Γ ⊢ a₂ : A`, `Γ ⊢ a₁ ≡ₚ a₂`, and `f₁`
inhabiting a proposition `P`, it produces `∃ P', Γ ⊢ P' : Sort 0 ∧ Γ ⊢ f₁ a₁ : P' ∧
Γ ⊢ f₂ a₂ : P'` — which is precisely `DescentOut`'s `.inr` disjunct at the node.  Its one
hypothesis is `hsu`, i.e. `VEnv.SortUniq` (`Theory/Typing/SortUniq.lean`), the same one
`NormalEq.appDF_proofIrrel` already takes.  It is the first half of `appDF_proofIrrel`, split
out because `descend` needs the *escape*, not the `NormalEq`.

`sorryAx`-tainted through `IsDefEq.uniq` and `IsDefEqU.of_l`, exactly as `appDF_proofIrrel`
is; the *new* content is only that E3 needs nothing beyond what is already assumed there.

**It was deliberately not landed inside `descend`.**  `descend`'s statement is refuted, so
threading `hsu` through it (and through `appDF_extra_of_descend`, `parRed`, `parRedS`,
`church_rosser`) would be work spent on a statement that has to be restated anyway.  Nothing
in `ChurchRosser.lean` was edited this session.

### 2.2 Non-vacuity, and one honest negative

`appDF_proof_escape` has **no useful `_fires` witness**, and this is stated rather than
faked.  Its conclusion is "the node is a proof"; at any concrete witness small enough to
check, the node's proposition is visible and the conclusion is provable directly, without the
lemma.  So a `_fires` theorem would be a tautology of exactly the kind `StrengthenWitness.lean`
was corrected for twice.  It is not written.

The **refutation's** non-vacuity is structural rather than a separate witness: its premises
are honest derivations over a `VEnv.WF` environment (`refEnv_wf`, `[propext, Quot.sound]`),
and its conclusion `¬ DescendStatement refParams` is not provable without them.  The
anti-strawman check is `descendStatement_holds : DescendStatement I`, proved **by**
`@VEnv.NormalEq.descend I` — so `DescendStatement` is `descend`'s type, verbatim, not a
paraphrase. **[machine-checked; that one is `sorryAx`-tainted, inherited from `descend`, which
is the point.]**

---

## 3. The refutation

`Theory/Typing/DescendRefute.lean` (new, ~500 lines, no `sorry`).

### 3.1 The environment

`refEnv`: six `.axiom` steps from `VEnv.empty`, **no definitional-equality rules at all**.

```
P : Prop            D : P                 T : Type
C : P → T           E : P → P             F : (P → P) → T
```

`refEnv_wf : refEnv.WF` **[machine-checked, `[propext, Quot.sound]`]**.  `E`'s type
`P → P` is itself a proposition (`imax 0 0 = 0`), which is what lets an *eta-expanded*
argument be `NormalEq` to a constant.  `T` is declared at `Sort 1`, which is what makes
"the node is not a proof" reachable.

`refEnv` has no rules, so `VEnv.DeltaFragment refEnv` holds vacuously and
`VEnv.paramsOfDelta` gives `refParams : VEnv.Params` **[machine-checked]**.  It also makes
`Lean4Lean.Pat refEnv` empty (`refNoPat`), hence `ParRed.extra` unfireable — which is how
every "does not reduce" step is discharged.

### 3.2 The three witnesses

All at `Γ = [P]`, whose `.bvar 0` is a *proof* of `P`.

| witness | `q` | left term `g` | right term `g'` | why `g ≡ₚ g'` | `sorry` hit |
|---|---|---|---|---|---|
| A | `C · D` | `C h` | `C D` | `appDF` + `proofIrrel` on the two proofs `h`, `D` | 1799 |
| B | `F · E` | `F (λx. E x)` | `F E` | `appDF` + `etaL` (`P → P` is a Prop, so the body is `refl`) | 1784 |
| C | `C · D` | `(λx. C h) D` | `C D` | `appDF` + `etaL` whose body applies `C` to the *outer* proof variable | 1779 |

In each case:

* **the answer disjunct fails** — `refParRedS_G`, `_G2`, `_G3` compute the full reduct set
  (a singleton for A and B; `{g, C h}` for C, because C's node is a β-redex whose contractum
  is witness A's left term), and none of the reducts matches `q`, nor is any of them a
  `.lam` (which is what `DescentLam (k+1)` would need). **[machine-checked]**
* **the escape disjunct fails** — each `g` inhabits `T`, and `refNotProof` shows nothing of
  type `T` is a proof, from `SortUniq` and `UniqTyping`. **[machine-checked]**

### 3.3 Which branch each witness reaches — and how sure that is

**[read, from `ChurchRosser.lean:1745-1801`]**, not machine-checked: `descend` dispatches on
the `NormalEq` constructor and then on the `Matches` constructor, and the branch is
determined by the shape of the two recursive results.

* A: outer `appDF`; `hm` is `.app`; function child's `NormalEq` is `refl` → `.inl ⟨0,…⟩`;
  argument child's is `proofIrrel` → `.inr`.  That is the `esca` branch, **:1799**.
* B: same, except the argument child's `NormalEq` is `etaL` whose body is `refl`, so its
  descent takes `descend`'s `etaL` case and returns `.inl ⟨0+1,…⟩`.  With `kf = 0` and
  `ka = succ`, that is **:1784**.  (Note this is *why* witness B's argument is `λx. E x` and
  not `λx. x`: with `λx. x` the body's `NormalEq` is `proofIrrel`, the descent escapes, and
  the branch reached would be :1799 again, not :1784.  This was caught and corrected.)
* C: the *function* child is the eta-expansion, so its descent returns `.inl ⟨0+1,…⟩` and
  `cases kf` takes `succ`, **:1779**, before the argument is looked at.

If a future reader wants this machine-checked rather than read, the instrument is a copy of
`descend` with the five `sorry`s replaced by five distinct `False` hypotheses; each witness
then discharges exactly one.  Not built this session.

### 3.4 What is *not* claimed

* Nothing here refutes `IsDefEq.church_rosser` at `refEnv`.  With no rules, `parRed`'s
  `appDF × extra` case — `descend`'s only consumer — never fires, so `church_rosser` at
  `refEnv` is untouched by this.
* Nothing here says any *particular* repair of `descend` is impossible.  It says the
  statement as written is false and must be restated. §4 is the analysis of which
  restatements survive.

---

## 4. Does restricting `q` to registered patterns repair it?  **[analysis]**

The obvious repair is to add `Pat q r` (or `Subpattern q p` for a registered `p`) to
`descend`.  All three witnesses die immediately, since `refEnv` registers nothing.

* **δ fragment: repaired, trivially.**  `Pat.delta` produces only `p = .const c`, so
  `descend`'s `.app` and `.var` cases are unreachable and only `refl` / `constDF` /
  `proofIrrel` / `etaL` survive — E3 and the closed cases. **[analysis; the `Pat`
  constructor list is [read] from `PatternRules.lean:270`]**
* **ι and quotient rules: not repaired.**  An ι-pattern is
  `rec.{ls} p m min i (c.{ls'} p b …)`; its argument position at the top node is the *major
  premise*, and `Matches` requires that position to be a constructor application
  syntactically.  For a large-eliminating `Prop` inductive the major premise is a **proof**:
  `Eq`, `HEq`, `Acc`, and `Quot α r` at `α : Prop`.  Then `Γ ⊢ h : a = a` for a variable `h`
  gives `NormalEq Γ (Eq.rec … h) (Eq.rec … (Eq.refl a))` by `appDF` + `proofIrrel`; the left
  term does not reduce (no `Matches`), and at a large-eliminating motive it is not a proof.
  That is witness A verbatim, at a registered pattern.
* **The same argument reaches `IsDefEq.church_rosser` itself.**  In such an environment
  `Eq.rec C m h ≡ m` holds (proof irrelevance, then the ι-rule) while `CRDefEq` needs a
  `ParRedS`-join followed by a `NormalEq`, and `Eq.rec C m h` is `ParRed`-normal, `m` is
  `ParRed`-normal, and no `NormalEq` constructor relates them when `C` is not a `Prop`.  So
  `church_rosser` is false for environments with an `Eq`-like ι-rule.  This is the familiar
  fact that Lean's *reduction* is not confluent in the presence of proof irrelevance; what is
  new here is that `ChurchRosser.lean` states confluence about the **declarative** judgment,
  where the fact bites.
* **`ChurchRosser.lean` knows half of this and did not draw the conclusion.**  Its own E5
  note (`:1552-1566`) says the missing side conditions are "the major premise's type is not a
  Π; small elimination, **which is false unguarded** — `Eq` is a `Prop` that large-eliminates
  — so the guard has to be right".  There is no right guard: the guard would have to exclude
  `Eq`, and `Eq`'s ι-rule is in every real environment.

**What it would take to machine-check the ι/quot half.**  A `Params` instance over an
environment carrying such a rule.  `paramsOfDelta` does not apply (the environment is not a
δ fragment) and `paramsOfWF` needs `PatWF`, whose ι and quot cases are open
(`docs/handoff-params.md` §1.1).  The cheapest route is `VEnv.empty.addQuot`: `Quot.lift` at
`α : Sort 0` is a large elimination out of a proposition, and `Pat.quot`'s three side
conditions are all supplied by `addQuot`.  That leaves `PatWF`'s quot case as the one
obligation — carry it as an explicit hypothesis, exactly as `SortUniq` is carried here, and
the refutation goes through conditionally.  Estimated one session.

---

## 5. Consequences for `IsDefEqU.weakN_iff`

`docs/handoff-weakn.md` §8's item 2 says the target "needs a deterministic reduction
relation", and that the two candidate sources are `ChurchRosser.lean` and
`HeadReduction.lean`, both gated on `Params`.  Three updates:

1. **The `Params` gate is gone** (§0.3) — `paramsOfWF` / `paramsOfDelta`. **[machine-checked
   in `ParamsBuild.lean`; used here]**
2. **`ChurchRosser.lean` is no longer merely circular; its key lemma is false.**  §4.3 of
   `handoff-weakn.md` listed three prerequisites and put "discharge `descend`'s five
   `sorry`s" third.  That item is not a matter of effort: three of the five cannot be
   discharged. The route needs a *different statement*, not a completion.
3. **`weakN_iff` itself was not attacked this session, and its statement is clean** (§6).
   The §1 verdict stands unchanged: `trans` *is* the statement, and no propagated
   restatement exists without a coherence clause whose base case is the target.

The honest summary for whoever picks up strengthening: the tree now has **no** candidate
reduction relation.  `HeadReduction.lean` is untouched by this session's finding and is the
only remaining one; nobody has run a confluence argument over it, and `RawDefEq.lean`'s
three-place judgment is still unexplored.

---

## 6. Auto-bound implicit audit of both targets  **[measured]**

The brief asked for this specifically, after `Params.extra_pat` and `Aligned.addInduct`.

```
@VEnv.IsDefEqU.weakN_iff : ∀ {Γ' : List VExpr} {env : VEnv} {U : Nat},
  env.WF → OnCtx Γ' (env.IsType U) →
    ∀ {n k : Nat} {Γ : List VExpr} {e1 e2 : VExpr},
      Ctx.LiftN n k Γ Γ' →
        (env.IsDefEqU U Γ' (VExpr.liftN n e1 k) (VExpr.liftN n e2 k) ↔ env.IsDefEqU U Γ e1 e2)

@VEnv.NormalEq.descend : ∀ [inst : VEnv.Params] (N : Nat) {g : VExpr},
  sizeOf g ≤ N →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      OnCtx Γ (VEnv.Params.env.IsType VEnv.Params.univs) →
        VEnv.NormalEq Γ g g' → q.Matches g' n1 n2 → VEnv.DescentOut Γ q g g' n1 n2
```

**Neither has an auto-bound defect.**  Every variable is used where it is meant to be:
`weakN_iff`'s `Γ'` is shared between `hΓ` and `W`; `descend`'s `n1`/`n2` are typed by the
same `q` that `Matches` and `DescentOut` use, and `env`/`univs` resolve to `Params`' fields
rather than to stray section variables.

`descend`'s defect is a *scope* defect, not a binding one: `q` is under-constrained, and the
type checker cannot see that because nothing about `q` is wrong — there is simply no
hypothesis about it.  Worth adding to the trap list: **a quantifier with no hypothesis on it
is as dangerous as a mis-bound one, and `#check` does not show the difference.**

---

## 7. Corrections this session makes to existing documents

| document | claim | correction |
|---|---|---|
| `ChurchRosser.lean:1541` | "every one of them waits on a hypothesis … None of their goals is known false" | **false**: #2, #3, #4 are false. **[machine-checked]** |
| `ChurchRosser.lean:1552` | E5 "waits on" two `Params` conditions to be carried as hypotheses | there is no satisfiable pair of conditions; the statement's `q` is the problem |
| `docs/handoff-weakn.md` §4.1 | "`Params` has no instance … the fatal blocker" | superseded by `docs/handoff-params.md`; `paramsOfDelta` is used here **[machine-checked]** |
| `docs/handoff-weakn.md` §4.3 step 3 | "discharge `NormalEq.descend`'s five `sorry`s" | not dischargeable; the statement must be restated |

Nothing in `docs/handoff-weakn.md` §§0–3 and §§5–8 was contradicted, and none of it was
re-measured this session; treat its figures as inherited.

---

## 8. What to pick up first

1. **Restate `descend`.**  It is the only way anything downstream of it moves.  The minimum
   is a `Pat`/`Subpattern` hypothesis on `q` plus `hsu`; that gets the δ fragment, which is
   the fragment `paramsOfDelta` can instantiate today, and E3 is already written
   (`appDF_proof_escape`).  Do **not** re-attempt E5 as stated.
2. **Decide whether confluence is wanted at all.**  §4's analysis says a restated `descend`
   still fails on ι/quot rules, and that `church_rosser` fails with it.  Before anyone spends
   a session on the restatement, spend the cheaper one machine-checking §4 over
   `VEnv.empty.addQuot` — if it confirms, the entire `ChurchRosser.lean` +
   `HeadReduction.lean` development (534 declarations, `docs/handoff-params.md` §3.1) is
   proving something false about real environments, and the strengthening route must look
   elsewhere.
3. **Do not** attack `IsDefEqU.weakN_iff` through Church–Rosser.  `docs/handoff-weakn.md` §5
   already ruled out six routes; this session removes the seventh.

---

## 9. Files

* `Lean4Lean/Theory/Typing/DescendRefute.lean` — **new**, no `sorry`.  The environment, the
  `Params` instance, the three witnesses, `refNotProof`, `DescendStatement`, the three
  refutations, and `appDF_proof_escape`.  Reachable from `lake build Lean4Lean.Theory` (the
  library globs `Lean4Lean.Theory.*`), not imported by `Lean4Lean/Theory.lean` and therefore
  not in the census's scope — it has no `sorry`, so the count is unaffected.
* `Lean4Lean/Theory/Typing/ChurchRosser.lean` — **unchanged**.  Its five `sorry`s are still
  there and this session did not earn the right to remove any of them; three of them cannot
  be removed at all.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**.
* `docs/handoff-weakn.md` — carries a pointer to this document; its body is otherwise
  untouched.

### Housekeeping for whoever merges

* `VEnv.UniqTyping` (this file) and `VEnv.UniqTy` (`Theory/Typing/SortUniqDown.lean`, landed
  concurrently) are the same statement under two names.  Dedupe; keep one.
* At the end of this session `lake build Lean4Lean.Theory` succeeds (1227 jobs) but
  `lake build Lean4Lean.Verify` does **not**: `Verify/EquivManager.lean:117` and
  `Verify/Environment/InductR.lean:873` are red from other streams' in-flight edits.  That
  is why `scripts/sorry-census.lean` cannot be re-run at the end of this session — it
  imports `Verify/Guard.lean`.  The census *was* run at the start (**21**, unchanged from
  the brief) and this session adds no `sorry` and removes none, so the count is still 21.
