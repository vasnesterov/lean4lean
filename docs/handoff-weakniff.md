# handoff-weakniff

Round start: 2026-09-05. HEAD `651a9b8`. Bare build green at 1677 jobs, guards 1/2/3 ✓, census 13.

Owner files: `Lean4Lean/Theory/Typing/WeakNAttack.lean` (new), this file. Everything else
read-only; `Theory/Typing/UniqueTyping.lean` (which holds the hole at `:172`) is **not** mine to
edit — if the hole is dischargeable I prove the content in `WeakNAttack.lean` and state the exact
edit. `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` frozen.

Target: `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:172`) — the
forward (strengthening) direction of

```
env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2
```

under `W : Ctx.LiftN n k Γ Γ'`, `henv : VEnv.WF env`, `hΓ : OnCtx Γ' (env.IsType U)`.
One of eight holes under `addDecl.WF_honest`, one of four genuinely live ones.

Marks: **[measured]** = a command run in this round; **[read]** = read off source in this round;
**[analysis]** = neither.

---

## §1 Shape questions

**Written before reading the five attacking files (`Strengthen.lean`, `StrengthenCanon.lean`,
`StrengthenVerdict.lean`, `StrengthenWitness.lean`, `StrengthenAxiom.lean`,
`StrengthenNarrow.lean`), before `docs/handoff-weakn.md`, and before running any script.**
The only thing read at write time was `UniqueTyping.lean:1-200` (the hole and its comment) and a
`grep -l` for the three names in the decomposition. Prediction lines are written in one pass
immediately after the questions and before any of those reads; answers are appended in §2.
**A filled answer is never edited**; corrections go in §2 with a date.

### The four shape questions, instantiated to "`IsDefEqU.weakN_iff` = `PiDescend` + `TransStrengtheningNarrow`"

**Q1 — Does the decomposition exist, judged on the *conclusion head* and on all three searches
(conclusion-head, hypothesis-shape, hole audit), not on the name in the comment?**
(a) Is there a declaration literally named `VEnv.StrengtheningTarget.iff_piDescend_narrow`; is it a
genuine `Iff` with both directions in the term; what is its **full arity including invisible
section binders**; and is it `sorryAx`-free — or does it itself inherit a hole, in which case
"this hole is **exactly** X + Y" is a docstring claim and not a measured one?
(b) What are `VEnv.PiDescend` and `VEnv.TransStrengtheningNarrow` — `def … : Prop` (instantiable at
a witness environment) or structures with side conditions; arity; cone size; hole set?
(c) **Definitional aliases** (method rule 3): does `StrengtheningTarget` have two or more names for
one statement — e.g. `Strengthening1`, `StrengtheningTarget`, `StrengtheningNarrow` differing only
by module — detectable as identical arity and cone in different modules? If so, any
conclusion-head search I run must be run against every alias.
(d) Does the *forward direction alone* have a name (the comment in `RestrictCompanion.lean` says
`StrengtheningTarget` **is** the forward direction), and is the backward direction really free
(`h.weakN henv W`) as the source line suggests?
  - Prediction (committed before the reads that resolve it): (a) yes, `iff_piDescend_narrow` exists and is a genuine `Iff`, but it is **not** `sorryAx`-free — it will carry `forallE_inv_stratified` and probably `rigidShapeUniqNS`, so "exactly" means "exactly, modulo two other holes". (b) both are `def … : Prop`, arity 1-2 (`env`, maybe `U`), cones in the low thousands. (c) yes, at least two aliases exist (`Strengthening1` / `StrengtheningTarget`), same statement; predict 3+ names. (d) yes, the forward direction has its own name and the backward direction is genuinely free.
  - Answer (§2): _____

**Q2 — Is the work in the direction I think, and is the narrowing real?**
(i) Which of the two conjuncts is the hard one? The comment prices `PiDescend` as "shape descent,
sorry-free reduction" — i.e. *already discharged* — and `TransStrengtheningNarrow` as the residual.
But `docs/handoff-pidescend.md` (round 8 of this same line) reports `PiDescend` **not proved**, only
decomposed to `PiDescendFst`. So: is `PiDescend` a *proved lemma*, an *open `def : Prop`*, or a
proved-modulo-other-holes lemma? These give three different prices for the round.
(ii) Is the `¬ b.Skips n k` restriction on the middle term actually a *weakening* of the `trans`
case, or is `TransStrengtheningNarrow` **equivalent** to the unrestricted `TransStrengthening` (the
comment's own argument — "without it the residual re-instantiates at the whole statement" — is an
argument that the *unrestricted* form is circular, which is not the same as the restricted form
being weaker)? If they are equivalent the decomposition is a restatement, not progress.
(iii) Is the whole question at risk of vacuity: is there a `VEnv.WF` environment where a
`Ctx.LiftN n k` with `n > 0` and a genuine `IsDefEqU` on lifted terms exists at all, so that the
forward direction has content?
  - Prediction (committed before the reads that resolve it): (i) `PiDescend` is an **open `def : Prop`**, not a proved lemma — the comment's "sorry-free reduction" describes the *reduction to it* being sorry-free, not `PiDescend` being proved; so the round's price is `PiDescendFst` + `TransStrengtheningNarrow`, two open items, not one. (ii) the narrowing is **real but small**: `TransStrengtheningNarrow` will be strictly weaker syntactically yet I predict an equivalence proof to the unrestricted form is available by a case split on `Skips`, i.e. the narrowing buys nothing on its own. (iii) not vacuous.
  - Answer (§2): _____

**Q3 — Measurement or docstring? Every count in my brief, classified.**
(i) `296` users of this hole, split `43` typing-half / `253` narrow residual (and `46/250` with
`hasType_app_bvar0` as a gate) — measured at `d67375b`, i.e. **dated**. Re-measure at `651a9b8`.
(ii) `addDecl.WF_honest` arity 6, cone 20433, exactly eight holes, and `IsDefEqU.weakN_iff` among
them. (iii) "Not circular with `WF.rigidShapeUniqNS` / `IsDefEqU.forallE_inv_stratified`" — is
`StrengthenNarrow.lean`'s cone table reproducible, and in particular does `PiDescend`'s or
`TransStrengtheningNarrow`'s cone reach `IsDefEqU.weakN_iff` itself (method rule 3's hole audit: a
producer can exist *and be useless*)? (iv) The family is described as five files but six names are
listed in the comment — count the modules that actually exist. (v) census 13, build 1677.
  - Prediction (committed before the reads that resolve it): (i) the 296/43/253 will **not** reproduce at `651a9b8` — expect a larger user count (the tree grew ~15 modules since `d67375b`) and a similar or slightly worse ratio. (ii) arity 6 / cone 20433 / eight holes will reproduce. (iii) the non-circularity will reproduce for `rigidShapeUniqNS` but I predict the `iff` itself **does** reach `IsDefEqU.weakN_iff` somewhere in its cone via a `Verify`-side lemma, making at least one of the two conjuncts' proofs useless-as-stated (rule 3's third search). (iv) six modules exist, the comment's "five files" is off by one, matching this session's earlier "family of five described as three". (v) census 13, 1677 reproduce.
  - Answer (§2): _____

**Q4 — Cheapest instrument first: every quantified argument at its extremes, current form.**
The statement quantifies `n`, `k`, `Γ`, `Γ'`, `e1`, `e2`, `env`, `U`, plus the structure
`Ctx.LiftN n k Γ Γ'` **which carries a side condition** — so the extremes include *what `LiftN`
permits and I would assume it forbids* (method rule 2). Concretely:
(a) `n = 0`: is `LiftN 0 k Γ Γ` inhabited, does `liftN 0 k e = e` hold definitionally, and is the
`n = 0` instance therefore **free**? If yes, any induction must be on something other than `n`.
(b) `k = 0` vs `k > 0`: is the `k = 0` (append-at-the-end) case the general one — i.e. does a
`LiftN n k` reduce to a `LiftN n 0` after a `SwapCtx`, which `ProjSkip.lean` claims to build?
(c) `Γ = []`: **is the empty-context instance a normal form of the whole statement** (a prior round
proved its target equivalent to its own empty-context instance)? If `Γ = []` then `e1`, `e2` are
closed and `liftN n k` is the identity on them — so this extreme is free and tells me the content
lives entirely in the *non-closed* case, i.e. in `bvar`.
(d) `e1 = e2`: free by `refl`. `e1`, `e2` both `Skips n k`: is that the case the narrow residual
excludes, and is *that* case already a lemma (`IsDefEq.skips` is right below the hole)?
(e) For `TransStrengtheningNarrow`: instantiate the middle term `b` at its extremes —
`b = bvar j` for a stripped `j` (the minimal `¬ Skips` witness), and `b` a large term mentioning a
stripped variable once. Is the minimal witness `b = bvar j` already enough to reconstruct the
general case, i.e. is the residual really about *one bvar*?
  - Prediction (committed before the reads that resolve it): (a) `n = 0` free — `LiftN 0 k Γ Γ` inhabited and `liftN 0 k e = e` by `rfl` or a one-line simp. (b) `k = 0` is **not** general enough on its own; the `SwapCtx` reduction exists but costs a `HasType.weakN_iff` per binder, which is circular here. (c) `Γ = []` free, and yes I predict the whole content is the `bvar` case plus the `trans` case — the two places where the *conclusion's* term is not determined by the premise's. (d) `e1 = e2` free; the both-`Skips` case is what `IsDefEq.skips` covers and it is a proved lemma. (e) **`b = bvar j` is enough** — predict the narrow residual is exactly "a conversion whose middle term is a stripped variable", and that this is refutable-looking rather than provable-looking, because a stripped variable can be equated to two different strengthened terms only if the ambient context is inconsistent.
  - Answer (§2): _____

## §2 Verdicts (append-only)

### Q1 — ANSWERED 2026-09-05. Prediction: (a) right, (b) right, (c) **wrong in an instructive way**, (d) right.

(a) `VEnv.StrengtheningTarget.iff_piDescend_narrow` **exists**, `StrengthenNarrow.lean:305`, a
genuine `Iff` built by `.trans` of two `iff`s **[read]**. It is **not** hole-free:
`StrengthenPiProp.lean`'s own measured table gives it cone **3662** carrying
`forallE_inv_stratified` and `WF.rigidShapeUniqNS` **[read; re-measured in §3 below]**. So the
comment's "**exactly**" is exact only modulo the tree's two pervasive holes — as predicted.

(b) `PiDescend` is `GateBodyDescend.lean:107`, a `def … : Prop` of two explicit args
(`env`, `U`); `TransStrengtheningNarrow` is `StrengthenNarrow.lean:130`, same shape. Both are
`∀`-statements over `{n k Γ Γ' …}` with a `Ctx.LiftN n k Γ Γ'` premise. Prediction right.

(c) **Wrong, and the failure mode is the opposite of the one I predicted.** There is no alias
collision: `Strengthening`, `Strengthening1`, `Strengthening1Uninhab`, `StrengtheningTarget`,
`StrengtheningCanon`, `StrengtheningCanonUninhab`, `TypingStrengthening`,
`TypingStrengthening1`, `TypingStrengthening1Uninhab`, `TypedStrengthening`,
`TransStrengthening`, `TransStrengtheningNarrow{,At,T,Neutral,Spine}`,
`SortConvStrengthening{,WF}`, `CheckStrengthening`, `PatCheckStrengthening`, `SortDescend`,
`PiDescend`, `PiDescendFst`, `ArgPin`, `PiCodLift{,Inhab,Neutral}` are **twenty-plus genuinely
different statements**, each with its own `iff` or one-way link. The hazard here is not
duplicate names for one statement; it is **one name per generation of narrowing, with the
comment naming generation 5 of 9**. See §2/Q2(i).

(d) Right. `StrengtheningTarget` (`Strengthen.lean:446`) is the forward direction with `OnCtx Γ'`
as its only context hypothesis, and the backward direction of the hole is `h.weakN henv W`,
one term **[read]**.

### Q2 — ANSWERED 2026-09-05. (i) prediction right on the parse, **wrong on the price**; (ii) prediction wrong — §8 of `StrengthenAudit.lean` closes this question in the other direction; (iii) right.

(i) `PiDescend` is an **open `def : Prop`**, and the comment's "sorry-free reduction" describes
the reduction, not the statement — as predicted. But the *price* is not "one open item": the
comment is **three generations stale**, and the chain below it is longer than the comment says.
Machine-checked links, all in the tree already **[read, then re-measured §3]**:

| generation | capstone | file |
|---|---|---|
| 5 | `StrengtheningTarget ↔ PiDescend ∧ TransStrengtheningNarrow` | `StrengthenNarrow.lean:305` |
| 7 | `StrengtheningTarget ↔ PiDescend ∧ TransStrengtheningNarrowNeutral` | `StrengthenPiProp.lean` §3 |
| 8 | `StrengtheningTarget ↔ PiDescend ∧ TransStrengtheningNarrowSpine` | `StrengthenAudit.lean` §2 |
| 8 | `PiDescend ↔ PiDescendFst ∧ SortConvStrengthening` | `PiDescendSplit.lean` §3 |
| 9 | `PiDescendFst ↔ PiCodLift` given `SortConvStrengthening` | `PiDescendFstCod.lean` §4 |
| 9b | `PiDescend ↔ PiCodLiftNeutral ∧ SortConvStrengthening` | `PiDescendFstCod.lean` §6 |

So the honest current statement of the hole is **`PiCodLiftNeutral ∧ TransStrengtheningNarrowSpine`**
(modulo `SortConvStrengthening`, which round 6 proved is a *consequence* of the typing half).

(ii) **My prediction that the narrowing "buys nothing on its own" is wrong as an assessment and
right as a fact, for a reason already proved in the tree.** `StrengthenAudit.lean` §8
(`mid_defeq_lift`, `midNormalise_trivial`, cones 144/150, **hole-free**) proves the middle term
is *always* convertible to a lift, so "it may be taken to be a lift" is a triviality and
**no further restriction on the middle term can sharpen the residual**. The narrowing is real as
a restriction on *representatives* and empty as a restriction on *conversion classes*. The tree
already ruled this direction out; I would have wasted the round on it.

(iii) Not vacuous. `StrengthenAudit.lean` §5 bounds the residual both ways: hypotheses jointly
satisfiable (`transStrengtheningNarrowSpine_hyps_satisfiable`), holds at a well-formed
environment (`exists_wf_narrowSpine`), conclusion not free (`no_neutral_proofIrrel`) **[read]**.

### Q4 — PARTIALLY ANSWERED 2026-09-05 (the extremes instrument, run before writing any Lean).

(a) `n = 0` **free, and already in the tree**: `Strengthening1.target`'s `zero` case is
`cases W.eq_of_zero; simpa using h` **[read]**. Prediction right.
(d) `e1 = e2` free; the both-`Skips` case is `IsDefEq.skips` and
`TransStrengtheningNarrow.vacuous_at_zero` / `.vacuous_of_closedN` cover the degenerate ends
**[read]**. Prediction right.
(e) **Wrong.** The minimal-witness reduction I predicted (`b = bvar j` suffices) is exactly what
`StrengthenAudit.lean` §8 rules out — see (ii). No restriction on `b` helps.
(c) `Γ = []` free, and the "content is the `bvar`/`trans` cases" half is right but is not news:
`Strengthen.lean` §1 closes the *inhabited*-entry case outright, so the content is the
uninhabited entry (§12), and `StrengthenCanon.lean` pins the entry to `bigFalse u = ∀ α : Sort u, α`,
one closed type per level. **The empty-context instance is not a normal form here**: the prefix
below the stripped entry cannot be emptied, because moving a closed entry down past the prefix is
context *exchange*, and exchange in this tree costs one `HasType.weakN_iff` per swapped binder
(`Verify/Typing/ProjSkip.lean:54`) — circular. That kill needs the hypothesis *"exchange is
free"*; it is not, and that is why the prefix stays.
(b) **This is the one extreme nobody has recorded, and it is the round's result.** Every
statement in the family (`Strengthening`, `Strengthening1`, `StrengtheningTarget`,
`StrengtheningCanon`, `TransStrengtheningNarrow*`, `PiDescend`, …, twenty-plus of them)
quantifies the *position* `k` and **none is stated at `k = 0`**. Whether `k` collapses is asked
nowhere in the six `docs/handoff-weakn*.md` sections or the sixteen `Theory/Typing/Strengthen*`
/ `PiDescend*` / `WeakN*` modules. See §3 — it collapses, and the proof is elementary.

### Q3 — ANSWERED 2026-09-05. (i) prediction **right** (numbers moved, and by more than I guessed); (ii) right; (iii) right that the collapse links are non-circular, **wrong** that one would reach the hole; (iv) wrong-ish — the family is *sixteen* modules, not five or six; (v) right.

Every count in the brief and in the tree's own comments, re-measured at `651a9b8` **[measured]**:

| claim, and where it is written | measured now | instrument |
| --- | --- | --- |
| "296 users … 43 typing / 253 narrow (46/250)" — `UniqueTyping.lean:180` | **311 / 51 typing / 260 narrow** | `scripts/weakn-gate-split.lean` (population: `Experimental.ConeJoin` closure) |
| "198 transitive users" — `StrengthenAudit.lean:7` | superseded | same |
| "136 transitive users" — `StrengthenPiProp.lean:7` | superseded | same |
| "131" — `NormalEqStrengthen.lean` docstring | superseded | same |
| "124, not 111" — `docs/handoff-weakn.md` §S.6 | superseded | same |
| — (no prose figure) | **13 direct / 417 transitive over 73 modules** | `scripts/users.lean` (population: whole build, 492 modules) |
| `addDecl.WF_honest` arity 6, cone 20433, exactly 8 holes | **confirmed, all three** | `scripts/exists.lean` |
| census 13 | **13** (pass A 492 modules + pass B 3) | `scripts/sorry-census-all.lean` |
| build 1677 jobs | **1677 before, 1678 after** (this file is the one new job) | `lake build` |
| "372 built modules" — `docs/handoff-pidescendfst.md` | **492** | `scripts/exists.lean` |
| five (six) attacking files — `UniqueTyping.lean:174` | **sixteen** modules: `Strengthen`, `StrengthenAudit`, `StrengthenAxiom`, `StrengthenCanon`, `StrengthenInhabGate`, `StrengthenNarrow`, `StrengthenPiProp`, `StrengthenVerdict`, `StrengthenWitness`, `CRPiDescend`, `NormalEqStrengthen`, `ParRedKWeakN`, `PiDescendFstCod`, `PiDescendSplit`, `WeakNForward`, `WeakNProjGate` | `ls` |

Two lessons rather than one. **(a) The two instruments disagree because their populations differ**
(311 vs 417) — neither is wrong, and quoting either without its population is how the tree
accumulated six numbers for one hole. **(b) The direction of drift is up**: every stale figure
understates. The brief's warning ("cross-check any count you rely on") earned its place again.

(iii) `WF.rigidShapeUniqNS` non-circularity reproduces, and **no declaration in my file reaches
`IsDefEqU.weakN_iff`** — measured on all seven seeds. My prediction that one of them would was
wrong; the reason it is wrong is worth keeping: `IsDefEq.uniq` (`UniqueTyping.lean:15`) sits
*above* the hole in the same file, so appealing to it costs `forallE_inv_stratified` and not the
hole.

## §3 The result: the position quantifier collapses, for the target and for both halves

New file `Lean4Lean/Theory/Typing/WeakNAttack.lean` (355 lines, 16 declarations, no `sorry`).
Its module docstring carries the mechanism, the honest accounting and the measured cone table;
the four links are

* `Strengthening1Inner.iff_target` — the hole ↔ its own instance at `k = 0`;
* `TypingStrengthening1Inner.iff_piDescend` — the **typing half** ↔ its instance at `k = 0`,
  and `TypingStrengthening1Inner.typingStrengthening1` is **`sorryAx`-free** (cone 3363);
* `TransStrengtheningNarrowInner.transNarrow` — the **`trans` residual** ↔ its instance at `k = 0`;
* `StrengtheningCanonUninhabInner.iff_target` — the crispest form the statement has reached:
  *adding `∀ (α : Sort u), α` as the innermost hypothesis of a well-formed context, at a level
  where it has no inhabitant, is conservative for conversion.*

The mechanism is one line of syntax — `(.lam A e).liftN n k = .lam (A.liftN n k) (e.liftN n (k+1))`,
so the λ-abstraction of a lift is a lift one binder further out — plus λ-injectivity for
conversion (`IsDefEqU.lamDF_inv`, §1 of the file, which did **not** exist in the tree: absence
checked three ways, name grep, `scripts/shape.lean` structurally over 492 modules with heads
`{VEnv.IsDefEqU, VExpr.lam}` (51 hits, none of this shape), and a docstring/hypothesis grep).

### Limits of the result, stated and where possible proved

1. **It is a reformulation, not a reduction in strength.** Every link is an `iff`. Nothing is
   closed, the census is unchanged at 13, and `UniqueTyping.lean:172`'s `sorry` stands.
2. **The prefix `Γ` below the entry is not emptied, and cannot be cheaply.** That move is context
   exchange, which costs one `HasType.weakN_iff` per swapped binder — the hole itself
   (`Verify/Typing/ProjSkip.lean:54`) **[read]**. So `Γ = []` is *not* a normal form here; the
   kill's hypothesis, for a later round to weaken, is *"exchange of a closed entry past a prefix
   is free"*.
3. **It does not separate the two halves**, and says nothing about which is harder.
4. **Properness is machine-checked** (`liftN_one_not_inner`): the innermost class is a proper
   subclass of the strippings, so the four links are not trivial directions read backwards.
5. **Three of the four links carry `IsDefEqU.forallE_inv_stratified`** (via `IsDefEq.uniq` inside
   λ-injectivity); only the typing half's collapse is unconditional. Hole-free ≠ discharged
   applies to the rest.

## §4 The exact edit to `UniqueTyping.lean` I did **not** make (not my file)

`Theory/Typing/UniqueTyping.lean:174-190`, the comment above the hole, is wrong in three ways:
it names round 5's capstone as "the current sharpest statement" (three generations stale), it
lists five files where there are sixteen, and its 296/43/253 split now measures 311/51/260.
The replacement I would make, and the whole edit:

```
-- OPEN.  Sixteen files attack this; `Theory/Typing/Strengthen.lean` has the statement and its
-- equivalents, and `docs/handoff-weakn.md` + `docs/handoff-weakniff.md` have the routes already
-- ruled out (do not reattempt them).  The sharpest statements are, in order of narrowness:
--   `StrengtheningCanonUninhabInner.iff_target` (`WeakNAttack.lean` §5) -- adding
--     `∀ (α : Sort u), α` as the INNERMOST hypothesis of a well-formed context, at a level where
--     it has no inhabitant, is conservative for conversion.  No position, entry or prefix-
--     insertion data quantified.
--   `StrengtheningTarget.iff_inner` (`WeakNAttack.lean` §5) -- the same, split into the typing
--     half (`TypingStrengthening1Inner`, equivalently `PiDescend`) and the `trans` residual
--     (`TransStrengtheningNarrowInner`), both at the innermost position.
--   `strengtheningTarget_iff_piDescend_spine` (`StrengthenAudit.lean` §2) and
--     `PiDescend ↔ PiCodLiftNeutral ∧ SortConvStrengthening` (`PiDescendFstCod.lean` §6) --
--     the same two conjuncts narrowed by the shape of the endpoints' type.
-- `scripts/weakn-gate-split.lean` measures the split of this hole's users at `651a9b8`: 311
-- transitive users over `Experimental.ConeJoin`'s closure, 51 needing only the typing half, 260
-- needing the narrow residual.  `scripts/users.lean` over the whole build reports 13 direct and
-- 417 transitive users; the two figures differ because the populations do.  Not circular with
-- `WF.rigidShapeUniqNS` / `IsDefEqU.forallE_inv_stratified`.
```

Nothing else in that file changes; the `sorry` and the theorem statement stay exactly as they are.

## §5 Scorecard

| question | prediction | verdict |
| --- | --- | --- |
| Q1(a) `iff` exists, genuine, not hole-free | yes / yes / carries the two pervasive holes | **right** |
| Q1(b) both conjuncts are `def : Prop`, low arity | yes | **right** |
| Q1(c) 3+ definitional aliases for one statement | yes | **wrong** — twenty-plus *distinct* statements, one per generation; the hazard was staleness, not aliasing |
| Q1(d) forward direction named, backward free | yes | **right** |
| Q2(i) `PiDescend` open, comment's parse | open `def`, reduction is what is sorry-free | **right on the parse, wrong on the price** — the comment is three generations stale |
| Q2(ii) the narrowing buys nothing on its own | equivalence available by a `Skips` case split | **wrong as stated, right in effect** — `StrengthenAudit` §8 proves no restriction on the middle term can sharpen the residual |
| Q2(iii) not vacuous | not vacuous | **right** |
| Q3(i) the dated counts will not reproduce | larger, similar ratio | **right** (296→311, 43→51, 253→260) |
| Q3(ii) `WF_honest` 6 / 20433 / 8 | reproduces | **right** |
| Q3(iii) one conjunct's cone reaches the hole | yes | **wrong** — none does, because `IsDefEq.uniq` sits above the hole in the same file |
| Q3(iv) six modules, comment off by one | six | **wrong** — sixteen |
| Q4(a) `n = 0` free | free | **right** (already in the tree) |
| Q4(b) `k = 0` not general enough on its own | needs `SwapCtx`, circular | **wrong, and this is the round's result** — `k = 0` *is* general, by λ-abstraction, and needs no swap |
| Q4(c) `Γ = []` free; content in `bvar`+`trans` | free; yes | **right, but not news**; and the empty *prefix* is not reachable (exchange is circular) |
| Q4(d) `e1 = e2` and both-`Skips` free | free | **right** |
| Q4(e) `b = bvar j` suffices for the residual | yes | **wrong** — `mid_defeq_lift` rules out every restriction on `b` |

Score: 8 right, 2 half, 6 wrong. The one that mattered was Q4(b), and it was wrong in the
*productive* direction: I priced the cheap extreme as circular on the strength of a fact about a
*different* move (`SwapCtx` for exchange) and nearly did not test it.

## §6 Method gaps, mine

1. **I nearly skipped the extreme that worked, because I had a reason not to.** Q4(b)'s
   prediction cited a real measured fact (`ProjSkip.lean`: swapping costs a `weakN_iff` per
   binder) and drew the wrong conclusion from it: exchange is circular, but λ-abstraction is not
   exchange. Refinement to method rule 2, for the next round: **when an extreme is predicted
   circular, name the specific move the circularity attaches to, and check that the extreme
   actually uses that move.** Twice today a cited-but-mismatched fact nearly killed a live route.
2. **My alias prior (Q1(c)) was aimed at the wrong failure.** In a corner with ten rounds of
   history, the danger is not two names for one statement but *nine* statements each claiming to
   be "the sharpest", with only the oldest cited in the place a reader looks. A cheap instrument
   for that: `git log -1 --date=short -- <each family file>` before believing any docstring's
   "current" claim. It cost me one tool call and reordered the whole round.
3. **I did not test whether the collapse composes with the *shape* narrowings** (round 7/8's
   `TransStrengtheningNarrowSpine`, round 9b's `PiCodLiftNeutral`). It should — the λ step
   preserves neither the type's shape (`T` becomes `.forallE A T`) nor `NeutralTy`, so in fact it
   probably does **not** compose, and the honest statement is that §5's capstone is the round-5
   decomposition collapsed, not the round-8 one. That is the first thing the next round should
   check, and I am recording it as a gap rather than guessing.
4. **Not measured: whether `TransStrengtheningNarrowInner`'s hypotheses are jointly satisfiable
   at `k = 0` specifically.** `StrengthenAudit.lean` §5 bounds the general residual; I inherited
   that bound rather than re-running it at the innermost instance, and an inner form whose
   premises were unsatisfiable would be a vacuous "narrowing". `inner_premises` bounds only the
   *lifting* premise, not the residual's `¬ Skips` + typing premises together.

## §7 Correction, appended (§6 gap 4 is closed)

Gap 4 above ("not measured: whether the inner residual's hypotheses are jointly satisfiable at
`k = 0`") is **closed, in the same round** and before reporting. `StrengthenAudit.lean` §5's
witness turns out to be at `n = 1`, `k = 0`, `Γ = []`, `Γ' = [.sort .zero]` — i.e. it is *already*
an innermost instance — so bound 1 transfers. `WeakNAttack.lean` §7's
`transStrengtheningNarrowInner_hyps_satisfiable` states it at the inner form directly:
**arity 0, cone 793, `sorryAx`-free** (the original bound 1 is 3456 and carries
`forallE_inv_stratified`, because it also asserts `NeutralTyNL` and not-a-Prop, which pull in
`IsType.not_lam`) **[measured]**. So §4's narrowing is not vacuous for want of an instance.

Gap 3 (does the collapse compose with the *shape* narrowings of rounds 7/8/9b?) stands, and I now
expect the answer to be **no**: the λ step replaces the endpoints' type `T` by `.forallE A T`,
which is not `NeutralTyNL`, so the inner form of `TransStrengtheningNarrowSpine` is not reached by
this argument. §5's capstone is therefore the **round-5** decomposition collapsed, not the
round-8 one. Stated as an expectation, not a measurement.

## §8 Final state

* `lake build`: **green, 1678 jobs** (1677 + this round's one new module) **[measured]**.
* Guards: `guard 1` 24 frozen axioms ✓, `guard 2` within whitelist ✓ (proof INCOMPLETE, as
  expected), `guard 3` 2/2 remaining ✓ **[measured]**.
* `scripts/sorry-census-all.lean`: **13**, unchanged (pass A over 492 modules, pass B 3)
  **[measured]**.
* `scripts/dup-names.lean` default run: no duplicates **[measured]**; and all ten new names are
  unique across the source tree (`grep -rln` over `--include=*.lean`, excluding my own file)
  **[measured]** — this module is a leaf that nothing imports, so it is outside
  `Experimental/ConeJoin`'s closure and the default `dup-names` run does not cover it.
* Files touched: `Lean4Lean/Theory/Typing/WeakNAttack.lean` (new, mine) and this file (new, mine).
  Nothing else. `UniqueTyping.lean` unedited — §4 states the edit I would make.
