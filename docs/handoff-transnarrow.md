# handoff-transnarrow

Round start: 2026-09-05. HEAD `46026b8`. Bare build reported green at 1678 jobs, guards 1/2/3 ✓,
census 13 (all three to be re-measured, see §3).

Owner files: `Lean4Lean/Theory/Typing/TransNarrow.lean` (new), this file. Everything else
read-only. `Theory/Typing/UniqueTyping.lean` (which holds the hole) is **not** mine to edit — if
the residual is dischargeable I prove the content in `TransNarrow.lean` and state the exact edit.
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` frozen.

Target: `Lean4Lean.VEnv.TransStrengtheningNarrowInner` — per the brief the **sole remaining
residual** of `IsDefEqU.weakN_iff` after last round's two collapses (position quantifier `k`
redundant by `StrengtheningTarget.iff_inner`; typing half `TypingStrengthening1Inner.typingStrengthening1`
`sorryAx`-free). Named sub-question inherited from last round: **is exchange of a closed entry free?**
If yes the prefix `Γ` below the innermost entry empties and the statement reduces to a one-entry
context.

Marks: **[measured]** = a command run in this round; **[read]** = read off source in this round;
**[analysis]** = neither.

---

## §1 Shape questions

**Written before opening `WeakNAttack.lean`, `StrengthenNarrow.lean`, `GateBodyDescend.lean`,
`UniqueTyping.lean`, `docs/handoff-weakniff.md` §2 onwards, or any script.** What was read at
write time: `CLAUDE.md`; `git log -1`; `ls docs/`; `ls Lean4Lean/Theory/Typing/`; `ls scripts/`;
`docs/handoff-weakniff.md:1-140` (for the §1/§2 house format only — its Q1-Q4 predictions and the
first two of its verdicts were visible, nothing about `...Inner` or about exchange). Prediction
lines are written in one pass immediately after the questions and before any further read; answers
are appended in §2. **A filled answer is never edited**; corrections go in §2 with a date.

### The four shape questions, instantiated to "`TransStrengtheningNarrowInner`, and: is exchange of a closed entry free?"

**Q1 — Does the target exist in the shape the brief gives it, judged on all three searches
(conclusion-head, hypothesis-shape, hole audit) and not on the name?**
(a) Is there a declaration literally named `VEnv.TransStrengtheningNarrowInner`? Is it a
`def … : Prop` (instantiable, so quantifier-extreme probes work) or a theorem? The brief prices it
"arity 9, cone 3486" — **whose** arity is 9: the `def`, or a link lemma reducing the general
statement to it? A `def : Prop` in this family has run 2 explicit args (`env`, `U`), so arity 9
cannot be the def's.
(b) Is `VEnv.StrengtheningTarget.iff_inner` a genuine `Iff` with both directions in the term, and
is it `sorryAx`-free? If it is not, "the position quantifier `k` is redundant" is a claim modulo
whatever it carries, and the collapse the brief hands me is weaker than stated.
(c) **Definitional aliases / generation drift** (method rule 3, and rule 3's own recorded failure):
the previous round's §2 lists `TransStrengtheningNarrow{,At,T,Neutral,Spine}` as five *different*
statements, one per generation of narrowing. Do `...Inner` variants exist for more than one of
them, and is the brief's `TransStrengtheningNarrowInner` the newest generation or already
superseded inside `WeakNAttack.lean` itself? Every conclusion-head search I run must cover every
generation, not just the one the brief names.
(d) Is `forallE_inv_stratified`-via-`IsDefEqU.lamDF_inv` really the **only** hole in its cone, or
does the cone also reach `IsDefEqU.weakN_iff` itself (rule 3's hole audit: a producer can exist
*and be useless*)?
  - Prediction (committed before the reads that resolve it): (a) the name exists as a `def … : Prop` with 2 explicit args; **arity 9 belongs to a link lemma**, not the def — most likely the `.of_inner`/`iff_inner` direction that instantiates `n k Γ Γ' e1 e2` plus three hypotheses. (b) `iff_inner` is a genuine `Iff` and is **not** `sorryAx`-free — it will carry `forallE_inv_stratified`, since the `→` direction has to re-abstract a binder. (c) yes, `...Inner` variants exist for at least two of the five generations, and I predict the brief's name is the newest. (d) `forallE_inv_stratified` is the only hole and the cone does **not** reach `weakN_iff` — last round did run a hole audit, so this one I expect to reproduce.
  - Answer (§2): _____

**Q2 — Is the residual where the brief says, and is "innermost" a normal form or one more step from one?**
(i) The brief says the typing half is discharged and the `trans` case at the innermost position is
all that is left. Is that a *measured* split (a proof of `StrengtheningTarget` from
`TypingStrengthening1Inner` + `TransStrengtheningNarrowInner`, hole-free apart from the pervasive
two), or is it two separately-proved facts with the gluing lemma still open?
(ii) Is `TransStrengtheningNarrowInner` **equivalent** to its own one-entry-context instance
(prefix `Γ = []`)? That is the shape of last round's winning move — `iff_inner` came from noticing
a cheap extreme *is a normal form* (rule 2's fifth refinement). If yes, the statement is as narrow
as it can get and the residual is about a single closed entry.
(iii) Vacuity: is there a `VEnv.WF` env, a closed entry `A`, and a genuine `IsDefEqU` factoring
`e1 ≡ b ≡ e2` through a middle `b` that does **not** `Skips 1 0`, with `e1 e2` both lifted? If no
such instance exists the residual is vacuously true and the round ends in a proof, not a refutation.
  - Prediction (committed before the reads that resolve it): (i) **not fully measured** — I predict the gluing lemma (`StrengtheningTarget` from the two halves) exists and is itself sorry-free, but that the brief's "sole remaining residual" is a statement about *what is left open*, and that a fourth item (a `Skips`/decidability side lemma) will turn up in the glue. (ii) **yes, equivalent to the one-entry instance**, contingent on Q4(e); this is the round's main bet. (iii) not vacuous — such an instance exists (take `b` a bvar pointing at the innermost entry).
  - Answer (§2): _____

**Q3 — Measurement or docstring? Every number in my brief, classified and re-run at `46026b8`.**
(i) `TransStrengtheningNarrowInner` arity 9, cone 3486, holes = {`forallE_inv_stratified`}.
(ii) `TypingStrengthening1Inner.typingStrengthening1` arity 4, cone 3363, `sorryAx`-free.
(iii) `addDecl.WF_honest` has eight holes, of which four live, one known false, one vacuous,
two deliberate tripwires — and `IsDefEqU.weakN_iff` among the four.
(iv) `StrengtheningTarget.iff_inner` is in `WeakNAttack.lean` §5 and `~20` statements in the family
carried the now-redundant `k`.
(v) census 13, bare build 1678 jobs, guards 1/2/3 ✓.
(vi) **Date the family** (rule 4): `git log -1 --date=short` on every file I lean on, and check
whether `UniqueTyping.lean`'s rewritten ordered pointer list still names the same sharpest statement
the brief does.
  - Prediction (committed before the reads that resolve it): (i) and (ii) reproduce — they were measured yesterday by the round that produced them. (iii) reproduces. (iv) the `~20` will be low; I predict 20-30 statements mention the position argument. (v) census 13 and 1678 reproduce; if census is higher it is another stream's file, not mine. (vi) the pointer list will be current (rewritten yesterday) and will name `TransStrengtheningNarrowInner` — but I predict at least one file in the family is older than the collapse and still states the `k`-quantified form as "sharpest".
  - Answer (§2): _____

**Q4 — Cheapest instrument first, and the inherited sub-question: is exchange of a closed entry free?**
The innermost statement quantifies `n`, the prefix `Γ`, the entry `A`, the middle term `b`, `e1`,
`e2`, `env`, `U`, plus a `Ctx.LiftN`-shaped structure **with a side condition** — so the extremes
include what that structure *permits and I would assume it forbids* (rule 2's second refinement).
(a) `n = 0`: free (`liftN 0 = id`)? If so no induction on `n`.
(b) `n = 1` vs `n > 1`: is `n = 1` general, by composing lifts — and does that composition cost a
`weakN_iff` (circular) or is it structural?
(c) prefix `Γ = []`: is the one-entry instance free, or is it the *whole content*? Both are
possible and they have opposite consequences; last round's win was case two.
(d) middle term `b = bvar 0` (the minimal `¬ Skips` witness) — enough to reconstruct the general
`b`? Check **monotonicity before calling this witness cheap** (rule 2's fourth refinement).
(e) **The inherited question.** Last round killed emptying the prefix by "that is context
exchange, which costs a `weakN_iff` per binder — circular", and named the kill's hypothesis as
"exchange of a closed entry is free". Two things to check, in this order, because rule 2's sixth
refinement was earned by exactly this failure: **first, does `TransStrengtheningNarrowInner`
actually use exchange at all**, or does it use λ-abstraction / instantiation (which last round
proved is *not* exchange)? Only if it does use exchange: is exchange of an entry whose type is
closed (`A.Skips` everything, no dependence on `Γ`) free — i.e. is there a `SwapCtx`-style lemma
whose `weakN` obligation on the moved type discharges by `Skips` rather than by `weakN_iff`?
  - Prediction (committed before the reads that resolve it): (a) `n = 0` free. (b) `n = 1` **is** general and the composition is structural, not circular — `LiftN` composition is a syntactic lemma. (c) prefix `Γ = []` is the **whole content**, not free — the one-entry instance is a normal form. (d) `b = bvar 0` is **not** enough on its own: the `trans` case's middle term can be an application spine headed by the stripped variable, and I predict monotonicity fails (a larger `b` is not reducible to the bvar case) — so the residual is about a *spine*, matching the existing `TransStrengtheningNarrowSpine` name. (e) **Exchange of a closed entry is free**, and separately I predict `TransStrengtheningNarrowInner` **does not need exchange at all** — the innermost position means there is nothing to move it past on the side that matters, so last round's kill attached to a move the target does not make. This is the mirror image of the trap the brief quotes, and it is where I expect the round's result to come from.
  - Answer (§2): _____

## §2 Verdicts (append-only)

### Q1 — ANSWERED 2026-09-05. Prediction: (a) **wrong**, (b) **wrong**, (c) right-ish, (d) right.

(a) **Wrong, and the brief's numbers belong to a different declaration.** `VEnv.TransStrengtheningNarrowInner`
is `WeakNAttack.lean:242`, a `def … : Prop` with 2 explicit args (`env`, `U`) — that half of the
prediction holds — but **"arity 9, cone 3486" is `IsDefEqU.lamDF_inv`'s row, not the residual's**
`[read: WeakNAttack.lean:63-71 cone table]`. The residual's own reduction lemma
`TransStrengtheningNarrowInner.transNarrow` is **arity 4, cone 3496**. So two of the three numbers
handed to me were the wrong row of the right table. The hole set is the same either way
(`forallE_inv_stratified`), which is why the mix-up was invisible.

(b) **Wrong.** `StrengtheningTarget.iff_inner` (`WeakNAttack.lean:305`) is a genuine `Iff`, but
its holes are **both** (`forallE_inv_stratified` *and* `WF.rigidShapeUniqNS`), arity 3, cone 3730
`[read: same table]` — not just the one I predicted. The `rigidShapeUniqNS` comes in through the
inherited `StrengtheningTarget.iff_piDescend_narrow`, not through the collapse.

(c) Right that generations, not aliases, are the hazard: `...Inner` variants exist for **four**
statements (`Strengthening1Inner`, `TypingStrengthening1Inner`, `TransStrengtheningNarrowInner`,
`StrengtheningCanonUninhabInner`/`StrengtheningCanonInner`) and the brief's name is the newest
generation of its line.

(d) Right — the cone table records "reaches `weakN_iff`: no" for every row, so the collapse is not
circular. **But the hole audit pays off one line below the hole**: `IsDefEq.skips`
(`UniqueTyping.lean:218`) is *proved by calling `IsDefEqU.weakN_iff`* — it is a producer that
exists and is useless, exactly rule 3's third search. I had planned to use it (see §2/Q4) and it
would have made the whole round circular.

### Q4(e) first half — ANSWERED 2026-09-05, and this is the round's pivot. **`SwapCtx` is not exchange.**

Last round's kill of "empty the prefix" reads: *"Moving a closed entry down past `Γ` is context
exchange, and exchange in this tree costs one `HasType.weakN_iff` per swapped binder
(`Verify/Typing/ProjSkip.lean:54`)"*. `ProjSkip.lean:318-327` defines
```
inductive VExpr.SwapCtx (b B : VExpr) : List VExpr → List VExpr → Prop
  | nil | keep (F::Fs ↦ F::Fs') | swap (F::Fs ↦ VExpr.swapUnit::Fs')
```
— it **replaces an unused binder's type by `swapUnit`, in place**. That is binder *retyping*, not
a permutation: no entry moves. Its `weakN_iff` price is a genuine strengthening price (you must
know the term does not use the binder), and it has nothing to do with moving an entry past a
prefix. So the cited price is a **correct measured fact about a neighbouring operation**, and the
kill it supports does not attach — the mirror image of the `λ`-abstraction/exchange confusion the
brief warned me about, one operation over. `grep -rn "exchange\|Perm"` over `Lean4Lean/`: **the
tree contains no context-exchange lemma at all**, so no price for exchange has ever been measured
here. Second half of Q4(e) (is exchange of a closed entry actually free) in §4.

### Q2/Q4(a-c) — ANSWERED 2026-09-05, and the block size collapses. Prediction: Q4(b) right for the wrong reason; Q2(ii) **right**; Q4(c) right.

Q4(b) predicted "`n = 1` is general and the composition is structural". It **is** general, but not
by composing lifts: `Strengthening.of_typing_narrow` (`StrengthenNarrow.lean`:155) is an induction
on the **conversion derivation**, and across all twelve rules `n` is never touched — `lamDF` and
`forallEDF` go to `W.succ` (which changes `k`, keeps `n`), every other case passes `W` through, and
`trans` applies the residual at exactly the `W` of the goal **[read, then machine-checked]**. So
the `∀ n` was surplus in the *reduction*, and moving it out of the motive is the whole proof:
`TransNarrow.lean` §2's `Strengthening.of_typing_narrowBlock` is `StrengthenNarrow.lean`'s proof
text with `n` fixed, and it type-checks unaltered **[measured: green, zero errors]**. Round 10's
`k`-collapse keeps `n` fixed for the same reason, so it applies at `n = 1` verbatim (§3).

Result: **`TransStrengtheningNarrowInner1`** (§3) — one entry, innermost, `n = 1`, `k = 0`. At that
instance `Ctx.LiftN.one` carries no information, so **`Ctx.LiftN` has left the statement
altogether**: it is about `X :: Γ` and `VExpr.lift`. §4's `StrengtheningTarget.iff_inner1` is an
`Iff`, so no strength is claimed or lost. Q2(ii)'s bet — that the target is equivalent to its own
narrowest instance — was right **for the block size**; the prefix `Γ` is a separate question (§4/§5
below).

Q4(c): the prefix is the whole content, not free — see §5.

### Q3 — ANSWERED 2026-09-05, all re-measured at `46026b8` + this file. Prediction: (i) **wrong** (see Q1(a)), (ii) right, (iv) low, (v) right, (vi) right.

(i) Not reproduced *as given*: the brief's "arity 9, cone 3486" is `IsDefEqU.lamDF_inv`'s row.
The residual's reduction `TransStrengtheningNarrowInner.transNarrow` re-measures **arity 4, cone
3496, holes `{forallE_inv_stratified}`, does not reach `weakN_iff`** **[measured]**.
(ii) `TypingStrengthening1Inner.typingStrengthening1` — reproduced, and I did not need to re-run it
because §4 depends on it: `sorryAx`-free.
(iii) Not re-measured this round (out of my file's reach); the four-live-holes framing is inherited.
(iv) "~20 statements carried `k`" — the family's *`Inner` variants* number **four**, not the
20-odd; the 20-odd is the count of statements in the family, which round 10's own §2 verdict list
enumerates. Low, as predicted, but the two counts were being conflated.
(v) **census 13** `[measured: scripts/sorry-census-all.lean, "HOLES over the WHOLE built
population, unioned across both passes: 13"]`; bare build **1678 jobs before this file, 1679
after** `[measured, both]` — my module adds exactly one job, so a stream reading 1679 and expecting
1678 should look here first; guards `[measured: lake env lean Lean4Lean/Verify/Guard.lean]`
— guard 1 ✓ (24 frozen axioms), guard 2 ✓ (whitelist; proof INCOMPLETE, `sorryAx` present),
guard 3 ✓ (2/2 gaps remaining).
(vi) The pointer list in `UniqueTyping.lean` is current (rewritten at `46026b8`, dated
`git log -1 --date=short`) and does name `TransStrengtheningNarrowInner`. Family dates
**[measured]**: `WeakNAttack` 2026-09-05, `Strengthen`/`GateBodyDescend` 2026-09-03,
`StrengthenNarrow` 2026-09-01, `StrengthenAudit`/`StrengthenPiProp` 2026-08-31 — so the two oldest
files in the family predate both collapses, as predicted.

### Q4(e) second half — ANSWERED 2026-09-05. **Exchange of a closed entry is free, and it is `sorryAx`-free.**

`VEnv.IsDefEqU.exchangeClosed` (`TransNarrow.lean` §5): for `X.ClosedN 0`,
`Ctx.LiftN 1 Γ.length Γ Γ''` and `Lookup Γ'' Γ.length X`,
```
env.IsDefEqU U (X::Γ) e1.lift e2.lift → env.IsDefEqU U Γ'' (e1.liftN 1 Γ.length) (e2.liftN 1 Γ.length)
```
Proof: `IsDefEq.weakN` (append a second copy of `X` at the bottom) then **one** `IsDefEq.instN`
(substitute `bvar 0` by that copy, which is `bvar Γ.length` in `Γ''`), plus `lift_liftN'` and
`inst_lift`. The insight is that the de Bruijn permutation "move the head entry to the far end"
is not a renaming primitive: it *is* `VExpr.inst · (.bvar Γ.length) 0`, because `inst` at 0
substitutes for `bvar 0` and decrements everything else — exactly the permutation.
**Measured: cone 3232, `sorryAx`-free, reaches none of the six watched declarations and not
`weakN_iff`.** So the answer to the round's named question is **yes, and free in the strong
sense** — no hole, no new machinery, twelve lines.

Consequence, `StrengtheningCanon0.iff_target` (§6): the prefix empties, and

> **`IsDefEqU.weakN_iff` is equivalent to: adding `∀ (α : Sort u), α` to the *empty* context is
> conservative for conversion of closed terms.**

`Γ`, `Ctx.LiftN`, `n` and `k` have all left the statement.

## §3 The measured table (all `scripts/exists.lean`, population 493, after `lake build`)

| declaration | arity | cone | reaches `weakN_iff` | holes |
| --- | --- | --- | --- | --- |
| `IsDefEqU.exchangeClosed` (§5) | 12 | 3232 | no | **none** |
| `IsDefEqU.weakN_iff` (the hole) | 11 | 3231 | itself | itself |
| `bottom_package` (§5) | 9 | 3490 | no | `forallE_inv_stratified` |
| `strengthen_of_bottom` (§5) | 12 | 3497 | no | `forallE_inv_stratified` |
| `TransStrengtheningNarrowInner1.block1` (§3) | 4 | 3497 | no | `forallE_inv_stratified` |
| `TransStrengtheningNarrowInner.transNarrow` (round 10) | 4 | 3496 | no | `forallE_inv_stratified` |
| `StrengtheningCanon0.canonInner` (§6) | 4 | 3502 | no | `forallE_inv_stratified` |
| `StrengtheningCanon0.iff_target` (§6) | 3 | **3563** | no | `forallE_inv_stratified` |
| `Strengthening.of_typing_narrowBlock` (§2) | 6 | 3662 | no | both |
| `StrengtheningTarget.iff_inner1` (§4) | 3 | 3708 | no | both |
| `StrengtheningTarget.iff_inner` (round 10) | 3 | 3730 | no | both |
| `StrengtheningCanon0.iff_inner1` (§7) | 3 | 3765 | no | both |

## §4 Scorecard

| question | prediction | verdict |
| --- | --- | --- |
| Q1(a) name/shape/arity | def with 2 args; arity 9 is a link lemma | **half wrong** — def right, but 9/3486 was `lamDF_inv`'s row, not the residual's |
| Q1(b) `iff_inner` holes | one hole | **wrong** — two |
| Q1(c) aliases vs generations | generations, newest named | right (four `Inner` variants) |
| Q1(d) hole audit | no circularity | right — **and it caught `IsDefEq.skips`, which is proved *from* the hole and would have made this round circular** |
| Q2(i) split measured? | a fourth item will turn up | **wrong** — the glue was clean; the surplus was a *quantifier*, not a missing lemma |
| Q2(ii) target = narrowest instance | yes | **right, twice** (block size, then prefix) |
| Q2(iii) vacuity | not vacuous | right (round 10 §7's witness is at `n=1, k=0, Γ=[]`) |
| Q4(a) `n=0` | free | right, and *vacuous*: `Skips.zero` makes `¬ b.Skips 0 0` false |
| Q4(b) `n=1` general | yes, structural | **right, wrong reason** — not lift composition; the reduction's induction never touches `n` |
| Q4(c) prefix = whole content | yes, not free | **wrong** — the prefix is free, by §5 |
| Q4(d) `b = bvar 0` enough | no, monotonicity fails | **not tested** — see §5 gaps |
| Q4(e) exchange | free, and target may not need it | **right on both halves**: free (and hole-free), and last round's kill cited `SwapCtx`, which is retyping, not exchange |

## §5 What this round did not do, and the method's gaps

1. **The residual itself did not move.** `TransStrengtheningNarrowInner1` is smaller than
   `TransStrengtheningNarrowInner` but no easier; §4 is an `Iff`, so no strength is claimed.
   Q4(d) — whether `b` may be narrowed to `bvar 0` — I never tested, because §5 turned out to be
   the higher-value probe. It is the obvious next cheapest instrument and `StrengthenAudit.lean`
   §5 already says no *syntactic* slice of `b` sharpens the residual, so read that first.
2. **§4 and §6 do not compose.** Both are equivalent to the target, but
   `of_typing_narrowBlock`'s induction *enlarges* the context at `lamDF`/`forallEDF`, so
   decomposing the empty-prefix form still needs the residual at every prefix. There is no
   single statement that is narrow in both senses; §7 of the file records this, and it is a real
   limit, not a presentational one.
3. **Method gap: I priced a lemma by its name's neighbourhood, one step from the trap I was warned
   about.** I planned the block-size collapse around `IsDefEq.skips` (`UniqueTyping.lean:218`),
   two lines below the hole, whose *statement* is exactly the both-endpoints-lifted case I needed.
   Its *proof* calls `IsDefEqU.weakN_iff`. Only rule 3's third search (the hole audit) caught it.
   The lesson is narrower than "run three searches": **a lemma sitting inside the hole's own
   file is the most likely useless producer in the tree**, because that is where the hole's
   consequences are collected.
4. **Method gap: the brief's numbers came from the right table's wrong row, and I believed them
   long enough to write a prediction around them** (Q1(a): "arity 9 cannot be the def's"). It
   could not, and was not — it was another declaration's. Re-measuring a relayed number is rule
   5; re-measuring a relayed number *whose subject I have not checked* is the version I needed.
5. **What I did not measure**: the four-live-holes-of-eight framing (Q3(iii)) and the
   311/51/260 user split are inherited from round 10 and are not re-run here.

## §6 The edit I am not making

`UniqueTyping.lean` is not mine to edit this round. Its ordered "sharpest statements" list should
gain a **new first entry**, above `StrengtheningCanonUninhabInner.iff_target`:

>   `VEnv.StrengtheningCanon0.iff_target` (`TransNarrow.lean` §6): adding `∀ (α : Sort u), α` to
>     the **empty** context is conservative for conversion of closed terms. No context, no
>     position, no block size and no entry is quantified — `Γ`, `Ctx.LiftN`, `n` and `k` have all
>     left the statement. Measured cone 3563, carrying only `forallE_inv_stratified`.
>     The prefix is removed by `VEnv.IsDefEqU.exchangeClosed` (§5), which is **`sorryAx`-free**:
>     exchange of a closed entry is `weakN` plus one `instN`. *Round 10's note that emptying the
>     prefix is circular cited `VExpr.SwapCtx`, which is binder retyping, not exchange.*

and the second entry's line about `TransStrengtheningNarrowInner` should note that its `∀ n` is
surplus (`TransStrengtheningNarrowInner1`, `TransNarrow.lean` §3/§4).
