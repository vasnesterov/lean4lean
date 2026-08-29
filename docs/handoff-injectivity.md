# Handoff: `Theory/Typing/Injectivity.lean` and its family

Session result, written for whoever picks this up next. Claims are marked
**[machine]** (a `sorry`-free Lean declaration in this tree, or a `lake build` /
`#print axioms` / cone-script run on this commit) or **[analysis]** (read off source or
argued, not machine-checked). The distinction is load-bearing: this corner has produced
three wrong verdicts in three sessions, every one of them from analysis, and every
correction from a machine run.

Everything below was verified against a green `lake build` — 1352 jobs, **all three
`Verify/Guard.lean` checks pass** (guard 2 still says "proof INCOMPLETE: sorryAx
present"). **[machine]**

---

## 0. Headline

1. **The census went 21 → 20**, and no other module's count moved. `IsDefEqU.sort_inv` is
   **proved**. Its statement, name and namespace are unchanged; every consumer sees it
   exactly as before. **[machine]**
2. **The four `proofIrrel` holes are closed** — in `forallE_inv`, `sort_forallE_inv`,
   `const_forallE_inv`, `const_sort_inv` — and, unlike what `§9.1` of the previous version
   of this document said, **this costs no statement a hypothesis and needed no human call**,
   because `VEnv.SortUniq` is now a theorem rather than an assumption. `Injectivity.lean`'s
   raw `sorry` count went **12 → 6**. **[machine]**
3. **`forallE_inv_stratified` is NOT a passenger, and the route in
   `docs/handoff-sortuniq.md` §9 fails.** It fails on the index, exactly where that document
   said the question would be settled. Two `sorry`-free implications now pin the shape:
   `PiInvStrat → SortUniq` and `SortUniq → PiInv → PiInvStrat`. So **relative to plain
   Π-injectivity, `forallE_inv_stratified` and `SortUniq` are equivalent** — the corner is a
   *circle*, not a chain. **[machine]**

Nothing was refuted this session.

---

## 1. Census, before and after **[machine]**

`lake env lean scripts/sorry-census.lean`, run at the start and at the end.

| module | before | after |
|---|---|---|
| `Theory.Inductive.Decl` | 1 | 1 |
| `Theory.Typing.ChurchRosser` | 1 | 1 |
| **`Theory.Typing.Injectivity`** | **7** | **6** |
| `Theory.Typing.UniqueTyping` | 1 | 1 |
| `Verify.Environment` | 1 | 1 |
| `Verify.Environment.Boundaries` | 1 | 1 |
| `Verify.Soundness` | 2 | 2 |
| `Verify.TypeChecker.InferType` | 1 | 1 |
| `Verify.TypeChecker.IsDefEq` | 2 | 2 |
| `Verify.TypeChecker.WHNF` | 1 | 1 |
| `Verify.Typing.Lemmas` | 3 | 3 |
| **TOTAL** | **21** | **20** |

The one that left is `Lean4Lean.VEnv.IsDefEqU.sort_inv`.

`Injectivity.lean`'s six remaining `sorry`s, by content:

| declaration | residual |
|---|---|
| `IsDefEqU.forallE_inv_stratified` | opaque `:= sorry` — see §3 |
| `IsDefEqU.forallE_inv` | **`trans` only** |
| `IsDefEqU.sort_forallE_inv` | **`trans` only** |
| `IsDefEqU.const_forallE_inv` | **`trans` only** |
| `IsDefEqU.const_sort_inv` | **`trans` only** |
| `IsDefEqU.const_app_inv` | opaque `:= sorry` — see §6 |

Every `trans` says the same thing: *a term convertible with a Π (resp. with a rule-free
constant application, resp. with a sort) reduces to one*. That is a normalisation statement,
and after this session it is **the only non-opaque residual left in the file**. The
sort-flavoured version of it is gone entirely.

---

## 2. `sort_inv` is proved. What actually happened

Two prior sessions established, and this session used:

* `VEnv.SortUniq` (universe uniqueness) implies `IsDefEqU.sort_inv` with **no normalisation
  argument** — `sort_inv_of_sortUniq`, `[propext, Quot.sound]`, `sorry`-free. The conversion
  derivation is never opened: `IsDefEqU U Γ (.sort u) (.sort v)` unfolds to *one* type
  inhabited by *both* endpoints, because `IsDefEq` here is type-indexed. **[machine]**
* `SortUniq` rides as a **passenger conjunct** inside `IsDefEq.uniq`'s own stratified
  induction — `uniqAux`. `IsDefEq.uniq` calls `sort_inv` nine times and every call is on its
  own IH output, so the fact can be carried instead of imported. **[machine]**

What was missing was the plumbing, and the plumbing was the whole difficulty: the
development lived *above* `UniqueTyping.lean`, and `sort_inv`'s consumers live above that.

**What was done.** The `uniqAux` development was moved *into* `Injectivity.lean`, as
`section UniqAux`, sitting between `forallE_inv_stratified` (which it needs) and the rest of
the family (which now needs it). `sort_inv_of_sortUniq` was moved from `SortUniqDown.lean`
to `SortUniq.lean` so `Injectivity.lean` can reach it — `SortUniqDown` imports `CycleConv`,
which imports `Injectivity`, so that file could never have been imported here.
`UniqueTyping.lean` is **byte-identical to HEAD**: its `IsDefEq.uniq` now calls the proved
`sort_inv` without any edit to its proof. **[machine]**

**Import order was the whole risk, and it is discharged by the build.** The section had to
land inside `Injectivity.lean` rather than in a file below it, because `CycleConv.lean` and
`ConstInvWitness.lean` import `Injectivity` and consume its theorems, and neither is this
stream's to edit.

### Files, and what moved

| file | change |
|---|---|
| `Theory/Typing/Injectivity.lean` | `sort_inv` reproved; `section UniqAux` added; four `proofIrrel` holes closed; `PiInv`/`PiInvStrat`/`piInvStrat_of` added. Imports gain `NotProof`. |
| `Theory/Typing/SortUniq.lean` | `sort_inv_of_sortUniq` moved in (statement unchanged); `variable` line declares `v` instead of auto-binding it. |
| `Theory/Typing/SortUniqDown.lean` | `sort_inv_of_sortUniq` moved out; `sort_inv_of_sortUniq'` (the `env.WF` packaging) stays, since `VEnv.WF` is not in `SortUniq.lean`'s import cone. |
| `Theory/Typing/UniqSort.lean` | reduced to the consequences that must come after `UniqueTyping` (`IsDefEq.uniq'`, `IsDefEqU.sort_inv'`) plus the `propLoopEnv` non-vacuity. |
| `Theory/Typing/UniqueTyping.lean` | **unchanged.** |

---

## 3. The main event: `forallE_inv_stratified` is not a passenger

`docs/handoff-sortuniq.md` §9 proposed replacing `forallE_inv_stratified` inside `uniqAux`'s
`app` case by the *unstratified* `forallE_inv` plus a re-stratification through
`HasTypeStratified.forallE_inv'`, and said "the index bookkeeping in the `app` case is where
it will succeed or fail."

**It fails, and it fails on the index.** Here is the machine-checked half, then the exact
failing step.

### 3.1 What is machine-checked **[machine]**

`Injectivity.lean` packages two statements as `Prop`s, with anti-strawman witnesses proving
that each is the corresponding theorem's type *verbatim*, not a paraphrase:

* `VEnv.PiInvStrat env U` — the statement of `IsDefEqU.forallE_inv_stratified`;
  `piInvStrat_axiom : env.WF → PiInvStrat env U` is that theorem, eta-expanded.
* `VEnv.PiInv env U` — the statement of `IsDefEqU.forallE_inv`;
  `piInv_axiom : env.WF → PiInv env U` likewise.

and proves, both `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**:

```
sortUniq_of_piInvStrat : env.WF → env.PiInvStrat U → env.SortUniq U
piInvStrat_of         : env.WF → env.SortUniq U → env.PiInv U → env.PiInvStrat U
```

So **relative to `PiInv`, `PiInvStrat` and `SortUniq` are equivalent.** `uniqAux` itself is
now `sorry`-free too (it takes `PiInvStrat` as a hypothesis; `piInvStrat_axiom` discharges
it). **[machine]**

`piInvStrat_of` is the machine-checked form of what `forallE_inv_stratified`'s docstring
asserted in prose — that its obstruction is *level alignment*, and that the alignment is
universe uniqueness. Its proof is three applications of `SortUniq`: one for the domain in
`Γ`, one for the codomain in `A::Γ`, and one for the codomain in `A'::Γ` — the last needing
`HasType.defeq_l` first, to move the conversion `forallE_inv` hands back from `A::Γ` to
`A'::Γ` along the domain conversion.

### 3.2 Where the circle refuses to open — the exact failing step **[analysis]**

Inside `uniqQ`'s `app` case at index `n`, with `IH : ∀ m < n, UniqAux env U m`:

* `forallE_inv'` re-stratifies the two Π-types and yields
  `HTS (A::Γ) B (.sort p) true (n-2)` — **index-bounded**, so `IH` applies to it.
* `forallE_inv` yields `IsDefEq (A::Γ) B B' (.sort w)` — an **unstratified** `IsDefEq`. Its
  `w` is chosen by that theorem's own induction and is tied to no index at all;
  `HasTypeStrong.stratify` turns `HasType (A::Γ) B (.sort w)` into `HTS … true N` for an `N`
  that is a function of derivation height, unrelated to `n`.
* The `app` case needs `p ≈ w` — to retype `d3.instN` from `.sort w` to the level `a7` uses.
  That is `SortUniq` on `B` at one bounded and one **unbounded** derivation. `IH` covers only
  `m < n`. **The instance needed is outside the induction hypothesis.**

Three escapes were checked and all close back on themselves:

1. *Bump the bounded derivation to level `w` with `HasTypeStratified.defeq`* — that
   constructor's conversion premise is `IsDefEq (.sort p) (.sort w) (.sort s)`, i.e. `p ≈ w`.
2. *Return `w` as the invariant's level instead of `v`* — then `a7` must be retyped instead,
   same equivalence.
3. *Ask `forallE_inv` for `IsDefEqU` only and retype with `isDefEq_iff`* — `isDefEq_iff` is
   `IsDefEq.uniq`, at unbounded index.

**Why the sort conjunct was free and the Π conjunct is not.** `sortType_level` derives
"`.sort s`'s type is `.sort (succ s)`" from the invariant's *typing components*, because a
sort's type is determined by the term. A Π's **codomain conversion** `B ≡ B'` is determined
by no typing whatsoever — recovering it *is* Π-injectivity. Rebuilding
`HTS Γ (.forallE A B) (.sort (imax p q)) true (n-1)` from `forallE_inv'`'s components does
work and gives `u ≈ imax p q`, but `imax` is not injective and the conversion is not
recovered, so the conjunct cannot be discharged uniformly the way the sort one was.

### 3.3 Correction to the method the brief handed me **[analysis, and it bit]**

> *"Grep an open lemma's call sites inside proved theorems. If every call is on an IH output,
> it is a passenger, not a primitive."*

`forallE_inv_stratified` **passes this test** — its only user is `IsDefEq.uniq`, and the call
is on `ih3`'s output. It is still not a passenger. The test is **necessary, not sufficient**.
The missing clause:

> A conjunct can ride along only if it is **derivable from the invariant's own components**.
> Being reachable from an IH output says the *inputs* are in scope; it says nothing about
> whether the *conclusion* follows from what the invariant already carries. Check the
> derivation, not the call site.

That is the third method-level correction this corner has produced, after
`handoff-stratified.md` §5's criterion being wrong about verdicts twice.

### 3.4 Statement audit of `forallE_inv_stratified` **[machine]**

Asked for specifically, after four statements this session's predecessors found FALSE by
auto-bound implicits and by missing scope.

```
@IsDefEqU.forallE_inv_stratified : ∀ {env} {Γ} {U} {A B A' B' V} {n} {V'} {n'},
  env.WF → OnCtx Γ (env.IsType U) →
  env.IsDefEqU U Γ (A.forallE B) (A'.forallE B') →
  env.HasTypeStratified U Γ (A.forallE B) V true n →
  env.HasTypeStratified U Γ (A'.forallE B') V' true n' → …
```

* **Auto-bound implicits: clean.** Eleven variables, all used, none captured from anything
  unrelated. (`pp.all` output inspected; no stray section variable, no wrong-typed binder.)
* **Scope: clean.** This is the `descend` defect — a quantifier with no hypothesis on it.
  `V`, `V'`, `n`, `n'` are each constrained by `h2`/`h3`, and `n`, `n'` also appear in the
  conclusion. There is no under-constrained variable that the conclusion asserts something
  about.
* **The statement is TRUE**, not merely open: `piInvStrat_of` derives it from `SortUniq` and
  `PiInv`, both of which are theorems of Lean's type theory. So this is not a fourth
  refutation. **[machine, modulo the standard-ness of the two inputs]**

---

## 4. The `proofIrrel` closure, and why it no longer needs a human call

The previous version of this document put, at §9 item 1, "Decide whether to hypothesise
`SortUniq` in `Injectivity.lean` … it weakens what four consumers can assume. **Do not do
this unilaterally.**"

**That decision has evaporated.** `SortUniq` is a theorem here now — `WF.sortUniq'`, proved
in the same file, above the four consumers — so the four `proofIrrel` holes close by calling
`forallE_not_proof` / `sort_not_proof` (`Theory/Typing/NotProof.lean`, `SortUniq.lean`) at
`WF.sortUniq' henv`. **No statement gained a hypothesis. No consumer can assume less than
before.** **[machine]**

The one mechanical cost: each of the four `aux` inductions had to be generalised over
`OnCtx Γ (env.IsType U)`, because `SortUniq` is stated with a well-formed-context guard and
the inductions quantify over `Γ`. All four use their IH only at the same `Γ`, so the change
is a threaded argument, nothing more.

### 4.1 An honest regression **[machine]**

`forallE_inv` now **depends on `forallE_inv_stratified`**, via `WF.sortUniq'`. The previous
document's headline #1 — "`forallE_inv`'s in-family dependencies: 1 → 0" — is reversed.

Measured dependency matrix on this commit (forward closure over declaration *values*, scope =
all `Lean4Lean` modules, 13792 declarations):

```
  forallE_inv             -> [forallE_inv_stratified]
  sort_inv                -> [forallE_inv_stratified]
  sort_forallE_inv        -> [forallE_inv_stratified]
  const_forallE_inv       -> [forallE_inv_stratified]
  const_sort_inv          -> [forallE_inv_stratified]
  IsDefEq.uniq            -> [forallE_inv_stratified]
  uniqAux                 -> []                              (sorry-free)
  piInvStrat_of           -> []                              (sorry-free)
  sortUniq_of_piInvStrat  -> []                              (sorry-free)
  NormalEq.descend        -> [forallE_inv_stratified, forallE_inv, weakN_iff]
  IsDefEq.church_rosser   -> [… + descend]

  direct users of forallE_inv_stratified: {IsDefEq.uniq, piInvStrat_axiom}
```

**Is the regression real?** No, and §3.1 is why. Even before, closing `forallE_inv`'s `trans`
alone would not have yielded `SortUniq`: `piInvStrat_of` shows `PiInv` reaches `PiInvStrat`
only *with* `SortUniq`, and nothing in the tree produces `SortUniq` except
`forallE_inv_stratified`. The dependency edge that was added merely makes visible a knot that
was already there. **[analysis]** But if a future session wants `forallE_inv` independent
again — say to prove it from a reduction relation and harvest it standalone — the two-line
undo is to revert its `proofIrrel` case to `sorry`; nothing else in the file needs it.

---

## 5. What is *not* claimed, and what is inherited

* **Nothing here proves `SortUniq` unconditionally.** `WF.sortUniq'` is `sorryAx`-tainted
  through `forallE_inv_stratified` and always will be until that statement, or a
  normalisation result, lands. `#print axioms Lean4Lean.VEnv.WF.sortUniq'` says so.
* **Non-vacuity.** `VEnv.propLoop_sortUniq : propLoopEnv.SortUniq 0` still fires, at a
  proved-`VEnv.WF` environment whose head reduction provably has a two-cycle
  (`propLoop_headStep_not_wf`) — so the `SortUniq` route is not a normalisation argument in
  disguise. `propLoop_no_direct_collapse'` and `propLoop_zero_not_defeq_one'` are the
  discharged consumers. **[machine]**
* **`piInvStrat_of` gets no `_fires` witness, deliberately.** Its hypotheses are exactly the
  two open statements of this corner; any concrete environment small enough to check makes
  the conclusion provable directly, so a `_fires` theorem would be the tautology that
  `StrengthenWitness.lean` was corrected for twice. The anti-strawman check that *does* have
  content is `piInvStrat_axiom` / `piInv_axiom`: both typecheck, which machine-checks that
  the packaged `Prop`s are the two theorems' types verbatim.
* **`docs/handoff-descend.md` is inherited, not re-derived.** `NormalEq.descend` is
  machine-checked false at three of its five holes, and its refutation argument suggests
  `IsDefEq.church_rosser` is false for environments with a large-eliminating `Prop`
  inductive. This stream owns `ChurchRosser.lean` and **did not edit it**; nothing here
  builds on any of its results. Treat them as suspect.
* **The cone script's "users of X" lists are scope-limited** to the modules imported by the
  measuring file. `sort_forallE_inv` shows zero users above because `HeadReduction.lean` and
  `ConstInvWitness.lean` were outside that scope; they do use it.

---

## 6. What is still open in this file, unchanged

* **`const_app_inv`** — still `:= sorry`, still untouched, and the §7 analysis of the
  previous version stands: its `proofIrrel` case is *not* refutable without the `IsType` side
  condition, and `IsType` does not propagate into the induction (at `appDF` the sub-spine has
  a Π type). **Settle the invariant before writing anything.** `ConstInvWitness.lean`
  machine-checks that both side conditions are load-bearing.
* **`IsDefEqU.weakN_iff`** (`UniqueTyping.lean`) — genuinely independent of this family; see
  `docs/handoff-weakn.md` and `docs/handoff-descend.md` §5. Not touched.
* **`HasArgsDF.of_isDefEqU`** — the congruence-side twin of `SpineInv.lean`'s
  `HasArgs.of_mkApp`, still the last named gap before `pat_wf`'s ι case can be attempted end
  to end. Not written.

---

## 7. Corrections this session makes to existing documents

| document | claim | correction |
|---|---|---|
| `docs/handoff-sortuniq.md` §9 bullet 3 | the passenger move "may replace `forallE_inv_stratified` in `uniqAux` by the unstratified `forallE_inv` plus a re-stratification" | **It cannot.** §3.2. The re-stratification is fine; the level alignment it then needs is `SortUniq` at an index the induction hypothesis does not reach. |
| `docs/handoff-sortuniq.md` §9 bullet 2 | the census win is "a reordering, not a proof" | Correct, and it is done: 21 → 20. But it is not a *file* reordering — `CycleConv` and `ConstInvWitness` import `Injectivity`, so the development had to move *into* `Injectivity.lean`, not below it. |
| `docs/handoff-injectivity.md` (prev.) §9.1 | hypothesising `SortUniq` in `Injectivity.lean` "weakens what four consumers can assume … do not do it unilaterally" | Moot. `SortUniq` is proved in-file; the four holes closed with **no** statement change. §4. |
| `docs/handoff-injectivity.md` (prev.) §0.1, §4 | "`forallE_inv`'s dependency on `forallE_inv_stratified` is **gone**" / "in-family dependencies 1 → 0" | Reversed, deliberately, by §4. The independence was not worth what it cost: it bought nothing, because `PiInv` alone never reaches `SortUniq`. |
| `docs/handoff-injectivity.md` (prev.) §1 | "8 `sorry`s in `Injectivity.lean` + 1 in `UniqueTyping.lean`" | Superseded. The file's raw count went 12 → **6**; the census count 7 → **6**. |
| the brief's method note | "if every call is on an IH output, it is a passenger, not a primitive" | Necessary, not sufficient. §3.3. |

---

## 8. What to pick up first

1. **The corner now has exactly one mathematical residual, and it is normalisation.**
   Every open statement in `Injectivity.lean` except `const_app_inv` is one `trans` case
   away from done, and `forallE_inv_stratified` is one `SortUniq` away, and `SortUniq` is
   one `IsDefEq.uniq` away, and `IsDefEq.uniq` is one `forallE_inv_stratified` away. **The
   knot only opens at a reduction relation.** Nothing incremental remains here.
2. **The tree has no candidate reduction relation.** `ChurchRosser.lean`'s is refuted at
   `descend`; `HeadReduction.lean`'s has never had a confluence argument run over it;
   `RawDefEq.lean`'s three-place judgment is unexplored. Before anyone spends a session on
   Π-injectivity's `trans`, **price `HeadReduction.lean`** — it is the only untried one, and
   `docs/handoff-descend.md` §5 says so too.
3. **If you want to break the circle without normalisation**, the one place to look is the
   *measure*. `uniqAux` is a well-founded induction on the stratification index `n`, and the
   whole obstruction in §3.2 is that one derivation's index is not bounded by `n`. A
   different measure — lexicographic on (index, term size), say, since `uniqQ`'s recursive
   calls at `app`/`lam` are on strict subterms — might make the unbounded side reachable.
   **Not attempted, not priced.** It is a redesign of `IsDefEq.uniq`'s induction, and the
   `app` case's `IH` calls are on `B`, which is a subterm of the *type*, not of `e`. That is
   the first thing to check, and it may kill the idea outright.
4. **Do not** re-attempt §3.2's three escapes; each is written out above with the step where
   it returns to its own conclusion.
5. **Do not** route through `ChurchRosser`. `descend` is false; see `docs/handoff-descend.md`.
