# Handoff: `Theory/Typing/Injectivity.lean` and its family

Session result, written for whoever picks this up next. Claims are marked
**[machine]** (checked by `lake build` / `#print axioms` / the cone script on this commit)
or **[source]** (read off code or another stream's report, not independently re-derived).

Everything below was verified against a green build of
`Lean4Lean.Theory.Typing.{Injectivity, UniqueTyping, SpineInv, NotProof, ChurchRosser,
HeadReduction, ParamsWitness}` and `Lean4Lean.Verify.Typing.Lemmas`. One file in the tree is
red — `Lean4Lean/Verify/Typing/ProjLevelWitness.lean:150`, `simp made no progress` — it is
untracked, belongs to another stream, imports only `Theory/Inductive/{Lemmas,Structure}`,
and is unrelated to anything here. **[machine]**

---

## 0. Headline

Three results, in decreasing order of how much they change the plan.

1. **`IsDefEqU.forallE_inv` is not a second obligation beyond `sort_inv`.** It is now proved
   by a *direct* induction on `IsDefEqStrong` whose residual is **exactly `sort_inv`'s two
   holes** — `trans` and `proofIrrel` — and nothing else. Its dependency on
   `forallE_inv_stratified` is **gone**. **[machine]**
   The file's own docstring said Π-injectivity additionally needs universe uniqueness *in
   the structural cases*. That is true of the *stratified* statement and false of the plain
   one; §2 has the reason.
2. **The whole Π/sort disjointness family now has one shared residual pair.**
   `sort_forallE_inv` and `const_sort_inv` were bare `sorry`s; both are now written-out
   inductions closing 9 of 11 cases, leaving the same `trans` and `proofIrrel`.
   `forallE_not_proof` (new, **sorry-free** given `SortUniq`) supplies the Π half of the
   `proofIrrel` residual, so that half is machine-checked to be **one** obligation
   (`VEnv.SortUniq`), not two. **[machine]**
3. **The concrete missing declaration between `forallE_inv` and `pat_wf` now exists.**
   `VEnv.HasArgs.of_mkApp` (`Theory/Typing/SpineInv.lean`, new) — ledger row B7's inverse —
   is proved, non-vacuity-checked, and uses `forallE_inv` in exactly one place. **[machine]**

Nothing was refuted this session. Nothing was closed outright: `sort_inv`'s `trans` case
(normalisation) and `SortUniq` remain the two primitives, and everything in the family
reduces to them.

---

## 1. The 9-sorry inventory, as found

The brief said "9 `sorry`s in `Injectivity.lean`". **[machine] correction:** it was **8 in
`Injectivity.lean` + 1 in `UniqueTyping.lean`** = 9 across the owned files. They are:

| # | file:decl | what it is | family |
|---|---|---|---|
| 1 | `Injectivity` `IsDefEqU.sort_inv` — `trans` | `.sort u ≡ e ≡ .sort v`, `e` arbitrary | **normalisation** |
| 2 | `Injectivity` `IsDefEqU.sort_inv` — `proofIrrel` | a sort is not a proof | **`SortUniq`** |
| 3 | `Injectivity` `IsDefEqU.forallE_inv_stratified` | opaque `:= sorry` | stratified: normalisation + level alignment |
| 4 | `Injectivity` `IsDefEqU.sort_forallE_inv` | opaque `:= sorry` | (was unclassified) |
| 5 | `Injectivity` `IsDefEqU.const_app_inv` | opaque `:= sorry` | (was unclassified) |
| 6 | `Injectivity` `IsDefEqU.const_forallE_inv` — `trans` | middle term arbitrary | **normalisation** |
| 7 | `Injectivity` `IsDefEqU.const_forallE_inv` — `proofIrrel` | a Π is not a proof | **`SortUniq`** |
| 8 | `Injectivity` `IsDefEqU.const_sort_inv` | opaque `:= sorry` | (was unclassified) |
| 9 | `UniqueTyping` `IsDefEqU.weakN_iff` — `→` direction | anti-weakening / strengthening | **independent** |

Note `forallE_inv` itself was *not* in the list: it was a derived corollary of #3.

Cheapness at the time of the inventory, predicted with `docs/handoff-stratified.md` §5's
criterion **before** any work, and recorded here because the prediction held:

* #4 and #8 — *cheap*. Their inductions are the same shape as `const_forallE_inv`'s, whose
  nine closing cases were already written out; they were opaque only because nobody had
  typed them. Predicted: reduce to the same two holes, close nothing new. **Held.**
* `forallE_inv` (via #3) — *predicted expensive, and the prediction was wrong in the useful
  direction*: see §2.
* #5 — *medium and structurally different*; §5.
* #9 — *independent of the whole family*; §6.
* #1, #2 — the two primitives. Not attackable in this file.

---

## 2. `forallE_inv`: what changed and why the old analysis was about a different statement

**Before.** `forallE_inv` was `let … := forallE_inv_stratified …`, i.e. a corollary of #3.
`forallE_inv_stratified`'s docstring argued Π-injectivity needs *two* things: `sort_inv`'s
`trans` **and** universe uniqueness, the latter in the *structural* cases (`forallEDF`,
`symm`) rather than only in `proofIrrel`.

**That argument is correct about `forallE_inv_stratified` and does not transfer to
`forallE_inv`.** The stratified conclusion pairs each conversion `A ≡ A' : .sort u` with a
`HasTypeStratified` derivation of `A` *at that same `u` and at the index inherited from
`h2`*. The conversion's `u` comes from the derivation being inverted; the stratified
derivation's level comes from `HasTypeStratified.forallE_inv'`. Aligning them is the
universe-uniqueness demand. **The plain statement has no such conjunct**, so `forallEDF`
hands both halves back on the nose and there is no level to align. The stratified docstring
already recorded that both consumers *discard* those components; what was missed is that
discarding them removes the **obstruction**, not merely the payload.

**The one real difficulty was `symm`, and it is dissolved by strengthening the induction.**
Inverting `.forallE A' B' ≡ .forallE A B` gives the codomain conversion in `A'::Γ` while the
goal wants `A::Γ` — a context conversion, the same thing that blocks `DefInv` clause (2) and
`PropConvInv`'s `forallEDF` case. It is avoidable *here* because
`IsDefEqStrong.forallEDF` carries the codomain conversion **in both contexts**
(`Strong.lean:54–55`). Carrying both conjuncts through the induction makes `symm` close by
`IsDefEq.symm` alone; the extra conjunct is dropped at the end. **[machine]**

**After.** `IsDefEqU.forallE_inv` is a direct induction, 9 of 11 cases closed:

| case | how it closes |
|---|---|
| `forallEDF` | on the nose, both conjuncts and both contexts |
| `symm` | `IsDefEq.symm` on the strengthened conclusion |
| `defeqDF` | IH |
| `extra` | `VEnv.WF.instL_lhs_ne_forallE` |
| `bvar`,`sortDF`,`constDF`,`appDF`,`lamDF`,`beta`,`eta` | vacuous on the shape of the left endpoint |
| **`trans`** | **OPEN** — arbitrary middle term; identical in content to `sort_inv`'s |
| **`proofIrrel`** | **OPEN** — "a Π is not a proof" |

`#print axioms Lean4Lean.VEnv.IsDefEqU.forallE_inv` → `[propext, sorryAx, Classical.choice,
Quot.sound]`, and the cone script reports it now depends on **none** of
`forallE_inv_stratified`, `sort_inv`, `uniq`, `weakN_iff`, `descend`. **[machine]**

**Consequence for `forallE_inv_stratified`:** its direct-user set is now exactly
`{IsDefEq.uniq}`. **[machine]** Its extra strength over the plain form is the *index bound*:
`uniq`'s `app` case feeds `d4`/`d5` straight back into the well-founded recursion at
`n₂ ≤ n`, and `HasType.stratify` yields an unbounded index, so re-routing `uniq` through the
plain lemma is **not** a matter of bookkeeping. Do not attempt it without pricing the
measure. **[source: read of `UniqueTyping.lean:44–60`]**

---

## 3. `sort_forallE_inv` and `const_sort_inv`: opaque → the same two holes

Both are now written-out inductions. Statements **unchanged**. **[machine]**

* `sort_forallE_inv` — `extra` closes from *both* `instL_lhs_ne_sort` and
  `instL_lhs_ne_forallE`; every other structural case is vacuous on one endpoint's shape.
  Its `proofIrrel` residual is *weaker* than `sort_inv`'s: **either** "a sort is not a proof"
  **or** "a Π is not a proof" suffices, because both endpoints are in hand.
* `const_sort_inv` — mirrors `const_forallE_inv` exactly, `RuleFreeHead` + `headConst?` on
  the `extra` case and `spineHead` on the shape cases.

### The `proofIrrel` residual is one obligation, and that is now machine-checked

`Theory/Typing/NotProof.lean` (new, **no `sorry`**) proves, from `VEnv.SortUniq` as an
explicit hypothesis:

* `HasTypeStrong.forallE_type` — the type of a Π is a sort (the mirror of
  `HasTypeStrong.sort_type`, needing `huniq` in the same `defeq` case and for the same
  reason);
* `VEnv.forallE_not_proof` — a Π is not a proof.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]` — **sorry-free**.
**[machine]**

So the four `proofIrrel` holes across `sort_inv`, `forallE_inv`, `sort_forallE_inv`,
`const_forallE_inv` are all consequences of `VEnv.SortUniq` and of nothing else.
`SortUniq` itself remains a hypothesis with no instance, and `Theory/Typing/SortUniq.lean`
argues no *model* route to it can exist.

**Not wired in.** These four holes stay `sorry` in `Injectivity.lean` because closing them
would mean adding a `SortUniq` hypothesis to the four theorem statements — a weakening of
the public statements, which is not mine to do. The lemma is there for whoever decides that
trade is worth making; it is a two-line change per site.

---

## 4. Cone numbers, before and after

Measured with `scripts/cone-measure.lean`'s `deps` (i.e. `value? (allowOpaque := true)`, so
theorem bodies are followed — the `.thmInfo` trap is handled), over all 5089→5112 `Lean4Lean.*`
declarations reachable from `ParamsWitness + UniqueTyping + ChurchRosser + HeadReduction +
PatternRules`. **[machine]**

| declaration | transUsers before | after |
|---|---|---|
| `IsDefEqU.forallE_inv` | 45 | 45 |
| `IsDefEqU.forallE_inv_stratified` | 88 | 87 |
| `IsDefEqU.sort_inv` | 87 | 87 |
| `IsDefEqU.sort_forallE_inv` | 3 | 3 |
| `IsDefEq.uniq` | 86 | 86 |
| `IsDefEqU.weakN_iff` | 42 | 42 |

The user counts are unchanged — statements did not move. What changed is the **dependency
matrix**, and this is the number that matters:

```
                                depends on (within the family)
  BEFORE  forallE_inv          [forallE_inv_stratified]
  AFTER   forallE_inv          []
```

and, unchanged and re-verified this session:

```
  forallE_inv_stratified  []          paramsOfWF              []
  Pat.extra               []          patWF_of_deltaFragment  []
  IsDefEqU.weakN_iff      []
  IsDefEq.uniq            [forallE_inv_stratified, sort_inv]
  NormalEq.descend        [forallE_inv_stratified, sort_inv, weakN_iff, uniq, forallE_inv]
  IsDefEq.church_rosser   [… all of the above, + descend]
```

**Acyclicity, re-verified rather than relayed. [machine]** `forallE_inv`, `paramsOfWF`,
`Pat.extra`, `patWF_of_deltaFragment` and `IsDefEqU.weakN_iff` have **no path** to any member
of the family, so `forallE_inv → pat_wf → paramsOfWF → church_rosser` is a sound
*consumption* chain. **The converse is not available**: `church_rosser` depends on
`forallE_inv`, `sort_inv`, `uniq`, `weakN_iff` and `descend`, so **Church–Rosser cannot be
used to prove anything in this file.** Anyone planning to "get `forallE_inv` from
confluence" should stop here.

Direct users, for planning: **[machine]**

* `forallE_inv_stratified` → `IsDefEq.uniq` (one).
* `forallE_inv` → `InferType.exists`, `NormalEq.{descend, parRed, weakN_inv_DFC}`,
  `ParRed.{defeq, triangle}`, `ParRedExt.parRed_beta`, `StRed.triangle`.
* `sort_forallE_inv` → `IsDefEq.reduce_forallE`, `IsDefEq.reduce_sort`.
* `sort_inv` → those two plus `IsDefEq.uniq`, `ParRedExt.parRed_beta`.
* `weakN_iff` → `IsDefEq.skips`, `IsDefEq.weakN_iff'`, `IsDefEqU.weak'_iff`,
  `NormalEq.weakN_inv_DFC`, `ParRed.weakN_inv`, `ParRedExt.parRed_beta`,
  `hasType_app_bvar0`, `VExpr.WF.weakN_iff`.

---

## 5. `pat_wf`'s ι and quot cases, priced — and the bridge built

The brief asked, if `forallE_inv` closed, whether `pat_wf` follows. It did not close, so the
question was answered the other way: **what exactly stands between them.**

**[source: dedicated trace of `PatternRules.lean`, `ParamsBuild.lean`,
`StructureClosed.lean`, cross-checked against `docs/design-inductive.md` §7.3/B7/M1,
`docs/handoff-params.md`, and `Verify/Typing/Expr.lean:85–99`]**

The ι case fires `IsDefEq.extra` on `D.iotaRule j q C` and instantiates the resulting
`mkLams Δ L ≡ mkLams Δ R` with `VEnv.IsDefEq.extra_applied`
(`Theory/Inductive/StructureClosed.lean:347`). Every hypothesis of `extra_applied` is
available to `PatWF` **except one**: `hargs : HasArgs U Γ Δ as`. `PatWF` holds only
`HasType U Γ e A`, and peeling `e` with `HasType.app_inv` returns *existential* domains with
nothing tying them to the telescope `Δ` the rule declares. Reconciling the two is
`IsDefEqU.forallE_inv`. The quotient case has the same shape at size 5+3; `extra_applied`'s
own docstring already flags the `α`/`r` double-use as "a reconciliation obligation, not
bookkeeping".

The bridging declaration existed **nowhere in the tree** — not as a proof, not as a
statement. It now does:

**`Lean4Lean/Theory/Typing/SpineInv.lean` (new), all [machine]:**

* `HasType.mkApp_head` — the head of a typed spine is typed. **Sorry-free**
  (`[propext, Quot.sound]`).
* `HasType.mkApp_arg` — the first argument is typed, at *some* domain. **Sorry-free.**
* **`VEnv.HasArgs.of_mkApp`** — ledger row **B7, inverse direction**:
  `as.length = As.length → Γ ⊢ f : mkPi As B → Γ ⊢ f.mkApp as : A → HasArgs U Γ As as`.
  Axioms: `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` is **entirely**
  `forallE_inv`, used in **exactly one place** (pinning `app_inv`'s invented domain `A₀'` to
  the declared `A₀`).
* `HasType.mkApp_inv` — B7's inverse as the ledger states it: additionally
  `IsDefEqU U Γ A (instAll B as)`.
* `HasArgs.of_mkApp_fires` — **non-vacuity**, per the project's acceptance criterion: the
  five hypotheses are jointly satisfiable at a genuine one-argument application
  (`(λ (x : Prop). x) (bvar 0)` over `Γ = [.sort .zero]`), in **every** `VEnv.WF`
  environment and at every universe count. No constants needed, so it is not
  environment-specific the way `CycleConv.propLoopEnv` witnesses are.

The induction is on the **spine**, not the telescope — the recursive call is about
`instTele a As`, a different list of the same length, so an induction on `As` has a vacuous
hypothesis exactly there. (Companion test, applied and it bit.)

**What remains between `of_mkApp` and `pat_wf`'s ι case [source]:** the congruence half —
bridging `instAll L as` to the matched `e` through `IsDefEq.constDF`/`mkAppDF`, whose
premises want `IsDefEq … A` at the function's domain while `Check.OK` supplies only
`IsDefEqU`. Retyping is `isDefEq_iff`, i.e. `uniq` again. A `HasArgsDF.of_isDefEqU`
companion is the analogous missing declaration and has not been written. Note also that ι/quot
therefore inherit **`sort_inv` as well as `forallE_inv`** — `ParamsBuild.lean:29–31` and
`docs/handoff-params.md` name only `forallE_inv`, and that is an undercount.

---

## 6. `IsDefEqU.weakN_iff` — the ninth sorry, and it is not in this family

`UniqueTyping.lean:174`, the strengthening (→) direction of
`IsDefEqU Γ' (e1.liftN n k) (e2.liftN n k) ↔ IsDefEqU Γ e1 e2`.

**[machine]** It depends on nothing in the Π/sort family, and eight declarations depend on
it, including `NormalEq.weakN_inv_DFC` — which is why `NormalEq` and everything above it is
tainted independently of `sort_inv`.

**[analysis, not machine-checked]** By the §5 criterion it is in the normalisation family
*as a statement*: induct on the conversion and `trans`'s middle term need not be a lift, and
the conclusion is asserted of the endpoints. The standard proof routes through confluence
(both sides reduce to a common term; reduction preserves `Skips`), which is circular here.
The §2 trick does not obviously apply — there is no `IsDefEqStrong` constructor that carries
the strengthened form in two shapes at once. **Not attempted this session. Do not assume it
is cheap because it is one line.**

---

## 7. `const_app_inv` — the remaining opaque statement, and why it was left

`Injectivity.lean`, `List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ IsDefEqU as as'` for two
applications of the same rule-free constant. Still `:= sorry`.

**[analysis]** Its induction closes the same way as its siblings on `constDF` (base case),
`appDF` (spine step, with list bookkeeping), `symm`, `defeqDF`, `extra` (`RuleFreeHead`), and
every shape case via `spineHead`. Two obstacles, and the second is a *design* question, not
a proof step:

1. `trans` — the family's hole.
2. `proofIrrel` — **not refutable without the `IsType` side condition**, and `IsType` does
   **not** propagate into the induction: at `appDF` the sub-spine `f` has type
   `.forallE A B`, which is not a sort, so `IsType f` is false in general. Threading it
   requires a different auxiliary invariant than the one the siblings use.

That is why it was not converted to labelled holes: doing so naively would have produced a
*fourth wrong statement* of the kind the module docstring warns about. Whoever takes it
should decide the invariant first. `ConstInvWitness.lean` machine-checks that both side
conditions are load-bearing, so neither can be dropped to make the invariant easier.

---

## 8. Bookkeeping the orchestrator must see

**Raw `sorry` token count in `Injectivity.lean` went 8 → 13.** No statement was added,
weakened, or changed; no new obligation was admitted. The rise is because **three theorems
moved from one opaque `:= sorry` each to a written-out induction with two labelled holes
each** (`sort_forallE_inv`, `const_sort_inv`, and `forallE_inv`, which previously had *zero*
of its own and inherited one). The metric that fell is the one that matters:

| metric | before | after |
|---|---|---|
| opaque `:= sorry` statements in `Injectivity.lean` | 4 | **2** |
| distinct residual *contents* in the file | 4 opaque + 4 labelled | **2 opaque + `trans` + `proofIrrel`** |
| `forallE_inv`'s in-family dependencies | 1 | **0** |
| sorry-free new lemmas added | — | **5** (`forallE_type`, `forallE_not_proof`, `mkApp_head`, `mkApp_arg`, plus the non-vacuity firing) |

New files, both leaves, imported by nobody yet:
`Lean4Lean/Theory/Typing/NotProof.lean`, `Lean4Lean/Theory/Typing/SpineInv.lean`.

---

## 9. What to pick up first

1. **Decide whether to hypothesise `SortUniq` in `Injectivity.lean`.** It is a public-statement
   change (four theorems gain a hypothesis) and needs a human call. If taken, four of the
   remaining holes close *today* from `sort_not_proof` and `forallE_not_proof`, and the
   entire Π/sort family collapses to `sort_inv`'s single `trans` case. This is the largest
   available step and it costs no new mathematics. **Do not do it unilaterally** — it weakens
   what four consumers can assume.
2. **`HasArgsDF.of_isDefEqU`** — the congruence-side twin of `of_mkApp`, and the last named
   gap before `pat_wf`'s ι case can be attempted end to end. Same shape, same ingredients
   (`isDefEq_iff`), and it will be equally sorry-tainted and equally worth landing.
3. **`NormalEq.descend`, priced** [source, from a dedicated read of `ChurchRosser.lean`]:
   exactly **five** `sorry`s, all in the `appDF` case (`:1769, 1779, 1784, 1799, 1801`).
   Two of them (E3, the "function is a proof" branches) are *already written out and
   machine-checked* as `NormalEq.appDF_proofIrrel:1342` — they need only that `descend`'s
   signature gain the `hsu` universe-uniqueness argument, threaded to
   `appDF_extra_of_descend` and `NormalEq.parRed`. That is `SortUniq` again, third sighting.
   The other three (E5) are a genuinely different kind of fact — `pat_major_not_pi` and
   friends, which `Theory/Inductive/Lemmas.lean:150` records as **not existing anywhere in
   the tree**, not even as statements; the shortest route to them runs through
   `const_forallE_inv` and is therefore circular with confluence, and the non-circular route
   (per rule shape, from `VEnv.RuleShape`) has never been tried.
   **But**: `descend` is *already* tainted through `uniq` and `weakN_iff` regardless, so
   "five sorries from a sorry-free `descend`" is false. Do not price it as five.
   Also: `ChurchRosser.lean:1872–1880` still claims `appDF_extra_of_descend` has a `sorry`;
   it has none, and `:1568` in the same file says so. Stale docstring.
4. **`const_app_inv`** — settle the `IsType` invariant question in §7 before writing anything.
5. **`weakN_iff`** — genuinely independent; worth a separate scouting pass, and worth *not*
   assuming it is easy.

