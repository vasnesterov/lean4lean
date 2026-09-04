# handoff-binderscan — deleting `hlen` from `PosIndex.recArgOf_binders_noBlock`

Stream: BinderScan. Started 2026-09-04, HEAD `42925b4` (bare build green 1667 jobs, guards 1/2/3 ✓, census 13).

Owned: `Lean4Lean/Verify/Inductive/BinderScan.lean` (new), `Lean4Lean/Verify/Inductive/PosIndex.lean` (existing),
`docs/handoff-binderscan.md` (this file).

Target: prove "the loop scans every `VExpr` binder" and thereby **delete** the hypothesis
`hlen : r.binders.length ≤ t.consumeMData.piArity` from `PosIndex.recArgOf_binders_noBlock`.

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `PosIndex.lean`, `PosReach.lean`, or `docs/handoff-posreach.md` in this session.**
Answers appended below the questions, once measured. Filled answers are never edited; corrections go in §2.

### The four shape questions, instantiated

**Q1. Does the target exist — by *conclusion head*, not by obligation name?**
The theorem I intend to prove is "the binder-scanning loop visits every binder of the `VExpr`
translation". Its conclusion head is *not* `recArgOf_binders_noBlock`. What is the conclusion head
of the general theorem — is it a statement about `posBinderDoms` (a collector over `Expr`)
being related to a `VExpr` binder telescope, or about `piArity`/`length`? Does something with that
conclusion head already exist in the repo (perhaps for a restricted `Expr` constructor set, or under
a different name in `PosReach.lean` / `Theory/Inductive/*`), so that "prove it" is really "generalise
an existing lemma's constructor coverage"?

**Q2. Is the work in the direction I think?**
The two prior rounds framed the obstruction as: `.mdata` is cheap (done), `.letE` is not
(`posBinderDoms (b.instantiate1 v)` is non-structural; the `TrExprS` side is a `vlet` *context*
entry), plus `whnf`'s zeta and δ. Is `hlen` actually *used* in the proof body in a way that a
constructor-complete scan lemma discharges — or is `hlen` load-bearing for something else
(e.g. an index-arithmetic side goal, an `Array.get` bound, a termination argument) that survives
the scan theorem? Concretely: **which goals in the current proof consume `hlen`, and how many?**

**Q3. Measurement or docstring?**
Which of my beliefs about this target come from *docstrings/handoff prose* versus from *measurement*?
Specifically: is the claim "`.mdata` clause is now cheap" measured (a lemma that compiles) or prose?
Is "`whnf` zeta and δ owe the same collector a story" measured (a concrete failing goal I can see)
or a prediction by a prior round? I must classify each before believing it.

**Q4. What does the implementation compare with, and is it opaque?**
Where in this path does the implementation branch on a comparison? `BEq Expr` is `Lean.Expr.eqv`,
`@[extern] opaque`, alpha-equivalence only, **not `decide`-able at any closed input**. Also
`Nat` comparisons (`≤` on `binders.length` vs `piArity`) are decidable but the *loop* may branch on
a `Name` equality or an `Array.any`, both of which defeated `decide` in `PosReach`. So: does the
binder-scanning loop's termination/branching go through an opaque comparison, and if so is the
correct move to *restate around* it (preferred — closeness to the C++ kernel outranks a smaller
trusted base) rather than replace it?

### Numbered predictions, made cold (blank — to be filled from measurement)

- **P1.** `hlen` is consumed by exactly ___ goal(s) in the current proof body.
  Prediction: **1** — a single `Nat` bound feeding an index/length step. If it is >1 the deletion is
  a multi-site job and the scan theorem alone is insufficient.
- **P2.** The `.letE` clause is **unproved, not false**. Prediction: unproved. Confidence: medium-high.
  Falsifier I will look for: a closed `Expr` with a `.letE` whose `posBinderDoms` misses a binder
  that the `VExpr` side has — i.e. an actual counterexample, which would mean `hlen` cannot be deleted
  and must instead be *justified* at each call site.
- **P3.** The general theorem is **not** unconditionally true: it needs the checker's rejection
  (`checkPositivity_reject`) as a side condition for at least one constructor, exactly as the
  `.mdata` tripwire case does. Prediction: **true** — the `.fvar` (let-bound) case will need it or
  a well-formedness hypothesis. Consequence if true: `hlen` is replaced by a *different*
  hypothesis rather than deleted, and I must say so rather than claim victory.
- **P4.** Cheapest instrument: instantiating the universally quantified numeral at its extremes.
  Here the numeral is `r.binders.length` (and `piArity`). Prediction: **`length = 0` is trivial and
  `length = piArity` (the boundary) is where the real content sits**; and I predict that testing
  `length = 0` and `length = piArity` will reveal whether `hlen` is used as `≤` or effectively as `=`.
  If the proof only ever needs the boundary case, `hlen` may be deletable by *strengthening the
  conclusion* instead of proving the scan theorem.
- **P5.** The `#eval` tripwire in `PosReach.lean` §4 stays load-bearing after deletion.
  Prediction: **it does not** — if the scan theorem is constructor-complete, `.mdata` descent becomes
  a *proved* step rather than an assumed one, and the tripwire guards a fact that is now a theorem.
  In that case I must add a *new* guard for whatever the new load-bearing fact is, or keep the old
  tripwire and state honestly that it now guards a theorem (defence in depth, not a rescue).
- **P6.** Cost/outcome. Prediction: **a third** — `.mdata` + the structural constructors
  (`app`/`forallE`/`lam`/`sort`/`const`/`bvar`/`lit`/`proj`) close; `.letE` and the let-bound `fvar`
  case do not, and I land with `hlen` weakened to a `.letE`-free or context-free side condition
  rather than deleted.

---

## §2 — Answers, measurements, and corrections (append-only)

### A1 / P1 — `hlen` is consumed at **two** sites, not one. (measured, 2026-09-04)

Read of `PosIndex.lean`:405-449 (`recArgOf_binders_noBlock`'s body). `hlen` occurs twice, in the two
arms of `recArgOf_binders_piBinderDoms`' disjunction:

| site | arm | what `hlen` does |
|---|---|---|
| 1 | `r.binders = S.piBinderDoms` | supplies `hn : S.piArity ≤ t.consumeMData.piArity`, the input to `TrExprS.splitPis_noConsts` |
| 2 | `S.piArity = 0` | with `H'.piArity_le` forces `r.binders = []`, making the goal vacuous |

**P1 was wrong (predicted 1).** The consequence is the one P1 flagged: the scan theorem alone is
**not** sufficient. Site 2 is a *different* obstruction, and one the brief does not name.

### A1b — the obstruction the brief does not name: `betaHead`. (measured, same read)

`VInductDecl'.recArgOf`'s second stage runs `VIndRestore.recog` at `VExpr.betaHead S`. §4.1's
docstring argues `betaHead` is the identity on a `forallE`, so "the only way stage 2 can produce
binders that `S` does not have is for `S` to be a head redex — and then `S.piArity = 0`, which §4.2's
hypothesis already collapses."  That is exactly site 2: **`hlen` is what collapses it.** Delete `hlen`
and a head β-redex `S` — e.g. `S = (fun _ : I => ∀ _ : I, I) a`, whose `piBinderDoms` is `[]` and whose
`betaHead` has binder `I` — reappears as an open case. `posBinderDoms t` cannot see it either
(source `.app`), so this is the **β twin of §3.2's `.mdata` witness**, and like it, it must be killed
by the checker's rejection (`whnf` β-reduces before scanning), not by a collector.

So the honest work list is **three** clauses, not two: the `.mdata`/`.letE`/`fvar` collector clauses
*and* a head-β clause at site 2.
### A2 / Q1+Q3 / P2 — the two dictionaries the brief called missing **already exist**, hole-free. (measured 2026-09-04)

Searched by conclusion head, not by name (`grep "TrExprS.*instantiate1"`), and found in
`Lean4Lean/Verify/Typing/Lemmas.lean`:

* **ζ (the `vlet`↔`ldecl` dictionary):** `TrExprS.inst_let` (:2280)
  `(henv : Ordered env) (H : TrExprS env Us ((none, .vlet A₀ e₀') :: Δ) e e') (h₀ : TrExprS env Us Δ e₀ e₀') : TrExprS env Us Δ (e.instantiate1' e₀) e'`
  — the **VExpr side is unchanged** (`e'`), the `Expr` side is ζ-substituted. Exactly the shape the
  `.letE` clause of the bridge needs. Proved via `TrExprS.instN_let` / `VLCtx.InstLet` (:488).
* **β:** `TrExprS.inst` (:2189) `… TrExprS Δ (e.instantiate1' e₀) (e'.inst e₀')` — the VExpr side is
  `e'.inst e₀'`, which is what `VExpr.betaHead` produces at a head redex.

**Q3's answer, then: the claim "the `.letE` clause needs R1/R2's `vlet`↔`ldecl` dictionary, and that is
the expensive part" was *prose*, not measurement.** The dictionary is upstream of `PosIndex` in the
import closure and needs only `Ordered env`. Two rounds costed the `.letE` clause without grepping for
its conclusion head.

**P2 revised, and this is the round's central correction.** The `.letE` difficulty is **not** in the
`Expr`→`VExpr` bridge — `inst_let` closes it. It is in the **checker→certificate** direction: turning
`checkPositivity.loop`'s success at a `.letE` into evidence about the ζ-*reduct*, which needs
`whnf`'s ζ step as an equality of `M Expr` values (the `.letE` arm of `whnf'` falls **through** to the
`whnfCache` lookup, unlike the `.mdata` arm which returns before it — that asymmetry is why
`whnf_mdata` was cheap and ζ is not).

### A3 — δ and β owe the collector **nothing**. (measured, by case analysis on `TrExprS`)

The brief inherits "whnf's zeta and δ owe the same collector a story". **Measured false for δ, and for
β at the binder telescope.** The obligation `∀ A ∈ S.piBinderDoms, NoConsts Sn A` is **vacuous unless
`S` is a `.forallE`**, and `TrExprS`'s constructors fix which `Expr` heads can produce a `.forallE`:

| `t`'s head | `S` | `S.piBinderDoms` | whnf step whnf would take | owed? |
|---|---|---|---|---|
| `.forallE` | `.forallE` | non-empty | none (`whnf_forallE`) | yes — have it |
| `.mdata` | unchanged | may be non-empty | mdata-strip | yes — have it (`whnf_mdata`) |
| `.letE` | `body'` | may be non-empty | **ζ** | **yes — the residual** |
| `.bvar`/`.fvar` | the `VLCtx` entry | may be non-empty | local δ | **no** — `hctx` supplies it directly |
| `.const` | `.const` | `[]` | global δ | **no** — vacuous |
| `.app` | `.app` | `[]` | β, ι, Nat, native | **no** — vacuous |
| `.lam` | `.lam` | `[]` | none | **no** — vacuous |
| `.sort` | `.sort` | `[]` | none | **no** — vacuous |
| `.lit` | `l.toConstructor`'s image | `[]` (via `hlit`) | Nat/String | **no** — `hlit` gives a whole-term miss |
| `.proj` | `D.projTerm …` | `[]` if `projTerm` is app-headed | ι | **no** — vacuous (to be checked) |
| `.mvar` | — | — | — | **no** — `TrExprS` has no `.mvar` constructor |

So the whole general theorem reduces to **exactly one** whnf obligation, ζ, plus the already-cited
`whnf_forallE` and `whnf_mdata`. The `.fvar` local-δ case that the brief called a hard part is
**free**: `recArgOf_binders_noBlock` already carries `hctx`, which covers `vlet` entries because
`VLCtx.find?` on a `vlet` returns the *value*.
### A4 — **the general theorem is PROVED, hole-free.** (measured 2026-09-04)

`Lean4Lean.TrExprS.piBinderDoms_noConsts` in `Lean4Lean/Verify/Inductive/BinderScan.lean`:

```
(henv : VEnv.Ordered env) (hpS) (hlit) (hproj) :
  ∀ {t : Expr}, ScanCert p t → ∀ {Δ : VLCtx} {S : VExpr}, TrExprS env Us Δ t S →
    (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x) →
    ∀ A ∈ S.piBinderDoms, VExpr.NoConsts Sn A
```

**No arity hypothesis.** Induction on the certificate, `TrExprS` inverted at each node; twelve cases,
all closed. The `.letE` case is one line — `ih (hbody.inst_let henv hval) hctx`. `hpS`/`hlit`/`hproj`
are `TrExprS.noConsts`' own three side conditions (already hypotheses of the target theorem);
`henv : VEnv.Ordered env` is new and is used **only** by the `.letE` case.

Supporting lemmas, all `rfl`-level: `VExpr.piBinderDoms_eq_nil`, `VExpr.noConsts_piBinderDoms`,
`VInductDecl'.projTerm_ne_forallE` (a projection translates to a recursor *application*, so `.proj` is
vacuous — the last of the twelve heads to be settled, and settled by `VExpr.mkApp_ne_forallE`).

So the whole difficulty has moved to **one place**: producing `ScanCert p t` from
`checkPositivity stats t ctor idx cx = .ok u`.
### A5 — the checker→certificate direction is **also** hole-free, on the `.letE`-free path. (measured)

`Lean4Lean.AddInductive.checkPositivity_loop_scanCert` / `checkPositivity_scanCert`
(`BinderScan.lean` §5): `scanShapeNoLet t = true → checkPositivity stats t ctor idx c = .ok u →
ScanCert p t`, where `scanShapeNoLet` forbids a `.letE` **only on the descent path** (head `.mdata`,
pi codomains) — nothing is said about domains, let-values, or anything under an `.app`.

Structure: fuel induction, with a **structural** recursion on `t` nested inside the successor step,
because `checkPositivity_loop_mdata` is an equality at the *same* fuel. The pi step needs
`ScanCert.unsubst_fvar` (§4), reading the loop's `body.instantiate1 (.fvar fv)` evidence back to
`body`; that is structural on the `.mdata`/`.forallE` skeleton and is **exactly** where
`scanShapeNoLet` is spent — un-substituting through §2's `.letE` clause would need the σ-composition
`(b[fvar v]_{d+1})[v'[fvar v]_d]_0 = (b[v']_0)[fvar v]_d`, and the tree has only the adjacent-index
form `Lean4Lean.instantiate1'_instantiate1'` (`Verify/Expr.lean`:1116).

**So the ζ residual has moved.** It is no longer "the bridge cannot cross a `vlet`" (it can — §3) and
no longer "`whnf`'s ζ step needs an `M`-value equality" (not needed — the certificate absorbs it).
It is now a **de Bruijn σ-composition lemma at non-adjacent indices**. That is a much smaller and
much better-localised obligation than either round predicted.

**No δ, β, ι, Nat or native reduction appears anywhere in §5.** Confirmed by construction: the eight
other heads discharge by their trivial `ScanCert` clause.

### A6 / P4 — the cheapest instrument paid off, and it was the **`0` extreme**. (measured)

`hlen` is `r.binders.length ≤ t.consumeMData.piArity`. Instantiating the right-hand numeral at `0`
produced the refutation directly: a `t` with `t.consumeMData.piArity = 0` whose translation has
`piArity = 1`. `Lean4Lean.hlen_not_derivable` (`BinderScan.lean` §7):

```
Δ = [(none, .vlet (.sort .zero) (.forallE (.sort .zero) (.const I [])))],  t = .bvar 0,
S = .forallE (.sort .zero) (.const I []),  r.binders = [.sort .zero]
```
satisfies **every** hypothesis of `PosIndex` §4.2 — `TrExprS`, `hctx`, and
`checkPositivity stats t ctor idx cx = .ok ()` as a *real monadic value* — while `hlen` is false and
the conclusion is true. **So `hlen` was never derivable from `hchk`.** Both prior rounds' stated plan
("discharge `hlen`") was impossible; only changing what the `Expr` side certifies could work.

`.bvar` was chosen over `.fvar` on purpose: `whnf'`'s **first** match arm returns a `.bvar` unchanged
before the cache and without consulting a `LocalContext`, so `checkPositivity`'s success needed only a
new `whnf_bvar` (the positive twin of `whnf_forallE`) and no R1/R2 machinery at all.

### A7 / P5 — the tripwire, and what is load-bearing now. (measured)

**`PosReach` §4's tripwire is untouched** (not my file, and still meaningful: it guards `PosIndex` §4.2,
which stays in the tree, and it is the live check that `addDecl` routes through `checkPositivity`).

But the load-bearing set **has** changed, and P5 was right about the direction. For
`recArgOf_binders_noBlock_noLen` the `.mdata` descent is no longer an assumed behaviour: `whnf_mdata`
and `whnf_forallE` are theorems read off `whnf'`'s source, so a change there breaks the **build**, not
the statement. The one behavioural debt that remains is the `.letE` path, and it was previously
guarded by nothing. So `BinderScan` §8 arms a **new** tripwire on exactly it, and it is not decoration:

| measured at `Lean4Lean.addDecl`, 2026-09-04 | result |
|---|---|
| `scanShapeNoLet` of the positive `let`-headed field `let β := α; (_ : β) → W α` | `false` (by `rfl`) |
| `addDecl` on that declaration | **ACCEPTED** |
| `addDecl` on `let β := α; (_ : W α) → W α` | **REJECTED** |

The first two rows together are the point: §6's new hypothesis excludes a shape that the checker
**actually accepts**, so the residual is real rather than vacuous. The third says the clause §5 cannot
yet prove is plausibly *true* — a proof gap, not a bug. Both arms `throwError` if they flip.

### A8 / Q4 — the opaque, and a third way `decide` fails. (measured)

`Lean.Expr.eqv` (`@[extern] opaque`, alpha-equivalence only) **never appears on this path**: the
branching this file reasons about is `hasIndOcc` (an `anySub`, pure) and `Nat` comparison. Nothing was
restated around an opaque and nothing was replaced, so `CLAUDE.md`'s ordering (closeness to the C++
kernel outranks a smaller trusted base) is not engaged.

`decide` was tried once, at §7's `¬ (r.binders.length ≤ t.consumeMData.piArity)`, and **failed** —
`"Expected type must not contain free variables"`, because the `VIndRecArg` record carries the free
index `κ`. Discharged by `Nat.not_succ_le_zero` instead. That is a **third** distinct `decide` failure
mode on this path, alongside the free `Name` and the `Array.anyM.loop` cases `PosReach` §5(c) records.
No `decide` was regressed.

---

## §3 — Scorecard on §1's cold predictions

| # | prediction | outcome |
|---|---|---|
| P1 | `hlen` consumed at exactly **1** site | **wrong** — 2 sites; and the second (`betaHead`) is an obstruction no brief named |
| P2 | the `.letE` clause is unproved, not false | **right** (§8's tripwire measures it), but the difficulty was in a different place than predicted: the *bridge*'s `.letE` is one line |
| P3 | the general theorem needs the checker's rejection as a side condition, so `hlen` is replaced not deleted | **half right** — §3 is fully unconditional (no rejection anywhere), yet §6 does keep two hypotheses, so "not a clean deletion" was the right call for the wrong reason |
| P4 | instantiate the numeral at its extremes; `0` and the boundary carry the content | **right, and it was the whole refutation** (§7) |
| P5 | the `PosReach` tripwire stops guarding an unproved load-bearing fact | **right**, and a new tripwire was armed on the fact that replaced it (§8) |
| P6 | "a third": `.mdata` + structural heads close, `.letE` and the let-bound `fvar` do not | **amount right, identity wrong in a favourable direction** — `.letE` closed in the bridge, the let-bound `fvar` was *free*, and what did not close is a de Bruijn σ-composition plus the head-β branch |

Four of six substantially right. The one that mattered most (P4) was the cheap instrument, and the one
that was most wrong (P1) was wrong because I predicted from the theorem's *statement* instead of
counting occurrences in its *body* — a 30-second measurement I should have made before predicting.

## §4 — Where the residual now sits, exactly

1. **`instantiate1'` σ-composition at non-adjacent indices**:
   `(b[fvar v]_{d+1})[v'[fvar v]_d]_0 = (b[v']_0)[fvar v]_d`. `Verify/Expr.lean`:1116
   (`instantiate1'_instantiate1'`) has only the adjacent form `(j+1, j)`. Hand-checked true at
   `d ∈ {0,1}` and `e1 ∈ {bvar 0, bvar 1, bvar 2}` before this round stopped; the proof should mirror
   `instantiate1'_instantiate1'`'s. **With it, `scanShapeNoLet` disappears from §4, §5 and §6.**
2. **The head-β branch (`hβ`)**: `VExpr.betaHead` can expose binders `S` itself does not have, via
   `VInductDecl'.recArgOf`'s stage 2. The `VExpr`-side dictionary exists (`TrExprS.inst`,
   `Verify/Typing/Lemmas.lean`:2189, whose target *is* `e'.inst e₀'`); missing is the `Expr`-side step
   at `.app (.lam ..) a`, i.e. a `ScanCert` β clause plus §5's case for it. Independent of (1).

Nothing else. In particular **do not** build a whnf-closed binder-domain collector, and **do not**
price `whnf`'s ζ step as an `M Expr` equality: §3's case analysis (A3) shows δ/β/ι/Nat/native owe
nothing, and the certificate absorbs ζ.

## §5 — Method gaps, stated against myself

* **I predicted from statements, not bodies.** P1 cost me the `betaHead` obstruction for the whole
  orientation phase. Counting occurrences of the hypothesis in the proof body is cheaper than any
  prediction and should precede predicting.
* **I did not grep by conclusion head before believing two rounds of handoff prose.** `TrExprS.inst_let`
  had been sitting in `Verify/Typing/Lemmas.lean` the entire time. The rule "measurement or docstring"
  exists precisely for this and I applied it late — after writing §1, but only because §1 forced the
  question.
* **The `.proj` head was the last vacuity I checked and the one I nearly assumed.** It resolved by
  `VExpr.mkApp_ne_forallE`, but I had no argument for it until I read `projCore`'s body. Assuming it
  would have been a hole disguised as a `rfl`.
* **`hβ` is stated, not investigated.** I did not measure whether a head-β-redex field type is
  *reachable* through `addDecl` — the analogue of `PosReach` §4 for the β branch. That measurement is
  cheap (a `#eval` on `.app (.lam ..) a`-headed field) and a successor should make it before pricing (2).
* **Build cost.** Bare `lake build` **green at 1668 jobs**, guards 1/2/3 ✓ (guard 2 still
  "proof INCOMPLETE: sorryAx present", unchanged), **census 13**, **zero warnings** in either owned
  file. Measured 2026-09-04 on a tree that also picked up another stream's commit `09980a3`
  (`InductMap.lean`) mid-round; the brief's baseline of 1667 and my 1668 therefore differ by less than
  the two new files, so **treat 1668 as the measurement and 1667 as possibly stale** rather than
  inferring a job-count delta from it. New axioms in the cone: none beyond
  `Lean.Expr.instantiate1_eq`, already on guard 1's whitelist.
