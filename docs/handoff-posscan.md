# `docs/handoff-posscan.md` — closing `posSyn_of_recArgOf`'s three-part decidable check

Round of **2026-09-04**.  Owned files: `Lean4Lean/Verify/Inductive/PosScan.lean` (new), this file.
HEAD at start `e0aee76`, verified green by a bare `lake build`: **1659 jobs, exit 0, 2026-09-04**.

Target, from `Verify/Inductive/WFPos.lean` §3.1: `VIndField.posSyn_of_recArgOf` gives all five
syntactic conjuncts of `VIndField.WF.pos`'s `some` branch from B6's reader **plus three assumed
hypotheses** —

* **(A)** `hlen : r.args.length = (D.types.getD r.idx default).indices.length` (index arity)
* **(B)** `hbind : ∀ B ∈ r.binders, D.NoBlock B` (the binder scan)
* **(C)** `hargs : ∀ a ∈ r.args, D.NoBlock a` (the residual scan)

WFPos's own one-line statement of the gap: *"`recogAt` performs no `NoBlock` scan."*  The job is to
supply (A), (B), (C) from what `Lean4Lean/Inductive/Add.lean` actually does — `checkPositivity`'s
`hasIndOcc` calls and `isValidIndAppIdx`'s residual scan — rather than assuming them.

## §1 Priors — written 2026-09-04 before writing any Lean, never edited afterwards

### Shape prior S1 — does the target already exist?  (searched by conclusion head, not by name)

The obligation is called `posSyn_of_recArgOf`'s hypotheses; nothing that discharges them need
contain `posSyn`, `pos`, or `WF`.  Conclusion heads I will search: **`VInductDecl'.NoBlock`** (for B
and C), **`Lean4Lean.hasIndOcc`** (the implementation side), and the arity equation has no single
head so I will search `VIndRecArg.args` + `VIndType.indices` together, and `VInductDecl'.recArgOf`
+ `VIndRecArg.args` for a reader-side arity lemma.

**Prediction.** `NoBlock` will have *many* producers — I expect ≥ 10 — but essentially all of them
either `decide` instances / concrete-block firings or `NoBlock`-preservation plumbing, and **none**
concluding `NoBlock` from an implementation success.  `hasIndOcc` I predict has **zero** theorems
about it anywhere in `Verify/` (definition plus call sites only), because if a `hasIndOcc` success
lemma existed WFPos would have cited it instead of assuming (B) and (C).  For (A) I predict there
*is* a reader-side arity lemma or near-miss — `recArgOf` computes `args` as a `drop`, and B6 already
proved `recArgOf_idx_lt`, so an arity sibling is the obvious thing to have written next; I give that
40%.  If it exists, part (A) is free and the round is about (B) and (C) only.

### Shape prior S2 — is the work in the direction I think it is?

I believe the deliverable is *two halves meeting at a bridge*: an implementation-side theorem
"`checkPositivity` / `isValidIndAppIdx` returned `.ok` ⇒ `¬ hasIndOcc` on the scanned subterms",
and an abstract-side theorem "(A)(B)(C) hold of `recArgOf`'s answer given those `¬ hasIndOcc`
facts", joined by a translation `Lean.Expr ↔ VExpr` relation carrying `¬ hasIndOcc` to `NoBlock`.

**Prediction, and this is the one I most expect to be wrong.** The bridge is the real cost and it
does not exist: `NoBlock` is a `VExpr` predicate over a `VInductDecl'`, `hasIndOcc` is a `Lean.Expr`
predicate over an `Array Expr` of `indConsts`, and nothing relates `stats.indConsts` to `D`'s member
names.  If so the honest shape of the result is **not** "the check is closed" but "the check is
closed on each side of a named, stated bridge", and I must say which of the three parts the bridge
blocks.  Secondary prediction: the *abstract* half — deriving (A)(B)(C) from `recArgOf`'s own
definition plus a scan predicate stated at `VExpr` level — is where the actual proof content is, and
where I should spend the round, because it is the half `posSyn_of_recArgOf` consumes directly.
I also predict the direction is **not** through `TypeChecker.M.WF` (see S3).

### Shape prior S3 — is what I am about to trust a measurement or a docstring?

Three things the brief hands me as prose that I will re-measure rather than trust:

1. *"`recogAt` performs no `NoBlock` scan."*  This is WFPos's sentence, not a theorem.  I will read
   `recogAt`/`recArgOf`'s definition and check whether the scan is genuinely absent or merely
   absent from the *reported* answer while being present in the guard.  **Prediction: genuinely
   absent** — but I expect to find that `recArgOf` *does* fix `r.args` as `spineArgs.drop D.np`,
   which makes (A) a computation about `spineArgs` length and not an independent check.  That would
   make (A) provable and (B)(C) genuinely external.  This is the prediction I care most about.
2. *"`TypeChecker.M.WF`'s well-formedness hypothesis is refuted by a single `.inductInfo`."*  The
   brief says the previous round *instantiated* `venvsWF_refuted_at_inductInfo` rather than taking
   it from prose, and tells me to expect the same obstacle.  I will instantiate it too.
   **Prediction: it reproduces**, and therefore the implementation-side theorem must be about the
   raw monadic value (`checkPositivity … ctx s = .ok r`), exactly as `checkConstantVal_noNestedName`
   is.
3. *`VIndRecArg.exists_indep` is off `pos`'s path.*  WFPos measured this for itself; it is not
   measured for me.  **Prediction: off my path too**, because (A)(B)(C) are all `Decidable`
   statements with no `∃` over independent binders in them, and `exists_indep` is
   `binders_indep`'s obligation.  I will measure with `scripts/exists.lean` watching it.

### Cost prior C1 (written after S1-S3, deliberately)

If S2's bridge prediction holds, the closable fraction this round is (A) fully, (B) and (C) as
abstract-side statements conditional on a named scan predicate, and the implementation-side
`.ok ⇒ ¬hasIndOcc` theorems — so "closed on both sides of one stated bridge", not "closed".
Budget guess: (A) small, the implementation-side scans medium (the `for` loops in
`isValidIndAppIdx` are `Id.run` + `forIn`, which is the same unfolding pain as `NoNestedAll`'s
monadic plumbing), the bridge unbounded and therefore out of scope.

## §2 Measurements, appended the moment each answers a prior

### M1 (2026-09-04) — S1 scored: **half wrong, and the wrong half is the expensive one**

`HEADS="VInductDecl'.NoBlock" lake env lean --run scripts/shape.lean`, population **473 built
modules**, 2026-09-04: **115 constants** conclude something mentioning `VInductDecl'.NoBlock`, of
which 4 are structure fields (`VIndField.WF.pos`, `PosSyn.args_noBlock`, `PosSyn.binders_noBlock`,
`VIndCtor.WF.args_fresh`).  So the ≥10 half of S1 was right (115 ≫ 10), and the character was right
too: the cheap end is entirely witnesses (`MRedex.TQWit.tq_hostile_args_not_noBlock`,
`RecArgIndep.raiRedex_not_noBlock`, `BlockCtx.raiΓ_not_noBlock`, …), `decide` instances
(`VInductDecl'.decidableNoBlock`) and preservation plumbing (`VIndRestore.restore_noBlock`,
`noBlock_noCSubst`, `VInductDecl'.noBlock_spineFn`).

**The prediction that was wrong: "`hasIndOcc` has zero theorems about it".**  It has several, and
they are in `Verify/Inductive/Add.lean` — `AddInductive.hasIndOcc_eq` (the specification, i.e.
`hasIndOcc ↔ anySubterm`), `hasIndOcc_hpS` (the `Array Expr` → `List Name` connector, described in
the file as "connects the checker's `Array Expr` predicate to `NoConsts`' `List Name`"), and a
theorem at `Verify/Inductive/Add.lean`:1307 whose hypothesis is literally
`AddInductive.hasIndOcc stats.indConsts t = false`.  `Verify/Inductive/CanonGapMeasure.lean`:112
also holds "the syntactic reading of `AddInductive.isValidIndApp?`".  So **S2's "bridge does not
exist" is now in doubt in the direction of good news**, and the next measurement is what exactly
those give and whether `PosScan` can cite them (`can-cite.py`).

Also surfaced, and not predicted: `AddInductive.VIndField.pos_none_of_isDefEqU`
(`Verify/Inductive/Add.lean`, arity 7) — the implementation-to-`pos` link **for the `none` branch**
already exists.  That is direct evidence for S2's direction (impl → abstract, per branch) and tells
me the `some` branch is the sibling that is missing, which is a much sharper statement of the target
than the brief's.
### M2 (2026-09-04) — S2 scored **wrong in the good direction**; the bridge exists

`python3 scripts/can-cite.py Lean4Lean.Verify.Inductive.WFPos …` (2026-09-04): WFPos's import
closure is **205 modules** and already contains `Lean4Lean.Verify.Inductive.Add`, so `anySub_forallE`,
`TrExprS.noConsts` and `AddInductive.M.WF` are all **YES** — citable from a file importing WFPos.
`grep -rln 'import Lean4Lean.Verify.Inductive.WFPos'` returns **nothing**, so `PosScan` importing
WFPos creates no cycle and WFPos has no consumers to disturb.

`scripts/exists.lean`, 473 modules, 2026-09-04, with `VEnv.IsDefEq.uniq`/`uniqU` and
`VIndRecArg.exists_indep` **watched**:

| name | module | arity | cone | hole | sorryAx in cone | watched |
|---|---|---|---|---|---|---|
| `Lean4Lean.hasIndOcc_eq` | `Verify.Inductive.Add` | 2 | 805 | no | **no** | none |
| `Lean4Lean.TrExprS.noConsts` | `Verify.Inductive.Add` | 13 | 3616 | no | **no** | none |
| `AddInductive.M.WF.positivity_none` | `Verify.Inductive.Add` | 10 | 18935 | no | **yes** (8 holes) | **`IsDefEq.uniq`, `IsDefEq.uniqU`** |
| `VIndRecArg.exists_indep` | `Theory.Inductive.Decl` | 18 | 851 | **yes** | yes (itself) | none |
| `VEnvs.WF.no_inductInfo` | `Verify.InductFlip` | 5 | 6094 | no | no | none |
| `VIndField.posSyn_of_recArgOf` | `Verify.Inductive.WFPos` | 8 | 1826 | no | **no** | none |

**The design consequence, and it decides the round.**  The `none` branch's existing route
(`M.WF.positivity_none`) costs a **tainted** cone of 18935 with `IsDefEq.uniq` in it, because it goes
through `whnf.WF`.  My three parts are all *syntactic*, so if I read the checker's `Bool` guards
directly instead of through `M.WF`, the result stays in the hole-free 805/3616 neighbourhood.  So the
`some` branch is not merely the sibling of `positivity_none`: it is the branch that **does not need
the sort upgrade at all**, which is a strictly better position than the `none` branch is in.

### M3 (2026-09-04) — S3.1 scored **right on `recogAt`, wrong on part (A)**, and (A) turns out not to be a check at all

`Theory/Inductive/NestedBuild.lean`:144, read rather than trusted.  `recogAt R i k S` computes
`ξ := (splitPis S.piArity S).1`, `b`, `sp := b.spineArgs`, `nA := (R.tyArgs k).length`, and its guard
is exactly three conjuncts — `b.spineFn = .const (R.tyName k) (R.tyLvls k)`,
`sp.take nA = (R.tyArgs k).map (·.liftN (ξ.length + i))`, and `nA ≤ sp.length` — returning
`args := sp.drop nA`.  **There is no `NoBlock` scan and no arity comparison anywhere in it**, so
WFPos's one-line statement of the gap is confirmed by measurement, not taken from its prose.

**But my 40% guess that "(A) may already have a reader-side lemma" was wrong in a more interesting
way than either branch I wrote down: (A) is implied by conjunct 7.**  `VEnv.HasArgs.length_eq`
(`Theory/Inductive/Lemmas.lean`:683) gives `As.length = as.length`, and
`VExpr.length_liftTele` gives `(liftTele n As k).length = As.length`.  So `PosTy.indexArgs` at
`T' := D.types[r.idx]`, instantiated with the `D.types[r.idx]? = some T'` that conjunct 1 supplies,
yields `r.args.length = T'.indices.length` outright.  **The "three-part decidable check" is
therefore a two-part check**, and part (A) never needed the implementation at all.  §1 of
`PosScan.lean` is that reduction.
### M4 (2026-09-04) — the unpredicted obstacle, and it is `BEq Expr`

`~/lean4/src/Lean/Expr.lean`:811 — `instance : BEq Expr where beq := Expr.eqv`, and `:808`
`@[extern "lean_expr_eqv"] opaque eqv (a b : @& Expr) : Bool`.  So **two of `isValidIndAppIdx`'s
three tests compare `Expr`s with a body-less `@[extern] opaque`**: the head test
`I == stats.indConsts[i]!` and the parameter-prefix test `stats.params[i]! != args[i]!`.  This is the
exact situation Part 0 of `Verify/Inductive/Add.lean` was written to escape for `hasIndOcc`, and I
did not predict it in any of S1-S3 or C1.

Three consequences, and they are all good for the shape of the result:

1. The **residual scan** (part C) and the **arity test** (the checker's counterpart of part A) are
   *not* affected — the first is `hasIndOcc`, already specified by `hasIndOcc_eq`, and the second is
   `Nat`'s `==`, which has a `LawfulBEq`.  So the two things this round is for stay axiom-clean.
2. `Expr.eqv` **is** readable, but only through the frozen interface axiom
   `Lean.Expr.eqv_eq` (`Verify/Axioms.lean`:829, `axiom eqv_eq (e1 e2) : e1.eqv e2 = e1.eqv' e2`),
   which is on guard 1's whitelist (`Verify/Guard.lean`:119).  So the head/parameter tests are
   readable at the cost of one whitelisted axiom, and `PosScan` keeps them in a separate lemma so
   that `#print axioms` shows exactly which results pay it.
3. **`Expr.eqv` is alpha-equivalence ignoring binder names and annotations**, so
   `isValidIndAppIdx`'s success does *not* give `stats.params[j]! = t.getAppArgs[j]!` — only
   `stats.params[j]! == t.getAppArgs[j]!`.  Stating the parameter conjunct as an `Eq` would have
   been **false**.  For the head the two coincide, because `stats.indConsts[i]!` is a `.const` node
   (`checkInductiveTypes` pushes `.const indType.name stats.levels`) and
   `Lean.Expr.eqv_const : e == .const c ls ↔ e = .const c ls` (`Verify/Expr.lean`:1397).
### M5 (2026-09-04) — the lemma that decides part (B), and it is not in the tree

`Lean4Lean/TypeChecker.lean`:529 — `whnf'`'s **first** match arm is
`| .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e`.  So **`whnf` is the identity
on a pi-headed term**, with no cache and no fuel consumed.  Consequence, and it is the whole reason
part (B) is closable at all: `checkPositivity.loop`'s `let t ← whnf t` does **nothing** while the
term is pi-headed, so the loop's binder descent follows the *stored* syntactic pi telescope exactly,
which is the same telescope `VIndRestore.recogAt` splits with `splitPis S.piArity S`.  The whnf only
bites once the stored telescope is exhausted — and `Verify/Inductive/CanonGapMeasure.lean` §1's
`cgmRedex` is the witness that it can then reveal structure the stored term does not have.

`AddInductive.whnf_forallE` is that fact, proved in `PosScan.lean` §3, and it covers the
`recDepth = 0` case too (there `whnf` throws, so the success hypothesis is contradictory).  Searched
for first by conclusion head (`TypeChecker.whnf` + `Expr.forallE`) — **nothing in the tree concludes
it**, and `M.WF.whnf`, the only existing statement about `whnf` in `AddInductive.M`, gives a
`TrExpr`, i.e. an `IsDefEqU`, which is strictly weaker and carries the tainted cone of M2.
### M6 (2026-09-04) — S3.2 scored: the `M.WF` obstacle reproduces, and it was avoidable

`scripts/exists.lean` (M2's table) instantiated rather than quoted: `VEnvs.WF.no_inductInfo`
(`Verify/InductFlip.lean`, arity 5, cone 6094, hole-free) exists, so the `NoNestedAll` reasoning
carries: a name fact routed through `checkConstantVal.WF`'s `ves.WF env` is vacuous at any
environment holding an `.inductInfo`.  Prediction **correct**, and the second half of the prediction
— that the implementation-side theorems must therefore be about the raw monadic value — is what
`PosScan.lean` §3 does (`M_bind_ok`, `withLocalDecl_ok`, `whnf_forallE`, all about `x c = .ok r`).

What I had *not* predicted is that the `M.WF` route carries a second, independent cost here:
`M.WF.positivity_none`'s cone contains `VEnv.IsDefEq.uniq`/`uniqU` (M2), because `whnf.WF` only
delivers an untyped `IsDefEqU`.  Reading the `Bool` guards directly avoids that entirely, and the
axiom tables below are the receipt.

### M7 (2026-09-04) — S3.3 scored: `exists_indep` is off my path, structurally

Nothing in `PosScan.lean` mentions `VIndRecArg.exists_indep` and nothing has it in its cone
(`scripts/exists.lean`, 473 modules, 2026-09-04, with `exists_indep` **watched** — reported "none of
6" for every name queried in M2's table, including `posSyn_of_recArgOf`, the declaration §1 refines).
The structural reason is the one S3.3 predicted: all three parts of the check are `Decidable`
statements with no `∃` over independent binders, and `exists_indep` is `VIndField.WF.binders_indep`'s
obligation, not `pos`'s.  This is the same verdict `WFPos` §5(d) reached for itself, measured
separately here rather than inherited.
### M7-correction (2026-09-04) — a defect in M2 and M7, found by reading the instrument

`scripts/exists.lean`:115 sets its watch list from `$WATCH`, defaulting to **six names that do not
include `VIndRecArg.exists_indep`** (`VEnv.HasArgs.of_mkApp`, `IsDefEq.uniq`, `IsDefEq.uniqU`,
`AxiomConservativityWF`, `StrengtheningTarget`, `SortWitness`).  M2's table header and M7 both said
"with `exists_indep` watched"; in those runs it was **queried as a name, not watched**, so
"none of 6" was not evidence about it.  Corrected by re-running with
`WATCH="…exists_indep …IsDefEq.uniq …IsDefEq.uniqU"`, population **477 built modules**, 2026-09-04:

| name | module | arity | cone | hole | sorryAx | `exists_indep`/`uniq`/`uniqU` in cone |
|---|---|---|---|---|---|---|
| `VIndField.args_len_of_posTy` | `Verify.Inductive.PosScan` | 8 | 646 | no | no | none of 3 |
| `VIndField.posSome_of_recArgOf` | `…PosScan` | 11 | 1880 | no | no | none of 3 |
| `AddInductive.isValidIndAppIdx_eq` | `…PosScan` | 3 | 2251 | no | no | none of 3 |
| `AddInductive.isValidIndAppIdx_residual_noOcc` | `…PosScan` | 7 | 2280 | no | no | none of 3 |
| `AddInductive.isValidIndAppIdx_of` | `…PosScan` | 7 | 2279 | no | no | none of 3 |
| `AddInductive.whnf_forallE` | `…PosScan` | 7 | 7239 | no | no | none of 3 |
| `AddInductive.checkPositivity_loop_binderDoms` | `…PosScan` | 10 | 7394 | no | no | none of 3 |
| `AddInductive.checkPositivity_binderDoms` | `…PosScan` | 9 | 7397 | no | no | none of 3 |
| `InductiveDeclExamples.ntreeNode_field1_posSome` | `…PosScan` | 3 | 2028 | no | no | none of 3 |
| `AddInductive.PosScanWit.psT_valid` | `…PosScan` | 0 | 4826 | no | no | none of 3 |
| `VIndField.posSyn_of_recArgOf` (the target) | `Verify.Inductive.WFPos` | 8 | 1826 | no | no | none of 3 |

So the verdict of M7 survives the correction, but it was unmeasured when first written.  Note the
cone sizes: the implementation-side results sit at **2251-7397 and hole-free**, versus
`M.WF.positivity_none`'s **18935 with `IsDefEq.uniq` in it** — the gap is the price of `whnf.WF`.

### M8 (2026-09-04) — axiom ledger, and the split is by design

`lake build Lean4Lean.Verify.Inductive.PosScan`, all 31 `#print axioms` lines, 2026-09-04:

* `propext` only: `args_len_of_posTy`, `posBinderDoms`, `posBinderDoms_noOcc`,
  `posBinderDoms_instantiate1'`.
* `+ Quot.sound`: `posSyn_of_recArgOf_posTy`, `posSome_of_recArgOf`, `forIn_scan_run`,
  `anySub_instantiate1'_fvar`, `ntreeNode_field1_posSyn_of_posTy`, `ntreeNode_field1_posSome`,
  `psField_binderDoms`.
* `+ Classical.choice`: every `isValidIndAppIdx_*` projection, `M_bind_ok`, `withLocalDecl_ok`,
  `whnf_forallE`, `checkPositivity_loop_forallE`, `checkPositivity_loop_validApp`, `psBad_invalid`,
  `psField_binder_noOcc`.  Standard; inherited through `simp`.
* `+ Lean.Expr.instantiate1_eq`: **exactly** `checkPositivity_loop_binderDoms` and
  `checkPositivity_binderDoms` — the two that read the loop's fvar-instantiated evidence back to the
  stored term.
* `+ Lean.Expr.eqv_eq, Lean.Level.instLawfulBEqLevel (+ Lean.Syntax.structEq_eq)`:
  `isValidIndAppIdx_head_const` and §4.1's `psT_valid`/`psT_numArgs`/`psT_residual` — the ones that
  read `BEq Expr`.

All of `propext`, `Classical.choice`, `Quot.sound`, `Lean.Expr.eqv_eq`, `Lean.Expr.instantiate1_eq`,
`Lean.Level.instLawfulBEqLevel`, `Lean.Syntax.structEq_eq` are on `Verify/Guard.lean`'s
`axiomWhitelist` (checked at `Guard.lean`:115-137), so **no new axiom and no whitelist change**.

### M9 (2026-09-04) — green

Bare `lake build` at the end of the round: **Build completed successfully (1662 jobs), exit 0**,
2026-09-04.  Baseline at HEAD `e0aee76` was 1659 jobs; the three new jobs are `PosScan`'s targets.
(The first end-of-round build reported 1663 because a scratch probe file I had copied into
`Lean4Lean/Tests/` — a directory I do not own — was still there.  It was deleted and the build
re-run; `git status` now shows exactly the two files this round owns.  Recorded because a job count
that moved for a reason unrelated to the work is exactly the kind of number a later round would
mis-attribute.)
No `sorry` in `PosScan.lean` (the build's `declaration uses 'sorry'` lines are all pre-existing, in
`Theory/Typing/*` and `Theory/Inductive/Decl.lean`).

## §3 What closed, and what did not

**Part (A), the index-arity equation: closed, and it was never an implementation obligation.**
`VIndField.args_len_of_posTy` derives it from conjunct 7 plus conjunct 1.  So `WFPos`'s "three-part
decidable check" is a **two-part check**.  `AddInductive.isValidIndAppIdx_numArgs` is the independent
implementation route to the same equation, so the two are not the same argument twice.

**Part (C), the residual scan: closed on the implementation side, exactly.**
`AddInductive.isValidIndAppIdx_eq` is an `=` on `Bool`, not an implication, and
`isValidIndAppIdx_of` is its converse — so §2 is a *reading* of `isValidIndAppIdx`, not an
approximation of it.  `isValidIndAppIdx_residual_noOcc` is part (C).

**Part (B), the binder scan: closed on the implementation side over the stored pi telescope.**
`AddInductive.checkPositivity_binderDoms` — a successful `checkPositivity` proves every domain of
`posBinderDoms t` is block-free.  The lemma that makes it possible is `whnf_forallE` (M5).

**What is left, and it is one thing, named:** the `Expr → VExpr` transfer's **indexing**
correspondence — that the `k`-th entry of `posBinderDoms F.type` translates to the `k`-th entry of
`r.binders`, and likewise for the residual arguments and `r.args`.  The *predicate* transfer already
exists and is hole-free (`TrExprS.noConsts`, cone 3616); the indexing is R1/R2's telescope
correspondence in `Verify/Inductive/Add.lean`.  This is **unproved, not false** — `PosScan.lean` §5(b)
states it as the residue rather than assuming it, in the style of `VIndField.pos_none_of_isDefEqU`.

So: `WF.pos`'s five syntactic conjuncts now follow from the reader plus **proved facts on each side of
one named indexing bridge**, with the assumed decidable check reduced from three parts to zero
*abstract* parts (A from typing, B and C from the checker) — and the honest one-sentence verdict is
that the check is closed on both sides and not yet composed across the `Expr`/`VExpr` boundary.

## §4 Edits I would need in files I do not own — **none**

`PosScan.lean` imports only `Verify.Inductive.WFPos` and adds nothing to any other file.  No frozen
file is touched.  Two observations that *could* motivate edits elsewhere, recorded and not acted on:

1. `Verify/Inductive/WFPos.lean`'s `posSyn_of_recArgOf` could drop its `hlen` argument in favour of
   `args_len_of_posTy`; I did not propose it, because `posSyn_of_recArgOf` is still the right lemma
   for a consumer who has no `PosTy`, and `PosScan` adds the `PosTy` variant beside it instead.
2. `Verify/Inductive/CanonGapMeasure.lean`'s `CGMGuard.cgmBinderDoms` and `PosScan`'s
   `posBinderDoms` are the same function.  They cannot be merged today without moving one of them,
   because `CanonGapMeasure` imports `Experimental.ConeJoin` and is not in `WFPos`'s closure.  The
   duplication is deliberate and flagged in `posBinderDoms`' docstring under ledger row 113f's
   naming rule.

## §5 My method's gaps

1. **The instrument-default defect (M7-correction).**  I wrote "with `exists_indep` watched" twice
   before reading `scripts/exists.lean`:115 and discovering that its watch list defaults to six other
   names.  Rule 3 says read a docstring before contradicting it; the sharper rule this round wants is
   *read the instrument's default before quoting its output as evidence about a specific name*.
2. **I did not predict `BEq Expr`.**  Four priors, none about the *readability* of the check's own
   primitives — and one of the three tests turned out to be readable only through a frozen axiom and
   another to be un-`decide`-able at a closed block.  A fifth shape prior belonged here: *what does
   the implementation compare things with?*
3. **My part-(B) statement is `Expr`-side only, and I chose that scope rather than discovering it.**
   I priced the R1/R2 indexing bridge as out of scope at C1 and never re-tested that judgement after
   `whnf_forallE` turned out cheap.  It is possible the bridge is cheaper than C1 assumed, and this
   round produced no measurement either way.
4. **`checkPositivity_loop_validApp` is a one-step lemma and I did not compose it into a
   whole-telescope residual scan** the way I did for the binder scan.  Composing it needs the
   `isValidIndApp?`-at-the-reduct fact to be carried through the same fuel induction; the pieces are
   all in §2/§3 and nothing suggests it resists, but it is not done.
5. **`.mdata` and whnf-revealed binders (§5(b) 1-2) make `posBinderDoms` a *sub*-telescope of what
   the checker scans.**  That direction is safe, but I did not exhibit a term where the two actually
   differ; `cgmRedex` differs in the head, not in the binders.  A witness with a stored redex
   *under* a pi would settle it, and I did not build one.
