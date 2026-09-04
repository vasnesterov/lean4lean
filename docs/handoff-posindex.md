# `docs/handoff-posindex.md` — the `Expr`→`VExpr` **indexing** bridge for `VIndField.WF.pos`

Round of **2026-09-04**.  Owned files: `Lean4Lean/Verify/Inductive/PosIndex.lean` (new), this file.
HEAD at start `3aca413`; briefed baseline: bare `lake build` green at **1662 jobs**, guards 1/2/3
passing, census **13**.  Predecessor: `docs/handoff-posscan.md` (same date), whose §5(b) item 3 names
this round's target as its residue.

Target, in `PosScan`'s own words: *"the `Expr`→`VExpr` **indexing** correspondence (`k`-th of
`posBinderDoms F.type` ↔ `k`-th of `r.binders`)"*, plus the analogous statement for the residual
arguments and `r.args`.  The predicate half (`TrExprS.noConsts`) is done; only the indexing is open.

## §1 Priors — written 2026-09-04 before any Lean, never edited afterwards

Orientation done before writing this section, and it is only reading: `docs/handoff-posscan.md`,
`PosScan.lean` §§1-3/5/6, `TrExprS` (`Verify/Typing/Expr.lean`:153-183), `VExpr.splitPis` /
`VIndCtor.skeleton` (`Theory/Inductive/Decl.lean`:1144), `VExpr.piArity`
(`Theory/Inductive/Telescope.lean`:95), `VIndRestore.recogAt` + `recogAt_binders`
(`Theory/Inductive/NestedBuild.lean`:144), and a *headers-only* grep of `Verify/Inductive/Add.lean`.
No Lean was elaborated and no script was run.

### Shape prior S1 — does the target already exist?  (searched by **conclusion head**, not by name)

The obligation has no name of its own; PosScan states it only in prose.  Its conclusion is a
*correspondence between two pi telescopes across `TrExprS`*, so the heads I will search are
**`Lean4Lean.posBinderDoms`** (anything that concludes about it besides PosScan's own three),
**`Lean4Lean.VExpr.splitPis`** and **`Lean4Lean.VExpr.piArity`** (a VExpr-side telescope reader),
and **`Lean4Lean.TrExprS`** (which will be enormous, so I will filter it for `forallE`).
`scripts/shape.lean` is blind to anything whose type is literally `Prop`; a `def` returning `Prop`
or an `abbrev` for the correspondence would be invisible to it, so I will also `grep` for
`splitPis`/`piArity` beside `TrExprS` in one command as a second instrument.

**Predictions.**
* **65%** that a *single-step* `.forallE` inversion for `TrExprS` already exists — some
  `trExprS_forallE_inv` / `TrExprS.forallE_inv` — because `VExpr.natLE`'s docstring
  (`Verify/Typing/Expr.lean`) speaks of "a plain iterated `trExprS_arrow_inv'`", which is that
  inversion under another name.  If it exists, my bridge is a short induction over it and the round's
  content is **not** the induction.
* **25%** that a whole-*telescope* version exists (`TrExprS` of `mkPi`), and **80%** that
  `(splitPis S.piArity S).1` has no recursive-collector companion lemma, i.e. I will have to
  introduce the VExpr-side analogue of `posBinderDoms` myself.
* **~0%** that the *composed* bridge exists.  If it did, `WFPos` §3.1 and `PosScan` §5(b) would not
  both be phrased as assumptions.

### Shape prior S2 — is the work in the direction I think it is?

I think the round's real content is **not** the induction but the **sign of the direction**, and that
`PosScan` §5(b) has it backwards.  Reasoning, written before measuring:

`TrExprS.forallE` maps `Expr.forallE name ty body bi` to `VExpr.forallE ty' body'` structurally, so
the `Expr`→`VExpr` direction — "the `k`-th stored `Expr` domain corresponds to the `k`-th `VExpr`
domain, for every `k` below `(posBinderDoms e).length`" — should be a two-case structural induction.
But **the direction part (B) actually needs is the converse.**  Part (B) is
`∀ B ∈ r.binders, D.NoBlock B`, a quantifier over the **`VExpr`** list; the checker's evidence
(`checkPositivity_binderDoms`) is a quantifier over the **`Expr`** list.  So closing part (B) needs
every `r.binders` entry to *have* a `posBinderDoms` preimage, i.e. `(vBinderDoms e').length ≤
(posBinderDoms e).length`.

**Prediction, and it is the one I care about: that converse is FALSE, and I can witness it.**  Four
`TrExprS` constructors can produce a `VExpr.forallE` from an `Expr` that is *not* a `.forallE`, so
`posBinderDoms` returns `[]` while the `VExpr` side has binders:

1. **`TrExprS.mdata`** — `.mdata d e ↦ e'`, so `.mdata d (.forallE ..)` translates to a pi.
2. **`TrExprS.letE`** — `.letE .. body ..  ↦ body'`, and `body'` may be a pi.
3. **`TrExprS.fvar`** — `Δ.find? (.inr fv) = some (e, A)` with a `.vlet` binding whose value is a pi.
4. **`TrExprS.bvar`** — the same through `.inl i`.

If that is right, then `PosScan` §5(b)'s sentence *"those extra binders are scanned by the checker and
are not in `posBinderDoms`, so this direction only makes the conclusion weaker, never wrong"* is true
of the `Expr`-side lemma **and exactly wrong for the transfer**: a weaker `Expr`-side scan cannot
cover a `VExpr` list it does not surject onto.  Consequence for the deliverable: the honest result is
*"the bridge is proved in the direction that exists, the direction part (B) needs is false for
`posBinderDoms`, here is the witness, and here is the decidable side condition that repairs it"* —
which is precisely the **separation witness PosScan says it did not build** (its §5.5: "`cgmRedex`
differs in the head, not in the binders").  I predict the repair is a side condition on the *tail* of
the stored pi telescope: strip leading `.forallE`s and require the head not be one of the four heads
above.  Secondary prediction, 60%: `TrProj`'s output and `Literal.toConstructor` are application
forms, never pis, so `proj` and `lit` are **not** in the dangerous list and the side condition is a
four-way exclusion rather than a seven-way one.

I also predict the direction is **not** through R1/R2 — see S3.1.

### Shape prior S3 — measurement or docstring?

Three claims handed to me as prose, to be re-measured rather than trusted.

1. **The brief's own sentence: "the indexing is R1/R2's telescope correspondence in
   `Verify/Inductive/Add.lean`".**  `Verify/Inductive/Add.lean`:1215, seen in a headers grep, says
   *"The context correspondence — and it turned out **not** to be R1/R2"*, and :1265 says the
   discharge used there is "*weaker* than the R1/R2 telescope correspondence".  **Prediction (70%):
   the brief is imprecise.** What R1/R2 supplies is `VLCtx.find?_mkFVars_rev`, an *fvar-index*
   dictionary for the `mkFVars` context; the pi-telescope correspondence I need is a `TrExprS`
   structural induction that needs no `mkFVars` at all and can therefore be proved *without* R1/R2.
   If so, the round is cheaper than the brief prices it — and the price moves to S2's direction
   question instead.
2. **`TrExprS.noConsts` "cone 3616, hole-free"** (`docs/handoff-posscan.md` M2).  Re-measure with
   `scripts/exists.lean` rather than inherit; also re-measure `posSyn_of_recArgOf` (1826) and
   `checkPositivity_binderDoms` (7397), since composing with the latter is the end-to-end claim.
   **Prediction: reproduces**, and `checkPositivity_binderDoms` carries `Lean.Expr.instantiate1_eq`.
3. **`recogAt_binders` gives `r.binders = (splitPis S.piArity S).1`** — I read this rather than took
   it, so it is measured already.  What is *not* measured is that this equals the recursive
   "collect all leading pi domains" function.  **Prediction: it does**, by induction, and there is no
   existing lemma saying so (S1's 80%).

### Shape prior S4 — what does my path compare with, and is it opaque?

The prior `PosScan` §5.2 says belonged in its own §1.  For me the answer differs from PosScan's and I
want it on the record before measuring: **my bridge touches no `BEq` at all.**  `posBinderDoms` is a
`match`, `splitPis`/`piArity` are `match`es, `TrExprS` is an inductive, and `VLCtx.find?` compares
`FVarId`s (a `Name`, with a `LawfulBEq`), not `Expr`s.  **Prediction: no `Lean.Expr.eqv_eq` anywhere
in my cone**, and the axiom set is `propext` + `Quot.sound` + `Classical.choice`, plus
`Lean.Expr.instantiate1_eq` on exactly those results that compose with
`checkPositivity_binderDoms`.  Risk I name in advance: a *counterexample* for S2 needs a concrete
`VEnv` in which `env.IsType 0 [] (.sort .zero)` holds, and building one may cost more than the
positive half.  If it does, I will state the refutation as a `TrExprS`-hypothetical
(`∀ env Us, ... → False` at an assumed `IsType`) rather than at a closed environment, and say so.

### Cost prior C1 (written after S1-S4, deliberately)

If S2 holds, the round's output is: (i) the VExpr-side collector plus its `splitPis` identity —
small; (ii) the `Expr`→`VExpr` prefix correspondence by induction on `TrExprS` — small if S1's 65%
lands, medium otherwise; (iii) the refutation of the converse — medium, dominated by the `VEnv`
obligations; (iv) the decidable side condition and the repaired equality — medium; (v) part (B)
end-to-end *under* (iv) — small.  What I price as **out of scope**: making the side condition
unconditional, which needs an `Expr`-side scan closed under `whnf` (zeta and delta included), i.e. a
statement about `checkPositivity`'s descent rather than about a pure function.  I also price the
`r.args` half at "same proof, half the length" and will do it only after the binder half lands.

## §2 Measurements, appended the moment each answers a prior

### M1 (2026-09-04) — S1 and S2 scored together, and **the tree already knows my central claim**

Read `Verify/Inductive/Add.lean`:1739-1830 (reached from a headers grep, not from a name search).
Three things there that between them re-price the whole round:

1. **`Lean.Expr.piArity`** (`Verify/Inductive/Add.lean`:1742) — the `Expr` counterpart of
   `VExpr.piArity`, and its docstring is my S2 prediction, already in the tree:
   *"`TrExprS` does **not** determine it (`.mdata`/`.letE` translate through), so the loop invariant
   tracks it."*
2. **`ElimLoopInv.spine : Bs.length ≤ type.piArity`** (:1803), whose docstring states the falsity
   direction outright: *"**Not derivable from `tr`**: a `.mdata`- or `.letE`-wrapped domain translates
   to a `forallE` target without being a `forallE` itself, so the syntactic spine has to be tracked
   separately."*
3. **`TrExprS.forallE_target`** (:1826, arity 1 after the derivation) — `TrExprS Δ (.forallE ..) X →
   ∃ A B, X = .forallE A B`.  This is S1's 65% single-step inversion: it **exists**, so that half of
   S1 scored right; but it gives only the *target's shape*, not the domain correspondence, so the
   65% was right about existence and wrong about sufficiency.

**How S2 scores: right in content, and its novelty claim is wrong.**  My prediction that the
direction part (B) needs is false, and false because of `.mdata`/`.letE`, is **correct** — but it is
not a new finding: `ElimLoopInv.spine`'s docstring says it, and `Expr.piArity` exists precisely
because of it.  What is *new* is where the falsity bites: `ElimLoopInv` carries the inequality for the
**constructor** telescope, where its docstring argues the caller has it free; nobody has carried it
for a **field**'s own telescope, which is what `recArgOf`/`posBinderDoms` need.

**And the tree's idiom is better than the repair I predicted.**  I predicted a four-way head exclusion
(`bvar`/`fvar`/`letE`/`mdata`).  The tree's `piArity` inequality is *one `Nat` inequality* that covers
all four heads at once and is already the established shape.  So the design changes here: state the
bridge with `piArity` on both sides, not with a head-exclusion predicate.  The consequence is a
sharper statement than I priced at C1:

* **unconditional:** `TrExprS Δ t S → t.piArity ≤ S.piArity` (every `Expr` pi forces a `VExpr` pi);
* so the side condition `S.piArity ≤ t.piArity` is **equivalent to equality**, and part (B) follows
  from the bridge plus that one equality — nothing else.

S1's "~0% that the composed bridge exists" stands: nothing in the tree relates `posBinderDoms` (or any
`Expr` pi-domain list) pointwise to `splitPis`, and `grep` for `splitPis`/`piArity` across `Verify/`
(40 hits, 2026-09-04) shows the two `piArity`s are never mentioned in the same theorem.

### M2 (2026-09-04) — the bridge itself, and S3.1 scored: it is **not** R1/R2

`lake build Lean4Lean.Verify.Inductive.PosIndex`, exit 0, 2026-09-04: §1 and §2 elaborate.  The
bridge `TrExprS.binderDoms` is **twelve lines**, a structural recursion on the source `Expr` with the
index along for the ride, and it uses:

* **no `VLCtx.mkFVars`** and no `find?_mkFVars_rev` — i.e. **none of R1/R2**;
* no `VContext`, no `M.WF`, no `VLCtx.WF`, no `OnCtx`, no environment well-formedness;
* only `TrExprS.forallE`'s own two recursive arguments.

So **S3.1 scored right (its 70%)**: the brief's sentence *"the indexing is R1/R2's telescope
correspondence in `Verify/Inductive/Add.lean`"* is imprecise.  R1/R2 supplies the *fvar-index*
dictionary and `TrExprS.forallE_target` (the target's shape); the pointwise domain correspondence
needs neither, because `TrExprS.forallE` already carries the extended context in its own premise.
`Verify/Inductive/Add.lean`:1215's own sentence — *"the context correspondence — and it turned out
**not** to be R1/R2"* — was the better guide than the brief.

Also landed, and it is the arithmetic S1/M1 predicted: `TrExprS.piArity_le`,
`t.piArity ≤ S.piArity` at every `TrExprS`, unconditionally, with `posBinderDoms`/`piBinderDoms`
length identities.  Plus the general `splitPis` lemma the tree lacked:
`VExpr.splitPis_fst : (splitPis n e).1 = e.piBinderDoms.take n`, **with no side condition** (it holds
in the truncating case as well), whence `(splitPis e.piArity e).1 = e.piBinderDoms` — which is exactly
the form `VIndRestore.recogAt_binders` hands over.

### M3 (2026-09-04) — S2's falsity half scored **right, and now witnessed**

`lake build Lean4Lean.Verify.Inductive.PosIndex`, exit 0, 2026-09-04.  Two theorems:

* `trExprS_piArity_lt` — at **every** `VEnv`, with no environment hypothesis at all (sorts type
  themselves): `t = .mdata m ((_ : Sort 0) → Sort 0)` has `t.piArity = 0`, `posBinderDoms t = []`,
  while its translation has `piArity = 1` and `piBinderDoms = [.sort .zero]`.
* `binders_noBlock_not_transferable` — the sharp form.  At any environment declaring
  `I : Sort 0` at no universe parameters, the field type `.mdata m ((_ : I) → I)` translates to
  `∀ (_ : I), I`, on which **`VIndRestore.recogAt` fires** (`prRestore_recogAt`) with
  `binders = [.const I []]`; every domain the `Expr` scan sees is block-free *because there are none*
  (`posBinderDoms t = []`), and `.const I []` is not `NoConsts Sn` for any `Sn` containing `I`.

So `PosScan.checkPositivity_binderDoms` is **not** strong enough to discharge
`VIndField.WF.pos`'s `binders_noBlock`, and no `VExpr`-side strengthening can fix it: the missing
information is on the `Expr` side.  `PosScan` §5(b)'s *"a weakening, and again in the safe
direction"* is true of the `Expr`-side lemma read alone and **wrong for the transfer** — which is
exactly the sign error S2 predicted, now machine-checked.  `PosScan` §5.5 asked for a witness
separating `posBinderDoms` from what the checker scans and noted its near-miss (`cgmRedex`) differs
in the **head**; these two differ in the **binders**, which is the separation it named.

Not predicted, and worth recording: the witness needs **no `.letE`**.  `.mdata` alone suffices, and
`.mdata` is the cheapest of the four heads S2 listed — the counterexample costs one `TrExprS.mdata`
and two `sortDF`s.

### M4 (2026-09-04) — §4 lands: the composition needs **exactly one** extra hypothesis

`recArgOf_binders_noBlock` elaborates.  Its hypotheses, and each one's provenance:

| hypothesis | where it comes from |
|---|---|
| `checkPositivity stats t ctor idx cx = .ok u` | the checker, via `PosScan.checkPositivity_binderDoms` |
| `D.recArgOf i S = some r` | B6's two-stage reader |
| `TrExprS env Us Δ t S` | the translation relation |
| `hS`, `hlit`, `hproj` | `TrExprS.noConsts`' three side conditions (`Verify/Inductive/Add.lean`) |
| `hctx` | the all-`vlam` context invariant, also `Add.lean`'s |
| **`r.binders.length ≤ t.piArity`** | **nothing yet — this is the new one, and §3.2 proves it is not removable** |

Two things fell out that I had not priced at C1:

* **`recArgOf`'s second stage costs nothing.**  I expected `VExpr.betaHead` to need separate work.
  It does not: `betaHead` is the identity on a `forallE` (`betaSpine [] f = f`, so
  `VExpr.betaHead_forallE` is `rfl`), so `recArgOf_binders_piBinderDoms` concludes
  `r.binders = S.piBinderDoms ∨ S.piArity = 0`, and the right disjunct is collapsed by the same
  `hlen` hypothesis (via `TrExprS.piArity_le`, `t.piArity = 0`, hence `r.binders = []`, hence
  vacuous).  One hypothesis handles both stages.
* **The `Nat` hypothesis is equivalent to an equality.**  `TrExprS.piArity_le` gives
  `t.piArity ≤ S.piArity` unconditionally, so `S.piArity ≤ t.piArity` forces equality.  That is a
  better statement than "one more inequality to carry".

### M5 (2026-09-04) — §5, and an asymmetry I had not predicted anywhere

The args half is **not** "the same proof, half the length" (C1's guess).  `TrExprS.forallE` adds the
new domain at the *head* of both telescopes, so §2's bridge is index-preserving; `TrExprS.app` adds the
new argument at the *tail* of both spines (`VExpr.spineArgs (.app f a) = f.spineArgs ++ [a]`), so when
the source spine is shorter — which §3 shows it can be — **left indices are shifted by the difference
and only right indices agree.**  `TrExprS.spineArgs_index` is therefore stated over
`Expr.getAppArgsRevList` and `VExpr.spineArgs.reverse`.

Found while doing it, by conclusion head rather than by name: `TrExprS.mem_spineArgs`
(`Verify/Inductive/Add.lean`:1606, arity 5) is the **index-free membership shadow** of that bridge,
consumed by `VIndCtor.mem_args_of_mem_getAppArgs`.  It is the safe direction, which is why membership
sufficed there and does not suffice here.  S1's search would not have found it — it concludes a
`TrExprS`, and `TrExprS` was going to be "enormous, so I will filter it for `forallE`", and this one is
about `app`.  **That is a real gap in my own S1 instrument choice**, recorded in §5 below.

### M6 (2026-09-04) — axiom ledger, and S4 scored **right**

`lake build Lean4Lean.Verify.Inductive.PosIndex`, all 20 `#print axioms` lines, 2026-09-04:

* **no axioms at all:** `VLCtx.pushVLams`, `VLCtx.noConsts_pushVLams`.
* `propext` only: `VExpr.splitPis_fst`, `VExpr.length_piBinderDoms`, `VExpr.splitPis_piArity_fst`,
  `length_posBinderDoms`, `VExpr.mem_splitPis`, `VExpr.betaHead_forallE`.
* `+ Quot.sound`: `prRestore_recogAt`, `recArgOf_binders_piBinderDoms`.
* `+ Classical.choice`: `TrExprS.binderDoms`, `TrExprS.piArity_le`, `trExprS_piArity_lt`,
  `binders_noBlock_not_transferable`, `TrExprS.splitPis_noConsts`, `TrExprS.spineArgs_index`,
  `TrExprS.spine_length_le`, `TrExprS.spineArgs_noConsts`, `PosIndexWit.binderDoms_fires`.
* `+ Lean.Expr.instantiate1_eq`: **exactly one** — `recArgOf_binders_noBlock`, the single result that
  composes with `PosScan.checkPositivity_binderDoms`, which is where that axiom lives.

**`Lean.Expr.eqv_eq` appears nowhere in this file**, which is S4's headline prediction, and the reason
is the one S4 gave: nothing here compares two `Expr`s.  Checked against `Verify/Guard.lean` myself:
`axiomWhitelist` (`Guard.lean`:143) is `[propext, Classical.choice, Quot.sound] ++ frozenAxioms`, and
`frozenAxioms` (:115-137) contains `Lean.Expr.instantiate1_eq`.  So **no new axiom and no whitelist
change**, and nothing on my path is a frozen axiom the tree did not already pay for.

### M7 (2026-09-04) — cones, holes, and the watch list set **explicitly**

`scripts/exists.lean`, population **478 built modules**, 2026-09-04, run with
`WATCH="Lean4Lean.VIndRecArg.exists_indep Lean4Lean.VEnv.IsDefEq.uniq Lean4Lean.VEnv.IsDefEq.uniqU"`
— set explicitly, because `scripts/exists.lean`:115 defaults to six *other* names and
`docs/handoff-posscan.md` §5.1 records that mistaking the default for the watch cost that round two
false claims.  The script confirmed `watching 3 declarations`.

| name | module | arity | cone | hole | sorryAx in cone | watched (3) |
|---|---|---|---|---|---|---|
| `VExpr.splitPis_fst` | `…PosIndex` | 2 | 404 | no | no | none |
| `trExprS_piArity_lt` | `…PosIndex` | 3 | 782 | no | no | none |
| `recArgOf_binders_piBinderDoms` | `…PosIndex` | 5 | 957 | no | no | none |
| `binders_noBlock_not_transferable` | `…PosIndex` | 12 | 1878 | no | no | none |
| `TrExprS.piArity_le` | `…PosIndex` | 6 | 3625 | no | no | none |
| **`TrExprS.binderDoms`** (the bridge) | `…PosIndex` | 9 | **3648** | no | **no** | none |
| `TrExprS.spineArgs_index` | `…PosIndex` | 9 | 3642 | no | no | none |
| `TrExprS.spine_length_le` | `…PosIndex` | 6 | 3652 | no | no | none |
| `PosIndexWit.binderDoms_fires` | `…PosIndex` | 3 | 3680 | no | no | none |
| `TrExprS.spineArgs_noConsts` | `…PosIndex` | 19 | 3682 | no | no | none |
| `TrExprS.splitPis_noConsts` | `…PosIndex` | 17 | 3734 | no | no | none |
| **`recArgOf_binders_noBlock`** (§4.2) | `…PosIndex` | 23 | **7784** | no | **no** | none |
| `TrExprS.noConsts` (inherited) | `Verify.Inductive.Add` | 13 | 3616 | no | no | none |
| `checkPositivity_binderDoms` (inherited) | `…PosScan` | 9 | 7397 | no | no | none |
| `VIndField.posSyn_of_recArgOf` (the consumer) | `…WFPos` | 8 | 1828 | no | no | none |

**S3.2 scored right**: `TrExprS.noConsts` reproduces at cone **3616, hole-free**, so the number
inherited from `docs/handoff-posscan.md` M2 was a measurement, not a docstring.  So does
`checkPositivity_binderDoms` at 7397.

**One number moved and I am not attributing it to my own work.**  `posSyn_of_recArgOf` measures
**1828** here where `PosScan` M7-correction measured **1826** on the same day, and nothing in this
round touches `WFPos` or anything it imports.  The population also moved (477 → 478).  A concurrent
stream is live in `Theory/Typing/` (its untracked `TrianglePort.lean` is in the working tree, and is
**not** in the build — no `.olean`), so the most likely cause is a declaration that stream added
somewhere `WFPos`' cone reaches.  Recorded rather than smoothed over: a cone that moves for a reason
outside the round is exactly what a later round mis-attributes.

### M8 (2026-09-04) — green, guards, census

Bare `lake build` at the end of the round: **Build completed successfully (1664 jobs), exit 0**,
2026-09-04.  Baseline at HEAD `3aca413` was **1662**; the two new jobs are `PosIndex`'s targets, and
nothing else is added — `PosIndex` is imported by no file (checked: `grep -rln PosIndex` returns only
itself), and the other stream's `TrianglePort.lean` has no `.olean`, so it contributes none of them.

Guards, `lake build Lean4Lean.Verify.Guard`, 2026-09-04:

* guard 1: *Axioms.lean declares exactly the 24 frozen axioms ✓*
* guard 2: *kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)*
* guard 3: *checker cone implementation gaps within frozen list (2/2 remaining) ✓*

`scripts/sorry-census.lean`, 2026-09-04: **TOTAL 13**, unchanged, and
`Lean4Lean.VIndRecArg.exists_indep` is still listed with **0 transitive users**.

**Warnings from the file I own: none.**  `lake build Lean4Lean.Verify.Inductive.PosIndex` emits no
`warning:` line whose path is `PosIndex.lean`, and no `sorry` (`grep -c sorry` = 0).

**Late re-poll, and it is not mine.**  A bare `lake build` re-run *after* the 1664-job green above
came back **failed at 1663/1664**, the single failing target being the concurrent stream's
`Lean4Lean/Theory/Typing/TrianglePort.lean` (three `Application type mismatch` errors at :298 and
:303) — a file this round does not own, which entered the build between the two runs when that stream
added an import.  Re-polled once as the brief requires, and the failure reproduced with the *same*
single target.  It cannot be caused by this round: `PosIndex` is imported by nothing
(`grep -rln PosIndex` returns only itself), so nothing in `Theory/` can see it.  Everything else,
including all 214 targets of `PosIndex`' own closure, replayed green.  Reported rather than waited
out, because the honest statement of my own green is "1663 of 1664, with the one failure in another
stream's file mid-edit" and not "1664".

## §3 What closed, and what did not

**The indexing correspondence is proved — in the direction that exists.**  `TrExprS.binderDoms`
(arity 9, cone 3648, hole-free): if the source's `k`-th stored pi domain is `d`, the target's `k`-th
pi domain exists and `d` translates to it, in the `VLCtx` extended by the target's first `k` domains.
`TrExprS.spineArgs_index` (arity 9, cone 3642) is the same for application spines, right-anchored.
Both are **unconditional** — no `VLCtx.WF`, no `VContext`, no `M.WF`, no environment
well-formedness, and **none of R1/R2**.

**`WF.pos`'s `binders_noBlock` now follows end to end — from the checker plus one `Nat` hypothesis,
and not without it.**  `recArgOf_binders_noBlock` (arity 23, cone 7784, hole-free,
`Lean.Expr.instantiate1_eq` its only frozen axiom) composes `checkPositivity`'s success, `recArgOf`'s
answer, a `TrExprS` and `r.binders.length ≤ t.piArity`.

**The direction the transfer needs is FALSE, and this round has the witness.**  `.mdata` at the head
of a field type hides a binder from `posBinderDoms` while `TrExprS` translates straight through
(`trExprS_piArity_lt`, at every `VEnv`); at an environment declaring `I : Sort 0`, the field type
`.mdata m ((_ : I) → I)` makes the `Expr` scan vacuous while `recogAt` fires with a block-carrying
binder (`binders_noBlock_not_transferable`).  So the residue `PosScan` left is not one thing but two:
an indexing correspondence, which is now proved, and a **directional hypothesis**, which is now known
to be indispensable rather than merely unproved.  `PosScan` §5.5 asked for a witness separating
`posBinderDoms` from what the checker scans and noted its near-miss differed in the **head**; these
differ in the **binders**.

**Not done:** composing §5 into `∀ a ∈ r.args, D.NoBlock a`.  Blocked outside this file, for the
reason `PosScan` §5.4 records: the residual scan runs on the whnf **reduct**, and
`checkPositivity_loop_validApp` was never composed into a whole-telescope scan.  §5 is the transfer
that composition will consume when it exists.

**`VIndRecArg.exists_indep` stayed off the path**, measured with the watch list set explicitly
(M7): none of the 15 names queried has it in its cone, and the census still shows it with 0
transitive users.  The structural reason is unchanged and is not this round's discovery: every
statement here is `NoBlock` of a telescope entry, with no `∃` over independent binders in it.

## §4 Edits I would need in files I do not own — **none**

`PosIndex.lean` imports only `Verify.Inductive.PosScan` and adds nothing to any other file.  No frozen
file is touched, and no file I do not own is modified (`git status` shows exactly the two files this
round owns, plus another stream's).  Three things that *could* motivate edits elsewhere, recorded and
**not acted on**:

1. **`PosScan`'s `posBinderDoms` is the wrong `Expr`-side object for part (B)**, and §3.2 is the
   proof.  The verbatim edit I would propose, if asked, is to `Verify/Inductive/PosScan.lean` §3, and
   it is *not* a one-liner: it would replace

       def posBinderDoms : Expr → List Expr
         | .forallE _ dom b _ => dom :: posBinderDoms b
         | _ => []

   with a whnf-closed collector.  Its `.mdata` clause is
   `| .mdata _ e => posBinderDoms e` and is structural; its `.letE` clause is
   `| .letE _ _ v b _ => posBinderDoms (b.instantiate1 v)` and is **not** structural (well-founded
   recursion), and its `TrExprS` counterpart is a `vlet` *context* entry rather than a substitution,
   so the correspondence would need a substitution lemma this file does not have.  I therefore do
   **not** propose the edit; I propose the `Nat` hypothesis, which is what §4 carries.
2. `Verify/Inductive/PosScan.lean` §5(b)'s sentence *"this direction only makes the conclusion
   weaker, never wrong"* is true of the `Expr`-side lemma and misleading about the transfer.  Its
   correction is content, not a code change, and it is stated here instead.
3. `Verify/Inductive/Add.lean` could state `ElimLoopInv.spine`'s inequality once, generically, as
   `TrExprS.piArity_le`'s converse-hypothesis; I did not propose it, because `ElimLoopInv` needs it
   at a constructor and §4 needs it at a field, and the two are discharged from different places.

## §5 My method's gaps

1. **My S1 search plan would not have found `TrExprS.mem_spineArgs` (M5).**  I wrote that `TrExprS`
   as a conclusion head "will be enormous, so I will filter it for `forallE`" — and the one existing
   half-bridge in the tree is about `app`.  I found it by reading `Add.lean`'s R2 section, not by the
   instrument I planned.  The sharper rule: when the target is a *correspondence*, the conclusion head
   is the relation, and filtering it by the constructor you happen to care about discards the sibling
   you most need to know about.
2. **All four of my priors were about the positive half; none was about non-vacuity.**  §6's firing
   exists because rule "a relation with no instance proves nothing" is in this project's culture, not
   because any prior of mine asked for it — and the firing turned up the fact that the *composed*
   transfer cannot be fired hypothesis-free today, because `TrExprS.noConsts`' `hproj` is open in
   `Add.lean`.  A fifth prior belonged here: *at what concrete input can I run the finished statement,
   and what stops me?*
3. **I priced the args half at "same proof, half the length" and it is a different proof** (M5).  The
   left/right alignment asymmetry is visible in `TrExprS`'s two rules and I had read both before
   writing C1; I simply did not look.  Cost prior written after the shape priors, and still wrong about
   shape.
4. **I did not measure whether `hlen` is dischargeable, which is the question the next round turns
   on.**  `ElimLoopInv.spine`'s docstring claims the caller has the constructor-level inequality free
   because *"`isValidIndAppIdx` rejects any constructor whose stored spine is not a literal `forallE`
   chain"* — that is prose, of exactly the kind S3 exists to re-measure, and I re-measured neither it
   nor its field-level analogue.  If it is true at a field, §4's hypothesis is free and part (B) is
   closed outright; if it is false, §3.2's counterexample is *reachable* and the gap is a soundness
   question rather than a proof-engineering one.  **That is the next round's target, and I did not
   settle which way it goes.**
5. **A cone I cannot account for** (M7): `posSyn_of_recArgOf` reads 1828 against `PosScan`'s 1826 on
   the same day.  I attributed it to the concurrent `Theory/Typing/` stream on circumstantial grounds
   (its untracked file, the population moving 477 → 478) and did **not** confirm it by diffing the two
   cones, which the instrument can do (`CONE_IN`).  Recorded as unexplained rather than explained.
