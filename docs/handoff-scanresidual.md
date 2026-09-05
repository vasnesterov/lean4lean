# handoff-scanresidual

Round start: 2026-09-05. HEAD claimed `9438e39`. Owner files:
`Lean4Lean/Verify/Inductive/ScanResidual.lean` (new),
`Lean4Lean/Verify/Inductive/BinderScan.lean`, `Lean4Lean/Verify/Inductive/PosIndex.lean`,
this file.

Target: two items.
1. `instantiate1'` σ-composition at **non-adjacent** indices:
   `(b[fvar v]_{d+1})[v'[fvar v]_d]_0 = (b[v']_0)[fvar v]_d`.
2. `hβ`: the `Expr`-side β step at `.app (.lam ..) a`.

## §1 Shape questions (written BEFORE reading anything; predictions blank)

**Q1 (extremes).** Instantiate the quantified numeral `d` in item 1 at its extremes,
`d = 0` and `d = <boundary>`. At `d = 0` the statement collapses to the adjacent form
already in the tree (`Verify/Expr.lean`:1116). Question: *is the general `d` form
actually needed by the three call sites in `BinderScan.lean` §4/§5/§6, or does every
call site instantiate at `d = 0`?* If every site is `d = 0`, item 1 is discharged by
the existing adjacent lemma and no new lemma is needed.
  - Prediction: the general `d` is needed at §5/§6 (scan descends under binders, so `d` = binder depth), but §4 may be `d=0`. Expect at most one genuinely non-adjacent site.
  - Answer (§2): _____

**Q2 (reachability / vacuity).** The previous round's own unmeasured question:
*is a head-β-redex field type (`.app (.lam ..) a` in a constructor field position,
whose whnf is a `.forallE`) reachable through `addDecl` at all?* Cheap `#eval`:
build such a declaration and see whether `addDecl` accepts it, and whether the
positivity scan ever sees an unreduced `.app (.lam ..) _` head.
  - Prediction: unreachable — `Lean.Expr` field types in a real inductive come from the elaborator already in whnf-normal enough that a head `.app (.lam ..) _` never survives; but `addDecl` takes arbitrary `Expr`, so the *kernel* must accept it. Predict: reachable via a hand-built decl, so item 2 is NOT vacuous.
  - Answer (§2): _____

**Q3 (dictionary already in tree).** Search **by conclusion head**, never by name.
For item 1 the conclusion head is `instantiate1'`/`instantiate1` equality between
two nested instantiations; for item 2 it is a `TrExprS`/`TrExpr` whose `VExpr` side
is `VExpr.betaHead` / `e'.inst e₀'`. *Do lemmas with those conclusion heads already
exist, hole-free?* (`TrExprS.inst` at `Verify/Typing/Lemmas.lean`:2189 is claimed
in hand, arity 12, cone 5083.) Two prior rounds declared this target's dictionaries
missing and were wrong both times.
  - Prediction: yes for item 2 (`TrExprS.inst` stated as in hand). For item 1, predict a `d`-general σ-composition lemma does NOT exist (only adjacent at Expr.lean:1116) but a `VExpr`-side analogue does.
  - Answer (§2): _____

**Q4 (tripwire).** `BinderScan.lean` §8 arms an `#eval` tripwire guarding the `.letE`
debt: it asserts `scanShapeNoLet` is false on a positive `let`-field `addDecl` accepts,
and that `addDecl` rejects the non-positive twin. *If item 1 closes and `scanShapeNoLet`
disappears from §4/§5/§6, does §8's tripwire still guard anything?* A tripwire guarding
nothing must be retired explicitly, not left in place.
  - Prediction: if item 1 closes, `scanShapeNoLet` becomes provable/removable and §8's first conjunct (`scanShapeNoLet` false on an accepted let-field) still *holds* as a fact but guards no debt -> must be retired.
  - Answer (§2): _____

## §2 Verdicts (append-only; never edit a filled answer above)

### Q2 — ANSWERED 2026-09-05 (FIRST MEASUREMENT, run before anything else was read for it)

**A head-β-redex field type IS reachable. Item 2 is NOT vacuous.** Prediction correct.

Witnesses (in `PosReachWit.tryInd`'s harness, `α` = `bvar 0` inside the field):

* `fldGoodB := .app (.lam x Type ((_ : x) → W α)) α` — β-contracts to `(_ : α) → W α`.
  `Lean4Lean.addDecl` **ACCEPTS**.
* `fldBadB := .app (.lam x Type ((_ : W x) → W α)) α` — β-contracts to `(_ : W α) → W α`.
  `Lean4Lean.addDecl` **REJECTS**: "(kernel) arg #2 of 'WBadB.mk' has a non positive occurrence
  of the datatypes being declared".

So `checkPositivity`'s `whnf` does perform the head β step, and the shape `hβ` excludes occurs in
an accepted declaration. Measured alongside: `fldGoodB.consumeMData.piArity = 0`,
`posBinderDoms fldGoodB = []`, and — the load-bearing one — **`scanShapeNoLet fldGoodB = true`**.
So this witness *satisfies* §4's `.letE` side condition and still lands in the `hβ` branch: the two
residuals are genuinely independent, and closing item 1 cannot touch item 2.

### Q1 — ANSWERED 2026-09-05 (extremes instrument run first, as the method requires)

**The general `d` is needed, and instantiating at the extreme did not shortcut it.** Prediction
half-right.

* The *call site* in `BinderScan` §5 is `d = 0` (`ScanCert.unsubst_fvar ... body 0 hs ...`), but
  `unsubst_fvar` increments `d` at every `.forallE`, so the lemma's own recursion needs general `d`.
* At `d = 0` the statement is **still not** an instance of the tree's adjacent
  `instantiate1'_instantiate1'`: that lemma's right-hand side carries a lift on the substituted term
  (`e3.liftLooseBVars' 0 1`), so specialising it gives `(e[u]_1)[w']_0 = (e[w'↑1]_0)[u]_0`, not the
  needed `(e[u]_1)[w[u]_0]_0 = (e[w]_0)[u]_0`. The extremes instrument **refuted the hope**, it did
  not discharge the obligation.
* What it did buy: the two-index form `(e[u]_{k+j+1})[w[u]_j]_k = (e[w]_k)[u]_{k+j}` is the right
  induction-strengthened statement (`k` moves under binders, `j` is fixed), and it needs one further
  lemma that was **not** in the tree: `(w[u]_j)↑(s,k) = (w↑(s,k))[u]_{j+k}` for `s ≤ j`.

### Q3 — ANSWERED 2026-09-05 (conclusion-head search, not name search)

* **Item 1's dictionary was absent, as predicted.** Searching for the conclusion head
  "`instantiate1'` of an `instantiate1'`, equated" over all of `Lean4Lean/` returns exactly one hit,
  `Lean.Expr.instantiate1'_instantiate1'` (`Verify/Expr.lean`:1116-1118), the adjacent form.
  Searching for "`liftLooseBVars'` of an `instantiate1'`" returns three hits, all of them
  `instantiate1'` **of a lift** (the other order), none the commutation. So both §1 and §2 are new.
* **Item 2's dictionary exists but is priced differently than the brief says.**
  `Lean4Lean.TrExprS.inst` (`Verify/Typing/Lemmas.lean`:2189) requires
  `t₀ : env.HasType Us.length Δ.toCtx e₀' A₀` — a **typing** hypothesis for the β argument.
  `TrExprS.inst_let`, the ζ twin §3 uses, requires none. That asymmetry is the whole cost of item 2:
  the bridge (`TrExprS.piBinderDoms_noConsts`) is currently typing-free, and a β clause would import
  `HasType` into it.
  A *second*, unmentioned dictionary was found by the same search and is worth citing:
  `Lean4Lean.VExpr.betaHead_eq_self_of_noLam` + `VInductDecl'.recArgOf_eq_recog_of_noLam`
  (`Verify/Inductive/B6.lean`:168, 190) — stage 2 collapses to stage 1 on a `.lam`-free `S`. It does
  **not** cover the reachable witness above (`fldGoodB`'s translation contains a `.lam`), which is
  why it is not a route to `hβ`.

### CORRECTION to the target brief (this is §2, so it belongs here)

`BinderScan` §9(d) claims that with the σ-composition "`scanShapeNoLet` disappears from §5 and §6".
**That is wrong, and item 1 does not close the `.letE` residual.** Measured by rebuilding §4 and
re-reading §5:

* `scanShapeNoLet` is spent **twice** in `BinderScan` §5's `.forallE` case and once in its `.letE`
  case. §2's σ-composition removes the *first* use only — `ScanCert.unsubst_fvar_all` (§3 of this
  file) is now unconditional, which is a strictly more general lemma than `BinderScan`'s §4.
* The surviving use is §5's own `.letE` head case, which needs `whnf`'s ζ step, and that is **not**
  available as an `M Expr` equality the way `whnf_mdata` is: `whnf'`'s `.mdata` arm returns *before*
  the cache (`TypeChecker.lean`:531), whereas `.letE` falls through to `whnfCore'`, whose `.letE`
  arm is `save <|← whnfCore (body.instantiate1 val)` (`TypeChecker.lean`:416-417) — it **inserts
  under the pre-ζ key**. So the two computations' states diverge after the step, and the equality
  needs cache-irrelevance for `reduceNative`, `reduceNat`, `unfoldDefinition` and `whnf`'s own loop.
* Worse, and this is the part no prior round noticed: **even granting that equality, §5's induction
  has no measure.** The equality is at the *same* `inductiveFuel` (as `checkPositivity_loop_mdata`
  is), and `body.instantiate1' val` is not a structural subterm of `.letE _ _ val body _` — the
  `.mdata` case gets away with a nested structural induction on `t` precisely because `e` *is* a
  subterm. `let x := big; x x` ζ-reduces to `big big`, so no size measure exists either. Closing
  §5's `.letE` case therefore needs a termination argument for the head-ζ chain (morally
  `whnfCore`'s own), or the `whnf'.WF` bridge — not one substitution lemma.

### Q4 — ANSWERED 2026-09-05

**The §8 tripwire is NOT retired; it still guards a live debt.** Prediction wrong — it predicted the
tripwire would become a fact guarding nothing. It does not, because `scanShapeNoLet` survives in
`BinderScan` §5/§6 (see the CORRECTION above). `BinderScan` §8's prose now carries a dated
"Still armed, checked 2026-09-05" note saying exactly why.

A **second**, independent tripwire is armed in `ScanResidual` §6 for the β residual, with the same
two-arm self-checking shape: positive head-β-redex field must be ACCEPTED (else the residual is a
fiction), non-positive twin must be REJECTED (else the β branch is *false*, not unproved). Both arms
fire green at build time.

## §3 What was landed (2026-09-05, HEAD `9438e39` + this round)

New file `Lean4Lean/Verify/Inductive/ScanResidual.lean` (605 lines). Bare `lake build` green,
**1670 jobs** (was 1668); guards 1 ✓ / 2 ✓ (proof INCOMPLETE: sorryAx — `kernel_sound` unchanged) /
3 ✓ (2/2); hole census **13**, unchanged. Every result below is hole-free with no sorryAx in cone;
the only frozen axiom that appears is `Lean.Expr.instantiate1_eq`, which is in `Guard.lean`'s
`frozenAxioms` (line 121) and was already in `BinderScan` §5's cone.

| result | arity | cone | what it is |
|---|---|---|---|
| `Lean.Expr.liftLooseBVars_instantiate1'` | 8 | 1556 | `(w[u]_j)↑(s,k) = (w↑(s,k))[u]_{j+k}`, `s ≤ j` — **new**, not in the tree |
| `Lean.Expr.instantiate1'_instantiate1'_closed` | 8 | 1628 | item 1, two-index form, `u` closed |
| `Lean.Expr.instantiate1'_instantiate1'_fvar` | 4 | 1629 | item 1 verbatim, at `.fvar v` |
| `Lean4Lean.ScanCert.unsubst_fvar_all` | 8 | 1688 | `BinderScan` §4 with `scanShapeNoLet` **deleted** |
| `Lean4Lean.hβ_not_derivable` | 16 | 7508 | `hβ` is a false hypothesis at a real configuration |
| `Lean4Lean.VExpr.noConsts_betaHead` | 3 | 488 | block-freeness survives head β (VExpr half of item 2) |
| `Lean4Lean.recArgOf_binders_noBlock_of_noConsts` | 8 | 1008 | both reader stages, from `NoConsts S` alone |
| `Lean4Lean.recArgOf_binders_noBlock_noLen_beta` | 25 | 9010 | `BinderScan` §6 with `hβ` weakened to the checker's early return |

Supporting: `Lean.Expr.instantiate1'_bvar_{lt,self,gt}`, `liftLooseBVars_bvar_{lt,ge}` (the five
`bvar` clauses, so §1/§2's arithmetic is a `rw` chain); `Lean4Lean.scanHead`,
`scanHead_instantiate1'_fvar`, `ScanCert.of_scanHead_false`, `scanHead_cases` (collapse §3's
`13 × 13` case split to four real cases); `VExpr.noConsts_mkApp'`, `noConsts_spine`,
`noConsts_betaSpine`; `recArgOf_binders_piBinderDoms_beta` (`PosIndex` §4.1 keeping the β stage
*visible* instead of collapsing it to `S.piArity = 0`); `hβ_beta_of_hβ` (the weakening is a
weakening); `ScanResidualWit.fldB_scanShape`, `fldGoodB_gap`.

## §4 Method gaps this round leaves

1. **The brief's own pricing of item 1 was wrong and I only caught it by rebuilding §5.** The
   `exists.lean`-style absence check tells you a *name* is missing; nothing in the toolkit tells you a
   *claim in a docstring* about what a lemma will buy is false. The instrument that caught it was
   re-reading the consumer's proof term by term and counting the uses of the hypothesis. There is no
   script for that.
2. **I did not attempt the `whnf`-ζ M-equality, so my claim that it is blocked is a reading of
   `whnfCore'`'s source, not a machine-checked refutation.** The *measure* obstruction (§7(a) third
   bullet) is solid — it is a statement about `Expr`, not about `whnf`. The cache obstruction is
   prose. A successor who wants to overturn it should try the equality directly rather than trust me.
3. **`hβ_not_derivable`'s witness is a `vlet` configuration, not a reachable declaration.** Its
   reachability half is a separate `#eval` on a *different* term (`fldGoodB`). Nothing in the file
   proves those two are the same shape; they are the same shape by inspection only. That is the same
   gap `BinderScan` §7/§8 has, inherited deliberately.
4. **`recArgOf_binders_noBlock_noLen_beta`'s new second arm is never discharged at a call site here.**
   I did not check `Verify/Inductive/Add.lean` to see whether `hasIndOcc stats.indConsts t = false`
   is available there, so "strictly weaker" is proved (`hβ_beta_of_hβ`) but "more useful" is not
   measured.
5. **Item 2's remaining price is stated but not paid, and I did not verify that
   `env.HasType Us.length Δ.toCtx e₀' A₀` is actually available at
   `VIndField.WF.pos`'s call site.** If it is, item 2 is a bounded job; if it is not, it is the
   `VContext` widening two earlier rounds declined. That measurement is the cheapest next step and
   costs one read of `Verify/Inductive/Add.lean`.

### §4 gap 5, measured before signing off (2026-09-05)

I did the one read. Three facts, all cheap for a successor to re-check:

1. **`recArgOf_binders_noBlock` and `recArgOf_binders_noBlock_noLen` have no call sites.** A grep for
   both names over `Lean4Lean/` returns only their own files and docs. So "is `HasType` available at
   the call site" has no answer yet — there is no call site.
2. **The assembly route that *does* exist works in a `VContext`**, which carries
   `mlctx_wf : mlctx.WF venv lparams` (`Verify/Inductive/Add.lean`:644). So the typing information
   `TrExprS.inst` wants is in principle reachable there, unlike in `BinderScan` §3's interface, which
   takes a bare `VLCtx`. Item 2's widening is therefore a widening of §3's *interface*, not a request
   for information nobody has.
3. **And the existing route does not use syntactic `whnf` lemmas at all.**
   `AddInductive.M.WF.positivity_none` (`Add.lean`:1296) goes through
   `M.WF.whnf` (`Add.lean`:1275) = `TypeChecker.whnf.WF`, which hands back
   `c.TrExpr e₁ e'` — the *reduct's* translation, with an `IsDefEqU` back to the original. That is a
   different architecture from `PosScan`/`PosReach`/`BinderScan`'s `whnf_forallE` / `whnf_mdata` /
   `whnf_bvar` line. **Caveat, and it is why this does not simply dissolve both residuals:**
   `whnf.WF` gives `A'` with `IsDefEqU A A'`, not `A' = VExpr.betaHead A`, and
   `VIndField.WF.pos` needs `D.NoBlock B` for the *syntactic* `r.binders`. So the defeq is too weak
   at exactly the point that matters. Recording it anyway: a successor pricing either residual should
   price *both* architectures, and should not assume the syntactic line is the only one.

### Dated correction to §3's header (2026-09-05, end of round)

§3 above says "HEAD `9438e39` + this round". While I worked, another stream committed and HEAD moved
to **`0f7e6b0`** ("residual B is satisfiable -- and the itemisation that priced it graded the
load-bearing item wrong"). All the numbers in §3's table and the guard/census figures were
**re-measured on `0f7e6b0`** after that commit landed: bare `lake build` green, **1670 jobs**
(1668 → 1670 is exactly this file's two jobs, so that commit added no module); guards 1 ✓, 2 ✓
(proof INCOMPLETE: sorryAx), 3 ✓ (2/2); hole census **13**, re-run and unchanged. Every figure in
this document is dated 2026-09-05 and taken at `0f7e6b0`.
