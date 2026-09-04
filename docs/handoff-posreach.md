# `docs/handoff-posreach.md` — is `PosIndex` §3.2's counterexample **reachable**?

Round of **2026-09-04**.  Owned files: `Lean4Lean/Verify/Inductive/PosReach.lean` (new), this file,
and `bugs-found.md` (append-only, and only if the answer is yes).  HEAD at start `1191a23`.
Predecessor: `docs/handoff-posindex.md` (same date), whose §4 leaves exactly one hypothesis
(`hlen : r.binders.length ≤ t.piArity`) on `recArgOf_binders_noBlock` and whose §3.2
(`binders_noBlock_not_transferable`) is the abstract counterexample this round has to either
*realise* or *kill*.

The question, stated once: **can a field type reach `VIndField.WF.pos`'s consumers with its
`Expr`-side positivity scan vacuously clean and a block name among its `VExpr`-side binders?**

## §1 Priors — written 2026-09-04 before any Lean, never edited afterwards

Orientation done before writing this section, and it is only reading — no Lean elaborated, no script
run, no `lake build`: `PosIndex.lean` in full, `docs/handoff-posindex.md` §§1-2 headers,
`PosScan.lean` §3.2/§3.3/§5(b), `Verify/Inductive/Add.lean`:1740-1840 (`Lean.Expr.piArity`,
`ElimLoopInv` and its `spine` field's docstring), `Inductive/Add.lean`:40-70 (`anySubterm`,
`stripAnnotation`), :176 (`consumeAnnotations`), :261 (`hasIndOcc`), :300-390
(`isValidIndAppIdx`, `isValidIndApp?`, `isRecArg`, `checkPositivity`, `checkConstructors`),
`TypeChecker.lean`:325-400 and :527-556 (`whnfCore'`, `whnf'`), `Verify/Typing/Expr.lean`:153-183
(`TrExprS`), and the `#eval` tripwire shapes in `NoNestedAll.lean` §5.3 and `RestoreFaithful.lean`
§5.1.

### Shape prior S1 — does the target already exist?  (searched by **conclusion head**)

Three conclusion heads to search, none of them by the name I would give my own lemma:

* **`TypeChecker.whnf` at a `.mdata`.**  `PosScan`'s `whnf_forallE` is the only `whnf`-behaviour
  lemma I have seen in `Verify/Inductive/`; the `.mdata` twin is what this round needs, and I
  predict **it does not exist** (`PosScan` §5(b)(2) states the `.mdata` fact as *prose about the
  source*, which is precisely the shape this round is auditing).
* **`checkPositivity` concluding `.error`.**  Every `checkPositivity` lemma in the tree is
  success-direction (`checkPositivity_loop_forallE`, `_loop_validApp`, `_loop_binderDoms`,
  `_binderDoms`).  A *rejection* lemma is what killing a counterexample needs, and I predict
  **there is none**: the tree has no `checkPositivity … = .error` anywhere.
* **head-`mdata` stripping as a function.**  `Lean.Expr.consumeMData` exists upstream but is
  `@[extern]`-adjacent territory and `Inductive/Add.lean` already had to write `consumeAnnotations`
  by hand for exactly that reason; I predict I must define my own `consumeMData` and that nothing
  in the tree concludes about `(consumeMData e).piArity`.

`scripts/shape.lean` is blind to anything whose type is literally `Prop`, so a `def` returning
`Prop` would not show; all three heads above are `Bool`/`Except`/`Nat`-valued or inductive
predicates, so the blindness does not bite here.

### Shape prior S2 — is the work in the direction I think?

The brief offers two worlds (prose holds at a field ⇒ `hlen` dischargeable ⇒ proof engineering;
prose fails ⇒ soundness question).  **I predict a third**, and I am writing it down before measuring
so it cannot be retrofitted:

1. The prose claim **fails at a field**.  `checkConstructors`' loop applies `isValidIndAppIdx` only
   to the *terminal* of the constructor chain, never to a domain; the `dom` handed to
   `checkPositivity` is unconstrained, and `checkPositivity`'s **first act is `whnf`**, which is the
   opposite of "must be a literal `forallE` chain".  So `hlen` is **not** dischargeable as stated.
2. The counterexample is nevertheless **unreachable**, for the very reason (1) holds: `whnf'`'s
   second match arm is `| .mdata _ e => return ← whnf' e`, so the loop descends *past* the
   annotation §3.2 hides the pi behind, reaches the `.forallE` arm, tests
   `hasIndOcc stats.indConsts dom` on the block-carrying domain, and **throws**.  The
   information §3.2 says is "missing on the `Expr` side" is missing from
   `checkPositivity_binderDoms`' *statement*, not from `checkPositivity`'s *behaviour*.
3. So the repair is to weaken `hlen`, not to file a bug: replace `t.piArity` by
   `(consumeMData t).piArity`, which is exactly the arity `TrExprS` sees, because `TrExprS.mdata`
   passes straight through.

If (2) is wrong the answer is yes and `bugs-found.md` gets an entry.  If (2) is right,
`bugs-found.md` is **not** touched.

### Shape prior S3 — measurement or docstring?  (this round is entirely this question)

Two docstrings are on trial and I must not substitute a third for them:

* Under test: `ElimLoopInv.spine`'s *"the caller has the fact for free — `checkConstructors` has
  already run and `isValidIndAppIdx` rejects any constructor whose stored spine is not a literal
  `forallE` chain."*  Even if true of the **constructor**, it is silent about a **field**, and
  `hlen` is a field-level statement.  I predict the constructor reading is true and the field
  reading is false, and that the docstring's error is one of *scope*, not of fact.
* **My own** claim that `whnf` strips `.mdata` is, right now, a *reading of source*
  (`TypeChecker.lean`:531) — i.e. exactly the kind of thing this round exists to distrust.  It does
  not count until it is an elaborated theorem about `TypeChecker.whnf`.  `PosScan` §5(b)(2) already
  asserts it in prose; I will not cite that as evidence.
* `AddInductive.whnf_forallE` is a *measurement* (elaborated), and it is about `.forallE`, not
  `.mdata`; I will not stretch it.

### Shape prior S4 — what does the implementation compare with, and is it opaque?

`isValidIndAppIdx`'s head test is `I == stats.indConsts[i]!`, i.e. `Lean.Expr.eqv`, an `@[extern]`
`opaque` giving alpha-equivalence and **not `decide`-able at any closed input** (`PosScan` §5(c)).
Consequence for this round, decided in advance: **any rejection proof must route through the
`hasIndOcc dom` throw, never through `isValidIndApp? = none`.**  `hasIndOcc` is `anySubterm`, pure
total Lean over `replaceNoCacheT`, so it *is* `decide`-able — and `replaceNoCacheT` descends into
`.mdata`'s child (`Lean4Lean/Expr.lean`:56), so `hasIndOcc` sees under an annotation while
`posBinderDoms` does not.  That asymmetry is the whole mechanism of prior S2(2).

Secondary: `hasIndOcc` calls `Expr.constName!`, a `panic!`-partial projection, on `indConsts`
entries; harmless because `checkInductiveTypes` only ever pushes `.const`, but it means a witness
must supply `.const`-shaped `indConsts` or the `Bool` is junk.

### Cost prior (after the three shape priors, as required)

* `whnf_mdata` (the `.mdata` twin of `whnf_forallE`): **cheap**, ~15 lines, same `simp only`
  unfolding chain as `whnf_forallE` plus one extra `Inner.whnf'` step.  Risk: `Inner.whnf'`'s
  `.mdata` arm recurses into `Inner.whnf'` *directly* rather than through `Methods.withFuel`, so no
  fuel bookkeeping — if instead it went through `m.whnf` I would need a depth-decrement and the
  lemma would cost a second induction.  Predicted: no induction needed.
* `checkPositivity` invariance under head `.mdata`: **cheap given the above**, an equality of two
  `loop` calls at the *same* fuel.
* the rejection theorem (§3.2's witness is thrown out): **cheap**, `decide` on one `hasIndOcc`.
* an `#eval` tripwire showing `addDecl` **accepts** an `.mdata`-wrapped *positive* field (so the
  shape is real and the arity gap is real even though the counterexample is not): **medium**, the
  cost is building a well-typed `InductiveType` by hand, not the proof.
* the general theorem "the loop scans every `VExpr` binder" (which would close part (B) with no
  `Nat` hypothesis at all): **expensive and out of scope** — it needs the `.letE` and
  let-bound-`fvar` cases, and the latter needs R1/R2's dictionary relating `VLCtx` `vlet` entries to
  the `LocalContext`'s `ldecl`s.  Predicted residue of this round.
