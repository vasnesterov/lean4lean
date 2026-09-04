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

## §2 MEASUREMENTS — appended live, 2026-09-04, each entry written before the next tool call

Round restarted after a crash that produced no Lean.  §1 above is the predecessor's and is
**unedited**.  HEAD at restart `a76446d`.

### M1 — the prose claim **fails at a field**.  S2(1)/S3 first bullet: **CONFIRMED**

`Lean4Lean/Inductive/Add.lean`, `checkConstructors`' inner `loop`: the `.forallE` branch handles a
field with `ensureType` / universe check / `checkPositivity stats dom n i` / `consumeAnnotations dom`
/ `withLocalDecl`, and `isValidIndAppIdx` appears **only** in that loop's `else` arm —
`else if !isValidIndAppIdx stats t idx then throw … "invalid return type"`.  So the test is applied
to the **terminal** of the constructor chain and to **no domain**.  A field's type is never required
to be a literal `forallE` chain; `checkPositivity`'s own first act is `whnf`, which is the opposite
requirement.  `hlen : r.binders.length ≤ t.piArity` is therefore **not** dischargeable as stated,
and the step-4 repair is the right one.  The docstring `ElimLoopInv.spine`'s error is one of
**scope** (true of the constructor terminal, silent about a field) exactly as S3 predicted.

### M2 — `whnf'`'s `.mdata` arm does not go through `Methods.withFuel`.  Cost-prior risk: **as predicted**

`Lean4Lean/TypeChecker.lean`:530-531, inside `Inner.whnf'`:

```
| .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
| .mdata _ e => return ← whnf' e
```

The recursive call is to `whnf'` itself, at the *same* `Methods` dictionary — `Methods.withFuel`
(:911-921) is what maps `m.whnf` to `whnf' e (withFuel n)`, and this arm never reaches it.  So there
is no `recDepth` decrement across a `.mdata`, and for a *single* annotation one unfolding step
suffices with **no induction**, as §1's cost prior predicted.  (Induction would still be needed for
an arbitrarily deep annotation stack; §3 below says which of the two I proved.)

### M3 — `Lean.Expr.consumeMData` is upstream, pure, and usable.  S1 third bullet: **HALF MISS**

`grep -rn consumeMData --include=*.lean .` over the whole repo: **0 hits**, so the second half of S1's
third bullet ("nothing in the tree concludes about `(consumeMData e).piArity`") is **CONFIRMED**.  The
first half is **WRONG**: `Lean.Expr.consumeMData` exists and `#print` gives

```
def Lean.Expr.consumeMData : Expr → Expr := fun x => Expr.brecOn x Expr.consumeMData._f
```

i.e. structural recursion over `Expr`, no `partial`, no `@[extern]`, no `_unsafe_rec` companion, and
`rw [Lean.Expr.consumeMData]` discharges the `.mdata` equation directly (checked in a scratch file).
The analogy with `consumeAnnotations` does not carry: that one had to be hand-written because
`Lean.Expr.consumeTypeAnnotations` is **`partial`**, hence body-less; `consumeMData` is not.  So this
round writes **no** new recursive definition, which is also the better outcome for guard 3 (no new
`_unsafe_rec`).

### M4 — `whnf_mdata` proved, general in `e`, **no induction**.  Cost prior 1: **CONFIRMED, and cheaper**

`Lean4Lean/Verify/Inductive/PosReach.lean`, `AddInductive.whnf_mdata`:

```
theorem whnf_mdata {m : MData} {e : Expr} :
    (liftM (TypeChecker.whnf (.mdata m e)) : M Expr) = (liftM (TypeChecker.whnf e) : M Expr)
```

Elaborated `lake build Lean4Lean.Verify.Inductive.PosReach`, exit 0, 2026-09-04.  **8 lines** against
§1's predicted ~15, the same `simp only` unfolding chain as `whnf_forallE` plus `TypeChecker.Inner.whnf'`,
`funext`, and a `recDepth` case split — **no induction**, exactly as predicted.  Two ways it came out
*stronger* than §1 asked for:

* it is an **equality of `M Expr` values**, not a success-direction implication, so it composes by
  `rw` inside `checkPositivity.loop`;
* it is general in `e` — no `.forallE` premise.  The reason is the one M2 measured: the `.mdata` arm
  touches neither the `whnfCache` nor `Methods.withFuel`, so `whnf (.mdata m e)` and `whnf e` are the
  *same computation*, including at `recDepth = 0` where both throw `.deepRecursion`.  So the
  arbitrarily-deep annotation stack costs nothing extra either (§3 below iterates it structurally).

### M5 — `checkPositivity` invariance under a head `.mdata`.  Cost prior 2: **CONFIRMED**

`checkPositivity_loop_mdata` is **4 lines** and is exactly what §1 asked for — an equality of two
`loop` calls at the *same* fuel:

```
  | 0, _   => by rw [checkPositivity.loop, checkPositivity.loop]
  | _+1, _ => by rw [checkPositivity.loop, checkPositivity.loop, whnf_mdata]
```

Iterated to `checkPositivity_loop_consumeMData` (whole annotation stack, still same fuel) and lifted to
the entry point as `checkPositivity_consumeMData`.  The entry-point step needed `exact` rather than
`rw` because `checkPositivity`'s `readThe Context` leaves a `match Except.pure c with …`; the match
reduces definitionally, so nothing had to be proved about it.  `checkPositivity_binderDoms_consumeMData`
is the one-line composition `PosIndex` §4.2 consumes.

### M6 — the rejection theorem.  Cost prior 3: **CONFIRMED as cheap, MISS on `decide`**

`checkPositivity_reject` — stronger than §1 asked for.  §1 wanted "§3.2's witness is thrown out"; the
theorem proved is the whole *shape*:

```
theorem checkPositivity_reject (ht : t.consumeMData = .forallE nm dom body bi)
    (hocc : hasIndOcc stats.indConsts dom = true) :
    checkPositivity stats t ctor idx c ≠ .ok u
```

— any annotation stack over a pi whose domain carries a block occurrence, at every fuel including 0.
Route as prior S4 committed in advance: through the `hasIndOcc dom` throw, never through
`isValidIndApp? = none`.  `checkPositivity_reject_mdata_witness` specialises it to §3.2's witness
verbatim.

**The `decide` prediction is a MISS**, and in the direction `PosScan` §3.5 already warned about:
`decide` on `hasIndOcc #[.const I []] (.const I []) = true` fails outright — *"Expected type must not
contain free variables"*, because `I` is a bound `Name` — and even at a closed `I` `PosScan` §3.5
records that `Array.any` routes through `Array.anyM.loop`, which is well-founded and does not reduce
in the kernel.  What discharges it is `PosScan`'s own `hasIndOcc_const` plus
`simp [Lean.Expr.constName!]`, i.e. **rewriting, not evaluation**.  So there is **no new `decide`
anywhere in this round**, and rule 5's concern does not arise: `PosScan` and `PosIndex`'s deliberate
avoidance of `decide` at the residual clause is not regressed, and the rejection is not evaluated
either.

### M7 — the `hlen` repair lands, and it is *tight*.  Step 4: **done, one line of new proof**

`PosIndex.recArgOf_binders_noBlock` now reads
`(hlen : r.binders.length ≤ t.consumeMData.piArity)`.  `lake build Lean4Lean.Verify.Inductive.PosIndex`,
exit 0, 215 jobs, 2026-09-04.  The proof needed **one** new line, `have H' := H.consumeMData`, plus
mechanical substitution of `H'` for `H` and `t.consumeMData` for `t`; the two facts it consumes are
`TrExprS.consumeMData` (`TrExprS.mdata` has no side condition, so stripping is free) and
`checkPositivity_binderDoms_consumeMData` (§2.1).  `PosIndex` now imports `PosReach`, so the layering
is `PosScan ← PosReach ← PosIndex`.

**The repair is tight, and that is checkable.**  At §3.2's own witness `t = .mdata m ((_ : I) → I)`:
`t.piArity = 0` but `t.consumeMData.piArity = 1`, and `r.binders.length = 1`.  So the **old** `hlen`
was false at the witness (which is why the old theorem was safe), while the **new** `hlen` is
*satisfied* there.  The weakened theorem is therefore saved from §3.2 by `hchk` **alone** — i.e. by
the rejection of M6 and nothing else.  If `whnf` ever stopped descending past `.mdata`,
`recArgOf_binders_noBlock` would become **false**, not merely unproved.  That is what the §4 tripwire
guards, and it is the sharpest statement of the round: the answer "unreachable" is now load-bearing
for a theorem, not just reassuring.

### M8 — the tripwire fires on the first try, all three arms.  Cost prior 4: **CONFIRMED (medium, and the cost was where predicted)**

`Lean4Lean.addDecl` at `Kernel.Environment.empty`, on `W (α : Type) : Type` with one constructor
`mk`, three field types:

| field type of `mk` | `addDecl` |
|---|---|
| `(_ : α) → W α` (plain, positive) | **ACCEPTED** |
| `.mdata {} ((_ : α) → W α)` (annotated, positive) | **ACCEPTED** |
| `.mdata {} ((_ : W α) → W α)` (annotated, non-positive — §3.2's shape) | **REJECTED**: `(kernel) arg #2 of 'WBad.mk' has a non positive occurrence of the datatypes being declared` |

So the *shape* is reachable and the arity gap is real at an **accepted** declaration
(`posBinderDoms fldGoodM = []` while `fldGoodM.consumeMData.piArity = 1`, both `rfl`), while the
non-positive instance is not — which is the whole answer of the round, now executable.  §1's cost
estimate "medium, the cost is building a well-typed `InductiveType` by hand" was right about *where*
the cost is; the estimate was pessimistic about *how much* — the first shape tried type-checked, the
only care needed being the `.bvar` indices and the `imax` universe check (`Sort 1` throughout keeps
`resultLevel.geq'` satisfied).

### M9 — the two halves are linked at one witness.  Not in §1's plan; added because §1's plan left the link by-eye

`PosIndex` §3.3 (new): `binders_noBlock_witness_rejected` and
`binders_noBlock_not_transferable_unreachable`.  §3.2's `∃` gained two conjuncts
(`t = .mdata m ((_ : I) → I)` and `r.binders.length = 1`, both `rfl`) so that the witness which breaks
the transfer and the term which the checker rejects are provably **the same `t`** rather than the same
term typed twice.  The composed theorem carries, at one witness: the translation, `recogAt` firing, the
vacuous `Expr` scan, the failure of `∀ B ∈ r.binders, NoConsts`, **the rejection at every fuel and
context**, `t.piArity = 0` (the old `hlen` fails), and `r.binders.length ≤ t.consumeMData.piArity`
(the new `hlen` holds).  `lake build Lean4Lean.Verify.Inductive.PosIndex`, exit 0, 215 jobs,
2026-09-04, first try.

## §3 The measured table — every name this round introduced

Measured 2026-09-04 at HEAD `a76446d` + this round's working tree, by `/tmp/measure.lean` over the
import closure of `Lean4Lean.Verify.Inductive.PosIndex` (**13304** non-internal `Lean4Lean`
declarations, 16014 graph nodes counting internal companions as pass-through — the fix
`scripts/sorry-census.lean` records).  `fwdcone` = transitive `Lean4Lean` constants the declaration
depends on, theorem values read with `allowOpaque := true`; `users` = non-internal `Lean4Lean`
declarations that transitively reach it, **inside this closure**.  Both numbers move if a declaration
is moved between modules, so they are dated and scoped and not comparable with `PosIndex`'s or
`PosScan`'s own rounds.

| name | arity | fwdcone | users | axioms |
|---|---|---|---|---|
| `AddInductive.whnf_mdata` | 2 | 865 | 10 | p, C, Q |
| `AddInductive.checkPositivity_loop_mdata` | 7 | 911 | 9 | p, C, Q |
| `consumeMData_mdata` | 2 | 6 | 10 | p |
| `consumeMData_eq_self` | 2 | 30 | 0 | p |
| `AddInductive.checkPositivity_loop_consumeMData` | 6 | 917 | 8 | p, C, Q |
| `AddInductive.checkPositivity_consumeMData` | 5 | 920 | 2 | p, C, Q |
| `AddInductive.checkPositivity_binderDoms_consumeMData` | 9 | 1092 | 1 | p, C, Q, **`Lean.Expr.instantiate1_eq`** |
| `AddInductive.hasIndOcc_forallE_of_dom` | 6 | 144 | 5 | p, Q |
| `AddInductive.checkPositivity_loop_reject` | 13 | 1008 | 4 | p, C, Q |
| `AddInductive.checkPositivity_reject` | 12 | 1011 | 3 | p, C, Q |
| `AddInductive.checkPositivity_reject_mdata_witness` | 9 | 1025 | 2 | p, C, Q |
| `TrExprS.consumeMData` | 6 | 196 | 1 | p, C, Q |
| `PosReachWit.fldGoodM_gap` | 0 | 53 | 0 | p |
| `PosReachWit.fldBadM_gap` | 0 | 53 | 0 | p |
| `binders_noBlock_witness_rejected` (PosIndex §3.3) | 11 | 1026 | 1 | p, C, Q |
| `binders_noBlock_not_transferable_unreachable` (PosIndex §3.3) | 14 | 1220 | 0 | p, C, Q |

and the two `PosIndex` declarations this round changed:

| name | arity | fwdcone | users | axioms |
|---|---|---|---|---|
| `binders_noBlock_not_transferable` (§3.2, +2 conjuncts) | 12 | 322 | 1 | p, C, Q |
| `recArgOf_binders_noBlock` (§4.2, `hlen` weakened) | 23 | 1451 | 0 | p, C, Q, **`Lean.Expr.instantiate1_eq`** |

`p` = `propext`, `C` = `Classical.choice`, `Q` = `Quot.sound`.

**The one non-standard axiom, checked against `Guard.lean` myself.**  `Lean.Expr.instantiate1_eq`
appears at `Lean4Lean/Verify/Guard.lean`:121, inside the frozen 24-axiom whitelist that check 1
enforces.  It is inherited, not introduced: `PosScan`'s `checkPositivity_loop_binderDoms` already
carries it (its own docstring names it "guard 1's whitelisted interface axiom for the extern"), and
`checkPositivity_binderDoms_consumeMData` is a one-line composition with it.  **No axiom outside
Guard.lean's list is reached by anything this round adds, and no `sorryAx`** — `grep -c sorry` is 0 in
both owned files and no `#print axioms` line reports one.

## §4 Build, guards, census — 2026-09-04

* **Bare `lake build`: exit 0, `Build completed successfully (1665 jobs)`.**  1664 before
  `PosReach.lean` existed, so the new module is the single added job.
* **guard 1**: `Axioms.lean declares exactly the 24 frozen axioms ✓`
* **guard 2**: `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)` —
  unchanged; this round touches nothing on `kernel_sound`'s path.
* **guard 3**: `checker cone implementation gaps within frozen list (2/2 remaining) ✓` — unchanged.
  Nothing was added to the allowlist: `Lean.Expr.consumeMData` is upstream, structural and
  `partial`-free (M3), so no new recursive definition and no new `_unsafe_rec` companion.
* **census: `lake env lean scripts/sorry-census.lean` — `TOTAL declarations directly containing
  sorryAx: 13`.**  Unchanged, same 13 names as before (`VIndRecArg.exists_indep` among them, untouched
  and off this path).
* **Warnings from files I own: none.**  One appeared (`ReaderT.pure` unused in a `simp only`) and was
  removed.
* The `#eval` tripwire logs at build time:
  `PosReach/§4: plain positive field ACCEPTED, .mdata-wrapped POSITIVE field ACCEPTED …,
  .mdata-wrapped NON-POSITIVE field REJECTED … ✓`.

## §5 §1's scorecard, cost estimates included

| §1's prediction | verdict | evidence |
|---|---|---|
| S1: no `whnf`-at-`.mdata` lemma exists | **HIT** | `whnf_forallE` was the only `whnf`-behaviour lemma in `Verify/Inductive/`; `whnf_mdata` is new |
| S1: no `checkPositivity … = .error` anywhere in the tree | **HIT** | every `checkPositivity` lemma was success-direction; `checkPositivity_reject` is the first rejection |
| S1: must hand-write `consumeMData` | **MISS** | `Lean.Expr.consumeMData` is upstream, `brecOn`, non-`partial`; the `consumeAnnotations` analogy fails because `consumeTypeAnnotations` is `partial` and this is not (M3) |
| S1: nothing concludes about `(consumeMData e).piArity` | **HIT** | zero repo hits for the name |
| S1: `scripts/shape.lean`'s `Prop` blindness does not bite | **HIT** (unexercised) | no `def` returning `Prop` was needed |
| S2's "third world", clause 1 — prose **fails at a field** | **HIT** | M1: `isValidIndAppIdx` only in `checkConstructors`' `else` arm |
| S2 clause 2 — counterexample **unreachable** via `whnf'`'s `.mdata` arm | **HIT** | M2/M4/M6; `bugs-found.md` untouched, as S2 said it would be |
| S2 clause 3 — repair is `t.piArity` → `(consumeMData t).piArity` | **HIT** | M7; and `TrExprS.mdata` passing through is exactly why (`TrExprS.consumeMData`) |
| S3 — `ElimLoopInv.spine`'s error is one of **scope**, not fact | **HIT** | M1: true of the constructor terminal, silent about a domain |
| S3 — the `.mdata` claim "does not count until it is an elaborated theorem" | **HONOURED** | it is now `whnf_mdata`; `PosScan` §5(b)(2)'s prose was not cited as evidence |
| S4 — route the rejection through `hasIndOcc dom`, never `isValidIndApp? = none` | **HONOURED** | `checkPositivity_reject`'s only input is `hasIndOcc … dom = true`; §5(b) of `PosReach` records the limit this imposes |
| S4 — a witness must supply `.const`-shaped `indConsts` | **HIT** | `hst : stats.indConsts = #[.const I []]`, and `hasIndOcc_const` is what evaluates it |
| cost 1: `whnf_mdata` ~15 lines, no induction | **HIT, better** | 8 lines, no induction, and *general* in `e` and an *equality* (M4) |
| cost 1's risk: `.mdata` arm might go through `m.whnf` and need a second induction | **did not fire** | M2: it recurses into `whnf'` at the same dictionary |
| cost 2: loop invariance cheap, same fuel | **HIT** | 4 lines (M5) |
| cost 3: rejection cheap, `decide` on one `hasIndOcc` | **HIT on cheap, MISS on `decide`** | `decide` fails on free variables *and* on `Array.anyM.loop`; `hasIndOcc_const` + `simp` does it (M6) |
| cost 4: `#eval` tripwire medium, cost in the hand-built `InductiveType` | **HIT on where, pessimistic on how much** | first shape tried was accepted (M8) |
| cost 5: general "loop scans every `VExpr` binder" expensive, out of scope, predicted residue | **HIT** | left undone, for the reason §1 gave; see §6 |

**Score: 15 hits, 2 misses (`consumeMData` hand-written; `decide`), 2 calibration errors both in the
optimistic-for-us direction.**  §1's unusual specificity paid: the only thing it got structurally wrong
was an availability question it flagged as an assumption to check, and the round it planned cost about
half what it priced.

## §6 What I left out of scope, and my method's gaps

**Out of scope, deliberately, exactly as §1 predicted:** the general theorem *"the loop scans every
`VExpr` binder"*, which would delete the arity hypothesis instead of weakening it.  Its `.mdata` clause
is now cheap — that is §2 of `PosReach` — but its `.letE` clause is not: the whnf-faithful reading is
`posBinderDoms (b.instantiate1 v)`, not structural, and its `TrExprS` counterpart is a `vlet`
**context** entry rather than a substitution, so it needs the R1/R2 dictionary relating `VLCtx` `vlet`
entries to the `LocalContext`'s `ldecl`s.  Nothing measured here suggests it is false.  `whnf` also
does zeta and δ, so the same collector owes a story for a `let`-bound `fvar` and for an unfoldable
head; neither is attempted.

**Gaps in my own method, in order of how much they should worry a reader:**

1. **`PosReach` and `PosIndex` are census orphans.**  `scripts/cone-orphans.py`: 505 modules, 328 in
   the census cone, 141 orphaned — and `PosScan`, `PosIndex` and now `PosReach` are three of the 141.
   So `scripts/sorry-census.lean`'s "13" **does not see my files at all**; that number is evidence that
   I broke nothing in the census cone, not evidence that my files are hole-free.  The independent
   evidence for that is per-declaration: 16 `#print axioms` lines, none reporting `sorryAx`, plus
   `grep -c sorry` = 0.  Pre-existing for `PosScan`/`PosIndex`; `PosReach` inherits it by importing
   into the same island.
2. **The rejection covers one throw, not the whole check.**  `checkPositivity` has a second rejection
   path (`isValidIndApp? = none`) and prior S4 correctly forbids proving anything about it, because
   `Lean.Expr.eqv` is an `@[extern]` `opaque`.  A field whose annotation hides an *invalid
   application* rather than a *non-positive pi* is outside everything proved here.
3. **The tripwire tests one block shape.**  One inductive, one parameter, one constructor, one field,
   empty `MData` (`{}`).  It shows the arity gap occurs in *an* accepted declaration; it does not
   survey which real annotations occur in practice, and a non-empty `MData` might interact with
   `consumeAnnotations`' `isAnnotation` guard differently (untested).
4. **`recArgOf_binders_noBlock` still carries `hproj`**, `Verify/Inductive/Add.lean`'s open side
   condition on `TrProj`.  Unchanged by this round and not this file's residue (`PosIndex` §7(f)); it
   means the composed transfer still cannot fire hypothesis-free.
5. **`whnf_mdata` is about `TypeChecker.whnf` as *this* checker defines it.**  It is not a statement
   about the C++ kernel, and nothing here checks that `type_checker.cpp`'s `whnf` also descends past
   `mdata` — the C++ side would be a separate measurement, and no divergence is claimed or entered in
   `divergences.md`.
6. **Cone and user counts are closure-relative and dated.**  They were taken over
   `PosIndex`'s import closure, which includes `PosReach` only because I made `PosIndex` import it;
   moving any of these declarations between modules changes every number in §3's table.
