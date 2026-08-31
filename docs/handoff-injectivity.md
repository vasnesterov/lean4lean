# Handoff: `Theory/Typing/Injectivity.lean` and its family

Claims are marked **[machine]** (a `sorry`-free Lean declaration in this tree, or a
`lake build` / `#print axioms` / cone-script run on this commit) or **[analysis]** (read off
source or argued, not machine-checked). The distinction is load-bearing: this corner has
produced wrong verdicts in six sessions, every one of them from analysis, and every correction
from a machine run.

Sections 1–3 and 5–7 are from the session that narrowed `PiInvStrat` to `PiInvStratApp`; their
numbers were measured then, with internal names *included* (see §1.2's header).  **§0's opening
paragraph, §4A and §8 are from the 2026-08-30 session** and use the census convention (internal
names skipped), so their counts are smaller for the same statements — the two are not in
conflict, they are different scopes, and each section says which it used.

**§4D is from the 2026-08-30 fourth session** (`BaseUniqTerm.lean`); it answers §8 item 1 and
corrects the way that item's "prize" was phrased.

**§4E is from the 2026-08-30 fifth session** (`BaseUniqChain.lean`); it **corrects §4D.5** — the
`peelEq` `defeq` case is breakable, and the break is machine-checked.

Files added or changed on 2026-08-30: **`Lean4Lean/Theory/Typing/RetypeCase.lean`** (new),
**`Lean4Lean/Theory/Typing/RetypeAdmissible.lean`** (new, later the same day),
**`Lean4Lean/Theory/Typing/ProofRetypeHeads.lean`** (new, third session of the day —
see **§4C**, which corrects §4B.6 and answers §4B.5's open question),
one import line in `Lean4Lean/Experimental/ConeJoin.lean`, and this
document.  Nothing else was touched.  §4B is the later session and supersedes §4A.4.  `lake build Lean4Lean.Theory.Typing.RetypeCase` is
green; a whole-tree `lake build` fails in `Theory/Typing/ChurchRosser.lean`, another stream's
in-flight edit (`Alternative 'keta' has not been provided`, line 2240), which is why the
end-of-session census and `dup-names` runs are blocked — see §8. **[machine]**

---

## 0. Headline

**Fourth session, 2026-08-30 — `BaseUniq` is proved by induction on the term, and the open
check §8 item 1 named is settled in the affirmative.**  `uniqStrong_of_baseUniq` *can* be
applied at a proper subterm without re-entering the whole statement, because
`HasTypeStrong.peelEq` rewrites the **type** and never the **subject**.  Indexing both
predicates by the subject (`BaseUniqAt`, `UniqStrongAt`) makes the recursion structural:
`baseUniqAt_of_sortUniq_piInv` elaborates to `VExpr.brecOn`, and the elaborated step function
takes its two recursive calls at `x.1.1` (the function of an `.app`) and `x.2.1` (the body of
a `.lam`) and nowhere else.  Hence `retypes_of_sortUniq_piInv`: `Ordered env + SortUniq +
PiInv → retypes`, `sorryAx`-free.  **But the *implication* is not new** — see §4D.2 — and the
brief's phrasing of the prize needs correcting.  `Theory/Typing/BaseUniqTerm.lean`, 23
declarations (2 defs, 21 theorems).  §4D. **[machine]**

**Third session, 2026-08-30 — `ProofRetype` is not a residual of its own, and two of §4B's
readings are wrong.**  All four residuals of `IsDefEqStrong.retypes` follow from **one**
statement, `BaseUniq` (any two *base* typings of a term are at convertible types), by a
three-line argument that mentions no rule; `retypes_of_baseUniq` reproves `retypes` with **no
induction over `IsDefEqStrong` at all**.  `BaseUniq` in turn is free at three of six head
shapes (`bvar`, `const`, `sort`), and its residual `.app` case is exactly Π-injectivity — so
`ProofRetype`'s content is *not* special to proofs and is *not* free of normalisation content.
And §4B.5's open question is answered: `UniqStrong → BaseUniq` and `BaseUniq + SortUniq →
UniqStrong`, so the residual is **equivalent to unique typing modulo `SortUniq`**, not strictly
weaker.  All in `Theory/Typing/ProofRetypeHeads.lean`, 19 declarations, `sorryAx`-free.  §4C.
**[machine]**

**Later session, 2026-08-30: §4A.4's open question is answered, and the answer is that the
question was about the wrong statement.**  `HasTypeStrong.retype` — the `hasType'` `retype`
case *with the conversion premise dropped* — is at least as strong as the case, and has
nothing to induct on, because the case carries that premise and it was thrown away.  With it kept, the case is proved: `IsDefEqStrong.retypes`
(`Theory/Typing/RetypeAdmissible.lean`), `sorry`-free, with **no `PiInvStratApp`, no
`VEnv.WF`, no `SortUniq`, and no member of the injectivity family**.  Nine of
`IsDefEqStrong`'s thirteen rules cost nothing; the residual is exactly the four *computation*
rules — `beta`, `eta`, `proofIrrel`, `extra`.  §4B. **[machine]**


**Session of 2026-08-30 adds one result, and it is a correction to `Theory/Typing/Enlarged.lean`
rather than a new proof.**  Enlarged.lean says the in-place `retype` enlargement *forces* a
`retype` constructor into `HasTypeStrong` and thence into `HasTypeStratified`, so that `uniq`'s
own induction gains a case whose obligation (`UniqAcross`) collapses back to `uniq`.  **"Forces"
is wrong.**  The case is a theorem — `HasTypeStrong.retype` in the new
`Theory/Typing/RetypeCase.lean`, `sorry`-free, from `PiInvStratApp` alone.  What kills the
enlargement is not an unprovable obligation but a **measured cone regression**, and both routes
out of the case are now priced.  §4A. **[machine]**

1. **The `NormalEq`-has-no-`trans` route does not reach this target — it is CIRCULAR, and the
   circularity is measured, not argued.** `IsDefEq.church_rosser` reaches exactly four
   sorry-carrying declarations, and **three of the four are this corner's own targets**:
   `NormalEq.descend`, `IsDefEqU.forallE_inv`, `IsDefEqU.weakN_iff`,
   `IsDefEqU.forallE_inv_stratified`. The shortest path to the target is
   `NormalEq.defeq → IsDefEq.transU_r → IsDefEq.trans_r → IsDefEq.uniq →
   forallE_inv_stratified`. §2. **[machine]**
2. **The circle survives every re-indexing, and the reason is now stated in one line.**
   `uniqQ`'s `app` case needs `SortUniq` at a level manufactured by Π-injectivity from an
   *unstratified* conversion. Every proposed repair — height-indexing `HasTypeStratified`'s
   `defeq` conversion, an asymmetric invariant bounding only one derivation, decoupling the
   levels in the conclusion, choosing the level from the bounded side — was walked to its
   failing step this session and each returns to the same demand. §4. **[analysis]**
3. **The obligation is narrowed and the narrowing is machine-checked.** `PiInvStrat` is
   consumed exactly once, in `uniqQ`'s `app` case, and that call discards the whole domain
   conjunct and passes the *same* index twice. The new `PiInvStratApp` is that instance:
   strictly weaker (no domain conjunct, one index instead of two), and it is what
   `uniqAux`, `WF.sortUniq'`, `WF.uniq'`, `IsDefEqU.sort_inv` and `IsDefEq.uniq'` now take.
   §3. **[machine]**
4. **The narrowed statement is still equivalent to `SortUniq`** — `sortUniq_iff_piInvStratApp`,
   `sorry`-free, both directions — so narrowing shrinks the residual without cutting the
   circle. And it is **not vacuous**: `piInvStratApp_fires` exhibits an instance with
   syntactically different domains over *every* environment, `sorryAx`-free. §3. **[machine]**
5. **No refutation.** `forallE_inv_stratified` was pushed at from the one direction `VEnv.WF`
   leaves open (`VDecl.WF.unsafeDef` is circular by design and makes WF environments
   inconsistent — `Theory/MutualDefUnsound.lean`). It does not reach: the block's values are
   typechecked in `env'`, which carries the constants but **not** the new defeqs, so every
   defeq added is type-correct, and a proof-level inconsistency does not put two sorts at a
   common type. §5. **[analysis]**
6. **Census unchanged, 19 → 19.** Measured at the start and at the end of the session with
   `scripts/sorry-census.lean`. **[machine]**

Three of the brief's premises are corrected in §7. One of them —
*"`VIndRecArg.exists_indep` is a strict dependency on `forallE_inv`"* — is not a measured
dependency at all: `exists_indep`'s forward cone is **empty**.

---

## 1. Census and cones, measured on this commit **[machine]**

`lake env lean scripts/sorry-census.lean`, before and after — **identical**, TOTAL 19:
`Theory.Inductive.Decl` 1, `Theory.Typing.ChurchRosser` 1, **`Theory.Typing.Injectivity` 6**,
`Theory.Typing.UniqueTyping` 1, `Verify.Environment` 1, `Verify.Environment.Boundaries` 1,
`Verify.Soundness` 2, `Verify.TypeChecker.InferType` 1, `Verify.TypeChecker.IsDefEq` 2,
`Verify.TypeChecker.WHNF` 1, `Verify.Typing.Lemmas` 2.

### 1.1 Forward cones (which open statements each target reaches)

Over declaration *values*, theorem bodies included, `allowOpaque := true`:

```
  forallE_inv_stratified  -> []
  weakN_iff               -> []
  forallE_inv             -> [forallE_inv_stratified]
  const_app_inv           -> [forallE_inv_stratified]
  const_forallE_inv       -> [forallE_inv_stratified]
  const_sort_inv          -> [forallE_inv_stratified]
  sort_forallE_inv        -> [forallE_inv_stratified]
  VIndRecArg.exists_indep -> []                              <- §7, brief correction
  NormalEq.descend        -> [forallE_inv, weakN_iff, forallE_inv_stratified]
  NormalEq.trans          -> [forallE_inv, weakN_iff, forallE_inv_stratified]
  NormalEq.parRed         -> [descend, forallE_inv, weakN_iff, forallE_inv_stratified]
  ParRed.church_rosser    -> [forallE_inv, weakN_iff, forallE_inv_stratified]
  IsDefEq.church_rosser   -> [descend, forallE_inv, weakN_iff, forallE_inv_stratified]
```

So the corner has **two** open roots, `forallE_inv_stratified` and `weakN_iff`, and everything
else in `Injectivity.lean` bottoms out in the first. That half of the brief is confirmed.

### 1.2 Reverse cones inside `kernel_sound`'s reach

Transitive users over the import closure of `Verify/Bridge.lean` (i.e. exactly what
`kernel_sound` can use), with internal names included:

| statement | users | reaches `addDecl.WF` | reaches the Bridge export | **direct** consumers |
|---|---|---|---|---|
| `IsDefEqU.forallE_inv_stratified` | 249 | yes | yes | `IsDefEq.uniq`, `piInvStrat_axiom` |
| `IsDefEqU.sort_inv` | 233 | yes | yes | `IsDefEq.uniq` |
| `IsDefEq.uniq` | 232 | yes | yes | `trans_l`, `trans_r`, `uniqU`, `isDefEq_iff`, `prim_domain_nat` |
| `IsDefEqU.weakN_iff` | 169 | yes | yes | `IsDefEq.skips`, `weakN_iff'`, `weak'_iff`, `VExpr.WF.weakN_iff`, `ConditionallyWHNF.weakN_inv` |
| `IsDefEqU.forallE_inv` | 65 | yes | yes | `HasType.piUniq`, `piInv_axiom` |
| `IsDefEqU.sort_forallE_inv` | **0** | no | no | — |
| `IsDefEqU.const_sort_inv` | **0** | no | no | — |
| `IsDefEqU.const_forallE_inv` | **0** | no | no | — |
| `IsDefEqU.const_app_inv` | **0** | no | no | — |

**Two things to read off this table.**

* Four of `Injectivity.lean`'s six holes are **dead in the goal's cone**. They are needed by
  `TrProj.uniq` and `quotReduceRec.WF`, which are themselves `sorry`s, so the edge does not
  exist yet. Work on them buys nothing for `kernel_sound` until those two are written.
* This **corrects `docs/backward-analysis.md` §3** on the current commit: it reported
  `forallE_inv_stratified`'s direct consumers as `IsDefEq.uniq` and `IsDefEqU.forallE_inv`, and
  `forallE_inv`'s as `TrExpr.beta` and `inferApp.loop.WF`. Both moved. `forallE_inv` now
  reaches the stratified form only through `WF.sortUniq'`, and its own direct consumers are
  `HasType.piUniq` and `piInv_axiom`. §7.

---

## 2. The `NormalEq` route, measured and closed **[machine]**

The brief asks whether the manoeuvre that closed facts (A)–(D) — *`VEnv.NormalEq` has no
`trans` constructor, transitivity there is a theorem and `church_rosser` has already paid for
it* — reaches `forallE_inv_stratified`. **It does not, and cannot as the tree stands, because
the payment has not been made: `church_rosser` is downstream of the target.**

Shortest dependency paths, machine-extracted:

```
NormalEq.defeq  →  IsDefEq.transU_r  →  IsDefEq.trans_r  →  IsDefEq.uniq
                →  IsDefEqU.forallE_inv_stratified

NormalEq.trans  →  NormalEq.weakN_iff  →  NormalEq.weakN_inv_DFC
                →  IsDefEqU.forallE_inv   (and, separately, → IsDefEqU.weakN_iff)

ParRed.church_rosser  →  ParRed.triangle  →  IsDefEqU.forallE_inv
```

The first path is the structural one and it is not a bookkeeping accident: `IsDefEq` is
four-place, so *composing two conversions at different types* is a theorem, not a rule, and
that theorem is `uniq`. Every use of `NormalEq.defeq`, `IsDefEq.trans_r`, `IsDefEqU.of_l/of_r`
or `IsDefEqU.defeqDF` pays `uniq`. So the whole `ChurchRosser.lean` development sits *below*
this corner, not above it, and using it here would be circular.

**The K-rule status, re-measured.** `grep KStep` now returns hits in three files —
`KRule.lean`, `KDescend.lean`, `KCanonical.lean` (the last is untracked and red). `ParRed`
still has **eight** constructors — `bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `beta`,
`extra` — and **no `K` constructor**. `KDescend.lean` proves its restatement *relative to a
hypothesis* `hK : KStep Γ e e' → ParRed Γ e e'`, which nothing supplies. So the previous
handoff's §6 verdict stands, for a sharper reason than before: the descent is not unconditional
and `ParRed` is unextended. **[machine]**

**Consequence.** The only way the `NormalEq` manoeuvre could reach this target is if
`ChurchRosser.lean` were re-based on a judgment whose `trans` and `symm` are *rules* — the
`IsDefEqU'` enlargement of `docs/backward-analysis.md` §5. That is a change to
`Theory/Typing/Basic.lean`, which this stream does not own. **[analysis]**

---

## 3. What landed: the obligation narrowed, and the circle re-checked at the narrower point

### 3.1 `PiInvStratApp` **[machine]**

`uniqQ` calls `hstrat` exactly once, in the `app` case:

```lean
have ⟨_, d3, d4, d5⟩ := hstrat hΓ ⟨_, c1⟩ c3 c4
```

`c3` and `c4` carry the **same** index, and the whole first (domain) conjunct was already being
discarded. So the statement the entire `Verify/` cone rests on is

```lean
def PiInvStratApp (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ} {A B A' B' V V' : VExpr} {n : Nat},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    env.HasTypeStratified U Γ (.forallE A B) V true n →
    env.HasTypeStratified U Γ (.forallE A' B') V' true n →
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n
```

New declarations in `Injectivity.lean`, all `sorry`-free except where noted:

| name | what |
|---|---|
| `PiInvStratApp` | the narrowed statement |
| `PiInvStrat.app` | the one-line implication `PiInvStrat → PiInvStratApp` |
| `piInvStratApp_axiom` | its inhabitant, from `forallE_inv_stratified` — **`sorryAx`-tainted, by design** |
| `sortUniq_of_piInvStratApp` | `PiInvStratApp → SortUniq` (was `sortUniq_of_piInvStrat`) |
| `piInvStratApp_of` | `SortUniq → PiInv → PiInvStratApp` |
| `sortUniq_iff_piInvStratApp` | the two, as an `↔` |
| `piInvStratApp_fires` | non-vacuity |
| `sortUniq_of_piInvStrat` | kept as a wrapper; **not** on any consumer's path |

`uniqQ`, `uniqAux`, `WF.sortUniq'`, `WF.uniq'` and `UniqSort.lean`'s `IsDefEq.uniq'` all take
the narrow form now. `piInvStrat_axiom`, `piInv_axiom`, `piInvStrat_of`,
`piInvStrat_of_sortUniq` are unchanged, so `PatWF.lean`'s single point of contact
(`piInv_axiom`) is untouched.

Axioms: `sortUniq_iff_piInvStratApp`, `piInvStratApp_of`, `sortUniq_of_piInvStratApp`,
`uniqAux` → `[propext, Classical.choice, Quot.sound]`; `PiInvStrat.app` → `[propext]`;
`piInvStratApp_fires` → `[propext, Quot.sound]`. **No `sorryAx` in any of them.**

### 3.2 Why this is a narrowing and not a restatement **[machine + analysis]**

*Machine:* `PiInvStrat.app` is proved and the converse is neither proved nor used. The two
dropped components are the domain conjunct `∃ u, IsDefEq Γ A A' (.sort u) ∧ HasTypeStratified
Γ A (.sort u) true n` and the second index `n'`.

*Analysis:* the domain conjunct is exactly the half whose `symm` case was described as the
second obstruction in earlier versions of this document. Dropping it removes that case from the
obligation entirely. What remains is the codomain half, which is where `SortUniq` actually
bites.

### 3.3 Non-vacuity, and why it had to be re-checked **[machine]**

Forcing both stratified hypotheses to the same index could have emptied the statement; and a
witness with `A = A'` would make the conclusion an instance of reflexivity and prove nothing.
`piInvStratApp_fires` avoids both:

* domains `.sort (.imax .zero .zero)` and `.sort .zero` — **syntactically different**, so the
  conclusion is not reflexivity, and the two codomains genuinely live in different contexts,
  which is the transport the conclusion's third component has to perform;
* both Π-types have `HasTypeStratified` derivations at index `1`, the same index;
* it holds over **every** `env`, with no `VEnv.WF`, no constant and no rule;
* `sorryAx`-free.

### 3.4 What the narrowing does **not** do **[machine]**

`sortUniq_iff_piInvStratApp` is the honest answer: the narrow statement is still `SortUniq`
verbatim, relative to `PiInv`. The circle is smaller, not cut. Census 19 → 19.

---

## 4. The circle: the exact failing step, and four repairs walked to it

The failing step, stated once and precisely:

> Inside `uniqQ`'s `app` case at index `n+1`, `hstrat` must return a `HasTypeStratified`
> derivation of the codomain **at the level the conversion is stated at**. The conversion comes
> from plain Π-injectivity applied to an *unstratified* `IsDefEq`, so its level is a function
> of a freshly built derivation whose height the induction never generates. Aligning it with
> the bounded level costs `SortUniq` at an unbounded index, and `uniqQ` has `SortUniq` only at
> indices `< n`.

**Four repairs, each walked to its failing step this session. All [analysis]; do not
re-attempt without reading the failing step.**

1. **Decouple the levels in the conclusion.** State the conclusion as three independent
   existentials (`∃ u, IsDefEq …` and `∃ u₀, HasTypeStratified …` separately). *The
   `forallEDF` and `symm` cases then close on the nose* — the decoupled statement is exactly
   `forallE_inv` plus bookkeeping already available from `h2.forallE_inv'`. **It fails at the
   consumer, not the producer**: `uniqQ` uses `d3`'s level to convert the final type and `d4`'s
   level to talk to the induction hypothesis, and it needs them to be one level. Recovering
   that is `SortUniq` at the same unbounded index. This is the ORCHESTRATOR.md
   "audit against consumers" rule biting: the change is free on the producing side and fatal on
   the consuming side.
2. **Bound the conversion by height.** Replace `HasTypeStratified.defeq`'s unstratified
   `IsDefEq` premise by a height-indexed `IsDefEqStrong` (`HasTypeStrong.defeq` already carries
   an `IsDefEqStrong`, so `stratify` would still go through by taking a `max`). Everything
   becomes bounded — and the bound is **increasing**: Π-injectivity's proof composes `trans`
   steps, so the output height exceeds the input height, and the `SortUniq` instance is needed
   at an index *larger* than the induction's. This is the same defect as the dead
   lexicographic-measure idea, in a form that survives the "the input is not a recursive call"
   objection and dies anyway.
3. **Make the invariant asymmetric** — bound only `n₁`, leave `n₂` free, so an unbounded second
   derivation is admissible. Dies in the **`bvar` case**: the invariant's own conclusion asks
   for `HasTypeStratified Γ B (.sort v) true (n-1)`, and the `bvar` case's only source for it
   is `b2.mono`, which needs `n₂ - 1 ≤ n - 1`. The conclusion's index bound *forces* the
   symmetric hypothesis.
4. **Read the level off the bounded side instead.** Take `u := v₁` (the level `a7` already
   carries) rather than the conversion's `w`. Converting `d3` from `.sort w` to `.sort v₁` is
   `IsDefEqU.of_l`, which is `uniq` again, at the same instance. Symmetrically, converting
   `a7` up to level `w` needs `HasTypeStratified.defeq`, whose premise is `.sort v₁ ≡ .sort w`.
   Both directions are the same equation.

**And one route that is *not* closed, but is not this stream's to take.** Under
`docs/backward-analysis.md` §5's `IsDefEqU'` enlargement — `trans`/`symm`/conversion become
*rules* of the untyped closure — `IsDefEq.uniq` leaves `kernel_sound`'s cone, and with it
`forallE_inv_stratified` and `sort_inv`. That would dissolve this target rather than prove it.
It does **not** remove `forallE_inv`, which is the normalisation half and gets no easier.
`Theory/Typing/Basic.lean` is not this stream's file. **[analysis]**

---

## 4A. The `retype` enlargement, resolved on both routes  *(new this session)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/RetypeCase.lean`** — six
declarations, all `sorry`-free, `#print axioms` block at the end of the file.  It is imported by
nothing; it is a pricing file, and it adds nothing to any cone.

### 4A.1 What Enlarged.lean claims, and what is wrong with it **[machine]**

`Theory/Typing/Enlarged.lean`'s "obligation the enlargement creates" section argues:

> Adding `retype` to `IsDefEq` forces a matching constructor in `IsDefEqStrong` … **That forces
> one in `HasTypeStrong` too**, because `IsDefEqStrong.hasType'` must produce
> `HasTypeStrong Γ e₂ B` from `HasTypeStrong Γ e₂ A` and `HasTypeStrong Γ e₁ B` … And that
> forces one in `HasTypeStratified`, whose induction is what proves `IsDefEq.uniq`.

The first "forces" is false.  `HasTypeStrong.retype` states exactly that step over the judgments
the tree has **today** — no enlargement is needed to state it — and proves it:

```lean
theorem HasTypeStrong.retype (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hpi : PiInvStratApp env U)
    (h1A : env.HasTypeStrong U Γ e₁ A true) (h1B : env.HasTypeStrong U Γ e₁ B true)
    (h2A : env.HasTypeStrong U Γ e₂ A true) : env.HasTypeStrong U Γ e₂ B true
```

It does **not** take the conversion `IsDefEqStrong Γ e₁ e₂ A`: what the case needs is unique
typing at `e₁` and nothing else.  Two supporting lemmas were missing from `Strong.lean` and are
here: `HasTypeStrong.isType` (every `HasTypeStrong` derivation carries a typing of its own type
— eight one-line cases) and `HasTypeStrong.sortConv` (level realignment of such a typing).

Consequence: `HasTypeStrong` and `HasTypeStratified` stay exactly as they are, `uniqQ`'s
induction gains **no** case, and the in-place enlargement introduces **no new open statement**.
`Enlarged.uniqU_of_uniqAcross` is still true; it is simply not the obligation.

### 4A.2 Route A's real price, measured **[machine]**

Reverse cones over declaration *values* (`allowOpaque := true`), internal names skipped — the
`scripts/sorry-census.lean` convention — over the import closure of `Verify/Bridge.lean`:

| declaration | transitive users |
|---|---|
| `IsDefEqU.forallE_inv_stratified` | 201 |
| `IsDefEqStrong.hasType'` | **232** |
| union | 234 |
| in `users(hasType')` but not `users(forallE_inv_stratified)` | **33** |

(The census's 238 for `forallE_inv_stratified` is the same measurement in a wider scope — it
imports `Experimental.ConeJoin`.  The 33-declaration *difference* is stable across both scopes.)

Route A gives `hasType'` the hypothesis `PiInvStratApp`, i.e. adds the edge
`hasType' → forallE_inv_stratified`.  The corner's cone therefore goes **201 → 234**.

And it destroys the disconnecting set.  Cutting the (E) family of twelve retyping lemmas plus
`HasType.piUniq` plus `IsDefEq.weakN_iff'`:

| cuts | `forallE_inv_stratified` users |
|---|---|
| none | 201 |
| (E) | 72 |
| (E) + `piUniq` | 64 |
| (E) + `piUniq` + `weakN_iff'` | **21** |
| the same three, **with Route A's one new edge** | **104** |

So the enlargement re-imports the corner through a larger door than the one it closes.  This is
a *measured* verdict where the previous one ("it could not be established that no restructuring
closes the case") was an absence of evidence.

**Correction to the enlargement study relayed in this stream's brief.**  Its minimal
disconnecting set — `retype`-enlargement + `HasType.piUniq` + `IsDefEq.weakN_iff'` — was priced
by *cutting edges*, which models the (E) family becoming free.  That model omits the edge the
enlargement itself creates at `hasType'`.  Priced with that edge, the set does not disconnect.
The brief's "all three take it to 4" is also not reproducible here: the same three cuts leave 21
in this scope, of which four are the census-dead `const_*_inv`/`sort_forallE_inv` and five are
packaging (`piInvStrat_axiom`, `piInvStratApp_axiom`, `piInv_axiom`, `piInvStrat_of_sortUniq`,
`IsProof.app'_fires`).  Different instrument, not a contradiction — but the number to quote is
21, with the list.

### 4A.3 Route B, and why no restructuring of `uniqQ` closes it **[machine]**

If one avoids Route A's price by adding the constructor after all, the cost lands in `uniqQ`.
`RetypeCaseCore` is that case's obligation **in its weakest useful form**: only the conversion
conjunct of `UniqAux`'s conclusion is demanded, the node's three premises are taken at a *single*
index, and the index bounds `uniqQ` actually offers are kept (`m < n` for the premises, `n₂ ≤ n`
for the competing derivation).  Then:

* `uniqStrat_of_retypeCase` — the obligation at every index gives unique typing for two
  `HasTypeStratified` derivations of one term at unrelated indices;
* `uniqU_of_retypeCase` — hence `IsDefEq.uniq` itself.

**This is `Enlarged.uniqU_of_uniqAcross` with the index bounds kept, and that is what it buys.**
§4's repairs 2 and 3 — "bound the conversion by height", "make the invariant asymmetric" — were
walked to a failing step by analysis.  The collapse above closes them by machine: even the
index-bounded, single-conjunct form of the obligation implies the theorem whose induction it is
a case of.  No re-indexing of `uniqQ` can absorb it.

`retypeCase_of_piInvStratApp` is the other half: the obligation is satisfiable from exactly the
input the tree already pays, so it is the corner restated, not an absurd demand.

**The structural reason, in one line.** `uniqQ` decrements the second derivation's index only by
inverting it *against the first derivation's subject shape* (`intro (.app …)`, `(.bvar …)`, …).
`retype` carries no subject shape — its premise is a derivation of a *different* term — so `n₂`
cannot be decremented and the case's obligation is the invariant at the undecremented index.
Every other constructor of `HasTypeStratified` is subject-directed; `retype` is the only one
that is not. **[analysis]**

### 4A.4 The one question that would change the verdict **[open]**

**Is `HasTypeStrong.retype` provable without `PiInvStratApp`?**  If it is, Route A is free, the
201 → 234 regression evaporates, and the in-place enlargement goes through with no new hole and
no cone cost.

What is known:

* It does **not** collapse.  Instantiating `e₂ := e₁` makes the statement trivial, so — unlike
  `RetypeCaseCore` — it does not imply `uniq` back.  Several attempts to derive `SortUniq` from
  it failed for a concrete reason: to get information out you need a term `e₂ ≠ e₁` that shares a
  type with `e₁` and whose membership in `B` is decidable by inversion, and in a bare
  environment there is no such term. **[analysis]**
* Semantically it is *weaker* than unique typing: it says the type-sets of any two terms are
  disjoint-or-equal, where `uniq` says each type-set is a single conversion class. **[analysis]**
* It is not refutable from the `unsafeDef` direction, for the reason in §5. **[analysis]**

That gap — a statement strictly weaker than `uniq`, whose only known proof goes through `uniq` —
is the most promising thing in this corner right now, and it did not exist as a named target
before this session.

---

## 4B. `retypes`: the obligation Route A actually has, proved  *(session of 2026-08-30, later)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/RetypeAdmissible.lean`** —
seventeen declarations, all `sorry`-free, `#print axioms` block at the end.  Imported by nothing; like
`RetypeCase.lean` it adds nothing to any cone.

### 4B.1 The premise §4A.4 threw away **[machine]**

`RetypeCase.lean`'s `HasTypeStrong.retype` states the `hasType'` `retype` case as

> `e₁ : A → e₁ : B → e₂ : A → e₂ : B`

and its docstring says, as if it were a virtue, that *"the conversion premise
`IsDefEqStrong Γ e₁ e₂ A` is not needed and is not taken"*.  It is not needed **by that
proof** (which goes through `uniqAux`, i.e. unique typing, and so needs nothing else).  But
the case **carries** it: `hasType'`'s `retype` node is built from `IsDefEqStrong Γ e₁ e₂ A`
*together with* `HasTypeStrong Γ e₁ B`, and inside an induction one has the premise, not only
its induction hypothesis.  Dropping it produced a statement with no attack surface: there is
nothing to induct on, since its three premises are typings of two unrelated terms.  The
conversion-free form **implies** the conversion-carrying one (via `hasType'`); the converse is
not known, so it is at least as strong and plausibly strictly so.

With the premise kept, the statement is

```lean
theorem IsDefEqStrong.retypes (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U) :
    ∀ {Γ e₁ e₂ A}, env.IsDefEqStrong U Γ e₁ e₂ A → CtxStrong env U Γ →
      ∀ {B}, (env.HasTypeStrong U Γ e₁ B true ∨ env.HasTypeStrong U Γ e₂ B true) →
        env.IsDefEqStrong U Γ e₁ e₂ B
```

and it is proved by induction on the conversion.  `HasTypeStrong.retype_of_conv` is the
`hasType'` case read off it; `HasTypeStrong.retype_of_conv'` is the same in the hypothesis
shape the consumers carry (`Ordered env` + `OnCtx`, which `IsDefEq.strong` already has, so
placing the obligation there costs **no** new hypothesis).

### 4B.2 Nine rules free, four residual — and the pattern is the point **[machine]**

| rule | cost |
|---|---|
| `bvar`, `symm`, `trans`, `defeqDF` | free (structural) |
| `sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF` | free (congruence) |
| `beta`, `eta`, `proofIrrel`, `extra` | **residual** |

The congruence rules are free for a reason that is worth stating, because it is exactly the
reason `SortUniq` does *not* appear.  In a congruence rule the two sides have the same head,
so a base typing of the left side is rebuilt for the right side **at the very same type**,
from the induction hypotheses of the sub-conversions.  No two levels are ever compared.  In
`appDF`, the induction hypothesis at the function turns `f : .forallE A₀ B₀` — whatever
Π-type the *typing* derivation chose, which need not be the one the *conversion* is indexed
at — into `f ≡ f' : .forallE A₀ B₀`; `IsDefEqStrong.instDF` supplies the codomain congruence
and `appDF` re-fires at `B₀.inst a`.  `lamDF`/`forallEDF` are the same move with
`IsDefEqStrong.defeqDF_l` doing the context conversion.  The inner induction that strips
`HasTypeStrong.defeq` wrappers is `HasTypeStrong.peelTo`, also new here.

The four residuals are the rules whose two sides have **unrelated head shapes**, so a base
typing of one side says nothing about the other.  Each is stated with the entire premise list
of its own rule available plus the *peeled* (`false`, i.e. non-`defeq`) base typing of one
side — the weakest form the induction ever needs, which is the right polarity for a hypothesis
(`ORCHESTRATOR.md` rule 3).

### 4B.3 Pricing, non-vacuity, collapse test **[machine]**

* **Upper bound.**  `retypes_of_piInvStratApp`: all four residuals follow from
  `PiInvStratApp` through `uniqAux` (`uniqStrong_of_piInvStratApp`,
  `{beta,eta,proof,extra}Retype_of_uniqStrong`).  So nothing here is a *new* obligation; the
  question is only whether they are strictly weaker.
* **Non-vacuity.**  `retypes_fires` runs the theorem over **every** environment at an instance
  with `e₁ ≠ e₂` **and** `A ≠ B` syntactically (`.sort (.imax .zero .zero) ≡ .sort .zero`,
  typed at `.sort (.succ (.imax .zero .zero))` and re-indexed at `.sort (.succ .zero)`), and
  that instance goes through the `sortDF` case, which uses **none** of the four residuals.  So
  the conclusion is neither reflexivity nor the input re-indexed at its own type.
* **Collapse test** (`ORCHESTRATOR.md` rule 5) — passes, by inspection of the residuals'
  premises: `BetaRetype` fires only when the left endpoint is a β-redex, `EtaRetype` only at
  an η-expansion, `ExtraRetype` only at an `env.defeqs` instance, `ProofRetype` only when the
  shared type is a proposition inhabited by both endpoints.  None of those can be met by a
  general `IsDefEqStrong Γ e₁ e₂ A`, so the reduction is proper and not a restatement.
  **[analysis]**
* **No negative control of the rejection kind is available, and the reason is the finding.**
  Every neighbouring weakening (e.g. replacing "`B` is a type of `e₁`" by "`B` is a type in
  `Γ`") is refuted only by showing some `IsDefEqStrong Γ e₁ e₂ B` *underivable*, and this tree
  has no inversion principle that pins a term's types without exactly the content of
  `SortUniq`.  Recorded per rule 4: *"no witness" is not evidence of truth.* **[analysis]**

### 4B.4 The one thing that does not transfer to the enlarged judgment for free **[analysis]**

`retypes` is about the judgment the tree has today.  Under the in-place enlargement
(`IsDefEqStrong` gains `retype`), `weakN`, `instN`, `instL`, `mono`, `defeq`, `hasType`,
`isType'` and `forallE_inv'` each gain a `retype` case discharged by a premise's induction
hypothesis, and `HasTypeStrong` gains no constructor at all, so `refl` and `peelTo` are
untouched.  **But `retypes` and `hasType'` would then have to be proved by one simultaneous
induction**, and exactly one line forces it: `retypes`' `trans` case reaches `e₂ : B` through
`d1.hasType'.2` where `d1` is *constructed* from an induction hypothesis, not a
sub-derivation.  Merging costs nothing — conclude
`IsDefEqStrong Γ e₁ e₂ B ∧ e₁ : B ∧ e₂ : B` and read `e₂ : B` off the induction hypothesis
— and the merged induction's new `retype` case is then discharged by the *first* premise's
induction hypothesis alone.  The merge is **not** carried out here (the enlarged judgment is
not defined in this tree); what *is* checked is that the appeal to `hasType'` occurs in
exactly one case.

### 4B.6 How much *not* to read into this **[analysis]**

The four residuals are localised, not known to be weak.  Each one asks for the same thing in a
different place: relate the type its own rule is indexed at to an *arbitrary base type of one
of the two endpoints* — which is unique typing at that endpoint, restricted to one term shape.

* `BetaRetype` needs it at `.lam A e`, i.e. Π-injectivity.  Plain `PiInv`
  (`IsDefEqU.forallE_inv`) is **not** enough on its own: the two Π-types are related through a
  chain of `HasTypeStrong.defeq` wrappers, and composing those into the single `IsDefEqU` that
  `PiInv` consumes is composition-at-different-types, i.e. `uniq`.  This is the four-place
  obstruction of §2, reappearing where one would like the normalisation half alone to pay.
* `EtaRetype` and `ExtraRetype` are the same shape at an η-expansion and at a `df.lhs`
  instance.
* `ProofRetype` is **not** normalisation content: it is unique typing at an arbitrary proof.
  It is the residual worth attacking first, precisely because it is the one this corner has
  never named.

So this section does not claim the residuals are free.  It claims three things, all measured:
nine of thirteen rules are free **unconditionally**, the obligation is localised to four named
rule instances instead of "unique typing", and the statement §4A.4 asked about was not the
obligation.

### 4B.5 What this does and does not do to Route A's price **[machine]**

Re-measured on this commit, same instrument and scope as §4A.2 (reverse cones over
declaration values, `allowOpaque := true`, internal names skipped, import closure of
`Verify/Bridge.lean`):

| declaration | transitive users |
|---|---|
| `IsDefEqU.forallE_inv_stratified` | 209 |
| `IsDefEqStrong.hasType'` | 240 |
| `IsDefEq.strong` | 243 |
| union with `hasType'` | 242 |
| union with `strong` | 245 |
| in `users(hasType')` but not `users(forallE_inv_stratified)` | **33** |
| in `users(strong)` but not `users(forallE_inv_stratified)` | 36 |

(§4A.2 measured 201 / 232 / 234 / 33 earlier the same day; the tree grew, and **the
33-declaration difference is unchanged**, as §4A.2 predicted.)

So: if the four residuals are discharged from `PiInvStratApp`, Route A still costs
209 → 242 and §4A.2's verdict stands unchanged.  **What has changed is what the open question
is.**  It was "prove `HasTypeStrong.retype`", a statement with no induction to do and no known
route but unique typing.  It is now "prove four residuals about β, η, δ and proof
irrelevance", each with its own rule's premises in hand.  That is a different kind of target,
and it is the first time this corner has produced one that is *not* a restatement of itself.

---

## 4C. `ProofRetype` decided down to three head shapes  *(third session of 2026-08-30)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/ProofRetypeHeads.lean`** — nineteen
declarations, all `sorry`-free, with a `#print axioms` block at the end (no `sorryAx`
anywhere).  It imports `RetypeAdmissible.lean` and `SortUniq.lean` and is imported only by
`Experimental/ConeJoin.lean`, so it adds nothing to any cone that reaches `kernel_sound`.
**The one import line added to `ConeJoin.lean` is the only edit outside this stream's own
files**, and it is there because both instruments measure that file's closure: a leaf module
outside it is invisible to `scripts/dup-names.lean` and `scripts/sorry-census.lean`.

### 4C.1 Verdict **[machine + analysis]**

`ProofRetype` is **not decided** — neither proved nor refuted.  What *is* decided is that it
was the wrong thing to single out, and the two reasons §4B gave for singling it out are both
wrong.

### 4C.2 The four residuals are one statement, and the induction is unnecessary **[machine]**

```lean
def BaseUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e A B}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)
```

`retypeAt_of_baseUniq` re-indexes *any* `IsDefEqStrong Γ e₁ e₂ A` at *any* base type of either
endpoint, from `BaseUniq` and `Ordered env`.  Its proof mentions no rule: a rule's premises are
used only to build that rule's own conclusion, which is then handed to this lemma.  So

* `proofRetype_of_baseUniq`, `betaRetype_of_baseUniq`, `etaRetype_of_baseUniq`,
  `extraRetype_of_baseUniq` are the same one-line corollary four times, and
* `retypes_of_baseUniq` reproves `IsDefEqStrong.retypes` from `BaseUniq` **without inducting
  over `IsDefEqStrong`**.  The thirteen-case induction of `RetypeAdmissible.lean` is not needed
  for it; that file's real content is the nine free *congruence* cases, which is a different
  (and still correct) claim.

**Correction to §4B.6.**  `ProofRetype` is not "the odd one out"; it is one instantiation of
`BaseUniq`, and so are the other three.

### 4C.3 The `defeq` chain is walked, not composed **[machine]**

§4B.6 and `RetypeAdmissible.lean`'s docstring say plain Π-injectivity cannot discharge
`BetaRetype` because *"the two Π-types are related through a chain of `HasTypeStrong.defeq`
wrappers, and composing those into the single `IsDefEqU` that `PiInv` consumes is
composition-at-different-types, i.e. `uniq`."*  **The chain does not have to be composed.**

`HasTypeStrong.peelDown` walks it one `defeqDF` at a time, transporting the conversion the rule
already has down to a *base* type of the endpoint, and it takes **no hypothesis at all** — no
`Ordered`, no `CtxStrong`, no `SortUniq`.  Composition is needed only if the chain is wanted as
an *equation*: that is `HasTypeStrong.peelEq`, and it is the single place in this file where a
level is compared with a level, which is why it — and only it — takes `SortUniq`.

So the four-place obstruction of §2 does **not** apply to the residuals.  It applies to the
converse direction of §4C.5.

### 4C.4 Three of six head shapes are free; the residual is three **[machine]**

`baseUniq_of` discharges, with **no hypothesis**:

| head | why it is free |
|---|---|
| `.bvar` | `Lookup.uniq` — the two base types are syntactically equal |
| `.const` | `env.constants` is a function — the two base types are syntactically equal |
| `.sort` | base typings of `.sort l` are `.sort (.succ l')` and `.sort (.succ l'')` with `l ≈ l'`, `l ≈ l''`; `sortDF` closes it |

and reduces `BaseUniq` to three named hypotheses, `BaseUniqApp`, `BaseUniqLam`,
`BaseUniqForallE`.  Their prices, each machine-checked:

| head | discharged by | Π-injectivity? |
|---|---|---|
| `.forallE` | `SortUniq` **alone** — `baseUniqForallE_of_sortUniq` | no |
| `.lam` | unique typing at the **body**, a proper subterm — `baseUniqLam_of_uniqStrong` | no |
| `.app` | unique typing at the **function** *plus* `PiInv` — `baseUniqApp_of` | **yes** |

**Correction to §4B.6 and to the brief that set this session.**  *"`ProofRetype` is unique
typing at an arbitrary proof, which is not normalisation content at all"* is wrong: the term
whose base type is taken is unrestricted, so it ranges over applications, and at an application
the obligation is Π-injectivity.  `ProofRetype` is not the cheap residual; it contains the
`.app` case, and hence the same content `BetaRetype` does, plus the `.forallE` case, which is
`SortUniq`.

### 4C.5 §4B.5's open question, answered **[machine]**

* `baseUniq_of_uniqStrong` : `UniqStrong env U → BaseUniq env U`  *(one line)*
* `uniqStrong_of_baseUniq` : `Ordered env → SortUniq env U → BaseUniq env U → UniqStrong env U`

So `BaseUniq` is **equivalent to unique typing over `HasTypeStrong`, modulo `SortUniq`**.  Since
the four residuals follow from `BaseUniq` (§4C.2) and `BaseUniq` follows from `UniqStrong`,
which follows from `PiInvStratApp` (`uniqStrong_of_piInvStratApp`, §4B.3), the whole residual
sits inside the corner and cannot be strictly weaker except by exactly the amount `SortUniq`
accounts for.  §4B.5 left *"whether they are strictly weaker is open"*; the answer is **no, not
modulo `SortUniq`** — and `sortUniq_iff_piInvStratApp` (§3, given `PiInv`) closes the circle.

### 4C.6 Non-vacuity, negative control, collapse test **[machine, except where marked]**

* **`proofRetype_fires`** — over **every** `Ordered` environment, `ProofRetype` fires at
  `Γ = [prhB, prhA]`, `h = .bvar 1`, `h' = .bvar 0`, `p = prhB`, `X = prhA`, where
  `prhA = ∀ (X : Sort (imax 0 0)), (∀ Y : Prop, Y)` and `prhB = ∀ (X : Prop), (∀ Y : Prop, Y)`.
  The two endpoints are syntactically different **and** `p ≠ X` syntactically, so the
  conclusion is neither reflexivity nor the `proofIrrel` rule's own conclusion.  It goes
  through the free `bvar` case.
* **`baseUniqApp_nonvacuous`** — over every `Ordered` environment, an application with **two
  syntactically different base types**: with
  `Γ = [(X : Type) → Sort (imax 0 0)]`, the term `.app (.bvar 0) (.sort .zero)` is base-typed
  at both `.sort (.imax .zero .zero)` and `.sort .zero`.
* **`base_types_not_syntactically_unique`** — the *rejection-style negative control* §4B.3 said
  was unavailable, for this statement: the neighbouring strengthening *"two base typings of the
  same term have syntactically equal types"* — which would make `BaseUniq` trivial and which
  **is** how all three free cases are discharged — is **false**, at a witness that differs from
  the free cases in no arity and no shape.  This is a control for the free/residual split, not
  for `ProofRetype` itself; §4B.3's statement about `ProofRetype` still stands.
* **Collapse test** (`ORCHESTRATOR.md` rule 5): `BaseUniqApp`, `BaseUniqLam` and
  `BaseUniqForallE` each fire only at their own head, and `proofRetype_fires`' witness is at a
  `.bvar`, which none of the three admits.  So `baseUniq_of` is a reduction and not a
  restatement.  **[machine witness, analysis reading]**

### 4C.7 What is *not* claimed **[analysis]**

Every implication in §4C.4 is an **upper** bound.  Nothing here shows a residual *requires*
Π-injectivity — only that Π-injectivity discharges the `.app` case and that nothing weaker is
known to.  No refutation is offered either: a refutation of `BaseUniq` needs an `Ordered`
environment in which some term has two base types that are **not** convertible, and `Ordered`
type-checks every `defeqs` entry, so such an environment exists only where Π-injectivity itself
fails in it.  Establishing *that* is an underivability proof, and this tree still has no
instrument for one (§5, §4B.3).  Per `ORCHESTRATOR.md` rule 4: *"no witness" is not evidence of
truth.*

Two routes were considered and dropped, with the step each fails at:

1. **Refute `BaseUniq` at a junk `Ordered` environment.**  Add a type-correct `defeqs` entry
   `∀x:A, B ≡ ∀x:A, B' : .sort .zero` (allowed: `VDefEq.WF` asks only that both sides are typed
   at `df.type`), give `f` the first Π-type, and `.app f a` acquires the two base types
   `B.inst a` and `B'.inst a`.  **Fails at:** showing those two are not convertible.  A
   proof-irrelevant model collapses all propositions with the same truth value, so it cannot
   separate them; and any model that validates the junk entry must make the two Π-types equal,
   which for an inhabited domain forces the codomains equal too.
2. **Extract a lower bound from `ProofRetype`.**  `IsDefEqStrong.hasType` turns its conclusion
   into *"every proof of `p` is typeable at `X`"*, which is real content.  **Fails at:** turning
   that back into a type *equation* — there is no inversion principle for
   `IsDefEqStrong Γ h h' X` that pins `X`, which is the same wall as everywhere else in this
   corner.

---

## 4D. `BaseUniq` by induction on the term  *(fourth session of 2026-08-30)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/BaseUniqTerm.lean`** — 23
declarations (2 defs, 21 theorems), all `sorry`-free, `#print axioms` block at the end.  It imports
`ProofRetypeHeads.lean` and is imported only by `Experimental/ConeJoin.lean` (one import line,
the only edit outside this stream's own files), so it adds nothing to any cone that reaches
`kernel_sound`.

### 4D.1 The open check of §8 item 1, settled **[machine]**

> *"What has to be checked is that `uniqStrong_of_baseUniq` can be applied at a proper subterm
> without re-entering the whole statement."*

**It can.**  The reason is one line about `HasTypeStrong.peelEq`: peeling `defeq` wrappers
changes the *type* and never the *subject*, so `uniqStrong_of_baseUniq`'s proof, run at a fixed
subject `e`, consumes `BaseUniq` **only at `e`**.  Making that visible to the elaborator is the
whole trick:

```lean
def BaseUniqAt   (env : VEnv) (U : Nat) (e : VExpr) : Prop := …   -- both typings at flag `false`
def UniqStrongAt (env : VEnv) (U : Nat) (e : VExpr) : Prop := …   -- both typings at flag `true`

theorem uniqStrongAt_of_baseUniqAt (henv : Ordered env) (hsu : env.SortUniq U)
    {e : VExpr} (hbu : BaseUniqAt env U e) : UniqStrongAt env U e
```

and then `baseUniqAt_of_sortUniq_piInv : Ordered env → SortUniq → PiInv → ∀ e, BaseUniqAt env U e`
by pattern match on `e`.

**Read the elaborated program, not the source layout** (`ORCHESTRATOR.md`).  `#print` on the
declaration gives `VExpr.brecOn`, and `#print` on its step function `…._f` gives the six
branches with their recursive calls named:

```
| .bvar _      => baseUniqAt_bvar                       -- no recursive call
| .sort _      => baseUniqAt_sort                       -- no recursive call
| .const _ _   => baseUniqAt_const                      -- no recursive call
| .forallE _ _ => baseUniqAt_forallE hsu                -- no recursive call
| .lam _ b     => baseUniqAt_lam henv (uniqStrongAt_of_baseUniqAt henv hsu x.2.1)
| .app f _     => baseUniqAt_app henv hpi (uniqStrongAt_of_baseUniqAt henv hsu x.1.1)
```

`x.1.1` is the `below`-field for the function, `x.2.1` the one for the body.  No branch reaches
the statement at any term other than a direct subterm.  This is the machine answer; it is not
read off the source.

### 4D.2 **Correction to the brief: the prize as phrased was already available** **[machine]**

The brief called the target *"`SortUniq + PiInv → retypes`, with no `VEnv.WF`, no
stratification, no `PiInvStratApp`"* and treated the implication as the prize.  **The
implication was already reachable** by composing two things already in the tree:

```lean
Injectivity.piInvStratApp_of          : VEnv.WF env → SortUniq → PiInv → PiInvStratApp
RetypeAdmissible.retypes_of_piInvStratApp : VEnv.WF env → PiInvStratApp → … → Retypes
```

`retypes_of_sortUniq_piInv_via_strat` in the new file is that composite, written out so the
comparison is a hypothesis list and not an assertion.  The measured delta is:

| | via `PiInvStratApp` (already available) | `retypes_of_sortUniq_piInv` (new) |
|---|---|---|
| environment hypothesis | `VEnv.WF env` | **`Ordered env`** |
| `#print axioms` | `propext, Classical.choice, Quot.sound` | **`propext, Quot.sound`** |
| machinery used | `HasTypeStratified`, `uniqAux`, height induction | none |
| induction | over `IsDefEqStrong`, height-indexed | **structural recursion on `VExpr`** |

So the contribution is a **weaker hypothesis and a structurally different proof**, not a new
implication between named statements.  Anyone quoting "no `PiInvStratApp`" should quote the row
that carries it: `VEnv.WF` → `Ordered`, and `Classical.choice` dropped.

### 4D.3 What is proved **[machine]**

| name | statement |
|---|---|
| `uniqStrongAt_of_baseUniqAt` | `Ordered → SortUniq → BaseUniqAt e → UniqStrongAt e` |
| `baseUniqAt_bvar` / `_sort` / `_const` | free, no hypothesis |
| `baseUniqAt_forallE` | from `SortUniq`, no recursive call |
| `baseUniqAt_lam` | from `Ordered` + `UniqStrongAt` at the **body** |
| `baseUniqAt_app` | from `Ordered` + `PiInv` + `UniqStrongAt` at the **function** |
| `baseUniqAt_of_sortUniq_piInv` | the recursion |
| `baseUniq_of_sortUniq_piInv` | `Ordered → SortUniq → PiInv → BaseUniq` |
| `uniqStrong_of_sortUniq_piInv` | `… → UniqStrong` (compare `uniqStrong_of_piInvStratApp`, which takes `VEnv.WF`) |
| `retypes_of_sortUniq_piInv` | `… → Retypes` |
| `retype_of_conv_of_sortUniq_piInv` | the `hasType'` `retype` case |
| `{beta,eta,proof,extra}Retype_of_sortUniq_piInv` | the four computation-rule residuals |

All `[propext, Quot.sound]`; none mentions `sorryAx`.

### 4D.4 Non-vacuity and the negative control **[machine]**

* **`baseUniqAt_app_fires`** — over every `Ordered` environment, the `.app` branch fires at
  `ProofRetypeHeads.baseUniqApp_nonvacuous`'s witness, where the two base types are
  **syntactically different**, so the conclusion is neither `refl` nor the input re-indexed at
  its own type; and its recursive call is at the function `.bvar 0`, so the descent visibly
  happens.  `SortUniq` and `PiInv` are *carried*, not discharged — this fires the branch and is
  **not** evidence the two hypotheses are jointly satisfiable (`ORCHESTRATOR.md` rule 4).
* **The negative control, and it is the one that matters here.**  The recursive calls take
  `UniqStrongAt` (flag `true`) at the subterm, not `BaseUniqAt` (flag `false`).  That single
  `Bool` is the *only* thing that puts `SortUniq` in the result:
  `uniqStrongAt_of_baseUniqAt` is the file's sole consumer of `SortUniq`, so the neighbouring
  reading — *"the recursion needs only `BaseUniqAt` at the subterm"* — would deliver
  `PiInv → retypes` with **no `SortUniq` at all**, which is a strictly stronger and much more
  valuable result.  It is **false**: `app_fn_premise_is_not_base` shows that in that same
  witness the second `.app` node's function premise
  `HasTypeStrong [prhPi1] (.bvar 0) prhPi2 true` has **no** `false` derivation, because
  `Lookup` pins the only base type of `.bvar 0` to `prhPi1`.  `base_flag_not_droppable` states
  the rejection.  The two readings differ in one `Bool`: same arity, same shape, same head —
  no arity or shape check separates them.

### 4D.5 The localisation goes through at the subject and **not** at the type **[analysis]**

The obvious next move is to localise `SortUniq` the same way and get rid of it.  It does not
work, and the failing step is exact:

* `baseUniqAt_forallE` *would* localise — it uses `SortUniq` only at the Π's own domain `D` and
  body `b`, both proper subterms.
* `uniqStrongAt_of_baseUniqAt` does **not**.  It goes through `HasTypeStrong.peelEq`, whose
  `defeq` case (`ProofRetypeHeads.lean`, the `| defeq h1 h2 h3 h4 h5 _ _ ih5` branch) applies
  `SortUniq` at the derivation's intermediate **type** `A` — an arbitrary term, with no
  structural relation to the subject.
* Proving `UniqStrongAt` by induction on the *derivation* instead hits the same wall in the same
  case: the two conversions `A' ≡ A : .sort u` and `A' ≡ B : .sort w` are indexed at different
  sorts, and composing them is the four-place obstruction of §2.

So `SortUniq` is **not** a passenger here (`ORCHESTRATOR.md` rule 6): it is consumed at a place
the term recursion does not reach.

### 4D.6 What is *not* claimed **[analysis]**

Every implication is an upper bound; nothing shows `BaseUniq` *requires* `PiInv`.  No cone
moved: `BaseUniqTerm.lean` is imported only by `ConeJoin.lean`.  The census is unchanged, and
the corner's circle is **not** cut — `sortUniq_iff_piInvStratApp` still says `SortUniq` and
`PiInvStratApp` are interderivable given `PiInv`.

---

## 4E. The `peelEq` `defeq` case is **broken** — the chain, not the equation  *(fifth session of 2026-08-30)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/BaseUniqChain.lean`** — 40
declarations (1 inductive, 5 defs, 34 theorems), all `sorry`-free, `#print axioms` block at the end.  It imports
`ProofRetypeHeads.lean` and is imported by `BaseUniqTerm.lean` (one line, so that
`Experimental/ConeJoin.lean` — not this stream's file — reaches it without an edit outside this
stream's own files).  Nothing else was touched except the superseded paragraph in
`BaseUniqTerm.lean`'s own docstring and this document.

### 4E.1 The verdict: **broken**, and §4D.5 is wrong as stated **[machine]**

§4D.5 said `SortUniq` is consumed inside `peelEq`'s `defeq` case *"at a place the term recursion
does not reach"*, and item 1 of §8 told the next reader not to re-attempt the localisation.
**That is false as stated**, and the brief's own guess was right: working rule 5 applies to
`peelEq` exactly.  `peelEq` is an inversion; what it discards is that the `defeq` wrappers form
a *walk*.  Consumers only ever need the walk.  Composition into a single **equation** is the
only thing that puts two conversions at different sorts side by side, and that is the entire
job `SortUniq` was doing there.

State the conclusion as a chain

```lean
inductive ConvC (env) (U) (Γ) : VExpr → VExpr → Prop
  | refl : ConvC env U Γ A A
  | step : env.IsDefEqStrong U Γ A B (.sort u) → ConvC env U Γ B C → ConvC env U Γ A C
```

(the links are **not** required to be at the same sort) and the two blocked steps become free:

| | `ProofRetypeHeads` / `BaseUniqTerm` | `BaseUniqChain` |
|---|---|---|
| peel the `defeq` chain | `peelEq`: `Ordered`, `SortUniq`, `CtxStrong` | `peelChain`: **no hypothesis** |
| base ⇒ full unique typing | `uniqStrongAt_of_baseUniqAt`: `Ordered`, `SortUniq` | `uniqStrongCAt_of_baseUniqCAt`: **no hypothesis** |

Both are checked to depend on `[propext]` alone — not even `Quot.sound`.  **Nowhere in the file
are two conversions indexed at different sorts composed**, so §2's four-place obstruction never
arises in this development.

### 4E.2 Where the demand moved, head by head **[machine]**

`baseUniqCAt_of` still elaborates to `VExpr.brecOn`; `#print`ing its step function
`baseUniqCAt_of._f` gives (recursive calls named as the elaborator emits them):

```
| .bvar _        => baseUniqCAt_bvar                       -- no recursive call
| .sort _        => baseUniqCAt_sort                       -- no recursive call
| .const _ _     => baseUniqCAt_const                      -- no recursive call
| .forallE D b   => baseUniqCAt_forallE hsi (…x.1.1) (…x.2.1)   -- TWO recursive calls
| .lam _ b       => baseUniqCAt_lam henv (…x.2.1)
| .app f _       => baseUniqCAt_app henv hpi (…x.1.1)
```

The row that changed is `.forallE`.  In `BaseUniqTerm` it makes **no** recursive call and pays
`SortUniq`; here it makes **two** — at the Π's own domain and its own body, both proper
subterms — and pays `ConvSortInv`.  So `SortUniq` is not consumed at an unreachable place; the
two subterm calls plus one chain-inversion replace it.

### 4E.3 The residual, and the honest price **[machine]**

```lean
retypes_of_convInv : Ordered env → ConvSortInv env U → ConvPiInv env U →
  IsDefEqStrong U Γ e₁ e₂ A → CtxStrong env U Γ → Retypes env U Γ e₁ e₂
```

with **no `SortUniq`, no `VEnv.WF`, no stratification, no `PiInvStratApp`**, on
`[propext, Quot.sound]`.  `ConvSortInv` is *a chain between two syntactic sorts forces the
levels equivalent*; `ConvPiInv` is Π-injectivity along a chain.

**The circle is not cut, and both directions are machine-checked** — quote this row with the
headline:

* `convSortInv_of_sortUniq`, `convPiInv_of_sortUniq_piInv` — the old hypotheses imply the new
  ones, so the new theorem **subsumes** the old: `retypes_of_sortUniq_piInv_via_chain`
  re-derives `BaseUniqTerm.retypes_of_sortUniq_piInv` at a statement checked to be the same one
  (both were elaborated against a written-out common type).
* `sortUniq_of_convInv` — the new hypotheses give `SortUniq` straight back (run the recursion at
  the term in question, invert the resulting chain).  `sortUniq_iff_convSortInv` states the
  equivalence, given `ConvPiInv`.

* `peelEq_of_peelChain` — `peelEq` **is** `peelChain` followed by `ConvC.collapse`, and
  `collapse` is the only consumer of `SortUniq` in the composite.  This is the split, stated as
  a theorem rather than as prose: everything `SortUniq` did in `peelEq` other than align the
  sorts of adjacent links was bookkeeping the chain absorbs.

So the contribution is **not** a weaker hypothesis set.  It is: the four-place obstruction is
gone from this route; `SortUniq`'s residual role is exactly *reading a level off a conversion*
(sort injectivity), which is normalisation content; and the two remaining hypotheses are the
chain forms of the corner's two already-named halves rather than a statement about arbitrary
terms in arbitrary derivations.

### 4E.4 Non-vacuity and the negative controls **[machine]**

The two new recursive calls are fired separately, over **every** environment, at Π-terms whose
two base types are *syntactically different*, and the two witnesses differ in which subterm
carries the difference:

* `forallE_body_fires` — `(X : Type) → Sort (imax 0 0)`, base types
  `.sort (imax 2 (succ (imax 0 0)))` and `.sort (imax 2 (succ 0))`: the difference is entirely
  in the **codomain** level.
* `forallE_domain_fires` — `(X : Prop) → Prop`, base types `.sort (imax (succ 0) (succ 0))` and
  `.sort (imax (succ (imax 0 0)) (succ 0))`: entirely in the **domain** level.

**The rejections.**  Each one-call reading is refuted outright, at the level algebra:
`forallE_body_call_not_droppable` refutes *"the domain equivalence determines the Π's level"*
(`imax 0 0 = 0` but `imax 0 1 = 1`), and `forallE_domain_call_not_droppable` refutes
*"the codomain equivalence does"* (`imax 0 1 = 1` but `imax 2 1 = 2`).  So neither call is a
passenger.  `baseUniqCAt_app_fires` re-fires the `.app` branch through the chain-valued
conclusion at `ProofRetypeHeads.baseUniqApp_nonvacuous`'s witness.

`ConvSortInv` and `ConvPiInv` are *carried* by these witnesses, not discharged: firing a branch
is not evidence they are jointly satisfiable (`ORCHESTRATOR.md` rule 4).

### 4E.5 What is *not* claimed **[analysis]**

Every implication is an upper bound; nothing shows `ConvSortInv` is necessary and no refutation
of it is offered.  No cone moved — `BaseUniqChain.lean` is reached only through
`BaseUniqTerm.lean` and `ConeJoin.lean`, neither of which is in `kernel_sound`'s cone.  The
census is unchanged (19, byte-identical listing before and after).  In particular this does
**not** touch `forallE_inv_stratified`: it removes `SortUniq` from one route to `retypes`, and
`retypes` was never the open root.

---

## 4F. The **negative** conjuncts, and a vacuous supply upstream  *(sixth session of 2026-08-30/31)*

New file, owned by this stream: **`Lean4Lean/Theory/Typing/InjSortPiModel.lean`** — 31
declarations (5 defs, 26 theorems), all `sorry`-free, `#print axioms` block at the end.  It
imports `Theory/SemanticRouteClosed.lean` and `Theory/Typing/RigidNodeCircle.lean` and is
imported by **nothing** — `Experimental/ConeJoin.lean` was NOT edited (five streams collided on
it earlier the same day).  **The import line the next orchestrator should add is:**

```lean
import Lean4Lean.Theory.Typing.InjSortPiModel
```

Nothing else in the tree was touched except `docs/vacuity-ledger.md` (rows 23–25 and a
correction to row 12) and this document.

### 4F.1 The brief's framing, corrected **[machine]**

The brief said: *"`Theory/SemanticRouteClosed.lean` measured the semantic route to this corner …
no argument from `Theory/SetModel/` can close your target."*  True of the target as a whole, and
**false of one of its named conjuncts** — and the reason is a polarity distinction that neither
that file nor this document had made.

`RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes the second hole into five conjuncts.
Two are **positive** (`PiInv`, `RigidConstAppInv`): they ask for a *derivation*, so the model
would have to run backwards, which is faithfulness, which no soundness model has.  **Three are
negative** — `RigidSortPiDisj`, `RigidConstPiDisj`, `RigidConstSortDisj` — and a negative
statement is exactly what soundness alone can settle: assume the conversion, push it through
part 4, contradict a set fact.  The derivation is a hypothesis, never a conclusion, so
faithfulness never appears.  `SemanticRouteClosed.lean` measured only `SortUniq` (part 3) and
`PiInv`'s domain conjunct (part 4) — both positive — and concluded the model "helps precisely as
far as `SortInv` and no further".  Three fifths of the second hole were never measured.

### 4F.2 What is proved **[machine]**

| name | statement |
|---|---|
| `singleton_pt_ne_pt`, `true_not_mem_piProp`, `true_not_mem_function` | `{•} ≠ •`; `{•}` is in no impredicative `∀`; `{•}` is not a function (`•` is not a Kuratowski pair) |
| `true_not_mem_mkForallProp` / `_mkForallType` | both branches of the proof split |
| `true_mem_U` | `{•} ∈ U κ i` for every `i ≤ n` |
| **`interp_sort_ne_interp_forallE`** | **a universe stage is never the denotation of a `∀`** — no hypothesis on `env`, no injectivity input, nothing beyond the chain the model already assumes |
| `SortPiEqSupply` / `SortPiEqSupplyAt` / `sortPiEqSupplyAt_of_supply` | the part-4 supply in `SortEqSupply`'s shape, and the strictly smaller thing consumed (one valuation, no `ρ ∈ interpCtx` guard, no `M.ls` tie) |
| `semantic_sortPiDisj`, `semantic_rigidSortPiDisj`, `rigidShapeUniqNS_of_four` | the route, and the bridge with four conjuncts instead of five |
| **`sortPiSupplyAll_iff`** | **the collapse test, FAILING**: the supply is *equivalent* to `RigidSortPiDisj` |
| `ConstNotUniv`, `interp_const_eq_U_iff`, `not_constNotUniv`, `const_denot_arbitrary` | the residual for the other two negative conjuncts, and its refutation unguarded |
| `vFalse`, `onCtx_vFalse`, `interp_vFalse`, `interpCtx_vFalse` | `[∀ p : Prop, p]` is a legitimate context whose interpretation is **empty**, in every model and on both branches |
| `not_sortPiEqSupply`, `not_sortEqSupply`, **`sortInvSupply_vacuous`** | the supplies are refuted at that context — and the upstream packaged route to `SortInv` is **vacuous for every `env` and `nv`** |
| `pt_mem_U`, `pt_mem_piProp_empty`, `U_piProp_not_disjoint`, `empty_ctx_has_valuation` | the four controls |

All `[propext, Classical.choice, Quot.sound]` except `onCtx_vFalse` (`[propext]`); none mentions
`sorryAx`.  Forward cones of all thirteen headline results, measured with
`scripts/hole-cone.lean`'s walker verbatim (`allowOpaque := true`, type *and* value): **`holes
reached: []` in every case** — in particular neither `forallE_inv_stratified` nor
`rigidShapeUniqNS` nor `weakN_iff`.  The route is not circular through the corner it measures.

### 4F.3 The honest verdict: no census movement, and why **[machine]**

`sortPiSupplyAll_iff` is the receipt.  The supply is per-conversion because `SetModel.sound` is
`Above`-wrapped — the threshold is produced *by the derivation*, so a chain long enough to use it
can only be chosen after the derivation is in hand — and once `SortPiEqSupplyAt` is refuted, "the
supply exists for every such conversion" says only "there is no such conversion".  So
`rigidShapeUniqNS_of_four` is `rigidShapeUniqNS_of_family` with a conjunct renamed, **not** a
narrowing.  Census unchanged; the file is imported by nothing and moves no cone.

What is *not* a restatement is `interp_sort_ne_interp_forallE`, which takes no supply and is not
equivalent to anything in the corner.  It is the **first proved semantic residual** for a
conjunct other than `SortInv`; rows 8, 9 and 25 of `docs/vacuity-ledger.md` are the three whose
residuals are *refuted*.  The dividend is contingent: when `SetModel.sound`'s deferred inputs
(`hle`, `henv`, `hS`, `hC : CoherentOn`, `hR`, `hRd`) are discharged, `RigidSortPiDisj` follows
from them plus this theorem with no further residual on the sort/Π side.

### 4F.4 The sharp negative, and it applies to the whole semantic programme **[machine]**

`Sound.eq` quantifies over `ρ ∈ interpCtx M L Γ`.  For `Γ = [∀ p : Prop, p]` there is no such
`ρ`: `interp_vFalse` computes the denotation to `∅` in **every** model and on **both** branches
of the proof split (impredicatively because `False ∈ Prop` and nothing is in `False`;
predicatively because a function on `Prop` would have to take a value in `False`), and
`onCtx_vFalse` shows the context is legitimate over every environment.  Hence:

* `not_sortEqSupply` — `SemanticRoute.SortEqSupply V env nv [vFalse] u v` is false **for every
  pair of levels**, equivalent ones included;
* `sortInvSupply_vacuous` — therefore the hypothesis of
  `SemanticRoute.semantic_sortInv_packaged` is false for every `env` and every `nv`, because
  reflexivity of `.sort .zero` supplies a conversion at that context.

**Correction to `Theory/SemanticRouteClosed.lean`.**  Its table records the part-4 route to
`SortInv` as "**CLOSED, and exact**", with `sortEqRaw_iff` as the exactness control.  That control
is about `SortEqRaw`, which mentions no context and no `ρ`; it does not certify `SortEqSupply`,
which is what `semantic_sortInv` and `semantic_sortInv_packaged` consume.  The *content* of the
upstream route is untouched — `U_injOn` and `semantic_sortInv` are correct and non-vacuous where
the model can see the conversion — but the ∀-over-all-contexts packaging is not, and no semantic
route into this corner can be finished without discharging a **valuation obligation** for the
context the judgement lives in.  That obligation is new, it is not level-flavoured, and it is
invisible to every instrument this corner has used so far.

### 4F.5 What is *not* claimed **[analysis where marked]**

* No hole is closed; `WF.rigidShapeUniqNS` and `forallE_inv_stratified` both still carry their
  `sorry`.
* Nothing here touches the **first** hole.  `forallE_inv_stratified` is `SortUniq` given `PiInv`,
  both positive, both measured semantically dead upstream.
* No claim that `RigidSortPiDisj` is unprovable syntactically, and no claim the valuation
  obligation is unsatisfiable — only that *this* interpretation, the only one the tree has, does
  not satisfy it at `[∀ p : Prop, p]`.
* `not_constNotUniv` is a refutation of the *unguarded* residual only.  Under `Coherent` the two
  constant-spine conjuncts may well be semantically reachable; `Theory/SetModel/` does not
  construct a `Coherent` `ModelData.cnst`, so it cannot be tried yet.  **That is the next thing
  to try in this corner if the semantic route is picked up again**, and it is worth more than
  another pass at the circle: two of the five conjuncts turn on it. **[analysis]**

### 4F.6 Build and census state at the end of the sixth session **[machine]**

* `~/.elan/bin/lake build Lean4Lean.Theory.Typing.InjSortPiModel` — **green**, 31 declarations,
  no `sorry`, `#print axioms` on all 26 theorems shows no `sorryAx`.
* `~/.elan/bin/lake build Lean4Lean.Theory.Typing.Injectivity` — green; two `sorry`s, at
  lines 261 (`forallE_inv_stratified`) and 1046 (`WF.rigidShapeUniqNS`), unchanged.
* `~/.elan/bin/lake build Lean4Lean.Verify.Guard Lean4Lean.Experimental.ConeJoin` — green.
  guard 1 ✓ (25 frozen axioms), guard 2 ✓ (`proof INCOMPLETE: sorryAx present`), guard 3 ✓
  (51/54 implementation gaps remaining).
* `scripts/sorry-census.lean` — **TOTAL 14**.  `Theory.Equiconsistency` 1 (0 users);
  `Theory.Inductive.Decl` 1 (0); `Theory.Typing.ChurchRosser` 1 (`NormalEq.descend`, 49);
  **`Theory.Typing.Injectivity` 2 (`WF.rigidShapeUniqNS` 236, `IsDefEqU.forallE_inv_stratified`
  528)**; `Theory.Typing.UniqueTyping` 1 (`weakN_iff`, 137); `Verify.Environment` 1 (1);
  `Verify.Soundness` 2 (0, 0); `Verify.TypeChecker.InferType` 1 (0);
  `Verify.TypeChecker.IsDefEq` 2 (1, 2); `Verify.Typing.Lemmas` 2 (30, 94).  This stream
  contributes **0**.
* `scripts/dup-names.lean` — *"no duplicate Lean4Lean declarations across the joined cone"*.
  Since `ConeJoin.lean` was deliberately **not** edited, that run does not see the new file; it
  was checked separately by elaborating a scratch module importing `Experimental.ConeJoin` **and**
  `Theory.Typing.InjSortPiModel` together — **no collision**, 33 constants visible in the
  `Lean4Lean.InjSortPi` namespace.
* Forward cones of the thirteen headline results, `scripts/hole-cone.lean`'s walker verbatim
  (`allowOpaque := true`, type *and* value), over the Theory closure of the new file (3 629
  non-internal `Lean4Lean` declarations): **`holes reached: []` in every case**.  Those closure
  sizes are not comparable with the census's; quote the closure with the count.

**A blockage that existed for most of this session, and its cause, recorded because it will
recur.**  Until roughly the last hour, `scripts/sorry-census.lean` and `scripts/dup-names.lean`
could not be run at all: both import `Experimental/ConeJoin.lean`, whose closure contains
`Verify/Expr.lean`, and `Verify/Expr.lean` failed to elaborate —
`Lean4Lean/Verify/Expr.lean:1360:4: Type mismatch … has type replaceNoCache … but is expected to
have type replace …`, twelve times.  The cause was the *uncommitted* deletion of
`@[simp] axiom Lean.Expr.replace_eq` from the frozen `Lean4Lean/Verify/Axioms.lean` (with the
matching 25 → 24 edit in the frozen `Verify/Guard.lean`) — the proposal that commit `365ccbd`
itself records as **REFUTED** (*"deleting Expr.replace_eq breaks the build"*), left sitting in the
working tree.  `instantiateLevelParamsCore_eq`'s opening `simp [instantiateLevelParamsCore]`
relied on that `@[simp]` axiom to turn `replace` into `replaceNoCache`.  Another stream reverted
the two frozen files mid-session (commit `8173ebc`, *"record the frozen-file near-miss — uncommitted
edits survived a branch delete"*), after which every measurement above ran.  **Lesson for the
orchestrator: an uncommitted edit to a frozen file blocks every stream's instruments at once, and
no stream may clear it.**

---

## 5. The refutation attempt, and why it does not reach **[analysis]**

The brief asks for a machine-checked negative if one exists. The one crack in the hypothesis
`VEnv.WF env` is `VDecl.WF.unsafeDef`: `VEnv.WF` is `∃ ds, VEnv.WF' ds env` with **no purity
filter**, and `unsafeDef` is circular by design — `Theory/MutualDefUnsound.lean` machine-checks
that it admits `f : (∀ p : Prop, p) := f` and that the resulting environment is inconsistent.
So `SortUniq` and `forallE_inv_stratified` are asserted over environments that are *known to
prove `False`*.

It does not reach a refutation, for a reason worth recording so nobody re-walks it:

* `unsafeDef` checks each member's value in `env'`, which is `env` plus the block's
  **constants** — `addConsts`, not `addDefEqs`. The block's own defining equations are **not**
  available while its values are typechecked. So every defeq the step adds is `c ls ≡ v : T`
  with both sides honestly typed at `T` in a sound environment.
* Breaking `SortUniq` needs a single term with two sort types, hence a conversion between two
  sorts at different levels, hence — since `extra`'s left-hand side is always a constant
  application (`WF.instL_lhs_ne_sort`) — a chain through a constant `c` with `c ≡ .sort u` and
  `c ≡ .sort v`. One constant has one value.
* The mutual-block escape (two members `c₁ ≡ .sort u`, `c₂ ≡ .sort v`, joined by `proofIrrel`
  at a common `Prop` type `T`) requires `.sort u : T` with `T : .sort .zero`, i.e. a sort typed
  at a proposition — which is `sort_not_proof`, and which is *already false* in the environment
  before the block. The first bad step cannot happen.
* A proof-level inconsistency is not enough on its own: `u ≈ v` is a statement about `VLevel`
  evaluation, not an object-level `Prop`, so an inhabitant of every proposition does not touch
  it.

**Verdict: no refutation found, and the shape of the argument says none is available from this
direction.** Recorded per ORCHESTRATOR.md rule 3: *"no witness" is not evidence of truth* — this
is an argument that one particular family of witnesses is empty, not a proof of the statement.

### 5.1 A correction to `Theory/Typing/SortUniq.lean`'s "There is no model route" **[analysis]**

That section argues: add cumulativity; any nested-universe model validates it; `SortUniq` is
false there; therefore no model can establish `SortUniq`. **The inference is too strong as
written.** What the argument shows is that no model which *also* models cumulativity can prove
`SortUniq` — which rules out the nested-universe constructions, including the one
`~/lean-type-theory/soundness.tex` builds, but not a *level-tagged* model in which
`⟦Sort u⟧ ∩ ⟦Sort v⟧ = ∅` for `u ≉ v`.

**The section's conclusion nevertheless stands**, for a different reason, and this is worth
having written down: a level-tagged interpretation is exactly `SetModel/Interp.lean`'s
`LevelAssign`, whose `srt_sound` field is `SortUniq` restated, and whose unguarded form is
machine-refuted by `LevelAssignUnsat.no_levelAssign`. To tag a raw term with a level you must
already know its level is unique. So: *the model route is closed because the tag is the
statement*, not because every model validates cumulativity. Anyone re-reading that docstring
should not take the stronger claim as established.

---

## 6. Prior results, re-checked and still standing **[machine]**

* **`sort_inv` is proved**, from `SortUniq` alone (`sort_inv_of_sortUniq`), with no `trans`
  case. Unchanged.
* **`SortUniq` is a theorem** (`WF.sortUniq'`), now relative to `PiInvStratApp`. It closes the
  `proofIrrel` case of `forallE_inv`, `sort_forallE_inv`, `const_forallE_inv`, `const_sort_inv`
  with no statement gaining a hypothesis, and `const_app_inv`'s through `IsType.not_isProof`.
* **Every non-opaque residual in the file is a single `trans` case**, and it says the same
  thing five times: *a term convertible with a Π (resp. a rule-free constant application, resp.
  a sort) reduces to one*.
* **`const_app_inv`'s invariant is `¬ IsProof`**, not `IsType`; `IsProof.forallE_fires`
  machine-witnesses that `IsType` genuinely cannot be carried (a proof can be a function).
* **`NormalEq.descend` is machine-checked false**; do not route through `ChurchRosser.lean`.
* **Non-vacuity of the `SortUniq` route**: `propLoop_sortUniq` fires at `CycleConv.propLoopEnv`,
  a proved-`VEnv.WF` environment whose head reduction provably has a two-cycle.
* **`weakN_iff` ⟺ `PiDescend`**, `sorry`-free, in `Strengthen.lean`
  (`Strengthening.iff_typed`, `Strengthening.of_typing`, `TypingStrengthening.iff_piDescend`,
  `PiDescend.sortDescend`). `weakN_iff`'s cone is **empty** — it is an independent obligation,
  and unlike the injectivity family it has never been reduced to anything smaller than
  `PiDescend`.

### 6.1 `PiDescend`, priced this session **[analysis]**

`PiDescend` needs: from `Γ ⊢ f : T` and `T.liftN n k ≡ .forallE A B` upstairs, produce
`T ≡ .forallE A₀ B₀` downstairs. Case-splitting on `T`'s head through `HasTypeStrong`:

* `T = .forallE A₀ B₀` — the Π is already there, **but the argument half still needs
  `Strengthening`** to descend `S.liftN ≡ A₀.liftN`, so the case is not free;
* `T = .sort l` and `T = .lam …` — both **close outright** from `sort_forallE_inv` (a lambda's
  base type is a Π, and a Π is not a sort);
* `T = .bvar i`, `T = .const c ls`, `T = .app f₁ a₁` — **open**; the first is "a variable is not
  convertible to a Π", the third is the normalisation statement again.

The two closing cases need one lemma that is not in the tree: *a lambda's type is not a sort*
(`¬ env.HasType U Γ (.lam A b) (.sort u)`), which follows from `HasType.lam_inv`'s pattern in
`Strong.lean` plus `sort_forallE_inv`. Both cases then reduce to `sort_forallE_inv` at `Γ'`,
using only that `(.sort l).liftN = .sort l`.

**But the head split is not a reduction of `PiDescend`, and this is the collapse test failing —
recorded so nobody writes the statement.** The `T = .forallE A₀ B₀` case looks free (the Π is
already there) and is not: the conclusion also demands `Γ ⊢ a : A₀`, and getting it from
`Γ' ⊢ a.liftN n k : A` requires descending `IsDefEqU Γ' (S.liftN) (A₀.liftN)` to `Γ`, which is
`Strengthening` — the target itself. So any standalone `PiDescendNeutral → PiDescend` would
have to take `Strengthening` as a hypothesis, and `Strengthening → PiDescend` is already
proved (`Strengthening.typing.piDescend`): the "reduction" would be a tautology. The place the
head split belongs is **inside** `TypingStrengthening.of`'s induction, where the IH is
available, not in a new `Prop`.

So `PiDescend` is not a fourth independent thing: it is the same normalisation content reached
from the strengthening side.

---

## 7. Corrections this session makes

| source | claim | correction |
|---|---|---|
| this stream's brief | "`VIndRecArg.exists_indep` is a strict dependency on `forallE_inv`" | **Not a measured dependency.** `exists_indep`'s forward cone is **empty** and no path from it to `forallE_inv` exists — it is an opaque `sorry`. The claim is read off its *docstring*, which says its intended proof would need `forallE_inv`. That is analysis about an unwritten proof, not a dependency. **[machine]** |
| this stream's brief | "ask whether the `NormalEq`-has-no-`trans` manoeuvre reaches your target" | It does not, and the obstruction is circularity, not difficulty: `IsDefEq.church_rosser` reaches `forallE_inv_stratified`, `forallE_inv` and `weakN_iff`. §2. **[machine]** |
| this stream's brief | "`church_rosser` currently reaches four sorry-carrying declarations, one of which is `descend`" | Correct — and the other three are this corner's own targets, which is the load-bearing half. §2. **[machine]** |
| `docs/backward-analysis.md` §3 | `forallE_inv_stratified`'s direct consumers are `IsDefEq.uniq` and `IsDefEqU.forallE_inv`; `forallE_inv`'s are `TrExpr.beta` and `inferApp.loop.WF` | On this commit: `forallE_inv_stratified`'s are `IsDefEq.uniq` and `piInvStrat_axiom`; `forallE_inv`'s are `HasType.piUniq` and `piInv_axiom`, and it reaches the stratified form only through `WF.sortUniq'`. The *shape* of §3's conclusion is unchanged; the names are not. §1.2. **[machine]** |
| `docs/backward-analysis.md` §3 | `sort_inv` is one of the load-bearing open statements | `sort_inv` is **proved**. Its 233 users are real but its cone is `[forallE_inv_stratified]`. **[machine]** |
| previous `handoff-injectivity.md` §6 | "`grep KStep` returns hits only inside `KRule.lean`" | Now three files (`KRule`, `KDescend`, `KCanonical`). The conclusion is unchanged and sharper: `ParRed` still has eight constructors and no `K`, and `KDescend`'s descent is proved *relative to* an unsupplied `hK`. §2. **[machine]** |
| `Theory/Typing/Enlarged.lean` | adding `retype` to `IsDefEq` "forces a matching constructor in `HasTypeStrong`", because `IsDefEqStrong.hasType'` cannot close its `retype` case | **Not forced.**  `HasTypeStrong.retype` (`Theory/Typing/RetypeCase.lean`) proves that case, `sorry`-free, from `PiInvStratApp` alone, without the conversion premise.  `UniqAcross` is a real collapse but not the obligation. §4A.1. **[machine]** |
| this stream's brief | the enlargement study's minimal disconnecting set (`retype` + `piUniq` + `weakN_iff'`) "takes it to 4" | Not reproducible in the `Verify/Bridge.lean` scope: the same three cuts leave **21**, and the disconnecting set is priced by cutting edges only — it omits the edge Route A creates at `hasType'`, which takes the same three cuts to **104**. §4A.2. **[machine]** |
| this stream's brief | "an *in-place* enlargement is a strict regression — `uniqU_of_uniqAcross` machine-checks that the new case's obligation implies `uniqU` back" | Right conclusion, wrong reason.  The in-place enlargement is a regression because of a **cone** cost (201 → 234, and 21 → 104 under the disconnecting cuts), not because it opens a new hole — on Route A it opens none. §4A. **[machine]** |
| `Theory/Typing/SortUniq.lean` docstring | "`SortUniq` is not a semantic consequence of Lean's rules, so no argument from any model can establish it" | The argument rules out models that also validate cumulativity, not all models. The conclusion survives because the level-tagged alternative *is* `LevelAssign`, refuted unguarded. §5.1. **[analysis]** |

### 7.2 Corrections from the fourth 2026-08-30 session **[machine]**

| source | claim | correction |
|---|---|---|
| this stream's brief, and §8 item 1 | the prize is *"`SortUniq + PiInv → retypes`, with no `VEnv.WF`, no stratification, no `PiInvStratApp`"* | The **implication** was already available: `piInvStratApp_of` (`VEnv.WF + SortUniq + PiInv → PiInvStratApp`) composed with `retypes_of_piInvStratApp`.  Written out as `retypes_of_sortUniq_piInv_via_strat`.  What is actually new is `VEnv.WF env` → `Ordered env`, `Classical.choice` dropped, and a structural recursion on `VExpr` in place of a height-indexed induction. §4D.2. |
| this stream's brief | *"the open check, and it is the whole risk: can `uniqStrong_of_baseUniq` be applied at a proper subterm without re-entering the whole statement?"* | It can, and the reason is short: `peelEq` rewrites the type, never the subject.  Confirmed by `#print` on the elaborated recursion, not by reading the source. §4D.1. |
| §4C.4 (this document) | the head table's `.lam` and `.app` rows say "unique typing at the body / at the function" | Correct, and now sharper: what those rows need is unique typing **at flag `true`** (`UniqStrongAt`), not at flag `false` (`BaseUniqAt`).  The distinction is machine-refuted, not stylistic: `base_flag_not_droppable`.  It is the single reason `SortUniq` remains in the result. §4D.4. |

### 7.1 Corrections from the later 2026-08-30 session **[machine]**

| source | claim | correction |
|---|---|---|
| `Theory/Typing/RetypeCase.lean` and §4A.4 of this document | the `hasType'` `retype` case is `HasTypeStrong.retype`, and "the conversion premise is not needed and is not taken" | The case **carries** `IsDefEqStrong Γ e₁ e₂ A`.  Not taking it leaves a statement with nothing to induct on, at least as strong as the case (the converse implication is not known).  With it, the case is proved with no `PiInvStratApp` and no `VEnv.WF`: `IsDefEqStrong.retypes`.  §4B. |
| this stream's brief, and §1.2 | "**Four of `Injectivity.lean`'s six holes have zero users.**  Do not spend time on them" | **Stale.**  `scripts/sorry-census.lean` on this commit: `sort_forallE_inv` **8**, `const_sort_inv` **1**, `const_forallE_inv` **1**, `const_app_inv` **1**.  Still small, still the lowest-value targets in the file, but no longer dead. |
| this stream's brief | `forallE_inv_stratified` has 238 transitive users; `weakN_iff` 169 | Census on this commit: `forallE_inv_stratified` **345**, `weakN_iff` **100**, `forallE_inv` **98**, `NormalEq.descend` **40**.  The tree moved under both numbers; quote the census, not the brief. |
| §1.2 | `forallE_inv` has 65 users in the `Verify/Bridge.lean` closure | **13** on this commit with internal names skipped.  §1.2's table was measured with internal names *included*; the two conventions differ by a large factor and the table's header says so — but the two numbers have been quoted side by side in briefs, and they are not comparable. |

TOTAL declarations directly containing `sorryAx`: **19**, unchanged.  `scripts/dup-names.lean`:
*no duplicate `Lean4Lean` declarations across the joined cone* — both re-run at the end of the
later session, and both now run clean (§8's note that they were blocked by a red
`ChurchRosser.lean` no longer applies).

---

## 8. What to pick up first

*(rewritten by the later 2026-08-30 session; the earlier list is kept below it where it still
holds)*

*(item 1 rewritten by the fourth 2026-08-30 session; see §4D.  The third session's version is
kept below it as item 1a, because its head table is still the right map.)*

0. **If the instruments will not run, check the frozen files for uncommitted edits first.**
   §4F.6 records a session in which `sorry-census.lean` and `dup-names.lean` were dead for hours
   because an uncommitted, *self-declared-refuted* deletion in `Verify/Axioms.lean` broke
   `Verify/Expr.lean:1360`.  No stream may clear that; it was reverted at commit `8173ebc`.

0a. **The semantic route is NOT exhausted, and the polarity split is why** (§4F).  Three of the
   second hole's five conjuncts are *negative*, so soundness alone can settle them without
   faithfulness.  One of the three now has a **proved** residual
   (`InjSortPiModel.interp_sort_ne_interp_forallE`); the other two turn on `Coherent`, which
   `Theory/SetModel/` does not yet construct — **that is the highest-value unexplored item in
   this corner.**  And §4F.4's valuation obligation is a new, un-instrumented debt on *every*
   semantic route, including the upstream one this document treated as closed.

1. **`BaseUniq` by term recursion is done, and so is the `SortUniq` localisation §4D.5 said
   was impossible.**  `BaseUniqTerm.lean` (§4D) and `BaseUniqChain.lean` (§4E).  Three things
   follow.

   * **§4D.5 and the previous version of this item are wrong**, and the correction is machine-
     checked: with the conclusion stated as a chain (`ConvC`), `peelChain` and
     `uniqStrongCAt_of_baseUniqCAt` take **no hypothesis at all** (`[propext]`), and `SortUniq`
     leaves the route entirely.  Do not re-derive that; read §4E.
   * **The residual is `ConvSortInv`** — sort injectivity along a conversion chain — and
     `sortUniq_iff_convSortInv` says it is the *same* hypothesis as `SortUniq` given
     `ConvPiInv`.  So the corner is still a circle; what is new is that the demand is now a
     statement about `sort ~ … ~ sort` chains rather than about arbitrary terms, and no step of
     the proof composes conversions at different sorts.
   * **The flag is still load-bearing** (§4D.4).  `base_flag_not_droppable` applies verbatim to
     the chain version: the `.forallE`, `.lam` and `.app` premises the recursion consumes are at
     flag `true`.
   * The next thing to try, if this corner is picked up again: `ConvSortInv` is the *only*
     hypothesis of `retypes_of_convInv` that is not `Ordered` or `ConvPiInv`, and every chain it
     is applied to has both endpoints syntactic sorts and arises from `UniqStrongCAt` at a
     proper subterm.  Whether that shape can be exploited was **not** examined this session.

1a. **`BaseUniqApp` — `Theory/Typing/ProofRetypeHeads.lean`.**  Do **not** attack `ProofRetype`,
   `BetaRetype`, `EtaRetype` or `ExtraRetype` separately: all four are corollaries of
   `BaseUniq`, and `BaseUniq` is free at `.bvar`, `.const` and `.sort`, is `SortUniq` at
   `.forallE`, and is a plain structural recursion at `.lam`.  **Everything that is not already
   `SortUniq` lives in `BaseUniqApp`**, and there it is Π-injectivity.  The one thing in this
   corner that has never been tried and is now *stateable*: prove `BaseUniq` by induction on
   the **term** (not on a derivation), using `SortUniq` for `.forallE`, `uniqStrong_of_baseUniq`
   at the subterm for `.lam`, and `PiInv` for `.app` — that would give
   `SortUniq + PiInv → retypes` with **no `VEnv.WF`, no stratification and no
   `PiInvStratApp`**.  The recursion is well-founded on the term; what has to be checked is that
   `uniqStrong_of_baseUniq` can be applied at a proper subterm without re-entering the whole
   statement.
2. **Do not re-attack the circle from inside `Injectivity.lean`** (unchanged, see below).
3. **Do not restate the `hasType'` case without its conversion premise.**  That is what
   §4A.4's open question was, and it is what made the case look unattackable.
4. **`weakN_iff` is still the better-value target in this stream's own files**, at 100 census
   users with an empty cone — but read §6.1's collapse-test note before writing anything.
5. **Do not** re-attempt §4's four repairs, the lexicographic measure, the unique-typing
   shortcut for `const_app_inv`'s level half, or any route through `ChurchRosser`.

### Build and census state at the end of the **fifth** session **[machine]**

Working tree at commit `aa3585e` plus **`Theory/Typing/BaseUniqChain.lean`** (new), two edits in
`Theory/Typing/BaseUniqTerm.lean` (an import line, and the superseded paragraph marked as such),
and this document.  Nothing else was touched.

* `lake build Lean4Lean.Theory.Typing.BaseUniqChain` — green, 40 declarations, no `sorry`.
  `#print axioms` on all of them: `[propext, Quot.sound]`, with `peelChain`,
  `uniqStrongCAt_of_baseUniqCAt` and `sortWF_of_hasTypeStrong` on `[propext]` alone.  No
  `Classical.choice` anywhere in the file.
* `lake build Lean4Lean.Theory.Typing.BaseUniqTerm` — green.
* `lake env lean scripts/sorry-census.lean` at the start and at the end of the session —
  **byte-identical**, TOTAL 19.  The full listing on this commit:
  `Theory.Inductive.Decl` 1 (`VIndRecArg.exists_indep`, 0 users);
  `Theory.Typing.ChurchRosser` 1 (`NormalEq.descend`, 42);
  `Theory.Typing.Injectivity` 6 (`sort_forallE_inv` 8, `forallE_inv` 145, `const_sort_inv` 1,
  **`forallE_inv_stratified` 389**, `const_forallE_inv` 1, `const_app_inv` 1);
  `Theory.Typing.UniqueTyping` 1 (`weakN_iff`, 124);
  `Verify.Environment` 1 (`addDecl.WF`, 1); `Verify.Environment.Boundaries` 1
  (`checkPrimitiveDef.WF.rest`, 6); `Verify.Soundness` 2 (`kernel_sound` 0,
  `kernel_complete` 0); `Verify.TypeChecker.InferType` 1 (`inferProj.WF`, 0);
  `Verify.TypeChecker.IsDefEq` 2 (`isDefEqUnitLike.WF` 1, `tryEtaStructCore.WF` 2);
  `Verify.TypeChecker.WHNF` 1 (`quotReduceRec.WF`, 1); `Verify.Typing.Lemmas` 2
  (`TrProj.weak'_inv` 28, `TrProj.uniq` 83).
  **Correction to the brief:** it quoted 365 transitive users for `forallE_inv_stratified`; the
  census on this commit reports **389**.
* `lake env lean scripts/dup-names.lean` — *"no duplicate Lean4Lean declarations across the
  joined cone"*, which also confirms `BaseUniqChain.lean` is inside `ConeJoin.lean`'s closure.

### Build and census state at the end of the **fourth** session **[machine]**

Working tree at commit `dadea04` plus `Theory/Typing/BaseUniqTerm.lean` (new) and one
`ConeJoin.lean` import line.  Two other streams have `KCanonical.lean` and `KMeasure.lean`
modified in the tree; no whole-tree `lake build` was run.

* `~/.elan/bin/lake build Lean4Lean.Theory.Typing.BaseUniqTerm` — green.
* `~/.elan/bin/lake build Lean4Lean.Experimental.ConeJoin` — green.
* `scripts/sorry-census.lean` on the **ConeJoin import closure**, run at the start and again at
  the end: **byte-identical**, TOTAL **19**.  The new file contributes **0**.
* `scripts/dup-names.lean` on the same closure: **clean**, and it saw the new file (the import
  line was added before the run).
* Per-hole transitive users on that closure, this run: `forallE_inv_stratified` **365**,
  `forallE_inv` **123**, `weakN_iff` **111**, `TrProj.uniq` 83, `NormalEq.descend` 40,
  `TrProj.weak'_inv` 28, `sort_forallE_inv` 8, `checkPrimitiveDef.WF.rest` 6,
  `const_sort_inv` / `const_forallE_inv` / `const_app_inv` 1 each, `addDecl.WF` 1,
  `isDefEqUnitLike.WF` 1, `quotReduceRec.WF` 1, `tryEtaStructCore.WF` 2,
  `exists_indep` / `kernel_sound` / `kernel_complete` / `inferProj.WF` 0.  **Quote the closure
  with the count** — these are not comparable with §1.2's or §4B.5's narrower-closure numbers.
* Every declaration in `BaseUniqTerm.lean` is checked by the file's own `#print axioms` block;
  none mentions `sorryAx`, and every one of them is `[propext, Quot.sound]` except
  `retypes_of_sortUniq_piInv_via_strat`, which is the *old* route written out for comparison and
  carries `Classical.choice`.

### Build and census state at the end of the **third** session **[machine]**

Working tree at commit `b31d9c3` plus `Theory/Typing/ProofRetypeHeads.lean` and one
`ConeJoin.lean` import line.  `~/.elan/bin/lake build Lean4Lean.Theory.Typing.ProofRetypeHeads`
and `... Lean4Lean.Experimental.ConeJoin` are both green.  Measured **on the ConeJoin import
closure** (the only closure either instrument uses, and the closure now contains the new file):

* `scripts/sorry-census.lean`: **TOTAL 19**, unchanged.  The new file contributes **0**.
* `scripts/dup-names.lean`: **clean** — and, unlike a run before the import was added, this run
  actually saw the new file.
* Per-hole transitive users on that closure, same run: `forallE_inv_stratified` 358,
  `weakN_iff` 111, `forallE_inv` 110, `TrProj.uniq` 83, `NormalEq.descend` 40,
  `TrProj.weak'_inv` 28, `sort_forallE_inv` 8, `checkPrimitiveDef.WF.rest` 6,
  `const_sort_inv` / `const_forallE_inv` / `const_app_inv` 1 each.  **These are not comparable
  with §1.2's or §4B.5's numbers** — those were measured on a narrower closure earlier in the
  day; quote the closure with the count.
* Every declaration in `ProofRetypeHeads.lean` is checked by the file's own `#print axioms`
  block; none mentions `sorryAx`.  No whole-tree `lake build` was run.

### Build and census state at the end of the later session **[machine]**

`~/.elan/bin/lake build Lean4Lean.Theory.Typing.RetypeCase Lean4Lean.Theory.Typing.RetypeAdmissible`
is green.  `scripts/sorry-census.lean`: **TOTAL 19**, unchanged from the start of the day.
`scripts/dup-names.lean`: clean.  Every declaration in `RetypeAdmissible.lean` is checked by
the file's own `#print axioms` block; none mentions `sorryAx`.  A whole-tree `lake build` was
**not** run — other streams have files in flight — so "green" here is the two narrow targets
plus the census and `dup-names` runs, which do import the wider tree.

---

### The earlier list from the same day, still standing where it does not conflict

1. **`HasTypeStrong.retype` without `PiInvStratApp`** (§4A.4).  New this session, the only
   target in this corner that is not known to be equivalent to the corner itself, and the whole
   `retype` enlargement turns on it.
2. **Do not re-attack the circle from inside `Injectivity.lean`.** Six sessions have walked it to
   the same step from eight directions (§4 and §4A.3 here, §5.1 of the previous version,
   `handoff-stratified.md` §3).  The statement is narrowed as far as its consumer allows and is
   still `SortUniq`.
3. **Do not propose the in-place `retype` enlargement as a disconnecting move** without pricing
   the `hasType'` edge first (§4A.2).  Route A costs 201 → 234; Route B reopens `uniq` and its
   obligation collapses with the index bounds kept (§4A.3).
4. **`weakN_iff` is still the better-value target in this stream's own files.**  It reaches the
   Bridge with 169 users (census), its cone is empty, and unlike the injectivity family nothing
   has ever been subtracted from it.  §6.1 gives two of six head cases for free from
   `sort_forallE_inv` — but read the collapse-test note there first: they must be written
   *inside* `TypingStrengthening.of`'s induction, and a standalone `PiDescendNeutral` statement
   would be a tautology.
5. **Do not** re-attempt §4's four repairs, the lexicographic measure, the unique-typing shortcut
   for `const_app_inv`'s level half, or any route through `ChurchRosser`.


(Item 1 of that list is answered by §4B; item 3's pricing warning still applies.)
