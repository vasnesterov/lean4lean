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

Files added or changed on 2026-08-30: **`Lean4Lean/Theory/Typing/RetypeCase.lean`** (new) and
this document.  Nothing else was touched.  `lake build Lean4Lean.Theory.Typing.RetypeCase` is
green; a whole-tree `lake build` fails in `Theory/Typing/ChurchRosser.lean`, another stream's
in-flight edit (`Alternative 'keta' has not been provided`, line 2240), which is why the
end-of-session census and `dup-names` runs are blocked — see §8. **[machine]**

---

## 0. Headline

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

---

## 8. What to pick up first

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

### Build and census state when this section was written **[machine]**

`~/.elan/bin/lake build Lean4Lean.Theory.Typing.RetypeCase` is green.
`scripts/sorry-census.lean` at session start: **TOTAL 19**, `forallE_inv_stratified` 238
transitive users.  Re-running it at session end is **blocked**: `Theory/Typing/ChurchRosser.lean`
is another stream's in-flight edit and is red (`Alternative 'keta' has not been provided`, line
2240), and the census imports it through `Experimental.ConeJoin`.  Nothing in this session adds
a `sorry`: every declaration in `RetypeCase.lean` is checked by the file's own `#print axioms`
block and none mentions `sorryAx`.  `scripts/dup-names.lean` is blocked by the same red file; the
six new names were checked against the tree by hand and none collides.
