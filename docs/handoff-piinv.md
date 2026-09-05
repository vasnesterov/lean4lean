# handoff-piinv — is `VEnv.PiInv` true at `VEnv.WF`?

Stream: PiInv. Opened 2026-09-05, HEAD `aec6aad` (bare build green 1672 jobs, guards 1/2/3 ✓, census 13).

Owned: `Lean4Lean/Theory/Typing/PiInvWF.lean` (new), `docs/handoff-piinv.md` (this file).
Read-only, explicitly: `Lean4Lean/Theory/Typing/Injectivity.lean` (holds the target hole).
Frozen: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

Target: `Lean4Lean.VEnv.PiInv` (= `RigidPiUniq`, per `Injectivity.lean:1014`
`rigidPiUniq_iff_piInv`). The census (`docs/handoff-injcensus.md`) established that of the five
members of `RigidShapeUniqNS`, four are refuted from `Ordered` alone by one shared witness and
`PiInv` is the odd one out and load-bearing; and that the needed assembly direction takes only
`Ordered` + `ProofTransport` + the five members, so **per-row answers compose**. Hence: attack
this one member alone.

**Question: is `PiInv` provable at `VEnv.WF`, refutable at `VEnv.WF`, or open?** Every refutation
on this front so far is at `Ordered`, and each proves its own witness lies outside `VEnv.WF`. Nobody
has tried either direction at `VEnv.WF`.

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `Injectivity.lean`, `RigidNodeCircle.lean`, `InjCensus.lean`,
`InjMethod.lean`, `InjPiRogue.lean`, or any `docs/handoff-inj*.md` in this session.** Answers are
appended below in §2 as measured. **A filled answer is never edited**; corrections go in §2 with a
date.

### The four shape questions, instantiated to "`PiInv` at `VEnv.WF`"

**Q1. Does the target exist — judged on the *conclusion head*, not the obligation's name?**
(a) Is there a declaration literally named `VEnv.PiInv`, is it a `def … : Prop` (so it can be
instantiated at a witness environment) or a structure/class, and what is its **full arity including
invisible section binders** (method rule 5)? (b) Does `rigidPiUniq_iff_piInv` exist under that name,
is it a genuine `Iff` (both directions in the term), and is it `sorryAx`-free — or is one direction
conditional, in which case "`PiInv` **is** `RigidPiUniq`" is a docstring claim and not a measured
one? (c) What is the *conclusion head* of `PiInv`'s body: a conversion judgement (`IsDefEq`/`IsDefEqU`)
on the domains, on the codomains, or a conjunction of both — and is it under a `∀ Γ`, i.e. is it an
open-term statement after all, contra "rules relate closed terms"? (d) Do `VEnv.WF` and `Ordered`
exist as I assume, and is `VEnv.WF` a structure with named clauses I can instantiate, or a
`Nonempty`/inductive whose clauses are not separately nameable?

**Q2. Is the work in the direction I think?**
I am briefed to prove-or-refute `PiInv` at `VEnv.WF`. Direction-checks: (i) is the *hard* direction
of `PiInv` producing a conversion (positive, needs a derivation) or consuming one (needs a
¬conversion fact)? The census says positive, which is what makes refutation structurally hard; a
refutation therefore needs to falsify `PiInv` by exhibiting a `VEnv.WF` environment where the
premise holds and the conclusion's conversion is **not derivable** — a ¬derivability fact, which in
this repo is the expensive kind. (ii) Does anything *downstream* need `PiInv` only in a weaker,
already-available form (e.g. at a fixed `U`, or only for `const`-headed spines), so that the honest
answer is "the client's obligation is weaker than `PiInv` and provable" rather than "`PiInv` is
true"? (iii) Is `VEnv.WF` even *inhabited* by an environment rich enough to make `PiInv` non-vacuous
— i.e. is the whole question at risk of being decided by vacuity (no `VEnv.WF` env has any Π
conversion), which would be a real but hollow answer and must be reported as such.

**Q3. Measurement or docstring?**
Facts in my brief that must each be classified *measured here* vs *prose*: (i) `rigidPiUniq_iff_piInv`
is a two-way, hole-free identification; (ii) `VEnv.imax_dom_not_pinned` — arity 0, cone 591,
hole-free, "no level conjunct can be smuggled in"; (iii) `InjCensus.not_wf_censusEnv` and
`InjMethod.not_wf_injEnv` hole-free; (iv) `InjCensus.ordered_not_enough_for_piInv` — my brief says it
is **conditional** (stated at `roguePiEnv` with member 2 as antecedent), so method rule 3 applies: I
must read its hypotheses off the statement and never quote it flat; (v) `SubstCRefute`,
`DefInvRefute.defInv_all_false`, `propAgree_conclusion_not_sortUniq` (cone 588) — measured, and at
what generality. Every one gets `#print axioms` / `scripts/exists.lean` before I cite it.

**Q4. What does the structure branch on, and where are its extremes — i.e. what does `VEnv.WF`
permit that I am assuming it forbids?**
This is the round's whole instrument. `Ordered` witnesses are exhausted, so the extremes to probe
are the ones `VEnv.WF` **fails to forbid**. Enumerate `VEnv.WF`'s clauses and, for each, name the
environment state it does *not* rule out:
- `defeqs`: `VEnv.WF` presumably types every δ-rule and pins one rule per constant. Does it forbid a
  δ-rule whose two sides are **Π-headed with non-convertible domains**? A rule `c ≡ ∀x:α.β` where the
  *same* `c` also unfolds elsewhere? A rule at a **different universe level** on each side?
- constants: does `VEnv.WF` forbid a constant whose type is a Π but whose *value* is not, or an
  `opaque`/axiom-like constant with no value (the extremes of "has a value" being none and one)?
- levels: no level conjunct (established), so a Π with `imax`-domain levels is permitted; that is the
  extreme the sibling row exploits and this row cannot.
- the universe bound `U`: extremes `U = 0` (Prop-only) and `U` large; `Γ = []` vs non-empty; the two
  Π's domains equal vs distinct; codomains closed vs `bvar`-dependent.
The deliverable per probe is: *which `VEnv.WF`-legal state could break `PiInv`*, and does `VEnv.WF`
actually permit it (proved), or is the state excluded by a **named clause** (which clause)?

### Numbered predictions, made cold (to be judged only against measurement)

- **P1.** `VEnv.PiInv` exists as a `def … : Prop`, arity ≥ 2 counting invisible section binders
  (`env`, `U`), and its body is `∀ Γ dom₁ cod₁ dom₂ cod₂, IsDefEqU … (forallE …) (forallE …) → (dom
  conversion) ∧ (cod conversion under an extended Γ)`. Prediction: it **does** quantify over an open
  `Γ` and the codomain conjunct lives in `Γ, dom`. Confidence: medium-high. Falsifier: reading the def.
- **P2.** `rigidPiUniq_iff_piInv` is a genuine two-way hole-free `Iff` (my brief's phrase "neither
  weaker nor stronger" is measured). Confidence: medium — brief-sourced, and method rule 4 says a
  docstring's claim is not evidence. Falsifier: `#print axioms` + reading the term.
- **P3.** The verdict. Prediction: **still open at `VEnv.WF`, and refutation at `VEnv.WF` is the
  wrong target** — I predict `PiInv` is *true* at `VEnv.WF` but its proof needs exactly the
  Π-inversion-one-index-down that `unique.tex` §1 gets from its alternation index, and that
  `SubstC`'s falsity at n=1 blocks importing that argument. So I predict I land at: no refutation
  witness exists inside `VEnv.WF` (and I predict I can prove a *partial* version of that: that the
  four `Ordered`-refuting witnesses' defect is excluded by a named `VEnv.WF` clause), and no full
  proof. Confidence: medium. Falsifier either way: a `VEnv.WF` witness, or a closed proof.
- **P4.** The obstruction, named. Prediction: the load-bearing missing input is **not** confluence and
  **not** a level fact but the **codomain conjunct under an extended context** — i.e. `PiInv`'s
  second component needs transport of a conversion across a context whose variable changes type,
  which is precisely what `DefInvRefute` refuted at `⊢₁`. Prediction: the **domain** conjunct of
  `PiInv` is *provable* at `VEnv.WF` (or at `Ordered` + one clause) and only the codomain conjunct is
  open, so `PiInv` splits and the split is the round's actual deliverable. Confidence: medium-low.
  Falsifier: finding the domain conjunct equally blocked, or `PiInv` having no codomain conjunct at all.
- **P5.** Vacuity risk. Prediction: **not** vacuous — `VEnv.WF` environments with Π conversions
  exist (any environment with a δ-rule between two Π types, or just reflexivity, makes the premise
  satisfiable), so the question is real. Confidence: high. But I predict the *interesting* premises
  (a Π-Π conversion that is not reflexivity-up-to-α) require a δ-rule, and I predict `VEnv.WF`'s
  typing clause on `defeqs` is what constrains them. Falsifier: a proof that `VEnv.WF` forces every
  Π-Π conversion to be trivial, which would make `PiInv` true but hollow.
- **P6.** Cost/outcome. Prediction: I land with a measured table of `VEnv.WF`'s clauses vs the states
  each fails to forbid, at least one new machine-checked lemma in `PiInvWF.lean` (most likely: the
  domain conjunct at some strength, or the proof that a candidate `VEnv.WF` witness is *not*
  `VEnv.WF`), and a one-sentence verdict of **open** with a named obstruction. I predict I do **not**
  close `PiInv` and I predict I do **not** refute it. Confidence: medium.

---

## §2 — Verdicts, appended as measured (append-only; each entry dated)

### V1 (2026-09-05) — Q1 answered: the target exists; but "`RigidPiUniq` **is** `PiInv`" is **conditional on `SortUniq`**

`Lean4Lean.VEnv.PiInv` — `Theory/Typing/Injectivity.lean:347`, **arity 2** (`env`, `U`; both
section binders, invisible in the statement — method rule 5), cone 31, hole-free.

```
def PiInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u)
```

**P1 is RIGHT on all three counts**: `def … : Prop`; arity 2 counting invisible binders; open `Γ`
under `OnCtx`, with the codomain conjunct in `A::Γ`. There is no level conjunct and no index —
confirming `imax_dom_not_pinned`'s relevance rather than re-deriving it.

**P2 is WRONG, and this is a method-rule-3 correction to my brief.** The brief says
`rigidPiUniq_iff_piInv` shows `RigidPiUniq` *"is `VEnv.PiInv`: neither weaker nor stronger"*. Read
off the compiled environment, the `Iff` is **not** free:

| name | arity | hypotheses | verdict |
|---|---|---|---|
| `Lean4Lean.VEnv.PiInv.rigidPiUniq` | 4 | `henv : VEnv.WF env` | `PiInv → RigidPiUniq` costs `WF` only |
| `Lean4Lean.VEnv.piInv_of_rigidPiUniq` | 5 | `henv : VEnv.WF env`, **`hsu : env.SortUniq U`** | the converse costs `SortUniq` too |
| `Lean4Lean.VEnv.rigidPiUniq_iff_piInv` | 4 | `henv`, **`hsu`** | the `↔` is stated *under* `SortUniq` |

All three are `sorryAx`-free (cones 3230 / 3452 / 3454). So the honest statement is: **`PiInv` is
at least as strong as `RigidPiUniq` at `VEnv.WF`, and they coincide only relative to `SortUniq`** —
the corner's *other* open node. "Neither weaker nor stronger" must not be quoted flat; it is an
equivalence modulo an open hypothesis, exactly the error pattern method rule 3 names.

Corollary for the question I was given: refuting `PiInv` at `VEnv.WF` is **strictly easier** than
refuting `RigidPiUniq` there (`PiInv.rigidPiUniq` is the free direction), and proving it is
strictly harder. My target is the strong end of the pair.

### V2 (2026-09-05) — Q4 answered: **`VEnv.WF` does not forbid `.unsafeDef`, so a `VEnv.WF` environment can be inconsistent**

`VEnv.WF env := ∃ ds, VEnv.WF' ds env` (`Theory/Typing/Env.lean:132–136`), and `VEnv.WF'` chains
`VDecl.WF` steps with **no `isPure`/`noUnsafe` filter**. `VDecl.WF` has seven constructors, one of
which is `unsafeDef`, whose values are typechecked in `env'` — the environment *already carrying the
block's own constants*. Its own docstring calls it "circular by design … the only `VDecl.WF` rule
that can make a well-formed environment inconsistent", and `Theory/MutualDefUnsound.lean`
machine-checks a step (`selfRef_wf`, cone 864, hole-free) plus its inconsistency
(`selfRef_inconsistent`, cone 799, hole-free).

So the answer to "what does `VEnv.WF` permit that I am assuming it forbids" is: **inconsistency.**
`Theory/Consistency.lean`'s `leanTTConsistent` quantifies over `VEnv.LeanWF`, the *pure* fragment —
not over `VEnv.WF`. Nothing in the corner had used this. Two consequences, one of which is proved
and one of which is my own limit:

* **Proved (§1 of `PiInvWF.lean`)**: `∃ env, VEnv.WF env ∧ ¬ env.Consistent`. Hence **no model
  argument can prove `PiInv` at `VEnv.WF`**: a soundness model of a `VEnv.WF` environment would
  have to interpret one that proves `falseProp`. This is a *second and independent* reason the
  semantic route is dead, on top of `SemanticRouteClosed.lean`'s (which is about the shape of the
  conclusion, not about the environment class).
* **Limit, also proved (§1)**: this witness cannot refute `PiInv`. Its added rule is
  `.const f [] ≡ .const f []` — **reflexive** (`selfRefDV.toDefEq` has `lhs = rhs`), so `extra`
  produces nothing that `refl` did not. The `unsafeDef` clause buys inconsistency and *no new
  conversion between distinct terms*. Method rule 7: I prove my own witness's uselessness rather
  than leaving it as an implied refutation.

### V3 (2026-09-05) — the rule-source enumeration, and where non-orthogonality can come from

`VEnv.WF`'s only sources of entries in `env.defeqs` are the `VDecl.WF` constructors: `.def`
(one δ-rule, `VDefVal.toDefEq`, lhs `.const c (VLevel.params uvars)`, value typed *before* the
constant exists — well-founded), `.unsafeDef` (the same shape, values typed *with* the block's
constants — circular), `.quot`, `.induct`. `.axiom`, `.opaque` and `.example` add **no** rule:
`.axiom` can give a constant of any `IsType` type, but a term is not a conversion.
`addConst` fails on a name already present (and `addConsts` folds it), so **every constant carries
at most one δ-rule** — no `VEnv.WF` analogue of `InjPiRogue`'s two-rules-on-one-constant, and no
analogue of `InjCensus.censusEnv`'s non-`const`-headed lhs.

Consequence, stated as analysis (not machine-checked here): δ + β + η at one rule per constant is an
**orthogonal** rewrite system, and circularity from `.unsafeDef` costs termination, not confluence.
So a `VEnv.WF` refutation of `PiInv` cannot come from the δ layer; it must come from a
**non-left-linear, type-directed** rule. In `IsDefEq` there is exactly one: **`proofIrrel`**. That
localises the whole refutation question, and §2 of `PiInvWF.lean` prices it.

`.induct`'s large-elimination guard is present and is not a way in: `VInductDecl'.WF.isLE`
(`Theory/Inductive/Decl.lean:826`) demands `LECond` — `lvl.IsNeverZero`, or a single type with at
most one constructor all of whose fields are `Prop`s or occur in the conclusion's arguments. That is
the subsingleton-elimination guard, so no `VEnv.WF` environment can large-eliminate a `Prop` with
two constructors, which would have collapsed two unrelated ι-reducts under `proofIrrel`. I checked
for that hole specifically; it is closed.

### V4 (2026-09-05) — the deliverable: `Lean4Lean/Theory/Typing/PiInvWF.lean`, 16 declarations, all hole-free

Names as `scripts/exists.lean` prints them (population **487** built modules). Every row: *own value
is a hole: false; cone reaches sorryAx: false*. `#print axioms` run separately on each; no `sorryAx`
anywhere.

| name (all `Lean4Lean.VEnv.*`, module `Theory.Typing.PiInvWF`) | arity | cone | axioms |
|---|---|---|---|
| `wf_permits_inconsistent` | 0 | 877 | `[propext, Quot.sound]` |
| `wf_permits_inconsistent_inert` | 0 | — | `[propext, Quot.sound]` |
| `unsafeSelfRule_refl` | 0 | 71 | **none** |
| `unsafeSelfEnv_rules_refl` | 6 | 384 | `[propext, Quot.sound]` |
| `ForallEProofPair` (def) | 2 | 33 | — |
| `SortZeroConvProp` (def) | 2 | 30 | — |
| `SortZeroOneConv` (def) | 2 | 31 | — |
| `hasType_falseProp` | 3 | 617 | `[propext, Quot.sound]` |
| `hasType_piOne` | 3 | 618 | `[propext, Quot.sound]` |
| `not_piInv_of_forallEProofPair` | 3 | 44 | `[propext]` |
| `sortZeroOneConv_of_piInv_of_propConv` | 4 | 628 | `[propext, Quot.sound]` |
| `not_forallEProofPair_of_sortUniq` | 4 | 2380 | `[propext, Classical.choice, Quot.sound]` |
| `not_propConv_of_sortUniq` | 4 | 2117 | `[propext, Quot.sound]` |
| `not_sortZeroOneConv_of_sortUniq` | 4 | 2120 | `[propext, Quot.sound]` |
| `proofIrrel_route_self_defeating` | 4 | 2394 | `[propext, Classical.choice, Quot.sound]` |
| `sortUniq_of_route_open` | 4 | 2386 | `[propext, Classical.choice, Quot.sound]` |

(`wf_permits_inconsistent_inert` was added after the cone run; its axioms are measured, its cone is
`wf_permits_inconsistent`'s plus `unsafeSelfEnv_rules_refl`'s.)

The measured content, in one table — **the route table**:

| # | statement | what it says |
|---|---|---|
| 1 | `wf_permits_inconsistent_inert` | `∃ env, VEnv.WF env ∧ ¬ env.Consistent ∧ ∀ df, env.defeqs df → df.lhs = df.rhs` |
| 2 | `not_piInv_of_forallEProofPair` | two Π's with **non-convertible domains** inhabiting one `Prop` ⟹ `¬ PiInv env U` |
| 3 | `sortZeroOneConv_of_piInv_of_propConv` | `SortZeroConvProp` + `PiInv` ⟹ `Sort 0 ≡ Sort 1` at a sort |
| 4 | `not_forallEProofPair_of_sortUniq` | `Ordered` + `SortUniq` ⟹ ¬(route entry, Π form) |
| 5 | `not_propConv_of_sortUniq` | `Ordered` + `SortUniq` ⟹ ¬(route entry, sort form) |
| 6 | `not_sortZeroOneConv_of_sortUniq` | `Ordered` + `SortUniq` ⟹ ¬(route **exit residual**) |
| 7 | `proofIrrel_route_self_defeating` | 4 ∧ 5 ∧ 6 at once |

Rows 4–6 are the self-defeat: **one `SortUniq` refutes both ends of the route.** Row 6 is the part
that was not obvious and is the reason the route cannot be walked in the other configuration either
— if you *drop* `SortUniq` to get the route's entry, you lose the discrimination its exit needs.

### V5 (2026-09-05) — why the proof side is blocked too, measured

The `VEnv.WF`-only instruments a proof of `PiInv` at `VEnv.WF` would reach for are all
`sorryAx`-tainted **through `PiInv` itself**:

| instrument | module | arity | cone | holes in cone |
|---|---|---|---|---|
| `VEnv.WF.uniq'` | `Theory.Typing.Injectivity` | 12 | 3439 | `IsDefEqU.forallE_inv_stratified` |
| `VEnv.WF.sortUniq'` | ″ | 3 | 3441 | ″ |
| `VEnv.HasType.defeqU_l'` | ″ | 10 | 3440 | ″ |
| `VEnv.IsType.not_isProof` | ″ | 7 | 3456 | ″ |
| `VEnv.WF.proofTransport` | ″ | 3 | 3445 | ″ |
| `VEnv.WF.sortUniq` | `Theory.Typing.SortUniqFacts` | 3 | 3475 | ″ |

So at `VEnv.WF` there is **no** ¬conversion or uniqueness instrument that is not already downstream
of the hole. That is the precise sense in which "nobody has proved `PiInv` at `VEnv.WF`" is
structural: `VEnv.WF` adds, over `Ordered`, exactly the instruments that are circular here. Together
with §V2 (the model route is dead because `VEnv.WF` permits inconsistency) and
`Theory/SemanticRouteClosed.lean` (the model route is dead for a second, conclusion-shaped reason),
the proof side has no live entrance in this tree.

### V6 (2026-09-05) — verdict

**`PiInv` is still open at `VEnv.WF` — neither proved nor refuted — and the obstruction is now
named on both sides.**

* **Refutation side.** `VEnv.WF` admits exactly four rule sources (`.def`, `.unsafeDef`, `.quot`,
  `.induct`), one δ-rule per constant, `const`-headed lhs, and the large-elimination guard closed.
  The `Ordered`-level defects that refute the census's other four members (non-`const`-headed lhs;
  two rules on one constant) are therefore unavailable, and the newly found `.unsafeDef` freedom is
  **inert** (row 1). The one remaining non-left-linear rule is `proofIrrel`, and the route it opens
  is **self-defeating** (rows 4–6): it needs `SortUniq` to fail at its entrance and a `SortUniq`
  instance to hold at its exit.
* **Proof side.** Every `VEnv.WF`-only instrument is `sorryAx`-tainted through
  `forallE_inv_stratified` (V5), and the model route is dead twice over (V2 + `SemanticRouteClosed`).

So `PiInv`'s row in the census table stays **one-sided and unmeasured on the sufficiency axis**, but
its *insufficiency* column now has content it did not have: `Ordered` was not measurably
insufficient, and `VEnv.WF` is now measurably **not sufficient by any route this tree can walk**,
which is a different and weaker claim than "false", and must be quoted as such.

### V7 (2026-09-05) — scorecard on §1's cold predictions

| pred | verdict |
|---|---|
| **P1** (`def … : Prop`, arity ≥ 2 with invisible binders, open `Γ`, codomain conjunct in `A::Γ`) | **RIGHT**, all three parts (V1) |
| **P2** (`rigidPiUniq_iff_piInv` is a free two-way identification) | **WRONG** — the `↔` is stated **under `SortUniq`**; only `PiInv → RigidPiUniq` is free at `VEnv.WF` (V1). My brief's "neither weaker nor stronger" is an equivalence modulo an open node. |
| **P3** (open at `VEnv.WF`; no `VEnv.WF` refutation witness; obstruction is the `unique.tex` alternation index blocked by `SubstC`) | **RIGHT on the verdict, WRONG on the obstruction.** Open, no witness — but the obstruction I could actually measure is not `SubstC`/alternation at all: it is the self-defeat of the `proofIrrel` route plus the `sorryAx`-circularity of every `VEnv.WF`-only instrument. I never needed to touch the confluence story. |
| **P4** (the *codomain* conjunct is the blocked half; the domain conjunct is provable) | **WRONG, and inverted.** The refutation route lands on the **domain** conjunct (`not_piInv_of_forallEProofPair` and `sortZeroOneConv_of_piInv_of_propConv` both consume `.1`), and nothing here makes the domain half cheaper than the codomain half. `Theory/SemanticRouteClosed.lean` §3 independently records the *domain* conjunct's semantic route as DEAD. My `DefInvRefute`-flavoured guess was about the **stratified** system and does not transfer. |
| **P5** (not vacuous; `VEnv.WF`'s `defeqs` typing clause constrains the interesting premises) | **HALF RIGHT.** Not vacuous ✓. But the constraint that matters is not the typing of `defeqs` — it is `addConst`'s **name-freshness**, which is what forces one δ-rule per constant and kills the whole rogue-rule family at `VEnv.WF` (V3). |
| **P6** (a `VEnv.WF`-clause table; ≥ 1 new machine-checked lemma; verdict *open* with a named obstruction; no proof, no refutation) | **RIGHT** — 16 declarations, verdict open, obstruction named, hole census unchanged at 13. |

Build state at close: bare `lake build` green, **1673 jobs** (baseline 1672 + `PiInvWF`), guard 1 ✓
(24 frozen axioms), guard 2 ✓ (`proof INCOMPLETE: sorryAx present`, unchanged), guard 3 ✓ (2/2),
hole census **13** (unchanged). `PiInvWF.lean` warnings: **none**. `PiInvWF` is listed by
`scripts/sorry-census-all.lean` among modules a fixed-import census cannot reach — the same status as
`InjCensus` and `InjMethod`, the precedent for a witness/pricing-only module.

## §3 — Gaps in my own method

1. **"`proofIrrel` is the only non-left-linear rule, so it is the only refutation route" is
   ANALYSIS, not a theorem.** I read the rule sources off `VDecl.WF` and the orthogonality argument
   off the shapes of `toDefEq`/ι-rules; I did **not** machine-check "no `VEnv.WF` refutation of
   `PiInv` avoids `proofIrrel`". Proving that would be an induction over `IsDefEq` — i.e. the
   theorem itself. Anyone quoting the self-defeat result must keep the word *route* in it: what is
   proved is that **this** route is closed, not that all are.
2. **`ForallEProofPair` and `SortZeroConvProp` have no non-vacuity witness.** I could not show either
   is satisfiable at *any* environment (satisfiability at a `VEnv.WF` one would refute `PiInv`; even
   at `Ordered` I have none). They are hypotheses in the `PiLevelPin`/`SortUniq` style. So rows 2–3
   of the route table could in principle be vacuous, and their value is as a *reduction*, not a
   witness. `Injectivity.IsProof.forallE_fires` shows a Π-**typed** term can be a proof in an
   ordinary context; that is *not* the same as a Π-**headed** term being one, and the gap between
   them is exactly what I could not close.
3. **`SortZeroOneConv` is the canonical instantiation's residual, not the general one.** A cleverer
   `ForallEProofPair` might produce domains whose non-convertibility is refutable by something other
   than `SortUniq`. I chose `Prop` / `Sort 1` because `VLevel.imax_zero` makes both Π's typeable at
   `.sort .zero` with **no constraint on the domains at all** — which is the most permissive choice
   available — but "no other discriminator exists" rests on `UnivDiscrim.lean` having none plus
   `handoff-injcensus.md` §V3's two-technique enumeration, both of which are *absence* claims about
   the tree, not impossibility results.
4. **I did not attempt `PiInv ∅ U`.** `∅` **is** `VEnv.WF` (`WF'.empty`), so refuting `PiInv` there
   would settle the question outright, and proving it there would not (the statement is universally
   quantified over `VEnv.WF` environments). I judged a refutation at `∅` to need the same
   ¬conversion primitive and did not pursue it; that judgement is unmeasured, and `∅` is the
   cheapest unexplored witness left on this row.
5. **The `.unsafeDef` finding is proved but its consequence for the *model* route is argued.**
   `wf_permits_inconsistent_inert` is machine-checked; "therefore no model argument can prove `PiInv`
   at `VEnv.WF`" is a one-line inference I did not formalise (it would need a statement of what a
   model *is* at this generality, which lives in `Theory/SetModel/` and is not mine).
