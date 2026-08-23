# Scoping: algorithmic conversion + a logical relation

**Verdict: do not build.** Three reasons, in the order that decides it. The first is
machine-checked and is new; the second is a measurement of this repo, not an estimate; the
third is the scope.

1. **The environment class the targets are stated over is not normalising.**
   `Theory/Typing/LogRelRowZero.lean` (new, sorry-free, `[propext, Quot.sound]`) exhibits a
   `VEnv.WF` environment — reachable from the *empty* environment in one declaration step —
   whose weak-head reduction has a two-cycle between closed terms that are both well typed.
   Every open statement in `Theory/Typing/Injectivity.lean` is quantified over exactly that
   class. So a logical relation cannot deliver them **as stated**, and the repair (re-cut the
   environment class and re-route the `Verify/` consumers) is owned by another stream and has
   never been priced. §1.
2. **The route is not untried, and the tree records what it cost.**
   `Experimental/LogRel.lean` is a genuine typed Kripke logical relation — `Classifier` (a
   PER bundle), `LogRel` with `stuck | sort | forallE`, Kripke weakening, reducible
   substitutions, `fundamental`. It is 379 lines and stops inside `fundamental`'s **`trans`**
   case, with `_ => sorry` for every remaining rule. `Experimental/ShapeLogRel.lean` is the
   coarsened version carried to **8435 lines**; it currently **fails to build** (12 errors),
   and **49 of its 653 declarations are `sorryAx`-backed — including `LR` and `LRS`, the
   logical relation itself**. Its seam was provably vacuous, twice. §4.
3. **The scope is a normalisation proof for full Lean**, nested inductives included
   (`CLAUDE.md` forbids narrowing that), for which no published proof exists. §3.

**And one thing came out the other way, which is worth carrying regardless of the verdict.**
The two facts that closed every previous route — impredicative formation and proof
irrelevance (`docs/model-interface.md` §6) — do **not** obstruct a logical relation. They
neutralise each other. Machine-checked, §2. That is a *negative check*: it says the route is
not excluded at the point one would most expect it to be. It does **not** say a route exists
(trap #8), and it does not move the verdict.

---

## 0. Two corrections to the premise, before anything else

Both were in the brief that commissioned this document, and both change what has to be
priced.

**(a) A logical relation does not avoid a reduction relation. It avoids *confluence*.**
Every logical-relation development in the literature, and both of this repo's own attempts,
are built on weak-head reduction: `Experimental/LogRel.lean`'s `LogRel` constructors are
literally `Γ ⊢ A ⤳* .sort l` and `Γ ⊢ X ⤳* .forallE A B`, and its `stuck` case is "no
reduct is a normal type". What the logical relation replaces is Church–Rosser: instead of
proving confluence and reading injectivity off it, one proves the *consequences* of
confluence directly, by an induction that a conversion derivation can be fed into.

So `handoff-stratified.md` §8's conclusion — "what is missing is a **reduction relation**,
something that says what the middle term does" — is *satisfied* by this route, not bypassed
by it. That is the right way to read the route, and it is why §1's check bites: the missing
thing really is a reduction relation, and the row-zero question is whether one exists at the
generality required.

**(b) It is not outside anything the repo has.** `handoff-stratified.md` §9 flags
`Experimental/` as "the same idea carried much further"; that is about
`ShapeLogRel.lean`'s *shape lattice*, which is a finite abstraction of types and whose
refutations (`IsType.common` and every relativisation) are artifacts of the abstraction.
`Experimental/LogRel.lean` is a different and much closer thing: a textbook
Abel–Öhman–Vezzosi-shaped Kripke logical relation. Its refutations are not recorded anywhere
in `docs/`, because it has none — it simply stops. §4 reads it.

---

## 1. Row zero, check 1 — **machine-checked, and it is the decisive one**

### The check

*Which single assumption is most likely to kill the route?* That the reduction the logical
relation is defined over terminates on the environments the targets quantify over. Run it
first.

`Theory/Typing/Injectivity.lean` states every open target as

```lean
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) …
```

and `VEnv.WF env` is `∃ ds, VEnv.WF' ds env` over *arbitrary* `VDecl`s
(`Theory/Typing/Env.lean`). `VDecl.WF` includes `unsafeDef`, whose members are typechecked in
the environment **that already carries the block's own constants**. That is the whole content
of `Theory/MutualDefUnsound.lean`, which is in the tree as a regression test.

Two members that name each other therefore install `f ≡ g` **and** `g ≡ f` as
definitional-equality rules.

### The result

`Theory/Typing/LogRelRowZero.lean`, sorry-free, `[propext, Quot.sound]`:

```lean
theorem exists_wf_env_headStep_cycle :
    ∃ (env : VEnv) (e₁ e₂ : VExpr), env.WF ∧ e₁ ≠ e₂ ∧
      env.HeadStep e₁ e₂ ∧ env.HeadStep e₂ e₁ ∧
      env.HasType 0 [] e₁ falseProp ∧ env.HasType 0 [] e₂ falseProp

theorem headStep_not_wf : ¬ WellFounded (fun a b => loopEnv.HeadStep b a)
```

Three things about the witness, each of which had to be checked rather than assumed:

* **It is over the empty environment plus one step** (`loop_wf : VDecl.WF VEnv.empty …`), so
  it does not turn on the prelude, on inductives, or on anything about `Nat`.
* **Both terms are genuinely well typed** (`loop_hasType`), at `falseProp = ∀ p : Prop, p`,
  so this is not a junk-term artifact. `MutualDefUnsound.falseProp_isType` supplies the type
  over any environment.
* **`HeadStep` is defined in the file with no side conditions at all** — δ at the head, β at
  the head, congruence in a function position. It is deliberately *not*
  `Theory/Typing/HeadReduction.lean`'s `⤳`, which sits under `VEnv.Params`, a class nothing
  instantiates; a statement about that relation would be vacuous. The negative is therefore
  about the environment and nothing else.

### What it does and does not settle

**Settled.** No normalisation argument — logical relation, reducibility candidates, or
otherwise — can prove `IsDefEqU.sort_inv`, `forallE_inv_stratified`, `sort_forallE_inv`,
`const_app_inv`, `const_forallE_inv` or `const_sort_inv` at the generality they are stated
at. The reduction diverges.

**Not settled, and not claimed.** That those statements are *false* on such an environment.
They are probably true: to make `sort_inv` fail one needs a rule relating a sort to something
else, and every `VDefVal.toDefEq` left-hand side is a constant. *Aiming a refutation of
`sort_inv` at a `.unsafeDef` environment is a cheap open thread and nobody has tried it* — an
inconsistent environment is exactly where `proofIrrel` is strongest, since `falseProp`'s
inhabitant makes every proposition inhabited. If it succeeds, the statements need re-cutting
whatever route is taken.

### Is it repairable? Yes — but the repair is not this stream's, and it has never been priced

The obvious move is to restrict to the pure fragment. `Theory/Consistency.lean` already
defines `VEnv.LeanWF` for exactly that, and `Verify/Bridge.lean:236` proves
`TrEnv .safe env venv → venv.LeanWF`. So the *model* side is already cut correctly.

The **algorithm** side is not, and that is the cost:

| consumer | where | environment |
|---|---|---|
| `TrProj.uniq`, `TrProj.defeqDFC`, `TrProj.weak'_inv` | `Verify/Typing/Lemmas.lean` | `henv : VEnv.WF env` |
| `reduceRecursor.WF`'s quotient / `Quot.ind` branches | `Verify/TypeChecker/WHNF.lean` | via `VContext` |
| `IsDefEq.uniqU` uses | `Verify/TypeChecker/{Basic,InferType}.lean` | `c.Ewf : VEnv.WF c.venv` |

`VContext` (`Verify/TypeChecker/Basic.lean:190`) carries `safety : DefinitionSafety` and
`trenv : TrEnv safety env venv`, and `TrEnv'.unsafeDef` fires at non-`safe` safety by design
— *because the kernel really does δ-unfold `partial` definitions*
(`MutualDefUnsound.lean`, "This is not an implementation divergence"). So the type-checker
correctness proofs are stated over an environment class that provably contains δ-cycles, and
re-cutting them at `.safe` is a `Verify/`-stream refactor of unknown size.

**This is a prerequisite for any normalisation route, not only this one**, and it is the one
finding here that is worth acting on regardless of the verdict.

---

## 2. Row zero, check 2 — impredicativity and proof irrelevance **do not** block it

### The check

*Which is the second-most-likely killer?* That the logical relation's defining recursion has
no well-founded measure, because impredicative `Prop` lets `∀ (A : Type 500), P A` sit at
level `0` with a domain at level `501`. In a predicative hierarchy the Π case recurses into
the domain at a level bounded by the Π's own; impredicativity destroys that bound. This is
the point at which every previous route died (`docs/model-interface.md` §6:
impredicative formation forces the `{•}` collapse; proof irrelevance forces the
identification).

### The result — the bound holds exactly where recursion is needed

`Theory/Typing/LogRelRowZero.lean`, sorry-free, `[propext]`:

```lean
theorem imax_measure (h : (VLevel.imax u v).eval ls ≠ 0) :
    u.eval ls ≤ (VLevel.imax u v).eval ls ∧ v.eval ls ≤ (VLevel.imax u v).eval ls

theorem imax_domain_unbounded (k : Nat) (ls : List Nat) :
    ∃ u : VLevel, u.eval ls = k ∧ (VLevel.imax u .zero).eval ls = 0
```

Read together:

* **Where a Π-type is not a proposition, the hierarchy is predicative** and both components
  are bounded by the Π's level. The measure exists.
* **Where it is a proposition, the measure fails completely** — the domain's level is
  unbounded. So the logical relation's Π case *must* be non-recursive there.
* And that is exactly the case where **proof irrelevance makes recursion unnecessary**: at a
  proposition, all inhabitants are identified, so the relation is the total relation on
  well-typed terms and never consults the domain.

**So the two facts that closed every previous route are, in this setting, the same fact
pointing the other way: impredicativity is confined to precisely the case proof irrelevance
trivialises.** That is the one genuinely encouraging thing in this document, and it is worth
recording because the natural expectation runs the other way and would have mis-scheduled the
work.

*Trap #8 applies.* This is a negative check. It licenses "the route is **not excluded** at
its most feared point". It does **not** license "the route is open", and it does not move the
verdict, which rests on §1 and §3.

### A design consequence, and it is forced

`imax_measure` is stated **per level valuation** (`ls : List Nat`), and it has to be:
`VLevel` is symbolic, and `VLevel.imax u v` evaluates to `0` at some valuations and to
`max u v` at others whenever `v` is a parameter. There is no valuation-independent measure.

So a logical relation for this theory is a **family indexed by a level valuation**, exactly
as `Theory/SetModel/` is (`docs/model-interface.md` §3). Every consequence (`u ≈ v`) is then
recovered by quantifying over valuations, which is what `VLevel.Equiv` already is
(`equiv_def : a ≈ b ↔ ∀ ls, a.eval ls = b.eval ls`). No obstacle; a fact to build in from
line one rather than discover at line 3000.

---

## 3. What it consists of, for *this* theory

Not the generic recipe — the component list against this tree, with the hard parts named.

| # | component | state in tree | difficulty |
|---|---|---|---|
| 1 | weak-head reduction on `VExpr`, **and its determinism** | `HeadReduction.lean` (696 l) — but under `[VEnv.Params]`, uninstantiated. `Pattern`/`PatternDecode`/`PatternRules`/`DeltaUnique` (4450 l) supply rule decoding and `pat_uniq` | **must be restated `Params`-free**; see the circularity note below |
| 2 | the relation itself, per valuation, per universe level | `Experimental/LogRel.lean` is the design; nothing on `VExpr` | the `Sort`/Π/neutral cases are textbook |
| 3 | the **Prop/irrelevant** case | nothing | new, but §2 says it is the *simple* case |
| 4 | the case for **inductive type applications, generically over `VInductDecl'`, nested included** | nothing syntactic. The set model's analogue (`SetModel/Inductive.lean`, `IndStage`, `IndCard`, `IndInterp`, `CtorTrans`) took a whole stream | **the largest single item, and the one with no precedent** |
| 5 | canonicity inside (4): a reducible inhabitant of an inductive whnfs to a constructor application | nothing | needed for (6) |
| 6 | the ι-rule case of the fundamental lemma, one per `iotaRule` (`Inductive/Decl.lean:617`) | nothing | rests entirely on (5) |
| 7 | `Acc.rec` | falls under (4)/(6) — `Acc` is an ordinary inductive here | needs well-founded recursion *inside* the relation |
| 8 | the quotient rule `quotDefEq` (`Theory/Quot.lean:11`) | nothing | small; `Quot.sound` is an *axiom*, contributes no reduction |
| 9 | definitional **η** | nothing | free — a *typed* logical relation at Π is extensional; this is a reason to prefer it |
| 10 | fundamental lemma over the 21 constructors of `IsDefEqStrong` (13) + `HasTypeStrong` (8) | the judgments exist, sorry-free | the `trans` case is where `Experimental/LogRel.lean` stops |
| 11 | escape/adequacy, then the injectivity family | `Injectivity.lean` states the targets | small once (10) lands |

**The hard parts, named.** (4)+(5)+(6) — generic inductive families with nested
declarations. Everything else in the theory is either textbook (Π, `Sort`, neutral, η) or
made *easy* by proof irrelevance (§2). This is the opposite of the expected answer, and it
matters: the difficulty is not `Prop`, it is inductives.

**One thing this theory does *not* have, which is a real saving.** The abstract theory has
**no K-like reduction and no structure η**: `Inductive/Decl.lean:457` states that explicitly
("neither K-like reduction nor structure eta contributes a side condition"), and the only
rule forms in a `VEnv.WF` environment are δ-rules, `quotDefEq`, and `iotaRules`. K-like
reduction is a *kernel algorithm* fact that `Verify/` must justify against this theory (via
proof irrelevance), not a rule the relation would have to model. The standard obstacle —
"a recursor fires on a neutral major premise, so neutrals are not stable" — does not arise
here.

### The circularity note on (1), which is easy to miss

`VEnv.Params.pat_wf` **needs `IsDefEqU.forallE_inv`** — `PatternRules.lean:1985–2020` traces
this in detail. So the tree's existing weak-head reduction is gated on the very family the
logical relation is being built to prove. It is not a genuine cycle (the two classes named
`Params` are different, and the route terminates through the shape model), but the shape
model's exports are `sorryAx`-tainted and vacuous. **Practically: the reduction relation an
LR would sit on has to be rebuilt without the gate.** That is 696 lines to restate plus
whatever `pat_uniq` costs unconditionally.

---

## 4. What survives from the current tree

The question was "reusable / dead / **wrong**". The distinction pays here in an unusual
direction:

> **Nothing in the tree becomes wrong.** A logical relation adds no rule to any judgment —
> it is metatheory over the same `IsDefEq`. Contrast candidate 1 of
> `docs/options-circularity-breakers.md` (instantiation as a rule), which made
> `SubstCRefute`'s conclusion derivable and so required the refutation to be *deleted*. That
> is a real advantage of this route and it should be recorded even though the route is not
> being taken.

| | lines | fate |
|---|---|---|
| `Typing/Strong.lean` | 1066 | **reusable, essential.** `HasTypeStrong` is Carneiro's separated typing judgment with `defeq` isolated in one constructor; `IsDefEq.strong` is the bridge; `HasTypeStrong.regular` (trap #12) gives every constructor's type its own typing for free, which is what a fundamental lemma needs at every case |
| `Typing/DeclRules.lean` | 264 | **reusable, essential.** `instL_lhs_ne_sort` / `instL_lhs_ne_forallE` classify a WF environment's rules as δ / quot / ι — exactly the case split the `extra` case of the fundamental lemma needs |
| `Typing/{Pattern,PatternDecode,PatternRules,DeltaUnique}.lean` | 4450 | **reusable**, and it is the reduction relation's infrastructure. `Injectivity.lean`'s own docstring records that this cone imports neither `Injectivity` nor `UniqueTyping` |
| `Typing/HeadReduction.lean` | 696 | **reusable only after de-gating** — see §3 |
| `Typing/{Lemmas,EnvLemmas,Basic,Env}.lean` | ~1100 | reusable (weakening, substitution, inversion for the ambient judgment) |
| `Typing/Injectivity.lean` | 382 | **the targets, unchanged.** The route delivers all six |
| `Typing/Stratified.lean` | 531 | **dead, not wrong.** The alternation index has no counterpart in a logical relation. `Stratified.{mono,weakN,instN}` stay true and stay unused |
| `Typing/UniqueTypingN.lean` | 719 | **dead, not wrong.** `DefInv`, `SubstC`, `PropTypeAgree`, `SortForallEDisjoint` at the index are all *weaker* than what the relation proves unstratified. `HasTypeN.*_inv` — the handoff's "asset" — is inversion for a judgment the route does not use |
| `Typing/{SubstCRefute,SubstTRefute}.lean` | 393 | **dead, and still true.** They refute statements about the index; the route has no index |
| `Typing/{ShapeSpine,UnivDiscrim}.lean` | 736 | **dead, and still true** |
| `Typing/{SortUniq,SortUniqFacts}.lean` | 174 | **partly live**: the cumulativity refutation of `SortUniq` as a *semantic* consequence survives and is what forces a syntactic route in the first place |
| `Typing/ChurchRosser.lean` | 2207 | **mostly dead.** `NormalEq` is replaced by the relation. `ParRed` (no typing hypotheses, layerable) may be reusable as the reduction. All 88 declarations are currently vacuous — nothing instantiates `Params` |
| `Experimental/LogRel.lean` | 379 | **reusable as a design template only** — it is over `SExpr` under the vacuous `[Params]`, so nothing in it is available as a proof. Read it before writing a line |
| `Experimental/ShapeLogRel.lean` | 8435 | **dead**, and see below |

**Net: ~2550 lines of the current stratified cone go dead (none of it false), ~6500 lines of
reduction/typing infrastructure carry over.**

### `Experimental/LogRel.lean`, read — the most informative thing in the tree

379 lines. A typed Kripke logical relation, in the modern style:

* `Classifier'` is a **PER bundle** — `EqTy' / HasTy' / DefEq'` with `defEq'_symm`,
  `defEq'_left`, `defEq'_self`;
* `Classifier.forallE` quantifies over **all weakenings** `Ctx.Lift' ρ Γ Δ` — the Kripke
  worlds — and stores the domain's classifier and a codomain classifier indexed by a
  *reducible argument*;
* `LogRel : ∀ Γ A u, Classifier Γ A u → Type` with `stuck | sort | forallE`, each carrying a
  reduction `⤳*` to its head normal form;
* `LogRelV` / `ClassifierV` — **reducible substitutions**, and `LVIsType` / `LVHasType` /
  `LVDefEq` — the validity judgments;
* `fundamental (H : Γ ⊢ a ≡ b : A) (J : ⊩ᵛ Γ) : ∃ u, ∃ JA : J ⊩ᵛ[u] A, JA ⊩ᵛ a ≡ b`.

**And `LRIsType.irrel` is proved, sorry-free, at line 157–181.** This is the load-bearing
observation of the whole document, so state it precisely:

```lean
theorem LRIsType.irrel' (J1 : Γ ⊩[u] A) (J2 : Γ ⊩[u'] A) : u = u' ∧ J1 ≍ J2
instance : Subsingleton (Γ ⊩[u] A)
```

Its proof is: the two relations are forced into the same constructor because weak-head
reduction is **deterministic** (`determ`), and in the `sort` case that immediately yields
`u = u'`. **That is universe uniqueness, and it is where every member of the injectivity
family comes from.** See §5.

Where it stops, and this is the honest measurement: `fundamental`'s **`trans`** case is
`sorry`, and every rule other than `bvar / symm / trans / sort` is `_ => sorry`. Three
supporting lemmas are also `sorry`: `LREqTy.defeq_r` (:244) and all three cases of
`LREqTy.symm` (:246). So the file reaches the fundamental lemma and stops at the first case
that needs the PER laws to compose across two different classifier derivations. **`Prop`,
proof irrelevance, constants, inductives, ι-rules and quotients are not represented in the
relation at all** — `NormalType` is `sort | forallE` and nothing else.

### `Experimental/ShapeLogRel.lean` — the empirical price

8435 lines. It **fails to build**: 12 errors, so lake emits no `.olean` and its four
dependents (`ShapeLogRelAdequacy`, `UniqueTyping`, `BridgeInjectivity`, `Reflect/Capstone`)
are never attempted and carry stale artifacts. Its own axiom sweep records **49 of 653
declarations `sorryAx`-backed**, and the list includes `LR` and `LRS` — the logical relation
itself — along with `LE_Interp.sound`, `LE_Interp.forallE_inv`, and the entire join family.
Its `[ParamsExtra]` seam was **provably unsatisfiable, twice**, so everything downstream of
it was vacuously true. Its own §19 records the verdict: *"Option 3 is therefore NOT
're-prove two statements the shape model established'. The shape model never established
them."*

That development is a coarser thing than a real logical relation — it abstracts types by a
finite shape lattice, and its six refuted statements are all artifacts of the abstraction.
But as a **price signal** it is exactly on point: 8435 lines spent, currently red, seam
vacuous, relation `sorryAx`-backed.

---

## 5. What it would deliver — the whole family, and there is no cheaper sub-target

### The mechanism, named

Everything the project wants comes from **one lemma**: `LRIsType.irrel` — "the logical
relation at a type is unique" — together with **determinism of weak-head reduction**.

Given those, for a type `A`:

* `A`'s relation is in exactly one case, determined by `A`'s (unique) weak head normal form;
* two derivations `Γ ⊢ A : .sort u` and `Γ ⊢ A : .sort v` produce two relations at `A`, which
  `irrel` identifies, forcing `u = u'` in the `sort` case.

From that, in one step each:

| target | how |
|---|---|
| `IsDefEqU.sort_inv` | `.sort u` and `.sort v` land in the `sort` case; `irrel` gives the level |
| `IsDefEqU.forallE_inv{,_stratified}` | the `forallE` case *stores* the domain's and codomain's relations; `irrel` identifies them |
| `IsDefEqU.sort_forallE_inv` | the two are different constructors; whnf determinism separates them |
| `const_app_inv`, `const_forallE_inv`, `const_sort_inv` | the (missing, §3 item 4) inductive/constant case, same way |
| `SortUniq` | `sort_inv` + the `defeq` case |
| `PropUniq`, `PropTypeAgree` | the same, restricted to the `= 0` test |
| a confluence development | subsumed — the relation replaces it |

**So there is no cheaper sub-target inside the route.** One cannot build "the part of the
relation that decides propositionhood": deciding whether `A` is a proposition requires `A`'s
whnf; if the whnf is `Π(x:α).β` the answer is decided by `β`'s sort in context `α::Γ`, which
requires `α` to be a reducible type and `β` a reducible family — i.e. the full apparatus at
the domain. This is `handoff-stratified.md` §8's "a sorts-only normalisation is not a
shortcut", transposed, and it fails for the same reason: the Π case drags in the whole
type structure. *Analysis, not machine-checked.*

---

## 6. The honest alternative: is `PropUniq` + `PropTypeAgree` a cheaper target?

The brief asks this directly, because the model needs those two and not unique typing.
**Answer: they are a strictly smaller *statement*, but not a smaller *build*, and the two
apparent ways to make them smaller are both closed.**

### (a) `PropUniq` cannot be weakened away from the model's interface

`docs/model-interface.md` §5 already settles the two obvious weakenings: the minimum
convention was attempted and refuted at `propSound_of_mem_sort`'s load-bearing
`u.eval ls = 0` and at `Sound.proof`'s use of the premise's own sort. The `↔`-form stands,
and it needs `PropUniq`.

Restated from the syntax side: whatever `IsProp` is defined to be, the `⇒` direction of

```
IsProp Γ A ↔ u.eval ls = 0     whenever Γ ⊢ A : .sort u
```

says that *every* sort of `A` agrees with the one `IsProp` was defined from. That is
`PropUniq` verbatim. There is no formulation of a syntax-directed interpretation that avoids
it.

### (b) A **derivation-directed** interpretation does not remove it either — it is the same statement

This is the one idea in this neighbourhood that has not been written down, so it is worth
closing explicitly.

`PropSplit` exists only because `interp` is *syntax*-directed: `docs/model-interface.md` §5's
argument is "the collapse must be decided at `lam` and `app`, which **carry no type**". A
`lam` *derivation* does carry its type. So: interpret derivations, not terms.

**It relocates `PropUniq` to a coherence obligation, and the obligation is `PropUniq`.**
`HasTypeStrong.lam` carries `v.WF uvars` and `A::Γ ⊢ B : .sort v`. Two derivations of the
same `Γ ⊢ .lam A b : .forallE A B` may pick `v` and `v'` for the same `B`; the interpretation
branches on whether the codomain is a proposition; so coherence of the derivation-directed
interpretation demands `Γ ⊢ B : .sort v`, `Γ ⊢ B : .sort v'` ⟹ `v ≈ 0 ↔ v' ≈ 0`. That is
`PropUniq`.

And coherence is not optional: the soundness induction's `trans` case has two derivations for
the middle term and must give them one value. *Analysis, not machine-checked, but it is one
line from the constructor list — trap #11 in a new instance, and trap #12's advice (read the
constructors before pricing) is what produced it.*

### (c) A **type-directed** interpretation removes `PropSplit` — and is a logical relation

The remaining escape is to make the interpretation type-directed: define `⟦A⟧` by recursion
on `A`'s structure and interpret `Γ ⊢ e₁ ≡ e₂ : A` as membership in `⟦A⟧`'s relation. Then
`lam` and `app` never need a Prop decision, because the *type* index supplies it. This does
work, and `PropSplit` disappears.

But recursion on `A`'s structure only makes sense at `A`'s weak head normal form, and `trans`
needs the relation to be a PER. **That is exactly a logical relation**, and it is priced in
§§1–5. So the cheap-looking escape from the model's two imports is the expensive route,
reached from the other end.

### Conclusion on the cheaper target

`PropUniq` + `PropTypeAgree` is a genuinely weaker *statement* than unique typing — that gain
is real and it is what step 1 of `model-interface.md` §5 bought. It is **not** a cheaper
*build*: every route to it goes through the same construction, and the two ways to dodge the
construction are (b) the same statement and (c) the construction itself.

---

## 7. What this leaves

Five routes are now closed and this is the sixth priced out. The state:

* **the reference's `thm:utype`** — invalid, machine-checked;
* **four repairs to the alternation index** — closed by index arithmetic;
* **`unique.tex` §§3–4 at the index** — closed, `SubstT` false;
* **universe discrimination / `common_sort`** — refuted;
* **the hereditary strengthening** — equivalent to the statement it would prove;
* **a logical relation** — not excluded on its two most-feared assumptions (§2), and priced
  out on scope, on this repo's own two attempts, and on §1's environment-class check.

Three things are worth doing, in this order, and none of them is "build a logical relation":

1. **Re-cut the environment class of the injectivity family** (§1). It is a prerequisite for
   *any* normalisation-flavoured route, it is cheap to state, and the mismatch is currently
   invisible: `Verify/`'s consumers run at arbitrary `DefinitionSafety` while the model side
   is already correctly cut at `VEnv.LeanWF`. Owned by the `Verify/` stream.
2. **Try to refute `sort_inv` on a `.unsafeDef` environment** (§1). Cheap, and decisive
   either way: if it succeeds, the statements need re-cutting and (1) becomes mandatory
   rather than hygienic; if it fails, that is evidence the statements survive the class they
   are stated over.
3. **Escalate the real choice.** The remaining options are (i) a normalisation proof for
   Lean, which is an open research problem — the largest comparable machine-checked CIC
   development, MetaCoq, assumes normalisation rather than proving it (*recollection, not
   verified in this session; check before quoting*) — or (ii) assuming `PropUniq` /
   normalisation explicitly, which `Verify/Guard.lean`'s axiom whitelist forbids. That is a
   project-owner decision and it should be taken as one rather than absorbed by another
   stream.

---

## 8. Confidence, kept apart

**Machine-checked** (`Theory/Typing/LogRelRowZero.lean`, sorry-free, `[propext, Quot.sound]`):

* `VEnv.WF` admits an environment with a well-typed weak-head reduction two-cycle, one
  declaration step from empty (`exists_wf_env_headStep_cycle`, `headStep_not_wf`);
* a non-propositional Π-type bounds both its components' levels (`imax_measure`), and a
  propositional one bounds neither (`imax_domain_unbounded`).

**Measurements of this repo** (reproducible; counts from a full read of the files named):

* `Experimental/LogRel.lean`: 379 lines, `LRIsType.irrel` proved, `fundamental` stops at
  `trans`, no `Prop`/const/inductive case in the relation;
* `Experimental/ShapeLogRel.lean`: 8435 lines, 12 build errors, 49 of 653 declarations
  `sorryAx`-backed including `LR`/`LRS`, seam provably vacuous twice;
* `Verify/`'s injectivity consumers run at arbitrary `DefinitionSafety` via `VContext`;
* the abstract theory has no K-like reduction and no structure η
  (`Inductive/Decl.lean:457`), and exactly three rule forms: δ, `quotDefEq`, `iotaRules`;
* `VEnv.Params.pat_wf` needs `forallE_inv` (`PatternRules.lean:1985–2020`).

**Analysis, not machine-checked:**

* no cheaper sub-target exists inside the route (§5), by the same argument that closed
  sorts-only normalisation;
* a derivation-directed interpretation relocates `PropUniq` to coherence, where it is the
  same statement (§6b);
* the component list and difficulty ordering in §3, in particular that generic nested
  inductives are the largest item.

**Reading result / recollection, flagged as the weakest item here:** that no machine-checked
normalisation proof exists for CIC or for Lean's theory, and that MetaCoq's verified checker
is conditional on a normalisation assumption. Check before quoting.
