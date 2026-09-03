# handoff-injcorner — the two Injectivity.lean holes, re-measured and one of them narrowed

Owner file: `Lean4Lean/Theory/Typing/InjCorner.lean` (new this round).
All measurements below were taken on **2026-09-03, 16:00–16:20 UTC**, on the working tree at
`1191a23` + the four uncommitted files listed in `git status` at session start.  **Re-measure
before quoting.**  Counts in this tree decay; three prose counts I checked had decayed (§1.3).

## §0 What this round did and did not do

* **Did not close either hole.**  Both `sorry`s stand.
* **Did** re-measure the load-bearing consumer sets of both holes (§1), which are much smaller
  than the reference counts suggest — 3 and 2 respectively.
* **Did** narrow hole B's three *negative* conjuncts to their **closed-context** forms, machine
  checked, hole-free, with the converse, so the reduction is an equivalence over the family of
  `VEnv.WF` environments and cannot be re-attacked as an open direction (§2).
* **Did** locate exactly what blocks the same move for hole B's two *positive* conjuncts: it is
  axiom conservativity + strengthening, i.e. `IsDefEqU.weakN_iff` (another of the 13 holes) and
  `ConstVar.AxiomConservativity` — so the asymmetry is a named node, not a gap in effort (§3).
* **Did not** find a counterexample to either hole; §4 records the two refutation attempts that
  failed and why, so they are not retried.

(sections filled in as the round progressed; see below)

## §1 What each hole states, and who actually depends on it

### §1.1 Hole B — `Injectivity.lean:1046`

    theorem WF.rigidShapeUniqNS (henv : VEnv.WF env) : env.RigidShapeUniqNS U := sorry

`RigidShapeUniqNS` (`Injectivity.lean:1006`): for every `Γ` with `OnCtx Γ (env.IsType U)`, every
`e`, `T` and every pair of `RigidShape`s `s₁ s₂` that are not both sorts, if `e` converts to both
`s₁.toExpr` and `s₂.toExpr` **at the same type `T`**, `e` is not a proof, and each shape's
`RuleFree` side condition holds, then `s₁.Compat env U Γ s₂`.  `Compat`'s diagonal entries are the
three injectivity facts (sort levels `≈`; Π domains and codomains convertible, the codomain in
*both* contexts; same-head spines' levels `≈` and arguments convertible) and its six off-diagonal
entries are `False`.  With `sort`/`sort` excluded, that is **eight entries**, and
`RigidNodeCircle.rigidShapeUniqNS_iff_family` proves it *equivalent* (given `SortUniq` and
`ProofTransport`) to the five-fold conjunction

    PiInv ∧ RigidSortPiDisj ∧ RigidConstAppInv ∧ RigidConstPiDisj ∧ RigidConstSortDisj

### §1.2 Hole A — `Injectivity.lean:261`, the `sorry` on line 268

    theorem IsDefEqU.forallE_inv_stratified (henv) (hΓ) (h1 : IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
        (h2 : HasTypeStratified U Γ (.forallE A B) V true n)
        (h3 : HasTypeStratified U Γ (.forallE A' B') V' true n') :
        (∃ u, IsDefEq U Γ A A' (.sort u) ∧ HasTypeStratified U Γ A (.sort u) true n) ∧
        ∃ u, IsDefEq U (A::Γ) B B' (.sort u) ∧ HasTypeStratified U (A::Γ) B (.sort u) true n ∧
             HasTypeStratified U (A'::Γ) B' (.sort u) true n'   := sorry

Π-injectivity, with each conversion **paired with a stratified typing derivation at the same
level and at the index inherited from the hypothesis**.  The level alignment is the content; the
plain (unstratified) form is `PiInv`, which is hole B's `pi`/`pi` entry.

### §1.3 Reference counts, measured 2026-09-03 16:05–16:12 UTC with `lean_references`

| symbol | total refs | of which uses (refs − 1 decl) | files |
|---|---|---|---|
| `VEnv.RigidShapeUniqNS` (the `def`) | 39 | 38 | 14 |
| `VEnv.WF.rigidShapeUniqNS` (**the hole**) | **4** | **3** | 2 |
| `VEnv.WF.rigidShapeUniq` (the wrapper) | 9 | 8 | 2 |
| `VEnv.IsDefEqU.forallE_inv` | 60 | 59 | 20 |
| `VEnv.IsDefEqU.forallE_inv_stratified` (**hole A**) | **3** | **2** | 2 |

**Hole B has exactly three direct consumers**, and all three are load-bearing:

1. `Injectivity.lean:1065`, `WF.rigidShapeUniq` — the nine-entry wrapper, whose own 8 uses are
   the five inversion theorems' `trans` cases (lines 1265, 1268, 1336, 1392, 1395, 1456, 1459)
   plus `ShapeIndep.lean:102`;
2. `Injectivity.lean:1215`, `IsDefEqU.forallE_inv` — via `RigidShapeUniqNS.piUniq`, i.e. the
   `pi`/`pi` entry only.  This is the wide consumer: 59 uses in 20 files, `Verify/Typing/Lemmas`
   and `ChurchRosser` included;
3. `ShapeIndep.lean:364` (`rows12_hold`) — deliberately tainted, per that file's own docstring.

**Hole A has exactly two**: `UniqueTyping.lean:44` (inside `IsDefEq.uniq`'s `app` case) and
`Injectivity.lean:546` (`piInvStrat_axiom`, packaging only).  The `uniq` call passes the **same**
index for both stratified premises and **discards the first conjunct**, so the only instance any
consumer needs is `PiInvStratApp` (`Injectivity.lean:...`), which `Injectivity.lean` already
records and which `piInvStratApp_iff_convStep2_sortInv` (`InjChainStep.lean:227`) prices.

**Decayed prose counts found (report, do not trust):**  the tree's prose gives hole A as a
"534-user hole" (`docs/handoff-injectivity.md:1238`), "736-user" (`docs/audit-doc-claims.md:376`),
"714-user" (`docs/handoff-sortinv-route.md:13,56,160`), "449-user"
(`Theory/Typing/RigidNodeCircle.lean:44`, `ORCHESTRATOR.md:572`), "515-user"
(`Theory/SemanticRouteClosed.lean:129`) and "468-user" (`ORCHESTRATOR.md:822`); hole B as
"176-user" (`RigidNodeCircle.lean`) and "460-user" (`docs/vacuity-ledger.md` row 183).  These are
*forward-cone* (transitive) counts, not reference counts, and they disagree with each other by a
factor of 1.6.  A fresh transitive measurement is in §5.

## §2 The result: hole B's three **negative** conjuncts are context-free

`Lean4Lean/Theory/Typing/InjCorner.lean`, all hole-free
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; build: 110 jobs, zero warnings in the
file):

    SortPiDisjNil    env U : ∀ {u A B},        ¬ env.IsDefEqU U [] (.sort u) (.forallE A B)
    ConstPiDisjNil   env U : ∀ {c ls as A B},  env.RuleFreeHead c →
                                               ¬ env.IsDefEqU U [] ((.const c ls).mkApp as) (.forallE A B)
    ConstSortDisjNil env U : ∀ {c ls as u},    env.RuleFreeHead c →
                                               ¬ env.IsDefEqU U [] ((.const c ls).mkApp as) (.sort u)

    rigidSortPiDisj_iff_nil     : (∀ env, env.WF → env.RigidSortPiDisj U)   ↔ (∀ env, env.WF → SortPiDisjNil env U)
    rigidConstPiDisj_iff_nil    : (∀ env, env.WF → env.RigidConstPiDisj U)  ↔ (∀ env, env.WF → ConstPiDisjNil env U)
    rigidConstSortDisj_iff_nil  : (∀ env, env.WF → env.RigidConstSortDisj U)↔ (∀ env, env.WF → ConstSortDisjNil env U)

and the composite

    rigidShapeUniqNS_of_nilFamily :
      (∀ env, env.WF → PiInv env U) → (∀ env, env.WF → RigidConstAppInv env U) →
      (∀ env, env.WF → ConvStep2 env U) →
      (∀ env, env.WF → SortPiDisjNil env U) → (∀ env, env.WF → ConstPiDisjNil env U) →
      (∀ env, env.WF → ConstSortDisjNil env U) →
      ∀ env, env.WF → env.RigidShapeUniqNS U

**Mechanism.**  `ShapeIndepStep.axiomize_step` replaces the outermost context entry by a fresh
axiom (`FreshNames`, discharged by `ShapeIndepFresh.freshNames`, which I re-measured as
**hole-free**, cone 1090 — `ShapeIndep.lean`'s claim about it is accurate), shortening `Γ` by one
and enlarging `env` by one constant.  A negative conjunct's `IsDefEqU` is a **hypothesis**, so it
transports *forward* (`IsDefEqU.mono` then `IsDefEqU.instN`).  Both shapes survive `VExpr.inst`:
`.sort u` literally, `.forallE`/spines componentwise (`VExpr.mkApp_inst`), rule-freeness by
`axiomize_step`'s own `∀ c', env.RuleFreeHead c' → env'.RuleFreeHead c'`.  This is
`ShapeIndep.spineVarPiDisj_of_constPiDisj`'s induction with the `spineHead` case analysis deleted.

**The quantification over environments is load-bearing** and is stated as such: the reduction is
*not* available at a fixed `env`, because each step adds a constant.  The `↔`s are therefore in the
`∀ env, env.WF → …` form.  This is the same shape `ShapeIndep.lean`'s rows take.

**Control (§5 of the file).**  `ShapeIndep`'s analogous induction has a **free base case** —
`SpineVar.spineVarPiDisj_nil` closes the empty-context instance outright, since a closed term
cannot have a `.bvar` spine head.  Nothing like that is available here, and
`nil_endpoints_typeable` machine-checks why: `.sort .zero` and
`.forallE (.sort .zero) (.sort .zero)` are both closed, both typeable at `[]`, over **every**
environment.  So §2 is a genuine restriction and not a disguised discharge.

### §2a Cone measurements for this round's declarations (`scripts/exists.lean`, 2026-09-03 16:22 UTC, population 417 modules)

| declaration | arity | cone | own value a hole | cone reaches `sorryAx` |
|---|---|---|---|---|
| `SortPiDisjNil` | 2 | 14 | no | **no** |
| `ConstPiDisjNil` | 2 | 400 | no | **no** |
| `ConstSortDisjNil` | 2 | 400 | no | **no** |
| `rigidSortPiDisj_of_nil` | 5 | 3313 | no | **no** |
| `rigidConstPiDisj_of_nil` | 5 | 3316 | no | **no** |
| `rigidConstSortDisj_of_nil` | 5 | 3316 | no | **no** |
| `rigidSortPiDisj_iff_nil` | 1 | 3392 | no | **no** |
| `rigidConstPiDisj_iff_nil` | 1 | 3395 | no | **no** |
| `rigidConstSortDisj_iff_nil` | 1 | 3395 | no | **no** |
| `rigidShapeUniqNS_of_nilFamily` | 9 | 3578 | no | **no** |
| `nil_endpoints_typeable` | 1 | 582 | no | **no** |
| `nil_is_an_instance` | 6 | 38 | no | **no** |

`lean_minimal_hypotheses` on `rigidSortPiDisj_of_nil`: **both** explicit binders (`hfresh`, `H`)
are load-bearing.  So the reduction is not free in either input.

For contrast, the same instrument on the holes: `WF.rigidShapeUniqNS` cone 630, own value a hole;
`IsDefEqU.forallE_inv_stratified` cone 48, own value a hole; `IsDefEqU.forallE_inv` cone 3574,
holes `[forallE_inv_stratified, rigidShapeUniqNS]`; `WF.sortUniq'` cone 3441, hole
`[forallE_inv_stratified]`; `WF.proofTransport` cone 3445, hole `[forallE_inv_stratified]`.
`RigidShapeUniqNS`, `PiInv`, `ConvStep2`, `RigidSortPiDisj`, `RigidConstAppInv`,
`RigidConstPiDisj`, `RigidConstSortDisj`, `rigidShapeUniqNS_iff_family` (cone 3500) and
`rigidShapeUniqNS_of_family_convStep2` (cone 2397) are all hole-free — they are `Prop`s and
implications, so the open content is entirely in the two `sorry`s.

## §3 Why the two **positive** conjuncts do not move — and it is a named node

`PiInv` and `RigidConstAppInv` conclude with a conversion *in `Γ`*.  Forward transport delivers it
in `Γ'` over `env'`; pulling it back needs

1. **anti-substitution** — the tree's inversion of a context operation is
   `UniqueTyping.IsDefEqU.weakN_iff`, itself one of the thirteen holes (its own comment prices it
   at 296 users, and `docs/handoff-confluence.md:295` re-measured a related figure to 312 —
   another decayed count); and
2. **axiom conservativity** — `ShapeIndep.lean`'s module docstring already names this node, for
   the sibling reason that `¬ IsProof` transports backwards, not forwards.  In the tree it is
   `VEnv.AxiomConservativityWF` (`Theory/Typing/ConstVar.lean`, cone 362) and
   `VEnv.AxiomConservativity` (`Theory/Typing/StrengthenAxiom.lean`, cone 362); both are `Prop`s
   with **no unconditional inhabitant** — `exists.lean` reports them hole-free only because a
   `def` has no proof term, which says nothing about satisfiability.

`RigidConstAppInv` is blocked twice: its `¬ env.IsProof U Γ ((.const c ls).mkApp as)` *hypothesis*
is negative in the wrong position and also transports backwards.

So the polarity split in `InjSortPiModel.lean`'s table (positive conjuncts semantically dead,
negative ones reachable) and the context-freeness split found here **coincide**, and both are
explained by the same thing: the only two tools the tree has for moving a judgement between
contexts and environments run forward, and a positive conjunct needs them to run backward.
**[analysis for the coincidence; machine-checked for the three forward reductions]**

## §4 The payoff for the semantic route, and its exact size

`InjSortPiModel.lean` item 4 is the sharpest known limit on *every* semantic route into this
corner: `SetModel.sound`'s conclusion is quantified over `ρ ∈ interpCtx M L Γ`, and
`interpCtx_vFalse` shows that set is **empty** for `Γ = [∀ p : Prop, p]` in every model the tree
has, on both branches of the proof split — hence `not_sortPiEqSupply` and
`sortInvSupply_vacuous`.  At `Γ = []` the obligation is discharged by that file's own
`empty_ctx_has_valuation`.

Composing: `rigidSortPiDisj_iff_nil` says the whole of `RigidSortPiDisj` is its `Γ = []`
instance (over `VEnv.WF` environments), so **item 4's blindness does not apply to it**, and the
model's residual for that conjunct drops to `SetModel.sound`'s deferred inputs
(`hle`, `henv`, `hS`, `hC : CoherentOn`, `hR`, `hRd`) plus the already-proved
`interp_sort_ne_interp_forallE`.

**Not built here, deliberately**: composing it in Lean would re-import the `PropSplit`/`ModelData`
layer into `Theory/Typing`, and the two halves are hole-free in their own files, so the
composition adds no assurance.  Marked **[analysis]**.  The two other negative conjuncts get the
same context elimination but no semantic payoff: `InjSortPiModel.lean` item 3 shows they are dead
for an unrelated reason (`CoherentOn.const_type` constrains `M.cnst c us` by membership only,
refuted by `SetModel/CoherentConstShape.lean`).

## §5 Is hole B true?  Two refutation attempts, both closed by an existing control

I looked for a counterexample first, on the grounds that this tree has produced machine-checked
refutations of its published reference.  **I did not find one, and the reason is structural
enough to record so nobody repeats it.**

**Attempt 1 — differing spine arity.**  `Compat`'s `app`/`app` entry concludes
`List.Forall₂ (env.IsDefEqU U Γ) as as'`, which forces `as.length = as'.length`.  Break it and hole
B is false.  The natural construction: a declared `D : Sort 1` with a δ-rule `D ≡ D → D` makes a
constant `c : D` inhabit `D → D` as well, so `c` and `c c` both inhabit `D` at the same type.  But
*inhabiting a common type is not being convertible*.  With `RuleFreeHead c` there is no rule whose
left-hand side is headed by `c`; joining `c` to `c c` through a hub constant `f` needs **two** rules
on head `f`, and `DeltaUnique.WF.defEqHeadsUnique` forbids that at any `VEnv.WF` environment.  That
is precisely the mechanism of `RigidConstPrice.not_wf_rcSortEnv` / `not_wf_rcPiEnv` /
`not_wf_rcLvlEnv`.  **Closed.**

**Attempt 2 — level-list mismatch.**  `Forall₂ (· ≈ ·) ls ls'` fails only if
`(const c ls).mkApp as ≡ (const c ls').mkApp as'` is derivable with `ls ≉ ls'`.  The three
constructors that could deliver it are `constDF` (requires `ls ≈ ls'` pointwise), `proofIrrel`
(excluded by the `¬ IsProof` premise — and that exclusion is regression-tested as
`ConstInvWitness.lean`'s `w2`) and `extra` (excluded by `RuleFreeHead` — `w1`).  A hub route hits
`defEqHeadsUnique` again; `RigidConstPrice.not_rigidConstAppInvNP_rcLvlEnv` refutes the
`¬ IsProof`-free variant at a **non-`WF`** environment, with `not_wf_rcLvlEnv` as the control
recording that it does not transfer.  **Closed.**

So: **hole B is very likely true**, and the tree already carries the equivalences that a successor
would otherwise re-derive — `RigidNodeCircle.rigidShapeUniqNS_iff_family` (five conjuncts),
`RigidConstPrice.constFamily_iff_rigidShapeUniqNS` (the three constant ones jointly),
`SortPiDisjPrice.sortPiDisjUC_iff_rigidShapeUniqNS`, `Injectivity.rigidPiUniq_iff_piInv` (the
`pi`/`pi` entry **is** `PiInv`), and now this round's three context-elimination `↔`s.

## §6 Vacuity in the other direction (brief (d)): measured, and the answer is NO

The question was whether hole B is only ever *used* at instances where it is trivially available.
Measured at all **ten** instantiation sites (2026-09-03 16:12 UTC):

| site | entry instantiated |
|---|---|
| `Injectivity.lean:1215` (`forallE_inv`) | `pi`/`pi` |
| `Injectivity.lean:1265, 1268` (`sort_forallE_inv`) | `sort`/`pi`, `pi`/`sort` |
| `Injectivity.lean:1336` (`const_app_inv`) | `app`/`app` |
| `Injectivity.lean:1392, 1395` (`const_forallE_inv`) | `app`/`pi`, `pi`/`app` |
| `Injectivity.lean:1456, 1459` (`const_sort_inv`) | `app`/`sort`, `sort`/`app` |
| `ShapeIndep.lean:102, 364` | generic (all) |

All eight surviving entries are consumed; modulo the `symm` pairing that is all five conjuncts.  So
**no entry is dead and the conjunction cannot be trimmed** — `rigidShapeUniqNS_iff_family` being an
`↔` already says as much, and the site table says it is not an artefact of the packaging either.

There *is* a weaker true statement in the neighbourhood, and it is worth stating because it is the
honest version of "the proofs are circular": each of those `trans` cases appeals to hole B **at
exactly the entry the surrounding theorem is proving**, and each surrounding theorem is (∀-closed)
that entry — e.g. `IsDefEqU.const_sort_inv` *is* `RigidConstSortDisj`.  So the five inversion
proofs in `Injectivity.lean` contribute shape bookkeeping and nothing else, which
`Injectivity.lean`'s own section docstring states ("the ten closing cases are *shape* bookkeeping,
and the eleventh carries all of the content").  This round's contribution to that picture is that
three of the five entries lose their context.

**One route that looks like an escape and is not.**  `Verify/Typing/NoConfGuard.lean` §6.1
(`rigidConstAppInv_of_wf`, `rigidConstPiDisj_of_wf`, `rigidConstSortDisj_of_wf`) proves all three
constant conjuncts at every `VEnv.WF` environment.  Re-measured 2026-09-03 16:08 UTC: each has cone
≈ 7 480 and **holes `[weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, descend]`** — hole B
among them, so the route closes the conjuncts through their own target.  That file says so itself;
the measurement confirms it rather than contradicting it.  (`patWF_of_wf`: cone 4 062, holes
`[forallE_inv_stratified, rigidShapeUniqNS]`.  `PatWF` and `paramsOfWF` are themselves hole-free.)

## §7 Hole A (line 268), triaged

* **What it needs.**  Level alignment between a conversion's level and a `HasTypeStratified`
  derivation's level at a fixed index.  `Injectivity.lean`'s own docstring for it is accurate and
  its two bullets (the `forallEDF` and `symm` failures) are analysis, not machine-checked
  impossibility.
* **Is it true?**  No refutation exists or is suggested anywhere in the tree, and
  `Injectivity.piInvStratApp_fires` machine-checks that the narrowed form is non-vacuous at a
  non-degenerate witness (two *syntactically different* domains, codomains in different contexts,
  `imax 0 0 ≈ 0` without equality), over **every** environment.  `ForallInvPrice.hyp_inhabited_iff`
  gives the strongest inhabitation statement available for a hypothesis equivalent to an open
  target.  Treat it as true.
* **Is it load-bearing?**  Yes, but through a *single* instance.  Two direct consumers (§1.3);
  `UniqueTyping.lean:44` discards the first conjunct and passes one index for both premises, so the
  live obligation is `PiInvStratApp`, and `Injectivity.sortUniq_iff_piInvStratApp` makes that
  **equivalent to `VEnv.SortUniq`** given `PiInv` and `VEnv.WF`.  `InjChainStep.lean`'s
  `sortUniq_iff_convStep2_sortInv` splits it further into `ConvStep2 ∧ SortInv` over `PiInv`.
* **Shared node.**  `ConvStep2` appears in the price of *both* holes
  (`InjSpineTransport.rigidShapeUniqNS_of_family_convStep2`), and is the only thing that does.  It
  therefore remains the single highest-leverage target in this corner, and this round did not touch
  it.
* **Nothing in this round narrows hole A.**  Its statement quantifies over a context and its
  conclusion is positive on both conjuncts, so §3's obstruction applies to it in full.

## §8 Edits I would propose to `Injectivity.lean` (stated, not made — the file is not mine)

**None are required.**  Neither hole is closed, so the `sorry` on line 1046 and the one on line 268
must stay.  One optional, purely documentary edit:

* In the docstring of `WF.rigidShapeUniqNS` (`Injectivity.lean:1039–1045`), immediately before the
  closing `-/`, insert:

      `Theory/Typing/InjCorner.lean` removes the *context* from three of the five conjuncts of
      `RigidNodeCircle.rigidShapeUniqNS_iff_family` — `RigidSortPiDisj`, `RigidConstPiDisj`,
      `RigidConstSortDisj` are each equivalent, over the family of `VEnv.WF` environments, to
      their `Γ = []` restriction (`rigidSortPiDisj_iff_nil` and siblings, hole-free).  The two
      *positive* conjuncts provably do not move by that route: it needs `IsDefEqU.weakN_iff` and
      axiom conservativity.

  Zero semantic effect; skip it if the human prefers no churn in a file this widely consumed.

## §9 What I could not do, with the reason

* **Did not close hole B.**  Its residual after this round is
  `PiInv ∧ RigidConstAppInv ∧ ConvStep2` (context-carrying) plus three context-free disjointness
  facts.  Nothing in the tree supplies any of the first three without passing through hole A or
  hole B; I re-measured the one candidate (`NoConfGuard` §6.1) and it is circular (§6).
* **Did not close hole A.**  Untouched by design: the brief's priority was hole B, and hole A's
  live instance is already priced to `ConvStep2 ∧ SortInv`.
* **Did not build the semantic composition of §4.**  It would import `PropSplit`/`ModelData` into
  `Theory/Typing`; both halves are hole-free in their own files.
* **Did not measure forward (transitive) user counts to replace the decayed prose figures.**  Two
  attempts: a per-declaration cone scan over the whole built population (O(n·|cone|), killed after
  ~25 min) and a single-pass reverse-dependency BFS (`/tmp/rev2.lean`, adapted from
  `scripts/exists.lean`'s population walker — worth re-creating, it is the right shape), which did
  not get past `importModules` within the budget while another stream was building the tree.  The
  **reference** counts in §1.3 are exact and are the ones to use; the prose figures listed there
  should be treated as unverified until someone lands a reverse-BFS instrument in `scripts/`.  Note also
  that the tree was being **built concurrently by another stream** during this session
  (`Verify/Inductive/FlipConstruct.olean` appeared mid-run at 18:12 local), so any population
  count taken here is a snapshot of a moving tree.
* **No divergence from the C++ kernel and no C++ kernel bug found** in this round; nothing for
  `divergences.md` or `bugs-found.md`.
