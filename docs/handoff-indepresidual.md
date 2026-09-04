# handoff: `Lean4Lean.VIndRecArg.exists_indep` — the pure-confluence residual

Owner file: `Lean4Lean/Theory/Inductive/IndepResidual.lean` (new, mine).
This doc: `docs/handoff-indepresidual.md` (new, mine).

## Priors (written BEFORE any measurement this round)

1. **The residual is TRUE but not provable without confluence.** The briefing says
   everything reduces to `VEnv.RigidConstPiDisj` / `RigidConstSortDisj`, both FALSE at
   `Ordered`, but rescued at *staged* environments by
   `RecArgIndepClose.defeq_noBlock_of_staged`. Prior: 65% the statement is true,
   30% I find a genuine counterexample, 5% it is independent of what is stated.
2. **`VEnv.WF` will turn out to be needed after all** — 40%. The briefing hopes not.
   My prior is that "no rule mentions the block" is not by itself enough: confluence
   of the *ambient* rules still has to be invoked to rule out a defeq chain that
   detours through unrelated constants and comes back. That detour argument needs
   either a real Church–Rosser lemma for `VDefEq`/`Ordered`, or `WF`.
3. **The one candidate counterexample will NOT lift to a refutation** — 70%. The
   briefing already flags it negates the clause at a single `r`; an existential over
   `r` is free to pick another. Prior: to refute you need a *uniform* obstruction,
   i.e. a block where EVERY candidate residual fails, which means a family, not a point.
4. **(c) will find no witness where a binder genuinely must move** — 60%. If the real
   nested block `ntreeAux` has empty binder lists on all recursive fields, then a
   moving-binder witness has to be hand-built and will be artificial; the honest answer
   may be "none exists in this tree".
5. **The consuming module is `Lean4Lean/Theory/Inductive/Decl.lean`** and nothing else
   (1 direct / 1 transitive user, self-faithfulness). So even a full close buys 1 hole,
   not a cone. Value here is mostly *epistemic* (is it true?) not structural.
6. **Cone estimate for my new file: small, < 50**, because it will import only what
   `Decl.lean` already needs plus `RecArgIndepClose`. I predict `exists.lean` reports
   the target as WATCHED IN CONE.
7. Prior that this is a **seventh/eighth already-done assignment**: 25%. `shape.lean`
   on helpers first.

## Measurements (appended as made)

### M1 — baseline, 2026-09-04

Whole-tree `lake build`: **green, 1644 jobs**, before I wrote a line.

`scripts/users.lean`, population **458 built modules / 27219 non-internal declarations**:

| name | direct | transitive |
|---|---|---|
| `Lean4Lean.VIndRecArg.exists_indep` | **1** | **1** (module `Lean4Lean.Theory.Inductive.RecArgIndep`) |
| `Lean4Lean.VIndRecArg.BindersIndep` | 43 | 1868 (232 modules) |
| `Lean4Lean.VEnv.RigidConstPiDisj` | 32 | 40 |
| `Lean4Lean.VEnv.RigidConstSortDisj` | 33 | 41 |
| `Lean4Lean.RecArgIndepClose.indepGoal_iff_indepUpgrade` | 0 | 0 |
| `Lean4Lean.RecArgIndepClose.defeq_noBlock_of_staged` | 0 | 0 |

**Prior 1/5 confirmed on the inertness figure.**  The 1-direct/1-transitive claim in
`docs/handoff-recargindepclose.md` reproduces at a *larger* population (431 → 458 modules), so it
is not an artefact of the earlier population.  The single user is the faithfulness check.

New fact the earlier round did not record: `RigidConstPiDisj`/`RigidConstSortDisj` are **40/41
transitive-user** predicates, i.e. proving either *in general* is worth far more than this hole.
`RecArgIndepClose`'s own two headline lemmas have **0 users** — they are reductions nothing cites.

### M2 — the attack I chose, and why (before writing Lean)

The residual is: at a staged `env`, is a block spine `I_j p π` convertible to a Π or a sort?
Everything in the tree that could answer it is a confluence statement, and confluence *as the tree
states it* is refuted (`Lean4Lean.KCanonical.not_crStatement_of_kstep`; commit 6bd173f, another
stream, refutes the confluence **method** as well).  So a direct proof is out of budget.

What is *not* out of budget, and is new: **`Theory/Typing/ConstSubst.lean` can delete the block.**
It has `Lean4Lean.VEnv.IsDefEqU.substC` — transport of a judgement along a constant substitution
`σ : Name → Option VExpr`, the only transport in `Theory/` that can *remove* a constant.  Its four
`Lean4Lean.CSubst.WF` obligations are, at a staged environment, exactly the two facts
`RecArgIndepClose` already proved plus two trivia:

* `const` ← `Lean4Lean.RecArgIndepClose.env₀_const_noBlock_of_staged`
* `defeq` ← `Lean4Lean.RecArgIndepClose.defeq_noBlock_of_staged`
* `closed`, `val` ← chosen by whoever picks the replacement values.

So the *plan*: prove `CSubst.WF σ env env₁ U` for any σ whose domain is the block, and read off

1. **conservativity**: an `env`-conversion between block-free terms is an `env₁`-conversion;
2. **value-immateriality**: if a block-free `A` is convertible to `I_j p π` then `A` is convertible
   to `t p π` for **every** closed `t` of the arity — so the block spine behaves exactly like a
   universally quantified variable, and the residual becomes a statement with no inductive
   vocabulary in it at all.

Predicted outcome, recorded before doing it: this does **not** close the hole (the target statement
stays open) but it replaces two open predicates by one, and moves the open predicate off the block.

### M3 — `blockSubst_WF` proved (2026-09-04)

`Lean4Lean.IndepResidual.blockSubst_WF` compiles.  Statement: for `hstage : env₀.addIndTypes D =
some env`, `Ordered env₀`, `Ordered env₁`, `env₀ ≤ env₁`, a substitution `σ` whose domain is
exactly `D.blockNames`, closed values, and `val` from plain well-typedness —
`σ.WF env env₁ U`.  Both non-trivial fields come from `RecArgIndepClose`:
`const` ← `env₀_const_noBlock_of_staged`, `defeq` ← `defeq_noBlock_of_staged`; the builder is
`Lean4Lean.CSubst.WF_of_hasType` and the syntactic bridge is
`Lean4Lean.VExpr.NoConsts.noCSubst` (already in the tree, `Theory/Inductive/RestoreBridge.lean` —
**not** re-proved here; the `shape.lean` run on my helper shapes is what found it).

So `defeq_noBlock_of_staged` was worth more than the round that proved it claimed: it is not just
"the hub refutation route is closed", it is one of the two side conditions that let the block be
**deleted** from any judgement.

### M4 — the file, measured (2026-09-04)

`Lean4Lean/Theory/Inductive/IndepResidual.lean`, whole-tree `lake build` **green, 1646 jobs**.
`scripts/exists.lean` (population **460 built modules**), every row
`own value is a hole: false; cone reaches sorryAx: false` and
`watched declarations in cone: none of 6`:

| fully-qualified name | arity | cone |
|---|---|---|
| `Lean4Lean.IndepResidual.blockSubst_WF` | 14 | 2480 |
| `Lean4Lean.IndepResidual.onCtx_substC` | 7 | 832 |
| `Lean4Lean.IndepResidual.defeqU_noBlock_transport` | 14 | 851 |
| `Lean4Lean.IndepResidual.onCtx_noBlock_transport` | 10 | 859 |
| `Lean4Lean.IndepResidual.blockSpine_defeq_transport` | 18 | 858 |
| `Lean4Lean.IndepResidual.not_defeq_blockSpine_of` | 18 | 859 |
| `Lean4Lean.IndepResidual.blockSpine_not_defeq_forallE_of_sortVal` | 23 | 868 |
| `Lean4Lean.IndepResidual.blockSpine_not_defeq_sort_of_piVal` | 21 | 865 |
| `Lean4Lean.IndepResidual.isDefEqType_substC` | 9 | 824 |
| `Lean4Lean.IndepResidual.blockSpineType_defeq_transport` | 18 | 858 |
| `Lean4Lean.IndepResidual.noBlockType_not_defeqType_blockSpine` | 31 | 2183 |
| `Lean4Lean.IndepResidual.Rai.raiσ_WF` | 1 | 2509 |
| `Lean4Lean.IndepResidual.Rai.raiσ'_WF` | 1 | 2511 |
| `Lean4Lean.IndepResidual.Rai.raiPi_hasType` | 0 | 1490 |
| `Lean4Lean.IndepResidual.Rai.rai_blockSpine_not_defeq_forallE` | 8 | 2551 |
| `Lean4Lean.IndepResidual.Rai.rai_blockSpine_not_defeq_sort` | 5 | 2552 |
| `Lean4Lean.IndepResidual.Rai.rai_noBlockType_not_defeqType_blockSpine` | 7 | 2571 |

`#print axioms` on **all 33** declarations of the file (helpers included): 32 ×
`[propext, Quot.sound]`, 1 × `does not depend on any axioms` (`Rai.raiD_blockNames`).  No
`sorryAx`, no `Classical.choice`.

### M5 — the status change, which is the real payoff

`scripts/shape.lean` on `Lean4Lean.VEnv.RigidSortPiDisj` (population 460) turned up
`Theory/Typing/InjSortPiModel.lean`, whose verdict table reads:

* `RigidConstPiDisj` — **dead** at the model layer (`VEnv.not_constNotUniv`,
  `SetModel/CoherentConstShape.lean`'s `not_coherentConstNotPi`): `ModelData.cnst` is a free field,
  so a constant may denote anything and `interp` cannot separate a spine from a Π.
* `RigidConstSortDisj` — **dead**, same reason (`not_coherentConstNotUniv`).
* `RigidSortPiDisj` — semantic residual **PROVED** (`InjSortPi.interp_sort_ne_interp_forallE`);
  the separating element is `{•}`.

So the reduction is not only 2 → 1.  It moves the hole's residual off **both** of the two
conjuncts the model layer has measured as *unreachable* and onto the **one** conjunct where the
model layer already supplies the fact.  That is a change of status, not of count, and neither
`Decl.lean` nor `RecArgIndepClose.lean` records it.

And the terminal target is startlingly small: `Theory/Typing/InjCorner.lean`'s
`VEnv.rigidSortPiDisj_iff_nil` shows the family form of `RigidSortPiDisj` is exactly its
empty-context restriction, and `VEnv.nil_endpoints_typeable` names its one open instance as
`.sort .zero` vs `.forallE (.sort .zero) (.sort .zero)` — `Prop ≢ (Prop → Prop)`.  **Those are the
two replacement values §3 picks**, arrived at from the other end (they are the sort-shaped and
Π-shaped inhabitants of `Sort 1`), which is a coincidence worth recording because it means the two
routes bottom out at literally the same pair of terms.

---

## (a) Did I close the residual?  **No — I relocated it, and the relocation changes its status.**

Not closed, and I do not think a round should be spent trying to close it head-on at the
`Ordered`/confluence level: commit `6bd173f` (another stream, this session) refutes the confluence
*method*, and `Lean4Lean.KCanonical.not_crStatement_of_kstep` refutes confluence as the tree states
it.  What I did instead:

**`RecArgIndepClose` §2's two residual predicates collapse to one, and the one is the smallest
member of its family.**  `Lean4Lean.IndepResidual.blockSpine_not_defeq_forallE_of_sortVal_ctx`
(cone 874) and `Lean4Lean.IndepResidual.blockSpine_not_defeq_sort_of_piVal_ctx` (cone 871) derive
block-spine/Π and block-spine/sort disjointness at a staged environment from
`Lean4Lean.VEnv.RigidSortPiDisj` at the environment the block substitutes into — the conjunct with
no constant in it.  The mechanism is `Lean4Lean.IndepResidual.blockSubst_WF`: the block is
**deletable** by a constant substitution, so a block spine is convertible to *whatever* closed
inhabitant of its arity one likes; pick a sort-shaped one for the Π side and a Π-shaped one for the
sort side.

**Fired at a real staged environment, the target is the empty environment.**
`Lean4Lean.IndepResidual.Rai.rai_blockSpine_not_defeq_forallE` (cone 2551) and
`Rai.rai_blockSpine_not_defeq_sort` (cone 2552): at `RecArgIndep.raiEnv0 =
VEnv.empty.addIndTypes raiD`, both halves of the residual are `VEnv.RigidSortPiDisj ∅` — no
constants, no δ-rules.

### The exact edit to `Decl.lean` — written out, **not made**

`Decl.lean` is not mine and I did not touch it.  The edit I would propose is a **docstring
addition only; the statement, the hypotheses, the conclusion and the `sorry` all stay.**  In the
paragraph beginning "**Why it is a `sorry` and not a proof.**", after the sentence ending
"So the residual is **pure confluence**, and plausibly does not need `VEnv.WF` at all.", insert:

> `Theory/Inductive/IndepResidual.lean` narrows it once more, and changes its status.  At a staged
> environment the block is *deletable*: `IndepResidual.blockSubst_WF` builds a `CSubst.WF` from
> `RecArgIndepClose`'s own two theorems, so `VEnv.IsDefEqU.substC` carries any judgement into an
> environment that never heard of the block, and a block spine is therefore convertible to
> **every** closed inhabitant of its arity.  Substituting a sort-shaped inhabitant turns
> `RigidConstPiDisj` for the block into `VEnv.RigidSortPiDisj`, and a Π-shaped one turns
> `RigidConstSortDisj` into the same predicate
> (`IndepResidual.blockSpine_not_defeq_forallE_of_sortVal_ctx`,
> `blockSpine_not_defeq_sort_of_piVal_ctx`).  That matters beyond the count:
> `Theory/Typing/InjSortPiModel.lean` grades `RigidConstPiDisj` and `RigidConstSortDisj` as
> **dead** at the model layer (`ModelData.cnst` is a free field —
> `InjSortPi.not_constNotUniv`, `SetModel.not_coherentConstNotPi`,
> `SetModel.not_coherentConstNotUniv`), while `RigidSortPiDisj`'s semantic residual is a
> **theorem** (`InjSortPi.interp_sort_ne_interp_forallE`).  At the one staged environment where the
> reduction has been fired end to end, the target is `VEnv.RigidSortPiDisj ∅` — an environment with
> no constants and no δ-rules (`IndepResidual.Rai.rai_blockSpine_not_defeq_forallE`,
> `rai_blockSpine_not_defeq_sort`).

Nothing else changes.  I did not make this edit; the orchestrator should confirm it with the human.

## (b) Is the residual true?  **Not refuted, and I can say why no refutation of this shape exists.**

* **The earlier round's reading of the one candidate is correct.**  Re-measured:
  `Lean4Lean.RecArgIndep.not_bindersIndep_raiRec1` (cone 714, hole-free) negates
  `BindersIndep` at **one** `r`, and `exists_indep`'s conclusion is an existential free to pick
  another.  It is not a refutation and cannot be made into one without showing *no* `r'` works,
  which at `raiEnv` is itself a rigidity statement.
* **A genuine counterexample would have to manufacture a derivation, and the substitution argument
  shows it cannot be manufactured out of environment pathology.**  The tempting route is: make
  `env₀` conversion-degenerate (a hub identifying anything that already shares a type — which
  `VEnv.Ordered` permits, see `VEnv.ordered_sortPiEnv`) so that a *block-free* type becomes
  convertible to the block spine, and then the binder `P x` exists.  That route is closed
  structurally: `blockSubst_WF` says any such conversion transports to `env₁` with the block
  replaced by an arbitrary value, i.e. it is a **necessary** condition on the conversion.  Failure
  of the necessary condition refutes the conversion; *satisfaction* of it does not produce one.
  And nothing can produce one: no rule of a staged environment mentions the block
  (`defeq_noBlock_of_staged`), and the block constants are added last, so no rule is ever added
  afterwards either.  So a refutation would have to come from β, η or proof irrelevance alone
  generating a block constant on one side of a conversion whose other side is block-free — which is
  the negation of the very statement, not an independent route to it.
* **What is machine-checked here is the negative half only**: the *target* of my reduction is false
  at `Ordered` environments (`Lean4Lean.IndepResidual.not_rigidSortPiDisj_rogueSortPiEnv`,
  cone 2350, hole-free), so no successor should read the collapse as having removed the
  `Ordered`-vs-`VEnv.WF` gap.  It removes it only at `∅`, and there by construction.
* **Verdict**: still `[analysis, not proved]` both ways, exactly as the previous round graded it —
  but the open statement is now one predicate at one environment instead of two predicates at a
  staged one, and the previous round's "pure confluence" is now "sort/Π disjointness, at `∅`".

## (c) Instantiation — and the surprising fact, preserved

**No witness in this tree needs a binder to move, and nesting is *why*, not despite.**  Re-measured
rather than quoted:

| fact | name | cone |
|---|---|---|
| `ntreeAux`'s recursive field has `ξ = []` | `Lean4Lean.RecArgIndepClose.NTreeHyps.nl_binders_nil` | 16 |
| `W'.mk` has `ξ ≠ []` and an earlier recursive field, and still skips | `Lean4Lean.InductiveDeclExamples.wMk_BindersIndep` | 1533 |
| the one clause negation, at one `r` | `Lean4Lean.RecArgIndep.not_bindersIndep_raiRec1` | 714 |
| what makes that reachable: a constant whose *type* mentions the block | `Lean4Lean.RecArgIndep.raiCiP_type_hasBlock` | 375 |
| and no `Ordered` environment stages `raiD` into it | `Lean4Lean.RecArgIndep.rai_not_staged` | 936 |

So `exists_indep_of_binders_nil` closes the real nested block, and `W'.mk`'s non-empty telescope is
closed because its binder is the block's own **parameter**, which skips.  The nesting axis makes the
hole *weaker*: `ntreeAux`'s recursive fields carry no binders at all, so the very construction that
motivates the whole nested-inductive effort cannot exhibit the residual case.

**A witness where a binder genuinely must move does not exist in this tree, and I can now say what
it would take.**  The tree's only binder that mentions an earlier recursive field is
`RecArgIndep.raiB = raiP (bvar 0)`, and its head constant is *absent from the staged environment*:
`Lean4Lean.IndepResidual.Rai.raiEnv0_P_none` (cone 3511) — `raiEnv0.constants raiP = none`.  So the
binder is not even in the staged environment's vocabulary, which is the blunt form of
`rai_not_staged`.  To build a moving-binder witness at a *staged* environment one would have to
supply a block-free type convertible to the block spine, and
`Rai.rai_noBlockType_not_defeqType_blockSpine` (cone 2571) shows that at `raiD` this is impossible
over `VEnv.SortUniq ∅` and `VEnv.RigidSortPiDisj ∅`.  **A moving-binder witness at a staged
environment is therefore not merely absent: it is a counterexample to the reduction target.**

### The one gap inside my own method, stated rather than papered over

`noBlockType_not_defeqType_blockSpine` — the two-substitution comparison, which is what handles the
`.lam`-domain route where the block-free side is an *arbitrary* type — needs a **block-free
context**, because `σ` and `σ'` send the same context to two *different* contexts and
`RecArgIndep.isDefEqType_trans_of_sortUniq` needs one.  Where the hole lives the context is not
block-free (an earlier recursive field's stored type **is** a block spine), so that lemma covers the
`.lam` route only when every earlier field is non-recursive — which is
`RecArgIndep.bindersIndep_of_pre_norec`'s regime, already closed.  The Π and sort routes have no
such defect (§2a is stated with the context travelling along the substitution).  **This is the next
piece of work on this hole**, and it is smaller than confluence: it needs a transport that keeps one
context, or a context conversion between the two images.

### A correction to a file I do not own (not edited)

`Theory/Typing/ShapeVar.lean`:459 says the route through `VEnv.HasType.bvar_inv` "goes via
`.strong` and **carries `sorryAx`**".  Measured today (`scripts/exists.lean`, population 461):
`Lean4Lean.VEnv.HasType.bvar_inv`, module `Lean4Lean.Theory.Typing.Strong`, arity 8, cone 2333,
`own value is a hole: false; cone reaches sorryAx: false`.  The docstring is **stale**.  This
matters for this hole specifically: `RecArgIndepClose` §2's enumeration steps of the form "then
`x`'s type must convert to a Π" are `HasType` inversions on a `bvar`, and they are available
hole-free — so formalising the enumeration is not blocked on a tainted lemma, as a reader of that
docstring would conclude.  I did not edit `ShapeVar.lean`.

## Round-close

* whole-tree `lake build`: **green, 1648 jobs** (final re-run; other streams landed modules during
  the round — the population grew 458 → 465 while I worked, which is why every figure above carries
  the population it was taken at)
* census (`scripts/sorry-census-all.lean --run`), final re-run: on disk 489; default-target
  population **465**; Experimental out of population 24; **BUILT 465, NOT BUILT 0**; **HOLES 13**
  (pass A 13, pass B 0)
* guards, all three from the build log:
  * `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`
  * `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
  * `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`
* warnings from `Lean4Lean/Theory/Inductive/IndepResidual.lean`: **0**
* in-repo "not explicitly referenced" warnings: **63 across 23 files**, none of them mine — drift,
  reported as the brief asks (the brief's prior was ~66 across 24; it has drifted *down* by 3/1)
* `python3 scripts/layer-check.py`: **exit 0**; hard rule ok (66 `Theory/SetModel/` modules, none
  reaches `Verify/`); soft report unchanged at four files
  (`CommutationLemmas`, `EtaGuardLand`, `NoConfRepair`, `StructEtaPrice`), and my file is not among
  them
* consuming module, named up front as required, and **the honest version of the answer**:
  `scripts/can-cite.py Lean4Lean.Theory.Inductive.Decl …` returns **NO** for every declaration in my
  file — `Decl.lean`'s closure is 15 modules and mine sits downstream of it, and so does
  `RecArgIndepClose` (closure 109, also NO).  So the *content* cannot discharge the `sorry` in
  place; the proposed `Decl.lean` edit is a **docstring** edit, and the realistic consuming route is
  a **fourth drop-in** beside `RecArgIndep.exists_indep_of_pre_norec` / `_of_binders_nil` /
  `_of_i_zero` — the hole's ten hypotheses plus `VEnv.RigidSortPiDisj` at the substituted
  environment — which needs `RecArgIndepClose` §2's enumeration *formalised*, the piece neither
  round has written.  Today my file has **0 users**, exactly like `RecArgIndepClose`'s two headline
  lemmas (`indepGoal_iff_indepUpgrade`, `defeq_noBlock_of_staged`, both 0/0 in M1), and I am not
  hiding that.  This is the same import-direction wall the previous round hit when it declined
  `RigidShapeUniqNS.constPiDisj`; nothing I did moves it, and this round's value is epistemic —
  *what* the residual is, and whether it is reachable — rather than structural.
