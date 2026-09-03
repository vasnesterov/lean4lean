# `VInductDecl'.WFC` on the nested path: the third route is closed, and it is closed by a *refutation*

Target: `docs/handoff-restrict.md`'s flagged-but-unchecked item —

> `InductR.lean` §4's claim that `WFC` is unavailable on the nested path — if that reading is
> wrong, `WFC` is a third and much shorter route.

**Answer: the reading is right, and the situation is stronger than "unavailable".
`VInductDecl'.WFC env D K` is *refutable* at the nested configuration.** So the third route does
not exist, and had it been taken it would have discharged `VIndRestore.ValAt` — and every other
residual — by `absurd`. Outcome 2 of the brief, with the obstruction named, plus one documentation
correction (outcome 3) that also closes the natural repair.

Everything below is in **`Lean4Lean/Theory/Inductive/WFCRoute.lean`** (new, orphan leaf, 384 lines,
all `sorryAx`-free). No other file was edited.

---

## 1. What was actually there before, and what was not

| Where | What it is |
|---|---|
| `Verify/Environment/InductR.lean` §4 (`:452`, `:465`) | prose: `WFC.ctors` is staged over `addIndTypesC D K`, "an environment in which a companion member's own constructor type is not even well-formed" |
| `Theory/Inductive/NestedHead.lean` `ntreeAux_staging` | three **staging** `rfl`s: `typeConsts` has `_nested.List_1`; `typeConstsC ntreeK` does not; `NTree.node`'s second field type is `.app (.const \`_nested.List_1 [.param 0]) (.bvar 1)` |
| that theorem's docstring | the *assertion* "at that staging the clause is not merely weaker, it is unsatisfiable" |
| anywhere | **no theorem saying so** |

So the tree had the ingredients and an assertion, and the assertion had never been instantiated.
That is exactly the shape the brief warned about — except that this time the prose was **right**.

## 2. The mechanism (§2 of the file)

`VIndCtor.WF` is stated over the environment where the block's type constants are declared, and
`VIndCtor.WF.isType` (`Theory/Inductive/Lemmas.lean`) converts it into a **closed** typing
`e₁.IsType D.uvars [] (C.type D j)`. A closed typing in `e₁` cannot mention a constant `e₁` does
not declare — that is `VEnv.IsDefEq.noCSubst'` (`Theory/Typing/ConstSubst.lean`), a structural
induction over the derivation. But `C.type D j = mkPi (C.params ++ fieldTypes) (C.canonResult D j)`
and `C.canonResult D j = D.tyApp j …`, whose spine head *is*
`.const (D.types.getD j default).name`. Hence:

```
VInductDecl'.not_WFC_of_undeclared        -- e₁.constants T.name = none  →  ¬ D.WFC env K
VInductDecl'.not_WFC_of_fresh_companion   -- T.name ∈ K ∧ env.constants T.name = none → ¬ D.WFC env K
VInductDecl'.not_WFC_of_field             -- the field-telescope form (used for the j = 0 obstruction)
```

Both need `C ∈ T.ctors`. Two supporting lemmas: `VExpr.NoCSubst.mkApp_head` (new; `mkPi_tele`
was already in `Theory/Inductive/NestedTele.lean`) and `VIndCtor.type_mkPi_head`.

**Constraint respected.** `HasArgs.of_mkApp` is not used; neither is `PiInv`, nor
`HasType.app_inv`/`const_inv`, nor any application inversion at all. `noCSubst'` takes the
derivation apart structurally and the context is `[]`, so its `hΓ` premise is `nofun`. This was
the design choice that made the whole thing three lemmas instead of a spine-inversion project.

## 3. Instantiated (§3), twice over, at the block Lean's own kernel runs nested elimination on

At the `NTree`/`List` witness, at the *real* staged environment `env₃ = env₁.addIndTypesC ntreeAux
ntreeK` (the environment `AddInductStagesR`'s first stage produces), with
`env₃.Ordered` supplied by the existing `addConstList_ordered` chain:

* **`ntreeAux_not_WFC`** — obstruction 1: `_nested.List_1.nil`'s stored type ends in
  `_nested.List_1 α`, and `env₃` does not declare `_nested.List_1`. This is §4's stated reason,
  now a theorem.
* **`ntreeAux_not_WFC_node`** — obstruction 2, *independent*: `NTree.node`'s second field type is
  `_nested.List_1 α`, and `NTree` is a member **the user wrote** (`j = 0`, `∉ ntreeK`). This is
  `ntreeAux_staging`'s stated reason, now a theorem.
* **`ntreeAux_not_WFC'`** — the refutation with **no hypotheses left**, via
  `ntreeAux_declared_exists`.
* **`ntree_WFC_vacuates`** — `∀ P : Prop, ntreeAux.WFC env₁ ntreeK → P`. This is why the result is
  worth a theorem rather than a note: `WFC` is not "true but unproved", it is *false*, so an
  obligation carrying `D.WFC venv K` as a conjunct is **vacuously true** at the witness.
* **`ntreeAux_WFC_flips`** — the collapse test. Same `D`, same `env₁`:
  `WFC env₁ [] ∧ ¬ WFC env₁ ntreeK ∧ WF env₁`. Only the staging of the `ctors` clause changes.
  (Working rule "a hypothesis can be inert": §2's lemmas *are* inert at `K = []` — `T.name ∈ []`
  has no witness — so their content lives entirely at `K ≠ []`, which is where the nested path is.)

## 4. The documentation correction (outcome 3), and the fourth route it closes

§4's reason names *the companion member's own* constructor type. That is true, but it is not the
whole obstruction, and the difference is load-bearing: a reader of §4 alone would conclude that a
`WFC` whose `ctors` clause is restricted to `T.name ∉ K` — check only the members the user wrote,
where the type constant *is* declared — would be satisfiable. **It is not.**

`VInductDecl'.WFCOwnCtors` (§2b) is exactly that weakening, and
**`ntreeAux_not_WFCOwnCtors`** refutes it at the same witness, because on a nested block the
user's own constructor mentions the *auxiliary* member's constant. That is what nesting *is*.

> **Correction for you to apply, if you want it** (I do not edit `InductR.lean`).
> `Verify/Environment/InductR.lean:465` currently reads:
> "… `VInductDecl'.WFC … K`, whose clause is staged over `addIndTypesC D K` — an environment in
> which **a companion member's own constructor type** is not even well-formed."
> The accurate statement is: "… in which **any constructor type mentioning a dropped constant** is
> not well-formed — on the nested path that includes the *user's* own constructors, since a nested
> field's stored type is headed by the auxiliary member's constant. Machine-checked:
> `Theory/Inductive/WFCRoute.lean`'s `ntreeAux_not_WFC` (companion member),
> `ntreeAux_not_WFC_node` (user's member) and `ntreeAux_not_WFCOwnCtors` (the restricted clause is
> false too)."
> Same for `Theory/Inductive/NestedHead.lean`'s `ntreeAux_staging` docstring: its "not merely
> weaker, it is unsatisfiable" is now `ntreeAux_not_WFC_node`, and can cite it.

## 5. Second witness, and a hypothesis proved load-bearing (§6)

*A count is only as meaningful as the population it ranges over*, so §2 was run on the other
family in the tree — `CompanionResolve.lean` Part 8's `fooDecl`/`fooCompDecl`. The result is a
complete characterisation of when `WFC` can hold at a companion member, and it **agrees exactly**
with what was already proved there:

* `fooComp_WFC : fooCompDecl.WFC env₁ [\`Foo]` holds at *arbitrary* `env₁` — and §2 does not
  contradict it, because `fooCompDecl`'s member has `ctors := []` and every lemma above needs
  `C ∈ T.ctors`. Its docstring ("re-staging restores the clause's *domain*; it does not give it
  any *content* at `ctors = []`") is exact.
* `fooDecl_WFC : fooDecl.WFC env₁ [\`Foo]` — whose member *does* have a constructor — is stated
  under `h : VEnv.empty.addInduct' fooDecl = some env₁`, i.e. under `Foo ∈ env₁`.
  **`fooDecl_not_WFC_of_fresh` proves that `h` is load-bearing**: drop it and the statement is
  false, not merely unproved.
* **`fooDecl_WF_and_not_WFC : fooDecl.WF VEnv.empty ∧ ¬ fooDecl.WFC VEnv.empty [\`Foo]`** — the
  flip at a second, fully independent witness, with no hypotheses at all.

**The dividing line is exactly `env.constants T.name`.** With a *fresh* companion name and a
non-empty constructor list, `WFC` is refutable. That is the nested path's configuration by
construction (`mkUniqueName`), and it is `fooDecl_WFC`'s configuration only because `Foo` is
already declared. So §4's parenthetical — "`WFC` exists for the *other* companion shape, a block
re-declaring a type that is already in the environment … the nested path never does that" —
identified the right pivot.

## 6. Why the lead looked short, and why it is not

The strongest pro-`WFC` evidence in the tree is `InductR.lean:184`, not `:452`/`:465`:

```
AddInductStagesR.addIndTypesC : ∃ et, env₁.addIndTypesC D K = some et
```

`WFC.ctors`'s staging premise is supplied **for free by the step itself**, whereas `WF.ctors`'s
premise (`env.addIndTypes D = some et`) is not — which is why `InductStepNested` has to carry
`(∃ et, venv.addIndTypes D = some et)` as a separate conjunct, and why `ctors_nonvacuous` exists
to read it back. That asymmetry is real and it is exactly what made `WFC` look like a shortcut.

**The trap is that the premise is free *because* the predicate is false there.** `WFC`'s other
four fields (`types_ne`, `params`, `types`, `isLE`) are byte-identical to `WF`'s; the re-staged
`ctors` clause is the entire difference, and it is the clause that goes from vacuous (on the
re-declaration companion shape) to *false* (on the fresh-name nested shape).

### Does it shorten the route to `ValAt`? No — and this says something about `ValAt`

`WFC` does not mention `R` at all, so it cannot produce `ValAt`'s judgement
(`e₁.HasType ci.uvars [] (R.tyVal D j) ci.type`) other than by `absurd`. More usefully: the
statement `WFC` was reaching for — *the companion members' constructor constants are well-formed
at the smaller environment* — **already exists and is already proved**, as
`VEnv.ctorConstsCR_wf_of_substC'` / `ntreeAux_ctorConstsCR_wf` (`Theory/Typing/ConstSubstNested.lean`)
— for the **substituted** constants, `ctorConstsCR R K`, whose constants *are* declared in `env₃`.

That is the structural reason `ValAt` is the residual and not an artefact of route choice: at the
smaller environment a companion's constructors can only be well-formed **through the
substitution**, and `WFC` is that same statement with the substitution omitted. Omitting it is
what makes it false. `TrIndDeclN.trCtors` is staged over the same `addIndTypesC D K` and is
satisfiable precisely because it compares against `TrIndCtorR … R …`, the restored form.

**Conclusion: the lead is retired, permanently, and so is its natural repair. `ValAt` remains the
residual and the substitution is not bypassable here.** Nothing in this file touches the flip.

---

## 7. Where you were wrong (highest-value section)

1. **"A cone of 5 means the definition is tiny, which is exactly why a wrong 'unavailable' reading
   would be expensive."** The cone size was a red herring. `WFC` is a `structure` — there is no
   proof term whose cone could tell you anything about *satisfiability*, and hole-freeness of a
   definition is not a property at all in the sense the brief used it. The price of this lead was
   never in the definition; it was in whether the hypothesis set is jointly inhabited at a real
   block, which only the witness could answer.
2. **The three note locations were mis-weighted.** You described `:184` as the one that
   "distinguishes what is staged over `env.addIndTypes D` from what is staged over `WFC … K`" —
   that is `:465`. `:184` is `AddInductStagesR.addIndTypesC`, and it is the *only* pro-`WFC`
   evidence in the tree (§6 above). If you had read it as I did, the lead would have looked
   *stronger*, not weaker — which is the right calibration: it was a good lead that terminates in
   a false predicate, not a bad lead.
3. **The layering worry did not materialise.** You offered `Verify/Inductive/WFCRoute*` in case
   the work needed both `Theory/` and `Verify/`. It needed only `Theory/`: the question reads like
   a `Verify/` question because the notes live there, but the *fact* is entirely about `Theory/`
   objects — `WFC`, `addIndTypesC`, `ntreeAux`, `ntreeK`, `env₃`. `grep -rln "^import
   Lean4Lean.Verify" Lean4Lean/Theory/` is empty.
4. **Outcome ranking.** You ranked "`WFC` is available" above "proved unavailable". The outcome
   actually obtained is *better than outcome 2 as you framed it*: **false** beats **unavailable**,
   because it (a) retires the lead permanently, (b) retires the obvious repair `WFCOwnCtors`,
   (c) turns two pre-existing prose assertions into theorems, and (d) proves an existing
   hypothesis (`fooDecl_WFC`'s `h`) load-bearing. A route that is merely unprovable can be
   revisited; one that is refuted cannot.
5. **Nothing you asserted about the tree was false.** All three named notes say what you quoted,
   `VInductDecl'.WFC` is where you said (arity 3, `Theory/Inductive/CompanionResolve.lean`), and
   `VEnv.WFC` indeed does not exist. This is the first round in this corner where the absence /
   presence claims in the brief all held up.

---

## 8. Verification record

* **`lake build`: 1591 jobs, exit 1.** `Lean4Lean.Theory.Inductive.WFCRoute` builds/replays clean.
  The two failures are **another stream's**, not mine, and pre-date my file:
  `Theory/Inductive/TeleCongr.lean:182` — `Unknown constant
  Lean4Lean.VIndRestore.minorCtorHargs_of_hargs'` — and `Theory/Inductive/HTeleRecB.lean:106`,
  both downstream of an in-flight rename in `Theory/Inductive/RecTyped.lean` (` M` in
  `git status`, owned by the `HAsDrop*`/`RecTyped.lean`/`HargsShared.lean` stream). My file is an
  orphan leaf: `grep -rln WFCRoute --include=*.lean Lean4Lean/` returns only itself, so it cannot
  be implicated in either.
* **`lake env lean --run scripts/sorry-census-all.lean`: 13 holes**; `BUILT: 406`;
  `in population but NOT BUILT: 2` — the two files above. **My file adds no hole.**
* **`#print axioms` on all 16 of my declarations** (§7 of the file, names read off this file's own
  `namespace` lines — `Lean4Lean`, `Lean4Lean.VExpr`, `Lean4Lean.InductiveDeclExamples` — never
  composed from the path): `[propext]`, `[propext, Quot.sound]`, or
  `[propext, Classical.choice, Quot.sound]`. **No `sorryAx` anywhere.** `NoCSubst.mkApp_head`
  depends on no axioms at all. Confirmed independently by `lean_verify` on
  `ntreeAux_not_WFC'`.
* **Guards, unchanged:** `guard 1 ✓ (24 frozen axioms)`, `guard 2 ✓ (whitelist; proof INCOMPLETE —
  sorryAx present)`, `guard 3 ✓ (2/2)`.
* **`lake env lean --run scripts/dup-names.lean`:** "no duplicate Lean4Lean declarations across
  the joined cone."
* **`grep -c "automatically included section variable"`: 3, of which 0 are mine.** Honest caveat:
  the baseline is 18 and I cannot reproduce 18 because the build aborts at another stream's two
  files before the rest of the tree is elaborated. What is measurable is that my file contributes
  **zero** — it emits no warnings of any severity (`lean_diagnostic_messages` at `warning`: empty).
* **Layering:** `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — **empty**.
* **Frozen files** (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read
  for editing, not written, not `touch`ed; absent from `git status`.
* **Other streams' files** (`InductR.lean`, `CompanionResolve.lean`, `Companion.lean`,
  `NestedHead.lean`, `ConstSubstNested.lean`, `NestedTele.lean`, `DeclExamples.lean`,
  `RestrictCompanion.lean`, `Decl.lean`, `Lemmas.lean`): read and imported, **never edited**.
* No state-changing `git`, no `lake update`, nothing sent outside this repo. Not touched: the flip,
  `tryEtaStructCore.WF`, `isDefEqUnitLike.WF`.

### 8a. Measured vs read off

**Measured this session (by the compiler, at a witness):** that `WFC` is false at `ntreeAux`/`ntreeK`
by two independent obstructions; that `WFCOwnCtors` is false there too; that `WFC` holds at
`K = []` for the same block and environment; that `fooDecl_WFC`'s `h` is load-bearing and
`fooDecl.WF VEnv.empty ∧ ¬ fooDecl.WFC VEnv.empty [\`Foo]`; every axiom line above; the census
(13 / 406 / 2); dup-names; the layering grep; that my file emits no warnings; that the two build
failures are in files whose import cones do not contain mine.

**Read off source, not independently re-proved:** the statement of
`AddInductStagesR.addIndTypesC` (`InductR.lean:184`) and hence the §6 claim that `WFC`'s staging
premise is free while `WF`'s is not; that `InductStepNested` carries the `addIndTypes` success as
a separate conjunct (read from its definition at `InductR.lean:476`); that `WFC`'s four
non-`ctors` fields are identical to `WF`'s (read by comparing the two `structure` bodies);
that `ntreeAux_ctorConstsCR_wf` proves the substituted constructor constants well-formed at
`env₃` (read from `ConstSubstNested.lean`, not re-elaborated); that the `RecTyped.lean` rename is
what broke `TeleCongr`/`HTeleRecB` (inferred from the error text plus `git status`, not from that
stream's own report).
