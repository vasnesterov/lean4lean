# Handoff: instantiating `VEnv.Params`

**Question asked:** can `Lean4Lean.VEnv.Params` (`Theory/Typing/ChurchRosser.lean:12`) be
instantiated from `VEnv.WF`?

**Answer: yes, and nine of its ten fields already were.**  `Params` is now inhabited
(`propLoopParams`, sorry-free), and there is a general constructor
`paramsOfWF : env.WF → (U : Nat) → PatWF env U → Params` (sorry-free) whose one hypothesis is
a *single named field*, `pat_wf`.  On the δ fragment even that is discharged
(`paramsOfDelta`), so `Params` is unconditionally inhabited over every environment whose
rules are all δ-rules.

Marks: **[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced; **[read]** = read off source;
**[analysis]** = neither.

---

## 0. The three things to know before touching this

0. **`extra_pat` is not the hard field, and it is not "an invariant `VEnv.WF` does not
   supply".**  The task brief and `docs/handoff-weakn.md` §4.1 both said it was.  It is
   proved for an *arbitrary* `VEnv.WF` environment by `Lean4Lean.Pat.extra`
   (`Theory/Typing/PatternRules.lean:1708`, sorry-free), and
   `VInductDecl'.iotaRule`'s η-expanded right-hand side was *designed* to make it hold on the
   nose — its docstring (`Theory/Inductive/Decl.lean:595-616`, on `VInductDecl'.iotaRule`) says so in as many words, and ends "the shape chosen here is what leaves `pat_wf` as the only field with real content".
   **[machine-checked: `paramsOfWF` assigns `extra_pat := fun _ => Pat.extra henv`.]**
1. **The construction was already ~90 % in the tree and unconnected.**
   `Theory/Typing/PatternRules.lean` (2101 lines, **0/204 declarations `sorryAx`-tainted**
   **[measured]**) defines `Lean4Lean.Pat env` and proves `Pat.simple`, `Pat.uniq`,
   `Pat.app_l_uniq`, `Pat.app_uniq`, `Pat.extra` — five of the six non-data fields — for any
   `env.WF`.  Nothing referenced `VEnv.Params` from there; the missing artefact was the
   twelve-line `Params.mk`.  This file is *in the owned set of this stream* and its closing
   section already predicted exactly this ("`Params`' six fields are now five proved and one
   open").
2. **The one open field is `pat_wf`, and it is not circular with the strengthening target.**
   Forward reachability over the declaration graph: `IsDefEqU.forallE_inv`,
   `forallE_inv_stratified` and `sort_inv` have **NO PATH** to any of `IsDefEqU.weakN_iff`,
   `IsDefEq.weakN_iff'`, `IsDefEq.weakN_iff`, `HasType.weakN_iff`, `VExpr.WF.weakN_iff`,
   `OnCtx.weakN_inv`.  Neither do `paramsOfWF`, `paramsOfDelta`, `Pat.extra`, `Pat.uniq`,
   `patWF_of_deltaFragment` or `propLoopParams`. **[measured]**

---

## 1. Field-by-field verdict on `Params`

Ten fields.  `Γ`, `df`, `ls`, `p`, `r`, … are the class's auto-bound implicits.

| field | kind | verdict at an arbitrary `VEnv.WF env` |
|---|---|---|
| `env : VEnv` | data | free — it is the environment you are instantiating at |
| `henv : env.WF` | proof | **literally the hypothesis**.  Not extra. |
| `univs : Nat` | data | free |
| `Pat : (p : Pattern) → p.RHS × p.Check → Prop` | data | free, and the canonical choice exists: `Lean4Lean.Pat env` (`PatternRules.lean:270`), an inductive family with one constructor per rule shape (δ / ι / quot) |
| `pat_simple` | proof | **derivable** — `Pat.simple` **[machine-checked]** |
| `pat_uniq` | proof | **derivable from `env.WF`** — `Pat.uniq henv`.  Needs the declaration history (`addConst` rejects duplicates), which is exactly what `VEnv.WF` carries. **[machine-checked]** |
| `pat_app_l_uniq` | proof | **derivable** — `Pat.app_l_uniq` (arity arithmetic on `Pattern.varN`) **[machine-checked]** |
| `pat_app_uniq` | proof | **derivable** — `Pat.app_uniq`, via `Pat.Leaves.rec_ne_ctor` (no recursor name is a constructor name) **[machine-checked]** |
| `extra_pat` | proof | **derivable from `env.WF`** — `Pat.extra henv`, dispatching on `VEnv.WF.ruleShape`.  See §0.0. **[machine-checked]** |
| `pat_wf` | proof | **OPEN.**  The one semantic field: a registered rule, fired at a term the environment types, is a definitional equality.  δ case proved (`patWF_delta`); ι and quot cases need `IsDefEqU.forallE_inv` (`Injectivity.lean`, `sorry`) to invert the applied spine's typing against the rule's declared telescope. **[δ case machine-checked; ι/quot: read, from `PatternRules.lean`'s closing section, plus analysis]** |

So the honest one-line answer to "is `extra_pat` genuinely extra?": **no**, and the field that
*is* extra is `pat_wf`, which nobody named.

### 1.1 Why `pat_wf`'s δ case is free and its ι/quot cases are not

`patWF_delta` **[machine-checked]**: for `Pat.delta`, the matched term is `.const c ls` and the
rule is `⟨u, .const c (VLevel.params u), v, t⟩`.  `HasType.const_inv` gives
`env.constants c = some ci` and `ls.length = ci.uvars`; `Ordered.defEqWF` applied to the rule
and `const_inv` again at `Γ = []` give `u = ci.uvars`; then `IsDefEq.extra` *is* the rule and
`VLevel.inst_map_id` turns `(params u).map (inst ls)` back into `ls`.  Nothing else is used.

For ι and quot the matched term is an *application spine*, and the rule is the λ-abstracted
`mkLams Δ L`.  Getting from "`Γ ⊢ rec p m min i (c p b) : A`" to "each argument is typed at the
domain `Δ` declares" is `HasType.app_inv` repeatedly, and reconciling the two domains is
Π-injectivity. **[analysis; `PatternRules.lean`'s closing section states the same conclusion]**

---

## 2. What is in the tree now

### `Lean4Lean/Theory/Typing/ParamsBuild.lean` (new, 121 lines, no `sorry`)

| name | statement | axioms |
|---|---|---|
| `VEnv.PatWF env U` | the one open field, at `Pat := Lean4Lean.Pat env` | — (a `def`) |
| `VEnv.paramsOfWF` | `env.WF → (U : Nat) → PatWF env U → Params` | `[propext, Classical.choice, Quot.sound]` **[measured]** |
| `VEnv.DeltaFragment env` | every registered pattern is a bare `.const` | — |
| `VEnv.patWF_delta` | the δ case of `pat_wf`, unconditionally | `[propext, Classical.choice, Quot.sound]` |
| `VEnv.patWF_of_deltaFragment` | `PatWF` on the δ fragment | `[propext, Classical.choice, Quot.sound]` |
| `VEnv.paramsOfDelta` | **`Params` from `env.WF` alone, on the δ fragment** | `[propext, Classical.choice, Quot.sound]` |
| `VEnv.church_rosser_of_patWF` | `env.WF → PatWF → OnCtx Γ → IsDefEq → CRDefEq Γ e₁ e₂` | `sorryAx` **inherited from `church_rosser`** — see §5 |

### `Lean4Lean/Theory/Typing/ParamsWitness.lean` (new, 225 lines, no `sorry`)

A hand-built instance over `CycleConv.propLoopEnv`, importing only `ChurchRosser.lean` and
`CycleConv.lean` — an independent check that does not go through `PatternRules.lean`'s 2101
lines.

| name | statement | axioms |
|---|---|---|
| `VEnv.propLoopParams` | **`Params` is inhabited** | `[propext, Classical.choice, Quot.sound]` **[measured]** |
| `VEnv.propLoopEnv_parRed_fires`, `…_fires'` | `ParRed [] A B`, `ParRed [] B A` by `ParRed.extra` | sorry-free |
| `VEnv.propLoopEnv_crDefEq_fires` | `CRDefEq [] A B`, proved by hand, joined at `B` by a **real** δ-step | sorry-free |
| `VEnv.propLoopEnv_church_rosser_fires` | the same conclusion via `IsDefEq.church_rosser` | `sorryAx` (inherited) |
| `VEnv.propLoopEnv_key_length`, `…_deltaFragment` | `propLoopEnv` is in the δ fragment (via `VDefEq.key` lengths: δ-rules key to one name, quot and ι rules to two) | sorry-free |
| `VEnv.propLoopParamsOfWF` | the same environment's instance, out of `paramsOfDelta` | sorry-free |

**Non-vacuity, per the acceptance criterion.**  `propLoopEnv` has two constants and two
δ-rules, is `VEnv.WF` (`propLoopEnv_wf`), and its head reduction is *not* well-founded
(`propLoop_headStep_not_wf`).  `extra_pat` is discharged at rules that fire:
`propLoopEnv_parRed_fires` is a `ParRed.extra` step, and `propLoopEnv_crDefEq_fires` joins `A`
and `B` at `B` along that step, not at a reflexivity.  The instance is **not** available over
`VEnv.empty` by the same construction — `VEnv.empty` has no constants and no rules, so its
`Pat` table is empty and the `parRed`/`crDefEq` witnesses do not exist.

Neither instance is registered as a global `instance`; both are `@[instance_reducible] def`s.
A global instance would let every `[Params]`-quantified theorem in `ChurchRosser.lean` and
`HeadReduction.lean` be silently specialised to one witness.  Use
`attribute [local instance]` or `@`-application.

---

## 3. Measurements

Instrument: the same forward/reverse declaration-graph walk as `scripts/cone-measure.lean`
(`getUsedConstantsAsSet` with `allowOpaque := true`, so `.thmInfo` bodies are seen), scoped to
all `Lean4Lean.*` declarations reachable from `Lean4Lean.Theory` + the new files: **5096
declarations**.

### 3.1 How much is downstream of `Params`  **[measured]**

| seed | direct users | transitive users |
|---|---|---|
| `VEnv.Params` | 538 | **545** |
| `VEnv.Params.env` | 324 | 356 |
| `VEnv.Params.Pat` | 71 | 144 |

By module: **355 `ChurchRosser.lean`, 179 `HeadReduction.lean`**, 9 `ParamsWitness.lean`, 2
`ParamsBuild.lean`.  So the brief's "how big is the dead weight" number is **534 pre-existing
declarations** — and they are no longer dead weight, because the structure is inhabited and
constructible.

Taint, same scope **[measured]**: `ChurchRosser.lean` **40/445** declarations `sorryAx`-tainted,
`HeadReduction.lean` **21/216**, `PatternRules.lean` **0/204**, `PatternDecode.lean` **0/229**.

### 3.2 The circularity, re-measured  **[measured]**

Declarations that use the `weakN` family (`IsDefEqU.weakN_iff`, `IsDefEq.weakN_iff'`,
`IsDefEq.weakN_iff`, `HasType.weakN_iff`, `VExpr.WF.weakN_iff`, `OnCtx.weakN_inv`)
**directly**, across `ChurchRosser.lean` *and* `HeadReduction.lean`:

| declaration | which of the family |
|---|---|
| `NormalEq.weakN_inv_DFC` | `IsDefEqU.weakN_iff`, `IsDefEq.weakN_iff`, `HasType.weakN_iff`, `VExpr.WF.weakN_iff`, `OnCtx.weakN_inv` |
| `ParRedExt.parRed_beta` | `IsDefEqU.weakN_iff`, `HasType.weakN_iff` |
| `ParRed.weakN_inv` | `IsDefEqU.weakN_iff` |
| `hasType_app_bvar0` | `IsDefEqU.weakN_iff` |

**Exactly the four `docs/handoff-weakn.md` §4.2 names, confirmed independently, and none in
`HeadReduction.lean`.**  Transitively 18 `ChurchRosser.lean` declarations are affected
(`CRDefEq.trans`, `DescentLam.beta`, `DescentLam.instN`, `IsDefEq.church_rosser`,
`NormalEq.appDF_extra_of_descend`, `NormalEq.descend`, `NormalEq.parRed`, `NormalEq.parRedS`,
`NormalEq.trans`(+`._unary`), `NormalEq.weakN_iff`, `NormalEq.weakN_inv_DFC`,
`ParRed.church_rosser`, `ParRed.triangle`, `ParRed.weakN_inv`, `ParRedExt.parRed_beta`,
`ParRedS.church_rosser`, `hasType_app_bvar0`).

**The instantiation route is not part of that cycle** (§0.2).

### 3.3 A blocker nobody has priced: `PatternRules.lean` and `Verify/` cannot coexist

**[measured]** `import Lean4Lean.Theory` alongside `Verify/TypeChecker`, `Verify/Typing/DefEqCtx`
and `Verify/Environment/Lemmas` compiles.  Replacing the first import with
`Lean4Lean.Theory.Typing.ParamsBuild` **fails**:

    error: import Lean4Lean.Verify.Environment.Lemmas failed, environment already contains
    'Lean4Lean.VEnv.addDefEqs_le._f' from Lean4Lean.Theory.Typing.DeltaUnique

Full list of colliding names (15, from 7 source declarations) **[measured]**:

| name | Theory side | Verify side |
|---|---|---|
| `VEnv.HasArgs.defeqDFC` (+2 aux) | `Theory/Typing/PatternRules.lean` | `Verify/Typing/DefEqCtx.lean` |
| `VEnv.addConst_defeqs` | `Theory/Typing/DeltaUnique.lean` | `Verify/TypeChecker/Reduce.lean` |
| `VEnv.addConsts_defeqs` (+2 aux) | `Theory/Typing/DeltaUnique.lean` | `Verify/TypeChecker/Reduce.lean` |
| `VEnv.addDefEqs_defeqs` (+2 aux) | `Theory/Typing/DeltaUnique.lean` | `Verify/TypeChecker/Reduce.lean` |
| `VEnv.addDefEqs_le` (+2 aux) | `Theory/Typing/DeltaUnique.lean` | `Verify/Environment/Lemmas.lean` |
| `VInductDecl'.ctorsAll.eq_1` | `Theory/Inductive/Lemmas.lean` | `Theory/Inductive/Structure.lean` |
| `VInductDecl'.selfLvls.eq_1` | `Theory/Inductive/Lemmas.lean` | `Theory/Inductive/Structure.lean` |

`Theory/Typing/DeclRules.lean`'s docstring flags the `_defeqs` half of this ("a downstream file
that saw both would fail to compile") but the consequence was not drawn: **nothing under
`Verify/` — where `kernel_sound` lives — can currently import `paramsOfWF`.**  The fix is
mechanical (rename five declarations; the last two are auto-generated equation lemmas and need
their generation forced in one place), but it is not this stream's to make alone:
`DeltaUnique.lean`, `Inductive/Lemmas.lean` and `Verify/` are owned elsewhere.  Only
`PatternRules.lean`'s `HasArgs.defeqDFC` is in this stream's set, and renaming one of seven
fixes nothing.

---

## 4. A defect found and fixed in `ChurchRosser.lean`

`Params.extra_pat` read

```lean
env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars → …
```

where **`uvars` is an auto-bound implicit of the field** — a fresh universally quantified
`Nat`, unrelated to `Params.univs`.  `#check @Params.extra_pat` showed it explicitly, before the fix:
`∀ [self : Params] {Γ} {df} {ls} {uvars : Nat}, …`. **[measured, pre-fix]**  (`uvars` is the section
variable of `Theory/Typing/Basic.lean`, where `IsDefEq.extra` states the same hypothesis
correctly; inside the class it auto-bound instead of resolving.)

Consequence: the field demanded its conclusion — including a semantic `Check.OK` at
`IsDefEqU env univs _` — for level lists that are *not* well-formed for the judgment.
`Pat.extra` cannot supply that: its ι case goes through `IsDefEqU.instL`, which needs
`l.WF univs`.  Changed to `l.WF univs`.  The sole consumer (`ChurchRosser.lean:2203`, inside
`NormalEq.parRed`'s `extra` case) holds `l.WF univs` from `IsDefEq.extra`, so the narrowing
costs it nothing; `ChurchRosser.lean` and `HeadReduction.lean` both still build unchanged.
**[measured: full `lake build` clean, 1340 jobs, Guard's three checks pass.]**

Whether the *unfixed* field was outright false is not settled here: its δ case holds for any
`ls` (the check is `Check.true`), so a refutation would have to run through the ι case.

---

## 5. The residual, and the collapse test applied to it

`paramsOfWF : env.WF → (U : Nat) → PatWF env U → Params`.  Applying
`docs/handoff-weakn.md` §6's test — *can the residual's quantifiers be instantiated so its
premises degenerate into the target's?*:

* **`PatWF env U` is one of `Params`' own ten fields**, at the fixed choice
  `Pat := Lean4Lean.Pat env`.  So this is a **reduction of a ten-field class to one field**,
  not an elimination of a difficulty.  Say it that way and nothing is oversold.
* It is **not** a tautology in the other direction: `Params → PatWF env U` is *not* available,
  because a `Params` may carry any `Pat` it likes and `PatWF` is about the canonical one.
* What the reduction actually buys, and it is not nothing: nine fields are discharged; the
  residual is a *named, `sorry`-free-statable* lemma; and the residual has **NO PATH** to the
  `weakN` family **[measured]**, so it cannot be the hidden circularity.
* On the δ fragment the residual is **gone**, not reduced (`paramsOfDelta`).

`church_rosser_of_patWF` is the unlocked statement, and it is `sorryAx`-tainted — it inherits
`NormalEq.descend`'s five `sorry`s and `IsDefEqU.forallE_inv_stratified` through
`IsDefEq.church_rosser`.  It is recorded because typechecking it *is* the check that
`paramsOfWF` discharges every obligation `church_rosser` asks for; it is **not** a proved
result and must not be cited as one.

---

## 6. Corrections to `docs/handoff-weakn.md` §4

| §4 claim | status |
|---|---|
| "`synthInstance?` … reports **NO instance** of `Lean4Lean.VEnv.Params`" | true when written, and still true of *registered* instances — deliberately, §2.  Two `def`s now exist. |
| "`extra_pat` … is an invariant on the environment that `VEnv.WF` does **not** supply" | **false** — `Pat.extra henv` proves it for any `env.WF`. §0.0 |
| "even a fully de-circularised `ChurchRosser.lean` proves nothing about `UniqueTyping.lean:174`" | **overstated**: the prerequisite it names (instantiating `Params`) is now one open field away, and that field is not circular with the target. |
| "The prerequisite is *instantiating `Params` from `VEnv.WF`* — a separate project" | true, and the project was ~90 % done in `PatternRules.lean`, which §4 did not consult |
| "four declarations at ~20 call sites" | **confirmed** independently; exactly four direct users, 18 transitive, none in `HeadReduction.lean`. §3.2 |
| verdict "do not start here" | now a judgement call, not a fact.  The three prerequisites it lists are still all real, and (3) — `NormalEq.descend`'s five `sorry`s — is untouched. |

The §8 recommendation "the first tractable step toward a reduction relation is instantiating
`Params` from `VEnv.WF`" was **right**, and the step turned out to be twelve lines.

---

## 7. What to pick up first

1. **`pat_wf` for the ι and quot cases** (`PatWF`, `ParamsBuild.lean`).  It is the whole
   remaining gap between `VEnv.WF` and `Params`, it is not circular with `weakN_iff`
   **[measured]**, and it reduces to `IsDefEqU.forallE_inv` (`Injectivity.lean`, open).
   Do not restate it: `PatWF env U` is the statement, and `patWF_delta` is one third of it.
2. **The seven-name collision of §3.3.**  Until it is fixed, no result proved through
   `PatternRules.lean` can reach `Verify/`, so nothing here can serve `kernel_sound` even if
   `pat_wf` lands.  Cheap, mechanical, and cross-stream.
3. **`NormalEq.descend`'s five `sorry`s** and the four-declaration circularity of §3.2 — both
   unchanged, both still required before Church–Rosser can serve `IsDefEqU.weakN_iff`.
4. **Do not** re-litigate `extra_pat`.  It is proved.

---

## 8. Files

* `Lean4Lean/Theory/Typing/ParamsBuild.lean` — **new**, 121 lines, no `sorry`.
* `Lean4Lean/Theory/Typing/ParamsWitness.lean` — **new**, 225 lines, no `sorry`.
* `Lean4Lean/Theory/Typing/ChurchRosser.lean` — **one-token change** in `Params.extra_pat`
  (`l.WF uvars` → `l.WF univs`) plus a docstring paragraph recording why.  §4.
* `Lean4Lean/Theory/Typing/PatternRules.lean` — **unchanged**; it did the work.
* `Lean4Lean/Theory.lean` — **unchanged** (not in this stream's set).  The two new modules are
  picked up by the `Lean4Lean.Theory.*` glob and build under the default target
  **[measured: `lake build`, 1340 jobs, clean]**, but they are not in `Lean4Lean/Theory.lean`'s
  import list, so `scripts/cone-measure.lean`'s scopes do not see them.
