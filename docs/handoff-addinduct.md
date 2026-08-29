# Handoff: `AddInduct`'s constructor — the measurement, the patch, and the `Eq` gap closed

Scope: `inductive AddInduct` (`Verify/Environment/Basic.lean:109`) has no constructors, so
`TrEnv'.induct` can never fire. This document separates **machine-checked** from **read off
source**, gives the measured blast radius before and after, states the exact flip patch, and
records the one result that turned out not to need the flip at all.

New file, all of it owned by this stream: **`Lean4Lean/Verify/InductFlip.lean`**.
New instrument: **`scripts/blast-addinduct.lean`**.
Docstring corrections in owned files: `Verify/Environment/Basic.lean`, `Verify/Environment.lean`.

Build state at the end of this stream: `lake build Lean4Lean.Verify` green, 1215 jobs, all
three of Guard's checks passing, no new `sorry`, no new axiom.

---

## 0. The headline, first

Two results, both machine-checked, both contradicting a claim that was standing in the tree.

**(a) The `Eq` gap is closed, and it was never an `AddInduct` obligation.**

`docs/handoff-eq-safety.md` §3 states that `htr` — *a safe inductive `Eq` translates to
`eqConst`* — "is the `AddInduct` / `TrEnv'.induct` obligation and nothing else … not provable
today because `AddInduct` has no constructors". `Verify/EqSafety.lean:110-113` says the same.
**Both are wrong.**

```lean
theorem checkEqType.WF_quotReady_closed {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady
```

is proved, sorry-free, in `Verify/InductFlip.lean` §3.4. Machine-checked cone facts: the
transitive `getUsedConstantsAsSet` cone of that theorem (7327 declarations) contains **no**
`AddInduct` lemma — not `AddInduct.to_addInduct`, not `AddInductStages`, not `AddIndConsts`.
`AddInduct` and `TrEnv'.induct` appear only as constructors of `TrEnv'`, which the proof
inducts through uniformly via `TrEnv.find?`.

Why the earlier reading was wrong: `TrEnv.find?` (`Verify/Environment/Lemmas.lean`) already
returns the model's constant at a *visible* name **together with its `TrConstant`**, for every
`TrEnv'` step and without asking which step introduced it. The missing piece was never the
inductive rule; it was the *identity* of the translated type, which `TrExprS.unique` gives from
a translation witness plus absence of `.proj`. The remaining half — turning `checkEqType`'s
`lctx.mkForall #[α] …` comparison into a closed `Expr` — is the item
`docs/handoff-eq-safety.md` §4 deliberately deferred; `Lean.LocalContext.mkBinding_eq`
(`Verify/LocalContext.lean`) is the step it was missing, and §3.1–§3.2 below do it.

**(b) `addDecl.WF`'s `inductDecl` branch is a false statement, not an open one.**

```lean
theorem VEnvs.WF.no_inductInfo {ves : VEnvs} {env : Environment} (wf : ves.WF env) {n v} :
    env.constants.find? n ≠ some (.inductInfo v)
```

One line from `TrEnv'.no_inductInfo` at `.unsafe`. So `ves.WF env` is **unsatisfiable** for any
kernel environment whose map holds an `.inductInfo`, and `addDecl.WF`
(`Verify/Environment.lean:258`, the `| inductDecl _ _ _ _ => sorry` at :272) is proving
something false for every declaration whose success inserts one. `Verify/Bridge.lean`'s `PreludeBridge` docstring records the same fact ("`TrEnv`
provably contains no inductive declaration at all"); stating it at the `VEnvs` level makes the
consequence for `addDecl.WF` explicit rather than implicit.

---

## 1. The blast radius, measured

Instrument: `scripts/blast-addinduct.lean` — the `scripts/cone-measure.lean` graph (same
`deps`, same `value? (allowOpaque := true)` fix for the `.thmInfo` scan trap), over all
**12778** `Lean4Lean` source declarations in the closure of `Verify/`. Reproduce with
`~/.elan/bin/lake env lean scripts/blast-addinduct.lean`. Everything in this section is
machine output, not grep.

### 1.1 Tier 1 — proofs that case on the empty relation

Seven seeds. Their **statements** stay true after the flip (except the last); only the proofs
must change.

| seed | direct | transitive |
|---|---|---|
| `AddInduct.to_addInduct` (`Environment/Basic.lean:113`) | 2 | 134 |
| `Aligned.addInduct` (`Environment/Lemmas.lean:67`) | 1 | 114 |
| `AddInduct.le` (`SafeFragment.lean:250`) | 1 | 4 |
| `TrEnv'.of_value` (`Environment/Lemmas.lean`) | 1 | 55 |
| `TrEnv'.find?_shape` (`TypeChecker/Reduce.lean:57`) | 1 | 66 |
| `TrEnv'.defeqs_shape` (`TypeChecker/Reduce.lean:172`) | 0 | 0 |
| `TrEnv'.no_inductInfo` (`Environment/Extension.lean:17`) | 1 | 10 |

**Union: 182 transitive users, 18 modules** — Primitive 29, IsDefEq 25, InferType 20,
Extension 16, Reduce 13, TypeChecker 11, Inductive/Add 9, Bridge 8, Environment 8,
SafeFragment 8, Checker 7, Environment/Lemmas 7, TypeChecker/Basic 7, WHNF 7,
Environment/Basic 3, EquivManager 2, EqSafety 1, Boundaries 1.

### 1.2 Tier 2 — statements that become false

Seeds: `TrEnv'.no_inductInfo`, `TrEnv.not_inductInfo`, `.not_ctorInfo`, `.not_recInfo`,
`TypeChecker.VContext.not_inductInfo`, `inductiveReduceRec_eq_none`, `checkEqType.WF`,
`TrEnv'.find?_shape`, `TrEnv.find?_shape`.

**Union: 68 transitive users — of which 56 are already `sorryAx`-tainted.** Only **12** are
currently sorry-free, and that is the real cost of the flip:

| sorry-free tier-2 user | verdict |
|---|---|
| `TrEnv.find?_shape` | **repairable** — restate with three more disjuncts (`AddInductStages.find?_shape`) |
| `checkEqType.WF` | **repairable** — `checkEqType.WF_quotReady_closed` (already proved, §0a) |
| `addQuot.WF` | **repairable modulo the `AddQuot` construction** (§6) |
| `TrEnv.not_inductInfo` | **dies** |
| `TrEnv.not_ctorInfo` | **dies** |
| `TrEnv.not_recInfo` | **dies** |
| `TypeChecker.VContext.not_inductInfo` | **dies** |
| `TypeChecker.Inner.inductiveReduceRec_eq_none` | **dies** — needs ι-reduction (M3) |
| `TypeChecker.Inner.reduceProjCore_none` | **dies** — needs projection reduction |
| `TypeChecker.Inner.reduceProjCore.WF` | **dies** (through the above) |
| `TypeChecker.Inner.inferProj_always_throws` | **dies** |
| `TypeChecker.Inner.tryEtaStructCore_never_true` | **dies** — needs structure eta |

### 1.3 The correction this measurement forces

`Verify/Environment/Basic.lean`'s own note said the flip makes "*everything* in `Verify/` go
red". That over-states it in one direction and under-states the diagnosis in another:

* 182 declarations are *touched*, but 173 of them only need their induct arm supplied (or
  nothing at all), and every one of those arms is already proved.
* Of the 68 whose statements go false, 56 are already `sorryAx`-tainted, so the flip destroys
  **no axiom-level content** there — it converts already-tainted proofs into build errors.
* The set that genuinely loses proved content is **nine declarations**, all in
  `Verify/TypeChecker/`. Those need ι-reduction, projection reduction and structure eta.
  `Verify/TypeChecker/Reduce.lean`'s own note ("'repair the consumers' is not available for
  those three") is exactly right, and the measurement puts a number on it.

This corrected paragraph is now in `Verify/Environment/Basic.lean`'s section header.

---

## 2. The constructor, stated

```lean
def AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
    (m₂ : ConstMap) (env₂ : VEnv) : Prop := AddInductStages m₁ env₁ decl m₂ env₂
```

with `AddInduct.to_addInduct := AddInductStages.to_addInduct`. `AddInductStages`
(`Verify/Environment/Basic.lean:219`, pre-existing and proved) is

```
∃ mt et mc ec e₃,
  AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) D.typeConsts m₁ env₁ mt et ∧
  AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v)   D.ctorConsts mt et mc ec ∧
  AddIndConsts (fun ci => ∃ v, ci = .recInfo v)    D.recConsts  mc ec m₂ e₃ ∧
  env₂ = e₃.addIndRules D
```

**Where the shape is forced by the spec, and where there was a choice.**

*Forced.*
- Three folds in the order types → constructors → recursors, ι-rules last: this is exactly
  `VEnv.addInduct'`'s own staging (`Theory/Inductive/Decl.lean`), and it is what makes
  `to_addInduct` compose. The constructor stage *cannot* be stated at `env₁`: a constructor's
  stored type names the block's own type constant, so its `TrConstant` is unsatisfiable before
  `addIndTypes` has run. `R10.Wit.addInductStages_wit` is the witness for that, and
  `no_trIndCtor_at_base` (`Verify/Environment/Induct.lean`) records the same wall from the
  other side.
- The lists `D.typeConsts`, `D.ctorConsts`, `D.recConsts` and the constants `⟨D.uvars, T.type⟩`,
  `⟨D.uvars, C.type D j⟩`, `⟨D.recUvars, D.recType j⟩` come from `VInductDecl'` verbatim; there
  is nothing to choose.
- `env₂ = e₃.addIndRules D` rather than a relation: `addIndRules` is a total function.

*Chosen.*
- **The per-stage shape predicate** `S`. `AddIndConsts` is parameterised by a
  `ConstantInfo → Prop` and instantiated to `.inductInfo` / `.ctorInfo` / `.recInfo` per stage,
  rather than to "one of the three" globally. That is what lets `AddInductStages.find?_shape`
  tell a consumer *which* kind of constant a block name carries. Nothing in the spec requires
  it; it is strictly more informative and costs nothing.
- **The `ConstantInfo` is existential.** `InductiveVal`/`ConstructorVal`/`RecursorVal` carry
  elaboration bookkeeping (`numNested`, `isReflexive`, `rules`, …) that `VInductDecl'` does not
  model. `TrConstant` pins the two things that matter — universe count and type. Pinning more
  would need `VInductDecl'` to grow fields with no abstract meaning.
- **The safety level in `AddIndConsts.cons` is the literal `.safe`, not the `TrEnv'` index.**
  See §3.

---

## 3. The safety gate

`AddIndConsts.cons` carries `TrConstant .safe env ci ci'`, i.e. `.safe ≤ ci.safety`, and `.safe`
is the top of `DefinitionSafety`, so antisymmetry pins `ci.safety = .safe`
(`AddIndConsts.find?`, pre-existing). That is the whole gate, and it is already written; the
flip is what wires it in.

Three things about it that are **not** what the surrounding documentation says.

1. **The gate is on *declared* constants only.** `AddIndConsts.find?` constrains the block's own
   type/constructor/recursor constants. It says nothing directly about constants the block
   *references*. Answering the coordinator's G3 question: the referenced side is inherited from
   the environment rather than checked, and the mechanism is `TrExprS.const`, whose premise is
   `env.constants c = some ci` — the **`VEnv`**, not the kernel map. A `partial`/`unsafe`
   constant reaches the kernel map only through `TrEnv'.ignore`, which gives it *no* `VEnv`
   counterpart, so a block whose stored types name one cannot be translated at all. This is the
   same shape as `resolveC_target_safe`: the property is a consequence of the declaration
   history, not an added check. It is read off `TrExprS`'s definition, not separately
   machine-checked here.
2. **"An unsafe block is taken by `TrEnv'.ignore` instead" is false at `.unsafe`.**
   `ignore`'s premise is `¬ safety ≤ ci.safety`, and `.unsafe` is the bottom of the order, so
   `.unsafe ≤ ci.safety` holds for every `ci` (`ignore_unavailable_at_unsafe`,
   `Verify/TypeChecker/Reduce.lean` — pre-existing, machine-checked). `Theory/Inductive/Decl.lean`'s
   R10 handover and `Verify/Environment/Induct.lean`'s `TrIndDecl.safe` both state the false
   version. The gate therefore leaves `TrEnv' .unsafe` with **no rule at all** for an unsafe
   inductive. It does not create that gap (today `TrEnv' .unsafe` has no rule for a *safe*
   inductive either) but the flip does not close it, and it must be closed before
   `addDecl.WF`'s `inductDecl` branch can be discharged for an `unsafe inductive`.
3. **Gating `TrEnv'.induct` on `safety = .safe` is not an option.** It would leave a safe
   inductive with no rule at `.unsafe` — by (2), `ignore` cannot take it — so `VEnvs.WF` would
   again be unsatisfiable for any environment with an inductive. The `.safe` in
   `AddIndConsts.cons` must stay independent of the `TrEnv'` index.

---

## 4. Non-vacuity

`Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` is the standing warning: an inductive
block admitted with *vacuously satisfied* constructor obligations is not merely weak but
inconsistent. The mechanism is that `VInductDecl'.WF.ctors` is staged over
`env.addIndTypes D = some env₁`, which is `none` for a block re-declaring an existing type — so
the constructor half of `WF` is discharged by `absurd` at every companion block. The coordinator
sharpened this mid-stream: `fooComp_WFC` shows re-staging alone does not fix it, and the shape
that worked was making the content a **definition** rather than a check.

Machine-checked answers, all in `Verify/InductFlip.lean` §2:

* **`AddInductStages.addIndTypes`** — the relation *supplies* `env₁.addIndTypes D = some et`.
  It is not a hypothesis staged over something that might fail; it falls out of the first fold.
* **`AddInductStages.ctors_wf`** — consequently, from `D.WF env₁` plus the relation, the
  constructor obligations `C.WF et D j T` are **actually available** for every `j`, `T`, `C`.
  The `absurd` route that discharges `fooComp_WF` is unavailable here.
* **`AddInductStages.type_fresh`** — every type name the block declares is *fresh* in `env₁`.
  So the `fooCompDecl` shape — re-declaring `Foo` in order to lie about its constructors — has
  **no instance** of `AddInduct` at all. This is the G1 guard, obtained for free from
  `VEnv.addConst`'s freshness rather than added as a check.
* **`AddIndConsts.find?_of_not_mem` / `AddInductStages.find?_of_not_mem`** — the *definition*
  shape the coordinator asked for. `m₂` is `m₁` with **exactly** the block's constants inserted:
  outside `D.allNames` the map is unchanged. So a `VInductDecl'` that under-reports its
  constructors cannot be paired with a constant map that contains them — the under-reporting is
  visible in `m₂`, not merely unchecked. (This is the anti-lie property; it does *not* by itself
  discharge `addDecl.WF`'s obligation to show the executable `addInductive`'s output map is the
  one `AddInduct` builds. See §6.)

**Replay at a concrete witness** (`Verify/InductFlip.lean`, `namespace R10.Wit`), in the style
`Theory/Typing/PropConv.lean` replays at index zero:

* **`R10.Wit.decl_WF : decl.WF VEnv.empty`** — the one-type one-nullary-constructor block
  `inductive U : Type | unit : U` is well-formed, and its `ctors` field is discharged by a real
  `VIndCtor.WF`, because `VEnv.empty.addIndTypes decl` succeeds.
* **`R10.Wit.induct_premises_wit`** — `TrEnv'.induct`'s two premises hold **at once**
  (`decl.WF VEnv.empty` and `AddInductStages m VEnv.empty decl m' env'`), the block's type has a
  non-empty `ctors` list, and the constructor obligation is discharged rather than dodged.
  The recursor really carries its minor premise — `decl.recConsts`'s value is checked by `rfl`
  in `Verify/Environment/Basic.lean` — so `fooComp_inconsistent`'s
  `∀ (C : Foo → Prop) (m : Foo), C m` shape does not arise.

---

## 5. G4: ι-rule keys

Raised by the coordinator from `Theory/Inductive/CompanionResolve.lean`: `VEnv.addInductC`
threads its recursor renaming `rn` into `recConstsC` but not into `addIndRules`, so a block
declares `rn (mkRecName J)` while emitting its ι-rules under `mkRecName J` — a constant it never
declared (`VInductDecl'.key_iotaRule_ne_renamed`).

`AddInduct` is built on `VEnv.addInduct'`, which has no renaming parameter, so the defect cannot
arise. Machine-checked rather than argued:

```lean
theorem AddInductStages.iotaRule_declared (H : AddInductStages m₁ env₁ D m₂ env₂)
    (hdf : df ∈ D.iotaRules) :
    ∃ j q T C, D.types[j]? = some T ∧ C ∈ T.ctors ∧ D.types.getD j default = T ∧
      df = D.iotaRule j q C ∧
      env₂.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ ∧
      env₂.constants C.name = some ⟨D.uvars, C.type D j⟩
```

Composed with `VInductDecl'.key_iotaRule` (`Theory/Typing/DeltaUnique.lean`, which gives
`(D.iotaRule j q C).key = [Lean.mkRecName (D.types.getD j default).name, C.name]`) and the
`D.types.getD j default = T` conjunct, this says: **both names of every emitted rule's
`VDefEq.key` are constants the same step declares, at the types it declares them with.**

*Why the composition is done by hand rather than in one theorem*: `VDefEq.key` lives in
`Theory/Typing/DeltaUnique.lean`, and **that module cannot be imported into `Verify/` at all** —
it and `Verify/Environment/Lemmas.lean` both declare `VEnv.addDefEqs_le`, so the import fails
with `environment already contains 'Lean4Lean.VEnv.addDefEqs_le._f'`. Worth fixing on the Theory
side if `VDefEq.key` is ever wanted in `Verify/`; not this stream's file.

---

## 6. The flip patch, exactly

Seven files. **Four are not this stream's**, so none of them was touched; this is the
specification, and every piece of content it needs is proved somewhere this stream owns.

**(1) `Verify/Environment/Basic.lean` (owned).** Replace the empty `inductive AddInduct` with
the `def` of §2 and `AddInduct.to_addInduct := AddInductStages.to_addInduct`.

**(2) `Verify/Environment/Lemmas.lean` (owned).**
- `Aligned.addInduct`'s `nomatch H` → `Aligned.addInductStages`. That proof already exists, in
  `Verify/TypeChecker/Reduce.lean`; it must **move** to `Lemmas.lean` (Reduce is downstream) and
  be deleted from Reduce. Note `Aligned.addInduct`'s current *statement* is also wrong: its
  `env₁`/`env₂` are auto-bound implicits unrelated to `venv₁`/`venv₂`, so it says nothing.
- `TrEnv'.of_value`'s `| induct _ h1 H ih => cases h1` → use
  `AddInductStages.of_value_arm` (proved, `Verify/InductFlip.lean` §1) to reduce to `ih`, then
  `.mono AddInductStages.le`. `of_value_arm` must move to `Basic.lean` or `Lemmas.lean` at flip
  time (it is in `InductFlip.lean`, which is downstream).

**(3) `Verify/Environment.lean` (owned).** `checkEqType.WF` → `checkEqType.WF_quotReady_closed`'s
statement (proof: that theorem). Then `addQuot.WF`'s second branch must build `TrEnv'.quot`
instead of `False.elim`. **This is the one repair that is not yet in hand** — see §7.

**(4) `Verify/SafeFragment.lean` (NOT owned).** `AddInduct.le`'s `nomatch H` →
`AddInductStages.le` (proved, `Basic.lean`). One line. `TrEnv'.quotReady_of_quotInit`'s induct
case already reads `hadd.le`, so it needs no change.

**(5) `Verify/Environment/Extension.lean` (NOT owned).** **Delete `TrEnv'.no_inductInfo`.** It
becomes false. Its only consumer is `checkEqType.WF`, handled by (3).

**(6) `Verify/TypeChecker/Reduce.lean` (NOT owned).**
- `TrEnv'.find?_shape`: gain three disjuncts
  `∨ (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)`; induct arm is
  `AddInductStages.find?_shape` (proved, `Basic.lean`). Same for `TrEnv.find?_shape`.
- `TrEnv'.defeqs_shape`: gain `∨ ∃ D, df ∈ D.iotaRules`; induct arm is `AddInductStages.defeqs`
  (proved, `Basic.lean`).
- **Delete `TrEnv.not_inductInfo`, `.not_ctorInfo`, `.not_recInfo` and
  `TypeChecker.VContext.not_inductInfo`.** All false; `ctorInfo_recInfo_reachable` (already in
  that file) plus the flip is the refutation.
- **Delete or `sorry` `reduceProjCore_none` and `reduceProjCore.WF`.**
- Delete `Aligned.addInductStages` (moved to `Lemmas.lean` by (2)).

**(7) `Verify/TypeChecker/{WHNF,InferType,IsDefEq}.lean` (NOT owned).** `sorry` (or prove):
`inductiveReduceRec_eq_none` (WHNF), `inferProj_always_throws` (InferType),
`tryEtaStructCore_never_true` (IsDefEq). `isDefEqUnitLike_never_true` is already `sorry`-adjacent
and dies with the same argument.

**Net axiom-cone effect of the flip:** nine sorry-free declarations become `sorry`; nothing that
is currently sorry-free *outside* that list is lost, because every other tier-1 arm is proved and
the remaining 56 tier-2 users are already `sorryAx`-tainted.

---

## 7. What to pick up first

1. **`addQuot.WF`'s `AddQuot` construction.** This is now the *only* thing between the checker
   and a non-vacuous `addQuot.WF`, and it is orthogonal to `AddInduct`. Needed: from the
   executable `Environment.addQuot`, exhibit
   `AddQuot env.constants env'.constants (ves.venv safety) (venv' safety)` — four `AddQuot1`
   steps, each wanting `TrConstant .safe env (.quotInfo …) quotXConst`, i.e. a `TrExprS` for the
   stored type. The technique is settled and demonstrated: `Lean.LocalContext.mkForall_single`
   plus `mkBinding_eq` computes the `mkForall`, and `trExprS_eqStoredType` is the pattern for
   the translation. `Quot.lift`'s six binders make it the largest of the four; a `mkForall`
   lemma for two, three and four binders (the obvious iteration of `mkBindingList_cons`) is the
   first thing to write. Also needed: `Environment.add`'s effect on the constant map and
   `markQuotInit`'s on `quotInit`.
2. **The flip itself**, as §6, as one coordinated commit. Everything on the owned side is proved;
   the decision the human owns is whether to take nine `sorry`s in `Verify/TypeChecker/` now.
   Recommendation: **not yet**, because those nine are the *only* thing keeping the projection
   and ι-reduction obligations visible as theorems rather than as `sorry`s, and there is no
   consumer that becomes non-vacuous in exchange — `addDecl.WF`'s `inductDecl` branch also needs
   §7.3 before the flip buys anything.
3. **`addDecl.WF`'s `inductDecl` branch.** `AddInduct` constrains the *model*; the branch must
   additionally show that the map the executable `addInductive` produces **is** the map
   `AddInductStages` builds (`find?_of_not_mem` gives the "no extra entries" half of what that
   requires, on the abstract side). Until that is proved, a `VInductDecl'` and a kernel
   `InductiveVal` block are related only by an existential, and the coordinator's "prefer a
   definition to a check" warning applies here rather than to `AddInduct` itself.
4. **The `.unsafe` hole of §3.2.** `TrEnv'` has no rule for an unsafe inductive at any safety
   level, before or after the flip, and `ignore` cannot supply one. Either `TrEnv'` gains a rule
   that adds an unsafe block's constants without a positivity witness, or `addDecl.WF` must
   restrict to safe `inductDecl`s and say so.

---

## 8. Corrections to standing claims

Each is machine-checked; the file named is **not** this stream's unless marked.

| where | claim | correction |
|---|---|---|
| `docs/handoff-eq-safety.md` §3, §6.1 | `htr` is "a pure `AddInduct` obligation", "not provable today" | False. `checkEqType.WF_quotReady_closed`, no `AddInduct` in its cone (§0a). |
| `Verify/EqSafety.lean:26-27, 110-113` (not owned) | same | same |
| `Verify/SafeFragment.lean:60-63` (not owned) | the honest replacement "is not provable from the checker **as written**"; the fix is a checker change | Accurate, and now **discharged**: the checker change landed (`3bc24d6`), and `WF_type` does use `info.isUnsafe = false`. Not a correction — recorded so the note is not read as a live blocker. |
| `docs/handoff-eq-safety.md` §6.1 | `htr` is "*the only* thing between the checker and a non-vacuous `addQuot.WF`" | Also wrong in the other direction: the `AddQuot` construction (§7.1) is a second, larger obligation, and it is now the only one left. |
| `Verify/Environment/Basic.lean:140` (owned, **fixed**) | the flip makes "*everything* in `Verify/` go red" | Over-stated; 174 of 182 tier-1 users only need arms that are already proved, and the irreparable set is eight declarations (§1.3). |
| `Theory/Inductive/Decl.lean:703` (not owned) | an unsafe block "is taken by `TrEnv'.ignore` instead" | False at `.unsafe` (`ignore_unavailable_at_unsafe`). Same wording in `Verify/Environment/Induct.lean`'s `TrIndDecl.safe`. Already recorded in `Verify/TypeChecker/Reduce.lean`; repeated here because two files still carry the false version. |
| `Verify/Environment.lean` (owned, **fixed**) | `checkEqType.WF`/`addQuot.WF` blocked on `AddInduct` | Blocked on the `AddQuot` construction only. |

---

## 9. Inventory of what this stream proved

All in `Lean4Lean/Verify/InductFlip.lean`, all sorry-free (22 declarations checked by
`collectAxioms`; zero `sorryAx`), all axioms within `Verify/Axioms.lean`'s frozen 29.

*§1 stage lemmas.* `AddIndConsts.constants_of_mem`, `AddIndConsts.find?_of_not_mem`,
`AddInductStages.find?_of_not_mem`, `AddInductStages.constants_of_type`,
`AddInductStages.of_value_arm`.

*§2 non-vacuity.* `AddInductStages.addIndTypes`, `AddInductStages.ctors_wf`,
`AddInductStages.type_fresh`, `R10.Wit.decl_WF`, `R10.Wit.induct_premises_wit`.

*§3 the `Eq` obligation.* `Lean.LocalContext.wf_empty`, `.toList_empty`, `.find?_empty`,
`.find?_mkLocalDecl_empty`, `.mkForall_single`; `eqStoredType`, `mkForall_eqStoredType`,
`checkEqType.WF_type`; `TrExprS.IsUnique.of_eqv`, `isUnique_eqStoredType`,
`trExprS_eqStoredType`, `Lean.Expr.eqv_symm`; `TrEnv.quotReady_of_eq_type`;
**`checkEqType.WF_quotReady_closed`**.

*§4 G4.* `AddInductStages.iotaRule_declared`.

*§5 the cost of the emptiness.* `VEnvs.WF.no_inductInfo`.

**Not proved, and not attempted:** the flip itself; `addQuot.WF`; `addDecl.WF`'s `inductDecl`
branch; the nine `Verify/TypeChecker/` declarations of §1.2.

---

## 10. One interaction to watch

Another stream has an untracked `Lean4Lean/Std/LocalContext.lean` defining a pure-Lean
`Lean4Lean.LocalContext` (its own `mkLocalDecl`, `find?`, `mkForall`, plus `toLean`/`ofLean`).
There is no name clash today — this stream's lemmas are on `Lean.LocalContext` — but if
`ExprBuildT` in `Lean4Lean/Quot.lean` is switched to that type, then
`Lean.LocalContext.mkForall_single`, `.find?_mkLocalDecl_empty` and hence
`mkForall_eqStoredType` / `checkEqType.WF_type` must be ported. That would be a *net win*: the
port would drop `Lean.Expr.abstract_eq`, `.abstractRange_eq`, `.lowerLooseBVars_eq`,
`.hasLooseBVar_eq`, `PersistentArray.WF.toList'_push`, `PersistentHashMap.WF.find?_eq` and
`.toList'_insert` from `checkEqType.WF_quotReady_closed`'s axiom cone (it currently uses all of
them, and nothing else beyond `propext`/`Classical.choice`/`Quot.sound` and
`Lean.Expr.eqv_eq`, `Lean.Level.instLawfulBEqLevel`, `Lean.Syntax.structEq_eq`,
`PersistentHashMap.findAux_isSome`).
