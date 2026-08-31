# Class / structure satisfiability audit

Read-only audit stream. Every class and structure in `Lean4Lean/` that is used as a
hypothesis, whether it has a witness anywhere in the tree, and — for the witness-free
ones — whether it is satisfiable.

Snapshot: `02e9802`, working tree with live edits in `Experimental/ParamsInstance.lean`,
`Experimental/SExpr.lean`, `Experimental/ShapeLogRel.lean`,
`Theory/Typing/ChurchRosser.lean`. 2026-08-23. Six streams were editing during the pass;
`Experimental/ShapeLogRel.olean` and `Theory/Typing/ChurchRosser.olean` went missing
mid-pass, so numbers for those two modules are source-level only.

---

## Answer, up front

**No new unsatisfiable class was found.** Two already-known-defective ones are confirmed
still open, and one previously-suspect class (`VEnv.Params`) is now confirmed *satisfiable*
by a compiling witness. Six mainline Props that had never been witnessed are now
machine-checked satisfiable.

The audit's real result is a **negative** one, and it is structural rather than logical:

> `Theory/SetModel/` rests on `SetModel.LevelAssign`, and **no `LevelAssign` has ever been
> constructed, for any environment**. Constructing one is provably equivalent to
> `IsDefEqU.sort_inv` plus unique typing — and `IsDefEqU.sort_inv` is a `sorry`
> (`Theory/Typing/Injectivity.lean:84`). Every other unwitnessed structure in the model
> stream — `ModelData`, `CoherentOn`, `AxiomsValidated`, `LevelAssign.Stable`,
> `IndSignature`, `IndSignature.WF`, `IsStageSignature`, `IsSubsingletonSignature`,
> `CtxInvariant` — is downstream of it, so the whole set-model stream is un-instantiated at
> a single pinch point rather than at nine.

That is not vacuity: the statements are conditional, not false. But nothing in
`Theory/SetModel/` (547 declarations, 68 source lines mentioning `LevelAssign`, 179
environment constants whose type mentions it) is currently known to apply to *any*
environment, including the empty one.

---

## Method, and how much to trust it

1. **Enumerate.** `grep -rn` over `Lean4Lean/` for `class`/`structure` declarations: **98
   in all**, of which **6 are classes** and **90 are structures outside `Tests/`**.
2. **Witness detection — machine, not grep.** A Lean metaprogram (`#census`) walks
   `env.constants` and, for every structure `S` declared under `Lean4Lean`, collects the
   declarations whose type's conclusion (after stripping `∀`/`let`/`mdata`) has head `S`,
   excluding `S`'s own projections, recursors, `noConfusion` and `mk`/`injEq`/`ext`
   auto-decls. Column **WIT**. It also counts declarations whose type *mentions* `S`
   (column **USE**), as a proxy for how much depends on it.
3. **Adjudicate WIT=0 by hand**, then machine-check a witness where one plausibly exists.

**Known false negatives of WIT** (stated because a "no witness" claim is only as good as
the detector):

* **Notation hides the head.** `VEnv.LE`, `EquivManager.LE`, `VEnv'.LE`,
  `SExpr.Classifier.LE` all report WIT=0 because their witnesses are stated as `env ≤ env`,
  whose head is `LE.le`. All four have a `.rfl` lemma. **Four of the twelve mainline WIT=0
  hits were this.**
* **Theorem values are not loaded from `.olean`.** `ConstantInfo.value?` returns `none` for
  every imported theorem in this configuration (checked directly on
  `Bridge.hasPrimitives_empty`), so a planned second signal — "does any proof term mention
  `S.mk`?" — is void for Props and was discarded. WIT is the only automated signal.
* **Anonymous constructors inside larger proofs** are not counted; WIT counts only
  declarations whose *conclusion* is `S`.

WIT is therefore a **trigger**, not a verdict, exactly as the brief says. Every verdict
below is either a compiling witness or a stated inference.

---

## Verdicts: instance-free classes and structures

Ordered by consumers (USE). Only entries with WIT=0, or WIT>0 with no *ground* witness
(every producer takes an `S` as input), are listed; the 60-odd structures with ordinary
ground witnesses are omitted.

### Mainline (`Theory/`, `Verify/`)

| Class / structure | Where | USE | Verdict | Evidence |
|---|---|---|---|---|
| `VEnv.Params` | `Theory/Typing/ChurchRosser.lean:12` | 494 | **satisfiable** (trivially) | machine-checked: `paramsTrivial` at `env := .empty`, `Pat := fun _ _ => False`; all eight fields vacuous. Axioms: `propext, Quot.sound`. **But no instance exists at any non-empty environment** — see ranked unknown #2. |
| `SetModel.LevelAssign` | `Theory/SetModel/Interp.lean:251` | 179 | **unknown — the pinch point** | Only producer is `LevelAssign.mono` (`LevelAssign → LevelAssign`). `lvl_sound`/`srt_sound` are `IsDefEqU.sort_inv` and unique typing in functional form (the structure's own docstring says so); `sort_inv` is `sorry` at `Injectivity.lean:84`. Not satisfiable even at `env := .empty` by a constant assignment: `HasType .empty nv Γ (.sort .zero) (.sort (.succ .zero))` holds, so `lvl` cannot be constant. |
| `SetModel.IndSignature` | `Theory/SetModel/Inductive.lean:123` | 172 | **satisfiable [inferred], unwitnessed** | Plain data + four definability instances; a constant-function signature should satisfy them. Nothing in the tree builds one. |
| `SetModel.ModelData` | `Theory/SetModel/Interp.lean:229` | 145 | **satisfiable [inferred], unwitnessed** | Three data fields, no Props. Every producer (`defExtend`, `oracleExtend`) takes a `ModelData` or a `LevelAssign` as input. Downstream of `LevelAssign` in practice. |
| `SetModel.IndSignature.WF` | `Theory/SetModel/Inductive.lean:149` | 37 | **satisfiable [inferred], unwitnessed** | One field, vacuous when `S.Q = ∅`. Downstream of `IndSignature`. |
| `VInductDecl'.WF` | `Theory/Inductive/Decl.lean:370` | 36 | **satisfiable — machine-checked** | `fooDecl_WF` below. Was the highest-USE mainline Prop with no witness at all. |
| `SetModel.IsStageSignature` | `Theory/SetModel/IndStage.lean:43` | 32 | **satisfiable [inferred], unwitnessed** | Four membership clauses; vacuous/trivial for a degenerate signature. Downstream of `IndSignature`. |
| `SetModel.LevelAssign.Stable` | `Theory/SetModel/InterpSubst.lean:117` | 24 | **unknown** | Downstream of `LevelAssign`: cannot be stated without one. |
| `SetModel.CoherentOn` | `Theory/SetModel/InterpSound.lean:716` | 19 | **unknown** | WIT=6, but **every one of the six is an inductive step** taking a `CoherentOn` as input (`coherentOn_defConst`, `coherentOn_defEq`, `coherentOn_addConstList`, `coherentOn_addDefEq`, `coherentOn_addConst`, `coherentOn_addDefEqFold`). No base case exists. A base case at `env := .empty` looks easy (`const_congr` by `Above.pure rfl`, the rest vacuous) but still needs an `L : LevelAssign`. |
| `SetModel.CtxInvariant` | `Theory/SetModel/InterpSound.lean:429` | 15 | **unknown** | Downstream of `LevelAssign`/`ModelData`. |
| `Verify.PrimitiveResult` | `Verify/Environment/Boundaries.lean:21` | 11 | **satisfiable** [inferred, one line] | All three fields are guarded by `allow = true`; `allow := false` discharges every one. |
| `SetModel.IsSubsingletonSignature` | `Theory/SetModel/Inductive.lean:633` | 10 | **satisfiable [inferred], unwitnessed** | Both fields vacuous when `S.Q = ∅`. Downstream of `IndSignature`. |
| `TypeChecker.NatFacts` | `Verify/Primitive.lean:1003` | 9 | **satisfiable [inferred], unwitnessed** | WIT=2 but both producers take a real `TrExprS`/`NatFacts` input. Genuinely satisfiable whenever the checker has seen `Nat`; no ground instance because none is needed. |
| `SetModel.AxiomsValidated` | `Theory/SetModel/InterpSound.lean:1007` | 5 | **unknown** | One field, vacuous for `ds := []` — but needs an `L : LevelAssign`. Downstream. |
| `VEnv.LE`, `EquivManager.LE` | `Theory/VEnv.lean:35`, `Verify/EquivManager.lean:169` | 6, 6 | **satisfiable** | `LE.rfl := ⟨id, id⟩` at `VEnv.lean:41` / `EquivManager.lean:175`. WIT false negative (the `≤` notation). |
| `VEnv.IsStructure` | `Theory/Inductive/Structure.lean:478` | 46 | **satisfiable — machine-checked** | `fooEnv_IsStructure` below. Previously WIT=1 with only `IsStructure.mono`, i.e. no ground witness. |
| `VIndType.WF`, `VIndCtor.WF`, `VIndField.WF` | `Theory/Inductive/Decl.lean:341/318/269` | 23, 34, 13 | **satisfiable — machine-checked** | All three exercised by `fooDecl_WF` below. Previously WIT=1 with only `.mono` each. |
| `VInductDecl'.RecCtx` | `Theory/Inductive/Lemmas.lean:1010` | 33 | **satisfiable — machine-checked** | `fooRecCtx` below. |
| `VInductDecl'.IotaCtx` | `Theory/Inductive/Lemmas.lean:3037` | 33 | **satisfiable** [inferred] | Same route as `RecCtx` via `WF.iotaCtx` (`Lemmas.lean:3557`), which needs only `D.WF env` + `Ordered` + the three `addInd*` equations — all supplied by the `fooDecl` witness. Not separately compiled. |
| `VIndCtor.Interface` | `Theory/Inductive/Lemmas.lean:1745` | 15 | **satisfiable** [inferred] | `VIndCtor.WF.interface` (`Lemmas.lean:1767`) takes `Ordered env` + `WF` + the stored-constant equation; all three hold for `fooEnv`. Not separately compiled. |
| `VInductDecl'.ProjClosed` | `Theory/Inductive/Structure.lean:271` | 26 | **satisfiable** [inferred] | Sole producer `IsStructure.projClosed`; `IsStructure` is now witnessed. |
| `VEnv.HasPrimitives` | `Verify/Typing/Expr.lean:248` | 97 | **satisfiable** | ground witness `Bridge.hasPrimitives_empty` (`Verify/Bridge.lean:81`). Listed only because the discarded `mk`-scan reported it as unwitnessed — a detector artefact, not a finding. |

Pure data structures with WIT=0 (`VDefVal`, `TypeChecker.Context`, `TypeChecker.State`,
`AddInductive.Context`, `ElimNestedInductive.Result`, `SExpr.IProp`, `VEnv'.VConstant`,
`VEnv'.VDefEq`, `VConstVal`, `StructureExamples.TP`) are satisfiable by construction — they
are records of unconstrained fields, built inline with `⟨…⟩` rather than by a named
producer. No verdict needed.

### `Experimental/`

| Class / structure | Where | USE | Verdict |
|---|---|---|---|
| `SExpr.ParamsExtra` | `Experimental/SExpr.lean:695` | 9 | **unsatisfiable at any realistic environment — confirmed still open.** `extra_pat` matches `Pattern.MatchesS` against the *unpeeled* `.instL ls (.mk df.lhs)`, and every rule with parameters is λ-abstracted (`quotDefEq`'s lhs is `fun α r β f c a => …`). The mainline copy in `ChurchRosser.lean` was cured by λ-peeling; this one was not. Documented at `Experimental/ParamsInstance.lean:37-43`. Formally satisfiable only where `env.defeqs` is empty or all-δ. |
| `SExpr.CtorBundle` | `Experimental/SExpr.lean:782` | 29 | **uninhabited for `Prop`-valued constructors — confirmed still open.** Field `hu0 : u ≠ .zero` is false for `Eq.refl : ∀ {α : Sort u} (a : α), a = a`, whose type's sort is `imax (u+1) (imax u 0) = 0`; yet `Eq.refl` must be `classify`-ed `.ctor` because `Eq.rec`'s ι-rule matches on it. `IsDefEqStrong.const` demands `∀ cl, CtorBundle c cl`. Documented in the structure's own docstring; not a soundness hole because `IsDefEq.strong` is a `sorry`. |
| `Lean4Lean.Params` (shape model) | `Experimental/SExpr.lean:25` | 550 | **satisfiable for an arbitrary `env.WF`** — `paramsOfWF` (`Experimental/ParamsInstance.lean:143`) discharges all eight fields. This is the one class that stopped being instance-free during the session. |
| `SExpr.LogRel` | `Experimental/MoreStepIndexed.lean:371` | 20 | **unwitnessed for a mechanical reason**: the file has a `#exit` at line 420, and the two producers (`TypeEqS` at :421, `TypeEq` at :443) are *after* it, so they are never elaborated. 69 of the file's 489 lines are dead. |
| `SExpr.Classifier.LE` | `Experimental/MoreStepIndexed.lean:353` | 6 | **satisfiable** — `Classifier.LE.rfl` at :358. WIT false negative. |
| `VEnv'.LE` | `Experimental/Stronger.lean:32` | 6 | **satisfiable** — same `≤`-notation false negative. |
| `Lean4Lean.Typing` | `Experimental/NormalEq.lean:20` | 322 | **satisfiable [inferred], unwitnessed.** A 40-field record of the typing rules; taking `IsDefEq := VEnv.IsDefEq env U` satisfies it field-for-field. File is headed `-- TODO: remove, this is now part of ChurchRosser.lean`, so the 322 consumers are all inside a module marked for deletion. Low priority. |
| `SExpr.StrongSoundEq`, `SExpr.LogRelBase`, `SExpr.LogRel` (ShapeLogRel) | `Experimental/ShapeLogRel.lean:5715/6406/6412` | — | **satisfiable [source-level only]** — `StrongSoundEq.rfl` (:5731), `StrongSoundEq.mk'` (:5743), `LR0 : LogRel Γ 0` (:6448). Not machine-checked: the module's `.olean` was absent throughout the pass. |

---

## Ranked unknowns

By how much depends on them.

**1. `SetModel.LevelAssign` — gates the entire set-model stream.**
547 declarations in `Theory/SetModel/`; 179 environment constants whose type mentions
`LevelAssign`; every other unwitnessed model structure is downstream. What is needed:
`IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean:84`, `sorry`) and the term-level
companion, then `Classical.choice`. See `docs/research-sort-inv.md`, which independently
concludes there is no shorter route. **The audit's contribution here is that the dependence
is not diffuse — it is one structure, and constructing it closes all nine.**

**2. `VEnv.Params` at a non-empty environment.**
USE=494. Satisfiable, but the only compiling witness is `env := .empty` with `Pat` false,
so every consumer of `[VEnv.Params]` — `NormalEq.parRed`, `IsDefEq.church_rosser` — is
currently known non-vacuous only for the empty environment. The route to a real instance
is visible and short: `Theory/Typing/PatternRules.lean` already supplies `Pat`,
`Pat.simple` and `Pat.uniq`, and `Experimental/ParamsInstance.lean:143` shows five of the
eight mainline fields can be read off an arbitrary `env.WF`. What remains is the three
mainline-only fields — the semantic `pat_wf`, `pat_app_l_uniq`/`pat_app_uniq`, and the
λ-peeled `extra_pat`. **This is the highest-value instance still missing, and it is not
blocked on a `sorry`.**

**3. `SExpr.ParamsExtra`.** USE=9 but it gates the shape-model route to
`IsDefEqU.forallE_inv`, which is why `paramsOfWF` exists at all. Unsatisfiable as stated.
The mainline fix (λ-peeling) transfers verbatim; nobody has applied it.

**4. `SExpr.CtorBundle.hu0`.** USE=29, and it is the second independent reason
`IsDefEq.strong` is false. The fix named in the source is to drop `hu0` and give
`LE_Interp.build_spine` a `.bot` branch for `Prop`-valued inductives.

**5. `SetModel.IndSignature` and its three Props.** Satisfiable-looking but unwitnessed; a
single degenerate signature (`Q := ∅`) would witness `IndSignature`, `IndSignature.WF`,
`IsStageSignature` and `IsSubsingletonSignature` at once and cost perhaps thirty lines. Not
attempted here because the definability side-conditions need `Foundation` API I did not
audit.

---

## Machine-checked witnesses

All compile against the working tree with `lake env lean`; each ends in `#print axioms`
showing no `sorryAx`. Scratch paths (nothing was written into the repo):

`/tmp/claude-1000/-home-vasilii-lean4lean/4000239b-99f6-4f08-ac38-da08c157a78e/scratchpad/`

| File | Proves | Axioms |
|---|---|---|
| `W_Params.lean` | `paramsTrivial : VEnv.Params` at `env := .empty` | `propext, Quot.sound` |
| `W_Ind3.lean` | `fooDecl_WF : fooDecl.WF .empty` — witnesses `VInductDecl'.WF`, `VIndType.WF`, `VIndCtor.WF`, `VIndField.WF` | `propext, Quot.sound` |
| `W_Struct3.lean` | the above, plus `∃ e, VEnv.empty.addInduct' fooDecl = some e` by `rfl`, `fooEnv_IsStructure : VEnv.IsStructure …`, `fooRecCtx : ∃ e, fooDecl.RecCtx e` | `propext, Classical.choice, Quot.sound` |

`fooDecl` is `inductive Foo : Prop | mk : Prop → Foo` — one `Prop`-valued type, one
constructor, one non-recursive field, no parameters, no indices, `isLE := false`. It is
deliberately the *smallest* declaration that still exercises `VIndField.WF.pos`,
`VIndField.WF.level` (`imax 1 0 = 0` — the `Prop` case), `VIndCtor.WF.result` (via
`constDF` in the staged environment), and `IsStructure.decl`.

**Recommendation: land `W_Struct3.lean` as a regression test**, next to
`Theory/Inductive/DeclExamples.lean`. That file currently checks ~60 `rfl` facts about
`eqDecl`/`natDecl`/`accDecl` — binder counts, canonical types, ι-rules — but **proves no
`WF` for any of them**, which is why `VInductDecl'.WF` had never been tested against a
concrete declaration despite 36 consumers. Route to that file's owner.

---

## Incidental findings

1. ~~**Duplicate declaration name.** `Lean4Lean.VEnv.addDefEqs_le` is declared twice…~~
   **FIXED (`3e13a0f`), and this entry was stale.** The clash — along with four siblings —
   was deduplicated, none of them renamed; `Verify/InductFlip.lean:325` records it. The
   `Theory`/`Verify` import wall it created is down, which is why the whole-tree census and
   `Experimental/ConeJoin.lean` now run at all.

   Retained here because the *check* it motivated is now permanent:
   `scripts/dup-names.lean` imports `Experimental.ConeJoin` so that a collision between the
   two cones surfaces as an import error rather than a silent wall, and it is part of the
   pre-commit set. Re-verified 2026-08-31: no duplicate `Lean4Lean` declaration across the
   joined cone, and no `addDefEqs_le` declaration remains in either
   `Theory/Typing/DeltaUnique.lean` or `Verify/Environment/Lemmas.lean`.

2. **`#exit` at `Experimental/MoreStepIndexed.lean:420`** leaves 69 lines (including the
   only two producers of `SExpr.LogRel`) unelaborated. The only `#exit` in the tree.

3. **`Experimental/` modules are not mutually importable.** Still true (re-verified
   2026-08-31), but the names were recorded wrongly here: they are `Classifier` and
   `Classifier'`, **not** `SExpr.Classifier`. `Classifier'` is a `structure` in
   `CoinductiveLogRel.lean:15` and a declaration of the same name in `StepIndexed.lean`;
   `Classifier` is `def`'d in `CoinductiveLogRel.lean:18` and again in
   `StepIndexed.lean:11`. Plus `WHRed` (Thierry vs Thierry2). Expected for a scratch
   directory; recorded so nobody plans a combined `Experimental.lean` root. Note these do
   **not** show up in `scripts/dup-names.lean`, which walks the joined *cone* — `Experimental/`
   modules outside `ConeJoin.lean` are not in it.

4. ~~**`ConstantInfo.value?` is `none` for every imported theorem** in this build
   configuration.~~ **WRONG AS STATED — and this entry is a trap that has since cost real
   time.** `value?` takes an `allowOpaque` argument defaulting to `false`, and it is *that*
   default, not the build configuration or the import, which hides theorem values. Measured
   on an imported theorem (`VEnv.NormalEq.defeq`):

   | call | result |
   | --- | --- |
   | `ci.value?` | `none` |
   | `ci.value? (allowOpaque := true)` | `some …` |

   So no audit tool needs the modules elaborated from source; it needs one keyword argument.
   The failure mode is silent and looks like success: a dependency walk without
   `allowOpaque := true` sees **types only**, so every theorem's cone comes back clean and a
   `sorry`-tainted proof measures as `sorry`-free. That is exactly what happened on
   2026-08-31 to an ad-hoc cone script written without reading
   `scripts/hole-cone.lean`, whose own header documents the trap.

   **Rule: cone measurements go through `scripts/hole-cone.lean`'s `deps`.** Do not write a
   competing walker; if you must, copy `deps` verbatim.
