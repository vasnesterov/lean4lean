# Handoff: the set-model layer

Scope: `Lean4Lean/Theory/SetModel/` (24 files) and `Lean4Lean/Theory/Equiconsistency.lean`.
Written at the end of a session whose brief was "inventory the 12 `sorry`s in `SetModel/`,
three of them in `SoundInduction.lean`, and attack those three first."

**That brief was wrong about the facts on the ground, and the correction is the first
section.** Everything below is separated into *machine-checked* (a build ran, or
`#print axioms` was executed, and the output is quoted) and *read off source* (analysis).

---

## 0. Correction to the brief — machine-checked

| claim in the brief | measured |
|---|---|
| `SetModel/` has 12 `sorry`s | **0.** `grep` finds no `sorry` token in any of the 24 files; only prose mentions. |
| 3 of them are in `SoundInduction.lean` | **0.** `SoundInduction.lean` is complete: `soundAbove`, `sound`, `sound_nil`, `interp_congr` all proved. |
| `Equiconsistency.lean` has 1 `sorry` | **correct** — `Equiconsistency.lean:47`, the only one in the files this stream owns. |

Measurement, reproducible:

```
$ lake build Lean4Lean.Theory
warning: Lean4Lean/Theory/Inductive/Decl.lean:390:8: declaration uses `sorry`
warning: Lean4Lean/Theory/Typing/Injectivity.lean:{222,292,326,373,402,412,464}:8: declaration uses `sorry`
warning: Lean4Lean/Theory/Typing/UniqueTyping.lean:172:8: declaration uses `sorry`
warning: Lean4Lean/Theory/Typing/ChurchRosser.lean:1706:8: declaration uses `sorry`
warning: Lean4Lean/Theory/Equiconsistency.lean:45:8: declaration uses `sorry`
Build completed successfully.
```

No `SetModel/` file appears. `docs/backward-analysis.md:227` already recorded "22 files, 0 live
`sorry`s, verified", so the brief was stale rather than measuring something else.

Also machine-checked (`#print axioms`), the whole soundness chain is `sorryAx`-**free**:

```
Lean4Lean.SetModel.soundAbove                            [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.sound                                 [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.sound_nil                             [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.interp_congr                          [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.interp_falseProp                      [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.falseProp_above_false                 [propext, Classical.choice, Quot.sound]
Lean4Lean.SetModel.exists_threshold_not_hasType_falseProp[propext, Classical.choice, Quot.sound]
```

**This does not mean the layer is done.** `SetModel/` has no `sorry`s because its debts are
carried as *unconstructed parameters and undischarged hypotheses*, not as holes. That is a
harder failure mode to see, and §2 is a new instance of it that had gone unpriced.

---

## 1. The one `sorry` this stream owns, and how much of it is needed

`Lean4Lean/Theory/Equiconsistency.lean:45`

```lean
theorem leanTT_equiconsistent_zfc_omega_inaccessibles :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent := by sorry
```

* **Nothing in the repository references it.** (`grep -rn leanTT_equiconsistent --include=*.lean`
  returns only its own declaration.) It is a *stated-but-never-used* headline theorem.
* `kernel_sound` needs **one direction only** — the upper bound
  `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent`. The lower bound (build models of
  `ZFC + n inaccessibles` inside Lean TT) is not on the path.

Added this session, proved, in the same file:

```lean
theorem inconsistent_of_upper_bound
    (h : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent)
    (hbad : ¬ leanTTConsistent) : Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰
theorem upper_bound_of_equiconsistent
    (h : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent
```

so the endgame can aim the whole `SetModel/` tower at the implication and never at the `↔`.
The `↔` is left stated with its `sorry`; it is a real theorem, just not this project's.

---

## 2. New finding: `PropSplit.Stable` was never audited, and it is not free

**This is the substantive result of the session.**

### The gap

`soundAbove` (`SetModel/SoundInduction.lean:199`) runs on six hypotheses:

```lean
(hle : env₀ ≤ envF) (henv : env₀.Ordered) (hS : L.Stable) (hC : CoherentOn M L env₀)
(hR : CtxInvariant L R) (hRd : … → R (A' :: Γ) (A :: Γ))
```

`SetModel/PropSplitAudit.lean` audits `PropSplit` in three parts — upper bound, "the fields do
real work", lower bound (`propSplitOf`, from `PropUniq ∧ PropTypeAgree`). `SetModel/
CoherentWitness.lean` audits `CoherentOn` and the `CtxInvariant`/`hRd` pair. **Nothing audits
`PropSplit.Stable`** (`SetModel/InterpSubst.lean:121`), and nothing in the tree proves it for any
`PropSplit`.

That matters because `docs/backward-analysis.md:225` states

> **So `PropSplit` is *equivalent* to `PropUniq ∧ PropTypeAgree`, not merely implied by it.**
> That is the model's entire syntactic import

and then, three lines later, lists `hS : L.Stable` among the six standing hypotheses.
`Stable` is *also* a statement about the typing judgement, so "entire syntactic import" is
measured against the wrong object. `docs/model-interface.md`'s standing label inherits the same
omission.

Note this is the exact failure signature `SetModel/LevelAssignUnsat.lean` and
`SetModel/CoherentWitness.lean` were written to catch — "a structure whose producers all consume
the same structure has never had its fields tested" — applied one level up: `LevelAssign.Stable`
was refuted and repaired, `PropSplit.Stable` inherited the repair, and the *repaired* form was
never tested for satisfiability.

### What was proved — machine-checked

New file, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`:
**`Lean4Lean/Theory/SetModel/StableAudit.lean`**.

`VEnv.PropDescend env nv` — four statements, one per `Stable` field, each the direction that
weakening/substitution does *not* supply, each restricted to the sort actually evaluating to zero:

| field | content |
|---|---|
| `sort_lift` | `Γ' ⊢ A.liftN n k : Sort u`, `u.eval ls = 0`, `Ctx.LiftN n k Γ Γ'` ⟹ `∃ v, Γ ⊢ A : Sort v ∧ v.eval ls = 0` |
| `proof_lift` | the same for a term and its type |
| `sort_inst` | `Γ ⊢ B.inst e₀ k : Sort u`, `u.eval ls = 0`, `Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ`, `Γ₀ ⊢ e₀ : A₀` ⟹ `∃ v, Γ₁ ⊢ B : Sort v ∧ v.eval ls = 0` |
| `proof_inst` | the same for a term and its type |

and the results

```lean
theorem propSplitOf_stable    (henv : env.Ordered) (hD : env.PropDescend nv) :
    (propSplitOf env nv hU hT).Stable
theorem propDescend_of_stable (hS : (propSplitOf env nv hU hT).Stable) : env.PropDescend nv
theorem propSplitOf_stable_iff (henv : env.Ordered) :
    (propSplitOf env nv hU hT).Stable ↔ env.PropDescend nv
theorem propSplitOfAgree_stable (nv) (henv) (hf : ∃ e, env.HasType 0 [] e falseProp)
    (hT : env.PropTypeAgree 0) (hD : env.PropDescend nv) :
    (propSplitOfAgree env nv henv hf hT).Stable
theorem exists_stable_propSplit … : ∃ L : PropSplit env nv, L.Stable
```

The four `←` directions are `HasType.weakN` / `HasType.instN` and cost only `env.Ordered`
(`propSplitOf_isPropAt_lift` and its three siblings).

**Collapse test, passed and recorded.** `propDescend_of_stable` is the converse, so the reduction
is an *equivalence*, not a sufficient condition: `PropDescend` cannot be dodged by a cleverer
proof against the same construction. (`PropDescend` is not vacuously true either — at `n = 0`
its `sort_lift` is trivial, but it quantifies over all `n`, and the `n ≥ 1` instances are the
content.)

### The `OnCtx` gap — the sharpest actionable item

`Theory/Typing/Strengthen.lean` already names the two statements `PropDescend`'s **`lift`** fields
are made of: `TypingStrengthening` (a lifted term typeable upstairs is typeable downstairs) and
`SortDescend` (…and at a sort). Both files import together — checked; `Strengthen.lean` is *not*
behind the `PropShadow`/`UniqueTypingN` wall of §4.

Proved this session (sorry-free, axioms `[propext, Quot.sound]` — no `Classical.choice`):

```lean
theorem sort_lift_of_strengthening  (henv) (hU : env.PropUniq nv)
    (hTS : env.TypingStrengthening nv) (hSD : env.SortDescend nv) … :
    ∃ v, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0
theorem proof_lift_of_strengthening (henv) (hT : env.PropTypeAgree nv)
    (hTS : env.TypingStrengthening nv) … :
    ∃ B v, v.WF nv ∧ env.HasType nv Γ e B ∧ env.HasType nv Γ B (.sort v) ∧ v.eval ls = 0
```

(`proof_lift` needs no `SortDescend`: validity `IsDefEq.isType` supplies the descended term's
type-of-type, and `PropTypeAgree` transports propositionhood between the two types it has
upstairs.)

**The catch, and it is the whole remaining gap on the `lift` half.** Both carry
`OnCtx Γ (env.IsType nv)` and `OnCtx Γ' (env.IsType nv)`, which `Strengthen.lean`'s statements
require and which `PropSplit.Stable` **does not have**: `Stable.prop_liftN` is stated for
arbitrary `Γ`, `Γ'`, because `interp_liftN`/`interp_inst` recurse over raw syntax and assume only
`ClosedN`. That is exactly the junk-context gap that refuted the unguarded `LevelAssign`.

So the concrete next task is: **thread `OnCtx Γ (env.IsType nv)` through
`SetModel/InterpSubst.lean`'s `interp_liftN`/`interp_inst` and into `PropSplit.Stable`'s four
fields.** `sound` already has `OnCtx Γ (env₀.IsType nv)`, so it is available at the point of use;
the question is whether the structural recursion can carry it (each `lam`/`forallE` step needs
`env.IsType nv Γ A` for the binder, which the strong judgement supplies). If it can, the two
`lift` fields of item 6 collapse to work the strengthening stream is already doing, and only the
two `inst` fields remain novel.

### What it costs, and the trade-off it exposes — read off source

* `PropDescend.sort_lift` is a **strengthening** statement. `Theory/Typing/Strengthen.lean`
  reduces general strengthening to `PiDescend` and records the general form as `sorryAx`-tainted
  through Π-injectivity; its §1 (`IsDefEqU.strengthen_of_instN`) proves strengthening only when
  the stripped context entry is *inhabited*, which `Ctx.LiftN` does not give.
* `PropDescend.sort_inst` is harder: it asks that `B` be typeable whenever `B.inst e₀ k` is.
  Candidate refuting witness, **stated, not machine-checked**, in `StableAudit.lean`:
  `A₀ = Prop → Prop`, `e₀ = fun p : Prop => p`, `Γ₁ = [Prop → Prop]`, `Γ = []`, `k = 0`,
  `B = (bvar 0) falseProp falseProp`. Instantiated, the head `(fun p => p) falseProp` has type
  `falseProp = ∀ p : Prop, p`, a Π, so the outer application types; un-instantiated, the head
  `(bvar 0) falseProp` has type `Prop`, and refuting *that* being a Π is exactly
  `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean`, open). **So a machine-checked
  refutation of `sort_inst` is blocked on the same injectivity statement `PropSplit` was
  introduced to avoid.** Reported as open, not as refuted.
* The other route into `PropSplit` pays differently. `LevelAssign.toPropSplit`
  (`SetModel/Interp.lean:447`) defines `IsPropAt` as a *function* of the syntax, and for a
  function `Stable` is just commutation with lift/inst: `toPropSplit_stable` (proved this
  session, three lines, from a new `LevelAssign.Commutes`). But `LevelAssign` needs `sort_inv`
  and `srt_uniq`, i.e. unique typing.

| route | `prop_sound`/`proof_sound` | `Stable` |
|---|---|---|
| `propSplitOf` (from `PropTypeAgree`) | free | `PropDescend` — **open**, strengthening-shaped |
| `LevelAssign.toPropSplit` | needs `LevelAssign` = `sort_inv` + `srt_uniq` | `Commutes` — plausible for a syntactic recursion |

**Headline, and it should replace the standing label.** The `PropSplit` re-parameterisation does
not remove the model's syntactic import from `SortUniq`/`sort_inv`; measured against
`PropSplit ∧ Stable` — which is what `soundAbove` consumes — it **relocates** it, out of
`prop_sound` and into `Stable`. Whether `PropDescend` is easier than `sort_inv` is an open
question this file does not answer. It is a narrowing of *one* obligation, not of the pair.

---

## 3. What the model layer still owes

Ordered by what blocks what. "MC" = machine-checked this session; everything else is read off
source and the cited file.

| # | obligation | status |
|---|---|---|
| 1 | `soundAbove`/`sound`/`sound_nil`/`interp_congr` — the thirteen-case induction | **proved**, sorry-free (MC) |
| 2 | `interp_falseProp` (`⟦∀ p : Prop, p⟧ ∅ = ∅`), branch-independent | **proved**, sorry-free (MC) |
| 3 | `falseProp_above_false` / `exists_threshold_not_hasType_falseProp` | **proved**, sorry-free (MC) |
| 4 | `VEnv.PropTypeAgree env 0` | **open**, syntax side |
| 5 | `VEnv.PropUniq env 0` | **discharged** from the goal's own `hfalse`, `PropUniqFromFalse.lean` (MC) |
| 6 | `VEnv.PropDescend env nv` (= `PropSplit.Stable` for `propSplitOf`) | **open, newly identified** (§2) |
| 7 | `M : ModelData V` — the constant assignment | **never constructed**; `Cnst.lean` has `cnstOf`/`oracleExtend` and the step lemmas |
| 8 | `CoherentOn M L env₀` for a real environment | **open**: step lemmas `coherentOn_add{Const,DefEq,ConstList,Induct}` proved; the outer induction over `VEnv.WF'` is not written |
| 9 | `AxiomsValidated` for the three prelude axioms | model-side facts proved (`propext_of_mem_UProp`, `exists_choiceFunction_mem_U`, `exists_quotient_lift`); **not wired** to the induction |
| 10 | `.induct`: per-constant `OracleOK` and per-ι-rule obligations | **open**, pushed out by `coherentOn_addInduct` |
| 11 | `NoBlock.indep` (`interpSig` well-definedness) | **open** (`model-interface.md` §2) |
| 12 | `interpSig₃_wf` / `_stage` at the translated data | reduced to soundness part 3 plus one statement per constructor; see `model-interface.md` §5 |
| 13 | `CtxInvariant L R` + `hRd` | **audited consistent**, `ctxInvariant_prop_agrees` (`CoherentWitness.lean`) |
| 14 | `Above M False → False` (a `ModelData` whose `κ` carries the chain) | **open**; `exists_inaccessibleChain` (`Inaccessible.lean:199`) supplies the chain, the assembly is not written |
| 15 | `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent` — the composition of 1–14 | **not written**; the `↔` in `Equiconsistency.lean` is its only statement, `sorry` |

Nothing in this list is *refuted*. Items 4, 6, 10, 11 are the genuinely open mathematics;
7, 8, 9, 14, 15 are construction/plumbing that no one has run because they wait on 4 and 6.

---

## 4. Import walls — checked

The brief asked whether a wall like the removed `Theory`/`Verify` one exists around `SetModel/`.

* **A hard wall does exist**, and it is a duplicate-name clash, not a design boundary:
  `import Lean4Lean.Theory.SetModel.StableAudit` followed by
  `import Lean4Lean.Theory.Typing.UniqueTypingN` fails outright —
  `environment already contains 'Lean4Lean.VEnv.PropTypeAgree' from
  Lean4Lean.Theory.SetModel.PropSplitAudit` (machine-checked). Same for `PropShadow.lean`'s
  `VEnv.PropUniq`. **No result in `Theory/Typing/{PropShadow,UniqueTypingN}` about those names
  can ever be composed with `SetModel/` until one side renames.** That is an endgame blocker,
  not a nuisance, and it should be fixed by renaming the `Theory/Typing` copies (they are the
  newer, `(U n : Nat)`-arity ones).
* `Theory/Typing/Strengthen.lean` **is** importable alongside `SetModel/` (machine-checked) —
  it is on the other side of the clash. That is what makes §2's reduction usable.
* Otherwise `SetModel/` already imports `Theory/Typing/` freely (`SoundInduction.lean` imports
  `Theory.Typing.Strong`; `PropUniqFromFalse.lean` imports `Theory.Typing.CycleConv`;
  `PropReduce.lean` imports `Theory.Typing.Lemmas`). No wall. `StableAudit.lean` compiles
  against `InterpSubst` + `PropUniqFromFalse` with no new import machinery.
* **The name collision the brief warns about is real and still stands.** `VEnv.PropUniq` and
  `VEnv.PropTypeAgree` are declared in `SetModel/PropSplitAudit.lean` (lines 105 and 119) *and*
  in `Theory/Typing/{UniqueTypingN, PropShadow}` with different statements. Everything in this
  document and in `StableAudit.lean` means the `PropSplitAudit` ones, whose bodies are:

  ```lean
  def PropUniq (env) (nv) : Prop := ∀ {Γ A u v ls}, u.WF nv → v.WF nv →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A (.sort v) → (u.eval ls = 0 ↔ v.eval ls = 0)
  def PropTypeAgree (env) (nv) : Prop := ∀ {Γ e A A' u u' ls}, u.WF nv → u'.WF nv →
    env.HasType nv Γ e A → env.HasType nv Γ e A' →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A' (.sort u') → (u.eval ls = 0 ↔ u'.eval ls = 0)
  ```

  Do not resolve a cross-tree claim about either name without quoting the body.

---

## 5. What to pick up first

1. **Thread `OnCtx` through `SetModel/InterpSubst.lean` (§2, "The `OnCtx` gap").** This is the
   cheapest thing on the list with real leverage: it is a refactor inside a file this stream
   owns, and it converts `PropDescend`'s two `lift` fields into `TypingStrengthening ∧
   SortDescend`, already-named statements another stream is working on. Do this before anything
   else in item 6.
2. **`PropDescend`'s two `inst` fields (§2, item 6).** No analogue exists in
   `Theory/Typing/Strengthen.lean`; these are novel. Two ways forward, and they should be priced
   against each other before either is attempted:
   * prove it — `sort_lift` is prop-restricted strengthening, so it should be taken to whoever
     owns `Theory/Typing/Strengthen.lean`, who already has `PiDescend`;
   * or refute `sort_inst` — the witness is written down in `StableAudit.lean`; the refutation
     needs `IsDefEqU.sort_forallE_inv`, so it becomes available the moment the injectivity
     stream closes that. **If `sort_inst` is false, `propSplitOf` is the wrong construction and
     the model needs a syntactic `PropSplit` (an `inferType`-shaped recursion) instead** — that
     is a design change, not a proof, and it should be discovered now rather than after items
     7–9 are built on top.
3. **Item 8, the `CoherentOn` outer induction.** It is the largest piece of construction that is
   *not* blocked on 4 or 6 — the step lemmas are all proved and `AxiomsValidated` is stated.
   Writing it would turn items 7, 8, 9 into one theorem and expose whether `M.cnst` can be
   defined at `nv = 0` (`backward-analysis.md` §9's RZ-1, currently unanswered).
4. **Do not** spend time on `Equiconsistency.lean`'s `↔`. Only `inconsistent_of_upper_bound`'s
   hypothesis is on the path, and that hypothesis is item 15.

---

## 6. Files touched this session

| file | change |
|---|---|
| `Lean4Lean/Theory/SetModel/StableAudit.lean` | **new.** `PropDescend`, the four weakening/substitution directions, `propSplitOf_stable_iff`, `propSplitOfAgree_stable`, `exists_stable_propSplit`, `sort_lift_of_strengthening`, `proof_lift_of_strengthening`, `LevelAssign.Commutes`, `toPropSplit_stable`. Sorry-free; `[propext, Classical.choice, Quot.sound]`. |
| `Lean4Lean/Theory/Equiconsistency.lean` | added `inconsistent_of_upper_bound`, `upper_bound_of_equiconsistent`. The pre-existing `sorry` at :45 is untouched. |

No frozen file was read for anything but its statement, and none was edited.
