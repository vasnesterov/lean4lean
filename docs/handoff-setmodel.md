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

## 7. Session of 2026-09-01: the recorded obstruction was misattributed, and the `.induct` residual closed twice

**Written by the orchestrator from the stream's reports, not by the stream** — that agent was killed
by an API error immediately before writing this section, having just noted that two of the line
numbers it was about to use were off by one. Every claim below is machine-checked in the named
declaration and the headline theorems were independently re-verified with `#print axioms`. Per
ledger row 90, citations here name **declarations**, not lines.

### 7.1 The obstruction on record was wrong at the level of a type

§2 of this file, and `StableAudit.lean`, recorded a candidate refutation of `PropDescend.sort_inst`
and said it was blocked on `IsDefEqU.sort_forallE_inv`, flagged as **stated but not
machine-checked**. It was briefed to three separate streams on that basis. **It does not work, and
the blockage is not `sort_forallE_inv`.**

The note claimed `B.inst e₀ 0`'s inner head `(fun p : Prop => p) falseProp` "has type
`falseProp = ∀ p : Prop, p`, a Π-type, so the outer application types". **Its type is `Prop`** —
exactly like `(bvar 0) falseProp` at `Γ₁`. In `Theory/SetModel/InstDescendAudit.lean`:

- `w_head_unsubst`, `w_head_subst` — the two typings, both at `.sort .zero`;
- `w_head_inst` — the instantiation identity, by `rfl`;
- `w_types_of_sortPiConv` — **one** `Prop ≡ Π` hypothesis derives **both** typings.

So the witness is **symmetric**: whatever settles `sort_forallE_inv` settles both sides together,
and **no disposition of it can make this witness refute `sort_inst`.** `sort_inst` remains open;
what is gone is the recorded reason for believing it refutable — and with it the reason to feed a
`sorryAx`-tainted lemma into this corner at all. Corrected in place in `StableAudit.lean`.

*Lesson, and it is the orchestrator's:* a claim flagged "stated but not machine-checked" in a file
this layer owns was quoted as an obstruction three times. **A `[not machine-checked]` flag is a
request to check, not a citation.**

### 7.2 The level condition in the residual is free

`SortInstDescend0` is `sort_inst` with the conclusion's `v.eval ls = 0` dropped.
`sortInstDescend_iff` proves the two **equivalent** given `Ordered` and `PropUniq` — both of which
`modelFits_of_propSplitUp_inputs` already assumes. Bounded both ways as ledger rows 51/77b/82b
demand: `→` is projection; `←` forward-substitutes the descended typing and compares the two sorts,
which works because `PropSplitAudit.PropUniq` is **pointwise in `ls`** rather than the `≈` form.
`sortInstDescend0_nonvacuous` checks neither side is empty, at `k = 0` so the substitution genuinely
substitutes.

**So the entire content of the residual is typeability descent. None of it is about levels.**

### 7.3 The model side and the syntactic side do share a residual — but not the one on record

Walking `SortInstDescend0`'s cases:

| case | status |
| --- | --- |
| `.sort`, `.const`, `.bvar i (i ≠ k)` | free — substitution is the identity, or the lookup transports |
| **`.bvar k`** | **uniqueness of typing for `e₀`** |
| `.forallE`, `.app`, `.lam` | **inversion at a sort** |

`sortInstDescend0_bvar_forces_sort` is the machine-checked half: from `e₀ : A₀` and `e₀ : Sort u`
the residual demands a sort for `.bvar 0` at `A₀ :: Γ₀`, whose only type is `A₀.lift`
(`bvar0_type_is_lift`). That is `UniqueTyping`-strength. The three syntactic cases need inversion
because the premise's derivation need not have the matching rule at its root — `defeqDF`, `trans`
and `proofIrrel` all apply.

Both are downstream of the same injectivity work as `sort_forallE_inv` but are **different
statements** from it. **No equivalence with `UniqueTyping` is claimed** — only that one instance of
the residual demands its content.

*Bearing of concurrent work, stated as a question rather than an answer:* the syntactic side's sort
residual has since been reduced to `SortMidNonSort` + `SortNotProof`, both *descent* statements, and
`docs/critical-path.md` §"The convergence" prices those as instances of one fact plus
Church–Rosser. Whether that reaches this residual has **not** been checked. Do not assume it does.

The orchestrator's suggested lever — `DeclRules.WF.instL_lhs_ne_forallE` / `WF.piPi_extra_closed`,
on the grounds that the model side always has `VEnv.WF` — **is not the lever**: the `extra` case was
never the residual on either side, and `VEnv.WF` does not supply inversion.

### 7.4 The `.induct` residual: closed at the small eliminator, then at the large one

Both in `Theory/SetModel/UnitOracleWitness.lean` and `Theory/SetModel/UnitOracleLarge.lean`, and
both `Above`-free at arbitrary `κ` — every proof through `Above.pure`, **no `κ` chosen anywhere**.

- **Small.** `unitDecl_WF` (`inductive Unit1 : Prop | mk`) is `WF` over the **empty** environment —
  unlike `boxDecl`, no ambient constant is needed — and `inductOracleOK_unit` proves both
  `InductOracleOK` fields. Anti-vacuity both ways: no telescope that could be empty,
  `interp_Unit1_ne_empty`, a hypothesis-free true motive, a non-empty minor domain, non-nil
  ι-rules.
- **Large.** `unitDeclLE_WF` is the block Lean **actually** declares (`isLE := true`, permitted here
  because the constructor has no fields), and `inductOracleOKL` proves both fields at **both level
  slices**. `recFnL_beta` makes the ι-rule's left side really apply the oracle's value and reduce to
  the minor premise; the right side is the η-expanded β-redex `iotaRule` builds, reducing to the
  same. **Nothing about the rule ever wanted the value to be `•`.** And
  `interpL_unitRule_sides_of_zero`: at a `Prop` instantiation every binder of `recType` is
  propositional again, so large elimination **into `Prop`** collapses to the small case. Both slices
  non-empty (`exists_eq_zero_level`, `exists_ne_zero_level`), so the split is real.

**The finding to keep: the oracle's level branch is FORCED, not a convenience.**
`pt_not_mem_interpL_recType_of_ne` excludes `•` at `n ≠ 0` *given any inhabitant of the motive
space*, while at `n = 0` the type is a proposition whose only element is `•`. So **no level-uniform
oracle value exists for a large eliminator** — the model-side shadow of `Prop`'s collapse. The
inhabitant hypothesis is load-bearing, not cosmetic: a junk `κ` with `U κ n = ∅` empties the motive
space and `recFnL κ n` collapses to `∅ = •`, forcing nothing. Hence the statement is **conditional**
rather than at a chosen `κ`.

### 7.5 Two forecasts from this layer's own docstrings, both wrong in the same direction

`InductOracleWitness.lean` predicted `SetModel/IndInterp.lean` would be needed — first for the small
case, then for the large one. **Both false, both corrected in place.** What needs the fixed point is
a block with **recursive fields**, and neither `unitDecl` nor `unitDeclLE` has any. Four reusable,
`interp`-free lemmas carried the large case instead, of which one removes a real structural
obstacle:

- `mkLam_mem_mkForallType_of_dom` — lands `mkLam` in `mkForallType` when the domains merely **agree
  at the valuation**. `InterpSound.mkLam_mem_mkForallType` demands the same *term*, which is
  impossible here: **the oracle's value cannot mention `interp`, because `interp` reads `M.cnst`.**
- `mkForallType_singleton_const` — a `∀` over a singleton domain with constant codomain **is** the
  function space.
- `mem_mkForallType_of_graph`, `mkLam_ext`.

**The frontier, re-recorded:** not large elimination, not "an inhabited domain" — both closed. It is
a block with **recursive fields** (needs `IndInterp.lean`) or with **parameters/indices**.

### 7.6 The model import, unhedged

`modelFits_of_propSplitUp_inputs` needs `Ordered`, `PropUniq 0`, `PropTypeAgree 0`,
`InstDescendUp 0` and `OracleFits`.

- `PropTypeAgree 0` is **irreducible**: `NotProofNoModel.nonempty_propSplit_iff_agree` makes
  `Nonempty (PropSplit env nv)` equivalent to `PropUniq nv ∧ PropTypeAgree nv`, so **no choice of
  predicate removes it**, the `propSplitUp` route included. It is the real unique-typing content.
  Do not spend a round there.
- `InstDescendUp 0` is **not closed** (§7.2, §7.3).
- Input A is **discharged** — `inaccModelInput` is a theorem (`ModelExists.lean`).
- `ModelFitsLeanInput` cannot be refuted by an `.axiom` step any more
  (`axiom_mem_pureOverPrelude`), so any refutation must come from an `.induct` step at a `WF` block
  with an uninhabited declared constant — which is why §7.4 matters beyond bookkeeping. **But
  `ModelFitsVacuous.lean`'s own disclaimer lists TWO unknowns and this is only the second.** The
  first is independent and untouched: `ModelFits` demands a `PropSplit env 0` with `L.Stable`, and
  **the tree exhibits none unconditionally** — `exists_stable_propSplit` takes `PropTypeAgree 0` and
  `PropDescend nv`, i.e. exactly the open inputs.
- One thing that *looks* like a vacuity and is not: `exists_stable_propSplit`'s hypothesis
  `∃ e, HasType 0 [] e falseProp` appears to demand an inhabitant of `∀ p : Prop, p`, i.e.
  inconsistency. It is the **goal's own** hypothesis — `kernel_sound` is proved by refuting "the
  kernel accepts a proof of `False`" — so it is free wherever the reduction is consumed.

### 7.7 Tried and failed, with the failing step

1. **The recorded `sort_inst` refutation** — symmetric; §7.1. *Three briefs pointed at a
   non-obstruction.*
2. **`WF.instL_lhs_ne_forallE` as the lever for `InstDescendUp`** — the `extra` case was never the
   residual, and `VEnv.WF` does not supply inversion.
3. **`IndInterp.lean` for `Unit1`, twice** — §7.5; the fixed point is needed only for recursive
   fields.
4. **`sort_not_proof` via the interpretation** — `NotProofNoModel.sortNotProof_of_propSplit` already
   gets it from `PropSplit` with no interpretation, dominating any model construction.
5. **Structure-level two-way bounds** — ledger row 11a is this directory's own case:
   `inductOracleOK_empty` sits at the block with *no* type formers, whose `allConsts` is `[]`, so
   its `staged` is `True` and the bound said nothing about the field that was refuted. **Bound field
   by field.**

### 7.8 Traps of this directory

- **`Above M P := ∃ m, IsInaccessibleChain m M.κ → P`** is vacuously true at a `κ` that fails to be
  a chain, and such a `κ` exists (`not_isInaccessibleChain_const`). Positive bounds must factor
  through `Above.pure`, be wrapper-stripped, or be `∀ κ` — **never** choose one. (Audited: no claim
  in the tree exhibits the worthless shape.)
- **`interpCtx M L [∀ p : Prop, p]` is empty in every model**, so a hypothesis quantifying over
  `ρ ∈ interpCtx` for all `Γ` can be vacuous (`sortInvSupply_vacuous`).
- The field is **`CoherentOn.const_type`** (`Coherent` is docstring-only) and it constrains `M.cnst`
  by **membership only**.
- **`coherentOn_witness` certifies coherence at an environment the induction never visits** — prefer
  `axEnv_wf'` or `boxDecl_history`.
- `InaccChainOmega.lean` installs two global instances; `ModelExists.lean` has **four** `instance`
  declarations though its docstring says three.
- **Never feed `IsDefEqU.sort_forallE_inv` into anything meant to be clean** — `sorryAx`, and its
  cone contains both injectivity holes.
- A **deliberate** duplication: `falsePropTy`/`falseProp_prop` in `InstDescendAudit.lean` duplicate
  `Companion.lean`'s `falseProp_hasType` (identical proof). Pulling `Theory/Inductive/Companion.lean`
  onto the model side to share two lines is the worse trade; the docstring records this. Do not
  "fix" it.

### 7.9 What to pick up first

**`InstDescendUp 0`'s `.bvar k` case**, and treat it as the uniqueness-of-typing instance it is
(§7.3) rather than as a descent problem — then decide, on evidence, whether the syntactic side's
`SortMidNonSort`/`SortNotProof` reduction reaches the three syntactic cases. That question is open
and this file does not answer it.

**Do not** re-attack `PropTypeAgree 0` (irreducible), the `sort_inst` refutation (§7.1), or
`IndInterp.lean` for a block without recursive fields (§7.5).

### 7.10 Measured / read / not run

**[measured]** this session: `#print axioms` on every new declaration in
`InstDescendAudit.lean`, `UnitOracleWitness.lean`, `UnitOracleLarge.lean` — `[propext]`,
`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**; guards 1–3
all ✓ at each build.

**[read]** off source, not run: the collision scans for the new files were plain greps over
declaration headers, reported as such. One of them found the real `falseProp_hasType` clash.

**[not run]** by the stream: `scripts/sorry-census.lean` and `scripts/dup-names.lean` — the tree was
not quiescent. The orchestrator ran them at a quiescent commit: **census 13**, dup-names clean,
build green. The Kernel Arena was **not** run this session; no implementation file changed, so the
last recorded result stands — but *expected is not measured*.

---

## 8. Session of 2026-09-02: the `←` half named, and its witness gap measured

Brief: *target the `←` half of `Equiconsistency.lean`'s `↔` as a separately named theorem;
prove as much as is reachable; leave the `↔` open.*  Done, plus the anti-vacuity measurement
that turns out to be the substantive result.

Everything below is **[measured]** unless marked `[read]`.  New file:
`Lean4Lean/Theory/SetModel/UpperBound.lean` (365 lines, 20 declarations, sorry-free).

### 8.0 Audit of the five claims I was asked to check against the tree

| claim as briefed | verdict |
|---|---|
| `CnstRecursion.coherentOn_cnstOf` runs the full `VEnv.WF'` recursion with **six of seven** `VDecl` forms discharged; which is open? | **The recursion is a complete theorem — no form is left as a goal.** All seven are handled: `.def`/`.opaque`/`.example` outright, `.unsafeDef` *refuted* by `noUnsafe`, `.axiom`/`.quot`/`.induct` from the `OracleFits` **hypothesis**. What is open is not a form but a *field* of that hypothesis at `.induct`: `InductOracleOK`. `stagedOcc_allConsts` closes the `.induct` occurrence side-condition; inhabitation is what is not discharged. So "six of seven discharged" is the wrong shape of statement — the file's own §"What is proved outright" table says `.induct`'s **occurrence** condition is proved and its **inhabitation** is not, which is correct |
| `InductOracleOK` is a two-field structure | **correct** — `consts` and `rules` (`CnstRecursion.lean:504`), bounded field by field in `InductOracleAudit.lean` §5 |
| `consts`' positive bound closed twice (`inductOracleOK_zero`, `inductOracleOK_unit`), large eliminator closed (`inductOracleOKL`) | **correct**; `inductOracleOK_zero` (`InductOracleWitness.lean:270`), `inductOracleOK_unit` (`UnitOracleWitness.lean:687`), `inductOracleOKL` (`UnitOracleLarge.lean:1206`) all exist |
| the `rules`-negative cell is "bounded tighter but not closed", **and its wording is probably unachievable** | **the source has already been corrected and the ledger row is stale.** `InductOracleAudit.lean` §5's `rules` row carries "**Reworded 2026-09-01: the previous wording asked for the wrong thing**". The right wording, verbatim from the source and confirmed here: a `WF` block's ι-rules are well typed, so *a correct model must satisfy `DefEqOK` at each of them — a refutation there would refute the model, not the field*; the honest control is refutability of the field's **body** at a `VDefEq` of our choosing, which is `not_defEqOK_falseType`. So: the briefed wording is indeed unachievable, and the achievable one is already in place |
| `AxiomsValidated` fully closed, `hκ` by `InaccChainOmega.exists_inaccessibleChain_omega` | **correct.** `AxiomsValidatedAudit.axiomsValidated_of_coherentOn` takes `hκ`; `axiomsValidatedAbove_of_coherentOn` is the `hκ`-free half. Both present, both bounded (`not_axiomsValidated_falseProp`, `axiomsValidated_extAx`) |
| `IsDefEqU.sort_inv` listed "open, one `sorry`" but absent from the 13-hole census — resolve | **the row is stale in form and right in substance.** `IsDefEqU.sort_inv` (`Injectivity.lean:565`) has **no `sorry` of its own** — it is `sort_inv_of_sortUniq (WF.sortUniq' henv) …`, three lines. `#print axioms` gives `[propext, sorryAx, Classical.choice, Quot.sound]`: the taint comes from `IsDefEqU.forallE_inv_stratified` (`:261`), which *is* a census row. So the census is right, the ledger's "one `sorry`" is wrong, and "open" is right. **Ledger row should read: `sort_inv` is proved from `forallE_inv_stratified` and carries its hole.** (Exactly the vacuity-ledger's blindness kind 3 — dropped qualifier — so it is worth fixing in place.) |

### 8.1 What landed — the `←` half, from three unbundled inputs

`SetModel/UpperBound.lean`, all `[propext, Classical.choice, Quot.sound]` or cleaner, no
`sorryAx`, no frozen axiom:

```lean
def PropTypeAgreeInput : Prop := ∀ env : VEnv, env.LeanWF → env.PropTypeAgree 0
def InstDescendInput   : Prop := ∀ env : VEnv, env.LeanWF → env.InstDescendUp 0
def OracleInput        : Prop := ∀ V [SetStructure V] … (κ) (hκ) (env) (ds),
  VEnv.WF' ds env → PureOverPrelude ds →
  ∀ (henv : env.Ordered) (hU : env.PropUniq 0) (hT : env.PropTypeAgree 0),
    ∃ ls o, OracleFits (propSplitUp env 0 henv hU hT) κ ls o ds

theorem upper_bound_of_inputs (hTI) (hII) (hO) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent
```

and in `Theory/Equiconsistency.lean` (which this stream owns), the two named forms the
endgame reads off: `leanTTConsistent_of_consistent_zfcInacc` and
`inconsistent_zfcInacc_of_inputs`.  **The `↔` at `:46` keeps its single `sorry`, untouched**
— census TOTAL unchanged at 13, same rows.

Two things the unbundling buys that `ModelExists.upper_bound_of_modelFits` (one hypothesis,
`ModelFitsLeanInput`) does not:

* **`VEnv.PropUniq 0` disappears from the input list.**  `env.Consistent` is a negation, so
  its own hypothesis is available inside the proof, and `PropUniq.of_propTypeAgree` consumes
  it.  `ModelFitsLeanInput`'s shape has nowhere to put that, so it cannot make the saving.
* **no existential over `PropSplit`, `ls`, `o`, `R`.**  `ModelFits` is an existential, so a
  proof of it may be discharged at *any* split; here the split is the named `propSplitUp`,
  fixed before the oracle obligations are stated.

### 8.2 The measurement that matters: `VEnv.LeanWF` is not known to be inhabited

This is the anti-vacuity result, and it applies to the *whole* corner rather than to anything
this session added.

`leanTTConsistent = ∀ env, env.LeanWF → env.Consistent`.  **No declaration in the tree
exhibits an `env` with `env.LeanWF`**, and the three inputs above quantify over the same
class.  So (all proved in §3 of the new file):

```lean
theorem upper_bound_vacuous_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) :
    PropTypeAgreeInput ∧ InstDescendInput ∧ OracleInput ∧ leanTTConsistent
```

— premises **and** conclusion go true together.  Recorded as a theorem rather than prose
because the vacuity ledger's kind 4 (an unproved negative) is the expensive mistake here.

§4 pins the missing object, and does so **exactly** rather than sufficiently:

```lean
def PreludeWF : Prop := ∃ env : VEnv, VEnv.WF' leanPrelude.reverse env
theorem exists_leanWF_iff : (∃ env : VEnv, env.LeanWF) ↔ PreludeWF
```

The `←` is `ds := []`; the `→` is `exists_wf'_of_append` — a longer Lean history contains a
prelude-only prefix at an intermediate environment, so the user part `ds` cannot supply the
witness.  **`PreludeWF` is the whole of it.**

This is the model side's analogue of vacuity-ledger row 104a (`addDecl.WF` *is* inhabited,
witness the empty environment).  Here the witness must be a prelude environment.

### 8.3 One of the seven prelude steps discharged

`preludeRev_eq` lists them in `VEnv.WF'` order (most recent first), so the innermost — the
only one over `VEnv.empty` — is `.induct eqIndDecl`.  Proved this session:

```lean
theorem eqIndDecl_WF (env : VEnv) : VInductDecl'.WF env eqIndDecl        -- [propext, Quot.sound]
theorem exists_eqIndDecl_history : ∃ env, VEnv.WF' [VDecl.induct eqIndDecl] env
```

Note the generality: **over an arbitrary environment.**  Nothing in the `Eq` block's data
mentions any constant but its own type former, and `ctors` reads that out of the staged
environment `env₁` via `addConstList_constants`, exactly as `unitDecl_WF` does.  The proof is
pure introduction rules — `sortDF`, `bvar`, `forallEDF`, one `constDF` and three `appDF`s for
`Eq α a a` — with no rewriting and no transport, which is the soundness ledger's standing
prediction about constructor-spine de Bruijn arithmetic holding for a fourth time.

**So the witness gap is six steps, not seven, and it is *unbuilt* rather than blocked.**
`[read]` for the costing of the remaining six:

* `iffIndDecl`, `nonemptyIndDecl` — same pattern, and also over an arbitrary environment
  (neither block's data mentions `Eq`).  What `Eq` avoided is `VIndField.WF`: `Eq.refl` has
  **no fields**, while `Iff.intro` has two and `Nonempty.intro` one, so each needs
  `binders_indep`, `level` (`imax F.lvl D.lvl ≤ D.lvl`, which is *not* `decide`-able as
  stated — `VLevel.le` is a `∀ ls`) and `pos` (`∃ A, NoBlock A ∧ IsDefEqType Γ F.type A`,
  discharged by `A := F.type` plus a `NoConsts` fact).  Attempted this session and **failed
  at exactly those three fields** — see §8.5.
* the three `.axiom` steps are the expensive half: `propext`'s type mentions `Iff` and `Eq`,
  `Classical.choice`'s mentions `Nonempty`, `Quot.sound`'s mentions `Eq`, `Quot` and
  `Quot.mk`, so each needs a `constDF`/`appDF` spine over an environment whose constant map
  is the *result* of the earlier `addInduct'` folds.  That is the size of derivation
  `QuotInterp.lean` pays for `Quot.lift`, not a one-liner — and unlike `eqIndDecl_WF` it
  cannot be stated over an arbitrary environment.
* the `.quot` step needs `VEnv.addQuot` to succeed and the four quotient constants' types to
  be types.

### 8.4 Positive control: which input is *not* the binding constraint

§5 of the new file.  At a certified `VEnv.WF'` history the recursion is entitled to visit —
`unitEnv`, from `UnitOracleWitness.unitDecl_history` — `OracleFits` is **discharged outright,
at an arbitrary `PropSplit` and an arbitrary `κ`** (`exists_oracleFits_unit`, via
`oracleFits_unit`).  So input 3's payload is *satisfiable*; what is missing there is only the
split.  At a *prelude* history that is no longer true: its `.induct` steps are `eqIndDecl`,
`iffIndDecl`, `nonemptyIndDecl`, all with parameters and (for `Eq`) an index, which is
vacuity-ledger row 83c's open frontier for `InductOracleOK`.  **Both statements are needed;
neither implies the other**, and conflating them is how "the oracle is done" gets said.

### 8.5 Tried and failed, with the step it failed at

1. **Making the `↔` at `Equiconsistency.lean:46` derive its `←` half from the new theorem.**
   Not possible without introducing a hypothesis into the `↔`'s own statement: the `←` half is
   available only *conditionally* on the three inputs, so an unconditional `←` cannot be
   supplied and the `sorry` cannot be split without trading one hole for another.  The `↔` is
   left byte-identical.  **Failed at**: there is no unconditional `←`; this is a fact about
   the tree, not about the proof attempt.
2. **`iffIndDecl.WF env`.**  The block-level fields (`types_ne`, `params`, `types`, `isLE`,
   `params_eq`, `args_len`, `args_ty`, `result`) all went through on the `eqIndDecl_WF`
   pattern first try.  It **failed at `VIndField.WF`**, three fields at once: `binders_indep`
   was not in my field list at all (the structure has four fields, not three); `level` is
   `VLevel.imax F.lvl D.lvl ≤ D.lvl` and `by decide` fails — no `Decidable` instance, because
   `VLevel.le` quantifies over all valuations; and `pos`'s `NoBlock` is `VExpr.NoConsts`,
   which `trivial` does not close.  None of the three looks hard; all three are missing
   one-line lemmas.  Reverted rather than left half-built.
3. **Factoring the reduction through `ModelFitsLeanInput`.**  Failed at `PropUniq`: that
   input's shape has no place for the goal's own inconsistency hypothesis, so going through it
   would have *added* `PropUniqInput` as a fourth input.  Going directly to
   `leanTTConsistent` is what removes it — the reason `consistent_of_inputs` re-derives
   `consistent_of`'s application rather than calling `leanTTConsistent_of_lean`.
4. **`by decide` for `VLevel.WF` inside `constDF`'s level-list side conditions at `Eq`.**
   Fails on the bare `∀ l ∈ ls, l.WF uvars` because `ls` is a metavariable at that point; the
   fix is to `intro l hl; simp at hl; subst hl; decide`, i.e. name the level first.  Same
   family as the ledger's "do not ascribe coercion indices" note: give the elaborator the
   shape before the decision procedure.

### 8.6 Measured / read / not run

**[measured]** `lake build`: **1500 jobs** before this session's file, **1501** after, 0
errors in any file, and the sorry set unchanged (13 declarations).  Guards, verbatim:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`lake build Lean4Lean.Experimental.ConeJoin` green — relevant because
`Theory/Equiconsistency.lean` now imports the `SetModel/` tower, so `Verify/SoundnessAssembly`
and everything downstream of it does too.  No name collision: `ConeJoin` already imported
`SetModel.ModelExists`, `SetModel.PropUpFits` and `SetModel.UnitOracleWitness` alongside
`Verify.SoundnessAssembly`, and the `VEnv.PropUniq` / `VEnv.PropTypeAgree` wall recorded in §4
of this document **is gone** — the `Theory/Typing` copies are now `PropUniqN` /
`PropTypeAgreeN`.  §4 should be marked resolved.

`scripts/sorry-census.lean`: **TOTAL 13**, no row changed.
`#print axioms` on all 13 new declarations: quoted in the file's own census block; the two
strongest are `[propext, Classical.choice, Quot.sound]`, `eqIndDecl_WF` is
`[propext, Quot.sound]`, `preludeRev_eq` depends on no axioms.

**[read]** off source, not run: the costing of the six remaining prelude steps (§8.3), and
the claim that no declaration in the tree produces `∃ env, env.LeanWF` — that one is a grep
over `LeanWF` occurrences plus inspection of each hit, so it is a *floor* on the search, not a
theorem. If someone finds such a witness, §8.2 collapses and that is the best possible news.

**[not run]** the Kernel Arena (no implementation file changed) and `scripts/dup-names.lean`.

### 8.7 What to pick up first

1. **`PreludeWF`.**  It is the cheapest thing on the list with the largest effect: until it
   holds, *every* theorem in this corner — including `soundAbove` composed all the way to the
   `←` half — is a statement about a possibly-empty class.  Order: `iffIndDecl_WF` and
   `nonemptyIndDecl_WF` (three small `VIndField.WF` lemmas, §8.5 item 2), then the `.quot`
   step, then the three axiom types, which need the staged constant maps and are the real
   work.
2. **`InstDescendUp 0`'s `.bvar k` case**, unchanged from §7.9 — still the sharpest open
   mathematics on the model side.
3. **Do not** re-attack `PropTypeAgree 0` (irreducible, §7.6), the `sort_inst` refutation
   (§7.1), or `Equiconsistency.lean`'s `↔` (§8.5 item 1).

## 9. Session of 2026-09-02 (second): `PreludeWF` is a theorem — the corner is no longer vacuous

Brief: *prove `PreludeWF`; do not weaken it, do not add a hypothesis; audit the briefing
against the tree.*  **Done in full.**  New file
`Lean4Lean/Theory/SetModel/PreludeWitness.lean` (462 lines, 34 declarations, sorry-free).

Everything below is **[measured]** unless marked `[read]`.

### 9.1 What landed

```lean
theorem preludeWF          : PreludeWF                                   -- [propext, Quot.sound]
theorem exists_leanWF      : ∃ env : VEnv, env.LeanWF                    -- via exists_leanWF_iff
theorem preludeEnv_leanWF  : preludeEnv.LeanWF
theorem not_forall_not_leanWF : ¬ ∀ env : VEnv, ¬ env.LeanWF
```

`not_forall_not_leanWF` is the point: it **refutes the hypothesis of
`upper_bound_vacuous_of_no_leanWF`**, so §8.2's collapse can no longer be used to discharge
`PropTypeAgreeInput`, `InstDescendInput`, `OracleInput` or `leanTTConsistent`.  Every theorem
in this corner is now a statement about a class with a member, and the member is named.

The seven steps, all discharged (`preludeEnv_history : VEnv.WF' leanPrelude.reverse preludeEnv`):

| step | discharge | cost |
|---|---|---|
| `.induct eqIndDecl` | `eqIndDecl_WF` (§8.3, previous session) | — |
| `.induct iffIndDecl` | `iffIndDecl_WF (env)`, **arbitrary** environment | ~55 lines |
| `.axiom propextConst` | `propextConst_WF` over `iffEnv` | 12 lines |
| `.induct nonemptyIndDecl` | `nonemptyIndDecl_WF (env)`, **arbitrary** environment | ~40 lines |
| `.axiom choiceConst` | `choiceConst_WF` over `nonemptyEnv` | 7 lines |
| `.quot` | `choiceEnv_quotReady` + `quotEnv_add`, **two `rfl`s** | 2 lines |
| `.axiom quotSoundConst` | `quotSoundConst_WF` over `quotEnv` | ~45 lines |

Plus the reduction of the `←` half to something with content:

```lean
theorem preludeEnv_consistent_of_inputs (hTI) (hII) (hO)
    (hc : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) : preludeEnv.Consistent
```

and `propTypeAgree_of_input`, `instDescend_of_input`, `consistent_of_leanTTConsistent`:
each input, and the conclusion, now says something at a *named* environment.

### 9.2 Audit of the briefing — three claims wrong, and all three in the same direction

I was asked to check the brief against the tree.  Three of its costings are wrong, and every
one of them **overstated** the difficulty, which is the opposite of §8.0's failure mode and
worth recording as such.

| claim as briefed | verdict |
|---|---|
| `eqIndDecl_WF` over an arbitrary environment, `[propext, Quot.sound]`, with `exists_eqIndDecl_history`; six steps remain; `exists_leanWF_iff`'s `→` via `exists_wf'_of_append` so `ds` cannot help | **correct**, all four, checked at source |
| `VLevel.imax ≤` is a `∀ ls` and so not `decide`-able | **correct** — `VLevel.LE a b := ∀ ls, a.eval ls ≤ b.eval ls` (`Theory/VLevel.lean:41`) |
| `NoBlock` is `VExpr.NoConsts` rather than `trivial` | **correct**, and sharper than briefed: `NoConsts` is a `def` by pattern match, not a structure, so `⟨trivial, trivial⟩` needs the existential's `A` given **explicitly** — with `A` a metavariable the anonymous constructor is rejected outright ("expected type is not an inductive type") |
| **"three missing one-liners"** for `iffIndDecl_WF` / `nonemptyIndDecl_WF`, at `binders_indep`, `level`, `pos` | **the count and the characterisation are both wrong, and no lemma was missing.** (i) The blocking field list is wrong: `binders_indep` is `nofun` (both blocks' fields are non-recursive, so `VIndRecArg.exists_indep` — which carries a `sorry` — is **not** on this file's cone), while **`hasType`**, which the brief does not mention, was a real obstacle: `forallEDF` types a pi at `.sort (.imax u v)` and the recorded `F.lvl` is `.zero`, so a `defeqDF` through `sortDF … VLevel.imax_zero` is needed. (ii) Nothing was *missing*: `VLevel.imax_zero` and `VLevel.le_antisymm_iff` are already in `Theory/VLevel.lean`, and `level` is `(VLevel.le_antisymm_iff.1 VLevel.imax_zero).1`. What was needed was **explicit arguments**, not new lemmas — `A := F.type`, `u := VLevel.zero`, `(l := .zero)` on `sortDF` |
| **the `.quot` step "needs `addQuot` to succeed and the four quotient constants' types to be types"** | **REFUTED.** `VDecl.WF.quot` (`Theory/Typing/Env.lean:43`) asks for exactly `env.QuotReady` — which is `env.constants ``Eq = some eqConst`, **one `rfl`** — and `env.addQuot = some env'`. Well-formedness of `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` is a **theorem**, `addQuot_WF` (`Theory/Typing/QuotLemmas.lean:7`), which delivers `Ordered env'` from `QuotReady`. So this was the **cheapest** of the six steps, not a middle-cost one |
| **the three axiom types are "the expensive half, with spines the size of `Quot.lift`'s"** | **REFUTED as a costing.** They are the largest of the six but not large: 12 / 7 / 45 lines, each one `constDF` per constant head plus `appDF`s and `bvar`s, every step `exact`, no rewriting, no transport, no `instL` bookkeeping beyond what `exact` computes. The `QuotInterp.lean` comparison is a category error: what `QuotInterp.lean` pays for `Quot.lift` is its **model interpretation**, a different obligation from "its type is a type" |

### 9.3 The environment chain, and why its `rfl`s are not tautologies

The seven environments are **computed**:

```lean
def eqEnv : VEnv := (VEnv.empty.addInduct' eqIndDecl).getD .empty
theorem eqEnv_add : VEnv.empty.addInduct' eqIndDecl = some eqEnv := rfl
```

and likewise for `iffEnv`, `propextEnv`, `nonemptyEnv`, `choiceEnv`, `quotEnv`, `preludeEnv`.
The pattern is `fooEnv_eq` from `Theory/Inductive/DeclExamples.lean:1359` in a form that
*names* the result.  **The `rfl` is load-bearing**: had any `addConst`/`addInduct'` returned
`none`, `getD .empty` would have returned `VEnv.empty` and the statement would read
`none = some VEnv.empty`, which `rfl` refuses.  So these seven `rfl`s certify, as a side
effect, freshness and pairwise distinctness of all sixteen names the prelude declares.

Every constant lookup the axiom spines need is `rfl` too (`iffEnv_Iff`, `iffEnv_Eq`,
`nonemptyEnv_Nonempty`, `choiceEnv_quotReady`, `quotEnv_Eq`, `quotEnv_Quot`,
`quotEnv_QuotMk`), so no monotonicity lemma (`VEnv.addConst_le`, `addConstList_le`) is used
anywhere in this file.  §5 adds controls: `preludeEnv_propext`, `preludeEnv_choice`,
`preludeEnv_quotSound`, `preludeEnv_quotLift`, `preludeEnv_eqRec` (positive; the recursors
really are there), `preludeEnv_no_Nat` (negative), `preludeEnv_ordered` (via
`VEnv.WF.ordered`, the one declaration in the file that reaches `Classical.choice`).

Total elaboration cost of the file: **~4 s**, and `lake build` went 1501 → 1502 jobs.  The
whole thing was cheaper than the audit of the costing that said it would be expensive.

### 9.4 Tried and failed, with the step it failed at

1. **`⟨_, ⟨trivial, trivial⟩, ⟨_, ?_⟩⟩` for `VIndField.WF.pos`.**  Failed twice, at two
   different placeholders.  First at `A`: `VExpr.NoConsts iffIndDecl.blockNames ?A` "is not an
   inductive type", because `NoConsts` is a `def` by pattern match and cannot be reduced with
   `A` unknown.  Then, after giving `A`, at the `IsDefEqType` existential's `u`: "don't know
   how to synthesize placeholder for argument `w`", because a `?_` inside a structure instance
   is elaborated after the surrounding term.  **Fix**: give both explicitly —
   `pos := ⟨VExpr.forallE (.bvar 1) (.bvar 1), ⟨trivial, trivial⟩, ⟨VLevel.zero, ?_⟩⟩`.
2. **`.sortDF trivial trivial (.refl _)` as the `Sort 1` argument of `Eq.{1}` in
   `propextConst_WF`.**  Failed at the first `trivial`: `VLevel.WF 0 ?l`, i.e. `l` was still a
   metavariable when the argument was elaborated, even though the expected *type*
   `.sort (.succ .zero)` determines it.  **Fix**: `(l := .zero) (l' := .zero)`.  Same family as
   §8.5 item 4 — name the level before the decision procedure runs.
3. **`(VEnv.IsDefEq.bvar (.succ (.succ .zero))).appDF …` for `r a b` in `quotSoundConst_WF`.**
   Failed at `appDF`: a `bvar` head's type comes out of the `Lookup` proof as
   `Γ[i].lift.lift.…`, and with `Γ` itself a metavariable nothing can be unified with
   `.forallE A B`.  **Fix**: a `have hr : … (.bvar 2) (.forallE (.bvar 3) (.forallE (.bvar 4)
   (.sort .zero)))` with the context written out.  *Only the head needs this* — `bvar`s in
   argument position are checked against a known domain and go through bare.
4. **`simp only [iffIndDecl, …] at hF; subst hF` on `C.fields[i]? = some F`.**  Failed at
   `subst`: `simp only [iffIndDecl]` does not reduce `[f₀, f₁][0]?`, so the hypothesis is not
   an equation with a variable on one side.  **Fix**: `List.getElem?_cons_zero` /
   `List.getElem?_cons_succ` in the simp set, and `nomatch hF` for the out-of-range arm.  The
   `nomatch`/`nofun` forms also drop `Classical.choice` from the axiom set: with `simp`
   everywhere, `iffIndDecl_WF` was `[propext, Classical.choice, Quot.sound]`; replacing five
   `simp`s by `nofun` / `nomatch` brought it to `[propext, Quot.sound]`, matching
   `eqIndDecl_WF`.
5. **Nothing was attempted and abandoned at the level of a step.**  All six steps closed; no
   hypothesis was introduced anywhere, and `PreludeWF` is stated byte-identically to
   `UpperBound.lean`'s definition.

### 9.5 Measured / read / not run

**[measured]** `lake build`: **1502 jobs**, "Build completed successfully", **0 errors in any
file** — including the four files another stream owns.  Guards, verbatim:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`lake build Lean4Lean.Experimental.ConeJoin` green.  `scripts/sorry-census.lean`: **TOTAL 13**,
**no row changed** — the new file contains no `sorry` and trades none.
`scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone"; and a
direct grep confirms all fourteen new top-level names (`iffIndDecl_WF`, `eqEnv`, …,
`preludeEnv`, `preludeWF`) occur **nowhere else in the tree**.
`#print axioms` on all 34 declarations: `[propext, Quot.sound]` throughout, the two exceptions
being `preludeEnv_ordered` and `preludeEnv_consistent_of_inputs`, which reach
`Classical.choice` through `VEnv.WF.ordered` and `upper_bound_of_inputs` respectively.  **No
`sorryAx`, no frozen axiom, nothing new on the frozen cone.**

**[read]** off source, not run: that `VIndRecArg.exists_indep`'s `sorry` is off this file's
cone is *measured* (`#print axioms`), but the *reason* — both blocks' fields are
non-recursive — is read off `Consistency.lean:96` and `:126`.

**[not run]** the Kernel Arena (no implementation file changed); `scripts/hole-cone.lean`.

### 9.6 What this does and does not buy

* It does **not** move `kernel_sound`, `Equiconsistency.lean`'s `↔`, or any census row.  H2's
  three inputs are exactly as open as they were.
* It **does** remove the possibility that they are open *about nothing*.  Before this file,
  `upper_bound_of_inputs` could have been discharged in four lines from an emptiness proof;
  now it cannot.  Row 126 of `docs/vacuity-ledger.md` moves from "UNMEASURED, and nothing in
  the tree settles it" to "measured, and the answer is no".
* One structural consequence worth having: `preludeEnv` is a concrete, `Ordered`,
  `LeanWF` environment.  Anything in this corner that wants a *reachable instance* to
  instantiate at — a positive control for `PropTypeAgree 0`, `InstDescendUp 0`, or the
  `.induct` oracle obligations at a block with parameters and an index — now has one, and it
  is the one the statements are actually about, unlike `unitEnv` (§8.4).

### 9.7 What to pick up first

1. **`InstDescendUp 0`'s `.bvar k` case** — unchanged from §7.9 and §8.7, still the sharpest
   open mathematics on the model side, and now the sharpest *non-vacuous* one.
2. **`InductOracleOK` at `eqIndDecl` / `iffIndDecl` / `nonemptyIndDecl`** — vacuity-ledger row
   83c's frontier, and `preludeEnv` is now a named environment to attack it at.  This is the
   part of `OracleInput` that §8.4 correctly said is *not* covered by
   `oracleFits_unit_at_consumer`.
3. **`PropTypeAgree 0` at `preludeEnv`** is now a *concrete* question rather than a schema.
   §7.6 says do not re-attack the general statement; the instance at `preludeEnv` is a
   different object and has not been looked at.
4. **Note for whoever needs `preludeEnv` downstream**: `PreludeWitness.lean` is built by the
   `Lean4Lean.Theory.*` glob but **nothing imports it**, so it is not in `ConeJoin`'s closure
   and the census/dup-names scripts do not see it.  If you want `preludeEnv` available to
   `Equiconsistency.lean` or to the `Verify/` side, add the import there; there is no name
   collision (checked).

## 10. Session of 2026-09-02 (third): `InductOracleOK` at a **prelude** block, and the parameter nobody has built

Brief: *§9.7 items 2 and 3 — `InductOracleOK` at `eqIndDecl`/`iffIndDecl`/`nonemptyIndDecl`,
then `PropTypeAgree 0` at `preludeEnv`; audit the briefing against the tree.*

**One of the three `.induct` blocks is closed, at `preludeEnv`, in the shape `OracleFits`
asks for.**  The other two are measured rather than costed.  And the session's sharpest
result is negative and applies to the whole corner: items 2 and 3 of §9.7 are **one item**,
because every `.induct` witness in this directory is quantified over a `PropSplit` that
nothing in the tree constructs.

New file: `Lean4Lean/Theory/SetModel/PreludeOracle.lean` (1521 lines, 171 declarations,
**sorry-free**), imported by `Theory/Equiconsistency.lean` so it is connected, not merely
proved (row 128b's lesson).  Everything below is **[measured]** unless marked `[read]`.

### 10.1 What landed

```lean
theorem inductOracleOK_NE (L : PropSplit envF nv) (κ) (ls) (hle : nonemptyEnv ≤ envF) :
    InductOracleOK L κ ls (neOracle κ ls) (neOracle κ ls) nonemptyIndDecl
theorem nonemptyEnv_le_preludeEnv : nonemptyEnv ≤ preludeEnv
theorem inductOracleOK_NE_at_preludeEnv (L : PropSplit preludeEnv nv) (κ) (ls) : …
theorem cnstOf_preludeTail : cnstOf L κ ls (neOracle κ ls) preludeTail = neOracle κ ls
theorem oracleStepOK_NE_at_preludeEnv (L : PropSplit preludeEnv nv) (κ) (ls) :
    OracleStepOK L κ ls (neOracle κ ls) (.induct nonemptyIndDecl)
      [.axiom propextConst, .induct iffIndDecl, .induct eqIndDecl]
```

`oracleStepOK_NE` is the point of `cnstOf_preludeTail`: `OracleFits` states each step's
obligation at `cnstOf` applied to the *tail* of the list, so `InductOracleOK` at the oracle
itself is not yet the step.  The two coincide here because the prelude's first four steps
assign exactly the ten names `neOracle` is non-`∅` at, and `neOracle` is `∅` — which is
`cnstOf … []` — everywhere else.  **So this is the obligation at the step's own position in
`leanPrelude.reverse`, not a statement at a convenient assignment.**

**The oracle is not new.**  `neOracle κ ls = (preludeWitness κ ls).cnst`, byte for byte the
joint witness `PreludeSpec.preludeSpec_satisfiable` already exhibits for
`EqSpec`/`IffSpec`/`NonemptySpec`.  Nothing was tuned: `Nonempty ↦ nonemptyFn κ n` is the
intended squash and the other two names get `∅`, which **is** `•` (`pt_def`).  The same
assignment that validates the three standard axioms' specifications discharges the `.induct`
residual at the block `Classical.choice`'s type mentions.  *That file's existence is the
single largest omission in the brief* — see §10.2.

Why the block is not a re-run of the two easy ones, all machine-checked:

* `boxDecl` met the residual because its parameter denoted `∅`.  Here the parameter denotes a
  **universe** (`interp_param_ne_empty`), and `not_mem_interp_zeroOracle_NE_type` **refutes**
  the `∅`-everywhere oracle at the type former: `∀ α : Prop, Prop` is a function space over
  the nonempty `U₀`, and `∅ = •` is not a function on a nonempty domain.
* `unitDecl` has no parameter and no constructor field.  This block has one of each
  (`ne_params`, `neCtor_fields`), so the type former's value is a genuine internal function,
  landed with `UnitOracleLarge.mkLam_mem_mkForallType_of_dom`.
* The squash must be **faithful**, in both directions: the constructor's obligation forces
  `α ≠ ∅ → ⟦Nonempty α⟧ = {•}` (`mem_interp_NE_intro`) and the recursor's forces the converse
  (`pt_mem_interp_NE_recType` case-splits on `α = ∅` and uses
  `ne_empty_iff_isNonempty` to produce the `val` the minor premise needs).  Both branches fire
  at `U₀`: `nonemptyFn_zero_empty`, `nonemptyFn_zero_true`.

Why the recursor is nevertheless cheap: `nonemptyIndDecl.isLE = false`, so `elimLvl = .zero`
and the **whole** of `recType 0` is a proposition (`hasType_recB1`: sort
`imax (imax 0 1) (imax (imax u 0) (imax 0 0))`, which evaluates to `0`).  `interp` takes
`mkForallProp` at every binder and the oracle's value is `•`.  Same for the ι-rule: both sides
are λ-nests whose body is a *proof*, so `interp_lam_proof` settles `• = •` with no
β-computation — this is `UnitOracleWitness`' argument at a four-binder telescope.

`Above`-free, both fields, arbitrary `κ`: `mem_interp_consts_NE`, `defEq_rules_NE`.  **No `κ`
is chosen anywhere**; every proof goes through `Above.pure`.

### 10.2 The headline negative: §9.7 items 2 and 3 are **one** item

`InductOracleOK L κ ls o c D` is quantified over `L : PropSplit envF nv`, and **no declaration
in this tree constructs a `PropSplit`, at any environment.**  The only three producers are
`PropSplitAudit.propSplitOf` and `PropSplitUp.propSplitUp` (both taking `PropUniq` *and*
`PropTypeAgree`) and `Interp.LevelAssign.toPropSplit` (taking a structure nothing builds —
and whose unguarded ancestor was outright unsatisfiable, `LevelAssignUnsat.lean`).

`PropSplit` is therefore exactly the shape `LevelAssignUnsat.lean`'s own opening paragraph
names as the test that found two unsatisfiable structures: *a structure whose producers all
consume the same structure has never had its fields tested.*  Nothing here says it is
unsatisfiable — `nonempty_propSplit_iff_agree` says precisely what it costs — but the
**vacuity** consequence is immediate and it is retroactive:

> `inductOracleOK_zero` (row 11a/72), `inductOracleOK_unit`, `inductOracleOKL`,
> `exists_oracleFits_unit`, `oracleFits_unit_at_consumer` and §10.1 above are **all** statements
> about a parameter class not known to be non-empty.  This is `docs/vacuity-ledger.md` §0's
> eighth blindness, at the one place in this corner where nobody had looked.

Machine-checked at the named environment:

```lean
theorem nonempty_propSplit_preludeEnv_iff :
    Nonempty (PropSplit preludeEnv 0) ↔ preludeEnv.PropUniq 0 ∧ preludeEnv.PropTypeAgree 0
theorem nonempty_propSplit_preludeEnv_of_propTypeAgree
    (hT : preludeEnv.PropTypeAgree 0) (hf : ∃ e, preludeEnv.HasType 0 [] e falseProp) :
    Nonempty (PropSplit preludeEnv 0)
```

and `PropUniq` is free where the reduction is consumed (§7.6's last bullet: `env.Consistent` is
a negation, so the goal's own inhabitant of `falseProp` feeds `PropUniq.of_propTypeAgree`).  So
**the entire content of "the `.induct` oracle results are not vacuous" is
`PropTypeAgree preludeEnv 0`** — `UpperBound.PropTypeAgreeInput`'s instance at the witness
environment, and nothing else.  Item 2 does not stand without item 3.

This is not a defect of §10.1: `coherentOn_cnstOf` quantifies over the same `L`, so the witness
is stated at exactly the strength its consumer wants.  It is a fact about the layer.

### 10.3 A correction to `NotProofNoModel.lean` §6: the level-layer gap **closes at `nv = 0`**

§6 of that file records that the model's pointwise `PropTypeAgree` and the syntactic side's
`IsPropN`-shaped statement *do not compose*: `propTypeAgree_equivZero` gives one direction and
`propAgree_pointwise_not_from_equivZero` refutes the other.  **Its witness is `.param 0` /
`.param 1` at `WF 2`, so it needs `nv ≥ 2` — and the only `nv` this corner uses is `0`.**

```lean
theorem eval_const_of_wf_zero : u.WF 0 → ∀ ls ls', u.eval ls = u.eval ls'
theorem propTypeAgree_zero_iff_equivZero (env) :
    env.PropTypeAgree 0 ↔ (… → (u ≈ .zero ↔ u' ≈ .zero))
theorem propTypeAgree_preludeEnv_iff_equivZero : …
```

A `WF 0` level contains no `.param`, so its evaluation is constant in `ls` and the two shapes
are **equivalent**.  `PropTypeAgreeInput` is `PropTypeAgree env 0`, and
`PropReduce.PropTypeAgree.of_zero` lifts `0` to every `nv` with no hypothesis, so the instance
the reduction consumes is exactly the one where the recorded non-composition does not bite.

**What still separates the two streams is therefore the `HasTypeN U n` / `HasType 0` bridge and
the fact that `PropTypeAgreeN` is itself open — not the level layer.**  `NotProofNoModel.lean`
§6's "closing `PropTypeAgreeN` does not close `PropSplit`'s import" is true as stated (about
`nv ≥ 2`) and misleading as read; the two repairs it proposes (pinning `PropSplit`'s valuation,
a large mechanical edit) are **not needed for `nv = 0`**.  That is the cheapest thing found this
session and it was found by reading the counterexample's `WF 2` rather than its conclusion.

### 10.4 The other two prelude blocks: measured, not costed

Every statement in §13 of the new file is `rfl`.

| | `nonemptyIndDecl` | `iffIndDecl` | `eqIndDecl` |
|---|---|---|---|
| `isLE` | **false** | true | true |
| `elimLvl` | `.zero` | `.param 0` | `.param 0` |
| `recUvars` | 1 | 1 | 2 |
| indices | `[]` | `[]` | `[.bvar 1]` |
| binders before the result in `recType 0` | 4 | 5 | 6 |
| `recType 0` is a proposition | **yes** | no | no |

`iff_recType` and `eq_recType` write both types out in full, as `rfl`, so the next stream does
not have to rediscover them.  The single structural difference is `isLE`: at `isLE := true` the
recursor's result is `Sort (param 0)`-valued, so at an instantiation with `u.eval ls ≠ 0` the
innermost binder is not propositional, `interp` takes `mkForallType`, and `•` is not a legal
value — the situation `UnitOracleLarge.recFnL` handles with a **three**-layer `mkLam` for a block
with no parameters and no fields.  `Iff` wants five layers and `Eq` six, and `Eq`'s motive is
itself a two-binder pi because of the index.

Also measured: `preludeWitness` assigns `∅` to **both** recursors
(`preludeWitness_eqRec_empty`, `preludeWitness_iffRec_empty`), so `PreludeSpec.lean`'s witness is
not a candidate oracle at either block.  **I did not prove that it fails there** — that would be
`UnitOracleLarge.pt_not_mem_interpL_recType_of_ne` transported to a five- or six-binder
telescope — and the file flags it as a fact about the assignment rather than a refutation, per
`docs/vacuity-ledger.md` §0 kind 4.

### 10.5 Audit of the briefing — four checks, and where it is wrong

| claim as briefed | verdict |
|---|---|
| `InductOracleOK` at the three prelude blocks is row 83c's frontier and the part of `OracleInput` that §8.4 says is *not* covered by `oracleFits_unit_at_consumer` | **correct**, checked at source in `UpperBound.lean` §5 and `InductOracleAudit.lean` §5 |
| `preludeEnv` is the environment to attack it at | **correct, and it works**: `nonemptyEnv ≤ preludeEnv` is three `VDecl.WF.le` steps from `PreludeWitness.lean`'s own theorems, and `oracleStepOK_NE_at_preludeEnv` is the result |
| build on `inductOracleOK_zero`, `inductOracleOK_unit`, `inductOracleOKL`, `exists_oracleFits_unit` rather than redo them | **half wrong, in a way worth recording.**  `inductOracleOK_zero`'s oracle is *refuted* here (`not_mem_interp_zeroOracle_NE_type`) and `inductOracleOK_unit`'s mechanism (no parameter, no field) does not transfer at all.  What transferred was the **discipline** of `UnitOracleWitness.lean` §4 (`hle` + `isProp_iff`) and exactly two lemmas from `UnitOracleLarge.lean` (`mkLam_mem_mkForallType_of_dom`, `pt_not_mem_mkForallType_of_nonempty`).  And the brief omits the file that actually made the session cheap: **`SetModel/PreludeSpec.lean` already contains `nonemptyFn`, the intended denotation, with its definability and value lemmas, and `preludeWitness`, an assignment that is already the oracle.**  Had that been in the brief the session would have started an hour earlier |
| row 83c's `rules`-negative cell is worded unachievably | **correct**; the source was already reworded 2026-09-01 |
| §7.6's instruction not to re-attack the general `PropTypeAgree` stands; the instance at `preludeEnv` is a different object | **correct that it had not been looked at, misleading as a hint.**  The instance is not a different *statement* — it is the same statement restricted to one environment, and its typing content is not smaller.  What is genuinely new is §10.2's reduction and §10.3's level-layer correction, neither of which required attacking the typing content |
| §9.7 item 4: "`PreludeWitness.lean` is built by the glob but **nothing imports it**" | **STALE — it is imported twice**, by `Theory/Equiconsistency.lean:4` and `Experimental/ConeJoin.lean:160`, wired by row 128b on the same day §9 was written.  The brief pointed me at §9.7, whose fourth item is wrong |

### 10.6 Tried and failed, with the step it failed at

1. **Writing the squash by hand.**  `{z ∈ ({pt} : V) ; ∃ x ∈ a, z = z}` — `definability` fails
   at `ℒₛₑₜ-function₁ fun a => {z ∈ {pt} ; ∃ x, x ∈ v 40}` with *maximum rule application depth
   (30) reached*, exactly the first failure mode `SetModel/Definability.lean`'s docstring
   describes.  **Fix**: do not write it — `PreludeSpec.nonemptyFn` exists, with
   `nonemptyFib_definable` done by the relation reformulation.
2. **`InterpSound.mkLam_mem_mkForallType` for the type former.**  Failed at unification: it
   needs the domain function *and its definability proof term* to be the same on both sides,
   and here one comes from the oracle and one from `interp`.  This is the failure
   `Cnst.lean:323` already documents; **fix**:
   `UnitOracleLarge.mkLam_mem_mkForallType_of_dom`, which asks only that the domains *agree at
   the valuation*.
3. **Typing lemmas at fixed contexts.**  §5 was first written at `[.sort u]`, `[motTy u, .sort u]`
   … with no tail.  Failed at `hasType_iotaLamE`: the ι-rule's η-expansion needs `iotaLamE`
   typed *inside* `ctxF u`, so its own λ-bodies live in a longer context.  **Fix**: every
   context abbrev takes a tail `Γ`; `Lookup` does not care, and the interpretation is then read
   at `Γ = []`.  ~90 lines rewritten.
4. **`rw [neOracle_NE]` after `interp_const`.**  `interp_const` produces `(neM κ ls).cnst n us`
   and `rw` will not delta-reduce that to `neOracle κ ls n us`.  **Fix**: restate the three
   values at `(neM κ ls).cnst` (`neM_cnst_NE`, `neM_cnst_intro`, `neM_cnst_rec`), each proved by
   the corresponding `neOracle_*` up to defeq.
5. **`show (if m = ``propext then _ else _)` for `cnstUpdate`.**  `cnstUpdate c n v` is
   `fun m ↦ if m = n then v else c m`, so the `if` is at the **function** level and
   `cnstUpdate c n v m us` is `(if … then v else c m) us`.  **Fix**: `cnstUpdate_apply`.
6. **`.trans` on `VEnv.LE`** resolves to `Preorder.trans` and fails; write `VEnv.LE.trans`.
7. **`match us, hlen with | [w], _ => …`** for `us.length = 1` inside a *tactic* block: branches
   take tactics, and the exhaustiveness checker demands the impossible cases.  **Fix**: a
   standalone term-mode `eq_singleton_of_length_one`.
8. **Not attempted, deliberately**: `iffIndDecl` and `eqIndDecl` (§10.4 — five and six `mkLam`
   layers, and the level branch will be forced there as it is for `unitDeclLE`), and the
   const-true-squash refutation at `nonemptyIndDecl` (`Nonempty ↦ λ α. {•}` satisfies the
   constructor and should fail at the recursor).  The second needs the whole §7 chain re-run at
   a second oracle, ~200 lines; the negative that *did* land is the weaker
   `not_mem_interp_zeroOracle_NE_type`.  Neither is claimed.
9. **`InstDescendUp 0`'s `.bvar k` case** — untouched, as the brief allowed.

### 10.7 Measured / read / not run

**[measured]** `lake build`: **1503 jobs** (1502 before), "Build completed successfully",
**0 errors in any file**.  Guards, verbatim:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard` green.
`scripts/sorry-census.lean`: **TOTAL 13**, **no row changed**, none traded.
`scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone".
`#print axioms` on 34 named declarations of the new file: `[propext]`, `[propext, Quot.sound]`
or `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no frozen axiom, nothing new on
the frozen cone**.  Every shape lemma in §1 and §13 is `rfl`, so those two sections are
measurements of the blocks rather than transcriptions.

**[read]** off source, not run: **"nothing in this tree constructs a `PropSplit`"** (§10.2) is a
grep over `PropSplit` occurrences plus inspection of the three producers — a *floor* on the
search, not a theorem, exactly the epistemic status of §8.6's `LeanWF` grep.  If someone finds
one, §10.2 collapses and that is the best possible news.  Also read: that
`UnitOracleLarge.recFnL` is three `mkLam` layers.

**[not run]** the Kernel Arena (no implementation file changed); `scripts/hole-cone.lean`,
`scripts/hole-rank.lean`.

### 10.8 Ledger rows this session should produce

Left to the orchestrator rather than written into `docs/vacuity-ledger.md`, since a second
stream is live in the tree:

* **`InductOracleOK` closed at a prelude block** — `inductOracleOK_NE`,
  `oracleStepOK_NE_at_preludeEnv`, at the oracle `PreludeSpec.lean` already built; row 83c's
  frontier narrows from "parameters/indices" to "**large elimination** with parameters", i.e.
  `iffIndDecl` and `eqIndDecl` only.
* **NEW blindness instance, and it is retroactive** — `PropSplit` is not known inhabited at any
  environment, so rows 11a, 72 and 83c's positive cells, and §10.1, are all conditional on
  `PropTypeAgree preludeEnv 0`.  Amend those rows rather than add one; the equivalence is
  `nonempty_propSplit_preludeEnv_iff`.
* **`NotProofNoModel.lean` §6's non-composition is about `nv ≥ 2`** —
  `propTypeAgree_zero_iff_equivZero`.  The two repairs that file proposes are unnecessary at the
  instance H2 consumes.
* **`inductOracleOK_zero`'s oracle is refuted at a prelude block** —
  `not_mem_interp_zeroOracle_NE_type`.  The empty-domain mechanism does not reach the prelude.

### 10.9 What to pick up first

1. **`PropTypeAgree preludeEnv 0`.**  It was item 3; it is now item 1, because §10.2 makes it
   the vacuity guard for *everything* in this corner, and §10.3 removes the level-layer
   obstruction at the only `nv` that matters.  The remaining bridge is `HasTypeN U n` ↔
   `HasType 0`; that is a statement about the syntactic side's stratification, not about the
   model, so **check whether `Theory/Typing` already has it before building anything**.
2. **`iffIndDecl` before `eqIndDecl`** — five binders and no index against six with one, and
   `UnitOracleLarge.recFnL` is the template.  Expect the oracle's value to branch on
   `u.eval ls = 0` exactly as `unitOracleL`'s does; §7.4's "the level branch is FORCED" should
   reappear, and the `= 0` slice should be free by §10.1's argument.
3. **The const-true refutation at `nonemptyIndDecl`**, to close the `consts` cell's negative
   direction *at a `WF` prelude block* rather than at a block of one's own choosing.
4. **`InstDescendUp 0`'s `.bvar k` case** — unchanged from §7.9, §8.7 and §9.7, and still
   untouched.

**Do not** re-attack: `inductOracleOK_zero`'s oracle at any prelude block (refuted, §10.1),
`InterpSound.mkLam_mem_mkForallType` against an oracle-supplied domain (§10.6 item 2), the
`sort_inst` refutation (§7.1), or `Equiconsistency.lean`'s `↔` (§8.5 item 1).

---

## 11. Session of 2026-09-02 (fourth): the wall question, answered — **`PropTypeAgree preludeEnv 0` is NOT the injectivity wall**

### 11.0 The answer, plainly

**No. `PropTypeAgree preludeEnv 0` does not reduce to any of the four holes gating
`Bridge.kernel_sound_of`, and it is not gated on them.**  It splits into two pieces, and
neither piece is one of those four:

| piece | status |
|---|---|
| **A.** the *context-guarded* statement `PropTypeAgreeOnCtx preludeEnv 0` | **DISCHARGED at `preludeEnv`, twice, by two independent routes** — one through `forallE_inv_stratified`, one with no hole at all |
| **B.** the *context guard* — `PropTypeAgree` quantifies over every `Γ`, junk contexts included | **open, and it is nobody's target.**  Not `weakN_iff`, contrary to `NotProofNoModel.lean` §5 |

So the corner does **not** share a wall with the nine refinement holes.  What it shares with
them is *one of two* routes; the other route is `Theory/Typing/PropConv.lean` +
`Theory/Typing/PropShadow.lean`, i.e. the live target of the other stream, and it touches
none of `forallE_inv_stratified`, `rigidShapeUniqNS`, `weakN_iff`, `descend`.

New file: `Lean4Lean/Theory/SetModel/PropAgreeWall.lean` (301 lines, 15 declarations — 14 theorems plus the `CtxReplace` definition,
**sorry-free**), imported by `Theory/Equiconsistency.lean` so the reduction is load-bearing.

### 11.1 What landed

```lean
-- route A: the guarded import at the witness environment, NOTHING assumed
theorem preludeEnv_propTypeAgreeOnCtx : preludeEnv.PropTypeAgreeOnCtx 0
theorem preludeEnv_propUniqOnCtx     : preludeEnv.PropUniqOnCtx 0

-- route B: the same statement from the SYNTACTIC side, `sorryAx`-FREE
theorem propTypeAgreeOnCtx_of_stratifiedN (henv : Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropTypeAgreeOnCtx 0

-- the residual, named as one object
def CtxReplace (env) (nv) : Prop := …            -- context replacement, not deletion
theorem preludeEnv_propTypeAgree_of_ctxReplace (h : CtxReplace preludeEnv 0) :
    preludeEnv.PropTypeAgree 0
theorem nonempty_propSplit_preludeEnv_of_ctxReplace (h) (hf) : Nonempty (PropSplit preludeEnv 0)
theorem nonempty_propSplit_preludeEnv_of_stratifiedN (h) (pta) (pun) (hf) : Nonempty (…)
```

Route A is `NotProofNoModel.WF.propTypeAgreeOn` / `WF.propUniqOn` at
`PreludeWitness.preludeEnv_WF`.  **Measured, not read:** a forward cone walk over
type-and-value dependencies (`/tmp` script, same algorithm as `scripts/hole-cone.lean`) reports
that `WF.propTypeAgreeOn`'s cone (3444 declarations) contains **exactly one** sorry-carrying
declaration, `VEnv.IsDefEqU.forallE_inv_stratified` — and **not** `rigidShapeUniqNS`,
**not** `weakN_iff`, **not** `descend`.  Same for `WF.propUniqOn`, `WF.sortUniq'`,
`IsDefEqU.sort_inv`, `IsDefEq.uniqU`.

> **Correction to two source docstrings.**  `NotProofNoModel.WF.propTypeAgreeOn` says it is
> "`sorryAx`-tainted through `IsDefEqU.forallE_inv_stratified` **and `WF.rigidShapeUniq`**".
> The second half is wrong: `WF.rigidShapeUniq` is not in the cone at all.  The whole cone is
> one hole.  Same correction applies to that file's §5 axiom-check paragraph.

Route B is new and is the substantive result.  Three ingredients, no holes:
`VEnv.HasType.stratifyN` lands the four unstratified premises at a common index;
`PropTypeAgreeN` carries `IsPropN Γ A` to `IsPropN Γ A'` there; `PropUniqN` reads the level
back off `A'`'s two sort typings.  The `.conv (.sortDF …)` step is why the index is `N+1`
(`sortDF` concludes one index up, `conv` wants both premises at one index, `Stratified.mono`
pays for it free).

**§10.3 turns out to be load-bearing, not a docstring correction.**  `nv = 0` is *essential*
to route B: `NEAudit.equivZero_iff_eval_zero` is what converts the model's pointwise
conclusion into the stratified side's `≈ .zero` shape, and at `nv ≥ 2` that step is refuted
(`propAgree_pointwise_not_from_equivZero`).  `PropTypeAgreeInput` is at `nv = 0`, so the one
instance H2 consumes is the one instance where the two streams compose at all.  Last round's
"cheapest thing found" is what makes this round's route exist.

**Anti-vacuity for route B, machine-checked**: `propUniqN_zero` and `propTypeAgreeN_zero`
prove both inputs **at the base index, at every environment, with no hypothesis**, through
`HasTypeN.uniq_zero` (`≡₀` is syntactic equality).  What that does *not* show — and the
distinction is kept deliberately — is that `∀ n` holds anywhere; `stratifyN` chooses the
index and it is not `0`.  The `∀ n` form is the other stream's open target, and route B is the
statement that closing it closes the model's import.

### 11.2 The residual, and the correction that matters most

The guard is common to **both** routes and neither removes it: the only bridge from
unstratified `HasType` to `HasTypeN` is `HasType.stratifyN`, which takes
`OnCtx Γ (env.IsType U)` because `IsDefEq.strong` does — `Strong.lean`'s `CtxStrong` *is*
"every entry is a type", by definition, so this is not bookkeeping that can be shaved.

> **`NotProofNoModel.lean` §5 is wrong that the gap is `IsDefEqU.weakN_iff`.**  `weakN_iff` is
> stated over `Ctx.LiftN n k Γ Γ'` at a **lifted** term, so the entries it deletes are exactly
> the ones the derivation never mentions.  A junk entry that is *looked up* is outside its
> reach.  Machine-checked witnesses, at **every** `Ordered` environment:
> `not_onCtx_junk : ¬ OnCtx [.bvar 0] (env.IsType 0)` (`.bvar 0` is not `ClosedN 0`, so it
> inhabits no sort in `[]`), `hasType_junk_sort` (typing *is* derivable there, so the extra
> quantifier range is inhabited and the gap is not vacuous), and
> `hasType_junk_lookup : env.HasType 0 [.bvar 0] (.bvar 0) (.bvar 1)` — a derivation in the
> junk context whose subject *is* the junk entry.

So the residual is **context replacement**, not deletion: `CtxReplace` in the new file.  It is
not one of the four holes, it has no consumer anywhere else in the tree, and nobody is working
on it.

**And it should not be proved.**  `NotProofNoModel.lean` §5's own alternative is cheaper and it
is now the recommendation: **guard `PropSplit`'s two fields with `OnCtx`** (priced there at 64
call sites through `isProp_iff`/`isProof_iff`, ~40 of them in `SetModel/QuotInterp.lean`, plus
`soundAbove` carrying `OnCtx` beside `CtxClosed` — the induction already builds
`⟨hΓ, _, h.hasType⟩` at every binder).  With that edit, `Nonempty (PropSplit preludeEnv 0)` is
**a theorem** — route A discharges it modulo `forallE_inv_stratified`, route B modulo the other
stream's `PropTypeAgreeN`/`PropUniqN`, and `PropUniq` is free at the consumer as §10.2 says.
That is the single highest-value edit in this corner and it is a flag day, not a proof.

### 11.3 The §10.9 bridge: audited, and it exists

§10.9 item 1 names the remaining bridge as `HasTypeN U n` ↔ `HasType 0` and says to check
`Theory/Typing` first.  Checked (`lean_local_search` is unusable in this tree — no `rg` on
PATH — so this is `lean_run_code` type-checking the candidates plus structural greps over
declaration headers, reported as such):

* **`→` exists and is what both routes use.**  `VEnv.HasType.stratifyN`
  (`Theory/Typing/Stratified.lean`, reference basics (3)/(4)), `[propext, Quot.sound]`,
  **no `sorryAx`** — with `Ordered env` and `OnCtx Γ (env.IsType U)`.  Restated at
  `preludeEnv` as `stratifyN_at_preludeEnv` so the `Ordered` half is discharged and the
  `OnCtx` half is visible.
* **`←` is absent, deliberately**, and that file says so: it needs `IsDefEq.uniq` because
  `IsDefEqN`'s `conv` is three-place while `IsDefEq.defeqDF` demands a type.  Route B does not
  use it, so §10.9's "the remaining bridge" is **not** the obstruction — the obstruction is the
  `OnCtx` the existing bridge carries.

### 11.4 Audit of the briefing — where it is wrong

| claim as briefed | verdict |
|---|---|
| `PropTypeAgree preludeEnv 0` is the vacuity guard for the entire `.induct` corner | **correct**, and unchanged: `nonempty_propSplit_preludeEnv_iff` + `PropUniq.of_propTypeAgree` |
| §7.6: `PropTypeAgree 0` is irreducible, no choice of predicate removes it, do not spend a round there | **half right, and the half that is wrong sent five rounds the wrong way.**  "No choice of predicate removes it" is right about `PropSplit`'s *fields* (that is `nonempty_propSplit_iff_agree`).  "Irreducible" is **false**: it factors as guarded statement + context guard, the guarded half is a theorem at `preludeEnv` **today**, and it has a second route that touches no hole |
| §10.9 item 1: the remaining bridge is `HasTypeN U n` ↔ `HasType 0` | **wrong about which half and about what it costs.**  The needed half exists, sorry-free (§11.3); the converse is not needed.  What the bridge *does* cost is `OnCtx`, which is the actual residual |
| does it reduce to `forallE_inv_stratified`, `rigidShapeUniqNS`, `weakN_iff`, or `descend`? | **the guarded half reduces to `forallE_inv_stratified` alone** (cone-measured), and to nothing at all on route B.  The unguarded half reduces to **none of the four** — `weakN_iff` provably does not supply it (§11.2) |
| "H2's model side and the nine refinement holes may share a wall" | **refuted as a structural claim.**  They share one route out of two.  The corner's true blocker is a statement (`CtxReplace`) that no other part of the tree wants, and the cheap fix is an edit to `PropSplit`, not a proof |
| the correction that "the instance at `preludeEnv` is a different object" is false | **correct, and it cuts both ways**: the guarded statement at `preludeEnv` is not *easier* for being restricted — it is discharged because `preludeEnv_WF` is a theorem (row 128), not because the environment is small |

### 11.5 Tried and failed, with the step it failed at

1. **Refuting `PropTypeAgree preludeEnv 0` at a junk context.**  Got as far as: `IsDefEq`'s
   only retyping rule is `defeqDF`, which converts **at a sort**, so any two types of one term
   are joined by a sort-conversion; a counterexample therefore needs a failure of `PropUniq`
   (two sort typings of one type at differing propositionhood) or of `PropConvInv` — the same
   content one level in.  Junk contexts do **not** help: `propUniq_of`'s and
   `propTypeAgree_of`'s `bvar` cases use `Lookup.uniq`, not the entry being a type, so the
   stratified statements carry **no context guard at all**.  Not claimed as a negative
   (`docs/vacuity-ledger.md` §0 kind 4); the file says so in its own words.
2. **Deriving `CtxReplace` from `weakN_iff`.**  Failed at the referenced entry — §11.2.  This
   is what turned into the correction.
3. **Weakening `IsDefEq.strong`'s context hypothesis** so the unguarded statement is reachable.
   Failed at the definition: `CtxStrong env U Γ := OnCtx Γ fun Γ A => ∃ u, IsDefEqStrong U Γ A A (.sort u)`
   — the guard is what "strong" *means*, and `IsDefEqStrong` ships a type's typing at every
   node.  This is a `Theory/Typing` file, so it was read, not edited.
4. **`PropTypeAgree → sort_not_proof → sort_inv → SortUniq → forallE_inv_stratified` as a
   *lower* bound** (i.e. "proving it would prove the hole").  Step 1 is machine-checked
   (`sortNotProof_of_propTypeAgree`, sorry-free, no `OnCtx`); step 2 is **prose only** in
   `PiLevelPin.lean` §"Where the demand actually comes from" ("with it, `sort_inv` follows from
   `WF.rigidShapeUniq` alone"), and step 4 needs `UniqTy` on top of `SortInv`
   (`SortUniqDown.sortUniq_of`).  Not attempted — it is a `Theory/Typing` result, and it is a
   *consequence* of `PropTypeAgree`, not a bound on it.  **Named here because it is a real
   opportunity for whoever owns `Theory/Typing`: an independent `sort_not_proof` plus
   `rigidShapeUniq` is claimed to give `sort_inv` without `forallE_inv_stratified`, and
   `sortNotProof_of_propTypeAgree` already supplies the first input from a strictly weaker
   hypothesis than `SortUniq` and with `OnCtx` dropped.**
5. **`lean_local_search` / `lean_hammer_premise`** — unusable: the MCP tool requires `rg` on
   PATH and it is not installed.  Every "checked with the LSP" claim here is
   `lean_run_code` / `lean_diagnostic_messages`, and every "checked by grep" is labelled.

### 11.6 Measured / read / not run

**[measured]** `lake build`: **1504 jobs** (1503 before — the new file), "Build completed
successfully", **0 errors in any file I own**.  Guards, verbatim:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard` green (1431 jobs), same
three guards.  `scripts/sorry-census.lean`: **TOTAL 13**, **no row changed, none traded, no new
hole**.  `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined
cone".  `#print axioms` on all 14 new theorems: `[propext]`, `[propext, Quot.sound]`,
`[propext, Classical.choice, Quot.sound]`, or — for the **four** that go through route A —
`[propext, sorryAx, Classical.choice, Quot.sound]`, `sorryAx` there being
`forallE_inv_stratified` and nothing else.  **No frozen axiom, nothing new on the frozen
cone.**  Route B's four declarations (`propTypeAgreeOnCtx_of_stratifiedN`, `propUniqN_zero`,
`propTypeAgreeN_zero`, `preludeEnv_propTypeAgreeOnCtx_of_stratifiedN`) are `sorryAx`-**free**.

Hole user counts as of this commit: `forallE_inv_stratified` **718**, `rigidShapeUniqNS`
**460**, `weakN_iff` **312**, `descend` **200**.  Four of the 718 are this file's route-A
declarations; the rest of the movement since the last recorded figures is not mine to
attribute — a second stream is live in the tree.

**[read]** off source, not run: `PiLevelPin.lean`'s claim that `sort_not_proof` + `rigidShapeUniq`
gives `sort_inv` (prose in that file, §11.5 item 4); the 64-call-site price of guarding
`PropSplit`'s fields (`NotProofNoModel.lean` §5's own count, not re-counted here); and
§11.5 item 1's "the stratified statements carry no context guard at all" — that is inspection
of `propUniq_of`'s and `propTypeAgree_of`'s `bvar` cases in `Theory/Typing/PropConv.lean`
(they use `Lookup.uniq`, never that the entry is a type), not a theorem.

**[not run]** the Kernel Arena (no implementation file changed); `scripts/hole-cone.lean` and
`scripts/hole-rank.lean` as shipped — the cone measurement used a private copy of
`hole-cone.lean`'s algorithm seeded at the five declarations of interest, because the shipped
seed list is another stream's.

### 11.7 What to pick up first

1. **Guard `PropSplit`'s two fields with `OnCtx`.**  This is the item, and it is an edit rather
   than a proof: it converts `Nonempty (PropSplit preludeEnv 0)` from open into a theorem
   modulo `forallE_inv_stratified` (route A) — or modulo the other stream's own targets
   (route B) — and it retires `CtxReplace` entirely.  Price: `soundAbove` carries `OnCtx`
   beside `CtxClosed` (cheap; `ctxClosed_of_isType` recovers the rest) and 64 call sites of
   `isProp_iff`/`isProof_iff` each discharge an `OnCtx` for their own context, ~40 of them in
   `SetModel/QuotInterp.lean` at hand-built contexts.  Read `NotProofNoModel.lean` §5 before
   starting; it priced this and nobody funded it.
2. **Tell the `Theory/Typing` stream about route B.**  `propTypeAgreeOnCtx_of_stratifiedN`
   means `PropTypeAgreeN` + `PropUniqN` at every index buys the model's entire syntactic
   import at `nv = 0`.  That is a consumer those two statements did not know they had, and it
   is `sorryAx`-free.  The blocking residuals on that side are `SortForallEDisjoint`
   (`UniqueTypingN.lean` — `AppCase` walled on both sides) and `PropUniqN.AppCase`
   (`PropConv.lean`), plus `DefInv`/`SortInvN` at every index, which is `unique.tex` §§3–4
   transcribed over `IsDefEqN` and nobody has written it.
3. **`iffIndDecl` before `eqIndDecl`** — unchanged from §10.9 item 2, and now the *only*
   remaining `.induct` frontier at a prelude block.
4. **`InstDescendUp 0`'s `.bvar k` case** — unchanged from §7.9, §8.7, §9.7 and §10.9, and
   still untouched.  Note that §11 does **not** touch `InstDescendUp`: `ModelFits` needs it
   independently.

**Do not** re-attack: everything §10.9's list names, plus — new — **`weakN_iff` as the route to
the unguarded `PropTypeAgree`** (refuted, §11.2) and **`PropTypeAgree preludeEnv 0` as an
instance of the injectivity wall** (it is not, §11.0; the guarded half is already discharged).

## 12. Session of 2026-09-02 (fifth): the `OnCtx` guard on `PropSplit` is DONE — `Nonempty (PropSplit preludeEnv 0)` is a theorem, and `CtxReplace` is retired

### 12.0 The result, plainly

**`PropSplit`'s two fields now carry `OnCtx Γ (env.IsType nv)`, and
`Nonempty (PropSplit preludeEnv 0)` is a theorem with no hypotheses.**  §11.2's recommendation
was right, and §11's residual `CtxReplace` has **no consumer left** in the tree.

```lean
-- Theory/SetModel/Interp.lean (the real definition; see 12.1)
structure PropSplit (env : VEnv) (nv : ℕ) where
  …
  prop_sound  : ∀ {ls Γ A u},   OnCtx Γ (env.IsType nv) → u.WF nv → env.HasType nv Γ A (.sort u) →
                                (IsPropAt ls Γ A ↔ u.eval ls = 0)
  proof_sound : ∀ {ls Γ e A u}, OnCtx Γ (env.IsType nv) → u.WF nv → env.HasType nv Γ e A →
                                env.HasType nv Γ A (.sort u) → (IsProofAt ls Γ e ↔ u.eval ls = 0)

-- Theory/SetModel/PropSplitAudit.lean  (the guarded producer)
noncomputable def propSplitOfOnCtx (env) (nv) (hU : env.PropUniqOnCtx nv)
    (hT : env.PropTypeAgreeOnCtx nv) : PropSplit env nv
theorem exists_propSplit_onCtx (hU) (hT) : Nonempty (PropSplit env nv)

-- Theory/SetModel/PreludeOracle.lean  (the payoff; NO hypotheses)
theorem nonempty_propSplit_preludeEnv : Nonempty (PropSplit preludeEnv 0)
noncomputable def propSplitPreludeEnv : PropSplit preludeEnv 0     -- as data

-- Theory/SetModel/PropAgreeWall.lean  (route B, sorryAx-FREE, hypothesis-carrying)
theorem propUniqOnCtx_of_stratifiedN (henv : Ordered env) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropUniqOnCtx 0
theorem nonempty_propSplit_of_stratifiedN (henv) (pta : ∀ n, env.PropTypeAgreeN 0 n)
    (pun : ∀ n, env.PropUniqN 0 n) : Nonempty (PropSplit env 0)
```

**Modulo exactly what.**  My brief said "modulo nothing at all via route B"; that is **wrong,
and the correction matters**:

| route | hypotheses | axioms |
|---|---|---|
| **A** — `nonempty_propSplit_preludeEnv` | **none** | `[propext, sorryAx, Classical.choice, Quot.sound]`; the `sorryAx` is `IsDefEqU.forallE_inv_stratified` and nothing else |
| **B** — `nonempty_propSplit_of_stratifiedN` | `Ordered env` + `∀ n, PropTypeAgreeN env 0 n` + `∀ n, PropUniqN env 0 n` (the other stream's open targets) | `[propext, Classical.choice, Quot.sound]` — **`sorryAx`-free** |

So: *unconditional* modulo one hole, or *hole-free* modulo two hypotheses.  There is no route
that is both, and claiming one would be the ledger's blindness 4.

### 12.1 Correction to the brief, before anything else

* **`PropSplit` is declared in exactly one place**: `Theory/SetModel/Interp.lean:391`.  What
  `InterpSubst.lean:121` declares is **`PropSplit.Stable`**, a *different* structure over a
  `PropSplit`.  There is no re-export and there never was; the brief's "establish which is the
  real definition and which the re-export" has no second candidate.
* **The 64-call-site price is a 2.5× undercount** (see 12.4).
* **"~40 of them in `QuotInterp.lean`"** — it is **88** there.

### 12.2 What landed, file by file (15 files, all in `Theory/SetModel/`)

| file | what changed |
|---|---|
| `Interp.lean` | the guard on both fields; `prop_congr`/`proof_congr` gain `hΓ`; `LevelAssign.toPropSplit` ignores it; new `import Theory.Typing.Lemmas` (for `OnCtx`) |
| `PropSplitAudit.lean` | `PropTypeAgreeOnCtx`/`PropUniqOnCtx` **moved here** from `NotProofNoModel.lean` (they are now inputs of the producer, three files earlier); `PropTypeAgree.onCtx`/`PropUniq.onCtx`; `onCtx_sortZero`; `propSplitOfOnCtx`, `exists_propSplit_onCtx`; `propSplitOf_isPropAt_iff`/`propSplitOf_isProofAt_iff` (the *unguarded* soundness of the `propSplitOf` instance, which `PropSplitUp.lean` needs and the fields no longer say) |
| `SoundInduction.lean` | **`soundAbove` now carries `OnCtx Γ (env₀.IsType nv)` instead of `CtxClosed Γ`** — §11.2's "the induction already builds `⟨hΓ, _, h.hasType⟩` at every binder" is correct; `ctxClosed_of_isType` moved above it and recovers `CtxClosed` in the five cases that still want it; `isProp_iff`/`isProof_iff` take `hΓ` **second** (`isProp_iff hle hΓ hA hw`); new `onCtxF` transports the guard along `env₀ ≤ envF` |
| `InterpSound.lean` | `PropSplit.mono` transports the guard by `OnCtx.mono (·.mono h)` |
| `Cnst.lean` | the four general helpers (`pt_mem_interp_forallE_prop`, `mkLam_mem_interp_forallE(')`, `interp_app_of_proof_sorted`, `interp_lam_congr_of_type`) gain `hΓA`/`hΓ` |
| `FalseProp.lean` | `not_isProp_sort_zero` gains `hΓ`; `isType_falseProp`/`onCtx_falseProp` **moved here** from `NotProofNoModel.lean` |
| `NotProofNoModel.lean` | `propTypeAgree_of_propSplit` → **`propTypeAgreeOnCtx_of_propSplit`**, `propUniq_of_propSplit` → **`propUniqOnCtx_of_propSplit`**, `nonempty_propSplit_iff_agree` now the **guarded** iff, `sortNotProof_of_propSplit` gains `OnCtx Γ` |
| `PropSplitUp.lean` | fields ignore the guard; the two comparison lemmas go through the new `propSplitOf_*_iff` |
| `QuotInterp.lean` | **16 + 16 new `onCtxQ_*` spine lemmas** (`Δ`-general and at `Δ = []`), 88 applications repaired; `interp_quotIndQ` gains `hqm`, `interp_quotLiftQ` gains `heq`/`hv`, `interp_quotLiftRab` gains `hv`, `quotLift_f_props` gains `hu`, `interp_quotDefMkAp` gains `heq`/`hv`, `interp_quotDefRhsBody` gains `heq` |
| `UnitOracleWitness.lean` | 4 new `onCtxU_*`; 12 readings + `motive_app_mem_UProp`, `pt_mem_of_mem_motive_app`, `exists_true_motive` gain the guard |
| `UnitOracleLarge.lean` | 4 new `onCtxL_*`; 20 readings + `interpL_motTyU`, `interpL_minTy_at`, `motiveL_app_mem_U` gain it |
| `PreludeOracle.lean` | 7 new `onCtxNE_*` (one per named context `ctx1…ctxM`); 19 readings + `interp_NEapp`, `mem_interp_NE_type` gain it; **`nonempty_propSplit_preludeEnv` and `propSplitPreludeEnv`** land here |
| `PropAgreeWall.lean` | route B's missing half (`propUniqOnCtx_of_stratifiedN`), `nonempty_propSplit_of_stratifiedN`, the retirement statement, and §6's anti-vacuity block |
| `CoherentWitness.lean`, `AboveAudit.lean` | one guard each |

### 12.3 Anti-vacuity — because the edit *narrows a quantifier*

Run in both directions, machine-checked, in `PropAgreeWall.lean` §6:

1. **The narrowing is real.**  `not_onCtx_junk` + `hasType_junk_sort` (already there from §11)
   say the guard excludes a context in which typing *is* derivable.  The guarded fields say
   strictly less than the unguarded ones.  That is the price, and it is paid knowingly: nothing
   in the tree ever proved the unguarded statements, at any environment.
2. **The narrowed structure is still non-degenerate.**  `witness_not_isPropAt_prop`,
   `witness_isPropAt_bvar`, `witness_not_constant` — `PropSplitAudit`'s "both branches fire"
   check, re-run **at the witness object** rather than at the class.  The `bvar` instance lives
   at `[Prop]`, which the guard admits (`onCtx_sortZero`), so the check did not survive by
   moving to a context the guard rejects.
3. **The class is inhabited where the recursion goes.**  `propSplitPreludeEnv` is a
   `PropSplit preludeEnv 0` **as data**, no hypotheses.
4. **Nothing is stranded.**  All ~161 guard-consuming applications discharge the guard at their
   own context; **no obligation was pushed up as a hypothesis of an `OracleOK`/`InductOracleOK`
   result** (that would have been ledger blindness 8 in a new costume).  The one statement that
   another stream might notice getting weaker is
   `NotProofNoModel.sortNotProof_of_propSplit`, which now takes `OnCtx Γ (env.IsType nv)` — it
   has **no Lean consumers** (grep: only prose mentions in `Theory/Typing/SortUniq.lean` and
   `InjSpineTransport.lean`), and those prose consumers supply exactly that guard anyway
   (`onCtx_falseProp`).  **`sortNotProof_of_propTypeAgree`'s statement is unchanged** — it
   takes the *unguarded* `VEnv.PropTypeAgree`, whose definition I did not touch.

### 12.4 The true call-site count — measured, not read

`NotProofNoModel.lean` §5's "64 call sites, ~40 of them in `QuotInterp.lean`" is **low by
about 2.5×**, and the QuotInterp figure is out by 2×.  Measured three independent ways:

* **`lake build` error count at the moment each file first broke** (this is the sharpest
  number, because it *is* "sites that need repair"): `QuotInterp` **83**, `PreludeOracle`
  **61**, `UnitOracleLarge` **54**, `UnitOracleWitness` **32**, `Cnst` **8**, `PropSplitUp`
  **8**, `FalseProp` **2**, `AboveAudit` **2**, `CoherentWitness` **1** — plus
  `SoundInduction`, `Interp`, `InterpSound`, `PropSplitAudit`, `NotProofNoModel` which I
  repaired before they could break.  (Lean emits ~2 errors per site, so this is an upper
  bound on errors and a lower bound on nothing.)
* **Inserted arguments, counted in the diff against `git show HEAD:`**: **161** applications
  gained a guard argument, **88** of them in `QuotInterp.lean`.  This is a floor — the regex
  only matches the `… hle X` shapes.
* **Signatures**: **100** new `(hΓ/hΔ/hΓA : OnCtx …)` binders tree-wide, of which ~30 are the
  new spine lemmas' own hypotheses and ~70 are consumer theorems that had to acquire the guard.

**And the qualitative shape of the cost was mis-priced too.**  §5 says each site "would have
to discharge a fresh `OnCtx` obligation for its own context, and those obligations are not
currently proved anywhere".  True, but they are *cheap and systematic*: every hand-built
context in those four files is the binder telescope of a declared constant's type, and the
entry-by-entry typing derivation was **already in the file** (`quotRelTy_type`,
`quotIndHyp_type`, `quotLiftC_type`, `hasTypeL_motTy`, `hasType_minTy`, …).  So the whole
obligation set collapses to **47 `OnCtx` lemmas of two to four lines each** — 32 in `QuotInterp.lean` (half of
them the `Δ = []` specialisations the elaborator needs, 12.5 item 2), 4 + 4 + 7 in the three
oracle files — one per distinct context, and the rest is argument threading.  There is **no new mathematics in this edit** —
which is what "a flag day, not a proof" should have meant, and §5 did not say.

### 12.5 What I tried that failed, and the step it failed at

1. **Harvesting the needed contexts from the compiler.**  Inserted `trivial` at all **41**
   `isProp_iff`/`isProof_iff` sites in `QuotInterp.lean` intending to read the expected
   `OnCtx Γ …` off the error messages.  **Failed at elaboration order**: the guard argument is
   checked *before* `Γ` is solved, so every message reads `OnCtx ?m.344 (env₀.IsType ?m.341)`.
   Recovered by reading the enclosing `have hnp… : ¬ L.IsProof M ⟦ctx⟧ …` statements out of the
   source instead — which is grep, and is labelled as such.
2. **Stating the spine lemmas only in `Δ`-general form.**  `onCtxQ_alpha hu trivial` fails
   because `Δ` is a metavariable when `trivial : True` is checked against `OnCtx ?Δ …`.  Fixed
   by adding 16 `Δ = []` variants (`onCtxQ_sort'`, …); the same bug then recurred three more
   times in `UnitOracleLarge.lean`, where `(Γ := [])` was the cheaper fix.
3. **`OnCtx.toF` by dot notation.**  Declared inside `namespace Lean4Lean.SetModel`, so its
   real name is `SetModel.OnCtx.toF` while `hΓ.toF` looks for `Lean4Lean.OnCtx.toF`.  Renamed
   to a plain `onCtxF`.  Same class of failure at `(… : env.PropUniq nv).onCtx`: `PropUniq`
   whnf's to a `∀`, so dot notation resolves against `Function`.  Use the qualified name.
4. **Guarding with something weaker than `OnCtx`.**  Considered and rejected on paper before
   starting: the guard has to *imply* `OnCtx` (because `IsDefEq.uniqU` and `IsDefEqU.sort_inv`
   need it, via `IsDefEq.strong`'s `CtxStrong`) and has to be *provable at the call sites*, and
   `hasType_junk_lookup` shows nothing derivable from the typing premise alone can do the first
   job.  Not attempted in Lean; recorded as reasoning, not as a theorem.
5. **Leaving the obligations as hypotheses of the oracle theorems** (the cheap way out).
   Rejected: `docs/vacuity-ledger.md` §0's eighth blindness — an obligation carried as a
   hypothesis counts as zero — and it would have moved the vacuity from `PropSplit` to
   `InductOracleOK` rather than removing it.

### 12.6 Measured / read / not run

**[measured]** `lake build`: **1506 jobs** (1505 before — the guard adds no module; the +1 is
noise from the other live streams' files), "Build completed successfully", **0 errors in any
file**, mine or anyone's.  Guards, verbatim:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: green, **1432 jobs**, same
three guards verbatim.  `scripts/sorry-census.lean`: **TOTAL 13**, **no row changed, none
traded, no new hole**.  `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across
the joined cone".  Hole user counts: `forallE_inv_stratified` **725** (718 → 725; the +7 are my
seven route-A declarations, `nonempty_propSplit_preludeEnv`, `propSplitPreludeEnv`,
`nonempty_propSplit_preludeEnv_no_ctxReplace`, `witness` and its three checks),
`rigidShapeUniqNS` **460**, `weakN_iff` **312**, `descend` **200** — the last three unmoved.
`#print axioms` on everything added or materially changed: `[propext]`, `[propext, Quot.sound]`,
`[propext, Classical.choice, Quot.sound]`, or `[propext, sorryAx, Classical.choice, Quot.sound]`
for the route-A ones, the `sorryAx` being `forallE_inv_stratified` alone.  **No frozen axiom
anywhere; nothing new on the frozen cone.**  Route B's chain
(`propUniqOnCtx_of_stratifiedN`, `nonempty_propSplit_of_stratifiedN`,
`nonempty_propSplit_preludeEnv_of_stratifiedN'`) is `sorryAx`-**free**.

**[read]** off source, not run: that the `Theory/Typing` consumers of
`sortNotProof_of_propSplit` supply `OnCtx Γ (env.IsType U)` — that is `NotProofNoModel.lean`
§4's own claim about `Theory/Typing/Injectivity.lean`'s call sites, and this round did not
re-check it (the lemma has no Lean consumers, so nothing depends on it being true).  Also
grep-level, not LSP: the "no Lean consumers of `sortNotProof_of_propSplit`" claim itself.

**[not run]** the Kernel Arena (no implementation file changed).  `lean_local_search` and
`lean_hammer_premise` were **not usable** (row 131f confirmed again: `which rg` → nothing), so
every search in this round was `grep`/`sed` over source plus `lake build` diagnostics; there is
no "exhaustive search" claim in this section that rests on anything stronger.

### 12.7 What to pick up first

1. **Route B's two inputs are now the model corner's *entire* remaining syntactic import.**
   `∀ n, PropTypeAgreeN env 0 n` and `∀ n, PropUniqN env 0 n` at `preludeEnv` buy
   `Nonempty (PropSplit preludeEnv 0)` with **no hole of any kind**
   (`nonempty_propSplit_of_stratifiedN`).  That is a strictly better deal than route A and it
   is the `Theory/Typing` stream's own target; tell them the consumer exists.
2. **`CtxReplace` is retired — do not fund it.**  `PropAgreeWall.CtxReplace` and its two
   reductions are kept as the record of what the *unguarded* `VEnv.PropTypeAgree` costs, and
   `nonempty_propSplit_preludeEnv_no_ctxReplace` is the one-line proof that nothing needs them.
   `VEnv.PropTypeAgree` itself survives only as the hypothesis of
   `sortNotProof_of_propTypeAgree`.
3. **`iffIndDecl` before `eqIndDecl`** — unchanged from §10.9/§11.7, and now the only remaining
   `.induct` frontier at a prelude block whose *parameter* is known inhabited.
4. **`InstDescendUp 0`'s `.bvar k` case** — unchanged from §7.9 onward, untouched again.
5. **A cheap follow-up nobody has done**: the 47 new `onCtx*` spine lemmas make the four oracle
   files' hand-built contexts first-class objects.  Anything else that wants "this telescope is
   a well-formed context" (`SoundInduction.sound` at a non-empty context, `interp_congr`)
   can now take them off the shelf.

**Do not** re-attack: everything §10.9 and §11.7 name, plus — new — **`CtxReplace`**
(retired, 12.0), **`weakN_iff` as its route** (refuted, §11.2), and **guarding `PropSplit`**
(done).
