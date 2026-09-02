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

---

## 13. Session of 2026-09-02 (sixth): **`InstDescendUp 0`'s `.bvar k` case is CLOSED** — and it was never the sharpest mathematics, it was a missing guard

### 13.0 The result, plainly

`Theory/SetModel/InstDescendBvar.lean` (new, 616 lines, 46 declarations, **no `sorry`**) proves the
`B = .bvar k` instance of **both** fields of `VEnv.InstDescendUp`, at **every** `k`, with exactly
one change to the field's statement: the premise's *witness context* carries `OnCtx`.

```lean
-- §4, the headline.  Compare InstDescendUp.prop_inst with B := .bvar k.
theorem VEnv.prop_inst_bvar (henv : env.Ordered) (hR : env.SortRetypeOnCtx nv)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ (.bvar k)
theorem VEnv.proof_inst_bvar (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv) … (analogous)

-- §6, from `env.WF` and nothing else:
theorem VEnv.prop_inst_bvar_of_wf  (henv : env.WF) …
theorem VEnv.proof_inst_bvar_of_wf (henv : env.WF) …

-- §8b, and this one is `sorryAx`-FREE:
theorem SetModel.InstDescendBvar.proof_inst_bvar_of_stratifiedN (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) … 
```

`VEnv.IsPropUpOn` / `IsProofUpOn` are `IsPropUp` / `IsProofUp` with
`OnCtx Γ' (env.IsType nv)` demanded of the context their existential produces — the same guard
`PropSplit`'s two fields acquired in §12.  **The conclusion is the unguarded predicate**, i.e.
literally what `InstDescendUp` asks for.

Three things follow, and each is measured rather than argued:

1. **§7.3 was right about *what* the case needs and wrong about *how hard* it is.**  The content is
   `SortRetypeOnCtx` — "a term with a type *and* a sort has that type convertible to that sort" —
   which is the `B = .sort u` instance of `IsDefEq.uniq`, a theorem the tree has had all along
   (`sortRetypeOnCtx_of_wf`, one line).  For `proof_inst` the demand is weaker still: `A₀` need
   only *have* a vanishing sort, which is `PropTypeAgreeOnCtx` + `IsDefEq.isType`
   (`propTypeAgreeOnCtx_retype`, four lines, **`sorryAx`-free**).
2. **No strengthening, anywhere.**  The conclusion's witness context is the premise's own witness
   context with one binder added (`A₀.lift' l :: Γ'`), so the uniqueness comparison happens where
   the premise supplied its typing and no defeq ever travels down a lift.  The general `k` reduces
   to `k = 0` for free, because `(.bvar k).inst e₀ k` is `e₀` lifted out of `Γ₀`
   (`VExpr.bvar_inst_self`) and `isPropUp_liftN` is free in **both** directions (§12/PropSplitUp §3).
3. **What is left is not mathematics.**  §7 of the new file names the residual in both framings and
   proves the reductions:
   * keep the premise unguarded ⇒ you owe `PropUpNormalise` (normalise `IsPropUp`'s witness
     context), which follows from `UnguardedStrengthen` = `IsDefEqU.weakN_iff` **with its
     `OnCtx Γ'` hypothesis deleted**.  That is *strictly stronger* than the tree's hole and is
     **not one of the four big holes**;
   * guard the premise (what landed) ⇒ the cost moves to `PropSplit.Stable`'s four still-unguarded
     fields.  `PropUpOnLiftAscend` is the single obligation that appears, and
     `isPropUpOn_liftN_up` shows it is free the moment the target context is guarded.  A §12-style
     flag day on `Stable`, with **no new mathematics**.

A by-product worth more than it looks: **`IsPropUpOn` is a strictly better predicate than
`IsPropUp`.**  `isPropUpOn_iff` / `isProofUpOn_iff` give `prop_sound` / `proof_sound` from the
**guarded** imports `PropUniqOnCtx` / `PropTypeAgreeOnCtx` — the ones that *are* theorems at
`preludeEnv` — whereas `isPropUp_iff` needs the unguarded `PropUniq` / `PropTypeAgree`, which are
not.  So `SetModel.propSplitUpOn` is a `PropSplit` from the same inputs as
`PropSplitAudit.propSplitOfOnCtx`, and `propSplitUpOnPreludeEnv` is one at `preludeEnv` **as data**.

### 13.1 Audit of the briefing — five checks, and three places it is wrong

| brief said | measured |
|---|---|
| the `.bvar k` case is named in §7.9, §8.7, §9.7, §10.9 — "four consecutive rounds" | **six**: §11.7 item 4 and §12.7 item 4 name it too.  Grep over `docs/handoff-setmodel.md` for `bvar k` |
| "has never been touched" | **correct** for `InstDescendUp`.  `InstDescendAudit.sortInstDescend0_bvar_forces_sort` is the `.bvar 0` instance of `SortInstDescend0` — the *canonical*-predicate residual, a different statement — and it derives a *demand* rather than proving a case |
| "the sharpest open mathematics on the model side" | **wrong, and it has been wrong for six rounds.**  The mathematics is one application of `IsDefEq.uniq`; what was open is the statement's shape.  This is the same mis-costing §12 found for `PropSplit`'s missing guard, one layer down |
| "and it is now also the sharpest *non-vacuous* one" | half right.  `PropSplit preludeEnv 0` is inhabited, but that is not what makes *this* statement non-vacuous — `InstDescendUp` quantifies over junk contexts, and §8 of the new file exhibits premise-and-conclusion witnesses at `preludeEnv` directly (`bvar_zero_instance`, `bvar_one_instance`) rather than inheriting non-vacuity from the class |
| "does it depend on any of the four big holes … it is the kind of question this corner has answered wrongly before" | **answered by measurement, §13.3: on exactly one, `forallE_inv_stratified`, and only for the `prop_inst` half; the `proof_inst` half depends on none.  Not `weakN_iff`, not `rigidShapeUniqNS`, not `descend`** |

One further correction, to this file's own §7.3: **its case table does not transfer from
`SortInstDescend0` to `InstDescendUp`.**  §7.3 lists `.bvar i (i ≠ k)` as free.  For
`InstDescendUp`, whose predicate re-chooses a witness context, `i > k` is free
(`prop_inst_bvar_high`) but **`i < k` is not** — there the variable points at an entry of `Γ₁`
whose `Γ`-counterpart is its own instantiation, so the case is a *smaller instance of the same
descent*, not a transport.  §9 of the new file records this and closes the classes that are
genuinely free: every closed `B` (so `.sort`, `.const`) and `.bvar (k+j+1)`.

### 13.2 What landed

One new file, `Theory/SetModel/InstDescendBvar.lean`, imports `SetModel.PropAgreeWall` and
`Theory.Typing.UniqueTyping`.  Nothing else in the tree changed — **no existing file was edited**,
so no other stream can be broken by this round.

| § | content |
|---|---|
| 1 | `Ctx.InstN.eq_append` / `.liftN_target` / `.liftN_source` — `Ctx.InstN` exposes `Ctx.LiftN k 0 Γ₀ Γ` and `Ctx.LiftN k 0 (A₀::Γ₀) Γ₁`; `VExpr.bvar_inst_self`, `bvar_zero_liftN` |
| 2 | `SortRetypeOnCtx` + `sortRetypeOnCtx_of_wf`; `propTypeAgreeOnCtx_retype` |
| 3 | `IsPropUpOn` / `IsProofUpOn`, `of_hasType`, `isPropUp`/`isProofUp` (forget the guard), `of_lift'` / `of_liftN` (guard-preserving descent) |
| 4 | `isPropUpOn_bvar_zero`, `isProofUpOn_bvar_zero` (the `k = 0` core), `prop_inst_bvar`, `proof_inst_bvar` |
| 5 | `isPropUpOn_iff`, `isProofUpOn_iff`, `SetModel.propSplitUpOn` |
| 6 | `prop_inst_bvar_of_wf`, `proof_inst_bvar_of_wf`, `prop_inst_bvar_on_of_wf` |
| 7 | `PropUpNormalise`, `UnguardedStrengthen`, `propUpNormalise_of_unguardedStrengthen`, `prop_inst_bvar_of_normalise`, `PropUpOnLiftAscend`, `isPropUpOn_liftN_up` |
| 8 | anti-vacuity at `preludeEnv`; 8b route B |
| 9 | the free part: `prop_inst_of_liftN`, `prop_inst_closed`, `prop_inst_bvar_high` (+ proof twins) |

### 13.3 The dependence question, measured

Forward hole-cone over type **and** value with `allowOpaque := true` (the `scripts/hole-cone.lean`
walker, re-seeded on this file's declarations and run out of `/tmp`; every cone's *complete* list of
`sorryAx`-carrying members is reported, not just the four named holes).

| seed | four big holes in cone | all `sorryAx` members of cone |
|---|---|---|
| `Ctx.InstN.liftN_target` / `.liftN_source` | none | none |
| `isPropUpOn_bvar_zero`, `isProofUpOn_bvar_zero` | none | none |
| **`prop_inst_bvar`, `proof_inst_bvar`** | **none** | **none** |
| `propTypeAgreeOnCtx_retype` | none | none |
| `isPropUpOn_iff`, `isProofUpOn_iff`, `propSplitUpOn` | none | none |
| `prop_inst_of_liftN`, `prop_inst_closed`, `prop_inst_bvar_high` | none | none |
| `propUpNormalise_of_unguardedStrengthen`, `isPropUpOn_liftN_up` | none | none |
| **`proof_inst_bvar_of_stratifiedN`** | **none** | **none** |
| `sortRetypeOnCtx_of_wf` | `forallE_inv_stratified` | `forallE_inv_stratified` |
| `prop_inst_bvar_of_wf`, `proof_inst_bvar_of_wf`, `prop_inst_bvar_of_normalise` | `forallE_inv_stratified` | `forallE_inv_stratified` |
| `preludeEnv_sortRetypeOnCtx`, `propSplitUpOnPreludeEnv`, `bvar_zero_instance`, `bvar_one_instance`, `not_isPropUpOn_sort` | `forallE_inv_stratified` | `forallE_inv_stratified` |

`IsDefEqU.weakN_iff` and `WF.rigidShapeUniqNS` **are** in the module's import closure (checked by
`env.find?`) and appear in **no** cone — so this is "available and unused", not "unreachable".
`NormalEq.descend` is not even in the import closure (`env.find?` returns `none`).

`#print axioms` on all 40 declarations: `[propext]`, `[propext, Quot.sound]`,
`[propext, Classical.choice, Quot.sound]`, or — for the eight that route through `IsDefEq.uniq` /
`WF.propTypeAgreeOn` — `[propext, sorryAx, Classical.choice, Quot.sound]`.  **No frozen axiom
anywhere.  No new `sorry`, none traded.**

### 13.4 Anti-vacuity — run on the hypotheses *and* on both sides of the implication

This corner is the ledger's most exposed, so all four checks were run, machine-checked, at
`preludeEnv`:

1. **The hypotheses hold at `preludeEnv`, with nothing assumed.**
   `preludeEnv_sortRetypeOnCtx : preludeEnv.SortRetypeOnCtx 0` (from `preludeEnv_WF`), and
   `PropAgreeWall.preludeEnv_propTypeAgreeOnCtx` supplies the `proof_inst` input.  `preludeEnv` is
   the environment `PreludeWitness` builds from `leanPrelude.reverse` — not a chosen `κ`, no
   `Above` wrapper anywhere in this file (grep: zero occurrences of `Above`), and reached without
   any `VDecl.unsafeDef`.
2. **The premise is inhabited *and* discriminating.**  `bvar_zero_instance` exhibits
   `IsPropUpOn preludeEnv 0 ls [] ((.bvar 0).inst falseProp 0)` — the same configuration as
   `InstDescendAudit.sortInstDescend0_nonvacuous`, so the substitution genuinely substitutes — and
   `not_isPropUpOn_sort` proves `¬ IsPropUpOn preludeEnv 0 ls [] (.sort .zero)`, so the premise is
   not the constant-true predicate.  (That negative uses the **guarded** `PropUniqOnCtx`, which is
   a theorem at `preludeEnv`; `PropSplitUp.not_isPropUp_sort` needs the unguarded `PropUniq`,
   which is not — another place where the guard buys something.)
3. **The conclusion holds at those witnesses**, so the implication is not satisfied by a false
   antecedent: both conjuncts of `bvar_zero_instance` and `bvar_one_instance` are proved.
4. **The guard sits on the premise only, and that is checked rather than asserted.**
   `bvar_one_instance` runs at `k = 1` with `Γ₁ = [.bvar 0, Prop]`, a context that is **not**
   `OnCtx` (`PropAgreeWall.not_isType_bvar`), and the theorem still delivers.  So the conclusion
   really is the unguarded predicate over unguarded contexts, and the result is not the guarded
   statement in disguise.

Ledger blindness 4 (*an obligation carried as a hypothesis counts as zero*) applies to
`PropUpNormalise` / `UnguardedStrengthen` / `PropUpOnLiftAscend` and is **not** dodged: they are
labelled residuals, not results, and §13.7 says which one to fund.

### 13.5 What I tried that failed, and the step it failed at

1. **Refuting `InstDescendUp`'s `.bvar k` case at a junk context.**  Three configurations, all
   dead at the same step.  (a) `Γ₀ = [.bvar 0]`, `e₀ = .bvar 0`, `A₀ = .bvar 1`
   (`PropAgreeWall.hasType_junk_lookup`): the *premise* fails, because `.bvar 0`'s only type there
   is `.bvar 1` and converting it to a sort needs `HasType [.bvar 0] (.bvar 1) (.sort w)`, which
   `Lookup` cannot give.  (b) a rogue `env.defeqs` whose `extra` rule types a **bvar** at
   `.sort .zero` at every context: makes the premise true and *also* makes the conclusion true, at
   the lift that maps the conclusion's variable onto the same index.  (c) the same with a **closed**
   rogue left-hand side, which does separate premise from conclusion — but then the refutation needs
   `¬ HasType Γ'' (.bvar j) (.sort v)` for every `Γ''` above `Γ₁`, and `IsDefEq.closedN'` cannot
   supply it: its hypothesis is `CtxClosed Γ`, which a junk context fails by construction.
   **So the falsity of the unguarded statement is itself gated on a non-derivability argument.**
   Not attempted in Lean past reading `closedN'`'s binder; recorded as reasoning, per row 40's rule
   that an unproved negative is a conjecture.
2. **`HasType.weak'_iff` as the discharge of `PropUpNormalise`.**  Failed at its own binder:
   `variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in`
   (`Theory/Typing/UniqueTyping.lean`) — the guard is on the **larger** context, which is exactly
   `IsPropUp`'s possibly-junk witness context.  So `weakN_iff`, *as the tree states it*, does not
   reach this residual; `UnguardedStrengthen` is the strictly stronger statement that would.
   Read off source (grep + `lean_hover_info`), not run.
3. **`Ctx.Lift'.pushOut` for the general `k`.**  My first plan was to build a context above both
   `Γ₁` and the premise's witness context.  Abandoned before writing it: `OnCtx` of a pushout is
   not derivable from `OnCtx` of the two legs (each leg's `.skip` entries are arbitrary), and — the
   real killer — `Γ₁` is itself unguarded in `InstDescendUp`.  Replaced by "descend to `Γ₀`, then
   ascend freely", which needs no pushout at all.  *That is why §4 is twelve lines.*
4. **Guarding the conclusion too** (`IsPropUpOn` on both sides at general `k`).  Fails at the
   ascent `IsPropUpOn ls (A₀::Γ₀) → IsPropUpOn ls Γ₁`, which needs `OnCtx Γ₁`;
   `bvar_one_instance` is a real instance where `Γ₁` is junk.  So the mixed shape (guarded premise,
   unguarded conclusion) is the strongest available, not a convenience.
5. **`isPropUp_liftN` at the source for arbitrary `B`.**  Works only when `B.inst e₀ k` is a lift
   out of `Γ₀`.  §9 is exactly that class; `.bvar i` with `i < k` is what it excludes, which is how
   §13.1's correction to §7.3 was found.
6. **Elaboration friction, twice.**  `IsPropUpOn.of_hasType` and `isPropUpOn_iff` both need
   `(u := …)` / `(Γ := [])` given explicitly: the `u.WF nv` and `OnCtx Γ` arguments are checked
   before the later arguments solve `u` and `Γ`, so `trivial` meets a metavariable.  Same class of
   failure as §12.5 items 1–2.

### 13.6 Measured / read / not run

**[measured]** `lake build Lean4Lean.Theory.SetModel.InstDescendBvar`: green, **1210 jobs**
("Build completed successfully"), `lean_diagnostic_messages` on the file: **zero items** — no
errors, no warnings, no `sorry` warning.  `grep -c sorry` on the file: 3 hits, all the string
`sorryAx` inside docstrings; **no `sorry` tactic**.  `#print axioms` on all 40 declarations (§13.3).
Hole cones (§13.3) by the `hole-cone.lean` walker re-seeded on this file.  Import-closure presence
of the four holes by `env.find?`.

**[read]** off source, not run: that `IsDefEqU.weakN_iff` / `HasType.weak'_iff` carry `OnCtx Γ'`
on the larger context (grep + the `variable!` line); that `PropSplit.Stable`'s four fields are
unguarded (`Theory/SetModel/InterpSubst.lean`'s structure, read directly); that `Stable`'s
consumers (`SoundInduction.soundAbove`, `Cnst`, `FalseProp`, `InterpSound`) would be able to supply
`OnCtx` — that last one is **inferred** from §12.2's statement that `soundAbove` now carries
`OnCtx Γ (env₀.IsType nv)`, and was **not** re-verified at each call site this round.  Treat the
"flag day is cheap" costing in §13.0 item 3 as a costing, not a measurement.

**[not run]** by the stream, as the brief directed: the full `lake build`, guards 1–3,
`scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`, the Kernel Arena (no
implementation file touched).  `lean_local_search` and `lean_hammer_premise` were **unusable**
(`which rg` → nothing; row 131f confirmed a third time), so every search claim in this section rests
on `grep`/`sed` over source, `lean_diagnostic_messages`/`lean_goal`/`lean_hover_info`, or a Lean
`run_cmd` over the environment — never on a substring count presented as a structural fact.

**Collision check** (grep over declaration headers, labelled as such): the 46 new names do not
occur elsewhere in the tree.  The three that sit in shared namespaces — `Ctx.InstN.eq_append`,
`VExpr.bvar_inst_self`, `VExpr.bvar_zero_liftN` — were each grepped individually and are new.

### 13.7 What to pick up first

1. **Guard `PropSplit.Stable`'s four fields with `OnCtx`.**  This is now the highest-value item in
   the corner and it is *bookkeeping*, not mathematics: it turns `prop_inst_bvar` /
   `proof_inst_bvar` into the literal fields of a guarded `InstDescendUp`, and
   `isPropUpOn_liftN_up` shows the `lift` fields survive the change.  It is the same edit §12 made
   one layer up, and §12.4 measured that edit's true cost (161 argument insertions, 47 spine
   lemmas, **no new mathematics**) — expect less here, because `Stable` has four fields and far
   fewer consumers than `PropSplit` (`SoundInduction`, `Cnst`, `FalseProp`, `InterpSound`,
   `AboveAudit`, `InductOracleWitness`, `InductOracleAudit`).  **Verify the consumer count before
   starting; §13.6 flags it as read, not measured.**
2. **The remaining cases of `InstDescendUp`, in this order**: `.bvar i` with `i < k` (a smaller
   instance of the same descent — try induction on `Ctx.InstN` with the §4 core as the base case),
   then `.forallE` / `.app` / `.lam`, which still need inversion at a sort and are the only cases
   where §7.3's "injectivity" verdict survives.  `.sort`, `.const`, every closed `B`, and
   `.bvar (k+j+1)` are **done** (§9).
3. **Tell the `Theory/Typing` stream that route B now buys more than `PropSplit`.**
   `∀ n, PropTypeAgreeN env 0 n` + `∀ n, PropUniqN env 0 n` gives, `sorryAx`-free, *both*
   `Nonempty (PropSplit env 0)` (§12.7 item 1) **and** `InstDescendUp 0`'s `proof_inst` `.bvar k`
   case (`proof_inst_bvar_of_stratifiedN`).
4. **Do not fund `UnguardedStrengthen`.**  It is `weakN_iff` with its guard deleted, i.e. strictly
   harder than a 312-user hole, and item 1 removes the need for it entirely.  Likewise do not spend
   a round trying to refute `InstDescendUp` at a junk context: §13.5 item 1 shows the refutation is
   itself gated on inversion.
5. **Cheap and unclaimed**: `SetModel.propSplitUpOn` is a third `PropSplit` producer from the
   guarded inputs, and `propSplitUpOnPreludeEnv` is one at `preludeEnv` as data.  Anything that
   wanted a *lift-closed* `PropSplit` at `preludeEnv` — `PropUpFits.modelFits_of_propSplitUp_inputs`
   is the obvious customer — can now take it off the shelf, and it needs `PropUniqOnCtx` rather
   than `PropUniq`.

**Do not** re-attack: everything §10.9, §11.7 and §12.7 name, plus — new — **`CtxReplace`**
(retired), **`UnguardedStrengthen`** (item 4), and **`.bvar k` itself** (done; if you think it is
still open, read `prop_inst_bvar`'s statement and note that only the *premise* moved).

---

## 14. Session of 2026-09-02 (seventh): ruling 140 executed — **the guarded lift fields are FREE, and the flag day is REFUTED at `interp_liftN`**

One new file, `Theory/SetModel/StableGuarded.lean` (600 lines, 29 declarations, **no `sorry`**).
**No existing file was edited**, so no other stream can be broken by this round.

### 14.0 The result, plainly

Ruling 140 said: guard `PropSplit.Stable`'s four fields with `OnCtx`; "a flag day with no new
mathematics"; `isPropUpOn_liftN_up` already shows the `lift` field is free. **Both halves of that
costing are wrong, in opposite directions**, and this round measured both.

**Proved (all `sorryAx`-free, cones empty — §14.3):**

```lean
-- §1.  The pushout of two lifts carries the guard.  THIS IS NEW MATHEMATICS.
theorem Ctx.Lift'.pushOut_onCtx (henv : env.Ordered) : ∀ (l₁ l₂ : Lift) {Γ Γ₁ Γ₂},
    Ctx.Lift' l₁ Γ Γ₁ → Ctx.Lift' l₂ Γ Γ₂ → OnCtx Γ₁ (env.IsType nv) → OnCtx Γ₂ (env.IsType nv) →
    ∃ Γ₃, Ctx.Lift' (Lift.pushOutL l₁ l₂) Γ₁ Γ₃ ∧ Ctx.Lift' (Lift.pushOutR l₁ l₂) Γ₂ Γ₃ ∧
      OnCtx Γ₃ (env.IsType nv)

-- §2.  The two `lift` fields for the GUARDED lift-closed predicate, both directions, no hole.
theorem VEnv.isPropUpOn_lift'  (henv) (W : Ctx.Lift' ρ Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) :
    env.IsPropUpOn nv ls Γ' (A.lift' ρ) ↔ env.IsPropUpOn nv ls Γ A
theorem VEnv.isProofUpOn_lift' (…analogous)
theorem VEnv.isPropUpOn_liftN / isProofUpOn_liftN   -- the `Ctx.LiftN` forms
theorem VEnv.propUpOnLiftAscend_at                  -- the ascent, at a guarded target

-- §3.  The guarded structure, and the payoff.
structure PropSplit.StableOn (L : PropSplit env nv) : Prop      -- four fields, `OnCtx` on both ctxs
theorem PropSplit.Stable.stableOn : L.Stable → L.StableOn       -- so `StableOn` is the WEAKER demand
theorem propSplitUpOn_stableOn_prop_liftN  / _proof_liftN       -- discharged for `propSplitUpOn`
theorem propSplitUpOn_stableOn (…) (hpi) (hei) : (propSplitUpOn …).StableOn  -- residual VISIBLE

-- §4.  Where the guard cannot be paid — and this is a THEOREM, not a conjecture.
def  InterpLiftNObligation (env) (nv) : Prop        -- what `interp_liftN`'s binder cases would owe
theorem not_interpLiftNObligation : ¬ InterpLiftNObligation env 0
theorem not_isType_sort_param (hΓ : OnCtx Γ fun _ A => A.LevelWF 0) :
    ¬ env.IsType 0 Γ (.sort (.param 0))

-- §6.  `InstDescendUp`'s `.bvar k` case with BOTH sides guarded -- what §13.5 item 4 wrote off.
theorem VEnv.prop_inst_bvar_on (henv) (hR : env.SortRetypeOnCtx nv)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀) (h : env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUpOn nv ls Γ₁ (.bvar k)
theorem VEnv.proof_inst_bvar_on (…analogous, from `PropTypeAgreeOnCtx`)

-- §7.  The ASCENT halves of both `inst` fields, for the guarded predicate -- free.
theorem OnCtx.instN (henv : env.Ordered) : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
    env.HasType nv Γ₀ e₀ A₀ → OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv)
theorem VEnv.isPropUpOn_instN_up / isProofUpOn_instN_up
-- …so all four `StableOn` fields are closed at `B = .bvar k` for `propSplitUpOn`:
theorem VEnv.isPropUpOn_instN_bvar  (henv) (hR) (W) (hΓ₁) (h₀) :
    env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k) ↔ env.IsPropUpOn nv ls Γ₁ (.bvar k)
theorem VEnv.isProofUpOn_instN_bvar (…analogous)
```

**§6 also refutes one of §13.5's own verdicts.**  §13.5 item 4 says guarding `InstDescendUp`'s
conclusion as well as its premise "fails at the ascent `IsPropUpOn ls (A₀::Γ₀) → IsPropUpOn ls Γ₁`,
which needs `OnCtx Γ₁`", and concludes "the mixed shape … is the strongest available".  It is not:
`StableOn.prop_instN` **supplies** `OnCtx Γ₁`, and with §2's guarded `isPropUpOn_liftN` the fully
guarded case is §4's proof with one lemma swapped — nine lines, empty hole cone.  "The strongest
available" was a statement about the *lemmas then available*, written as one about the mathematics.

**Where the ruling is wrong, measured:**

| ruling 140 said | measured |
|---|---|
| "a flag day with **no new mathematics**" | **wrong.** The ascent for the *guarded* predicate needs `OnCtx` of the **pushout** of two lifts, which the tree did not have. `PropSplitUp` §1 had the syntactic pushout only. §1 is 47 lines, five cases, and the `.cons`/`.cons` case needs the pushout square to commute before the new entry can be weakened into place. §13.5 item 3 wrote this step off — correctly for *its* setting (there the ascent target `Γ₁` was unguarded), wrongly as a general verdict |
| "`isPropUpOn_liftN_up` already shows the `lift` field is free once the target is guarded" | **half right, and the missing half is the whole difficulty.** `isPropUpOn_liftN_up` proves the ascent only when the *source witness is the canonical one* (`HasType Γ A (.sort u)` directly). `Stable.prop_liftN` quantifies over an arbitrary source, whose witness lives at some `Γ''` above `Γ`. Closing that gap **is** §1 |
| "guard `Stable`'s four fields … a flag day" | **the flag day is impossible.** §4 proves the obligation `interp_liftN`/`interp_inst` would owe is **FALSE**, at every environment, at a non-degenerate lift and a guard-satisfying context. So `Stable` cannot acquire the guard while those two keep their present hypotheses |
| "expect the same shape [as §12]: 161 applications, 47 spine lemmas" | **wrong by two orders of magnitude, and in the direction nobody predicted.** The four fields have **exactly 10 applications tree-wide** (§14.2), of which **6 are the ones that cannot pay** |

### 14.1 The answer to the question that "makes this a ruling rather than a rename"

> *say plainly whether anything that consumed the unguarded field now needs the guard discharged
> somewhere it cannot be.*

**Yes, and it is refuted rather than merely unproved.** `InterpSubst.interp_liftN` and
`interp_inst` are recursions over **raw syntax**; the only hypothesis either has about the term is
`ClosedN`. At `.lam A b` and `.forallE A B` they apply the field at
`W' : Ctx.LiftN n (k+1) (A :: Γ) (A.liftN n k :: Γ')` (`InterpSubst.lean:239`, `:261`, `:419`,
`:446`), so a guarded field demands
`OnCtx (A.liftN n k :: Γ') = OnCtx Γ' ∧ env.IsType nv Γ' (A.liftN n k)`.

`not_interpLiftNObligation` refutes the second conjunct with `A := .sort (.param 0)` — a **closed**
term, so `ClosedN` cannot exclude it — at `Ctx.LiftN 1 0 [] [Prop]` with `OnCtx [Prop]` satisfied.
The refutation is `IsDefEq.levelWF` and nothing else: no inversion, no hole, no `Ordered`, no
environment hypothesis. Contrast §13.5 item 1, where the analogous negative had to be filed as a
conjecture; this one is a theorem.

`StableAudit.lean`'s note ("its consumers … recurse over raw syntax and assume only `ClosedN`")
said this in prose and called threading the guard "the actionable next step for the model side".
**That prose was right about the obstruction and wrong that it is actionable.** The two ways out,
neither costed here:

1. Give `interp_liftN`/`interp_inst` a hypothesis that **types every binder of the term** (an
   inductive `TyBinders Γ e`, hereditary under going under a binder by construction, transported
   along `liftN`/`instN` by `IsType.weakN`/`instN`), then discharge it at `InterpSound.lean`'s
   **six** call sites (`:199`, `:240`, `:348`, `:364`, `:511`, `:682`). Deriving `TyBinders` from a
   typing derivation is `HasType`-inversion at `.lam`, i.e. hole territory; deriving it *inside*
   the `sound` induction (which has the sub-derivations) is the plausible route and was **not
   attempted**.
2. Leave `Stable` unguarded and use `StableOn` only where the interpretation is not involved. That
   is what this file does, and it is why `StableOn` is a **new structure** rather than an edit to
   `Stable`.

### 14.2 The true call-site count — measured with `lean_references`, not grep

`lean_local_search` and `lean_hammer_premise` are still unusable here (`which rg` → nothing; row
131f, confirmed a fourth time). `lean_references` works, and was used for every count below.

| symbol | total refs | breakdown |
|---|---|---|
| `PropSplit.Stable` (the type) | **32** | 1 declaration, 1 mine, **30 pre-existing** across 11 files: `StableAudit` 6, `CnstRecursion` 3, `InterpSound` 8, `PropSplitUp` 3, `AboveAudit` 2, `InterpSubst` 3, `InductOracleAudit` 1, `InductOracleWitness` 1, `SoundInduction` 1, `FalseProp` 1, `Cnst` 1 |
| `Stable.prop_liftN` | 7 | 1 decl, 1 mine, 3 producer `where`-clauses, **2 applications** (`StableAudit:206`, `InterpSubst:261`) |
| `Stable.proof_liftN` | 8 | 1 decl, 1 mine, 3 producers, **3 applications** (`StableAudit:207`, `InterpSubst:224`, `:239`) |
| `Stable.prop_instN` | 7 | 1 decl, 1 mine, 3 producers, **2 applications** (`StableAudit:208`, `InterpSubst:446`) |
| `Stable.proof_instN` | 8 | 1 decl, 1 mine, 3 producers, **3 applications** (`StableAudit:209`, `InterpSubst:399`, `:419`) |

**So the four fields have 10 applications in the whole tree.** Six are inside
`interp_liftN`/`interp_inst` and **provably cannot pay** (§14.1). The other four are
`StableAudit.propDescend_of_stable`, which *can* pay trivially — its conclusion would simply become
the **guarded** `PropDescend`, which is the shape `StableAudit.sort_lift_of_strengthening` and
`proof_lift_of_strengthening` already have. The 30 `Stable`-as-hypothesis sites are untouched by a
field-guard change; only applications matter.

**Why §12's 161 does not transfer**, and this is the lesson: `PropSplit`'s two guarded fields are
*soundness* fields, applied wherever a term's propositionhood is read off a typing — hundreds of
places. `Stable`'s four are *stability* fields, applied only inside the two substitution lemmas
that consume them. **Counting a previous flag day's applications is not a prediction of the next
one's**; the fields' role, not the structure's popularity, sets the count.

### 14.3 Axioms and cones — measured

`lake build Lean4Lean.Theory.SetModel.StableGuarded`: green, **1211 jobs**, "Build completed
successfully". `lean_diagnostic_messages` / `lake env lean` on the file: **zero items** — no errors,
no warnings, no `sorry` warning. `grep -n sorry` on the file: **0 hits**.

`#print axioms` on all 29 census entries: `[propext]`, `[propext, Quot.sound]`,
`[propext, Classical.choice, Quot.sound]` — **except one**, `liftN_field_discriminates`, which is
`[propext, sorryAx, Classical.choice, Quot.sound]`. **No frozen axiom anywhere. No new `sorry`,
none traded.**

Forward hole-cone over type **and** value with `allowOpaque := true`, seeded on all 26 theorem/def
declarations (`/tmp/hc-stableguarded.lean`, the `scripts/hole-cone.lean` walker re-seeded), each
cone's *complete* `sorryAx` membership reported:

| seed | cone | holes |
|---|---|---|
| `pushOut_onCtx`, `isPropUpOn_lift'`, `isProofUpOn_lift'`, `isPropUpOn_liftN`, `isProofUpOn_liftN`, `propUpOnLiftAscend_at` | 2144–2151 | **none** |
| `Stable.stableOn` | 195 | **none** |
| `propSplitUpOn_stableOn_prop_liftN` / `_proof_liftN` / `propSplitUpOn_stableOn` | 2166–2176 | **none** |
| `not_isType_sort_param`, `not_interpLiftNObligation`, `interpLiftNObligation_iff_binder_isType` | 165–920 | **none** |
| `onCtx_bvar_prop`, `notOnCtx_lift_target`, `notOnCtx_inst_target` | 604–1224 | **none** |
| `liftN_field_positive`, `preludeEnv_stableOn_liftN` | 3776–3778 | **none** |
| `prop_inst_bvar_on`, `proof_inst_bvar_on` | 2171, 2480 | **none** |
| `OnCtx.instN`, `isPropUpOn_instN_up`, `isProofUpOn_instN_up` | 1124–1902 | **none** |
| `isPropUpOn_instN_bvar`, `isProofUpOn_instN_bvar` | 2252, 2527 | **none** |
| **`liftN_field_discriminates`** | 4031 | **exactly `[forallE_inv_stratified]`** |

The one hole enters through `InstDescendBvar.not_isPropUpOn_sort` → `preludeEnv_propUniqOnCtx` →
`preludeEnv_WF`, i.e. route A, and it is in the *anti-vacuity discriminating check* only — no
result depends on it. `IsDefEqU.weakN_iff` and `WF.rigidShapeUniqNS` are in the import closure
(`env.find?`) and appear in **no** cone — available and unused. `NormalEq.descend` is **not** in the
closure (`env.find?` returns `none`).

**Hole-free is not discharged, reported separately as instructed:**

| result | holes | open hypotheses |
|---|---|---|
| `pushOut_onCtx`, `isPropUpOn_lift'` + 3 siblings, `propUpOnLiftAscend_at` | none | none beyond `env.Ordered` and the field's own guard |
| `propSplitUpOn_stableOn_prop_liftN` / `_proof_liftN` | none | `PropUniqOnCtx` + `PropTypeAgreeOnCtx` (theorems at `preludeEnv`, via route A with `forallE_inv_stratified`, or route B `sorryAx`-free from the `∀ n` statements) |
| `propSplitUpOn_stableOn` | none | the above **plus the two `inst` fields** (`hpi`, `hei`) — i.e. `InstDescendUp` at the guarded predicate, of which only `.bvar k` is closed. **This is an open residual carried as a hypothesis, and it is labelled as one** |
| `not_interpLiftNObligation`, `not_isType_sort_param` | none | none |

### 14.4 Anti-vacuity — and a **correction to §13.4 item 4 / ledger rows 139d, 140d**

**The correction first, because it retracts a check this corner reported as passed.** §13.4 item 4
and rows 139d/140d claim `bvar_one_instance` runs "with `Γ₁ = [.bvar 0, Prop]`, a context that is
**not** `OnCtx` (`PropAgreeWall.not_isType_bvar`)", and conclude from that witness that the guard
sits on the premise only. **That context *is* `OnCtx`.** `StableGuarded.onCtx_bvar_prop` proves
`OnCtx [(.bvar 0), Prop] (env.IsType 0)` at **every** environment with **no hypotheses**:

```lean
theorem onCtx_bvar_prop : OnCtx [(VExpr.bvar 0 : VExpr), (VExpr.sort .zero : VExpr)] (env.IsType 0)
```

`not_isType_bvar` is about `¬ env.IsType 0 [] (.bvar 0)` — the variable over the **empty** context.
In `[.bvar 0, Prop]` the variable is looked up in `[Prop]` and its type is `Prop.lift = Prop`,
which is a sort, so `IsType` holds. This is ledger blindness 2 in the shape it warns about: a
citation that names a real theorem about a *different* configuration. **`bvar_one_instance` is
still true and still worth having — it shows the theorem works at `k = 1` — but it does not
establish that the guard sits on the premise only, and rows 139d/140d should be amended.**

The four checks for *this* round, all machine-checked:

1. **The narrowing is real, with witnesses the guard genuinely excludes.**
   `notOnCtx_lift_target` : `Ctx.LiftN 1 0 [] [.sort (.param 0)] ∧ ¬ OnCtx [.sort (.param 0)]` —
   so `Stable.prop_liftN` speaks at that lift and `StableOn.prop_liftN` says nothing.
   `notOnCtx_inst_target` does the same for the two `inst` fields **with the field's typing premise
   satisfied**: `Ctx.InstN [] (∀p:Prop,p) Prop 1 [.sort (.param 0), Prop] [.sort (.param 0)]`
   together with `preludeEnv.HasType 0 [] (∀p:Prop,p) Prop` and
   `¬ OnCtx [.sort (.param 0), Prop] (preludeEnv.IsType 0)`. Both use an out-of-range universe
   *parameter*, not a variable — which is what makes them work where §13.4's witness did not.
2. **The narrowed fields still have content, at `preludeEnv`.** `liftN_field_positive` exhibits the
   guarded `prop_liftN` instance at `Ctx.LiftN 1 0 [] [Prop]` (guard satisfied, `onCtx_prop`)
   relating two statements that are **both true** — `∀ p : Prop, p` is a proposition at `[]` and its
   lift is one at `[Prop]`. `preludeEnv_stableOn_liftN` gives **both** guarded `lift` fields at
   `preludeEnv` at every guarded lift, with no hypotheses.
3. **The fields are not constant-true.** `liftN_field_discriminates`: at the same guarded lift with
   `A := Prop`, both sides are **false**. (This is the one declaration carrying `sorryAx`, via
   `not_isPropUpOn_sort`; the positive check in item 2 is `sorryAx`-free, so the non-degeneracy does
   not rest on the hole.)
4. **Nothing was smuggled in as a satisfiable-looking hypothesis.** The obvious way to "discharge"
   `VEnv.PropUpOnLiftAscend` — which is stated *without* a guard — is to assume "every lift target
   is `OnCtx`". I wrote that lemma, then **deleted it**: `notOnCtx_lift_target` refutes the
   hypothesis, so the lemma would have been vacuous, and shipping it would have been ledger
   blindness 4 in a new costume. **`PropUpOnLiftAscend` as `InstDescendBvar` §7 states it is NOT
   discharged by this round**; what is discharged is `propUpOnLiftAscend_at`, its guarded form.

**`Above`**: zero occurrences in the new file outside the §5 note that says so; no chosen `κ`, no
`VDecl.unsafeDef` in any witness chain. So no result here is free at a false
`IsInaccessibleChain` antecedent.

### 14.5 What I tried that failed, and the step it failed at

1. **`propUpOnLiftAscend_of_onCtx`**, discharging the *unguarded* `PropUpOnLiftAscend` from
   `∀ {n k Γ Γ'}, Ctx.LiftN n k Γ Γ' → OnCtx Γ'`. **It compiled**, which is the danger: the
   hypothesis is refuted by `notOnCtx_lift_target`, so the lemma is vacuous. Deleted before
   landing, and recorded here because a green `#print axioms` would not have caught it.
2. **A counterexample to the `interp_liftN` obligation using a variable.** Tried `Γ = [Prop]`,
   `A = .bvar 0` (`ClosedN 1` ✓): failed because `IsType [Prop] (.bvar 0)` is **true** — the same
   miscalculation §13.4 made. Tried `Γ = [∀p:Prop,p]`, `A = .bvar 0`: refuting `IsType` there needs
   `Prop ≢ Π`, i.e. `sort_forallE_inv`, a hole. Recovered by moving from variables to **levels**:
   `A = .sort (.param 0)` is closed, and `IsDefEq.levelWF` refutes its typing with no hole at all.
   *That is why §4 is nine lines.*
3. **Deriving `OnCtx Γ` from `IsPropUpOn nv ls Γ A`** (which would have made the guard free on the
   premise side). Fails at `Ctx.Lift'.cons`: `OnCtx Γ'` gives `IsType Γ'' (X.lift' l)` and one needs
   `IsType Γ_ X`, which is strengthening. Abandoned at that case, not attempted in Lean.
4. **Guarding only the *inserted* entries of a lift** instead of the whole target, hoping for a
   hereditary guard that `interp_liftN`'s recursion could maintain. Abandoned on paper: the
   insertion set is hereditary under `.succ`, but `isPropUpOn_liftN`'s ascent needs `OnCtx` of the
   **whole** target, and recovering that from `OnCtx Γ` + typed insertions needs `OnCtx Γ`, which
   `interp_liftN` also lacks. So the hereditary reformulation moves the problem, it does not solve
   it.
6. **The ascent half of the `inst` fields, first attempt.** Wrote `prop_inst_bvar_on_rev` by hand
   at `B = .bvar k`, trying to build it out of lift identities the way §6's descent is built.
   **Failed and was withdrawn**: at `.bvar k` the ascent asks "the variable of type `A₀` is a
   proposition at `Γ₁`, therefore `e₀` is one at `Γ`", and the lift-out-of-`Γ₀` route that makes
   the *descent* free runs the wrong way. **The mistake was mine, not `PropSplitUp`'s**: §4 of that
   file proves the ascent for *general* `B` (`isPropUp_instN_up`) through the syntactic square
   `Ctx.InstN.pushLift'`, which I had not read before attempting the special case. §7 is that
   proof ported to the guarded predicate, and the only new ingredient is `OnCtx.instN` — eight
   lines, two cases, `IsType.instN` in the `.succ` one. **Lesson, and it is row 129c's again:
   I doubted a claim in the source before checking whether the source had the lemma.**
5. **The in-place flag day, as a measurement.** *Not run.* I had planned §12.4's sharpest
   measurement — edit `Stable`, count errors per file, revert — and dropped it once §4 proved the
   edit cannot be completed: the error count would have measured a repair that does not exist,
   while leaving the tree red for two concurrent streams. `lean_references` gave the count instead
   (§14.2), and it is exact rather than an upper bound.

### 14.6 Measured / read / not run

**[measured]** `lake build Lean4Lean.Theory.SetModel.StableGuarded`: **1211 jobs**, green, zero
diagnostics. `#print axioms` on all 29 census entries (§14.3). Hole cones on all 26 theorem/def
declarations plus import-closure presence of the four big holes (§14.3), by the re-seeded
`hole-cone.lean` walker. All call-site counts by `lean_references` (§14.2). `onCtx_bvar_prop`, and
therefore the §13.4 correction, is a **compiled Lean theorem**, not a reading.

**[read]** off source, not run: that `InterpSound.lean`'s six `interp_liftN`/`interp_inst` call
sites are at `:199`, `:240`, `:348`, `:364`, `:511`, `:682` (grep); that repair route 1 of §14.1
would need `HasType` inversion at `.lam` — that is an argument about what a proof would need, and
is a **costing, not a measurement**. The line numbers `InterpSubst.lean:224/239/261/399/419/446`
for the six unpayable applications are from `lean_references`, hence measured.

**[not run]** by the stream, as the brief directed: the full `lake build`, guards 1–3,
`scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`, the Kernel Arena (no
implementation file touched). **Also not done, for want of budget**: the `PropAgreeWall.lean`
route-B weakening to `PropTypeAgreeNOn`/`PropUniqNOn` via
`Theory/Typing/PropAgreeGuarded.propAgreeOn_of_stratifiedNOn` (verified present:
`PropAgreeGuarded.lean:193`), and `InductOracleOK` at `iffIndDecl` (verified present:
`Theory/Consistency.lean:96`, five binders, no index; `UnitOracleLarge.recFnL` at `:434` is the
template). Both are untouched and both remain cheap.

**Collision check** (grep over declaration headers, labelled as such): the 23 new names do not
occur elsewhere in the tree. The two in shared namespaces — `Ctx.Lift'.pushOut_onCtx` and
`PropSplit.StableOn` / `PropSplit.Stable.stableOn` — were grepped individually and are new.

### 14.7 What to pick up first

1. **Do NOT re-attempt guarding `Stable` in place.** `not_interpLiftNObligation` is a theorem: the
   obligation is false. Anyone who wants the guard on `Stable` must first give
   `interp_liftN`/`interp_inst` a binder-typing hypothesis (§14.1 route 1) — a substantial,
   independently statable piece of work whose hard step is getting `TyBinders` out of the `sound`
   induction, **not** the threading.
2. **`propSplitUpOn_stableOn`'s two remaining inputs are the `inst` fields' DESCENT halves at
   general `B`, and nothing else.** State of those two fields for `propSplitUpOn` after this round:
   **ascent halves — done at every `B`** (§7, `isPropUpOn_instN_up` / `isProofUpOn_instN_up`, empty
   cones); **descent halves — done at `B = .bvar k`** (§6), and `InstDescendBvar` §9's free classes
   (every closed `B`, hence `.sort`/`.const`; `.bvar (k+j+1)`) **should port by swapping
   `isPropUp_liftN` for §2's `isPropUpOn_liftN`** — that swap is nine lines and **was not done this
   round**. It is the cheapest unclaimed item in this corner. Then `.bvar i` with `i < k` (a smaller
   instance of the same descent), then `.forallE`/`.app`/`.lam`, which are the only cases where
   §7.3's "injectivity" verdict survives.
3. **Amend ledger rows 139d and 140d** for §14.4's correction, and §13.4 item 4 with it. The claim
   retracted is narrow (one witness does not show what it was said to show) but it is in the
   ledger's own anti-vacuity column, which is the one place a wrong entry is most expensive.
4. **`iffIndDecl` before `eqIndDecl`** — unchanged from §10.9/§11.7/§12.7/§13.7, untouched again;
   this is now the **seventh** consecutive section to name it. Per row 140b's lesson, someone should
   unfold it before copying the description forward an eighth time.
5. **`PropAgreeWall.lean`'s route-B weakening** (§14.6): `propAgreeOn_of_stratifiedNOn` exists and
   is a genuine weakening of what route B needs. Ten lines, no new mathematics — and this time that
   phrase has been checked against the source rather than inherited.

6. **One line for the orchestrator, because I may not write it.** Neither
   `Theory/SetModel/InstDescendBvar.lean` (§13's file) nor `Theory/SetModel/StableGuarded.lean`
   (this one) is imported by anything, so **the tree-wide build and `dup-names` do not see either**;
   only a direct `lake build` of the module does. The exact edit, in
   `Lean4Lean/Experimental/ConeJoin.lean` (a FROZEN-adjacent file I am forbidden to touch), is one
   added line:

   ```lean
   import Lean4Lean.Theory.SetModel.StableGuarded  -- 2026-09-02: guarded lift fields free; the Stable flag day refuted
   ```

   which transitively pulls `InstDescendBvar` as well. Until then, "no `sorry`, no frozen axiom" for
   these two files rests on the per-module builds and cones reported here, not on guard 1.

**Do not** re-attack: everything §10.9, §11.7, §12.7 and §13.7 name, plus — new — **guarding
`Stable` in place** (refuted, 14.1), **the unguarded `PropUpOnLiftAscend`** (its natural discharge
is vacuous, 14.4 item 4), and **`[.bvar 0, Prop]` as a junk context** (it is not one, 14.4).

---

## 15. Session of 2026-09-02 (eighth): Task 2 was **already in HEAD** — what was owed was the grading, and the grading is worse than the re-pricing looks

*Written incrementally, in the order the work happened.*

### 15.0 The `#print axioms`-first check, run before proving anything, as instructed

Four things the brief asserts; all four **verified present and as described**, so this brief is
not a third instance of row 144d.

| asserted | verified |
|---|---|
| `inductOracleOK_NE` | `Lean4Lean.SetModel.NEAudit.inductOracleOK_NE`, `[propext, Classical.choice, Quot.sound]` |
| `UnitOracleLarge.recFnL` | `Lean4Lean.SetModel.UnitAudit.recFnL` (`UnitOracleLarge.lean:434`), same axioms |
| `propAgreeOn_of_stratifiedNOn` | `Theory/Typing/PropAgreeGuarded.lean:193`, present |
| `regPi_false` | `Lean4Lean.VEnv.regPi_false : ¬ env.RegPi U n`, **every** `env`/`U`/`n`, `[propext]` |

Note the namespaces: the brief's `UnitOracleLarge.recFnL` and `SetModel.inductOracleOK_NE`
are **file** names, not Lean names — the declarations live in `SetModel.UnitAudit` and
`SetModel.NEAudit`. `#print axioms` on the brief's spelling fails with
*unknown constant*, which cost two minutes and is worth writing down.

### 15.1 **Task 2's named target is already a theorem in HEAD.** Third occurrence of row 144d

The brief says "`RegPiSat.lean` **reportedly** already holds the repair (`RegPiOn`/`Regular`),
and the named re-pricing target is `propTypeAgree_appCase_on_of`". It does not merely hold the
repair; **it holds the re-priced consumer, its induction, and the whole assembly**, all
sorry-free, all in HEAD:

```lean
-- Theory/Typing/RegPiSat.lean §4, ALREADY THERE
theorem propTypeAgree_appCase_on_of (dinv : env.SortInvN U (k+1)) (hreg : env.RegPiOn U (k+1))
    (hinst : env.InstLvl U (k+1)) (huniq : env.PropUniqN U (k+1)) (pci : env.PropConvInv U (k+1)) :
    PropTypeAgreeN.AppCaseOn env U (k+1)                     -- [propext, Classical.choice, Quot.sound]
theorem propTypeAgree_on_of  … : env.PropTypeAgreeOnN U n
theorem propTypeAgreeOn_of_residuals … : env.PropTypeAgreeOnN U (k+1)
```

So **nothing was owed on the re-pricing**. What was never done — and is the actual content of
the brief's question ("what the guarded form actually buys, and whether the assembly becomes
non-vacuous or merely differently conditional") — is the **grading**. That is §15.2.

### 15.2 The grading: **merely differently conditional**, and the positive control is degenerate

New file `Lean4Lean/Theory/SetModel/RegPiRepriced.lean` (14 declarations, **0 `sorry`**),
**imported by `Theory/Equiconsistency.lean`** so it is connected on landing rather than
orphaned (rows 128b / 133c / 142e — this is the fourth round in a row that lesson has come up,
and the fix costs one line in a file this stream owns).

```lean
def RepricedInput (env) (U k) : Prop :=          -- the five hypotheses, bundled
  env.SortInvN U (k+1) ∧ env.Regular U (k+1) ∧ env.InstLvl U (k+1) ∧
    env.PropUniqN U (k+1) ∧ env.PropConvInv U (k+1)
theorem propTypeAgreeOnN_of_repricedInput : RepricedInput env U k → env.PropTypeAgreeOnN U (k+1)

theorem regPi_false_at_preludeEnv : ¬ preludeEnv.RegPi U n         -- what the repair removes
theorem not_repricedInput_piLvlEnv : ¬ RepricedInput piLvlEnv 0 0  -- what it does NOT remove
theorem ordered_not_enough_for_repricedInput :
    ¬ ∀ env, Ordered env → ∀ k, RepricedInput env 0 k
theorem propTypeAgreeOnN_zero_free (env) (U) : env.PropTypeAgreeOnN U 0   -- the finding
theorem zero_replay_is_free :
    (∀ U, propLoopEnv.PropTypeAgreeOnN U 0) ∧ (∀ env U, env.PropTypeAgreeOnN U 0)
theorem regConvE_zero_is_syntactic : env.IsDefEqN U 0 Γ A A' ↔ A = A'
def RegularAtSucc : Prop := ∃ env U k, env.Regular U (k+1)          -- nothing inhabits this
```

| | before the repair | after |
|---|---|---|
| a hypothesis false at **every** environment | `RegPi` (`regPi_false`) | **none** |
| the bundle refuted at some `Ordered` env, at the least *stated* index | yes a fortiori | **yes**, `not_repricedInput_piLvlEnv` |
| the bundle refuted at some `VEnv.WF` env | yes a fortiori | **not known** |
| a **non-degenerate** positive instance | none | **none** |

Three things this settles, each machine-checked and none of them read off a docstring:

1. **What the repair buys is real but narrow.** `regPi_false` is at *every* environment, so it
   was false at `preludeEnv` — the `VEnv.WF` environment `PreludeWitness.lean` actually builds,
   no `VDecl.unsafeDef` anywhere. `regPi_false_at_preludeEnv` names it, because "false at every
   environment" only bites once one of them is exhibited as reachable. After the repair, **no
   hypothesis of `propTypeAgreeOn_of_residuals` is refuted at every environment.** That is the
   whole of the gain and it is worth having.
2. **The bundle is still refuted at `Ordered`, at the smallest index the consumer is stated at.**
   The offending member is `PropUniqN`, by row 144's `piLvlEnv_propUniqN_false` at `n = 1`;
   `propTypeAgreeOn_of_residuals` is stated only at `k+1`, so `k = 0` is the least instance and
   it is empty. `piLvlEnv` is provably **not** `VEnv.WF` (`piLvlEnv_not_wf`), so this does not
   touch the real target — the vacuity **changed shape** (from "internal to one hypothesis, at
   every environment" to "at an exhibited non-`WF` environment") rather than disappearing.
3. **The one positive control in the tree is degenerate, and this is the finding.**
   `RegPiSat.lean` §4 offers `propTypeAgreeOn_zero_from_residuals : propLoopEnv.PropTypeAgreeOnN U 0`
   as the replay showing the repaired chain fires. **Its conclusion is free**:
   `PropTypeAgreeOnN.zero` proves it at *every* environment with no hypotheses (via
   `HasTypeN.uniq_zero`), and the `RegConvE` input is free at index `0` only because
   `IsDefEqN U 0` **is** syntactic equality (`regConvE_zero_is_syntactic`). So the replay
   demonstrates satisfiability at the one index where the conclusion needs nothing, which is no
   evidence at all about the indices where the theorem is stated. `zero_replay_is_free` puts
   both halves in one statement so the collapse cannot be read past.

   `RegPiSat.lean` is scrupulous about the *negative* side of this ("the three that cannot be
   fired at index `0`", blocked at `SortInvN env U 1`). What it does not say is that the
   positive control it does offer proves nothing — and that is the half a reader carries away
   as reassurance. **This is ledger blindness 7 with the sign flipped**: not "green because the
   hypotheses are unsatisfiable at the degenerate instance" but "green because the *conclusion*
   is free at the degenerate instance".

**And one residual the re-pricing newly created, which nobody has graded.** `Regular` rests on
`RegConvE` (`regular_of`), and `RegConvE` has an instance at index `0` and **nowhere else** —
`RegConvE.zero`'s entire proof is a rewrite along `IsDefEqN.zero_iff`. `EnvReg` is free at every
index for a `ConstPropType` environment, and `InstLvl` at `k+1` is the tree's usual residual, so
`RegConvE env U (k+1)` is the *new* member of the bundle and it is completely untested:
`RegularAtSucc` (`∃ env U k, env.Regular U (k+1)`) is **inhabited by nothing in the tree**.
`regularAtSucc_of` states what would suffice. Not attempted: proving `RegConvE propLoopEnv U (k+1)`
directly is "conversion preserves being a type, at the index", i.e. the same induction
`regular_of'` is, so it is circular as stated — recorded as reasoning, **not** as a refutation.

**Measured**: `lake build Lean4Lean.Theory.SetModel.RegPiRepriced` green, **1232 jobs**,
`lake env lean` on the file: **zero diagnostics**. `lake build Lean4Lean.Theory.Equiconsistency`
green after wiring the import, **1239 jobs**. `#print axioms` on all 14 declarations:
`[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` — **no
`sorryAx`, no frozen axiom, nothing new on the frozen cone**. `grep -c "sorry"` on the file: 0.

### 15.3 Task 1: the level branch at `iffIndDecl` is **measured and confirmed** — and §10.9's other prediction is **refuted**

New file `Lean4Lean/Theory/SetModel/IffOracle.lean` (516 lines, **84 declarations**, **0
`sorry`**), also imported by `Theory/Equiconsistency.lean`.  `InductOracleOK` at `iffIndDecl` is
**not** closed; what is closed is the part §10.9 asked to be *verified rather than assumed*, plus
the piece of infrastructure the next stream would otherwise build first.

```lean
-- §3.  The datum `VInductDecl'.recType_isType` withholds: it returns `IsType`, i.e. the sort
--      existentially, and the level branch is a statement about WHICH sort.
theorem hasType_iffRecType (hu : u.WF nv) (Γ) :
    iffEnv.HasType nv Γ ((iffIndDecl.recType 0).instL [u]) (.sort (iffRecSort u))
-- §4.  Four `imax`es, each `0` exactly when its codomain is.
theorem iffRecSort_eval_eq_zero_iff : (iffRecSort u).eval ls = 0 ↔ u.eval ls = 0
-- §5.  Five `VDecl.WF.le` steps, so nothing below is at an unreachable environment.
theorem iffEnv_le_preludeEnv : iffEnv ≤ preludeEnv
-- §6.  The model consequence, and the headline.
theorem isProp_iffRecType_iff : L.IsProp M Γ ((iffIndDecl.recType 0).instL [u]) ↔ u.eval M.ls = 0
theorem pt_not_mem_interp_iffRecType_of_ne (hn : u.eval M.ls ≠ 0) :
    (pt : V) ∉ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅
theorem eq_pt_of_mem_interp_iffRecType_of_zero (h0 : u.eval M.ls = 0) :
    v ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ → v = pt
theorem level_branch_forced (hu₀ hu₁) (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0)
    (hv₀ : v ∈ ⟦recType.instL [u₀]⟧) : v ∉ ⟦recType.instL [u₁]⟧
```

**The prediction is confirmed, and it is now a theorem rather than a reading.**  §7.4's "the
level branch is FORCED" reappears at `iffIndDecl` exactly as §10.9 said it would, at a block
with **two parameters and two constructor fields** rather than none of either.  Both slices are
non-empty (`exists_eq_zero_level`, `exists_ne_zero_level`), so `level_branch_forced` is not a
vacuous implication.

**Two things came out better than predicted, and one worse.**

*Better, 1 — the `≠ 0` exclusion needs no hypothesis here.*
`UnitOracleLarge.pt_not_mem_interpL_recType_of_ne` carries `hg : g ∈ ⟦motTyU u⟧` — an inhabitant
of the motive space — because at `unitDeclLE` the outermost binder *is* the motive and a junk `κ`
can make `U κ n` empty.  At `iffIndDecl` the outermost binder is a **parameter over `Prop`**, and
`∅ ∈ U κ 0` at every `κ` (`U_zero`, `mem_UProp_iff`), so
`pt_not_mem_interp_iffRecType_of_ne` is unconditional.  **The parameter makes this obligation
cheaper, not dearer** — which is the opposite of how §10.4 priced the block ("`Iff` wants five
layers", i.e. read as strictly harder throughout).

*Better, 2 — the level computation is `imax`'s doing, not `Prop`'s.*  Two of the five binders
have a `Prop` domain and a possibly-non-`Prop` codomain, so their sorts are `imax 1 X`; the
telescope stays propositional at `u.eval ls = 0` only because `imax _ 0 = 0`.  Had the parameters
been `Type`-valued the branch would be identical (`imax 2 0 = 0`).  So the mechanism is not
"`Prop` parameters collapse" and a stream that transports this to `eqIndDecl` — whose first
parameter is `.sort (.param 1)`, a **Type** — should expect the same shape.  That is a
prediction, labelled as one.

*Worse — **§10.9's "the `= 0` slice should be free by §10.1's argument" is FALSE at this
block.***  It is free at `nonemptyIndDecl` because the recursor type's *truth* in the model
follows from the minor premise's own value.  Here the proposition to be verified at `= 0` is

> for all `p q ∈ U κ 0`, every motive `f`, every minor premise and every `h ∈ ⟦Iff p q⟧`,
> `• ∈ f ‘ h`

and closing it needs **`iffFn`'s faithfulness in both directions** — the easy half is
`PreludeSpec.iffFn_value` (`⟦Iff p q⟧ = if p = q then {•} else ∅`), and the other half is
"`⟦p → q⟧` and `⟦q → p⟧` both nonempty implies `p = q`", i.e. the model-side shadow of `propext`
(`PreludeSpec.propext_of_mem_UProp` is the tool).  **So `iffIndDecl` is the first block in this
corner where the *constructor's* content is needed to close the *recursor's* obligation**, and
the `= 0` slice is not free.  This is recorded in the file's §7 as OPEN, not as done.

What is left at the block, from the file's own §7 table: `• ∈ ⟦Iff.rec's type⟧` at `= 0` (above);
`Iff ↦ iffFn ∈ ⟦Prop → Prop → Prop⟧`; `Iff.intro ↦ •` (its type **is** a proposition — measured:
`imax _ (imax _ (imax 0 (imax 0 0))) = 0`, so this one really is the small-eliminator argument);
the `≠ 0` slice's five-layer `mkLam` value, two of whose layers are over `U κ 0`; and the single
ι-rule (`iffIndDecl.iotaRules.length = 1`, `#reduce`d).

### 15.4 What I tried that failed, and the step it failed at

1. **`VInductDecl'.recType_isType` as the typing input.**  It is a theorem
   (`Theory/Inductive/Lemmas.lean:1623`) and it gives `env.IsType D.recUvars [] (D.recType j)` —
   the sort **under an `∃`**.  `isProp_iff` needs the sort *named*, because the level branch is a
   statement about its evaluation.  So the existential is unusable and §3's derivation had to be
   written by hand.  This is worth knowing before someone else reaches for it at `eqIndDecl`.
2. **`Lookup.zero'` / `Lookup.succ'`.**  `Theory/Typing/Meta.lean` is **not** in
   `PreludeOracle`'s import closure, so those two do not resolve; the raw constructors
   (`.bvar .zero`, `.bvar (.succ (.succ .zero))`) do, and the lift computations unify.
3. **`.appDF` against an expected `.sort u`.**  `appDF`'s conclusion is `B.inst a`, and
   `?B.inst a =?= .sort u` is not solvable, so `hasType_minBodyI` and `hasType_resI` both failed
   with a metavariable in the function's type.  **Fix**: state the motive variable's type
   explicitly first (`hasType_mot_ctxQ`, `hasType_mot_ctxH`) so `B` is pinned.  This is the same
   class of failure as §12.5 items 1–2 and §13.5 item 6, in a fourth costume.
4. **`hasType_motTyI hu (ictxA Γ)`.**  `ictxB` already prepends **two** entries, so passing
   `ictxA Γ` produced a three-`Prop` context.  Caught by the type mismatch; worth a line because
   the abbrev names are the same shape as `UnitOracleLarge`'s and there the offset is one.
5. **`.imax`'s `WF` for `sortN`.**  `⟨trivial, …⟩` does not close `(minSortI u).WF nv`: the
   nesting is `⟨⟨⟨_,_⟩, ⟨_,_⟩, hu⟩, _⟩`, i.e. `mpSortI`'s own `WF` twice plus `u`'s.  Trivial to
   fix, easy to mis-nest.
6. **Reaching for `interp_forallE_type` at the top binder without staging the body.**  It reads
   `¬ L.IsProp M (A :: Γ) B`, i.e. the *body's* propositionhood one binder in — so the four
   intermediate bodies (`recBH`, `recBN`, `recBM`, `recBB`) and their four sorts had to be named
   and typed separately.  That is why §3 has nine lemmas rather than one.
7. **Attempting the `= 0` slice.**  Stopped at the step above: the proposition's *truth* needs
   `iffFn`'s hard direction.  Not attempted in Lean past writing the goal down; recorded as a
   costing, not as a refutation of anything.

### 15.5 Measured / read / not run

**[measured]**
* `lake build Lean4Lean.Theory.SetModel.RegPiRepriced`: green, **1232 jobs**.
* `lake build Lean4Lean.Theory.SetModel.IffOracle`: green, **1204 jobs**.
* `lake build Lean4Lean.Theory.Equiconsistency` (after wiring both imports): green, **1240 jobs**
  (1239 with `RegPiRepriced` alone).
* `lake env lean` on both new files: **zero diagnostics** — no errors, no warnings, no `sorry`
  warning.  `grep -c sorry`: `IffOracle` **0**, `RegPiRepriced` **1** and that one is the word
  "sorry-free" inside a docstring.
* **`#print axioms` on all 98 declarations** (84 in `IffOracle`, 14 in `RegPiRepriced`): each is
  `[]`, `[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`.
  **No `sorryAx` anywhere.  No frozen axiom.  No new `sorry`, none traded.**
* **Hole cones**, forward over type **and** value with `allowOpaque := true`, the
  `scripts/hole-cone.lean` walker re-seeded on **all 98** declarations out of `/tmp`, reporting
  each cone's *complete* `sorryAx` membership as well as the four named holes:
  **`seeds walked: 98; seeds with any hole: 0`.**  Not one cone contains a `sorryAx`-carrying
  member, so a fortiori none contains `forallE_inv_stratified`, `weakN_iff`,
  `rigidShapeUniqNS` or `descend`.  Import-closure presence by `env.find?`:
  `forallE_inv_stratified`, `weakN_iff`, `rigidShapeUniqNS` **are** in the closure and in **no**
  cone (available and unused); `NormalEq.descend` is **not** in the closure.
* Block shape facts by `#reduce`: `iffIndDecl.allConsts.map Prod.fst = [Iff, Iff.intro, Iff.rec]`,
  `iffIndDecl.iotaRules.length = 1`.  `iffEnv`'s three constant lookups are `rfl`.
* Collision check: both files declare into **fresh namespaces**
  (`Lean4Lean.SetModel.IffAudit`, `Lean4Lean.SetModel.RegPiAudit`) — `grep` over the tree finds
  no other occurrence of either, so no name in either file can collide.

**Hole-free is not discharged, reported separately as instructed:**

| result | holes | open hypotheses |
|---|---|---|
| `hasType_iffRecType`, the nine §3 typing lemmas, `iffRecSort_eval_eq_zero_iff` | none | `u.WF nv` only |
| `isProp_iffRecType_iff`, `isProp_recBB_iff` | none | `iffEnv ≤ envF` (a theorem at `preludeEnv`), `OnCtx Γ`, and **a `PropSplit envF nv`** — inhabited at `preludeEnv` as data (`propSplitPreludeEnv`, route A with `forallE_inv_stratified`; or route B `sorryAx`-free) |
| `pt_not_mem_interp_iffRecType_of_ne` | none | the same, and nothing else — in particular **no** motive-space inhabitant and **no** parameter-space inhabitant (this row is correct as written; see §16.3's three-point scale) |
| ~~`level_branch_forced`~~ | none | **CORRECTED 2026-09-02 (§17.1, ledger row 149b/151b).** This row originally read "the same, and nothing else" and was **wrong**: `level_branch_forced` also carries `hv₀ : v ∈ ⟦(iffIndDecl.recType 0).instL [u₀]⟧`, a *member* hypothesis, which the row omitted. By `IffAudit.exists_mem_interp_iffRecType_zero_iff` (landed §17.1) `hv₀` is satisfiable **iff** `pt ∈ ⟦recType[u₀]⟧`, i.e. iff the `= 0` slice holds — and that slice is **OPEN** at `iffIndDecl` (row 146b), so the hypothesis is unmeasured, not discharged. Quote `IffAudit.no_level_uniform_value` (a negation, no member hypothesis) when an unconditional form is wanted. The "both slices non-empty" control cited in this section is about the two **level** slices and never bore on `hv₀`. |
| `iffEnv_le_preludeEnv` | none | none |
| `not_repricedInput_piLvlEnv`, `zero_replay_is_free`, `propTypeAgreeOnN_zero_free` | none | none |
| `propTypeAgreeOnN_of_repricedInput` | none | the five-member bundle, **which is refuted at `piLvlEnv`** — this is the one place in this round where a hypothesis is not merely open |

**Anti-vacuity.**  `Above` occurs **nowhere** in either new file (grep: zero occurrences); no `κ`
is chosen anywhere in `IffOracle` — every statement is at an arbitrary `κ : ℕ → V` — so nothing
here is free at a false `IsInaccessibleChain` antecedent.  Both witness environments are
exhibited and graded: `preludeEnv` is `VEnv.WF` (`preludeEnv_WF`), built by
`preludeEnv_history` with **no `VDecl.unsafeDef`**, and `iffEnv ≤ preludeEnv` is proved; `piLvlEnv`
is `Ordered` and **provably not `WF`**, and §15.2 says so in the row that uses it.  The `= 0` /
`≠ 0` split is a real split (`exists_eq_zero_level`, `exists_ne_zero_level`), so
`level_branch_forced` is not satisfied by an empty slice.

**[read]** off source, not run: that `Theory/Inductive/Lemmas.lean:1623` is `recType_isType`'s
declaration and that it returns `IsType` (read, then confirmed by `#check` — so the *shape* claim
is measured and only the line number is grep); that `PreludeSpec.propext_of_mem_UProp` is the
tool for the `= 0` slice's hard half (read, **not** attempted).  §15.3's prediction that
`eqIndDecl`'s branch has the same shape because `imax 2 0 = 0` is **reasoning, not a
measurement**.

**[not run]** as the brief directed: the full `lake build`, guards 1–3,
`scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`, the Kernel Arena (no
implementation file touched).  `lean_local_search` and `lean_hammer_premise` were **unusable
again** (`which rg` → nothing; row 131f, **fifth** confirmation), so every search claim above
rests on `grep`/`sed` over source, `#reduce`/`#check`/`#print axioms`, `lake env lean`
diagnostics, or the re-seeded cone walker — never on a substring count presented as a structural
fact.  `lean_references` was **not** needed this round (no call-site counting).

### 15.6 What to pick up first

1. **`iffIndDecl`'s `= 0` slice, and it needs `PreludeSpec`, not more telescope work.**  §3–§6 are
   done and reusable; the next step is `iffFn`'s faithfulness (`⟦p → q⟧`, `⟦q → p⟧` both nonempty
   ⇒ `p = q`), which is `PreludeSpec.lean`'s business and is the model-side `propext`.  **Do not
   start from §10.9's "free by §10.1's argument"** — that is refuted at this block (15.3).
2. **Then `Iff.intro ↦ •`**, which *is* the small-eliminator argument: its type is measurably a
   proposition.  Cheapest remaining piece of the `consts` field.
3. **Then the `≠ 0` value**: a five-layer `mkLam`, two layers over `U κ 0`.
   `UnitOracleLarge.mkLam_mem_mkForallType_of_dom` and `mem_mkForallType_of_graph` are the
   entries; `recFnL` is *not* a template for the layers over a universe, only for the ones over a
   singleton.
4. **`RegConvE env U (k+1)` — the residual the `RegPi` repair created and nobody has graded.**
   `RegularAtSucc` (`∃ env U k, env.Regular U (k+1)`) is inhabited by nothing in the tree, and
   `RegConvE`'s only instance is at index `0` where `IsDefEqN` is syntactic equality.  Either
   exhibit one at `k+1` or record it as a second unchecked hypothesis; **as it stands the repaired
   assembly has no non-degenerate instance at all** (15.2 item 3).
5. **`propAgreeOn_of_stratifiedNOn` route-B weakening: DO NOT FUND IT.**  I did not make this
   edit, and the reason is not budget.  `Theory/Typing/AppUniqRefute.lean` already contains
   `piLvlEnv_propUniqNOn_all_false` and `ordered_not_enough_for_propUniqNOn` — **the guarded
   `∀ n, PropUniqNOn` is refuted at `Ordered`, and that file's own §"What this closes" says in
   terms that §11 item 3's proposed edit to `PropAgreeWall.lean` "does not change that".**  So the
   weakening buys a strictly weaker hypothesis that is *also* refuted at the same environment.  It
   remains worth having only if a consumer carries `VEnv.WF` rather than `Ordered`, and the brief's
   standing caveat is right about that; but it discharges nothing, and the ten lines should be spent
   only once someone has named the `VEnv.WF`-carrying consumer.  **Verified, not assumed:
   `propAgreeOn_of_stratifiedNOn` is present at `PropAgreeGuarded.lean:193` and takes
   `Ordered env`.**
6. **`eqIndDecl`** — now genuinely next after `iffIndDecl`'s `consts` field, and 15.3 says what to
   expect (the same branch, for `imax`'s reason rather than `Prop`'s; six binders, one index, a
   two-binder motive, and a **`Type`-valued** first parameter, so the `≠ 0` exclusion will need the
   nonemptiness of `U κ (v.eval ls)` rather than of `U κ 0`).

**Do not** re-attack: everything §10.9, §11.7, §12.7, §13.7 and §14.7 name, plus — new —
**`propTypeAgree_appCase_on_of`** (already a theorem in HEAD, 15.1), **`recType_isType` as a
source of the recursor's sort** (it withholds it, 15.4 item 1), and **`iffIndDecl`'s `= 0` slice
as a free case** (refuted, 15.3).

---

## 16. Session of 2026-09-02 (ninth): `eqIndDecl` — the transfer signal **holds**, the `≠ 0` exclusion acquires a hypothesis that is both **satisfiable and necessary**, and §15's own anti-vacuity table has a gap

*Written incrementally, in the order the work happened.*

### 16.0 The `#print axioms`-first check, run before proving anything

Thirteen names, resolved **by namespace**.  All thirteen present and as described — this brief is
**not** a fourth instance of row 144d/146e.

| brief's name | real name | axioms |
|---|---|---|
| `inductOracleOK_NE` | `SetModel.NEAudit.inductOracleOK_NE` | `[propext, Classical.choice, Quot.sound]` |
| `recFnL` | `SetModel.UnitAudit.recFnL` | same |
| `pt_not_mem_interp_iffRecType_of_ne` | `SetModel.IffAudit.…` | same |
| `level_branch_forced` | `SetModel.IffAudit.…` | same |
| `iffEnv_le_preludeEnv`, `hasType_iffRecType`, `isProp_iffRecType_iff` | `SetModel.IffAudit.…` | `[propext, Quot.sound]` |
| `RegularAtSucc`, `regularAtSucc_of` | `SetModel.RegPiAudit.…` | `[propext]` / `[propext, Quot.sound]` |
| `recType_isType` | `Lean4Lean.VInductDecl'.recType_isType` | `[propext, Quot.sound]` |
| `mkLam_mem_mkForallType_of_dom`, `pt_not_mem_mkForallType_of_nonempty` | `SetModel.UnitAudit.…` | `[propext, Classical.choice, Quot.sound]` |
| `nonemptyEnv_le_preludeEnv` | `SetModel.NEAudit.…` | `[propext, Quot.sound]` |

**And the naming trap struck again, this time inside §15 itself.**  §15.3 and §15.6 cite
`PreludeSpec.iffFn_value` and `PreludeSpec.propext_of_mem_UProp`.  `PreludeSpec.lean` declares
into `Lean4Lean.SetModel`, **not** `Lean4Lean.SetModel.PreludeSpec`, so both spellings fail with
*unknown constant*.  The real names are `SetModel.iffFn_value`, `SetModel.eqFn_value`,
`SetModel.propext_of_mem_UProp` — **verified by `#check`**.  Row 146e recorded this trap as the
orchestrator's; it is the *handoff's* too, and the next stream will hit it at the exact lemma the
`= 0` slice needs.

### 16.1 What landed

New file `Lean4Lean/Theory/SetModel/EqOracle.lean` (879 lines, **116 declarations**, **0
`sorry`**, namespace `Lean4Lean.SetModel.EqAudit`, fresh — `grep` over the tree finds no other
occurrence), **imported by `Theory/Equiconsistency.lean`** on the same edit that created it, so it
was never orphaned (rows 128b / 133c / 142e — fifth round running).

`InductOracleOK` at `eqIndDecl` is **not** closed.  What is closed is the level branch, the
typing telescope it rests on, and — new relative to `iffIndDecl` — a **bracketed** account of the
one hypothesis this block adds.

```lean
-- §3.  The telescope, with the sort EXPLICIT, at BOTH recursor universes (`recUvars = 2`).
theorem hasType_eqRecType (hu : u.WF nv) (hv : v.WF nv) (Γ) :
    eqEnv.HasType nv Γ ((eqIndDecl.recType 0).instL [u, v]) (.sort (eqRecSort u v))
-- §4.  Six `imax`es.  `v` NEVER occupies a codomain position — the transfer signal, tested.
theorem eqRecSort_eval_eq_zero_iff : (eqRecSort u v).eval ls = 0 ↔ u.eval ls = 0
theorem eqRecSort_eval_eq_zero_iff_of_ne_zero (_hv : v.eval ls ≠ 0) : …   -- the control
theorem exists_four_corners : ∀ bu bv : Bool, ∃ u v, …                    -- the two levels are independent
-- §5.  One new `VDecl.WF.le` step; `eqEnv` is the FIRST environment of `leanPrelude.reverse`.
theorem eqEnv_le_iffEnv : eqEnv ≤ iffEnv
theorem eqEnv_le_preludeEnv : eqEnv ≤ preludeEnv
-- §6.  The model consequence.
theorem isProp_eqRecType_iff : L.IsProp M Γ ((eqIndDecl.recType 0).instL [u,v]) ↔ u.eval M.ls = 0
theorem pt_not_mem_interp_eqRecType_of_ne (hn : u.eval M.ls ≠ 0) (hx : x ∈ U M.κ (v.eval M.ls)) :
    (pt : V) ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅
theorem eq_pt_of_mem_interp_eqRecType_of_zero (h0 : u.eval M.ls = 0) (hw : w ∈ ⟦…⟧) : w = pt
theorem level_branch_forced …
theorem no_level_uniform_value …          -- §6.6, the form with no member hypothesis
-- §6.4 / §6.5 / §6.5b.  The new hypothesis, bracketed.
theorem exists_mem_U_of_eq_zero / exists_mem_U_of_chain / exists_mem_U_omegaChain
theorem pt_mem_interp_eqRecType_of_empty_dom …        -- the exclusion is FALSE without `hx`
theorem vsetV_empty : vsetV (∅ : V) = ∅
theorem pt_mem_interp_eqRecType_at_zeroChain …        -- …at an EXHIBITED `κ`
theorem exists_mem_interp_eqRecType_zero_iff …        -- §6.6, the gap in §15.5's table
-- §7.  Block facts, all `rfl`.
theorem eq_allConsts / eq_iotaRules_length / eqRefl_fields / iffIntro_fields_length
theorem hasType_EqReflType / reflSort_eval_eq_zero    -- `Eq.refl`'s type IS a proposition
theorem hasType_EqType / eqTyFormerSort_eval_zero     -- `Eq`'s type former is NOT
```

### 16.2 **The transfer signal HOLDS** — and it is a theorem, not a reading

§15.3's positive signal (repeated in the brief) was: the collapse at `iffIndDecl` is **`imax`'s**
(`imax _ 0 = 0`), not `Prop`'s, so `eqIndDecl`'s `Type`-valued parameter should behave the same.

**Confirmed, and it is stronger than predicted.**  `eqRecSort_eval_eq_zero_iff`'s right-hand side
**does not mention `v` at all**; the six-step proof is six `imax_eq_zero_iff`s in which `v`
appears only ever as a *domain*.  I checked it where it could have failed rather than only where
it was convenient:

* `eqRecSort_eval_eq_zero_iff_of_ne_zero` instantiates at a `v` with `v.eval ls ≠ 0` — a
  genuinely `Type`-valued parameter — and the branch is unchanged;
* `exists_four_corners` shows the two universes are **independent**, i.e. all four
  `(u = 0?, v = 0?)` corners are populated, so the previous control is not covering a corner that
  does not exist.

This is the first prediction in this corner that was made about a block *before* the block was
touched and then held.  It is worth saying plainly because §10.9's other prediction did not
(row 146b) and §10.4's pricing did not either (16.5 below).

### 16.3 The prediction that cost something, and I brought back more than was asked

The brief also predicted: *"the `≠ 0` exclusion will need the nonemptiness of `U κ (v.eval ls)`
rather than of `U κ 0`."*  **Right.**  `pt_not_mem_interp_eqRecType_of_ne` carries
`hx : x ∈ U M.κ (v.eval M.ls)`.  That puts this block **third** on a three-point scale nobody had
drawn:

| block | what the `≠ 0` exclusion needs | why |
|---|---|---|
| `iffIndDecl` | **nothing** | outermost binder is a parameter over `Prop`; `∅ ∈ U κ 0` always |
| `eqIndDecl` | an inhabitant of the **parameter** space | outermost binder is `α : Sort v`; `U κ (i+1) = vsetV (κ i)` can be empty |
| `unitDeclLE` | an inhabitant of the **motive** space | no parameters at all; the motive is the outermost binder |

So `eqIndDecl` is strictly *between* the two, not simply "harder", and the motive-space
hypothesis `UnitOracleLarge` needs is the strongest of the three (the motive space is a function
space over the parameter space).

**What was not asked for, and is the part I would keep:** the hypothesis is *bracketed on both
sides*, machine-checked.

* **Satisfiable, three ways.**  `exists_mem_U_of_eq_zero` (free at `v.eval ls = 0` — recovers
  `iffIndDecl`'s situation as a special case); `exists_mem_U_of_chain` (free under
  `IsInaccessibleChain n κ` with `v.eval ls ≤ n`, which is the hypothesis
  `CnstRecursion.leanTTConsistent_of` already carries, so it is **not a new assumption**);
  `exists_mem_U_omegaChain` (free at *every* index at `omegaChain V`, which is a chain of every
  finite length).
* **Necessary, at an exhibited `κ`.**  `pt_mem_interp_eqRecType_of_empty_dom` proves that with
  `U M.κ (v.eval M.ls) = ∅` the conclusion of the exclusion is **false** — `mkForallType` over an
  empty domain is `{∅}`, the empty function, so `•` is a member.  And the configuration is
  reached, not hypothetical: `vsetV_empty` (`vsetV ∅ = ∅`, four lines) gives
  `U zeroChain (i+1) = ∅`, and `pt_mem_interp_eqRecType_at_zeroChain` instantiates the refutation
  at `v := .succ .zero`, `κ := zeroChain` — the same junk chain `AboveAudit.above_false_zeroChain`
  uses.  `U_zero_nonempty` shows `1` really is the least index where this can happen.

That is the shape row 146c asked for, run in the direction nobody runs it: not "is the hypothesis
satisfiable" but "**is the hypothesis doing anything**".  Here it is, and both answers are yes.

### 16.4 **A gap in §15.5's own anti-vacuity table**, and it is not cosmetic

`IffAudit.level_branch_forced` takes `hv₀ : v ∈ ⟦iffRecType.instL [u₀]⟧`.  §15.5's table lists
that theorem's open hypotheses as *"the same [as `isProp_iffRecType_iff`'s], and nothing else — in
particular **no** motive-space inhabitant"*.  **`hv₀` is not in that list, and its satisfiability
is not known.**  The "both slices non-empty" control quoted alongside
(`exists_eq_zero_level` / `exists_ne_zero_level`) is about the two **level** slices; it says
nothing about whether either *interpretation* has a member.

And the two are not independent — they are the same question:

```lean
theorem exists_mem_interp_eqRecType_zero_iff (hu₀) (h0 : u₀.eval M.ls = 0) :
    (∃ w : V, w ∈ ⟦eqRecType.instL [u₀, v]⟧) ↔ (pt : V) ∈ ⟦eqRecType.instL [u₀, v]⟧
```

i.e. **the member hypothesis is satisfiable exactly when the `= 0` slice — the obligation both
files record as OPEN — is true.**  So the implication form of `level_branch_forced`, at *both*
blocks, is conditional on an undischarged obligation.  By this project's own standard that is
"unmeasured", not "no hypothesis but the usual".

*The content survives; only the packaging has to change.*  `no_level_uniform_value` states
`¬ ∃ w, w ∈ ⟦u₀-slice⟧ ∧ w ∈ ⟦u₁-slice⟧` — a **negation**, unconditional in the candidate value,
and it does not evaporate if a slice turns out empty.  That is the form to quote, and the same
restatement should be made at `iffIndDecl`; it is three lines there.  I did **not** edit
`IffOracle.lean` (one-lemma edit, but it is last round's file and a second stream is live), so
this is stated-but-not-landed for `iffIndDecl` and landed for `eqIndDecl`.

### 16.5 **§10.4's pricing of the two blocks is backwards**, and the reason is measurable

§10.4 and §15.6 price the remaining blocks by binder count: *"`Iff` wants five layers and `Eq`
six"*, hence `eqIndDecl` last.  For the `mkLam` **value** that is right.  For the `= 0` **slice**
it is the wrong metric, and the right one is **constructor fields**.

* `iffIndDecl`'s `= 0` slice needs, per row 146b, `Iff`'s faithfulness in both directions, the
  hard half being the model-side `propext`.  That difficulty is **`Iff.intro`'s**, not
  `Iff.rec`'s: `iffIntro_fields_length = 2` (measured), both fields are implications, so
  accepting the constructor forces "`p → q` and `q → p` both inhabited ⇒ `p = q`".
* `eqRefl_fields = []` (measured).  `Eq.refl` has **no fields** — two parameters, one result
  index, nothing else.  There is no propext analogue to pay.  And the faithfulness datum is
  already in the tree as an **equation**, both directions at once:
  `SetModel.eqFn_value : α ∈ U κ i → a ∈ α → b ∈ α → (((eqFn κ i) ‘ α) ‘ a) ‘ b = if a = b then {•} else ∅`
  (verified by `#check`; note the namespace, 16.0).  From it, `h ∈ ⟦Eq α a b⟧` forces both
  `a = b` and `h = •`, and the minor premise supplies the value.

**So `eqIndDecl`'s `= 0` slice should be the cheapest of the three remaining pieces, not the
dearest.**  Labelled a **costing** — not attempted in Lean, per ledger §0 kind 4.

### 16.6 What the nine-lemma telescope actually cost here, and the new failure mode

The brief said to expect `iffIndDecl`'s nine-lemma telescope again and to say what it cost.
**It cost about thirty lemmas, and the extra was not the sixth binder.**

`iffIndDecl`'s two parameters are `.sort .zero`, i.e. **closed**.  `eqIndDecl`'s are `α : Sort v`
and `a : α`, and every application in the telescope applies a function to a **bound variable**.
`.appDF`'s conclusion is `B.inst a`, and `B.inst a` reduces through
`VExpr.instVar 0 a 0 = VExpr.liftN 0 a` — and `liftN_zero` is a **theorem proved by induction on
the expression**, not a definitional unfolding.  So `.appDF` cannot unify the domain, and every
application step needs its equation carried.  Fix, and it is the reusable part:

```lean
theorem hasType_app' (hf : env.HasType nv Γ f (.forallE A B)) (ha : env.HasType nv Γ a A)
    (hC : B.inst a = C) : env.HasType nv Γ (.app f a) C := hC ▸ hf.appDF ha
```

with each `hC` closed by `simp [VExpr.inst, VExpr.instVar]` or `simp [VExpr.inst, VExpr.inst_lift]`.
**Anyone doing a block with non-closed parameters — i.e. every real inductive — will hit this.**
It is a fifth costume of the §12.5 items 1–2 / §13.5 item 6 / §15.4 item 3 family (a
metavariable or a non-reducing substitution in `appDF`'s type), and the first one where the fix
generalises.

### 16.7 What I tried that failed, and the step it failed at

1. **`.appDF` chains stated with the reduced type directly** (the `iffIndDecl` idiom).  Failed at
   *"`ha` has type `HasType Γ a α` but is expected to have type `IsDefEq … ((.bvar 0).inst α)`"*.
   Diagnosis and fix: 16.6.
2. **`simpa [VExpr.inst] using this` to bridge the gap.**  Failed twice, differently: `simp` will
   not fire on `(VExpr.bvar 0).inst α` without `VExpr.inst` *and* `VExpr.instVar` in the simp set,
   and when it does fire it normalises `HasType` to `IsDefEq` and then reports a mismatch against
   an unnormalised goal.  `rw [show … = … from by simp …]` on the hypothesis works; `simpa` does
   not.  This is worth a line because `simpa` is the reflex.
3. **`def zeroChain (V : Type*) [SetStructure V] : ℕ → V := fun _ ↦ ∅`.**  Failed at
   `EmptyCollection V`: `∅ : V` needs `[V↓[ℒₛₑₜ] ⊧* 𝗭]`, which `SetStructure` does not give — and
   re-binding `V` explicitly drops the section's instance.  Fix: leave `V` implicit from the
   section variables.
4. **Passing `M` as `_` to `pt_mem_interp_eqRecType_of_empty_dom`.**  Two successive
   *deterministic timeout at `whnf` / `isDefEq`* (200000 heartbeats) — unification tries to
   reduce `interp` against a concrete `ModelData` literal.  Fix: name `M` and `v` explicitly and
   pre-compute the `U … = ∅` side condition as a `have`.  **No heartbeat bump was needed**; the
   timeout was a symptom of an under-determined elaboration, not of a hard problem.
5. **`vsetV ∅ = ∅` by `eq_empty_of_forall_not_mem`.**  No such lemma here; `mem_ext_iff` plus
   `mem_vsetV_iff_mem_Vset`, `mem_Vset_iff` and `Ordinal.lt_def` does it in five lines.
6. **`PreludeSpec.eqFn_value` / `PreludeSpec.propext_of_mem_UProp`** — *unknown constant*, twice,
   copied straight out of §15.  See 16.0.
7. **Not attempted, deliberately**: the `= 0` slice (16.5 costs it and says it is next), the
   `≠ 0` slice's six-layer `mkLam`, the ι-rule, `Eq`'s type-former value, and the three-line
   restatement inside `IffOracle.lean` (16.4 — last round's file, second stream live).

### 16.8 Measured / read / not run

**[measured]**
* `lake build Lean4Lean.Theory.SetModel.EqOracle`: green, **1205 jobs**.
* `lake build Lean4Lean.Theory.Equiconsistency` after wiring the import: green, **1241 jobs**
  (1240 before).  The one warning it prints is `Equiconsistency.lean:52`, **pre-existing** — my
  diff to that file is a single `import` line.
* `lake env lean` on `EqOracle.lean`: **zero diagnostics** — no errors, no warnings, no `sorry`
  warning.  `grep -c sorry` on the file: **0**.
* **`#print axioms` (via `collectAxioms`) on all 116 declarations of `Lean4Lean.SetModel.EqAudit`**:
  36 `[]`, 20 `[propext]`, 44 `[propext, Quot.sound]`, 16
  `[propext, Classical.choice, Quot.sound]`.  **`sorryAx` count: 0.  No frozen axiom.  No new
  `sorry`, none traded.**
* **Hole cones**, forward over type **and** value with `allowOpaque := true`, a walker re-seeded
  on **all 116** declarations, run in an environment importing `EqOracle` *and*
  `Theory.Typing.ChurchRosser` so that all four named holes are reachable.  **Presence verified in
  the measuring environment, not assumed:**

  ```
  Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.IsDefEqU.weakN_iff              : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.WF.rigidShapeUniqNS             : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.NormalEq.descend                : present = true, sorryAx-tainted = true
  seeds walked: 116;  seeds with any sorryAx-carrying member: 0
  ```

  **Note for the next stream:** `descend`'s Lean name is `Lean4Lean.VEnv.NormalEq.descend`, and
  `ChurchRosser` must be imported or it reads `present = false` — exactly the blind-environment
  failure the brief warns about, which I hit on the first run and fixed.
* **Tainted controls, which fire — including transitively, not only on the seed itself:**
  `IsDefEqU.sort_inv` (cone 3409) reports `forallE_inv_stratified`; `NormalEq.descend` (cone 3837)
  reports three of the four.  So a zero on the 116 seeds is a measurement, not a broken walker.
* Block shape facts by `rfl`: `eqIndDecl.recUvars = 2`, `allConsts = [Eq, Eq.refl, Eq.rec]`,
  `iotaRules.length = 1`, `params.length = 2`, `indices = [.bvar 1]`, `eqRefl_fields = []`,
  `iffIntro_fields_length = 2`.  `eqEnv`'s three constant lookups are `rfl`.
* Namespace collision check: `grep -rn 'EqAudit'` over `Lean4Lean/` and `docs/` before writing —
  **zero** prior occurrences.

**Hole-free is not discharged, reported separately as instructed:**

| result | holes | open hypotheses |
|---|---|---|
| §3's ~30 typing lemmas, `hasType_eqRecType`, `hasType_app'` | none | `u.WF nv`, `v.WF nv` only |
| §4's seven level lemmas and three controls | none | **none** |
| `eqEnv_le_iffEnv`, `eqEnv_le_preludeEnv` | none | **none** |
| `isProp_eqRecType_iff`, `isProp_recBA_iff` | none | `eqEnv ≤ envF` (a theorem at `preludeEnv`), `OnCtx Γ`, and a **`PropSplit envF nv`** — inhabited at `preludeEnv` as data (`propSplitPreludeEnv`, §12) |
| `pt_not_mem_interp_eqRecType_of_ne` | none | the same, **plus** `x ∈ U M.κ (v.eval M.ls)` — satisfiable (§6.4) and necessary (§6.5) |
| `level_branch_forced` | none | the same, **plus** `hw₀`, whose satisfiability **is** the open `= 0` slice (§6.6) — *unmeasured*, and this is 16.4 |
| `no_level_uniform_value` | none | the same as the exclusion; **no member hypothesis** |
| `pt_mem_interp_eqRecType_at_zeroChain`, `vsetV_empty`, `exists_mem_U_omegaChain` | none | none beyond the ambient instances |

**Anti-vacuity.**  `Above` occurs in **no statement** in the file (three mentions, all prose), so
nothing is free at a false `IsInaccessibleChain` antecedent.  **Two `κ`s are chosen, both
deliberately, both in controls, never in a positive bound**, and the file says so in its header:
`omegaChain V` (a good `κ`) only to *satisfy* a hypothesis, `zeroChain` (a bad `κ`, the ledger §0
sixth-blindness one) only to *refute* an unconditional claim.  Every statement in §§3, 4, 6.1,
6.2, 6.3, 6.6 is at an arbitrary `κ`.  Witness environments: `eqEnv ≤ preludeEnv` is proved,
`preludeEnv` is `VEnv.WF` (`preludeEnv_WF`) with **no `VDecl.unsafeDef`** in
`preludeEnv_history`.  Both level slices are non-empty and the two universes are independent
(`exists_four_corners`, four corners).  **Conclusion-freeness checked too** (row 146c's new
shape): `exists_mem_U_omegaChain`'s conclusion `∃ x, x ∈ U κ j` is **not** free — §6.5b exhibits a
`κ` and a `j` where it fails; and `pt_not_mem_interp_eqRecType_of_ne`'s conclusion is not free
either, by the same witness.

**[read]** off source, not run: nothing load-bearing.  16.5's costing of the `= 0` slice is
**reasoning from two measured facts** (`eqRefl_fields = []`, `eqFn_value`'s statement), not a
measurement of the slice; it is labelled a costing.  16.4's claim that
`IffAudit.level_branch_forced` has the same gap is read off that theorem's *statement* (`hv₀` is
in its binder list) plus the machine-checked `exists_mem_interp_eqRecType_zero_iff` at
`eqIndDecl`; the corresponding lemma at `iffIndDecl` is **not** written.

**[not run]** as the brief directed: the full `lake build`, guards 1–3,
`scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`, the Kernel Arena (no
implementation file touched).  `lean_local_search` / `lean_hammer_premise` **not used** — `rg` is
still absent (row 131f, sixth confirmation); every search claim rests on `grep`/`sed` over source,
`#check`/`#reduce`/`collectAxioms`, `lake env lean` diagnostics, or the re-seeded cone walker.
`lean_references` was not needed (no call-site counting this round).

### 16.9 Where the brief was wrong, and where it was right

| brief's assertion | verdict |
|---|---|
| the `imax` transfer signal should carry to `eqIndDecl`'s `Type`-valued parameter | **right, and now a theorem** (16.2), with the four-corner control |
| the `≠ 0` exclusion will need nonemptiness of `U κ (v.eval ls)` | **right** (16.3) — and it is both satisfiable and necessary, which was not asked |
| six binders, one index, a two-binder motive | **right**, all `rfl` (16.1, §7.1) |
| "expect the same nine-lemma telescope and say what it cost" | **understated**: ~30 lemmas, and the extra cost is *not* the sixth binder — it is `liftN_zero` in `appDF`'s substitution (16.6), a failure mode `iffIndDecl` could not exhibit because its parameters are closed |
| row 146b: a prediction that held for the branch says nothing about the slice | **right in direction, wrong in sign for this block** — the slice here is *cheaper*, not dearer, and 16.5 measures why |
| §15.5's anti-vacuity is complete for `level_branch_forced` | **wrong** — `hv₀` is unlisted and unmeasured (16.4) |
| `RegConvE env U (k+1)` / `RegularAtSucc` uninhabited | **verified present and as described**; not attacked (the graded fallback was not needed) |

### 16.10 What to pick up first

1. **`eqIndDecl`'s `= 0` slice — and take it *before* `iffIndDecl`'s.**  16.5 is the argument:
   `Eq.refl` has no fields, `SetModel.eqFn_value` is already a two-directional equation, and there
   is no `propext` to pay.  §§3–6 of `EqOracle.lean` are done and reusable.  If 16.5's costing is
   right this is the cheapest open item in the corner; if it is wrong, finding that out is worth
   more than another telescope.
2. **Restate `IffAudit.level_branch_forced` as a negation** (`no_level_uniform_value`'s shape),
   three lines, and amend §15.5's table.  Until then, do not quote that theorem as unconditional
   (16.4).
3. **Then `Eq.refl ↦ •`** — `hasType_EqReflType` + `reflSort_eval_eq_zero` already prove its type
   is a proposition at every `v`, so this is the small-eliminator argument and it is the cheapest
   remaining `consts` cell at this block, as `Iff.intro ↦ •` is at `iffIndDecl`.
4. **`Eq`'s type former** needs a real internal function (`eqTyFormerSort_eval_zero` shows its
   sort is `1`, not `0`) — `SetModel.eqFn` **is** the intended denotation and
   `UnitAudit.mkLam_mem_mkForallType_of_dom` is the entry, exactly as `nonemptyFn` was at
   `nonemptyIndDecl` (§10.1).
5. **`RegConvE env U (k+1)` / `RegularAtSucc`** — unchanged from §15.6 item 4, still inhabited by
   nothing, not attacked this round because `eqIndDecl` did not stall.
6. **Carry `hasType_app'` forward** (16.6).  Any block whose parameters are not closed needs it,
   which is all of them outside this prelude.

**Do not** re-attack: everything §10.9, §11.7, §12.7, §13.7, §14.7 and §15.6 name, plus — new —
**`eqIndDecl`'s level branch** (done, 16.2), **the unconditional `≠ 0` exclusion at `eqIndDecl`**
(refuted at `zeroChain`, 16.3), **`.appDF` with the reduced type stated directly at a block with
open parameters** (16.6/16.7 item 1), and **`simpa` as the bridge for `VExpr.inst`**
(16.7 item 2).

---

## 17. Session of 2026-09-02 (tenth): Task 2 landed in three lines; Task 1's costing is **tested**

*Written incrementally, in the order the work happened. Sections appear as they are proved.*

### 17.0 The `#print axioms`-first check, run before proving anything, as instructed

Everything the brief names, resolved **by namespace** and measured with `Lean.collectAxioms`
(`#check` first, to catch the naming trap). **Nothing in this brief was already in HEAD**, so this
is *not* a fourth instance of row 144d/146e — but the *naming* trap fired again, exactly where the
brief predicted.

| brief's / handoff's spelling | real name | axioms |
|---|---|---|
| `eqRecSort_eval_eq_zero_iff` | `SetModel.EqAudit.eqRecSort_eval_eq_zero_iff` | `[propext]` |
| `SetModel.eqFn_value` | `Lean4Lean.SetModel.eqFn_value` | `[propext, Classical.choice, Quot.sound]` |
| `eqRefl_fields`, `iffIntro_fields_length` | `SetModel.EqAudit.…` | `[propext]` |
| `hasType_app'` | `SetModel.EqAudit.hasType_app'` | `[propext]` |
| `level_branch_forced` (iff) | `SetModel.IffAudit.level_branch_forced` | `[propext, Classical.choice, Quot.sound]` |
| `exists_mem_interp_eqRecType_zero_iff` | `SetModel.EqAudit.…` | `[propext, Classical.choice, Quot.sound]` |
| `no_level_uniform_value` | `SetModel.EqAudit.…` | `[propext, Classical.choice, Quot.sound]` |
| `liftN_zero` | `Lean4Lean.VExpr.liftN_zero` | `[propext]` |
| `hasType_EqReflType` / `reflSort_eval_eq_zero` | `SetModel.EqAudit.…` | `[propext, Quot.sound]` / `[propext]` |
| `pt_not_mem_interp_eqRecType_of_ne`, `eq_pt_of_mem_interp_eqRecType_of_zero` | `SetModel.EqAudit.…` | `[propext, Classical.choice, Quot.sound]` |
| `isProp_recBA_iff` | `SetModel.EqAudit.…` | `[propext, Quot.sound]` |
| `pt_mem_interp_NE_recType` | `SetModel.NEAudit.pt_mem_interp_NE_recType` | `[propext, Classical.choice, Quot.sound]` |
| `inductOracleOK_NE` | `SetModel.NEAudit.inductOracleOK_NE` | `[propext, Classical.choice, Quot.sound]` |
| `PreludeSpec.iffFn_value` | — | **UNKNOWN CONSTANT** (real: `SetModel.iffFn_value`) |
| `PreludeSpec.propext_of_mem_UProp` | — | **UNKNOWN CONSTANT** (real: `SetModel.propext_of_mem_UProp`) |
| `SetModel.PreludeSpec.iffFn_value` (the fully-qualified guess) | — | **UNKNOWN CONSTANT** |

`sorryAx` count over the whole list: **0**.

**One thing the brief did not name and I found while measuring**, which the next stream must not
mistake for mine: `NEAudit.nonempty_propSplit_preludeEnv` and `NEAudit.propSplitPreludeEnv` in
`PreludeOracle.lean` print `[propext, sorryAx, Classical.choice, Quot.sound]` — **pre-existing**
(route A through `forallE_inv_stratified`; §15.5 records the sorry-free route B alternative). It is
in the import closure of everything below, so *nothing in this corner may be quoted as
"sorry-free at `preludeEnv`" via that route.* My own additions do not touch it.

### 17.1 Task 2: landed, and it is three lines as forecast

`Lean4Lean/Theory/SetModel/IffOracle.lean`, new §6.6 (my only edit to that file):

```lean
theorem no_level_uniform_value (hu₀ : u₀.WF nv) (hu₁ : u₁.WF nv)
    (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0) :
    ¬ ∃ w : V, w ∈ ⟦(iffIndDecl.recType 0).instL [u₀]⟧ ∧ w ∈ ⟦(iffIndDecl.recType 0).instL [u₁]⟧
theorem exists_mem_interp_iffRecType_zero_iff (hu₀ : u₀.WF nv) (h0 : u₀.eval M.ls = 0) :
    (∃ w : V, w ∈ ⟦(iffIndDecl.recType 0).instL [u₀]⟧) ↔ (pt : V) ∈ ⟦…⟧
```

Both `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. `lake build
Lean4Lean.Theory.SetModel.IffOracle`: green, **1204 jobs** (unchanged — the module count does not
move for an in-file addition). `grep -c sorry` on the file: **0**.

**And it is strictly better than its `eqIndDecl` twin**, which is the one thing worth noting:
`EqAudit.no_level_uniform_value` still carries `hx : x ∈ U M.κ (v.eval M.ls)` because
`eqIndDecl`'s outermost binder is `α : Sort v`; `iffIndDecl`'s is a parameter over `Prop`, so the
`Iff` version's *only* open hypotheses are `hle : iffEnv ≤ envF` (a theorem at `preludeEnv`) and
the `PropSplit` parameter. So the accounting-gap fix at `iffIndDecl` produces an
**unconditional-in-both-`w`-and-`κ`** statement, which the `eqIndDecl` one cannot be.

**§15.5's table corrected** in place, with the old text struck through and the reason recorded, so
a reader of §15 alone cannot carry away the wrong accounting.

### 17.2 Task 1: the costing is **TESTED, and it holds for the conclusion** — `eqIndDecl`'s `= 0` slice is PROVED

New file `Lean4Lean/Theory/SetModel/EqZeroSlice.lean` (783 lines, **78 declarations**, **0
`sorry`**, namespace `Lean4Lean.SetModel.EqZeroAudit` — `grep` over `Lean4Lean/` and `docs/` before
writing found **zero** prior occurrences), **imported by `Theory/Equiconsistency.lean` on the same
edit that created it**, so it was never orphaned (rows 128b / 133c / 142e — sixth round running).

```lean
-- §5.  The headline.  `InductOracleOK`'s `consts` obligation at `Eq.rec`, `= 0` branch.
theorem pt_mem_interp_eqRecType_of_zero (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
    (h0 : u.eval M.ls = 0) (hspec : EqSpec M v) :
    (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅
-- §5.1.  The SECOND `consts` cell, which §16.10 item 3 also asked for.
theorem pt_mem_interp_EqReflType (hspec : EqSpec M v) :
    (pt : V) ∈ ⟦Eq.refl's type at v⟧          -- no `h0`: `reflSort_eval_eq_zero` at EVERY `v`
theorem not_pt_mem_interp_EqReflType_of_empty …  -- …and `EqSpec` is NECESSARY there
-- §4.  The reusable parts.
theorem interp_eqAp_bvars …            -- ⟦Eq α a b⟧ = M.cnst ``Eq [v] ‘ α ‘ a ‘ b, at any context
theorem isProof_reflC1_ctxM …          -- `Eq.refl α` IS a proof: `imax v 0 = 0` at every `v`
theorem value_mem_of_mem_mkForallType … -- a member of a `mkForallType` is a function on its domain
theorem motive_value_mem_UProp …        -- at `u.eval = 0` the motive's values are truth values
-- §6.  The transfer crux, measurable without the `iffIndDecl` telescope.
theorem pt_mem_mkForallProp_self (hp : p ∈ UProp) : (pt : V) ∈ ⟦p → p⟧
```

**Both cells are discharged from `EqSpec M v` alone.**  `EqSpec` (`SetModel/PreludeSpec.lean`,
note the namespace) pins the type former's oracle value to
`M.cnst ``Eq [v] ‘ α ‘ a ‘ b = if a = b then {•} else ∅`, and it is **satisfied by this
development's own witness**: `SetModel.preludeWitness_eq : ∀ κ ls u, EqSpec (preludeWitness κ ls) u`
(`#check`ed, `[propext, Classical.choice, Quot.sound]`).  So the hypothesis is not new — it is the
one `PreludeSpec.lean` was written to state and `preludeSpec_satisfiable` already meets.

**The shape of the proof, for whoever does the next block.**  Six `mem_interp_forallE_prop_iff`
peels (all six binders are impredicative at `u.eval M.ls = 0`, §3), then:

1. `hw : w ∈ ⟦Eq α a b⟧` plus `EqSpec` forces `a = b` **and** `w = •`;
2. the goal `• ∈ f ‘ b ‘ w` becomes `• ∈ f ‘ a ‘ •`, which is **literally the minor premise's own
   type** (`interp_minTyE_val`), inhabited by `m`;
3. and it is a subset of `{•}` because the motive's own type says its values are truth values at
   `u.eval = 0` (`motive_value_mem_UProp`).

Step 3 is the one a reader will underestimate: `m ∈ f ‘ a ‘ •` alone does **not** give
`• ∈ f ‘ a ‘ •`.  `InterpSound.propSound_of_mem_sort` would, but its hypothesis is part 3 of
interpretation soundness — i.e. the theorem this whole corner is building toward — so it is
**circular here**, and the motive binder has to be unfolded instead (two `mkForallType`s, because
the motive's type is *not* a proposition: its sort is `imax v (imax 0 (u+1)) ≥ 1`).

### 17.3 …**but the costing's REASON is wrong, and that is the finding worth carrying**

Row 149c / §16.5 price `eqIndDecl`'s slice below `iffIndDecl`'s on two grounds:

> `eqRefl_fields = []` against `iffIntro_fields_length = 2` — so the `propext` half that makes
> `iffIndDecl`'s slice hard is `Iff.intro`'s — and `SetModel.eqFn_value` is **already a
> two-directional equation in the tree**.

The first ground is right and §5 confirms what it predicts.  **The second does not distinguish the
two blocks at all**, and I checked rather than assumed:

| datum | `Eq` | `Iff` |
|---|---|---|
| the faithfulness equation in the tree | `eqFn_value : eqFn κ i ‘ α ‘ a ‘ b = if a = b then {•} else ∅` | `iffFn_value : iffFn ‘ p ‘ q = if p = q then {•} else ∅` — **same shape** |
| the specification a slice would assume | `EqSpec M v` | `IffSpec M` (no level argument — `iffIndDecl.uvars = 0`) |
| witnessed by | `preludeWitness_eq` | `preludeWitness_iff` — **the same `ModelData`** |

All six cells `#check`ed this session.  So "the equation is already in the tree" is true on both
sides, and it cannot be the reason `eqIndDecl` is cheaper.

**What does differ at the recursor is the minor premise's binders, and it is a `rfl`-backed
structural fact rather than a reading.**  `IffAudit.minTyI` is

```lean
.forallE (.forallE (.bvar 2) (.bvar 2))            -- x : a → b
  (.forallE (.forallE (.bvar 2) (.bvar 4))         -- y : b → a
    (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))))
```

— `Iff.rec`'s minor premise carries the **constructor's two field binders**, where
`EqAudit.minTyE` (`.app (.app (.bvar 0) (.bvar 1)) (reflAp v (.bvar 2) (.bvar 1))`) carries none.
That is the true cost difference: to reach `• ∈ f ‘ •` from a minor premise at `iffIndDecl` one
must first traverse those two binders, which needs `⟦a → b⟧` and `⟦b → a⟧` **inhabited**.

**And that does not need the model-side `propext` either.**  By the time the minor premise is
consumed, the major premise plus `IffSpec` have *already* given `a = b`, so both binders are
`⟦a → a⟧`, and `pt_mem_mkForallProp_self` (§6, six lines, proved) says a `∀` from a truth value to
itself is inhabited: a proposition is a subset of `{•}`, so a member of the domain *is* `•`, and
the codomain is the domain.

**So row 146b / §15.3's "the `= 0` slice needs `iffFn`'s faithfulness in both directions, and the
hard half is the model-side `propext`" appears misattributed at the recursor.**  The `propext`
content is `Iff.intro`'s obligation — §16.5 got that right — and `Iff.rec`'s slice should go
through from `IffSpec` exactly as `Eq.rec`'s does from `EqSpec`.  **Labelled a costing, not a
theorem**: the `iffIndDecl` slice was *not* attempted, because it needs its own copies of §§1–4
(the `snoc` ladder, the `OnCtx` chain, the `IsProp` chain, the ten `¬IsProof` decisions) — about
forty lemmas, none of which transfer from `Eq`'s contexts.  The one crux that is measurable
without them is `pt_mem_mkForallProp_self`, and it is proved.

**Net verdict on row 149c.**  Conclusion right, reason wrong, margin much smaller than advertised:
not "no `propext` versus `propext`" but "no field binders versus two, both traversable".  This is
the seventh costing in this corner to come back qualified, and the first where the *conclusion*
survived and only the *argument* failed — which is a different failure mode from rows 146b and
149c's own and worth distinguishing: an argument that reaches the right answer by a route that
does not exist will mis-price the *next* block.

### 17.4 The `liftN_zero` / `hasType_app'` tax the brief predicted — measured, and one new detail

§16.6 / row 149c: *"`eqIndDecl`'s parameters are open, so `appDF`'s `B.inst a` reduces through
`liftN_zero`, a theorem rather than a reduction — `hasType_app'` exists for exactly this, and every
non-prelude block will hit it."*  **Right, and I used `EqAudit.hasType_app'` six times.**  Two
things to add:

1. **The simp set is not the one §16.6 gives.**  §16.6 says each `hC` closes by
   `simp [VExpr.inst, VExpr.instVar]` or `simp [VExpr.inst, VExpr.inst_lift]`.  For an argument
   that is a `.bvar` at a *generic* index — which is what a reusable lemma needs — the goal is
   `VExpr.liftN 1 (.bvar (i+1)) = .bvar (i+2)`, and that needs **`liftVar` in the simp set** (note:
   `liftVar` is *not* in the `VExpr` namespace — `VExpr.liftVar` is an *unknown constant*, which
   cost a round) and then an **`omega`**, because `simp` normalises the index to `1 + (i + 1)` and
   stops.  The working incantation is
   `by simp [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar]; omega`.
2. **State the index as `i+1`, never `i`.**  `(.forallE (.bvar (i+1)) (.sort .zero)).inst (.bvar j)`
   is `.forallE (.bvar i) (.sort .zero)` **only when `i ≥ 1`**; at `i = 0` the substitution fires
   instead and the result is a lift of `.bvar j`.  A lemma stated at a generic `.bvar i` therefore
   does not hold, and `simp` reports "made no progress" rather than anything informative.  All
   three of this file's uses instantiate at `i ∈ {0, 1, 3}`, so writing the binder as `i+1`
   throughout makes one lemma serve all three contexts.

### 17.5 What I tried that failed, and the step it failed at

1. **`InterpSound.propSound_of_mem_sort` for step 3 of §17.2.**  It is exactly the statement
   needed ("a term of a `Prop`-level sort denotes a subset of `{•}`") and it is a theorem in HEAD —
   but its hypothesis is `⟦e⟧ρ ∈ ⟦A⟧ρ`, i.e. **part 3 of interpretation soundness**, which is what
   this whole corner is building toward.  **Circular here.**  Fix: unfold the motive binder
   instead (`motive_value_mem_UProp`, two `mkForallType` peels).  Worth writing down because the
   lemma's *name* makes it look like free infrastructure.
2. **`value_eq_of_kpair_mem` without an `IsFunction` instance in scope.**  *failed to synthesize
   instance of type class `IsFunction g`*.  Fix: `have hfun : IsFunction g := IsFunction.of_mem hfn`
   — a plain `have` is enough (a local hypothesis of class type is a local instance);
   `QuotInterp.quotLift_fCod` does the same three lines inline, and
   `value_mem_of_mem_mkForallType` is now the reusable form.
3. **`VExpr.liftVar` in a simp set** — *unknown constant*.  The declaration is `Lean4Lean.liftVar`,
   outside the `VExpr` namespace, even though `VExpr.liftN` is inside it (`Theory/VExpr.lean:17`
   versus `:38`).
4. **A generic `Eq`-application lemma at `.bvar i`.**  `simp` reported *"made no progress"* on the
   second application's substitution.  Diagnosis and fix: 17.4 item 2.
5. **`include hv in` placed *after* a docstring.**  *unexpected token 'include'; expected 'lemma'*.
   The repo's order is `omit … in`, then `include … in`, then the docstring, then the declaration;
   `EqOracle.lean` follows it and I did not, twice.
6. **Passing `Γ` positionally to my own context lemmas.**  `EqAudit` declares
   `variable (Γ : List VExpr)` (explicit) and this file declares `{Γ : List VExpr}` (implicit), so
   `onCtx_B hu hv trivial Γ` is a *function expected* error and the `trivial` for `OnCtx [] _`
   cannot be elaborated until `Γ` is pinned.  Fix: `(Γ := [])` named argument at every call.  Five
   occurrences.
7. **`omega` for the `read_peel` chain without `(j := …)`.**  The index is determined by the
   *third* argument and `omega` runs first, so it sees `j < n` with `j` a metavariable and reports
   *"No usable constraints found"*.  Fix: name `j` explicitly.
8. **`[V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]` omitted from the `snoc`-reading section.**  `IsSeq`/`isSeq_empty` need it
   (`PreludeSpec.lean` declares them under both instances), and the failure is a bare
   *failed to synthesize instance*, four lines away from the cause.
9. **Not attempted, deliberately, and each for a stated reason**:
   * the `iffIndDecl` `= 0` slice (17.3 — needs its own §§1–4, ~40 lemmas);
   * the **necessity of `EqSpec` at the recursor cell**.  The negative bound there needs the oracle
     to be too *true* rather than too empty, hence a `ModelData` whose `Eq` is a constant-`{•}`
     internal function **and** a motive separating two elements of `α` — two `mkLam` nests.  Note
     that `PreludeOracle.lean:905` asserts the analogous control for `Nonempty` ("a constant-true
     `Nonempty` satisfies the constructor and fails here") **in prose**; the only negative bound
     that file actually *proves* is `not_mem_interp_zeroOracle_NE_type`, of the cheap
     too-empty shape at the type former.  So the expensive control has no precedent in the tree
     either, and 17.6 records the cheap one I did land.
   * the `≠ 0` slice's six-layer `mkLam` value, the ι-rule, and `Eq`'s type-former value.

### 17.6 Measured / read / not run

**[measured]**
* `lake build Lean4Lean.Theory.SetModel.IffOracle`: green, **1204 jobs** (unchanged).
* `lake build Lean4Lean.Theory.SetModel.EqZeroSlice`: green, **1206 jobs**.
* `lake build Lean4Lean.Theory.Equiconsistency` after wiring the import: green, **1242 jobs**
  (1241 before).  Its one warning is `Equiconsistency.lean:53`, the **pre-existing** `sorry`
  (`:52` in §16 — the line moved by one because my diff to that file is a single `import`).
* `lake env lean` on `EqZeroSlice.lean` and on `IffOracle.lean`: **zero diagnostics** — no errors,
  no warnings, no `sorry` warning, no linter warning.  `grep -c sorry` on `EqZeroSlice.lean`: **0**;
  on `IffOracle.lean`: **0**.
* **`#print axioms` (via `Lean.collectAxioms`) on all 78 declarations of
  `Lean4Lean.SetModel.EqZeroAudit` plus the 2 new `IffAudit` ones — 80 seeds**: 1 `[propext]`,
  41 `[propext, Quot.sound]`, 38 `[propext, Classical.choice, Quot.sound]`.  **`sorryAx` count: 0.
  No frozen axiom.  No new `sorry`, none traded.**
* **Hole cones**, forward over type **and** value with `allowOpaque := true`, the walker re-seeded
  on **all 80**, in an environment importing `EqZeroSlice` *and* `Theory.Typing.ChurchRosser`.
  **Presence verified in the measuring environment, not assumed** (row 149d's check, run first):

  ```
  Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.IsDefEqU.weakN_iff              : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.WF.rigidShapeUniqNS             : present = true, sorryAx-tainted = true
  Lean4Lean.VEnv.NormalEq.descend                : present = true, sorryAx-tainted = true
  seeds walked: 80;  seeds with any sorryAx-carrying cone member: 0
  ```
* **Tainted controls fire, transitively:** `IsDefEqU.sort_inv` (cone 3409) reaches
  `forallE_inv_stratified`; `NormalEq.descend` (cone 3837) reaches three of the four.  So the zero
  over 80 seeds is a measurement, not a broken walker.
* `#check` on `SetModel.eqFn_value`, `SetModel.iffFn_value`, `SetModel.EqSpec`, `SetModel.IffSpec`,
  `SetModel.preludeWitness_eq`, `SetModel.preludeWitness_iff` — all six present, and the two
  `if _ = _ then {•} else ∅` equations are of the **same shape** (17.3).
* `IffAudit.minTyI`'s two field binders and `EqAudit.minTyE`'s absence of any: read off `abbrev`s
  whose defining equation is `rfl` in the tree.
* Namespace collision check: `grep -rn 'EqZeroAudit'` over `Lean4Lean/` and `docs/` **before**
  writing — zero prior occurrences.

**Hole-free is not discharged, reported separately as instructed:**

| result | holes | open hypotheses |
|---|---|---|
| §1's 19 `snoc`-reading lemmas | none | none beyond the ambient `𝗭𝗙`/`𝗔𝗖` instances |
| §2's seven `OnCtx` lemmas, §4's typing lemmas | none | `u.WF nv`, `v.WF nv`, `OnCtx Γ` |
| §3's six `IsProp` lemmas, §4's ten `¬IsProof`/`IsProof` decisions | none | the same, **plus** `eqEnv ≤ envF` (a theorem at `preludeEnv`) and a **`PropSplit envF nv`** — inhabited at `preludeEnv` as data (`propSplitPreludeEnv`), but see the `sorryAx` note in 17.0 |
| `interp_eqAp_bvars`, `interp_majTyE_val`, `interp_minTyE_val`, `interp_resE_val`, `interp_eqApX_val`, `interp_eqApP_val` | none | the same |
| `value_mem_of_mem_mkForallType`, `pt_mem_mkForallProp_self` | none | **none** (pure set theory) |
| `motive_value_mem_UProp` | none | the same as §3, plus `h0 : u.eval M.ls = 0` |
| **`pt_mem_interp_eqRecType_of_zero`** | none | the same, plus **`EqSpec M v`** — satisfiable at `preludeWitness` (`preludeWitness_eq`), necessity **not proved at this cell** (17.5 item 9) |
| **`pt_mem_interp_EqReflType`** | none | the same **minus `h0`**, plus `EqSpec M v` — and here `EqSpec` **is** shown necessary (`not_pt_mem_interp_EqReflType_of_empty`) |

**Anti-vacuity, and this corner is the most exposed in the repo.**

* **`Above` occurs in no statement in either file** (grep: zero occurrences in `EqZeroSlice.lean`,
  zero in `IffOracle.lean`), so nothing here is free at a false `IsInaccessibleChain` antecedent.
* **No `κ` is chosen anywhere in `EqZeroSlice.lean`.**  Every statement is at an arbitrary
  `κ : ℕ → V` and an arbitrary `ModelData`, so no result rests on a good or a junk chain — unlike
  `EqOracle.lean` §§6.4–6.5b, which choose two deliberately and say so.
* **The `PropSplit` parameter and `hle`.**  `hle : eqEnv ≤ envF` is discharged at `preludeEnv` by
  `EqAudit.eqEnv_le_preludeEnv`; `preludeEnv` is `VEnv.WF` (`preludeEnv_WF`) and its history has no
  `VDecl.unsafeDef`.  `PropSplit preludeEnv nv` is inhabited (`propSplitPreludeEnv`) — **but by a
  route that carries `sorryAx`** (17.0), so the honest statement is "inhabited as data, not
  sorry-free by that route", and §15.5 records a sorry-free route B.
* **The hypothesis is not empty**: `EqSpec M v` is *satisfied* at `preludeWitness` for every `κ`,
  `ls` and `v` (`preludeWitness_eq`), and `PreludeSpec.eqFn_refl` / `eqFn_distinct` show both
  branches of its `if` are exercised there, so it is not met by a degenerate `Eq`.
* **The CONCLUSION is not free**, which is the check row 146c says every instrument sails past.
  Two independent witnesses:
  1. `EqAudit.pt_not_mem_interp_eqRecType_of_ne` **refutes the same membership** on the `u.eval ≠ 0`
     branch (over a nonempty parameter space), and `EqAudit.exists_ne_zero_level` says that branch
     is populated.  So `• ∈ ⟦Eq.rec's type⟧` is *false* at some reachable instantiation and `h0` is
     load-bearing, not decoration.
  2. At the constructor cell, `not_pt_mem_interp_EqReflType_of_empty` refutes the conclusion at any
     oracle whose `Eq` value is empty at a reflexive instance the model reaches — so
     `pt_mem_interp_EqReflType` is not a statement that holds at every `M`.
* **`no_level_uniform_value` at `iffIndDecl` (17.1)** is a negation, so it cannot be satisfied by an
  empty slice; its only open hypotheses are `hle` and the `PropSplit` parameter.
* **A gap I am leaving open and naming**: the necessity of `EqSpec` at the **recursor** cell.  It is
  the one place where this file's hypothesis is satisfiable-but-unmeasured, exactly the shape 17.1
  fixed for `hv₀`, and 17.5 item 9 says what it would cost.

**[read]** off source, not run: 17.3's conclusion that `Iff.rec`'s `= 0` slice needs no model-side
`propext` — **reasoning from three measured facts** (`iffFn_value`'s shape, `minTyI`'s shape,
`pt_mem_mkForallProp_self`), *not* a proof of that slice, and labelled a costing.  17.5 item 9's
claim that `PreludeOracle.lean:905`'s constant-true control is prose rather than a theorem: read
off that file, then confirmed by `grep` finding no `trueNE`-shaped declaration.

**[not run]** as the brief directed: the full `lake build`, guards 1–3,
`scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`, the Kernel Arena (no
implementation file touched).  `lean_local_search` / `lean_hammer_premise` **not used** — `rg` is
still absent (row 131f, **seventh** confirmation); every search claim above rests on `grep`/`sed`
over source, `#check`/`Lean.collectAxioms`, `lake env lean` diagnostics, or the re-seeded cone
walker.  `lean_references` was not needed (no call-site counting this round).

### 17.7 Where the brief was wrong, and where it was right

| brief's assertion | verdict |
|---|---|
| "`eqIndDecl`'s `= 0` slice should be the cheapest remaining item here" | **right about the item** — proved this session, and the second `consts` cell (`Eq.refl ↦ •`) came with it |
| "…because `eqRefl_fields = []` against `iffIntro_fields_length = 2`" | **right**, and it is the true cost difference (17.3) |
| "…and because `SetModel.eqFn_value` is already a two-directional equation in the tree" | **WRONG as a distinguishing reason**: `iffFn_value` is the same equation, `IffSpec` the same hypothesis, `preludeWitness` the same witness (17.3) |
| the `propext` half is `Iff.intro`'s | **right, and stronger than stated** — it appears to be *only* `Iff.intro`'s, so `Iff.rec`'s slice should not need it at all (17.3, a costing) |
| expect `hasType_app'`/`liftN_zero`, and every non-prelude block will hit it | **right**, six uses — and the recipe in §16.6 is incomplete for a generic `.bvar` argument (17.4) |
| Task 2 is three lines | **right**, and the `iffIndDecl` version is *better* than its `eqIndDecl` twin (17.1) |
| §15.5's table under-reports `level_branch_forced`'s hypotheses | **right**, corrected in place (17.1) |
| "three of my briefs have asked for work already in HEAD" — is this a fourth? | **no.** All sixteen names checked resolve and none of the two tasks was done (17.0) |
| the naming trap is now in the handoffs | **right** — `PreludeSpec.iffFn_value`, `PreludeSpec.propext_of_mem_UProp` and `SetModel.PreludeSpec.iffFn_value` are all *unknown constant* (17.0) |
| the `present = true` check matters | **right, and it was cheap**: all four read `present = true` here on the first run *because* I imported `ChurchRosser` as §16.8 instructed — the check cost nothing and would have caught it |

### 17.7b Ledger rows, and a numbering collision

Rows **151, 151b, 151c, 151d**.  Note for the orchestrator: I first wrote them as 150–150d and
found **another stream had already taken 150–150d** in `docs/vacuity-ledger.md` in the same window
(the `VInductDecl'.WF (mpAux mpAuxNodeB)` block).  Renumbered to 151.  Two concurrent streams both
appending to the same table will silently produce duplicate row ids; whoever appends next should
`grep -n "^| 15"` first rather than reading the tail of the file.

### 17.8 What to pick up first

1. **`iffIndDecl`'s `= 0` slice, and do NOT budget `propext` for it.**  17.3 is the argument, and
   `pt_mem_mkForallProp_self` is the one piece already proved.  The cost is the §§1–4 telescope at
   `Iff`'s contexts (~40 lemmas, none transferable), *not* the mathematics.  If 17.3 is wrong the
   failure will be at the two field binders of `minTyI`, and that is worth knowing either way.
2. **The necessity of `EqSpec` at the recursor cell** (17.5 item 9).  This is the only
   satisfiable-but-unmeasured hypothesis this file introduces, it is the same shape as the `hv₀` gap
   17.1 just closed, and the control has **no precedent in the tree** — `PreludeOracle.lean:905`
   asserts the `Nonempty` analogue in prose only.  Two `mkLam` nests: a constant-`{•}` `Eq`
   denotation, and a motive separating two elements of `α`.
3. **`Eq`'s type former** — unchanged from §16.10 item 4.  `SetModel.eqFn` is the intended
   denotation, `eqTyFormerSort_eval_zero` shows its sort is `1` not `0` so `•` is illegal, and
   `UnitAudit.mkLam_mem_mkForallType_of_dom` is the entry.  With `Eq.rec` and `Eq.refl` now done
   this is the **last** of the three `consts` cells at this block.
4. **Then the ι-rule** (`eq_iotaRules_length = 1`) and the `≠ 0` slice's six-layer `mkLam`.
5. **`RegConvE env U (k+1)` / `RegularAtSucc`** — unchanged from §15.6 item 4 and §16.10 item 5,
   still inhabited by nothing, still not attacked.
6. **Carry `value_mem_of_mem_mkForallType` and `pt_mem_mkForallProp_self` forward.**  The first is
   needed at every block whose motive is not over a singleton; the second at every block whose
   constructor has `Prop`-valued fields.

**Do not** re-attack: everything §10.9, §11.7, §12.7, §13.7, §14.7, §15.6 and §16.10 name, plus —
new — **`eqIndDecl`'s `= 0` slice** (proved, 17.2), **`Eq.refl ↦ •`'s membership** (proved, §5.1),
**`InterpSound.propSound_of_mem_sort` as free infrastructure for a slice** (circular, 17.5 item 1),
**a generic `Eq`-application lemma stated at `.bvar i` rather than `.bvar (i+1)`** (false at
`i = 0`, 17.4 item 2), and **`VExpr.liftVar`** (unknown constant; it is `Lean4Lean.liftVar`).

## 18. Session of 2026-09-02 (eleventh): the **type-former cell is CLOSED**, and `EqSpec` is *refuted* as its hypothesis — the brief's Task-1 framing was wrong in one specific way

New file: `Lean4Lean/Theory/SetModel/EqTypeFormer.lean` (namespace **`Lean4Lean.SetModel.EqTFAudit`**
— not the filename; §16's row-146e trap again). Imported from `Theory/Equiconsistency.lean` on the
same edit, so it was never orphaned.

Per-module build: `lake build Lean4Lean.Theory.SetModel.EqTypeFormer` → **1207 jobs**, ✔, 2.0s.
No `sorry` added, none traded. `#print axioms` on all 17 declarations, by namespace: every one is
`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`. **No `sorryAx` anywhere in
this file**, and no new frozen-axiom dependency.

### 18.1 Proved

| name (`Lean4Lean.SetModel.EqTFAudit.*`) | what |
|---|---|
| `eqFn_mem_interp_EqType` | **`eqFn M.κ (v.eval M.ls) ∈ ⟦∀ (α : Sort v) (a b : α), Prop⟧ ∅`** — the cell |
| `mem_interp_EqType_of_eqFn` | same, packaged as `OracleOK`'s `type` field wants it, from `hfn : M.cnst ``Eq [v] = eqFn M.κ (v.eval M.ls)` |
| `not_isProp_tf1/2/3` | the three binders' codomains are not propositions (`imax v (imax v 1)`, `imax v 1`, `1`) |
| `hasType_tf2/3` | the two inner telescopes typed with explicit sorts (what `not_isProp_*` need) |
| `preludeWitness_cnst_eq` | `(preludeWitness κ ls).cnst ``Eq [w] = eqFn κ (w.eval ls)` — **`rfl`** |
| `preludeWitness_congr_Eq` | the `congr` field at `Eq`, level computation only |
| `mem_interp_EqType_preludeWitness` | the cell at this development's own witness |
| **`oracleOK_Eq`** | **both `OracleOK` fields at the name `Eq`**, arbitrary `κ`, arbitrary `envF ≥ eqEnv`, via `oracleOK_of` (so `Above.pure` twice) |
| `eqSpec_badEqM`, `not_mem_interp_EqType_badEqM`, `eqSpec_not_sufficient` | the control of 18.2 |

The proof is **three** applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`, one per `mkLam`
layer of `SetModel.eqFn`, and nothing else — no set-theoretic content beyond
`true_mem_UProp`/`empty_mem_UProp` at the innermost body. §17.8 item 3 named the entry correctly.
Total: ~35 lines of tactic proof. **The route was cheap, not expensive, and not closed.**

### 18.2 Where the brief is wrong — Task 1's hypothesis

> "Two of the three are done … **both from `EqSpec M v` alone** … The **type former** is what
> remains."

The framing invites the reading that the type-former cell is the third instance of the same
pattern and wants the same hypothesis. **It is not, and it does not.** `EqSpec` is *refuted* as a
sufficient hypothesis here, machine-checked:

```lean
theorem eqSpec_not_sufficient (L : PropSplit envF nv) (ls : List ℕ) {v : VLevel}
    (hv : v.WF nv) (hle : eqEnv ≤ envF) (hvz : v.eval ls ≠ 0) :
    ∃ M : ModelData V, EqSpec M v ∧
      ¬ (M.cnst ``Eq [v] ∈ (interp M L [] (eqTypeFormerType v)).toFun ∅)
```

The reason is structural and worth carrying to every future type-former cell:

* the `Eq.rec` and `Eq.refl` cells conclude **`• ∈ …`**. That is decided by *applied values*, and
  `EqSpec` — an equation about `M.cnst ``Eq [v] ‘ α ‘ a ‘ b` — is exactly the right strength.
* the type-former cell concludes **`M.cnst ``Eq [v] ∈ …`**. By `mem_mkForallType_iff` that asks the
  value *itself* to be a set of Kuratowski pairs, functional, with domain `U M.κ (v.eval M.ls)`.
  Application `‘` is a **read** of a graph; an equation about reads constrains nothing outside what
  the read sees. So no value-level spec can imply this cell, for any block.

The hypothesis that does work is the value's **identity**: `hfn`. It costs nothing in this corner
(`preludeWitness_cnst_eq` is `rfl`), but it is a *different kind* of assumption from `EqSpec`, and
a stream that budgeted "EqSpec again" would have mis-scoped the file.

**Honesty about the control's strength.** `badEqM` uses `zeroChain`, where
`U zeroChain (j+1) = ∅` (`EqAudit.U_zeroChain_succ`), so `EqSpec` holds *vacuously* there while the
conclusion still has content (`mkForallType` over an empty domain sits inside `Y ^ ∅`, whose only
member is `∅`, and the bad entry `{•}` is not `∅`). That is a genuine proof that
`EqSpec ⊬ cell`, and it is the cheapest one; it is **not** the stronger statement "EqSpec is
insufficient at a good `κ`". A non-vacuous version is available and I did not build it: take
`M.cnst ``Eq [v] := eqFn κ i ∪ {∅}` — `∅` is not a Kuratowski pair (`⟨a,b⟩ₖ = {{a},{a,b}}` is
inhabited), so `subset_prod_of_mem_function` fails while every applied value is unchanged. That
would hold at an arbitrary `κ`. Priced at ~15 lines; it needs the `value`/`‘` lemma that adding a
non-pair leaves reads unchanged, which I did not locate.

### 18.3 Anti-vacuity, this corner specifically

* **`Above` occurs in no statement in the new file.** `oracleOK_Eq` goes through `oracleOK_of`,
  which is `Above.pure` on both fields — so the substance is the *unwrapped* proposition
  `mem_interp_EqType_preludeWitness`, and there is no false antecedent to hide behind.
* **No `κ` is chosen in any positive statement.** `eqFn_mem_interp_EqType`, `oracleOK_Eq` and
  everything they use are at an arbitrary `κ : ℕ → V`, arbitrary `ModelData`, arbitrary `v`. The
  only named `κ` in the file is `zeroChain`, in §3's **control**, i.e. in a negative statement.
* **The conclusion is not free** — checked in the direction the brief warns about, not only the
  hypothesis direction. `not_mem_interp_EqType_badEqM` exhibits an assignment at which the *same
  conclusion shape* is FALSE. So "eqFn lands in the interpretation" is not a statement that holds
  of every assignment at every environment; it discriminates.
* **`hle : eqEnv ≤ envF` is load-bearing — labelled REASONING, not measured.**
  `lean_minimal_hypotheses` reports "load-bearing" but its own docstring says a body naming `hle`
  fails to elaborate without the binder, so that verdict measures the *body*, not necessity. The
  argument: `hle` is what `isProp_iff` uses to reach `L.prop_sound`; with `IsProp` unconstrained
  `interp` could take the `mkForallProp` branch, whose members are `⊆ {•}`, and `eqFn κ i` is
  neither `∅` nor `{•}` as soon as `U κ i` has an inhabited member. Not run.
* `L : PropSplit envF nv` is a parameter of both the positive statement and the control, so they
  sit on identical footing; the known wall (`Nonempty (PropSplit preludeEnv 0)`) is untouched
  either way. Note also that **`NEAudit.nonempty_propSplit_preludeEnv` prints `sorryAx`** — I
  re-confirmed this in the same build log — so nothing above may be quoted as "sorry-free *at
  `preludeEnv`*" by routing through it. What is sorry-free is everything in the new file, at an
  arbitrary `envF ≥ eqEnv`.

### 18.4 Status of `InductOracleOK` at `eqIndDecl` after this file

| obligation | status |
|---|---|
| `consts` at `Eq` (type former) | **CLOSED** (`oracleOK_Eq`), both fields |
| `consts` at `Eq.refl` | **closed** (`EqZeroAudit.pt_mem_interp_EqReflType`); level-uniform, `reflSort_eval_eq_zero` is unconditional |
| `consts` at `Eq.rec`, `u.eval ls = 0` | proved (`EqZeroAudit.pt_mem_interp_eqRecType_of_zero`) |
| `consts` at `Eq.rec`, `u.eval ls ≠ 0` | **OPEN**; `•` is *refuted* there, so the value must be the six-layer `mkLam` |
| `rules` (one ι-rule) | open |

**"Hole-free" is not "discharged", and cell-closed is not block-closed.** `OracleOK`'s `type` field
quantifies over *all* `us` of the right length, so `Eq.rec`'s cell is a single statement spanning
both level slices; the `= 0` slice does not close it and no level-uniform value can
(`EqAudit.no_level_uniform_value`). Two of three `consts` cells are closed. `InductOracleOK` at
`eqIndDecl` is **not** closed.

### 18.5 Task 2 also landed: `EqSpec` is **necessary at the recursor cell**

New file: `Lean4Lean/Theory/SetModel/EqRecNecessity.lean` (namespace
**`Lean4Lean.SetModel.EqRecNec`**), imported from `Theory/Equiconsistency.lean` on the same edit.
Per-module build: **1208 jobs**, ✔, 3.2s. `#print axioms` on all 13 declarations: every one
`[propext, Classical.choice, Quot.sound]`. **No `sorryAx`.** No new `sorry`, none traded.

| name (`Lean4Lean.SetModel.EqRecNec.*`) | what |
|---|---|
| `eqTrueFn`, `eqTrueFn_value` | a **constant-`{•}`** `Eq` denotation: three `mkLam` layers, `SetModel.eqFn` with the `if` deleted |
| `sepMot`, `sepW`, `sepMot_value_self`, `sepMot_value_other` | the **separating motive**, two layers, environment-passing (the inner layer reads `a` at index 1 and `x` at index 2) |
| `sepMot_mem_interp_motTyE` | the motive really inhabits `⟦motTyE u v⟧` — two `mkLam_mem_mkForallType_of_dom`s |
| `badTrueM`, `not_eqSpec_badTrueM` | the model, and the check that **what it violates is exactly `EqSpec`**, at the non-reflexive instance only |
| **`not_pt_mem_interp_eqRecType_badTrue`** | **`• ∉ ⟦Eq.rec's type⟧` at `badTrueM`** — so `pt_mem_interp_eqRecType_of_zero`'s hypothesis cannot be dropped |
| `eqSpec_necessary_at_recursor` | packaged: `∃ M, M.κ = κ ∧ M.ls = ls ∧ ¬EqSpec M (.succ .zero) ∧ ¬(• ∈ …)` |
| **`recCell_discriminates`** | the tight bracket: at **one and the same** `κ, ls, L, hle, u := .zero, v := .succ .zero`, the membership **holds** at `preludeWitness` and **fails** at `badTrueM` |

Total ~150 lines. §17.8 item 2 was right about the *shape* (two `mkLam` nests) and wrong about the
*price*: see 18.6.

### 18.6 Where the brief is wrong — Task 2's costing

> "It is reported to need a constant-true `Eq` plus a separating motive — two `mkLam` nests. … the
> expensive control has no precedent in the tree … Price it yourself."

Three corrections, in descending order of how much they would have mis-scoped the block:

1. **The dominant cost is not the two nests — it is that the control cannot live where the slice
   lives.** The separation needs `α` with two distinct elements. At `u.eval ls = 0` (the slice's own
   branch) that is fine, but the *carrier's* level is `v`, and at `v.eval ls = 0` every carrier is a
   subset of `{•}`, so **no** motive separates two of its elements. The control therefore forces
   `v.eval ls = 1` **and** `IsInaccessibleChain n κ` with `0 < n`. That is the first
   chain-dependent hypothesis anywhere in this corner's controls — `EqOracle.lean` §6.4/§6.5 and
   `EqZeroSlice.lean` §5 are all at an arbitrary `κ`. Anyone pricing "two `mkLam` nests" would have
   budgeted zero for this and then discovered mid-file that the statement has to change shape.
2. **"No precedent in the tree" is right about the statement and wrong about the lever.** The
   two-element carrier is `℘{•} ∈ U κ 1` via `SetModel.U_mem_succ`, and
   `PreludeSpec.eqFn_distinct` already uses exactly that lever, for exactly this purpose (to make
   `eqFn`'s `else` branch fire). So the missing thing was not a technique, it was a hundred lines of
   assembly. Pricing it as "expensive because unprecedented" over-charges.
3. **"Expensive" is wrong outright.** ~150 lines, no new infrastructure, no set-theoretic content
   beyond `U_mem_succ` + `mem_UProp_iff`. The reason is that `EqZeroSlice.lean` §§1–4 (the
   `snoc`-ladder, the `OnCtx` ladder, the `IsProp` chain, the four `interp_*_val` equations) are
   **exactly** the lemmas a refutation needs, used in the `.1` direction instead of the `.2`
   direction of the same `mem_interp_forallE_prop_iff`. The forty-lemma telescope that made the
   positive slice expensive is what makes its control cheap. **This generalises**: every future
   `= 0` slice buys its own necessity control at a large discount, so long as the block has a
   carrier at a level where two elements exist.

What I confirm rather than repeat: `PreludeOracle.lean:905`'s parenthetical "(§9)" is a **dangling
cross-reference** — §9 of that file proves `not_mem_interp_zeroOracle_NE_type` (the *empty* oracle
at the *type former*) and nothing about a constant-true `Nonempty` at the recursor. Checked by
reading §9 in full. The `Eq` analogue now exists, so the `Nonempty` one is a transcription rather
than a design problem.

### 18.7 Measured versus read off

**Measured** (instrument run, output in this session):

* per-module `lake build`: 1207 jobs (`EqTypeFormer`), 1208 jobs (`EqRecNecessity`);
* `#print axioms` on all 30 new declarations, addressed **by namespace**
  (`Lean4Lean.SetModel.EqTFAudit.*`, `Lean4Lean.SetModel.EqRecNec.*`), not by filename;
* **forward cone over type AND value with `allowOpaque := true`**, walker copied from
  `scripts/hole-cone.lean`, run out of `/tmp` over 19 seeds (every substantive new declaration).
  **Presence check first, as instructed** — in the measuring environment
  (`EqTypeFormer` + `EqRecNecessity` + `Theory/Typing/ChurchRosser` + `Injectivity` +
  `RigidNodeCircle`):

  | hole | `present` |
  |---|---|
  | `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | **true** |
  | `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | **true** |
  | `Lean4Lean.VEnv.WF.rigidShapeUniqNS` | **true** |
  | `Lean4Lean.VEnv.NormalEq.descend` | **true** |

  Result: **every one of the 19 cones has `bigHoles []` and `sorryAx-carriers []`.** Cone sizes
  1098–7110. So the claim "hole-free" is a measurement, and it is not the vacuous one — the holes
  were reachable in the environment that reported them absent.
* `lean_diagnostic_messages` for both files: zero errors, zero warnings.

**Reasoning, not run** (labelled as such):

* that `hle : eqEnv ≤ envF` is semantically necessary in `oracleOK_Eq`.
  `lean_minimal_hypotheses` says "load-bearing" but its verdict is about the proof *body* naming
  `hle`, not about necessity; the argument is in `EqTypeFormer.lean` §3's note and 18.3 above.
* the ~15-line price of the non-vacuous version of `eqSpec_not_sufficient` (18.2).
* the transfer claim in 18.6 item 3 (every `= 0` slice buys its control cheaply). Untested at
  `iffIndDecl`.

Search-tool provenance: **`lean_local_search` and `lean_hammer_premise` were not used** (reported
broken here — `rg` absent). Every "does X exist / where is X" claim above is backed by `grep` over
the working tree, plus `lean_diagnostic_messages` / `lean_minimal_hypotheses` for the two
measurements that need elaboration. `lean_references` was not needed.

### 18.8 The two infrastructure traps — not exercised, so not confirmed either way

* **`InterpSound.propSound_of_mem_sort` is circular at a slice.** I never reached for it: the
  `¬IsProp` facts came from `SoundInduction.isProp_iff` + an explicit `HasType` derivation
  (`hasType_tf2/tf3`), which is the route `EqZeroSlice.lean` already uses. So the warning cost me
  nothing and I add no evidence for or against it.
* **`hasType_app'` needs `Lean4Lean.liftVar` and `.bvar (i+1)`.** Also not exercised — the `Eq`
  type former's binders are `.sort v`, `.bvar 0`, `.bvar 1`, all typed by bare `.bvar` derivations,
  and the recursor control reuses `EqZeroSlice`'s existing `interp_*_val` equations rather than
  building new applications. Carry the warning forward; nothing here tests it.

### 18.9 What to pick up first

1. **`Eq.rec`'s `≠ 0` slice — the six-layer `mkLam`, and it is now the *only* thing between this
   block and `consts` being closed.** `EqRecNecessity.lean`'s `eqTrueFn` is a worked three-layer
   example of building such a value from `PreludeSpec`'s `mkLam` idiom, and
   `EqTFAudit.eqFn_mem_interp_EqType` is a worked example of landing one in a nested
   `mkForallType`. The two together are the whole recipe; what is new at the recursor is that the
   innermost body must *depend on the minor premise*, which neither of those does.
2. **Then the ι-rule** (`eq_iotaRules_length = 1`). Unchanged in priority from §17.8 item 4.
3. **`iffIndDecl`'s `= 0` slice** — still §17.8 item 1, and 18.6 item 3 now predicts its
   *necessity control* will be cheap once the slice exists. Do the slice first.
4. **The non-vacuous form of `eqSpec_not_sufficient`** (18.2): `eqFn κ i ∪ {∅}`, at arbitrary `κ`.
   Only worth doing if someone challenges the vacuous-`EqSpec` control; it changes no downstream
   statement.
5. **`RegConvE env U (k+1)` / `RegularAtSucc`** — unchanged from §17.8 item 5, still inhabited by
   nothing, still not attacked.

**Do not** re-attack: everything §10.9–§17.8 name, plus — new — **`Eq`'s type-former cell**
(closed, 18.1), **`EqSpec` as a hypothesis for the type-former cell** (refuted, 18.2),
**`EqSpec`'s necessity at the recursor cell** (proved, 18.5), and **the reading that
`PreludeOracle.lean:905`'s "(§9)" points at a proof** (it does not, 18.6).

## 19. Session of 2026-09-02 (twelfth): the `≠ 0` slice is **PROVED** — `Eq.rec`'s `consts` cell is closed at both slices, and `preludeWitness` is **refuted** as a witness for it

Written incrementally, as landed. Files: `Lean4Lean/Theory/SetModel/EqRecLarge.lean` (new, imported
from `Theory/Equiconsistency.lean` on the same edit).

### 19.1 The slice, proved

```lean
theorem EqLargeAudit.eqRecFn_mem_interp_eqRecType
    (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
    (hspec : EqSpec M v) (hn : u.eval M.ls ≠ 0) :
    eqRecFn M.κ (u.eval M.ls) (v.eval M.ls) ∈
      (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅
```

`eqRecFn` is the six-layer `mkLam` `λ α a motive m b h, m`, written in `Definability.lean`'s
environment-passing style (each layer's domain is read out of the valuation, nothing captured). The
proof is **six applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`**, one per binder, and it
went through on the first elaboration — no failed step at the cell itself.

**The single hypothesis is `EqSpec M v`, the same one the `= 0` slice needs**, and it is used in
exactly two places: identifying the motive binder's domain (§19.2) and collapsing `h : Eq α a b` to
`b = a`, `h = •` at the innermost step.

`Above` occurs in no statement in the file. Every positive statement is at an **arbitrary**
`κ : ℕ → V`, an arbitrary `ModelData`, arbitrary `u`, `v`. **No `κ` is chosen anywhere in this
file** — not even in a control (§19.4 gets its control for free from an existing theorem, which is
why).

### 19.2 The one genuinely new piece of infrastructure: `mkForallType_ext`

The brief said "a six-layer `mkLam`" and priced it as six copies of the type-former cell's step.
**That costing is right about five of the six layers and wrong about the third.** The oracle's value
may not call `interp` (circularity), so every layer's domain has to be *written down* and then
matched with `interp`'s by `mkLam_mem_mkForallType_of_dom`'s `hdom : G' ρ' = G ρ` — an **exact set
equality**. Five domains are literals or reads (`U κ nv`, `ρ ‘ 0` twice, `(ρ‘2 ‘ ρ‘1) ‘ •`,
`eqFn κ nv ‘ ρ‘0 ‘ ρ‘1 ‘ ρ‘4`). The **motive** binder's is not: it is
`Π x ∈ α, Π w ∈ ⟦Eq α a x⟧, U κ nu`, a two-layer dependent product.

So the file adds

```lean
theorem mkForallType_ext (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkForallType G' hG' F' hF' ρ' = mkForallType G hG F hF ρ
```

(plus `mkFamUnion_ext`, which it needs) — the `mkForallType` analogue of the existing
`UnitAudit.mkLam_ext`, and the lemma that lets the oracle's own spelling of a *type* be identified
with `interp`'s. `motSet` is that spelling; `motSet_eq_interp_motTyE` is the identification, and it
is where `EqSpec` first enters. **This is reusable and is the thing to pick up for any other
large-eliminator block**: `unitDeclLE` never needed it because `⟦Unit1 → Sort u⟧` is
`U κ n ^ {•}`, a *non*-dependent function space with an existing literal
(`UnitAudit.mkForallType_singleton_const`).

### 19.3 …and the whole `consts` cell at `Eq.rec` is closed, both slices

```lean
theorem EqLargeAudit.oracleOK_EqRec (hle : eqEnv ≤ envF) {c : Name → List VLevel → V}
    (hspec : ∀ w : VLevel, EqSpec (⟨κ, ls, c⟩ : ModelData V) w)
    {o : Name → List VLevel → V} (ho : ∀ us, o ``Eq.rec us = eqRecVal κ ls us) :
    OracleOK L κ ls o c ``Eq.rec ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩
```

`eqRecVal κ ls [u, v] = if u.eval ls = 0 then • else eqRecFn κ (u.eval ls) (v.eval ls)` — the same
level-branching shape `UnitOracleLarge.unitOracleL` uses, forced for the same reason
(`EqAudit.no_level_uniform_value`). Both `OracleOK` fields; `Above` discharged by `Above.pure`
(`oracleOK_of`), so **no chain hypothesis and no chosen `κ`**. `eqIndDecl_recUvars : … = 2` is `rfl`.

**Status of `InductOracleOK` at `eqIndDecl` after this file:**

| obligation | status |
|---|---|
| `consts` at `Eq` (type former) | proved (`EqTFAudit.oracleOK_Eq`, §18) |
| `consts` at `Eq.refl` | proved (`EqZeroAudit.pt_mem_interp_EqReflType`, §17) |
| `consts` at `Eq.rec`, `u.eval ls = 0` | proved (`EqZeroAudit.pt_mem_interp_eqRecType_of_zero`) |
| `consts` at `Eq.rec`, `u.eval ls ≠ 0` | **PROVED here** (`eqRecFn_mem_interp_eqRecType`) |
| `consts` at `Eq.rec`, as one `OracleOK` | **PROVED here** (`oracleOK_EqRec`) |
| `rules` (the one ι-rule) | see §19.6 |

### 19.4 **`preludeWitness` is REFUTED at this cell** — the finding I did not expect

`SetModel.pt` is *literally* `∅` (`Universe.lean:53`), and `preludeWitness`'s `cnst` sends every
name outside `{Eq, Iff, Nonempty}` to `∅`. So its `Eq.rec` entry **is** `•`, and therefore:

```lean
theorem preludeWitness_mem_interp_eqRecType_of_zero (h0 : u.eval ls = 0) : … ∈ …      -- holds
theorem preludeWitness_not_mem_interp_eqRecType (hn : u.eval ls ≠ 0)
    {x : V} (hx : x ∈ U κ (v.eval ls)) : … ∉ …                                        -- FAILS
```

Both machine-checked. So **the corner's shared joint witness cannot discharge `InductOracleOK` at
`eqIndDecl` as it stands** — it is correct on the `Prop` branch and refuted on the other. This was
invisible before the `≠ 0` slice existed, because until now nobody could exhibit a value that *does*
work there, so the natural reading was "the slice is open", not "the witness is wrong".

The fix is known (`eqRecVal`, §19.3) and is not new mathematics. **I did not make it**:
`preludeWitness` lives in `PreludeSpec.lean` and is consumed by `PreludeWitness.lean`,
`EqTypeFormer.lean` §4 and `preludeSpec_satisfiable`; changing its `cnst` is a decision about the
corner's shared witness, not about this slice. Whoever takes it should expect the same gap at
`Iff.rec` and `Nonempty.rec`, for exactly the same reason (`else ∅` is `else •`).

### 19.5 Anti-vacuity, in the form the brief demands

`recCell_discriminates_of_ne`: at **one and the same** `(envF, nv, L, M, u, v)` with `EqSpec M v`,
`u.eval M.ls ≠ 0` and a parameter-space inhabitant, `eqRecFn ∈ ⟦Eq.rec's type⟧` **and**
`• ∉ ⟦Eq.rec's type⟧`. `eqRecFn_ne_pt` then closes the loophole that the two named values might be
the same set. This is `EqRecNec.recCell_discriminates`'s form, not the empty-hypothesis form, so it
does catch a conclusion that holds of everything — which matters here, because
`mkForallType` over an empty domain is `{∅}` and the statement would otherwise be at risk of
degenerating exactly the way §18.2's positive control did.

**Where the brief is wrong about this.** It says "the `≠ 0` side condition needs a **parameter**-space
inhabitant — `EqAudit.pt_not_mem_interp_eqRecType_of_ne` carries `x ∈ U M.κ (v.eval M.ls)`". That
hypothesis belongs to the **exclusion of `•`**, and `eqRecFn_mem_interp_eqRecType` — the slice
itself — carries no such hypothesis and needs none. So the three-point scale
"`iffIndDecl` nothing / `eqIndDecl` a parameter-space inhabitant / `unitDeclLE` a motive-space one"
grades the *negative* controls, not the slices. The slice at `eqIndDecl` costs `EqSpec` and nothing
else.

### 19.6 The ι-rule: shape measured, and **its typing turns out to be free**

`EqAudit.eq_iotaRules_length = 1`. All of the following are `rfl`, guessed-and-checked rather than
read off (`eqRule_lhs_instL`, `eqRule_rhs_instL`, `eqRule_type_instL`, `eq_iotaCtx`,
`eq_iotaCtx_reverse`, `eqRule_uvars`):

* `lhs.instL [u,v] = λ α a motive m, Eq.rec α a motive m a (Eq.refl α a)` — **six** application
  nodes, one of which (`Eq.refl α`) is a proof, so `interp` discards its argument
  (`EqZeroAudit.isProof_reflC1_ctxM` already proves that);
* `rhs.instL [u,v] = λ α a motive m, (λ α a motive m, m) α a motive m` — the η-expansion
  `Decl.lean` insists on, i.e. a **four-fold β-redex**. Reading `iotaLam` alone would miss this;
* `type.instL [u,v] = ∀ α a motive m, motive a (Eq.refl α a)` — `minTyE` one binder deeper;
* `((iotaCtx eqCtor).map (VExpr.instL [u,v])).reverse = EqAudit.ectxN [] u v` **on the nose**, so
  every `OnCtx`/`IsProp`/`interp_*_val` lemma in `EqZeroSlice.lean` applies to the ι-rule unchanged.
  That is worth more than it sounds: it means the rule needs *no new context ladder*.

`eqRuleSort_eval_eq_zero_iff : (imax (succ v) (imax v (imax (motSortE u v) (imax u u)))).eval ls = 0
↔ u.eval ls = 0` — pure level arithmetic, no typing needed, so **the ι-rule has the same two slices
as the recursor** and this is available before any derivation exists.

**And the part I expected to dominate is free.** The saturated recursor spine's typing — six
`hasType_app'` steps each with its own `.inst` equation, exactly the trap §18.8 carries forward —
does not have to be written at all:

```lean
theorem eqRule_WF : VDefEq.WF eqEnv (eqIndDecl.iotaRule 0 0 eqCtor)   -- both sides typed
theorem eqRule_lhs_hasType : eqEnv.HasType 2 [] (…).lhs (…).type
theorem eqRule_rhs_hasType : eqEnv.HasType 2 [] (…).rhs (…).type
```

from `VInductDecl'.iotaRules_WF` (`Theory/Inductive/Lemmas.lean`, general, for every block) applied
to `eqIndDecl.IotaCtx eqE3`, which `VInductDecl'.WF.iotaCtx` produces from three staged
`addConstList`s that are all `rfl` at `VEnv.empty` for this block. Twelve lines, no `VExpr`
arithmetic, and `#print axioms` shows **no `sorryAx`** — so `eqIndDecl_WF` and the general ι
machinery are both hole-free on this path.

**This is the thing to know before attacking the rule, and it was in no handoff.** §17.8 item 4 and
§18.9 item 2 both priced the ι-rule without noticing that `Theory/Inductive/` already types both
sides of it.

### 19.7 What is OPEN, and what I tried

**Open: the ι-rule itself** (`InductOracleOK.rules` at `eqIndDecl`), both slices. What each needs,
now that §19.6 has removed the guesswork:

1. **`= 0` slice.** `DefEqOK` wants ⟦lhs⟧∅ = ⟦rhs⟧∅ and ⟦lhs⟧∅ ∈ ⟦type⟧∅. Both sides are proofs at
   `u.eval ls = 0`, so `interp_lam_proof` gives `pt` twice and the equality is free — *but*
   `interp_lam_proof` needs `L.IsProof M (ectxA [] v) (inner 3-fold lam)`, and `isProof_iff` needs
   the inner lam's `HasType` **at `nv`, instantiated**, plus the *type's own* sort derivation
   (`HasType nv [] (type.instL [u,v]) (.sort (eqRuleSort u v))`). §19.6 supplies the first at
   `uvars = 2` uninstantiated; what is missing is (a) a `HasType.instL`-style transfer to `nv` with
   `[u,v]`, and (b) `.forallEDF` four times for the sort, which needs two `.bvar` lemmas
   `EqOracle.lean` does not have (`hasType_a_ctxN`, `hasType_mot_ctxN`) and two `hasType_app'` steps
   for `motive a (Eq.refl α a)` at `ectxN`. I did **not** attempt (a) — I stopped at the point where
   I had verified §19.6 and judged the remaining budget better spent on the write-up than on a
   half-finished slice. So: **not attempted, not failed.**
   Then `pt ∈ ⟦type⟧∅` is a four-layer `mkForallProp` membership whose innermost step is
   *literally* the one in `pt_mem_interp_eqRecType_of_zero` (`motive_value_mem_UProp` forces
   `m = pt`). Estimate: 60–80 lines, no new mathematics.
2. **`≠ 0` slice.** Four-layer `mkLam` on both sides, plus the computation
   `eqRecFn ‘ α ‘ a ‘ f ‘ m ‘ b ‘ • = m` (the analogue of `UnitAudit.recFnL_beta`; five
   `mkLam_value` steps off the definitions in §3 of the new file) and the four-fold β-redex on the
   right. `UnitOracleLarge.lean` §10 is the template at three binders and three app nodes and runs
   ~100 lines; expect 150–200 here. **Note the model must be the one whose `Eq.rec` entry is
   `eqRecVal`** — at `preludeWitness` the lhs's ⟦·⟧ is not the function (§19.4).

**Open, and I now think it is cheap: `EqSpec`'s necessity for the `≠ 0` slice.** I did *not* build
it, and I want to be explicit about where the obvious route dies:
`EqRecNec.sepMot_mem_interp_motTyE` — the separating motive, the only motive-in-`⟦motTyE⟧` in the
tree — carries `h0 : u.eval M.ls = 0` as a hypothesis, because its fibres land in `U κ 0 = UProp`.
So it **cannot** be reused at `u.eval ls ≠ 0`, and the control needs a fresh motive whose values lie
in `U κ nu` for `nu ≠ 0`. That is where I stopped. `recCell_discriminates_of_ne` (§19.5) covers the
anti-vacuity requirement without it.

**Refuted:** `preludeWitness` as a witness for this cell (§19.4) — machine-checked, both
directions.

### 19.8 Measurements versus readings

**Measured (runs):**

* Per-module `lake build` job counts, every increment: `Lean4Lean.Theory.SetModel.EqRecLarge`
  **1209 jobs**, `Build completed successfully`, zero errors, zero warnings at every one of the
  seven increments. `Lean4Lean.Theory.Equiconsistency` (edited to import the new file)
  **1245 jobs**, `Build completed successfully`.
* `#print axioms` on **all 49 declarations of the new file, by fully-qualified name in
  `Lean4Lean.SetModel.EqLargeAudit`** — every one resolved (no *unknown constant*, the trap §18.7
  flags for `PreludeSpec.*`), and **none depends on `sorryAx`**. The heaviest is
  `[propext, Classical.choice, Quot.sound]`; `eqIndDecl_recUvars` depends on nothing.
* **No new `sorry`, none traded.** The full `Equiconsistency` build reports exactly the five
  pre-existing `declaration uses 'sorry'` warnings (`Inductive/Decl.lean:405`,
  `Typing/Injectivity.lean:261`, `:1046`, `Typing/UniqueTyping.lean:190`,
  `Equiconsistency.lean:56`) — the same five as before this session.
* **Cone measurement, over type *and* value with `allowOpaque := true`**, in an environment
  importing `EqRecLarge` + `ChurchRosser` + `Injectivity` + `UniqueTyping`. Presence check first,
  because §18.7's environment had to be arranged for it:

  | hole | `present` |
  |---|---|
  | `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | **true** |
  | `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | **true** |
  | `Lean4Lean.VEnv.WF.rigidShapeUniqNS` | **true** |
  | `Lean4Lean.VEnv.NormalEq.descend` | **true** |

  All **12** seeded cones: `bigHoles []`, `sorryAx-carriers []`. Cone sizes 696–8313
  (`eqRecFn_mem_interp_eqRecType` 6897, `oracleOK_EqRec` 6943,
  `preludeWitness_mem_interp_eqRecType_of_zero` 8313, the four `rfl` shape lemmas 696–1043).
* Every "does X exist / what is X's shape" claim above is backed by `grep` over the working tree
  plus `lean_run_code` for the six ι-rule shape guesses and the `eqRule_WF` chain (both probed in a
  scratch snippet before being landed). **`lean_local_search` and `lean_hammer_premise` were not
  used** (reported broken here). `lean_references` was not needed.

**Hole-free is not discharged.** Everything above is a *reachability* measurement: it says no
`sorryAx` is in these cones. It does **not** say the `≠ 0` slice is discharged at any concrete
model, and §19.4 is the proof that it is not discharged at the one witness the corner has.
Nothing here goes through `NEAudit.nonempty_propSplit_preludeEnv` (which prints `sorryAx`), so
nothing above is claimed "sorry-free at `preludeEnv`"; the new file's statements are all
parametric in `L : PropSplit envF nv` with `hle : eqEnv ≤ envF`, exactly as `EqZeroSlice.lean`'s.

**Reasoning, not a run** (labelled as such):

* the 60–80 / 150–200 line estimates in §19.7;
* the claim that `Iff.rec` and `Nonempty.rec` have the *same* `preludeWitness` gap as `Eq.rec`
  (§19.4) — it follows from `pt = ∅` and `else ∅`, but I checked neither block's exclusion lemma;
* that `hle : eqEnv ≤ envF` and `hu`/`hv` are *semantically* necessary in
  `eqRecFn_mem_interp_eqRecType`. They are used in the proof body; I did not run
  `lean_minimal_hypotheses`, and §18.7 records that its verdict is about the body anyway;
* that `mkForallType_ext` is what any other large-eliminator block will need (§19.2). Argued from
  `unitDeclLE`'s non-dependent motive space, not tested at `iffIndDecl`.

### 19.9 The two infrastructure traps, and one of them **did** bite

* **`InterpSound.propSound_of_mem_sort` is circular at a slice.** Not exercised, again: every
  `¬IsProp` came from `SoundInduction.isProp_iff` plus an existing `HasType` derivation. Warning
  carried forward, no new evidence.
* **`hasType_app'` needs `Lean4Lean.liftVar`, an `omega`, and `.bvar (i+1)`.** *This one is real and
  I confirmed it obliquely*: it is exactly the cost §19.6 shows you do not have to pay, because
  `VInductDecl'.iotaRules_WF` already types the spine. The recipe's difficulty is why the shortcut
  matters. I never wrote a `hasType_app'` call in this session.
* **New trap, cost me one build:** `VExpr.instL` takes the level list **first**
  (`instL : List VLevel → VExpr → VExpr`), so `e.instL us` works by generalized field notation but
  `(VExpr.instL · us)` as a `List.map` argument does **not** — it type-errors with
  "`[u, v]` … expected to have type `VExpr`". Write `(VExpr.instL us)`.
* **`Above` appears in no statement in the new file**, and no `κ` is chosen anywhere in it — not
  even in a control, because the control (§19.5) borrows
  `EqAudit.pt_not_mem_interp_eqRecType_of_ne`, which is at an arbitrary `κ` with an explicit
  parameter-space inhabitant instead. So the `Above`-is-free-at-a-false-antecedent hazard does not
  arise here.

### 19.10 Where the brief was wrong

Three places, in decreasing importance.

1. **"`preludeWitness`'s `Eq` entry **is** `eqFn`, so the corner already pays the hypothesis."**
   True at `Eq`, and it reads as though the witness is in good shape at this block. It is **not**:
   its `Eq.rec` entry is `•` and the `≠ 0` slice refutes it (§19.4). The brief's framing pointed at
   the slice as the only obstacle; the slice is now closed and the *witness* is the obstacle.
2. **"the `≠ 0` side condition needs a **parameter**-space inhabitant … the three-point scale
   across blocks: `iffIndDecl` nothing, `eqIndDecl` a parameter-space inhabitant, `unitDeclLE` a
   motive-space one."** That scale grades the **negative controls** (`•` is excluded), not the
   slices. `eqRecFn_mem_interp_eqRecType` needs no inhabitant of anything: its only hypothesis is
   `EqSpec M v` (§19.5).
3. **"a six-layer `mkLam` — its own handoff says take the slice first."** Right about the order and
   right that it is six layers, but the costing "six copies of the type-former cell's step" is wrong
   at one layer: the **motive** binder's domain is a dependent product that the oracle has to spell
   out itself, and matching it needs a new combinator (`mkForallType_ext`, §19.2). Five layers were
   the predicted price; the sixth was a missing lemma. Symmetrically, the brief (and §17.8, §18.9)
   over-priced the ι-rule: its typing is free (§19.6).

### 19.11 What to pick up first

1. **The ι-rule's `= 0` slice**, with §19.6 in hand — `eqRule_lhs_hasType` / `eqRule_rhs_hasType`
   are landed and hole-free; what is missing is the `instL` transfer to `nv` and the four-fold
   `.forallEDF` sort derivation. This closes half of the last obligation at `eqIndDecl`.
2. **The ι-rule's `≠ 0` slice.** `UnitOracleLarge.lean` §10 is the template; `eqRecFn`'s five
   `mkLam_value` β-steps are the new content.
3. **Decide the `preludeWitness` question** (§19.4). Either extend its `cnst` with `eqRecVal` (and
   the `Iff.rec` / `Nonempty.rec` analogues), or introduce a separate oracle for the `.induct`
   steps. `oracleOK_EqRec` is already stated so that either choice works: the oracle `o` is a
   parameter pinned by `ho`, independent of the ambient `c`. **This is a shared-witness decision,
   not a slice — it needs the coordinator, not a stream.**
4. **`iffIndDecl`'s `= 0` slice** — unchanged from §18.9 item 3, and §18.6 item 3's prediction is
   still untested.
5. **`EqSpec`'s necessity at the `≠ 0` slice** (§19.7) — only worth doing if challenged; needs a
   motive at a non-`Prop` universe, which is the one thing `EqRecNec.sepMot` cannot give.

**Do not** re-attack: everything §10.9–§18.9 name, plus — new — **`Eq.rec`'s `≠ 0` slice**
(proved), **the `Eq.rec` `consts` cell as an `OracleOK`** (proved, both slices), **`preludeWitness`
at the `Eq.rec` cell** (refuted), and **hand-typing the ι-rule's recursor spine** (unnecessary —
§19.6).

### 19.12 **Repo hazard — needs one `git add`**

While this session was running, another stream's commit (`b57d2e0`) swept up my edit to
`Theory/Equiconsistency.lean`, so **`HEAD` now imports
`Lean4Lean.Theory.SetModel.EqRecLarge` while `EqRecLarge.lean` itself is still untracked**
(`git status`: `?? Lean4Lean/Theory/SetModel/EqRecLarge.lean`). A fresh checkout of `HEAD` will not
build. I did no git operations (not mine to do): **the new file needs adding and committing.**
Verified: `git show HEAD:Lean4Lean/Theory/Equiconsistency.lean | grep -c EqRecLarge` = 1.

### 19.13 Files touched

* `Lean4Lean/Theory/SetModel/EqRecLarge.lean` — **new**, 686 lines, no `sorry` (49 `#print axioms` lines, all resolving).
* `Lean4Lean/Theory/Equiconsistency.lean` — one import line, added on the same edit as the file
  (already in `HEAD`, see §19.12).
* `docs/handoff-setmodel.md` — this section.

## 20. Session of 2026-09-02 (thirteenth): the shared witness priced — **the repair is two cells, not three**, and its dominant cost is an import cycle, not a re-proof count

Brief: price the `preludeWitness` fix that §19 declined to take; measure whether the same gap
hits `Iff.rec` and `Nonempty.rec`; find out whether anything *depends* on the recursor entries
being `•`.

**All of it landed in one new file, `Lean4Lean/Theory/SetModel/PreludeRecGap.lean`** (543 lines,
namespace `Lean4Lean.SetModel.RecGap`), imported from `Theory/Equiconsistency.lean` on the same
edit. No existing file was changed except that import line. `PreludeSpec.lean` is **untouched**.

### 20.1 Where the brief is wrong

Three places, and the third is the one that changes what to do next.

1. **"the fix is one edit for three cells rather than one" — no, two cells.**
   `Nonempty.rec` is not affected and cannot be. `NEAudit.ne_isLE : nonemptyIndDecl.isLE = false`
   and `NEAudit.ne_elimLvl : … = .zero` are already `rfl` in the tree: a small eliminator has no
   elimination universe, so `Nonempty.rec`'s type is a proposition at *every* instantiation and
   `•` is the **correct** value there — `NEAudit.pt_mem_interp_NE_recType` proves it, and
   `RecGap.preludeWitness_mem_interp_neRecType` restates it at the shared witness. The gap is a
   consequence of `isLE = true`, which holds at `eqIndDecl` and `iffIndDecl` and nowhere else in
   the prelude.

2. **"how many existing results about `preludeWitness` would need re-proof" is the wrong cost
   axis.** The re-proof count is *small* (§20.4: four statements refuted or removed, one proof
   needing one extra rewrite, everything else verbatim — measured by running it). The cost that
   actually blocks the edit is an **import cycle**, and no re-proof count would have surfaced it:
   `eqRecFn` is defined in `EqRecLarge.lean`, seven files **downstream** of `PreludeSpec.lean`
   (`PreludeSpec ← PreludeOracle ← IffOracle ← EqOracle ← EqZeroSlice ← EqTypeFormer ←
   EqRecNecessity ← EqRecLarge`, read off `grep ^import`). Putting `eqRecVal` into
   `preludeWitness` requires *relocating* the six-layer `mkLam` nest (`EqLargeAudit.motSet`,
   `lamH`, `lamB`, `lamM`, `lamF`, `lamA`, `eqRecFn`, `eqRecVal` and `EqRecLarge` §2's three
   definability lemmas) up into `PreludeSpec.lean` first. That relocation is *mechanical* — those
   definitions use only `mkLam`, `mkForallType`, their `_definable` lemmas (`Definability.lean`)
   and `eqFn` (`PreludeSpec.lean` itself), all of which `PreludeSpec.lean` already has — but it is
   a relocation across eight modules, and it also breaks the `#print axioms` block at the bottom
   of `EqRecLarge.lean` (nine names move out of `EqLargeAudit`). **Reasoning, not a run**: I did
   not perform the relocation, so "mechanical" is an argument from the import graph and the
   definitions' dependency sets, not a build.

3. **The three-point scale grades the negative controls, not the obligations** — the brief says so
   itself and then asks for it applied to §4.3's `OracleOK`. It does not apply there.
   `oracleOK_EqRec_preludeWitnessR` is a *positive* obligation, and the honest statement about it
   is the one in §20.6: hole-free and `sorryAx`-free, at an arbitrary `κ`, with `Above` discharged
   by `Above.pure`, and **not discharged** as part of `InductOracleOK` because the `Eq.refl` and
   type-former cells and the `rules` field are separate statements. The scale applies to
   `RecGap.eqRec_arm_ne_empty` and to §1's refutation.

### 20.2 PROVED — `Iff.rec` is refuted at the shared witness (the flagged item, now a run)

`RecGap.preludeWitness_not_mem_interp_iffRecType`: at `u.eval ls ≠ 0`,
`(preludeWitness κ ls).cnst ``Iff.rec [u] ∉ ⟦(iffIndDecl.recType 0).instL [u]⟧ ∅`.

Cost: **one rewrite.** `IffAudit.pt_not_mem_interp_iffRecType_of_ne` already existed and — unlike
its `Eq` and `Unit` counterparts — carries **no** hypothesis about an inhabitant of any parameter
space, because `Iff`'s outermost recursor binder is a parameter over `Prop` and `∅ ∈ U κ 0` at
every `κ`. So the `Iff.rec` refutation is strictly *cheaper* than §19's `Eq.rec` one. This
upgrades `NEAudit.preludeWitness_iffRec_empty`, whose own docstring said "*a fact about the
assignment, not yet a refutation of `InductOracleOK` at those blocks*".

### 20.3 REFUTED — the `Nonempty.rec` half of the brief's question

`RecGap.preludeWitness_mem_interp_neRecType`: `•` **is** in `⟦Nonempty.rec's type⟧` at every `u`,
no branch, no side condition. So the shared witness is already right at that cell.

*Where the anti-vacuity control stands there, and it is not good.* The
`EqRecNec.recCell_discriminates` form cannot be had at `Nonempty.rec` as "a bad *value*": the type
is a proposition, so `mem_interp_forallE_prop_iff` makes every member equal `•` and excluding any
`w ≠ •` is free. The informative control has to vary the **model**, and at that block the control
is **prose**: `PreludeOracle.lean:905` asserts "a constant-true `Nonempty` satisfies the
constructor and fails here", and the machine-checked analogue of
`EqRecNec.not_pt_mem_interp_eqRecType_badTrue` at `nonemptyIndDecl` **does not exist**. What does
exist as a run is the faithfulness the cell consumes: `NEAudit.nonemptyFn_zero_empty` and
`NEAudit.nonemptyFn_zero_true`. Recording this as an open control, not claiming it.

### 20.4 MEASURED — the re-proof census, run rather than estimated

`RecGap.preludeWitnessR` is `preludeWitness` with one extra arm,
`else if n = ``Eq.rec then EqLargeAudit.eqRecVal κ ls us`. The brief's guessed shape
(`eqRecVal κ ls [u,v] = if u.eval ls = 0 then • else eqRecFn …`) is right. Each row below is an
existing result restated at `preludeWitnessR` with the **same proof term**; "verbatim" means the
file compiles, not that it looks similar.

| existing result | file | verdict |
|---|---|---|
| `SetModel.preludeWitness_eq` / `_iff` / `_nonempty` | `PreludeSpec` | verbatim (×3) |
| `SetModel.preludeSpec_satisfiable` | `PreludeSpec` | verbatim |
| `EqTFAudit.preludeWitness_cnst_eq` | `EqTypeFormer` | verbatim, **still `rfl`** |
| `EqTFAudit.mem_interp_EqType_preludeWitness`, `oracleOK_Eq` | `EqTypeFormer` | verbatim (`RecGap.mem_interp_EqType_preludeWitnessR`, `oracleOK_Eq_preludeWitnessR`) |
| `EqTFAudit.preludeWitness_congr_Eq` | `EqTypeFormer` | **DOES NOT transfer** — `(kernel) deterministic timeout`; one line rewritten (§20.4a) |
| `NEAudit.neOracle_NE` / `_intro` / `_rec` | `PreludeOracle` | `simp` proofs need no change |
| `EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero` | `EqRecLarge` | statement survives, **one extra rewrite** (`RecGap.preludeWitnessR_cnst_eqRec_zero`) |
| `NEAudit.preludeWitness_eqRec_empty` | `PreludeOracle` | **REFUTED** |
| `EqLargeAudit.preludeWitness_cnst_eqRec` | `EqRecLarge` | **REFUTED** |
| `NEAudit.neOracle_eq_empty_of_not_mem` | `PreludeOracle` | **REFUTED** — one extra hypothesis (§20.5) |
| `EqLargeAudit.preludeWitness_not_mem_interp_eqRecType` | `EqRecLarge` | **REMOVED, not repaired** |

**So: 4 statements refuted or removed, 2 proofs needing repair (one an extra rewrite, one a kernel timeout), everything else verbatim.**
Not one of the three `*Spec` witnesses gets harder, and none gets easier — they read `M.cnst` only
at `Eq`, `Iff`, `Nonempty`, so an arm added *after* those three is invisible to them. The one
thing that could plausibly have broken did not: `preludeWitness_cnst_eq` is `rfl` at
`preludeWitness` and `RecGap.preludeWitnessR_cnst_eq` is **still `rfl`**, which matters because
`EqTFAudit.eqSpec_not_sufficient` shows the type-former cell needs the value's *identity*, not
just its applied values.

#### 20.4a The one row that did NOT transfer — and I only found it because I ran it

I first wrote this census listing `EqTFAudit.preludeWitness_congr_Eq` as "transfers through
`_cnst_eq`". **That was wrong**, and I had already written it into this handoff before compiling
it. At `preludeWitnessR` its proof

```lean
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitness_cnst_eq, preludeWitness_cnst_eq, VLevel.equiv_def.mp h ls]
  · rfl
```

fails at the **last `rfl`** with `(kernel) deterministic timeout` — and note *which* stage: the
declaration **elaborates**, `#print axioms` reports it clean, and the kernel then rejects it. An
elaboration-only check would have passed it. The degenerate branch (`us` of length ≥ 2, both sides
`∅`) is the culprit: closing it by `rfl` asks the kernel to whnf the whole `if`-cascade including
the new arm's body, which contains `eqRecFn`'s six-layer `mkLam` nest with its `definability`
proofs. The first `rfl` (both lists empty) is **fine** — measured, in the sense that the repaired
proof leaves it untouched and compiles.

The fix is two lines: name the `Eq` arm once by `simp`
(`RecGap.preludeWitnessR_cnst_Eq_arm`) and close the degenerate branch by `rw` on it, so `rfl`
never sees the cascade. `RecGap.preludeWitnessR_cnst_eq` stays `rfl` — the difference is that it
is at `us = [w]`, where the arm fires and the cascade is not traversed.

**This is the sharpest single number in the costing:** the relocation of §20.1 item 2 will make the
`Eq.rec` arm's body a *local* definition of `PreludeSpec.lean`, and every `rfl` in that file and
downstream that whnfs `preludeWitness.cnst` at a non-`[w]` level list is a candidate for the same
kernel timeout. `NEAudit.neOracle_NE` / `_intro` / `_rec` are `simp`, not `rfl`, so they are safe;
`EqTFAudit.preludeWitness_cnst_eq` is `rfl` at `[w]`, so it is safe; `preludeWitness_congr_Eq` is
the one that is not, and there is exactly one of it.

**The last row is a difference in kind, not degree.** A costing that lists
`preludeWitness_not_mem_interp_eqRecType` as "needs re-proof" is wrong: after the repair that
statement is **false**. What survives is `EqAudit.pt_not_mem_interp_eqRecType_of_ne`, a statement
about the value `•`, which is what the refutation was really about and is already in the tree.

**The payoff, and it is the deliverable:** `RecGap.oracleOK_EqRec_preludeWitnessR` is
`OracleOK L κ ls (preludeWitnessR κ ls).cnst (preludeWitnessR κ ls).cnst ``Eq.rec
⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩` — **one assignment**, no side oracle parameter, no
chain hypothesis, no chosen `κ`. `EqLargeAudit.oracleOK_EqRec` needed two assignments precisely
because `preludeWitness` could not supply the second; at the repaired witness `ho` is `rfl`-adjacent
(`RecGap.preludeWitnessR_cnst_eqRec`, by `simp`) and `EqSpec` is §20.4's first row.

**The discriminating control, in the form the trap list demands** and now at the *actual* shared
witness rather than an abstract value: `RecGap.repair_discriminates` — one `L`, one
`M = preludeWitnessR κ ls`, one `(u, v)`, **one interpretation** — the repaired entry is in it and
`preludeWitness`'s entry (`•`) is not; `RecGap.repair_changes_the_value` shows the two entries are
different sets. Both halves are at the *same* `interp (preludeWitnessR κ ls) …`, deliberately:
`interp` at the two witnesses is *extensionally* the same (`Eq.rec`'s type mentions `Eq` and
`Eq.refl`, not `Eq.rec`, and the two agree there) but not `rfl`-equal, and no `interp`
constant-congruence lemma exists to bridge them. Where each hypothesis goes is unchanged from
`EqRecLarge` §7: the *positive* half needs no parameter-space inhabitant, the **exclusion** needs
`hx`, and `hx` is a hypothesis *about the given* `κ`, not a construction of one.

### 20.5 The answer to "is there a reason it was `else ∅`" — two parts, pointing opposite ways

**Yes, at `Nonempty.rec`, and it is load-bearing.** `NEAudit.oracleOK_NE_rec` and
`NEAudit.mem_interp_consts_NE` both rewrite with `NEAudit.neOracle_rec : … recN us = •` and then
apply `pt_mem_interp_NE_recType`. That is a real dependency, and it is the one `.induct` step of
the prelude discharged today. It is **not a conflict** — it is a constraint: the fallback must
stay `∅` at `Nonempty.rec`, and both cells the repair touches are at other names.

**And one place depends on the *fallback's shape*:** `NEAudit.neOracle_eq_empty_of_not_mem`
(`m ≠ Eq → m ≠ Iff → m ≠ Nonempty → neOracle κ ls m us = ∅`) is **refuted** by the repair at
`m := ``Eq.rec``. Its only consumer is `NEAudit.cnstOf_preludeTail`, and all three of
`RecGap.preludeWitnessR_cnst_empty_of_not_mem` (repaired shape, one extra hypothesis
`m ≠ ``Eq.rec``), `RecGap.eqRec_arm_ne_empty` (the extra hypothesis is **necessary**, not
defensive — without it the statement is false, at `u.eval ls ≠ 0` and a `κ` with an inhabited
`U κ (v.eval ls)`) and `RecGap.eqRec_mem_eqIndDecl_allNames` (the consumer **can** supply it,
because `Eq.rec ∈ eqIndDecl.allNames`) are proved. So: **a cheap extension, not a conflict** —
one extra hypothesis and one extra line in `cnstOf_preludeTail`.

Note `neOracle` is `(preludeWitness κ ls).cnst` *definitionally* and `NEAudit.neM_eq` is `rfl`, so
the repair is not optional-per-file: repairing `preludeWitness` repairs the prelude's oracle too,
which is exactly why it is a shared-witness decision.

### 20.6 What is NOT discharged — hole-free is not discharged

Measured with a cone over **type and value**, `allowOpaque := true`, in an environment importing
`PreludeRecGap` plus `Theory.Typing.{AppCodType0, Injectivity, UniqueTyping, ChurchRosser}`.
**All four big holes `present = true`** (`IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
`IsDefEqU.weakN_iff`, `NormalEq.descend`) — checked, because `descend` reads absent without
`ChurchRosser` and every cone then looks clean. Both controls fire (`piInv_axiom`: cone 3539,
2 holes, `sorryAx true`; `WF.sortUniq'`: cone 3404, 1 hole, `sorryAx true`). **All 27 seeds:
0 holes, `sorryAx false`.** `#print axioms` by namespace on all 24 `RecGap.*` theorems:
`[propext, Classical.choice, Quot.sound]` only — no new `sorry`, none traded, no frozen-axiom
dependency.

Hole-free ≠ discharged. Still open, and none of it is claimed here:

* **`Iff.rec` has no value.** `iffRecFn` does not exist anywhere (`grep` over
  `Lean4Lean/**.lean`; `lean_local_search` and `lean_hammer_premise` are broken in this
  environment, `lean_references` works). §1 is a **negation**, and a negation is free if the
  interpretation is empty. At `Eq.rec` that worry is answered — `eqRecFn_mem_interp_eqRecType`
  exhibits a member, so the gap is provably *repairable*. At `Iff.rec` nothing is exhibited, so §1
  leaves open which of two things holds: the cell is satisfiable by an unwritten `iffRecFn`, or
  `⟦Iff.rec's type⟧` is **empty** at `u.eval ls ≠ 0` and the block's obligation is unsatisfiable.
  Either way `preludeWitness` fails it. **This is the sharpest open question in the corner.**
* `InductOracleOK` at `eqIndDecl` is still not assembled: §20.4 closes the `Eq.rec` `consts` cell
  at one witness, `EqTFAudit.oracleOK_Eq` the type-former cell, `EqZeroAudit.pt_mem_interp_EqReflType`
  the `Eq.refl` cell — the **`rules` field** (the ι-rule, whose typing `EqRecLarge` §10.1 shows is
  free) is not done, and nothing has been composed.
* `NEAudit.nonempty_propSplit_preludeEnv` prints `sorryAx` via route A, so nothing above is called
  "sorry-free at `preludeEnv`" through it. Everything above is parametric in `L : PropSplit envF nv`.
* The relocation of §20.1 item 2 is unperformed.

### 20.7 What I tried that failed, and the step it failed at

* `simp [eqIndDecl, VInductDecl'.allNames, VInductDecl'.allConsts, VInductDecl'.typeConsts,
  VInductDecl'.recConsts]` for `Eq.rec ∈ eqIndDecl.allNames` — **failed at the residual goal**
  `` `Eq.rec = Lean.mkRecName `Eq ``, which `simp` will not close (it is `rfl` but not a
  simp-normalisable equation). Fix: `simp only [allNames, allConsts, recConsts, List.map_append,
  List.mem_append]; right; simp [eqIndDecl]; rfl`. Same at `Iff`.
* `RecGap.repair_changes_the_value` — **failed at elaboration** with `Unknown identifier L`:
  `include hu hv hle in` does not pull in the explicit `L`, whose statement does not mention it.
  Fix: `include L hu hv hle in`, exactly as `EqLargeAudit.eqRecFn_ne_pt` already does. Worth
  recording because it is the third time this file family has hit it.
* `EqTFAudit.preludeWitness_congr_Eq`'s proof, verbatim — **failed at the KERNEL**, not at
  elaboration: `(kernel) deterministic timeout` on the last `rfl`. See §20.4a; this is the one
  place where my own read-off costing was refuted by a run, and the run is the reason the census
  above says two repairs rather than one.
* Stating `repair_discriminates` with the two memberships at `interp (preludeWitness κ ls)` and
  `interp (preludeWitnessR κ ls)` respectively — **not attempted past the design step**: it needs
  an `interp` congruence in the constant assignment, which does not exist. Stated at one
  interpretation instead (see §20.4).

### 20.8 What to pick up first

1. **Build `iffRecFn`** and its `Iff.rec` arm. It settles §20.6's sharpest open question, it is the
   second of the two cells, and the scaffolding is all present: five `mkLam` layers (not six),
   both parameters over `UProp` rather than `U κ n`, `iffIndDecl.recUvars = 1` so the `if` keys on
   a one-element `match`, no index (`NEAudit.iff_indices = []`) so the motive's domain is a
   *single* `mkForallType`, the `≠ 0` exclusion already free, the level-branch obstruction already
   proved. **The one genuinely new cost**: `IffAudit.minTyI` is
   `∀ (mp : a → b), (b → a) → motive (Iff.intro a b mp mpr)` — two nested function spaces and an
   application of the **constructor** inside the motive's argument, where `Eq`'s minor premise had
   `Eq.refl` which `interp` discards as a proof. There is no counterpart to that step in
   `EqRecLarge.lean`.
2. **Then take the relocation** (§20.1 item 2) and the repair, in one edit, at both arms. Doing it
   before step 1 lands a half-repaired witness that §1 still refutes.
3. `eqIndDecl`'s `rules` field, from `EqLargeAudit.eqRule_WF` / `eqRule_lhs_hasType`.
4. The machine-checked bad-model control at `Nonempty.rec` (§20.3), if the `Nonempty` block's cell
   is ever quoted as more than "correct by `isLE = false`".

### 20.9 Files touched this session

* `Lean4Lean/Theory/SetModel/PreludeRecGap.lean` — **new**, 543 lines, no `sorry`
  (24 `#print axioms` lines, all resolving, all `Lean4Lean.SetModel.RecGap.*`).
* `Lean4Lean/Theory/Equiconsistency.lean` — one import line, added on the same edit as the file.
* `docs/handoff-setmodel.md` — this section.

Per-module `lake build` job counts: baseline `EqRecLarge` + `PreludeOracle` **1209 jobs**, exit 0;
with `PreludeRecGap` **1210 jobs**, exit 0 (the new module elaborates in ~2 s);
`lake build Lean4Lean.Theory.Equiconsistency` **1246 jobs**, exit 0, validating the import line
(the five `declaration uses \`sorry\`` warnings are the pre-existing ones: `Inductive/Decl.lean:405`,
`Typing/Injectivity.lean:261` and `:1046`, `Typing/UniqueTyping.lean:190`, and
`Equiconsistency.lean:57` — the main `↔`). No full
`lake build`, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`, no
`lean_build` MCP call.

## 21. Session of 2026-09-02 (fourteenth): the sharpest open question, **answered affirmatively** — `Iff.rec`'s cell is SATISFIABLE, and *both* its slices are now closed

Brief: build `iffRecFn`, or show the `Iff.rec` cell is unsatisfiable. §20.6 called this the sharpest
open question in the corner, because `RecGap.preludeWitness_not_mem_interp_iffRecType` is a
**negation** and a negation is free if `⟦Iff.rec's type⟧` is empty at `u.eval ls ≠ 0`.

**Answer: SATISFIABLE.** `IffLargeAudit.iffRecFn_mem_interp_iffRecType` exhibits a member. So §1 of
`PreludeRecGap.lean` is a genuine refutation of the shared witness, not a free negation, and the gap
is provably *repairable*. All of it landed in one new file,
`Lean4Lean/Theory/SetModel/IffRecLarge.lean` (1154 lines, namespace `Lean4Lean.SetModel.IffLargeAudit`,
86 theorems, no `sorry`), imported from `Theory/Equiconsistency.lean` on the same edit. No existing
file was changed except that import line. `PreludeSpec.lean` is **untouched**.

**And the deliverable is larger than the brief asked for.** With the `≠ 0` machinery in place the
`= 0` slice — `IffAudit` §7's fourth table row, recorded there as OPEN — came out in seven short
lemmas plus twenty-five lines, so what landed is the **whole `Iff.rec` `consts` cell**
(`oracleOK_IffRec`, both level slices, one `OracleOK`), plus the **joint** repair of the shared
witness at both `Eq.rec` and `Iff.rec` (`preludeWitnessRR`).

### 21.1 The value, stated

`iffRecFn κ nu = λ a b motive min h, (min ‘ •) ‘ •` — five `mkLam` layers, environment-passing
style, at the innermost valuation `snoc⁵ ∅ a b f min h` reading `0,1,2,3,4`. The body is
`(ρ ‘ 3) ‘ • ‘ •`: the minor premise **applied to two points**, where `Eq.rec`'s body was the minor
premise itself. The two points are the denotations of `Iff.intro`'s fields `mp : a → b` and
`mpr : b → a`, both proofs.

Why it is legal: `h ∈ ⟦Iff a b⟧` forces `a = b` (by `IffSpec`) and `h = •`; at `a = b` both field
spaces are `⟦a → a⟧`, and a proposition is a subset of `{•}`, so `•` inhabits each; the minor
premise's own type then *is* `f ‘ •`, which is `f ‘ h`.

### 21.2 Where the brief is wrong

Four places.

1. **The framing was binary and under-scoped.** "Build `iffRecFn`, or show the cell is
   unsatisfiable" left out the object that was actually reachable: the `= 0` slice. `IffOracle.lean`
   §7 lists `• ∈ ⟦Iff.rec's type⟧` at `u.eval = 0` as OPEN *and predicts in prose that it needs
   `iffFn`'s faithfulness in both directions, i.e. the model-side shadow of `propext`*. That
   prediction is **refuted, measured**: `Lean4Lean.SetModel.propext_of_mem_UProp` is **not in the
   cone** of `pt_mem_interp_iffRecType_of_zero` (checked with the type-and-value cone,
   `allowOpaque := true`). `EqZeroSlice.lean` §6's counter-costing is confirmed, for the reason it
   gave. So the honest deliverable is a whole cell, and the brief's cost axis (one slice) would have
   stopped a stream one lemma short of it.
2. **"One genuinely new cost: two nested function spaces and a constructor application inside the
   motive's argument, with no counterpart in the `Eq` work" — half right, and the half that is wrong
   is the one it emphasised.** The *constructor application* has an exact counterpart:
   `EqZeroAudit.isProof_reflC1_ctxM` discards `Eq.refl α` for precisely the same reason
   (`Lean.Nat.imax _ 0 = 0`), and `IffLargeAudit.isProof_introC3` is its twin — three lemmas, no new
   mathematics. What has no counterpart is that the two field spaces are **propositional**: their
   codomains are `Prop`, so `interp` takes the *impredicative* `mkForallProp` branch at each, which
   needed a genuinely new combinator (`mkForallProp_ext`, the analogue of
   `EqLargeAudit.mkForallType_ext`) and made the minor premise's domain a **four**-`_ext` match
   where `Eq`'s motive was two. That is the new cost, and it is a `mkForallProp` cost, not a
   constructor cost.
3. **A cost the brief did not price at all, and it is where I lost the most time.**
   `IffAudit.hasType_introAp_ctxQ` builds the constructor's saturated application as one four-fold
   `.appDF` chain, so the **intermediate types never appear** — and `interp`'s `app` clause tests
   exactly those. `trace_state` prints them as unreduced `.inst` chains
   (`(…forallE…).inst (.bvar 4) (0+1)).inst (.bvar 3)`), which is not an answer. I had to
   `deriving instance Repr for VExpr` in a scratch file and `#eval` the chain to get
   `Iff.intro a b mp : ∀ (_ : b → a), Iff a b`, i.e.
   `.forallE (.forallE (.bvar 3) (.bvar 5)) (iffAp (.bvar 5) (.bvar 4))` at `ictxQ`. **Measured, not
   read off**; no hover, reference search, or reading of `IffOracle.lean` would have produced it.
4. **`EqZeroSlice.lean` §6's "inhabitation is `pt_mem_mkForallProp_self` below and costs nothing"
   is right about the fact and wrong about the lemma.** That lemma's `G` and `F` are *constant*
   functions (`fun _ ↦ p`, `fun _ _ ↦ p`), but the oracle must read its domains out of the valuation
   (`Definability.lean`'s "read the environment, do not capture"), so `G ρ = ρ ‘ i`. It does not
   apply. Measured: `pt_mem_mkForallProp_self` is **not** in my cone. Replaced by two four-line
   lemmas, `pt_mem_impSet01` / `pt_mem_impSet10`.

Where the brief is **right**, and confirmed by running: 5 layers not 6; no index, so the motive's
domain is a single `mkForallType` (`NEAudit.iff_indices = []`); both parameters over `UProp` (they
are over `U κ 0`, and `U_zero` is `rfl`, so the two spellings are interchangeable at no cost);
`iffIndDecl.recUvars = 1`, so `eqRecVal`'s two-element `match` becomes a one-element one
(`iffRecVal`); the `≠ 0` exclusion is free; the level-branch obstruction is already proved. And
"repairing only the `Eq.rec` arm lands a witness the `Iff.rec` refutation still kills" — right, which
is why §21.5 lands both arms and not one.

### 21.3 PROVED

| result | statement |
|---|---|
| `iffRecFn_mem_interp_iffRecType` | **the `≠ 0` slice**: `iffRecFn M.κ (u.eval M.ls) ∈ ⟦(iffIndDecl.recType 0).instL [u]⟧ ∅` at `u.eval M.ls ≠ 0`, from `IffSpec M` alone |
| `pt_mem_interp_iffRecType_of_zero` | **the `= 0` slice** — `IffAudit` §7's fourth row, CLOSED, from `IffSpec M` alone, **no model-side `propext`** |
| `oracleOK_IffRec` | **the whole `consts` cell at `Iff.rec`**, both slices, one `OracleOK`, arbitrary `κ`, no chain hypothesis |
| `iffRecCell_discriminates`, `iffRecFn_ne_pt` | the anti-vacuity controls, in the `RecGap.repair_discriminates` form |
| `mkForallProp_ext` | the missing combinator (the `mkForallType_ext` analogue) |
| `isProof_introC3` + `hasType_introC3`/`Ty` | `Iff.intro a b mp` **is a proof**, at every level valuation |
| `impSet01_eq_interp_mpTy`, `impSet10_eq_interp_mprTy` | the two field spaces, matched to `interp` — used by **both** slices |
| `minSet_eq_interp_minTyI`, `motSetI_eq_interp_motTyI` | the two domains the oracle spells for itself |
| `preludeWitnessRR` + 14 theorems | the **joint** repair (§21.5) |

`interp_iffAp_bvars`, `interp_majTyI_val`, `interp_resI_val`, `interp_minBody_val` are the four
interpretation values at the closed context; the `snoc` reads are `EqZeroAudit`'s `r2_*`–`r5_*`
**instantiated verbatim** — `Iff.rec`'s five-entry tower `a,b,f,min,h` sits at the same indices as
`Eq.rec`'s first five, so no new ladder was needed. That is the single cheapest reuse in the file.

### 21.4 The `= 0` slice, and why it is not free the way `Nonempty`'s was

At `u.eval = 0` the minor premise is **itself** a proposition (`minSortI u` evaluates to `u.eval`),
so `interp` takes the impredicative branch there too and `minSet` does **not** apply — `minSet` is
`≠ 0`-only. The `= 0` slice therefore goes through `mem_interp_forallE_prop_iff` five times and then
uses the two field-space matchings (§21.3) to extract `• ∈ f ‘ •` from the minor premise. Seven new
`isProp_*_of_zero` lemmas, all one-liners off `IffAudit`'s `sort*_eval_eq_zero_iff`.

### 21.5 The joint repair — both arms, one witness

`RecGap.preludeWitnessR` repairs only `Eq.rec`, and `RecGap.preludeWitness_not_mem_interp_iffRecType`
still refutes it (now that §21.3 shows that theorem is not vacuous, this is a real objection, not a
bookkeeping one). `IffLargeAudit.preludeWitnessRR` adds the fifth arm
`else if n = ``Iff.rec then iffRecVal κ ls us`, and:

* the three `*Spec` witnesses transfer **verbatim** (`preludeWitnessRR_eq` / `_iff` / `_nonempty`,
  `preludeSpecRR_satisfiable`) — an arm added after the first three is invisible to them;
* `preludeWitnessRR_cnst_eq` is **still `rfl`** at `us = [w]`, so the type-former cell survives
  (`oracleOK_Eq_preludeWitnessRR`, `mem_interp_EqType_preludeWitnessRR`);
* both recursor cells are discharged at the *same* assignment:
  `oracleOK_IffRec_preludeWitnessRR` and `oracleOK_EqRec_preludeWitnessRR`;
* `Nonempty.rec` is untouched and still `•` (`preludeWitnessRR_mem_interp_neRecType`), which
  `NEAudit.oracleOK_NE_rec` depends on;
* `joint_repair_discriminates` gives the control at **both** cells at one witness and one
  interpretation each, and `joint_repair_changes_the_iffRec_value` shows the `Iff.rec` entry really
  changes. As in §20.4, both halves are stated at `interp (preludeWitnessRR κ ls)` deliberately:
  `interp` at the two witnesses is extensionally equal but not `rfl`-equal, and **no `interp`
  constant-congruence lemma exists**.

**What the joint repair still needs** (unperformed, and the thing to pick up first): the relocation
`PreludeRecGap.lean`'s header describes, now roughly doubled. The `Iff` side adds `impSet`,
`minSet`, `motSetI`, `lamHI`, `lamNI`, `lamFI`, `lamBI`, `iffRecFn`, `iffRecVal` and their nine
definability lemmas to the eight `Eq`-side definitions already listed — about **nineteen**
declarations to move into `PreludeSpec.lean`. Measured constraint, not reasoning: those definitions
use only `mkLam`, `mkForallType`, `mkForallProp`, their `_definable` lemmas (`Interp.lean`,
`Definability.lean`), `pt`, `U`, and `iffFn`/`eqFn` (`PreludeSpec.lean` itself), so nothing they need
is downstream. Everything *else* in this file — every `hasType_*`, `isProp_*`, `interp_*_val` — can
stay downstream, because only the `cnst` arm's *value* has to move.

### 21.6 The kernel trap, **reproduced and worse at five arms**

§20.4a's finding replicates. The naive `preludeWitnessRR_congr_Eq` — degenerate branch (`us` of
length ≥ 2, both sides `∅`) closed by `rfl` — is rejected with `(kernel) deterministic timeout`,
after elaborating cleanly, and `#print axioms` on the rejected declaration prints **`does not depend
on any axioms`**. New datum: at five arms it takes between **two and eight minutes of wall clock**
before the kernel gives up, where at four arms the previous stream saw it promptly. So the trap
**scales with the number of `if` arms**, which is exactly the number the relocation keeps adding.
Fix is §20.4a's: name the `Eq` arm once by `simp` (`preludeWitnessRR_cnst_Eq_arm`) and never let
`rfl` see the cascade; landed as `preludeWitnessRR_congr_Eq` (§14.1 of the file). Every
`preludeWitnessRR_cnst_*` in the file is `simp`, never `rfl`, for this reason.

### 21.7 What I tried that failed, and the step it failed at

* `rw [show (3 - 1 - 2 : ℕ) = 0 from rfl]` after `simp only [List.length_cons, List.length_nil]` —
  **failed at "No goals to be solved"**. `simp only` reduces the `Nat` subtraction literal and closes
  the goal by `rfl` *when the two indices coincide*. It does **not** close it when the read has to be
  peeled (`σ3 ‘ 1` versus `(snoc σ3 x) ‘ 1`), and there the explicit `show`-rw plus
  `EqZeroAudit.read_peel` is required. The rule, which no handoff states: the `show`-rw is needed
  exactly at the *peeling* steps, not at the coinciding ones. Two of my four numeral steps were of
  each kind.
* `(by rw [interp_sort])` for the two `U κ 0` binder domains — **failed at "unsolved goals"**: `rw`'s
  terminal `rfl` will not unfold `VLevel.eval ls .zero` to `0`. Fix: `rw [interp_sort]; rfl`. This is
  new in the family — `EqRecLarge`'s outermost domain is at a level *variable* `v`, so no reduction is
  ever needed there. Any block with a `Prop`-valued parameter will hit it.
* Reading `Iff.intro a b mp`'s type off `IffOracle.lean` — **failed at the `.inst` chain** (§21.2
  item 3). Recovered by `#eval` with a derived `Repr`.
* The naive `preludeWitnessRR_congr_Eq` — **failed at the KERNEL**, not at elaboration (§21.6).
* Reusing `EqZeroAudit.pt_mem_mkForallProp_self` for the field spaces' inhabitation — **failed at
  unification**: its `G`/`F` are constant, mine read the valuation (§21.2 item 4). Not attempted past
  the `refine`.

### 21.8 Bounds, and what is NOT discharged

**Axioms, `#print axioms` by namespace** (not by filename — this file declares into
`Lean4Lean.SetModel.IffLargeAudit`, while the names it reuses live in `Lean4Lean.SetModel`,
`…IffAudit`, `…EqZeroAudit`, `…EqLargeAudit`, `…RecGap`): all 86 `#print axioms` lines resolve (one per theorem, no duplicates);
47 report `[propext, Classical.choice, Quot.sound]`, 38 report `[propext, Quot.sound]`, and
`iffIndDecl_recUvars` reports none. **No `sorryAx`, no new `sorry`, none traded, no frozen-axiom
dependency.**

**Cone, over type *and* value, `allowOpaque := true`**, in an environment importing `IffRecLarge`
plus `Theory.Typing.{AppCodType0, Injectivity, UniqueTyping, ChurchRosser}`. **All four big holes
`present = true`** (`IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `IsDefEqU.weakN_iff`,
`NormalEq.descend`) — checked, because `descend` reads absent without `ChurchRosser` and every cone
then looks clean. Both controls fire: `piInv_axiom` cone 3576, `sorryAx true`, 2 holes;
`WF.sortUniq'` cone 3441, `sorryAx true`, 1 hole. **All 26 seeds: 0 holes, `sorryAx false`**
(cones 1491–8533).

`Above` **does not occur** in the file except in two prose lines; `oracleOK_of` discharges both
`OracleOK` fields with `Above.pure`, so no `IsInaccessibleChain` hypothesis is used and **no `κ` is
chosen** — every statement is at an arbitrary `κ : ℕ → V`. The anti-vacuity controls here need **no**
parameter-space inhabitant at all (`IffAudit.pt_not_mem_interp_iffRecType_of_ne` carries none,
because `Iff`'s outermost binder is a parameter over `Prop` and `∅ ∈ U κ 0` at every `κ`), so unlike
`EqRecLarge` §7 there is no `hx` whose satisfiability and necessity has to be argued. The
three-point scale grades the negative controls, and these are the negative controls.

**Hole-free is not discharged.** Still open, none of it claimed:

* `InductOracleOK` at `iffIndDecl` is **not assembled**. This file closes one of three `consts`
  cells. The other two are `IffAudit` §7's rows: `Iff ↦ iffFn ∈ ⟦Prop → Prop → Prop⟧` (template:
  `EqTFAudit.eqFn_mem_interp_EqType`) and `Iff.intro ↦ •`. The **`rules` field** (one ι-rule,
  `iffIndDecl.iotaRules.length = 1`) is not done either.
* `eqIndDecl`'s `rules` field is still not done (unchanged from §20.8 item 3).
* The relocation and the real `PreludeSpec.lean` edit are unperformed (§21.5).
* `NEAudit.nonempty_propSplit_preludeEnv` prints `sorryAx`, so **nothing here is "sorry-free at
  `preludeEnv`"** through it. Everything above is parametric in `L : PropSplit envF nv`.
* The machine-checked bad-model control at `Nonempty.rec` (§20.3) still does not exist.

**Tooling, named.** I used none of `lean_references`, `lean_local_search`, `lean_hammer_premise`, so
I neither confirm nor refute the brief's claims about them. My enumeration tool was `grep -rn` over
`Lean4Lean/**/*.lean` — treat it as a **floor**. Ground truth for the cone and the axioms is the
compiler: `lake build`, `#print axioms`, and a `lake env lean` cone script. The one shape
measurement (`Iff.intro a b mp`'s type) was `#eval` with a derived `Repr`, which is also the
compiler.

### 21.9 What to pick up first

1. **The relocation and the real edit** to `PreludeSpec.lean`, at **both** arms, in one step
   (§21.5). Nineteen declarations, mechanical by the import-graph measurement, and **measure the
   kernel-timeout surface first** (§21.6): the trap scales with arm count and the relocation adds
   arms.
2. **`Iff`'s other two `consts` cells** — the type-former and `Iff.intro ↦ •`. Both should now be
   short: the whole context ladder (`onCtxI_M` … `onCtxI_Qb`), the proof/value split, and
   `interp_iffAp_bvars` are in this file, and `Iff.intro`'s type *is* a proposition
   (`IffAudit` §7 says so, and `isProof_introC3` is the same computation one application further in).
3. **The two ι-rules.** `EqRecLarge` §10.1's argument is block-generic — `VInductDecl'.iotaRules_WF`
   from `D.IotaCtx env`, produced by `VInductDecl'.WF.iotaCtx` from three staged `addConstList`s,
   all `rfl` at `VEnv.empty` — so `iffIndDecl`'s rule's *typing* should be free the same way.
   **Not run**, so this is an argument from the shape of the lemma, not a measurement.
4. The `Nonempty.rec` bad-model control, if that cell is ever quoted as more than "correct by
   `isLE = false`".

### 21.10 Files touched this session

* `Lean4Lean/Theory/SetModel/IffRecLarge.lean` — **new**, 1154 lines, no `sorry`, 86 theorems,
  86 `#print axioms` lines (all resolving, all `Lean4Lean.SetModel.IffLargeAudit.*`).
* `Lean4Lean/Theory/Equiconsistency.lean` — one import line, added on the same edit as the file.
* `docs/handoff-setmodel.md` — this section.

Per-module `lake build` job counts, all exit 0: `Lean4Lean.Theory.SetModel.PreludeRecGap`
**1210 jobs** (baseline); `Lean4Lean.Theory.SetModel.IffRecLarge` **1211 jobs** (the new module
elaborates in ~9 s); `lake build Lean4Lean.Theory.Equiconsistency` **1247 jobs**, validating the
import line. The five `declaration uses 'sorry'` warnings are the pre-existing ones
(`Inductive/Decl.lean:561`, `Typing/Injectivity.lean:261` and `:1046`,
`Typing/UniqueTyping.lean:190`, `Equiconsistency.lean:58` — the main `↔`; the last two line numbers
differ from §20.9's because of my import line and another stream's edit to `Decl.lean`). No full
`lake build`, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`, no `lean_build`
MCP call.

---

## 22. The kernel-timeout surface, measured — and the one-line shape fix that removes it

Brief: measure the kernel cost of the `if`-cascade witness across arm counts before touching
`PreludeSpec.lean`; if the surface says the relocation is unaffordable, stop and say so.

**Verdict: the surface clears the relocation, and it clears it in a *better* shape than the brief
asked for.** The trap is not the arm count and not the `rfl`. It is a single syntactic choice in
how the witness is written, and reversing that choice removes the trap entirely — no `simp`
workaround, no arm-lemma detour, naive `rfl` everywhere, at 1/50 of the default heartbeat budget.

### 22.1 The instrument (and why wall clock was the wrong axis)

`(kernel) deterministic timeout` is raised by the kernel's own `check_system`, which reads the
**`maxHeartbeats` option** — the same one the elaborator uses. So the trap has a *deterministic*
cost measure, not just a wall clock, and it can be dialled:

* `set_option maxHeartbeats 2000 in` reproduces the five-arm failure in **3.6 s** total instead of
  minutes, and `#print axioms` on the rejected declaration still prints
  `does not depend on any axioms` — the trap, at 1/100 the cost of observing it.
* Wall clock is **linear in the budget**: ≈1.2 s per 1000 heartbeat-units of burn. So §20.4a /
  §14.1's "two to eight minutes before the kernel rejects it" is **not a measurement of the
  proof's cost** — it is the time to exhaust the default 200 000-unit budget. Corrected below.
* The elaborator/kernel split falls out for free: at `maxHeartbeats 4000` the failing declarations
  fail with `(kernel) deterministic timeout`, i.e. **elaboration finished inside 4000 units while
  the kernel could not**. The gap is not marginal; see 22.3.

All runs are `lake env lean /tmp/km/*.lean` against the built `.olean`s — no module was created and
no `lake build` was run for the measurement. Import overhead baseline: 2.4 s.

### 22.2 Phase 1 table: arms × formulation × outcome × wall clock

`cell A` is the failing shape: `cnst ``Eq (a::b::t) = cnst ``Eq (a'::b'::t')` — the degenerate
branch of `preludeWitness_congr_Eq`, both sides cascades, `us` differing. All at
`maxHeartbeats 4000` unless stated. "heavy" = the arm body is `eqRecVal κ ls us` / `iffRecVal κ ls
us` (which unfold to the six- and five-layer `mkLam` nests); "light" = `∅`.

| witness | `if` arms | untaken-arm bodies | cell | formulation | outcome | wall |
|---|---|---|---|---|---|---|
| `w3` (= `preludeWitness`) | 3 | — | A | `rfl` | **pass** | 12.3 s / 20 decls |
| `w4` (= `preludeWitnessR`) | 4 | heavy, `us`-dep | A | `rfl` | **(kernel) timeout** | |
| `w5` (= `preludeWitnessRR`) | 5 | heavy, `us`-dep | A | `rfl` | **(kernel) timeout** | |
| `w7` | 7 | heavy, `us`-dep ×4 | A | `rfl` | **(kernel) timeout** | |
| `s5` | 5 | light (`∅`) | A | `rfl` | **pass** | |
| `s7` | 7 | light (`∅`) ×4 | A | `rfl` | **pass** | 8.3 s / 14 decls |
| `h4` | 3 + heavy fallback | heavy, `us`-dep | A | `rfl` | **(kernel) timeout** | |
| `hX4` | 3 + heavy fallback | heavy, **no `us`** (`eqRecVal κ ls [zero,zero]`) | A | `rfl` | **pass** | |
| `hY4` | 3 + fallback | light, `us`-dep (stuck matcher) | A | `rfl` | **pass** | |
| `hZ4` | 3 + fallback | `κ us.length` | A | `rfl` | **pass** | |
| `hW4` | 3 + fallback | `us`-dep matcher-over-`ite`, **`eqRecFn` replaced by `pt`** | A | `rfl` | **pass** | 2.9 s / 8 decls |
| `h4` | 4 | heavy, `us`-dep | A, same tail variable | `rfl` | **(kernel) timeout** | |
| `h4` | 4 | heavy, `us`-dep | A, **closed** level lists both sides | `rfl` | **(kernel) timeout** @200 000 | 2 m 17 s |
| `w4` | 4 | heavy | A | `rfl`, `maxHeartbeats 0` | **PASSES** | **8 m 17 s** |
| `w5`,`w7` | 5,7 | heavy | `cnst Eq (a::b::t) = (∅:V)` (one side a literal) | `rfl` | **pass** | |
| `w5`,`w7` | 5,7 | heavy | `cnst Eq [w] = eqFn …` (arm 1) | `rfl` | **pass** | |
| `w5`,`w7` | 5,7 | heavy | deepest arm, `cnst Iff.rec us = iffRecVal …` | `rfl` | **pass** | |
| `w5`,`w7` | 5,7 | heavy | fallback, `cnst Nat us = ∅` | `rfl` | **pass** | |
| `w7` | 7 | heavy | A with the **same** `us` both sides | `rfl` | **pass** | |
| `w5`,`w7` | 5,7 | heavy | arm lemma `cnst Eq us = match us with …` | `simp [w]` | **pass** | |
| **`e5`** | **5, η-contracted** | heavy, `us`-dep | A, **and every other cell, and the full congruence theorem** | **`rfl`** | **pass** | **2.9 s** |

### 22.3 What makes an arm expensive — the answer, and it is not the arm count

Three claims in the brief and in `PreludeRecGap` §20.4a / `IffRecLarge` §14.1 are **wrong**:

1. **"The cost scales with arm count."** It does not. `s7` — *seven* arms — passes the naive `rfl`
   at 4000 heartbeats. `h4` — *three* `if`s, one heavy fallback — fails. Arm count is a confound:
   the arms being added happened to carry the `mkLam` nests.
2. **"The `rfl` at the end is the problem."** Not on its own: `B`, `C`, `D`, `E`, `F` are all `rfl`
   through the same five- and seven-arm cascades and all pass. What fails is specifically `rfl`
   between **two** cascade terms at **different** `us`.
3. **"It takes 2–8 minutes and then the kernel refuses it."** It takes 2–8 minutes because that is
   how long burning the default budget takes. At `maxHeartbeats 0` the four-arm naive `rfl`
   **succeeds** in 8 m 17 s, i.e. it needs ≈4.1 × 10⁵ heartbeat-units against a default of
   2 × 10⁵. The proof is **not** divergent; it is a factor ~2 over budget.

The measured predictor is a **conjunction**, and each conjunct is refuted alone:

> the blowup happens iff an **untaken** arm's body both (a) mentions `us` and (b) unfolds to
> `eqRecFn`/`iffRecFn`.

* drop (a) — `hX4`, heavy body at a *closed* level list — **passes**;
* drop (b) — `hY4`/`hZ4`/`hW4`, `us`-dependent bodies of ordinary size, `hW4` keeping the exact
  matcher-over-`ite` shape of `eqRecVal` with only `eqRecFn` swapped for `pt` — **all pass**.

So the cost lives **inside `eqRecFn`/`iffRecFn`** (six and five `mkLam` layers, each carrying
`definability` proof terms), and it is reached only because the two sides differ at `us`.

Mechanism, consistent with all twelve cells but **not itself measured** (I did not instrument the
kernel): both sides are applications of the same head, so the kernel tries argument-wise congruence
*before* reducing the `ite`; congruence descends into the untaken else-branch, which is
`eqRecVal κ ls us` vs `eqRecVal κ ls us'`; those have the same head too, so it recurses, fails on
the scrutinee, and unfolds — into the `mkLam` nests. The taken branch, which is what makes the goal
true, is only reached after that whole descent has been paid for. Treat this paragraph as a
hypothesis; the twelve rows above are the measurement.

### 22.4 The fix: η-contract the witness. Zero proof cost.

The witness is written `cnst := fun n us ↦ if n = ``Eq then … else … else ∅`. Write it instead as

```lean
  cnst := fun n ↦
    if n = ``Eq then (fun us ↦ match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (fun us ↦ match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (fun us ↦ match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else if n = ``Eq.rec then eqRecVal κ ls
    else if n = ``Iff.rec then iffRecVal κ ls
    else fun _ ↦ ∅
```

— branch on `n` alone, each arm a *function* of `us`. Now no untaken arm mentions `us`, so the two
sides of any `us`-differing comparison have **syntactically identical** untaken branches and the
congruence attempt succeeds instead of descending. Measured at five arms (`e5`, last row of 22.2):

* cell A by naive `rfl` — **passes**, at `maxHeartbeats 4000`;
* A with closed level lists — passes;
* arm 1, deepest arm, `Nonempty.rec`, the fallback — all naive `rfl`, all pass;
* **the whole `preludeWitness_congr_Eq`, degenerate branch by `rfl`** — passes.

This supersedes `PreludeRecGap` §4.5's and `IffRecLarge` §14.1's prescription ("name the `Eq` arm
once by `simp` and never let `rfl` see the cascade"). That prescription works, and it is what
`preludeWitnessR_cnst_Eq_arm` / `preludeWitnessRR_cnst_Eq_arm` do; but it is a workaround for a
self-inflicted shape, and it costs an extra lemma plus an `rw` at every use site. The η-contraction
costs nothing and keeps every downstream statement a `rfl`.

### 22.5 The relocation, **run** rather than read off the import graph

`/tmp/km/reloc.lean` and `/tmp/km/reloc2.lean`: a file importing **only**
`Lean4Lean.Theory.SetModel.PreludeSpec`, i.e. exactly `PreludeSpec.lean`'s own surface
(`Cnst` + `Definability` + itself), carrying the whole payload extracted verbatim by `awk` from
`EqRecLarge.lean` and `IffRecLarge.lean` (`section Combinators`, `section Definable`,
`section Value` of each, plus `eqRecVal`/`iffRecVal`).

**It compiles clean, exit 0, no errors and no warnings, in 3.8 s.** One textual change was needed:
`EqLargeAudit.const_definable₂` → `const_definable₂`, because the two halves land in one namespace.
Nothing else — the brief's "those need only `mkLam`, `mkForallType`, their `_definable` lemmas and
`eqFn`/`iffFn`, all already imported" is **confirmed by running it**.

**The count is wrong, though: 40 declarations, not ~19.** Measured by name:

| block | declarations |
|---|---|
| `EqRecLarge` §1 combinators | `mkFamUnion_ext`, `mkForallType_ext` |
| `EqRecLarge` §2 definability | `eqAt_definable`, `eqAt_definable₂`, `minAt_definable`, `const_definable₂` |
| `EqRecLarge` §3 value | `motSet`, `lamH`, `lamB`, `lamM`, `lamF`, `lamA`, `eqRecFn` + the six `_definable` companions |
| `EqRecLarge` §9 | `eqRecVal` |
| `IffRecLarge` §1 | `mkForallProp_ext` |
| `IffRecLarge` §2 | `iffAt_definable`, `appPt_definable₂`, `minAppPt_definable₂` |
| `IffRecLarge` §3 value | `impSet`, `minSet`, `motSetI`, `lamHI`, `lamNI`, `lamFI`, `lamBI`, `iffRecFn` + the seven `_definable` companions |
| `IffRecLarge` §13 | `iffRecVal` |

19 + 21 = **40**. The brief's 19 is the `Eq` half with the `lam*_definable` companions and
`mkFamUnion_ext` omitted; `IffRecLarge` §14's "eight definitions more … plus §2's three
definability lemmas and `mkForallProp_ext`" (12) is likewise short by the `Iff` half's eight
`_definable` companions. The *character* of the estimate holds — mechanical, no new imports — but
the size is 2.1×.

### 22.6 The full drop-in, compiled

`/tmp/km/reloc2.lean` = the 40 declarations + the η-contracted five-arm `preludeWitness'` + every
cell the downstream files read, each in its **naive** form, at the **default** heartbeat budget:
`_eq`/`_iff`/`_nonempty`/`preludeSpec_satisfiable`; `cnst ``Eq [w]`, `cnst ``Iff []`,
`cnst ``Nonempty [w]`, `cnst ``Eq.rec us`, `cnst ``Iff.rec us`, `cnst ``Nonempty.rec us`,
`cnst ``Nonempty.intro us` — all `rfl`; `preludeWitness_congr_Eq` with the degenerate branch by
**`rfl`**; and `neOracle_eq_empty_of_not_mem` in its repaired five-hypothesis shape by `simp`.

**Exit 0, 4.0 s, no errors, no warnings.** So the answer to "is the relocation affordable in the
current shape" is: yes, and the repaired shape is *cheaper* than the present one, because the
`_cnst_Eq_arm` + `rw` detour disappears.

### 22.7 The fallout inventory, and the one thing the census misses

Enumeration tool: `rg` (**which is present in this environment — ripgrep 14.1.1**; see 22.10).
`rg -c preludeWitness Lean4Lean` gives 315 occurrences in 9 files. The reverse-import closure of
`PreludeSpec.lean`, computed by a Python walk over `^import` lines of all 369 `.lean` modules, is
**24 modules** — 17 in `SetModel`, plus `Theory/Equiconsistency`, `Experimental/ConeJoin`,
`Verify/ClosednessPropagation`, `Verify/SoundnessAssembly`, and three `Verify/Inductive/*`. Of those
seven non-`SetModel` modules, **none mentions `preludeWitness`, `neOracle` or `neM`** (`rg` over
`Lean4Lean/Verify`, `Lean4Lean/Experimental`, `Theory/Equiconsistency.lean` — the only hits are four
import *comments* in `Equiconsistency.lean`). So they need rebuilding, not editing — which matters,
because `Experimental/ConeJoin.lean` is in the closure and is a file no stream may touch.

Declarations the repair breaks, with **their consumers**, all located by `rg`:

| refuted / changed | at | consumers |
|---|---|---|
| `EqLargeAudit.preludeWitness_cnst_eqRec` | `EqRecLarge:425` | `EqRecLarge:437`, `EqRecLarge:447`, `PreludeRecGap:379`, `IffRecLarge:988` |
| `EqLargeAudit.preludeWitness_not_mem_interp_eqRecType` | `EqRecLarge:433` | none (only its own `#print axioms`) |
| `EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero` | `EqRecLarge:444` | none; statement survives, one extra rewrite |
| `RecGap.preludeWitness_cnst_iffRec` | `PreludeRecGap:62` | `PreludeRecGap:75`, `IffRecLarge:992`, `IffRecLarge:1002` |
| `RecGap.preludeWitness_not_mem_interp_iffRecType` | `PreludeRecGap:72` | none in code (prose + an import comment) |
| `NEAudit.preludeWitness_eqRec_empty` | `PreludeOracle:1476` | none |
| `NEAudit.preludeWitness_iffRec_empty` | `PreludeOracle:1481` | none |
| `NEAudit.neOracle_eq_empty_of_not_mem` | `PreludeOracle:1341` | `PreludeOracle:1375` (`cnstOf_preludeTail`) |
| `EqTFAudit.preludeWitness_congr_Eq` | `EqTypeFormer:269` | `EqTypeFormer:297` (`oracleOK_Eq`) — and with η-contraction its proof needs **no** change |

`NEAudit.neM_eq : neM κ ls = preludeWitness κ ls := rfl` (`PreludeOracle:552`) survives: `neOracle`
is *defined* as `(preludeWitness κ ls).cnst`, so both sides move together and the `rfl` is
syntactic. `cnstOf_preludeTail`'s tactic proof is unaffected except at its one call to
`neOracle_eq_empty_of_not_mem`, and §5.3's argument that the two extra hypotheses are suppliable
there is sound: the branch that reaches it has `m ∉ eqIndDecl.allNames` and `m ∉
iffIndDecl.allNames`, while `Eq.rec ∈ eqIndDecl.allNames` and `Iff.rec ∈ iffIndDecl.allNames`
(`RecGap.eqRec_mem_eqIndDecl_allNames`, `RecGap.iffRec_mem_iffIndDecl_allNames`, both already in the
tree).

**What the census in `PreludeRecGap` §4 misses, and it is not cosmetic.** Repairing `preludeWitness`
*in place* destroys the negative control that gives the repair its content. `RecGap.repair_discriminates`
and `IffLargeAudit.joint_repair_discriminates` are of the form "the repaired witness is in the
interpretation **and `preludeWitness` is not**". After the edit there is no `preludeWitness` in the
failing shape, so both theorems either fail to compile (they rewrite with
`preludeWitness_cnst_eqRec` / `preludeWitness_cnst_iffRec`, which become false) or degenerate into
"the repaired witness differs from itself". The repair must therefore **preserve the old assignment
under a new name** in the same edit. `/tmp/km/reloc2.lean` does this as `preludeWitnessPt`, and
checks that it is a *legitimate* control rather than a broken object: `pwPt_cnst_eqRec` and
`pwPt_cnst_iffRec` are still `•`, `pwPt_eq`/`pwPt_iff`/`pwPt_nonempty` still meet all three
specifications, and `pw_agree_Eq`/`_Iff`/`_NE` are `rfl` — so the two witnesses differ *only* at the
two recursor cells, which is exactly what a discrimination theorem wants. All of that compiles in
the same 4.0 s run.

### 22.8 Phase 2, **performed**: the relocation and the real edit, both arms, one edit

`PreludeSpec.lean` now carries the payload and the repaired witness; `SetModel.preludeWitness` — the
assignment `NEAudit.neOracle` *is* (`neOracle := (preludeWitness κ ls).cnst`, so `NEAudit.neM_eq`
stays `rfl`) — has both recursor arms. `Nonempty.rec` was **not** touched: it falls through to `∅`,
which is `•`, which `nonemptyIndDecl.isLE = false` makes correct, and
`RecGap.preludeWitness_mem_interp_neRecType` still proves it at the new witness with no change.

**`PreludeSpec.lean`** (+407 lines): the 40 relocated declarations (42 installed, counting the two `_pair`/`_single` `rfl`s pulled up with them), verbatim except
`EqLargeAudit.const_definable₂ → const_definable₂`; `eqRecVal`, `iffRecVal`, `eqRecVal_pair`,
`iffRecVal_single` (the last two moved up as well, because §8 of `EqRecLarge.lean` now needs
`eqRecVal_pair` earlier in its own file); the η-contracted five-arm `preludeWitness`; the preserved
pre-repair `preludeWitnessPt`; and the cell lemmas — six `_cnst_*` all `rfl`,
`preludeWitness_congr_Eq` with a `rfl` degenerate branch, `preludeWitness_cnst_empty`, the three
`preludeWitnessPt_*` specification proofs, the two `preludeWitnessPt_cnst_*Rec` `= •` facts and the
three `preludeWitness_agree_*` `rfl`s.

**`EqRecLarge.lean`** (−255/+…): §§1--3 and `eqRecVal`/`eqRecVal_pair` deleted, replaced by a
pointer note and one `export Lean4Lean.SetModel (…)` — after which **no use site anywhere had to be
rewritten**, and `#print axioms Lean4Lean.SetModel.EqLargeAudit.motSet` still resolves (through the
alias; verified, it prints `Lean4Lean.SetModel.motSet`). §8's two refuted theorems are restated at
`preludeWitnessPt` (`preludeWitnessPt_not_mem_interp_eqRecType`,
`preludeWitnessPt_mem_interp_eqRecType_of_zero`), and two new ones say what the repair buys at the
real witness: `preludeWitness_mem_interp_eqRecType_of_zero` (the census's "one extra rewrite", which
is exactly `rw [preludeWitness_cnst_eqRec, eqRecVal_pair, if_pos h0]`) and
`preludeWitness_mem_interp_eqRecType_of_ne`.

**`IffRecLarge.lean`**: §§1--3 and `iffRecVal`/`iffRecVal_single` deleted + `export`; §14's
`joint_repair_discriminates` and `joint_repair_changes_the_iffRec_value` re-pointed at
`preludeWitnessPt`; and a **new §15** with the installed repair at the shared witness —
`oracleOK_IffRec_preludeWitness`, `oracleOK_EqRec_preludeWitness`,
`preludeWitness_mem_interp_iffRecType`, `installed_repair_discriminates` (both cells, one `L`, one
`κ`, one `ls`, one level tuple, **one `interp` — the repaired witness's, in all four conjuncts**) and
`installed_repair_changes_the_iffRec_value`.

**`PreludeRecGap.lean`**: §1's `preludeWitness_cnst_iffRec` deleted (it is now
`SetModel.preludeWitnessPt_cnst_iffRec`) and `preludeWitness_not_mem_interp_iffRecType` restated as
`preludeWitnessPt_not_mem_interp_iffRecType`; §4.3's `repair_discriminates` /
`repair_changes_the_value` re-pointed at `preludeWitnessPt`. §2's `Nonempty.rec` results unchanged.

**`PreludeOracle.lean`**: `neOracle_eq_empty_of_not_mem` grew `h4 : m ≠ ``Eq.rec` and
`h5 : m ≠ ``Iff.rec` and is now `simpa [neOracle] using preludeWitness_cnst_empty …`;
`cnstOf_preludeTail` supplies both, in the branch §5.3 predicted, by the `recConsts` route
(`simp only [VInductDecl'.allNames, allConsts, recConsts, List.map_append, List.mem_append]; right;
simp [eqIndDecl]; rfl` — the `typeConsts` `simp` the three existing bullets use does **not** close
these two, which is the one thing §5.3 did not say); and §13's `preludeWitness_eqRec_empty` /
`preludeWitness_iffRec_empty` are deleted, with a note recording that they were refuted rather than
upgraded and naming their four replacements.

**Every module in the reverse-import closure builds.** `lake build Lean4Lean.Theory.Equiconsistency`
**1247 jobs**, exit 0; adding the `Verify` tail,
`lake build Lean4Lean.Verify.ClosednessPropagation Lean4Lean.Verify.Inductive.CanonGapMeasure
Lean4Lean.Verify.Inductive.UniformOccMeasure` **1447 jobs**, exit 0 — which pulled in
`Verify.SoundnessAssembly` and `Experimental.ConeJoin` as dependencies and built both. Per-module:
`PreludeSpec` **1158** (4.9 s), `PreludeOracle` **1203** (4.3 s), `EqTypeFormer` **1207** (2.3 s,
**rebuilt with no source change at all** — see below), `EqRecLarge` **1209** (2.5 s),
`PreludeRecGap` **1210** (2.2 s), `IffRecLarge` **1211** (3.2 s). `MemberRedexScan` was not built,
per the brief. No full `lake build`, no guards, no `sorry-census`, no `dup-names`, no `lean_build`
MCP call.

**`EqTypeFormer.lean` needed zero changes.** Its `preludeWitness_cnst_eq` (`rfl`) and
`preludeWitness_congr_Eq` (degenerate branch by `rfl`) — the very proof `PreludeRecGap` §4.5
identified as the one that does not transfer — compiled unmodified against the five-arm witness.
That is the sharpest confirmation of 22.4 available: the trap was the shape, not the arms.

### 22.9 Proved / open / refuted, and hole-free vs discharged

**Proved, and new.** `SetModel.preludeSpec_satisfiable` at the repaired witness (all three
specifications still met, proofs byte-identical); the six `preludeWitness_cnst_*` cells and
`preludeWitness_congr_Eq`; `preludeWitness_cnst_empty`;
`EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero` and `_of_ne`;
`IffLargeAudit.preludeWitness_mem_interp_iffRecType`;
`IffLargeAudit.oracleOK_EqRec_preludeWitness` and `oracleOK_IffRec_preludeWitness` — **the two
`consts` cells at the two large-eliminator recursors, discharged at the shared witness with no side
oracle parameter, no chain hypothesis and no chosen `κ`**; `installed_repair_discriminates` and
`installed_repair_changes_the_iffRec_value` as the anti-vacuity controls; and the negative control's
legitimacy (`preludeWitnessPt_eq`/`_iff`/`_nonempty`, `preludeWitness_agree_*`).

**Axioms, by namespace** (`#print axioms` on 50 names, `Lean4Lean.SetModel.*`,
`…EqLargeAudit.*`, `…IffLargeAudit.*`, `…RecGap.*`, `…EqTFAudit.*`, `…NEAudit.*`): every one is
`[propext, Classical.choice, Quot.sound]`. **No `sorryAx`, no new frozen-axiom dependency, no
axiom traded.** `NEAudit.cnstOf_preludeTail` and `NEAudit.oracleStepOK_NE` are clean again — they
printed `sorryAx` in the intermediate broken state, which is a reminder that an axiom print during a
failing build reports the *error recovery*, not the proof.

**No new `sorry`, none traded.** The five `declaration uses 'sorry'` warnings in the
`Equiconsistency` build are the pre-existing ones: `Inductive/Decl.lean:561`,
`Typing/Injectivity.lean:261` and `:1046`, `Typing/UniqueTyping.lean:190`,
`Equiconsistency.lean:58` (the main `↔`).

**Hole-free is not discharged.** Still open, none of it claimed:

* `InductOracleOK` at `eqIndDecl` and `iffIndDecl` is **not assembled**. Two of three `consts` cells
  are now closed at the shared witness at each block (the recursor by §15, the type former by
  `EqTFAudit.oracleOK_Eq` for `Eq`); `Iff`'s type-former cell and `Iff.intro ↦ •` are still
  `IffAudit` §7's rows, and **both blocks' `rules` fields are still not done**.
* `NEAudit.propSplitPreludeEnv` still prints `sorryAx`, so **nothing here is "sorry-free at
  `preludeEnv`"** through it; everything above is parametric in `L : PropSplit envF nv`.
* The machine-checked bad-model control at `Nonempty.rec` (§20.3) still does not exist.
* `RecGap.preludeWitnessR` and `IffLargeAudit.preludeWitnessRR` are now **redundant** — the objects
  they were instruments for are in `PreludeSpec.lean`. They still compile and their theorems still
  hold; they should be retired, and with them `preludeWitnessRR_cnst_Eq_arm` /
  `preludeWitnessR_cnst_Eq_arm`, whose whole reason to exist was the trap 22.4 removes.
* Nothing here mentions `Above`, at any point, so no result is free at a false antecedent.

**Refuted, and now stated at the preserved control instead of deleted.**
`preludeWitnessPt_not_mem_interp_eqRecType` (`Eq.rec`, `≠ 0` slice) and
`preludeWitnessPt_not_mem_interp_iffRecType` (`Iff.rec`, `≠ 0` slice). Both are non-vacuous: the
matching `∈` at the repaired witness is proved in the same files, so the interpretation is not empty.

### 22.10 What failed, and the step it failed at

* **The naive `rfl` at five arms**, reproduced first: `(kernel) deterministic timeout`, after
  elaboration succeeded and `#print axioms` printed `does not depend on any axioms`. Failed at the
  *kernel*, not the elaborator — which is how I learned the elaborator closes it inside 4000
  heartbeats.
* **First matrix run**: `` `Unit.rec `` is not a constant (`Unit` is a `def` for `PUnit`), so `w7`
  and `s7` were `sorry`-poisoned and their five rows were noise. Failed at *elaboration of the
  witness definition*, before any measurement. Re-ran with `` `Nat.rec ``/`` `And.rec ``.
* **`maxHeartbeats 4000` for the whole file**: too small for the elaborator on two cells
  (`A_h4_closed` reported `(deterministic) timeout at isDefEq` rather than a kernel error), so the
  budget dial cuts both ways and a low global budget cannot separate the two engines by itself. Fixed
  by reading the *message*, not the exit code.
* **`G_congr_w7` in the harness**: `rw [arm, arm, VLevel.equiv_def.mp h ls]` failed with "did not
  find an occurrence" in the `us = [a]` case, because the arm lemma leaves a `match` the rewrite
  cannot see through. Failed at the *middle* branch, not the degenerate one — a harness bug, not a
  cost result; the tree's own version uses the `[w]` cell lemma there and is right.
* **`preludeWitness_mem_interp_iffRecType` first placed in `PreludeRecGap.lean`**: unknown
  identifier `IffLargeAudit.iffRecFn_mem_interp_iffRecType` — `IffRecLarge.lean` *imports*
  `PreludeRecGap.lean`, so the positive half of the `Iff.rec` story cannot live beside the negative
  half. Failed at *elaboration of the new theorem*; moved to §15.
* **`eqRecVal_pair` left behind in `EqRecLarge.lean`**: §8 now needs it and §8 precedes §9. Failed at
  *`EqRecLarge` §8's two new rewrites*; fixed by moving `eqRecVal_pair` (and `iffRecVal_single`)
  upstream too, which is why the payload is 42 declarations installed rather than 40 measured.
* **`cnstOf_preludeTail`'s two new bullets** with the `typeConsts` `simp` the three existing bullets
  use: unsolved goals. `Eq.rec` is in `recConsts`, not `typeConsts`. Failed at the *`simp`*, fixed by
  copying `RecGap.eqRec_mem_eqIndDecl_allNames`'s proof inline (it cannot be reused: it lives
  downstream).
* **`/-- … -/` with no declaration after it** where I removed a theorem: `unexpected token 'end'`.
  Trivial, but it is the second time this session a doc-comment/`/-!` confusion cost a build.

### 22.11 Measured versus read off

| claim | source | status |
|---|---|---|
| relocation needs no new import | brief + `PreludeRecGap` header, read off `^import` | **measured**: payload compiles against `PreludeSpec`'s surface, 3.8 s |
| relocation is ~19 declarations | brief, read off the import graph | **measured wrong**: 40 to move, 42 installed |
| cost scales with arm count | `IffRecLarge` §14.1, from two data points | **measured wrong**: 7 light arms pass, 3 arms + 1 heavy `us`-dependent body fail |
| the naive `rfl` is refused by the kernel | §20.4a, measured | **true but mis-priced**: it *succeeds* at `maxHeartbeats 0` in 8 m 17 s; the default budget is ~2× too small |
| `#print axioms` cannot see the trap coming | brief | **confirmed**, reproduced twice |
| `Nonempty.rec` must stay untouched | brief | **confirmed**: untouched, and `RecGap.preludeWitness_mem_interp_neRecType` needed no change |
| the fix is `simp` then `rw` | `PreludeRecGap` §4.5 | **superseded**: η-contraction makes every cell `rfl` again |
| `neOracle_eq_empty_of_not_mem`'s extra hypotheses are suppliable at the one use site | `PreludeRecGap` §5.3, argued | **measured**: yes, but not by the `simp` the site already uses |
| `Iff.rec`'s cell is satisfiable | `IffRecLarge` §7, measured | used, and now installed at the shared witness |
| the two ι-rules are free from `VInductDecl'.iotaRules_WF` | §21.9 item 3, "argument from the shape of the lemma, not a measurement" | **still not measured** |

### 22.12 Tooling, named — and one brief claim that is simply false

* **`rg` is present and works: ripgrep 14.1.1 (`rg --version`).** The brief's "all three search
  instruments are unreliable — `rg` is absent so `lean_local_search`/`lean_hammer_premise` are dead"
  is wrong on its premise. I used `rg` throughout; treat its counts as floors anyway, because a
  string search cannot see through an `export` alias or a `simp` set.
* Every enumeration above names its tool. The 24-module reverse-import closure and the 369-module
  count are from a **Python walk over `^import` lines**, not `rg` — that is exact for this repo's
  import style and is the one enumeration here I would call complete rather than a floor.
* **The absence claim in 22.7** — that no module outside `SetModel` touches the repair — is not a
  string search for a name I hoped was absent: the objects are `SetModel.preludeWitness`,
  `NEAudit.neOracle` (**defined** as `(preludeWitness κ ls).cnst`) and `NEAudit.neM` (**defined** as
  `⟨κ, ls, neOracle κ ls⟩`), and I searched for all three definitions' names plus every relocated
  definition's name across `Lean4Lean/Verify` and `Lean4Lean/Experimental`. Zero hits, and the
  build of the whole closure — `ConeJoin` and `SoundnessAssembly` included — is the independent
  check.
* Ground truth everywhere is the compiler: `lake build`, `lake env lean`, `#print axioms`.
  `lean_references`, `lean_local_search` and `lean_hammer_premise` were not used, so I neither
  confirm nor refute the brief's claims about the latter two.
* **Not mine**: `Lean4Lean/Verify/Inductive/NestedRestoreWit.lean` is modified in the working tree
  (one line, `nfnAux_builtFresh → (nfnAux_builtFresh h)`). Another stream's in-flight edit; I did
  not touch that file and it is unrelated to this change.

### 22.13 Where the brief is wrong

Asked for plainly, so: four things.

1. **"The cost scales with arm count, and the relocation adds arms."** No. The predictor is a
   *conjunction* about untaken arm bodies (`us`-dependent **and** unfolding to `eqRecFn`), and
   dropping either conjunct removes the cost at any arm count up to seven. Framing the gate as
   "measure across arm counts" pointed at the confound; the cells that settled it are the ones that
   vary body *shape* at fixed arm count (`hX4`, `hY4`, `hZ4`, `hW4`), which the brief did not ask
   for.
2. **"Wall clock 2--8 minutes, then refused."** That is the default heartbeat budget burning, not the
   proof's cost. The right instrument is `maxHeartbeats`, which makes the trap reproducible in 3.6 s
   and shows the proof *terminates* at 8 m 17 s. A gate framed on wall clock would have concluded
   "unaffordable"; the correct conclusion is "affordable, and the shape is wrong".
3. **"~19 declarations, mechanical."** Mechanical: right, and now run rather than read. Nineteen:
   wrong by 2.1× (40 measured, 42 installed). The omissions are systematic — every `lam*_definable`
   companion — so the same undercount would have recurred in any similar estimate.
4. **The under-scoped question, and it is the one that would have half-settled a cell.** The brief
   priced the relocation and the two arms, and said nothing about what repairing `preludeWitness`
   *in place* does to the theorems that make the repair meaningful. `RecGap.repair_discriminates`
   and `IffLargeAudit.joint_repair_discriminates` discriminate the repaired witness **against
   `preludeWitness`**; edit `preludeWitness` and their negative half evaporates. Doing "both arms in
   one edit" as instructed, without also preserving the pre-repair assignment, would have landed two
   `consts` cells whose anti-vacuity controls had silently become trivial — the exact failure mode
   the brief's own "check the CONCLUSION is not free" warns about, arriving from the direction it
   did not look. `preludeWitnessPt` is the fix, and it had to be part of the same edit.

Two things the brief got right that mattered: **do both arms at once** (a witness repaired only at
`Eq.rec` is refuted by `preludeWitnessPt_not_mem_interp_iffRecType`'s predecessor, and the `Iff`
half cost almost nothing once `iffRecFn` existed), and **leave `Nonempty.rec` alone** (its
`isLE = false` makes `•` correct, and the fall-through preserves that with no proof at all).

### 22.14 What to pick up first

1. **The `rules` fields at `eqIndDecl` and `iffIndDecl`** — now the only unfinished part of
   `InductOracleOK` at the two blocks whose `consts` recursor cells §15 closes. `EqRecLarge` §10.1's
   block-generic argument (`VInductDecl'.iotaRules_WF` from `D.IotaCtx env`) is still **an argument
   from the shape of the lemma, not a measurement** (§21.9 item 3, unchanged).
2. **`Iff`'s other two `consts` cells** — the type former and `Iff.intro ↦ •` — unchanged from
   §21.9 item 2, and now the only `consts` gap left at that block.
3. **Retire `preludeWitnessR` / `preludeWitnessRR`** and the two `_cnst_Eq_arm` lemmas. They are
   dead weight and, worse, they document a workaround for a trap that no longer exists; leaving them
   invites the next stream to reproduce the applied shape.
4. **`NEAudit.propSplitPreludeEnv`'s `sorryAx`.** It is the single thing standing between this
   corner and any claim at `preludeEnv` rather than at an arbitrary `L : PropSplit envF nv`.
5. If any future witness must be written in the applied `fun n us ↦ if …` shape for a reason I did
   not find, the escape hatches measured in 22.2 are, in increasing cost: state each side against a
   literal (`B` rows, `rfl`), the arm-lemma + `rw` route (`G` rows, one extra lemma), or
   `set_option maxHeartbeats 800000` (works, 8 minutes per declaration, and pollutes the build time
   of every module downstream).

### 22.15 Files touched this session

* `Lean4Lean/Theory/SetModel/PreludeSpec.lean` — +407 lines: the relocated payload, the
  η-contracted repaired `preludeWitness`, `preludeWitnessPt`, and 19 cell/control lemmas.
* `Lean4Lean/Theory/SetModel/EqRecLarge.lean` — §§1--3 + `eqRecVal`/`eqRecVal_pair` removed, one
  `export`, §8 restated at `preludeWitnessPt` and two new positive results at `preludeWitness`.
* `Lean4Lean/Theory/SetModel/IffRecLarge.lean` — §§1--3 + `iffRecVal`/`iffRecVal_single` removed,
  one `export`, §14 re-pointed, **new §15** (five theorems), §15→§16 renumbered.
* `Lean4Lean/Theory/SetModel/PreludeRecGap.lean` — §1 restated at `preludeWitnessPt`, §4.3
  re-pointed.
* `Lean4Lean/Theory/SetModel/PreludeOracle.lean` — `neOracle_eq_empty_of_not_mem` +2 hypotheses,
  `cnstOf_preludeTail` +2 bullets, §13's two refuted `∅`-statements replaced by a note.
* `docs/handoff-setmodel.md` — this section.

No new file, so no `Equiconsistency.lean` import line was needed. `Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean`, `Experimental/ConeJoin.lean`, `Theory/Inductive/*` and
`Theory/Typing/*` were not touched; `implGapWhitelist` was not touched; no git operation was run.
