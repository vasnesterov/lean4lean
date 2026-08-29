# Handoff: the inductive side — the nested constant-map repair, and the one blocker left

Successor to the previous revision of this file (the `sorry` inventory, the false
`inductDecl` branch, and the nested wall).  §§0–4 are this round; §§5–8 carry forward the
parts of the previous revision that are still true, corrected where they are not.

Everything below is either **[MC]** machine-checked (a Lean proof in this tree, named), **[EV]**
checked by evaluation (a `#eval` that fails the build on regression — a test, not a proof), or
**[SRC]** read off source without a proof.

**Build state.** `lake build Lean4Lean Lean4Lean.Verify Lean4Lean.Theory` green, 1299 jobs.
`lake build Lean4Lean.Verify.Guard`: guard 1 ✓, guard 2 ✓ (proof INCOMPLETE, unchanged),
guard 3 ✓ (54/54, unchanged).  `lake env lean scripts/sorry-census.lean` → **21**, unchanged.
No `sorry` added, no frozen file touched.

**Files.**
New, owned: **`Lean4Lean/Verify/Environment/InductR.lean`** (939 lines, **76 declarations, 0
`sorryAx`-tainted**, axioms `propext`/`Classical.choice`/`Quot.sound` only).
Edited, owned: `Verify/Environment/Basic.lean`, `Verify/Environment/Induct.lean`,
`Verify/InductFlip.lean`, `Verify/Inductive/AddDeclWF.lean` — the last three only by moving
declarations (unchanged text) plus docstring corrections; §7 has the ledger.

---

## 0. The headline

**The nested wall is down on the constant-map side, and the remaining blocker is one rule in
one file this stream does not own.**

* `AddInductStages` — the previously intended definition of `AddInduct` — is still refuted for
  a nested block.  That theorem (`TrIndDecl.not_addInductStages`, `tBlock_not_addInductStages`)
  is unchanged and still true **[MC]**.  What changed is that `AddInductStages` is no longer
  what `AddInduct` should be.
* The repair is **`AddInductStagesR`**: the same three folds, run over
  `VInductDecl'.typeConstsC K`, `ctorConstsCR R K` and `recConstsR R` — the constant lists of
  `VEnv.addInductR`, which `Theory/Inductive/NestedHead.lean` already carries with the recursor
  renaming `R.recName` threaded through.  No second mechanism was invented.
* The invariant is proved: **every constant the step adds to the map is one the translated
  declaration accounts for** (`TrIndDeclN.mem_indDeclNamesN` ∘
  `AddInductStagesR.find?_of_not_mem`, composed as `InductStepNested.find?_of_not_mem`) **[MC]**.
* The refutation re-run: `T.rec_1 ∈ indDeclNamesN [tIndType] 1` **[MC]**, so
  `TrIndDeclN.not_addInductStagesR` is inapplicable to the block that produced the finding;
  three negative controls show it still bites everywhere else **[MC]**; and the checker's own
  added-name set for that block is *exactly* `indDeclNamesN [tIndType] 1` **[EV]**.
* Non-vacuity: `InductStepNested` has a model at a real nested block with every environment
  side condition discharged — `inductStepNested_wit_closed` **[MC]** — with `NFn.rec_1`
  landing in the output map and
  `NFn.rec`/`NFn.rec_1`'s *stored kernel types* translating to the abstract ones.

**The one blocker left, exactly** (§5): `TrEnv'.wf` feeds `AddInduct.to_addInduct` to
`VDecl.WF.induct` (`Theory/Typing/Env.lean`), whose second hypothesis is
`env.addInduct' decl = some env'`.  A nested step gives `env.addInductR D K R = some env'`
instead.  That rule must become `VEnv.AddNestedB`, which needs the declaration history `ds`
that `VDecl.WF` does not carry.  `Theory/Typing/Env.lean` is another stream's file; the edit is
stated in §5 and **not made**.

---

## 1. `AddInductStagesR` and its invariant

### 1.1 The definition

```lean
def AddInductStagesR (m₁ : ConstMap) (env₁ : VEnv) (D : VInductDecl')
    (K : List Name) (R : VIndRestore) (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  ∃ mt et mc ec e₃,
    AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) (D.typeConstsC K)      m₁ env₁ mt et ∧
    AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v)   (D.ctorConstsCR R K)   mt et mc ec ∧
    AddIndConsts (fun ci => ∃ v, ci = .recInfo v)    (D.recConstsR R)       mc ec m₂ e₃ ∧
    env₂ = e₃.addIndRulesR D R
```

`K` names the auxiliary members: their type constants and constructors are **not** declared
(`typeConstsC`/`ctorConstsCR` filter them out), but their recursors **are**, under
`R.recName (mkRecName ·)` — which is exactly `mkAuxRecNameMap`'s renaming.  That third stage
is the whole repair.

Proved about it, all **[MC]**: `to_addInductR` (discharges into `VEnv.addInductR` as
`AddInductStages.to_addInduct` discharges into `addInduct'`), `.le`, `.map_wf`, `.find?_shape`,
`.defeqs`, `.find?_of_not_mem`, `.addIndTypesC`.

**Conservativity** **[MC]**: `AddInductStages.toR` and `AddInductStagesR.of_addInductStages` —
at `K = []`, `R = D.idRestore`, `D.Canonical`, the new relation *is* the old one.  So nothing
proved about the non-nested case is given up; this is a generalisation, not a rival.

### 1.2 The names, and why they are a function of the declaration

```lean
def auxRecName (types : List InductiveType) (k : Nat) : Name :=
  Lean4Lean.appendIndexAfter' (Lean.mkRecName (types.headD default).name) (k + 1)

def indDeclNamesN (types : List InductiveType) (numNested : Nat) : List Name :=
  indDeclNames types ++ (List.range numNested).map (auxRecName types)
```

That is `mkAuxRecNameMap` (`Lean4Lean/Inductive/Add.lean:898`) read back **[SRC]**: it renames
`mkRecName indName` to `appendIndexAfter' (mkRecName types[0].name) k` for
`k = 1 … numNested`, over `mainInfo.all.drop types.length`.  `indDeclNamesN_zero` **[MC]** says
the list collapses to `indDeclNames` at `numNested = 0`.

The point of the shape: the extra names depend only on `types` and `numNested`, so the
invariant does not go slack.  §3's negative controls check that.

### 1.3 `TrIndDeclN`: the translation, with the name discipline

`TrIndDecl` (`Verify/Environment/Induct.lean`) with three additions, all of them *name*
discipline — the semantic content stays in `VInductDecl'.WF`:

| clause | content |
|---|---|
| `length` | `D.types.length = types.length + numNested` — the auxiliary members are appended after the user's.  `ElimNestedInductive` **pushes** them onto `newTypes`, which starts as `types.toArray` (`Add.lean:855`, `:933`) **[SRC]**, and check C corroborates **[EV]**. |
| `companions` | `∀ j T, D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j)` — **`K` is exactly the auxiliary tail**.  Left-to-right stops a user member being dropped from the map; right-to-left makes the auxiliary members undeclared. |
| `recName_own` | a member the user wrote keeps its recursor name |
| `recName_aux` | `R.recName (mkRecName T.name) = auxRecName types (j - types.length)` — `mkAuxRecNameMap`, as a clause |

plus `TrIndCtorR`, which compares against `R.ctorName C.name` and against the **restored**
stored type `C.typeR D R j` — the type `Environment.addInductive` actually publishes, after
`restoreNested` rewrote the auxiliary heads back.  `trCtors` is staged over
`env.addIndTypesC D K`, which is exactly the environment `AddInductStagesR`'s first stage
produces.

`TrIndDecl.toN` **[MC]**: at `numNested = 0`, `K = []`, `R = D.idRestore` (and `D.Canonical`),
`TrIndDecl` gives `TrIndDeclN`.  Conservativity on the syntactic side.

### 1.4 The invariant, stated

> **Every constant the step adds to the map is one the translated declaration accounts for.**

Two halves, both **[MC]**:

* `AddInductStagesR.find?_of_not_mem` — outside `D.allNamesCR R K`, `m₂.find? n = m₁.find? n`.
  Inherited from `AddIndConsts.find?_of_not_mem`, which is list-generic.  This is what makes
  the relation a **definition of the output map**, not a check on it.
* `TrIndDeclN.mem_indDeclNamesN` — `D.allNamesCR R K ⊆ indDeclNamesN types numNested`.

Composed: `InductStepNested.find?_of_not_mem`.  `InductStepNested.find?_shape` carries the
safety gate (`AddDeclWF.lean` §1) through unchanged: every constant the step declares is one of
the three inductive shapes and is `safe`-tagged.

---

## 2. `InductStepNested`: the obligation, and two corrections it embodies

```lean
def InductStepNested (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) (numNested : Nat) : Prop :=
  ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore),
    TrIndDeclN venv lp np types false numNested D K R ∧
    (∃ et, venv.addIndTypes D = some et) ∧
    D.WF venv ∧
    AddInductStagesR m venv D K R m' venv'
```

**Correction 1 — it is `WF`, not `WFC`.**  The first draft of this obligation used
`VInductDecl'.WFC venv K` (`Theory/Inductive/CompanionResolve.lean`'s G1 re-staging).  That is
**wrong here** and does not typecheck at the witness.  `D` is the *auxiliary* block, and
`AddInductive.run` checks it in a scratch environment where **all** its type constants,
auxiliary ones included, are declared — which is `WF.ctors`' staging (`env.addIndTypes D`), not
`WFC.ctors`' (`addIndTypesC D K`, where a companion member's own constructor type is not even
well-formed).  `WFC` exists for the *other* companion shape: a block re-declaring a type
already in the environment (`fooCompDecl`).  The nested path never does that — `mkUniqueName`
gives the auxiliary members fresh `_nested.*` names.  This matches `VEnv.AddNestedB`, which
also takes `D.WF env`.

**Correction 2 — the vacuity guard has to be a conjunct.**  `WF.ctors`' premise is
`env.addIndTypes D = some env₁`, which is `none` on a name collision; that is precisely the
mechanism by which `fooComp_WF` holds vacuously and `fooComp_inconsistent` bites.
`AddInductStagesR` does **not** supply it (it only declares the non-companion types — that is
the whole point of `typeConstsC`).  So the success is an explicit conjunct, and
`InductStepNested.ctors_nonvacuous` **[MC]** reads it back as an inhabited obligation.  The
non-nested `InductStepSafe` got this for free from `AddInductStages.addIndTypes`; the nested
one does not, and silently keeping the old shape would have re-opened the `fooComp` hole.

Also **[MC]**: `.le`, `.map_wf`, `.find?_of_not_mem`, `.find?_shape`, `.induct_premises`.

---

## 3. The refutation, re-run

`tBlock_not_addInductStages` (now in `InductR.lean`, text unchanged) says: for
`inductive Box (A : Type) | mk : A → Box A` then `inductive T | mk : Box T → T`, no `D` with
`TrIndDecl … [tIndType] false D` stands in `AddInductStages` between a map without `T.rec_1`
and one with it.  **Still true, still proved.**

Its nested-aware counterpart is `TrIndDeclN.not_addInductStagesR`, with side condition
`n ∉ indDeclNamesN types numNested`.  At the block:

| name | statement | verdict |
|---|---|---|
| `trec1_mem_indDeclNamesN` **[MC]** | `T.rec_1 ∈ indDeclNamesN [tIndType] 1` | **the wall is gone** — the side condition is `False`, so the refutation is inapplicable |
| `tBlock_not_refuted_at_trec1` **[MC]** | the same, packaged with every other hypothesis of the refutation available | there is no derivation of `¬ AddInductStagesR` by this route |
| `trec1_not_mem_indDeclNamesN_zero` **[MC]** | `T.rec_1 ∉ indDeclNamesN [tIndType] 0` | **negative control**: at `numNested = 0` the wall is intact.  The repair is gated on `numNested`, not a blanket permission. |
| `trec2_not_mem_indDeclNamesN` **[MC]** | `T.rec_2 ∉ indDeclNamesN [tIndType] 1` | **negative control**: a *second* auxiliary recursor is still refuted at `numNested = 1` |
| `foo_not_mem_indDeclNamesN` **[MC]** | `Foo ∉ indDeclNamesN [tIndType] n`, for every `n` | **negative control**: the auxiliary family does not leak; the map is still pinned outside the block.  Via `auxRecName_tIndType`, which computes the family to `T.rec_1, T.rec_2, …`. |

And against the checker itself:

* **check C** **[EV]** — the set of constants `addDecl` adds for the `T` block is **exactly**
  `indDeclNamesN [tIndType] 1`.  Measured: `added = [T.mk, T.rec_1, T, T.rec]`,
  `expected = [T, T.mk, T.rec, T.rec_1]`.  Both inclusions are checked, so the name list is a
  *definition* of the added set, not a permissive over-approximation.
* **check C′** **[EV]** — and `indDeclNamesN [tIndType] 0` does **not** cover it, so check C is
  not vacuous and the original finding has not regressed.
* **check D** **[EV]** — the shapes: `T ↦ .inductInfo`, `T.mk ↦ .ctorInfo`,
  `T.rec, T.rec_1 ↦ .recInfo`, all `isUnsafe = false`, all with `all = [T]`.  That is
  `find?_shape` plus the safety gate, at a block with an auxiliary recursor.

---

## 4. Non-vacuity: a closed model at a real nested block

The witness is `Theory/Inductive/NestedBuild.lean` §6's block, which already had the
declaration side and Lean-kernel cross-checks and lacked only the constant map:

```
inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α
inductive NFn            | node : PFn NFn → NFn
```

with `nfnAux`/`nfnK`/`nfnRestore` the auxiliary block, restoration and companion list, and
`nfnAux_WF` already proved (in *any* environment, with `binders_indep` discharged by the
substitution theorem rather than by emptiness).

The three constant lists, by `rfl` **[MC]** — read them:

```lean
nfnAux.typeConstsC nfnK          = [(NFn,      ⟨0, Sort 1⟩)]
nfnAux.ctorConstsCR nfnRestore nfnK = [(NFn.node, ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)]
nfnAux.recConstsR nfnRestore     = [(NFn.rec,   ⟨1, recTypeR … 0⟩),
                                    (NFn.rec_1, ⟨1, recTypeR … 1⟩)]
```

One type constant, one constructor constant — the companion `_nested.PFn_1` and its
constructor `_nested.PFn_1.mk` are declared nowhere — and **two** recursors, the second
renamed.  That is the finding, accommodated.

| name | content |
|---|---|
| `tr_nodeType`, `tr_recType0`, `tr_recType1` **[MC]** | Lean's **stored** types for `NFn.node`, `NFn.rec` and `NFn.rec_1` translate (`TrExprS`) to `typeR`/`recTypeR … 0`/`recTypeR … 1`.  The `Expr` side is spliced from the kernel by `exprOf%` — the `Expr`-side counterpart of `Theory/Meta.lean`'s `vconst(type_of% …)` — so it cannot drift from a hand transcription. |
| `trIndDeclN_wit` **[MC]** | the syntactic half, including `recName_aux`: `nfnRestore.recName (mkRecName _nested.PFn_1) = auxRecName [nfnIndType] 0 = NFn.rec_1` |
| `addInductStagesR_wit` **[MC]** | all four stages fire; the output map holds `.recInfo` at `NFn.rec` **and at `NFn.rec_1`**, and holds **nothing** at `_nested.PFn_1` |
| `inductStepNested_wit` **[MC]** | the join: `TrIndDeclN` ∧ `addIndTypes` success ∧ `nfnAux_WF` ∧ `AddInductStagesR`, at one block |
| `inductStepNested_wit_closed` **[MC]** | the same with **no hypotheses on the environment** beyond the declaration history (`VEnv.empty.addInduct' pfnDecl = some env₂`) and any well-formed empty constant map — the freshness side conditions are discharged, not assumed |

So all three conjuncts of `InductStepNested` meet at one nested block, with `NFn.rec_1` in the
output map, and the `WF` conjunct is a real obligation rather than an `absurd`.

---

## 5. The blocker, stated exactly (and not acted on)

`TrEnv'.induct` is consumed by `TrEnv'.wf` / `TrEnv'.wf_noUnsafe`
(`Verify/Environment/Basic.lean`, owned) as

```lean
| induct h1 h2 _ ih => have ⟨_, H⟩ := ih; exact ⟨_, H.decl <| .induct h1 h2.to_addInduct⟩
```

and `VDecl.WF.induct` (`Theory/Typing/Env.lean:46`, **not owned**) is

```lean
  | induct :
    decl.WF env →
    env.addInduct' decl = some env' →
    VDecl.WF env (.induct decl) env'
```

With `AddInduct := fun m₁ env₁ D m₂ env₂ => ∃ K R, AddInductStagesR m₁ env₁ D K R m₂ env₂`,
`to_addInduct` yields `∃ K R, env₁.addInductR decl K R = some env₂`.  For a nested block that
is **not** `addInduct'` of any `VInductDecl'` — the constant lists differ by construction — so
the rule has to be generalised.

**What it must be generalised to, and why not the obvious thing.**  Replacing the hypothesis by
`∃ K R, env.addInductR decl K R = some env'` is *unsound*: with `K` and `R` free, a step could
drop constants or rename them arbitrarily.  The sound form is `VEnv.AddNestedB`
(`Theory/Inductive/NestedBuild.lean`), which pins them via `D.Built R K ds env occ` — and that
quantifies over the declaration **history** `ds`, which `VDecl.WF env d env'` does not carry
(`VEnv.WF'` does).  So the change is at the `VDecl.WF`/`VEnv.WF'` boundary, which is a design
decision in another stream's file.  `docs/handoff-nested-build.md` §10 item 4 is the same item
seen from the Theory side, and it says the same thing: *`AddNestedB` should be the clause, with
`AddNestedB.toAddNested` bridging.*

**Nothing was edited in `Theory/Typing/Env.lean` or `Theory/VDecl.lean`.**

---

## 6. The flip: current file set

**Verdict: still not landable within this stream's files, and the set grew by one.**  Do not
half-land it.

| # | file | owned? | what the flip does to it |
|---|---|---|---|
| 1 | `Verify/Environment/Basic.lean` | **yes** | `inductive AddInduct` → `def AddInduct := ∃ K R, AddInductStagesR …`; `to_addInduct`; the `induct` arms of `TrEnv'.wf` and `TrEnv'.wf_noUnsafe` |
| 2 | `Verify/Environment/Lemmas.lean` | **yes** | `Aligned.addInduct`'s `nomatch H`; `TrEnv'.of_value`'s induct arm → `AddInductStagesR`'s analogue of `AddInductStages.of_value_arm` |
| 3 | **`Theory/Typing/Env.lean`** | **no** | **new this round** — `VDecl.WF.induct` must accept the nested step (§5) |
| 4 | `Verify/SafeFragment.lean` | no | `AddInduct.le`'s `nomatch H` → `AddInductStagesR.le` (one line) |
| 5 | `Verify/Environment/Extension.lean` | no | delete `TrEnv'.no_inductInfo` (becomes false) |
| 6 | `Verify/TypeChecker/Reduce.lean` | no | `TrEnv'.find?_shape`, `TrEnv'.defeqs_shape` gain disjuncts; `Aligned.addInductStages` → the `R` version and **move** it to (2); delete `TrEnv.not_inductInfo`/`.not_ctorInfo`/`.not_recInfo`/`VContext.not_inductInfo`; delete-or-`sorry` `reduceProjCore_none`/`reduceProjCore.WF` |
| 7 | `Verify/TypeChecker/WHNF.lean` | no | `inductiveReduceRec_eq_none` dies |
| 8 | `Verify/TypeChecker/InferType.lean` | no | `inferProj_always_throws` dies |
| 9 | `Verify/TypeChecker/IsDefEq.lean` | no | `tryEtaStructCore_never_true` and `isDefEqUnitLike_never_true` die |

**9 files, 7 unowned.**  Previous measurement: 8 files, 6 unowned.  Everything the flip needs
on rows 1–2 and 4 is now in hand (`AddInductStagesR.{le,map_wf,find?_shape,defeqs,to_addInductR}`);
row 3 is the design change of §5; rows 5–9 are the human's standing ruling, unchanged.

The order that makes sense is unchanged from the previous handoff except that step 1 is now
done: **(1) fix `AddInduct` for nested blocks — done**; (2) settle row 3 with the
`Theory/Typing` stream; (3) flip once, as one coordinated commit; (4) take the nine
`Verify/TypeChecker/` statements.

**Standing ruling untouched.**  Nothing here changes the ι-reduction / projection-reduction /
structure-eta calculus, so the nine `Verify/TypeChecker/` statements stay as they are.

---

## 7. Ledger of edits to owned files

| file | change |
|---|---|
| `Verify/Environment/InductR.lean` | **new**, 939 lines, 76 declarations, 0 `sorryAx` |
| `Verify/Environment/Basic.lean` | received `AddIndConsts.constants_of_mem`, `.find?_of_not_mem`, `AddInductStages.find?_of_not_mem`, `.addIndTypes` **moved unchanged** from `Verify/InductFlip.lean`, so that `Induct.lean`/`InductR.lean` can use them without depending on the type-checker layer; `AddInduct`'s docstring corrected (it named `AddInductStages` as the intended definition) |
| `Verify/InductFlip.lean` | those four declarations removed (they are re-exported through `Basic.lean`, which it imports); nothing else |
| `Verify/Environment/Induct.lean` | received `indDeclNames`, `exists_getElem?_of_lt`, `TrIndDecl.mem_indDeclNames`, `TrIndDecl.not_addInductStages` **moved unchanged** from `Verify/Inductive/AddDeclWF.lean`, for the same reason |
| `Verify/Inductive/AddDeclWF.lean` | those four declarations removed; the `T`/`Box` block literals, `trec1_not_declared`, `tBlock_not_addInductStages` and check B **moved unchanged** to `InductR.lean`; imports `InductR` instead of `Induct`; §2's docstring gains a **RESOLVED** note and §3's a **SUPERSEDED for nested blocks** note.  `InductStepSafe` and `AddInductiveObligation` are untouched — they remain the *non-nested* obligation |

No unowned file was edited.  `Verify/TypeChecker/Reduce.lean` was red for part of this session
(another stream's uncommitted work); it was not touched, and it is green now.

---

## 8. Carried forward from the previous revision, still true

* **The `sorry` inventory.** 21 tree-wide, unchanged.  The five tainted declarations in
  `Verify/Inductive/Add.lean` (`AddInductive.M.WF.{ensureType,whnf,field_step,elim_field_step,positivity_none}`)
  are tainted *by inheritance* through `Verify/TypeChecker/{InferType,IsDefEq,WHNF}.lean`.
  Nothing in this stream's files adds taint.
* **`addDecl.WF`'s `inductDecl` branch is false, not open.**  `addDecl_inductDecl_post_false`,
  `addDecl_inductDecl_WF_false` **[MC]**, check A **[EV]**.  Unchanged.
* **The `.unsafe` hole.**  `unsafe_induct_unreachable` **[MC]**: `TrEnv' .unsafe` has no rule
  at all for an unsafe inductive, and the flip does not close it.  Independent of everything
  above; still needs a design decision between a `TrEnv'` rule that is the inductive analogue
  of `unsafeDef`, and a `VEnvs.WF` that does not demand a model at `.unsafe`.
* **`Aligned.addInduct`'s statement**, corrected in a previous round (named environments, not
  auto-bound implicits), is unchanged and is what the flip's arm must be proved against.
* **Not proved, and not attempted this round:** the flip; `AddInductiveObligation` /
  its nested counterpart as a refinement of `Environment.addInductive` (nothing in `Verify/`
  refines the top-level wrapper yet, which is why §3's checker-side facts are `[EV]`); the
  `.unsafe` rule; the nine `Verify/TypeChecker/` declarations; `Theory/Typing/Env.lean` (§5).
