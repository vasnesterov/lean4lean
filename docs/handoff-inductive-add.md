# Handoff: the inductive side — the nested step is stateable now, and the blocker moved

Successor to the previous revision (which named the declaration history `ds` as the one
remaining blocker).  §§0, 5–8 are this round; §§1–4 carry forward **unchanged** and are still
true.

Everything below is either **[MC]** machine-checked (a Lean proof in this tree, named), **[EV]**
checked by evaluation (a `#eval` that fails the build on regression — a test, not a proof), or
**[SRC]** read off source without a proof.

**Build state.** All 96 `Lean4Lean/Theory/**` modules green, plus `Lean4Lean.Verify.Soundness`,
`.SafeFragment`, `.Bridge`, `.InductFlip`, `.Inductive.AddDeclWF`, `.Environment.*`.
(`Theory/Typing/HeadRedStuck.lean` and `Verify/Typing/{ProjSkip,StructureUniq}.lean` went red
and green again during the session under *other* streams' edits; they were not touched.)
`lake env lean scripts/sorry-census.lean` → **20**, unchanged.  No `sorry` added, no frozen
file touched, no unowned file edited.

**Files.**
New, owned: **`Lean4Lean/Theory/Inductive/Restore.lean`** (360 lines, 39 declarations) and
**`Lean4Lean/Theory/Inductive/NestedOrdered.lean`** (179 lines, 9 declarations); both
`sorryAx`-free, axioms `propext`/`Classical.choice`/`Quot.sound` only.
Edited, owned: `Theory/Inductive/{Decl,Lemmas,Nested,NestedHead,NestedBuild,Companion,CompanionResolve}.lean`,
`Theory/Typing/Env.lean`, `Verify/Environment/{Basic,InductR}.lean`.  §7 has the ledger.

---

## 0. The headline

**The previous handoff's blocker was real but was only half the obstruction, and the half it
named is now gone.**

* **The declaration history is not needed.**  `ds : List VDecl` was threaded through
  `VIndRestore.Faithful`, `VNestedOcc.Occurs`, `VInductDecl'.Built` and `VEnv.AddNested{,B}`
  for exactly one purpose: `hist : VDecl.induct N.decl ∈ ds`, "this block was declared
  earlier".  That is now **`VInductDecl'.Declared`** — `∃ env₀ env₁, env₀.addInduct' D = some
  env₁ ∧ env₁ ≤ env` — a statement about the environment alone, and a history discharges it
  (`VEnv.WF'.declared` **[MC]**).  Every one of those five definitions has lost its `ds`
  parameter, and both end-to-end witnesses were re-proved through the new clause **[MC]**.
* **The step is now nameable at `Theory/Typing/Env.lean`.**  It was not: `VEnv.addInductR` and
  `VIndRestore.Faithful` lived in `Theory/Inductive/NestedHead.lean`, which is *downstream* of
  `Env.lean` (`Env` ← `DeltaUnique` ← `Nested` ← `Companion` ← `CompanionResolve` ←
  `NestedHead`), so the rule could not have been written even with `ds` solved.  The
  definitional core moved **verbatim** upstream into `Theory/Inductive/Restore.lean`; the
  `example` at the end of `Env.lean`'s new section is the machine-checked proof that
  `VEnv.AddNestedStep` elaborates there **[MC]**.
* **`npJ` was an under-constrained parameter, and is now pinned.**  `VEnv.AddNested` takes
  `npJ : Nat → Nat`, the parameter count the companion is presented at; existentially
  quantifying it (which a `VDecl.WF` rule must) would have let a companion be presented at a
  *wrong* instantiation of the block it claims to be, with its recursor's minor premises then
  matching nothing — `fooComp_inconsistent`'s failure mode by another route.
  `Faithful.ctors_complete` now also asserts `npJ j = D₀.np`, `D₀` being the block the
  environment holds, so `VEnv.AddNestedStep := ∃ npJ, AddNested …` gives a caller nothing
  **[MC]**.
* **The rule text is written, machine-checkable, and *not added*** — see §5 for exactly why,
  and `Theory/Typing/Env.lean`'s new section docstring for the text.
* **Two theorems now stand where "the history" used to**, and they are the actual content:
  `VEnv.addInductR_ordered` (the restored types are well typed) and a repair of
  `Theory/Typing/DeltaUnique.lean`'s freshness argument, **which is false for a nested block**
  — `VEnv.iotaRulesR_major_not_fresh` **[MC]**, with a model
  (`nfn_companion_key_not_fresh` **[MC]**).

**Non-vacuity.**  `VEnv.AddNestedStep`, the premise the rule would take, has models at both
nested witnesses: `ntreeAux_AddNestedStep` and `nfnAux_AddNestedStep` **[MC]**, via
`AddNestedB.toAddNestedStep` **[MC]**.  So the rule would not be vacuous, and the two remaining
theorems are the only thing between it and the tree.

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

## 5. The blocker, restated — and it is **not** the declaration history

The previous revision said: *`VDecl.WF.induct`'s hypothesis is `env.addInduct' decl = some
env'`; a nested step gives `addInductR`; the generalisation must be `VEnv.AddNestedB`, which
needs `ds`, which `VDecl.WF` does not carry; that is a design change in another stream's file.*

The first two clauses are still true.  **The rest was wrong or incomplete**, and this is the
correction.

### 5.1 What is now done (owned, green)

| item | status |
|---|---|
| `ds` in `Faithful`/`Occurs`/`Built`/`AddNested`/`AddNestedB` | **gone**, replaced by `VInductDecl'.Declared` **[MC]** |
| a history discharges `Declared` | `VEnv.WF'.declared` **[MC]** |
| `addInductR`/`Faithful` nameable at `Env.lean` | **yes** — moved to `Theory/Inductive/Restore.lean`; `example` in `Env.lean` **[MC]** |
| `npJ` free ⇒ under-constrained | **closed**: `ctors_complete` pins `npJ j = D₀.np` **[MC]** |
| the rule's premise is inhabited | `ntreeAux_AddNestedStep`, `nfnAux_AddNestedStep` **[MC]** |
| conservativity at `K = []` | `VEnv.AddNested_nil` (unchanged), `addInductR_ordered_nil` **[MC]** |

The rule, in full, as it would be added to `VDecl.WF` (the text also sits in `Env.lean`'s
section docstring, where it is next to the two reasons it is not there):

```lean
  | inductNested {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore} :
    VEnv.AddNestedStep env D K R env' →
    VDecl.WF env (.induct D) env'
```

### 5.2 Obstruction 1 — `VEnv.addInductR_ordered`, a theorem nobody had named

`VEnv.WF.ordered` (`Theory/Typing/EnvLemmas.lean`) extracts `Ordered` from `VEnv.WF`, and its
`induct` arm is `addInduct_WF`, i.e. `addInduct'_ordered_final`.  The nested arm needs

    env.Ordered → env.addInductR D K R = some env' → env'.Ordered

and that is **not bookkeeping**.  `Ordered` (`Theory/Typing/Lemmas.lean`) records that every
constant's type was `IsType` at its staging environment and every `defeq` was `WF` when added.
`addInductR` declares a user constructor at `C.typeR D R j` — in which a field the auxiliary
block stored as `_nested.List_1 α` has been rewritten back to `List (Tree α)` — and the
recursors at `D.recTypeR R j`, and emits `D.iotaRulesR R`.  None of that follows from
`D.WF env`, which is about the *auxiliary* block's own stored types.  **This is the nested
soundness theorem**, and it is what actually stands between here and the rule.

`Theory/Inductive/NestedOrdered.lean` does the part that is bookkeeping and names the rest:

* `VEnv.addInductR_stages` **[MC]** — the three constant stages and the rule fold, the
  `addInduct'_stages` analogue (`allConstsCR` is a *left*-associated append of three).
* `VEnv.addInductR_ordered` **[MC]** — `Ordered env'` from four staged obligations, in
  `addInduct'_ordered`'s shape.
* `VEnv.addInductR_typeConstsC_wf` **[MC]** — the first of the four is **free**: `typeConstsC`
  only *removes* members, so the type constants' stored types are covered by `D.WF env`
  verbatim.
* `VEnv.addInductR_ordered'` **[MC]** — hence `Ordered` from exactly **three** obligations:
  **(A)** a declared constructor's *restored* stored type is a type at the environment holding
  the step's type constants; **(B)** each *renamed* recursor's *restored* type is a type at the
  environment holding those and the constructors; **(C)** each *restored* ι-rule is a
  well-formed `VDefEq` there.  They are to be discharged from `Faithful` + `D.WF env`.
* `VEnv.addInductR_ordered_nil` **[MC]** — at `K = []`, `R = idRestore`, `D.Canonical` the three
  collapse to what `addInduct'` already discharges.  So they are about the *restoration*, not
  about inductives, and nothing has been strengthened.

### 5.3 Obstruction 2 — `DeltaUnique`'s freshness argument is **false** for a nested block

`Theory/Typing/DeltaUnique.lean`'s `keys_induct` (the `induct` arm of `VEnv.WF'.keys`) turns on

> `hfresh` — every name in the key of a rule the step emits is absent from `env`.

For `addInduct'` that is immediate: a key is `[I_j.rec, C.name]` and the step declares both.
For a nested step the key of a **companion** member's ι-rule is
`[R.recName I_j.rec, R.ctorName C.name]` (`VInductDecl'.key_iotaRuleR`), and the second
component is the constructor of the block the environment **already holds**.
`VIndRestore.Faithful.ctor_agree` says so in as many words:

* `VEnv.iotaRulesR_major_not_fresh` **[MC]** — under `Faithful`, a companion ι-rule's major
  name is `env.contains`.
* `VEnv.mem_key_iotaRuleR_major` **[MC]** — and it really is in the key.
* `InductiveDeclExamples.nfn_companion_key_not_fresh` **[MC]** — the model: `nfnAux`'s
  companion rule is keyed `[NFn.rec_1, PFn.mk]`, and `env₂` holds `PFn.mk`.

The freshness that *is* available is of the key's **head** (`recName_mem_allNamesCR` puts the
renamed recursor among the step's own constants, and `addConstList` succeeded), so the nested
arm is a different argument, not a transcription.  Whether `KeyMajorUnique`/`KeyHeadDelta`
survive it is **not settled here** and is the next thing to check on that side.

### 5.4 Obstruction 3 — four one-line case additions in two unowned files

Measured, not guessed: a clone constructor was added to `VDecl.WF`, the tree built, every
`Alternative \`inductNested\` has not been provided` collected, patched, rebuilt, until
`Lean4Lean.Theory` (96 modules) and `Verify.{Soundness,SafeFragment,Bridge}` were green again.
The **complete** list is nine sites in five files:

| file | sites | owned? | what the nested case needs |
|---|---|---|---|
| `Theory/Typing/EnvLemmas.lean` | 1 (`VEnv.WF.ordered`) | **yes** | `addInductR_ordered` — §5.2 |
| `Theory/Typing/DeclRules.lean` | 1 (`WF'.defeq_isDeclRule`) | **yes** | `addInductR_defeqs_iff` + `IsDeclRule` for `iotaRulesR` |
| `Theory/Inductive/Nested.lean` | 5 (`VDecl.WF.le`, `WF'.exists_addInduct'`, `WF'.induct_eq_of_type_name` ×2, `WF'.iotaRule_provenance`) | **yes** | `addInductR_le` (exists); the rest are about `addInduct'`-provenance and need restating |
| `Theory/Typing/DeltaUnique.lean` | 3 (`WF'.defEqHeads`, `WF'.keys`, `WF'.iotaTypes`) | **no** | §5.3 |
| `Theory/Typing/PatternRules.lean` | 1 (`WF'.ruleShape`) | **no** | `ruleShape_inductR` |

Nothing in `Verify/` case-splits on `VDecl.WF`; `Verify.Soundness` built green throughout the
probe.  The probe was then **fully reverted** (`git checkout`), including the two unowned
files.

So the ask on the unowned side is four `| inductNested … =>` arms — but they are *not* one-line
until §5.2 and §5.3 are done, which is why the rule is not added.

---

## 6. The flip: current file set, and why it still cannot land

**Verdict: unchanged — not landable, and it is now clear that it is not landable for a second,
independent reason.**

| # | file | owned? | what the flip does to it |
|---|---|---|---|
| 1 | `Verify/Environment/Basic.lean` | **yes** | `inductive AddInduct` → `def AddInduct := ∃ K R, AddInductStagesR …`; `to_addInduct`; the `induct` arms of `TrEnv'.wf`/`.wf_noUnsafe` |
| 2 | `Verify/Environment/Lemmas.lean` | **yes** | `Aligned.addInduct`'s `nomatch H`; `TrEnv'.of_value`'s induct arm |
| 3 | `Theory/Typing/Env.lean` | **yes** (this round) | the `inductNested` rule — blocked by §5.2/§5.3, **not** by ownership |
| 4 | `Verify/SafeFragment.lean` | no | `AddInduct.le`'s `nomatch H` → `AddInductStagesR.le` (one line) |
| 5 | `Verify/Environment/Extension.lean` | **yes** | delete `TrEnv'.no_inductInfo` (becomes false) |
| 6 | `Verify/TypeChecker/Reduce.lean` | no | shape lemmas gain disjuncts; four deletions; two delete-or-`sorry` |
| 7 | `Verify/TypeChecker/WHNF.lean` | no | `inductiveReduceRec_eq_none` dies |
| 8 | `Verify/TypeChecker/InferType.lean` | no | `inferProj_always_throws` dies |
| 9 | `Verify/TypeChecker/IsDefEq.lean` | no | `tryEtaStructCore_never_true`, `isDefEqUnitLike_never_true` die |

**Rows 6–9 are the human's standing ruling** (those nine statements stay as theorems), and they
are proved *by the emptiness of `AddInduct`*.  Giving `AddInduct` constructors makes them
false and their files red, and this stream neither owns them nor may take that decision.  So
the flip is gated on a decision, not only on proofs — and independently on §5.2/§5.3, which
gate row 3.  **The order is: (i) `addInductR_ordered`; (ii) the `DeltaUnique` repair; (iii)
row 3 plus the nine case arms of §5.4, as one commit; (iv) bring rows 6–9 to the human.**

---

## 7. Ledger of edits to owned files

| file | change |
|---|---|
| `Theory/Inductive/Restore.lean` | **new**, 360 lines, 39 declarations.  `VIndRestore`, `idRestore`, `tyAppR`/`tyAppR'`/`ctorAppR`, all of Part 2's restored recursor construction, `iotaRulesR`, `recConstsR`, `ctorConstsCR`, `allConstsCR`, `addIndRulesR`, `addInductR`, `instAt`, `Faithful`, `AddNested`, **moved verbatim** from `NestedHead.lean`; `tyAppH` + its two conservativity lemmas from `CompanionResolve.lean`; `typeConstsC` from `Companion.lean`.  New: `VEnv.AddNestedStep`, and the `npJ j = D₀.np` clause in `Faithful.ctors_complete` |
| `Theory/Inductive/NestedOrdered.lean` | **new**, 179 lines, 9 declarations: §5.2's factoring and §5.3's refutation |
| `Theory/Inductive/Decl.lean` | received `VInductDecl'.Declared`, `.mono` |
| `Theory/Inductive/Lemmas.lean` | received `Declared.constants_type`, `.constants_ctor`, `.allNames_nodup` |
| `Theory/Inductive/Nested.lean` | received `VEnv.WF'.declared` |
| `Theory/Inductive/NestedHead.lean` | the moved declarations removed (a pointer note in their place); `Faithful` lost `ds`, gained the `npJ` clause; `AddNested`/`AddNested_nil`/`AddNested_keys_declared` lost `ds`; `ntreeRestore_faithful` re-proved through `Declared` |
| `Theory/Inductive/NestedBuild.lean` | `Occurs`/`Built`/`AddNestedB` lost `ds`; `Occurs.hist` is now `Declared`; `Built.toFaithful` discharges the `npJ` clause by `rfl`; received `AddNestedB.toAddNestedStep`, `ntreeAux_AddNestedStep`, `nfnAux_AddNestedStep`, `nfn_companion_key_not_fresh` |
| `Theory/Inductive/{Companion,CompanionResolve}.lean` | `typeConstsC` / `tyAppH`+2 removed (moved, with a pointer note); nothing else |
| `Theory/Typing/Env.lean` | imports `Theory.Inductive.Restore`; new section docstring carrying the `inductNested` rule text and the two reasons it is not added; the `example` that machine-checks nameability.  **The inductive itself is unchanged.** |
| `Verify/Environment/{Basic,InductR}.lean` | docstring corrections only: both said the blocker is the declaration history and that it was the *only* one |

No unowned file was edited.  The `VDecl.WF` probe of §5.4 was reverted in full.

---

## 8. Carried forward from the previous revision, still true

* **The `sorry` inventory.** **20** tree-wide, unchanged this round.  The five tainted declarations in
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
* **`addDecl.WF` is still false at `inductDecl`.**  It is one of the 20, and closing it
  honestly was contingent on the flip landing.  It did not.  `Verify/Inductive/AddDeclWF.lean`'s
  drafted replacement obligation is untouched.
* **Not proved, and not attempted this round:** the flip; `AddInductiveObligation` /
  its nested counterpart as a refinement of `Environment.addInductive` (nothing in `Verify/`
  refines the top-level wrapper yet, which is why §3's checker-side facts are `[EV]`); the
  `.unsafe` rule; the nine `Verify/TypeChecker/` declarations; `Theory/Typing/Env.lean` (§5).
