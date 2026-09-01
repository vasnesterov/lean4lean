> **Superseded in part by `docs/handoff-nested-build.md`.**  §7.1 (the abstract
> `replaceIfNested`), §5's `BindersIndep` item, §5's positivity item and §5's universe-count
> item are addressed there; §1–§4 and §3's three refutations stand unchanged.

# The nested head, spent: `restoreNested` as a parameter — and three corrections

Successor to `docs/handoff-nested-head.md`.  Everything new is in
**`Lean4Lean/Theory/Inductive/NestedHead.lean`** (new file, ~1200 lines, **no `sorry`**, every
theorem on `[propext, Quot.sound]` or a subset; only the two theorems that go through
`Exists.choose` also use `Classical.choice`).  One other file was edited: a false note in
`Lean4Lean/Theory/Inductive/Decl.lean` (§6).  No frozen file was touched.
`lake build Lean4Lean.Theory.Inductive.NestedHead` is green.

---

## 0. Bottom line

| question | answer |
|---|---|
| Is G4 repaired? | **Yes.** `iotaLhsR`/`ihValuesR`/`iotaRuleR` thread the recursor renaming *and* the constructor renaming; `VEnv.addInductR` builds constants and rules from one and the same restoration. |
| Is the "declared = emitted" invariant stated and proved? | **Yes.** `VInductDecl'.iotaRulesR_key_declared` and `VEnv.addInductR_key_declared`.  Same shape as the `Verify/` side's `AddInductStages.iotaRule_declared`. |
| Is the head generalised? | **Yes**, and conservatively: every restored construction equals its `Decl.lean` original at `D.idRestore` (`recTypeR_id`, `iotaRuleR_id`, `addInductR_eq_addInduct'`, …). |
| Does a real nested block go through? | **Yes, end to end.**  `ntreeAux_AddNested`: `Tree α` with `node : α → List (Tree α) → Tree α`, well-formed, canonical, restoration faithful, step succeeds. |
| Is the restored output *right*? | **Machine-checked against Lean's own kernel.**  `ntreeAux_recTypeR_0/_1` are the types of `NTree.rec` and `NTree.rec_1`; `ntreeAux_iotaLamR_0/_1/_2` are the three reduction rules Lean actually **stores**. |
| Does `resolveC` model `restoreNested`? | **No — refuted.**  §3. |
| Do the companion guards constrain a nested block? | **No.**  `CompanionShape` vacuous; `CompanionComplete` and `CompanionSound` *false*.  §3. |
| Is G1's re-staging right? | **No** — for a nested block it makes `WF.ctors` unsatisfiable.  §3. |
| Is `fooComp_inconsistent` still live? | **Yes.**  The unsoundness is real; only the guard that rules it out changes name (`VIndRestore.Faithful.ctors_complete`).  All `CompanionResolve.lean` witnesses re-elaborate. |

---

## 1. The correction that reorganises everything

`docs/handoff-nested-companion.md` and `docs/handoff-nested-head.md` model a nested block as
*the user's block with `List` as an extra member whose type constant is already declared* — the
"companion".  `Lean4Lean/Inductive/Add.lean` does something else, and the difference is not
cosmetic.

For `inductive Tree (α : Type u) | node : α → List (Tree α) → Tree α`,
`ElimNestedInductive.run` produces

```
_nested.List_1      : ∀ (α : Type u), Type u
_nested.List_1.nil  : ∀ (α : Type u), _nested.List_1 α
_nested.List_1.cons : ∀ (α : Type u), Tree α → _nested.List_1 α → _nested.List_1 α
Tree                : ∀ (α : Type u), Type u
Tree.node           : ∀ (α : Type u), α → _nested.List_1 α → Tree α
```

Three things to read off this, each of which contradicts the companion model:

* **The auxiliary member carries the *block's* parameter telescope**, `[α : Type u]`, not
  `List`'s.  It is a *fresh* type of a *fresh* name.
* **`_nested.List_1.cons`'s first field is recursive into `Tree`.**  `List`'s parameter
  position has become a recursive position — that *is* nested induction.  `List`'s own `cons`
  has a non-recursive first field.
* **The auxiliary block is an ordinary mutual inductive.**  `AddInductive.run` checks it as it
  stands; `VInductDecl'` expresses it with no new machinery and `VInductDecl'.WF` is the right
  predicate for it.

Restoration acts *afterwards*, on **what is emitted**: `Environment.addInductive`'s final loop
ranges over the user's `types` only, so the auxiliary type constant and its constructor
constants are **never added**; the user's constructor types are re-stored with
`_nested.List_1 α` rewritten to `List (Tree α)`; every recursor — the user's and the auxiliary
one — is added with type and rules rewritten, the auxiliary one under a fresh name
(`mkAuxRecNameMap`: `_nested.List_1.rec ↦ Tree.rec_1`).

So the head generalisation is not a change to what is *checked*.  It is a parameter of what is
*declared*.

---

## 2. What the file does

### `VIndRestore` — `restoreNested` as data

```lean
structure VIndRestore where
  tyName   : Nat → Name          -- `_nested.List_1 ↦ List`
  tyLvls   : Nat → List VLevel   -- the levels the presented head is applied at
  tyArgs   : Nat → List VExpr    -- the stored instantiation, over the block's params
  ctorName : Name → Name         -- `restoreCtorName`
  recName  : Name → Name         -- `mkAuxRecNameMap`
```

`VInductDecl'.idRestore` is the identity restoration.  `tyAppR`/`tyAppR'`/`ctorAppR` are
`tyApp`/`tyApp'`/`ctorApp'` with it applied; `tyAppR` is literally
`CompanionResolve.lean`'s `tyAppH`, so the down payment is spent rather than re-derived.

Every recursor-side construction is copied with the restoration threaded:
`motiveTypeR`, `minorTypeR`, `recTypeR`, `iotaCtxR`, `ihValuesR`, `iotaLamR`, `iotaLhsR`,
`iotaTypeR`, `iotaRuleR`, `iotaRulesR`, `recConstsR`, `ctorConstsCR`, `allConstsCR`, and
`VEnv.addIndRulesR` / `VEnv.addInductR`.  `ihType`/`ihTypes` are **not** on the list and are
used verbatim: they mention no block head, only `r.binders`, `r.args` and de Bruijn variables,
and `VIndField.WF.pos` forces those to be block-free, so restoration cannot touch them.

### Conservativity — this is a generalisation, not a rival spec

Every construction, at `D.idRestore`, **is** its `Decl.lean` original:
`tyAppR_id`, `tyAppR'_id`, `ctorAppR_id`, `canonResultR_id`, `canonTypeR_id`, `typeR_id`,
`fieldTypesR_id`, `motiveTypeR_id`, `motivesR_id`, `minorTypeR_id`, `minorsR_id`,
`recTypeR_id`, `iotaCtxR_id`, `ihValuesR_id`, `iotaLamR_id`, `iotaLhsR_id`, `iotaTypeR_id`,
`iotaRuleR_id`, `iotaRulesR_id`, `recConstsR_id`, `ctorConstsCR_id`, `allConstsCR_id_nil`,
`VEnv.addIndRulesR_id`, and

```lean
theorem VEnv.addInductR_eq_addInduct' (env) (h : D.Canonical) :
    env.addInductR D [] D.idRestore = env.addInduct' D
```

**One side condition, stated not hidden.**  `VIndCtor.Canonical D` says a recursive field's
*stored* type is its canonical form `∀ ξ, I_idx params π` on the nose.  `VIndField.WF.pos`
only requires this up to defeq (`Decl.lean`'s `(fun _ : T => Nat) r` example), so the
constructor-side conservativity equations are conditional on it.  It holds of every witness in
`DeclExamples.lean` and of every constructor `ElimNestedInductive` generates
(`replaceIfNested` instantiates `J`'s own stored type, whose recursive positions are
applications of a block constant on the nose).  `ntreeAux_Canonical` is the machine-checked
instance.

### G4, repaired — and the invariant

`iotaLhsR` heads its left-hand side with `R.recName (mkRecName I_j)` and its major premise with
`R.ctorName C.name`; `ihValuesR` calls `R.recName (mkRecName I_{r.idx})`.  Then

```lean
theorem VInductDecl'.key_iotaRuleR (D) (R) (j q) (C) :
    (D.iotaRuleR R j q C).key = [R.recName (mkRecName (D.types.getD j default).name),
                                R.ctorName C.name]

theorem VInductDecl'.iotaRulesR_key_declared (D) (R) (K) (h : df ∈ D.iotaRulesR R) :
    ∃ n, df.key.head? = some n ∧ n ∈ D.allNamesCR R K

theorem VEnv.addInductR_key_declared (hadd : env.addInductR D K R = some env')
    (h : df ∈ D.iotaRulesR R) : ∃ n, df.key.head? = some n ∧ env'.contains n
```

> **Every ι-rule the step emits is keyed to a recursor constant the same step declares.**

That is the invariant whose absence made G4 invisible: no field of any `WF` predicate mentions
which constant a rule reduces.  It matches the shape the `Verify/` side landed independently
(`AddInductStages.iotaRule_declared`).  The negative is kept:
`VInductDecl'.iotaRule_key_not_declared` for the general statement,
`ntreeAux_iotaRule_key_not_declared` for the concrete failure of the *unrepaired*
`addInductC` at the nested witness, and `key_iotaRule_ne_renamed` (`CompanionResolve.lean`)
still applies to it.

### What the restoration owes

```lean
def VIndRestore.instAt (R) (D) (npJ j) (e) : VExpr :=
  mkPi D.params (VExpr.instAll (VExpr.splitPis npJ (e.instL (R.tyLvls j))).2 (R.tyArgs j))

structure VIndRestore.Faithful (R) (D) (ds) (env) (K) (npJ) : Prop where
  ty_agree       -- `J`'s stored type, instantiated at `A`, is the auxiliary member's own
  ctor_agree     -- likewise for each constructor, against `C.typeR D R j`
  ctors_complete -- **G2**: the auxiliary member's constructors, restored, are all of `J`'s
```

`ty_agree` and `ctor_agree` are *equations between stored types* — checkable with no typing
judgement.  `ctors_complete` is `fooComp_inconsistent`'s guard, transplanted: a companion
recursor with too few minor premises is still an eliminator with no minors over an inhabited
type.

### The step

```lean
def VEnv.AddNested (ds) (env) (D) (K) (R) (npJ) (env') : Prop :=
  D.WF env ∧ D.Canonical ∧ R.Faithful D ds env K npJ ∧ env.addInductR D K R = some env'
```

`AddNested_nil` : at `K = []`, `R = idRestore`, this **is** `VDecl.WF.induct`'s premise pair
(`Faithful` is vacuous there — the formal content of "a block with no nested occurrence needs
no restoration").  `AddNested_keys_declared` carries G4's invariant through the step.

Note what the check is: `VInductDecl'.WF`, **unchanged**.  Not `WFC`, not a resolved block.

---

## 3. Three refutations (machine-checked)

All at `ntreeAux`, the auxiliary block for `NTree α = Tree α`.

### 3.1 `resolveC` does not model `restoreNested`

* `ntreeAux_resolveC_none` : `ntreeAux.resolveC [.induct listDecl] [`_nested.List_1] = none`.
  The companion's name is one the history has never declared and never will, so `AddCompanion`
  is not a relation any genuine nested block stands in.
* `ntreeAuxL_resolveC_loses_recursion` : name the member `List` instead — the identification
  `Companion.lean` makes — and resolution *does* fire, replacing it by `List`'s own record.
  `listCons.recFields.length = 1` while `nlistCons.recFields.length = 2`: the recursor loses
  the induction hypothesis for `NTree`.

`restoreNested` carries the **auxiliary** member's constructors *forward* with the
instantiation substituted; `resolveC` carries the **declaring** block's constructors *backward*
with nothing substituted.  The two are not the same operation and not even the same direction.
(`CompanionResolve.lean` §2's argument for a definition — "`restoreNested` copies rather than
checks" — is right about *copying*; it identified the wrong thing as being copied.)

### 3.2 The companion guards do not constrain a nested block

* `ntreeAux_CompanionShape_vacuous` : `CompanionShape` quantifies over history blocks declaring
  a type named in `K`; `K` holds the auxiliary name, so the quantifier is empty.  It is
  therefore **not** a residue the head generalisation removes — `docs/handoff-nested-head.md`
  §6.3's prediction that the parameter-count conjunct becomes a substitution lemma does not
  arise, because the conjunct has nothing to range over.
* `ntreeAux_not_CompanionComplete`, `ntreeAux_not_CompanionSound` : both are **false**, not
  weak.  They ask the history / the environment for the auxiliary name.

`VIndRestore.Faithful` replaces all three, and is non-vacuous (`ntreeRestore_faithful`).

### 3.3 `addInduct'` does not refuse a nested block, and G1 would break it

* `ntreeAux_allNames` : the abstract step declares seven constants (including
  `_nested.List_1`, its two constructors and `_nested.List_1.rec`) where
  `Environment.addInductive` declares four.  Nothing is refused — the auxiliary name is fresh.
  So `Companion.lean`'s premise ("the refusal is one `addConst` on an already-taken name") is
  about the `J`-as-companion model only.
* `ntreeAux_staging` : `VInductDecl'.WFC` stages the constructor clause over `addIndTypesC`,
  which drops `_nested.List_1`'s type constant — and `NTree.node`'s stored field type *is*
  `_nested.List_1 α`.  At that staging the clause is **unsatisfiable**, not merely weaker.

  So "G1 must never land without G2" should be read as scoped to the companion model.  Under
  the auxiliary model G1 is not an improvement to make at all: `VInductDecl'.WF` already
  stages over `addIndTypes`, which is what `AddInductive.run` does.

**None of this rehabilitates `fooCompDecl`.**  `fooComp_inconsistent` is untouched; the
`CompanionResolve.lean` witnesses (`fooComp_killed`, `fooComp_admitted_repaired`,
`fooComp_WFC`, `fooDecl_WFC`, `fooComp_resolveC`, `fooCompRec_ne_mkRecName`,
`resolveC_zero_ctors`, `resolveC_complete`, `AddCompanion_nil`) all re-elaborate in
`NestedHead.lean`'s regression block, so a change breaking any of them breaks this file too.

---

## 4. The witness, end to end

`inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α` is declared **in the
file**, so Lean's own kernel runs the nested elimination on it and `NTree.rec`, `NTree.rec_1`
and their stored rules are ground truth, not a transcription of this spec.

| check | content |
|---|---|
| `ntreeNode_typeR` | the re-stored constructor type **is** `@NTree.node`'s |
| `ntreeAux_recTypeR_0` | `swap01 (recTypeR R 0) = type_of% @NTree.rec` — motives and minors headed `List (NTree α)` |
| `ntreeAux_recTypeR_1` | `swap01 (recTypeR R 1) = type_of% @NTree.rec_1` — the **companion's** recursor |
| `ntreeAux_iotaLamR_0/_1/_2` | the three ι-rule right-hand sides **are** `vrecrule(NTree.rec, 0)`, `vrecrule(NTree.rec_1, 0)`, `vrecrule(NTree.rec_1, 1)` — the rules Lean stores |
| `ntreeAux_allNamesCR` | the step declares exactly `[NTree, NTree.node, NTree.rec, NTree.rec_1]` |
| `ntreeAux_key_0/_1/_2` | keys `[NTree.rec, NTree.node]`, `[NTree.rec_1, List.nil]`, `[NTree.rec_1, List.cons]` |
| `ntreeAux_keys_declared` | …every one of them a constant the step declares |
| `ntreeAux_Canonical` | both recursive fields stored canonically |
| `ntreeAux_WF` | **`VInductDecl'.WF` for the auxiliary block** — two types, three constructors, three recursive fields, including the one that is recursive *only because* of the instantiation |
| `ntreeRestore_faithful` | `ty_agree`, `ctor_agree`, `ctors_complete` against `List` as the history declares it — every equation `rfl` |
| `ntreeAux_admitted` | freshness + `Nodup`, so the extension succeeds |
| `ntreeAux_recs_declared` | `NTree.rec_1` present at `recTypeR R 1` |
| **`ntreeAux_AddNested`** | all of the above, assembled |

A **negative control** was run during development: replacing `tyArgs 1` by the parameter run
(i.e. deleting the head generalisation) makes `ntreeNode_typeR`, `ntreeAux_recTypeR_0/_1` and
the three `iotaLamR` checks all fail.  The checks discriminate.

`listDecl` (`List` as a block of the history) is validated the same way:
`listType.type`, `listNil.type`, `listCons.type` and `swap01 (listDecl.recType 0)` are Lean's.

---

## 5. Still open, named precisely

* **`VIndRecArg.BindersIndep` under the substitution.**  At the witness every recursive field
  has `ξ = []`, so `ntreeAux_binders_indep` discharges it by emptiness — the clause is *reached*
  but not *exercised*.  The general obligation is real: an auxiliary constructor's `ξ` is `J`'s
  constructor's `ξ` with the instantiation substituted, so nesting in a type with a
  higher-order constructor field (`Acc`-shaped) is the configuration that would exercise it.
  `wDecl_WF` (`DeclExamples.lean`) remains the standing witness at the hard configuration, but
  not at a nested one.  **No nested witness with a non-empty `ξ` exists.**
* **Positivity for a nested head.**  Read off `Add.lean`, *not* machine-checked: the nested
  positivity question reduces to the auxiliary block's *ordinary* `checkPositivity`.  A
  parameter of `J` that occurs negatively in `J`'s constructors becomes, after instantiation, a
  negative occurrence of a block constant in the auxiliary constructor, and the ordinary check
  rejects it.  `ntreeAux_WF` discharges `VIndField.WF.pos` for the positive case, including
  `nlistCons`'s first field.  **The rejection direction has no witness** — building one needs
  `¬ ∃ A, NoBlock A ∧ IsDefEqType …`, i.e. defeq reasoning, so it was not attempted.
* **Universe-count agreement**, resolved but only as a *statement*: it is not a constraint
  between two blocks (`CompanionShape`'s first conjunct) but the single equation
  `ci.uvars = (R.tyLvls j).length` in `Faithful.ty_agree`/`ctor_agree`, discharged by `rfl` at
  the witness.  Whether `ElimNestedInductive` always establishes it is read off source
  (`replaceIfNested` passes `I_lvls` from the occurrence and `st.lvls` for the auxiliary type)
  and is **not** machine-checked.
* **`Faithful` against a general history**: only `ntreeRestore_faithful` exists.  There is no
  theorem saying `ElimNestedInductive` *produces* a faithful restoration — that is the
  refinement-side obligation, and it is the natural next target.
* **`ctors_complete` is stated, never derived.**  In the implementation it is by construction
  (`replaceIfNested` maps over `J_info.ctors`); in the abstract theory nothing forces it, which
  is exactly the `fooComp_inconsistent` shape.  A `resolveC`-style *definition* is still the
  right answer — but it must build the auxiliary member from `J` **with the instantiation**,
  not replace it by `J`.  That function is the abstract counterpart of `replaceIfNested` and
  does not exist yet.
* **`VDecl`/`Typing/Env.lean` wiring.**  `VEnv.AddNested` is not yet a `VDecl.WF` clause.
  `AddNested_nil` is the conservativity theorem that would make the flip a no-op.
* **Consistency of the result** — `leanTTConsistent`, open, as always.

---

## 6. Two items outside this file

* **Fixed, in a file this stream owns.**  `Lean4Lean/Theory/Inductive/Decl.lean`'s R10 handover
  said an unsafe inductive block "is taken by `TrEnv'.ignore` instead".  That is false and now
  machine-checked false (`TrEnv'.ignore_unavailable_at_unsafe`,
  `Verify/TypeChecker/Reduce.lean`): `.unsafe` is the bottom of `DefinitionSafety`, so
  `ignore`'s premise `¬ safety ≤ ci.safety` never holds there.  The note now says the honest
  thing — an unsafe inductive is **unhandled**, not handled-by-ignoring.  The same false claim
  in `Verify/Environment/Induct.lean`'s `TrIndDecl.safe` is *not* this stream's file.
* **Named, not fixed.**  `VEnv.addDefEqs_le` is declared twice with the same statement:
  `Lean4Lean/Theory/Typing/DeltaUnique.lean:773` (explicit args) and
  `Lean4Lean/Verify/Environment/Lemmas.lean:181` (implicit args).  This is what blocks
  importing `DeltaUnique.lean` into `Verify/`.  Neither file is owned by this stream
  (`Theory/Typing/` is not `Theory/Inductive/`), so it is reported rather than fixed.  The
  cheap fix is to delete the `Theory` copy and have `PatternRules.lean:503` use the `Verify`
  one — except that inverts the dependency, so more likely: keep the `Theory` one, delete the
  `Verify` duplicate, and make `Verify/Environment/Lemmas.lean` import it.

---

## 7. What to pick up first

1. **The abstract `replaceIfNested`.**  A function taking `J`'s block, an instantiation `A` and
   an index remapping to the auxiliary member — making `Faithful.ctors_complete` and
   `ctor_agree` *consequences of a construction* rather than hypotheses, exactly as `resolveC`
   was meant to do for the companion model.  This is the one remaining place a caller can lie.
2. **A nested witness with a non-empty `ξ`**, to exercise `BindersIndep` under the
   substitution.  Nest something `Acc`-shaped.
3. **The `VDecl`/`Typing/Env.lean` flip**, using `AddNested_nil` as the conservativity theorem.
   Do **not** flip `WF.ctors` onto `addIndTypesC` (§3.3).
4. **Refinement side**: prove `ElimNestedInductive` produces a `Faithful` restoration.  This is
   where lean4#14576/#14577 (the unchecked `Ds` arguments) lives, and where the historical
   soundness bug was.

---
---

# Part II — `OccResidue` spent: the residue is `member` + `occurs`

*Appended 2026-09-01 by the `OccResidue` stream (four rounds, commits `61166b7`, `50858df`,
`873f5f4`, `4de3a3b`, plus the implementation fix `dcf6ec5`).  Part I above is earlier and is not
revised by this; where Part I §7 lists "what to pick up first", items 1 and 4 are now largely
done — the abstract `replaceIfNested` is `VNestedOcc.member` and the refinement-side `Faithful`
is `VInductDecl'.Built.toFaithful`.  §15 below is the current answer, and the banner at the
top of this file still applies to Part I only.*

Files this stream owns and wrote: `Lean4Lean/Verify/Inductive/NestedOccData.lean` and
`Lean4Lean/Verify/Inductive/NestedRunInvariant.lean`.

---

## 8. The state, unhedged

**`VInductDecl'.Built`'s eight clauses.**  Four come from `ElimNestedInductive.Result.RestoreData`
(`RestoreData.mkRestore_built`).  Of the other four, collected as
`ElimNestedInductive.Result.OccResidue`:

* **`head` closes** in general — `Result.OccData.head`.
* **`ctorName_inv` closes** in general — `Result.OccData.ctorName_inv`.
* **`member` and `occurs` remain**, and are exactly `Result.SemResidue`.

`Result.OccData.occResidue` is the reduction; `OccData.mkRestore_built`, `_faithful`,
`_canonical`, `_AddNested`, `_AddNestedStep` re-derive the whole nested step from
`RestoreData ∧ OccData ∧ SemResidue`.

`OccData` is six fields — `auxName`, `auxHead`, `ctorName`, `srcCtorPrefix`, `auxCtors`,
`ctorNodup` — all name-and-head facts about the checker's `Result`, none mentioning `TrExprS`,
`VEnv`, or any judgement, all decidable at a concrete block.

**The monadic side.**  `ElimNestedInductive.MWF` is the calculus with the state invariant a
*parameter* on both sides; `EWF_iff` exhibits `AddInductiveStep.lean`'s `EWF` as its instance at
`fun s => s.nestedAux = #[]`, so nothing there is lost.  With it:

* **`replaceAppendsOnly : ∀ env, ReplaceAppendsOnly env` — proved, no hypothesis at all.**
* **`runSkelExtends : ∀ env, RunSkelExtends env` — proved, no hypothesis at all.**
* `run_prefix` is the entrywise form: on `j < types.length`, `run`'s output member carries the
  *input* member's name and its constructors' names, in order.

**The four `RestoreData` prefix fields, individually** (`NestedOccData.lean` §8):

| field | status |
| --- | --- |
| `ownName` | **claimed** (`Result.ownName_of_run`) — but as a statement about the checker's *input* |
| `ownCtor` | **claimed** (`Result.ownCtor_of_run`) — likewise |
| `name` | **prefix half only** (`Result.name_prefix_of_run`); tail half open |
| `ctor` | **declined** — for a circle, not a gap |

`ownName`/`ownCtor` do not become *provable*: they become statements about `types`, which
`Environment.addInductive`'s caller hands in.  That is still progress — the obligation moves off
the checker's *output*, which no caller can inspect, onto its *input*.  There it is row 58's
unchecked fact.

Neither tail half follows and this is structural: `RunSkelExtends` pins only the prefix (by
design — `replaceIfNested` *creates* the tail), and `TrIndDeclN.trType`/`trCtors` are quantified
over `types[j]? = some t`, which is `none` past the cut.  **`TrIndDeclN` says nothing about `D`'s
companion members.**

**The single strongest fact this stream found:** `Built.member` is what pins `D`'s companion
members, and nothing else in the chain does.  Witnessed by `NestedWit.nfnAuxBadTy` +
`nfnResult_restoreData_badD` + `occurs_badD` + `semResidue_not_member_badD`: perturb `D`'s
companion member's stored type, leave `occ` alone, and `RestoreData` (all 14), `OccData` (all 6),
`mkRestore_built`'s `hl`/`ha`, **and `occurs`** all still hold while `member` is false.

---

## 9. Three things asked for that were not provable, and why

### 9.1 `mkUniqueName`'s freshness against the input block — **false**

I said (and it was carried into a later brief) that what would break `ctor`'s circle is
"`mkUniqueName`'s freshness against the input block".  There is no such freshness.
`mkUniqueName`'s loop tests `env.contains r` and nothing else — `mkUniqueName_fresh`
(`NestedRunInvariant.lean`) is the exact and only statement.  The block being declared is not in
`env`; keeping its names apart from what is already there is `Environment.addInductive`'s separate
business.  `NestedOccData.lean` §10.1 exhibits a block where `mkUniqueName`'s output collides
with a member of the block being declared.

**Do not try to prove it.**  It is false, not merely unproved.

### 9.2 The two commutation lemmas for `member` — declined, with suppliers named

`member`'s content is that the checker's `Expr`-level companion rebuild agrees with
`VNestedOcc.member` after translation.  Three commutations; `NestedOccData.lean` §9 records them.

* **(A) `instantiateLevelParamsNoCache` vs `instL` — already exists**: `Lean4Lean.TrExprS.instL`
  (`Verify/Typing/Lemmas.lean`), stated over core's pure `instantiateLevelParamsNoCache`,
  mentioning neither `Expr.replace` nor the cached `instantiateLevelParams`.  Side conditions
  (`mapM (VLevel.ofLevel Us) ls = some ls'`, `ps.length = ls.length`) are supplied by
  `replaceIfNested`.
  **But "already proved" was true of the statement and false of the cone**: `TrExprS.instL`'s
  cone is **9446 with four holes** and its `#print axioms` carries `sorryAx` plus five frozen
  axioms.  It also lands in `TrExpr` (∃ up to `IsDefEqU`), not `TrExprS`, and `Built.member` is a
  *syntactic* `VIndType` equality — that gap is content, not bookkeeping.
* **(B) `instantiateForallParams` vs `splitPis`/`instAll` — not proved.**  An `n`-fold `TrExprS`
  substitution composed with a `forallE`-peeling lemma.  Side conditions `ps.size = n` (supplied
  by `isNestedInductiveApp?` via the `assert!`) and the spine translating.  **It will need the
  frozen axiom `Lean.Expr.instantiateRevRange_eq`** (guard 1 whitelist) — flagged because
  shrinking that list is progress and this would block removing that entry.
* **(C) `LocalContext.mkForall` vs `mkPi` — not proved.**  Pure half exists
  (`Verify/LocalContext.lean`: `mkBinding_eq`, `mkBindingList1_abstract`, `mkBindingList_eq_fold`),
  side conditions `b.looseBVarRange' = 0` and `xs.Nodup`, both supplied by `withParams`'
  `mkFreshId`.  **The `xs.Nodup` supplier is `Verify/NameGenerator.lean`** —
  `NameGenerator.Reserves`, `next_reserves_self`, `not_reserves_self`, `NameGenerator.LE`.  Using
  it needs `MWF.withParams'` restated with an `ngen`-reservation invariant alongside `I`: a
  refactor of that lemma, not a use of it.  The `TrExprS` half is the bulk of the work.

Neither (B) nor (C) becomes an `OccData` field.  **`member` needs no new field and no new
premise** — that conclusion survived all four rounds.

### 9.3 `ctor`'s circle — a translation-relation gap, not a name-discipline fact

`RestoreData.ctor` is the bundle's *only* statement that the checker's constructor names and
`D`'s agree on user members.  `TrIndDeclN` relates the two sides only through `R.ctorName`
(`TrIndCtorR` is `c.name = R.ctorName C.name`).  Closing the prefix half needs
`R.ctorName C.name = C.name`, i.e. `VIndRestore.OwnId.ctorName` — and `mkRestore_ownId`'s
`ctorName` clause is proved **from `RestoreData.ctor`**.  Circular.

The escape (`¬ IsNestedName C.name` ⇒ the `ctorRenames` lookup misses) needs a bound on a
`D`-side name, and `ownCtor` bounds only the checker's.  So the fix is one new clause on
`TrIndDeclN`:

```
ctorName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
  ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name
```

which the nested path establishes by construction (`run.loop` rebuilds each constructor as
`{ ctor with type := … }`; `run_prefix` is the proof, already in place).  `TrIndDeclN` is a
definition the `addDecl.WF` chain consumes, so this is **reported, gated on a human decision, not
done**.

---

## 10. The two `#eval` witnesses, and what each does and does not guard

Both live in `NestedOccData.lean` §10.  The distinction between them is the clearest example in
this repo of a test that looks like a guard and is not.

* **§10.1, the collision.**  A constructor-less member carrying the exact name
  `mkUniqueName (`_nested ++ ``PFn)` returns, alongside an ordinary nested member.  Runs the
  real `ElimNestedInductive.run` and the real `Environment.addInductive`.  **Guards the finding**:
  it `throwError`s if `checkNoNestedAux` starts rejecting the block, if `run` stops producing the
  duplicate, or if `addInductive` starts *accepting* it.  What it settles is proof-side —
  `RestoreData.ownName` is exactly what excludes this state and nothing in the implementation
  does.  Outcome is a rejection, not unsoundness, and **C++ rejects identically**.

* **§10.2, first `#eval` — guards nothing.**  It *models* the old gate inline by iterating
  `divIndType.ctors` (which is empty) and then calls `checkNoNestedAux` on the member type
  directly.  It never calls `Environment.addInductive`, so it passes identically with and without
  the fix.  It demonstrates the difference between two *checks*.  The commit message for the fix
  claimed this eval meant the fix "cannot be silently reverted"; that claim was **false** and is
  now corrected in the file.

* **§10.2, second `#eval` — the actual regression test.**  Calls the real
  `Environment.addInductive` and requires the failure to be the **reserved-prefix** error
  specifically; `divIndType` has no constructors, so only the member-type `checkNoNestedAux` call
  can produce that message.  It fails if the fix is reverted *and* if the rejection moves to some
  other cause.  The negative control was run both ways.

**The general lesson to carry:** an `#eval` that reconstructs the code path it is testing tests
your model of the code, not the code.  A guard must call the real entry point and pin the
*reason* for the outcome, not just the outcome.

---

## 11. The concentration measurement, two-sided

| seeds | cone | holes |
| --- | --- | --- |
| `OccData.mkRestore_built` + `OccData.mkRestore_AddNestedStep` (the nested step **without** `member`) | 2565 | **0** |
| the same **plus** `TrExprS.instL` | 9446 (+6881) | **4** |

Holes that arrive, with transitive `Lean4Lean` user counts:

```
VEnv.IsDefEqU.weakN_iff                214
VEnv.IsDefEqU.forallE_inv_stratified   590
VEnv.WF.rigidShapeUniqNS               356
VEnv.NormalEq.descend                  145
```

**These figures are *relative*, not absolute**: my instrument walks reverse edges only where both
endpoints are `Lean4Lean.*` and skips internal names.  The census's absolute figures for the same
four were 296 / 650 / 409 / 193.  Compare mine to mine, the census's to the census's.

The reading: **the nested step chain is hole-free today, and `member` is precisely where the
injectivity/confluence cluster would enter.**  A `member` built on `TrExprS.instL` may still be
the right thing to have, but it must be labelled "modulo the injectivity/confluence cluster" and
must not be counted as closing the clause.

---

## 12. Tried and failed, with the failing step

* **The bundle claim on the four `RestoreData` prefix fields — wrong twice over.**  I wrote that
  `name`, `ctor`, `ownName`, `ownCtor` "follow from a single statement about `replaceIfNested`".
  Failing step: `name` and `ctor` are not `r`-side facts at all (they compare `r.types` to
  `D.types`, so they need `TrIndDeclN`), and even with it only their prefix halves follow.  This is
  ledger row 11a recurring in a corner already warned about.  **A bundle claim here has now been
  wrong three times; claim fields individually.**
* **The `member`-not-slack bound that did not cover the case that mattered.**
  `semResidue_not_member_badTy` (perturbing `pfnOcc`'s *source* block) shows `member` is not slack
  in `RestoreData ∧ OccData ∧ hl ∧ ha`.  Failing step: the witness also violates `occurs`
  (`pfnOccBadTy_not_occurs`), so it said nothing about the hypothesis set that mattered.  The
  bound that does is `nfnAuxBadTy`, which perturbs **`D`**.  *A non-slackness bound is only as
  strong as the hypothesis set it holds the field against.*
* **`Declared` vs "unrecoverable" — a conflation.**  I read `Theory/Inductive/Decl.lean`'s
  `VInductDecl'.Declared` docstring's "unrecoverable" as "not pinned".  It means *not recoverable
  from a `Lean.Declaration`*.  `VEnv.LE.constants` is **exact** equality of the `VConstant`, and
  `addInduct'` runs `addIndRecs`, so `Declared D env` pins `D.recType j` exactly, hence `indices`
  up to injectivity of `recType` in that field (unproved, and no longer needed).
* **Predicted that the `assert!`/`unreachable!` panics would force arity side conditions on
  `ReplaceAppendsOnly`.**  Failing step: `panic_eq` — `Inhabited (M α)` resolves through
  `instInhabitedOfMonad`, i.e. `pure default`, so a panic returns `default` **with the incoming
  state**.  A wrong comment in `AddInductiveStep.lean` (since corrected) was costing a real
  hypothesis.
* **An `#eval` collision scenario via a member that references itself** — rejected by
  `checkNoNestedAux`, which scans constructor types and therefore catches a self-reference to a
  `_nested`-named member.  The scenario that works uses a **constructor-less** member.
* **An O(n²) reverse-user scan** for §11 — killed by its own timeout (exit 143), superseded by a
  version that builds the reverse adjacency map once.  Read-only, nothing to undo.

---

## 13. Traps

* **`srcCtorPrefix` and `ownName` are unchecked name-discipline facts** under row 58's standing
  decision: do not add a check neither kernel performs.  `OccData.srcCtorPrefix` (`J`'s
  constructor names carry `J`'s own name as a prefix) is the third such fact and the first about
  the *previously declared* block; it has **no** witness that it fails and stays flagged.
  `RestoreData.ownName` now **does** have its witness (§10.1) — **and the decision still stands**,
  because C++ rejects that block identically, so adding the check would not close a divergence.
* **No conjunct on `AddNested`, `Built`, or `InductStepNested`.**  `InductStepNested` has a model
  (`inductStepNested_wit'`) rather than an unsatisfiable precondition, which is why the decision
  is live; a conjunct there changes a definition the `addDecl.WF` chain consumes.  Same for the
  `TrIndDeclN.ctorName_own` clause of §9.3.
* **`VIndCtor.typeR` must not become the substitution** (ledger row 36).  Unchanged by this
  stream.
* **`RestoreData.ownName`/`ownCtor` stay hypotheses.**  Row 58.
* **Frozen files** — `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`: read,
  never edit.
* **`Verify/Typing/Lemmas.lean` was cited, never edited** (another stream's).  `TrExprS.instL`
  lives there.

---

## 14. Measured / read off source / not run

**Measured (machine-checked in-tree).**  Everything in §8; the two `#eval`s of §10 (they run at
build time and `throwError` on regression); the cone and axiom figures of §11 and below.
`#print axioms` on every declaration this stream proved: `[propext]`,
`[propext, Quot.sound]`, or `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no frozen
axiom, anywhere in this stream's own proofs.**  Hole cones, all **0 holes**:
`replacePrefix_replacePrefix` 1489, `getAppFn_mkAppRange` 1606, `getAppFn_stored` 1718,
`OccData.head` 696, `OccData.ctorName_inv` 1938, `occResidue` 2089, `mkRestore_built` 2154,
`mkRestore_faithful` 2483, `mkRestore_AddNestedStep` 2564, `MWF.forIn'` 218, `EWF_iff` 25,
`panic_eq` 426, `MWF.isNestedApp'` 5096, `MWF.replaceIfNested'` 5517, `replaceAppendsOnly` 5573,
`SkelExt.set` 704, `run_loop_skel` 5759, `runSkelExtends` 5770, `run_prefix` 5774,
`ownName_of_run` 5794, `name_prefix_of_run` 5789, `nfnResult_restoreData_badD` 3762,
`semResidue_not_member_badD` 1371, `mkUniqueName_fresh` 2444.  Guards, every round: guard 1 ✓ (24
axioms) / guard 2 ✓ (INCOMPLETE) / guard 3 ✓ (2/2).

**Read off source, not machine-checked.**  That the C++ kernel calls `check_no_nested_aux` once
per `inductive_type` and once per constructor (`~/lean4/src/kernel/inductive.cpp`,
`environment::add_inductive`) — the basis for the divergence, now fixed in `dcf6ec5`.  That
`replaceIfNested` pushes `(replaceParams params (mkAppRange (.const J I_lvls) 0 I_nparams args) As,
auxJ_name)` to `nestedAux` in lockstep with the `newTypes.push` — this is what makes
`OccData.auxHead` a fact about the implementation, and `Result.getAppFn_stored` is the `Expr`-level
half proved, but the lockstep itself is read, not proved.

**Not run: `scripts/sorry-census.lean` and `scripts/dup-names.lean`.**  Both import
`Experimental/ConeJoin.lean`, and two other streams were mid-edit inside its import closure
throughout the last two rounds.  The signature of that condition is a build failing with
`object file '…/<Module>.olean' of module … does not exist` — a `.olean` moving underneath a
`lake env lean` invocation.  Running either instrument then reports numbers for a tree that never
existed.  The last quiescent figures, from the orchestrator at `d451fe5`: build green 1402 jobs,
guards all ✓, dup-names clean, census **13**.  §11's reverse-cone measurement was done in a
private ConeJoin-importing file under `/tmp`, which is safe because it is read-only and its
failure mode is the visible one above.

---

## 15. What to pick up first

**Ask for the `TrIndDeclN.ctorName_own` decision, then do `MWF.withParams'`.**  I partly disagree
with taking `ctor`'s clause first: it is the right *next result* and `run_prefix` makes it cheap,
but it is gated on a human decision about a definition the `addDecl.WF` chain consumes, so a fresh
agent cannot start there — it can only draft the clause and stop.  Request the decision in the
first message, and meanwhile do the one piece of work that is unblocked, entirely inside
`Verify/Inductive/*`, and needed either way: **restate `MWF.withParams'` with an
`ngen`-reservation invariant** (`Verify/NameGenerator.lean` supplies `Reserves`/`LE`).  That yields
`xs.Nodup` for commutation (C), which is the first of `member`'s two open commutations, and
`member` is the load-bearing clause — with the §11 label attached, not counted as closed.
