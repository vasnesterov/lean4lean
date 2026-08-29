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
