# The abstract `replaceIfNested`: the companion member stops being data

Successor to `docs/handoff-nested-restore.md` (read that first for `VIndRestore`,
`VEnv.addInductR`, `VIndRestore.Faithful` and `VEnv.AddNested`).

Two new files, both `sorry`-free, both green:

* **`Lean4Lean/Theory/Inductive/NestedBuild.lean`** (~1225 lines) — the construction, its
  correctness, `BindersIndep` under substitution, and two end-to-end witnesses.
* **`Lean4Lean/Theory/Inductive/NestedPositivity.lean`** (~262 lines) — the nested-positivity
  reduction and the rejection witness.  **This file imports `Lean4Lean.Environment`**, i.e. a
  `Theory/` module depends on the implementation.  That is deliberate (the rejection witness
  has to *run* the checker) and it is a leaf module, so no cycle is possible — but if that
  layering is unwanted, the `run_meta` block at the end belongs in
  `Lean4Lean/Tests/NestedInductive.lean`, which this stream does not own.

Nothing else was edited.  `NestedHead.lean` and `CompanionResolve.lean` are untouched; their
witnesses are re-elaborated in `NestedBuild.lean` Part 10 so that breaking any of them breaks
this file too.  `lake build` (all 1339 jobs, guards included) is green.

Axioms: every new theorem is on `[propext, Quot.sound]`, plus `Classical.choice` where the
proof goes through `Exists.choose`, `omega` or `simp`.

---

## 0. Bottom line

| question | answer |
|---|---|
| Is `Faithful.ctors_complete` still a hypothesis? | **No.** `VNestedOcc.member_ctors_complete`. |
| Is `Faithful.ctor_agree` still a hypothesis? | **No.** `VNestedOcc.ctor_typeR`, and **unconditionally** — no canonicity, no shape condition on `J`. |
| Is `Faithful.ty_agree` still a hypothesis? | **No** — it is definitional for a built member. |
| Is `VIndCtor.Canonical` still a side condition on the companion? | **No.** `VNestedOcc.member_Canonical`; only the user's own members need `CanonicalOwn`. |
| Is the new obligation strictly stronger? | **Yes, machine-checked**: `ntreeAuxI_faithful` ∧ `ntreeAuxI_not_built`. |
| Does the old step still follow? | **Yes.** `VEnv.AddNestedB.toAddNested`. |
| Does a nested witness with non-empty `ξ` exist? | **Yes**, two ways: `pfnAuxMk_xi_nonempty` and the `WF` proof `nfnAux_WF` that uses it. |
| Is `BindersIndep` established under substitution? | **Yes**, `VNestedOcc.bindersIndep`, from `VExpr.Skips.instAll` + `VExpr.skips_splitPis`. |
| Is nested positivity's reduction machine-checked? | **At the implementation, yes** (`NestedPositivity.lean`'s `run_meta`); at the abstract level, all but one defeq non-existence. |
| Is there a rejection witness? | **Yes.** `badNestDecl` is refused by this development, with a message naming the *auxiliary* constructor. |
| Is universe-count agreement machine-checked? | It is now a *derived* clause (`Occurs.lvls_len ⟹ Faithful.ty_agree`'s `uvars` conjunct), discharged at two witnesses.  That `ElimNestedInductive` establishes it is still read off source. |

---

## 1. What was wrong, precisely

`VIndRestore.Faithful` (`NestedHead.lean`) has three clauses.  `ty_agree` and `ctor_agree` are
equations a caller asserts about the companion member; `ctors_complete` asserts its
constructor list is `J`'s.  Nothing forces a caller to have *obtained* the member from `J`.
That is the shape that produced `InductiveDeclExamples.fooComp_inconsistent`: a field the spec
merely checks, where `Environment.addInductive` **copies**.

The implementation does not check anything here.  `ElimNestedInductive.replaceIfNested`
(`Lean4Lean/Inductive/Add.lean:819`) *writes* the auxiliary member:

```
auxJ_type   := lctx.mkForall As <| ← instantiateForallParams
                 (J_info.type.instantiateLevelParams J_info.levelParams I_lvls) I_nparams args
auxJ_ctors  ← J_info.ctors.mapM fun J_ctor_name => …          -- J's WHOLE list
```

so the fix is to make the spec write it too.

## 2. The construction

```lean
structure VNestedOcc where
  decl     : VInductDecl'      -- J's block, from the history
  idx      : Nat               -- which member of it (replaceIfNested does all of I_val.all)
  lvls     : List VLevel       -- I_lvls
  args     : List VExpr        -- Ds, over the new block's parameters
  auxName  : Lean.Name         -- mkUniqueName (`_nested ++ J_name)
  ctorName : Lean.Name → Lean.Name   -- J_ctor_name.replacePrefix J_name auxJ_name
```

`VNestedOcc.instAt` is `lctx.mkForall As ∘ instantiateForallParams ∘ instantiateLevelParams`,
and

```lean
VNestedOcc.member N H R : VIndType :=
  { name := N.auxName, type := N.instAt H N.src.type,
    indices := instAllTele (N.src.indices.map (·.instL N.lvls)) N.args 0,
    ctors := N.src.ctors.map (N.ctor H R) }
```

`H : VIndHeader` (`uvars`, `params`, `nm`, `names`) rather than the finished `VInductDecl'`:
an auxiliary member's own field types are headed by constants of the block being declared —
including its own name — so the finished block cannot be an input.  `VInductDecl'.header`
produces one, and every statement is made against `D.header`.

### The recogniser is the whole trick

The implementation replaces `J Ds π` by `Iaux As π` in a second pass (`replaceAllNested`).
Modelling *that* would need the replacement to be inverted by `VIndField.typeR` — a lemma
about two functions.  Instead:

```lean
def VIndRestore.recogAt (R) (i k : Nat) (S : VExpr) : Option VIndRecArg :=
  -- split S's leading pis as ξ; require the body to be
  --   (R.tyName k).{R.tyLvls k} (R.tyArgs k)↑(|ξ|+i) π
def VIndRestore.recog (R) (nm i : Nat) (S : VExpr) : Option VIndRecArg :=
  (List.range nm).findSome? (R.recogAt i · S)
```

reads the rewrite **off the restoration**, and

```lean
theorem VIndRestore.recog_sound (h : R.recog nm i S = some r) (D) : r.canonTypeR D R i = S
```

says `VIndField.typeR` is a left inverse of it *by construction*.  No `VInductDecl'` appears in
the definition (`VInductDecl'.tyAppR` ignores its `VInductDecl'` argument), which is what
breaks the circularity.

`VNestedOcc.field` then takes the substituted type `S = instAll (F₀.type.instL ls) A i`, and

* `recog … = some r` → stores the **block-headed** canonical form `r.canonTypeH H i`,
* `recog … = none`  → stores `S` with `recArg := none`.

Either way `(N.field H R i F₀).typeR D R i = S` — `VNestedOcc.field_typeR` — which is why
`ctor_agree` comes out with no hypothesis about `J`'s field shapes at all.  (The `NestedHead`
route needed `VIndCtor.Canonical`; a built member *has* it, `VNestedOcc.ctor_Canonical`.)

### The three theorems

```lean
theorem VNestedOcc.ctor_typeR (N H R D j C₀)
    (hname : R.tyName j = N.tyName) (hls : R.tyLvls j = N.lvls) (hargs : R.tyArgs j = N.args)
    (hnp : C₀.params.length = N.decl.np) (hA : N.args.length = N.decl.np)
    (hlv : N.lvls.length = N.decl.uvars) :
    (N.ctor H R C₀).typeR D R j = N.instAt H (C₀.type N.decl N.idx)

theorem VNestedOcc.member_ctors_complete (hcn : ∀ C ∈ N.src.ctors, R.ctorName (N.ctorName C.name) = C.name) :
    (N.member H R).ctors.map (fun C => R.ctorName C.name) = N.src.ctors.map (·.name)

theorem VNestedOcc.member_Canonical (hC : C ∈ (N.member D.header R).ctors) : C.Canonical D
```

`ty_agree`'s equation is `rfl` for a built member.

The arithmetic that makes `ctor_typeR` go through is one new lemma,
`VExpr.map_instAll_bvars_at : (bvars k as.length).map (instAll · as k) = as.map (·.liftN k)` —
the shifted form of `VExpr.map_instAll_bvars`.  That is `tyAppH`'s stored block appearing out
of the parameter run, i.e. exactly the head generalisation `CompanionResolve.lean` Part 9 paid
for.

## 3. The step

```lean
structure VInductDecl'.Built (D) (R) (K) (ds) (env) (occ : Nat → VNestedOcc) : Prop where
  member       : ∀ j T, D.types[j]? = some T → T.name ∈ K → T = (occ j).member D.header R
  occurs       : … → (occ j).Occurs ds env
  tyName/tyLvls/tyArgs : … → R.tyName j = (occ j).tyName  (etc.)
  ctorName_inv : … → ∀ C ∈ (occ j).src.ctors, R.ctorName ((occ j).ctorName C.name) = C.name

def VEnv.AddNestedB ds env D K R occ env' : Prop :=
  D.WF env ∧ D.CanonicalOwn K ∧ D.Built R K ds env occ ∧ env.addInductR D K R = some env'

theorem VEnv.AddNestedB.toAddNested :
    AddNestedB ds env D K R occ env' → VEnv.AddNested ds env D K R (fun j => (occ j).decl.np) env'
```

`VNestedOcc.Occurs` is what the occurrence owes the *history*, and it contains nothing about
the auxiliary member:

```lean
structure Occurs (N) (ds) (env) : Prop where
  hist        : VDecl.induct N.decl ∈ ds
  idx_lt      : N.idx < N.decl.types.length
  lvls_len    : N.lvls.length = N.decl.uvars      -- universe-count agreement, item 4
  args_len    : N.args.length = N.decl.np         -- replaceIfNested's own assert!
  ty_const    : env.constants N.tyName = some ⟨N.decl.uvars, N.src.type⟩
  ctor_params : ∀ C ∈ N.src.ctors, C.params.length = N.decl.np
  ctor_const  : ∀ C ∈ N.src.ctors, env.constants C.name = some ⟨N.decl.uvars, C.type N.decl N.idx⟩
```

`ty_const`/`ctor_const` are what the step that declared `J` produced (`VEnv.addInduct'_types`,
`addInduct'_ctors`).

**Residual reliance, stated:** a caller could in principle supply an `occ j` whose `decl` is a
*truncated* copy of `J` — `ctor_const` only constrains the constructors `N.src.ctors` lists.
`Occurs.hist` then requires that truncated block to be **in `ds`**, so the guarantee is only as
strong as "block names in the declaration history are unique".  That is a `VDecl`/`VEnv.WF`
fact, outside this file, and it is exactly the same reliance `NestedHead.lean`'s
`ctors_complete` had (it also quantifies existentially over `ds`).  Nothing got weaker; it is
now visible.

## 4. `Built` is strictly stronger than `Faithful` — machine-checked

`Faithful` never mentions the companion member's index telescope: its clauses compare stored
types and constructor names, and `VIndCtor.typeR` does not depend on `T.indices`.

* `ntreeAuxI` — `ntreeAux` with the companion's `indices := [Prop]`.
* `ntreeAuxI_faithful` — `VIndRestore.Faithful` still holds.
* `ntreeAuxI_not_built` — `Built` does not.

(`VInductDecl'.WF.types`' `canon` clause constrains `T.indices` up to defeq, so this is not by
itself a soundness hole.  It is the demonstration that a *checked* field leaves slack a
*computed* one does not.)

## 5. Witness 1: `ntreeAux`, rebuilt

`inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α`, from `NestedHead.lean`.

| name | content |
|---|---|
| `ntreeAux_member_built` | `ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore)` — **`rfl`**.  `_nested.List_1`, its type, its index telescope and *both* constructors are computed from `List`'s block. |
| `listOcc_recog_field0` | the recogniser fires on `List.cons`'s **first** field, non-recursive in `List`, recursive in the auxiliary block only because of the instantiation |
| `listOcc_recog_field1` | …and on the self-reference `List (NTree α) ↦ _nested.List_1 α` |
| `listOcc_recog_field1_fails` | **negative control**: present member 1 at the parameter run instead of `[NTree α]` and the second field is no longer recognised |
| `listOcc_occurs` | `Occurs` against `List` as the history declares it |
| `ntreeAux_built` | `Built` |
| `ntreeAux_AddNestedB`, `ntreeAux_AddNested_of_built` | the step, and `NestedHead.lean`'s step from it |
| `ntreeRestore_faithful_of_built` | `NestedHead.lean`'s `ntreeRestore_faithful`, **derived** |

All of `NestedHead.lean` §4's checks are re-elaborated (Part 10) and unchanged.

## 6. Witness 2: a nested block with a non-empty `ξ`

`docs/handoff-nested-restore.md` §5's first open item: *no nested witness with a non-empty `ξ`
exists.*  Now one does.

```lean
inductive PFn (α : Type) where | mk : α → (Prop → α) → PFn α
inductive NFn where            | node : PFn NFn → NFn
```

`PFn`'s higher-order field `Prop → α` becomes, at `α := NFn`, the recursive field
`Prop → NFn` with `ξ = [Prop]`.  Lean's own generated minor premise is
`(a : NFn) → (a_1 : Prop → NFn) → motive_1 a → ((a : Prop) → motive_1 (a_1 a)) → motive_2 (PFn.mk a a_1)`
— the `Acc`-shaped configuration, at a *nested* block.

Checked against Lean's kernel, all `rfl`:

| check | content |
|---|---|
| `pfnType.type`, `pfnMk.type`, `pfnDecl.recType 0` | `= type_of% @PFn`, `@PFn.mk`, `@PFn.rec` |
| `nfnAux_member_built` | `nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore)` — including the `ξ = [Prop]` binder telescope, which the recogniser reads off |
| `nfnNode.typeR …` | `= type_of% @NFn.node` |
| `nfnAux.recTypeR … 0 / 1` | `= type_of% @NFn.rec` / `@NFn.rec_1` |
| `nfnAux.iotaLamR … 0 / 1` | `= vrecrule(NFn.rec, 0)` / `vrecrule(NFn.rec_1, 0)` — the rules Lean **stores** |

and then

| name | content |
|---|---|
| `pfnAuxMk_xi_nonempty` | `∃ r, fields[1].recArg = some r ∧ r.binders ≠ []` |
| `ntreeAux_binders_all_nil` | for contrast: **every** recursive field of `ntreeAux` has `ξ = []` (`decide`) |
| `nfnAux_WF` | `VInductDecl'.WF` for the auxiliary block, with `binders_indep` discharged by the substitution theorem rather than by emptiness |
| `pfnAuxMk_bindersIndep_nonvacuous` | the clause's premise is inhabited at `i = 1`: an earlier field exists, it is recursive, and `ξ` is non-empty |
| `nfnAux_built`, `nfnAux_AddNestedB`, `nfnAux_AddNested` | the second end-to-end step |

### `BindersIndep` under the substitution — proved

```lean
theorem VExpr.Skips.instN  (hj : j < m) (he : e.Skips 1 j) : (e.inst a m).Skips 1 j
theorem VExpr.Skips.instAll (hj : j < k) (he : e.Skips 1 j) : (instAll e as k).Skips 1 j
theorem VExpr.skips_splitPis : S.Skips 1 t → (splitPis n S).1[k]? = some B → B.Skips 1 (k + t)
```

`instAll` at cut `i` touches only `J`'s parameters (indices `≥ i`); every earlier field sits
strictly below, and the entries it substitutes are lifted past the cut.  So the whole
obligation reduces to a `Skips` fact about `J`'s own constructor:

```lean
def VNestedOcc.SrcIndep (N H R C₀) : Prop :=
  ∀ i i' t F F', C₀.fields[i]? = some F → C₀.fields[i']? = some F' →
    ((N.field H R i' F').recArg).isSome → i' + 1 + t = i → (F.type.instL N.lvls).Skips 1 t

theorem VNestedOcc.bindersIndep (h : N.SrcIndep H R C₀) (i F r)
    (hF : (N.fieldsFrom H R 0 C₀.fields)[i]? = some F) (hr : F.recArg = some r) :
    r.BindersIndep ((N.fieldsFrom H R 0 C₀.fields).take i) i
```

`pfnOcc_srcIndep` discharges `SrcIndep` at the witness (`rfl` on the `Skips` equation).

**Open, and stated as such:** that `SrcIndep` holds for *every* well-formed `J`.  The argument
is the one `VIndRecArg.exists_indep` records — an earlier field becomes recursive exactly when
its `J`-type is a *parameter* position, and nothing in `J`'s own declaration can eliminate an
abstract parameter, so a later field's type cannot depend on its value.  Turning that into a
proof needs `IsDefEqU.forallE_inv` (`Typing/Injectivity.lean`, open).  `SrcIndep` is the
checkable statement that argument would discharge; the reduction *to* it is now a theorem.

## 7. Nested positivity (`NestedPositivity.lean`)

```lean
inductive Neg (α : Type) : Type where | mk : (α → False) → Neg α    -- fine: α is a parameter
inductive BadNest                     | mk : Neg BadNest → BadNest  -- must be refused
```

### Machine-checked, at the implementation

`NestedPositivity.lean`'s `run_meta` builds both declarations **by hand** (no elaborator) and
runs `Lean4Lean.addDecl` on them:

* the strictly positive control `OkNest`/`Wrap` is **accepted**;
* `BadNest` is **rejected**, and the assertion checks the message both says
  `non positive occurrence` and names a `_nested…` constant.  Lean's own kernel gives the same
  message: `arg #1 of '_nested.…Neg_1.mk' has a non positive occurrence of the datatypes being
  declared`.

So the claim "*nested positivity reduces to the auxiliary block's ordinary
`checkPositivity`*" — which `docs/handoff-nested-restore.md` recorded as **read off
`Add.lean`, not machine-checked** — is now checked at the level that matters: the rejection
happens in `AddInductive.run`'s ordinary positivity loop, on the *auxiliary* constructor.
This is the rejection witness the handoff asked for.

### Machine-checked, abstractly

`badAuxMk := negOcc.ctor badHeader badRestore negMk` is the construction of §2 applied to
`Neg`'s constructor at the instantiation `[BadNest]`:

| name | content |
|---|---|
| `badAuxMk_field_type` | the built field is `BadNest → False` — the same field the kernel names |
| `badAuxMk_recog_none` | `VIndRestore.recog … = none`: `VIndField.WF.pos`'s `some` branch is unavailable |
| `badAuxMk_field_recArg_none` | …so the built field is non-recursive |
| `badAuxMk_field_not_noBlock` | …and the obvious `none`-branch witness `A := F.type` is unavailable, because `F.type` mentions a block constant |
| `okAuxMk_field_recArg`, `okAuxMk_field_type` | accept control: the *good* nesting **is** recognised, so the `none` above discriminates |

### Still open, named

```lean
def badAux_pos_open (env : VEnv) (Γ : List VExpr) : Prop :=
  ¬ ∃ A, VExpr.NoConsts badBlockNames A ∧
    env.IsDefEqType 0 Γ (badAuxMk.fields.getD 0 default).type A
```

`VIndField.WF.pos`'s `none` branch is *definitional* block-freeness on purpose
(`Decl.lean`'s `(fun _ : T => Nat) r` example).  Every syntactic route is closed above; that no
*other* `A` works is a whnf-inversion statement about the staged environment, downstream of
`IsDefEqU.forallE_inv` exactly as `exists_indep` is.  **It was not attempted and remains
open.**

## 8. Universe-count agreement (item 4)

It is no longer a free-standing `Faithful` field.  `Faithful.ty_agree`/`ctor_agree`'s
`ci.uvars = (R.tyLvls j).length` conjunct is *derived* in `Built.toFaithful` from
`Occurs.lvls_len : N.lvls.length = N.decl.uvars` together with `Built.tyLvls`.  It is
discharged by `rfl` at both witnesses, and it is a hypothesis of `ctor_typeR` (without it the
level instantiation `ownLvls.map (·.inst ls) = ls` fails and the whole equation collapses), so
it is now *load-bearing* rather than decorative.

What is **still read off source**, unchanged: that `ElimNestedInductive` always establishes it
(`replaceIfNested` passes `I_lvls` from the occurrence and `st.lvls` for the auxiliary type).
That is a refinement-side obligation, §10.

## 9. Corrections to the relay

* `docs/handoff-nested-restore.md` §7.1 says the abstract `replaceIfNested` "must build the
  auxiliary member from `J` **with the instantiation**".  Right, but the *replacement* half —
  rewriting `J Ds π` back to `Iaux As π` — does not need to be modelled at all.  Recognising
  the **restored** shape against `R` gives `ctor_agree` unconditionally; modelling the
  replacement would have needed an inversion lemma between two functions and a canonicity
  hypothesis on `J`.
* The same §7.1 lists `ctor_agree` and `ctors_complete` as the places a caller can lie.
  `ty_agree` is one too (it pins only the member's stored *type*, not its indices or its field
  data) — §4 exhibits the slack.
* §5's "no nested witness with a non-empty `ξ` exists" was accurate; it is now false (§6).
* §5's "the rejection direction has no witness at all" was accurate about the *abstract*
  theory.  At the implementation a rejection witness was cheap, and it also settles the
  reduction claim (§7).  Nothing in the previous handoff suggested looking there.

## 10. What to pick up first

1. **`ElimNestedInductive` produces a `VNestedOcc`.**  The refinement-side obligation, and now
   a much smaller target than "produces a `Faithful` restoration": what must be shown is that
   the pass's `newTypes[k]` *is* `VNestedOcc.member` of the occurrence it recorded in
   `nestedAux`, and that its `Occurs` clauses hold.  Everything downstream is done.  This is
   also where lean4#14576/#14577 (the unchecked `Ds`) lives.
2. **`SrcIndep` for a general `J`** (§6), i.e. `VIndRecArg.exists_indep`'s open argument.  The
   reduction to it is proved; only the defeq step is missing.
3. **`badAux_pos_open`** (§7), the abstract rejection.  Same injectivity dependency.
4. **The `VDecl`/`Typing/Env.lean` flip**, unchanged from the previous handoff:
   `VEnv.AddNested_nil` is the conservativity theorem.  `AddNestedB` should be the clause, with
   `AddNestedB.toAddNested` bridging.  Do **not** flip `WF.ctors` onto `addIndTypesC`
   (`handoff-nested-restore.md` §3.3).
5. **A nested witness with indices**, and one nesting into a *mutual* `J`.  `VNestedOcc.idx`
   already ranges over `J`'s whole block (that is what `replaceIfNested` does for
   `I_val.all`), and `Built`'s `occ : Nat → VNestedOcc` already allows several auxiliary
   members, but neither is exercised: both witnesses nest a single-member, index-free `J`.
6. **The naming residue.**  `Built.ctorName_inv` is the one clause that is still an assertion,
   and it is about `Lean.Name` only (`restoreCtorName` inverts `replacePrefix`).  A
   `Name`-level lemma would remove it.

## 11. Inventory

**Proved (machine-checked).**  `VIndRestore.recogAt_sound`, `recog_sound`, `recogAt_idx`,
`recog_idx_lt`, `recogAt_binders`, `recog_binders`; `VExpr.mkApp_spineFn_spineArgs`,
`mkPi_splitPis`, `map_instAll_bvars_at`, `skips_liftN_lo`, `Skips.instN`, `Skips.instAll`,
`skips_splitPis`; `VNestedOcc.field_typeR`, `fieldTypes_from`, `ctor_fieldTypesR`,
`canonResult_instAll`, `ctor_typeR`, `instAt_eq`, `member_ctors_complete`, `ctor_Canonical`,
`member_Canonical`, `Occurs.src_mem`, `bindersIndep`; `VInductDecl'.Built.toFaithful`,
`Built.canonical`; `VEnv.AddNestedB.toAddNested`; witnesses `ntreeAux_member_built`,
`listOcc_recog_field0/1`, `listOcc_recog_field1_fails`, `listOcc_occurs`, `ntreeAux_built`,
`ntreeAuxI_faithful`, `ntreeAuxI_not_built`, `ntreeAux_AddNestedB`,
`ntreeAux_AddNested_of_built`, `ntreeRestore_faithful_of_built`, `nfnAux_member_built`,
`pfnAuxMk_xi_nonempty`, `pfnOcc_srcIndep`, `pfnAuxMk_bindersIndep`,
`pfnAuxMk_bindersIndep_nonvacuous`, `ntreeAux_binders_all_nil`, `nfnAux_WF`, `nfnAux_built`,
`nfnAux_AddNestedB`, `nfnAux_AddNested`; `badAuxMk_field_type`, `badAuxMk_recog_none`,
`badAuxMk_field_recArg_none`, `badAuxMk_field_not_noBlock`, `okAuxMk_field_recArg`,
`okAuxMk_field_type`; the `run_meta` accept/reject assertions.

**Stated, open.**  `VNestedOcc.SrcIndep` for a general `J`; `badAux_pos_open`.

**Read off source, not machine-checked.**  That `ElimNestedInductive` produces a `VNestedOcc`
satisfying `Occurs` (including `lvls_len`); that `restoreCtorName` inverts the auxiliary
constructor naming for every `J`.

**Refuted this round.**  Nothing.  §9 corrects four statements of the previous handoff, three
of which were true when written.
