import Lean4Lean.Theory.Inductive.CompanionResolve

/-!
# The nested head: `restoreNested` as a parameter of the recursor construction

`Theory/Inductive/CompanionResolve.lean` Part 9 cashed the down payment for the nested head:
`VInductDecl'.tyAppH` carries a **stored instantiation** and `tyAppH_bvars` pins it as a
generalisation of `VInductDecl'.tyApp`.  This file spends it.

## What the implementation actually does

Read off `Lean4Lean/Inductive/Add.lean` (`ElimNestedInductive`, `Environment.addInductive`),
for `inductive Tree (α) | node : α → List (Tree α) → Tree α`:

* `ElimNestedInductive.run` produces an **auxiliary block** whose members are the user's own
  types together with one fresh member per nested occurrence — here `_nested.List_1`, with
  the *block's* parameter telescope `[α]`, not `List`'s:

  ```
  _nested.List_1     : ∀ (α : Type), Type
  _nested.List_1.nil : ∀ (α : Type), _nested.List_1 α
  _nested.List_1.cons: ∀ (α : Type), Tree α → _nested.List_1 α → _nested.List_1 α
  Tree               : ∀ (α : Type), Type
  Tree.node          : ∀ (α : Type), α → _nested.List_1 α → Tree α
  ```

  **This is an ordinary mutual block.**  Nothing about `VInductDecl'` needs generalising to
  express it; `_nested.List_1.cons`'s first field is *recursive into `Tree`*, which is the
  entire content of nested induction.  `AddInductive.run` checks it as it stands.

* Only then does `restoreNested` act, and it acts on **what is emitted**, not on what is
  checked: the auxiliary type constants and their constructor constants are *never added*
  (`Environment.addInductive`'s final loop ranges over the user's `types` only), the user's
  constructor types are re-stored with `_nested.List_1 α` rewritten to `List (Tree α)`, and
  every recursor — the user's and the auxiliary ones — is added with its type and rules
  rewritten and, for the auxiliary ones, under a fresh name (`mkAuxRecNameMap`:
  `_nested.List_1.rec ↦ Tree.rec_1`).

So the companion member is `_nested.List_1`, and the three things restoration changes about
it are exactly: the head constant (`_nested.List_1 ↦ List`), the levels it is applied at, and
the parameter spine it is applied to (`α ↦ (Tree α)`).  Constructor names are rewritten the
same way (`restoreCtorName`), and recursor names by `mkAuxRecNameMap`.

`VIndRestore` below is that data, and `VInductDecl'.tyAppR`/`tyAppR'`/`ctorAppR` are
`tyApp`/`tyApp'`/`ctorApp'` with it applied.  `VInductDecl'.idRestore` is the identity
restoration, and every construction below is proved equal to its `Decl.lean` original there
— which is what makes this a *generalisation* rather than a second, unrelated spec.

## Corrections to `docs/handoff-nested-head.md`

Three claims relayed from earlier streams are wrong, and Part 7 refutes each at the witness.

1. **The companion member is not the declaring block's member, and `resolveC` is unavailable.**
   The companion is `_nested.List_1`, a name the history never declares, so
   `VInductDecl'.resolveC` returns `none` (`ntreeAux_resolveC_none`).  Naming the member `List`
   instead — the identification `Theory/Inductive/Companion.lean` makes — makes resolution fire
   and *destroys* the nested structure: `List`'s own `cons` has a non-recursive first field
   where the auxiliary member's has a recursive one, so the recursor loses the induction
   hypothesis for `NTree` (`ntreeAuxL_resolveC_loses_recursion`).
2. **The companion guards say nothing, or are false, on a real nested block.**
   `CompanionShape` is vacuous (`ntreeAux_CompanionShape_vacuous`) — so it is not a residue the
   head generalisation "removes"; `CompanionComplete` and `CompanionSound` are outright false
   (`ntreeAux_not_CompanionComplete`, `ntreeAux_not_CompanionSound`), because both ask the
   environment or the history for the *auxiliary* name.  `VIndRestore.Faithful` is the
   replacement, and it is discharged at the witness (`ntreeRestore_faithful`).
3. **`addInduct'` does not refuse a nested block, and G1's re-staging would break it.**
   The auxiliary member's name is fresh, so nothing is refused (`ntreeAux_allNames`): the
   abstract step succeeds, it just declares three constants restoration removes.  And
   `VInductDecl'.WFC`, which stages the constructor clause over `addIndTypesC`, drops the
   auxiliary type constant that `NTree.node`'s own stored field type mentions
   (`ntreeAux_staging`) — at that staging the clause is unsatisfiable, not merely weak.
   `VInductDecl'.WF` as it stands is the right predicate for the auxiliary block, and
   `ntreeAux_WF` is the witness.

None of this touches `fooComp_inconsistent`: a companion recursor with too few minor premises
is still unsound.  What moves is *which* statement rules it out —
`VIndRestore.Faithful.ctors_complete` rather than `VInductDecl'.CompanionComplete`.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars liftTele shift shiftTele)

/-! ### Moved to `Theory/Inductive/Restore.lean`

The restoration data (`VIndRestore`, `idRestore`, `tyAppR`/`tyAppR'`/`ctorAppR`), the whole of
Part 2's restored recursor construction, `VEnv.addInductR`, `VIndRestore.instAt`,
`VIndRestore.Faithful` and `VEnv.AddNested` now live in `Theory/Inductive/Restore.lean`,
**verbatim**.  They had to move *upstream of* `Theory/Typing/Env.lean` so that `VDecl.WF`
can name the nested step; this file keeps every theorem about them.  -/

namespace VInductDecl'
variable (D : VInductDecl') (R : VIndRestore)


@[simp] theorem tyAppR_id (j k : Nat) (args : List VExpr) :
    D.tyAppR D.idRestore j k args = D.tyApp j k args := D.tyAppH_bvars j k args

@[simp] theorem tyAppR'_id (j k : Nat) (args : List VExpr) :
    D.tyAppR' D.idRestore j k args = D.tyApp' j k args := by
  rw [tyAppR', idRestore]
  simp only [VInductDecl'.ownLvls_inst_selfLvls, VInductDecl'.atRecTele, VExpr.map_instL_bvars]
  exact D.tyAppH_bvars' j k args

@[simp] theorem ctorAppR_id (j : Nat) (C : VIndCtor) (k : Nat) (args : List VExpr) :
    D.ctorAppR D.idRestore j C k args = D.ctorApp' C k args := by
  rw [ctorAppR, ctorApp', idRestore]
  simp only [VInductDecl'.ownLvls_inst_selfLvls, VInductDecl'.atRecTele, VExpr.map_instL_bvars,
    VExpr.map_liftN_bvars_lo (Nat.le_refl 0), Nat.add_zero, id_eq]

end VInductDecl'


/-! ## Part 3: conservativity

Every construction of Part 2, at `D.idRestore`, **is** its `Theory/Inductive/Decl.lean`
original — **all of them unconditionally, since ruling 116d.**  They used to be conditional on
`VIndCtor.Canonical` / `VInductDecl'.Canonical`; `VIndField.typeR`'s `some` branch is now a
restoration of the *stored* type rather than a replacement of it, so the whole block collapses
through `VIndRestore.restore_id`, which has no hypotheses.  `VInductDecl'.Canonical` was
load-bearing nowhere else and is gone.

This is what makes Part 2 a generalisation rather than a rival specification, and it is what
lets `VEnv.addInductR` replace `VEnv.addInduct'` without disturbing anything already proved
about the latter (`addInductR_eq_addInduct'`). -/

@[simp] theorem VIndRecArg.canonResultR_id (r : VIndRecArg) (D : VInductDecl') (i : Nat) :
    r.canonResultR D D.idRestore i = r.canonResult D i :=
  D.tyAppR_id _ _ _

@[simp] theorem VIndRecArg.canonTypeR_id (r : VIndRecArg) (D : VInductDecl') (i : Nat) :
    r.canonTypeR D D.idRestore i = r.canonType D i := by
  rw [canonTypeR, canonType, canonResultR_id]

/-- **Unconditional since ruling 116d.**  It used to carry the field's canonicity as a
hypothesis, because `typeR`'s `some` branch replaced the stored type by `canonTypeR`; the branch
is now a restoration of the stored type, and at `idRestore` a restoration is the identity
(`VIndRestore.restore_id`) — for *every* expression, canonical or not. -/
@[simp] theorem VIndField.typeR_id {F : VIndField} {D : VInductDecl'} {i : Nat} :
    F.typeR D D.idRestore i = F.type := by
  rw [VIndField.typeR]
  split
  · rfl
  · exact VIndRestore.restore_id D i F.type

/-- Unconditional; was conditional on `C.Canonical D`. -/
theorem VIndCtor.fieldTypesR_id {C : VIndCtor} {D : VInductDecl'} :
    C.fieldTypesR D D.idRestore = C.fields.map (·.type) := by
  rw [VIndCtor.fieldTypesR]
  refine List.ext_getElem? fun n => ?_
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def,
    Nat.zero_add]
  cases hf : C.fields[n]? with
  | none => rfl
  | some F => exact congrArg some VIndField.typeR_id

/-- Unconditional; was conditional on `C.Canonical D`. -/
theorem VIndCtor.typeR_id {C : VIndCtor} {D : VInductDecl'} {j : Nat} :
    C.typeR D D.idRestore j = C.type D j := by
  rw [VIndCtor.typeR, VIndCtor.type, VIndCtor.canonResult, fieldTypesR_id,
    VInductDecl'.tyAppR_id]

namespace VInductDecl'
variable (D : VInductDecl')

@[simp] theorem motiveTypeR_id (t : Nat) : D.motiveTypeR D.idRestore t = D.motiveType t := by
  rw [motiveTypeR, motiveType, tyAppR'_id]

@[simp] theorem motivesR_id : D.motivesR D.idRestore = D.motives :=
  List.map_congr_left fun t _ => D.motiveTypeR_id t

theorem minorTypeR_id {q t : Nat} {C : VIndCtor} :
    D.minorTypeR D.idRestore q t C = D.minorType q t C := by
  rw [minorTypeR, minorType, VIndCtor.fieldTypesR_id, ctorAppR_id]

theorem mem_ctorsAll_of_mem_zipIdx {j q : Nat} {C : VIndCtor}
    (hm : ((j, C), q) ∈ D.ctorsAll.zipIdx) : (j, C) ∈ D.ctorsAll :=
  List.zipIdx_map_fst 0 D.ctorsAll ▸ List.mem_map_of_mem hm

theorem minorsR_id : D.minorsR D.idRestore = D.minors := by
  refine List.map_congr_left ?_
  rintro ⟨⟨t, C⟩, q⟩ -
  exact D.minorTypeR_id

theorem recTypeR_id (j : Nat) : D.recTypeR D.idRestore j = D.recType j := by
  rw [recTypeR, recType, tyAppR'_id, motivesR_id, D.minorsR_id]

theorem iotaCtxR_id {C : VIndCtor} :
    D.iotaCtxR D.idRestore C = D.iotaCtx C := by
  rw [iotaCtxR, iotaCtx, motivesR_id, D.minorsR_id, VIndCtor.fieldTypesR_id]

@[simp] theorem ihValuesR_id (C : VIndCtor) : D.ihValuesR D.idRestore C = D.ihValues C := by
  simp only [ihValuesR, ihValues, idRestore, id_eq]

theorem iotaLamR_id {q : Nat} {C : VIndCtor} :
    D.iotaLamR D.idRestore q C = D.iotaLam q C := by
  rw [iotaLamR, iotaLam, D.iotaCtxR_id, ihValuesR_id]

theorem iotaLhsR_id {j : Nat} {C : VIndCtor} :
    D.iotaLhsR D.idRestore j C = D.iotaLhs j C := by
  rw [iotaLhsR, iotaLhs, ctorAppR_id]; rfl

theorem iotaTypeR_id {j : Nat} {C : VIndCtor} :
    D.iotaTypeR D.idRestore j C = D.iotaType j C := by
  rw [iotaTypeR, iotaType, ctorAppR_id]

theorem iotaRuleR_id {j q : Nat} {C : VIndCtor} :
    D.iotaRuleR D.idRestore j q C = D.iotaRule j q C := by
  rw [iotaRuleR, iotaRule, D.iotaCtxR_id, iotaLhsR_id, D.iotaLamR_id, iotaTypeR_id]

theorem iotaRulesR_id : D.iotaRulesR D.idRestore = D.iotaRules := by
  refine List.map_congr_left ?_
  rintro ⟨⟨j, C⟩, q⟩ -
  exact D.iotaRuleR_id

theorem recConstsR_id : D.recConstsR D.idRestore [] = D.recConsts := by
  refine List.map_congr_left ?_
  rintro ⟨T, j⟩ -
  rw [idRestore]
  exact congrArg (fun e => (Lean.mkRecName T.name, (⟨D.recUvars, e⟩ : VConstant)))
    (by rw [VIndRestore.csubst_nil, VExpr.substC_id]; exact D.recTypeR_id j)

/-- The declared constructor constants are unchanged by the identity restoration.

**This used to hold for *every* companion list `K`, and now holds only at `K = []`.**  What
changed is that `ctorConstsCR` declares `(C.typeR D R j).substC (R.csubstTy D K)`, and at
`D.idRestore` a *companion* member's substitution value is `mkLams D.params (I_j.{ownLvls}
params)` — the **η-expansion** of `I_j`, not `I_j` — so at a nonempty `K` the declared type is
the stored one with each companion head η-expanded, which is defeq but not equal.  The
configuration is degenerate (`idRestore` presents a companion member as *itself*, which
`ElimNestedInductive` never does: the auxiliary name always differs from the real one), and
both consumers — `AddInductStages.toR` and `AddInductStagesR.of_addInductStages`
(`Verify/Environment/InductR.lean`) — are at `K = []`. -/
theorem ctorConstsCR_id :
    D.ctorConstsCR D.idRestore [] = D.ctorConstsC [] := by
  rw [ctorConstsCR, VInductDecl'.ctorConstsC]
  refine filterMap_congr_left ?_
  rintro ⟨j, C⟩ -
  simp only [idRestore, id_eq]
  split
  · rfl
  · exact congrArg some (congrArg (fun e => (C.name, (⟨D.uvars, e⟩ : VConstant)))
      (by rw [VIndRestore.csubstTy_nil, VExpr.substC_id]; exact VIndCtor.typeR_id))


theorem allConstsCR_id_nil :
    D.allConstsCR D.idRestore [] = D.allConsts := by
  rw [allConstsCR, VInductDecl'.allConsts, typeConstsC_nil, D.ctorConstsCR_id,
    ctorConstsC_nil, D.recConstsR_id]

end VInductDecl'

/-- At `K = []` the substitution `addIndRulesR` now applies is the identity
(`VIndRestore.csubst_nil`), so the identity restoration still folds exactly `addIndRules`'
list.  This is what keeps conservativity a `rfl`-level fact after the substitution landed. -/
theorem VInductDecl'.iotaRulesRS_id_nil {D : VInductDecl'} :
    D.iotaRulesRS D.idRestore [] = D.iotaRules := by
  rw [VInductDecl'.iotaRulesRS, VIndRestore.csubst_nil, ← D.iotaRulesR_id]
  refine List.map_congr_left (fun df _ => ?_) |>.trans (List.map_id _)
  cases df; simp [VDefEq.substC]

theorem VEnv.addIndRulesR_id (env : VEnv) {D : VInductDecl'} :
    env.addIndRulesR D [] D.idRestore = env.addIndRules D := by
  rw [VEnv.addIndRulesR, VEnv.addIndRules, VInductDecl'.iotaRulesRS_id_nil]

/-- **Conservativity of the repaired step.**  With no companion members and the identity
restoration, `addInductR` *is* `addInduct'`. -/
theorem VEnv.addInductR_eq_addInduct' (env : VEnv) {D : VInductDecl'} :
    env.addInductR D [] D.idRestore = env.addInduct' D := by
  rw [VEnv.addInductR, D.allConstsCR_id_nil, VEnv.addInduct'_eq]
  cases env.addConstList D.allConsts with
  | none => rfl
  | some env₁ => exact congrArg some (VEnv.addIndRulesR_id env₁)

/-! ## Part 4: G4, repaired — and the invariant whose absence hid it

`docs/handoff-nested-head.md` §4 records G4: `VEnv.addInductC` threads the recursor renaming
into `recConstsC` and stops, so it **declares** `rn (mkRecName J)` and **emits its ι-rules
under `mkRecName J`**.  `VInductDecl'.key_iotaRule_ne_renamed` is the core of that; what was
missing is the *invariant* the defect violates, because no field of any `WF` predicate says
anything about which constant an emitted rule is keyed on.

Here it is, and it holds of the repaired step by construction:

> **every ι-rule the step emits is keyed to a recursor constant the same step declares.**

Both halves are needed.  `key_iotaRuleR` computes the key from `iotaLhsR`; `recName_mem_allNamesCR`
says the name it computes is one of the step's own constants. -/

theorem VInductDecl'.headName_ctorAppR (D : VInductDecl') (R : VIndRestore) (j : Nat)
    (C : VIndCtor) (k : Nat) (args : List VExpr) :
    VExpr.headName (D.ctorAppR R j C k args) = some (R.ctorName C.name) := by
  rw [VInductDecl'.ctorAppR, VExpr.headName_mkApp]

/-- **The restored ι-rule's key**: the *renamed* recursor of its own type, then the *restored*
constructor name.  Compare `VInductDecl'.key_iotaRule`, where both are un-renamed. -/
theorem VInductDecl'.key_iotaRuleR (D : VInductDecl') (R : VIndRestore) (j q : Nat)
    (C : VIndCtor) :
    (D.iotaRuleR R j q C).key
      = [R.recName (Lean.mkRecName (D.types.getD j default).name), R.ctorName C.name] := by
  show ((VExpr.peelLams (VExpr.mkLams (D.iotaCtxR R C) (D.iotaLhsR R j C))).2 |> fun b =>
    (VExpr.headName b).toList ++ ((VExpr.spine b).2.getLast?.bind VExpr.headName).toList) = _
  rw [VExpr.peelLams_mkLams]
  rw [show (VExpr.peelLams (D.iotaLhsR R j C)).2 = D.iotaLhsR R j C from by
    rw [VInductDecl'.iotaLhsR, VExpr.mkApp_concat]; rfl]
  simp only [VInductDecl'.iotaLhsR, VExpr.headName_mkApp,
    VExpr.spine_mkApp (e := VExpr.const
      (R.recName (Lean.mkRecName (D.types.getD j default).name))
      (VLevel.params D.recUvars)) (by nofun)]
  simp [List.getLast?_append, VInductDecl'.headName_ctorAppR]

/-- A constant applied to a spine has no leading λ to peel — so `VDefEq.key` reads the whole
spine.  (`Theory/Typing/StructureRuleFree.lean` has this as `peelLams_snd_mkApp_const`, but
that file imports `Injectivity.lean` and is not in this cone.) -/
theorem VExpr.peelLams_snd_mkApp_notLam : ∀ (as : List VExpr) {f : VExpr},
    (∀ A b, f ≠ .lam A b) → (VExpr.peelLams (f.mkApp as)).2 = f.mkApp as
  | [], f, hf => by
    cases f
    case lam A b => exact absurd rfl (hf A b)
    all_goals rfl
  | _ :: as, f, _ => by
    rw [VExpr.mkApp_cons]
    exact peelLams_snd_mkApp_notLam as (f := .app f _) nofun

/-- **The key of a declaration-shaped rule, computed.**  `VDefEq.key` peels the λs, reads the
head constant, then the head constant of the spine's last argument; for a `mkLams`-over-a-
constant-spine left-hand side that is exactly the head plus the last argument's head.

`key_iotaRuleR` above is the unsubstituted instance; the point of having it in general is that
`VEnv.addIndRulesR` registers a `substC` of that shape, and `substC` preserves the shape. -/
theorem VDefEq.key_of_lhs {df : VDefEq} {G as : List VExpr} {c : Lean.Name}
    {ls : List VLevel} {m : VExpr}
    (h : df.lhs = VExpr.mkLams G ((VExpr.const c ls).mkApp as))
    (hm : as.getLast? = some m) :
    df.key = c :: (VExpr.headName m).toList := by
  have hpeel : (VExpr.peelLams df.lhs).2 = (VExpr.const c ls).mkApp as := by
    rw [h, VExpr.peelLams_mkLams]
    exact VExpr.peelLams_snd_mkApp_notLam as (f := VExpr.const c ls) (by nofun)
  show ((VExpr.headName (VExpr.peelLams df.lhs).2).toList ++
    (((VExpr.spine (VExpr.peelLams df.lhs).2).2.getLast?).bind VExpr.headName).toList) = _
  rw [hpeel, VExpr.headName_mkApp, VExpr.spine_mkApp (e := VExpr.const c ls) (by nofun), hm]
  rfl

/-- **…and substituting does not move it.**  `VEnv.addIndRulesR` registers
`(D.iotaRuleR R j q C).substC σ`, and `substC` is structural, so the left-hand side stays a
`mkLams` over a constant spine whose last argument stays headed by the restored constructor —
*provided* neither head is in σ's domain, which is `VIndRestore.KeysFree`.

This is the fact the closing note of the previous revision of
`Theory/Inductive/NestedOrdered.lean` said "needs `Faithful` plus freshness of the auxiliary
names, not `rfl`".  It needs neither: it needs exactly the two `σ … = none` side conditions,
and the audit of where *those* come from is at `VIndRestore.KeysFree`
(`Theory/Inductive/Restore.lean`). -/
theorem VInductDecl'.key_iotaRuleR_substC (D : VInductDecl') (R : VIndRestore) {σ : CSubst}
    (j q : Nat) (C : VIndCtor)
    (hrec : σ (R.recName (Lean.mkRecName (D.types.getD j default).name)) = none)
    (hctor : σ (R.ctorName C.name) = none) :
    ((D.iotaRuleR R j q C).substC σ).key
      = [R.recName (Lean.mkRecName (D.types.getD j default).name), R.ctorName C.name] := by
  have hlhs : ((D.iotaRuleR R j q C).substC σ).lhs
      = VExpr.mkLams ((D.iotaCtxR R C).map (VExpr.substC · σ))
          ((VExpr.const (R.recName (Lean.mkRecName (D.types.getD j default).name))
            (VLevel.params D.recUvars)).mkApp
              ((VExpr.bvars (C.fields.length + (D.nm + D.nmin)) D.np ++
                VExpr.bvars (C.fields.length + D.nmin) D.nm ++
                VExpr.bvars C.fields.length D.nmin ++
                C.args.map (fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length) ++
                [D.ctorAppR R j C (C.fields.length + (D.nm + D.nmin))
                  (VExpr.bvars 0 C.fields.length)]).map (VExpr.substC · σ))) := by
    show ((VExpr.mkLams (D.iotaCtxR R C) (D.iotaLhsR R j C)).substC σ) = _
    rw [VExpr.substC_mkLams, VInductDecl'.iotaLhsR, VExpr.substC_mkApp,
      VExpr.substC_const_none hrec]
  rw [VDefEq.key_of_lhs hlhs (m := (D.ctorAppR R j C (C.fields.length + (D.nm + D.nmin))
        (VExpr.bvars 0 C.fields.length)).substC σ) (by simp [List.getLast?_append]),
    VInductDecl'.ctorAppR, VExpr.substC_mkApp, VExpr.substC_const_none hctor,
    VExpr.headName_mkApp]
  rfl

/-- No substituted restored ι-rule is a δ-rule: its key has two names, a δ-rule's has one. -/
theorem VInductDecl'.not_isDeltaRule_iotaRuleR_substC (D : VInductDecl') (R : VIndRestore)
    {σ : CSubst} (j q : Nat) (C : VIndCtor)
    (hrec : σ (R.recName (Lean.mkRecName (D.types.getD j default).name)) = none)
    (hctor : σ (R.ctorName C.name) = none) :
    ∀ c, ¬ VEnv.IsDeltaRule ((D.iotaRuleR R j q C).substC σ) c := by
  intro c hd
  have hk := VEnv.key_of_isDeltaRule hd
  rw [D.key_iotaRuleR_substC R j q C hrec hctor] at hk
  exact absurd hk (by simp)

/-- Every rule of `iotaRulesR` is an `iotaRuleR` of a constructor of the block. -/
theorem VInductDecl'.mem_iotaRulesR {D : VInductDecl'} {R : VIndRestore} {df : VDefEq}
    (h : df ∈ D.iotaRulesR R) :
    ∃ j C, (j, C) ∈ D.ctorsAll ∧
      df.key = [R.recName (Lean.mkRecName (D.types.getD j default).name), R.ctorName C.name] := by
  rw [VInductDecl'.iotaRulesR, List.mem_map] at h
  obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := h
  exact ⟨j, C, D.mem_ctorsAll_of_mem_zipIdx hm, D.key_iotaRuleR R j q C⟩

/-- The renamed recursor of any member is one of the step's own declared names. -/
theorem VInductDecl'.recName_mem_allNamesCR (D : VInductDecl') (R : VIndRestore)
    (K : List Lean.Name) {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    R.recName (Lean.mkRecName (D.types.getD j default).name) ∈ D.allNamesCR R K := by
  rw [VInductDecl'.getD_types hT, VInductDecl'.allNamesCR]
  refine List.mem_map_of_mem (f := (·.1))
    (a := (R.recName (Lean.mkRecName T.name),
      (⟨D.recUvars, (D.recTypeR R j).substC (R.csubst D K)⟩ : VConstant))) ?_
  simp only [VInductDecl'.allConstsCR, List.mem_append]
  exact .inr (List.mem_map_of_mem (List.mk_mem_zipIdx_iff_getElem?.2 hT))

/-- **The invariant.**  Every ι-rule `VEnv.addInductR` emits is keyed to a recursor constant
that the same step declares.

This is the statement no `WF` field expresses and whose absence made G4 invisible: `WF`
constrains the *types* of the constants a block declares and the *typing* of its rules, never
the identity of the constant a rule reduces.  It is stated about the constant list and the
rule list directly, so it is checkable on the definitions alone. -/
theorem VInductDecl'.iotaRulesR_key_declared (D : VInductDecl') (R : VIndRestore)
    (K : List Lean.Name) {df : VDefEq} (h : df ∈ D.iotaRulesR R) :
    ∃ n, df.key.head? = some n ∧ n ∈ D.allNamesCR R K := by
  obtain ⟨j, C, hjC, hk⟩ := VInductDecl'.mem_iotaRulesR h
  obtain ⟨T, hT, -⟩ := VInductDecl'.mem_ctorsAll hjC
  exact ⟨_, by rw [hk]; rfl, D.recName_mem_allNamesCR R K hT⟩

/-- Every rule `VEnv.addIndRulesR` actually registers is a substituted restored ι-rule of a
constructor of the block, and — under `KeysFree` — carries the *same* key as the unsubstituted
one.  This is the lemma that lets every `key`-based argument keep reading
`key_iotaRuleR` after the substitution landed. -/
theorem VInductDecl'.mem_iotaRulesRS {D : VInductDecl'} {R : VIndRestore} {K : List Lean.Name}
    {df : VDefEq} (hfree : R.KeysFree D K) (h : df ∈ D.iotaRulesRS R K) :
    ∃ j C, (j, C) ∈ D.ctorsAll ∧
      df.key
        = [R.recName (Lean.mkRecName (D.types.getD j default).name), R.ctorName C.name] := by
  rw [VInductDecl'.iotaRulesRS, List.mem_map] at h
  obtain ⟨df₀, hdf₀, rfl⟩ := h
  rw [VInductDecl'.iotaRulesR, List.mem_map] at hdf₀
  obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := hdf₀
  have hm' := D.mem_ctorsAll_of_mem_zipIdx hm
  obtain ⟨h1, h2⟩ := hfree (j, C) hm'
  exact ⟨j, C, hm', D.key_iotaRuleR_substC R j q C h1 h2⟩

/-- `iotaRulesR_key_declared` for the rules the step really emits. -/
theorem VInductDecl'.iotaRulesRS_key_declared (D : VInductDecl') (R : VIndRestore)
    (K : List Lean.Name) (hfree : R.KeysFree D K) {df : VDefEq} (h : df ∈ D.iotaRulesRS R K) :
    ∃ n, df.key.head? = some n ∧ n ∈ D.allNamesCR R K := by
  obtain ⟨j, C, hjC, hk⟩ := VInductDecl'.mem_iotaRulesRS hfree h
  obtain ⟨T, hT, -⟩ := VInductDecl'.mem_ctorsAll hjC
  exact ⟨_, by rw [hk]; rfl, D.recName_mem_allNamesCR R K hT⟩

/-- …and it survives the step: the constant the rule is keyed on is present in the resulting
environment, at the recursor type the step gave it. -/
theorem VEnv.addInductR_key_declared {env env' : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} (hadd : env.addInductR D K R = some env') (hfree : R.KeysFree D K)
    {df : VDefEq}
    (h : df ∈ D.iotaRulesRS R K) : ∃ n, df.key.head? = some n ∧ env'.contains n := by
  obtain ⟨n, hn, hmem⟩ := D.iotaRulesRS_key_declared R K hfree h
  refine ⟨n, hn, ?_⟩
  rw [VInductDecl'.allNamesCR, List.mem_map] at hmem
  obtain ⟨c, hc, rfl⟩ := hmem
  rw [VEnv.addInductR, Option.map_eq_some_iff] at hadd
  obtain ⟨env₁, h1, rfl⟩ := hadd
  refine ⟨c.2, ?_⟩
  rw [VEnv.addIndRulesR, VEnv.addDefEqList_constants]
  exact VEnv.addConstList_constants h1 c hc

/-- **The negative, at the same granularity.**  For the *unrepaired* `VEnv.addInductC` the
invariant fails: the rule head is the un-renamed `mkRecName J`, and under a renaming that
actually renames — the nested path's own (`fooCompRec_ne_mkRecName`) — that is not among the
recursor names the step declares.

The hypothesis is exactly "the block declares no constant called `mkRecName J`", which for a
companion block is the situation `Companion.lean` puts it in: `J` is not declared (it is
already there), so neither is `J.rec`. -/
theorem VInductDecl'.iotaRule_key_not_declared (D : VInductDecl') (K : List Lean.Name)
    (rn : Lean.Name → Lean.Name) (j q : Nat) (C : VIndCtor)
    (hnd : Lean.mkRecName (D.types.getD j default).name ∉ D.allNamesC K rn) :
    ∃ n, (D.iotaRule j q C).key.head? = some n ∧ n ∉ D.allNamesC K rn :=
  ⟨_, by rw [D.key_iotaRule j q C]; rfl, hnd⟩

/-! ## Part 5: the step's structural facts, and the restoration's obligations

The `Companion.lean` facts about `addInductC` carry over verbatim: the constant list is what
changed, not the way it is added. -/

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'} {R : VIndRestore} {K : List Lean.Name}

theorem addInductR_le (h : env.addInductR D K R = some env') : env ≤ env' := by
  rw [VEnv.addInductR, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  exact (addConstList_le h1).trans (VEnv.addDefEqList_le _ _)

theorem addInductR_constants (h : env.addInductR D K R = some env') :
    ∀ c ∈ D.allConstsCR R K, env'.constants c.1 = some c.2 := by
  rw [VEnv.addInductR, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  intro c hc
  rw [VEnv.addIndRulesR, VEnv.addDefEqList_constants]
  exact addConstList_constants h1 c hc

theorem addInductR_constants_of_not_mem {n : Lean.Name} (h : env.addInductR D K R = some env')
    (hn : n ∉ D.allNamesCR R K) : env'.constants n = env.constants n := by
  rw [VEnv.addInductR, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rw [VEnv.addIndRulesR, VEnv.addDefEqList_constants]
  exact addConstList_constants_of_not_mem h1 hn

theorem addInductR_eq_some_iff :
    (∃ env', env.addInductR D K R = some env') ↔
      (∀ n ∈ D.allNamesCR R K, env.constants n = none) ∧ (D.allNamesCR R K).Nodup := by
  simp only [VInductDecl'.allNamesCR]
  rw [← addConstList_eq_some_iff (cs := D.allConstsCR R K)]
  constructor
  · rintro ⟨env', h⟩
    rw [VEnv.addInductR, Option.map_eq_some_iff] at h
    exact ⟨_, h.choose_spec.1⟩
  · rintro ⟨env₁, h⟩
    exact ⟨_, by rw [VEnv.addInductR, h]; rfl⟩

/-- Every ι-rule the step emits is in the resulting environment's `defeqs`.  Since
2026-08-31 the rules it emits are `iotaRulesRS` — the restored rules *substituted* — so this
is stated about those. -/
theorem addInductR_defeqs (h : env.addInductR D K R = some env') :
    ∀ df ∈ D.iotaRulesRS R K, env'.defeqs df := by
  rw [VEnv.addInductR, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  exact VEnv.addDefEqList_defeqs _ _

end VEnv

/-! ### What the restoration owes

A restoration is not free: presenting an auxiliary member as `J.{ls} A` is a claim that `J`
instantiated at `A` *is* that member.  `instAt` is the instantiation — strip `J`'s own
parameter binders and substitute `A`, then re-abstract over the block's parameters — and
`Faithful` is the claim.

Note where the burden falls.  `ty_agree` and `ctor_agree` are equations between the
auxiliary block's own data and the *stored* types of constants the environment already holds,
so they are checkable without any typing judgement.  `ctors_complete` is **G2 for the nested
model**: the auxiliary member's constructor list, restored, must be all of `J`'s — the
`fooComp_inconsistent` failure mode transplanted, and the one obligation resolution was
introduced to discharge. -/


/-- **Conservativity.**  With no auxiliary members and the identity restoration, the step is
**exactly** `VDecl.WF.induct`'s premise pair — no new obligation on, and none removed from, any
existing declaration.  It used to carry `hc : D.Canonical` on **both** sides, as a hypothesis
*and* as a conjunct of `AddNested`; since ruling 116d neither is there.  `Faithful` is vacuous at
`K = []`, which is the formal content of "a block with no nested occurrence needs no
restoration". -/
theorem VEnv.AddNested_nil {env env' : VEnv} {D : VInductDecl'} {npJ : Nat → Nat} :
    VEnv.AddNested env D [] D.idRestore npJ env' ↔ D.WF env ∧ env.addInduct' D = some env' := by
  rw [VEnv.AddNested, VEnv.addInductR_eq_addInduct' env]
  constructor
  · rintro ⟨h1, -, -, h4⟩; exact ⟨h1, h4⟩
  · rintro ⟨h1, h4⟩
    exact ⟨h1, D.idRestore_ownId [],
      ⟨by rintro _ _ _ ⟨⟩, by rintro _ _ _ ⟨⟩, by rintro _ _ _ ⟨⟩⟩, h4⟩

/-- **G4 travels with the step.**  Every ι-rule the step emits is keyed to a constant the step
declares, and that constant is present in the resulting environment. -/
theorem VEnv.AddNested_keys_declared {env env' : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} {R : VIndRestore} {npJ : Nat → Nat}
    (h : VEnv.AddNested env D K R npJ env') {df : VDefEq} (hdf : df ∈ D.iotaRulesR R) :
    ∃ n, df.key.head? = some n ∧ n ∈ D.allNamesCR R K ∧ env'.contains n := by
  obtain ⟨n, hn, hmem⟩ := D.iotaRulesR_key_declared R K hdf
  refine ⟨n, hn, hmem, ?_⟩
  rw [VInductDecl'.allNamesCR, List.mem_map] at hmem
  obtain ⟨c, hc, rfl⟩ := hmem
  exact ⟨c.2, VEnv.addInductR_constants h.2.2.2 c hc⟩


/-! ## Part 7: a real nested block, end to end

`Tree α` with a constructor taking `List (Tree α)` — the canonical nested declaration, and the
one `docs/handoff-nested-head.md` names.  Lean's own kernel runs the nested elimination on the
declaration below, so `NTree.rec`, `NTree.rec_1` and their stored reduction rules are **ground
truth**, not a transcription of this specification: the checks marked `vconst(type_of% …)` and
`vrecrule(…, i)` read the environment.

Everything in this section is `rfl` or `decide`.  The point of the section is that it is not
an argument. -/

namespace InductiveDeclExamples

universe u

/-- The motivating declaration.  Its elimination produces one auxiliary member. -/
inductive NTree (α : Type u) where
  | node : α → List (NTree α) → NTree α

/-! ### The auxiliary block, as `ElimNestedInductive.run` produces it

`_nested.List_1` carries **the block's** parameter telescope `[α : Type u]`, not `List`'s, and
`_nested.List_1.cons`'s first field is *recursive into `NTree`* — the parameter position of
`List` has become a recursive position.  That is the whole content of nested induction, and it
is why the auxiliary block is an ordinary mutual inductive that needs no new spec. -/

def ntreeNode : VIndCtor where
  name := ``NTree.node
  params := [.sort (.succ (.param 0))]
  fields :=
    [{ type := .bvar 0, lvl := .succ (.param 0), recArg := none },
     { type := .app (.const `_nested.List_1 [.param 0]) (.bvar 1), lvl := .succ (.param 0),
       recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def nlistNil : VIndCtor where
  name := `_nested.List_1.nil
  params := [.sort (.succ (.param 0))]
  fields := []
  args := []

def nlistCons : VIndCtor where
  name := `_nested.List_1.cons
  params := [.sort (.succ (.param 0))]
  fields :=
    [{ type := .app (.const ``NTree [.param 0]) (.bvar 0), lvl := .succ (.param 0),
       recArg := some { binders := [], idx := 0, args := [] } },
     { type := .app (.const `_nested.List_1 [.param 0]) (.bvar 1), lvl := .succ (.param 0),
       recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def ntreeAux : VInductDecl' where
  uvars := 1
  params := [.sort (.succ (.param 0))]
  lvl := .succ (.param 0)
  isLE := true
  types :=
    [{ name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
       indices := [], ctors := [ntreeNode] },
     { name := `_nested.List_1,
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
       indices := [], ctors := [nlistNil, nlistCons] }]

/-- The companion list: the auxiliary member, which is never declared. -/
def ntreeK : List Lean.Name := [`_nested.List_1]

example : ntreeAux.nm = 2 := rfl
example : ntreeAux.nmin = 3 := rfl
example : ntreeAux.ctorsAll = [(0, ntreeNode), (1, nlistNil), (1, nlistCons)] := rfl
example : ntreeAux.recUvars = 2 := rfl

/-- The block is canonical: both recursive fields are stored in their canonical form, which is
what `ElimNestedInductive` produces. -/
theorem ntreeAux_Canonical : ntreeAux.Canonical := by
  intro j C hC i F r hF hr
  rw [show ntreeAux.ctorsAll = [((0 : Nat), ntreeNode), (1, nlistNil), (1, nlistCons)] from rfl] at hC
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hC
  · match i, hF with
    | 0, hF => simp [ntreeNode] at hF; subst hF; simp at hr
    | 1, hF => simp [ntreeNode] at hF; subst hF; cases hr; rfl
    | (_ + 2), hF => simp [ntreeNode] at hF
  · simp [nlistNil] at hF
  · match i, hF with
    | 0, hF => simp [nlistCons] at hF; subst hF; cases hr; rfl
    | 1, hF => simp [nlistCons] at hF; subst hF; cases hr; rfl
    | (_ + 2), hF => simp [nlistCons] at hF

/-! ### The restoration, as `restoreNested`/`mkAuxRecNameMap` produce it -/

def ntreeRestore : VIndRestore where
  tyName j := if j = 1 then ``List else ``NTree
  tyLvls _ := [.param 0]
  tyArgs j := if j = 1 then [.app (.const ``NTree [.param 0]) (.bvar 0)] else [.bvar 0]
  ctorName n := if n = `_nested.List_1.nil then ``List.nil
                else if n = `_nested.List_1.cons then ``List.cons else n
  recName n := if n = `_nested.List_1.rec then ``NTree.rec_1 else n

/-- **The restoration is the identity on `NTree`**, the member the step declares: it is only
`_nested.List_1` that is renamed, re-levelled and re-instantiated.  This is
`VIndRestore.OwnId`, the clause `Faithful` cannot state because all three of its clauses are
guarded by `T.name ∈ K`. -/
theorem ntreeRestore_ownId : ntreeRestore.OwnId ntreeAux ntreeK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [ntreeAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [ntreeAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [ntreeAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [ntreeAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [ntreeAux] at hT

/-! ### The payoff: the restored declarations, against Lean's own

These are the checks the head generalisation exists for.  Without a stored instantiation the
left-hand sides would be headed `_nested.List_1 α`; Lean's are headed `List (NTree α)`. -/

/-- The user's constructor, re-stored. -/
theorem ntreeNode_typeR : ntreeNode.typeR ntreeAux ntreeRestore 0
    = (vconst(type_of% @NTree.node)).type := rfl

/-- **…and the substitution `VInductDecl'.ctorConstsCR` applies to it changes nothing.**

This is the faithfulness half of that `substC` (added 2026-08-31 to close obligation (A)'s
`RestoreClean` hole — see `ctorConstsCR`): the type the step declares is *still* the type
Lean's own kernel stores for `NTree.node`, at a block with a parameter, where the rewrite had
every chance to move something.  It cannot: `typeR` has already restored every position
`ElimNestedInductive` put `_nested.List_1` in, so the substitution's domain does not occur.

Note what this pins about the *shape*: Lean's stored type is `restoreNested`'s output, i.e.
the **contracted** `List (NTree α)`, not the β-redex `(fun α => List (NTree α)) α` that
`VExpr.substC` of the auxiliary type would give (`ntreeNode_substC_ne_typeR`,
`Theory/Typing/ConstSubstNested.lean`).  So "`typeR` *is* the substitution" is not available as
a definition: `TrConstant` (`Verify/Environment/Basic.lean`) relates the two through
`TrExprS`, which has no defeq slack. -/
theorem ntreeNode_declared_typeR :
    (ntreeNode.typeR ntreeAux ntreeRestore 0).substC (ntreeRestore.csubstTy ntreeAux ntreeK)
      = (vconst(type_of% @NTree.node)).type := rfl

/-- The same for the two recursors, whose declared types `recConstsR` now substitutes too. -/
theorem ntreeAux_declared_recTypeR_0 :
    swap01 ((ntreeAux.recTypeR ntreeRestore 0).substC (ntreeRestore.csubst ntreeAux ntreeK))
      = (vconst(type_of% @NTree.rec)).type := rfl

theorem ntreeAux_declared_recTypeR_1 :
    swap01 ((ntreeAux.recTypeR ntreeRestore 1).substC (ntreeRestore.csubst ntreeAux ntreeK))
      = (vconst(type_of% @NTree.rec_1)).type := rfl

theorem ntreeAux_recUvars_eq : ntreeAux.recUvars = (vconst(type_of% @NTree.rec)).uvars := rfl

/-- **`NTree.rec`'s type**, with `List (NTree α)` in both motive and minor premises. -/
theorem ntreeAux_recTypeR_0 : swap01 (ntreeAux.recTypeR ntreeRestore 0)
    = (vconst(type_of% @NTree.rec)).type := rfl

/-- **`NTree.rec_1`'s type** — the *companion's* recursor, the one G4 is about. -/
theorem ntreeAux_recTypeR_1 : swap01 (ntreeAux.recTypeR ntreeRestore 1)
    = (vconst(type_of% @NTree.rec_1)).type := rfl

/-- **The three ι-rule right-hand sides, against the rules Lean actually stores.**  Two of
them belong to `NTree.rec_1`, the companion recursor: with G4 unrepaired they would be keyed
on `_nested.List_1.rec`, a constant no step declares. -/
theorem ntreeAux_iotaLamR_0 : ntreeAux.iotaLamR ntreeRestore 0 ntreeNode
    = vrecrule(NTree.rec, 0) := rfl

theorem ntreeAux_iotaLamR_1 : ntreeAux.iotaLamR ntreeRestore 1 nlistNil
    = vrecrule(NTree.rec_1, 0) := rfl

theorem ntreeAux_iotaLamR_2 : ntreeAux.iotaLamR ntreeRestore 2 nlistCons
    = vrecrule(NTree.rec_1, 1) := rfl

/-! ### G4, at the witness: declared constants and emitted rule keys agree -/

/-- The step declares exactly what `Environment.addInductive` adds: the user's type, the
user's constructor, and **both** recursors — the auxiliary type and its constructors are not
declared at all. -/
theorem ntreeAux_allNamesCR : ntreeAux.allNamesCR ntreeRestore ntreeK =
    [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1] := rfl

theorem ntreeAux_key_0 : (ntreeAux.iotaRuleR ntreeRestore 0 0 ntreeNode).key
    = [``NTree.rec, ``NTree.node] :=
  ntreeAux.key_iotaRuleR ntreeRestore 0 0 ntreeNode

theorem ntreeAux_key_1 : (ntreeAux.iotaRuleR ntreeRestore 1 1 nlistNil).key
    = [``NTree.rec_1, ``List.nil] :=
  ntreeAux.key_iotaRuleR ntreeRestore 1 1 nlistNil

theorem ntreeAux_key_2 : (ntreeAux.iotaRuleR ntreeRestore 1 2 nlistCons).key
    = [``NTree.rec_1, ``List.cons] :=
  ntreeAux.key_iotaRuleR ntreeRestore 1 2 nlistCons

/-- …and every one of those keys names a constant the same step declares. -/
theorem ntreeAux_keys_declared (df : VDefEq) (h : df ∈ ntreeAux.iotaRulesR ntreeRestore) :
    ∃ n, df.key.head? = some n ∧ n ∈ ntreeAux.allNamesCR ntreeRestore ntreeK :=
  ntreeAux.iotaRulesR_key_declared ntreeRestore ntreeK h

/-- **The unrepaired step fails the same test.**  `VEnv.addInductC`'s ι-rules are keyed on
`_nested.List_1.rec`, which is not among the four names it declares. -/
theorem ntreeAux_iotaRule_key_not_declared (q : Nat) (C : VIndCtor) :
    ∃ n, (ntreeAux.iotaRule 1 q C).key.head? = some n ∧
      n ∉ ntreeAux.allNamesC ntreeK ntreeRestore.recName :=
  ntreeAux.iotaRule_key_not_declared ntreeK ntreeRestore.recName 1 q C (by decide)

/-! ### `List`, as a block of the declaration history -/

def listNil : VIndCtor where
  name := ``List.nil
  params := [.sort (.succ (.param 0))]
  fields := []
  args := []

def listCons : VIndCtor where
  name := ``List.cons
  params := [.sort (.succ (.param 0))]
  fields :=
    [{ type := .bvar 0, lvl := .succ (.param 0), recArg := none },
     { type := .app (.const ``List [.param 0]) (.bvar 1), lvl := .succ (.param 0),
       recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

def listType : VIndType where
  name := ``List
  type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
  indices := []
  ctors := [listNil, listCons]

def listDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.succ (.param 0))]
  lvl := .succ (.param 0)
  isLE := true
  types := [listType]

example : listType.type = (vconst(type_of% @List)).type := rfl
example : listNil.type listDecl 0 = (vconst(type_of% @List.nil)).type := rfl
example : listCons.type listDecl 0 = (vconst(type_of% @List.cons)).type := rfl
example : swap01 (listDecl.recType 0) = (vconst(type_of% @List.rec)).type := rfl

/-! ### The restoration is faithful -/

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

theorem list_const : env₁.constants ``List = some ⟨1, listType.type⟩ :=
  VEnv.addInduct'_types h (List.Mem.head _)

theorem listNil_const : env₁.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.head _)

theorem listCons_const : env₁.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.tail _ (List.Mem.head _))

/-- **The restoration's obligations, discharged at the witness.**  Every equation is `rfl`:
`List`'s stored type and constructor types, instantiated at `[NTree α]` and re-abstracted over
`[α : Type u]`, are the auxiliary member's own stored type and its restored constructor types;
and the auxiliary member's constructor list, restored, is `List`'s, in order. -/
theorem ntreeRestore_faithful :
    ntreeRestore.Faithful ntreeAux env₁ ntreeK (fun _ => 1) where
  ty_agree := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact ⟨_, list_const h, rfl, rfl⟩
    · simp [ntreeAux] at hT
  ctor_agree := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      obtain rfl | rfl := hC
      · exact ⟨_, listNil_const h, rfl, rfl⟩
      · exact ⟨_, listCons_const h, rfl, rfl⟩
    · simp [ntreeAux] at hT
  ctors_complete := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact ⟨listDecl, 0, listType, ⟨_, _, h, .rfl⟩, rfl, rfl, rfl, rfl⟩
    · simp [ntreeAux] at hT

/-! ### The step is admitted -/

theorem ntree_fresh (n : Lean.Name)
    (hn : n ∈ [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1]) :
    env₁.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

/-- **3c. `CompanionSound` is false too**: its `type_agree` clause asks the environment to
hold the companion member's name, and the auxiliary name is not in the environment — that is
the whole reason restoration exists. -/
theorem ntreeAux_not_CompanionSound : ¬ ntreeAux.CompanionSound env₁ ntreeK := by
  rintro ⟨hty, -⟩
  have := hty _ (List.Mem.tail _ (List.Mem.head _)) (by decide)
  rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at this
  exact absurd this nofun

/-! ### …and it is well-formed

The auxiliary block is an ordinary mutual inductive, so this is `mutDecl_WF`
(`Theory/Inductive/DeclExamples.lean`) with a parameter: two types, three constructors, three
recursive fields between them — including `_nested.List_1.cons`'s **first** field, which is
recursive only because the instantiation at `NTree α` turned `List`'s parameter position into
one.  That is the configuration nested induction exists for, and until this witness it had
none. -/

omit h in
theorem ntreeAux_params_WF {env : VEnv} :
    OnCtx ntreeAux.params.reverse (env.IsType ntreeAux.uvars) :=
  ⟨trivial, _, .sort (by decide)⟩

theorem ntree_const_staged {env₂ : VEnv} (hs : env₁.addIndTypes ntreeAux = some env₂) :
    env₂.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ :=
  VEnv.addConstList_constants hs
    (``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (by exact List.Mem.head _)

theorem nlist_const_staged {env₂ : VEnv} (hs : env₁.addIndTypes ntreeAux = some env₂) :
    env₂.constants `_nested.List_1
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ :=
  VEnv.addConstList_constants hs
    (`_nested.List_1, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

omit h in
theorem ntreeAux_binders_indep {pre : List VIndField} {i : Nat}
    {r : VIndRecArg} (hr : r.binders = []) : r.BindersIndep pre i := by
  intro i' t F' hF' hs he k B hB
  rw [hr] at hB
  simp at hB

/-- **`VInductDecl'.WF` for the auxiliary block.** -/
theorem ntreeAux_WF : ntreeAux.WF env₁ where
  types_ne := by simp [ntreeAux]
  params := ntreeAux_params_WF
  types := by
    intro T hT
    simp only [ntreeAux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := ntreeAux_params_WF, isType := ⟨_, by type_tac⟩,
              canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₂ hs j T hT C hC
    have ht := ntree_const_staged h hs
    have hf := nlist_const_staged h hs
    match j, hT with
    | 0, hT =>
      simp only [ntreeAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [ntreeNode, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, ntreeAux, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.bvar 0, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, by type_tac⟩ }
      | 1, hF =>
        simp only [ntreeNode, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, ntreeAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; exact ntreeAux_binders_indep rfl
                pos := ⟨by decide, rfl, nofun, nofun, ⟨ntreeAux_params_WF, _, by type_tac⟩,
                        by type_tac, fun T' hT' => by cases hT'; exact .nil, ⟨_, by type_tac⟩, by decide⟩ }
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT =>
      simp only [ntreeAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      obtain rfl | rfl := hC
      · exact { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := nofun,
                args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      · refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
                 args_len := rfl, args_fresh := nofun, args_ty := .nil,
                 result := by type_tac }
        intro i F hF
        match i, hF with
        | 0, hF =>
          simp only [nlistCons, List.getElem?_cons_zero, Option.some.injEq] at hF
          subst hF
          exact { hasType := by type_tac
                  level := fun ls => by simp [VLevel.eval, ntreeAux, Lean.Nat.imax]
                  binders_indep := fun r hr => by
                    cases hr; exact ntreeAux_binders_indep rfl
                  pos := ⟨by decide, rfl, nofun, nofun, ntreeAux_params_WF, by type_tac,
                          fun T' hT' => by cases hT'; exact .nil, ⟨_, by type_tac⟩, by decide⟩ }
        | 1, hF =>
          simp only [nlistCons, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hF
          subst hF
          exact { hasType := by type_tac
                  level := fun ls => by simp [VLevel.eval, ntreeAux, Lean.Nat.imax]
                  binders_indep := fun r hr => by
                    cases hr; exact ntreeAux_binders_indep rfl
                  pos := ⟨by decide, rfl, nofun, nofun, ⟨ntreeAux_params_WF, _, by type_tac⟩,
                          by type_tac, fun T' hT' => by cases hT'; exact .nil, ⟨_, by type_tac⟩, by decide⟩ }
        | (_ + 2), hF => simp [nlistCons] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, ntreeAux])

/-- **The nested block is admitted, end to end.**  The environment holding `List` is extended
by the auxiliary block presented through `restoreNested`, declaring exactly `NTree`,
`NTree.node`, `NTree.rec` and `NTree.rec_1`. -/
theorem ntreeAux_admitted :
    ∃ env₂, env₁.addInductR ntreeAux ntreeK ntreeRestore = some env₂ := by
  refine VEnv.addInductR_eq_some_iff.2 ⟨?_, ?_⟩ <;> rw [ntreeAux_allNamesCR]
  · intro n hn; exact ntree_fresh h n hn
  · decide

/-- **The whole step, on a real nested declaration.**  `VInductDecl'.WF` at the auxiliary
block, the restoration's obligations against `List` as the history declares it,
and the extension — the last of which declares `NTree.rec_1` at the type `restoreNested`
computes and keys its ι-rules on that same constant.

This is the end-to-end statement `docs/handoff-nested-head.md` asks for.  What it does *not*
claim is consistency of the result; that is `leanTTConsistent`, open. -/
theorem ntreeAux_AddNested :
    ∃ env₂, VEnv.AddNested env₁ ntreeAux ntreeK ntreeRestore
      (fun _ => 1) env₂ :=
  ⟨(ntreeAux_admitted h).choose, ntreeAux_WF h, ntreeRestore_ownId,
    ntreeRestore_faithful h, (ntreeAux_admitted h).choose_spec⟩

omit h in
/-- …and the declared recursors carry the restored types — `NTree.rec_1 : … List (NTree α) …`,
the constant the companion's ι-rules are keyed on. -/
theorem ntreeAux_recs_declared {env₂ : VEnv}
    (h2 : env₁.addInductR ntreeAux ntreeK ntreeRestore = some env₂) :
    env₂.constants ``NTree.rec = some ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩ ∧
      env₂.constants ``NTree.rec_1 = some ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩ :=
  ⟨VEnv.addInductR_constants h2 (``NTree.rec, ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩)
      (by rw [show ntreeAux.allConstsCR ntreeRestore ntreeK
            = [(``NTree, ⟨1, (ntreeAux.types.getD 0 default).type⟩),
               (``NTree.node, ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩),
               (``NTree.rec, ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩),
               (``NTree.rec_1, ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩)] from rfl]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
   VEnv.addInductR_constants h2 (``NTree.rec_1, ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩)
      (by rw [show ntreeAux.allConstsCR ntreeRestore ntreeK
            = [(``NTree, ⟨1, (ntreeAux.types.getD 0 default).type⟩),
               (``NTree.node, ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩),
               (``NTree.rec, ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩),
               (``NTree.rec_1, ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩)] from rfl]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

end

/-! ### Corrections: what the companion model got wrong about a nested block

Everything here is machine-checked at `ntreeAux`, and each item contradicts a claim relayed in
`docs/handoff-nested-head.md` or `docs/handoff-nested-companion.md`. -/

/-- **1. `resolveC` is unavailable.**  The companion member is `_nested.List_1`, a name the
history never declares, so the lookup fails and resolution returns `none`.  `VEnv.AddCompanion`
is therefore not a relation any genuine nested block stands in. -/
theorem ntreeAux_resolveC_none :
    ntreeAux.resolveC [VDecl.induct listDecl] ntreeK = none := rfl

/-- The same block with its companion member *named* `List` — the identification
`Theory/Inductive/Companion.lean` makes, which is what makes `resolveC` fire. -/
def ntreeAuxL : VInductDecl' :=
  { ntreeAux with types :=
      [ ntreeAux.types.getD 0 default,
        { name := ``List,
          type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
          indices := [], ctors := [nlistNil, nlistCons] } ] }

/-- **2. …and when it does fire it destroys the nested structure.**  Resolution replaces the
member by `List`'s own record, whose `cons` has a *non-recursive* first field: `List`'s
parameter position is a recursive position only after the instantiation at `NTree α`.  So the
resolved block has one recursive field where the auxiliary block has two — the recursor loses
the induction hypothesis for `NTree`, which is the entire content of nested induction.

`resolveC` models `restoreNested` in the wrong direction: `restoreNested` carries the
*auxiliary* member's constructors forward with the instantiation substituted; resolution
carries the *declaring* block's constructors backward with nothing substituted. -/
theorem ntreeAuxL_resolveC_loses_recursion :
    ntreeAuxL.resolveC [VDecl.induct listDecl] [``List]
        = some { ntreeAuxL with types := [ntreeAux.types.getD 0 default, listType] } ∧
      listCons.recFields.length = 1 ∧ nlistCons.recFields.length = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- **3a. `CompanionShape` says nothing about a nested block.**  It quantifies over the
history's blocks that declare a type named in `K`, and `K` holds the *auxiliary* name, which no
`.induct` step declares.  So the residue `docs/handoff-nested-head.md` §6 promises the head
generalisation will remove is not a constraint that has to be weakened — it is already empty,
and the constraint it was standing in for (`VIndRestore.Faithful`) is a different statement
about a different pair of blocks. -/
theorem ntreeAux_CompanionShape_vacuous :
    ntreeAux.CompanionShape [VDecl.induct listDecl] ntreeK := by
  rintro D₀ j₀ T₀ hD hT hK
  simp only [List.mem_singleton, VDecl.induct.injEq] at hD
  subst hD
  match j₀, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | (_ + 1), hT => simp [listDecl] at hT

/-- **3b. `CompanionComplete` is outright false for a nested block** — not weak, false.  It
asks the history to declare a type of the companion member's name, and `_nested.List_1` is a
name the history has never seen and never will. -/
theorem ntreeAux_not_CompanionComplete :
    ¬ ntreeAux.CompanionComplete [VDecl.induct listDecl] ntreeK := by
  rintro ⟨hc⟩
  obtain ⟨D₀, j₀, T₀, hD, hT, hn, -⟩ := hc 1 _ rfl (by decide)
  simp only [List.mem_singleton, VDecl.induct.injEq] at hD
  subst hD
  match j₀, hT with
  | 0, hT => cases hT; exact absurd hn (by decide)
  | (_ + 1), hT => simp [listDecl] at hT

/-- **4. `addInduct'` does not refuse the auxiliary block.**  `Companion.lean` locates "the
refusal" at one `addConst` on an already-taken name.  The auxiliary member's name is *fresh*,
so no refusal occurs: the abstract step succeeds and declares seven constants where
`Environment.addInductive` declares four.  The two extra type/constructor constants and the
un-renamed auxiliary recursor are exactly what restoration removes. -/
theorem ntreeAux_allNames :
    ntreeAux.allNames =
      [``NTree, `_nested.List_1, ``NTree.node, `_nested.List_1.nil, `_nested.List_1.cons,
       ``NTree.rec, `_nested.List_1.rec] := rfl

/-- **5. G1's re-staging is wrong for a nested block.**  `VInductDecl'.WFC` stages the
constructor clause over `addIndTypesC`, which drops the companion's type constant — but
`NTree.node`'s stored field type *is* `_nested.List_1 α`, so at that staging the clause is not
merely weaker, it is unsatisfiable.  The auxiliary block is checked with **all** its type
constants present (`AddInductive.run` builds the full intermediate environment and only the
emission drops them), which is what `VInductDecl'.WF` already says.

So the ordering rule "G1 must never land without G2" should be read as being about the
`J`-as-companion model only; under the auxiliary model G1 is not an improvement to make. -/
theorem ntreeAux_staging :
    ntreeAux.typeConsts.map (·.1) = [``NTree, `_nested.List_1] ∧
      (ntreeAux.typeConstsC ntreeK).map (·.1) = [``NTree] ∧
      (ntreeNode.fields.getD 1 default).type = .app (.const `_nested.List_1 [.param 0]) (.bvar 1) :=
  ⟨rfl, rfl, rfl⟩

/-! ### Regression: the `CompanionResolve.lean` witnesses are untouched

Nothing in this file edits `Theory/Inductive/Companion.lean` or
`Theory/Inductive/CompanionResolve.lean`; these re-elaborate their statements so that a change
breaking them breaks this file too. -/

example := @fooComp_killed
example := @fooComp_admitted_repaired
example := @fooComp_WFC
example := @fooDecl_WFC
example := @fooComp_resolveC
example := @fooCompRec_ne_mkRecName
example := @VInductDecl'.resolveC_zero_ctors
example := @VInductDecl'.resolveC_complete
example := @VEnv.AddCompanion_nil

end InductiveDeclExamples

end Lean4Lean
