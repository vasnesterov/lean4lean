import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Typing.ConstSubst

/-!
# The restoration data, and the nested declaration step — the *definitions*

This file exists for one reason: **`VDecl.WF` has to be able to name the nested step.**

`Theory/Typing/Env.lean` defines `VDecl.WF`/`VEnv.WF'`, and it sits *above* the whole
`Theory/Inductive/{Companion,CompanionResolve,NestedHead,NestedBuild}.lean` chain in the
import graph (`Theory.VDecl` imports `Theory.Inductive.Decl`, and `Nested.lean` imports
`Theory.Typing.DeltaUnique`, which imports `Env.lean`).  So the *step* — `VEnv.addInductR`
and the obligations that make it sound — could not be mentioned there at all, and the
`induct` rule's `env.addInduct' decl = some env'` had nothing to be generalised to: a nested
declaration produces `env.addInductR D K R = some env'`, which is **not** `addInduct'` of any
`VInductDecl'` (`tBlock_not_addInductStages`, `Verify/Environment/InductR.lean`).

The content is unchanged.  Every declaration below was **moved verbatim** from
`Theory/Inductive/NestedHead.lean` (Parts 1, 2, 4 and 6), from
`Theory/Inductive/CompanionResolve.lean` Part 9 (`tyAppH` and its two conservativity
`rfl`-lemmas) and from `Theory/Inductive/Companion.lean` (`typeConstsC`).  Only definitions
moved; every *theorem* about them stays in its original file, which now sees them through
this one.

The second thing that made the step unstateable at `Env.lean` was the declaration history
`ds : List VDecl`, which `VIndRestore.Faithful` used to carry and which `VDecl.WF env d env'`
does not have.  That is gone: `Faithful.ctors_complete` asks for `VInductDecl'.Declared`
(`Theory/Inductive/Decl.lean`) — the same fact stated over the environment alone — which a
history discharges through `VEnv.WF'.declared` (`Theory/Inductive/Nested.lean`).
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele shift shiftTele)

/-! ## Part 0: two pieces from further downstream

`tyAppH` is `CompanionResolve.lean` Part 9's generalised inductive-type head; `typeConstsC` is
`Companion.lean`'s "declare only the non-companion members".  Both are definitional
prerequisites of `VEnv.addInductR`. -/

namespace VInductDecl'

def tyAppH (n : Name) (ls : List VLevel) (A : List VExpr) (k : Nat) (args : List VExpr) :
    VExpr :=
  (VExpr.const n ls).mkApp (A.map (·.liftN k) ++ args)

/-- **Conservativity of the head generalisation.**  At the stored instantiation
`A = bvars 0 D.np` — "the parameters, in order", which is what every *non*-companion member
has — `tyAppH` is `VInductDecl'.tyApp` on the nose.

So the generalisation is one, and the existing offset lemmas about `tyApp` are its instances
rather than its neighbours. -/
theorem tyAppH_bvars (D : VInductDecl') (j k : Nat) (args : List VExpr) :
    tyAppH (D.types.getD j default).name D.ownLvls (VExpr.bvars 0 D.np) k args
      = D.tyApp j k args := by
  rw [tyAppH, VInductDecl'.tyApp, VExpr.map_liftN_bvars_lo (Nat.le_refl 0), Nat.add_zero]

/-- …and the same at the recursor's universe numbering. -/
theorem tyAppH_bvars' (D : VInductDecl') (j k : Nat) (args : List VExpr) :
    tyAppH (D.types.getD j default).name D.selfLvls (VExpr.bvars 0 D.np) k args
      = D.tyApp' j k args := by
  rw [tyAppH, VInductDecl'.tyApp', VExpr.map_liftN_bvars_lo (Nat.le_refl 0), Nat.add_zero]

/-- The type constants actually declared: the non-companion members only.  (Moved from
`Theory/Inductive/Companion.lean`, where the theorems about it stay.) -/
def typeConstsC (D : VInductDecl') (K : List Name) : List (Name × VConstant) :=
  D.typeConsts.filterMap fun c => if c.1 ∈ K then none else some c

end VInductDecl'

/-- Entrywise congruence for `List.filterMap`.  (Local: the corresponding `Mathlib` lemma is
not in this file's import chain.) -/
theorem filterMap_congr_left {α β : Type _} {f g : α → Option β} : ∀ {l : List α},
    (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr_left fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-! ## Part 1: the restoration data -/

/-- **`restoreNested`, as data.**  What the nested-elimination pass rewrites when it emits a
declaration it has already checked:

* `tyName j`/`tyLvls j`/`tyArgs j` — the member `j` of the auxiliary block is presented as
  `tyName j |>.{tyLvls j} (tyArgs j)`, where `tyArgs j` is a telescope over the *block's*
  parameters.  For a member the user wrote this is `I_j.{ownLvls} params`, i.e. the identity;
  for an auxiliary member it is `List.{u} (Tree α)`.
* `ctorName` — `ElimNestedInductive.Result.restoreCtorName`.
* `recName` — `mkAuxRecNameMap`.

Nothing here is checked: it is a *presentation*, and the obligations it incurs are the
subject of Part 4. -/
structure VIndRestore where
  tyName : Nat → Lean.Name
  tyLvls : Nat → List VLevel
  tyArgs : Nat → List VExpr
  ctorName : Lean.Name → Lean.Name
  recName : Lean.Name → Lean.Name

/-- The identity restoration: every member is presented as itself, at the block's own levels,
applied to the block's own parameter run.  This is what a block with no nested occurrence
gets, and it is the point at which every construction below collapses to its `Decl.lean`
original. -/
def VInductDecl'.idRestore (D : VInductDecl') : VIndRestore where
  tyName j := (D.types.getD j default).name
  tyLvls _ := D.ownLvls
  tyArgs _ := bvars 0 D.np
  ctorName := id
  recName := id

/-! ### The restoration as a constant substitution

Moved down from `Theory/Typing/ConstSubstNested.lean` (where the theorems about it stay),
because `VIndCtor.typeR` now *uses* it: the positions restoration used to copy verbatim —
a constructor's own parameter binders, a **non**-recursive field's stored type, the result's
index arguments — are the positions the old definition left a companion constant sitting in
(`nfnAuxDirty_refutation`, `Theory/Inductive/RestoreBridge.lean`), and the substitution is
what removes it.  See `VIndCtor.typeR` for why *this* rewrite and not the contracting one. -/

namespace VIndRestore

/-- The term the restoration presents member `j`'s type constant as, abstracted over the
block's parameters.  `mkLams` is the only place a β-redex can enter: at `D.np = 0` it is
absent and the presentation is a closed application. -/
def tyVal (R : VIndRestore) (D : VInductDecl') (j : Nat) : VExpr :=
  mkLams D.params ((VExpr.const (R.tyName j) (R.tyLvls j)).mkApp (R.tyArgs j))

/-- …and constructor `C` of member `j`, at the *same* spine — which is what
`VInductDecl'.ctorAppR` uses. -/
def ctorVal (R : VIndRestore) (D : VInductDecl') (j : Nat) (C : VIndCtor) : VExpr :=
  mkLams D.params ((VExpr.const (R.ctorName C.name) (R.tyLvls j)).mkApp (R.tyArgs j))

/-- …and the recursor, which `mkAuxRecNameMap` only renames.  A rename is a constant
substitution because `substC` replaces a constant by a *term*. -/
def recVal (R : VIndRestore) (D : VInductDecl') (n : Lean.Name) : VExpr :=
  .const (R.recName n) (VLevel.params D.recUvars)

/-- The type entries alone — the domain obligation **(A)** uses. -/
def csubstTyList (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) :
    List (Lean.Name × VExpr) :=
  (D.types.zipIdx.filter fun p => decide (p.1.name ∈ K)).map fun (T, j) => (T.name, R.tyVal D j)

/-- **The restoration, as a constant substitution.**  One entry for each companion member's
type constant, one for its recursor, one for each of its constructors. -/
def csubstList (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) :
    List (Lean.Name × VExpr) :=
  (D.types.zipIdx.filter fun p => decide (p.1.name ∈ K)).flatMap fun (T, j) =>
    (T.name, R.tyVal D j) ::
    (Lean.mkRecName T.name, R.recVal D (Lean.mkRecName T.name)) ::
    T.ctors.map fun C => (C.name, R.ctorVal D j C)

def csubstTy (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) : CSubst :=
  fun n => (R.csubstTyList D K).lookup n

def csubst (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) : CSubst :=
  fun n => (R.csubstList D K).lookup n

/-- **At an empty domain the substitution is the identity.**  This is what makes every
`idRestore` collapse lemma (`VIndField.typeR_id` and friends, `Theory/Inductive/NestedHead.lean`)
survive the redefinition: `idRestore.aux = []`, so the rewrite the new `typeR` applies is
`VExpr.substC CSubst.id`. -/
theorem csubstTy_nil (R : VIndRestore) (D : VInductDecl') : R.csubstTy D [] = CSubst.id := by
  funext n
  rw [csubstTy, csubstTyList,
    show (D.types.zipIdx.filter fun p => decide (p.1.name ∈ ([] : List Lean.Name))) = [] from
      List.filter_eq_nil_iff.2 (by simp)]
  rfl

/-- …and the same for the full substitution, which is what `recConstsR` uses. -/
theorem csubst_nil (R : VIndRestore) (D : VInductDecl') : R.csubst D [] = CSubst.id := by
  funext n
  rw [csubst, csubstList,
    show (D.types.zipIdx.filter fun p => decide (p.1.name ∈ ([] : List Lean.Name))) = [] from
      List.filter_eq_nil_iff.2 (by simp)]
  rfl

end VIndRestore

namespace VInductDecl'
variable (D : VInductDecl') (R : VIndRestore)

/-- `tyApp` with the head restored: `J.{ls} A(params) args`, `A` sitting `k` binders deep. -/
def tyAppR (_D : VInductDecl') (R : VIndRestore) (j k : Nat) (args : List VExpr) : VExpr :=
  tyAppH (R.tyName j) (R.tyLvls j) (R.tyArgs j) k args

/-- `tyApp'` with the head restored — the same at the recursor's level numbering, where the
stored instantiation is moved by `atRec` as well. -/
def tyAppR' (j k : Nat) (args : List VExpr) : VExpr :=
  tyAppH (R.tyName j) ((R.tyLvls j).map (·.inst D.selfLvls)) (D.atRecTele (R.tyArgs j)) k args

/-- `ctorApp'` with the head restored: `List.cons.{u} (Tree α) args`. -/
def ctorAppR (j : Nat) (C : VIndCtor) (k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (R.ctorName C.name) ((R.tyLvls j).map (·.inst D.selfLvls))).mkApp
    ((D.atRecTele (R.tyArgs j)).map (·.liftN k) ++ args)
end VInductDecl'

/-! ## Part 2: the recursor construction, restored

Every definition here is its `Theory/Inductive/Decl.lean` original with `tyApp`, `tyApp'`,
`ctorApp'` replaced by `tyAppR`, `tyAppR'`, `ctorAppR`, the two recursor heads renamed by
`R.recName`, and the stored field telescope replaced by its restored form.  `ihType`/`ihTypes`
are *not* on the list and are used verbatim: they mention no block head, only `r.binders`,
`r.args` and de Bruijn variables, and `VIndField.WF.pos` forces `r.binders` and `r.args` to be
block-free, so `restoreNested` does not touch them. -/

/-- `VIndRecArg.canonResult`, restored. -/
def VIndRecArg.canonResultR (r : VIndRecArg) (D : VInductDecl') (R : VIndRestore) (i : Nat) :
    VExpr := D.tyAppR R r.idx (r.binders.length + i) r.args

/-- `VIndRecArg.canonType`, restored. -/
def VIndRecArg.canonTypeR (r : VIndRecArg) (D : VInductDecl') (R : VIndRestore) (i : Nat) :
    VExpr := mkPi r.binders (r.canonResultR D R i)

/-- The stored type of field `i`, restored.  A recursive field is `∀ ξ, I_idx params π` and
its head is the thing restoration rewrites; a non-recursive one is only *definitionally*
block-free (`VIndField.WF.pos`'s `none` branch, deliberately — `Decl.lean`'s
`(fun _ : T => Nat) r`), so a companion constant can sit under a redex in it and the
restoration has to visit it too.

**This branch used to be `F.type`, verbatim, and that was a defect**:
`nfnAuxDirty_refutation` (`Theory/Inductive/RestoreBridge.lean`) is a block satisfying every
conjunct of `VEnv.AddNestedB` whose step declared `NFn.node` at a type mentioning
`_nested.PFn_1`, a constant the environment does not hold — so `VEnv.Ordered` failed and
obligation (A) of `VEnv.addInductR_ordered'` was **false**.  `ElimNestedInductive.restoreNested`
(`Lean4Lean/Inductive/Add.lean`) is a whole-expression `replaceNoCache`, so the implementation
restores the occurrence wherever it sits; this branch now does too. -/
def VIndField.typeR (F : VIndField) (D : VInductDecl') (R : VIndRestore) (i : Nat) : VExpr :=
  match F.recArg with
  | none => F.type
  | some r => r.canonTypeR D R i

/-- The constructor's stored field telescope, restored. -/
def VIndCtor.fieldTypesR (C : VIndCtor) (D : VInductDecl') (R : VIndRestore) : List VExpr :=
  C.fields.zipIdx.map fun (F, i) => F.typeR D R i

/-- **The side condition the restored field telescope carries.**  `VIndField.WF.pos` requires
a recursive field's stored type to be only *definitionally* `∀ ξ, I_idx params π`
(`Decl.lean`'s `(fun _ : T => Nat) r` example), so `typeR` — which rewrites the canonical form
— is the stored form only on a block whose recursive fields are stored canonically.

Every witness in `Theory/Inductive/DeclExamples.lean` is canonical, and so is every
constructor `ElimNestedInductive` generates: `replaceIfNested` builds an auxiliary
constructor's field types by instantiating the nested type's own stored type, whose recursive
positions are applications of a block constant on the nose. -/
def VIndCtor.Canonical (C : VIndCtor) (D : VInductDecl') : Prop :=
  ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F → F.recArg = some r →
    F.type = r.canonType D i

/-- The block-level form: every constructor of the block is canonical. -/
def VInductDecl'.Canonical (D : VInductDecl') : Prop :=
  ∀ j C, (j, C) ∈ D.ctorsAll → C.Canonical D

/-- A constructor's stored type, restored.  `Environment.addInductive` re-stores the
constructors of the *user's* types through `restoreNested`; a companion's constructors are
never declared at all.

**Three positions, three treatments, and the reason for each.**

* The **result head** is `tyAppR`: the *contracted* restored application.  This is what
  `restoreNested` produces — it strips the leading `nparams` binders into `As`, and at an
  occurrence emits `mkAppRange ((nested.abstract r.params).instantiateRev As) nparams …`,
  i.e. the nested instance with the *enclosing* parameters substituted and the occurrence's
  own `nparams` arguments **discarded**.  So it is *not* `VExpr.substC`, which would leave a
  saturated `D.np`-fold β-redex (`ntreeNode_substC_ne_typeR`) and re-instantiate at the
  occurrence's own arguments.  The difference is invisible at `D.np = 0` and load-bearing
  above it: `TrConstant` (`Verify/Environment/Basic.lean`) relates a declared constant to the
  implementation's through `TrExprS`, which has **no defeq slack**, so a spec that declared
  the redex would make `addDecl.WF` *false* for every parameterised nested block.
* `C.params` and `C.args` are rewritten by `VExpr.substC` — the *closed-value* substitution.
  Both are positions `restoreNested` leaves alone (the parameter binders are stripped and
  re-abstracted unchanged; `C.args` is `NoBlock` by `VIndCtor.WF.args_fresh`, so on anything
  the implementation can produce the rewrite is the identity and faithfulness is untouched).
  `substC` rather than the contracting rewrite because inside `C.params[p]` only `p`
  parameters are in scope, so a contracted `tyAppR` there would name de Bruijn indices that
  do not exist — the contracting rewrite is *unavailable* in a parameter binder, which is
  exactly why the implementation strips them.
* the field telescope is `fieldTypesR`, which restores each field per its `recArg`.

`C.args` is substituted rather than copied only to make the bridge
`(C.type D j).substC σ = C.typeR D R j` need no `NoCSubst` hypothesis on it; under
`args_fresh` the two are equal (`VIndRestore.noBlock_noCSubst`). -/
def VIndCtor.typeR (C : VIndCtor) (D : VInductDecl') (R : VIndRestore) (j : Nat) : VExpr :=
  mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)

namespace VInductDecl'
variable (D : VInductDecl') (R : VIndRestore)

def motiveTypeR (t : Nat) : VExpr :=
  let T := D.types.getD t default
  let ni := T.indices.length
  mkPi (liftTele t (D.atRecTele T.indices)) <|
    .forallE (D.tyAppR' R t (ni + t) (bvars 0 ni)) (.sort D.elimLvl)

def motivesR : List VExpr := (List.range D.nm).map (D.motiveTypeR R)

def minorTypeR (q t : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + q
  let nf := C.fields.length
  let V := D.ihTypes q C
  let nr := V.length
  mkPi (liftTele off (D.atRecTele (C.fieldTypesR D R)) ++ V) <|
    (VExpr.bvar (nr + nf + q + (D.nm - 1 - t))).mkApp <|
      C.args.map (fun a => shift off nr nf (D.atRec a)) ++
      [D.ctorAppR R t C (nr + nf + off) (bvars nr nf)]

def minorsR : List VExpr := D.ctorsAll.zipIdx.map fun ((t, C), q) => D.minorTypeR R q t C

def recTypeR (j : Nat) : VExpr :=
  let T := D.types.getD j default
  let ni := T.indices.length
  mkPi (D.atRecTele D.params ++ D.motivesR R ++ D.minorsR R ++
        liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) <|
    .forallE (D.tyAppR' R j (ni + D.nmin + D.nm) (bvars 0 ni)) <|
      (VExpr.bvar (1 + ni + D.nmin + (D.nm - 1 - j))).mkApp (bvars 1 ni ++ [.bvar 0])

def iotaCtxR (C : VIndCtor) : List VExpr :=
  D.atRecTele D.params ++ D.motivesR R ++ D.minorsR R ++
    liftTele (D.nm + D.nmin) (D.atRecTele (C.fieldTypesR D R))

/-- **G4's repair, half one.**  The recursor the induction hypotheses call is the *renamed*
one — the constant this block actually declares. -/
def ihValuesR (C : VIndCtor) : List VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  C.recFields.map fun (i, r) =>
    let d := nf - i
    let nxi := r.binders.length
    mkLams (shiftTele off d i (D.atRecTele r.binders)) <|
      (VExpr.const (R.recName (Lean.mkRecName (D.types.getD r.idx default).name))
          (VLevel.params D.recUvars)).mkApp <|
        bvars (nxi + nf + off) D.np ++ bvars (nxi + nf + D.nmin) D.nm ++
        bvars (nxi + nf) D.nmin ++
        r.args.map (fun a => shift off d i (D.atRec a) nxi) ++
        [(VExpr.bvar (nxi + (nf - 1 - i))).mkApp (bvars 0 nxi)]

def iotaLamR (q : Nat) (C : VIndCtor) : VExpr :=
  let nf := C.fields.length
  mkLams (D.iotaCtxR R C) <|
    (VExpr.bvar (nf + (D.nmin - 1 - q))).mkApp (bvars 0 nf ++ D.ihValuesR R C)

/-- **G4's repair, half two.**  The ι-rule's left-hand side is headed by the constant the
step declares, `R.recName (mkRecName I_j)`, and its major premise by the *restored*
constructor name. -/
def iotaLhsR (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  (VExpr.const (R.recName (Lean.mkRecName (D.types.getD j default).name))
      (VLevel.params D.recUvars)).mkApp <|
    bvars (nf + off) D.np ++ bvars (nf + D.nmin) D.nm ++ bvars nf D.nmin ++
    C.args.map (fun a => (D.atRec a).liftN off nf) ++
    [D.ctorAppR R j C (nf + off) (bvars 0 nf)]

def iotaTypeR (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  (VExpr.bvar (nf + D.nmin + (D.nm - 1 - j))).mkApp <|
    C.args.map (fun a => (D.atRec a).liftN off nf) ++
    [D.ctorAppR R j C (nf + off) (bvars 0 nf)]

def iotaRuleR (j q : Nat) (C : VIndCtor) : VDefEq :=
  let G := D.iotaCtxR R C
  { uvars := D.recUvars
    lhs := mkLams G (D.iotaLhsR R j C)
    rhs := mkLams G ((D.iotaLamR R q C).mkApp (bvars 0 G.length))
    type := mkPi G (D.iotaTypeR R j C) }

def iotaRulesR : List VDefEq :=
  D.ctorsAll.zipIdx.map fun ((j, C), q) => D.iotaRuleR R j q C

/-- The recursor constants, renamed and with restored types.  This *is*
`VInductDecl'.recConstsC` with the type restored as well as the name renamed — and, since
2026-08-31, with the restoration also **substituted through the positions `recTypeR` copies
verbatim**: see `ctorConstsCR` for why. -/
def recConstsR (K : List Lean.Name) : List (Lean.Name × VConstant) :=
  D.types.zipIdx.map fun (T, j) =>
    (R.recName (Lean.mkRecName T.name),
      ⟨D.recUvars, (D.recTypeR R j).substC (R.csubst D K)⟩)

/-- **The constructor constants actually declared, with restored names and types.**

The type is `C.typeR D R j` **with the restoration substituted through it**, and the
`substC` is the repair of a defect: `VIndCtor.typeR` restores the *result* head and the
*recursive* fields' heads, and copies `C.params`, every **non**-recursive field's stored type
and `C.args` verbatim — while `VIndCtor.WF.params_eq` and `VIndField.WF.pos`'s `none` branch
make those only *definitionally* block-free.  So a companion constant could sit under a redex
in one of them, `typeR` left it there, and the step declared a constant whose type names a
constant the environment does not hold: `VEnv.Ordered` failed and obligation (A) of
`VEnv.addInductR_ordered'` was **false** (`nfnAuxDirty_refutation`,
`Theory/Inductive/RestoreBridge.lean`).

`ElimNestedInductive.restoreNested` (`Lean4Lean/Inductive/Add.lean`) is a whole-expression
`replaceNoCache`, so the implementation restores the occurrence *wherever it sits*; this is
the abstract counterpart.  Two things about the placement are deliberate:

* the `substC` is **outside** `typeR`, not inside it.  `typeR` is also what
  `VIndRestore.Faithful.ctor_agree` and the recursor's minor premises are stated against, and
  those are equations about the *canonical* restored form; putting the rewrite here says
  exactly "this is what the step **declares**", which is what obligation (A) is about.
* it is `VExpr.substC` — the closed-value substitution — and **not** the contracting rewrite
  `tyAppR` is.  On a clean block (everything `ElimNestedInductive` can produce, since
  `checkNoNestedAux` rejects any input constructor type mentioning a `_nested` constant and
  `replaceIfNested` inserts the auxiliary constant only in saturated recursive-field
  positions) `substC` is the **identity**, so nothing the implementation declares moves and
  faithfulness is untouched.  A contracting rewrite is not even available in a parameter
  binder: inside `C.params[p]` only `p` parameters are in scope, so the `bvars k D.np` a
  contracted head names would be out of scope. -/
def ctorConstsCR (K : List Lean.Name) : List (Lean.Name × VConstant) :=
  D.ctorsAll.filterMap fun (j, C) =>
    if (D.types.getD j default).name ∈ K then none
    else some (R.ctorName C.name, ⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩)

def allConstsCR (K : List Lean.Name) : List (Lean.Name × VConstant) :=
  D.typeConstsC K ++ D.ctorConstsCR R K ++ D.recConstsR R K

def allNamesCR (K : List Lean.Name) : List Lean.Name := (D.allConstsCR R K).map (·.1)

end VInductDecl'

/-- The block's ι-rules, restored and renamed.

**Not** substituted, unlike `ctorConstsCR` and `recConstsR` — see the note at
`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) for why obligation **(C)**
still carries the defect those two just lost, and what closing it costs. -/
def VEnv.addIndRulesR (env : VEnv) (D : VInductDecl') (R : VIndRestore) : VEnv :=
  (D.iotaRulesR R).foldl VEnv.addDefEq env

/-- **The repaired companion-aware extension.**  `VEnv.addInductC` with the restoration
threaded all the way through: the constants it declares and the rules it emits are built from
the *same* `R`, which is what G4 was the absence of. -/
def VEnv.addInductR (env : VEnv) (D : VInductDecl') (K : List Lean.Name) (R : VIndRestore) :
    Option VEnv :=
  (env.addConstList (D.allConstsCR R K)).map (·.addIndRulesR D R)

/-- `J`'s stored type/constructor type, instantiated at the restoration's stored spine and
re-abstracted over the block's parameters. -/
def VIndRestore.instAt (R : VIndRestore) (D : VInductDecl') (npJ j : Nat) (e : VExpr) : VExpr :=
  mkPi D.params (VExpr.instAll (VExpr.splitPis npJ (e.instL (R.tyLvls j))).2 (R.tyArgs j))

/-- **The restoration's obligations.**  `npJ j` is the parameter count of the type member `j`
is presented as; it comes from the environment's `InductiveVal`, which the abstract theory
does not carry, so it is a parameter here. -/
structure VIndRestore.Faithful (R : VIndRestore) (D : VInductDecl')
    (env : VEnv) (K : List Lean.Name) (npJ : Nat → Nat) : Prop where
  /-- The presented head is a declared constant whose stored type, instantiated, is the
  auxiliary member's own stored type. -/
  ty_agree : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∃ ci : VConstant, env.constants (R.tyName j) = some ci ∧
      ci.uvars = (R.tyLvls j).length ∧ R.instAt D (npJ j) j ci.type = T.type
  /-- Each presented constructor is a declared constant whose stored type, instantiated, is
  the auxiliary member's own restored constructor type. -/
  ctor_agree : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ T.ctors, ∃ ci : VConstant,
      env.constants (R.ctorName C.name) = some ci ∧ ci.uvars = (R.tyLvls j).length ∧
      R.instAt D (npJ j) j ci.type = C.typeR D R j
  /-- **G2, for the nested model.**  The auxiliary member's constructors, restored, are
  exactly the constructors of the block of the history that declares `R.tyName j`, in order.
  Without this the companion recursor has too few minor premises, which is
  `InductiveDeclExamples.fooComp_inconsistent`. -/
  ctors_complete : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
      D₀.Declared env ∧ D₀.types[j₀]? = some T₀ ∧ T₀.name = R.tyName j ∧
        npJ j = D₀.np ∧
        T.ctors.map (fun C => R.ctorName C.name) = T₀.ctors.map (·.name)

/-- **`Faithful` is vacuous at `K = []`, for every restoration.**  Every one of its three
clauses is guarded by `T.name ∈ K`, so `Faithful` says nothing at all about the members a step
*declares*.  That is what `VIndRestore.OwnId` below exists to supply; see
`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) for the audit and
`InductiveDeclExamples.pfnJunk_would_have_passed` for the configuration it admits. -/
theorem VIndRestore.faithful_of_nil (R : VIndRestore) (D : VInductDecl')
    (env : VEnv) (npJ : Nat → Nat) : R.Faithful D env [] npJ :=
  ⟨by rintro _ _ _ ⟨⟩, by rintro _ _ _ ⟨⟩, by rintro _ _ _ ⟨⟩⟩

/-- **The restoration is the identity on the members the step declares.**

`Faithful`'s three clauses are all guarded by `T.name ∈ K`: they say nothing whatever about a
member the step *declares*.  That is a hole of exactly the shape the `npJ` one had, and a
larger one, because it is not repairable from inside `Faithful` — at `K = []` every clause is
vacuous, so `Faithful` holds of **every** restoration
(`VIndRestore.faithful_of_nil`, `Theory/Inductive/NestedOrdered.lean`).  With `R.tyName 0`
free, `VInductDecl'.ctorConstsCR` declares the block's own constructors at result types
headed by an arbitrary constant, and `recConstsR` declares its recursors under arbitrary
names; `VEnv.addInductR` still succeeds, and the environment gains constants at types nothing
relates to the block.  `VEnv.addInductR_ordered'`'s three obligations are then not merely
open but **false**, since `Ordered` fails at the very first declared constructor.

So the identity has to be asserted, and this is the assertion: on a member off `K`, the
restoration renames nothing and re-instantiates nothing.  `VInductDecl'.tyAppH_bvars` is the
payoff — under `OwnId`, `tyAppR` at such a member *is* `tyApp`, so restoration is invisible in
exactly the positions the step declares under their own names, which is what makes
`addInductR` agree with `addInduct'` on the user's block.  `VIndRestore.idRestore` satisfies
it for every `K` (`idRestore_ownId`). -/
structure VIndRestore.OwnId (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) : Prop where
  tyName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.tyName j = T.name
  tyLvls : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.tyLvls j = D.ownLvls
  tyArgs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.tyArgs j = VExpr.bvars 0 D.np
  recName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.recName (Lean.mkRecName T.name) = Lean.mkRecName T.name
  ctorName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    ∀ C ∈ T.ctors, R.ctorName C.name = C.name

/-- The identity restoration is the identity on every member, `K` or not. -/
theorem VInductDecl'.idRestore_ownId (D : VInductDecl') (K : List Lean.Name) :
    D.idRestore.OwnId D K where
  tyName j T hT _ := by
    show (D.types.getD j default).name = T.name
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  tyLvls _ _ _ _ := rfl
  tyArgs _ _ _ _ := rfl
  recName _ _ _ _ := rfl
  ctorName _ _ _ _ _ _ := rfl

/-- **The payoff.**  On a member the step declares, the restored type head *is* the block's
own type head — so `VIndCtor.typeR`'s result position, and `recTypeR`'s motive positions at
such a member, are `tyApp` unchanged. -/
theorem VIndRestore.OwnId.tyAppR_eq {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (h : R.OwnId D K) {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∉ K)
    (k : Nat) (args : List VExpr) : D.tyAppR R j k args = D.tyApp j k args := by
  have hg : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyAppR, h.tyName j T hT hK, h.tyLvls j T hT hK, h.tyArgs j T hT hK,
    ← hg, VInductDecl'.tyAppH_bvars]

/-! ## Part 6: the repaired step, assembled

`VEnv.AddCompanion` (`CompanionResolve.lean`) is *resolve, check, extend*.  Part 7 shows
resolution is unavailable on a genuine nested block, so the replacement is *check, verify the
restoration, extend* — with the check being `VInductDecl'.WF` **unchanged**, since the
auxiliary block is an ordinary mutual inductive. -/

/-- **The nested declaration step.**  `K` lists the auxiliary members, `R` is the restoration,
`npJ j` the parameter count of the type member `j` is presented as. -/
def VEnv.AddNested (env : VEnv) (D : VInductDecl') (K : List Lean.Name)
    (R : VIndRestore) (npJ : Nat → Nat) (env' : VEnv) : Prop :=
  D.WF env ∧ D.Canonical ∧ R.OwnId D K ∧ R.Faithful D env K npJ ∧
    env.addInductR D K R = some env'

/-- **The nested step, with the parameter count discharged rather than supplied.**

`npJ` is the only piece of `VEnv.AddNested` a caller *chooses*, and left free it would be a
hole: `Faithful.ty_agree`/`ctor_agree` are equations against `R.instAt D (npJ j) j`, so a
wrong split point would let a companion member be presented at a *different* instantiation of
the block it claims to be, and the companion's recursor would then carry minor premises that
do not match the real block's constructors — `fooComp_inconsistent`'s failure mode reached by
another route.  It is closed inside `Faithful` itself: `ctors_complete` now also asserts
`npJ j = D₀.np`, the parameter count of the block the *environment* holds.  So existentially
quantifying `npJ` here adds nothing a caller could exploit.

This is the premise of `VDecl.WF.inductNested` (`Theory/Typing/Env.lean`).  `VEnv.AddNestedB`
(`Theory/Inductive/NestedBuild.lean`) is the constructive form and implies it
(`AddNestedB.toAddNestedStep`); nothing forces a caller to go through `Faithful` by hand. -/
def VEnv.AddNestedStep (env : VEnv) (D : VInductDecl') (K : List Lean.Name)
    (R : VIndRestore) (env' : VEnv) : Prop :=
  ∃ npJ : Nat → Nat, VEnv.AddNested env D K R npJ env'

end Lean4Lean
