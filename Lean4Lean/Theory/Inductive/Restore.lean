import Lean4Lean.Theory.Inductive.Decl

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

/-- The stored type of field `i`, restored.  A non-recursive field mentions no block constant
(up to defeq) and is emitted verbatim; a recursive one is `∀ ξ, I_idx params π` and its head
is the thing restoration rewrites. -/
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
never declared at all. -/
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
`VInductDecl'.recConstsC` with the type restored as well as the name renamed. -/
def recConstsR : List (Lean.Name × VConstant) :=
  D.types.zipIdx.map fun (T, j) =>
    (R.recName (Lean.mkRecName T.name), ⟨D.recUvars, D.recTypeR R j⟩)

/-- The constructor constants actually declared, with restored names and types. -/
def ctorConstsCR (K : List Lean.Name) : List (Lean.Name × VConstant) :=
  D.ctorsAll.filterMap fun (j, C) =>
    if (D.types.getD j default).name ∈ K then none
    else some (R.ctorName C.name, ⟨D.uvars, C.typeR D R j⟩)

def allConstsCR (K : List Lean.Name) : List (Lean.Name × VConstant) :=
  D.typeConstsC K ++ D.ctorConstsCR R K ++ D.recConstsR R

def allNamesCR (K : List Lean.Name) : List Lean.Name := (D.allConstsCR R K).map (·.1)

end VInductDecl'

/-- The block's ι-rules, restored and renamed. -/
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

/-! ## Part 6: the repaired step, assembled

`VEnv.AddCompanion` (`CompanionResolve.lean`) is *resolve, check, extend*.  Part 7 shows
resolution is unavailable on a genuine nested block, so the replacement is *check, verify the
restoration, extend* — with the check being `VInductDecl'.WF` **unchanged**, since the
auxiliary block is an ordinary mutual inductive. -/

/-- **The nested declaration step.**  `K` lists the auxiliary members, `R` is the restoration,
`npJ j` the parameter count of the type member `j` is presented as. -/
def VEnv.AddNested (env : VEnv) (D : VInductDecl') (K : List Lean.Name)
    (R : VIndRestore) (npJ : Nat → Nat) (env' : VEnv) : Prop :=
  D.WF env ∧ D.Canonical ∧ R.Faithful D env K npJ ∧ env.addInductR D K R = some env'

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
