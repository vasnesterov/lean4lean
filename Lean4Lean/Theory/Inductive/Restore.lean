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

/-! ## Part 0a: `substC` against the telescope formers

`VExpr.substC` is a structural homomorphism, so it commutes with every `mk*` former.  These
three live here rather than in `Theory/Inductive/RestoreBridge.lean` (where `substC_mkApp` used
to sit) because `VEnv.addIndRulesR` now substitutes and
`Theory/Inductive/NestedKeys.lean` — which does *not* import `ConstSubstNested.lean` — needs
them to recompute a substituted rule's key. -/

namespace VExpr
variable {σ : CSubst}

theorem substC_mkApp : ∀ {as : List VExpr} {f : VExpr},
    (f.mkApp as).substC σ = (f.substC σ).mkApp (as.map (VExpr.substC · σ))
  | [], _ => rfl
  | a :: as, f => by
    rw [mkApp, List.map_cons, mkApp, substC_mkApp (as := as), substC_app]

theorem substC_mkLams : ∀ {As : List VExpr} {b : VExpr},
    (VExpr.mkLams As b).substC σ = VExpr.mkLams (As.map (VExpr.substC · σ)) (b.substC σ)
  | [], _ => rfl
  | _ :: As, b => by
    rw [VExpr.mkLams_cons, List.map_cons, VExpr.mkLams_cons, VExpr.substC_lam,
      substC_mkLams (As := As)]

@[simp] theorem map_substC_bvars : ∀ {lo n : Nat},
    (bvars lo n).map (VExpr.substC · σ) = bvars lo n
  | _, 0 => rfl
  | lo, n+1 => by rw [bvars, List.map_cons, map_substC_bvars (lo := lo) (n := n)]; rfl

/-! ### The spine head

`spineFn` is `Lean.Expr.getAppFn`.  It used to live in `Theory/Inductive/NestedBuild.lean`
(with `mkApp_spineFn_spineArgs`); it moved here because `VIndRestore.restore` — the
restoration operator `VIndField.typeR` now applies — has to read the head of a spine to
decide whether it is a block occurrence. -/

/-- The head of an application spine (`Lean.Expr.getAppFn`). -/
def spineFn : VExpr → VExpr
  | .app f _ => f.spineFn
  | e => e

@[simp] theorem spineFn_app {f a : VExpr} : (VExpr.app f a).spineFn = f.spineFn := rfl
@[simp] theorem spineFn_const {c : Lean.Name} {ls : List VLevel} :
    (VExpr.const c ls).spineFn = .const c ls := rfl

/-- Every term is its head applied to its spine. -/
theorem mkApp_spineFn_spineArgs : ∀ e : VExpr, mkApp e.spineFn e.spineArgs = e
  | .app f a => by
    rw [spineFn_app, spineArgs, VExpr.mkApp_append, mkApp_spineFn_spineArgs f]; rfl
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ => rfl

theorem spineFn_mkApp : ∀ (as : List VExpr) (f : VExpr), (mkApp f as).spineFn = f.spineFn
  | [], _ => rfl
  | a :: as, f => by rw [VExpr.mkApp_cons, spineFn_mkApp as, spineFn_app]

end VExpr

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

/-! ## Part 1b: the restoration as a **whole-expression rewrite**

`ElimNestedInductive.restoreNested` (`Lean4Lean/Inductive/Add.lean`) is an
`Expr.replaceNoCache` over the *whole* stored expression: at every subterm whose spine head is
an auxiliary constant it emits
`mkAppRange ((nested.abstract r.params).instantiateRev As) r.nparams args.size args`, i.e. the
restored head applied to the occurrence's arguments **from `nparams` on**, and it does *not*
descend into the replacement.  `VIndRestore.restore` is that operator at the `VExpr` level.

**Why a rewrite and not `VExpr.substC`.**  `substC` replaces a constant by a *closed term*, so
it must substitute `mkLams D.params (J.{ls} A)` and leaves the occurrence's own `D.np`
arguments in place — a saturated `D.np`-fold β-redex, which is what
`ntreeNode_substC_ne_typeR` (`Theory/Typing/ConstSubstNested.lean`) exhibits.  `TrConstant`
(`Verify/Environment/Basic.lean`) relates a declared constant to the implementation's through
`TrExprS`, which has **no defeq slack**, so a specification that declared the redex would make
`addDecl.WF` false for every parameterised nested block.  The rewrite *contracts*: it drops the
occurrence's own parameter run and splices `R.tyArgs j` weakened past the enclosing binders,
which is `VInductDecl'.tyAppR` on the nose.  (Row 36 of `docs/vacuity-ledger.md` is the record
of getting this backwards once.)

**Why the trigger is the *uniform* occurrence.**  `ElimNestedInductive.replaceIfNested` inserts
an auxiliary occurrence only as `mkAppRange (mkAppN (.const auxJ_name st.lvls) As) I_nparams …`
— the auxiliary constant at the **block's own levels** applied to the **block's own parameter
run** and then to the occurrence's indices.  So every occurrence the restoration has to undo is
syntactically `I_j.{D.ownLvls} (bvars k D.np ++ π)`, and that is exactly the trigger below.
It is also exactly the condition C++'s `check_uniform_ind_occs` (`inductive.cpp`) enforces
syntactically before nested elimination (ledger row 116e), and exactly
`CGMGuard.cgmValidIndApp`'s condition (`Verify/Inductive/CanonGapMeasure.lean` §3).

The point of the trigger being *syntactic and total* is that it needs no side condition: the
operator is defined on every `VExpr`, and `restore_id` — the identity restoration restores
nothing — holds **unconditionally**, which is what removes `VInductDecl'.Canonical` from
`NestedHead.lean`'s Part 3. -/

namespace VInductDecl'

/-- `memberIdxFrom ms n i`: the position of `n` in `ms`, offset by `i`. -/
def memberIdxFrom : List Name → Name → Nat → Option Nat
  | [], _, _ => none
  | m :: ms, n, i => if m = n then some i else memberIdxFrom ms n (i+1)

/-- Which member of the block the name `n` is, if any. -/
def memberIdx (D : VInductDecl') (n : Name) : Option Nat := memberIdxFrom D.blockNames n 0

theorem memberIdxFrom_spec : ∀ (ms : List Name) (n : Name) (i j : Nat),
    memberIdxFrom ms n i = some j → ∃ k, j = i + k ∧ ms[k]? = some n
  | [], _, _, _, h => absurd h nofun
  | m :: ms, n, i, j, h => by
    rw [memberIdxFrom] at h
    split at h
    · next he => cases h; exact ⟨0, rfl, by rw [List.getElem?_cons_zero, he]⟩
    · obtain ⟨k, rfl, hk⟩ := memberIdxFrom_spec ms n (i+1) j h
      exact ⟨k+1, by omega, by rwa [List.getElem?_cons_succ]⟩

theorem memberIdxFrom_none : ∀ (ms : List Name) (n : Name) (i : Nat),
    n ∉ ms → memberIdxFrom ms n i = none
  | [], _, _, _ => rfl
  | m :: ms, n, i, h => by
    rw [memberIdxFrom, if_neg (fun he => h (List.mem_cons.2 (Or.inl he.symm)))]
    exact memberIdxFrom_none ms n (i+1) (fun hm => h (List.mem_cons_of_mem _ hm))

theorem memberIdxFrom_complete : ∀ (ms : List Name) (n : Name) (i k : Nat),
    ms.Nodup → ms[k]? = some n → memberIdxFrom ms n i = some (i + k)
  | [], _, _, _, _, h => absurd h nofun
  | m :: ms, n, i, 0, _, hk => by
    rw [memberIdxFrom, if_pos (by simpa using hk)]; rw [Nat.add_zero]
  | m :: ms, n, i, k+1, hnd, hk => by
    rw [List.getElem?_cons_succ] at hk
    have hne : m ≠ n := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_of_getElem? hk)
    rw [memberIdxFrom, if_neg hne,
      memberIdxFrom_complete ms n (i+1) k (List.nodup_cons.1 hnd).2 hk]
    congr 1; omega

theorem memberIdx_spec' {D : VInductDecl'} {n : Name} {j : Nat}
    (h : D.memberIdx n = some j) : ∃ T, D.types[j]? = some T ∧ T.name = n := by
  obtain ⟨k, rfl, hk⟩ := memberIdxFrom_spec _ _ _ _ h
  rw [Nat.zero_add]
  rw [VInductDecl'.blockNames, List.getElem?_map, Option.map_eq_some_iff] at hk
  obtain ⟨T, hT, rfl⟩ := hk
  exact ⟨T, hT, rfl⟩

theorem memberIdx_spec {D : VInductDecl'} {n : Name} {j : Nat}
    (h : D.memberIdx n = some j) : (D.types.getD j default).name = n := by
  obtain ⟨T, hT, rfl⟩ := memberIdx_spec' h
  rw [List.getD_eq_getElem?_getD, hT]; rfl

theorem memberIdx_none {D : VInductDecl'} {n : Name} (h : n ∉ D.blockNames) :
    D.memberIdx n = none := memberIdxFrom_none _ _ _ h

theorem memberIdx_complete {D : VInductDecl'} (hnd : D.blockNames.Nodup) {j : Nat}
    {T : VIndType} (hT : D.types[j]? = some T) : D.memberIdx T.name = some j := by
  have h : D.blockNames[j]? = some T.name := by
    rw [VInductDecl'.blockNames, List.getElem?_map, hT]; rfl
  show memberIdxFrom D.blockNames T.name 0 = some j
  simpa using memberIdxFrom_complete _ _ 0 j hnd h

/-! The trigger is a *decision*, so `VExpr` needs decidable equality.  (These two
`deriving instance` lines used to sit in `Theory/Inductive/NestedBuild.lean`, where
`VIndRestore.recogAt` — the opposite direction, restored form to `VIndRecArg` — needs them
too.) -/
deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

/-- **The trigger.**  Is `e`, sitting `k` binders above the block's parameter telescope, a
*uniform* occurrence `I_j.{D.ownLvls} (bvars k D.np ++ π)` of a block member?  If so, its
member index and the residual arguments `π`. -/
def uniformOcc? (D : VInductDecl') (k : Nat) (e : VExpr) : Option (Nat × List VExpr) :=
  match e.spineFn with
  | .const n ls =>
    match D.memberIdx n with
    | some j =>
      if ls = D.ownLvls ∧ e.spineArgs.take D.np = bvars k D.np then
        some (j, e.spineArgs.drop D.np)
      else none
    | none => none
  | _ => none

/-- **Soundness of the trigger**: what it fires on *is* the occurrence it reports. -/
theorem uniformOcc?_sound {D : VInductDecl'} {k : Nat} {e : VExpr} {j : Nat} {rest : List VExpr}
    (h : D.uniformOcc? k e = some (j, rest)) : D.tyApp j k rest = e := by
  rw [uniformOcc?] at h
  split at h
  · next n ls hsp =>
    split at h
    · next j' hj =>
      split at h
      · next hc =>
        obtain ⟨rfl, h2⟩ := hc
        cases h
        rw [VInductDecl'.tyApp, memberIdx_spec hj, ← h2, List.take_append_drop, ← hsp,
          VExpr.mkApp_spineFn_spineArgs]
      · exact absurd h nofun
    · exact absurd h nofun
  · exact absurd h nofun

theorem noBlock_spineFn {D : VInductDecl'} : ∀ {e : VExpr}, D.NoBlock e →
    ∀ {n : Name} {ls : List VLevel}, e.spineFn = .const n ls → n ∉ D.blockNames
  | .app _ _, h, _, _, hs => noBlock_spineFn h.1 hs
  | .const _ _, h, _, _, hs => by cases hs; exact h
  | .bvar _, _, _, _, hs | .sort _, _, _, _, hs
  | .lam _ _, _, _, _, hs | .forallE _ _, _, _, _, hs => by cases hs

theorem noConsts_spineFn {S : List Name} : ∀ {e : VExpr}, VExpr.NoConsts S e →
    ∀ {n : Name} {ls : List VLevel}, e.spineFn = .const n ls → n ∉ S
  | .app _ _, h, _, _, hs => noConsts_spineFn h.1 hs
  | .const _ _, h, _, _, hs => by cases hs; exact h
  | .bvar _, _, _, _, hs | .sort _, _, _, _, hs
  | .lam _ _, _, _, _, hs | .forallE _ _, _, _, _, hs => by cases hs

/-- The trigger does not fire inside a block-free expression. -/
theorem uniformOcc?_noBlock {D : VInductDecl'} {k : Nat} {e : VExpr} (h : D.NoBlock e) :
    D.uniformOcc? k e = none := by
  cases hs : e.spineFn with
  | const n ls => simp only [uniformOcc?, hs, memberIdx_none (noBlock_spineFn h hs)]
  | _ => simp only [uniformOcc?, hs]

/-- **Completeness of the trigger** on the canonical head: it fires on `tyApp`, at the member
it names.  `Nodup` is needed because `memberIdx` reads the *first* member of that name; it is
the hypothesis `VEnv.addConstList`'s success supplies (`Theory/Inductive/Nested.lean`). -/
theorem uniformOcc?_tyApp {D : VInductDecl'} (hnd : D.blockNames.Nodup) {j : Nat}
    {T : VIndType} (hT : D.types[j]? = some T) (k : Nat) (args : List VExpr) :
    D.uniformOcc? k (D.tyApp j k args) = some (j, args) := by
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp, uniformOcc?, VExpr.spineFn_mkApp, hg]
  simp only [VExpr.spineFn_const, memberIdx_complete hnd hT, VExpr.spineArgs_mkApp,
    VExpr.spineArgs, List.nil_append]
  rw [show List.take D.np (bvars k D.np ++ args) = bvars k D.np from by simp,
    show List.drop D.np (bvars k D.np ++ args) = args from by simp, if_pos ⟨trivial, rfl⟩]

end VInductDecl'

namespace VIndRestore

/-- **The restoration, as a whole-expression rewrite** — `ElimNestedInductive.restoreNested`'s
`Expr.replaceNoCache` at the `VExpr` level.  `k` is the number of binders between the block's
parameter telescope and the current position, which is what `R.tyArgs j` has to be weakened
past.  Like `replaceNoCache`, the operator does **not** descend into a replacement. -/
def restore (R : VIndRestore) (D : VInductDecl') : Nat → VExpr → VExpr
  | _, .bvar i => .bvar i
  | _, .sort u => .sort u
  | k, .const n ls =>
    match D.uniformOcc? k (.const n ls) with
    | some (j, rest) => D.tyAppR R j k rest
    | none => .const n ls
  | k, .app f a =>
    match D.uniformOcc? k (.app f a) with
    | some (j, rest) => D.tyAppR R j k rest
    | none => .app (R.restore D k f) (R.restore D k a)
  | k, .lam A b => .lam (R.restore D k A) (R.restore D (k+1) b)
  | k, .forallE A b => .forallE (R.restore D k A) (R.restore D (k+1) b)

theorem tyAppR_idRestore (D : VInductDecl') (j k : Nat) (args : List VExpr) :
    D.tyAppR D.idRestore j k args = D.tyApp j k args := D.tyAppH_bvars j k args

/-- **The identity restoration restores nothing, unconditionally.**

This is the whole point of the reparameterisation: `VIndField.typeR_id` and every collapse
lemma below it used to need `VIndCtor.Canonical`, because `typeR`'s `some` branch *replaced*
the stored type by the canonical one.  With the branch a restoration of the stored type, the
collapse is this lemma, and it has no hypotheses. -/
theorem restore_id (D : VInductDecl') : ∀ (k : Nat) (e : VExpr), D.idRestore.restore D k e = e
  | _, .bvar _ | _, .sort _ => rfl
  | k, .const n ls => by
    rw [restore]
    split
    · next h => rw [tyAppR_idRestore]; exact VInductDecl'.uniformOcc?_sound h
    · rfl
  | k, .app f a => by
    rw [restore]
    split
    · next h => rw [tyAppR_idRestore]; exact VInductDecl'.uniformOcc?_sound h
    · rw [restore_id D k f, restore_id D k a]
  | k, .lam A b => by rw [restore, restore_id D k A, restore_id D (k+1) b]
  | k, .forallE A b => by rw [restore, restore_id D k A, restore_id D (k+1) b]

/-- **The restoration is the identity on a block-free expression** — for *every* `R`. -/
theorem restore_noBlock {R : VIndRestore} {D : VInductDecl'} :
    ∀ (k : Nat) (e : VExpr), D.NoBlock e → R.restore D k e = e
  | _, .bvar _, _ | _, .sort _, _ => rfl
  | _, .const _ _, h => by rw [restore, VInductDecl'.uniformOcc?_noBlock h]
  | k, .app f a, h => by
    rw [restore, VInductDecl'.uniformOcc?_noBlock h, restore_noBlock k f h.1,
      restore_noBlock k a h.2]
  | k, .lam A b, h => by rw [restore, restore_noBlock k A h.1, restore_noBlock (k+1) b h.2]
  | k, .forallE A b, h => by rw [restore, restore_noBlock k A h.1, restore_noBlock (k+1) b h.2]

/-- `restore` passes through a block-free binder telescope, tracking the depth. -/
theorem restore_mkPi_noBlock {R : VIndRestore} {D : VInductDecl'} :
    ∀ (As : List VExpr) (k : Nat) (b : VExpr), (∀ A ∈ As, D.NoBlock A) →
      R.restore D k (mkPi As b) = mkPi As (R.restore D (k + As.length) b)
  | [], _, _, _ => rfl
  | A :: As, k, b, h => by
    rw [VExpr.mkPi_cons, restore, restore_noBlock k A (h A List.mem_cons_self),
      restore_mkPi_noBlock As (k+1) b (fun B hB => h B (List.mem_cons_of_mem _ hB)),
      VExpr.mkPi_cons, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

/-- **The restoration of a uniform head is the restored head** — `tyApp ↦ tyAppR`, which is
what the whole apparatus is about. -/
theorem restore_tyApp {R : VIndRestore} {D : VInductDecl'} (hnd : D.blockNames.Nodup) {j : Nat}
    {T : VIndType} (hT : D.types[j]? = some T) (k : Nat) (args : List VExpr) :
    R.restore D k (D.tyApp j k args) = D.tyAppR R j k args := by
  have h := VInductDecl'.uniformOcc?_tyApp hnd hT k args (D := D)
  cases hsp : D.tyApp j k args with
  | const n ls => rw [restore]; rw [hsp] at h; rw [h]
  | app f a => rw [restore]; rw [hsp] at h; rw [h]
  | bvar i => rw [hsp] at h; exact absurd h nofun
  | sort u => rw [hsp] at h; exact absurd h nofun
  | lam A b => rw [hsp] at h; exact absurd h nofun
  | forallE A b => rw [hsp] at h; exact absurd h nofun

end VIndRestore

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

/-- The stored type of field `i`, restored.

**The `some` branch restores the *stored* type; it used to be `r.canonTypeR D R i`, the
canonical form with the head rewritten** (ledger ruling 116d).  The old branch *replaced* the
stored type rather than rewriting it, and the substitution was sound only under
`VIndCtor.Canonical` — a **syntactic** demand that `F.type` be `r.canonType D i` on the nose.
That demand is machine-checked **false** at a real Lean declaration: `ElimNestedInductive.run`
manufactures a recursive field whose stored type is a β-redex whenever a block nests through an
inductive with a dependent parameter, which `Lean.Json` and `Lean.PrefixTreeNode` both do
(`CGMAbstract.cgm_not_canonical`, `Verify/Inductive/CanonGapMeasure.lean`).  `Canonical` was
load-bearing **only** for the collapse equations of `Theory/Inductive/NestedHead.lean` Part 3,
and with this branch a rewrite those hold unconditionally
(`VIndRestore.restore_id`) — so it is gone.

The `none` branch stays `F.type` verbatim: `VInductDecl'.ctorConstsCR` and
`VInductDecl'.iotaRulesRS` apply `VExpr.substC` on top of `typeR`, and that is what cleans a
companion constant out of a *non*-recursive field (ledger row 26's repair).  Restoring it here
as well would change what those declare, which is a separate change with its own proof debt;
see ledger row 116f(i), which records that this docstring used to *claim* the `none` branch was
restored while the code did not do it. -/
def VIndField.typeR (F : VIndField) (D : VInductDecl') (R : VIndRestore) (i : Nat) : VExpr :=
  match F.recArg with
  | none => F.type
  | some _ => R.restore D i F.type

namespace VIndRestore

/-- **The bridge to the canonical restored form.**  On a *canonical* recursive field whose
binder telescope is block-free — the second is `VIndField.WF.pos`'s own conjunct, the first is
what `VIndCtor.Canonical` used to assert — restoring the **stored** type gives
`VIndRecArg.canonTypeR`, i.e. exactly what `VIndField.typeR`'s `some` branch used to *be*.

So the old definition is the special case of the new one at a canonical field, and every
statement that genuinely reads the canonical restored telescope can recover it here.  This is
where the conditionality went: it is no longer in the collapse lemmas, it is in this bridge. -/
theorem restore_canonType {R : VIndRestore} {D : VInductDecl'} (hnd : D.blockNames.Nodup)
    {r : VIndRecArg} {T : VIndType} (hT : D.types[r.idx]? = some T) {i : Nat}
    (hb : ∀ B ∈ r.binders, D.NoBlock B) :
    R.restore D i (r.canonType D i) = r.canonTypeR D R i := by
  rw [VIndRecArg.canonType, restore_mkPi_noBlock _ _ _ hb, VIndRecArg.canonTypeR,
    VIndRecArg.canonResult, VIndRecArg.canonResultR,
    show i + r.binders.length = r.binders.length + i from by omega,
    restore_tyApp hnd hT]


/-- **`VIndField.typeR` at a canonical field is what it used to be.**  So the change is a
generalisation of the old definition, not a rival one — at every field the old definition was
*sound* for. -/
theorem typeR_canonical {R : VIndRestore} {D : VInductDecl'} (hnd : D.blockNames.Nodup)
    {F : VIndField} {r : VIndRecArg} {T : VIndType} (hr : F.recArg = some r)
    (hT : D.types[r.idx]? = some T) {i : Nat} (hb : ∀ B ∈ r.binders, D.NoBlock B)
    (hcanon : F.type = r.canonType D i) : F.typeR D R i = r.canonTypeR D R i := by
  rw [VIndField.typeR, hr, hcanon, restore_canonType hnd hT hb]

end VIndRestore

/-- The constructor's stored field telescope, restored. -/
def VIndCtor.fieldTypesR (C : VIndCtor) (D : VInductDecl') (R : VIndRestore) : List VExpr :=
  C.fields.zipIdx.map fun (F, i) => F.typeR D R i

/-- **A syntactic side condition that is FALSE on the nested path, and is no longer a
hypothesis of anything in the specification.**

This docstring used to read: *"`VIndField.WF.pos` requires a recursive field's stored type to be
only definitionally `∀ ξ, I_idx params π`, so `typeR` — which rewrites the canonical form — is
the stored form only on a block whose recursive fields are stored canonically.  Every witness in
`Theory/Inductive/DeclExamples.lean` is canonical, and so is every constructor
`ElimNestedInductive` generates: `replaceIfNested` builds an auxiliary constructor's field types
by instantiating the nested type's own stored type, whose recursive positions are applications of
a block constant on the nose."*  **The last claim is machine-checked false** (ledger row 116a).
`instantiateForallParams` is a plain `instantiateRevRange` with no β step, so when a block nests
through an inductive with a *dependent* parameter `β : ι → Sort v` and the instance supplies
`β := fun _ => I`, a field stored as `β k` becomes the β-redex `(fun _ => I) k` — a **recursive**
field of the auxiliary block whose stored type is `.app`-headed, which no `r.canonType D i` ever
is (`CGMAbstract.cgm_canonType_ne_redex` / `cgm_not_canonical`,
`Verify/Inductive/CanonGapMeasure.lean`).  `Lean.Json` and `Lean.PrefixTreeNode` are both real
instances, reproduced from the empty environment by `CGMNestWit`.

Under ruling 116d it is **no longer a conjunct of `VEnv.AddNested`** and no longer a hypothesis
of any conservativity equation: `VIndField.typeR`'s `some` branch restores the *stored* type, so
`Theory/Inductive/NestedHead.lean` Part 3 collapses through `VIndRestore.restore_id`, which has
no hypotheses.  **The definition survives only because `Verify/` files still name it** —
`Verify/Inductive/CanonGapMeasure.lean` (which *refutes* it), `TrIndDeclNCtorOwn.lean`,
`NestedRestoreWit.lean`, `AddInductiveStep.lean`, `RunIdentity.lean`, `Environment/InductR.lean`
— and `Theory/Inductive/` may not edit those.  **The remaining deletion is those sites plus
these two definitions.** -/
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

/-- **The ι-rules the step actually registers**: the restored ones with the restoration
substituted through them, exactly as `ctorConstsCR` and `recConstsR` do for the constants.

The `substC` is the same repair, for the same defect and at the same place in the
construction.  `VInductDecl'.iotaCtxR` splices `C.fieldTypesR`, whose **non**-recursive
entries `VIndField.typeR` copies verbatim; `VIndField.WF.pos`'s `none` branch makes those only
*definitionally* block-free, so a companion constant could sit under a redex in one and the
step emitted a rule whose `type` named a constant the environment does not hold.  That is
`InductiveDeclExamples.nfnNodeDirty_fieldTypesR_dirty` /
`nfnAuxDirty_iotaCtxR_eq` (`Theory/Inductive/RestoreBridge.lean`), the block on which
obligation **(C)** of `VEnv.addInductR_ordered'` was false — the same witness that used to
refute **(A)** before `ctorConstsCR` gained its `substC`.

It is `csubst`, not `csubstTy`: an ι-rule mentions the companion's *constructors* (the major
premise) and its *recursor* (the induction hypotheses' calls) as well as its type, and all
three have to go.  The cost is that the rule's **key** is no longer `rfl`-visible:
`VInductDecl'.key_iotaRulesRS` (`Theory/Inductive/NestedKeys.lean`) is what re-establishes it,
from the fact that the *restored* recursor and constructor heads lie outside σ's domain. -/
def iotaRulesRS (K : List Lean.Name) : List VDefEq :=
  (D.iotaRulesR R).map (·.substC (R.csubst D K))

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

/-- The block's ι-rules, restored, renamed **and substituted** — `VInductDecl'.iotaRulesRS`.

This used to fold `D.iotaRulesR R` unsubstituted, which is what made obligation **(C)** of
`VEnv.addInductR_ordered'` false at `nfnAuxDirty`.  `K` is a parameter for exactly that
reason: the substitution `R.csubst D K` needs the companion list. -/
def VEnv.addIndRulesR (env : VEnv) (D : VInductDecl') (K : List Lean.Name) (R : VIndRestore) :
    VEnv := (D.iotaRulesRS R K).foldl VEnv.addDefEq env

/-- **The repaired companion-aware extension.**  `VEnv.addInductC` with the restoration
threaded all the way through: the constants it declares and the rules it emits are built from
the *same* `R`, which is what G4 was the absence of. -/
def VEnv.addInductR (env : VEnv) (D : VInductDecl') (K : List Lean.Name) (R : VIndRestore) :
    Option VEnv :=
  (env.addConstList (D.allConstsCR R K)).map (·.addIndRulesR D K R)

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

/-- **The restoration's own heads escape its own substitution.**

`VEnv.addIndRulesR` substitutes `R.csubst D K` through every ι-rule it registers, and a
substitution can move a rule's **key** (`VDefEq.key`): the key is the constant heading the
λ-peeled left-hand side plus the constant heading that spine's last argument, and those two
are `R.recName (mkRecName I_j)` and `R.ctorName C.name`.  If either were in σ's domain the
rewrite would replace it by a term, and `VInductDecl'.key_iotaRuleR` — which every
`KeysDeclared`/`KeyUnique` argument reads the key off — would no longer describe the rule the
environment holds.

This says it does not happen: the *restored* recursor and constructor heads are outside the
domain, which holds of every restoration that presents a companion member as a block the
environment already has (σ's domain is the **auxiliary** names `_nested.X`, the restored heads
are the real ones).

Like `VIndRestore.KeysDistinct` (`Theory/Inductive/NestedKeys.lean`) it is a purely syntactic
property of `R`, `D` and `K`, `decide`-able at a concrete block, and it is *not* derivable from
`Faithful` + `OwnId` + the two `addConstList` successes: nothing among those forbids
`R.recName (mkRecName I_j)` from being literally the auxiliary name `T.name` of a companion
member, since a companion member's own name is declared by *no* step (`typeConstsC` removes it)
and so freshness cannot separate the two.  That gap is why this is a hypothesis and not a
lemma; §3.3 of `NestedKeys.lean` discharges it at both nested witnesses. -/
def VIndRestore.KeysFree (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) : Prop :=
  ∀ p ∈ D.ctorsAll,
    R.csubst D K (R.recName (Lean.mkRecName (D.types.getD p.1 default).name)) = none ∧
    R.csubst D K (R.ctorName p.2.name) = none

/-- At `K = []` the substitution is empty, so `KeysFree` is free. -/
theorem VIndRestore.keysFree_nil (R : VIndRestore) (D : VInductDecl') : R.KeysFree D [] := by
  intro _ _
  rw [R.csubst_nil D]
  exact ⟨rfl, rfl⟩

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

namespace VIndRestore

/-- The rewrite the trigger performs is the **identity** at a member off `K` — the payoff of
`VIndRestore.OwnId`, at an arbitrary occurrence rather than at a `tyApp` written by hand. -/
theorem uniformOcc?_tyAppR_eq {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (hown : R.OwnId D K) {k : Nat} {e : VExpr} {j : Nat} {rest : List VExpr}
    (hu : D.uniformOcc? k e = some (j, rest)) (h : VExpr.NoConsts K e) :
    D.tyAppR R j k rest = D.tyApp j k rest := by
  rw [VInductDecl'.uniformOcc?] at hu
  split at hu
  · next m ms hsp =>
    split at hu
    · next hj =>
      split at hu
      · cases hu
        obtain ⟨T, hT, rfl⟩ := VInductDecl'.memberIdx_spec' hj
        exact hown.tyAppR_eq hT (VInductDecl'.noConsts_spineFn h hsp) _ _
      · exact absurd hu nofun
    · exact absurd hu nofun
  · exact absurd hu nofun

/-- **The restoration is the identity on anything free of *companion* constants** — which is
the fact the implementation's side has for free, since `ElimNestedInductive` invents the
auxiliary names.  Strictly weaker than `restore_noBlock`: an occurrence of a member the step
*declares* may be present, and `OwnId` makes the rewrite the identity on it
(`VIndRestore.OwnId.tyAppR_eq`).  This is the abstract counterpart of "`restoreNested` rewrites
exactly the names in `aux2nested`". -/
theorem restore_noK {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (hown : R.OwnId D K) :
    ∀ (k : Nat) (e : VExpr), VExpr.NoConsts K e → R.restore D k e = e
  | _, .bvar _, _ | _, .sort _, _ => rfl
  | k, .const n ls, h => by
    rw [restore]
    split
    · next hu => rw [uniformOcc?_tyAppR_eq hown hu h]; exact VInductDecl'.uniformOcc?_sound hu
    · rfl
  | k, .app f a, h => by
    rw [restore]
    split
    · next hu => rw [uniformOcc?_tyAppR_eq hown hu h]; exact VInductDecl'.uniformOcc?_sound hu
    · rw [restore_noK hown k f h.1, restore_noK hown k a h.2]
  | k, .lam A b, h => by
    rw [restore, restore_noK hown k A h.1, restore_noK hown (k+1) b h.2]
  | k, .forallE A b, h => by
    rw [restore, restore_noK hown k A h.1, restore_noK hown (k+1) b h.2]

/-- `restore` passes through a companion-free binder telescope, tracking the depth. -/
theorem restore_mkPi_noK {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (hown : R.OwnId D K) :
    ∀ (As : List VExpr) (k : Nat) (b : VExpr), (∀ A ∈ As, VExpr.NoConsts K A) →
      R.restore D k (mkPi As b) = mkPi As (R.restore D (k + As.length) b)
  | [], _, _, _ => rfl
  | A :: As, k, b, h => by
    rw [VExpr.mkPi_cons, restore, restore_noK hown k A (h A List.mem_cons_self),
      restore_mkPi_noK hown As (k+1) b (fun B hB => h B (List.mem_cons_of_mem _ hB)),
      VExpr.mkPi_cons, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

/-- **The bridge, in the form the built companion member needs**: `restore` of the *stored*
canonical form is `canonTypeR`, with the binder telescope only required to be free of
**companion** constants rather than of every block constant.  This is what
`VNestedOcc.field_typeR` uses, and the weaker hypothesis is the one that is actually true there
— a nested occurrence's binders routinely mention the block's *own* members (`Tree α`). -/
theorem restore_canonType_noK {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (hown : R.OwnId D K) (hnd : D.blockNames.Nodup)
    {r : VIndRecArg} {T : VIndType} (hT : D.types[r.idx]? = some T) {i : Nat}
    (hb : ∀ B ∈ r.binders, VExpr.NoConsts K B) :
    R.restore D i (r.canonType D i) = r.canonTypeR D R i := by
  rw [VIndRecArg.canonType, restore_mkPi_noK hown _ _ _ hb, VIndRecArg.canonTypeR,
    VIndRecArg.canonResult, VIndRecArg.canonResultR,
    show i + r.binders.length = r.binders.length + i from by omega,
    restore_tyApp hnd hT]

end VIndRestore

/-! ## Part 6: the repaired step, assembled

`VEnv.AddCompanion` (`CompanionResolve.lean`) is *resolve, check, extend*.  Part 7 shows
resolution is unavailable on a genuine nested block, so the replacement is *check, verify the
restoration, extend* — with the check being `VInductDecl'.WF` **unchanged**, since the
auxiliary block is an ordinary mutual inductive. -/

/-- **The nested declaration step.**  `K` lists the auxiliary members, `R` is the restoration,
`npJ j` the parameter count of the type member `j` is presented as. -/
def VEnv.AddNested (env : VEnv) (D : VInductDecl') (K : List Lean.Name)
    (R : VIndRestore) (npJ : Nat → Nat) (env' : VEnv) : Prop :=
  D.WF env ∧ R.OwnId D K ∧ R.Faithful D env K npJ ∧
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
