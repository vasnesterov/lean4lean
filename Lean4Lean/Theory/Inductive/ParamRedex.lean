import Lean4Lean.Theory.Inductive.StoredIota

/-!
# A **parameterised** redex block, and §T15's assembly at it

Ledger row 129b measured the limit of `Theory/Inductive/StoredIota.lean`: at `D.np = 0` the two
sides of §T15.7's `hrec` are the *same* `VExpr` after `σ` (`MRedex.MRWit.mr_obj_entry_substC_eq`,
by `decide`), so what §5.2 of that file proves at the companion-pointing field `MJ.obj` is a
**typing, not a conversion**.  The reason is `VIndRestore.substC_tyApp_comp`: substituting a
companion head yields `(mkLams D.params (R.tyBody D j)).mkApp (bvars k D.np ++ args)`, and at
`D.np = 0` that is `R.tyBody D j` on the nose — the redex is *empty*.  So the layer's one genuine
conversion is invisible at every block in the tree, and the residual was a **missing witness**
rather than a missing proof.

This file supplies the witness.  `MP` is `MRWit.MJ` with one (phantom) parameter, nesting through
the *same* `MRWit.MDep`, so the auxiliary block `mpAux mpAuxNodeB` is

* a **redex block** — Lean's own `MP.rec_1` stores the companion's field as `(fun x => MP α) k`
  (`mpAuxB_not_canonical`), exactly as at `MJ`, `Lean.Json` and `Lean.PrefixTreeNode`;
* **parameterised** — `np = 1` (`mpAuxB_np_one`), which is what row 129b says no block in this
  tree was.

What changes, and it is the point: at `np = 1` the substituted companion head is a **saturated
one-fold β-redex** and the restored head is its contractum, so the two sides of `hrec` are
different expressions (`mp_obj_entry_substC_ne`, `decide`) and §T15.7's obligation at `MJ.obj`'s
analogue is a **genuine conversion**.

What does *not* change, and it is the honest half: the `np = 0` route to obligations (B) and (C)
is unavailable here by its very first hypothesis (`hp : D.params = []`), and `hcl0` — the closedness
of the presented spine at `0` — is **false** at this block (`mp_not_tyArgs_closed0`).  So this
witness exercises §T15.7 and §T16.1 and refutes the hypotheses of §7.5–§7.7's strict equations; it
does not discharge (B)/(C), and §4 says exactly which step stops.
-/

namespace Lean4Lean
namespace MRedex
namespace MPWit

open Lean (Name)
open MRedex.MRWit (MDep mrNode mrDepDecl)

/-! ## §1 The block

`MP` is `MJ` with a parameter the constructor does not use: the nesting is the same
`MDep Prop (fun _ => ·)`, so everything row 127f/129b measured at `MJ` can be compared coordinate
by coordinate, and the *only* coordinate that moves is `np`. -/

/-- A parameterised sibling of `MRWit.MJ`.  Lean's own kernel runs the nested elimination and
stores the companion recursor `MP.rec_1`, whose companion minor premise has the field domain
`(fun x => MP α) k` — the redex. -/
inductive MP (α : Type) : Type where
  | obj : MDep Prop (fun _ => MP α) → MP α

def mpNestedName : Name := `_nested.MDep_1

/-- The field the elimination manufactures, one binder deeper than `MRWit.mrRedex` because the
parameter telescope is now non-empty: `(fun x : Prop => MP #2) #0`, in the context
`[field₀, α]`. -/
def mpRedex : VExpr := .app (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 2))) (.bvar 0)

/-- The companion constructor **as `VNestedOcc.field` computes it** — the stored redex, recorded
as recursive (`mpAuxNodeB_built`). -/
def mpAuxNodeB : VIndCtor where
  name := `_nested.MDep_1.node
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := mpRedex, lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

/-- The user's constructor, after `replaceAllNested` points it at the auxiliary member:
`_nested.MDep_1 α`, which is `tyApp 1 0 []` and therefore canonical. -/
def mpObj : VIndCtor where
  name := ``MP.obj
  params := [.sort (.succ .zero)]
  fields := [{ type := .app (.const mpNestedName []) (.bvar 0), lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def mpAux (Cn : VIndCtor) : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``MP, type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)),
       indices := [], ctors := [mpObj] },
     { name := mpNestedName, type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)),
       indices := [], ctors := [Cn] }]

def mpK : List Name := [mpNestedName]

/-- The presented spine of the companion **mentions the parameter** — that is the whole
difference from `MRWit.mrRestore`, and it is what makes `hcl0` false and `hrec` a conversion. -/
def mpRestore : VIndRestore where
  tyName j := if j = 1 then ``MDep else ``MP
  tyLvls _ := []
  tyArgs j := if j = 1 then [.sort .zero, .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))]
    else [.bvar 0]
  ctorName n := if n = `_nested.MDep_1.node then ``MDep.node else n
  recName n := if n = `_nested.MDep_1.rec then ``MP.rec_1 else n

def mpOcc : VNestedOcc where
  decl := mrDepDecl
  idx := 0
  lvls := []
  args := [.sort .zero, .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))]
  auxName := mpNestedName
  ctorName n := if n = ``MDep.node then `_nested.MDep_1.node else n

/-! ### The transcription, anchored on Lean's own environment -/

example : ((mpAux mpAuxNodeB).types.getD 0 default).type = (vconst(type_of% @MP)).type := rfl

/-- The user's member and its constructor are the ones the environment holds, once the
companion constant is substituted away. -/
theorem mp_obj_declared :
    (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
      (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK) = (vconst(type_of% @MP.obj)).type := rfl

example : (mpAux mpAuxNodeB).recUvars = (vconst(type_of% @MP.rec)).uvars := rfl

/-! ### …and on the construction: the written-out block is what `VNestedOcc` computes -/

theorem mpAuxNodeB_built :
    mpOcc.ctor (mpAux mpAuxNodeB).header mpRestore mrNode = mpAuxNodeB := rfl

theorem mpAux_member_built :
    (mpAux mpAuxNodeB).types[1]? = some (mpOcc.member (mpAux mpAuxNodeB).header mpRestore) := rfl

/-! ## §2 The two coordinates that matter -/

/-- **The block is parameterised.**  This is the coordinate row 129b says no redex block in the
tree had. -/
theorem mpAuxB_np_one : (mpAux mpAuxNodeB).np = 1 := rfl

theorem mpAuxB_params : (mpAux mpAuxNodeB).params = [.sort (.succ .zero)] := rfl

/-- …so the `np = 0` route's very first hypothesis is **false** here. -/
theorem mpAuxB_params_ne_nil : (mpAux mpAuxNodeB).params ≠ [] := by decide

/-- **The block is a redex block**: the companion's recursive field is stored `.app`-headed at a
`.lam`, and a canonical recursive field never is (`MRedex.canonType_ne_of_lamHead`). -/
theorem mpAuxNodeB_not_canonical : ¬ mpAuxNodeB.Canonical (mpAux mpAuxNodeB) := by
  intro h
  exact absurd (h 1 _ _ rfl rfl) (by decide)

theorem mpAuxB_ctorsAll_eq :
    (mpAux mpAuxNodeB).ctorsAll = [(0, mpObj), (1, mpAuxNodeB)] := rfl

theorem mpAuxB_not_canonical : ¬ (mpAux mpAuxNodeB).Canonical := by
  intro h
  refine mpAuxNodeB_not_canonical (h 1 mpAuxNodeB ?_)
  rw [mpAuxB_ctorsAll_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-! ## §3 The side conditions, at the parameterised redex block

Everything §1 of `StoredIota.lean` discharges at `mrAux mrAuxNodeB`, discharged here — except the
two that are **false**, which are named as theorems rather than omitted. -/

theorem mpAuxB_blockNames : (mpAux mpAuxNodeB).blockNames = [``MP, mpNestedName] := rfl

theorem mpAuxB_blockNames_nodup : (mpAux mpAuxNodeB).blockNames.Nodup := by decide

theorem mpAuxB_allNames_nodup : (mpAux mpAuxNodeB).allNames.Nodup := by decide

/-- **`OwnId`.**  `MP` — the member the step declares — is renamed to nothing, re-levelled to
nothing, and re-instantiated at `bvars 0 1 = [#0]`, i.e. at its own parameter.  (At `np = 0` this
clause is `tyArgs 0 = []`; here it has content.) -/
theorem mpRestore_ownId : mpRestore.OwnId (mpAux mpAuxNodeB) mpK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mpAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mpAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mpAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mpAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mpAux] at hT

/-- **The presented spine is closed at `D.np`** — which is what §T16.1 (`hcl`) asks for, and it
holds. -/
theorem mpRestore_tyArgs_closedNp :
    ∀ j, ∀ a ∈ mpRestore.tyArgs j, a.ClosedN (mpAux mpAuxNodeB).np := by
  intro j a ha
  by_cases h : j = 1
  · rw [show mpRestore.tyArgs j
        = [.sort .zero, .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))] from
      by simp [mpRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · trivial
    · exact ⟨trivial, trivial, Nat.lt_succ_self 1⟩
  · rw [show mpRestore.tyArgs j = [.bvar 0] from by simp [mpRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact Nat.zero_lt_one

/-- **…and it is NOT closed at `0`, which is where the whole `np = 0` route lives.**  `hcl0` is a
hypothesis of `VIndRestore.substC_atRec_fieldTypes`, of `csubst_recType_eq` (obligation (B)) and of
`csubst_iotaRules_eq` (obligation (C)); it is refuted here, exactly as
`InductiveDeclExamples.ntree_not_tyArgs_closed0` refutes it at the parameterised *canonical*
witness.  So a parameterised block cannot use the strict-equation route, whether or not it stores a
redex. -/
theorem mp_not_tyArgs_closed0 :
    ¬ (∀ j, ∀ a ∈ mpRestore.tyArgs j, a.ClosedN 0) := by
  intro h
  have := (h 1 (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))) (by decide)).2.2
  simp [VExpr.ClosedN] at this

/-! ### `SubstFree`, field by field -/

theorem mp_substFree_tyName :
    ∀ j, mpRestore.csubst (mpAux mpAuxNodeB) mpK (mpRestore.tyName j) = none := by
  intro j; by_cases h : j = 1 <;> simp only [mpRestore, h] <;> rfl

theorem mp_substFree_tyArgs : ∀ j, ∀ a ∈ mpRestore.tyArgs j,
    a.NoCSubst (mpRestore.csubst (mpAux mpAuxNodeB) mpK) := by
  intro j a ha
  by_cases h : j = 1
  · rw [show mpRestore.tyArgs j
        = [.sort .zero, .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))] from
      by simp [mpRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · trivial
    · exact ⟨trivial, (rfl : mpRestore.csubst (mpAux mpAuxNodeB) mpK ``MP = none), trivial⟩
  · rw [show mpRestore.tyArgs j = [.bvar 0] from by simp [mpRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial

theorem mp_substFree_recName : ∀ j, mpRestore.csubst (mpAux mpAuxNodeB) mpK
    (mpRestore.recName (Lean.mkRecName ((mpAux mpAuxNodeB).types.getD j default).name))
      = none := by
  rintro (_ | _ | j)
  · rfl
  · rfl
  · exact (rfl : mpRestore.csubst (mpAux mpAuxNodeB) mpK
      (mpRestore.recName (Lean.mkRecName (default : VIndType).name)) = none)

theorem mp_substFree_ctorName : ∀ (j : Nat) (T : VIndType),
    (mpAux mpAuxNodeB).types[j]? = some T → ∀ C ∈ T.ctors,
      mpRestore.csubst (mpAux mpAuxNodeB) mpK (mpRestore.ctorName C.name) = none := by
  rintro (_ | _ | j) T hT C hC
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · simp [mpAux] at hT

theorem mpRestore_substFree :
    mpRestore.SubstFree (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) :=
  ⟨mp_substFree_tyName, mp_substFree_tyArgs, mp_substFree_recName, mp_substFree_ctorName⟩

theorem mpRestore_domNodup : mpRestore.DomNodup (mpAux mpAuxNodeB) mpK := by
  show ((mpRestore.csubstList (mpAux mpAuxNodeB) mpK).map (·.1)).Nodup
  show ([`_nested.MDep_1, `_nested.MDep_1.rec, `_nested.MDep_1.node] : List Name).Nodup
  decide

theorem mpRestore_domSep : mpRestore.DomSep (mpAux mpAuxNodeB) mpK :=
  VIndRestore.domSep_of_allNames_nodup mpAuxB_allNames_nodup mpRestore_domNodup

/-- The domain is the three auxiliary names, and it is not empty. -/
theorem mp_csubstList_dom :
    (mpRestore.csubstList (mpAux mpAuxNodeB) mpK).map (·.1)
      = [`_nested.MDep_1, `_nested.MDep_1.rec, `_nested.MDep_1.node] := rfl

/-- **`hpos`**, the index bound, at both constructors. -/
theorem mpAuxB_pos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ (mpAux mpAuxNodeB).ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < (mpAux mpAuxNodeB).nm ∧
        ∀ B ∈ r.binders, (mpAux mpAuxNodeB).NoBlock B := by
  intro t C h
  rw [mpAuxB_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · rintro (_ | i) F r hF hr
    · cases hF; cases hr; exact ⟨by decide, nofun⟩
    · simp [mpObj] at hF
  · rintro (_ | _ | i) F r hF hr
    · cases hF; exact absurd hr nofun
    · cases hF; cases hr; exact ⟨by decide, nofun⟩
    · simp [mpAuxNodeB] at hF

/-- **`CanonicalOwn` holds** while `Canonical` fails — the same split as at `MJ`: the redex lives
in the companion constructor, and the user's constructor is stored canonically (here at
`tyApp 1 0 [] = _nested.MDep_1 #0`, which is where the parameter enters). -/
theorem mpObj_canonical : mpObj.Canonical (mpAux mpAuxNodeB) := by
  rintro (_ | i) F r hF hr
  · cases hF; cases hr; rfl
  · simp [mpObj] at hF

theorem mpAuxB_canonicalOwn : (mpAux mpAuxNodeB).CanonicalOwn mpK := by
  intro j C h hK
  rw [mpAuxB_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · exact mpObj_canonical
  · exact absurd (by decide) hK

/-! ## §4 The measurement row 129b asked for: at `np = 1` the two sides of `hrec` DIFFER

Row 129b's finding was that `MRedex.MRWit.mr_obj_entry_substC_eq` holds — the two sides of
§T15.7's `hrec` at the companion-pointing field are the *same* `VExpr` after `σ`, so §T16.1 proves
a typing there.  The reason is `VIndRestore.substC_tyApp_comp`: a substituted companion head is
`(mkLams D.params (R.tyBody D j)).mkApp (bvars k D.np ++ args)`, which at `D.np = 0` has an empty
argument list and so *is* the restored head.

At `np = 1` the argument list is `[#0]`, so the substituted side is a **saturated one-fold
β-redex** whose contractum is the restored side (`VIndRestore.instAll_tyBody`).  Both sides are
computed below and the difference is `decide`d. -/

/-- The stored entry after `σ`: `(fun α : Type => MDep Prop (fun _ => MP α)) #0` — a β-redex,
because `substC` must substitute a *closed* term for the companion constant and the occurrence's
own parameter argument stays where it is. -/
theorem mp_obj_entry_stored :
    (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      = .app (.lam (.sort (.succ .zero))
          (.app (.app (.const ``MDep []) (.sort .zero))
            (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))) (.bvar 0) := rfl

/-- …and the restored entry after `σ` is exactly its contractum. -/
theorem mp_obj_entry_restored :
    (((mpAux mpAuxNodeB).atRec (mpRestore.restore (mpAux mpAuxNodeB) 0
        (mpObj.fields.getD 0 default).type)).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      = .app (.app (.const ``MDep []) (.sort .zero))
          (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))) := rfl

/-- **THE measurement.**  The two sides of §T15.7's `hrec` at the companion-pointing field are
**different expressions** at this block — contrast `MRedex.MRWit.mr_obj_entry_substC_eq`, which is
the same statement with `=` at `np = 0`.  So `hrec` here is a **genuine conversion**, and the
sharpest §T15.7 form (`substC_atRec_fieldTypes_defeq'`, whose premise is that the substituted
entries differ) has a **true** premise at this field rather than a false one. -/
theorem mp_obj_entry_substC_ne :
    (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      ≠ (((mpAux mpAuxNodeB).atRec (mpRestore.restore (mpAux mpAuxNodeB) 0
          (mpObj.fields.getD 0 default).type)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := by decide

/-- …and the difference is **exactly one β step**: the stored side's head contraction *is* the
restored side.  (`VIndRestore.instAll_tyBody` is the general statement — "the contractum of a
substituted companion head is the restored head, exactly"; this is it at this block, computed.) -/
theorem mp_obj_entry_betaHead :
    VExpr.betaHead (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      = (((mpAux mpAuxNodeB).atRec (mpRestore.restore (mpAux mpAuxNodeB) 0
          (mpObj.fields.getD 0 default).type)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := rfl

/-! ### The redex field is still free — row 127f's lesson does NOT depend on `np`

The restoration is the identity at the redex field here too, and for the same reason: the redex's
head is the block's **own** member, so it is companion-free and `VIndRestore.restore_noK` applies.
That is worth having at `np = 1` because it separates the two findings: row 127f (a redex field
carries no obligation) is `np`-independent, while row 129b (the *companion-pointing* field's
obligation is degenerate) was an artefact of `np = 0` alone. -/

/-- The redex field's stored type mentions no companion constant. -/
theorem mp_redex_noK : VExpr.NoConsts mpK mpRedex :=
  ⟨⟨trivial, show ``MP ∉ mpK from by decide, trivial⟩, trivial⟩

theorem mp_restore_redex_id :
    mpRestore.restore (mpAux mpAuxNodeB) 1 mpRedex = mpRedex :=
  VIndRestore.restore_noK mpRestore_ownId 1 mpRedex mp_redex_noK

example : mpRestore.restore (mpAux mpAuxNodeB) 1 mpRedex = mpRedex := by decide

/-- **The companion constructor's field telescope is unchanged** — `mr_auxFieldTypesR_eq_fields`
at `np = 1`. -/
theorem mp_auxFieldTypesR_eq_fields :
    mpAuxNodeB.fieldTypesR (mpAux mpAuxNodeB) mpRestore = mpAuxNodeB.fields.map (·.type) := by
  decide

/-- **…and the user constructor's field telescope moves**, as at `MJ` — but now the move survives
`σ` (`mp_obj_entry_substC_ne`), which is the new fact. -/
theorem mp_objFieldTypesR_ne_fields :
    mpObj.fieldTypesR (mpAux mpAuxNodeB) mpRestore ≠ mpObj.fields.map (·.type) := by decide

/-! ## §5 §T15.7's `hrec` at the companion-pointing field — PRODUCED, and as a conversion

`StoredIota.lean` §5.2 produced `hrec` at `MJ.obj` from §T16.1 and §5.5 then measured that the
conclusion was a typing.  The same route is run here.  Two differences, and both are the point:

* the field's context is no longer `[]` — it must carry the block's parameter, because §T16.1's
  `hbv` is a `bvars 0 D.np` spine and at `np = 1` that spine is `[#0]`.  At `np = 0` `hbv` was
  `HasArgs.nil`; here it is a real lookup;
* the conclusion is a **conversion** (`mp_obj_entry_substC_ne`), not a typing.

§5.2 below gives the same conversion directly as one `IsDefEq.beta`, which is what
`mp_obj_entry_beta` says it must be, and needs no `Ordered` environment. -/

theorem mp_MP_type_hasType {env : VEnv} :
    env.HasType 0 [] (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
      (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)

theorem mp_MP_constant_wf {env : VEnv} :
    VConstant.WF env ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  ⟨_, mp_MP_type_hasType⟩

/-- The restored presentation of the companion member, computed — `MDep Prop (fun _ => MP α)`
**over the parameter**, which is what makes it not closed. -/
theorem mp_atRec_tyBody_one :
    (mpAux mpAuxNodeB).atRec (mpRestore.tyBody (mpAux mpAuxNodeB) 1)
      = .app (.app (.const ``MDep []) (.sort .zero))
          (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))) := rfl

/-- **§T16.1's `hbody`** at this block: `MDep Prop (fun _ => MP α) : Type` in a context whose
head is the parameter. -/
theorem mp_tyBody_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    (hMDep : env.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
    (hMP : env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env.HasType U (.sort (.succ .zero) :: Γ)
      ((mpAux mpAuxNodeB).atRec (mpRestore.tyBody (mpAux mpAuxNodeB) 1))
      (.sort (.succ .zero)) := by
  rw [mp_atRec_tyBody_one]
  have h1 : env.HasType U (.sort (.succ .zero) :: Γ) (.const ``MDep [])
      (.forallE (.sort (.succ .zero))
        (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)))) :=
    .constDF hMDep nofun nofun rfl .nil
  have h2 : env.HasType U (.sort (.succ .zero) :: Γ) (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  have h3 : env.HasType U (.sort (.succ .zero) :: Γ)
      (.app (.const ``MDep []) (.sort .zero))
      (.forallE (.forallE (.sort .zero) (.sort (.succ .zero))) (.sort (.succ .zero))) :=
    .appDF h1 h2
  have hMPc : env.HasType U (.sort .zero :: .sort (.succ .zero) :: Γ) (.const ``MP [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constDF hMP nofun nofun rfl .nil
  have h4 : env.HasType U (.sort (.succ .zero) :: Γ)
      (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1)))
      (.forallE (.sort .zero) (.sort (.succ .zero))) :=
    .lamDF (.sortDF trivial trivial rfl) (.appDF hMPc (.bvar (.succ .zero)))
  exact .appDF h3 h4

/-- **§T16.1's `hbv`, which is empty at `np = 0` and a real lookup here**: the parameter spine
`bvars 0 1 = [#0]`, typed against the block's parameter telescope. -/
theorem mp_hbv {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasArgs U (.sort (.succ .zero) :: Γ) ((mpAux mpAuxNodeB).atRecTele
      (mpAux mpAuxNodeB).params) (VExpr.bvars 0 (mpAux mpAuxNodeB).np) :=
  .cons (.bvar .zero) .nil

/-- **§T15.7's `hrec`, produced at the companion-pointing field of a PARAMETERISED redex block**
— `StoredIota.lean` §5.2 one `np` up, and now a conversion rather than a typing
(`mp_obj_entry_substC_ne`).

The context must begin with the block's parameter; that is not a convenience of the statement but
what §T16.1's `hbv` forces at `np > 0`. -/
theorem mp_hrec_obj {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.Ordered) (hOn : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType U))
    (hMDep : env.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
    (hMP : env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    ∃ u, env.IsDefEq U (.sort (.succ .zero) :: Γ)
      (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      (((mpAux mpAuxNodeB).atRec
          (mpRestore.restore (mpAux mpAuxNodeB) 0 (mpObj.fields.getD 0 default).type)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) (.sort u) :=
  VIndRestore.substC_atRec_stored_defeq_of_canonical (r := ⟨[], 1, []⟩) (i := 0)
    mpAuxB_blockNames_nodup rfl nofun rfl
    (VIndRestore.substC_atRec_canonType_defeq (K := mpK) mpRestore_substFree
      mpRestore_domSep.substAt (mpRestore_tyArgs_closedNp 1) henv rfl (by decide)
      (As := []) (B' := .sort (.succ .zero)) (w := .succ .zero)
      hOn ⟨hOn, _, .sortDF trivial trivial rfl⟩ mp_hbv
      (mp_tyBody_hasType hMDep hMP) rfl .nil rfl)

/-! ### §5.2 The same conversion as one β step, with no `Ordered` environment

`mp_obj_entry_betaHead` says the conversion is a head β-contraction, so `IsDefEq.beta` gives it
directly.  This is the cheaper route (§T16.1 pays `henv`, `hOn` and the parameter spine); it is
recorded because the *comparison* is what row 129b's successor needs: at `np = 0` the analogous
statement is `IsDefEq.rfl`-shaped and carries nothing (`MRWit.mr_obj_entry_substC_eq`), while here
neither route is degenerate. -/
theorem mp_hrec_obj_beta {env : VEnv} {U : Nat} {Γ : List VExpr}
    (hMDep : env.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
    (hMP : env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    ∃ u, env.IsDefEq U (.sort (.succ .zero) :: Γ)
      (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      (((mpAux mpAuxNodeB).atRec
          (mpRestore.restore (mpAux mpAuxNodeB) 0 (mpObj.fields.getD 0 default).type)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) (.sort u) :=
  ⟨.succ .zero, .beta (mp_tyBody_hasType hMDep hMP) (.bvar .zero)⟩

/-! ### §5.3 The field telescopes, assembled at both constructors -/

/-- **The redex constructor's field telescope is free at `np = 1` too** — row 127f is
`np`-independent.  Every recursive field of `mpAuxNodeB` is companion-free, so
`substC_atRec_fieldTypes_defeq_of_noK`'s `hrec` has a false premise. -/
theorem mp_hrec_nodeB_vacuous (i : Nat) (F : VIndField) (r : VIndRecArg)
    (hF : mpAuxNodeB.fields[i]? = some F) (hr : F.recArg = some r)
    (hnc : ¬ VExpr.NoConsts mpK F.type) : False := by
  rcases i with _ | _ | i
  · cases hF; exact absurd hr nofun
  · cases hF; exact hnc mp_redex_noK
  · simp [mpAuxNodeB] at hF

theorem mp_teleDefEq_fld_stored {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.TeleDefEq U Γ
      (((mpAux mpAuxNodeB).atRecTele (mpAuxNodeB.fields.map (·.type))).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)))
      (((mpAux mpAuxNodeB).atRecTele
          (mpAuxNodeB.fieldTypesR (mpAux mpAuxNodeB) mpRestore)).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))) :=
  VIndRestore.substC_atRec_fieldTypes_defeq_of_noK mpRestore_ownId
    (fun i F r hF hr hnc => absurd (mp_hrec_nodeB_vacuous i F r hF hr hnc) not_false)

/-- The user constructor's field really does point at a companion, so §5.3's escape is
unavailable at it. -/
theorem mp_objField_not_noK : ¬ VExpr.NoConsts mpK (mpObj.fields.getD 0 default).type :=
  fun h => h.1 (show mpNestedName ∈ mpK from by decide)

/-- **§T15.7's field telescope at `MP.obj`, assembled from a genuine conversion.**

This is the statement row 129b said this tree could not have: the `TeleDefEq` is built by
`VEnv.TeleDefEq.cons` at an entry that actually *moves* under `σ` (`mp_obj_entry_substC_ne`), so
`VEnv.TeleDefEq.of_entries'` takes its right disjunct rather than its left.  Compare
`MRWit.mr_teleDefEq_fld_obj_free`, which is the same conclusion at `np = 0` obtained with the
*empty* obligation. -/
theorem mp_teleDefEq_fld_obj {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.Ordered) (hOn : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType U))
    (hMDep : env.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
    (hMP : env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env.TeleDefEq U (.sort (.succ .zero) :: Γ)
      (((mpAux mpAuxNodeB).atRecTele (mpObj.fields.map (·.type))).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)))
      (((mpAux mpAuxNodeB).atRecTele (mpObj.fieldTypesR (mpAux mpAuxNodeB) mpRestore)).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))) :=
  VIndRestore.substC_atRec_fieldTypes_defeq' (by
    rintro (_ | i) F r hF hr hne
    · cases hF; exact mp_hrec_obj henv hOn hMDep hMP
    · simp [mpObj] at hF)

/-! ### §5.4 A closed witness: the environment premises are satisfiable

Same construction as `MRWit.mr_env_exists`, with `MDep` reused verbatim (`mr_MDep_constant_wf`)
and `MP` in place of `MJ`. -/

theorem mp_env_exists : ∃ env : VEnv, env.Ordered ∧
    env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ ∧
    env.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := ``MP)
    (ci := ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hMP : e1.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ := by
    rw [c1]; exact if_pos rfl
  have ho1 : e1.Ordered := .const .empty mp_MP_constant_wf he1
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := ``MDep)
    (ci := ⟨0, MRWit.mrDepType.type⟩) (by rw [c1]; exact if_neg (by decide))
  have c2 := VEnv.addConst_constants_eq he2
  refine ⟨e2, .const ho1 MRWit.mr_MDep_constant_wf he2, ?_, by rw [c2]; exact if_pos rfl⟩
  rw [c2]
  exact (if_neg (show ¬ ((``MDep : Name) = ``MP) from by decide)).trans hMP

/-- **§5.1's conclusion with every premise discharged**, in a concrete `Ordered` environment, at
the smallest context §T16.1 admits here — the block's parameter alone. -/
theorem mp_hrec_obj_closed : ∃ (env : VEnv) (u : VLevel), env.Ordered ∧
    env.IsDefEq 0 [.sort (.succ .zero)]
      (((mpAux mpAuxNodeB).atRec (mpObj.fields.getD 0 default).type).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      (((mpAux mpAuxNodeB).atRec
          (mpRestore.restore (mpAux mpAuxNodeB) 0 (mpObj.fields.getD 0 default).type)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) (.sort u) := by
  obtain ⟨env, henv, hMP, hMDep⟩ := mp_env_exists
  obtain ⟨u, hu⟩ := mp_hrec_obj (U := 0) (Γ := []) henv
    ⟨trivial, _, .sortDF trivial trivial rfl⟩ hMDep hMP
  exact ⟨env, u, henv, hu⟩

/-! ## §6 What does NOT go through, and it is not merely unavailable — it is FALSE

`StoredIota.lean` §2 instantiated four more things at `mrAux mrAuxNodeB`: the strict
field-telescope equation `VIndRestore.substC_atRec_fieldTypes`, obligation (B)
(`csubst_recType_eq`), obligation (C) (`csubst_iotaRules_eq`), and the two `TeleDefEq`
certificates `teleDefEq_fld_of_np_zero` / `iotaCtx_teleDefEq_of_np_zero`.  **All five carry
`hp : D.params = []`**, which is false here (`mpAuxB_params_ne_nil`), and four of them also carry
`hcl0`, which is false here too (`mp_not_tyArgs_closed0`).

That much is bookkeeping.  The measurement worth having is that their **conclusions** are false at
this block, so the hypotheses are load-bearing rather than conservative — and so the `np = 0` route
is not "unavailable pending work" but *inapplicable in principle* above `np = 0`. -/

/-- **The strict field-telescope equation is FALSE at a parameterised block.**
`VIndRestore.substC_atRec_fieldTypes`'s conclusion, at `MP.obj`: refuted, because the substituted
entry is a β-redex and its restoration is the contractum (`mp_obj_entry_substC_ne`).  So `hp`/`hcl0`
are doing real work in §7.5, and the `TeleDefEq` of §T15.7 is the *only* form available here. -/
theorem mp_fieldTypes_bridge_obj_false :
    ((mpAux mpAuxNodeB).atRecTele (mpObj.fields.map (·.type))).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      ≠ ((mpAux mpAuxNodeB).atRecTele (mpObj.fieldTypesR (mpAux mpAuxNodeB) mpRestore)).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := by decide

/-- **Obligation (B)'s strict form is FALSE at a parameterised block** — `csubst_recType_eq`'s
conclusion at the user's member.  (B) therefore has to be reached through §T15.3's
`VEnv.recConstsR_wf_of_blocks`, which is stated over *telescope defeqs* and carries no `np` bound,
and whose remaining input is `hargs`. -/
theorem mp_recTypeR_bridge_false :
    ((mpAux mpAuxNodeB).recType 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      ≠ ((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK) := by decide

/-- **Obligation (C)'s strict form is FALSE too** — `csubst_iotaRules_eq`'s conclusion, compared on
the rules' `type` components (`VDefEq` has no `DecidableEq`, as ledger row 129's §7 records). -/
theorem mp_iotaRules_bridge_false :
    ((mpAux mpAuxNodeB).iotaRules.map
        (·.substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).map VDefEq.type
      ≠ ((mpAux mpAuxNodeB).iotaRulesRS mpRestore mpK).map VDefEq.type := by decide

/-- Sanity: the (C) comparison above is **not** a length artefact — the two rule lists have the
same length, so `mp_iotaRules_bridge_false` is a per-rule difference. -/
theorem mp_iotaRules_length_eq :
    ((mpAux mpAuxNodeB).iotaRules.map
        (·.substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).length
      = ((mpAux mpAuxNodeB).iotaRulesRS mpRestore mpK).length := rfl

/-! ## §7 …and the one residual §8.6 says cannot be derived — SUPPLIED here

`NestedRules.lean` §8.6 reduces `(R.csubst D K).WF E₂ e₂ U` — the shared hypothesis of obligations
(B) and (C) — to its `val` clause, and `VIndRestore.tyVal_hasType_of_faithful` reduces the
companion half of `val` to `hsplit` + `hargs`.  `VIndRestore.instAt_indep_of_tyArgs` then shows
**`Faithful` cannot supply `hargs`**, because `instAt` does not read the presented spine when the
head's type body is closed after splitting.

`MDep`'s body after splitting its two parameters is `Sort 1` — **closed** — so this block is
exactly the configuration that docstring names, and `hargs` here is genuinely data.  It is data
this witness can produce, which is the useful half: the residual at a parameterised nested block is
*not* unreachable, only not derivable from `Faithful`. -/

/-- `hsplit` at the companion member: `MDep`'s stored type really has two leading binders. -/
theorem mp_hsplit :
    MRWit.mrDepType.type.instL (mpRestore.tyLvls 1)
      = VExpr.mkPi (VExpr.splitPis 2 (MRWit.mrDepType.type.instL (mpRestore.tyLvls 1))).1
          (VExpr.splitPis 2 (MRWit.mrDepType.type.instL (mpRestore.tyLvls 1))).2 := rfl

/-- **…and the body after the split is CLOSED**, which is precisely the hypothesis of
`VIndRestore.instAt_indep_of_tyArgs` — so at this block `instAt` is blind to the presented spine
and `hargs` cannot come from `Faithful`. -/
theorem mp_split_body_closed :
    (VExpr.splitPis 2 (MRWit.mrDepType.type.instL (mpRestore.tyLvls 1))).2.ClosedN 0 := trivial

/-- **`hargs` at the companion member, supplied.**  The presented spine `[Prop, fun _ => MP α]` is
well typed against `MDep`'s parameter telescope over the block's own parameters — and the second
entry *mentions the parameter*, which is what makes this a statement about a parameterised block
rather than about a closed spine. -/
theorem mp_hargs {env : VEnv}
    (hMP : env.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env.HasArgs (mpAux mpAuxNodeB).uvars (mpAux mpAuxNodeB).params.reverse
      (VExpr.splitPis 2 (MRWit.mrDepType.type.instL (mpRestore.tyLvls 1))).1
      (mpRestore.tyArgs 1) :=
  have hMPc : env.HasType 0 [.sort .zero, .sort (.succ .zero)] (.const ``MP [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constDF hMP nofun nofun rfl .nil
  .cons (.sortDF trivial trivial rfl)
    (.cons (.lamDF (.sortDF trivial trivial rfl)
      (.appDF hMPc (.bvar (.succ .zero)))) .nil)

/-! ## §8 Plainly: does §T15's assembly go through at a parameterised redex block?

**Yes for the layer this round targeted, no for obligations (B)/(C), and the boundary is sharp.**

| item | at `mrAux mrAuxNodeB` (`np = 0`) | at `mpAux mpAuxNodeB` (`np = 1`) |
|---|---|---|
| §T15.7 `hfld` at the redex ctor | free (`mr_teleDefEq_fld_stored`) | free (`mp_teleDefEq_fld_stored`) — row 127f is `np`-independent |
| §T15.7 `hfld` at the companion-pointing field | free after `σ` (`mr_teleDefEq_fld_obj_free`) | **a genuine conversion** (`mp_teleDefEq_fld_obj`, premise `mp_obj_entry_substC_ne`) |
| §T16.1 `substC_atRec_canonType_defeq` | premises trivial, conclusion a typing | premises discharged (`mp_hrec_obj`), conclusion a **conversion** |
| `hbv` (the parameter spine) | `HasArgs.nil` | a real lookup (`mp_hbv`) |
| §7.5's strict `substC_atRec_fieldTypes` | holds (`mr_fieldTypes_bridge_obj`) | **FALSE** (`mp_fieldTypes_bridge_obj_false`) |
| obligation (B), `np = 0` form | holds (`mr_recTypeR_bridge`) | **FALSE** (`mp_recTypeR_bridge_false`) |
| obligation (C), `np = 0` form | holds (`mr_iotaRules_bridge`) | **FALSE** (`mp_iotaRules_bridge_false`) |
| `hargs` for the `val` clause | vacuous at `np = 0` | **supplied** (`mp_hargs`), and provably not derivable from `Faithful` here (`mp_split_body_closed`) |

**Where it stops, named.**  (B) and (C) at `np > 0` must be reached through
`VEnv.recConstsR_wf_of_entries` / `VEnv.iotaRulesRS_wf_of_components`, which carry no `np` bound.
Their inputs, *read off their signatures*, are (i) `hsrc`/`hσ`/`he₂` — a **staged environment pair**
with `(R.csubst D K).WF E₂ e₂ D.recUvars`, which `NestedRules.lean` §8.6's `csubst_WF` reduces to
five staging successes plus obligation (A)'s bridge plus the `val` clause; (ii) the motive and minor
entry defeqs `hmot`/`hmin` (§T5/§T6), of which `hmin`'s `hfld` is the item this file closes; and
(iii) `hbody`, a head defeq under the recursor telescope.

**Where that leaves things, stated carefully because the obvious version of this sentence is
false.**  A full `(R.csubst D K).WF E₂ e₂` witness **does** exist in the tree —
`Theory/Typing/ConstSubstNested.lean`'s `nfnSubstAll_WF₂` / `nfnSubstAll_WF₃`, identified with the
general substitution by `nfn_csubst`, with `nfnAux_recConstsR_wf` instantiating obligation (B) off
it.  But `nfnAux` has `np = 0` (*read off* `NestedBuild.lean`), and §6 above shows the `np = 0`
route's conclusions are **false** above `np = 0`.  So the accurate statement is: **(B) and (C) have
an instance at a parameterless block and none at any parameterised block**, and what this file does
not do is instantiate the `nfnSubstAll_WF` template here.  The residual is a template instantiation
at `np = 1`, not new apparatus — a *smaller* residual than "an environment nobody has built", and
the difference is worth the extra sentence.
-/

/-! ## §9 A correction to row 129b, measured: the conversion needs `np > 0` ALONE

Row 129b (and the brief that quoted it) says:

> `hrec` is a genuine conversion only at a block that is **both** a redex block **and**
> parameterised, and this tree contains no such block.

The second clause was true and is now false (§1–§5).  **The first clause over-conjoins**, and the
tell was three lines away.  What makes the two sides of `hrec` differ is `VIndRestore.substC_tyApp_comp`
— a substituted companion head is `(mkLams D.params (R.tyBody D j)).mkApp (bvars k D.np ++ args)` —
and *redex-ness plays no part in it*.  At `np = 0` the argument list is empty and the two sides
coincide; at `np > 0` they differ, redex block or not.

So the tree already held a witness for the **conversion** half: `InductiveDeclExamples.ntreeAux`,
which is parameterised (`np = 1`, `uvars = 1`) and `ntreeAux_Canonical` — i.e. explicitly *not* a
redex block.  Measured below.  Row 129b's "there is no proof to find until [a parameterised redex
block] exists" is therefore wrong twice: the conversion could have been exhibited at `ntreeAux`
immediately, and §T16.1's producer runs there for the same reason it runs here.

**What the new block is actually for**, stated so the next round does not over-claim it either: it
is the first block in the tree that is *simultaneously* a redex block — so `hcanon` is **false**
there and ruling 122e's deletion has content — **and** parameterised — so §T15.7's obligation is a
conversion.  It is a *joint* witness, not the only witness of either half. -/

/-- **The conversion is available at a parameterised CANONICAL block too.**  Same statement as
`mp_obj_entry_substC_ne`, at `ntreeAux`'s companion-pointing field — a block that stores no redex.
So "redex block" was never a precondition of the conversion. -/
theorem ntree_obj_entry_substC_ne :
    ((InductiveDeclExamples.ntreeAux.atRec
        (InductiveDeclExamples.ntreeNode.fields.getD 1 default).type).substC
      (InductiveDeclExamples.ntreeRestore.csubst InductiveDeclExamples.ntreeAux
        InductiveDeclExamples.ntreeK))
      ≠ ((InductiveDeclExamples.ntreeAux.atRec
          (InductiveDeclExamples.ntreeRestore.restore InductiveDeclExamples.ntreeAux 1
            (InductiveDeclExamples.ntreeNode.fields.getD 1 default).type)).substC
        (InductiveDeclExamples.ntreeRestore.csubst InductiveDeclExamples.ntreeAux
          InductiveDeclExamples.ntreeK)) := by decide

/-- …and `ntreeAux` is not a redex block, which is the other half of the correction (quoted, not
re-proved: `InductiveDeclExamples.ntreeAux_Canonical`). -/
theorem ntree_canonical_and_parameterised :
    InductiveDeclExamples.ntreeAux.Canonical ∧ InductiveDeclExamples.ntreeAux.np = 1 :=
  ⟨InductiveDeclExamples.ntreeAux_Canonical, rfl⟩

end MPWit
end MRedex
end Lean4Lean
