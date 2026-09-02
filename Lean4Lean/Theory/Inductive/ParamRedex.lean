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

/-! ## §10 Where the assembly *really* stops: `hσ`'s `const` clause is FALSE, not unproved

§8 above, and `docs/handoff-iota-stored.md` §21/§25 and ledger row 132b, say the residual of
obligations (B)/(C) at a parameterised block is *"instantiating the `nfnSubstAll_WF₂` template at
`np = 1`, not new apparatus"*.  **That is wrong, and the correction is a refutation.**

`Theory/Typing/ConstSubstNested.lean` §B proves `VEnv.csubst_WF_staged_false`: at the staging pair
`E₂ = E₁.addIndCtors D`, `F₂ = F₁.addConstList (D.ctorConstsCR R K)` — the pair
`VEnv.addInductR_ordered'` fixes — **no** constant substitution leaving the declared
constructors alone is `CSubst.WF`, as soon as one declared constructor satisfies

    (C.type D j).substC σ ≠ (C.typeR D R j).substC (R.csubstTy D K)

because `CSubst.WF.const` at that constructor *is* that equation.  It is the syntactic bridge
`VEnv.ctorConstsCR_wf_of_substC` asks for as `hbridge` — the one `ctorConstsCR_wf_of_substC'`
exists to avoid — re-imposed through `hσ`.  It is refuted at `ntreeAux`
(`ntree_const_clause_ne`, `ntree_node_no_substC`), and it is refuted here too, which is what
this section records: the obstruction is not an artefact of the canonical witness.

The comparison below is against **Lean's own declared type for `MP.obj`**, which
`mp_obj_declared` identifies with `(mpObj.typeR …).substC (mpRestore.csubstTy …)`.  So what
`hσ`'s `const` clause demands of the environment at this block is *not* what Lean's kernel
declares — one β-step off it, exactly as `mp_obj_entry_substC_ne` measures one layer in. -/

/-- **`hσ`'s `const` clause is false at this block too.**  `hne` of
`VEnv.csubst_WF_staged_false`, verified at `MP.obj` — and against `type_of% @MP.obj`, i.e.
against what the environment really holds. -/
theorem mp_const_clause_ne :
    (mpObj.type (mpAux mpAuxNodeB) 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      ≠ (vconst(type_of% @MP.obj)).type := by decide

/-- …and the remaining hypotheses of `VEnv.csubst_WF_staged_false` hold at `MP.obj`, so the
refutation applies here verbatim once a staging pair for this block exists.  (It does not yet:
`mpAux mpAuxNodeB` has no `VInductDecl'.WF`, which is why the instance is stated at `ntreeAux`,
where `listDecl_WF` supplies the history.) -/
theorem mp_ctorName_id : mpRestore.ctorName ``MP.obj = ``MP.obj := rfl

theorem mp_own_not_K : ((mpAux mpAuxNodeB).types.getD 0 default).name ∉ mpK := by decide

theorem mp_csubst_obj_none : mpRestore.csubst (mpAux mpAuxNodeB) mpK ``MP.obj = none := rfl

theorem mp_obj_mem : (0, mpObj) ∈ (mpAux mpAuxNodeB).ctorsAll := by
  rw [mpAuxB_ctorsAll_eq]; exact List.Mem.head _


/-! ## §11 `VInductDecl'.WF` at the parameterised redex block — SUPPLIED

§10 above records, and `docs/handoff-iota-stored.md` §33.8/§40 and ledger row 141d repeat, that
`mpAux mpAuxNodeB` **has no `VInductDecl'.WF`**, and that this — not more substitution machinery —
is what obligations (B)/(C) need at this block.  This section supplies it.

Two things make it possible where the reader of §10 might expect it to fail:

* `VInductDecl'.WF` **does not require the block to be `Canonical`**.  Its positivity clause asks
  for `env.IsDefEqType D.uvars Γ F.type (r.canonType D i)` — a *definitional* equation — so a
  stored redex is admissible provided it contracts to the canonical application.  At this block
  the contraction is exactly one β step (`mp_redex_pos_defeq`), and that step **is** the block's
  distinguishing content: `mp_redex_ne_canonType` (`decide`) shows the two sides are different
  expressions, so this clause is a genuine conversion and not an identity.
* the constructor clause is staged over `env.addIndTypes D`, which declares both `MP` and
  `_nested.MDep_1`, so no history environment is needed: the block is well formed over **any**
  `env` (`mpAuxB_WF`), unlike `ntreeAux` whose restoration story needs `listDecl`.
-/

section
variable {env : VEnv}

theorem mpAuxB_params_WF :
    OnCtx (mpAux mpAuxNodeB).params.reverse (env.IsType (mpAux mpAuxNodeB).uvars) :=
  ⟨trivial, _, .sort (by decide)⟩

/-- The block's own type constant, in the staged environment the constructor clause is
stated over. -/
theorem mp_const_staged {env₂ : VEnv} (hs : env.addIndTypes (mpAux mpAuxNodeB) = some env₂) :
    env₂.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  VEnv.addConstList_constants hs
    (``MP, ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (by exact List.Mem.head _)

/-- …and the auxiliary companion member's. -/
theorem mpNested_const_staged {env₂ : VEnv}
    (hs : env.addIndTypes (mpAux mpAuxNodeB) = some env₂) :
    env₂.constants mpNestedName
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  VEnv.addConstList_constants hs
    (mpNestedName, ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

/-- **The redex field's stored type is NOT its canonical type** — so the positivity clause at
this field is a conversion, not an identity.  (Compare `mp_obj_entry_substC_ne`, which is the
same phenomenon one layer out, at `hrec`.) -/
theorem mp_redex_ne_canonType :
    mpRedex ≠ ({ binders := [], idx := 0, args := [] } : VIndRecArg).canonType
      (mpAux mpAuxNodeB) 1 := by decide

/-- **…and it contracts to it in exactly one β step.**  This is the whole content of
`VInductDecl'.WF` at the parameterised redex block. -/
theorem mp_redex_pos_defeq {env₂ : VEnv}
    (ht : env₂.constants ``MP
      = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) :
    env₂.IsDefEqType (mpAux mpAuxNodeB).uvars [.sort .zero, .sort (.succ .zero)] mpRedex
      (({ binders := [], idx := 0, args := [] } : VIndRecArg).canonType
        (mpAux mpAuxNodeB) 1) := by
  refine ⟨.succ .zero, ?_⟩
  exact VEnv.IsDefEq.beta (A := .sort .zero) (B := .sort (.succ .zero))
    (e := .app (.const ``MP []) (.bvar 2)) (e' := .bvar 0) (by type_tac) (by type_tac)

omit env in
theorem mp_binders_indep {pre : List VIndField} {i : Nat} {r : VIndRecArg}
    (hr : r.binders = []) : r.BindersIndep pre i := by
  intro i' t F' hF' hs he k B hB
  rw [hr] at hB
  simp at hB

/-- **`VInductDecl'.WF` at the parameterised redex block `mpAux mpAuxNodeB`**, over an
arbitrary environment. -/
theorem mpAuxB_WF : (mpAux mpAuxNodeB).WF env where
  types_ne := by simp [mpAux]
  params := mpAuxB_params_WF
  types := by
    intro T hT
    simp only [mpAux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := mpAuxB_params_WF, isType := ⟨_, by type_tac⟩,
              canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₂ hs j T hT C hC
    have ht := mp_const_staged hs
    have hf := mpNested_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [mpAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [mpObj, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mpAux, Lean.Nat.imax]
                binders_indep := fun r hr => by cases hr; exact mp_binders_indep rfl
                pos := ⟨by decide, rfl, nofun, nofun, mpAuxB_params_WF, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | (_ + 1), hF => simp [mpObj] at hF
    | 1, hT =>
      simp only [mpAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [mpAuxNodeB, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mpAux, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, by type_tac⟩ }
      | 1, hF =>
        simp only [mpAuxNodeB, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mpAux, Lean.Nat.imax]
                binders_indep := fun r hr => by cases hr; exact mp_binders_indep rfl
                pos := ⟨by decide, rfl, nofun, nofun,
                        ⟨mpAuxB_params_WF, _, by type_tac⟩, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, mp_redex_pos_defeq ht⟩ }
      | (_ + 2), hF => simp [mpAuxNodeB] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, mpAux])

end


/-! ## §12 The history block, and `hsrc` — the input §33.8 named as (B)'s blocker at `MP`

`docs/handoff-iota-stored.md` §33.8 and ledger row 141d both say: *(B) at `MP` dies on `hsrc`
(`∀ c ∈ D.recConsts, VConstant.WF E₂ c.2`), which `ntree_recConsts_wf` gets from
`VInductDecl'.recType_isType` off `D.RecCtx E₂`, and `RecCtx` comes from `VInductDecl'.WF` —
absent here.*  §11 supplies the `WF`; this section cashes it in.

`MP` nests through `MRWit.MDep`, so the history environment is `MDep`'s own block. -/

/-- **`MDep`'s block is well formed** — the history of the `MP` step, the counterpart of
`listDecl_WF` for `NTree`/`List`.  (It belongs beside `mrDepDecl` in `MemberRedex.lean`; it is
here so that the file `MemberRedexScan` reads is not disturbed.) -/
theorem mrDepDecl_WF : mrDepDecl.WF VEnv.empty where
  types_ne := by simp [mrDepDecl]
  params := ⟨⟨trivial, _, .sort (by decide)⟩, _, by type_tac⟩
  types := by
    intro T hT
    simp only [mrDepDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := ⟨⟨trivial, _, .sort (by decide)⟩, _, by type_tac⟩,
            isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₂ hs j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [mrDepDecl] at hT
      cases hT
      simp only [MRWit.mrDepType, List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have ht : env₂.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ :=
        VEnv.addConstList_constants hs (``MDep, ⟨0, MRWit.mrDepType.type⟩) (by exact List.Mem.head _)
      refine { params_len := rfl,
               params_eq := .succ (.succ .zero (by type_tac)) (by type_tac),
               fields := ?_, args_len := rfl, args_fresh := nofun, args_ty := .nil,
               result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [mrNode, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mrDepDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.bvar 1, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, by type_tac⟩ }
      | 1, hF =>
        simp only [mrNode, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mrDepDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.app (.bvar 1) (.bvar 0),
                        by simp [VInductDecl'.NoBlock, VExpr.NoConsts], _, by type_tac⟩ }
      | (_ + 2), hF => simp [mrNode] at hF
    | (_ + 1), hT => simp [mrDepDecl] at hT
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, mrDepDecl])

/-- …hence the history environment of the `MP` step really is `Ordered`. -/
theorem mpEnv_ordered {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    env₁.Ordered :=
  VInductDecl'.addInduct'_ordered_final .empty mrDepDecl_WF h

/-! ### §12.1 The four staging environments exist -/

theorem mp_fresh' {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (n : Name) (hn : n ∈ [``MP, mpNestedName, ``MP.obj, `_nested.MDep_1.node]) :
    env₁.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem mpAuxB_stagedE₁ {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    ∃ E₁, env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ :=
  VEnv.addConstList_eq_some_iff.2
    ⟨fun n hn => mp_fresh' h n (by revert hn; revert n; decide), by decide⟩

theorem mpAuxB_stagedF₁ {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    ∃ F₁, env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ :=
  VEnv.addConstList_eq_some_iff.2
    ⟨fun n hn => mp_fresh' h n (by revert hn; revert n; decide), by decide⟩

/-! ### §12.2 `hsrc` at the parameterised redex block -/

section
variable {env₁ E₁ E₂ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)

include h hE₁ hE₂ in
/-- **`hsrc` at `MP`.**  This is `ntree_recConsts_wf`'s proof verbatim at the *redex* block; the
only input it lacked was §11's `mpAuxB_WF`, and nothing about redex-ness enters. -/
theorem mp_recConsts_wf : ∀ c ∈ (mpAux mpAuxNodeB).recConsts, VConstant.WF E₂ c.2 := by
  intro c hc
  have henv₁ := mpEnv_ordered h
  have o1 := VInductDecl'.addIndTypes_ordered henv₁ mpAuxB_WF hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 mpAuxB_WF hE₁ hE₂
  have hR : (mpAux mpAuxNodeB).RecCtx E₂ := mpAuxB_WF.recCtx hE₁ hE₂ VEnv.LE.rfl o2
  simp only [VInductDecl'.recConsts, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : (mpAux mpAuxNodeB).types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < (mpAux mpAuxNodeB).nm := by
    rcases Nat.lt_or_ge j (mpAux mpAuxNodeB).types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  exact VInductDecl'.recType_isType hR hT hj (VInductDecl'.onCtxMinors hR)

end

/-! ## §13 Obligation (A) at the parameterised redex block

With §11's `WF` in hand this is `ntreeAux_ctorConstsCR_wf`'s proof at `MP`: obligation (A) through
`VEnv.ctorConstsCR_wf_of_substC'`, whose block-specific input is **one `IsDefEq.beta`** — the same
contraction §11 used for positivity, now at the constructor's field type.  Its value is that it
supplies `F₂.Ordered`, i.e. `he₂`, one of (B)'s three environment inputs. -/

/-- The value the restoration presents the companion member as: `λ α, MDep Prop (λ _, MP α)`.
At `np = 1` this is a **lambda**, which is what makes every occurrence a redex after substitution. -/
def mpVal : VExpr := .lam (.sort (.succ .zero))
  (.app (.app (.const ``MDep []) (.sort .zero))
    (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))

/-- …and the constructor value, the second lambda `csubst` carries. -/
def mpValNode : VExpr := .lam (.sort (.succ .zero))
  (.app (.app (.const ``MDep.node []) (.sort .zero))
    (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))

def mpSubst : CSubst := CSubst.one mpNestedName mpVal

theorem mpSubst_of_ne {n : Name} (h : n ≠ mpNestedName) : mpSubst n = none := CSubst.one_of_ne h

/-- **The general type-entry substitution at `MP` is `mpSubst`** — `VIndRestore.tyVal`'s
`mkLams` is the lambda. -/
theorem mp_csubstTy_eq : mpRestore.csubstTy (mpAux mpAuxNodeB) mpK = mpSubst := by
  funext n
  show List.lookup n [(mpNestedName, mpVal)] = _
  rw [List.lookup_cons]
  by_cases hn : n = mpNestedName
  · subst hn; rfl
  · rw [show (n == mpNestedName) = false from beq_eq_false_iff_ne.2 hn]
    exact (CSubst.one_of_ne hn).symm

theorem mp_csubst_ty_val :
    mpRestore.csubstTy (mpAux mpAuxNodeB) mpK mpNestedName = some mpVal := rfl

theorem mp_csubst_val :
    mpRestore.csubst (mpAux mpAuxNodeB) mpK mpNestedName = some mpVal := rfl

theorem mp_csubst_node_val :
    mpRestore.csubst (mpAux mpAuxNodeB) mpK `_nested.MDep_1.node = some mpValNode := rfl

theorem mp_csubst_rec_val :
    mpRestore.csubst (mpAux mpAuxNodeB) mpK `_nested.MDep_1.rec
      = some (.const ``MP.rec_1 [.param 0]) := rfl

theorem mpSubst_fresh {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    mpSubst.FreshIn env₁ := by
  intro c ci hc
  cases hn : mpSubst c with
  | none => rfl
  | some t =>
    have hce : c = mpNestedName := by
      by_cases he : c = mpNestedName
      · exact he
      · rw [mpSubst_of_ne he] at hn; exact absurd hn nofun
    subst hce
    rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
    exact absurd hc nofun

/-! ### §13.1 The two values of the substitution, over any environment holding
`MDep`, `MDep.node` and `MP`

Both are stated at the **concrete** universe counts the two consumers use — `0` for the `val`
clause (`ci.uvars = D.uvars = 0`) and `1` for the `const` clause (`D.recUvars = 1`).  A variable
`U` is not usable here: `type_tac` discharges `VLevel.WF U l` by `decide`, which needs `U`
closed. -/

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)

include hD hP in
theorem mpVal_hasTypeF : F.HasType 0 [] mpVal
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by type_tac

include hNd hP hD in
/-- **The `val` clause at the companion CONSTRUCTOR**, at the type the substitution produces —
which is `mpValNode`'s natural type with **one β step** at the result.  The `defeqDF` is that
step; everything else is `forallEDF` bookkeeping. -/
theorem mpValNode_hasTypeF : F.HasType 0 [] mpValNode
    ((mpAuxNodeB.type (mpAux mpAuxNodeB) 1).substC
      (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := by
  show F.HasType 0 [] mpValNode
    (.forallE (.sort (.succ .zero)) (.forallE (.sort .zero)
      (.forallE mpRedex (.app mpVal (.bvar 2)))))
  have hval : F.HasType 0 [] mpValNode
      (.forallE (.sort (.succ .zero)) (.forallE (.sort .zero)
        (.forallE mpRedex
          (.app (.app (.const ``MDep []) (.sort .zero))
            (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 3))))))) := by type_tac
  have hr : F.IsDefEq 0 [mpRedex, .sort .zero, .sort (.succ .zero)]
      (.app (.app (.const ``MDep []) (.sort .zero))
        (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 3))))
      (.app mpVal (.bvar 2)) (.sort (.succ .zero)) := by
    refine .symm (VEnv.IsDefEq.beta (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
      ?_ ?_) <;> type_tac
  exact .defeqDF (.forallEDF (.sortDF (l := .succ .zero) (l' := .succ .zero)
    (by decide) (by decide) rfl)
      (.forallEDF (.sortDF (l := .zero) (l' := .zero) (by decide) (by decide) rfl)
        (.forallEDF (show F.HasType 0 [.sort .zero, .sort (.succ .zero)] mpRedex
          (.sort (.succ .zero)) by type_tac) hr))) hval

include hD hP in
/-- **The datum `CSubst.WFD`'s `const` clause asks for and `CSubst.WF` cannot have**, at `MP.obj`:
the type `ctorConstsCR` declares and the type the substitution produces are definitionally equal
by **one β step** under one `forallEDF`.  §10's `mp_const_clause_ne` shows they are never *equal*. -/
theorem mp_obj_const_defeq :
    ∃ v, F.IsDefEq 1 []
      ((mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
        (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK))
      ((mpObj.type (mpAux mpAuxNodeB) 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) (.sort v) := by
  show ∃ v, F.IsDefEq 1 []
    (.forallE (.sort (.succ .zero))
      (.forallE (.app (.app (.const ``MDep []) (.sort .zero))
        (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))
        (.app (.const ``MP []) (.bvar 1))))
    (.forallE (.sort (.succ .zero))
      (.forallE (.app mpVal (.bvar 0)) (.app (.const ``MP []) (.bvar 1)))) (.sort v)
  have hbeta : F.IsDefEq 1 [.sort (.succ .zero)]
      (.app (.app (.const ``MDep []) (.sort .zero))
        (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))
      (.app mpVal (.bvar 0)) (.sort (.succ .zero)) := by
    refine .symm (VEnv.IsDefEq.beta (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
      ?_ ?_) <;> type_tac
  exact ⟨_, .forallEDF (.sortDF (l := .succ .zero) (l' := .succ .zero)
    (by decide) (by decide) rfl) (.forallEDF hbeta (by type_tac))⟩

end

section
variable {env₁ E₁ F₁ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)

include h in
theorem mdep_const : env₁.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ :=
  VEnv.addInduct'_types h (List.Mem.head _)

include h in
theorem mdepNode_const : env₁.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.head _)

include hF₁ in
theorem mpF₁_mp : F₁.constants ``MP
    = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  VEnv.addConstList_constants hF₁
    (``MP, ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (by exact List.Mem.head _)

include h hF₁ in
theorem mpF₁_mdep : F₁.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ :=
  (VEnv.addConstList_le hF₁).constants (mdep_const h)

include h hF₁ in
theorem mpF₁_mdepNode : F₁.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩ :=
  (VEnv.addConstList_le hF₁).constants (mdepNode_const h)

include h hF₁ in
theorem mpF₁_ordered : F₁.Ordered :=
  VEnv.addConstList_ordered (mpEnv_ordered h) (VEnv.addInductR_typeConstsC_wf mpAuxB_WF) hF₁

include h hE₁ hF₁ in
theorem mpSubst_WF : mpSubst.WF E₁ F₁ 0 := by
  have hfresh := mpSubst_fresh h
  refine CSubst.one_WF_of_hasType (U := 0) (ci := ⟨0, _⟩) (mpF₁_ordered h hF₁)
    ⟨trivial, ⟨trivial, trivial⟩, trivial, trivial, Nat.lt_succ_self 1⟩
    (mpNested_const_staged hE₁) ⟨trivial, trivial⟩ (mpVal_hasTypeF (mpF₁_mdep h hF₁) (mpF₁_mp hF₁)) ?_ ?_
  · intro c' ci' hne hc'
    by_cases hM : c' = ``MP
    · subst hM
      rw [mp_const_staged hE₁] at hc'; cases hc'
      exact ⟨mpF₁_mp hF₁, trivial, trivial⟩
    · have hmem : c' ∉ ((mpAux mpAuxNodeB).typeConsts.map (·.1)) := by
        show c' ∉ [``MP, mpNestedName]
        simp [hM, hne]
      rw [VEnv.addConstList_constants_of_not_mem hE₁ hmem] at hc'
      refine ⟨?_, (mpEnv_ordered h).noCSubstC hfresh hc'⟩
      have hmem₁ : c' ∉ (((mpAux mpAuxNodeB).typeConstsC mpK).map (·.1)) := by
        show c' ∉ [``MP]
        simp [hM]
      rw [VEnv.addConstList_constants_of_not_mem hF₁ hmem₁]; exact hc'
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₁] at hdf
    exact ⟨(VEnv.addConstList_defeqs hF₁) ▸ hdf, (mpEnv_ordered h).noCSubstD hfresh hdf⟩

include h hE₁ hF₁ in
/-- **Obligation (A) at the parameterised REDEX block.**  One `IsDefEq.beta`, exactly as at
`ntreeAux`; the parameter entry is unchanged and costs nothing (`TeleDefEq.rfl`). -/
theorem mpAuxB_ctorConstsCR_wf :
    ∀ c ∈ (mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK, VConstant.WF F₁ c.2 := by
  have hD := mpF₁_mdep h hF₁
  have hP := mpF₁_mp hF₁
  have henv₁ := mpEnv_ordered h
  refine VEnv.ctorConstsCR_wf_of_substC' mpAuxB_WF hE₁
    (VInductDecl'.addIndTypes_ordered henv₁ mpAuxB_WF hE₁) (mpF₁_ordered h hF₁)
    (mp_csubstTy_eq ▸ mpSubst_WF h hE₁ hF₁) ?_
  rintro j T C hT hK hC
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    refine ⟨.succ .zero, .rfl (.cons (u := .succ .zero) ?_ .nil), by type_tac⟩
    refine VEnv.IsDefEq.beta (A := .sort (.succ .zero)) (B := .sort (.succ .zero)) ?_ ?_ <;>
      type_tac
  | 1, hT =>
    cases hT
    exact absurd (by decide) hK
  | (_ + 2), hT => simp [mpAux] at hT

end

/-! ## §14 `hσ` at the parameterised redex block — `CSubst.WFD` at the second staging pair

The strict `CSubst.WF` is unavailable here: §10's `mp_const_clause_ne` is exactly the `hne` of
`VEnv.csubst_WF_staged_false`, which §10 could not cash in *because there was no staging pair*.
§12/§13 build one, so both halves now land: `mp_csubst_WF₂_false` (the refutation) and
`mp_csubst_WFD₂` (the repair). -/

theorem mp_csubst_closed : (mpRestore.csubst (mpAux mpAuxNodeB) mpK).Closed := by
  exact VIndRestore.csubst_closed mpRestore (mpAux mpAuxNodeB) mpK ⟨trivial, trivial⟩
    mpRestore_tyArgs_closedNp

theorem mp_csubst_ne {c : Name} (hn : mpRestore.csubst (mpAux mpAuxNodeB) mpK c = none) :
    c ≠ mpNestedName ∧ c ≠ `_nested.MDep_1.rec ∧ c ≠ `_nested.MDep_1.node := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd hn nofun

theorem mp_csubst_fresh {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    (mpRestore.csubst (mpAux mpAuxNodeB) mpK).FreshIn env₁ := by
  intro c ci hc
  cases hn : mpRestore.csubst (mpAux mpAuxNodeB) mpK c with
  | none => rfl
  | some t =>
    exfalso
    by_cases h1 : c = mpNestedName
    · subst h1
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    by_cases h2 : c = `_nested.MDep_1.rec
    · subst h2
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    by_cases h3 : c = `_nested.MDep_1.node
    · subst h3
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    · rw [show mpRestore.csubst (mpAux mpAuxNodeB) mpK c = none from by
        show List.lookup c [(mpNestedName, _), (`_nested.MDep_1.rec, _),
          (`_nested.MDep_1.node, _)] = none
        rw [List.lookup_cons, show (c == mpNestedName) = false from beq_eq_false_iff_ne.2 h1,
          List.lookup_cons,
          show (c == `_nested.MDep_1.rec) = false from beq_eq_false_iff_ne.2 h2,
          List.lookup_cons,
          show (c == `_nested.MDep_1.node) = false from beq_eq_false_iff_ne.2 h3]
        rfl] at hn
      exact absurd hn nofun

/-! ### §14.1 The remaining two staging environments -/

theorem mpAuxB_stagedE₂ {E₁ : VEnv} {env₁ : VEnv}
    (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁) :
    ∃ E₂, E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  have hn' : n ∈ [``MP.obj, `_nested.MDep_1.node] := by revert hn; revert n; decide
  rw [VEnv.addConstList_constants_of_not_mem hE₁
    (by show n ∉ [``MP, mpNestedName]; revert hn'; revert n; decide)]
  exact mp_fresh' h n (by revert hn'; revert n; decide)

theorem mpAuxB_stagedF₂ {F₁ : VEnv} {env₁ : VEnv}
    (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁) :
    ∃ F₂, F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  have hn' : n ∈ [``MP.obj] := by revert hn; revert n; decide
  rw [VEnv.addConstList_constants_of_not_mem hF₁
    (by show n ∉ [``MP]; revert hn'; revert n; decide)]
  exact mp_fresh' h n (by revert hn'; revert n; decide)

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)

include h hE₁ hF₁ hF₂ in
theorem mpF₂_ordered : F₂.Ordered :=
  VEnv.addConstList_ordered (mpF₁_ordered h hF₁) (mpAuxB_ctorConstsCR_wf h hE₁ hF₁) hF₂

include h hF₁ hF₂ in
theorem mpF₂_mdep : F₂.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ :=
  (VEnv.addConstList_le hF₂).constants (mpF₁_mdep h hF₁)

include h hF₁ hF₂ in
theorem mpF₂_mdepNode : F₂.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩ :=
  (VEnv.addConstList_le hF₂).constants (mpF₁_mdepNode h hF₁)

include hF₁ hF₂ in
theorem mpF₂_mp : F₂.constants ``MP
    = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  (VEnv.addConstList_le hF₂).constants (mpF₁_mp hF₁)

include hF₂ in
theorem mpF₂_obj : F₂.constants ``MP.obj
    = some ⟨0, (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
        (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)⟩ :=
  VEnv.addConstList_constants hF₂
    (``MP.obj, ⟨0, (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
      (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)⟩) (by exact List.Mem.head _)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **`hσ` at the parameterised REDEX block, in its corrected form.**  Every clause is
discharged, and **exactly one** constant uses `WFD`'s new freedom — `MP.obj`, through
`mp_obj_const_defeq`'s right disjunct.  The other four (`MP`, `MDep`, `MDep.node`, `MDep.rec`)
take the left disjunct, i.e. `CSubst.WF`'s clause verbatim.  Same count as at `ntreeAux`
(`ntree_csubst_WFD₂`: one of seven); so `WFD` is still not a weakening everything satisfies. -/
theorem mp_csubst_WFD₂ : (mpRestore.csubst (mpAux mpAuxNodeB) mpK).WFD E₂ F₂ 1 := by
  have henv₁ := mpEnv_ordered h
  have hFo := mpF₂_ordered h hE₁ hF₁ hF₂
  have hfresh := mp_csubst_fresh h
  have hD := mpF₂_mdep h hF₁ hF₂
  have hP := mpF₂_mp hF₁ hF₂
  have hNd := mpF₂_mdepNode h hF₁ hF₂
  refine ⟨mp_csubst_closed, ?_, ?_, ?_⟩
  · intro c ci hn hc
    obtain ⟨hd1, hd2, hd3⟩ := mp_csubst_ne hn
    by_cases hMP : c = ``MP
    · subst hMP
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show ``MP ∉ [``MP.obj, `_nested.MDep_1.node]; simp),
        mp_const_staged hE₁] at hc
      cases hc
      exact ⟨_, hP, .inl rfl⟩
    by_cases hOb : c = ``MP.obj
    · subst hOb
      rw [VEnv.addConstList_constants hE₂ (``MP.obj, ⟨0, mpObj.type (mpAux mpAuxNodeB) 0⟩)
        (by exact List.Mem.head _)] at hc
      cases hc
      refine ⟨_, mpF₂_obj hF₂, .inr ?_⟩
      intro Γ ls hls hlen
      match ls, hlen with
      | [], _ =>
        obtain ⟨v, hv⟩ := mp_obj_const_defeq hD hP
        exact ⟨v, hv.weak0 hFo⟩
    · have hm₂ : c ∉ ((mpAux mpAuxNodeB).ctorConsts.map (·.1)) := by
        show c ∉ [``MP.obj, `_nested.MDep_1.node]
        simp [hOb, hd3]
      have hm₁ : c ∉ ((mpAux mpAuxNodeB).typeConsts.map (·.1)) := by
        show c ∉ [``MP, `_nested.MDep_1]
        simp [hMP, show c ≠ `_nested.MDep_1 from hd1]
      rw [VEnv.addConstList_constants_of_not_mem hE₂ hm₂,
        VEnv.addConstList_constants_of_not_mem hE₁ hm₁] at hc
      refine ⟨_, ?_, .inl rfl⟩
      rw [(henv₁.noCSubstC hfresh hc).substC_eq]
      have hm₄ : c ∉ (((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK).map (·.1)) := by
        show c ∉ [``MP.obj]; simp [hOb]
      have hm₃ : c ∉ (((mpAux mpAuxNodeB).typeConstsC mpK).map (·.1)) := by
        show c ∉ [``MP]; simp [hMP]
      rw [VEnv.addConstList_constants_of_not_mem hF₂ hm₄,
        VEnv.addConstList_constants_of_not_mem hF₁ hm₃]
      exact hc
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₂, VEnv.addConstList_defeqs hE₁] at hdf
    rw [(henv₁.noCSubstD hfresh hdf).substC_eq,
      VEnv.addConstList_defeqs hF₂, VEnv.addConstList_defeqs hF₁]
    exact hdf
  · intro c t ci Γ ls ls' hσv hc
    by_cases hd1 : c = mpNestedName
    · subst hd1
      rw [mp_csubst_val] at hσv
      cases hσv
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show `_nested.MDep_1 ∉ [``MP.obj, `_nested.MDep_1.node]; decide),
        mpNested_const_staged hE₁] at hc
      cases hc
      exact CSubst.val_of_hasType hFo (mpVal_hasTypeF hD hP)
    by_cases hd3 : c = `_nested.MDep_1.node
    · subst hd3
      rw [mp_csubst_node_val] at hσv
      cases hσv
      rw [VEnv.addConstList_constants hE₂
        (`_nested.MDep_1.node, ⟨0, mpAuxNodeB.type (mpAux mpAuxNodeB) 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc
      cases hc
      exact CSubst.val_of_hasType hFo (mpValNode_hasTypeF hD hP hNd)
    by_cases hd2 : c = `_nested.MDep_1.rec
    · subst hd2
      exfalso
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show `_nested.MDep_1.rec ∉ [``MP.obj, `_nested.MDep_1.node]; simp),
        VEnv.addConstList_constants_of_not_mem hE₁
          (by show `_nested.MDep_1.rec ∉ [``MP, `_nested.MDep_1]; decide),
        VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
      exact absurd hc nofun
    · exfalso
      rw [show mpRestore.csubst (mpAux mpAuxNodeB) mpK c = none from by
        show List.lookup c [(mpNestedName, _), (`_nested.MDep_1.rec, _),
          (`_nested.MDep_1.node, _)] = none
        rw [List.lookup_cons, show (c == mpNestedName) = false from beq_eq_false_iff_ne.2 hd1,
          List.lookup_cons,
          show (c == `_nested.MDep_1.rec) = false from beq_eq_false_iff_ne.2 hd2,
          List.lookup_cons,
          show (c == `_nested.MDep_1.node) = false from beq_eq_false_iff_ne.2 hd3]
        rfl] at hσv
      exact absurd hσv nofun

end

/-! ## §15 Obligation (B) at `MP`, reduced to `hbridge` alone — and §10's refutation, cashed in

§12–§14 discharge **every environment-level input** of `VEnv.recConstsR_wf_of_substCD'` at
`mpAux mpAuxNodeB`: `hsrc` (§12.2), `hσ` (§14), `he₂` (§13).  What is left is the telescope
bridge and nothing else — the exact position `ntreeAux` was in after `ConstSubstNested.lean` §D,
before §E supplied `rhbridge`. -/

/-- **All four staging environments exist together**, so nothing below is hypothetical. -/
theorem mp_stage₂_exists :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ ∧
      F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' mrDepDecl = some e := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ := mpAuxB_stagedE₁ h
  obtain ⟨F₁, hF₁⟩ := mpAuxB_stagedF₁ h
  obtain ⟨E₂, hE₂⟩ := mpAuxB_stagedE₂ h hE₁
  obtain ⟨F₂, hF₂⟩ := mpAuxB_stagedF₂ h hF₁
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)

include hE₂ hF₂ in
/-- **§10's refutation, cashed in.**  §10 could only say *"the remaining hypotheses hold at
`MP.obj`, so the refutation applies once a staging pair for this block exists — it does not
yet"*.  It does now: **no** constant substitution is `CSubst.WF` between `MP`'s two staging
environments, for any `U`.  So `mp_csubst_WFD₂` is not a convenience; the strict form is false. -/
theorem mp_any_WF₂_false (σ : CSubst) {U : Nat} (hdom : σ ``MP.obj = none)
    (hne : (mpObj.type (mpAux mpAuxNodeB) 0).substC σ
      ≠ (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
          (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)) :
    ¬ σ.WF E₂ F₂ U :=
  VEnv.csubst_WF_staged_false hE₂ hF₂ mp_obj_mem (by decide) mp_ctorName_id hdom hne

include hE₂ hF₂ in
/-- …in particular for the block's own substitution. -/
theorem mp_csubst_WF₂_false {U : Nat} :
    ¬ (mpRestore.csubst (mpAux mpAuxNodeB) mpK).WF E₂ F₂ U :=
  mp_any_WF₂_false hE₂ hF₂ _ mp_csubst_obj_none
    (fun hh => mp_const_clause_ne (hh.trans mp_obj_declared))

include h hE₁ hE₂ hF₁ hF₂ in
/-- **Obligation (B) at the parameterised REDEX block, reduced to `hbridge` alone.**
Compare `InductiveDeclExamples.ntreeAux_recConstsR_wf_of_bridge`, which is the same statement at
the canonical parameterised block; §E of `ConstSubstNested.lean` then closed *its* bridge. -/
theorem mpAuxB_recConstsR_wf_of_bridge
    (hbridge : ∀ (j : Nat) (T : VIndType), (mpAux mpAuxNodeB).types[j]? = some T →
      ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
        ((mpAux mpAuxNodeB).recType j).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
          = VExpr.mkPi As B ∧
        ((mpAux mpAuxNodeB).recTypeR mpRestore j).substC
            (mpRestore.csubst (mpAux mpAuxNodeB) mpK) = VExpr.mkPi As' B' ∧
        F₂.TeleDefEq (mpAux mpAuxNodeB).recUvars [] As As' ∧
        F₂.IsDefEq (mpAux mpAuxNodeB).recUvars As.reverse B B' (.sort v)) :
    ∀ c ∈ (mpAux mpAuxNodeB).recConstsR mpRestore mpK, VConstant.WF F₂ c.2 :=
  VEnv.recConstsR_wf_of_substCD' (mp_recConsts_wf h hE₁ hE₂)
    (mp_csubst_WFD₂ h hE₁ hE₂ hF₁ hF₂) (mpF₂_ordered h hE₁ hF₁ hF₂) hbridge

end

/-! ### §15.1 What the residual bridge is, measured

Both recursor telescopes have **six** entries and the split is the same shape as `ntreeAux`'s
(`ConstSubstNested.lean` §E) but one entry shorter, because `MP` has two minor premises and
`NTree`'s auxiliary block has three.  The measurements below are `decide`, not read off. -/

/-- The two recursor types split into **six** π-entries each, on both sides. -/
theorem mp_recTele_len :
    ((VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.length,
      (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.length,
      (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.length,
      (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.length) = (6, 6, 6, 6) := by decide

/-- **The bodies of both recursors are IDENTITIES** — a negative result, and the third and
fourth instance in this corner of "the restoration is the identity at a position indexed by the
block's own member".  At `ntreeAux` only `rBody0` was free (`rBody0_eq`); here both are. -/
theorem mp_recBody_eq :
    ((VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).2
      = (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).2) ∧
    ((VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).2
      = (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).2) := by decide

/-- **Exactly which telescope entries move**: three of six at `MP.rec`, four of six at
`MP.rec_1`.  The two that never move are the parameter and the first motive; the sixth (the
major premise's domain) moves only at the companion recursor — `rMaj_node_eq`'s rule again. -/
theorem mp_recTele_moved :
    ((VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.zipWith (fun a b => a != b)
      (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1
      = [false, false, true, true, true, false]) ∧
    ((VExpr.splitPis 100 (((mpAux mpAuxNodeB).recType 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1.zipWith (fun a b => a != b)
      (VExpr.splitPis 100 (((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK))).1
      = [false, false, true, true, true, true]) := by decide

/-! ## §16 `hbridge` at `MP` — obligation (B) DISCHARGED at the parameterised REDEX block

§15 reduced (B) at `mpAux mpAuxNodeB` to `hbridge` alone.  This section proves it, modelled on
`ConstSubstNested.lean` §E, whose shape §15.1 measured: six π-entries each side, the first two
free, three moving at `MP.rec` and four at `MP.rec_1`, both bodies identities.

**Where the measurement in §15.1 under-counted, and it is a `decide`-checkable fact rather than
a judgement:** §15.1 said *"two β-lemmas suffice (`mpVal k`, `mpValNode k`) against §E's
three"*.  They suffice for the entries that **move**.  They do not suffice for the
derivation, because `mpA4` — the companion minor premise — contains the block's **stored field
redex** `(λ _ : Prop, MP #(m+1)) #k`, which is *identical on both sides* (row 143d: it is indexed
by the block's own member `MP`) and therefore contributes nothing to the bridge, yet still has to
be β-contracted for the induction hypothesis `#4 #0` to be typed at all.  So the count is **three
β-lemmas, of which two move and one only types** — and the third one exists precisely because
this is a *redex* block, which `ntreeAux` is not.  See §16.4. -/

def mpNt : VExpr := .const ``MP []
def mpDt : VExpr := .const ``MDep []
def mpNdt : VExpr := .const ``MDep.node []

/-- The contraction of `mpVal #k`: `MDep Prop (λ _, MP #(k+1))`. -/
def mpVc (k : Nat) : VExpr :=
  .app (.app mpDt (.sort .zero)) (.lam (.sort .zero) (.app mpNt (.bvar (k+1))))

/-- The contraction of `mpValNode #k`. -/
def mpNc (k : Nat) : VExpr :=
  .app (.app mpNdt (.sort .zero)) (.lam (.sort .zero) (.app mpNt (.bvar (k+1))))

/-- The block's **stored** field redex, as it appears inside the companion minor premise.  It
does **not** move under the restoration — the field is indexed by member `0`, i.e. `MP` itself. -/
def mpFd (m k : Nat) : VExpr := .app (.lam (.sort .zero) (.app mpNt (.bvar (m+1)))) (.bvar k)

/-! ### §16.1 The two substituted telescopes, written out -/

def mpA0 : VExpr := .sort (.succ .zero)
def mpA1 : VExpr := .forallE (.app mpNt (.bvar 0)) (.sort (.param 0))
def mpA2 : VExpr := .forallE (.app mpVal (.bvar 1)) (.sort (.param 0))
def mpA2' : VExpr := .forallE (mpVc 1) (.sort (.param 0))
def mpA3body : VExpr :=
  .forallE (.app (.bvar 1) (.bvar 0))
    (.app (.bvar 3) (.app (.app (.const ``MP.obj []) (.bvar 4)) (.bvar 1)))
def mpA3 : VExpr := .forallE (.app mpVal (.bvar 2)) mpA3body
def mpA3' : VExpr := .forallE (mpVc 2) mpA3body
def mpA4 : VExpr :=
  .forallE (.sort .zero)
    (.forallE (mpFd 4 0)
      (.forallE (.app (.bvar 4) (.bvar 0))
        (.app (.bvar 4) (.app (.app (.app mpValNode (.bvar 6)) (.bvar 2)) (.bvar 1)))))
def mpA4' : VExpr :=
  .forallE (.sort .zero)
    (.forallE (mpFd 4 0)
      (.forallE (.app (.bvar 4) (.bvar 0))
        (.app (.bvar 4) (.app (.app (mpNc 6) (.bvar 2)) (.bvar 1)))))
/-- `MP.rec`'s major premise domain — an application of the member the step declares, so the
restoration is the identity on it. -/
def mpA5₀ : VExpr := .app mpNt (.bvar 4)
/-- `MP.rec_1`'s major premise domain — a companion application, so it **moves**. -/
def mpA5₁ : VExpr := .app mpVal (.bvar 4)
def mpA5₁' : VExpr := mpVc 4
def mpBody₀ : VExpr := .app (.bvar 4) (.bvar 0)
def mpBody₁ : VExpr := .app (.bvar 3) (.bvar 0)

def mpTele₀ : List VExpr := [mpA0, mpA1, mpA2, mpA3, mpA4, mpA5₀]
def mpTeleR₀ : List VExpr := [mpA0, mpA1, mpA2', mpA3', mpA4', mpA5₀]
def mpTele₁ : List VExpr := [mpA0, mpA1, mpA2, mpA3, mpA4, mpA5₁]
def mpTeleR₁ : List VExpr := [mpA0, mpA1, mpA2', mpA3', mpA4', mpA5₁']

/-- The four decompositions `hbridge` asks for, all `rfl`. -/
theorem mprecType_eq_0 :
    ((mpAux mpAuxNodeB).recType 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = VExpr.mkPi mpTele₀ mpBody₀ := rfl
theorem mprecType_eq_1 :
    ((mpAux mpAuxNodeB).recType 1).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = VExpr.mkPi mpTele₁ mpBody₁ := rfl
theorem mprecTypeR_eq_0 :
    ((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = VExpr.mkPi mpTeleR₀ mpBody₀ := rfl
theorem mprecTypeR_eq_1 :
    ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = VExpr.mkPi mpTeleR₁ mpBody₁ := rfl

/-! ### §16.2 The three β-steps

Two of them **move** an entry (`mpVal #k` and `mpValNode #k`, the values the restoration
presents for the companion member and its constructor).  The third does not move anything: it
contracts the block's own **stored** field redex, which the restoration leaves alone, and exists
only so that the companion minor premise's induction hypothesis can be typed. -/

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hP in
/-- `MP`'s own constant, as a self-defeq at the type the environment holds. -/
theorem mpPC {Γ : List VExpr} : F.IsDefEq 1 Γ mpNt mpNt
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .constDF hP nofun nofun rfl .nil

include hOb in
theorem mpObjC {Γ : List VExpr} : F.IsDefEq 1 Γ (.const ``MP.obj []) (.const ``MP.obj [])
    (.forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))) :=
  .constDF hOb nofun nofun rfl .nil

include hD hP in
/-- **β-step 1**, and the one entries 2, 3 and (at `MP.rec_1`) 5 move by. -/
theorem mpBetaV {Γ : List VExpr} {k : Nat} (hk : Lookup Γ k (.sort (.succ .zero))) :
    F.IsDefEq 1 Γ (.app mpVal (.bvar k)) (mpVc k) (.sort (.succ .zero)) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 1) (Γ := Γ)
    (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
    (e := .app (.app (.const ``MDep []) (.sort .zero))
      (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))
    (by type_tac) (.bvar hk)
  simpa [mpVal, mpVc, mpNt, mpDt, VExpr.inst, VExpr.lift, VExpr.liftN] using h

include hP hNd in
/-- **β-step 2**, the one inside entry 4's minor premise. -/
theorem mpBetaN {Γ : List VExpr} {k : Nat} (hk : Lookup Γ k (.sort (.succ .zero))) :
    F.IsDefEq 1 Γ (.app mpValNode (.bvar k)) (mpNc k)
      (.forallE (.sort .zero) (.forallE (mpFd (k+1) 0) (mpVc (k+2)))) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 1) (Γ := Γ)
    (A := .sort (.succ .zero))
    (B := .forallE (.sort .zero)
      (.forallE (.app (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 2))) (.bvar 0))
        (.app (.app (.const ``MDep []) (.sort .zero))
          (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 3))))))
    (e := .app (.app (.const ``MDep.node []) (.sort .zero))
      (.lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))))
    (by type_tac) (.bvar hk)
  have e1 : k + 1 + 1 = k + 2 := rfl
  have e2 : k + 2 + 1 = k + 3 := rfl
  simpa [mpValNode, mpNc, mpFd, mpVc, mpNt, mpDt, mpNdt, VExpr.inst, VExpr.lift,
    VExpr.liftN, e1, e2] using h

include hP in
/-- **β-step 3 — the one §15.1's count missed.**  The stored field redex contracts; it is the
same expression on both sides of the bridge, so it moves nothing, but without it the companion
minor premise's induction hypothesis `#4 #0` has no type. -/
theorem mpBetaF {Γ : List VExpr} {m j : Nat} (hm : Lookup Γ m (.sort (.succ .zero)))
    (hj : Lookup Γ j (.sort .zero)) :
    F.IsDefEq 1 Γ (mpFd m j) (.app mpNt (.bvar m)) (.sort (.succ .zero)) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 1) (Γ := Γ)
    (A := .sort .zero) (B := .sort (.succ .zero))
    (e := .app (.const ``MP []) (.bvar (m+1)))
    (.appDF (mpPC hP) (.bvar (hm.succ (A := .sort .zero)))) (.bvar hj)
  simpa [mpFd, mpNt, VExpr.inst, VExpr.lift, VExpr.liftN] using h

end

/-! ### §16.3 The entry defeqs, and the bridge

Entries `mpA0` (the parameter) and `mpA1` (the motive for `MP`) do not move — `TeleDefEq.rfl`,
free.  Entries 2, 3, 4 move at both recursors; entry 5 moves only at `MP.rec_1`.  Both bodies are
identities and are discharged as *typings*, which is what `mp_recBody_eq` says. -/

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hD hP in
/-- Entry 2 — the motive for the companion member.  One `mpBetaV`. -/
theorem mpE2 : ∃ u, F.IsDefEq 1 [mpA1, mpA0] mpA2 mpA2' (.sort u) :=
  ⟨_, .forallEDF (mpBetaV hD hP (Γ := [mpA1, mpA0]) (k := 1) (.succ .zero))
    (.sortDF (l := .param 0) (l' := .param 0) (by decide) (by decide) rfl)⟩

include hD hP hOb in
/-- Entry 3 — `MP.obj`'s minor premise.  Two `mpBetaV`s: one at the domain (which is what
moves) and one inside the body, converting the induction hypothesis' argument. -/
theorem mpE3 : ∃ u, F.IsDefEq 1 [mpA2, mpA1, mpA0] mpA3 mpA3' (.sort u) := by
  refine ⟨_, .forallEDF (mpBetaV hD hP (Γ := [mpA2, mpA1, mpA0]) (k := 2)
      (.succ (.succ .zero)))
    (.forallEDF (v := .param 0)
      (.appDF (B := .sort (.param 0)) (.bvar (.succ .zero)) (.bvar .zero)) ?_)⟩
  exact .appDF (B := .sort (.param 0))
      (.bvar (.succ (.succ (.succ .zero))))
    (.appDF (.appDF (mpObjC hOb) (.bvar (.succ (.succ (.succ (.succ .zero))))))
      (.defeqDF (mpBetaV hD hP (k := 4) (.succ (.succ (.succ (.succ .zero)))))
        (.bvar (.succ .zero))))

include hD hP hNd in
/-- Entry 4 — the companion constructor's minor premise, and the only entry where all three
β-lemmas appear: `mpBetaN` for the constructor application (which moves), `mpBetaF` twice for the
**stored** field redex (which does not). -/
theorem mpE4 : ∃ u, F.IsDefEq 1 [mpA3, mpA2, mpA1, mpA0] mpA4 mpA4' (.sort u) := by
  have hfield : F.IsDefEq 1 [.sort .zero, mpA3, mpA2, mpA1, mpA0] (mpFd 4 0) (mpFd 4 0)
      (.sort (.succ .zero)) :=
    (mpBetaF hP (m := 4) (j := 0) (.succ (.succ (.succ (.succ .zero)))) .zero).trans
      (mpBetaF hP (m := 4) (j := 0) (.succ (.succ (.succ (.succ .zero)))) .zero).symm
  refine ⟨_, .forallEDF (.sortDF (l := .zero) (l' := .zero) (by decide) (by decide) rfl)
    (.forallEDF hfield (.forallEDF (v := .param 0)
      (.appDF (B := .sort (.param 0)) (.bvar (.succ (.succ (.succ (.succ .zero)))))
        (.defeqDF (mpBetaF hP (m := 5) (j := 1)
          (.succ (.succ (.succ (.succ (.succ .zero))))) (.succ .zero)) (.bvar .zero))) ?_))⟩
  exact .appDF (B := .sort (.param 0))
      (.bvar (.succ (.succ (.succ (.succ .zero)))))
    (.defeqDF (.symm (mpBetaV hD hP (k := 6)
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
      (.appDF (.appDF (mpBetaN hP hNd (k := 6)
          (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) (.bvar (.succ (.succ .zero))))
        (.bvar (.succ .zero))))

include hD hP in
/-- Entry 5 at `MP.rec_1` — the major premise's domain, a companion application.  One
`mpBetaV`.  At `MP.rec` the same entry is `mpA5₀`, an application of the block's **own**
member, and does not move at all. -/
theorem mpE5₁ : ∃ u, F.IsDefEq 1 [mpA4, mpA3, mpA2, mpA1, mpA0] mpA5₁ mpA5₁' (.sort u) :=
  ⟨_, mpBetaV hD hP (Γ := [mpA4, mpA3, mpA2, mpA1, mpA0]) (k := 4)
    (.succ (.succ (.succ (.succ .zero))))⟩

include hD hP hNd hOb in
theorem mpTeleDefEq₀ : F.TeleDefEq 1 [] mpTele₀ mpTeleR₀ := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  exact .rfl (.rfl (.cons h2 (.cons h3 (.cons h4 (.rfl .nil)))))

include hD hP hNd hOb in
theorem mpTeleDefEq₁ : F.TeleDefEq 1 [] mpTele₁ mpTeleR₁ := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  obtain ⟨u5, h5⟩ := mpE5₁ hD hP
  exact .rfl (.rfl (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil)))))

/-! ### The two bodies — both identities, so both are typings -/

/-- **Both bodies are free, and freer than §15.1 recorded**: they need no constant lookup at
all, only two `Lookup`s — so the two identity bodies cost nothing even in hypotheses. -/
theorem mpB₀ : ∃ v, F.IsDefEq 1 mpTele₀.reverse mpBody₀ mpBody₀ (.sort v) :=
  ⟨_, .appDF (B := .sort (.param 0))
    (.bvar (show Lookup mpTele₀.reverse 4
      (.forallE (.app mpNt (.bvar 5)) (.sort (.param 0))) from
      .succ (.succ (.succ (.succ .zero))))) (.bvar .zero)⟩

theorem mpB₁ : ∃ v, F.IsDefEq 1 mpTele₁.reverse mpBody₁ mpBody₁ (.sort v) :=
  ⟨_, .appDF (B := .sort (.param 0))
    (.bvar (show Lookup mpTele₁.reverse 3
      (.forallE (.app mpVal (.bvar 5)) (.sort (.param 0))) from
      .succ (.succ (.succ .zero)))) (.bvar .zero)⟩

include hD hP hNd hOb in
/-- **`hbridge` at `MP`, proved** — both recursors of the parameterised **redex** block.  The
counterpart of `InductiveDeclExamples.rhbridge` at the canonical parameterised block. -/
theorem mphbridge : ∀ (j : Nat) (T : VIndType), (mpAux mpAuxNodeB).types[j]? = some T →
    ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
      ((mpAux mpAuxNodeB).recType j).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
        = VExpr.mkPi As B ∧
      ((mpAux mpAuxNodeB).recTypeR mpRestore j).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK) = VExpr.mkPi As' B' ∧
      F.TeleDefEq (mpAux mpAuxNodeB).recUvars [] As As' ∧
      F.IsDefEq (mpAux mpAuxNodeB).recUvars As.reverse B B' (.sort v) := by
  rintro (_ | _ | j) T hT
  · obtain ⟨v, hv⟩ := mpB₀
    exact ⟨mpTele₀, mpTeleR₀, mpBody₀, mpBody₀, v, mprecType_eq_0, mprecTypeR_eq_0,
      mpTeleDefEq₀ hD hP hNd hOb, hv⟩
  · obtain ⟨v, hv⟩ := mpB₁
    exact ⟨mpTele₁, mpTeleR₁, mpBody₁, mpBody₁, v, mprecType_eq_1, mprecTypeR_eq_1,
      mpTeleDefEq₁ hD hP hNd hOb, hv⟩
  · simp [mpAux] at hT

end

/-- The type `ctorConstsCR` declares for `MP.obj`, written out — the shape `mpObjC` needs. -/
theorem mp_objType_eq :
    (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
        (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)
      = .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1))) := rfl

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **OBLIGATION (B) AT THE PARAMETERISED REDEX BLOCK, DISCHARGED.**  The counterpart of
`InductiveDeclExamples.ntreeAux_recConstsR_wf` at a block that is **not** `Canonical`. -/
theorem mpAuxB_recConstsR_wf :
    ∀ c ∈ (mpAux mpAuxNodeB).recConstsR mpRestore mpK, VConstant.WF F₂ c.2 :=
  mpAuxB_recConstsR_wf_of_bridge h hE₁ hE₂ hF₁ hF₂
    (mphbridge (mpF₂_mdep h hF₁ hF₂) (mpF₂_mp hF₁ hF₂) (mpF₂_mdepNode h hF₁ hF₂)
      (mp_objType_eq ▸ mpF₂_obj hF₂))

end

/-- …**and with nothing assumed**: `mp_stage₂_exists` supplies the five staging equations, so (B)
at `MP` is not hypothetical.  The (B) counterpart of `InductiveDeclExamples.ntreeAux_obligationB`
at a redex block. -/
theorem mpAuxB_obligationB :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ ∧
      F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ ∧
      ∀ c ∈ (mpAux mpAuxNodeB).recConstsR mpRestore mpK, VConstant.WF F₂ c.2 := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩ := mp_stage₂_exists
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂,
    mpAuxB_recConstsR_wf h hE₁ hE₂ hF₁ hF₂⟩

/-! ### §16.4 Anti-vacuity: what the bridge at `MP` really carries, and what it does not

Three positives and three negatives, all `decide` or `rfl`, none asserted. -/

theorem mpA2_ne : mpA2 ≠ mpA2' := by decide
theorem mpA3_ne : mpA3 ≠ mpA3' := by decide
theorem mpA4_ne : mpA4 ≠ mpA4' := by decide
theorem mpA5₁_ne : mpA5₁ ≠ mpA5₁' := by decide
theorem mpTele₀_ne : mpTele₀ ≠ mpTeleR₀ := by decide
theorem mpTele₁_ne : mpTele₁ ≠ mpTeleR₁ := by decide

/-- **Negative result 1**: `MP.rec`'s major-premise domain is an application of the member the
step declares, so the restoration is the identity on it — row 143d's rule, a *sixth* time. -/
theorem mpA5₀_eq : mpTele₀[5]? = some mpA5₀ ∧ mpTeleR₀[5]? = some mpA5₀ := ⟨rfl, rfl⟩

/-- **Negative result 2**: both bodies are identities, and `mpB₀`/`mpB₁` need no environment
hypothesis to type them. -/
theorem mpBody_eq : mpBody₀ = mpBody₀ ∧ mpBody₁ = mpBody₁ := ⟨rfl, rfl⟩

/-- **Negative result 3, and the correction to §15.1's count.**  The block's **stored** field
redex sits, *unchanged*, in entry 4 on both sides of the bridge… -/
theorem mpA4_field_shared :
    (∃ b, mpA4 = .forallE (.sort .zero) (.forallE (mpFd 4 0) b))
      ∧ (∃ b, mpA4' = .forallE (.sort .zero) (.forallE (mpFd 4 0) b)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- …and it really is a redex rather than its own contractum, which is why `mpBetaF` — a **third**
β-lemma, against §15.1's "two suffice" — has to exist even though it moves nothing.  It is the one
place where the block being a **redex** block costs the bridge anything. -/
theorem mpFd_ne : mpFd 4 0 ≠ .app mpNt (.bvar 4) := by decide

/-- The strict bridge is false at the **second** recursor too (§6 records `j = 0`), so
`mphbridge` cannot be obtained from `VEnv.recConstsR_wf_of_substC_of_eq` at either. -/
theorem mp_recTypeR_bridge_false_1 :
    ((mpAux mpAuxNodeB).recType 1).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      ≠ ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK) := by decide

/-! ## §17 Obligation (C) at `MP`: what it needs, measured — and `htele` at both ι-rules

`VEnv.iotaRulesRS_wf_of_hargsD` has nine hypotheses.  At `MP` **seven** are already theorems or
one-liners; the two that are not are `hσ` (a `CSubst.WFD` at the *third* staging pair, i.e. the
`ntree_csubst_WFD₃` analogue, which needs §H's recursor-type conversion first) and `hdata`.
This section discharges `hpos` and the whole of `htele`, and measures `hdata`.

Measured with `#eval` first, then landed as `decide`:

| rule | ι-ctx length | entries that move | ctx entry sizes L → R |
|---|---|---|---|
| `MP.obj` (`j = 0`) | **6** | **4** (`[F,F,T,T,T,T]`) | `[1,5,15,25,33,13]` → `[1,5,11,21,29,9]` |
| `_nested.MDep_1.node` (`j = 1`) | **7** | **3** (`[F,F,T,T,T,F,F]`) | `[1,5,15,25,33,1,7]` → `[1,5,11,21,29,1,7]` |

and the ι-contexts are **§16's telescope**: the five-entry prefix `mpA0…mpA4` is shared by both
rules *and* by both recursors, the `MP.obj` rule's sixth entry is `mpA5₁`/`mpA5₁'` on the nose (so
its ι-context **is** `mpTele₁`), and the companion rule's two extra entries are the block's own
`Prop` field and its **stored** field redex — *neither of which moves*.  That is cheaper than
`ntreeAux`, where node and cons each added one moving entry (§J). -/

def mpTeleP : List VExpr := [mpA0, mpA1, mpA2, mpA3, mpA4]
def mpTelePR : List VExpr := [mpA0, mpA1, mpA2', mpA3', mpA4']

/-- **The `MP.obj` ι-context is `mpTele₁`** — §16's `MP.rec_1` telescope on the nose, the
counterpart of `rIotaCtx_nil_eq`. -/
theorem mpIotaCtx_obj_eq :
    ((mpAux mpAuxNodeB).iotaCtx mpObj).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) = mpTele₁ := by decide

theorem mpIotaCtxR_obj_eq :
    ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpObj).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) = mpTeleR₁ := by decide

/-- The companion rule's ι-context is the shared prefix plus the constructor's own two fields —
`Prop` and the **stored** redex — and neither of the two moves. -/
theorem mpIotaCtx_node_eq :
    ((mpAux mpAuxNodeB).iotaCtx mpAuxNodeB).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      = mpTeleP ++ [.sort .zero, mpFd 5 0] := by decide

theorem mpIotaCtxR_node_eq :
    ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpAuxNodeB).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      = mpTelePR ++ [.sort .zero, mpFd 5 0] := by decide

/-- **`hpos` at `MP`, by `decide`** — re-indexed over `List`/`Option` membership first, because the
`∀ (t : Nat) … ∀ (i : Nat)` form is not `Decidable` (§38 item 2's guard). -/
theorem mpAuxB_recArg_lt : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ (mpAux mpAuxNodeB).ctorsAll →
    ∀ (i : Nat) (Fl : VIndField) (r : VIndRecArg), C.fields[i]? = some Fl →
      Fl.recArg = some r → r.idx < (mpAux mpAuxNodeB).nm := by
  have H : ∀ p ∈ (mpAux mpAuxNodeB).ctorsAll, ∀ Fl ∈ p.2.fields,
      ∀ r ∈ Fl.recArg, r.idx < (mpAux mpAuxNodeB).nm := by decide
  exact fun t C hmem i Fl r hi hr => H (t, C) hmem Fl (List.mem_of_getElem? hi) r hr

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hD hP hNd hOb in
/-- The five-entry prefix every telescope and every ι-context in this block shares, proved once
with an arbitrary tail. -/
theorem mpTeleDefEq_ext {As As' : List VExpr}
    (htail : F.TeleDefEq 1 [mpA4, mpA3, mpA2, mpA1, mpA0] As As') :
    F.TeleDefEq 1 [] (mpTeleP ++ As) (mpTelePR ++ As') := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  rw [show mpTeleP ++ As = mpA0 :: mpA1 :: mpA2 :: mpA3 :: mpA4 :: As from rfl,
    show mpTelePR ++ As' = mpA0 :: mpA1 :: mpA2' :: mpA3' :: mpA4' :: As' from rfl]
  exact .rfl (.rfl (.cons h2 (.cons h3 (.cons h4 htail))))

include hD hP hNd hOb in
/-- **`htele` at the `MP.obj` ι-rule** — literally §16's `MP.rec_1` telescope defeq. -/
theorem mpIotaTele_obj : F.TeleDefEq (mpAux mpAuxNodeB).recUvars []
    (((mpAux mpAuxNodeB).iotaCtx mpObj).map
      (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)))
    (((mpAux mpAuxNodeB).iotaCtxR mpRestore mpObj).map
      (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))) := by
  rw [mpIotaCtx_obj_eq, mpIotaCtxR_obj_eq]
  exact mpTeleDefEq₁ hD hP hNd hOb

include hD hP hNd hOb in
/-- **`htele` at the companion ι-rule** — the shared prefix, then two entries that do **not**
move.  Compare `rIotaTele_node`/`rIotaTele_cons`, which each need one `rbetaL` for their extra
field entry; `MP`'s extra entries are the block's own, so they are free. -/
theorem mpIotaTele_node : F.TeleDefEq (mpAux mpAuxNodeB).recUvars []
    (((mpAux mpAuxNodeB).iotaCtx mpAuxNodeB).map
      (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)))
    (((mpAux mpAuxNodeB).iotaCtxR mpRestore mpAuxNodeB).map
      (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))) := by
  rw [mpIotaCtx_node_eq, mpIotaCtxR_node_eq]
  exact mpTeleDefEq_ext hD hP hNd hOb (.rfl (.rfl .nil))

end

/-! ### §17.1 Anti-vacuity for §17, and the identity trap for a seventh time -/

theorem mpIotaCtx_obj_ne :
    ((mpAux mpAuxNodeB).iotaCtx mpObj).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      ≠ ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpObj).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := by decide

theorem mpIotaCtx_node_ne :
    ((mpAux mpAuxNodeB).iotaCtx mpAuxNodeB).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
      ≠ ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpAuxNodeB).map
        (VExpr.substC · (mpRestore.csubst (mpAux mpAuxNodeB) mpK)) := by decide

/-- **`hmaj` is FREE at `MP.obj`** — the block's own constructor, where the restoration is
`mpRestore_ownId`.  `rMaj_node_eq`'s rule at the redex block: **seventh** confirmation. -/
theorem mpMaj_obj_eq :
    ((mpAux mpAuxNodeB).ctorApp' mpObj (mpObj.fields.length
          + ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin))
        (VExpr.bvars 0 mpObj.fields.length)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      = ((mpAux mpAuxNodeB).ctorAppR mpRestore 0 mpObj (mpObj.fields.length
          + ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin))
        (VExpr.bvars 0 mpObj.fields.length)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK) := by decide

/-- …and **not** free at the companion constructor. -/
theorem mpMaj_node_ne :
    ((mpAux mpAuxNodeB).ctorApp' mpAuxNodeB (mpAuxNodeB.fields.length
          + ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin))
        (VExpr.bvars 0 mpAuxNodeB.fields.length)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)
      ≠ ((mpAux mpAuxNodeB).ctorAppR mpRestore 1 mpAuxNodeB (mpAuxNodeB.fields.length
          + ((mpAux mpAuxNodeB).nm + (mpAux mpAuxNodeB).nmin))
        (VExpr.bvars 0 mpAuxNodeB.fields.length)).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK) := by decide

/-! ### §17.2 `hdata` at both ι-rules of `MP` — the two residual `∃ A₀ v` triples -/

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hD hP hNd hOb in
theorem mpIotaHargs_obj :
    mpRestore.IotaHargs (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) F 0 mpObj := by
  refine ⟨mpIotaTele_obj hD hP hNd hOb, .app mpNt (.bvar 5), .succ .zero, ?_, ?_, ?_⟩
  · exact .bvar (.succ (.succ (.succ (.succ .zero))))
  · exact .appDF (mpPC hP) (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
  · exact .appDF (.appDF (mpObjC hOb)
        (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))
      (.defeqDF (mpBetaV hD hP (k := 5) (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.bvar .zero))

include hD hP hNd hOb in
theorem mpIotaHargs_node :
    mpRestore.IotaHargs (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) F 1
      mpAuxNodeB := by
  refine ⟨mpIotaTele_node hD hP hNd hOb, mpVc 6, .succ .zero, ?_, ?_, ?_⟩
  · exact .bvar (.succ (.succ (.succ (.succ .zero))))
  · exact (mpBetaV hD hP (k := 6)
      (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))).symm
  · exact .appDF (.appDF (mpBetaN hP hNd (k := 6)
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) (.bvar (.succ .zero)))
      (.bvar .zero)

end

/-! ## §18 Obligation (C) at `MP`: the recursor-stage `WFD`, and (C) discharged

§H/§I of `ConstSubstNested.lean` at `MP`.  The two lists the recursor stage folds, by `rfl`, which
is what makes `MP.rec` need `const`'s **defeq** disjunct and `_nested.MDep_1.rec` need `val`: -/

theorem mp_recConsts_eq : (mpAux mpAuxNodeB).recConsts
    = [(``MP.rec, ⟨1, (mpAux mpAuxNodeB).recType 0⟩),
       (`_nested.MDep_1.rec, ⟨1, (mpAux mpAuxNodeB).recType 1⟩)] := rfl

theorem mp_recConstsR_eq : (mpAux mpAuxNodeB).recConstsR mpRestore mpK
    = [(``MP.rec, ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩),
       (``MP.rec_1, ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩)] := rfl

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

/-! ### §18.1 The recursor telescopes are contexts -/

theorem mpIsTypeA0 : F.IsType 1 [] mpA0 := ⟨_, .sortDF (by decide) (by decide) rfl⟩

include hP in
theorem mpIsTypeA1 : F.IsType 1 [mpA0] mpA1 :=
  ⟨_, .forallEDF (.appDF (mpPC hP) (.bvar .zero))
    (.sortDF (l := .param 0) (l' := .param 0) (by decide) (by decide) rfl)⟩

include hD hP hNd hOb in
theorem mpOnCtx₀ : OnCtx mpTele₀.reverse (F.IsType 1) := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  exact ⟨⟨⟨⟨⟨⟨trivial, mpIsTypeA0⟩, mpIsTypeA1 hP⟩, ⟨_, h2.hasType.1⟩⟩, ⟨_, h3.hasType.1⟩⟩,
    ⟨_, h4.hasType.1⟩⟩,
    ⟨_, .appDF (mpPC hP) (.bvar (.succ (.succ (.succ (.succ .zero)))))⟩⟩

include hD hP hNd hOb in
theorem mpOnCtx₁ : OnCtx mpTele₁.reverse (F.IsType 1) := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  obtain ⟨u5, h5⟩ := mpE5₁ hD hP
  exact ⟨⟨⟨⟨⟨⟨trivial, mpIsTypeA0⟩, mpIsTypeA1 hP⟩, ⟨_, h2.hasType.1⟩⟩, ⟨_, h3.hasType.1⟩⟩,
    ⟨_, h4.hasType.1⟩⟩, ⟨_, h5.hasType.1⟩⟩

/-! ### §18.2 The two whole-pi conversions, and the shapes `WFD` asks for -/

include hD hP hNd hOb in
theorem mpRecPi0 : ∃ u, F.IsDefEq 1 []
    (((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
    (((mpAux mpAuxNodeB).recType 0).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
    (.sort u) := by
  obtain ⟨u, h⟩ := VEnv.IsDefEq.mkPi_congrU (mpTeleDefEq₀ hD hP hNd hOb)
    (by simpa using mpOnCtx₀ hD hP hNd hOb) mpB₀
  exact ⟨u, mprecType_eq_0 ▸ mprecTypeR_eq_0 ▸ h.symm⟩

include hD hP hNd hOb in
theorem mpRecPi1 : ∃ u, F.IsDefEq 1 []
    (((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
    (((mpAux mpAuxNodeB).recType 1).substC (mpRestore.csubst (mpAux mpAuxNodeB) mpK))
    (.sort u) := by
  obtain ⟨u, h⟩ := VEnv.IsDefEq.mkPi_congrU (mpTeleDefEq₁ hD hP hNd hOb)
    (by simpa using mpOnCtx₁ hD hP hNd hOb) mpB₁
  exact ⟨u, mprecType_eq_1 ▸ mprecTypeR_eq_1 ▸ h.symm⟩

include hD hP hNd hOb in
/-- **The `const` clause's defeq disjunct at `MP.rec`**, level- and context-generic — `instL` plus
`weak0` over §18.2, exactly as `rRecConstClause0`. -/
theorem mpRecConstClause0 (henv : F.Ordered) {U : Nat} :
    ∀ {Γ : List VExpr} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = 1 →
      ∃ v, F.IsDefEq U Γ
        ((((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls)
        ((((mpAux mpAuxNodeB).recType 0).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls) (.sort v) := by
  intro Γ ls hls _
  obtain ⟨u, h⟩ := mpRecPi0 hD hP hNd hOb
  obtain ⟨v, h2⟩ : ∃ v, F.IsDefEq U []
      ((((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls)
      ((((mpAux mpAuxNodeB).recType 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls) (.sort v) := ⟨_, h.instL hls⟩
  exact ⟨v, h2.weak0 henv⟩

include hD hP hNd hOb in
theorem mpRecConstClause1 (henv : F.Ordered) {U : Nat} :
    ∀ {Γ : List VExpr} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = 1 →
      ∃ v, F.IsDefEq U Γ
        ((((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls)
        ((((mpAux mpAuxNodeB).recType 1).substC
          (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls) (.sort v) := by
  intro Γ ls hls _
  obtain ⟨u, h⟩ := mpRecPi1 hD hP hNd hOb
  obtain ⟨v, h2⟩ : ∃ v, F.IsDefEq U []
      ((((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls)
      ((((mpAux mpAuxNodeB).recType 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls) (.sort v) := ⟨_, h.instL hls⟩
  exact ⟨v, h2.weak0 henv⟩

include hD hP hNd hOb in
/-- **The `val` clause's datum at `_nested.MDep_1.rec ↦ MP.rec_1`** — one `constDF` at the renamed
recursor plus one `defeqDF` along §18.2.  Note the difference from `rNestedRecVal`: at `MP` the
substituted value is a **bare constant** (`mp_csubst_rec_val`), which is why §15.1 could say
"two β-lemmas" for the *bridge*; it changes nothing here. -/
theorem mpNestedRecVal (henv : F.Ordered)
    (hrec1 : F.constants ``MP.rec_1 = some
      ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩)
    {U : Nat} {Γ : List VExpr} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (hll : List.Forall₂ (· ≈ ·) ls ls') (hlen : ls.length = 1) :
    F.IsDefEq U Γ
      ((VExpr.const ``MP.rec_1 [.param 0]).instL ls)
      ((VExpr.const ``MP.rec_1 [.param 0]).instL ls')
      ((((mpAux mpAuxNodeB).recType 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)).instL ls) := by
  obtain ⟨v, hv⟩ := mpRecConstClause1 hD hP hNd hOb henv (U := U) (Γ := Γ) hls hlen
  have hlen' : ls'.length = 1 := List.Forall₂.length_eq hll ▸ hlen
  match ls, ls', hlen, hlen', hls, hls', hll, hv with
  | [_], [_], _, _, hls, hls', hll, hv =>
    exact hv.defeqDF (.constDF hrec1 hls hls' rfl hll)

end

/-! ### §18.3 The third staging pair, and `WFD` at it -/

theorem mp_fresh₃ {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (n : Name) (hn : n ∈ [``MP, mpNestedName, ``MP.obj, `_nested.MDep_1.node,
      ``MP.rec, `_nested.MDep_1.rec, ``MP.rec_1]) :
    env₁.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem mpAuxB_stagedE₃ {env₁ E₁ E₂ : VEnv}
    (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
    (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂) :
    ∃ E₃, E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  have hn' : n ∈ [``MP.rec, `_nested.MDep_1.rec] := by revert hn; revert n; decide
  rw [VEnv.addConstList_constants_of_not_mem hE₂
      (by show n ∉ [``MP.obj, `_nested.MDep_1.node]; revert hn'; revert n; decide),
    VEnv.addConstList_constants_of_not_mem hE₁
      (by show n ∉ [``MP, mpNestedName]; revert hn'; revert n; decide)]
  exact mp_fresh₃ h n (by revert hn'; revert n; decide)

theorem mpAuxB_stagedF₃ {env₁ F₁ F₂ : VEnv}
    (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
    (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
    (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂) :
    ∃ F₃, F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  have hn' : n ∈ [``MP.rec, ``MP.rec_1] := by revert hn; revert n; decide
  rw [VEnv.addConstList_constants_of_not_mem hF₂
      (by show n ∉ [``MP.obj]; revert hn'; revert n; decide),
    VEnv.addConstList_constants_of_not_mem hF₁
      (by show n ∉ [``MP]; revert hn'; revert n; decide)]
  exact mp_fresh₃ h n (by revert hn'; revert n; decide)

/-- **All seven staging environments exist together**, so nothing below is hypothetical. -/
theorem mp_stage₃_exists :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃ ∧
      env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ ∧
      F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ ∧
      F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃ := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩ := mp_stage₂_exists
  obtain ⟨E₃, hE₃⟩ := mpAuxB_stagedE₃ h hE₁ hE₂
  obtain ⟨F₃, hF₃⟩ := mpAuxB_stagedF₃ h hF₁ hF₂
  exact ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hE₃ : E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)
variable (hF₃ : F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃)

include h hE₁ hE₂ hF₁ hF₂ hF₃ in
theorem mpF₃_ordered : F₃.Ordered :=
  VEnv.addConstList_ordered (mpF₂_ordered h hE₁ hF₁ hF₂)
    (fun c hc => mpAuxB_recConstsR_wf h hE₁ hE₂ hF₁ hF₂ c hc) hF₃

include h hF₁ hF₂ hF₃ in
theorem mpF₃_mdep : F₃.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩ :=
  (VEnv.addConstList_le hF₃).constants (mpF₂_mdep h hF₁ hF₂)

include h hF₁ hF₂ hF₃ in
theorem mpF₃_mdepNode : F₃.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩ :=
  (VEnv.addConstList_le hF₃).constants (mpF₂_mdepNode h hF₁ hF₂)

include hF₁ hF₂ hF₃ in
theorem mpF₃_mp : F₃.constants ``MP
    = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  (VEnv.addConstList_le hF₃).constants (mpF₂_mp hF₁ hF₂)

include hF₂ hF₃ in
theorem mpF₃_obj : F₃.constants ``MP.obj
    = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩ :=
  (VEnv.addConstList_le hF₃).constants (mp_objType_eq ▸ mpF₂_obj hF₂)

include hF₃ in
theorem mpF₃_rec : F₃.constants ``MP.rec
    = some ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩ :=
  VEnv.addConstList_constants hF₃
    (``MP.rec, ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 0).substC
      (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩) (by exact List.Mem.head _)

include hF₃ in
theorem mpF₃_rec1 : F₃.constants ``MP.rec_1
    = some ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
        (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩ :=
  VEnv.addConstList_constants hF₃
    (``MP.rec_1, ⟨1, ((mpAux mpAuxNodeB).recTypeR mpRestore 1).substC
      (mpRestore.csubst (mpAux mpAuxNodeB) mpK)⟩) (by exact List.Mem.tail _ (List.Mem.head _))

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **`hσ` at the ι-rule stage of the parameterised REDEX block** — obligation (C)'s environment
hypothesis.  `CSubst.WFD.mono` carries the whole of `mp_csubst_WFD₂` from `F₂` to `F₃`, so the only
new cases are the two constants stage 3 *declares*: `const` at `MP.rec` (§18.2's defeq disjunct)
and `val` at `_nested.MDep_1.rec` (which was `exfalso` at stage 2). -/
theorem mp_csubst_WFD₃ : (mpRestore.csubst (mpAux mpAuxNodeB) mpK).WFD E₃ F₃ 1 := by
  have hFo := mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃
  have hσ₂ := (mp_csubst_WFD₂ h hE₁ hE₂ hF₁ hF₂).mono (VEnv.addConstList_le hF₃)
  have hD := mpF₃_mdep h hF₁ hF₂ hF₃
  have hP := mpF₃_mp hF₁ hF₂ hF₃
  have hNd := mpF₃_mdepNode h hF₁ hF₂ hF₃
  have hOb := mpF₃_obj hF₂ hF₃
  refine ⟨mp_csubst_closed, ?_, ?_, ?_⟩
  · intro c ci hn hc
    by_cases hR : c = ``MP.rec
    · subst hR
      rw [VEnv.addConstList_constants hE₃ (``MP.rec, ⟨1, (mpAux mpAuxNodeB).recType 0⟩)
        (by exact List.Mem.head _)] at hc
      cases hc
      exact ⟨_, mpF₃_rec hF₃, .inr fun hls hlen =>
        mpRecConstClause0 hD hP hNd hOb hFo hls hlen⟩
    · have hm : c ∉ ((mpAux mpAuxNodeB).recConsts.map (·.1)) := by
        show c ∉ [``MP.rec, `_nested.MDep_1.rec]
        simp [hR, (mp_csubst_ne hn).2.1]
      rw [VEnv.addConstList_constants_of_not_mem hE₃ hm] at hc
      exact hσ₂.const hn hc
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₃] at hdf
    exact hσ₂.defeq hdf
  · intro c t ci Γ ls ls' hσv hc
    have hR : c ≠ ``MP.rec := by
      rintro rfl
      rw [show mpRestore.csubst (mpAux mpAuxNodeB) mpK ``MP.rec = none from rfl] at hσv
      exact absurd hσv nofun
    by_cases hr1 : c = `_nested.MDep_1.rec
    · subst hr1
      rw [mp_csubst_rec_val] at hσv
      cases hσv
      rw [VEnv.addConstList_constants hE₃
        (`_nested.MDep_1.rec, ⟨1, (mpAux mpAuxNodeB).recType 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc
      cases hc
      intro hls hls' hll hlen
      exact mpNestedRecVal hD hP hNd hOb hFo (mpF₃_rec1 hF₃) hls hls' hll hlen
    · have hm : c ∉ ((mpAux mpAuxNodeB).recConsts.map (·.1)) := by
        show c ∉ [``MP.rec, `_nested.MDep_1.rec]
        simp [hR, hr1]
      rw [VEnv.addConstList_constants_of_not_mem hE₃ hm] at hc
      exact hσ₂.val hσv hc

end

/-! ### §18.4 `hdata`, and obligation (C) DISCHARGED at the parameterised REDEX block -/

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hD hP hNd hOb in
/-- **`hdata` at `MP`** — the block has **two** ι-rules to `NTree`'s three, and §17.2 supplies both
triples. -/
theorem mpAuxB_hdata :
    ∀ (q j : Nat) (C : VIndCtor), (mpAux mpAuxNodeB).ctorsAll[q]? = some (j, C) →
      mpRestore.IotaHargs (mpAux mpAuxNodeB) (mpRestore.csubst (mpAux mpAuxNodeB) mpK) F j C := by
  intro q j C hq
  rw [mpAuxB_ctorsAll_eq] at hq
  match q with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact mpIotaHargs_obj hD hP hNd hOb
  | 1 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact mpIotaHargs_node hD hP hNd hOb
  | (n+2) => simp at hq

end

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' mrDepDecl = some env₁)
variable (hE₁ : env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁)
variable (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
variable (hE₃ : E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃)
variable (hF₁ : env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁)
variable (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)
variable (hF₃ : F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃)

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **OBLIGATION (C) AT THE PARAMETERISED REDEX BLOCK, DISCHARGED.**  The counterpart of
`InductiveDeclExamples.ntreeAux_iotaRulesRS_wf` at a block that is **not** `Canonical`. -/
theorem mpAuxB_iotaRulesRS_wf :
    ∀ df ∈ (mpAux mpAuxNodeB).iotaRulesRS mpRestore mpK, VDefEq.WF F₃ df :=
  VEnv.iotaRulesRS_wf_of_hargsD mpRestore_ownId mpRestore_domSep.substAt
    mpRestore_substFree mp_csubst_closed
    (mp_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃)
    (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃) mpAuxB_recArg_lt
    (mpAuxB_hdata (mpF₃_mdep h hF₁ hF₂ hF₃) (mpF₃_mp hF₁ hF₂ hF₃)
      (mpF₃_mdepNode h hF₁ hF₂ hF₃) (mpF₃_obj hF₂ hF₃))

end

/-- …**with nothing assumed** — the (C) counterpart of `mpAuxB_obligationB`. -/
theorem mpAuxB_obligationC :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃ ∧
      env₁.addConstList ((mpAux mpAuxNodeB).typeConstsC mpK) = some F₁ ∧
      F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂ ∧
      F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃ ∧
      (∀ df ∈ (mpAux mpAuxNodeB).iotaRulesRS mpRestore mpK, VDefEq.WF F₃ df) := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := mp_stage₃_exists
  exact ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃,
    mpAuxB_iotaRulesRS_wf h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃⟩

/-! ### §18.5 …so the nested declaration step preserves `Ordered` at a NON-CANONICAL block

`VEnv.addInductR_ordered'` has exactly three open obligations, and all three are now theorems at
`mpAux mpAuxNodeB`:

| obligation | at `MP` |
|---|---|
| `hctors` (A) | `mpAuxB_ctorConstsCR_wf` (§13) |
| `hrecs` (B) | `mpAuxB_recConstsR_wf` (§16) |
| `hrules` (C) | `mpAuxB_iotaRulesRS_wf` (§18.4) |

Until now the only blocks with all three were `nfnAux` (`np = 0`) and `ntreeAux` (`np = 1`,
**`Canonical`**).  `mpAux mpAuxNodeB` is neither: `mpAuxB_not_canonical`. -/

theorem mpAuxB_admitted {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    ∃ env₂, env₁.addInductR (mpAux mpAuxNodeB) mpK mpRestore = some env₂ := by
  refine VEnv.addInductR_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
  refine mp_fresh₃ h n ?_
  revert hn; revert n; decide

theorem mpAuxB_stages {env₁ : VEnv} (h : VEnv.empty.addInduct' mrDepDecl = some env₁) :
    ∃ E₁ E₂ E₃, env₁.addIndTypes (mpAux mpAuxNodeB) = some E₁ ∧
      E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂ ∧
      E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃ := by
  have hx : ∃ env', env₁.addInduct' (mpAux mpAuxNodeB) = some env' := by
    refine VEnv.addInduct'_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
    refine mp_fresh₃ h n ?_
    revert hn; revert n; decide
  obtain ⟨env', he⟩ := hx
  obtain ⟨E₁, E₂, E₃, h1, h2, h3, -⟩ := VEnv.addInduct'_stages he
  exact ⟨E₁, E₂, E₃, h1, h2, h3⟩

/-- **THE NESTED DECLARATION STEP PRESERVES `VEnv.Ordered` AT A NON-CANONICAL (REDEX) BLOCK.**
`ntreeAux_addInductR_ordered` at a block whose companion constructor stores a β-redex — the
configuration `MRedex`/`StoredIota`/§§1–10 of this file were built to reach. -/
theorem mpAuxB_addInductR_ordered :
    ∃ env₁ env', VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addInductR (mpAux mpAuxNodeB) mpK mpRestore = some env' ∧ env'.Ordered := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' mrDepDecl = some e := ⟨_, rfl⟩
  obtain ⟨env', he⟩ := mpAuxB_admitted h
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃⟩ := mpAuxB_stages h
  refine ⟨env₁, env', h, he, ?_⟩
  refine VEnv.addInductR_ordered' (mpEnv_ordered h) mpAuxB_WF mpRestore_ownId
    (fun {F₁} hF₁ => ?_) (fun {F₁ F₂} hF₁ hF₂ => ?_) (fun {F₁ F₂ F₃} hF₁ hF₂ hF₃ => ?_) he
  · exact mpAuxB_ctorConstsCR_wf h hE₁ hF₁
  · exact mpAuxB_recConstsR_wf h hE₁ hE₂ hF₁ hF₂
  · exact mpAuxB_iotaRulesRS_wf h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃

/-! ### §18.6 Anti-vacuity for (C) at `MP`: the strict `CSubst.WF` is FALSE at the ι-rule pair too

§15's `mp_csubst_WF₂_false` refutes it at the *constructor* pair; the same disagreement survives
both `addConstList`s, so `mp_csubst_WFD₃` is not a convenience either. -/

theorem mp_csubst_WF₃_false {E₁ E₂ E₃ F₁ F₂ F₃ : VEnv} {U : Nat}
    (hE₂ : E₁.addIndCtors (mpAux mpAuxNodeB) = some E₂)
    (hE₃ : E₂.addIndRecs (mpAux mpAuxNodeB) = some E₃)
    (hF₂ : F₁.addConstList ((mpAux mpAuxNodeB).ctorConstsCR mpRestore mpK) = some F₂)
    (hF₃ : F₂.addConstList ((mpAux mpAuxNodeB).recConstsR mpRestore mpK) = some F₃) :
    ¬ (mpRestore.csubst (mpAux mpAuxNodeB) mpK).WF E₃ F₃ U :=
  VEnv.subst_WF_false_of_const_ne
    ((VEnv.addConstList_le hE₃).constants
      (VEnv.addConstList_constants hE₂ (``MP.obj, ⟨0, mpObj.type (mpAux mpAuxNodeB) 0⟩)
        (by exact List.Mem.head _)))
    ((VEnv.addConstList_le hF₃).constants
      (VEnv.addConstList_constants hF₂
        (``MP.obj, ⟨0, (mpObj.typeR (mpAux mpAuxNodeB) mpRestore 0).substC
          (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)⟩) (by exact List.Mem.head _)))
    mp_csubst_obj_none (fun hh => mp_const_clause_ne (hh.symm.trans mp_obj_declared))

end MPWit
end MRedex
end Lean4Lean
