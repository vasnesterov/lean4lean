import Lean4Lean.Theory.Inductive.MemberRedex
import Lean4Lean.Theory.Inductive.NestedTele

/-!
# Ruling 122e's anti-vacuity certificate: the iota layer, at a block where `Canonical` is FALSE

`Theory/Inductive/NestedRules.lean` §7.5–§7.7 and `Theory/Inductive/NestedTele.lean` §T12/§T15
used to carry `hcanon : D.Canonical` (or `C.Canonical D`).  Ledger row 122d measured that
hypothesis **false at the block level** for every real nested inductive in the running
environment — `Lean.Json`, `Lean.PrefixTreeNode` and `MRedex.MRWit.MJ` — so every one of those
statements was **vacuous** there, and the `D.Canonical` conjunct of the `AddInductive.run`
specification was **unsatisfiable** for them.  Ruling 122e's answer: restate the layer over the
**stored** telescope, the way `VIndField.typeR`'s `some` branch was restated one layer in under
ruling 116d.  That is done; `VIndRestore.substC_atRec_restore` is the engine.

**This file is the check that removing a false hypothesis did not buy vacuity somewhere else.**
Removing a conjunct because nothing satisfies it is only progress if what is left has content at
the very instance the conjunct excluded.  So every hypothesis of the restated layer is discharged
here **at `mrAux mrAuxNodeB`** — `MRedex.MRWit`'s reproduction of `MJ`'s auxiliary block, the
block whose companion constructor stores the β-redex `(fun x : Prop => MJ) #0` and at which
`MRWit.mr_auxNodeB_block_not_canonical` refutes `Canonical`.  Then the restated equations are
instantiated there, and §3 says which of them have content there and which do not.

## What is certified, and what is not

* **Certified.** At `mrAux mrAuxNodeB` the seven side conditions hold (`§1`), and the restated
  field-telescope equation, obligation (B) and obligation (C) all hold there (`§2`).  So the
  restated statements are *strictly stronger* than the ones they replace: same conclusions,
  satisfiable hypotheses, at a block where the old hypotheses were unsatisfiable.
* **Certified, and it is the part that could have been left out.** §3 grades the three equations
  for degeneracy and one of them **is** degenerate: at the *companion* constructor `mrAuxNodeB`
  the restoration is the **identity** on the field telescope, because the redex's head is the
  block's own member and `OwnId` freezes the own member.  That is not a defect of the block — it
  is a general fact about the redex the elimination manufactures (`β k` with `β := fun _ => I`
  for `I` the own member) — so the redex field is precisely where restoration does nothing.  The
  same block's *user* constructor `mrObj` does exercise the moving case
  (`mr_objFieldTypesR_ne_fields`), and (B)/(C) are not identities either.
* **Not certified.** Nothing here says `mrAux mrAuxNodeB` is *well-formed* (`D.WF env`) or that
  its `Built` clauses hold — those are `MemberRedex.lean` §5/§8's business and `Built.fields_noK`
  still has no producer but `decide` (ledger row 117c).  The certificate is about the **syntactic**
  side conditions of the iota layer, which are exactly the ones `hcanon` sat among.
* **Not certified.** The parameterised (`D.np > 0`) route's per-field defeq. §T15.7's `hrec` is
  now stated over the stored type, which is what makes it *statable* at a redex field, but the
  producer for a redex field is a β step and lives in `MemberRedex.lean`
  (`MRedex.MRWit.mr_pos_beta`), not here.
* **The ruling's scope, checked.** §4 shows obligation **(A)** needed no restatement: its
  `hcanon` is consumed only through `D.CanonicalOwn K`, which quantifies over the members
  *outside* `K`, and `CanonicalOwn` **holds** at this very block (`mrAuxB_canonicalOwn`) while
  `Canonical` fails.  So the layer ruling 122e restated is exactly the layer that needed it.
-/

namespace Lean4Lean
namespace MRedex
namespace MRWit

open Lean (Name)

/-! ## §1 The seven side conditions, at the redex block

`mrAux mrAuxNodeB` is `[MJ, _nested.MDep_1]` with the companion's field `1` stored as
`mrRedex = (fun x : Prop => MJ) #0` and *recorded as recursive* (that is what `mrAuxNodeB` is:
`fieldB`'s reading, which is now `VNestedOcc.field`'s).  Every condition below is `rfl`/`decide`
or a two-line case split; the point is not that they are hard but that they are **jointly
satisfiable at this block**, which `D.Canonical` is not. -/

theorem mrAuxB_params_nil : (mrAux mrAuxNodeB).params = [] := rfl

theorem mrAuxB_np_zero : (mrAux mrAuxNodeB).np = 0 := rfl

theorem mrAuxB_blockNames : (mrAux mrAuxNodeB).blockNames = [``MJ, mrNestedName] := rfl

theorem mrAuxB_blockNames_nodup : (mrAux mrAuxNodeB).blockNames.Nodup := by decide

theorem mrAuxB_ctorsAll_eq : (mrAux mrAuxNodeB).ctorsAll = [(0, mrObj), (1, mrAuxNodeB)] := rfl

/-- **`OwnId`.**  `MJ` — the member the step declares — is renamed to nothing, re-levelled to
nothing and re-instantiated at nothing; only `_nested.MDep_1` moves. -/
theorem mrRestore_ownId : mrRestore.OwnId (mrAux mrAuxNodeB) mrK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mrAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mrAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mrAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mrAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [mrAux] at hT

/-- **`hcl0`.**  The presented spine is `[Prop, fun _ : Prop => MJ]`, both closed. -/
theorem mrRestore_tyArgs_closed0 : ∀ i, ∀ a ∈ mrRestore.tyArgs i, a.ClosedN 0 := by
  intro i a ha
  by_cases h : i = 1
  · rw [show mrRestore.tyArgs i
        = [.sort .zero, .lam (.sort .zero) (.const ``MJ [])] from by simp [mrRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · trivial
    · exact ⟨trivial, trivial⟩
  · rw [show mrRestore.tyArgs i = [] from by simp [mrRestore, h]] at ha
    exact absurd ha nofun

theorem mrRestore_domNodup : mrRestore.DomNodup (mrAux mrAuxNodeB) mrK := by
  show ((mrRestore.csubstList (mrAux mrAuxNodeB) mrK).map (·.1)).Nodup
  show ([`_nested.MDep_1, `_nested.MDep_1.rec, `_nested.MDep_1.node] : List Name).Nodup
  decide

/-- The domain is the three auxiliary names, and it is **not** empty — so `SubstAt`'s `some`
clauses have something to say at this block. -/
theorem mr_csubstList_dom :
    (mrRestore.csubstList (mrAux mrAuxNodeB) mrK).map (·.1)
      = [`_nested.MDep_1, `_nested.MDep_1.rec, `_nested.MDep_1.node] := rfl

theorem mrAuxB_allNames_nodup : (mrAux mrAuxNodeB).allNames.Nodup := by decide

theorem mrRestore_domSep : mrRestore.DomSep (mrAux mrAuxNodeB) mrK :=
  VIndRestore.domSep_of_allNames_nodup mrAuxB_allNames_nodup mrRestore_domNodup

/-! ### `SubstFree`, field by field

Four separate theorems rather than one `decide` on the structure: a structure-level decision can
be green while one field is vacuous, which is ledger blindness 7 at the level of a conjunction. -/

theorem mr_substFree_tyName :
    ∀ j, mrRestore.csubst (mrAux mrAuxNodeB) mrK (mrRestore.tyName j) = none := by
  intro j; by_cases h : j = 1 <;> simp only [mrRestore, h] <;> rfl

theorem mr_substFree_tyArgs : ∀ j, ∀ a ∈ mrRestore.tyArgs j,
    a.NoCSubst (mrRestore.csubst (mrAux mrAuxNodeB) mrK) := by
  intro j a ha
  by_cases h : j = 1
  · rw [show mrRestore.tyArgs j
        = [.sort .zero, .lam (.sort .zero) (.const ``MJ [])] from by simp [mrRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · trivial
    · exact ⟨trivial, (rfl : mrRestore.csubst (mrAux mrAuxNodeB) mrK ``MJ = none)⟩
  · rw [show mrRestore.tyArgs j = [] from by simp [mrRestore, h]] at ha
    exact absurd ha nofun

/-- The clause `VIndRestore.KeysFree` does **not** supply: quantified over every member index,
including the junk ones above `nm`. -/
theorem mr_substFree_recName : ∀ j, mrRestore.csubst (mrAux mrAuxNodeB) mrK
    (mrRestore.recName (Lean.mkRecName ((mrAux mrAuxNodeB).types.getD j default).name))
      = none := by
  rintro (_ | _ | j)
  · rfl
  · rfl
  · exact (rfl : mrRestore.csubst (mrAux mrAuxNodeB) mrK
      (mrRestore.recName (Lean.mkRecName (default : VIndType).name)) = none)

theorem mr_substFree_ctorName : ∀ (j : Nat) (T : VIndType),
    (mrAux mrAuxNodeB).types[j]? = some T → ∀ C ∈ T.ctors,
      mrRestore.csubst (mrAux mrAuxNodeB) mrK (mrRestore.ctorName C.name) = none := by
  rintro (_ | _ | j) T hT C hC
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · simp [mrAux] at hT

theorem mrRestore_substFree :
    mrRestore.SubstFree (mrAux mrAuxNodeB) (mrRestore.csubst (mrAux mrAuxNodeB) mrK) :=
  ⟨mr_substFree_tyName, mr_substFree_tyArgs, mr_substFree_recName, mr_substFree_ctorName⟩

/-! ### The index bound, which survives — and the canonicity, which does not -/

/-- **`hpos` holds at the redex block.**  This is the discriminating measurement: `hpos` and
`hcanon` were introduced together and always quoted together, and only one of them is true here.
The redex field's `recArg` is `⟨[], 0, []⟩` — index `0 < 2`, empty binder telescope — so the
index bound is fine; what fails is `F.type = r.canonType D 1`, because `F.type` is an
application and `canonType` never is (`MRedex.canonType_ne_of_lamHead`). -/
theorem mrAuxB_pos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ (mrAux mrAuxNodeB).ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < (mrAux mrAuxNodeB).nm ∧
        ∀ B ∈ r.binders, (mrAux mrAuxNodeB).NoBlock B := by
  intro t C h
  rw [mrAuxB_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · rintro (_ | i) F r hF hr
    · cases hF; cases hr; exact ⟨by decide, nofun⟩
    · simp [mrObj] at hF
  · rintro (_ | _ | i) F r hF hr
    · cases hF; exact absurd hr nofun
    · cases hF; cases hr; exact ⟨by decide, nofun⟩
    · simp [mrAuxNodeB] at hF

/-- …and the hypothesis ruling 122e removed is **false** at this very block.  Restated here as a
one-liner so §2's theorems and their refuted predecessor sit side by side. -/
theorem mrAuxB_not_canonical : ¬ (mrAux mrAuxNodeB).Canonical :=
  mr_auxNodeB_block_not_canonical

/-! ## §2 The restated layer, instantiated at the redex block

Each theorem below was **vacuous at this block** before ruling 122e and is a fact about it now.
That is the whole content of the ruling, and it is machine-checked rather than argued. -/

/-- **The field-telescope equation** (`VIndRestore.substC_atRec_fieldTypes`, `hcanon`/`hpos`
dropped) at the redex constructor.  This is the equation whose old proof went through
`typeR_canonical`, i.e. through the false hypothesis. -/
theorem mr_fieldTypes_bridge_nodeB :
    ((mrAux mrAuxNodeB).atRecTele (mrAuxNodeB.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      = ((mrAux mrAuxNodeB).atRecTele (mrAuxNodeB.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) :=
  VIndRestore.substC_atRec_fieldTypes mrAuxB_params_nil mrAuxB_blockNames_nodup
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- **…and at the user's constructor `MJ.obj`**, whose single recursive field the restoration
genuinely moves (`mr_objFieldTypesR_ne_fields`).  This is the non-degenerate instance of the
same equation, at the same block. -/
theorem mr_fieldTypes_bridge_obj :
    ((mrAux mrAuxNodeB).atRecTele (mrObj.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      = ((mrAux mrAuxNodeB).atRecTele (mrObj.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) :=
  VIndRestore.substC_atRec_fieldTypes mrAuxB_params_nil mrAuxB_blockNames_nodup
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- **Obligation (B) at the redex block** — `VEnv.recConstsR_wf_of_np_zero`'s `hbridge`. -/
theorem mr_recTypeR_bridge (j : Nat) (T : VIndType)
    (hT : (mrAux mrAuxNodeB).types[j]? = some T) :
    ((mrAux mrAuxNodeB).recType j).substC (mrRestore.csubst (mrAux mrAuxNodeB) mrK)
      = ((mrAux mrAuxNodeB).recTypeR mrRestore j).substC
          (mrRestore.csubst (mrAux mrAuxNodeB) mrK) :=
  VIndRestore.csubst_recType_eq mrAuxB_params_nil mrAuxB_blockNames_nodup mrRestore_ownId
    mrRestore_domSep mrRestore_tyArgs_closed0 mrRestore_substFree j T hT

/-- **Obligation (C) at the redex block** — `VEnv.iotaRulesRS_wf_of_np_zero`'s `hbridge`. -/
theorem mr_iotaRules_bridge :
    (mrAux mrAuxNodeB).iotaRules.map (·.substC (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      = (mrAux mrAuxNodeB).iotaRulesRS mrRestore mrK :=
  VIndRestore.csubst_iotaRules_eq mrAuxB_params_nil mrAuxB_blockNames_nodup mrRestore_ownId
    mrRestore_domSep mrRestore_tyArgs_closed0 mrRestore_substFree mrAuxB_pos

/-- **…and the same for the two `TeleDefEq` certificates `NestedTele.lean` binds.**  §T6's
`hfld` at the redex constructor. -/
theorem mr_teleDefEq_fld {env : VEnv} {U q : Nat} {Γ : List VExpr} :
    env.TeleDefEq U Γ
      (VExpr.liftTele ((mrAux mrAuxNodeB).nm + q)
        (((mrAux mrAuxNodeB).atRecTele (mrAuxNodeB.fields.map (·.type))).map
          (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))))
      (VExpr.liftTele ((mrAux mrAuxNodeB).nm + q)
        (((mrAux mrAuxNodeB).atRecTele
            (mrAuxNodeB.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
          (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))) :=
  VIndRestore.teleDefEq_fld_of_np_zero mrAuxB_params_nil mrAuxB_blockNames_nodup
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- §T15.4's `htele` at the redex block. -/
theorem mr_iotaCtx_teleDefEq {env : VEnv} {j : Nat} {T : VIndType}
    (hT : (mrAux mrAuxNodeB).types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    env.TeleDefEq (mrAux mrAuxNodeB).recUvars []
      (((mrAux mrAuxNodeB).iotaCtx C).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))
      (((mrAux mrAuxNodeB).iotaCtxR mrRestore C).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))) :=
  VIndRestore.iotaCtx_teleDefEq_of_np_zero mrAuxB_params_nil mrAuxB_blockNames_nodup
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree
    (VIndRestore.csubst_closed' mrAuxB_params_nil mrRestore_tyArgs_closed0) hT hC

/-- **`fieldTypesR_closedTele` at the redex constructor** — the `Canonical`-free restatement of
§T12.1's side condition 1, which used to route through `canonTypeR_closedN` and therefore
through `typeR_canonical`. -/
theorem mr_fieldTypesR_closedTele :
    VExpr.ClosedTele (mrAuxNodeB.fieldTypesR (mrAux mrAuxNodeB) mrRestore)
      (mrAux mrAuxNodeB).np :=
  VIndCtor.fieldTypesR_closedTele
    (fun j a ha => by
      have := mrRestore_tyArgs_closed0 j a ha
      rw [mrAuxB_np_zero]; exact this)
    (by rw [mrAuxB_np_zero]; simp [VExpr.ClosedTele, VExpr.ClosedN, mrAuxNodeB, mrRedex])

/-! ## §3 What is and is not degenerate here — the honest reading

A bridge that is `rfl` certifies nothing about the restoration, so this section grades each of
§2's equations.  **One of them is degenerate**, and it is recorded rather than glossed. -/

/-- The companion's field `1` really is the redex, and it really is recorded as recursive — so
`fieldTypesR` enters `typeR`'s `some` branch here, and `substC_atRec_restore` is exercised rather
than falling through the `none` branch. -/
theorem mr_fieldTypesR_hits_some_branch :
    (mrAuxNodeB.fields.getD 1 default).recArg = some ⟨[], 0, []⟩ ∧
      (mrAuxNodeB.fields.getD 1 default).type = mrRedex :=
  ⟨rfl, rfl⟩

/-- **But the restoration is the IDENTITY on the companion constructor's field telescope**, so
`mr_fieldTypes_bridge_nodeB` is degenerate — and the reason generalises, which is why it is worth
having in the tree.

The redex's head is `MJ`, the block's **own** member, and `OwnId` freezes the own member: the
trigger fires (`k = 2`, `D.np = 0`, so `bvars 2 0 = []` matches) and `tyAppR` at member `0`
rebuilds `const MJ []` unchanged.  And that is not an accident of this witness: the redex
`ElimNestedInductive` manufactures is `β k` where the nested instance supplies
`β := fun _ => I` with `I` the **own** member (`Theory/Inductive/Restore.lean`'s
`VIndCtor.Canonical` docstring; `Lean.Json` and `Lean.PrefixTreeNode` are the same shape), so at
*every* redex field the restoration is the identity.

**Consequence, stated rather than left implicit:** a redex block does not witness that
`substC_atRec_restore`'s `some` branch carries content.  `mr_objFieldTypesR_ne_fields` below
does, at the same block. -/
theorem mr_auxFieldTypesR_eq_fields :
    mrAuxNodeB.fieldTypesR (mrAux mrAuxNodeB) mrRestore = mrAuxNodeB.fields.map (·.type) := by
  decide

/-- **…and the same block's user constructor is the non-degenerate case.**  `MJ.obj`'s single
field is stored as the companion constant `_nested.MDep_1` and restored to
`MDep Prop (fun _ => MJ)`, so `mr_fieldTypes_bridge_obj` is an equation between two *different*
telescopes that `σ` identifies — `substC_atRec_restore`'s `some` branch doing real work, at a
block where the deleted `hcanon` was false. -/
theorem mr_objFieldTypesR_ne_fields :
    mrObj.fieldTypesR (mrAux mrAuxNodeB) mrRestore ≠ mrObj.fields.map (·.type) := by decide

/-- **Obligation (B) is not an identity at this block.**  The block's own recursor type for the
companion member and its restored form are different expressions; `mr_recTypeR_bridge` says `σ`
identifies them.  This is the (B)-level counterpart of `mr_recTypeR_ne`, which compares the two
*readings* of the field rather than the two sides of the bridge. -/
theorem mr_recTypeR_ne_recType :
    (mrAux mrAuxNodeB).recTypeR mrRestore 1 ≠ (mrAux mrAuxNodeB).recType 1 := by decide

/-- **Obligation (C) is not an identity either**: the ι-rules the step registers do not even have
the same *keys* as the block's own, so `mr_iotaRules_bridge` transports rules across a rename. -/
theorem mr_iotaRules_keys_move :
    (mrAux mrAuxNodeB).iotaRules.map VDefEq.key
      ≠ ((mrAux mrAuxNodeB).iotaRulesRS mrRestore mrK).map VDefEq.key := by decide

/-! ## §4 Obligation (A) needed no restatement — and here is why, at the same block

Ruling 122e targeted the (B)/(C) layer.  That scope was exactly right, and the reason is
measurable here rather than argued: Part 4b's (A) bridge
(`VIndRestore.ctorType_substC_eq_typeR_substC`, `Theory/Inductive/RestoreBridge.lean`) still
carries `hcanon : C.Canonical D`, and it is **not** vacuous at this block, because its only
consumer — `VEnv.ctorConstsCR_wf_of_np_zero'` — asks for `D.CanonicalOwn K`, which quantifies
over the members **outside** `K`, i.e. over the ones the step declares.

At `mrAux mrAuxNodeB` the redex lives in the **companion** constructor; the *own* constructor
`MJ.obj` is stored canonically on the nose.  So `CanonicalOwn` holds at the very block where
`Canonical` fails, and (A) keeps its content.  This is row 122d's "index 0 still carries real
content", machine-checked at the block rather than read off the shape of the proof. -/

/-- **(A)'s hypothesis at the user's constructor: TRUE.**  `MJ.obj`'s single recursive field is
stored as `const _nested.MDep_1 []`, which is `r.canonType D 0` on the nose (`D.np = 0`, so
`tyApp 1 0 [] = const _nested.MDep_1 []`). -/
theorem mrObj_canonical : mrObj.Canonical (mrAux mrAuxNodeB) := by
  rintro (_ | i) F r hF hr
  · cases hF; cases hr; rfl
  · simp [mrObj] at hF

/-- **…and therefore `CanonicalOwn` holds at the redex block**, while `Canonical` does not
(`mrAuxB_not_canonical`).  The companion index is discharged by `absurd … hK`, which is correct
and is the point: the companion is exactly where the kernel stores something non-canonical, and
`CanonicalOwn` does not ask about it. -/
theorem mrAuxB_canonicalOwn : (mrAux mrAuxNodeB).CanonicalOwn mrK := by
  intro j C h hK
  rw [mrAuxB_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · exact mrObj_canonical
  · exact absurd (by decide) hK

end MRWit
end MRedex
end Lean4Lean
