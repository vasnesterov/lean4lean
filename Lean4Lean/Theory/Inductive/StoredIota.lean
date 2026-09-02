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
* **Certified, and it corrects the handoff.** §5 (added after the first version of this file)
  closes §T15.7's `hrec` at this block, at **both** constructors, and the answer is not the one
  the handoff predicted.  At the *redex* field the obligation is **empty** — the restoration is the
  identity there, generally, by the pre-existing `VIndRestore.restore_noK` — so no join to
  `MRedex.MRWit.mr_pos_beta` is needed (§5.1; the β route is exhibited in §5.3 and shown to cost
  strictly more).  At the *companion-pointing* field of `MJ.obj` the obligation is real and is
  **produced** from §T16.1 (§5.2), with the environment premises discharged in an actually
  constructed `Ordered` environment (§5.4).
* **The ruling's scope, checked.** §4 shows obligation **(A)** needed no restatement: its
  `hcanon` is consumed only through `D.CanonicalOwn K`, which quantifies over the members
  *outside* `K`, and `CanonicalOwn` **holds** at this very block (`mrAuxB_canonicalOwn`) while
  `Canonical` fails.  So the layer ruling 122e restated is exactly the layer that needed it.
-/

namespace Lean4Lean
namespace MRedex
namespace MRWit

open Lean (Name)

/-! ## §1 The side conditions, at the redex block

`mrAux mrAuxNodeB` is `[MJ, _nested.MDep_1]` with the companion's field `1` stored as
`mrRedex = (fun x : Prop => MJ) #0` and *recorded as recursive* (that is what `mrAuxNodeB` is:
`fieldB`'s reading, which is now `VNestedOcc.field`'s).  Every condition below is `rfl`/`decide`
or a two-line case split; the point is not that they are hard but that they are **jointly
satisfiable at this block**, which `D.Canonical` is not. -/

theorem mrAuxB_params_nil : (mrAux mrAuxNodeB).params = [] := rfl

theorem mrAuxB_np_zero : (mrAux mrAuxNodeB).np = 0 := rfl

theorem mrAuxB_blockNames : (mrAux mrAuxNodeB).blockNames = [``MJ, mrNestedName] := rfl

/-- `hnd`.  **No longer a hypothesis of the iota layer at all**: it was dead through §7.5–§7.7 of
`NestedRules.lean` and §T12/§T15's `np = 0` route (it was used by exactly one step,
`typeR_canonical`, which ruling 122e deleted), and it has now been removed from those eleven
statements.  It survives here because §5.2's `substC_atRec_stored_defeq_of_canonical` genuinely
reads it, through `restore_canonType`. -/
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
  VIndRestore.substC_atRec_fieldTypes mrAuxB_params_nil
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- **…and at the user's constructor `MJ.obj`**, whose single recursive field the restoration
genuinely moves (`mr_objFieldTypesR_ne_fields`).  This is the non-degenerate instance of the
same equation, at the same block. -/
theorem mr_fieldTypes_bridge_obj :
    ((mrAux mrAuxNodeB).atRecTele (mrObj.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      = ((mrAux mrAuxNodeB).atRecTele (mrObj.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) :=
  VIndRestore.substC_atRec_fieldTypes mrAuxB_params_nil
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- **Obligation (B) at the redex block** — `VEnv.recConstsR_wf_of_np_zero`'s `hbridge`. -/
theorem mr_recTypeR_bridge (j : Nat) (T : VIndType)
    (hT : (mrAux mrAuxNodeB).types[j]? = some T) :
    ((mrAux mrAuxNodeB).recType j).substC (mrRestore.csubst (mrAux mrAuxNodeB) mrK)
      = ((mrAux mrAuxNodeB).recTypeR mrRestore j).substC
          (mrRestore.csubst (mrAux mrAuxNodeB) mrK) :=
  VIndRestore.csubst_recType_eq mrAuxB_params_nil mrRestore_ownId
    mrRestore_domSep mrRestore_tyArgs_closed0 mrRestore_substFree j T hT

/-- **Obligation (C) at the redex block** — `VEnv.iotaRulesRS_wf_of_np_zero`'s `hbridge`. -/
theorem mr_iotaRules_bridge :
    (mrAux mrAuxNodeB).iotaRules.map (·.substC (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      = (mrAux mrAuxNodeB).iotaRulesRS mrRestore mrK :=
  VIndRestore.csubst_iotaRules_eq mrAuxB_params_nil mrRestore_ownId
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
  VIndRestore.teleDefEq_fld_of_np_zero mrAuxB_params_nil
    mrRestore_ownId mrRestore_domSep.substAt mrRestore_tyArgs_closed0 mrRestore_substFree

/-- §T15.4's `htele` at the redex block. -/
theorem mr_iotaCtx_teleDefEq {env : VEnv} {j : Nat} {T : VIndType}
    (hT : (mrAux mrAuxNodeB).types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    env.TeleDefEq (mrAux mrAuxNodeB).recUvars []
      (((mrAux mrAuxNodeB).iotaCtx C).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))
      (((mrAux mrAuxNodeB).iotaCtxR mrRestore C).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))) :=
  VIndRestore.iotaCtx_teleDefEq_of_np_zero mrAuxB_params_nil
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

/-! ## §5 §T15.7's `hrec` at the redex field: the obligation is **EMPTY**, not hard

The handoff (`docs/handoff-iota-stored.md` §10 item 1) named this as "the next real obligation on
the parameterised nested path" and priced it as a join from `MRedex.MRWit.mr_pos_beta`'s β step to
§T16.1's sorted `IsDefEq`.  **That is not the obligation, and the correction follows from this
file's own §3.**  At the redex field the restoration is the *identity*
(`mr_auxFieldTypesR_eq_fields`), so `hrec`'s two sides are the **same expression** and the entry
does not move.  `VEnv.TeleDefEq.of_entries'` charges nothing for an unchanged entry — that is the
property §T15.7's docstring is built around — so the honest statement of §T15.7 asks for a defeq
only where the entry moves, and at a redex field it asks for nothing.

The reason generalises off this witness, and the lemma was already in the tree:
`VIndRestore.restore_noK` (`Theory/Inductive/Restore.lean`) makes the restoration the identity on
any expression free of **companion** constants, and the manufactured redex `(fun _ => I) k` has
`I` the block's **own** member.  §T15.7's new `substC_atRec_fieldTypes_defeq_of_noK` is that
observation as a hypothesis-shape: `hrec` only at fields whose stored type mentions a companion.

**So `mr_pos_beta` is not the missing producer, and no join to it is required.**  §5.3 shows the
join is nonetheless *available* — the β step does deliver `hrec` in the unweakened shape — so the
route the handoff named is not closed, merely unnecessary. -/

/-- The redex field's stored type mentions no **companion** constant: its only constant is `MJ`,
the member the step declares.  (Not `decide`: `VExpr.NoConsts` has no `Decidable` instance.) -/
theorem mr_redex_noK : VExpr.NoConsts mrK mrRedex :=
  ⟨⟨trivial, show ``MJ ∉ mrK from by decide⟩, trivial⟩

/-- **§3's `decide` is an instance of a theorem, not a coincidence of this witness.**  The same
`restore_noK` argument applies at every field whose stored type is companion-free, hence at every
redex field of every block whose nested instance is `fun _ => I` for `I` its own member. -/
theorem mr_restore_redex_id :
    mrRestore.restore (mrAux mrAuxNodeB) 1 mrRedex = mrRedex :=
  VIndRestore.restore_noK mrRestore_ownId 1 mrRedex mr_redex_noK

/-- …and the computation agrees, independently. -/
example : mrRestore.restore (mrAux mrAuxNodeB) 1 mrRedex = mrRedex := by decide

/-! ### §5.1 The obligation at the companion constructor is uninhabited *as a premise* -/

/-- **Every recursive field of `mrAuxNodeB` is companion-free**, so
`substC_atRec_fieldTypes_defeq_of_noK`'s `hrec` has a false premise at this constructor and
costs nothing.  Field `0` is not recursive at all; field `1` is the redex. -/
theorem mr_hrec_nodeB_vacuous (i : Nat) (F : VIndField) (r : VIndRecArg)
    (hF : mrAuxNodeB.fields[i]? = some F) (hr : F.recArg = some r)
    (hnc : ¬ VExpr.NoConsts mrK F.type) : False := by
  rcases i with _ | _ | i
  · cases hF; exact absurd hr nofun
  · cases hF; exact hnc mr_redex_noK
  · simp [mrAuxNodeB] at hF

/-- **§T15.7's field-telescope `TeleDefEq` at the redex constructor, with NO input at all** —
for every environment, every universe count and every context.  This is the parameterised
(`D.np > 0`) route's `hfld` at the redex block, and it is free.

**Read this honestly**: it is free *because* the two telescopes are equal here
(`mr_auxFieldTypesR_eq_fields`), so the certificate is the identity one — row 127f's lesson, one
layer out.  The content is not that a hard defeq was proved; it is that **the obligation the
handoff costed does not exist**.  §5.2 is the instance where something is actually proved. -/
theorem mr_teleDefEq_fld_stored {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.TeleDefEq U Γ
      (((mrAux mrAuxNodeB).atRecTele (mrAuxNodeB.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))
      (((mrAux mrAuxNodeB).atRecTele (mrAuxNodeB.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))) :=
  VIndRestore.substC_atRec_fieldTypes_defeq_of_noK mrRestore_ownId
    (fun i F r hF hr hnc => absurd (mr_hrec_nodeB_vacuous i F r hF hr hnc) not_false)

/-! ### §5.2 The obligation that DOES survive: `hrec` at a COMPANION-pointing field

Row 127f's lesson, executed one layer out.  `MJ.obj`'s single recursive field is stored as the
companion constant `_nested.MDep_1` and restored to `MDep Prop (fun _ => MJ)`
(`mr_objFieldTypesR_ne_fields`), so it is precisely the field where §T15.7's `hrec` is a **real**
obligation.  It is discharged here — at the block where `Canonical` is false — from §T16.1
(`substC_atRec_canonType_defeq`) through `substC_atRec_stored_defeq_of_canonical`, whose per-field
`hct` is *true* at this field (`mrObj_canonical`).

The two environment premises are constant lookups the staged environment supplies; they are the
same reduction `mr_const_hasType` performs for `mr_pos_beta`, and no stronger. -/

/-- The field really does point at a companion, so §5.1's escape is unavailable here. -/
theorem mr_objField_not_noK : ¬ VExpr.NoConsts mrK (mrObj.fields.getD 0 default).type :=
  fun h => h (show mrNestedName ∈ mrK from by decide)

/-- The restored presentation of the companion member, computed. -/
theorem mr_atRec_tyBody_one :
    (mrAux mrAuxNodeB).atRec (mrRestore.tyBody (mrAux mrAuxNodeB) 1)
      = .app (.app (.const ``MDep []) (.sort .zero)) (.lam (.sort .zero) (.const ``MJ [])) := rfl

/-- **§T16.1's `hbody` at this block**: `MDep Prop (fun _ => MJ)` is a type. -/
theorem mr_tyBody_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    (hMDep : env.constants ``MDep = some ⟨0, mrDepType.type⟩)
    (hMJ : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType U Γ ((mrAux mrAuxNodeB).atRec (mrRestore.tyBody (mrAux mrAuxNodeB) 1))
      (.sort (.succ .zero)) := by
  rw [mr_atRec_tyBody_one]
  have h1 : env.HasType U Γ (.const ``MDep [])
      (.forallE (.sort (.succ .zero))
        (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)))) :=
    .constDF hMDep nofun nofun rfl .nil
  have h2 : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  have h3 : env.HasType U Γ (.app (.const ``MDep []) (.sort .zero))
      (.forallE (.forallE (.sort .zero) (.sort (.succ .zero))) (.sort (.succ .zero))) :=
    .appDF h1 h2
  have h4 : env.HasType U Γ (.lam (.sort .zero) (.const ``MJ []))
      (.forallE (.sort .zero) (.sort (.succ .zero))) :=
    .lamDF (.sortDF trivial trivial rfl) (.constDF hMJ nofun nofun rfl .nil)
  exact .appDF h3 h4

/-- **§T15.7's `hrec`, PRODUCED at the companion-pointing field of the redex block.**  The
restoration genuinely *moves* this field (`mr_objFieldTypesR_ne_fields`), so §5.1's escape is
unavailable and §T16.1 has to run.  Everything §T16.1 asks for beyond the two constant lookups is
free here because `D.params = []` and the field's `recArg` has empty binders and empty
arguments — so `hbv`/`hAs` are `HasArgs.nil`, `hpi`/`hsort` are `rfl`, and `hOnp` is `hOn`.

**Read §5.5 before quoting this as a conversion.**  At `D.np = 0` the two sides turn out to be the
*same expression* after `σ`, so what is proved here is a well-typedness fact, not a conversion. -/
theorem mr_hrec_obj {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.Ordered) (hOn : OnCtx Γ (env.IsType U))
    (hMDep : env.constants ``MDep = some ⟨0, mrDepType.type⟩)
    (hMJ : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    ∃ u, env.IsDefEq U Γ
      (((mrAux mrAuxNodeB).atRec (mrObj.fields.getD 0 default).type).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      (((mrAux mrAuxNodeB).atRec
          (mrRestore.restore (mrAux mrAuxNodeB) 0 (mrObj.fields.getD 0 default).type)).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) (.sort u) :=
  VIndRestore.substC_atRec_stored_defeq_of_canonical (r := ⟨[], 1, []⟩) (i := 0)
    mrAuxB_blockNames_nodup rfl nofun rfl
    (VIndRestore.substC_atRec_canonType_defeq (K := mrK) mrRestore_substFree
      mrRestore_domSep.substAt (mrRestore_tyArgs_closed0 1) henv rfl (by decide)
      (As := []) (B' := .sort (.succ .zero)) (w := .succ .zero)
      hOn hOn .nil (mr_tyBody_hasType hMDep hMJ) rfl .nil rfl)

/-- **§T15.7's field telescope at `MJ.obj`, assembled** — the parameterised route's `hfld` at the
*user* constructor of the redex block, with `hrec` supplied at the one field that moves.  Together
with `mr_teleDefEq_fld_stored` this is §T15.7 discharged at **both** constructors of a block at
which `D.Canonical` is false. -/
theorem mr_teleDefEq_fld_obj {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.Ordered) (hOn : OnCtx Γ (env.IsType U))
    (hMDep : env.constants ``MDep = some ⟨0, mrDepType.type⟩)
    (hMJ : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    env.TeleDefEq U Γ
      (((mrAux mrAuxNodeB).atRecTele (mrObj.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))
      (((mrAux mrAuxNodeB).atRecTele (mrObj.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))) :=
  VIndRestore.substC_atRec_fieldTypes_defeq_of_noK mrRestore_ownId (by
    rintro (_ | i) F r hF hr hnc
    · cases hF; exact mr_hrec_obj henv hOn hMDep hMJ
    · simp [mrObj] at hF)

/-! ### §5.3 The β route the handoff asked for is AVAILABLE — it is just not needed

For the record, and because "cannot be closed" and "need not be closed" are different answers:
the join the handoff priced *does* go through.  At the redex field the two sides of `hrec` are the
same expression, so the β step contracts one of them to the own member and back, and `hrec` holds
in the **unweakened** §T15.7 shape as well.  This is `mr_pos_beta`'s content, generalised off
`U = 0` (its statement fixes `U = 0` and `Γ = [VExpr.sort .zero]`; §T15.7's consumers want
`U = D.recUvars`, which is `1` here, so the generalisation is needed to feed them and is one
line).

**The cost comparison is the point.**  Via §5.1 the redex field costs nothing and needs no
environment at all.  Via this route it costs one constant lookup and a β step, i.e. it pays a
typing that `VEnv.TeleDefEq.rfl` does not charge.  §5.1 is therefore the form to use, and the
handoff's "only thing standing between §T15's assembly and a redex block" was **not** standing
there. -/

/-- `mr_pos_beta`, at an arbitrary universe count and over an arbitrary tail context. -/
theorem mr_redex_defeq_own {env : VEnv} {U : Nat} {Γ : List VExpr}
    (hMJ : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    env.IsDefEq U (.sort .zero :: Γ) mrRedex (.const ``MJ []) (.sort (.succ .zero)) :=
  have hMJT : env.HasType U (.sort .zero :: .sort .zero :: Γ) (.const ``MJ [])
      (.sort (.succ .zero)) := .constDF hMJ nofun nofun rfl .nil
  .beta hMJT (.bvar .zero)

/-- …and `mr_pos_beta` itself is the `U = 0`, `Γ = []` instance, so nothing new is assumed. -/
example {env : VEnv} (hT : env.HasType 0 [VExpr.sort .zero, VExpr.sort .zero]
    (.const ``MJ []) (.sort (.succ .zero))) :
    env.IsDefEqType 0 [VExpr.sort .zero] mrRedex
      (({ binders := [], idx := 0, args := [] } : VIndRecArg).canonType (mrAux mrAuxNodeB) 1) :=
  mr_pos_beta hT

/-- **§T15.7's `hrec` at the redex field, in the shape the handoff asked for**, from the β step.
The context is the field's own: one earlier field (`Prop`) over `Γ`. -/
theorem mr_hrec_redex_via_beta {env : VEnv} {U : Nat} {Γ : List VExpr}
    (hMJ : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    ∃ u, env.IsDefEq U (.sort .zero :: Γ)
      (((mrAux mrAuxNodeB).atRec (mrAuxNodeB.fields.getD 1 default).type).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      (((mrAux mrAuxNodeB).atRec (mrRestore.restore (mrAux mrAuxNodeB) 1
          (mrAuxNodeB.fields.getD 1 default).type)).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) (.sort u) := by
  refine ⟨.succ .zero, ?_⟩
  show env.IsDefEq U (.sort .zero :: Γ) mrRedex mrRedex (.sort (.succ .zero))
  exact (mr_redex_defeq_own hMJ).trans (mr_redex_defeq_own hMJ).symm

/-! ### §5.4 The environment premises of §5.2 are satisfiable — a closed witness

`mr_hrec_obj` takes `henv`, `hOn` and two constant lookups.  `hOn` is `trivial` at `Γ = []`; the
other three are exhibited here in an actually-constructed `Ordered` environment, so §5.2 is not
green by an unsatisfiable premise.  (`MRedex.MRWit.mr_pos_beta`'s own hypothesis is only *reduced*
to a constant lookup by `mr_const_hasType`; this closes that reduction too.) -/

/-- `MJ : Sort 1` is a well-formed constant over any environment. -/
theorem mr_MJ_constant_wf {env : VEnv} : VConstant.WF env ⟨0, .sort (.succ .zero)⟩ :=
  ⟨_, .sortDF trivial trivial rfl⟩

/-- …and so is `MDep : (α : Type) → (α → Type) → Type`, at the level `forallEDF` computes. -/
theorem mr_MDep_type_hasType {env : VEnv} :
    env.HasType 0 [] mrDepType.type
      (.sort (.imax (.succ (.succ .zero))
        (.imax (.imax (.succ .zero) (.succ (.succ .zero))) (.succ (.succ .zero))))) :=
  .forallEDF (.sortDF trivial trivial rfl)
    (.forallEDF (.forallEDF (.bvar .zero) (.sortDF trivial trivial rfl))
      (.sortDF trivial trivial rfl))

theorem mr_MDep_constant_wf {env : VEnv} : VConstant.WF env ⟨0, mrDepType.type⟩ :=
  ⟨_, mr_MDep_type_hasType⟩

theorem mr_env_exists : ∃ env : VEnv, env.Ordered ∧
    env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩ ∧
    env.constants ``MDep = some ⟨0, mrDepType.type⟩ := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := ``MJ)
    (ci := ⟨0, .sort (.succ .zero)⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hMJ : e1.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩ := by
    rw [c1]; exact if_pos rfl
  have ho1 : e1.Ordered := .const .empty mr_MJ_constant_wf he1
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := ``MDep)
    (ci := ⟨0, mrDepType.type⟩) (by rw [c1]; exact if_neg (by decide))
  have c2 := VEnv.addConst_constants_eq he2
  refine ⟨e2, .const ho1 mr_MDep_constant_wf he2, ?_, by rw [c2]; exact if_pos rfl⟩
  rw [c2]
  exact (if_neg (show ¬ ((``MDep : Name) = ``MJ) from by decide)).trans hMJ

/-- **§5.2's conclusion, with every premise discharged**: the `hrec` §T15.7 asks for at the
companion-pointing field of the redex block holds in a *concrete* environment, at `Γ = []`. -/
theorem mr_hrec_obj_closed : ∃ (env : VEnv) (u : VLevel), env.Ordered ∧ env.IsDefEq 0 []
      (((mrAux mrAuxNodeB).atRec (mrObj.fields.getD 0 default).type).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK))
      (((mrAux mrAuxNodeB).atRec
          (mrRestore.restore (mrAux mrAuxNodeB) 0 (mrObj.fields.getD 0 default).type)).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK)) (.sort u) := by
  obtain ⟨env, henv, hMJ, hMDep⟩ := mr_env_exists
  obtain ⟨u, hu⟩ := mr_hrec_obj (U := 0) (Γ := []) henv trivial hMDep hMJ
  exact ⟨env, u, henv, hu⟩

/-! ### §5.5 …and the limit of what a redex block in THIS tree can witness

The honest grading of §5.2, and it is a measurement, not a reading.  `σ` identifies the two sides
of `hrec` at `MJ.obj`'s field **on the nose** — they are the same `VExpr`
(`mr_obj_entry_substC_eq`, `decide`).  So `mr_hrec_obj` proves `∃ u, IsDefEq U Γ X X (.sort u)`,
i.e. that the substituted entry is a *type*; it does not exercise a conversion.

The reason is structural and is §7.4's business: at `D.params = []` the strict head equation
`substC_tyApp'_eq_tyAppR'` holds (its `hcl0` is available — `mrRestore_tyArgs_closed0`), so
restoration-then-`σ` and `σ` alone agree syntactically.  `hrec` is a genuine *conversion* only
where that equation fails, i.e. at `D.np > 0`, which is exactly where
`InductiveDeclExamples.ntree_not_tyArgs_closed0` refutes `hcl0`.

**Consequence, stated so nobody re-prices this corner from the shape of the proof.**  A
non-degenerate instance of §T15.7's `hrec` needs a block that is *both* a redex block *and*
parameterised.  `Verify/Inductive/MemberRedexScan.lean` finds exactly three redex blocks in the
running environment — `MRedex.MRWit.MJ`, `Lean.Json`, `Lean.PrefixTreeNode` — and only the first
is transcribed as a `VInductDecl'` here, with `np = 0`.  The parameterised witness that *is*
transcribed (`ntreeAux`) is not a redex block.  So **no block in this tree can witness §T15.7's
`hrec` non-degenerately**, and the next step on this path is a witness (a transcription of
`Lean.PrefixTreeNode`'s auxiliary block, which has parameters), not a proof. -/

/-- **The two sides of §5.2's `hrec` are the same expression at this block.**  So §5.2 is a typing
obligation discharged, not a conversion. -/
theorem mr_obj_entry_substC_eq :
    ((mrAux mrAuxNodeB).atRec (mrObj.fields.getD 0 default).type).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK)
      = ((mrAux mrAuxNodeB).atRec (mrRestore.restore (mrAux mrAuxNodeB) 0
          (mrObj.fields.getD 0 default).type)).substC
        (mrRestore.csubst (mrAux mrAuxNodeB) mrK) := by decide

/-- …and therefore §T15.7's **sharpest** form (`substC_atRec_fieldTypes_defeq'`, whose premise is
that the *substituted* entries differ) has an empty obligation at `MJ.obj` too — the field
telescope defeq at the user constructor is free, for every environment and context.  Compare
`mr_teleDefEq_fld_obj`, which pays §T16.1's typing to get the same conclusion. -/
theorem mr_teleDefEq_fld_obj_free {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.TeleDefEq U Γ
      (((mrAux mrAuxNodeB).atRecTele (mrObj.fields.map (·.type))).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK)))
      (((mrAux mrAuxNodeB).atRecTele (mrObj.fieldTypesR (mrAux mrAuxNodeB) mrRestore)).map
        (VExpr.substC · (mrRestore.csubst (mrAux mrAuxNodeB) mrK))) :=
  VIndRestore.substC_atRec_fieldTypes_defeq' (by
    rintro (_ | i) F r hF hr hne
    · cases hF; exact absurd mr_obj_entry_substC_eq hne
    · simp [mrObj] at hF)

/-- **The only transcribed redex block is parameterless** — the half of §5.5's gap that is a fact
about this file rather than about the tree.  The other half, *read off source*: the parameterised
nested witness `InductiveDeclExamples.ntreeAux` satisfies `ntreeAux.Canonical`
(`Theory/Inductive/NestedHead.lean:646`), so it stores no β-redex and cannot serve either. -/
theorem mrAuxB_np_not_pos : ¬ (mrAux mrAuxNodeB).np > 0 := by decide

end MRWit
end MRedex
end Lean4Lean
