/-
# `CtorBeta`: obligation (A) at `D.np > 0`, reduced to the recursive fields alone

`docs/handoff-flipprice.md` §6 prices the nested `AddInduct` flip at three open items, of which
**(A)** is the general parameterful case of `VEnv.ctorConstsCR_wf_of_substC'`
(`Theory/Typing/ConstSubstNested.lean:208`), whose residual it describes as

> its telescope-defeq hypothesis: `TeleDefEq` on `C.params ++ fieldTypes` against
> `C.params ++ fieldTypesR`, **plus one `IsDefEq` on the canonical result**.

This file shows that residual is smaller than that, in general and with no bound on `D.np`:

* the **result** conjunct is free (§2), from `VIndRestore.OwnId.tyAppR_eq` plus
  `VEnv.IsType.mkPi_inv` — the source constant's own typing already contains it;
* the **parameter** block of the telescope is free, because both sides are the *same* list and
  `VEnv.TeleDefEq.rfl` carries no typing;
* every **non-recursive** field is free for the same reason (`VIndField.typeR`'s `none` branch is
  `F.type` on the nose);
* every **recursive** field whose stored type names no companion constant is free
  (`VIndRestore.restore_noK`).

What is left is one typed defeq per recursive field that actually mentions a companion — §3's
`hfld`. That is the same *shape* of datum as (B)'s and (C)'s residual, and (importantly) it is
**not** a new kind of obligation.

## Where the machinery came from

Nothing here is new mathematics.  §1 is `VIndRestore.substC_atRec_fieldTypes_defeq'` and
`…_of_noK` (`Theory/Inductive/NestedTele.lean` §T15.7) with `D.atRec` deleted: those are stated at
the *recursor's* level numbering, which is what (B) and (C) consume, and (A) consumes the
unprimed telescope.  §2 is `VEnv.IsType.mkPi_inv` (`Theory/Inductive/StructureClosed.lean:914`)
composed with `VIndRestore.OwnId.tyAppR_eq` (`Theory/Inductive/Restore.lean:914`) — a pair with,
as far as the environment scan in `CtorBetaScan.lean` can see, no common consumer before this
file.

`docs/handoff-ctorbeta.md` records what is measured and what is read off, and states
hole-freeness and non-vacuity separately.
-/
import Lean4Lean.Theory.Inductive.TeleMove2

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The field telescope, un-`atRec`'d

`VIndRestore.substC_atRec_fieldTypes_defeq'` relates
`(D.atRecTele (C.fields.map (·.type))).map (·.substC σ)` to
`(D.atRecTele (C.fieldTypesR D R)).map (·.substC σ)`.  Obligation (A) needs the same statement
without `atRec`: `VIndCtor.type` and `VIndCtor.typeR` are at the block's *own* levels.  The proof
is the same walk; only the outer transformation differs. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {σ : CSubst} {e : VEnv} {U : Nat} {C : VIndCtor}

/-- **The field telescope's `TeleDefEq`, reduced to the entries that move** — the unprimed
(own-levels) twin of `VIndRestore.substC_atRec_fieldTypes_defeq'`.

Non-recursive entries cost `VEnv.TeleDefEq.rfl`, which carries no typing at all: `VIndField.typeR`
copies them verbatim.  A recursive entry that `σ` identifies with its restoration is free for the
same reason. -/
theorem substC_fieldTypes_defeq' {Γ : List VExpr}
    (hrec : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r →
      F.type.substC σ ≠ (R.restore D i F.type).substC σ →
      ∃ u, e.IsDefEq U
        ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse ++ Γ)
        (F.type.substC σ) ((R.restore D i F.type).substC σ) (.sort u)) :
    e.TeleDefEq U Γ ((C.fields.map (·.type)).map (VExpr.substC · σ))
      ((C.fieldTypesR D R).map (VExpr.substC · σ)) := by
  refine VEnv.TeleDefEq.of_entries' (by simp [VIndCtor.fieldTypesR]) ?_
  intro i A A' hA hA'
  simp only [List.getElem?_map, VIndCtor.fieldTypesR, List.getElem?_zipIdx,
    Option.map_map] at hA hA'
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 hA
  obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.1 hA'
  rw [hF] at hF'
  cases hF'
  cases hr : F.recArg with
  | none =>
    refine Or.inl ?_
    simp only [Function.comp_def, Nat.zero_add, VIndField.typeR, hr]
  | some r =>
    by_cases hmv : F.type.substC σ = (R.restore D i F.type).substC σ
    · refine Or.inl ?_
      simp only [Function.comp_def, Nat.zero_add, VIndField.typeR, hr]
      exact hmv
    · refine Or.inr ?_
      obtain ⟨u, hu⟩ := hrec i F r hF hr hmv
      refine ⟨u, ?_⟩
      simp only [Function.comp_def, Nat.zero_add, VIndField.typeR, hr]
      exact hu

/-- **…and with the premise a caller can check without computing `σ`.** -/
theorem substC_fieldTypes_defeq {Γ : List VExpr}
    (hrec : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → R.restore D i F.type ≠ F.type →
      ∃ u, e.IsDefEq U
        ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse ++ Γ)
        (F.type.substC σ) ((R.restore D i F.type).substC σ) (.sort u)) :
    e.TeleDefEq U Γ ((C.fields.map (·.type)).map (VExpr.substC · σ))
      ((C.fieldTypesR D R).map (VExpr.substC · σ)) :=
  substC_fieldTypes_defeq' (fun i F r hF hr hmv => hrec i F r hF hr fun hid => hmv (by rw [hid]))

/-- **…and the obligation is only at fields that name a COMPANION constant.**

`VIndRestore.restore_noK` is the identity of the restoration on anything free of companion
constants, so a recursive field stored without one contributes `VEnv.TeleDefEq.rfl`.  This is the
unprimed twin of `substC_atRec_fieldTypes_defeq_of_noK`, and it is what makes the β-redex fields
`ElimNestedInductive` manufactures cost nothing here as well: those point at the block's **own**
member, which is not in `K`. -/
theorem substC_fieldTypes_defeq_of_noK {K : List Name} (hown : R.OwnId D K) {Γ : List VExpr}
    (hrec : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∃ u, e.IsDefEq U
        ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse ++ Γ)
        (F.type.substC σ) ((R.restore D i F.type).substC σ) (.sort u)) :
    e.TeleDefEq U Γ ((C.fields.map (·.type)).map (VExpr.substC · σ))
      ((C.fieldTypesR D R).map (VExpr.substC · σ)) :=
  substC_fieldTypes_defeq (fun i F r hF hr hmv =>
    hrec i F r hF hr fun hnc => hmv (VIndRestore.restore_noK hown i F.type hnc))

end
end VIndRestore

/-! ## §2 The result conjunct is free

`docs/handoff-flipprice.md` §6 lists (A)'s residual as the telescope defeq **plus one `IsDefEq` on
the canonical result**.  The second half is not a residual at all: at a member the step *declares*
the restored head **is** the block's own head (`VIndRestore.OwnId.tyAppR_eq`), so the two sides of
the result conjunct are the *same expression*, and the typing that makes it an `IsDefEq` is already
inside the source constant's own `IsType` — `VEnv.IsType.mkPi_inv` peels it out on `e₁.Ordered`
alone.

Note which hypothesis does the work: `hK : T.name ∉ K`.  `VInductDecl'.ctorConstsCR` declares
constructors only at members off `K` (its `if` is exactly that test), so this is not a restriction
— it is the reason the result position never carries a β-redex, whatever `D.np` is.  The β-gap
lives in the *field* telescope, not in the result. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e₁ : VEnv} {U : Nat}

/-- **(A)'s result conjunct, in general, with no bound on `D.np`.** -/
theorem ctorResult_defeq (hown : R.OwnId D K) (he₁ : e₁.Ordered)
    {C : VIndCtor} {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∉ K)
    (hty : e₁.IsType U [] ((C.type D j).substC σ)) :
    ∃ v : VLevel, e₁.IsDefEq U
      (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)).reverse)
      ((C.canonResult D j).substC σ)
      ((D.tyAppR R j C.fields.length C.args).substC σ) (.sort v) := by
  rw [VIndCtor.type, VExpr.substC_mkPi] at hty
  obtain ⟨-, hres⟩ := VEnv.IsType.mkPi_inv he₁ (Γ := []) ⟨⟩ hty
  rw [List.append_nil] at hres
  rw [hown.tyAppR_eq hT hK C.fields.length C.args,
    show D.tyApp j C.fields.length C.args = C.canonResult D j from rfl]
  exact hres

end
end VIndRestore

/-! ## §3 Obligation (A) at `D.np > 0`, reduced to the recursive fields

The composition.  Compare `VEnv.ctorConstsCR_wf_of_np_zero'`
(`Theory/Inductive/RestoreBridge.lean:595`), which is (A) in general at `D.params = []` and takes
nine side conditions; this one carries no bound on `D.np`, and of those nine keeps only `hown`.

What it does **not** do is discharge `hfld`.  This is a *reduction*, not a discharge: `hfld` is
one typed defeq per recursive field naming a companion constant, and that is the open half of (A).
Graded that way deliberately — `docs/vacuity-ledger.md` §0 asks for it, and two results earlier
today were reductions whose remaining hypothesis *was* the open obligation. -/

/-- **Obligation (A), general in `D.np`, reduced to the recursive fields that name a companion.**

Every other entry of `ctorConstsCR_wf_of_substC'`'s telescope defeq, and its whole result
conjunct, is discharged here:

| position | why it is free |
| --- | --- |
| `C.params` | the same list on both sides — `VEnv.TeleDefEq.rfl`, no typing |
| non-recursive field | `VIndField.typeR`'s `none` branch is `F.type` — same list entry |
| recursive field, no companion constant | `VIndRestore.restore_noK` — the restoration is the identity |
| the canonical result | §2: `OwnId.tyAppR_eq` makes the two sides equal, `IsType.mkPi_inv` types it |

`hfld`'s context is the one `VEnv.TeleDefEq` puts entry `i` in: the substituted stored types of
the earlier fields, over the substituted parameter telescope. -/
theorem VEnv.ctorConstsCR_wf_of_fieldsD {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore}
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hfld : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        ∃ u : VLevel, e₁.IsDefEq D.uvars
          ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
            ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
          (F.type.substC (R.csubstTy D K))
          ((R.restore D i F.type).substC (R.csubstTy D K)) (.sort u)) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  refine VEnv.ctorConstsCR_wf_of_substC' hD h₃ henv₃ he₁ hσ ?_
  intro j T C hT hK hCT
  have hwf : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ :=
    (hD.ctors env₃ h₃ j T hT C hCT).constant_wf henv₃
  obtain ⟨v, hres⟩ := VIndRestore.ctorResult_defeq hown he₁ hT hK (hwf.substC hσ)
  refine ⟨v, ?_, hres⟩
  rw [List.map_append, List.map_append]
  refine VEnv.TeleDefEq.append VEnv.TeleDefEq.refl
    (VIndRestore.substC_fieldTypes_defeq_of_noK hown ?_)
  intro i F r hF hr hnc
  simpa only [List.append_nil] using hfld j T C hT hK hCT i F r hF hr hnc

/-! ## §4 The witness: non-vacuity, at a PARAMETERISED nested block

Hole-freeness and non-vacuity are separate claims (`docs/vacuity-ledger.md` §0), and an axiom line
is evidence only of the first.  This section is the second, for §3: the hypothesis set of
`VEnv.ctorConstsCR_wf_of_fieldsD` is **jointly** inhabited at `ntreeAux` — the `NTree`/`List`
block, `D.np = 1`, a real nested declaration Lean's own kernel runs the nested elimination on.

Two things are checked, not one:

* `ntreeAux_ctorConstsCR_wf_of_fieldsD` — all seven hypotheses hold simultaneously and the
  conclusion follows, i.e. the theorem is not empty at `np > 0`;
* `ntree_fld_premise_fires` / `ntree_field0_free` — `hfld`'s own premise is **non-empty** there.
  Without this the reduction could be "free" only because nothing satisfies its premise: field 1 of
  `ntreeNode` names the companion and so *does* demand the datum, and field 0 does not
  (`recArg = none`).  So §3 charges exactly one defeq at `ntreeNode`, and that one defeq is a
  single `VEnv.IsDefEq.beta` — the same step `ntreeNode_beta_bridge` does by hand. -/

namespace InductiveDeclExamples

/-- `hfld`'s premise **fires** at `ntreeNode`'s second field: its stored type names the companion
`_nested.List_1`.  So the obligation §3 leaves open is not empty at this block. -/
theorem ntree_fld_premise_fires :
    ¬ VExpr.NoConsts ntreeK (.app (.const `_nested.List_1 [.param 0]) (.bvar 1)) := by decide

/-- …and `ntreeNode`'s first field is not charged at all: it is non-recursive. -/
theorem ntree_field0_free : (ntreeNode.fields.getD 0 default).recArg = none := rfl

/-- …and the **conclusion** is not vacuous either: the block really does declare a constructor
constant at a member off `K`, so `∀ c ∈ ctorConstsCR …` is not a statement about the empty list. -/
theorem ntree_ctorConstsCR_ne_nil : ntreeAux.ctorConstsCR ntreeRestore ntreeK ≠ [] := by decide

/-! ### §4a The restoration-data side conditions at `ntreeAux`

The four `decide`-able side conditions §7 carries.  They did not exist for `ntreeAux` — only the
`nfnAux` (`D.np = 0`) analogues did (`nfnRestore_tyVal_levelWF` / `nfnRestore_tyArgs_closed`,
`Theory/Inductive/RestoreBridge.lean:637`) — because nothing had asked for them at a
*parameterised* block. -/

theorem ntreeRestore_tyArgs_eq (i : Nat) : ntreeRestore.tyArgs i =
    if i = 1 then [VExpr.app (.const ``NTree [.param 0]) (.bvar 0)] else [VExpr.bvar 0] := rfl

theorem ntreeRestore_tyName_eq (i : Nat) :
    ntreeRestore.tyName i = if i = 1 then ``List else ``NTree := rfl

theorem ntreeRestore_tyVal_levelWF (i : Nat) :
    (ntreeRestore.tyVal ntreeAux i).LevelWF ntreeAux.uvars := by
  have hp : ∀ l ∈ [VLevel.param 0], VLevel.WF ntreeAux.uvars l := by decide
  rw [VIndRestore.tyVal, ntreeRestore_tyArgs_eq, ntreeRestore_tyName_eq,
    show ntreeRestore.tyLvls i = [VLevel.param 0] from rfl]
  by_cases hi : i = 1
  · simp only [hi, if_true]
    exact ⟨(by exact (by decide : VLevel.WF ntreeAux.uvars (VLevel.param 0))), hp, hp, trivial⟩
  · simp only [hi, if_false]
    exact ⟨(by exact (by decide : VLevel.WF ntreeAux.uvars (VLevel.param 0))), hp, trivial⟩

theorem ntreeRestore_tyArgs_closed (i : Nat) :
    ∀ a ∈ ntreeRestore.tyArgs i, a.ClosedN ntreeAux.np := by
  rw [ntreeRestore_tyArgs_eq]
  by_cases hi : i = 1
  · simp only [hi, if_true]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact ⟨trivial, Nat.zero_lt_one⟩
  · simp only [hi, if_false]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact Nat.zero_lt_one

theorem ntreeRestore_csubstTy_tyName (i : Nat) :
    ntreeRestore.csubstTy ntreeAux ntreeK (ntreeRestore.tyName i) = none := by
  rw [ntree_csubstTy, ntreeRestore_tyName_eq]
  by_cases hi : i = 1
  · simp only [hi, if_true]; exact ntreeSubst_of_ne (by decide)
  · simp only [hi, if_false]; exact ntreeSubst_of_ne (by decide)

theorem ntreeRestore_tyArgs_noCSubst (i : Nat) :
    ∀ a ∈ ntreeRestore.tyArgs i, a.NoCSubst (ntreeRestore.csubstTy ntreeAux ntreeK) := by
  rw [ntree_csubstTy, ntreeRestore_tyArgs_eq]
  by_cases hi : i = 1
  · simp only [hi, if_true]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact ⟨ntreeSubst_of_ne (by decide), trivial⟩
  · simp only [hi, if_false]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial


section
variable {env₁ env₂ env₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁) (henv₁ : env₁.Ordered)
variable (h₂ : env₁.addIndTypes ntreeAux = some env₂)
variable (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)

include h henv₁ h₂ h₃ in
/-- **Obligation (A) at the parameterised nested witness, through §3's general reduction.**

Compare `InductiveDeclExamples.ntreeAux_ctorConstsCR_wf`
(`Theory/Typing/ConstSubstNested.lean:965`), which reaches the same conclusion through
`ctorConstsCR_wf_of_substC'` directly and supplies the whole telescope by hand.  This one supplies
**only** the one moving field, which is the point of §3. -/
theorem ntreeAux_ctorConstsCR_wf_of_fieldsD :
    ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  have henv₂ : env₂.Ordered :=
    VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' h₂
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  refine VEnv.ctorConstsCR_wf_of_fieldsD ntreeAux_WF' h₂ henv₂ henv₃
    (ntree_csubstTy ▸ ntreeSubst_WF h henv₁ h₂ h₃) ntreeRestore_ownId ?_
  rintro j T C hT hK hC i F r hF hr hnc
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    match i, hF with
    | 0, hF => cases hF; exact absurd hr nofun
    | 1, hF =>
      cases hF
      refine ⟨.succ (.param 0), ?_⟩
      rw [ntree_csubstTy]
      refine VEnv.IsDefEq.beta (A := .sort (.succ (.param 0)))
        (B := .sort (.succ (.param 0))) ?_ ?_ <;> type_tac
    | (_ + 2), hF => simp [ntreeNode] at hF
  | 1, hT => cases hT; exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

end

end InductiveDeclExamples


/-! ## §6 The per-field datum at a CANONICAL recursive field

A canonical recursive field is `mkPi r.binders (D.tyApp r.idx k r.args)` with
`k = r.binders.length + i`, and its restoration is the same with `tyAppR` in place of `tyApp`
(`VIndRestore.restore_canonType_noK`, which asks only that the binders name no *companion*).  So
§3's `hfld` at such a field is one `mkPi` congruence over an unchanged binder telescope plus the
**head** defeq — which is exactly what §8.8 of `Theory/Inductive/NestedRules.lean` closed.

`hOn` is the binder telescope's own `OnCtx`; `hhead` is the head defeq. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv} {U : Nat}

/-- **§3's `hfld` at a canonical recursive field, reduced to the head defeq.** -/
theorem field_defeq_of_canonical (hown : R.OwnId D K) (hnd : D.blockNames.Nodup)
    {i : Nat} {F : VIndField} {r : VIndRecArg} (_hr : F.recArg = some r)
    (hcanon : F.type = r.canonType D i)
    {T' : VIndType} (hT' : D.types[r.idx]? = some T')
    (hb : ∀ B ∈ r.binders, VExpr.NoConsts K B) {Γ : List VExpr}
    (hOn : OnCtx ((r.binders.map (VExpr.substC · σ)).reverse ++ Γ) (e.IsType U))
    (hhead : ∃ v : VLevel, e.IsDefEq U ((r.binders.map (VExpr.substC · σ)).reverse ++ Γ)
      ((D.tyApp r.idx (r.binders.length + i) r.args).substC σ)
      ((D.tyAppR R r.idx (r.binders.length + i) r.args).substC σ) (.sort v)) :
    ∃ u : VLevel, e.IsDefEq U Γ (F.type.substC σ)
      ((R.restore D i F.type).substC σ) (.sort u) := by
  rw [hcanon, restore_canonType_noK hown hnd hT' hb, VIndRecArg.canonType,
    VIndRecArg.canonTypeR, VExpr.substC_mkPi, VExpr.substC_mkPi, VIndRecArg.canonResult,
    VIndRecArg.canonResultR]
  exact VEnv.IsDefEq.mkPi_congrU VEnv.TeleDefEq.refl hOn hhead

/-! ### §6a `substC` is invisible to the restored head — with no bound on `D.np`

`VIndRestore.substC_tyAppR` (`Theory/Inductive/RestoreBridge.lean:530`) is this statement, but it
sits in a `variable … include hp hnd hown hlw hcl` section and so carries **five hypotheses its
proof never uses**, `hp : D.params = []` among them.  That is why the parameterful route could not
reach it.  Restated here with the two hypotheses it actually needs; the proof is character for
character the one in `RestoreBridge.lean`.  (Reported rather than edited: `RestoreBridge.lean` is
not mine.) -/

/-- **The restored head is `σ`-invariant** — `substC_tyAppR` without `hp`/`hnd`/`hown`/`hlw`/`hcl`. -/
theorem substC_tyAppR_free (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K)) (j k : Nat) (args : List VExpr) :
    (D.tyAppR R j k args).substC (R.csubstTy D K)
      = D.tyAppR R j k (args.map (VExpr.substC · (R.csubstTy D K))) := by
  rw [VInductDecl'.tyAppR, VInductDecl'.tyAppH, VExpr.substC_mkApp,
    VExpr.substC_const_none (hnn j), List.map_append, List.map_map]
  congr 2
  exact List.map_congr_left fun a ha =>
    ((hna j a ha).liftN (n := k) (k := 0)).substC_eq


/-! ### §6b The head defeq, from §8.8 — the β-step itself

`VIndRestore.substC_tyApp_defeq_tyAppR_comp` (`Theory/Inductive/NestedRules.lean` §8.8) is the
typed β-step for the *unsubstituted* restored head, at any `D.np`.  §6 wants it with `substC` on
both sides and at a sort; §6a supplies the first, and `hsort` the second.  `hsort` is not slack:
`instAll B' args` is the head's declared type after the whole spine, and a *type* head's is a sort,
so a caller with `hbody` in hand has it.

**The residual, named.**  `hbv`, `hbody`, `hpi`, `hAs` are §8.8's own hypotheses, and §8.8's
docstring already says `hbody`/`hAs` are the same datum as the `val` clause of `(R.csubst D K).WF`
(§8.7's `hargs`) — genuinely data, by `VIndRestore.instAt_indep_of_tyArgs`.  So **(A) at `np > 0`
bottoms out in the same `hargs` that (B) and (C) do**, and that is the substantive finding of this
file: it is one obligation across all three, not three. -/

/-- **§6's `hhead` at a companion head, from §8.8's β-step.** -/
theorem head_defeq_of_beta (hnd : D.blockNames.Nodup)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np) (henv : e.Ordered)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {k : Nat} {args Γ As : List VExpr} {B B' : VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K))
    (hOn : OnCtx (D.params.reverse ++ Γ) (e.IsType D.uvars))
    (hbv : e.HasArgs D.uvars Γ D.params (VExpr.bvars k D.np))
    (hbody : e.HasType D.uvars (D.params.reverse ++ Γ) (R.tyBody D j) B)
    (hpi : VExpr.instAll B (VExpr.bvars k D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs D.uvars Γ As args)
    {v : VLevel} (hsort : VExpr.instAll B' args = .sort v) :
    ∃ w : VLevel, e.IsDefEq D.uvars Γ ((D.tyApp j k args).substC (R.csubstTy D K))
      ((D.tyAppR R j k args).substC (R.csubstTy D K)) (.sort w) := by
  refine ⟨v, ?_⟩
  rw [substC_tyAppR_free hnn hna,
    show args.map (VExpr.substC · (R.csubstTy D K)) = args from by
      rw [show args.map (VExpr.substC · (R.csubstTy D K)) = args.map id from
        List.map_congr_left fun a ha => (hargs a ha).substC_eq, List.map_id],
    ← hsort]
  exact substC_tyApp_defeq_tyAppR_comp hnd hlw hcl henv hT hK hargs hOn hbv hbody hpi hAs

/-- **…and at a head the step DECLARES there is no β-step at all**: `OwnId.tyAppR_eq` makes the two
sides the same expression, so the head defeq is whatever typing the source already has.  This is the
other half of §3's `hfld` premise: `¬ VExpr.NoConsts K F.type` can hold because a *binder* or an
*index argument* names a companion while the head does not. -/
theorem head_defeq_of_own (hown : R.OwnId D K)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∉ K)
    {k : Nat} {args Γ : List VExpr}
    (hty : ∃ v : VLevel, e.IsDefEq U Γ ((D.tyApp j k args).substC σ)
      ((D.tyApp j k args).substC σ) (.sort v)) :
    ∃ w : VLevel, e.IsDefEq U Γ ((D.tyApp j k args).substC σ)
      ((D.tyAppR R j k args).substC σ) (.sort w) := by
  rw [hown.tyAppR_eq hT hK]; exact hty

/-! ### §6c …and §6's `hOn` is free too

§6 asks for the `OnCtx` of the field's own binder telescope over the entry's prefix.  That is
`VEnv.OnCtx.mkPi_entry_inv` (`Theory/Inductive/NestedTele.lean` §T10) composed with
`VConstant.WF.substC_mkPi_inv` (§T3) — i.e. exactly the derivation `recTypeEntry_substC_onCtx`
performs for (B), transposed to (A)'s telescope.  So it costs nothing beyond the source
constant's own well-formedness, which `ctorConstsCR_wf_of_substC'` already has. -/

/-- **§6's `hOn`, and the field body's `IsType`, from the source constant alone.** -/
theorem ctorFieldEntry_onCtx {env₃ e₁ : VEnv} {σ : CSubst} {C : VIndCtor} {j i : Nat}
    {Bs : List VExpr} {Cd : VExpr} {F : VIndField}
    (he₁ : e₁.Ordered) (hσ : σ.WF env₃ e₁ D.uvars)
    (hs : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩)
    (hF : C.fields[i]? = some F) (hpi : F.type.substC σ = VExpr.mkPi Bs Cd) :
    OnCtx (Bs.reverse ++ ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse
        ++ (C.params.map (VExpr.substC · σ)).reverse)) (e₁.IsType D.uvars) ∧
      e₁.IsType D.uvars
        (Bs.reverse ++ ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse
          ++ (C.params.map (VExpr.substC · σ)).reverse)) Cd := by
  have hOnAll : OnCtx
      ((((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ))).reverse ++
        ([] : List VExpr)) (e₁.IsType D.uvars) := by
    simpa using (VConstant.WF.substC_mkPi_inv he₁ hσ (As := C.params ++ C.fields.map (·.type))
      (B := C.canonResult D j) hs).1
  have hidx : (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)))[
      C.params.length + i]? = some (VExpr.mkPi Bs Cd) := by
    rw [List.map_append, List.map_map, List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem?_map, hF]
    exact congrArg some hpi
  have hkey := VEnv.OnCtx.mkPi_entry_inv (U := D.uvars) he₁ hOnAll hidx
  rw [show ((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)).take
        (C.params.length + i)
      = C.params.map (VExpr.substC · σ)
        ++ ((C.fields.map (·.type)).map (VExpr.substC · σ)).take i from by
    rw [List.map_append, List.map_map]
    simp [List.take_append, List.take_of_length_le]] at hkey
  simpa [List.reverse_append] using hkey

/-! ### §6d The `hbv` spine is IN SCOPE at (A)'s field context — the §T4 failure mode does not fire

`Theory/Inductive/NestedTele.lean` §T4 records that `VIndRestore.substC_motiveType_defeq` is
**vacuous exactly above `D.np = 0`**: its `hbv` types the spine `VExpr.bvars (ni + t) D.np` in a
context of length `ni`, and for `D.np > 0` the spine's first element is `.bvar (ni + t + D.np - 1)`,
which no context that short can type.  §6b's `hbv` is the same *shape* of hypothesis, so it has to
be checked rather than assumed — and here it is in scope, for the structural reason that a
constructor's parameter binders sit at the **bottom** of its field context and `VIndCtor.WF.params_len`
says there are exactly `D.np` of them.

The inequality below is precisely "the top index of `VExpr.bvars (bs.length + i) D.np` is less than
the context's length": `bs.length + i + D.np ≤ length`.  So §6b/§8.8 at a *field* of a constructor
is not the motive case; nothing about it is empty above `D.np = 0`.

(This is a scope check, not a proof of `hbv`.  `hbv` itself is now a **theorem** and no longer a
datum: the conversion between the substituted `C.params` that sits in the context and the
`D.params` §8.8 asks for is `VIndCtor.WF.hasArgs_params_bvars_of_wf`
(`Theory/Inductive/TeleMove2.lean` §3), which routes F3's `VIndCtor.WF.params_eq` through
`VEnv.TeleDefEq.of_isDefEqCtx` into `VEnv.HasArgs.congr_tele`.  §7's `hbeta` therefore asks for
**four** components, not five; this scope check is what tells you the spine it produces is typable
at all.) -/

theorem ctorFieldCtx_bvars_in_scope {C : VIndCtor} {σ : CSubst} {i : Nat}
    (hi : i ≤ C.fields.length) (hlen : C.params.length = D.np) (bs : List VExpr) :
    bs.length + i + D.np ≤
      (bs.reverse ++ ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse
        ++ (C.params.map (VExpr.substC · σ)).reverse)).length := by
  simp only [List.length_append, List.length_reverse, List.length_take, List.length_map,
    ← hlen]
  omega

end
end VIndRestore



/-! ## §7 The whole chain: (A) at `D.np > 0` from §8.8's data alone

§3 ∘ §6 ∘ §6b ∘ §6c.  Read the hypotheses as three groups:

* `hD`/`h₃`/`henv₃`/`he₁`/`hσ` — what `ctorConstsCR_wf_of_substC'` already takes;
* `hown`/`hnd`/`hlw`/`hcl`/`hnn`/`hna` — the side conditions on the restoration *data*
  (`decide`-able at a witness), the same six `ctorConstsCR_wf_of_np_zero'` carries minus `hp` and
  minus `hcanon`;
* `hcan` — syntactic: at a recursive field naming a companion, the stored type is canonical, its
  binders name no companion, and its index arguments are `σ`-invariant;
* `hbeta` — **the only typed datum**: §8.8's inputs *minus* `hbv`, i.e. **four** of the five, and
  only at fields whose `recArg` points at a **companion** member.  `hbv` is discharged inside the
  proof from `VIndCtor.WF.hasArgs_params_bvars_of_wf` (`TeleMove2.lean` §3); the only hypothesis
  that discharge adds is `henv : env.Ordered`, which every caller already has (it is what `henv₃`
  is derived from — see §7b).  At a field pointing at the block's own member the head does not move
  at all (`§6b`'s `head_defeq_of_own`), and the typing that closes it comes out of §6c for free.

`hbeta` *is* `hargs` — §8.7's residual, the `val` clause of `(R.csubst D K).WF`, which
`VIndRestore.instAt_indep_of_tyArgs` shows is genuinely data rather than a lemma.  That is this
file's substantive claim: **obligation (A) at `np > 0` bottoms out in the same datum obligations (B)
and (C) do.**  It is a reduction, not a discharge. -/

theorem VEnv.ctorConstsCR_wf_of_betaD {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore}
    (henv : env.Ordered) (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hcan : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T → T.name ∉ K →
      C ∈ T.ctors → ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        F.type = r.canonType D i ∧ (∀ B ∈ r.binders, VExpr.NoConsts K B) ∧
          (∀ a ∈ r.args, a.NoCSubst (R.csubstTy D K)) ∧
          ∃ T' : VIndType, D.types[r.idx]? = some T')
    (hbeta : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T → T.name ∉ K →
      C ∈ T.ctors → ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        ∀ T' : VIndType, D.types[r.idx]? = some T' → T'.name ∈ K →
        ∃ (As : List VExpr) (B B' : VExpr) (v : VLevel),
          OnCtx (D.params.reverse ++
              ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
                ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                  ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)))
            (e₁.IsType D.uvars) ∧
          e₁.HasType D.uvars
              (D.params.reverse ++
                ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
                  ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                    ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)))
              (R.tyBody D r.idx) B ∧
          VExpr.instAll B (VExpr.bvars (r.binders.length + i) D.np) = VExpr.mkPi As B' ∧
          e₁.HasArgs D.uvars
              ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
                ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                  ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse))
              As r.args ∧
          VExpr.instAll B' r.args = VExpr.sort v) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  refine VEnv.ctorConstsCR_wf_of_fieldsD hD h₃ henv₃ he₁ hσ hown ?_
  intro j T C hT hK hCT i F r hF hr hnc
  obtain ⟨hcanF, hb, hargs, T', hT'⟩ := hcan j T C hT hK hCT i F r hF hr hnc
  have hCwf : VIndCtor.WF env₃ D j T C := hD.ctors env₃ h₃ j T hT C hCT
  have hs : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ := hCwf.constant_wf henv₃
  have hfpi : F.type.substC (R.csubstTy D K)
      = VExpr.mkPi (r.binders.map (VExpr.substC · (R.csubstTy D K)))
          ((D.tyApp r.idx (r.binders.length + i) r.args).substC (R.csubstTy D K)) := by
    rw [hcanF, VIndRecArg.canonType, VExpr.substC_mkPi, VIndRecArg.canonResult]
  obtain ⟨hOnΔ, hCd⟩ := VIndRestore.ctorFieldEntry_onCtx he₁ hσ hs hF hfpi
  refine VIndRestore.field_defeq_of_canonical hown hnd hr hcanF hT' hb hOnΔ ?_
  by_cases hK' : T'.name ∈ K
  · obtain ⟨As, B, B', v, hOn, hbody, hpi, hAs, hsort⟩ :=
      hbeta j T C hT hK hCT i F r hF hr hnc T' hT' hK'
    have hbv : e₁.HasArgs D.uvars
        ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
          ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
            ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse))
        D.params (VExpr.bvars (r.binders.length + i) D.np) := by
      have hi : i ≤ C.fields.length := Nat.le_of_lt (by
        simpa using (List.getElem?_eq_some_iff.1 hF).1)
      have hb := hCwf.hasArgs_params_bvars_of_wf henv he₁ hD h₃ hσ
        ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
          (((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse)
      rw [List.append_assoc] at hb
      simpa [Nat.min_eq_left hi] using hb
    exact VIndRestore.head_defeq_of_beta hnd hlw hcl he₁ hnn hna hT' hK' hargs hOn hbv hbody
      hpi hAs hsort
  · exact VIndRestore.head_defeq_of_own hown hT' hK' hCd

/-! ## §7b The whole chain, at the parameterised witness — §7's hypothesis set is jointly inhabited

§7 is a long conjunction, and `docs/vacuity-ledger.md` §0 is explicit that a conjunction of
individually satisfiable hypotheses can still be jointly empty — twice today a strengthening
silently emptied a premise.  `NestedTele.lean` §T4 is the precedent that matters here: the
*motive*-block analogue of §7's `hbv` is vacuous exactly above `D.np = 0`.

So §7 is instantiated at `ntreeAux` — `NTree`/`List`, `D.np = 1`, a real nested block — with every
one of its hypotheses discharged, `hbeta` included.  The `hbeta` witness is `As := []`,
`B = B' := Sort (u+1)`, and its **four** components are `type_tac`; that is the whole β-step at this
block, and it goes through §8.8 rather than by hand.

This is also where the `hbv` discharge is *exercised* rather than merely available: the `HasArgs`
component this witness used to build by hand is gone from it, and nothing replaced it. -/

namespace InductiveDeclExamples

section
variable {env₁ env₂ env₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁) (henv₁ : env₁.Ordered)
variable (h₂ : env₁.addIndTypes ntreeAux = some env₂)
variable (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)

include h henv₁ h₂ h₃ in
/-- **Obligation (A) at `ntreeAux`, through §7 — the general chain, not a bespoke bridge.** -/
theorem ntreeAux_ctorConstsCR_wf_of_betaD :
    ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  have henv₂ : env₂.Ordered :=
    VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' h₂
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  refine VEnv.ctorConstsCR_wf_of_betaD henv₁ ntreeAux_WF' h₂ henv₂ henv₃
    (ntree_csubstTy ▸ ntreeSubst_WF h henv₁ h₂ h₃) ntreeRestore_ownId (by decide)
    ntreeRestore_tyVal_levelWF ntreeRestore_tyArgs_closed
    ntreeRestore_csubstTy_tyName ntreeRestore_tyArgs_noCSubst ?_ ?_
  · rintro j T C hT hK hC i F r hF hr hnc
    match j, hT with
    | 0, hT =>
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      match i, hF with
      | 0, hF => cases hF; exact absurd hr nofun
      | 1, hF => cases hF; cases hr; exact ⟨rfl, nofun, nofun, _, rfl⟩
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT => cases hT; exact absurd (by decide) hK
    | (_ + 2), hT => simp [ntreeAux] at hT
  · rintro j T C hT hK hC i F r hF hr hnc T' hT' hK'
    match j, hT with
    | 0, hT =>
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      match i, hF with
      | 0, hF => cases hF; exact absurd hr nofun
      | 1, hF =>
        cases hF; cases hr; cases hT'
        refine ⟨[], .sort (.succ (.param 0)), .sort (.succ (.param 0)), .succ (.param 0),
          ?_, ?_, rfl, .nil, rfl⟩
        · show OnCtx [VExpr.sort (.succ (.param 0)), VExpr.bvar 0,
              VExpr.sort (.succ (.param 0))] (env₃.IsType 1)
          exact ⟨⟨⟨trivial, ⟨_, by type_tac⟩⟩, ⟨_, by type_tac⟩⟩, ⟨_, by type_tac⟩⟩
        · show env₃.HasType 1 [VExpr.sort (.succ (.param 0)), VExpr.bvar 0,
              VExpr.sort (.succ (.param 0))]
              (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))
              (.sort (.succ (.param 0)))
          type_tac
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT => cases hT; exact absurd (by decide) hK
    | (_ + 2), hT => simp [ntreeAux] at hT

end

end InductiveDeclExamples

end Lean4Lean

/-! ## §8 Axiom lines

Hole-free, and nothing more.  Non-vacuity is §4 and `docs/handoff-ctorbeta.md`. -/
#print axioms Lean4Lean.VIndRestore.substC_fieldTypes_defeq'
#print axioms Lean4Lean.VIndRestore.substC_fieldTypes_defeq_of_noK
#print axioms Lean4Lean.VIndRestore.ctorResult_defeq
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_fieldsD
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_fieldsD
#print axioms Lean4Lean.InductiveDeclExamples.ntree_fld_premise_fires
#print axioms Lean4Lean.VIndRestore.field_defeq_of_canonical
#print axioms Lean4Lean.VIndRestore.substC_tyAppR_free
#print axioms Lean4Lean.VIndRestore.head_defeq_of_beta
#print axioms Lean4Lean.VIndRestore.head_defeq_of_own
#print axioms Lean4Lean.VIndRestore.ctorFieldEntry_onCtx
#print axioms Lean4Lean.VIndRestore.ctorFieldCtx_bvars_in_scope
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_betaD
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_betaD
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorConstsCR_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_field0_free
#print axioms Lean4Lean.VIndRestore.substC_fieldTypes_defeq
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRestore_tyVal_levelWF
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRestore_tyArgs_closed
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRestore_csubstTy_tyName
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRestore_tyArgs_noCSubst
