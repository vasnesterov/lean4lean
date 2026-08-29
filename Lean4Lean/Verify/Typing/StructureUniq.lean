import Lean4Lean.Verify.Typing.ProjLevelWitness

/-!
# `IsStructure` uniqueness (design ledger G4), stated — and split in two

`VEnv.IsStructure` (`Theory/Inductive/Structure.lean`) deliberately does **not** claim that a
name belongs to at most one block; its docstring calls that ledger G4 and says it "needs
`VEnv.Sig` (I1)".  Two lemmas want it: `TrProj.uniq` (`Verify/Typing/Lemmas.lean`), where the
two `(D, T, C)` triples are *given* so nothing can be chosen, and — through it — `TrExprS.uniq`'s
`proj` case.  Until this file the statement **did not exist anywhere in the tree**, which is
worse than an open one: an open statement is visible in the `sorry` census, a missing one is
invisible until someone needs it.

## What is settled here

1. **The equality form — `D₁ = D₂ ∧ T₁ = T₂ ∧ C₁ = C₂` — is FALSE**, and not because of
   anything about environments: `barDecl` and `barDeclEq` below differ only in one
   `VIndField.lvl`, produce *literally the same* `addInduct'` output (`rfl`), and are both
   well-formed.  So both are `IsStructure barEnv `Bar``, at the same environment, through the
   same declaration step.  **No hypothesis on `env` can rescue the equality form** — not
   `VEnv.WF`, not `VEnv.Sig` — because the two derivations share their `decl` witness.
   Writing the equality form would have been a fourth wrong statement of the kind
   `docs/handoff-stratified.md` warns about.

2. **What survives is `StructureAgree`** (below): equality on everything `addInduct'` can see,
   and `≈` on the two fields it cannot — `VInductDecl'.lvl` and `VIndField.lvl`.  That is
   exactly the slack, and it is exactly enough for `TrProj`: `VInductDecl'.projTerm` reads
   `VIndField.lvl` only through `.inst us` inside `projCore`'s `lvls`, where
   `IsDefEq.constDF` accepts `≈`.

3. **The statement splits, and the halves have different prices.**  `IsStructure` pins the
   *three constants* `S`, `C.name` and `S.rec` (proved below: `IsStructure.const_ty`,
   `.const_ctor`, `.const_rec`).  `D.recUvars` and `D.recType 0` are therefore equal across the
   two derivations, and `D.isLE` follows (`IsStructure.isLE_eq`, proved).  Everything else in
   `StructureAgree`'s *syntactic* half is a decomposition of that one term equation — a
   purely syntactic obligation, no `IsDefEq` anywhere, named `RecTypeInj` below.
   The **level half is not**: `VIndField.lvl` occurs in no constant `addInduct'` declares
   (`barDeclEq_recType_eq`, `rfl`), so no syntactic argument can reach it.  Its only source is
   `VIndField.WF.hasType`, which says `F.lvl` is *a* sort of `F.type` in both derivations —
   making the level half a **`SortUniq`-family consumer**, the same family as
   `Theory/Typing/Injectivity.lean`'s `sort_inv`.  That dependency was not recorded anywhere
   before; the ledger's "needs `VEnv.Sig`" names the wrong obligation for this half and does
   not mention the other half is free of environments altogether.

## Auto-bound implicits

Every statement below binds its variables **explicitly** inside a `def … : Prop` or with named
`∀`s, because two statements produced in this development (`Params.extra_pat`,
`Aligned.addInduct`) were false by silent capture.  `#check` output for `StructureUniq`,
`StructureAgree` and `RecTypeInj` is reproduced in `docs/handoff-projections.md`.
-/

namespace Lean4Lean

open VExpr

/-! ## The relation two structure records can be expected to stand in -/

/-- Two records of the same field.  `type` and `recArg` are pinned exactly — they occur in the
constructor's declared type and in the recursor's minor premise — while `lvl` occurs in no
declared constant at all and can only ever be pinned up to `≈`. -/
structure VIndField.Agree (F₁ F₂ : VIndField) : Prop where
  type : F₁.type = F₂.type
  recArg : F₁.recArg = F₂.recArg

/-- The **syntactic half**: everything `addInduct'` writes into a constant.  Deliberately
excludes `VInductDecl'.lvl` and `VIndField.lvl`, which it cannot reach. -/
structure StructureAgree (D₁ : VInductDecl') (T₁ : VIndType) (C₁ : VIndCtor)
    (D₂ : VInductDecl') (T₂ : VIndType) (C₂ : VIndCtor) : Prop where
  uvars : D₁.uvars = D₂.uvars
  params : D₁.params = D₂.params
  isLE : D₁.isLE = D₂.isLE
  tyName : T₁.name = T₂.name
  tyType : T₁.type = T₂.type
  indices : T₁.indices = T₂.indices
  ctorName : C₁.name = C₂.name
  ctorParams : C₁.params = C₂.params
  ctorArgs : C₁.args = C₂.args
  fields : List.Forall₂ VIndField.Agree C₁.fields C₂.fields

/-- The **level half**.  `TrProj` needs it only through `projCore`'s `lvls`, so `≈` is the
right relation and equality is refuted (`structureUniq_eq_false`). -/
structure StructureLvlAgree (D₁ : VInductDecl') (C₁ : VIndCtor)
    (D₂ : VInductDecl') (C₂ : VIndCtor) : Prop where
  lvl : D₁.lvl ≈ D₂.lvl
  fields : ∀ k : Nat, (C₁.fields.getD k default).lvl ≈ (C₂.fields.getD k default).lvl

/-- **The statement, ledger G4.**  `env` declares `S` as at most one structure, up to the slack
`addInduct'` genuinely loses. -/
def VEnv.StructureUniq (env : VEnv) : Prop :=
  ∀ (S : Lean.Name) (D₁ D₂ : VInductDecl') (T₁ T₂ : VIndType) (C₁ C₂ : VIndCtor),
    env.IsStructure S D₁ T₁ C₁ → env.IsStructure S D₂ T₂ C₂ →
      StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ ∧ StructureLvlAgree D₁ C₁ D₂ C₂

/-! ## What `IsStructure` pins, proved

Three constants, and then the recursor's type and universe count. -/

namespace VEnv.IsStructure

variable {env : VEnv} {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

theorem const_ty (H : env.IsStructure S D T C) :
    env.constants S = some ⟨D.uvars, T.type⟩ := by
  obtain ⟨_, _, _, hadd, hle⟩ := H.decl
  exact H.name ▸ hle.constants (VEnv.addInduct'_types hadd (by simp [H.types]))

theorem const_ctor (H : env.IsStructure S D T C) :
    env.constants C.name = some ⟨D.uvars, C.type D 0⟩ := by
  obtain ⟨_, _, _, hadd, hle⟩ := H.decl
  refine hle.constants (VEnv.addInduct'_ctors hadd ?_)
  simp [VInductDecl'.ctorsAll, H.types, H.ctors]

theorem const_rec (H : env.IsStructure S D T C) :
    env.constants (Lean.mkRecName S) = some ⟨D.recUvars, D.recType 0⟩ := by
  obtain ⟨_, _, _, hadd, hle⟩ := H.decl
  refine H.name ▸ hle.constants (VEnv.addInduct'_recs hadd ?_)
  simp [H.types]

end VEnv.IsStructure

/-- **The fingerprint, proved.**  Two structure derivations for one name agree on the
declaration's universe count, the type's declared type, the recursor's universe count and the
recursor's *whole declared type*.  Everything in `StructureAgree` is a consequence of the last
equation; nothing in `StructureLvlAgree` is. -/
theorem VEnv.IsStructure.fingerprint {env : VEnv} {S : Lean.Name}
    {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (H₁ : env.IsStructure S D₁ T₁ C₁) (H₂ : env.IsStructure S D₂ T₂ C₂) :
    D₁.uvars = D₂.uvars ∧ T₁.type = T₂.type ∧
      D₁.recUvars = D₂.recUvars ∧ D₁.recType 0 = D₂.recType 0 := by
  have h1 := H₁.const_ty; have h2 := H₂.const_ty
  have h3 := H₁.const_rec; have h4 := H₂.const_rec
  rw [h1] at h2; rw [h3] at h4
  simp only [Option.some.injEq, VConstant.mk.injEq] at h2 h4
  exact ⟨h2.1, h2.2, h4.1, h4.2⟩

/-- …and `isLE` follows from the two universe counts. -/
theorem VEnv.IsStructure.isLE_eq {env : VEnv} {S : Lean.Name}
    {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (H₁ : env.IsStructure S D₁ T₁ C₁) (H₂ : env.IsStructure S D₂ T₂ C₂) :
    D₁.isLE = D₂.isLE := by
  obtain ⟨hu, -, hru, -⟩ := H₁.fingerprint H₂
  revert hru
  simp only [VInductDecl'.recUvars, hu]
  cases h₁ : D₁.isLE <;> cases h₂ : D₂.isLE <;> simp <;> omega

/-- **The syntactic residual of `StructureUniq`.**  Everything about the environment has been
discharged by `fingerprint`; what is left is that `VInductDecl'.recType` determines the block
data it is built from.  No `IsDefEq`, no `VEnv`, no universe reasoning — a decomposition of one
`mkPi` telescope.

*Collapse test.*  Its premises are term equations; the target's are two `IsStructure`
derivations.  Instantiating `D₁ = D₂` degenerates `RecTypeInj` to reflexivity, which does not
degenerate `StructureUniq` (whose two derivations may still carry different records — that is
exactly `structureUniq_eq_false`).  So this is a reduction, not a restatement. -/
def RecTypeInj : Prop :=
  ∀ (D₁ D₂ : VInductDecl') (T₁ T₂ : VIndType) (C₁ C₂ : VIndCtor),
    D₁.types = [T₁] → T₁.ctors = [C₁] → D₂.types = [T₂] → T₂.ctors = [C₂] →
    C₁.recFields = [] → C₂.recFields = [] →
    D₁.uvars = D₂.uvars → T₁.name = T₂.name → T₁.type = T₂.type →
    D₁.isLE = D₂.isLE → D₁.recType 0 = D₂.recType 0 →
    StructureAgree D₁ T₁ C₁ D₂ T₂ C₂

/-- **The syntactic half of G4 reduces to `RecTypeInj`, proved.**  This is the whole
environment-side argument; note that no hypothesis on `env` is used, which contradicts the
ledger's "needs `VEnv.Sig` (I1)" *for this half*. -/
theorem structureAgree_of_recTypeInj (h : RecTypeInj) {env : VEnv} {S : Lean.Name}
    {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (H₁ : env.IsStructure S D₁ T₁ C₁) (H₂ : env.IsStructure S D₂ T₂ C₂) :
    StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ := by
  obtain ⟨hu, hty, -, hrt⟩ := H₁.fingerprint H₂
  exact h D₁ D₂ T₁ T₂ C₁ C₂ H₁.types H₁.ctors H₂.types H₂.ctors H₁.noRec H₂.noRec
    hu (H₁.name.trans H₂.name.symm) hty (H₁.isLE_eq H₂) hrt

/-! ## The refutation of the equality form, and the non-vacuity check

`barDeclEq` is `barDecl` (`Verify/Typing/ProjLevelWitness.lean` — the tree's second complete
`VInductDecl'.WF` witness, and the first with two fields) with field 0's *recorded* level
replaced by an equivalent one.  `addInduct'` cannot see the difference. -/

/-- `barField0` with a different but `≈`-equal recorded level. -/
def barField0eq : VIndField := { barField0 with lvl := .max (.succ .zero) (.succ .zero) }
def barCtorEq : VIndCtor := { barCtor with fields := [barField0eq, barField1] }
def barTypeEq : VIndType := { barType with ctors := [barCtorEq] }
def barDeclEq : VInductDecl' := { barDecl with types := [barTypeEq] }

/-- **The two declarations produce the same environment**, by `rfl`. -/
theorem barDeclEq_addInduct : VEnv.empty.addInduct' barDeclEq = VEnv.empty.addInduct' barDecl :=
  rfl

/-- …and, in particular, the same recursor type: **`VIndField.lvl` is invisible to the
fingerprint**, so `StructureLvlAgree` cannot be a consequence of `RecTypeInj`. -/
theorem barDeclEq_recType_eq : barDeclEq.recType 0 = barDecl.recType 0 := rfl

theorem barDeclEq_WF : barDeclEq.WF .empty where
  types_ne := by simp [barDeclEq, barDecl]
  params := trivial
  types := by
    intro T hT
    simp [barDeclEq, barDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [barDeclEq, barDecl] at hT
      subst hT
      simp [barTypeEq, barType] at hC
      subst hC
      have hc : env₁.constants `Bar = some ⟨0, VExpr.sort .zero⟩ := by
        simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, barDeclEq, barDecl,
          barTypeEq, barType, VEnv.addConst, VEnv.empty] at he
        subst he; simp
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp [barCtorEq, barCtor],
               args_ty := .nil,
               result := .constDF hc nofun nofun rfl .nil }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp [barCtorEq, barCtor] at hF
        subst hF
        refine { hasType := ?_
                 level := fun ls => by simp [VLevel.eval, barDeclEq, barDecl, Lean.Nat.imax]
                 binders_indep := nofun
                 pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                         _, .sortDF trivial trivial (.refl _)⟩ }
        have h0 : env₁.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
          .sortDF trivial trivial (.refl _)
        have hlv : VEnv.IsDefEq env₁ 0 []
            (.sort (.succ .zero)) (.sort barField0eq.lvl) (.sort (.succ (.succ .zero))) :=
          .sortDF trivial ⟨trivial, trivial⟩
            (by simp [barField0eq, VLevel.equiv_def, VLevel.eval])
        exact hlv.defeqDF h0
      | 1, hF =>
        simp [barCtorEq, barCtor] at hF
        subst hF
        have hty : env₁.HasType barDeclEq.uvars
            ((List.map (fun x => x.type) (List.take 1 barCtorEq.fields)).reverse
              ++ barDeclEq.params.reverse)
            barField1.type (.sort barField1.lvl) := by
          show env₁.HasType 0 [barField0eq.type] _ _
          refine .forallEDF (.sortDF trivial trivial (.refl _)) ?_
          exact .bvar (.zero ..)
        exact { hasType := hty
                level := fun ls => by
                  simp [VLevel.eval, barDeclEq, barDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨barField1.type,
                        by simp [VInductDecl'.NoBlock, VExpr.NoConsts, barField1],
                        _, hty⟩ }
  isLE := by simp [barDeclEq, barDecl]

/-- **The same environment is a structure environment for `Bar` twice**, through the same
`addInduct'` step, with two *different* records. -/
theorem barEnv_IsStructureEq : barEnv.IsStructure `Bar barDeclEq barTypeEq barCtorEq where
  types := rfl
  name := rfl
  ctors := rfl
  noRec := rfl
  decl := ⟨.empty, barEnv, barDeclEq_WF, barDeclEq_addInduct.trans barEnv_eq.choose_spec,
    VEnv.LE.rfl⟩

/-- **The equality form of G4 is FALSE**, at an environment produced by a single well-formed
`addInduct'` step from `VEnv.empty`.  Both derivations share their `decl` witness, so this is
not repaired by any hypothesis on `env`. -/
theorem structureUniq_eq_false :
    ¬ ∀ (env : VEnv) (S : Lean.Name) (D₁ D₂ : VInductDecl') (T₁ T₂ : VIndType)
        (C₁ C₂ : VIndCtor), env.IsStructure S D₁ T₁ C₁ → env.IsStructure S D₂ T₂ C₂ →
        D₁ = D₂ ∧ T₁ = T₂ ∧ C₁ = C₂ := by
  intro h
  have := (h barEnv `Bar barDecl barDeclEq barType barTypeEq barCtor barCtorEq
    barEnv_IsStructure barEnv_IsStructureEq).1
  have := congrArg (fun D => (D.types.getD 0 default).ctors) this
  simp [barDecl, barDeclEq, barType, barTypeEq, barCtor, barCtorEq, barField0,
    barField0eq] at this

/-! ## Non-vacuity: both halves fire at the two-field witness

A statement about structures tested only at a one-field structure has not been shown
non-vacuous.  `barCtor` has two fields, one of them a `Prop` and one of them *not*
`≈ .zero` — the configuration that made `barRefutes` work. -/

theorem barDeclEq_StructureAgree :
    StructureAgree barDecl barType barCtor barDeclEq barTypeEq barCtorEq where
  uvars := rfl
  params := rfl
  isLE := rfl
  tyName := rfl
  tyType := rfl
  indices := rfl
  ctorName := rfl
  ctorParams := rfl
  ctorArgs := rfl
  fields := .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil)

theorem barDeclEq_StructureLvlAgree :
    StructureLvlAgree barDecl barCtor barDeclEq barCtorEq where
  lvl := .refl _
  fields := by
    intro k
    match k with
    | 0 => simp [barCtor, barCtorEq, barField0, barField0eq, VLevel.equiv_def, VLevel.eval]
    | 1 => exact .refl _
    | (_+2) => exact .refl _

/-- **The pair `(barDecl, barDeclEq)` is an instance of `StructureUniq`'s conclusion at
`barEnv`** — so the statement is satisfiable exactly where the equality form is refuted, which
is what makes `≈` the right relation rather than a weakening chosen to dodge the witness. -/
theorem barEnv_structureUniq_at_witness :
    StructureAgree barDecl barType barCtor barDeclEq barTypeEq barCtorEq ∧
      StructureLvlAgree barDecl barCtor barDeclEq barCtorEq :=
  ⟨barDeclEq_StructureAgree, barDeclEq_StructureLvlAgree⟩

end Lean4Lean
