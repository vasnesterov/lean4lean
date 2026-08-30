import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Theory.Inductive.StructureClosed
import Lean4Lean.Theory.Typing.Injectivity

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
   two derivations, and `D.isLE` follows (`IsStructure.isLE_eq`, proved).

4. **The level half is PROVED** (`structureLvlAgree_of_structureAgree`), *given* the syntactic
   half.  `VIndField.lvl` occurs in no constant `addInduct'` declares (`barDeclEq_recType_eq`,
   `rfl`), so no syntactic argument can reach it; its only source is `VIndField.WF.hasType`,
   which makes it a `SortUniq`-family consumer.  When this file was written `SortUniq` was a
   hypothesis nothing exhibited; it is now a **theorem** (`VEnv.WF.sortUniq'`,
   `Theory/Typing/Injectivity.lean`, relative to `IsDefEqU.forallE_inv_stratified` alone), so
   the half closes.

5. **`RecTypeInj` — the syntactic residual originally recorded below — is FALSE**
   (`recTypeInj_false`).  `StructureAgree.ctorParams` claims `C₁.params = C₂.params`, and
   `C.params` occurs *nowhere* in `D.recType`; it is spliced only into `VIndCtor.type`, the
   constructor constant.  So `structureAgree_of_recTypeInj` is a reduction to a statement that
   can never be supplied.  The repair is `structureAgree_ctor`: three of `StructureAgree`'s ten
   fields — `ctorParams`, the field `type`s and `ctorArgs` — come off the **constructor
   constant** via `VIndCtor.skeleton_type`, given only `C₁.name = C₂.name` and
   `D₁.np = D₂.np`.  See `docs/handoff-projections.md` for what is left after that.

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

/-! ## The level half, discharged

`SortUniq` was recorded above as this half's blocker, and at the time it was a hypothesis
nothing in the tree exhibited.  It is now a **theorem**: `VEnv.WF.sortUniq'`
(`Theory/Typing/Injectivity.lean`) proves `env.SortUniq U` for every `VEnv.WF` environment,
with `IsDefEqU.forallE_inv_stratified` as its only open input.  So the level half closes,
*given the syntactic half* — which is the direction that matters, because `VIndField.lvl` is
invisible to every constant `addInduct'` declares and the syntactic half is what supplies the
two derivations with a common context and a common subject.

The only environment fact used is `VIndCtor.WF env D 0 T C` **at `env` itself**, which
`VEnv.IsStructure.iotaCtx` delivers (`RecCtx.ctors`); no manual transport along the
`addInduct'` stages is needed. -/

section LvlHalf

open VExpr

/-- The constructor's well-formedness at `env` itself.  `IsStructure.decl` records the block
at a *past* environment; `iotaCtx` transports it forward. -/
theorem VEnv.IsStructure.ctorWF {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {T : VIndType} {C : VIndCtor} (henv : env.Ordered) (H : env.IsStructure S D T C) :
    VIndCtor.WF env D 0 T C :=
  (H.iotaCtx henv).toRecCtx.ctors 0 T H.types0 C H.memCtor

theorem VIndField.Agree.map_type : ∀ {l₁ l₂ : List VIndField},
    List.Forall₂ VIndField.Agree l₁ l₂ → l₁.map (·.type) = l₂.map (·.type)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h t => by simp [h.type, VIndField.Agree.map_type t]

theorem StructureAgree.fields_map {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType}
    {C₁ C₂ : VIndCtor} (hA : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) :
    C₁.fields.map (·.type) = C₂.fields.map (·.type) :=
  VIndField.Agree.map_type hA.fields

theorem StructureAgree.fields_length {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType}
    {C₁ C₂ : VIndCtor} (hA : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) :
    C₁.fields.length = C₂.fields.length := by
  simpa using congrArg List.length hA.fields_map

/-- **The level half of ledger G4, discharged.**  Given the syntactic half — which is exactly
what makes the two `VIndField.WF.hasType` derivations speak about the *same* term in the
*same* context — universe uniqueness delivers `≈` on every recorded level.

This is the statement `StructureUniq.lean` originally recorded as blocked on the
`SortUniq` family.  Nothing about `VEnv.Sig` is used, and `RecTypeInj` is not used either:
this half takes the syntactic half as a hypothesis rather than deriving it. -/
theorem structureLvlAgree_of_structureAgree {env : VEnv} {S : Lean.Name}
    {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (henv : VEnv.WF env)
    (H₁ : env.IsStructure S D₁ T₁ C₁) (H₂ : env.IsStructure S D₂ T₂ C₂)
    (hA : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) :
    StructureLvlAgree D₁ C₁ D₂ C₂ := by
  have hord := henv.ordered
  have huniq : env.SortUniq D₁.uvars := VEnv.WF.sortUniq' henv
  have hC₁ := H₁.ctorWF hord
  have hC₂ := H₂.ctorWF hord
  have hu := hA.uvars
  have hmap := hA.fields_map
  have hlen := hA.fields_length
  constructor
  · -- `D.lvl`: the constructor's result type is typed at it in both derivations.
    have hΓ₁ := hC₁.onCtxAllFields hord
    have hr₁ := hC₁.result
    have hr₂ := hC₂.result
    have hctx : ((C₂.fields.map (·.type)).reverse ++ D₂.params.reverse)
        = ((C₁.fields.map (·.type)).reverse ++ D₁.params.reverse) := by
      rw [hmap, hA.params]
    have hres : C₂.canonResult D₂ 0 = C₁.canonResult D₁ 0 := by
      simp only [VIndCtor.canonResult, VInductDecl'.tyApp, VInductDecl'.ownLvls,
        VInductDecl'.np, hu, hA.params, hA.ctorArgs, hlen,
        H₁.typesD, H₂.typesD, H₁.name, H₂.name]
    rw [hctx, hres, ← hu] at hr₂
    exact huniq hΓ₁ (hr₁.sort_r hord hΓ₁) (hr₂.sort_r hord hΓ₁) hr₁ hr₂
  · -- the field levels
    intro k
    by_cases hk : k < C₁.fields.length
    · have hk₂ : k < C₂.fields.length := hlen ▸ hk
      have hg₁ : C₁.fields[k]? = some (C₁.fields.getD k default) := by
        rw [List.getElem?_eq_getElem hk]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      have hg₂ : C₂.fields[k]? = some (C₂.fields.getD k default) := by
        rw [List.getElem?_eq_getElem hk₂]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₂]
      have hty : (C₁.fields.getD k default).type = (C₂.fields.getD k default).type := by
        have h1 : (C₁.fields.map (·.type))[k]? = some (C₁.fields.getD k default).type := by
          rw [List.getElem?_map, hg₁]; rfl
        have h2 : (C₂.fields.map (·.type))[k]? = some (C₂.fields.getD k default).type := by
          rw [List.getElem?_map, hg₂]; rfl
        rw [hmap, h2] at h1
        exact (Option.some.inj h1).symm
      have hf₁ := (hC₁.fields k _ hg₁).hasType
      have hf₂ := (hC₂.fields k _ hg₂).hasType
      have hΓ₁ := hC₁.onCtxFields hord k
      have hctx : (((C₂.fields.take k).map (·.type)).reverse ++ D₂.params.reverse)
          = (((C₁.fields.take k).map (·.type)).reverse ++ D₁.params.reverse) := by
        rw [hA.params, List.map_take, List.map_take, hmap]
      rw [hctx, ← hty, ← hu] at hf₂
      exact huniq hΓ₁ (hf₁.sort_r hord hΓ₁) (hf₂.sort_r hord hΓ₁) hf₁ hf₂
    · have hk₂ : ¬ k < C₂.fields.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact .refl _

end LvlHalf

/-! ## `RecTypeInj` is FALSE, and the syntactic half has to be re-routed

The section above reduced `StructureAgree` to `RecTypeInj` and described that as "the whole
environment-side argument".  **`RecTypeInj` is refuted below.**  The defect is not subtle once
it is pointed at: `StructureAgree.ctorParams` claims `C₁.params = C₂.params`, and `C.params`
**does not occur in `D.recType`** — not in `motiveType`, not in `minorType`, not in `ihType`,
not in `ctorApp'`, not in `tyApp'`.  The recursor is built over `D.params`; the constructor's
own copy `C.params` (F3) is spliced only into `VIndCtor.type`, the *constructor constant's*
type.  So a hypothesis set that mentions only `recType` cannot possibly pin it.

Because `structureAgree_of_recTypeInj` derives `StructureAgree` **from** `RecTypeInj`, that
theorem is a reduction to a false statement: it is true, and it is useless — its premise can
never be supplied.  This is the fifth statement in this development to turn out false rather
than open, and the third whose defect is a missing hypothesis rather than a wrong conclusion.

The re-route is in the next section: `C.params`, the field *types* and `C.args` come off the
**constructor constant** through `VIndCtor.skeleton_type`, which inverts `VIndCtor.type` on the
nose.  What the recursor type is actually needed for shrinks to one number, `D.np`. -/

/-- `barCtor` with a different parameter copy.  It is deliberately *ill-formed* — `barDecl.np`
is `0`, so `VIndCtor.WF.params_len` fails — because `RecTypeInj` asks for no well-formedness
whatsoever; that is the defect. -/
def barCtorPar : VIndCtor := { barCtor with params := [.sort .zero] }
def barTypePar : VIndType := { barType with ctors := [barCtorPar] }
def barDeclPar : VInductDecl' := { barDecl with types := [barTypePar] }

/-- **`C.params` is invisible to the recursor type**, by `rfl`, at the tree's two-field
witness. -/
theorem barDeclPar_recType_eq : barDeclPar.recType 0 = barDecl.recType 0 := rfl

/-- …and to the *whole* `addInduct'` step except the constructor constant: the recursor
constants and the ι-rules are identical. -/
theorem barDeclPar_recs_eq :
    (barDeclPar.recConsts, barDeclPar.iotaRules) = (barDecl.recConsts, barDecl.iotaRules) := rfl

/-- **`RecTypeInj` is false.** -/
theorem recTypeInj_false : ¬ RecTypeInj := by
  intro h
  have hA := h barDecl barDeclPar barType barTypePar barCtor barCtorPar
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl barDeclPar_recType_eq.symm
  have := hA.ctorParams
  simp [barCtor, barCtorPar] at this

/-! ## The re-route: the constructor constant pins three of the ten fields

`VIndCtor.skeleton` (`Theory/Inductive/Decl.lean`) splits a constructor's *stored* type back
into `(params, field types, result args)`, and `VIndCtor.skeleton_type` proves the round trip
holds on the nose given only `C.params.length = D.np` — which `VIndCtor.WF.params_len` records.
So once the two derivations agree on the constructor's **name** and on **`D.np`**, the
constructor constant hands over `ctorParams`, the field `type`s and `ctorArgs` with no
recursor reasoning at all.

`nf` needs no separate hypothesis: `C.type D j` is `mkPi` of exactly `np + nf` binders over a
`mkApp`, which is never a `.forallE`, so the binder count is read off the term. -/

/-- The number of leading `∀` binders of an expression. -/
def VExpr.piDepth : VExpr → Nat
  | .forallE _ b => b.piDepth + 1
  | _ => 0

theorem VExpr.piDepth_mkPi : ∀ (As : List VExpr) (b : VExpr), b.piDepth = 0 →
    (VExpr.mkPi As b).piDepth = As.length
  | [], b, h => h
  | _ :: As, b, h => by
    rw [VExpr.mkPi]; simp [VExpr.piDepth, VExpr.piDepth_mkPi As b h]

theorem VExpr.piDepth_mkApp : ∀ (as : List VExpr) (e : VExpr), e.piDepth = 0 →
    (e.mkApp as).piDepth = 0
  | [], _, h => h
  | _ :: as, _, _ => VExpr.piDepth_mkApp as _ rfl

theorem VExpr.piDepth_mkApp_const (c : Lean.Name) (us : List VLevel) (as : List VExpr) :
    ((VExpr.const c us).mkApp as).piDepth = 0 := VExpr.piDepth_mkApp as _ rfl

/-- **The constructor's stored type carries its own binder count.** -/
theorem VIndCtor.piDepth_type (C : VIndCtor) (D : VInductDecl') (j : Nat)
    (hp : C.params.length = D.np) :
    (C.type D j).piDepth = D.np + C.fields.length := by
  rw [VIndCtor.type, VExpr.piDepth_mkPi _ _ ?_, List.length_append, List.length_map, hp]
  exact VExpr.piDepth_mkApp_const ..

/-- **Three of `StructureAgree`'s ten fields, off the constructor constant.**  No recursor
type, no `RecTypeInj`; the only two inputs are the constructor's name and the parameter count.

This is the part of the syntactic half that `RecTypeInj` claimed and could not deliver. -/
theorem structureAgree_ctor {env : VEnv} {S : Lean.Name}
    {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (henv : env.Ordered)
    (H₁ : env.IsStructure S D₁ T₁ C₁) (H₂ : env.IsStructure S D₂ T₂ C₂)
    (hname : C₁.name = C₂.name) (hnp : D₁.np = D₂.np) :
    C₁.params = C₂.params ∧ C₁.fields.map (·.type) = C₂.fields.map (·.type) ∧
      C₁.args = C₂.args := by
  have hp₁ := (H₁.ctorWF henv).params_len
  have hp₂ := (H₂.ctorWF henv).params_len
  have hu := (H₁.fingerprint H₂).1
  have hty : C₁.type D₁ 0 = C₂.type D₂ 0 := by
    have h1 := H₁.const_ctor
    have h2 := H₂.const_ctor
    rw [hname, h2, hu] at h1
    simpa using (Option.some.inj h1).symm
  have hnf : C₁.fields.length = C₂.fields.length := by
    have d₁ := C₁.piDepth_type D₁ 0 hp₁
    have d₂ := C₂.piDepth_type D₂ 0 hp₂
    rw [hty, d₂] at d₁; omega
  have hs₁ := C₁.skeleton_type D₁ 0 hp₁
  have hs₂ := C₂.skeleton_type D₂ 0 hp₂
  rw [hty, hnf, hnp, hs₂] at hs₁
  exact ⟨congrArg Prod.fst hs₁.symm, congrArg (Prod.fst ∘ Prod.snd) hs₁.symm,
    congrArg (Prod.snd ∘ Prod.snd) hs₁.symm⟩

/-- The field records agree outright, for a structure: `recArg` is `none` on both sides
because `IsStructure.noRec` says there are no recursive fields. -/
theorem VIndCtor.recArg_eq_none {C : VIndCtor} (h : C.recFields = []) :
    ∀ F ∈ C.fields, F.recArg = none := by
  intro F hF
  obtain ⟨i, hi⟩ := List.mem_iff_getElem.1 hF
  cases hr : F.recArg with
  | none => rfl
  | some r =>
    exact absurd (h ▸ (show (i, r) ∈ C.recFields from by
      simp only [VIndCtor.recFields, List.mem_filterMap, List.mem_zipIdx_iff_getElem?]
      exact ⟨(F, i), by simp [List.getElem?_eq_getElem hi.1, hi.2], by simp [hr]⟩)) nofun

/-! ## G4, assembled: what is actually left

With the level half proved and the constructor constant supplying three of `StructureAgree`'s
ten fields, `VEnv.StructureUniq` reduces to **three syntactic equations** — and they are
equations `D.recType 0` really does determine, unlike `C.params`, which it does not (that is
`recTypeInj_false`).

`RecTypeResidual` is what `RecTypeInj` should have been.  It is stated *at* the two
`IsStructure` derivations rather than as a free-standing syntactic implication, because the
recursor-type decomposition genuinely needs one environment fact — the block's own constants do
not occur in `D.params` or `T.indices`, which is what pins the split point between the
parameter block and the motive.  `RecTypeInj` had no environment hypothesis at all, and that is
precisely why it is false. -/

theorem VIndField.Agree.forall₂_of : ∀ {l₁ l₂ : List VIndField},
    l₁.map (·.type) = l₂.map (·.type) →
    (∀ F ∈ l₁, F.recArg = none) → (∀ F ∈ l₂, F.recArg = none) →
    List.Forall₂ VIndField.Agree l₁ l₂
  | [], [], _, _, _ => .nil
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l₁, b :: l₂, h, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons ⟨h.1, by rw [h1 a (by simp), h2 b (by simp)]⟩
      (VIndField.Agree.forall₂_of h.2 (fun F hF => h1 F (by simp [hF]))
        (fun F hF => h2 F (by simp [hF])))

/-- **The residual of ledger G4.**  Three equations, all of them things the recursor's declared
type does determine. -/
def VEnv.RecTypeResidual (env : VEnv) : Prop :=
  ∀ (S : Lean.Name) (D₁ D₂ : VInductDecl') (T₁ T₂ : VIndType) (C₁ C₂ : VIndCtor),
    env.IsStructure S D₁ T₁ C₁ → env.IsStructure S D₂ T₂ C₂ →
      D₁.params = D₂.params ∧ T₁.indices = T₂.indices ∧ C₁.name = C₂.name

/-- **G4 reduces to `RecTypeResidual`, plus `VEnv.WF`.**  Both halves — syntactic and level —
are discharged here; nothing about `VEnv.Sig` is used anywhere. -/
theorem VEnv.structureUniq_of {env : VEnv} (henv : VEnv.WF env)
    (hres : env.RecTypeResidual) : env.StructureUniq := by
  intro S D₁ D₂ T₁ T₂ C₁ C₂ H₁ H₂
  obtain ⟨hpar, hidx, hname⟩ := hres S D₁ D₂ T₁ T₂ C₁ C₂ H₁ H₂
  have hnp : D₁.np = D₂.np := by rw [VInductDecl'.np, VInductDecl'.np, hpar]
  obtain ⟨hcp, hcf, hca⟩ := structureAgree_ctor henv.ordered H₁ H₂ hname hnp
  have hA : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ :=
    { uvars := (H₁.fingerprint H₂).1
      params := hpar
      isLE := H₁.isLE_eq H₂
      tyName := H₁.name.trans H₂.name.symm
      tyType := (H₁.fingerprint H₂).2.1
      indices := hidx
      ctorName := hname
      ctorParams := hcp
      ctorArgs := hca
      fields := VIndField.Agree.forall₂_of hcf
        (fun F hF => by
          have := VIndCtor.recArg_eq_none H₁.noRec F hF; exact this)
        (fun F hF => by
          have := VIndCtor.recArg_eq_none H₂.noRec F hF; exact this) }
  exact ⟨hA, structureLvlAgree_of_structureAgree henv H₁ H₂ hA⟩

end Lean4Lean
