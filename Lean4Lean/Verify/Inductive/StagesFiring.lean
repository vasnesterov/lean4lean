import Lean4Lean.Verify.Inductive.RunIdentity
import Lean4Lean.Verify.Inductive.Add

/-!
# Row 113a: `AddInductStages` at the map the executable actually builds

`docs/vacuity-ledger.md` row 113a reports that the tree has **no firing instance** of
`AddInductStages`: `R10.Wit.addInductStages_wit` (`Verify/Environment/Basic.lean`) exhibits an
`m'` of its own making, and `AddInductStages … R10.Wit.decl … m' …` is *false* for the `m'` the
checker produces, because `AddInductive.run` stores `R10.Wit.U.rec` with `levelParams = [u]`
while `R10.Wit.decl.recUvars = 0`.

This file does three things.

* §1 — the **general** mechanism, not the witness's instance of it: `AddInductStages` pins the
  stored `levelParams.length` of every recursor it declares to `D.recUvars`
  (`r113a_addInductStages_recUvars`).  So a block on which `isLargeEliminator` answers `true`
  can only be modelled by a `D` with `isLE = true`, and row 113a's `1 = 0` is this lemma at
  `R10.Wit.decl`.
* §2 — the refutation, as a theorem about any map storing a `levelParams ≠ []` recursor
  (`r113a_not_addInductStages_of_rec_lp`), plus the executed fact that the checker's map is
  such a map (§4's guard).
* §3 — the **repair**, carried out: `r113aDeclLE` is `R10.Wit.decl` with `isLE := true`, and
  `AddInductStages` holds of it at the map whose three entries are *exactly* the three
  `ConstantInfo`s the executable stores (`r113a_addInductStages_firing`), so `InductStepSafe`
  finally has an instance at the checker's own output (`r113a_inductStepSafe_firing`).

**What this does not do.**  The repair is *not* applied to `R10.Wit.decl` itself: that record,
`R10.Wit.recTypeE`, `R10.Wit.uRec` and `R10.Wit.tr_recType` all live in
`Verify/Environment/Basic.lean`, which this file's author does not own.  The corrected witness
is built here instead, and it is a *drop-in*: `TrIndDecl` never mentions `isLE`
(`Verify/Environment/Induct.lean`), and neither does `VIndType.WF` or `VIndCtor.WF` at
`uvars = 0`, so §3's `TrIndDecl` and `WF` proofs are `R10.Wit.trIndDecl_wit`'s and
`R10.Wit.decl_WF`'s verbatim with the one `isLE` field replaced.

**`D.Canonical` is deliberately absent** (`docs/vacuity-ledger.md` row 113 refutes the node
through it, and the repair there is a separate ruling), and **no `RecShape` is added** (row
113c) — `uRecReal`'s `rules`, `k`, `numMotives`, `numMinors` are recorded here only so that §4's
guard can compare them, not because `AddInductStages` constrains them.  It does not.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. `AddInductStages` pins each recursor's `levelParams.length` to `D.recUvars`

The chain is short and entirely inside the third fold: `AddIndConsts`' `cons` step carries a
`TrConstant .safe`, whose second conjunct is `ci.levelParams.length = ci'.uvars`, and
`D.recConsts` gives every entry the same `ci'.uvars = D.recUvars`.

The `Nodup` side condition is not decoration: without it a later insert could shadow the entry
the lemma reads back.  It is discharged for a real block by `addInduct'`'s own freshness, and at
a one-type block by `List.nodup_singleton`. -/

/-- One `AddIndConsts` fold reports back, at each name it inserts, the `ConstantInfo` it
inserted — with the stage's shape and the `TrConstant` universe count. -/
theorem r113a_addIndConsts_levelParams {S : ConstantInfo → Prop} :
    ∀ {cs : List (Name × VConstant)} {m env m₂ env₂ : _} {n : Name} {ci' : VConstant},
      AddIndConsts S cs m env m₂ env₂ → m.WF → (cs.map (·.1)).Nodup → (n, ci') ∈ cs →
      ∃ ci, m₂.find? n = some ci ∧ S ci ∧ ci.name = n ∧ ci.levelParams.length = ci'.uvars := by
  intro cs m env m₂ env₂ n ci' H
  induction H with
  | nil => intro _ _ h; cases h
  | @cons ci n₀ ci₀ cs m _ _ _ _ hname hS htr hfr _ hrest ih =>
    intro hwf hnd hmem
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd hmem
    rcases hmem with hmem | hmem
    · cases hmem
      refine ⟨ci, ?_, hS, hname, htr.2.1⟩
      rw [hrest.find?_of_not_mem (hwf.insert _ _ hfr) hnd.1, hwf.find?_insert]
      simp
    · exact ih (hwf.insert _ _ hfr) hnd.2 hmem

/-- **The general form of row 113a.**  Every recursor `AddInductStages` declares is stored with
`D.recUvars` universe parameters.  `D.recUvars = if D.isLE then D.uvars + 1 else D.uvars`
(`Theory/Inductive/Decl.lean`), so a checker that prepends a *fresh* elimination level — which
`getElimLevel` does exactly when `isLargeEliminator` answers `true` — forces `D.isLE = true`. -/
theorem r113a_addInductStages_recUvars {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {T : VIndType} {j : Nat}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hnd : (D.recConsts.map (·.1)).Nodup) (hT : (T, j) ∈ D.types.zipIdx) :
    ∃ ci, m₂.find? (Lean.mkRecName T.name) = some ci ∧ (∃ v, ci = .recInfo v) ∧
      ci.levelParams.length = D.recUvars := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, -⟩ := H
  have hmem : (Lean.mkRecName T.name, (⟨D.recUvars, D.recType j⟩ : VConstant)) ∈ D.recConsts := by
    simpa only [VInductDecl'.recConsts, List.mem_map] using ⟨(T, j), hT, rfl⟩
  obtain ⟨ci, hfind, hS, -, hlen⟩ :=
    r113a_addIndConsts_levelParams h3 (h2.map_wf (h1.map_wf hwf)) hnd hmem
  exact ⟨ci, hfind, hS, hlen⟩

/-! ## 2. The refutation at `R10.Wit.decl`

`R10.Wit.decl` has `uvars = 0` and `isLE = false`, so `recUvars = 0` and §1 forces the stored
`U.rec` to carry **no** universe parameters.  The checker stores `[u]`. -/

theorem r113a_wit_recUvars_zero : R10.Wit.decl.recUvars = 0 := rfl

theorem r113a_wit_recConsts_nodup : (R10.Wit.decl.recConsts.map (·.1)).Nodup := by
  simp [VInductDecl'.recConsts, R10.Wit.decl]

/-- **`AddInductStages` at `R10.Wit.decl` forces `U.rec`'s stored `levelParams` to be `[]`.** -/
theorem r113a_wit_rec_levelParams_nil {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {ci : ConstantInfo}
    (H : AddInductStages m₁ env₁ R10.Wit.decl m₂ env₂) (hwf : m₁.WF)
    (h : m₂.find? `R10.Wit.U.rec = some ci) : ci.levelParams = [] := by
  obtain ⟨ci', hfind, -, hlen⟩ := r113a_addInductStages_recUvars H hwf r113a_wit_recConsts_nodup
    (T := (R10.Wit.decl.types.getD 0 default)) (j := 0) (by simp [R10.Wit.decl])
  rw [show Lean.mkRecName (R10.Wit.decl.types.getD 0 default).name = `R10.Wit.U.rec from rfl,
    h] at hfind
  cases hfind
  exact List.eq_nil_of_length_eq_zero (hlen.trans r113a_wit_recUvars_zero)

/-- **Row 113a as a theorem.**  No constant map that stores `U.rec` with a nonempty
`levelParams` can be the output of `AddInductStages` at `R10.Wit.decl` — and §4's guard is the
executed fact that the checker's map is one of those. -/
theorem r113a_not_addInductStages_of_rec_lp {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {ci : ConstantInfo} (hwf : m₁.WF)
    (h : m₂.find? `R10.Wit.U.rec = some ci) (hlp : ci.levelParams ≠ []) :
    ¬ AddInductStages m₁ env₁ R10.Wit.decl m₂ env₂ :=
  fun H => hlp (r113a_wit_rec_levelParams_nil H hwf h)

/-! ## 3. The repair, carried out

`r113aDeclLE` is `R10.Wit.decl` with the single field `isLE` flipped to `true`.  Three things
change and nothing else:

| | at `isLE = false` | at `isLE = true` |
| --- | --- | --- |
| `recUvars` | `0` | `1` |
| `elimLvl` | `.zero` | `.param 0` |
| `selfLvls` | `[]` | `[]` (`uvars = 0`, so `atRec` is unchanged) |

So `recType 0`'s motive codomain becomes `.sort (.param 0)`, which is what the executable's
`Sort u` translates to, and `recConsts`' `VConstant.uvars` becomes `1`, which is what its
`levelParams = [u]` has length.  `params`/`types`/`ctorConsts`/`typeConsts` are untouched, and
`atRec` is untouched because `selfLvls` is `[]` either way at `uvars = 0` — which is why §3.1's
`TrIndDecl` and §3.2's `WF` are the existing proofs with one field changed. -/

namespace R113a

/-- `R10.Wit.decl` with `isLE := true`: the repair row 113a reports. -/
def declLE : VInductDecl' := { R10.Wit.decl with isLE := true }

theorem declLE_recUvars : declLE.recUvars = 1 := rfl

/-- The recursor constant the repaired declaration asks the map to carry: **one** universe
parameter, and `Sort (.param 0)` where the unrepaired one had `Prop`. -/
theorem declLE_recConsts : declLE.recConsts = [(`R10.Wit.U.rec, ⟨1,
    .forallE (.forallE (.const `R10.Wit.U []) (.sort (.param 0)))
      (.forallE (.app (.bvar 0) (.const `R10.Wit.U.unit []))
        (.forallE (.const `R10.Wit.U []) (.app (.bvar 2) (.bvar 0))))⟩)] := rfl

/-- The two earlier stages are literally unchanged. -/
theorem declLE_typeConsts : declLE.typeConsts = R10.Wit.decl.typeConsts := rfl
theorem declLE_ctorConsts : declLE.ctorConsts = R10.Wit.decl.ctorConsts := rfl
theorem declLE_types : declLE.types = R10.Wit.decl.types := rfl

/-! ### 3.1 The syntactic half survives verbatim

`TrIndDecl` mentions `D.uvars`, `D.np`, `D.types`, `VIndType.type` and `VIndCtor.type D j`; none
of them reads `isLE` (`VIndCtor.type` is `mkPi (params ++ fields) (canonResult D j)` and
`canonResult` goes through `ownLvls`, not `selfLvls`).  So this is
`R10.Wit.trIndDecl_wit` transported along `rfl`. -/
theorem trIndDecl_declLE : TrIndDecl VEnv.empty [] 0 [R10.Wit.uIndType] false declLE where
  safe := R10.Wit.trIndDecl_wit.safe
  uvars := R10.Wit.trIndDecl_wit.uvars
  np := R10.Wit.trIndDecl_wit.np
  length := R10.Wit.trIndDecl_wit.length
  trType := R10.Wit.trIndDecl_wit.trType
  trCtorsLen := R10.Wit.trIndDecl_wit.trCtorsLen
  trCtors := R10.Wit.trIndDecl_wit.trCtors

/-! ### 3.2 The declaration is well-formed, and `isLE` is now a *real* obligation

`R10.Wit.decl_WF` discharges the `isLE` field by `nofun` — the vacuity row 113b records.  Here
it must be met, and it is met by `LECond`'s **first** disjunct: `U : Type`, so `D.lvl` is
`.succ .zero`, which is `IsNeverZero`.  That is the same route the checker takes
(`stats.isNotZero` short-circuits `isLargeEliminator`), so the abstract justification of
`isLE = true` and the executable's are the same fact. -/
theorem declLE_LECond : declLE.LECond :=
  AddInductive.VInductDecl'.LECond.of_isNotZero
    (D := declLE) (Us := []) (resultLevel := .succ .zero) rfl rfl

theorem declLE_WF : declLE.WF VEnv.empty where
  types_ne := by simp [declLE, R10.Wit.decl]
  params := trivial
  types := by
    rintro T hT
    simp [declLE, R10.Wit.decl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ h j T hT C hC
    have hU : env₁.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants h (`R10.Wit.U, ⟨0, .sort (.succ .zero)⟩) (List.Mem.head _)
    match j, hT with
    | 0, hT =>
      simp [declLE, R10.Wit.decl] at hT
      subst hT
      simp at hC
      subst hC
      exact { params_len := rfl
              params_eq := .zero
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := VEnv.HasType.const (U := 0) hU nofun rfl }
  isLE := fun _ => declLE_LECond

/-! ### 3.3 The three `ConstantInfo`s the executable stores

`R10.Wit.uInd` and `R10.Wit.uCtor` are already exactly what `AddInductive.run` stores; the
recursor is not, and `uRecReal` is.  §4's guard is what makes that a checked claim rather than
a transcription.

`rules`, `k`, `numMotives` and `numMinors` are recorded for the guard's benefit only:
`AddInductStages`' third fold is `fun ci => ∃ v, ci = .recInfo v`, so it constrains **none** of
them.  That is `docs/vacuity-ledger.md` row 113c, and this file does not repair it. -/

/-- The `Expr` the executable stores as `U.rec`'s type: `{motive : U → Sort u} → motive U.unit →
(t : U) → motive t`. -/
def uRecTypeE : Expr :=
  .forallE `motive (.forallE `t (.const `R10.Wit.U []) (.sort (.param `u)) .default)
    (.forallE `unit (.app (.bvar 0) (.const `R10.Wit.U.unit []))
      (.forallE `t (.const `R10.Wit.U []) (.app (.bvar 2) (.bvar 0)) .default) .default)
    .implicit

/-- The recursor the executable stores, field for field. -/
def uRecReal : RecursorVal where
  name := `R10.Wit.U.rec
  levelParams := [`u]
  type := uRecTypeE
  all := [`R10.Wit.U]
  numParams := 0
  numIndices := 0
  numMotives := 1
  numMinors := 1
  rules := [{ ctor := `R10.Wit.U.unit, nfields := 0,
              rhs := .lam `motive (.forallE `t (.const `R10.Wit.U []) (.sort (.param `u)) .default)
                (.lam `unit (.app (.bvar 0) (.const `R10.Wit.U.unit [])) (.bvar 0) .default)
                .default }]
  k := false
  isUnsafe := false

/-- It is *not* `R10.Wit.uRec`, and the difference is exactly row 113a's. -/
theorem uRecReal_levelParams : uRecReal.levelParams = [`u] := rfl
theorem uRec_levelParams : R10.Wit.uRec.levelParams = [] := rfl

/-! ### 3.4 The recursor's type translates, at `uvars = 1` -/

section
variable {env : VEnv}
  (hU : env.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩)
  (hu : env.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩)

/-- The motive's type, `U → Sort u`, in the model. -/
abbrev motiveVLE : VExpr := .forallE (.const `R10.Wit.U []) (.sort (.param 0))

include hU in
theorem hasTy_U1 (Γ) : env.HasType 1 Γ (.const `R10.Wit.U []) (.sort (.succ .zero)) :=
  VEnv.HasType.const (Γ := Γ) (U := 1) hU nofun rfl

include hu in
theorem hasTy_unit1 (Γ) : env.HasType 1 Γ (.const `R10.Wit.U.unit []) (.const `R10.Wit.U []) :=
  VEnv.HasType.const (Γ := Γ) (U := 1) hu nofun rfl

include hU hu in
theorem tr_uRecType : TrExprS env [`u] [] uRecTypeE (declLE.recType 0) := by
  have hp0 : (VLevel.param 0).WF 1 := by decide
  have hlvl : VLevel.ofLevel [`u] (.param `u) = some (.param 0) := by simp [VLevel.ofLevel]
  have hb0 : ∀ Γ, env.HasType 1 (motiveVLE :: Γ) (.bvar 0) motiveVLE := fun _ => .bvar .zero
  have hb2 : ∀ A B Γ, env.HasType 1 (A :: B :: motiveVLE :: Γ) (.bvar 2) motiveVLE :=
    fun _ _ _ => .bvar (.succ (.succ .zero))
  have hbT : ∀ Γ, env.HasType 1 (VExpr.const `R10.Wit.U [] :: Γ) (.bvar 0)
      (.const `R10.Wit.U []) := fun _ => .bvar .zero
  have hM : env.IsType 1 [] motiveVLE :=
    ⟨_, .forallEDF (hasTy_U1 hU _) (.sortDF hp0 hp0 (.refl _))⟩
  have hH : ∀ Γ, env.HasType 1 (motiveVLE :: Γ)
      (.app (.bvar 0) (.const `R10.Wit.U.unit [])) (.sort (.param 0)) := fun Γ =>
    .appDF (hb0 Γ) (hasTy_unit1 hu _)
  have hB : ∀ Γ, env.HasType 1 (VExpr.const `R10.Wit.U [] ::
      (VExpr.app (.bvar 0) (.const `R10.Wit.U.unit [])) :: motiveVLE :: Γ)
      (.app (.bvar 2) (.bvar 0)) (.sort (.param 0)) := fun Γ =>
    .appDF (hb2 _ _ Γ) (hbT _)
  refine .forallE hM ?_ ?_ ?_
  · exact ⟨_, .forallEDF (hH _) (.forallEDF (hasTy_U1 hU _) (hB _))⟩
  · exact .forallE ⟨_, hasTy_U1 hU _⟩ ⟨_, .sortDF hp0 hp0 (.refl _)⟩
      (.const hU rfl rfl) (.sort hlvl)
  · refine .forallE ⟨_, hH _⟩ ?_ ?_ ?_
    · exact ⟨_, .forallEDF (hasTy_U1 hU _) (hB _)⟩
    · exact .app (hb0 _) (hasTy_unit1 hu _) (.bvar rfl) (.const hu rfl rfl)
    · refine .forallE ⟨_, hasTy_U1 hU _⟩ ⟨_, hB _⟩ (.const hU rfl rfl) ?_
      exact .app (hb2 _ _ _) (hbT _) (.bvar rfl) (.bvar rfl)

end


/-! ### 3.5 `AddInductStages` at the executable's map

The map below is `m` with **exactly** the three `ConstantInfo`s the executable stores inserted,
in the order it stores them.  §4's guard is what ties `uInd`/`uCtor`/`uRecReal` to the run;
this theorem is what says the relation holds of that map.

`IndShapeOf`/`CtorShapeOf` are reused from `Verify/Environment/Basic.lean` unchanged: they
mention `D` only through `D.np`, `D.types` and `D.ctorsAll`, none of which `isLE` touches, so
`R10.Wit.indShapeOf_uInd` and `R10.Wit.ctorShapeOf_uCtor` apply to `declLE` on the nose. -/

/-- The constant map the executable produces, spelled as the three inserts. -/
def realMap (m : ConstMap) : ConstMap :=
  ((m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)).insert `R10.Wit.U.unit
    (.ctorInfo R10.Wit.uCtor)).insert `R10.Wit.U.rec (.recInfo uRecReal)

/-- **Row 113a's repair, verified: `AddInductStages` has a firing instance.**

The output map is `realMap m`, whose three entries are the three `ConstantInfo`s
`Environment.addInductive` stores (§4's guard, check R1).  Contrast
`R10.Wit.addInductStages_wit`, whose output map stores `R10.Wit.uRec` — a recursor with
`levelParams = []`, which §2 shows is forced at `R10.Wit.decl` and which the executable never
builds. -/
theorem addInductStages_firing {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ env', AddInductStages m VEnv.empty declLE (realMap m) env' ∧
      VEnv.empty.addInduct' declLE = some env' ∧
      (realMap m).find? `R10.Wit.U.rec = some (.recInfo uRecReal) := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := `R10.Wit.U)
    (ci := ⟨0, .sort (.succ .zero)⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hU1 : e1.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := `R10.Wit.U.unit)
    (ci := ⟨0, .const `R10.Wit.U []⟩) (by rw [c1]; simp [VEnv.empty])
  have c2 := VEnv.addConst_constants_eq he2
  have hU2 : e2.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by rw [c2]; simp [hU1]
  have hu2 : e2.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩ := by rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := `R10.Wit.U.rec)
    (ci := ⟨1, declLE.recType 0⟩) (by rw [c2, c1]; simp [VEnv.empty])
  have w1 := hwf.insert `R10.Wit.U (.inductInfo R10.Wit.uInd) (hfr _)
  have f2 : (m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)).find? `R10.Wit.U.unit = none := by
    rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert `R10.Wit.U.unit (.ctorInfo R10.Wit.uCtor) f2
  have s1 : AddIndConsts (IndShapeOf declLE id) declLE.typeConsts
      m VEnv.empty (m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)) e1 :=
    .cons (ci := .inductInfo R10.Wit.uInd) rfl R10.Wit.indShapeOf_uInd
      ⟨by decide, rfl, .sort rfl⟩ (hfr _) he1 .nil
  have s2 : AddIndConsts (CtorShapeOf declLE id fun j => (declLE.types.getD j default).name)
      declLE.ctorConsts
      (m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)) e1
      ((m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)).insert `R10.Wit.U.unit
        (.ctorInfo R10.Wit.uCtor)) e2 :=
    .cons (ci := .ctorInfo R10.Wit.uCtor) rfl R10.Wit.ctorShapeOf_uCtor
      ⟨by decide, rfl, .const hU1 rfl rfl⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) declLE.recConsts
      (((m.insert `R10.Wit.U (.inductInfo R10.Wit.uInd)).insert `R10.Wit.U.unit
        (.ctorInfo R10.Wit.uCtor))) e2 (realMap m) e3 :=
    .cons (ci := .recInfo uRecReal) rfl ⟨_, rfl⟩ ⟨by decide, rfl, tr_uRecType hU2 hu2⟩
      (by rw [w1.find?_insert, hwf.find?_insert]; simp [hfr, Lean.mkRecName]) he3 .nil
  have H : AddInductStages m VEnv.empty declLE (realMap m) (e3.addIndRules declLE) :=
    ⟨_, _, _, _, e3, s1, s2, s3, rfl⟩
  refine ⟨_, H, H.to_addInduct, ?_⟩
  show (SMap.insert _ `R10.Wit.U.rec (ConstantInfo.recInfo uRecReal)).find? _ = _
  rw [w2.find?_insert]; simp

/-- **`InductStepSafe` at the executable's map.**  All three conjuncts of `AddDeclWF.lean` §3's
obligation at once, with the constant map on the right the one the run produces.

This is what `R10.Wit.inductStepSafe_wit` was *read* as saying and did not: its `m'` stores a
recursor the checker never builds. -/
theorem inductStepSafe_firing {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ venv', InductStepSafe m (realMap m) VEnv.empty venv' [] 0 [R10.Wit.uIndType] := by
  obtain ⟨venv', H, -, -⟩ := addInductStages_firing hwf hfr
  exact ⟨venv', declLE, trIndDecl_declLE, declLE_WF, H⟩

end R113a

/-! ## 4. The executed half

§3 is a theorem about three `ConstantInfo` literals; that they are *the* three the executable
stores is a fact about the executable.  `Environment.addInductive` does not reduce in the kernel
(`Expr.abstract`/`Expr.mkData` are `@[extern]`/`opaque` — `Verify/Axioms.lean` carries
`mkData_eq` for exactly that reason, and `Verify/Guard.lean` forbids `native_decide`), so this is
a **build-time check, not a proof**, in the same position as `AddDeclWF.lean` §4's check A.  It
`throwError`s on every failure path: a check that only `logInfo`s is not a guard.

**Check R1.**  From the empty environment, `Environment.addInductive` on `[R10.Wit.uIndType]`
succeeds, adds exactly the three names `U`, `U.unit`, `U.rec`, and stores at them exactly
`R10.Wit.uInd`, `R10.Wit.uCtor` and `R113a.uRecReal`.  Two consequences, and both directions of
row 113a rest on them:

* `§3`'s `addInductStages_firing` is about the map the run produces — so `AddInductStages` has a
  firing instance;
* the stored `U.rec` carries `levelParams = [u] ≠ []`, so §2's
  `r113a_not_addInductStages_of_rec_lp` applies to that same map and `R10.Wit.decl` is refuted
  at it.  If `getElimLevel` ever stops prepending a fresh level, this check fails rather than
  going quietly stale.
-/

open Elab Command in
#eval show CommandElabM Unit from do
  let env := Kernel.Environment.empty `main
  unless env.constants.map₁.toList.isEmpty && env.constants.map₂.toList.isEmpty do
    throwError "check R1: the base environment is not empty, so the name list below is not the block's"
  let .ok env' := Lean4Lean.Environment.addInductive env [] 0 [R10.Wit.uIndType] false false {}
    | throwError "check R1: addInductive REJECTED the U block"
  let names := (env'.constants.map₁.toList.map (·.1) ++ env'.constants.map₂.toList.map (·.1))
  unless names.length == 3 && names.contains `R10.Wit.U && names.contains `R10.Wit.U.unit &&
      names.contains `R10.Wit.U.rec do
    throwError "check R1: the run added {names}, not exactly [U, U.unit, U.rec] -- R113a.realMap is wrong"
  -- The run's map and `realMap` enumerate identically, *including which SMap stage* each
  -- constant landed in.  Measured limitation, stated so it is not over-read: `Std.HashMap`
  -- iterates by bucket, not by insertion, so this clause would **not** notice a permutation of
  -- the three stages (negative-tested: the reversed inserts enumerate the same list).  What it
  -- does notice is a fourth constant, a missing one, a renamed one, or a stage migration.
  let refNames := (R113a.realMap env.constants).map₁.toList.map (·.1) ++
    (R113a.realMap env.constants).map₂.toList.map (·.1)
  unless names == refNames do
    throwError "check R1: the run's map enumerates {names} but R113a.realMap enumerates \
      {refNames} -- the two are not the same map"
  let some (.inductInfo iv) := env'.find? `R10.Wit.U
    | throwError "check R1: U is not an inductInfo"
  unless iv.name == R10.Wit.uInd.name && iv.levelParams == R10.Wit.uInd.levelParams &&
      iv.type == R10.Wit.uInd.type && iv.numParams == R10.Wit.uInd.numParams &&
      iv.numIndices == R10.Wit.uInd.numIndices && iv.all == R10.Wit.uInd.all &&
      iv.ctors == R10.Wit.uInd.ctors && iv.numNested == R10.Wit.uInd.numNested &&
      iv.isRec == R10.Wit.uInd.isRec && iv.isUnsafe == R10.Wit.uInd.isUnsafe &&
      iv.isReflexive == R10.Wit.uInd.isReflexive do
    throwError "check R1: the stored U differs from R10.Wit.uInd"
  let some (.ctorInfo cv) := env'.find? `R10.Wit.U.unit
    | throwError "check R1: U.unit is not a ctorInfo"
  unless cv.name == R10.Wit.uCtor.name && cv.levelParams == R10.Wit.uCtor.levelParams &&
      cv.type == R10.Wit.uCtor.type && cv.induct == R10.Wit.uCtor.induct &&
      cv.cidx == R10.Wit.uCtor.cidx && cv.numParams == R10.Wit.uCtor.numParams &&
      cv.numFields == R10.Wit.uCtor.numFields && cv.isUnsafe == R10.Wit.uCtor.isUnsafe do
    throwError "check R1: the stored U.unit differs from R10.Wit.uCtor"
  let some (.recInfo rv) := env'.find? `R10.Wit.U.rec
    | throwError "check R1: U.rec is not a recInfo"
  unless rv.name == R113a.uRecReal.name && rv.levelParams == R113a.uRecReal.levelParams &&
      rv.type == R113a.uRecReal.type && rv.all == R113a.uRecReal.all &&
      rv.numParams == R113a.uRecReal.numParams && rv.numIndices == R113a.uRecReal.numIndices &&
      rv.numMotives == R113a.uRecReal.numMotives && rv.numMinors == R113a.uRecReal.numMinors &&
      rv.rules == R113a.uRecReal.rules && rv.k == R113a.uRecReal.k &&
      rv.isUnsafe == R113a.uRecReal.isUnsafe do
    throwError "check R1: the stored U.rec differs from R113a.uRecReal -- \
      levelParams={rv.levelParams} type={rv.type} rules={rv.rules.length}"
  -- the negative half, stated as its own failure: row 113a's `1 = 0`
  if rv.levelParams == ([] : List Name) then
    throwError "check R1: U.rec now has NO level parameters -- row 113a's refutation of \
      R10.Wit.decl has gone stale and r113a_not_addInductStages_of_rec_lp no longer applies"
  unless rv.levelParams.length == R113a.declLE.recUvars do
    throwError "check R1: stored levelParams.length={rv.levelParams.length} but \
      declLE.recUvars={R113a.declLE.recUvars} -- the isLE repair is the wrong one"
  logInfo m!"check R1: addInductive stores exactly uInd/uCtor/uRecReal; U.rec carries \
    levelParams={rv.levelParams} (length {rv.levelParams.length} = declLE.recUvars), so \
    AddInductStages FIRES at declLE and is REFUTED at R10.Wit.decl ✓"

end Lean4Lean
