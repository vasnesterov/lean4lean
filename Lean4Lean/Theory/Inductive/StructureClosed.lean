import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Inductive.Structure

/-!
# `VInductDecl'.ProjClosed` is a theorem, not a hypothesis

`TrProj.weak'`/`.instN`/`.weak'_inv` need the structure's stored telescopes closed at their
declared arities (`VInductDecl'.ProjClosed`).  This file derives that from
`VEnv.IsStructure` together with `VEnv.Ordered env`, which those lemmas already have — so
nothing is assumed.

## Why this is a separate file

The derivation needs `Theory/Inductive/Lemmas.lean` (`addInduct'_le`, `addInduct'_constants`,
`Ordered.closedC`), which is large and belongs to the inductive-keystone workstream.
`Structure.lean` deliberately imports only `Decl.lean` so that the definition of `TrProj`
and its `instL` theory do not depend on a file under active development; only this bridge
does.

## The two halves

*Field types* come from the **constructor constant**: `addInduct'_constants` puts
`⟨D.uvars, C.type D j⟩` into the environment, `Ordered.closedC` says a constant's type is
closed, and `closedN_mkPi` peels the binder telescope.  This needs `Ordered` only for the
*final* environment.

*Index telescopes* have no such constant to read off — `T.type` is only **definitionally**
`mkPi (params ++ indices) (sort lvl)` (F1), so `ClosedN T.type 0` says nothing about the
decomposition.  They come instead from `VIndType.WF.indices`, a judgement in the *earlier*
environment `env₀`, where `Ordered` is not available.  The step that makes this work is
that `VEnv.OnTypes` is **antitone** (`OnTypes.mono`): closedness of every constant's type
in `env` restricts to `env₀ ≤ env`.  Hence the `₀`-suffixed variants below, which are
`Inductive/Lemmas.lean`'s `OnCtx.ctxClosed` / `ClosedTele.of_onCtx` with `Ordered env`
weakened to the `OnTypes` fact they actually consume.
-/

namespace Lean4Lean

open VExpr VEnv

variable {env : VEnv} {U : Nat}

/-- `OnCtx.ctxClosed` with `Ordered env` weakened to the `OnTypes` fact it consumes. -/
theorem OnCtx.ctxClosed₀ (hc : OnTypes env fun _ e A => e.ClosedN ∧ A.ClosedN) :
    ∀ {Γ}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ =>
    ⟨h1.ctxClosed₀ hc, (h2.choose_spec.closedN' hc (h1.ctxClosed₀ hc)).1⟩

/-- `VExpr.ClosedTele.of_onCtx` with the same weakening. -/
theorem VExpr.ClosedTele.of_onCtx₀ (hc : OnTypes env fun _ e A => e.ClosedN ∧ A.ClosedN) :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VExpr.ClosedTele As Γ.length
  | [], _, _ => trivial
  | A :: As, Γ, h => by
    rw [VExpr.tele_ctx_cons] at h
    have hΓ : OnCtx (A :: Γ) (env.IsType U) := OnCtx.append_right h
    refine ⟨(hΓ.2.choose_spec.closedN' hc (hΓ.1.ctxClosed₀ hc)).1, ?_⟩
    simpa using VExpr.ClosedTele.of_onCtx₀ (As := As) (Γ := A :: Γ) hc h

/-- `addInduct'` runs `addIndTypes` first, so its success is available. -/
theorem VInductDecl'.addIndTypes_of_addInduct' {D : VInductDecl'} {env env' : VEnv}
    (h : env.addInduct' D = some env') : ∃ env₁, env.addIndTypes D = some env₁ := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨e₁, h1, _⟩ := h
  simp only [VInductDecl'.allConsts, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨_, ⟨e₃, h3, _⟩, _⟩ := h1
  exact ⟨e₃, h3⟩

variable {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

/-- **`ProjClosed` is derivable**: no field on `IsStructure`, no added hypothesis.
`Ordered env` is what `TrProj.weak'`/`.instN`/`.weak'_inv` already carry. -/
theorem VEnv.IsStructure.projClosed (henv : env.Ordered) (H : env.IsStructure S D T C) :
    D.ProjClosed T C := by
  obtain ⟨env₀, env₁, hWF, hadd, hle⟩ := H.decl
  have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
  have hc₀ : OnTypes env₀ (fun _ e A => e.ClosedN ∧ A.ClosedN) :=
    henv.closed.mono hle₀ id
  have hT : T ∈ D.types := by rw [H.types]; exact List.mem_singleton_self _
  refine ⟨?_, ?_, ?_⟩
  · -- parameters: `VInductDecl'.WF.params`, again in `env₀`
    have := VExpr.ClosedTele.of_onCtx₀ (Γ := []) hc₀ (by simpa using hWF.params)
    simpa using this
  · -- indices: from `VIndType.WF.indices`, a judgement in `env₀`
    have := VExpr.ClosedTele.of_onCtx₀ hc₀ (hWF.types T hT).indices
    simpa [VInductDecl'.np] using this
  · -- field types: from the constructor *constant*, which lives in `env`
    obtain ⟨env₁', hadd₁⟩ := VInductDecl'.addIndTypes_of_addInduct' hadd
    have hTj : D.types[0]? = some T := by rw [H.types]; rfl
    have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
    have hCwf := hWF.ctors env₁' hadd₁ 0 T hTj C hC
    have hmem : (C.name, (⟨D.uvars, C.type D 0⟩ : VConstant)) ∈ D.allConsts := by
      simp [VInductDecl'.allConsts, VInductDecl'.ctorConsts, VInductDecl'.ctorsAll,
        H.types, H.ctors]
    have hconst : env.constants C.name = some ⟨D.uvars, C.type D 0⟩ :=
      hle.constants (VEnv.addInduct'_constants hadd _ hmem)
    have hcl : VExpr.ClosedN (C.type D 0) 0 := henv.closedC hconst
    rw [VIndCtor.type] at hcl
    have := (VExpr.closedTele_append.1 (VExpr.closedN_mkPi.1 hcl).1).2
    simpa [hCwf.params_len, VInductDecl'.np] using this

/-! ## `HasArgs` transport

`Theory/Inductive/Lemmas.lean` has `HasArgs.instL`, `.weakN` and `.mono`; `TrProj`'s
recorded spine premises additionally need the `Ctx.Lift'` and `Ctx.InstN` versions. -/

theorem VEnv.HasArgs.weak' {env : VEnv} {U} {l : Lift} {Γ Γ' : List VExpr}
    (henv : VEnv.Ordered env) (W : Ctx.Lift' l Γ Γ') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U Γ' (VExpr.liftTele' l As) (as.map (·.lift' l))
  | _, _, .nil => .nil
  | A :: As, a :: as, .cons ha h => by
    refine .cons (ha.weak' henv W) ?_
    have ih := VEnv.HasArgs.weak' henv W h
    have hcomm : VExpr.liftTele' l (VExpr.instTele a As)
        = VExpr.instTele (a.lift' l) (VExpr.liftTele' l.cons As) :=
      VExpr.liftTele'_instTele (As := As) (a := a) (ρ := l) (j := 0)
    rwa [hcomm] at ih

theorem VEnv.HasArgs.instN {env : VEnv} {U k} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr}
    (henv : VEnv.Ordered env) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (t₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As as}, env.HasArgs U Γ₁ As as →
      env.HasArgs U Γ (VExpr.instTele e₀ As k) (as.map (·.inst e₀ k))
  | _, _, .nil => .nil
  | A :: As, a :: as, .cons ha h => by
    refine .cons (ha.instN henv W t₀) ?_
    have ih := VEnv.HasArgs.instN henv W t₀ h
    have hcomm : VExpr.instTele e₀ (VExpr.instTele a As) k
        = VExpr.instTele (a.inst e₀ k) (VExpr.instTele e₀ As (k+1)) :=
      VExpr.instTele_instTele (As := As) (a := a) (b := e₀) (m := k) (j := 0)
    rwa [hcomm] at ih

/-! ## `IotaCtx` from `IsStructure`

`VInductDecl'.WF.recCtx` takes `(hle : env₂ ≤ env₃) (henv₃ : env₃.Ordered)`, so it produces
`RecCtx` at *any* environment above the staged one — no `Ordered env₀` is needed, and the
recursor constants transport along `≤` from `addInduct'_constants`. -/

theorem VInductDecl'.addInduct'_stages {D : VInductDecl'} {env env' : VEnv}
    (h : env.addInduct' D = some env') :
    ∃ env₁ env₂ env₃, env.addIndTypes D = some env₁ ∧ env₁.addIndCtors D = some env₂ ∧
      env₂.addIndRecs D = some env₃ ∧ env₃.addIndRules D = env' := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨eF, h1, hF⟩ := h
  simp only [VInductDecl'.allConsts, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨e₂, ⟨e₁, ha, hb⟩, hc⟩ := h1
  exact ⟨e₁, e₂, eF, ha, hb, hc, hF⟩

theorem VEnv.IsStructure.iotaCtx (henv : env.Ordered) (H : env.IsStructure S D T C) :
    D.IotaCtx env := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, hF⟩ := VInductDecl'.addInduct'_stages hadd
  have hle₂ : env₂ ≤ env :=
    ((VEnv.addIndRecs_le h3).trans (hF ▸ VEnv.addIndRules_le)).trans hle
  refine ⟨hWF.recCtx h1 h2 hle₂ henv, fun j T' hT' => ?_⟩
  refine hle.constants (VEnv.addInduct'_constants hadd
    (Lean.mkRecName T'.name, ⟨D.recUvars, D.recType j⟩) ?_)
  simp only [VInductDecl'.allConsts, VInductDecl'.recConsts, List.mem_append, List.mem_map]
  exact .inr ⟨(T', j), List.mk_mem_zipIdx_iff_getElem?.2 hT', rfl⟩

/-! ## `IsDefEq` at a spine

`Theory/Inductive/Lemmas.lean:604` has `HasType.mkApp'`; there is no `IsDefEq` counterpart.
Same small gap as `Telescope.lean` having every `liftN` lemma and no `lift'` one.  This is
what applies an ι-rule, which `IsDefEq.extra` delivers λ-abstracted, to a concrete spine. -/

theorem VEnv.IsDefEq.mkApp' {env : VEnv} {U : Nat} :
    ∀ {As as Γ f g B}, env.HasArgs U Γ As as → env.IsDefEq U Γ f g (VExpr.mkPi As B) →
      env.IsDefEq U Γ (f.mkApp as) (g.mkApp as) (VExpr.instAll B as)
  | _, _, _, _, _, _, .nil, hf => hf
  | A :: As, a :: as, Γ, f, g, B, .cons ha has, hf => by
    have h1 := hf.appDF ha
    rw [VExpr.inst_mkPi_zero] at h1
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.mkApp_cons, VExpr.mkApp_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact VEnv.IsDefEq.mkApp' has h1

/-! ## The motive's declared type

`recApp_hasType''`'s `hspine` asks for the motive at `instAll ((D.motiveType 0).instL ls) ps`.
This computes that to the type `HasType.mkLams` produces for `VIndType.projMotive`. -/

theorem motiveType_instL_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps : List VExpr} {i : Nat}
    (hT : D.types.getD 0 default = T)
    (hus : us.length = D.uvars) (hps : ps.length = D.np) :
    VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps
      = VExpr.mkPi (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
          (.forallE ((VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ VExpr.bvars 0 T.indices.length))
            (.sort (D.elimLvl.inst (D.projLvls C us i)))) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.motiveType, hT, VExpr.liftTele_zero, VInductDecl'.atRecTele,
    VExpr.instL_mkPi, VInductDecl'.tyApp', VExpr.instL_mkApp, VExpr.instL,
    VExpr.map_instL_bvars, List.map_append, VExpr.instAll_mkPi, VExpr.instAll_forallE,
    VExpr.instAll_sort, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_map, Function.comp_def, VExpr.instL_instL, hself,
    List.length_map, Nat.zero_add, Nat.add_zero]
  rw [VExpr.map_instAll_bvars_top (Nat.le_refl _) (by simp [hps]),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_of_length_le (by simp [hps])]

end Lean4Lean
