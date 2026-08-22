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
  constructor
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

end Lean4Lean
