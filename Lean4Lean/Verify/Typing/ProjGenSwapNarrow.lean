import Lean4Lean.Verify.Typing.ProjGenSwap

/-!
# The collapse test for the generalised motive chain

`ProjGenMotive.lean` and `ProjGenSwap.lean` claim to generalise `projMotiveTerm`,
`ProjHasType` and `projMotiveTerm_hasType_swapped` along the **block index**.  A
generalisation that had drifted — to a different motive slot, a different `earlier` spine, or
a telescope one binder off — would still compile, and no non-vacuity firing at a wide block
would notice.  What notices is meeting the narrow theorem head-on.

`projMotiveTermG_hasType_swapped_narrow` below re-derives `projMotiveTerm_hasType_swapped`
(`ProjSkip.lean:1084`) **verbatim** — same hypotheses, same conclusion — from
`projMotiveTermG_hasType_swapped` at `j = 0`, `ms = []`.  The only steps are the three
compatibility lemmas (`projMotiveTermG_eq_projMotiveTerm`, `projHasTypeG_eq`,
`List.append_nil`) and `motiveCtx_wf` for the context premise.

This module is deliberately separate because it consumes the narrow chain, and therefore its
`sorryAx` route: `ProjSkip.lean` runs on `VEnv.HasType.swapCtx` → `weakN_iff`.  (So does
`ProjGenSwap.lean` itself; `ProjGenMotive.lean` does not.)
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
  {C : VIndCtor} {us : List VLevel}

/-- **The collapse test.**  This is `projMotiveTerm_hasType_swapped`'s statement, proved from
the generalised lemma alone. -/
theorem projMotiveTermG_hasType_swapped_narrow (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U Γ (projMotiveTerm D T C us ps i)
      (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps) := by
  have hord := henv.ordered
  have hTj : D.types[0]? = some T := by rw [H.types]; rfl
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  have hIH' : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us 0 k := by
    intro k hk hu
    rw [projHasTypeG_eq env U S D T C us k H.types H.ctors H.noRec h3]
    exact hIH k hk hu
  have hΔ := motiveCtx_wf hord hI H h3 h7 hΓ hps hpsA
  have h := projMotiveTermG_hasType_swapped (S := S) (ms := []) henv hI
    (H.projClosedG hord) hTj hC H.name h3 h7 hi hlvi hIH' hps rfl hpsA ⟨hΔ.1, hΔ.2⟩
  rwa [List.append_nil,
    projMotiveTermG_eq_projMotiveTerm D T C us ps i H.types H.ctors H.noRec h3] at h

/-- The same collapse for the body half. -/
theorem projMotiveBodyG_hasType_guarded_narrow (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) i))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hord := henv.ordered
  have hTj : D.types[0]? = some T := by rw [H.types]; rfl
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  have hIH' : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us 0 k := by
    intro k hk hu
    rw [projHasTypeG_eq env U S D T C us k H.types H.ctors H.noRec h3]
    exact hIH k hk hu
  have hΔ := motiveCtx_wf hord hI H h3 h7 hΓ hps hpsA
  have h := projMotiveBodyG_hasType_guarded (S := S) henv hI (H.projClosedG hord) hTj hC
    H.name h7 hi hlvi hIH' hps hpsA ⟨hΔ.1, hΔ.2⟩
  rwa [D.projArgsG_eq_projArgs T C us H.types H.ctors H.noRec h3] at h

end Lean4Lean
