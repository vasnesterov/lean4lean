import Lean4Lean.Theory.Typing.WeakNProjGate
import Lean4Lean.Verify.Typing.ProjGenSwap

/-!
# The restructure, machine-checked at the projection corner's crux

**This file imports `Lean4Lean.Verify.*` from `Lean4Lean.Theory.*`, which is backwards.**  It is
a *verification harness*, not architecture: it exists to check that the substitutions
`docs/handoff-weakn.md` §7.4 proposes for `Verify/Typing/ProjSkip.lean` actually elaborate at the
real call site, rather than only in prose.  When the edit is applied, this file should be deleted
(or moved into `Verify/Typing/`); nothing in `WeakNProjGate.lean` depends on it.

`docs/handoff-weakn.md` §7.1 measures that the projection corner's entire dependence on
`VEnv.IsDefEqU.weakN_iff` is **four call sites, all in `Verify/Typing/ProjSkip.lean`**:
`OnCtx.of_appendTele`, `VEnv.HasType.swapSkipped`, and the `OnCtx.weakN_inv` appeals inside
`OnCtx.swapCtx` and `VEnv.HasType.swapCtx`.  This file rebuilds that stack from
`VEnv.TypingStrengthening` and re-derives the corner's crux, `ftype_hasType_swappedG`
(`Verify/Typing/ProjGenSwap.lean:52`), verbatim except for the added hypothesis.

Measured (script in the handoff): `weakN_iff` is **absent** from the cone of everything here;
the hole set is `{IsDefEqU.forallE_inv_stratified}`, which the original already carries.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat}

/-- `VEnv.HasType.swapTele` (`ProjSkip.lean:245`) from the typing half, at a sort type. -/
theorem VEnv.HasType.swapTeleT (henv : VEnv.WF env) (HT : VEnv.TypingStrengthening env U)
    {Γ As : List VExpr} {A A' b : VExpr} {u : VLevel}
    (hΓ : OnCtx ((liftTele 1 As 0).reverse ++ A :: Γ) (env.IsType U))
    (H : env.HasType U ((liftTele 1 As 0).reverse ++ A :: Γ) (b.liftN 1 As.length) (.sort u)) :
    env.HasType U ((liftTele 1 As 0).reverse ++ A' :: Γ) (b.liftN 1 As.length) (.sort u) :=
  HT.hasType_sort_swapTele henv hΓ H

/-- `OnCtx.swapCtx` (`ProjSkip.lean:360`) from the typing half.  Cone: **no hole at all** --
the original's `OnCtx.weakN_inv` appeals become `TypingStrengthening.onCtx_inv'` and its
`OnCtx.of_appendTele` appeal becomes the hypothesis-free `VEnv.onCtx_of_appendL`. -/
theorem OnCtx.swapCtxT (henv : VEnv.WF env) (HT : VEnv.TypingStrengthening env U)
    {b B : VExpr} : ∀ {Fs Fs' : List VExpr}, VExpr.SwapCtx b B Fs Fs' → ∀ {Γ : List VExpr},
      OnCtx (Fs.reverse ++ Γ) (env.IsType U) → OnCtx (Fs'.reverse ++ Γ) (env.IsType U)
  | _, _, .nil, _, h => h
  | _, _, .keep (F := F) h, Γ, hΓ => by
    rw [VExpr.tele_ctx_cons] at hΓ ⊢
    exact OnCtx.swapCtxT henv HT h hΓ
  | _, _, .swap (F := F) (Fs₀ := Fs₀) hFs hb hB h, Γ, hΓ => by
    subst hFs
    rw [VExpr.tele_ctx_cons] at hΓ
    have hΓ0 : OnCtx Γ (env.IsType U) :=
      (VEnv.onCtx_of_appendL (As := (liftTele 1 Fs₀ 0).reverse) (Γ := F :: Γ) hΓ).1
    have hΓ' : OnCtx ((liftTele 1 Fs₀ 0).reverse ++ VExpr.swapUnit :: Γ) (env.IsType U) := by
      refine VEnv.OnCtx.weakTele henv.ordered Ctx.LiftN.one ⟨hΓ0, VExpr.swapUnit_isType⟩ ?_
      have W : Ctx.LiftN 1 Fs₀.length (Fs₀.reverse ++ Γ)
          ((liftTele 1 Fs₀ 0).reverse ++ F :: Γ) := by
        have := Ctx.LiftN.tele (As := Fs₀) (n := 1) (k := 0) (Γ := Γ) (Γ' := F :: Γ)
          Ctx.LiftN.one
        rwa [Nat.zero_add] at this
      exact HT.onCtx_inv' henv W hΓ
    rw [VExpr.tele_ctx_cons]
    exact OnCtx.swapCtxT henv HT h hΓ'

/-- `VEnv.HasType.swapCtx` (`ProjSkip.lean:332`) from the typing half, at a sort type -- which is
the generality **both** of its callers use it at (`ftype_hasType_swapped`,
`ftype_hasType_swappedG`; measured, handoff §7.1). -/
theorem VEnv.HasType.swapCtxT (henv : VEnv.WF env) (HT : VEnv.TypingStrengthening env U)
    {b : VExpr} {u : VLevel} :
    ∀ {Fs Fs' : List VExpr}, VExpr.SwapCtx b (.sort u) Fs Fs' → ∀ {Γ : List VExpr},
      OnCtx (Fs.reverse ++ Γ) (env.IsType U) →
      env.HasType U (Fs.reverse ++ Γ) b (.sort u) →
      env.HasType U (Fs'.reverse ++ Γ) b (.sort u)
  | _, _, .nil, _, _, H => H
  | _, _, .keep (F := F) h, Γ, hΓ, H => by
    rw [VExpr.tele_ctx_cons] at hΓ H ⊢
    exact VEnv.HasType.swapCtxT henv HT h hΓ H
  | _, _, .swap (F := F) (Fs₀ := Fs₀) (b₀ := b₀) hFs hb hB h, Γ, hΓ, H => by
    subst hFs hb
    rw [VExpr.tele_ctx_cons] at hΓ H
    have hΓ0 : OnCtx Γ (env.IsType U) :=
      (VEnv.onCtx_of_appendL (As := (liftTele 1 Fs₀ 0).reverse) (Γ := F :: Γ) hΓ).1
    have hΓ' : OnCtx ((liftTele 1 Fs₀ 0).reverse ++ VExpr.swapUnit :: Γ) (env.IsType U) := by
      refine VEnv.OnCtx.weakTele henv.ordered Ctx.LiftN.one ⟨hΓ0, VExpr.swapUnit_isType⟩ ?_
      have W : Ctx.LiftN 1 Fs₀.length (Fs₀.reverse ++ Γ)
          ((liftTele 1 Fs₀ 0).reverse ++ F :: Γ) := by
        have := Ctx.LiftN.tele (As := Fs₀) (n := 1) (k := 0) (Γ := Γ) (Γ' := F :: Γ)
          Ctx.LiftN.one
        rwa [Nat.zero_add] at this
      exact HT.onCtx_inv' henv W hΓ
    have H1 := VEnv.HasType.swapTeleT (A' := VExpr.swapUnit) henv HT hΓ H
    rw [VExpr.tele_ctx_cons]
    exact VEnv.HasType.swapCtxT henv HT h hΓ' H1

/-- **The corner's crux, from the typing half.**  `ftype_hasType_swappedG`
(`Verify/Typing/ProjGenSwap.lean:52`) verbatim, with `(HT : VEnv.TypingStrengthening env U)` added
and nothing else changed.  `weakN_iff` is absent from its cone. -/
theorem ftype_hasType_swappedGT {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} (henv : VEnv.WF env) (HT : VEnv.TypingStrengthening env U)
    (hI : D.IotaCtx env) (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T)
    (hC : C ∈ T.ctors) (h7 : ∀ l ∈ us, l.WF U) {i : Nat} (hi : i < C.fields.length)
    {Γ'' : List VExpr}
    (hΓ : OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'') (env.IsType U))
    {Fs' : List VExpr}
    (hsw : VExpr.SwapCtx ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us))
        ((C.fields.take i).map (fun F => F.type.instL us)) Fs') :
    env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Γ'')
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)) :=
  VEnv.HasType.swapCtxT henv HT (hsw.appendKeep (D.params.map (VExpr.instL us))) hΓ
    (ftype_hasTypeG henv.ordered hI H hTj hC h7 hi Γ'')

/-- …and the `OnCtx` companion `ProjGenSwap.lean:139` needs, hole-free. -/
theorem onCtxFields_swappedGT {D : VInductDecl'} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (HT : VEnv.TypingStrengthening env U) {b B : VExpr}
    {i : Nat} {Γ'' Fs' : List VExpr}
    (hΓ : OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'') (env.IsType U))
    (hsw : VExpr.SwapCtx b B ((C.fields.take i).map (fun F => F.type.instL us)) Fs') :
    OnCtx ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Γ'') (env.IsType U) :=
  OnCtx.swapCtxT henv HT (hsw.appendKeep (D.params.map (VExpr.instL us))) hΓ

end Lean4Lean
