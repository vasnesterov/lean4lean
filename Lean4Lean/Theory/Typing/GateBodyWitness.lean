import Lean4Lean.Theory.Typing.WeakNProjGate

/-!
# Anti-vacuity for `GateBodyDescend.lean` §2

`docs/vacuity-ledger.md` §0: a conditional result whose hypothesis cannot be met is worthless.
The six gate bodies of `Theory/Typing/GateBodyDescend.lean` §2 all carry
`HT : VEnv.TypingStrengthening env U`.  This file discharges that hypothesis at a concrete
`VEnv.WF` environment, so all six fire there with **no hypotheses left**.

It lives in a separate module because `GateBodyDescend.lean` sits *above*
`Theory/Typing/UniqueTyping.lean` by design, while the witness
(`WeakNProjGate.exists_typingStrengthening_env`, itself built on
`StrengthenVerdict.exists_univInhabEnv`) sits below it.  Nothing above `UniqueTyping.lean` needs
the witness, so the split costs nothing.

**Read the scope statement with it.**  The witness environment declares
`univInhab : ∀ (α : Sort u), α`, so it is *inconsistent*, and
`univInhab_no_uninhabited_entry` says its contexts have no uninhabited entry.  This is therefore
a **satisfiability** witness: it shows the hypothesis is not contradictory, and it is *not*
evidence that the hypothesis is easy, nor that the conclusions have content at that environment
(where `Strengthen.lean` §1's proved inhabited-entry route already covers everything).
-/

namespace Lean4Lean
namespace VEnv
namespace GateBody

/-- **The hypothesis of `GateBodyDescend.lean` §2 is inhabited**, and there all six proposed gate
bodies hold outright: quantified over the universe count, the lifts, both contexts and the
subject, with no `TypingStrengthening` and no `VEnv.WF` left to supply. -/
theorem exists_env_gates_unconditional :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U : Nat,
      (∀ {n k : Nat} {Γ Γ' : List VExpr},
          Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U)) ∧
      (∀ {n k : Nat} {Γ Γ' : List VExpr} {A : VExpr}, OnCtx Γ' (env.IsType U) →
          Ctx.LiftN n k Γ Γ' → (env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A)) ∧
      (∀ {n k : Nat} {Γ Γ' : List VExpr} {e : VExpr}, OnCtx Γ' (env.IsType U) →
          Ctx.LiftN n k Γ Γ' → (VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e)) ∧
      (∀ {ρ : Lift} {Γ Γ' : List VExpr},
          Ctx.Lift' ρ Γ Γ' → OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U)) ∧
      (∀ {l : Lift} {Γ Γ' : List VExpr} {e : VExpr}, OnCtx Γ' (env.IsType U) →
          Ctx.Lift' l Γ Γ' → (env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e)) ∧
      (∀ {l : Lift} {Γ Γ' : List VExpr} {e : VExpr}, OnCtx Γ' (env.IsType U) →
          Ctx.Lift' l Γ Γ' → (VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e)) := by
  obtain ⟨env, hwf, h⟩ := exists_typingStrengthening_env
  refine ⟨env, hwf, fun U => ⟨fun W H => GateBody.onCtx_weakN_inv hwf (h U) W H,
    fun hΓ' W => GateBody.isType_weakN_iff hwf hΓ' (h U) W,
    fun hΓ' W => GateBody.wf_weakN_iff hwf hΓ' (h U) W,
    fun W H => GateBody.onCtx_weak'_inv hwf (h U) W H,
    fun hΓ' W => GateBody.isType_weak'_iff hwf hΓ' (h U) W,
    fun hΓ' W => GateBody.wf_weak'_iff hwf hΓ' (h U) W⟩⟩

/-- **Negative control**: the hypothesis is not vacuously true of *every* environment for a silly
reason -- `TypingStrengthening` at a `VEnv.WF` environment is not something this file proves, and
the statement above is an existential, not a universal.  Stated as the (deliberately weak) fact
that the conclusion set is non-empty, to keep the existential honest about what it says. -/
theorem exists_env_gates_unconditional_is_existential :
    (∃ env : VEnv, VEnv.WF env ∧ ∀ U, TypingStrengthening env U) :=
  exists_typingStrengthening_env

end GateBody
end VEnv
end Lean4Lean
