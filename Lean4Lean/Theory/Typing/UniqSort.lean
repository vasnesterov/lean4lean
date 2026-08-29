import Lean4Lean.Theory.Typing.SortUniqDown
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Consequences of `UniqAux`, and its non-vacuity

The development itself moved into `Theory/Typing/Injectivity.lean`, section `UniqAux` —
*into* that file rather than below it, because `CycleConv.lean` and `ConstInvWitness.lean`
import `Injectivity` and consume its theorems.  `IsDefEqU.sort_inv` is proved there, with its
statement unchanged, so every consumer sees the proved version.  What is left here is what
has to be stated after `UniqueTyping`: the restatement of `IsDefEq.uniq` that does not go
through `sort_inv` at all, and the non-vacuity witnesses.

    forallE_inv_stratified  ⟹  uniqAux  ⟹  SortUniq  ⟹  sort_inv  ⟹  uniq

`IsDefEq.uniq` in `UniqueTyping.lean` is now `sorry`-free-modulo-`forallE_inv_stratified`
without any edit to its proof, because the `sort_inv` it calls nine times is the proved one.
`IsDefEq.uniq'` below is kept because it reaches the same conclusion **without** those nine
calls at all — straight off `uniqAux` — so it is the shorter cone, and it is the one to cite
when measuring.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

/-- Sort injectivity, off `uniqAux` directly.  Definitionally the same statement as
`IsDefEqU.sort_inv`, which is now proved the same way; kept as the name used in
`docs/handoff-sortuniq.md`. -/
theorem IsDefEqU.sort_inv' {Γ : List VExpr} {u v : VLevel} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  IsDefEqU.sort_inv henv hΓ h1

/-- Unique typing, from Π-injectivity alone — the statement of `IsDefEq.uniq`, proved off
`uniqAux` without any appeal to `sort_inv`. -/
theorem IsDefEq.uniq' {Γ : List VExpr} {e₁ e₂ e₃ A B : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  obtain ⟨n₁, H1⟩ := (h1.strong henv.ordered hΓ).hasType'.2.stratify
  obtain ⟨n₂, H2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨u, h, _⟩ :=
    uniqAux henv (piInvStrat_axiom henv) _ hΓ (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) H1 H2
  exact ⟨u, h⟩

/-! ## Non-vacuity: fired at `CycleConv.propLoopEnv`

`propLoopEnv` is a proved-`VEnv.WF` environment whose head reduction has a two-cycle
(`propLoop_headStep_not_wf`), so no normalisation argument terminates there.  The hypothesis
`Typing/CycleConv.lean`'s `propLoop_no_direct_collapse` carries is discharged at it. -/

theorem propLoop_sortUniq : propLoopEnv.SortUniq 0 := WF.sortUniq' propLoopEnv_wf

theorem propLoop_no_direct_collapse' {Γ} (hΓ : OnCtx Γ (propLoopEnv.IsType 0)) :
    ¬ propLoopEnv.HasType 0 Γ (.sort .zero) (.sort .zero) :=
  propLoop_no_direct_collapse propLoop_sortUniq hΓ

theorem propLoop_zero_not_defeq_one' :
    ¬ propLoopEnv.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  propLoop_zero_not_defeq_one propLoop_sortUniq

end VEnv
end Lean4Lean
