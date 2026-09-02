import Lean4Lean.Theory.Typing.AppCodType0
import Lean4Lean.Theory.Typing.StratLevelWF
import Lean4Lean.Theory.Typing.StrengthenVerdict

/-!
# The `app` case's levels are `WF`, and the last loophole in the `type0_pin` route closes

`Theory/Typing/AppCodType0.lean` refuted `AppCodType0On` outright and graded its conditioned
repair `AppCodType0OnC` a **collapse**: with `SortRedInv` it yields full level agreement
(`appLvlAgreeOn_of_sortRedInv_codType0OnC`), and on the sub-family where it is not vacuous —
both codomain instances literally sorts — it is *equivalent* to that stronger statement
(`codType0OnC_sortCase_iff_agree`).

**One loophole survived that grading, and it is a level-well-formedness loophole.**  Both
directions of the equivalence, and the sharper `codShareOn_sortCase_forces_syntactic_eq`, carry
side conditions `hu₀ : u₀.WF U` and `hu₁ : u₁.WF U` on the two codomain levels.  They are there
because the only `⊢₀` typing of a sort is `Stratified.sort`, whose premise is exactly `l.WF U`.
Nothing in that file supplies them: the guard `OnCtx Γ (env.IsType U)` constrains the *context*,
and `Stratified`'s unconditional `rfl` means a `⊢ₙ` derivation over a well-formed context can, a
priori, mention arbitrary levels.  So the fringe `B₀.inst a = .sort u₀` with `¬ u₀.WF U` was
unmeasured: on it, neither direction of the collapse was available, and `AppCodType0OnC` might
have been strictly stronger than the target there — or refutable there.

`Theory/Typing/StratLevelWF.lean` closes it.  `HasTypeN.levelWF` says a `⊢ₙ`-typing over a
`LevelWF` context has a `LevelWF` subject *and type*; `onCtx_levelWF` turns the guard into that
context hypothesis; `AppData` carries both function typings.  So the codomain instances are
`LevelWF` and the fringe is **empty**.

**What the trade actually is**, stated precisely rather than favourably: §2's theorems drop
`hu₀`/`hu₁` and pick up `hΓ` and `d`.  That is a strict weakening *for the consumer*, because
`AppCodType0OnC` and `AppLvlAgreeOn` both quantify over `hΓ` and `d` by definition — so at every
point of use nothing is added — and `codType0OnC_sortCase_of_agree'` is strictly weaker in
premises than `codType0OnC_sortCase_of_agree` outright.  It is *not* a strict weakening of the
bare `iff` lemma read in isolation.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. The `app` case's data is level-well-formed -/

/-- **Both codomain instances of an `AppData` are `LevelWF`, under the route's own guard.**

Read off `AppData.fn₀`/`arg₀` (and `fn₁`/`arg₁`) with `HasTypeN.levelWF`: the function's type is
a Π whose codomain is therefore `LevelWF`, the argument is `LevelWF`, and `LevelWF.inst`
combines them.  The guard enters only through `onCtx_levelWF`. -/
theorem AppData.levelWF {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U n Γ f a A₀ B₀ A₁ B₁) :
    (B₀.inst a).LevelWF U ∧ (B₁.inst a).LevelWF U := by
  have W := onCtx_levelWF (env := env) (U := U) hΓ
  have ⟨_, _, hB₀⟩ := HasTypeN.levelWF d.fn₀ W
  have ⟨_, _, hB₁⟩ := HasTypeN.levelWF d.fn₁ W
  have ⟨ha, _⟩ := HasTypeN.levelWF d.arg₀ W
  exact ⟨hB₀.inst ha, hB₁.inst ha⟩

/-- The form the collapse needs: **a codomain instance that is a sort has a `WF` level**, free.
This is the side condition `AppCodType0.lean` had to assume. -/
theorem AppData.sort_levelWF {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ u₁ : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U n Γ f a A₀ B₀ A₁ B₁)
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁) : u₀.WF U ∧ u₁.WF U := by
  obtain ⟨h₀, h₁⟩ := d.levelWF hΓ
  rw [e₀] at h₀; rw [e₁] at h₁
  exact ⟨h₀, h₁⟩

/-- Stated without the `AppData` bundle, for reuse: any `⊢ₙ`-typed term under the guard whose
*type* is a sort has a `WF` level. -/
theorem HasTypeN.sort_levelWF {Γ : List VExpr} {e : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.HasTypeN U n Γ e (.sort u)) : u.WF U :=
  (HasTypeN.levelWF h (onCtx_levelWF (env := env) (U := U) hΓ)).2

/-! ## 2. The collapse, with the loophole closed

Each theorem here is its `AppCodType0.lean` counterpart with `hu₀`/`hu₁` deleted. -/

/-- **`codType0OnC_sortCase_iff_agree` with no level side conditions.**  On the whole sort
sub-family — not a `WF`-level fragment of it — the conditioned side condition and full level
agreement are the same statement. -/
theorem codType0OnC_sortCase_iff_agree' (hsi : SortInvN env U (n+1))
    {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ u₁ u v : VLevel}
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U (n+1) Γ f a A₀ B₀ A₁ B₁)
    (c₀ : env.IsDefEqN U (n+1) Γ (B₀.inst a) (.sort u))
    (c₁ : env.IsDefEqN U (n+1) Γ (B₁.inst a) (.sort v)) :
    (∃ w w' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort w) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort w') ∧ w ≈ w') ↔ u ≈ v :=
  let ⟨hu₀, hu₁⟩ := d.sort_levelWF hΓ e₀ e₁
  codType0OnC_sortCase_iff_agree hsi hu₀ hu₁ e₀ e₁ c₀ c₁

/-- **`codShareOn_sortCase_forces_syntactic_eq` with no level side conditions.**  The weakest
form of the side condition still decides the two levels *syntactically*, everywhere on the sort
sub-family. -/
theorem codShareOn_sortCase_forces_syntactic_eq'
    {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ u₁ : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U n Γ f a A₀ B₀ A₁ B₁)
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (h : ∃ T : VExpr, env.HasTypeN U 0 Γ (B₀.inst a) T ∧ env.HasTypeN U 0 Γ (B₁.inst a) T) :
    u₀ = u₁ :=
  let ⟨hu₀, hu₁⟩ := d.sort_levelWF hΓ e₀ e₁
  codShareOn_sortCase_forces_syntactic_eq hu₀ hu₁ e₀ e₁ h

/-- The remaining direction, likewise unconditional: full agreement re-derives the conditioned
side condition on the sort sub-family. -/
theorem codType0OnC_sortCase_of_agree' (hsi : SortInvN env U (n+1))
    (h : AppLvlAgreeOn env U (n+1))
    {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ u₁ u v : VLevel}
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U (n+1) Γ f a A₀ B₀ A₁ B₁)
    (c₀ : env.IsDefEqN U (n+1) Γ (B₀.inst a) (.sort u))
    (c₁ : env.IsDefEqN U (n+1) Γ (B₁.inst a) (.sort v)) :
    ∃ w w' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort w) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort w') ∧ w ≈ w' :=
  (codType0OnC_sortCase_iff_agree' hsi e₀ e₁ hΓ d c₀ c₁).2 (h hΓ d c₀ c₁)

/-! ## 2b. A claim in `Stratified.lean` that this refutes

`Stratified.forallE` carries two premises `u.WF U` and `v.WF U`, and its docstring says of them:
"Nothing else records them, and they cannot be recovered afterwards without the soundness
direction (which needs `uniq`)."

**The second half of that is false.**  Over a `LevelWF` context they are recovered from the two
typing premises alone, by `HasTypeN.levelWF` reading the *type* `.sort u` — no `uniq`, no
soundness direction, no `Ordered env`, no environment at all.  See `forallE_wf_free` in
`StratLevelWF.lean`; the instance under this file's guard is below.

This does not make the premises removable for free — `thm:utype`'s `forallE` case needs them at
a context that is *not* known `LevelWF` unless the guard is threaded there too — but the stated
reason for keeping them is not the real one. -/

/-- `Stratified.forallE`'s two `WF` premises, recovered under the route's guard. -/
theorem forallE_wf_of_guard {Γ : List VExpr} {A B : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.HasTypeN U n Γ A (.sort u)) (h2 : env.HasTypeN U n (A::Γ) B (.sort v)) :
    u.WF U ∧ v.WF U :=
  forallE_wf_free (onCtx_levelWF (env := env) (U := U) hΓ) h1 h2

/-! ## 3. The fringe is empty, stated as such

The loophole was a *hoped-for* region of the premise space.  This says it does not exist, which
is the form a later reader will want: no `AppData` under the guard has a codomain instance that
is a sort at a non-`WF` level, so no refutation of `AppCodType0OnC` can live there. -/

/-- **The fringe is empty.**  There is no instance of the route's premises with a sort codomain
instance whose level is not `WF U`. -/
theorem no_badLevel_sortCase {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U n Γ f a A₀ B₀ A₁ B₁)
    (e₀ : B₀.inst a = .sort u₀) : u₀.WF U := by
  have h := (d.levelWF hΓ).1
  rw [e₀] at h
  exact h

/-- And the fringe is only empty *because of the guard*: drop it and the analogous statement is
false.  With a bad level in the context, `bvar` supplies both a function at a Π-type and an
argument at its domain — and the codomain instance is a sort at a non-`WF` level.

So the guard is load-bearing for §1–2, not decoration; and this is also where `Stratified`'s
unconditional `rfl` was *not* the culprit — no `rfl` appears in this witness.  The loophole was
never about `rfl`; it was about the guard's reach. -/
theorem badLevel_sortCase_without_guard (env : VEnv) (U n : Nat) :
    ∃ (Γ : List VExpr) (f a A₀ B₀ A₁ B₁ : VExpr) (u₀ : VLevel),
      AppData env U n Γ f a A₀ B₀ A₁ B₁ ∧ B₀.inst a = .sort u₀ ∧ ¬ u₀.WF U := by
  refine ⟨[.sort (.param U), .forallE (.sort (.param U)) (.sort (.param U))],
    .bvar 1, .bvar 0, .sort (.param U), .sort (.param U), .sort (.param U), .sort (.param U),
    .param U, ⟨?_, ?_, ?_, ?_⟩, rfl, Nat.lt_irrefl U⟩
  · exact Stratified.bvar (Lookup.succ Lookup.zero)
  · exact Stratified.bvar Lookup.zero
  · exact Stratified.bvar (Lookup.succ Lookup.zero)
  · exact Stratified.bvar Lookup.zero


section Audit

/-! `#print axioms`, by namespace.  Every declaration in this file is in `Lean4Lean.VEnv`; there is no second namespace. -/
#print axioms Lean4Lean.VEnv.AppData.levelWF
#print axioms Lean4Lean.VEnv.AppData.sort_levelWF
#print axioms Lean4Lean.VEnv.HasTypeN.sort_levelWF
#print axioms Lean4Lean.VEnv.codType0OnC_sortCase_iff_agree'
#print axioms Lean4Lean.VEnv.codShareOn_sortCase_forces_syntactic_eq'
#print axioms Lean4Lean.VEnv.codType0OnC_sortCase_of_agree'
#print axioms Lean4Lean.VEnv.forallE_wf_of_guard
#print axioms Lean4Lean.VEnv.no_badLevel_sortCase
#print axioms Lean4Lean.VEnv.badLevel_sortCase_without_guard

end Audit
end VEnv
end Lean4Lean
