import Lean4Lean.Theory.SetModel.SoundInduction

/-!
# What the set model owes for the `retype` rule of `Theory/Typing/Enlarged.lean`

`docs/backward-analysis.md` §5 says the `IsDefEqU'` enlargement is "model-neutral", as
*analysis, not machine-checked* (§10).  This file machine-checks it, for the enlargement
actually prototyped in `Theory/Typing/Enlarged.lean` — one rule,

    retype : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ : B → Γ ⊢ e₁ ≡ e₂ : B

`Theory/SetModel/` is **not edited** by this file; it only imports it.  `SoundInduction.lean`'s
induction is over `IsDefEqStrong`, which this file does not change either.  What is checked
here is the *case*: the exact obligation the induction would have to discharge if `retype`
were added, in the exact shapes `SoundInduction.lean` uses (`Sound`, and the `Above`-wrapped
`SoundAbove`).

**The answer is that the case is a re-pairing of its two induction hypotheses**: part 4 from
the first premise, part 3 from the second, with no side condition, no `PropSplit` field, and
no new threshold beyond `Above.and`.  Contrast `defeqDF`, whose case
(`SoundInduction.lean:226`) has to *transport* part 3 along part 4 for the types
(`defeqDF_sound`); `retype` does not, because its second premise already supplies part 3 at
the target type.

Compare the two other cases that pair IHs this way: `Sound.symm` (`InterpSound.lean:92`) and
`Sound.trans`.  `retype` joins them.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit env nv}

/-- **The model obligation for `retype`, discharged.**  Given soundness for the equation at
`A` and soundness for its left endpoint at `B`, soundness for the equation at `B` is the
pair of the two — `eq` from the first, `type` from the second.

This is the whole of what the enlargement costs the model. -/
theorem retype_sound {Γ : List VExpr} {e₁ e₂ A B : VExpr}
    (h₁ : Sound M L Γ e₁ e₂ A) (h₂ : Sound M L Γ e₁ e₁ B) : Sound M L Γ e₁ e₂ B where
  eq := h₁.eq
  type := h₂.type

/-- The same, in the `Above`-wrapped form the induction actually carries.  The two thresholds
merge by `Above.and`; nothing is unwrapped. -/
theorem retype_soundAbove {Γ : List VExpr} {e₁ e₂ A B : VExpr}
    (h₁ : SoundAbove M L Γ e₁ e₂ A) (h₂ : SoundAbove M L Γ e₁ e₁ B) :
    SoundAbove M L Γ e₁ e₂ B := h₁.imp₂ h₂ retype_sound

/-- For contrast, `defeqDF`'s case does **not** have this shape: it must move part 3 across
part 4 for the *types*, which is `defeqDF_sound`.  Spelled out so the difference between the
two rules is visible side by side rather than asserted. -/
theorem defeqDF_sound' {Γ : List VExpr} {e₁ e₂ A B : VExpr}
    (h₁ : Sound M L Γ A B (.sort u)) (h₂ : Sound M L Γ e₁ e₂ A) : Sound M L Γ e₁ e₂ B where
  eq := h₂.eq
  type ρ hρ := defeqDF_sound M L (h₁.eq ρ hρ) (h₂.type ρ hρ)

end Lean4Lean.SetModel
