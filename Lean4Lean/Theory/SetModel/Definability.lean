import Lean4Lean.Theory.SetModel.Interp

/-!
# Definability combinators for the interpretation's building blocks

Every function the model puts inside a `mkLam` — or a `repl`, or a `sep` — must
be `ℒₛₑₜ`-definable **jointly in all its arguments**, and `definability` cannot
be relied on to find those proofs by search once the terms are more than two
layers deep.

## What actually goes wrong, and what fixes it

`definability` is an `aesop` rule set, so it fails in two different ways
(`docs/foundation-gaps.md` §1):

* `maximum rule application depth (30) was reached` — proof *search* ran out of
  budget. The composition rules it needs are registered; it simply could not
  find the path.
* `internal error … goal N was not normalised` — a genuine defect, and no
  amount of extra hypotheses helps.

The first is the one that bites here, and the fix is not to give `aesop` more
lemmas but to **stop asking it to search**: `DefinableFunction₂.comp` applied
explicitly discharges in one step what the tactic cannot find in fifty. That is
all these combinators are — the compositions the interpretation actually uses,
each stated once so the call site is one application.

## The environment-passing discipline

There is a second, cheaper lesson embedded here. `interp`'s own `lam` clause
writes its fibre map as a function of the *environment*:

```
mkLam (interp Γ A).toFun _ (fun ρ v ↦ (interp (A::Γ) b).toFun (snoc ρ v)) _
```

Nothing is captured from an enclosing binder; everything is read back out of
`ρ`. That is what makes nested λs compose, because `fun a ↦ mkLam G hG F hF (r a)`
is then literally `mkLam G hG F hF ∘ r`. A construction that captures the
outer variable directly instead — as a first attempt at `Quot` did — breaks the
composition and needs a bespoke proof for every layer.

**So: read the environment, do not capture.**  `value_definable` below is what
makes that possible.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Projections -/

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem definable_fst : ℒₛₑₜ-function₂[V] (fun (x _ : V) ↦ x) := by definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem definable_snd : ℒₛₑₜ-function₂[V] (fun (_ y : V) ↦ y) := by definability

/-! ### Reading the environment

`ρ ‘ k` is how every term in the interpretation gets at a bound variable, so a
fibre map written in the environment-passing style is built from this. -/

theorem value_definable (k : V) : ℒₛₑₜ-function₁[V] (fun ρ ↦ ρ ‘ k) := by definability

theorem value_definable₂ (k : V) : ℒₛₑₜ-function₂[V] (fun (ρ _ : V) ↦ ρ ‘ k) := by
  definability

/-! ### Substituting into one argument

The composition `definability` cannot find. Both are `DefinableFunction₂.comp`
with a projection in the other slot. -/

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Substitute a definable function into the **first** argument. -/
theorem definable₂_comp₁ {f : V → V → V} (hf : ℒₛₑₜ-function₂[V] f)
    {g : V → V} (hg : ℒₛₑₜ-function₁[V] g) :
    ℒₛₑₜ-function₂[V] (fun x y ↦ f (g x) y) := by
  have h1 : ℒₛₑₜ-function₂[V] (fun (x _ : V) ↦ g x) := by definability
  exact hf.comp h1 definable_snd

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Substitute a definable function into the **second** argument. -/
theorem definable₂_comp₂ {f : V → V → V} (hf : ℒₛₑₜ-function₂[V] f)
    {g : V → V} (hg : ℒₛₑₜ-function₁[V] g) :
    ℒₛₑₜ-function₂[V] (fun x y ↦ f x (g y)) := by
  have h2 : ℒₛₑₜ-function₂[V] (fun (_ y : V) ↦ g y) := by definability
  exact hf.comp definable_fst h2

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Weaken a one-argument definable function by a dummy first argument.  Needed
whenever a fibre map ignores the environment. -/
theorem definable₂_const₁ {f : V → V} (hf : ℒₛₑₜ-function₁[V] f) :
    ℒₛₑₜ-function₂[V] (fun (_ y : V) ↦ f y) := by definability

/-! ### The binder formers, precomposed

`mkLam G hG F hF` is already definable in its environment (`mkLam_definable`).
What a nested λ needs is that composed with the map building the inner
environment — usually `snoc ρ ·`. -/

theorem mkLam_definable_comp (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F)
    {r : V → V} (hr : ℒₛₑₜ-function₁[V] r) :
    ℒₛₑₜ-function₁[V] (fun a ↦ mkLam G hG F hF (r a)) := by
  have := mkLam_definable G hG F hF
  definability

theorem mkForallType_definable_comp (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F)
    {r : V → V} (hr : ℒₛₑₜ-function₁[V] r) :
    ℒₛₑₜ-function₁[V] (fun a ↦ mkForallType G hG F hF (r a)) := by
  have := mkForallType_definable G hG F hF
  definability

theorem mkForallProp_definable_comp (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F)
    {r : V → V} (hr : ℒₛₑₜ-function₁[V] r) :
    ℒₛₑₜ-function₁[V] (fun a ↦ mkForallProp G hG F hF (r a)) := by
  have := mkForallProp_definable G hG F hF
  definability

end Lean4Lean.SetModel
