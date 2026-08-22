import Lean4Lean.Experimental.Reflect.Induction
import Lean4Lean.Experimental.UniqueTyping

/-!
# Reflection `SExpr → VExpr`: Π-injectivity

`IsDefEqU.forallE_inv` — the second of `Theory/Typing/Injectivity.lean`'s three `sorry`s —
relative to a `Params` / `ParamsExtra` instance, in the same style as
`Experimental/BridgeInjectivity.lean`'s `sort_inv_params` and `sort_forallE_inv_params`.

## Why this file exists separately

`forallE_inv`'s conclusion is a *positive* `VExpr` derivation, unlike `sort_inv`'s `u ≈ v`
and `sort_forallE_inv`'s `False`, so it needs the reflection `SExpr → VExpr` and not just
the forward bridge.  `docs/research-forallE-inv.md` §12 works through why no other route
reaches it.

This is the **only** file of `Experimental/Reflect/` that imports
`Experimental/UniqueTyping.lean`, and hence the only one that depends on
`ShapeLogRelAdequacy.lean` and `ShapeLogRel.lean`.  It does two things `Align.lean` and
`Induction.lean` deliberately cannot:

* discharges `SortUniq` from `SExpr.IsDefEq.uniq_sort`, and
* consumes `SExpr.forallE_inv`, the shape model's own Π-injectivity.

Keeping them here is what let the other 400 lines be written and checked while
`ShapeLogRel.lean` was being rewritten underneath.

## What is still missing to close `Theory/Typing/Injectivity.lean`

The same thing as for `sort_inv`: a `Params` (and `ParamsExtra`) instance for an arbitrary
`env` with `VEnv.WF env`.  Nothing in the repo instantiates either; see
`BridgeInjectivity.lean`'s module docstring, which says why `ParamsExtra` is the real
content.  Until then this is stated `Params`-relative, and `Injectivity.lean`'s derivation
of `forallE_inv` from `forallE_inv_stratified` stays as it is — note that once an instance
exists the arrow reverses, since this proof does not go through the stratified form.
-/

namespace Lean4Lean

open VExpr

variable [Params] [SExpr.ParamsExtra]

/-- `SortUniq`, discharged.  This is the whole content of the seam: `uniq_sort` carries a
`Ctx.WF Γ`, and the reflection has one at every node because its `VExpr`-side invariant
`OnCtx Γ (env.IsType U)` is maintainable through `beta` and `OnCtx.toSExpr` converts it. -/
theorem sortUniq : SortUniq := fun h1 h2 hΓ => SExpr.IsDefEq.uniq_sort h1 h2 hΓ

/-- **Π-injectivity**, relative to `Params`.

The chain: push the hypothesis forward with `VEnv.IsDefEq.toSExpr`; retype it at a sort
(the `SExpr` side's `HasTypeS.toStructural`, since a `.forallE` subject can only be typed
structurally by `HasTypeS.forallE`); apply the shape model's `SExpr.forallE_inv`; reflect
each component back with `reflect`; and bring each down to the ambient universe-parameter
count with `IsDefEq.descend'`. -/
theorem VEnv.IsDefEqU.forallE_inv_params {Γ : List VExpr} {A B A' B' : VExpr} {U : Nat}
    (hΓ : OnCtx Γ (Params.env.IsType U))
    (H : Params.env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, Params.env.IsDefEq U Γ A A' (.sort u)) ∧
    ∃ u, Params.env.IsDefEq U (A::Γ) B B' (.sort u) := by
  have henv : VEnv.Ordered Params.env := Params.henv
  obtain ⟨V, H⟩ := H
  obtain ⟨⟨wA, wB⟩, ⟨wA', wB'⟩, _⟩ :=
    H.levelWF (VEnv.CtxStrong.strong henv hΓ).levelWF
  have hΓA : OnCtx (A::Γ) (Params.env.IsType U) := ⟨hΓ, (H.hasType.1.forallE_inv henv).1⟩
  -- Forward, then retype at a sort.
  have hΓ' := hΓ.toSExpr
  have H' := VEnv.IsDefEq.toSExpr H
  obtain ⟨_, hstruct, transport⟩ := (SExpr.IsDefEq.toHasTypeS H' hΓ').1.toStructural
  cases hstruct with | forallE _ _ => ?_
  obtain ⟨_, hw⟩ := transport SExpr.IsDefEq.sort
  -- The shape model's Π-injectivity.
  obtain ⟨_, _, hAA, hBB⟩ := SExpr.forallE_inv hΓ' (hw.symm.defeqDF H')
  refine ⟨?_, ?_⟩
  · obtain ⟨U₁, x, y, T, le, hx, hy, hT, d⟩ := reflect henv sortUniq hAA Γ U rfl hΓ
    obtain ⟨_, rfl, _⟩ := SExpr.mk_eq_sort hT
    obtain ⟨wx, wy, _⟩ := d.levelWF (VEnv.CtxStrong.strong henv (hΓ.mono_uvars le)).levelWF
    exact ⟨_, d.descend' henv hΓ (VEnv.EqUpToLevels.of_mk hx wx (wA.mono le))
      (VEnv.EqUpToLevels.of_mk hy wy (wA'.mono le)) wA wA'⟩
  · obtain ⟨U₁, x, y, T, le, hx, hy, hT, d⟩ := reflect henv sortUniq hBB (A::Γ) U rfl hΓA
    obtain ⟨_, rfl, _⟩ := SExpr.mk_eq_sort hT
    obtain ⟨wx, wy, _⟩ := d.levelWF (VEnv.CtxStrong.strong henv (hΓA.mono_uvars le)).levelWF
    exact ⟨_, d.descend' henv hΓA (VEnv.EqUpToLevels.of_mk hx wx (wB.mono le))
      (VEnv.EqUpToLevels.of_mk hy wy (wB'.mono le)) wB wB'⟩

end Lean4Lean
