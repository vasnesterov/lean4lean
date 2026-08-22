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

/-! ## C4 — the stratified form, and the level alignment that makes it possible

`Theory/Typing/UniqueTyping.lean`'s `IsDefEq.uniq` consumes `forallE_inv_stratified`, not
`forallE_inv`, so delivering the unstratified form alone unblocks nothing there.  The
stratified conclusion pins the **same** level in its `IsDefEq` and in its
`HasTypeStratified`, and `uniq` genuinely uses that pinning (`UniqueTyping.lean:55`, where
`.sortDF … e3.symm` and `d3.instN` must meet at one level).

That pinning is the whole difficulty.  `forallE_inv` returns a level unrelated to the one
the stratified hypothesis carries, and reconciling two types of one term on the `VExpr` side
*is* `IsDefEq.uniq` — the thing being unblocked.  **It is not circular on the `SExpr` side**:
`SExpr.HasTypeS.uniq` is already proved, so `sort_uniq_of_hasType` below gets the level
equivalence for free, and the cycle opens.  See `docs/research-const-inv.md` §10.3. -/

/-- **Sort uniqueness for a term with two sort typings — without `IsDefEq.uniq`.**

This is `uniq` composed with `sort_inv`, restricted to sorts, but proved *independently* of
both by going through the `SExpr` side, where unique typing (`SExpr.HasTypeS.uniq`) is
already available.  That independence is the point: it is what lets `forallE_inv_stratified`
be derived rather than assumed. -/
theorem sort_uniq_of_hasType {Γ : List VExpr} {U : Nat} {e : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType U))
    (h1 : Params.env.HasType U Γ e (.sort u)) (h2 : Params.env.HasType U Γ e (.sort v)) :
    u ≈ v := by
  have hΓ' := hΓ.toSExpr
  have H1 := (SExpr.IsDefEq.toHasTypeS (VEnv.IsDefEq.toSExpr h1) hΓ').1
  have H2 := (SExpr.IsDefEq.toHasTypeS (VEnv.IsDefEq.toSExpr h2) hΓ').1
  have ⟨_, hw⟩ := H1.uniq hΓ' H2
  exact SLevel.mk_inj.1 (SExpr.sort_inv hΓ' hw)

/-- **Π-injectivity at a level of the caller's choosing.**  `forallE_inv_params` hands back
whatever levels the shape model produced; this retypes the two component equalities at any
levels the components are already known to inhabit. -/
theorem forallE_inv_at {Γ : List VExpr} {U : Nat} {A B A' B' : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType U))
    (h1 : Params.env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (hu : Params.env.HasType U Γ A (.sort u))
    (hv : Params.env.HasType U (A::Γ) B (.sort v)) :
    Params.env.IsDefEq U Γ A A' (.sort u) ∧
    Params.env.IsDefEq U (A::Γ) B B' (.sort v) := by
  have henv : VEnv.Ordered Params.env := Params.henv
  obtain ⟨⟨u', hA⟩, v', hB⟩ := VEnv.IsDefEqU.forallE_inv_params hΓ h1
  have hΓA : OnCtx (A::Γ) (Params.env.IsType U) := ⟨hΓ, _, hu⟩
  have eu : u' ≈ u := sort_uniq_of_hasType hΓ hA.hasType.1 hu
  have ev : v' ≈ v := sort_uniq_of_hasType hΓA hB.hasType.1 hv
  exact ⟨.defeqDF (.sortDF (hA.sort_r henv hΓ) (hu.sort_r henv hΓ) eu) hA,
    .defeqDF (.sortDF (hB.sort_r henv hΓA) (hv.sort_r henv hΓA) ev) hB⟩

/-- **C4.**  `IsDefEqU.forallE_inv_stratified` (`Theory/Typing/Injectivity.lean`), relative
to `Params`.

This is the link that makes Church–Rosser reachable: it unblocks `IsDefEq.uniq`, which
unblocks all of `ChurchRosser.lean`, which delivers const-application disjointness,
injectivity and rigidity together (`docs/research-const-inv.md` §5).

The two halves are asymmetric.  The domain needs no alignment at all — `hA₀`'s level is the
one `forallE_inv_at` is asked for.  The codomain does: `h3` types `B'` in `A'::Γ` while the
equality lives in `A::Γ`, so the two are brought together by context conversion along
`A ≡ A'` and then compared with `sort_uniq_of_hasType`. -/
theorem forallE_inv_stratified_params {Γ : List VExpr} {U n n' : Nat}
    {A B A' B' V V' : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType U))
    (h1 : Params.env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : Params.env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : Params.env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, Params.env.IsDefEq U Γ A A' (.sort u) ∧
       Params.env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, Params.env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      Params.env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      Params.env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := by
  have henv : VEnv.Ordered Params.env := Params.henv
  obtain ⟨hn, u₀, v₀, hA₀, hB₀⟩ := h2.forallE_inv'
  obtain ⟨hn', u₀', v₀', hA₀', hB₀'⟩ := h3.forallE_inv'
  obtain ⟨hAA, hBB⟩ := forallE_inv_at hΓ h1 hA₀.hasType hB₀.hasType
  have hΓA' : OnCtx (A'::Γ) (Params.env.IsType U) := ⟨hΓ, _, hA₀'.hasType⟩
  have hctx : VEnv.IsDefEqCtx Params.env U [] (A::Γ) (A'::Γ) := .succ (.refl hΓ) hAA
  have hB'v₀ : Params.env.HasType U (A'::Γ) B' (.sort v₀) :=
    VEnv.HasType.defeqDFC henv hctx hBB.hasType.2
  have ev : v₀' ≈ v₀ := sort_uniq_of_hasType hΓA' hB₀'.hasType hB'v₀
  have wv₀' : v₀'.WF U := hB₀'.hasType.sort_r henv hΓA'
  have wv₀ : v₀.WF U := hB'v₀.sort_r henv hΓA'
  refine ⟨⟨u₀, hAA, hA₀.mono (by omega)⟩, v₀, hBB, hB₀.mono (by omega), ?_⟩
  have := VEnv.HasTypeStratified.defeq (n := n' - 1) (u := .succ v₀') wv₀'
    (.sortDF wv₀' wv₀ ev) (.base (.sort' wv₀' wv₀' rfl)) (.base (.sort' wv₀ wv₀' ev.symm)) hB₀'
  exact (show n' - 1 + 1 = n' by omega) ▸ this

end Lean4Lean
