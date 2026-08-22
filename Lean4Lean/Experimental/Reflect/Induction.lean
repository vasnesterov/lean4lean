import Lean4Lean.Experimental.Reflect.Align

/-!
# Reflection `SExpr → VExpr`: the induction

Turns an `SExpr.IsDefEq` derivation between `mk`-images of `VExpr` terms back into a
`VEnv.IsDefEq` derivation.  See `docs/research-forallE-inv.md` §12 for why this is the route
to `IsDefEqU.forallE_inv`, and §12.2 for why the source is `SExpr.IsDefEq` rather than the
`trans'`-free `IsDefEq'`.

## The three design points, each forced

* **Preimages are existential, not computed.**  `SExpr.mk` is not injective, so there is no
  `rep : SExpr → VExpr` that commutes with `SExpr.instL` on the nose.  Choosing preimages
  existentially lets the `const` and `extra` cases land exactly (via `SExpr.mk_instL`), and
  concentrates the slack in the cases that must reconcile two sibling premises anyway —
  where `Align.lean`'s `align*` lemmas absorb it.

* **`Γ` is universally quantified**, over `VExpr` contexts whose `mk`-image is the `SExpr`
  context.  The binder cases must instantiate it at `Aᵥ :: Γ` where `Aᵥ` is produced by a
  *sibling* premise's induction hypothesis; in `beta` the binder's preimage comes from
  premise 2 and is needed for premise 1.  This is also what makes those cases need no
  alignment at all (§13.3): the context preimage is chosen once and threaded, rather than
  produced twice and reconciled.

* **`U` is universally quantified and `U ≤ U'` is in the conclusion.**  `uvars` is a bound,
  not a commitment (`IsDefEq.mono_uvars`), and the level side conditions the `VExpr` rules
  carry are discharged by choosing `U'` past whatever the chosen representatives mention
  (`VLevel.exists_wf`).  The ambient `U` is recovered at the very end by `IsDefEq.descend`,
  which is outside this file.

## `huniq`

The `trans'` rule has no `VExpr` counterpart, and its admissibility is `SExpr`-side sort
uniqueness.  That is taken here as an explicit hypothesis in the exact shape of
`SExpr.IsDefEq.uniq_sort`, **including its `Ctx.WF Γ`** — which is what makes it a seam
rather than a deferral: `uniq_sort` discharges it today, whereas
`IsDefEq.toIsDefEq'`'s `huniq` quantifies over all contexts with no well-formedness and is
not dischargeable.  The `Ctx.WF` is available at every node because the `VExpr`-side context
invariant `OnCtx Γ (env.IsType U)` is maintainable through `beta` (via `IsDefEq.isType`,
which `SExpr` has no analogue of) and `OnCtx.toSExpr` converts it.

Keeping `huniq` a hypothesis is what lets this file import only `Align.lean`, and so avoid
`ShapeLogRelAdequacy.lean` and `ShapeLogRel.lean` entirely.  The capstone discharges it.
-/

namespace Lean4Lean

open VExpr

variable [Params]

/-- What the reflection produces at one node: *some* `VExpr` derivation, at *some*
universe-parameter count at least the ambient one, whose three components are preimages of
the `SExpr` node's. -/
def Reflects (env : VEnv) (Γ : List VExpr) (U : Nat) (e₁' e₂' A' : SExpr) : Prop :=
  ∃ U' e₁ e₂ A, U ≤ U' ∧ SExpr.mk e₁ = e₁' ∧ SExpr.mk e₂ = e₂' ∧ SExpr.mk A = A' ∧
    env.IsDefEq U' Γ e₁ e₂ A

/-- Sort uniqueness on the `SExpr` side, in `SExpr.IsDefEq.uniq_sort`'s exact shape.
Discharged in the capstone; see the module docstring. -/
abbrev SortUniq [Params] : Prop :=
  ∀ {Γ : List SExpr} {e₁ e₂ e₃ : SExpr} {u v : SLevel},
    SExpr.IsDefEq Γ e₁ e₂ (.sort u) → SExpr.IsDefEq Γ e₂ e₃ (.sort v) →
    SExpr.Ctx.WF Γ → u = v

/-- **The reflection.** -/
theorem reflect (henv : VEnv.Ordered Params.env) (huniq : SortUniq) :
    ∀ {Γ' : List SExpr} {e₁' e₂' A' : SExpr}, SExpr.IsDefEq Γ' e₁' e₂' A' →
      ∀ (Γ : List VExpr) (U : Nat), Γ.map SExpr.mk = Γ' →
        OnCtx Γ (Params.env.IsType U) → Reflects Params.env Γ U e₁' e₂' A' := by
  intro Γ' e₁' e₂' A' H
  induction H with
  | @bvar Γ' i A' h =>
    intro Γ U hΓm hΓ
    subst hΓm
    obtain ⟨A, hL, hA⟩ := Lookup.of_map_mk h
    exact ⟨U, .bvar i, .bvar i, A, Nat.le_refl _, rfl, rfl, hA, .bvar hL⟩
  | symm _ ih =>
    intro Γ U hΓm hΓ
    obtain ⟨U', x, y, A, le, hx, hy, hA, d⟩ := ih Γ U hΓm hΓ
    exact ⟨U', y, x, A, le, hy, hx, hA, d.symm⟩
  | trans _ _ ih1 ih2 =>
    intro Γ U hΓm hΓ
    obtain ⟨U₁, x, y, A₁, le₁, hx, hy, hA₁, d1⟩ := ih1 Γ U hΓm hΓ
    obtain ⟨U₂, y', z, A₂, le₂, hy', hz, hA₂, d2⟩ := ih2 Γ U hΓm hΓ
    refine have hΓ' := hΓ.mono_uvars (Nat.le_trans le₁ (Nat.le_max_left U₁ U₂)); ?_
    have d1 := d1.mono_uvars (Nat.le_max_left U₁ U₂)
    have d2 := d2.mono_uvars (Nat.le_max_right U₁ U₂)
    have ⟨_, wy, wA₁⟩ := d1.levelWF (VEnv.CtxStrong.strong henv hΓ').levelWF
    exact ⟨_, x, z, A₁, Nat.le_trans le₁ (Nat.le_max_left ..), hx, hz, hA₁,
      d1.trans <| (d2.alignL henv hΓ' wy (hy'.trans hy.symm)).alignT henv hΓ' wA₁
        (hA₂.trans hA₁.symm)⟩
  | appDF _ _ ih1 ih2 =>
    intro Γ U hΓm hΓ
    obtain ⟨U₁, fv, fv', T, le₁, hf, hf', hT, d1⟩ := ih1 Γ U hΓm hΓ
    obtain ⟨U₂, av, av', Av, le₂, ha, ha', hA, d2⟩ := ih2 Γ U hΓm hΓ
    obtain ⟨Av₀, Bv₀, rfl, hA₀, hB₀⟩ := SExpr.mk_eq_forallE hT
    refine have hΓ' := hΓ.mono_uvars (Nat.le_trans le₁ (Nat.le_max_left U₁ U₂)); ?_
    have d1 := d1.mono_uvars (Nat.le_max_left U₁ U₂)
    have d2 := d2.mono_uvars (Nat.le_max_right U₁ U₂)
    have ⟨_, _, wT⟩ := d1.levelWF (VEnv.CtxStrong.strong henv hΓ').levelWF
    exact ⟨_, .app fv av, .app fv' av', Bv₀.inst av,
      Nat.le_trans le₁ (Nat.le_max_left ..), by simp [SExpr.mk, hf, ha],
      by simp [SExpr.mk, hf', ha'], by simp [hB₀, ha],
      d1.appDF (d2.alignT henv hΓ' wT.1 (hA.trans hA₀.symm))⟩
  | lamDF _ _ ih1 ih2 =>
    intro Γ U hΓm hΓ
    obtain ⟨U₁, Av, A'v, S, le₁, hA, hA', hS, d1⟩ := ih1 Γ U hΓm hΓ
    obtain ⟨uv, rfl, _⟩ := SExpr.mk_eq_sort hS
    obtain ⟨U₂, bv, b'v, Bv, le₂, hb, hb', hB, d2⟩ :=
      ih2 (Av::Γ) U₁ (by simp [hA, hΓm]) ⟨hΓ.mono_uvars le₁, _, d1.hasType.1⟩
    exact ⟨_, .lam Av bv, .lam A'v b'v, .forallE Av Bv, Nat.le_trans le₁ le₂,
      by simp [SExpr.mk, hA, hb], by simp [SExpr.mk, hA', hb'], by simp [SExpr.mk, hA, hB],
      (d1.mono_uvars le₂).lamDF d2⟩
  | trans' _ _ ih1 ih2 => sorry             -- B7, the only case using `huniq`
  | sort => sorry                           -- B2
  | const h1 h2 => sorry                    -- B2
  | forallEDF _ _ ih1 ih2 => sorry          -- B4
  | defeqDF _ _ ih1 ih2 => sorry            -- B3
  | beta _ _ ih1 ih2 => sorry               -- B4
  | eta _ ih => sorry                       -- B5
  | proofIrrel _ _ _ ih1 ih2 ih3 => sorry   -- B3
  | extra h1 h2 => sorry                    -- B2

end Lean4Lean
