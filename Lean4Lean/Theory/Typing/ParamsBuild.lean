import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.PatternRules

/-!
# `VEnv.Params` from `VEnv.WF`, modulo one field

`Theory/Typing/ChurchRosser.lean` and `Theory/Typing/HeadReduction.lean` are stated under
`variable [Params]`, and `Params` carries `env`/`henv` as fields, so nothing they prove is
about an arbitrary `VEnv.WF` environment until `Params` is *constructed* from one.

`Theory/Typing/PatternRules.lean` already proves five of the six non-data fields for the
canonical choice `Params.Pat := Lean4Lean.Pat env`:

| field | supplied by |
|---|---|
| `pat_simple` | `Pat.simple` |
| `pat_uniq` | `Pat.uniq henv` |
| `pat_app_l_uniq` | `Pat.app_l_uniq` |
| `pat_app_uniq` | `Pat.app_uniq` |
| `extra_pat` | `Pat.extra henv` |
| `pat_wf` | **open** -- `PatWF` below |

This file cashes that in: `paramsOfWF` builds the instance from `env.WF`, a universe count,
and `PatWF env U` alone, so the whole class is reduced to one named residual.  `PatWF` is
*not* a restatement of the target: it is one field of ten, and the other nine are discharged
here.

`PatWF` is then proved outright on the **δ fragment** (`patWF_of_deltaFragment`), where it
needs nothing but `IsDefEq.extra` and `HasType.const_inv`; the ι and quotient cases are what
need `IsDefEqU.forallE_inv` (`Theory/Typing/Injectivity.lean`).  `Theory/Typing/
ParamsWitness.lean` carries an independent hand-built instance over `CycleConv.propLoopEnv`.

**CORRECTED 2026-09-04.  `IsDefEqU.forallE_inv` is NOT open, and this file saying so cost three
rounds.**  Measured: arity 10, cone 3574, **`own value is a hole: false`** -- it is a *theorem*,
proved from `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`, which are the two actual
census holes.  So the ι and quotient cases are **priced, not blocked**, and
`Verify/Typing/ConstSpineWF.lean:57`'s `patWF_of_wf` discharges `PatWF` at an **arbitrary**
well-formed environment on exactly that footing.

What went wrong downstream: a round read "(open)" here and concluded that **no `Params` instance
over an environment containing a structure exists**; the correction of that round then guessed the
remaining obligation was `VEnv.WF` of the environment, which was **also** already proved
(`MutField.declEnv_wf`, `unitEnv_wf`, both `sorryAx`-free); and a third round finally built
`MutField.declParams` with **no hypotheses at all**.  "Tainted by a known hole" and "open" are
different verdicts, and the difference is one `scripts/exists.lean` run -- `own value is a hole:
false` together with a non-empty `holes in cone` is the signature of a theorem standing on holes.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

/-- **The one `Params` field `VEnv.WF` does not supply**, stated at the canonical `Pat`.

Semantically: a registered rule, fired at a term the environment actually types, is a
definitional equality of that environment. -/
def PatWF (env : VEnv) (U : Nat) : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr} {Γ : List VExpr},
    Pat env p r → p.Matches e m1 m2 → OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → r.2.OK (env.IsDefEqU U Γ) m1 m2 →
    env.IsDefEqU U Γ e (r.1.apply m1 m2)

/-- **`Params` from `VEnv.WF` plus `PatWF`.**  Nine of the ten fields come from `env.WF`
alone. -/
@[instance_reducible] def paramsOfWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : PatWF env U) : Params where
  env := env
  henv := henv
  univs := U
  Pat := Pat env
  pat_simple := Pat.simple
  pat_uniq := Pat.uniq henv
  pat_wf := hwf
  pat_app_l_uniq := Pat.app_l_uniq
  pat_app_uniq := Pat.app_uniq
  extra_pat := fun _ h1 h2 h3 => Pat.extra henv h1 h2 h3

/-! ## The δ fragment

`PatWF`'s δ case needs nothing that is not already proved: `HasType.const_inv` pins the
matched level list to the rule's `uvars`, and `IsDefEq.extra` is the rule.  It is the ι and
quotient cases that need `IsDefEqU.forallE_inv` (`Theory/Typing/Injectivity.lean` -- a
**theorem**, not a hole; see the module docstring's 2026-09-04 correction), so an environment that
registers only δ-rules gets a `Params` instance **hole-free**, while one with ι-rules gets one
**priced at two census holes** rather than not at all. -/

/-- Every pattern the environment registers is a δ-rule's: a bare `.const`. -/
def DeltaFragment (env : VEnv) : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat env p r → ∃ c, p = .const c

/-- **The δ case of `PatWF`, unconditionally.**  Stated separately from
`patWF_of_deltaFragment` so that a future ι/quot proof can reuse it. -/
theorem patWF_delta {env : VEnv} (henv : env.WF) {U : Nat} {c : Lean.Name} {u : Nat}
    {v t e A : VExpr} {m1 m2} {Γ : List VExpr} (hv : v.Closed)
    (hrule : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩)
    (hm : (Pattern.const c).Matches e m1 m2) (hΓ : OnCtx Γ (env.IsType U))
    (hT : env.HasType U Γ e A) :
    env.IsDefEqU U Γ e ((deltaRHS c v hv).apply m1 m2) := by
  cases hm
  rename_i ls
  obtain ⟨ci, hci, hlsWF, hlen⟩ := HasType.const_inv henv.ordered hΓ hT
  obtain ⟨ci', hci', -, hlen'⟩ :=
    HasType.const_inv (Γ := []) henv.ordered trivial (henv.ordered.defEqWF hrule).1
  rw [hci] at hci'
  cases hci'
  simp only [VLevel.params_length] at hlen'
  have hls : ls.length = u := by omega
  refine ⟨t.instL ls, ?_⟩
  have h := IsDefEq.extra (env := env) (uvars := U) (Γ := Γ) hrule hlsWF hls
  simpa [VExpr.instL, VLevel.inst_map_id hls, deltaRHS, Pattern.RHS.apply] using h

/-- **`PatWF` on the δ fragment.** -/
theorem patWF_of_deltaFragment {env : VEnv} (henv : env.WF) (U : Nat)
    (hd : DeltaFragment env) : PatWF env U := by
  intro p r e A m1 m2 Γ hp hm hΓ hT _
  obtain ⟨c, rfl⟩ := hd hp
  cases hp with
  | delta hv hrule => exact patWF_delta henv hv hrule hm hΓ hT

/-- **`Params` for a δ-fragment environment, from `VEnv.WF` alone.** -/
@[instance_reducible] def paramsOfDelta {env : VEnv} (henv : env.WF) (U : Nat) (hd : DeltaFragment env) : Params :=
  paramsOfWF henv U (patWF_of_deltaFragment henv U hd)

/-! ## What the instance unlocks

`IsDefEq.church_rosser` is stated about `Params.env`; through `paramsOfWF` it becomes a
statement about an arbitrary `VEnv.WF` environment.  **Not `sorry`-free**: it inherits
`sorryAx` from `NormalEq.descend` and `IsDefEqU.forallE_inv_stratified`.  Recorded because it
is the exact statement the strengthening route wants, and because typechecking it is the
check that `paramsOfWF` really discharges every obligation `church_rosser` asks for. -/
theorem church_rosser_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : PatWF env U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {e₁ e₂ A : VExpr}
    (H : env.IsDefEq U Γ e₁ e₂ A) : @CRDefEq (paramsOfWF henv U hwf) Γ e₁ e₂ :=
  @IsDefEq.church_rosser Γ (paramsOfWF henv U hwf) hΓ e₁ e₂ A H

end VEnv
end Lean4Lean
