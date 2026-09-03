/-
# `TeleMove2`: the `IsDefEqCtx`/`TeleDefEq` bridge, upstream of its consumers

This module holds what `Theory/Inductive/TeleCongr.lean` §1–§3 held, moved **upstream**.

`TeleCongr.lean` imported `CtorBeta.lean` and `RecTyped.lean`, so its discharges were downstream
of the two files that need to *state* the lighter obligations
(`docs/handoff-consumetele.md` §2, machine-checked with two `Unknown constant` probes).  Nothing
here is new mathematics relative to `TeleCongr.lean`; the point is the module position.  Everything
below compiles against `Theory/Inductive/NestedTele.lean` alone, which is what makes
`CtorBeta.lean` able to import it.

* §1 `VEnv.TeleDefEq.of_isDefEqCtx` / `.substC` / `.weak0` — the vocabulary bridge between
  `VIndCtor.WF.params_eq` (an **`IsDefEqCtx`**) and `VEnv.HasArgs.congr_tele` (which consumes a
  **`TeleDefEq`**).  The two relations agree entrywise but recurse from *opposite ends*, so the
  bridge is an induction on the `IsDefEqCtx` with a `TeleDefEq` accumulator.
* §2 `VIndRestore.csubstTy_freshIn` — freshness of the *type*-companion substitution in the
  **pre-block** environment, from the type-staging equation alone.
* §3 `VIndCtor.WF.hasArgs_params_bvars` — obligation (A)'s `hbv`: the parameter spine of a
  constructor's field context, typed against `D.params` rather than against the constructor's own
  substituted copy.  This is what lets `CtorBeta.lean`'s `ctorConstsCR_wf_of_betaD` ask for **four**
  data per companion-pointing recursive field instead of five.

`docs/handoff-telemove2.md` records the move and its measurements; `docs/handoff-telecongr.md`
records what the results do and do not claim (in particular that the `Faithful` shortcut is
**unavailable** at (A), whose field β-step sits at `T.name ∉ K`).
-/
import Lean4Lean.Theory.Inductive.NestedTele

namespace Lean4Lean

/-! ## §1 `IsDefEqCtx` → `TeleDefEq`, and `TeleDefEq` under `substC`

Neither is elsewhere in the tree, and the first is the load-bearing one: without it
`VIndCtor.WF.params_eq` cannot reach `congr_tele` at all. -/

namespace VEnv
variable {env env₀ env₁ : VEnv} {U : Nat} {σ : CSubst}

/-- **`IsDefEqCtx` is a `TeleDefEq`, read from the other end.**  The accumulator `Bs`/`Bs'` is
what makes the two recursion directions meet: `IsDefEqCtx.succ` adds its entry at the *outside*
(so at the *front* of the reversed telescope's tail), and `TeleDefEq.cons` consumes it at the
front, typed in exactly the context `IsDefEqCtx.succ` types it in. -/
theorem TeleDefEq.of_isDefEqCtx_aux :
    ∀ {Γ₁ Γ₂ : List VExpr}, env.IsDefEqCtx U [] Γ₁ Γ₂ →
      ∀ {Bs Bs' : List VExpr}, env.TeleDefEq U Γ₁ Bs Bs' →
        env.TeleDefEq U [] (Γ₁.reverse ++ Bs) (Γ₂.reverse ++ Bs')
  | _, _, .zero, _, _, h => by simpa using h
  | _, _, .succ hC hA, _, _, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact TeleDefEq.of_isDefEqCtx_aux hC (.cons hA h)

/-- **The bridge, at the shape `VIndCtor.WF.params_eq` has it.** -/
theorem TeleDefEq.of_isDefEqCtx {As As' : List VExpr}
    (h : env.IsDefEqCtx U [] As.reverse As'.reverse) : env.TeleDefEq U [] As As' := by
  have := TeleDefEq.of_isDefEqCtx_aux h (Bs := []) (Bs' := []) .nil
  simpa using this

/-- **`TeleDefEq` under constant substitution.**  `IsDefEq.substC` per entry; the `rfl` case
survives because a syntactically unchanged entry stays unchanged after `substC`. -/
theorem TeleDefEq.substC (hσ : σ.WF env₀ env₁ U) :
    ∀ {Γ As As' : List VExpr}, env₀.TeleDefEq U Γ As As' →
      env₁.TeleDefEq U (Γ.map (VExpr.substC · σ)) (As.map (VExpr.substC · σ))
        (As'.map (VExpr.substC · σ))
  | _, _, _, .nil => .nil
  | _, _, _, .rfl h => by
    simpa using TeleDefEq.rfl (TeleDefEq.substC hσ h (Γ := _ :: _))
  | _, _, _, .cons hA h => by
    simpa using TeleDefEq.cons (hA.substC hσ) (TeleDefEq.substC hσ h (Γ := _ :: _))

/-- **Weakening a closed telescope's `TeleDefEq` from `[]` into any context.**
`TeleDefEq.weakN` at `Ctx.LiftN Γ.length 0 [] Γ`, with both `liftTele`s removed by closedness —
which is the form both consumers need, since `hbv` and `hAs` name their telescopes *unlifted*. -/
theorem TeleDefEq.weak0 (henv : env.Ordered) {As As' : List VExpr} (Γ : List VExpr)
    (hcl : VExpr.ClosedTele As 0) (hcl' : VExpr.ClosedTele As' 0)
    (h : env.TeleDefEq U [] As As') : env.TeleDefEq U Γ As As' := by
  have := TeleDefEq.weakN (n := Γ.length) (k := 0) henv (Ctx.LiftN.zero Γ (by simp)) h
  rwa [hcl.liftTele_eq (Nat.le_refl 0), hcl'.liftTele_eq (Nat.le_refl 0), List.append_nil] at this

end VEnv

/-! ## §2 `csubstTy` is fresh in the **pre-block** environment

`VIndRestore.csubst_freshIn` (`NestedRules.lean` §9) needs all three staging successes because
`csubst`'s domain includes the companions' constructor and recursor names.  `csubstTy`'s domain is
only the companion *type* names, so its first branch alone suffices: **one** staging equation, and
`ctorConstsCR_wf_of_betaD` already carries exactly that one (`h₃`).

The environment matters and is easy to get wrong: this is freshness in `env`, the environment
*before* `addIndTypes`.  `(R.csubstTy D K).FreshIn env₃` is **false** whenever `K` names a member
of `D`, because `env₃` declares precisely the names `csubstTy` substitutes. -/

namespace VIndRestore

/-- **`csubstTy` is fresh in the pre-block environment**, from the type-staging success alone. -/
theorem csubstTy_freshIn {env E₁ : VEnv} {R : VIndRestore} {D : VInductDecl'}
    {K : List Lean.Name} (h₁ : env.addIndTypes D = some E₁) :
    (R.csubstTy D K).FreshIn env := by
  intro c ci hc
  cases hn : R.csubstTy D K c with
  | none => rfl
  | some v =>
    obtain ⟨j, T, hT, rfl, -, -⟩ := csubstTy_dom hn
    have := (VEnv.addConstList_fresh h₁).1 T.name (by
      rw [VInductDecl'.typeConsts_names]
      exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)
    rw [this] at hc; exact absurd hc nofun

end VIndRestore

/-! ## §3 Obligation (A)'s `hbv`, **derived**

`CtorBeta.lean` §7's `hbeta` asked for five data at every companion-pointing recursive field, and
its second component was

    e₁.HasArgs D.uvars Γfld D.params (VExpr.bvars (r.binders.length + i) D.np)

where `Γfld` carries the constructor's **own** parameter copy, substituted:
`(C.params.map (·.substC σ)).reverse` at its bottom.  `CtorBeta.lean` §6d proves the spine is in
scope, and what remained was the conversion between the substituted `C.params` that sits in the
context and the `D.params` §8.8 asks for.

That conversion is §1, and `hbv` is a **theorem**.  What it costs: no `Faithful`, no `PiInv`, no
`np` bound, no new datum.  `hclD` and `hσD` are the two facts about `D.params` alone, and
`..._of_wf` derives both from `D.WF env` plus one staging equation.

The statement is generic in the block `Δ` sitting above the parameters, so the same theorem serves
`CtorBeta.lean` §7 (`Δ` = the field's binders and the earlier fields) and any other field-context
shape. -/

namespace VIndCtor
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}
  {σ : CSubst}

/-- **The parameter spine of a constructor's field context, typed against `D.params`.**

`HasArgs.bvars` types it against the constructor's own substituted copy; `params_eq` +
§1's three bridges + `congr_tele` move it to the block's.  `Δ` is any block of binders sitting
above the parameters. -/
theorem WF.hasArgs_params_bvars (he₁ : e₁.Ordered) (hσ : σ.WF env₃ e₁ D.uvars)
    (hCwf : VIndCtor.WF env₃ D j T C)
    (hclD : VExpr.ClosedTele D.params 0)
    (hσD : D.params.map (VExpr.substC · σ) = D.params) (Δ : List VExpr) :
    e₁.HasArgs D.uvars (Δ ++ (C.params.map (VExpr.substC · σ)).reverse)
      D.params (VExpr.bvars Δ.length D.np) := by
  have hCp : OnCtx C.params.reverse (env₃.IsType D.uvars) := hCwf.params_eq.isType
  have hclC : VExpr.ClosedTele (C.params.map (VExpr.substC · σ)) 0 := by
    refine VExpr.ClosedTele.of_onCtx (U := D.uvars) (Γ := []) he₁ ?_
    have := VEnv.OnCtx.substC hσ hCp
    rw [List.map_reverse] at this; simpa using this
  -- the telescope conversion, moved into `e₁` and then into the field context
  have h0 : e₁.TeleDefEq D.uvars [] (C.params.map (VExpr.substC · σ)) D.params := by
    have := (VEnv.TeleDefEq.of_isDefEqCtx (As := C.params) (As' := D.params)
      (by simpa using hCwf.params_eq)).substC hσ (σ := σ)
    rwa [List.map_nil, hσD] at this
  have hΓ := VEnv.TeleDefEq.weak0 he₁ (Δ ++ (C.params.map (VExpr.substC · σ)).reverse)
    hclC hclD h0
  -- the spine, typed against the constructor's own copy, then converted
  have hbv := VEnv.HasArgs.bvars (env := e₁) (U := D.uvars) (Δ := Δ)
    (As := C.params.map (VExpr.substC · σ)) (Γ₀ := [])
  rw [List.append_nil, hclC.liftTele_eq (Nat.le_refl 0), List.length_map,
    hCwf.params_len] at hbv
  exact hbv.congr_tele he₁ hΓ

/-- …with the two `D.params` facts discharged from the block's own well-formedness and the
type-staging equation.  **No hypothesis here that `ctorConstsCR_wf_of_betaD` does not already
carry, except `env.Ordered`** — which every caller has, since it is what `env₃.Ordered` is
derived from. -/
theorem WF.hasArgs_params_bvars_of_wf {R : VIndRestore} {K : List Lean.Name}
    (henv : env.Ordered) (he₁ : e₁.Ordered) (hD : D.WF env)
    (h₃ : env.addIndTypes D = some env₃)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hCwf : VIndCtor.WF env₃ D j T C)
    (Δ : List VExpr) :
    e₁.HasArgs D.uvars
      (Δ ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
      D.params (VExpr.bvars Δ.length D.np) :=
  WF.hasArgs_params_bvars he₁ hσ hCwf
    (VExpr.ClosedTele.of_onCtx (U := D.uvars) (Γ := []) henv (by simpa using hD.params))
    (VEnv.OnCtx.substC_eq_tele henv (VIndRestore.csubstTy_freshIn h₃) (Δ := [])
      (by simpa using hD.params)) Δ

end VIndCtor

end Lean4Lean

/-! ## §4 Axiom lines

Read off the declarations' own namespaces, not composed from the path.  These must be **identical**
to the ones `TeleCongr.lean` printed for the same seven declarations before the move. -/
#print axioms Lean4Lean.VEnv.TeleDefEq.of_isDefEqCtx_aux
#print axioms Lean4Lean.VEnv.TeleDefEq.of_isDefEqCtx
#print axioms Lean4Lean.VEnv.TeleDefEq.substC
#print axioms Lean4Lean.VEnv.TeleDefEq.weak0
#print axioms Lean4Lean.VIndRestore.csubstTy_freshIn
#print axioms Lean4Lean.VIndCtor.WF.hasArgs_params_bvars
#print axioms Lean4Lean.VIndCtor.WF.hasArgs_params_bvars_of_wf
