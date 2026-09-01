import Lean4Lean.Theory.SetModel.AboveAudit
import Lean4Lean.Theory.SetModel.PropSplitUp

/-!
# `ModelFits` from the lift-closed split: the two `lift` fields leave the top-level input

`AboveAudit.modelFits_of_propSplit_inputs` reduces `ModelFits` to

    Ordered  ∧  PropUniq 0  ∧  PropTypeAgree 0  ∧  PropDescend 0  ∧  OracleFits

but it does so through `PropSplitAudit.propSplitOf`, and `StableAudit.lean` proves
that split is `Stable` **iff** `PropDescend` — whose two `lift` fields
`sort_lift_of_strengthening` / `proof_lift_of_strengthening` obtain from
`TypingStrengthening` + `SortDescend`, i.e. from the strengthening hole.

`PropSplitUp.lean` already built a *different* `PropSplit` — `propSplitUp`, over
the lift-closed predicate `IsPropUp` — whose `Stable` costs only
`InstDescendUp` (two fields, both substitution-descent, neither strengthening).
What was missing to use it at the top is the relation slot: `ctxAgreeRd_propSplitOf`
is proved for `propSplitOf` **only**, and `ModelFits` fixes one `L` for all four
components.  §1–§3 close that gap, so the reduction becomes

    Ordered  ∧  PropUniq 0  ∧  PropTypeAgree 0  ∧  InstDescendUp 0  ∧  OracleFits

with `PropUniq 0` still discharged from the goal's own `hfalse`
(`PropUniqFromFalse.PropUniq.of_propTypeAgree`).

The technical content is §1: **a lift splits at a marked context entry**
(`Ctx.Lift'.split_mid`).  `IsPropUp`'s witness lives in a context `Γ'` above
`Δ ++ A' :: Γ`, and to convert `A'` to `A` one needs to locate the image of the
marked entry inside `Γ'` and see that everything above it is independent of the
entry.  That done, `IsDefEq.defeqDFC'` — which already carries an arbitrary common
prefix — finishes.  No typing hypothesis is used in §1; it is de Bruijn
bookkeeping, like `PropSplitUp.lean`'s pushout.

§4 measures the trade exactly:

```
PropDescend nv  ↔  SortLiftDescend nv ∧ ProofLiftDescend nv ∧ InstDescendUp nv
```

so the *only* difference between the old top-level reduction and the new one is
the conjunct `SortLiftDescend ∧ ProofLiftDescend`.  Both `→` and `←` are proved,
so this is a bound in both directions rather than a one-way weakening, and the two
fields of `InstDescendUp` are exhibited separately at a substitution that really
substitutes.

## Only `nv = 0` is needed

`ModelFits` fixes `L : PropSplit env 0`, so `InstDescendUp env 0` is what §3 consumes.
Unlike `PropUniq` / `PropTypeAgree` — for which `PropReduce.lean` proves
`·.of_zero : · env 0 → · env nv` — there is **no** `nv`-reduction for `InstDescendUp`
or `PropDescend` in the tree, and none is needed: nothing downstream of `ModelFits`
asks for either at `nv > 0`.

## What this does **not** claim

`InstDescendUp env 0` is **open**, and this file does not construct a `PropSplit`
or claim `ModelFits` is satisfiable.  It also does not claim `InstDescendUp` is
*strictly* weaker than `PropDescend`: `→` of §4 shows it is no stronger, and the
`←` direction shows what would have to be added back, but no environment
separating them is exhibited.  `PropTypeAgree env 0` is untouched and remains
irreducible for this route: `NotProofNoModel.nonempty_propSplit_iff_agree` proves
`Nonempty (PropSplit env nv) ↔ PropUniq nv ∧ PropTypeAgree nv`, so no choice of
predicate removes it.
-/

namespace Lean4Lean

/-! ## 1. A lift splits at a marked entry -/

theorem Ctx.Lift'.split_mid : ∀ (l : Lift) {Δ Γ Γ' : List VExpr} {A : VExpr},
    Ctx.Lift' l (Δ ++ A :: Γ) Γ' →
    ∃ (Δ' : List VExpr) (ρ : Lift) (Γ'r : List VExpr),
      Γ' = Δ' ++ A.lift' ρ :: Γ'r ∧ Ctx.Lift' ρ Γ Γ'r ∧
      ∀ B : VExpr, Ctx.Lift' l (Δ ++ B :: Γ) (Δ' ++ B.lift' ρ :: Γ'r) := by
  intro l
  induction l with
  | refl =>
    intro Δ Γ Γ' A W
    cases W
    exact ⟨Δ, .refl, Γ, by simp, .refl, fun B => by simpa using Ctx.Lift'.refl⟩
  | skip l ih =>
    intro Δ Γ Γ' A W
    cases W with
    | skip W =>
      obtain ⟨Δ', ρ, Γ'r, rfl, Wρ, hall⟩ := ih W
      exact ⟨_ :: Δ', ρ, Γ'r, rfl, Wρ, fun B => (hall B).skip⟩
  | cons l ih =>
    intro Δ Γ Γ' A W
    match Δ with
    | [] =>
      simp only [List.nil_append] at W
      cases W with
      | cons W => exact ⟨[], l, _, rfl, W, fun B => by simpa using Ctx.Lift'.cons W⟩
    | Y :: Δ₀ =>
      simp only [List.cons_append] at W
      cases W with
      | cons W =>
        obtain ⟨Δ', ρ, Γ'r, rfl, Wρ, hall⟩ := ih W
        exact ⟨Y.lift' l :: Δ', ρ, Γ'r, rfl, Wρ, fun B => by
          simpa using Ctx.Lift'.cons (hall B)⟩

/-! ## 2. `CtxAgree` for the lift-closed predicate -/

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {env : VEnv} {nv : ℕ}

/-- The `IsPropUp` half, one direction, with an arbitrary common prefix. -/
theorem isPropUp_ctxConv (henv : env.Ordered) {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) (Δ : List VExpr) (ls : List ℕ) (B : VExpr)
    (hB : env.IsPropUp nv ls (Δ ++ A' :: Γ) B) : env.IsPropUp nv ls (Δ ++ A :: Γ) B := by
  obtain ⟨l, Γ', v, W, hv, hBv, h0⟩ := hB
  obtain ⟨Δ', ρ, Γ'r, rfl, Wρ, hall⟩ := Ctx.Lift'.split_mid l W
  refine ⟨l, Δ' ++ A.lift' ρ :: Γ'r, v, hall A, hv, ?_, h0⟩
  have hd : env.IsDefEq nv Γ'r (A'.lift' ρ) (A.lift' ρ) (.sort u) := by
    simpa using (h.weak' henv Wρ).symm
  exact VEnv.IsDefEq.defeqDFC' henv (.succ .zero hd) hBv

/-- The `IsProofUp` half, one direction, with an arbitrary common prefix. -/
theorem isProofUp_ctxConv (henv : env.Ordered) {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) (Δ : List VExpr) (ls : List ℕ) (e : VExpr)
    (he : env.IsProofUp nv ls (Δ ++ A' :: Γ) e) : env.IsProofUp nv ls (Δ ++ A :: Γ) e := by
  obtain ⟨l, Γ', C, v, W, hv, heC, hC, h0⟩ := he
  obtain ⟨Δ', ρ, Γ'r, rfl, Wρ, hall⟩ := Ctx.Lift'.split_mid l W
  have hd : env.IsDefEq nv Γ'r (A'.lift' ρ) (A.lift' ρ) (.sort u) := by
    simpa using (h.weak' henv Wρ).symm
  exact ⟨l, Δ' ++ A.lift' ρ :: Γ'r, C, v, hall A, hv,
    VEnv.IsDefEq.defeqDFC' henv (.succ .zero hd) heC,
    VEnv.IsDefEq.defeqDFC' henv (.succ .zero hd) hC, h0⟩

/-- **`CtxAgree` at defeq-converted contexts, for the lift-closed split.** -/
theorem propSplitUp_ctxAgree (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) :
    CtxAgree (propSplitUp env nv henv hU hT) (A' :: Γ) (A :: Γ) := by
  refine ⟨rfl, fun Δ ls => ⟨fun B => ⟨?_, ?_⟩, fun e => ⟨?_, ?_⟩⟩⟩
  · exact isPropUp_ctxConv henv h Δ ls B
  · exact isPropUp_ctxConv henv h.symm Δ ls B
  · exact isProofUp_ctxConv henv h Δ ls e
  · exact isProofUp_ctxConv henv h.symm Δ ls e

/-- **`ModelFits`' relation slot, discharged for the lift-closed split.** -/
theorem ctxAgreeRd_propSplitUp (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) : CtxAgreeRd (propSplitUp env nv henv hU hT) :=
  fun hd => propSplitUp_ctxAgree henv hU hT hd

/-! ## 3. `ModelFits` from the lift-closed split -/

section Fits

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`ModelFits` from three inputs plus the oracle.**  Compare
`AboveAudit.modelFits_of_propSplit_inputs`, whose proof-split slot is
`env.PropDescend 0` (four fields, two of them the strengthening-shaped `lift`
fields).  Here it is `env.InstDescendUp 0` (two fields, neither of them). -/
theorem modelFits_of_propSplitUp_inputs {κ : ℕ → V} {ds : List VDecl} (henv : env.Ordered)
    (hU : env.PropUniq 0) (hT : env.PropTypeAgree 0) (hI : env.InstDescendUp 0)
    (ls : List ℕ) (o : Name → List VLevel → V)
    (hfits : OracleFits (propSplitUp env 0 henv hU hT) κ ls o ds) : ModelFits κ env ds :=
  (modelFits_iff_ctxAgreeRd κ env ds).2
    ⟨ls, propSplitUp env 0 henv hU hT, o, propSplitUp_stable henv hU hT hI,
      ctxAgreeRd_propSplitUp henv hU hT, hfits⟩

/-- **The same with `PropUniq` discharged from the goal's own `hfalse`.**  The
model-side syntactic import at this point is `PropTypeAgree env 0` together with
`InstDescendUp env 0`, on top of `Ordered` and `OracleFits`. -/
theorem modelFits_of_agree_instDescendUp {κ : ℕ → V} {ds : List VDecl} (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0)
    (hI : env.InstDescendUp 0) (ls : List ℕ) (o : Name → List VLevel → V)
    (hfits : OracleFits
      (propSplitUp env 0 henv (VEnv.PropUniq.of_propTypeAgree henv hf hT) hT) κ ls o ds) :
    ModelFits κ env ds :=
  modelFits_of_propSplitUp_inputs henv _ hT hI ls o hfits

end Fits

end SetModel

/-! ## 4. The two residuals, bounded against each other -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **`PropDescend` is exactly the new residual plus the two `lift` statements.**

`→` is `PropSplitUp.instDescendUp_of_propDescend` together with the two
projections; `←` uses `propUpCollapse_of_sortLiftDescend` to turn the lift-closed
conclusion of `InstDescendUp` back into a typing at `Γ₁`.

So the difference between `AboveAudit.modelFits_of_propSplit_inputs` and
`modelFits_of_propSplitUp_inputs` is **precisely** `SortLiftDescend ∧
ProofLiftDescend` — the two fields `StableAudit.sort_lift_of_strengthening` and
`proof_lift_of_strengthening` obtain from `TypingStrengthening` + `SortDescend`,
i.e. from the strengthening hole.  Nothing else moved. -/
theorem propDescend_iff_instDescendUp :
    env.PropDescend nv ↔
      env.SortLiftDescend nv ∧ env.ProofLiftDescend nv ∧ env.InstDescendUp nv := by
  refine ⟨fun hD => ⟨hD.sortLiftDescend, hD.proofLiftDescend, instDescendUp_of_propDescend hD⟩,
    fun ⟨hSL, hPL, hI⟩ => ?_⟩
  refine ⟨fun W hu hA h0 => hSL W hu hA h0, fun W hu he hA h0 => hPL W hu he hA h0, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ ls W h₀ hu hB h0
    exact propUpCollapse_of_sortLiftDescend hSL ls _ _
      (hI.prop_inst W h₀ (IsPropUp.of_hasType hu hB h0))
  · intro _ _ _ _ _ _ _ _ _ ls W h₀ hu he hA h0
    exact proofUpCollapse_of_proofLiftDescend hPL ls _ _
      (hI.proof_inst W h₀ (IsProofUp.of_hasType hu he hA h0))

/-! ### Field-by-field bounds on `InstDescendUp`

Row 11a's discipline: a structure-level bound can be vacuous on the one field
that is false, so each field is exhibited separately.  For each, the premises are
inhabited *and* the conclusion holds at the same instance, at a substitution that
really substitutes (`k = 0`, `B`/`e` mentioning `bvar 0`).  The premise is
obtained from the conclusion by `isPropUp_instN_up`/`isProofUp_instN_up`, whose
ascent direction is free (`PropSplitUp.lean` §4), so nothing is assumed. -/

/-- The witness substitution: `(p : Prop) ⊢ …`, with `∀ q : Prop, q` substituted
for `p`.  `Ctx.InstN` at `k = 0`, so `·.inst e₀ 0` genuinely replaces `bvar 0`. -/
theorem instN_witness :
    Ctx.InstN ([] : List VExpr) falseProp (.sort .zero) 0 [(.sort .zero : VExpr)] [] := .zero

/-- **`prop_inst` is non-vacuous.**  `B = .bvar 0` is a proposition at `[Prop]`,
and `B.inst falseProp 0 = falseProp` is one at `[]`. -/
theorem instDescendUp_prop_inst_witness (henv : env.Ordered) (ls : List ℕ) :
    env.IsPropUp 0 ls [] ((VExpr.bvar 0).inst falseProp 0) ∧
      env.IsPropUp 0 ls [(.sort .zero : VExpr)] (.bvar 0) := by
  have hc : env.IsPropUp 0 ls [(.sort .zero : VExpr)] (.bvar 0) :=
    IsPropUp.of_hasType (u := .zero) trivial (VEnv.IsDefEq.bvar .zero) rfl
  exact ⟨isPropUp_instN_up henv instN_witness SetModel.allProp_hasType hc, hc⟩

/-- **`proof_inst` is non-vacuous.**  `e = λ (h : p), h` — the identity on the
context's propositional variable — is a proof at `[Prop]`, its type being
`.sort (.imax .zero .zero)`, and `e.inst falseProp 0` is the identity on
`∀ q : Prop, q` at `[]`.  Note the conclusion is a *proof*, not a proposition, so
this field is not an instance of the previous one. -/
theorem instDescendUp_proof_inst_witness (henv : env.Ordered) (ls : List ℕ) :
    env.IsProofUp 0 ls [] ((VExpr.lam (.bvar 0) (.bvar 0)).inst falseProp 0) ∧
      env.IsProofUp 0 ls [(.sort .zero : VExpr)] (.lam (.bvar 0) (.bvar 0)) := by
  have hp : env.HasType 0 [(.sort .zero : VExpr)] (.bvar 0) (.sort .zero) :=
    VEnv.IsDefEq.bvar .zero
  have hb : env.HasType 0 [(.bvar 0 : VExpr), (.sort .zero : VExpr)] (.bvar 0) (.bvar 1) :=
    VEnv.IsDefEq.bvar .zero
  have hb2 : env.HasType 0 [(.bvar 0 : VExpr), (.sort .zero : VExpr)] (.bvar 1)
      (.sort .zero) := VEnv.IsDefEq.bvar (.succ .zero)
  have he : env.HasType 0 [(.sort .zero : VExpr)] (.lam (.bvar 0) (.bvar 0))
      (.forallE (.bvar 0) (.bvar 1)) := .lamDF hp hb
  have hty : env.HasType 0 [(.sort .zero : VExpr)] (.forallE (.bvar 0) (.bvar 1))
      (.sort (.imax .zero .zero)) := .forallEDF hp hb2
  have hc : env.IsProofUp 0 ls [(.sort .zero : VExpr)] (.lam (.bvar 0) (.bvar 0)) :=
    IsProofUp.of_hasType (u := .imax .zero .zero) ⟨trivial, trivial⟩ he hty
      (by simp [VLevel.eval, Lean.Nat.imax])
  exact ⟨isProofUp_instN_up henv instN_witness SetModel.allProp_hasType hc, hc⟩

end VEnv

/-! ## Axiom census -/

#print axioms Lean4Lean.Ctx.Lift'.split_mid
#print axioms Lean4Lean.SetModel.isPropUp_ctxConv
#print axioms Lean4Lean.SetModel.isProofUp_ctxConv
#print axioms Lean4Lean.SetModel.propSplitUp_ctxAgree
#print axioms Lean4Lean.SetModel.ctxAgreeRd_propSplitUp
#print axioms Lean4Lean.SetModel.modelFits_of_propSplitUp_inputs
#print axioms Lean4Lean.SetModel.modelFits_of_agree_instDescendUp
#print axioms Lean4Lean.VEnv.propDescend_iff_instDescendUp
#print axioms Lean4Lean.VEnv.instN_witness
#print axioms Lean4Lean.VEnv.instDescendUp_prop_inst_witness
#print axioms Lean4Lean.VEnv.instDescendUp_proof_inst_witness

end Lean4Lean
