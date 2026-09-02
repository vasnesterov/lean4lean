import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.SetModel.PropSplitAudit
import Lean4Lean.Theory.Consistency

/-!
# `⟦∀ p : Prop, p⟧ = ∅`, and the consistency conclusion it gives

**This is the only place the goal touches the model.**  `kernel_sound` reaches
the model through exactly one statement — `leanTTConsistent`, i.e.
`¬ ∃ e, env.HasType 0 [] e falseProp` — and the model's contribution to it is
one equation: the denotation of `falseProp = ∀ p : Prop, p` at the empty
valuation is the empty set.  Composed with `sound_nil` (part 3 of soundness at
the empty context), a closed inhabitant of `falseProp` would denote an element
of `∅`.

Two things about the equation are worth stating, because both were open
questions before it was written.

**It is branch-independent.**  `interp`'s `forallE` clause splits on
`L.IsProp M [.sort .zero] (.bvar 0)`, and *both* branches give `∅`:

* the `mkForallProp` branch is `{•} ∩ ⋂_{v ∈ ⟦Prop⟧} F v`, and `∅ ∈ UProp`
  contributes the empty fibre;
* the `mkForallType` branch is a set of *functions* on `⟦Prop⟧`, and a function
  must have a value at `∅ ∈ ⟦Prop⟧`, which would have to lie in the empty fibre.

So the conclusion does not depend on the proof split being correct at the one
place it is finally applied.  `PropSplitAudit.prop_forces_true` does pin the
branch (it is the `mkForallProp` one, for *every* `PropSplit` —
`falseProp_isProp_branch` below), but `interp_falseProp` consults no `PropSplit`
field at all.

**It is unconditional — not `Above`-wrapped.**  The only universe the equation
mentions is `U M.κ 0 = UProp = ℘ {•}`, whose definition names no inaccessible.
So no chain hypothesis is consumed here, and the threshold in
`falseProp_above_false` is entirely `sound_nil`'s.

## What this does *not* discharge

`falseProp_above_false` concludes `Above M False`, i.e. *`False` above some
threshold of inaccessibles*.  Turning that into `False` needs a `ModelData`
whose `κ` carries a chain of that length, which is the outer construction
(`exists_inaccessibleChain` plus the constant assignment) and is not built here.
And the whole file runs against `L : PropSplit envF nv`, **a parameter nothing
in the tree constructs**; see `docs/model-interface.md`'s standing label.
-/

namespace Lean4Lean

namespace VEnv

/-! ### `[∀ p : Prop, p]` is an `OnCtx`-well-formed context

Moved here from `SetModel/NotProofNoModel.lean` on 2026-09-02: with `PropSplit`'s fields
guarded by `OnCtx`, this pair is needed by `not_isProp_sort_zero`'s use below, which is three
files earlier than where they used to live. -/

/-- `∀ p : Prop, p` is a type, at every environment: `.sort (.imax 1 0)`. -/
theorem isType_falseProp {env : VEnv} {nv : ℕ} : env.IsType nv [] falseProp :=
  ⟨.imax (.succ .zero) .zero,
    IsDefEq.forallEDF (HasType.sort (l := .zero) trivial) (IsDefEq.bvar .zero)⟩

/-- **`[falseProp]` is an `OnCtx`-well-formed context** — the hypothesis every consumer of
`sort_not_proof` supplies, and (since 2026-09-02) the one `PropSplit`'s fields want at the
context `interp_forallE_falseProp_sort_nonempty` works in. -/
theorem onCtx_falseProp {env : VEnv} {nv : ℕ} : OnCtx [falseProp] (env.IsType nv) :=
  ⟨trivial, isType_falseProp⟩

end VEnv

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- `falseProp` is a `∀` over `Prop` whose body is the bound variable.  Kept as a
named lemma so the two branch proofs below can rewrite by it without unfolding
the `vexpr` elaborator's output. -/
theorem falseProp_eq : falseProp = .forallE (.sort .zero) (.bvar 0) := rfl

/-- The domain of `falseProp`'s `∀` denotes `UProp`, at every valuation. -/
theorem interp_falseProp_dom (ρ : V) :
    (interp M L [] (.sort .zero)).toFun ρ = (UProp : V) := by
  rw [interp_sort]; rfl

/-- The body of `falseProp`'s `∀` denotes the value bound at the binder — the
statement that makes `∅ ∈ UProp` an *empty fibre*. -/
theorem interp_falseProp_body (v : V) :
    (interp M L [VExpr.sort .zero] (.bvar 0)).toFun (snoc ∅ v) = v := by
  rw [interp_bvar]
  have hdom : domain (∅ : V) = ((0 : ℕ) : V) := by simp [zero_def]
  show (snoc ∅ v) ‘ ((0 : ℕ) : V) = v
  rw [← hdom]; exact snoc_value_top IsFunction.empty

/-- **`⟦∀ p : Prop, p⟧ ∅ = ∅`** — no hypothesis on the proof split, no chain of
inaccessibles, no well-formedness.  The two `by_cases` branches are the two
clauses of `interp`'s `forallE` case, and neither can hold an element. -/
theorem interp_falseProp : (interp M L [] falseProp).toFun ∅ = (∅ : V) := by
  have hdom : (interp M L [] (.sort .zero)).toFun (∅ : V) = (UProp : V) :=
    interp_falseProp_dom ∅
  have hemp : (∅ : V) ∈ (interp M L [] (VExpr.sort .zero)).toFun (∅ : V) := by
    rw [hdom]; exact empty_mem_UProp
  refine subset_empty_iff_eq_empty.mp fun z hz ↦ ?_
  rw [falseProp_eq] at hz
  by_cases h : L.IsProp M [VExpr.sort .zero] (.bvar 0)
  · -- the impredicative `∀`: the fibre over `∅ ∈ ⟦Prop⟧` is empty
    have := (mem_interp_forallE_prop_iff M L h).1 hz |>.2 (∅ : V) hemp
    rw [interp_falseProp_body] at this
    simp at this
  · -- the dependent product: a function must have a value over `∅ ∈ ⟦Prop⟧`
    rw [interp_forallE_type M L h, mem_mkForallType_iff] at hz
    obtain ⟨y, -, hy⟩ := exists_of_mem_function hz.1 _ hemp
    have := hz.2 (∅ : V) hemp y hy
    rw [interp_falseProp_body] at this
    simp at this

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **The branch is in fact forced**, for every `PropSplit` —
`PropSplitAudit.prop_forces_true` at `M.ls`.  So the `by_cases` above is a
robustness result, not a necessity: the equation would hold with the
`mkForallProp` branch alone.  Recorded because it is what makes
"`⟦falseProp⟧ = ∅` does not depend on the split being right here" a *checked*
statement rather than a hope. -/
theorem falseProp_isProp_branch : L.IsProp M [VExpr.sort .zero] (.bvar 0) :=
  prop_forces_true L M.ls

/-! ## Non-vacuity: the `forallE` clause is not uniformly empty

`⟦falseProp⟧ = ∅` would say nothing if *every* `∀` denoted `∅`, or if `interp`
were the constant `∅`.  Two instances rule that out, in the shape
`PropSplitAudit` uses: exhibit the other branch rather than argue it exists.

`interp_falseProp_dom` is the first — `⟦Prop⟧ ∅ = UProp`, which contains `∅`.
The second is a **`∀` whose denotation is inhabited**, and it is `falseProp`'s
own consequence: a `∀` over an empty domain has the empty function in it. -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- `Prop` is not a proposition in any context — `prop_forces_false` at an
arbitrary `Γ`.  (The audit states it at `Γ = []`; nothing in its proof uses
that, and the instance below needs `Γ = [falseProp]`.) -/
theorem not_isProp_sort_zero (Γ : List VExpr) (hΓ : OnCtx Γ (envF.IsType nv)) :
    ¬ L.IsProp M Γ (.sort .zero) := by
  have h : envF.HasType nv Γ (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF (by trivial) (by trivial) rfl
  rw [show L.IsProp M Γ (.sort .zero) = L.IsPropAt M.ls Γ (.sort .zero) from rfl,
    L.prop_sound (u := .succ .zero) hΓ (by trivial) h]
  simp [VLevel.eval]

/-- **A `∀` with an inhabited denotation**, so the clause `interp_falseProp`
lands in is not uniformly empty.  `∀ x : (∀ p : Prop, p), Prop` takes the
dependent-product branch over a domain that `interp_falseProp` has just shown to
be `∅`, and the empty function inhabits it. -/
theorem interp_forallE_falseProp_sort_nonempty :
    (∅ : V) ∈ (interp M L [] (.forallE falseProp (.sort .zero))).toFun ∅ := by
  rw [interp_forallE_type M L (not_isProp_sort_zero _ VEnv.onCtx_falseProp),
    mem_mkForallType_iff]
  refine ⟨mem_function_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [interp_falseProp]; simp
  · rw [interp_falseProp]; simp
  · intro v hv; rw [interp_falseProp] at hv; simp at hv

section Consistency

variable (hle : env₀ ≤ envF) (henv : env₀.Ordered) (hS : L.Stable)
  (hC : CoherentOn M L env₀)
variable {R : List VExpr → List VExpr → Prop} (hR : CtxInvariant L R)
variable (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
  env₀.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hle henv hS hC hR hRd in
/-- **The consistency conclusion, assembled.**  A closed inhabitant of
`∀ p : Prop, p` denotes an element of `⟦falseProp⟧ ∅ = ∅`.

The conclusion is `Above M False` because `sound_nil` is `Above`-wrapped; the
equation itself contributes no threshold. -/
theorem falseProp_above_false {e : VExpr} (H : env₀.HasType nv [] e falseProp) :
    Above M False :=
  Above.imp (sound_nil hle henv hS hC hR hRd H) fun h ↦ by
    have := h.2
    rw [interp_falseProp] at this
    simp at this

include hle henv hS hC hR hRd in
/-- The form `leanTTConsistent` consumes, with the threshold exposed: any chain
of `m` inaccessibles refutes a closed proof of `falseProp`. -/
theorem exists_threshold_not_hasType_falseProp
    (h : ∃ e, env₀.HasType nv [] e falseProp) :
    ∃ m : ℕ, IsInaccessibleChain m M.κ → False :=
  let ⟨_, H⟩ := h; falseProp_above_false hle henv hS hC hR hRd H

end Consistency

end

end SetModel

end Lean4Lean
