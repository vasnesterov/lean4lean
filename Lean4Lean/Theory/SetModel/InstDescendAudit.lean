import Lean4Lean.Theory.SetModel.PropUpFits

/-!
# `InstDescendUp` / `PropDescend.sort_inst`: the recorded obstruction, audited

`StableAudit.lean`'s note says the candidate refutation of `PropDescend.sort_inst` is
"blocked on `IsDefEqU.sort_forallE_inv`", and records the witness

```
Γ₀ = [],  A₀ = Prop → Prop,  e₀ = fun p : Prop => p,  k = 0
Γ₁ = [Prop → Prop],  Γ = []
B  = (bvar 0) falseProp falseProp
```

with the claim that `B.inst e₀ 0` types while `B` does not, the latter needing `Prop ≡ Π`.
The note says the witness is **stated but not machine-checked**.

**§1 machine-checks it, and it does not work.**  Both sides need the *same* conversion.  The
inner head is `(bvar 0) falseProp` at `Γ₁` and `e₀ falseProp` at `Γ`, and on both sides its
type is `Prop` — `w_head_type_agree`, and the two terms are literally `inst`-related
(`w_head_inst`).  So the outer application needs a term of type `Prop` to be applied on *both*
sides, and `w_types_of_sortPiConv` derives **both** typings from one `Prop ≡ Π` hypothesis.
Whatever settles `sort_forallE_inv` settles the two sides together; this witness cannot
separate them, so it is not a refutation candidate at all, blocked or otherwise.

That is a correction to a claim in a file this directory owns, and it does *not* close
`sort_inst` — it removes a recorded reason for believing it false.

**§2 removes the level condition from the residual.**  `sort_inst`'s conclusion asks for a sort
that evaluates to `0`; `SortInstDescend0` asks only for *a* sort.  The two are equivalent given
`Ordered` and `PropUniq` — both of which the model side already assumes
(`modelFits_of_propSplitUp_inputs` takes `PropUniq 0` outright).  Bounded both ways:
`sortInstDescend0_of_sort_inst` and `sort_inst_of_sortInstDescend0`.  So **the propositionhood
in `sort_inst` is free and the entire content is typeability descent** — `B` typeable at a sort
over `Γ₁` whenever `B.inst e₀ k` is over `Γ`.

This is a localisation tested against its own target in both directions, as rows 51/77b/82b
require: `→` is projection, `←` is the `PropUniq` bridge, and neither is vacuous
(`sortInstDescend0_nonvacuous`).
-/

namespace Lean4Lean

open SetModel

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-! ## 1. The recorded witness, machine-checked -/

namespace InstDescendAudit

/-- `Prop → Prop`, the witness's `A₀`. -/
def wA₀ : VExpr := .forallE (.sort .zero) (.sort .zero)
/-- `fun p : Prop => p`, the witness's `e₀`. -/
def we₀ : VExpr := .lam (.sort .zero) (.bvar 0)
/-- `Γ₁ = [Prop → Prop]`. -/
def wΓ₁ : List VExpr := [wA₀]
/-- The witness's `B`: two arguments to the context variable. -/
def wB : VExpr := .app (.app (.bvar 0) falseProp) falseProp

theorem w_instN : Ctx.InstN ([] : List VExpr) we₀ wA₀ 0 wΓ₁ [] := .zero

theorem wB_inst : wB.inst we₀ 0 = .app (.app we₀ falseProp) falseProp := rfl

/-- `Prop : Sort 1`. -/
theorem sortZero_hasType {Γ : List VExpr} :
    env.HasType nv Γ (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial (.refl _)

/-- `∀ p : Prop, p` is a type, and its sort evaluates to `0`.

(This and `falseProp_prop` duplicate `Lean4Lean.falseProp_hasType`
(`Theory/Inductive/Companion.lean:403`), which is the same fact with the same proof.  It is not
reachable from `SetModel/PropUpFits.lean`'s import closure, so it is re-proved here rather than
pulling `Theory/Inductive/Companion.lean` into the model side; recorded so the duplication is
deliberate and visible.) -/
theorem falsePropTy {Γ : List VExpr} :
    env.HasType nv Γ falseProp (.sort (.imax (.succ .zero) .zero)) :=
  .forallEDF sortZero_hasType (.bvar .zero)

theorem falseProp_lvl_zero (ls : List ℕ) :
    (VLevel.imax (.succ .zero) .zero).eval ls = 0 := by simp [VLevel.eval, Lean.Nat.imax]

/-- `falseProp : Prop`, in the form the applications below consume. -/
theorem falseProp_prop {Γ : List VExpr} :
    env.HasType nv Γ falseProp (.sort .zero) := by
  have hconv : env.IsDefEq nv Γ (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
      (.sort (.succ (.imax (.succ .zero) .zero))) :=
    VEnv.IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero)
      ⟨trivial, trivial⟩ trivial
      (VLevel.equiv_def.mpr fun ls ↦ by simp [VLevel.eval, Lean.Nat.imax])
  exact .defeqDF hconv falsePropTy

theorem we₀_hasType : env.HasType nv ([] : List VExpr) we₀ wA₀ :=
  .lamDF sortZero_hasType (.bvar .zero)

theorem wbvar_hasType : env.HasType nv wΓ₁ (.bvar 0) wA₀ := .bvar .zero

/-! ### The two inner heads, and their types -/

/-- The inner head at `Γ₁` is the `inst`-preimage of the one at `Γ`, on the nose. -/
theorem w_head_inst : (VExpr.app (.bvar 0) falseProp).inst we₀ 0 = .app we₀ falseProp := rfl

/-- **The unsubstituted inner head types at `Prop`.** -/
theorem w_head_unsubst : env.HasType nv wΓ₁ (.app (.bvar 0) falseProp) (.sort .zero) :=
  .appDF wbvar_hasType falseProp_prop

/-- **The substituted inner head types at `Prop` too — the *same* type.** -/
theorem w_head_subst :
    env.HasType nv ([] : List VExpr) (.app we₀ falseProp) (.sort .zero) :=
  .appDF we₀_hasType falseProp_prop

/-- **The witness is symmetric.**  The outer application of `wB` needs its head to carry a
`Π` type, and on both sides the head's type is `Prop`.  There is no asymmetry for
`sort_forallE_inv` to be blocking. -/
theorem w_head_type_agree :
    env.HasType nv wΓ₁ (.app (.bvar 0) falseProp) (.sort .zero) ∧
      env.HasType nv ([] : List VExpr)
        ((VExpr.app (.bvar 0) falseProp).inst we₀ 0) (.sort .zero) :=
  ⟨w_head_unsubst, w_head_inst ▸ w_head_subst⟩

/-- **One `Prop ≡ Π` hypothesis gives BOTH sides.**  This is the decisive form: the witness's
premise and its would-be-failing conclusion are derivable from the *same* conversion, so no
disposition of `IsDefEqU.sort_forallE_inv` can make the witness refute `sort_inst`. -/
theorem w_types_of_sortPiConv {u : VLevel}
    (hconv : ∀ Γ : List VExpr, env.IsDefEq nv Γ (.sort .zero) wA₀ (.sort u)) :
    env.HasType nv wΓ₁ wB (.sort .zero) ∧
      env.HasType nv ([] : List VExpr) (wB.inst we₀ 0) (.sort .zero) := by
  refine ⟨?_, ?_⟩
  · exact .appDF (.defeqDF (hconv wΓ₁) w_head_unsubst) falseProp_prop
  · rw [wB_inst]
    exact .appDF (.defeqDF (hconv []) w_head_subst) falseProp_prop

/-! ## 2. The level condition in the residual is free

`PropDescend.sort_inst` asks for a sort **that evaluates to `0`**.  `SortInstDescend0` below
asks only for *a* sort.  The two are equivalent given `Ordered` and `PropUniq`, and the model
side assumes both outright (`modelFits_of_propSplitUp_inputs` takes `PropUniq 0`).  So the whole
content of the residual is **typeability descent**, and none of it is about levels. -/

/-- `PropDescend.sort_inst`, standalone. -/
def SortInstDescend (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    {B : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ → u.WF nv →
    env.HasType nv Γ (B.inst e₀ k) (.sort u) → u.eval ls = 0 →
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ₁ B (.sort v) ∧ v.eval ls = 0

/-- The same with the conclusion's level condition **dropped**: bare typeability descent. -/
def SortInstDescend0 (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    {B : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ → u.WF nv →
    env.HasType nv Γ (B.inst e₀ k) (.sort u) → u.eval ls = 0 →
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ₁ B (.sort v)

theorem PropDescend.sortInstDescend (hD : env.PropDescend nv) : SortInstDescend env nv :=
  fun W h₀ hu hB h0 ↦ hD.sort_inst W h₀ hu hB h0

/-- **`→`: projection**, and it is the trivial direction. -/
theorem sortInstDescend0_of_sortInstDescend (hD : SortInstDescend env nv) :
    SortInstDescend0 env nv := fun W h₀ hu hB h0 ↦
  let ⟨v, hv, hBv, _⟩ := hD W h₀ hu hB h0; ⟨v, hv, hBv⟩

/-- **`←`: the `PropUniq` bridge.**  Substituting the descended typing *forward* gives a second
sort for `B.inst e₀ k` at `Γ`, and `PropUniq` — pointwise in `ls`, which is exactly the form
`PropSplitAudit.PropUniq` has — makes the two agree on being `0`. -/
theorem sortInstDescend_of_sortInstDescend0 (henv : env.Ordered) (hU : env.PropUniq nv)
    (hD : SortInstDescend0 env nv) : SortInstDescend env nv := by
  intro Γ₀ e₀ A₀ k Γ₁ Γ B u ls W h₀ hu hB h0
  obtain ⟨v, hv, hBv⟩ := hD W h₀ hu hB h0
  refine ⟨v, hv, hBv, ?_⟩
  have hfwd : env.HasType nv Γ (B.inst e₀ k) ((VExpr.sort v).inst e₀ k) :=
    hBv.instN henv W h₀
  rw [show (VExpr.sort v).inst e₀ k = VExpr.sort v from rfl] at hfwd
  exact (hU hu hv hB hfwd).mp h0

/-- **The equivalence**, at the two inputs the model side already has. -/
theorem sortInstDescend_iff (henv : env.Ordered) (hU : env.PropUniq nv) :
    SortInstDescend env nv ↔ SortInstDescend0 env nv :=
  ⟨sortInstDescend0_of_sortInstDescend, sortInstDescend_of_sortInstDescend0 henv hU⟩

/-! ### Neither side is vacuous

Rows 51/77b/82b: a localisation must be tested against its own target, and a bound must not be
vacuous.  Both premises and conclusion hold at one instance — `k = 0`, so the substitution
genuinely replaces `bvar 0`. -/

/-- `Γ₀ = []`, `A₀ = Prop`, `e₀ = ∀ p : Prop, p`, `k = 0`, `Γ₁ = [Prop]`, `Γ = []`, `B = bvar 0`.
The premise holds (`B.inst e₀ 0 = falseProp`, a type whose sort evaluates to `0`) and so does
the conclusion (`bvar 0 : Prop` at `[Prop]`), so `SortInstDescend0`'s implication is not
vacuous and its conclusion is not unreachable. -/
theorem sortInstDescend0_nonvacuous (ls : List ℕ) :
    Ctx.InstN ([] : List VExpr) falseProp (.sort .zero) 0 [(.sort .zero : VExpr)] [] ∧
      env.HasType nv ([] : List VExpr) ((VExpr.bvar 0).inst falseProp 0)
        (.sort (.imax (.succ .zero) .zero)) ∧
      (VLevel.imax (.succ .zero) .zero).eval ls = 0 ∧
      env.HasType nv [(.sort .zero : VExpr)] (.bvar 0) (.sort .zero) :=
  ⟨.zero, falsePropTy, falseProp_lvl_zero ls, .bvar .zero⟩

/-! ## 3. What the residual actually needs — and it is **shared** with the syntactic side

Having removed the level condition (§2), `SortInstDescend0` is bare typeability descent.  Walk
the cases of `B`:

* `B = .sort _`, `B = .const _ _` — free, the substitution is the identity.
* `B = .bvar i` with `i ≠ k` — free, the lookup transports.
* `B = .bvar k` — **`e₀`'s two types must agree.**  `B.inst e₀ k` is `e₀` (up to a lift), so the
  premise types `e₀` at a sort while the hypothesis types it at `A₀`; the conclusion demands
  `A₀` be a sort.  `sortInstDescend0_bvar_forces_sort` below is that instance, machine-checked.
  This is `UniqueTyping`-strength.
* `B = .forallE _ _`, `B = .app _ _`, `B = .lam _ _` — the premise's derivation need not have the
  matching rule at its root (`defeqDF`, `trans`, `proofIrrel` all apply), so each needs
  **inversion at a sort**, i.e. `Injectivity.lean`'s territory.

**So the model side and the syntactic side do share a residual — but not the one on record.**
`StableAudit.lean` names `IsDefEqU.sort_forallE_inv` (`Prop ≡ Π`); §1 shows the witness offered
for that is symmetric, so that attribution is void.  What `SortInstDescend0` actually needs is
*uniqueness of typing* plus *inversion at a sort* — both downstream of the same injectivity
stream, but different statements from `sort_forallE_inv`.  Stated explicitly rather than
absorbed, as asked.

Note what this does **not** claim: no equivalence between `SortInstDescend0` and `UniqueTyping`
is proved here, only that one instance of the former demands the latter's content.  Any such
equivalence must be tested in both directions first (rows 51/77b/82b). -/

/-- **The `B = .bvar 0` instance of `SortInstDescend0`.**  From `e₀ : A₀` and `e₀ : Sort u` it
demands a sort for `.bvar 0` at `A₀ :: Γ₀`, whose only types are those convertible to `A₀.lift`.
That is uniqueness of typing for `e₀`, and it is reached with `k = 0`, so the substitution is a
genuine one. -/
theorem sortInstDescend0_bvar_forces_sort (hD : SortInstDescend0 env nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {u : VLevel} {ls : List ℕ}
    (h₀ : env.HasType nv Γ₀ e₀ A₀) (hu : u.WF nv)
    (hs : env.HasType nv Γ₀ e₀ (.sort u)) (h0 : u.eval ls = 0) :
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv (A₀ :: Γ₀) (.bvar 0) (.sort v) := by
  have W : Ctx.InstN Γ₀ e₀ A₀ 0 (A₀ :: Γ₀) Γ₀ := .zero
  have he : (VExpr.bvar 0).inst e₀ 0 = e₀ := by simp [VExpr.inst, VExpr.instVar]
  exact hD W h₀ hu (by rw [he]; exact hs) h0

/-- …and the demand really is on `A₀`: `.bvar 0`'s type at `A₀ :: Γ₀` is `A₀.lift`.  So the
conclusion above forces `A₀.lift` to be typeable at a sort, which for a general `A₀` is not
available. -/
theorem bvar0_type_is_lift {Γ₀ : List VExpr} {A₀ : VExpr} :
    env.HasType nv (A₀ :: Γ₀) (.bvar 0) A₀.lift := .bvar .zero

/-! ## 4. Axiom census -/

#print axioms Lean4Lean.VEnv.InstDescendAudit.w_head_type_agree
#print axioms Lean4Lean.VEnv.InstDescendAudit.w_types_of_sortPiConv
#print axioms Lean4Lean.VEnv.InstDescendAudit.sortInstDescend_iff
#print axioms Lean4Lean.VEnv.InstDescendAudit.sortInstDescend_of_sortInstDescend0
#print axioms Lean4Lean.VEnv.InstDescendAudit.sortInstDescend0_nonvacuous
#print axioms Lean4Lean.VEnv.InstDescendAudit.sortInstDescend0_bvar_forces_sort

end InstDescendAudit

end VEnv

end Lean4Lean
