import Lean4Lean.Theory.SetModel.Cnst
import Lean4Lean.Theory.SetModel.Definability

/-!
# The interpretation of `Quot`

`Quot` is the only primitive of the prelude whose type mentions no other
constant (see `SetModel/PreludeSpec.lean`), so it is the only one that can be
interpreted before the inductive interpretation exists.

## The level split, and why it is not an artefact

`setQuotient_mem_U` is stated at `U κ (i+1)`, never at `U κ 0`, and **that
restriction is real**: the set-theoretic quotient of a proposition is not a
proposition.  A member of `U κ 0 = UProp = ℘{•}` is a subset of `{•}`; its
quotient by any relation is a set of equivalence *classes*, and the one class of
`{•}` is `{•}` itself, so the quotient is `{{•}}`, which is not a subset of
`{•}`.

Lean agrees, for its own reasons: `Quot r : Sort u` for `α : Sort u`, so at
`u = 0` the quotient is a `Prop`, and every inhabited `Prop` is `True`.  So the
interpretation must split on the level and give the proof-irrelevant answer in
the `Prop` case — `{•}` when the domain is inhabited, `∅` otherwise.

This is the **third** place in the model where a statement that reads uniformly
has needed a level-sensitive case split.  The other two were `forallE`'s
codomain (impredicative `mkForallProp` versus `mkForallType`, split on whether
the codomain is a `Prop`) and `Coherent`'s level bound (`U κ i` is only a real
universe below the chain length).  The pattern is worth naming: **a construction
that is uniform in ZFC is rarely uniform across `Sort 0` versus `Sort (u+1)`,
because `Prop` is proof-irrelevant and impredicative while the higher universes
are neither.**  Expect a fourth.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Definability

Everything the model puts inside a `mkLam` has to be `ℒₛₑₜ`-definable **jointly
in all its arguments**, because the fibre map varies with the domain element.
That is a stronger demand than anything `SetModel/Universe.lean` needed:
`eqvStep_definable` is stated in the operator's last argument only, with the
carrier and relation fixed.

Plain `definability` does not reach any of these.  Two documented workarounds are
both needed, in combination:

* the `mem_ext_iff` route — restate `T = f a b` as a first-order membership
  formula and call `definability` on that (this is how `eqvStep_definable`
  itself is proved);
* passing `sep`'s definability argument explicitly rather than through its
  `autoParam`, since the `autoParam` runs `definability` without the local
  hypotheses that make it succeed.

Without the second, the `sep` inside `quotEqv` fails with
`aesop: internal error during proof reconstruction: goal N was not normalised`
— the same failure recorded as Foundation gap #1. -/

/-- The relation a `Quot` argument denotes, as a set of pairs.

`r` denotes a *curried internal function* `α → α → Prop`, so `(r ‘ x) ‘ y` is a
truth value and the relation it names is the set of pairs at which that value is
inhabited. -/
noncomputable def quotRel (α r : V) : V :=
  {p ∈ (α ×ˢ α : V) ; ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ (pt : V) ∈ (r ‘ x) ‘ y}

theorem quotRel_definable : ℒₛₑₜ-function₂[V] (fun α r ↦ quotRel α r) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T α r ↦ T = quotRel α r) by exact this
  have e : ∀ T α r : V, T = quotRel α r ↔ ∀ p, p ∈ T ↔ p ∈ α ×ˢ α ∧
      (∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ (pt : V) ∈ (r ‘ x) ‘ y) := by
    intro T α r; rw [mem_ext_iff]; simp [quotRel]
  simp only [e]
  definability

/-- One step of the equivalence-closure operator, definable **jointly** in the
carrier, the relation and the stage.  `Universe.lean`'s `eqvStep_definable`
fixes the first two. -/
theorem eqvStep_definable₃ : ℒₛₑₜ-function₃[V] (fun A R S ↦ eqvStep A R S) := by
  suffices ℒₛₑₜ-relation₄[V] (fun T A R S ↦ T = eqvStep A R S) by exact this
  have e : ∀ T A R S : V, T = eqvStep A R S ↔ ∀ p, p ∈ T ↔ p ∈ A ×ˢ A ∧
      ((∃ x ∈ A, p = ⟨x, x⟩ₖ) ∨ p ∈ R ∨
        (∃ x y : V, p = ⟨x, y⟩ₖ ∧ ⟨y, x⟩ₖ ∈ S) ∨
        (∃ x y z : V, p = ⟨x, z⟩ₖ ∧ ⟨x, y⟩ₖ ∈ S ∧ ⟨y, z⟩ₖ ∈ S)) := by
    intro T A R S; rw [mem_ext_iff]; simp [eqvStep]
  simp only [e]
  definability

theorem quotEqv_pred (A R : V) :
    ℒₛₑₜ-predicate[V] (fun p ↦ ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S) := by
  have := eqvStep_definable A R
  definability

/-- The equivalence closure, as the intersection of all closed subrelations —
a **Π₁ form**, deliberately.

`Universe.lean`'s `eqvClosure` is `lfp`, hence `⋂ˢ` of the prefixed points, and
`⋂ˢ`'s membership condition carries a nonemptiness clause; that existential is
what makes `definability` diverge.  Stating the same set by its universal
property removes the existential and the proof goes through.  The two agree —
`A ×ˢ A` is itself closed, so the family is nonempty — but nothing below needs
that, because `setQuotient_mem_U` holds for an arbitrary relation. -/
noncomputable def quotEqv (A R : V) : V :=
  sep (A ×ˢ A) (fun p ↦ ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S) (quotEqv_pred A R)

theorem quotEqv_definable : ℒₛₑₜ-function₂[V] (fun A R ↦ quotEqv A R) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T A R ↦ T = quotEqv A R) by exact this
  have hs := @eqvStep_definable₃ V
  have e : ∀ T A R : V, T = quotEqv A R ↔ ∀ p, p ∈ T ↔ p ∈ A ×ˢ A ∧
      ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S := by
    intro T A R; rw [mem_ext_iff]; simp [quotEqv, mem_sep_iff]
  simp only [e]
  definability

/-- **The denotation of `Quot α r` at universe index `i`.**

At `i = 0` the answer is proof-irrelevant: `Quot r` is a `Prop`, inhabited
exactly when `α` is.  Above that it is the set-theoretic quotient by the
equivalence closure of `r` — `Quot` does not require its relation to be an
equivalence, which is why the closure appears at all. -/
noncomputable def quotVal (α r : V) (i : ℕ) : V :=
  if i = 0 then (if α = ∅ then (∅ : V) else ({pt} : V))
  else setQuotient α (quotEqv α (quotRel α r))

theorem setQuotient_definable₂ : ℒₛₑₜ-function₂[V] (fun A R ↦ setQuotient A R) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T A R ↦ T = setQuotient A R) by exact this
  have e : ∀ T A R : V, T = setQuotient A R ↔ ∀ c, c ∈ T ↔
      ∃ x ∈ A, ∀ z, z ∈ c ↔ (z ∈ A ∧ (⟨x, z⟩ₖ : V) ∈ R) := by
    intro T A R
    rw [mem_ext_iff]
    simp only [mem_setQuotient_iff]
    refine forall_congr' fun c ↦ iff_congr Iff.rfl (exists_congr fun x ↦ and_congr_right fun _ ↦ ?_)
    rw [mem_ext_iff]
    simp [eqvClass]
  simp only [e]
  definability

/-- The `Prop` branch, as a first-order condition: the quotient of a proposition
is inhabited exactly when the proposition is. -/
theorem quotVal_zero_eq (α r : V) :
    quotVal α r 0 = {_z ∈ ({pt} : V) ; α ≠ ∅} := by
  rw [quotVal, if_pos rfl]
  refine subset_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · split at hz
    · exact absurd hz (by simp)
    · exact mem_sep_iff.2 ⟨hz, ‹_›⟩
  · obtain ⟨hz, hne⟩ := mem_sep_iff.1 hz
    rw [if_neg hne]; exact hz

theorem quotVal_definable₁ (α : V) (i : ℕ) : ℒₛₑₜ-function₁[V] (fun r ↦ quotVal α r i) := by
  by_cases h : i = 0
  · subst h
    suffices ℒₛₑₜ-relation[V] (fun T r ↦ T = quotVal α r 0) by exact this
    have e : ∀ T r : V, T = quotVal α r 0 ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ α ≠ ∅) := by
      intro T r; rw [quotVal_zero_eq, mem_ext_iff]; simp [mem_sep_iff]
    simp only [e]
    definability
  · simp only [quotVal, if_neg h]
    have h1 := quotRel_definable (V := V)
    have h2 := quotEqv_definable (V := V)
    have h3 := setQuotient_definable₂ (V := V)
    definability

theorem quotVal_definable (i : ℕ) : ℒₛₑₜ-function₂[V] (fun α r ↦ quotVal α r i) := by
  by_cases h : i = 0
  · subst h
    suffices ℒₛₑₜ-relation₃[V] (fun T α r ↦ T = quotVal α r 0) by exact this
    have e : ∀ T α r : V, T = quotVal α r 0 ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ α ≠ ∅) := by
      intro T α r; rw [quotVal_zero_eq, mem_ext_iff]; simp [mem_sep_iff]
    simp only [e]
    definability
  · simp only [quotVal, if_neg h]
    have h1 := @quotRel_definable V
    have h2 := @quotEqv_definable V
    have h3 := @setQuotient_definable₂ V
    definability

end

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)

include hκ in
/-- **`Quot` stays in its universe.**  Both branches, and the `Prop` branch
needs nothing from the chain — which is the point of splitting. -/
theorem quotVal_mem_U {i : ℕ} (hi : i < n) {α r : V} (hα : α ∈ U κ i) :
    quotVal α r i ∈ U κ i := by
  rw [quotVal]
  split
  · rename_i h0
    subst h0
    rw [U_zero]
    split
    · exact mem_UProp_iff.2 (by simp)
    · exact true_mem_UProp
  · rename_i h0
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact setQuotient_mem_U hκ (Nat.lt_of_succ_lt hi) hα

end

/-! ## `Quot`'s denotation, and its `const_type` obligation

`quotConst.type.instL [u]` is, definitionally,
`∀ (α : Sort u) (r : α → α → Prop), Sort u` — checked by `rfl` below.  The
typing derivations for its pi-spine are built by hand from `sortDF`, `bvar` and
`forallEDF`; no inversion principle is used, so this costs no injectivity. -/

/-- `α → α → Prop`, over the context `[Sort u]`. -/
def quotRelTy : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))

example (u : VLevel) :
    quotConst.type.instL [u] = .forallE (.sort u) (.forallE quotRelTy (.sort u)) := rfl

section Typing

variable {env : VEnv} {nv : ℕ} {u : VLevel}

theorem quotRelTy_type :
    env.HasType nv [.sort u] quotRelTy (.sort (.imax u (.imax u (.succ .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar .zero)
    (.forallEDF (VEnv.IsDefEq.bvar (.succ .zero)) (.sortDF trivial trivial rfl))

theorem quotCod_type (hu : u.WF nv) :
    env.HasType nv [.sort u] (.forallE quotRelTy (.sort u))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.succ u))) :=
  .forallEDF quotRelTy_type (.sortDF hu hu rfl)

theorem quotSortU_type (hu : u.WF nv) :
    env.HasType nv (quotRelTy :: [VExpr.sort u]) (.sort u) (.sort (.succ u)) :=
  .sortDF hu hu rfl

end Typing

section Interp

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

/-- Definability of the inner fibre map.  Written in the **environment-passing
style** — `α` is read back out of `ρ` rather than captured — which is what makes
the nesting compose. -/
theorem quotFib_fibre_definable (M : ModelData V) (u : VLevel) :
    ℒₛₑₜ-function₂[V] (fun ρ r ↦ quotVal (ρ ‘ ((0 : ℕ) : V)) r (u.eval M.ls)) :=
  definable₂_comp₁ (quotVal_definable _) (value_definable _)

/-- The inner λ, as a function of the environment: for the carrier recorded in
`ρ`, the map sending a relation to the quotient. -/
noncomputable def quotFib (M : ModelData V) (L : LevelAssign envF nv) (u : VLevel) : V → V :=
  mkLam (interp M L [.sort u] quotRelTy).toFun (interp M L [.sort u] quotRelTy).definable
    (fun ρ r ↦ quotVal (ρ ‘ ((0 : ℕ) : V)) r (u.eval M.ls)) (quotFib_fibre_definable M u)

theorem quotFib_definable : ℒₛₑₜ-function₁[V] (quotFib M L u) :=
  mkLam_definable _ _ _ _

/-- **The denotation of `Quot` at universe `u`.**  Two nested λs, each one
application of the combinators. -/
noncomputable def quotFn (M : ModelData V) (L : LevelAssign envF nv) (u : VLevel) : V :=
  mkLam (interp M L [] (.sort u)).toFun (interp M L [] (.sort u)).definable
    (fun ρ α ↦ quotFib M L u (snoc ρ α))
    (by have := quotFib_definable (M := M) (L := L) (u := u); definability)
    ∅

/-! ### Towards `Quot.mk`

`Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), Quot α r` — one λ deeper
than `Quot`, and the value layer costs exactly one more of each thing: one
`mem_ext_iff` lemma for the new primitive it uses (`eqvClass`), one for the
value itself, and one `.comp` for the fibre. See the ledger for the measurement. -/

theorem eqvClass_definable₃ : ℒₛₑₜ-function₃[V] (fun A R x ↦ eqvClass A R x) := by
  suffices ℒₛₑₜ-relation₄[V] (fun T A R x ↦ T = eqvClass A R x) by exact this
  have e : ∀ T A R x : V, T = eqvClass A R x ↔ ∀ z, z ∈ T ↔ (z ∈ A ∧ (⟨x, z⟩ₖ : V) ∈ R) := by
    intro T A R x; rw [mem_ext_iff]; simp [eqvClass]
  simp only [e]
  definability

/-- **The denotation of `Quot.mk α r a`.**  At `Prop` it is the proof object;
above that it is the equivalence class. -/
noncomputable def quotMkVal (α r a : V) (i : ℕ) : V :=
  if i = 0 then (pt : V) else eqvClass α (quotEqv α (quotRel α r)) a

theorem quotMkVal_definable (i : ℕ) :
    ℒₛₑₜ-function₃[V] (fun α r a ↦ quotMkVal α r a i) := by
  by_cases h : i = 0
  · subst h; simp only [quotMkVal]; definability
  · simp only [quotMkVal, if_neg h]
    have h1 := quotRel_definable (V := V)
    have h2 := quotEqv_definable (V := V)
    have h3 := eqvClass_definable₃ (V := V)
    definability

/-- The fibre map for `Quot.mk`'s innermost λ, in environment-passing style:
`α` and `r` are read out of `ρ` at indices `0` and `1`. -/
theorem quotMk_fibre_definable (i : ℕ) :
    ℒₛₑₜ-function₂[V] (fun ρ a ↦ quotMkVal (ρ ‘ ((0 : ℕ) : V)) (ρ ‘ ((1 : ℕ) : V)) a i) := by
  have hf := quotMkVal_definable (V := V) i
  have g1 : ℒₛₑₜ-function₂[V] (fun (ρ _ : V) ↦ ρ ‘ ((0 : ℕ) : V)) := by definability
  have g2 : ℒₛₑₜ-function₂[V] (fun (ρ _ : V) ↦ ρ ‘ ((1 : ℕ) : V)) := by definability
  exact hf.comp g1 g2 definable_snd

/-- `Quot.mk`'s value lands in `Quot`'s. -/
theorem quotMkVal_mem (i : ℕ) {α r a : V} (ha : a ∈ α) :
    quotMkVal α r a i ∈ quotVal α r i := by
  rw [quotMkVal, quotVal]
  split
  · rw [if_neg (fun h : α = ∅ ↦ by rw [h] at ha; exact absurd ha (by simp))]
    exact mem_singleton_iff.2 rfl
  · exact mem_setQuotient_iff.2 ⟨a, ha, rfl⟩

/-! ### The membership obligation -/

variable {n : ℕ} {κ : ℕ → V}

set_option maxHeartbeats 1000000 in
theorem quotFib_mem (hκ : IsInaccessibleChain n M.κ) (hu : u.WF nv)
    (hi : u.eval M.ls < n) {α : V} (hα : α ∈ U M.κ (u.eval M.ls)) :
    quotFib M L u (snoc ∅ α)
      ∈ (interp M L [.sort u] (.forallE quotRelTy (.sort u))).toFun (snoc ∅ α) := by
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  -- NB: `hval`'s type is deliberately *not* ascribed.  Writing `((0 : ℕ) : V)`
  -- where the lemma has `((Γ.length : ℕ) : V)` sends `whnf` into a loop: the
  -- two coercion shapes differ and unifying them unfolds the set-theoretic
  -- numerals.  Take the lemma's own form, then rewrite the index at `ℕ`.
  have hval := snoc_value_at_len M L (v := α) hnil
  rw [List.length_nil] at hval
  unfold quotFib
  refine mkLam_mem_interp_forallE' (env₀ := envF) (Γ := [VExpr.sort u]) (A := quotRelTy)
    (B := VExpr.sort u) (v := .succ u) (ρ := snoc ∅ α)
    VEnv.LE.rfl (quotSortU_type hu) (Nat.succ_ne_zero _) _ fun r _ ↦ ?_
  rw [hval, interp_sort]
  exact quotVal_mem_U hκ hi hα

set_option maxHeartbeats 1000000 in
/-- **`Quot`'s `const_type` obligation.** -/
theorem quotFn_mem (hκ : IsInaccessibleChain n M.κ) (hu : u.WF nv)
    (hi : u.eval M.ls < n) :
    quotFn M L u ∈ (interp M L [] (quotConst.type.instL [u])).toFun ∅ := by
  show quotFn M L u ∈ (interp M L [] (.forallE (.sort u) (.forallE quotRelTy (.sort u)))).toFun ∅
  refine mkLam_mem_interp_forallE' (env₀ := envF) VEnv.LE.rfl (quotCod_type hu)
    (fun h ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 h)) _ fun α hα ↦ ?_
  rw [interp_sort] at hα
  exact quotFib_mem hκ hu hi hα

end Interp

end Lean4Lean.SetModel
