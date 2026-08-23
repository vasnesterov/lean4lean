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

theorem quotRelTy_type {Δ : List VExpr} :
    env.HasType nv (.sort u :: Δ) quotRelTy (.sort (.imax u (.imax u (.succ .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar .zero)
    (.forallEDF (VEnv.IsDefEq.bvar (.succ .zero)) (.sortDF trivial trivial rfl))

theorem quotCod_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (.sort u :: Δ) (.forallE quotRelTy (.sort u))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.succ u))) :=
  .forallEDF quotRelTy_type (.sortDF hu hu rfl)

theorem quotSortU_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ) (.sort u) (.sort (.succ u)) :=
  .sortDF hu hu rfl

end Typing

/-! ### `Quot.mk`'s spine

`Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), Quot α r`.  Unlike `Quot`,
whose spine was `sortDF`/`bvar`/`forallEDF` throughout, the codomain here is a
*constant application*, so it needs `constDF` and two `appDF`s — this is the
cost that a constructor pays once, and it is what makes `Quot.mk` more expensive
than `Quot` rather than the extra λ. -/

/-- The codomain `Quot α r`, over `[α, r-type, Sort u]`. -/
def quotMkCod (u : VLevel) : VExpr :=
  .app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)

example (u : VLevel) : quotMkConst.type.instL [u]
    = .forallE (.sort u) (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u))) := rfl

section MkTyping

variable {env : VEnv} {nv : ℕ} {u : VLevel}

/-- `α`, seen from inside the `r` binder. -/
theorem bvar1_sortU {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ) (.bvar 1) (.sort u) :=
  VEnv.IsDefEq.bvar (.succ .zero)

/-- `α`, seen from inside the `a` binder. -/
theorem bvar2_sortU {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 1 :: quotRelTy :: VExpr.sort u :: Δ) (.bvar 2) (.sort u) :=
  VEnv.IsDefEq.bvar (.succ (.succ .zero))

/-- `Quot` itself, at the level the block is instantiated with. -/
theorem quotConst_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Γ : List VExpr} :
    env.HasType nv Γ (.const ``Quot [u]) (.forallE (.sort u) (.forallE quotRelTy (.sort u))) :=
  VEnv.IsDefEq.constDF hq (by simpa using hu) (by simpa using hu) rfl
    (List.Forall₂.cons rfl .nil)

/-- **The codomain is well-typed.**  `constDF`, then two `appDF`s; the two `inst`
computations come out to the lifted context types on the nose. -/
theorem quotMkCod_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 1 :: quotRelTy :: VExpr.sort u :: Δ) (quotMkCod u) (.sort u) :=
  VEnv.IsDefEq.appDF
    (VEnv.IsDefEq.appDF (quotConst_type hq hu) bvar2_sortU)
    (VEnv.IsDefEq.bvar (.succ .zero))

end MkTyping

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

/-! ### Computing `Quot`'s denotation

`Quot.mk`'s codomain is `Quot α r`, so its obligation needs the *value* of the
function `quotFn` at `α` and then at `r`, not merely its membership.  Two
applications of `mkLam_value`, one per λ. -/

section Values

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

theorem quotFn_value {α : V} (hα : α ∈ U M.κ (u.eval M.ls)) :
    (quotFn M L u) ‘ α = quotFib M L u (snoc ∅ α) := by
  unfold quotFn
  exact mkLam_value (by rw [interp_sort]; exact hα)

theorem quotFib_value {ρ r : V}
    (hr : r ∈ (interp M L [.sort u] quotRelTy).toFun ρ) :
    (quotFib M L u ρ) ‘ r = quotVal (ρ ‘ ((0 : ℕ) : V)) r (u.eval M.ls) := by
  unfold quotFib
  exact mkLam_value hr

end Values

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

/-- **`Quot.mk` is surjective onto the quotient.**  This is the first fact about
`setQuotient` the `Quot` obligations need that is not membership arithmetic, and
`Quot.ind` is what needs it: its conclusion quantifies over an arbitrary element
of the quotient while its hypothesis only speaks about classes of elements.

It holds uniformly across the level split, which was not guaranteed — the
degenerate branch has already produced one non-uniformity in this development.
At `Prop` the quotient is `{•}` when the carrier is inhabited and `∅` otherwise,
so an element of it forces the carrier nonempty and is itself `•`, which is what
`Quot.mk` denotes there. -/
theorem quotVal_surj {α r q : V} {i : ℕ} (hq : q ∈ quotVal α r i) :
    ∃ a ∈ α, q = quotMkVal α r a i := by
  rw [quotVal] at hq
  split at hq
  · rename_i h0
    have hα : α ≠ ∅ := by
      intro hα; rw [if_pos hα] at hq; exact absurd hq (by simp)
    rw [if_neg hα] at hq
    have hne : ∃ a : V, a ∈ α := by
      by_contra hc
      exact hα (subset_empty_iff_eq_empty.mp fun z hz ↦ absurd ⟨z, hz⟩ hc)
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, by rw [mem_singleton_iff.1 hq, quotMkVal, if_pos h0]⟩
  · rename_i h0
    obtain ⟨x, hx, rfl⟩ := mem_setQuotient_iff.1 hq
    exact ⟨x, hx, by rw [quotMkVal, if_neg h0]⟩

/-! ### `Quot.mk`'s witness splits on the level, and this time it is the *shape*

Run the `u = 0` check on `Quot.mk`'s type before building anything:

* `quotMkCod u` = `Quot α r` has sort `u` (`quotMkCod_type`);
* `∀ (a : α), Quot α r` has sort `imax u u`, which evaluates to `u`;
* `∀ (r : α → α → Prop), …` has sort `imax _ (imax u u)`;
* `∀ (α : Sort u), …` has sort `imax (u+1) (…)`.

At `u.eval = 0` every one of those `imax`es collapses to `0`, so **the whole
type of `Quot.mk` is a proposition** and its denotation is a subset of `{•}`.
The witness cannot be a nest of three λs; it has to be `•`.

This is the fourth level-sensitive split the standing check has caught, and it
differs from the previous three in kind: those changed the *value* of a
construction, this one changes the *shape of the witness*.  A nested-λ witness
would have been simply wrong here, not merely harder to prove — and nothing in
the `u ≠ 0` development would have hinted at it. -/

section MkTypingSpine

variable {env : VEnv} {nv : ℕ} {u : VLevel}

theorem quotMkInner_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ) (.forallE (.bvar 1) (quotMkCod u))
      (.sort (.imax u u)) :=
  .forallEDF bvar1_sortU (quotMkCod_type hq hu)

theorem quotMkMid_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.sort u :: Δ)
      (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u)))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.imax u u))) :=
  .forallEDF quotRelTy_type (quotMkInner_type hq hu)

/-- `α → α → Prop` lifted twice, i.e. the type `.bvar 1` has in `Γ₃`.  It is
also `quotRelTy.inst (.bvar 2)`, syntactically — which is what lets the second
`appDF` fire without any transport. -/
theorem quotRelTyLift_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 1 :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero)))
      (.sort (.imax u (.imax u (.succ .zero)))) :=
  .forallEDF bvar2_sortU
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
      (.sortDF trivial trivial rfl))

/-- The type of `Quot`'s own constant, in any context. -/
theorem quotConstTy_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv Δ (.forallE (.sort u) (.forallE quotRelTy (.sort u)))
      (.sort (.imax (.succ u) (.imax (.imax u (.imax u (.succ .zero))) (.succ u)))) :=
  .forallEDF (.sortDF hu hu rfl) (quotCod_type hu)

/-- The type of `Quot` applied to one argument. -/
theorem quotAppTy_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 1 :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero))) (.sort u))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.succ u))) :=
  .forallEDF quotRelTyLift_type (.sortDF hu hu rfl)

/-- **`Quot` applied to any two well-typed arguments.**  Stated generally rather
than once per de Bruijn index pair: the spine needs it at `(2,1)`, `(1,0)`,
`(3,2)` and `(4,3)`, and those differ only in which `Lookup` supplies the
arguments. -/
theorem quotAp_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Γ : List VExpr} {A R : VExpr} (hA : env.HasType nv Γ A (.sort u))
    (hR : env.HasType nv Γ R (quotRelTy.inst A)) :
    env.HasType nv Γ (.app (.app (.const ``Quot [u]) A) R) (.sort u) :=
  VEnv.IsDefEq.appDF (VEnv.IsDefEq.appDF (quotConst_type hq hu) hA) hR

/-- `Quot α r` where `α` and `r` sit at de Bruijn indices 1 and 0 — the shape
`Quot.ind`'s motive needs, one binder shallower than `quotMkCod`. -/
theorem quotIndAp_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ)
      (.app (.app (.const ``Quot [u]) (.bvar 1)) (.bvar 0)) (.sort u) :=
  VEnv.IsDefEq.appDF
    (VEnv.IsDefEq.appDF (quotConst_type hq hu) bvar1_sortU)
    (VEnv.IsDefEq.bvar .zero)

/-! ### `Quot.ind`'s spine

`Quot.ind : ∀ (α : Sort u) (r : α → α → Prop) (β : Quot α r → Prop),
  (∀ a : α, β (Quot.mk α r a)) → ∀ q : Quot α r, β q`

Five binders. Every codomain here is `Sort .zero` *by construction* — `β` lands
in `Prop` — so every `imax` collapses at every `u` and there is no level split;
see the note in the ledger on when to expect one. -/

/-- The motive's type, `Quot α r → Prop`, over `[r, α]`. -/
def quotIndBeta (u : VLevel) : VExpr :=
  .forallE (.app (.app (.const ``Quot [u]) (.bvar 1)) (.bvar 0)) (.sort .zero)

/-- `Quot.mk α r a`, over `[a, β, r, α]`. -/
def quotIndMkAp (u : VLevel) : VExpr :=
  .app (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2)) (.bvar 0)

/-- The inductive hypothesis, `∀ a : α, β (Quot.mk α r a)`, over `[β, r, α]`. -/
def quotIndHyp (u : VLevel) : VExpr :=
  .forallE (.bvar 2) ((VExpr.bvar 1).app (quotIndMkAp u))

/-- The quantified quotient element's type, over `[h, β, r, α]`. -/
def quotIndQ (u : VLevel) : VExpr :=
  .app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2)

example (u : VLevel) : quotIndConst.type.instL [u]
    = .forallE (.sort u) (.forallE quotRelTy (.forallE (quotIndBeta u)
        (.forallE (quotIndHyp u) (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0)))))) := rfl

theorem quotIndBeta_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ) (quotIndBeta u)
      (.sort (.imax u (.succ .zero))) :=
  .forallEDF (quotIndAp_type hq hu) (.sortDF trivial trivial rfl)

/-- `Quot.mk` itself, in any context. -/
theorem quotMkConst_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv Δ (.const ``Quot.mk [u])
      (.forallE (.sort u) (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u)))) :=
  VEnv.IsDefEq.constDF hqm (by simpa using hu) (by simpa using hu) rfl
    (List.Forall₂.cons rfl .nil)

/-- `Quot.mk α r a`, with `α`, `r`, `a` at indices 3, 2, 0. -/
theorem quotIndMkAp_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 2 :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (quotIndMkAp u)
      (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2)) :=
  VEnv.IsDefEq.appDF
    (VEnv.IsDefEq.appDF
      (VEnv.IsDefEq.appDF (quotMkConst_type hqm hu)
        (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero)))))
      (VEnv.IsDefEq.bvar (.succ (.succ .zero))))
    (VEnv.IsDefEq.bvar .zero)

theorem quotIndHyp_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ) (quotIndHyp u)
      (.sort (.imax u .zero)) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ .zero)))
    (VEnv.IsDefEq.appDF (VEnv.IsDefEq.bvar (.succ .zero)) (quotIndMkAp_type hqm hu))

theorem quotIndQ_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (quotIndQ u) (.sort u) :=
  VEnv.IsDefEq.appDF
    (VEnv.IsDefEq.appDF (quotConst_type hq hu) (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero)))))
    (VEnv.IsDefEq.bvar (.succ (.succ .zero)))

/-- The motive's type as it appears at the bottom of `Quot.ind`'s nest, i.e.
`quotIndBeta` lifted three times.  Stated in already-lifted form: `lift` does
not compute through a `def`, so `appDF` cannot see the `forallE` otherwise. -/
theorem quotIndBetaLift_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv
      (quotIndQ u :: quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) (.sort .zero))
      (.sort (.imax u (.succ .zero))) :=
  .forallEDF
    (quotAp_type hq hu (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero)))))
    (.sortDF trivial trivial rfl)

/-- `β q`, the innermost body.  Its type is `Sort .zero` *literally*, which is
what makes the whole spine collapse uniformly. -/
theorem quotIndBody_type {Δ : List VExpr} :
    env.HasType nv
      (quotIndQ u :: quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      ((VExpr.bvar 2).app (.bvar 0)) (.sort .zero) := by
  have hb : env.HasType nv
      (quotIndQ u :: quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.bvar 2)
      (.forallE (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) (.sort .zero)) :=
    VEnv.IsDefEq.bvar (.succ (.succ .zero))
  have hz : env.HasType nv
      (quotIndQ u :: quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.bvar 0) (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) :=
    VEnv.IsDefEq.bvar .zero
  exact VEnv.IsDefEq.appDF hb hz

theorem quotIndT4_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotIndHyp u :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0))) (.sort (.imax u .zero)) :=
  .forallEDF (quotIndQ_type hq hu) quotIndBody_type

theorem quotIndT3_type (hq : env.constants ``Quot = some quotConst)
    (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (quotIndHyp u) (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0))))
      (.sort (.imax (.imax u .zero) (.imax u .zero))) :=
  .forallEDF (quotIndHyp_type hqm hu) (quotIndT4_type hq hu)

theorem quotIndT2_type (hq : env.constants ``Quot = some quotConst)
    (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (quotIndBeta u)
        (.forallE (quotIndHyp u) (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0)))))
      (.sort (.imax (.imax u (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero)))) :=
  .forallEDF (quotIndBeta_type hq hu) (quotIndT3_type hq hqm hu)

theorem quotIndT1_type (hq : env.constants ``Quot = some quotConst)
    (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (VExpr.sort u :: Δ)
      (.forallE quotRelTy (.forallE (quotIndBeta u)
        (.forallE (quotIndHyp u) (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0))))))
      (.sort (.imax (.imax u (.imax u (.succ .zero)))
        (.imax (.imax u (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero))))) :=
  .forallEDF quotRelTy_type (quotIndT2_type hq hqm hu)

end MkTypingSpine

/-! ### Computing `Quot α r` inside `Quot.mk`'s spine -/

section MkCod

variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

/-- **The codomain of `Quot.mk` denotes what `Quot` says it does.**  Two
`interp_app_type` steps — neither partial application is a proof, since the sort
of each is an `imax` whose right argument is `u+1` — then the two `mkLam_value`
steps of `Quot`'s own nest. -/
theorem interp_quotMkCod (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u)
    {α r a : V} (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α)) :
    (interp M L [VExpr.bvar 1, quotRelTy, VExpr.sort u] (quotMkCod u)).toFun
        (snoc (snoc (snoc ∅ α) r) a)
      = quotVal α r (u.eval M.ls) := by
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have hρ₁ : snoc ∅ α ∈ interpCtx M L [VExpr.sort u] :=
    (mem_interpCtx_cons M L).mpr ⟨∅, hnil, α, by rw [interp_sort]; exact hα, rfl⟩
  have hρ₂ : snoc (snoc ∅ α) r ∈ interpCtx M L [quotRelTy, VExpr.sort u] :=
    (mem_interpCtx_cons M L).mpr ⟨_, hρ₁, r, hr, rfl⟩
  -- the two environment reads
  have v1 := snoc_value_at_len M L (v := α) hnil
  rw [List.length_nil] at v1
  have v2 := snoc_value_at_len M L (v := r) hρ₁
  have v3 := snoc_value_of_lt M L (v := r) hρ₁ (j := 0) (by simp)
  have v4 := snoc_value_of_lt M L (v := a) hρ₂ (j := 0) (by simp)
  have v5 := snoc_value_of_lt M L (v := a) hρ₂ (j := 1) (by simp)
  simp only [List.length_cons, List.length_nil] at v2
  -- neither partial application is a proof
  have hnp1 : ¬ L.IsProof M [VExpr.bvar 1, quotRelTy, VExpr.sort u] (.const ``Quot [u]) := by
    rw [isProof_iff hle (quotConst_type hq hu) (quotConstTy_type hu)
      ⟨hu, ⟨hu, hu, trivial⟩, hu⟩]
    exact fun h ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 h))
  have hnp2 : ¬ L.IsProof M [VExpr.bvar 1, quotRelTy, VExpr.sort u]
      (.app (.const ``Quot [u]) (.bvar 2)) := by
    rw [isProof_iff hle (VEnv.IsDefEq.appDF (quotConst_type hq hu) bvar2_sortU)
      (quotAppTy_type hu) ⟨⟨hu, hu, trivial⟩, hu⟩]
    exact fun h ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 h)
  show (interp M L _ (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1))).toFun _ = _
  rw [interp_app_type M L hnp2, interp_app_type M L hnp1, interp_const, interp_bvar,
    interp_bvar, hcnst]
  show ((quotFn M L u) ‘ ((snoc (snoc (snoc ∅ α) r) a) ‘ ((0 : ℕ) : V))) ‘
    ((snoc (snoc (snoc ∅ α) r) a) ‘ ((1 : ℕ) : V)) = _
  rw [v4, v3, v1, v5, v2, quotFn_value hα, quotFib_value hr, v1]

end MkCod

/-! ### `Quot.mk`'s witness

Three nested λs above `Prop`, and `•` at `Prop` — see the note above on why the
level changes the *shape* of the witness and not merely a value. -/

section MkFn

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

/-- Innermost λ: `fun a ↦ Quot.mk α r a`, with `α` and `r` read out of the
environment at indices `0` and `1`. -/
noncomputable def quotMkFibA (M : ModelData V) (L : LevelAssign envF nv) (u : VLevel) : V → V :=
  mkLam (interp M L [quotRelTy, VExpr.sort u] (.bvar 1)).toFun
    (interp M L [quotRelTy, VExpr.sort u] (.bvar 1)).definable
    (fun ρ a ↦ quotMkVal (ρ ‘ ((0 : ℕ) : V)) (ρ ‘ ((1 : ℕ) : V)) a (u.eval M.ls))
    (quotMk_fibre_definable _)

theorem quotMkFibA_definable : ℒₛₑₜ-function₁[V] (quotMkFibA M L u) :=
  mkLam_definable _ _ _ _

/-- Middle λ, over the relation. -/
noncomputable def quotMkFibR (M : ModelData V) (L : LevelAssign envF nv) (u : VLevel) : V → V :=
  mkLam (interp M L [VExpr.sort u] quotRelTy).toFun
    (interp M L [VExpr.sort u] quotRelTy).definable
    (fun ρ r ↦ quotMkFibA M L u (snoc ρ r))
    (by have := quotMkFibA_definable (M := M) (L := L) (u := u); definability)

theorem quotMkFibR_definable : ℒₛₑₜ-function₁[V] (quotMkFibR M L u) :=
  mkLam_definable _ _ _ _

/-- **The denotation of `Quot.mk` at universe `u`.**  At `Prop` the whole type is
a proposition, so the witness is `•`; above it, three λs. -/
noncomputable def quotMkFn (M : ModelData V) (L : LevelAssign envF nv) (u : VLevel) : V :=
  if u.eval M.ls = 0 then (pt : V)
  else mkLam (interp M L [] (.sort u)).toFun (interp M L [] (.sort u)).definable
    (fun ρ α ↦ quotMkFibR M L u (snoc ρ α))
    (by have := quotMkFibR_definable (M := M) (L := L) (u := u); definability) ∅

/-! ### `Quot.mk`'s value chain

Above `Prop`, one `mkLam_value` per λ.  At `Prop` there is nothing to state:
`Quot.mk α r` is proof-sorted there, so `interp_app_of_proof_sorted` gives `•`
without consulting the assignment at all. -/

theorem quotMkFn_value (h0 : u.eval M.ls ≠ 0) {α : V} (hα : α ∈ U M.κ (u.eval M.ls)) :
    (quotMkFn M L u) ‘ α = quotMkFibR M L u (snoc ∅ α) := by
  rw [quotMkFn, if_neg h0]
  exact mkLam_value (by rw [interp_sort]; exact hα)

theorem quotMkFibR_value {ρ r : V}
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun ρ) :
    (quotMkFibR M L u ρ) ‘ r = quotMkFibA M L u (snoc ρ r) := by
  unfold quotMkFibR
  exact mkLam_value hr

theorem quotMkFibA_value {ρ a : V}
    (ha : a ∈ (interp M L [quotRelTy, VExpr.sort u] (.bvar 1)).toFun ρ) :
    (quotMkFibA M L u ρ) ‘ a
      = quotMkVal (ρ ‘ ((0 : ℕ) : V)) (ρ ‘ ((1 : ℕ) : V)) a (u.eval M.ls) := by
  unfold quotMkFibA
  exact mkLam_value ha

end MkFn

section MkMem

variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

/-- The environment reads shared by the two branches. -/
theorem quotMk_env (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α)) :
    (snoc (snoc ∅ α) r) ‘ ((0 : ℕ) : V) = α ∧
    (snoc (snoc ∅ α) r) ‘ ((1 : ℕ) : V) = r ∧
    snoc (snoc ∅ α) r ∈ interpCtx M L [quotRelTy, VExpr.sort u] := by
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have hρ₁ : snoc ∅ α ∈ interpCtx M L [VExpr.sort u] :=
    (mem_interpCtx_cons M L).mpr ⟨∅, hnil, α, by rw [interp_sort]; exact hα, rfl⟩
  have v1 := snoc_value_at_len M L (v := α) hnil
  rw [List.length_nil] at v1
  have v2 := snoc_value_at_len M L (v := r) hρ₁
  simp only [List.length_cons, List.length_nil] at v2
  have v3 := snoc_value_of_lt M L (v := r) hρ₁ (j := 0) (by simp)
  exact ⟨by rw [v3, v1], v2, (mem_interpCtx_cons M L).mpr ⟨_, hρ₁, r, hr, rfl⟩⟩

/-- **The innermost λ.**  Above `Prop`. -/
theorem quotMkFibA_mem (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u) (h0 : u.eval M.ls ≠ 0)
    {α r : V} (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α)) :
    quotMkFibA M L u (snoc (snoc ∅ α) r)
      ∈ (interp M L [quotRelTy, VExpr.sort u] (.forallE (.bvar 1) (quotMkCod u))).toFun
          (snoc (snoc ∅ α) r) := by
  obtain ⟨e0, e1, -⟩ := quotMk_env (M := M) (L := L) hα hr
  unfold quotMkFibA
  refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotMkCod_type hq hu) hu h0 _
    fun a ha ↦ ?_
  rw [interp_bvar] at ha
  rw [interp_quotMkCod hle hq hu hcnst hα hr]
  show quotMkVal ((snoc (snoc ∅ α) r) ‘ ((0 : ℕ) : V))
    ((snoc (snoc ∅ α) r) ‘ ((1 : ℕ) : V)) a (u.eval M.ls) ∈ _
  rw [e0, e1]
  refine quotMkVal_mem _ ?_
  show a ∈ α
  rw [← e0]
  exact ha

/-- **The middle λ.**  Above `Prop`. -/
theorem quotMkFibR_mem (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u) (h0 : u.eval M.ls ≠ 0)
    {α : V} (hα : α ∈ U M.κ (u.eval M.ls)) :
    quotMkFibR M L u (snoc ∅ α)
      ∈ (interp M L [VExpr.sort u]
          (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u)))).toFun (snoc ∅ α) := by
  unfold quotMkFibR
  refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotMkInner_type hq hu) ⟨hu, hu⟩
    (fun h ↦ h0 (imax_eq_zero_iff.1 h)) _ fun r hr ↦ ?_
  exact quotMkFibA_mem hle hq hu hcnst h0 hα hr

set_option maxHeartbeats 1000000 in
/-- **`Quot.mk`'s `const_type` obligation**, in both branches. -/
theorem quotMkFn_mem (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u) :
    quotMkFn M L u ∈ (interp M L [] (quotMkConst.type.instL [u])).toFun ∅ := by
  show quotMkFn M L u ∈ (interp M L []
    (.forallE (.sort u) (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u))))).toFun ∅
  rw [quotMkFn]
  split
  · -- `Prop`: the whole type is a proposition, so the witness is `•`
    rename_i h0
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotMkMid_type hq hu)
      ⟨⟨hu, hu, trivial⟩, hu, hu⟩ (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 h0)) fun α hα ↦ ?_
    rw [interp_sort] at hα
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotMkInner_type hq hu) ⟨hu, hu⟩
      (imax_eq_zero_iff.2 h0) fun r hr ↦ ?_
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotMkCod_type hq hu) hu h0
      fun a ha ↦ ?_
    obtain ⟨e0, -, -⟩ := quotMk_env (M := M) (L := L) hα hr
    rw [interp_bvar] at ha
    rw [interp_quotMkCod hle hq hu hcnst hα hr]
    have hmem := quotMkVal_mem (α := α) (r := r) (a := a) (u.eval M.ls) (by rw [← e0]; exact ha)
    rwa [quotMkVal, if_pos h0] at hmem
  · -- above `Prop`: three λs
    rename_i h0
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotMkMid_type hq hu)
      ⟨⟨hu, hu, trivial⟩, hu, hu⟩
      (fun h ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 h))) _ fun α hα ↦ ?_
    rw [interp_sort] at hα
    exact quotMkFibR_mem hle hq hu hcnst h0 hα

end MkMem

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
    VEnv.LE.rfl (quotSortU_type hu) hu (Nat.succ_ne_zero _) _ fun r _ ↦ ?_
  rw [hval, interp_sort]
  exact quotVal_mem_U hκ hi hα

set_option maxHeartbeats 1000000 in
/-- **`Quot`'s `const_type` obligation.** -/
theorem quotFn_mem (hκ : IsInaccessibleChain n M.κ) (hu : u.WF nv)
    (hi : u.eval M.ls < n) :
    quotFn M L u ∈ (interp M L [] (quotConst.type.instL [u])).toFun ∅ := by
  show quotFn M L u ∈ (interp M L [] (.forallE (.sort u) (.forallE quotRelTy (.sort u)))).toFun ∅
  refine mkLam_mem_interp_forallE' (env₀ := envF) VEnv.LE.rfl (quotCod_type hu)
    ⟨⟨hu, hu, trivial⟩, hu⟩ (fun h ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 h)) _ fun α hα ↦ ?_
  rw [interp_sort] at hα
  exact quotFib_mem hκ hu hi hα

end Interp

end Lean4Lean.SetModel
