import Lean4Lean.Theory.SetModel.Cnst
import Lean4Lean.Theory.SetModel.Definability
import Lean4Lean.Theory.SetModel.PreludeSpec

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

/-! ### The partial applications inside `Quot.ind`'s body

`Quot.ind`'s body mentions `Quot.mk α r a` and `Quot α r`, so computing their
denotations needs to know, for each *partial* application, whether it is
proof-sorted.  `Quot.mk`'s own spine never formed those: `interp_quotMkCod`
only ever took `Quot` apart, never `Quot.mk`.

Two things make this cheap.  First, every lemma below lives over the context
`X :: quotIndBeta u :: quotRelTy :: .sort u :: Δ` with `X` a **variable** — the
last two binders of `Quot.ind` differ only in `X`, and no `Lookup` below index
`3` is used, so one statement serves both.  Second, the types are the `inst`s
that `appDF` produces, written out: `inst` computes on concrete input, so the
explicit form is accepted without transport. -/

variable {X : VExpr}

/-- `α → α → Prop` as it appears with `α` at index 3, i.e. `quotRelTy.inst (.bvar 3)`. -/
theorem quotIndRelLift_type {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero)))
      (.sort (.imax u (.imax u (.succ .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (.sortDF trivial trivial rfl))

/-- `Quot`'s type after one argument, with `α` at index 3. -/
theorem quotIndAppTy_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero))) (.sort u))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.succ u))) :=
  .forallEDF quotIndRelLift_type (.sortDF hu hu rfl)

/-- `Quot α`, with `α` at index 3. -/
theorem quotIndQuotAp1_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.const ``Quot [u]) (.bvar 3))
      (.forallE (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero))) (.sort u)) :=
  VEnv.IsDefEq.appDF (quotConst_type hq hu) (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))

/-- The type of `Quot.mk`'s own constant, as a sort. -/
theorem quotMkConstTy_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv Δ
      (.forallE (.sort u) (.forallE quotRelTy (.forallE (.bvar 1) (quotMkCod u))))
      (.sort (.imax (.succ u)
        (.imax (.imax u (.imax u (.succ .zero))) (.imax u u)))) :=
  .forallEDF (.sortDF hu hu rfl) (quotMkMid_type hq hu)

/-- `Quot.mk α`, with `α` at index 3. -/
theorem quotMkAp1_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.const ``Quot.mk [u]) (.bvar 3))
      (.forallE (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero)))
        (.forallE (.bvar 4) (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 1)))) :=
  VEnv.IsDefEq.appDF (quotMkConst_type hqm hu)
    (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))

theorem quotMkAp1Ty_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero)))
        (.forallE (.bvar 4) (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 1))))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.imax u u))) :=
  .forallEDF quotIndRelLift_type
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (quotAp_type hq hu (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
        (VEnv.IsDefEq.bvar (.succ .zero))))

/-- `Quot.mk α r`, with `α` at index 3 and `r` at index 2. -/
theorem quotMkAp2_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2))
      (.forallE (.bvar 3) (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3))) :=
  VEnv.IsDefEq.appDF (quotMkAp1_type hqm hu) (VEnv.IsDefEq.bvar (.succ (.succ .zero)))

theorem quotMkAp2Ty_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 3) (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)))
      (.sort (.imax u u)) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
    (quotAp_type hq hu (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero)))))

/-- The motive at index 1, i.e. `quotIndBeta` lifted twice — in already-lifted
form, so `appDF` can see the `forallE`. -/
theorem quotIndBetaLift2_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (X :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2)) (.sort .zero))
      (.sort (.imax u (.succ .zero))) :=
  .forallEDF
    (quotAp_type hq hu (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
      (VEnv.IsDefEq.bvar (.succ (.succ .zero))))
    (.sortDF trivial trivial rfl)

/-- `β (Quot.mk α r a)`, the body of the inductive hypothesis.  Its type is
`.sort .zero` literally — the fact the whole spine rests on. -/
theorem quotIndHypBody_type (hqm : env.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 2 :: quotIndBeta u :: quotRelTy :: VExpr.sort u :: Δ)
      ((VExpr.bvar 1).app (quotIndMkAp u)) (.sort .zero) :=
  VEnv.IsDefEq.appDF
    (show env.HasType nv _ (.bvar 1)
        (.forallE (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2)) (.sort .zero)) from
      VEnv.IsDefEq.bvar (.succ .zero))
    (quotIndMkAp_type hqm hu)

end MkTypingSpine

/-! ### `Quot.lift`'s spine

`Quot.lift : ∀ (α : Sort u) (r : α → α → Prop) (β : Sort v) (f : α → β),
  (∀ a b, r a b → f a = f b) → Quot α r → β`

Six binders and **two** universe parameters — the first constant here whose
type is not uniform in a single level.  The new cost is `Eq`: the hypothesis
binder's codomain is an `Eq`-application, so the spine needs `Eq`'s constant
where `Quot.mk`'s and `Quot.ind`'s needed only `Quot`'s.

`eqConst.type` is `∀ (α : Sort u) (a b : α), Prop`, which is
`.forallE (.sort u) quotRelTy` **on the nose** — the same `quotRelTy` the `Quot`
spine already uses.  That is not a coincidence worth much, but it does mean the
`Eq` application costs no new shape lemma. -/

/-- `α → β`, over `[β, r, α]`. -/
def quotLiftFTy : VExpr := .forallE (.bvar 2) (.bvar 1)

/-- `r a b`, over `[b, a, f, β, r, α]`. -/
def quotLiftRab : VExpr := .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)

/-- `@Eq β (f a) (f b)`, over `[hab, b, a, f, β, r, α]`. -/
def quotLiftEqAp (v : VLevel) : VExpr :=
  .app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
    (.app (.bvar 3) (.bvar 1))

/-- The hypothesis `∀ a b, r a b → f a = f b`, over `[f, β, r, α]`.  Its sort is
`imax u (imax u (imax 0 0))`, which evaluates to `0` at every `u` — the
hypothesis is a proposition, as it must be. -/
def quotLiftC (v : VLevel) : VExpr :=
  .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE quotLiftRab (quotLiftEqAp v)))

/-- `Quot α r`, over `[c, f, β, r, α]`. -/
def quotLiftQ (u : VLevel) : VExpr :=
  .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)

example (u v : VLevel) : quotLiftConst.type.instL [u, v]
    = .forallE (.sort u) (.forallE quotRelTy (.forallE (.sort v)
        (.forallE quotLiftFTy (.forallE (quotLiftC v)
          (.forallE (quotLiftQ u) (.bvar 3)))))) := rfl

section LiftTypingSpine

variable {env : VEnv} {nv : ℕ} {u v : VLevel}

/-- `Eq` itself, at the codomain level.  Note the level: `Quot.lift`'s equation
is between elements of `β`, so `Eq` is instantiated at `v`, not at `u`. -/
theorem eqConst_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Γ : List VExpr} :
    env.HasType nv Γ (.const ``Eq [v]) (.forallE (.sort v) quotRelTy) :=
  VEnv.IsDefEq.constDF heq (by simpa using hv) (by simpa using hv) rfl
    (List.Forall₂.cons rfl .nil)

theorem quotLiftFTy_type {Δ : List VExpr} :
    env.HasType nv (VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ) quotLiftFTy
      (.sort (.imax u v)) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ .zero))) (VEnv.IsDefEq.bvar (.succ .zero))

/-- `r a b` is a proposition — the two applications of `r`, with the
intermediate type ascribed so that `inst` computes. -/
theorem quotLiftRab_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ) quotLiftRab (.sort .zero) :=
  VEnv.IsDefEq.appDF
    (show env.HasType nv _ (.app (.bvar 4) (.bvar 1)) (.forallE (.bvar 5) (.sort .zero)) from
      VEnv.IsDefEq.appDF
        (show env.HasType nv _ (.bvar 4)
            (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) from
          VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
        (VEnv.IsDefEq.bvar (.succ .zero)))
    (VEnv.IsDefEq.bvar .zero)

/-- `f a`, where `f` sits at index 3 and the argument is given. -/
theorem quotLiftFAp_type {Δ : List VExpr} {i : ℕ}
    (ha : env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ) (.bvar i) (.bvar 6)) :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.bvar 3) (.bvar i)) (.bvar 4) :=
  VEnv.IsDefEq.appDF
    (show env.HasType nv _ (.bvar 3) (.forallE (.bvar 6) (.bvar 5)) from
      VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
    ha

theorem quotLiftEqAp_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (quotLiftEqAp v) (.sort .zero) :=
  VEnv.IsDefEq.appDF
    (show env.HasType nv _ (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.forallE (.bvar 4) (.sort .zero)) from
      VEnv.IsDefEq.appDF
        (show env.HasType nv _ (.app (.const ``Eq [v]) (.bvar 4))
            (.forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))) from
          VEnv.IsDefEq.appDF (eqConst_type heq hv)
            (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero))))))
        (quotLiftFAp_type (VEnv.IsDefEq.bvar (.succ (.succ .zero)))))
    (quotLiftFAp_type (VEnv.IsDefEq.bvar (.succ .zero)))

theorem quotLiftC_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftFTy :: VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (quotLiftC v) (.sort (.imax u (.imax u (.imax .zero .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (.forallEDF quotLiftRab_type (quotLiftEqAp_type heq hv)))

theorem quotLiftQ_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftC v :: quotLiftFTy :: VExpr.sort v :: quotRelTy ::
        VExpr.sort u :: Δ) (quotLiftQ u) (.sort u) :=
  quotAp_type hq hu (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
    (VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))

theorem quotLiftT6_type {Δ : List VExpr} :
    env.HasType nv (quotLiftQ u :: quotLiftC v :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ) (.bvar 3) (.sort v) :=
  VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero)))

theorem quotLiftT5_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftC v :: quotLiftFTy :: VExpr.sort v :: quotRelTy ::
        VExpr.sort u :: Δ) (.forallE (quotLiftQ u) (.bvar 3)) (.sort (.imax u v)) :=
  .forallEDF (quotLiftQ_type hq hu) quotLiftT6_type

theorem quotLiftT4_type (hq : env.constants ``Quot = some quotConst)
    (heq : env.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftFTy :: VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (quotLiftC v) (.forallE (quotLiftQ u) (.bvar 3)))
      (.sort (.imax (.imax u (.imax u (.imax .zero .zero))) (.imax u v))) :=
  .forallEDF (quotLiftC_type heq hv) (quotLiftT5_type hq hu)

theorem quotLiftT3_type (hq : env.constants ``Quot = some quotConst)
    (heq : env.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE quotLiftFTy (.forallE (quotLiftC v) (.forallE (quotLiftQ u) (.bvar 3))))
      (.sort (.imax (.imax u v)
        (.imax (.imax u (.imax u (.imax .zero .zero))) (.imax u v)))) :=
  .forallEDF quotLiftFTy_type (quotLiftT4_type hq heq hu hv)

theorem quotLiftT2_type (hq : env.constants ``Quot = some quotConst)
    (heq : env.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.sort v)
        (.forallE quotLiftFTy (.forallE (quotLiftC v) (.forallE (quotLiftQ u) (.bvar 3)))))
      (.sort (.imax (.succ v) (.imax (.imax u v)
        (.imax (.imax u (.imax u (.imax .zero .zero))) (.imax u v))))) :=
  .forallEDF (.sortDF hv hv rfl) (quotLiftT3_type hq heq hu hv)

theorem quotLiftT1_type (hq : env.constants ``Quot = some quotConst)
    (heq : env.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.sort u :: Δ)
      (.forallE quotRelTy (.forallE (.sort v)
        (.forallE quotLiftFTy (.forallE (quotLiftC v) (.forallE (quotLiftQ u) (.bvar 3))))))
      (.sort (.imax (.imax u (.imax u (.succ .zero)))
        (.imax (.succ v) (.imax (.imax u v)
          (.imax (.imax u (.imax u (.imax .zero .zero))) (.imax u v)))))) :=
  .forallEDF quotRelTy_type (quotLiftT2_type hq heq hu hv)

/-! #### The partial applications inside `Quot.lift`'s spine

Computing the denotations of `Quot α r`, of `r a b` and of `f a = f b` needs a
`¬IsProof` for every proper prefix of each application, and `isProof_iff` needs
a typing derivation *and* a sort derivation for each.  These are those. -/

theorem quotLiftQuotAp1_type (hq : env.constants ``Quot = some quotConst) (hu : u.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftC v :: quotLiftFTy :: VExpr.sort v :: quotRelTy ::
        VExpr.sort u :: Δ)
      (.app (.const ``Quot [u]) (.bvar 4))
      (.forallE (.forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))) (.sort u)) :=
  VEnv.IsDefEq.appDF (quotConst_type hq hu)
    (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))

theorem quotLiftAppTy_type (hu : u.WF nv) {Δ : List VExpr} :
    env.HasType nv (quotLiftC v :: quotLiftFTy :: VExpr.sort v :: quotRelTy ::
        VExpr.sort u :: Δ)
      (.forallE (.forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))) (.sort u))
      (.sort (.imax (.imax u (.imax u (.succ .zero))) (.succ u))) :=
  .forallEDF
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.sortDF trivial trivial rfl)))
    (.sortDF hu hu rfl)

/-- `r` itself, inside the hypothesis's two binders. -/
theorem quotLiftRTy_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero)))
      (.sort (.imax u (.imax u (.succ .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
      (.sortDF trivial trivial rfl))

theorem quotLiftRAp_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ)
      (.app (.bvar 4) (.bvar 1)) (.forallE (.bvar 5) (.sort .zero)) :=
  VEnv.IsDefEq.appDF
    (show env.HasType nv _ (.bvar 4)
        (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) from
      VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
    (VEnv.IsDefEq.bvar (.succ .zero))

theorem quotLiftRApTy_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 5) (.sort .zero)) (.sort (.imax u (.succ .zero))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
    (.sortDF trivial trivial rfl)

/-- The type of `Eq`'s own constant, as a sort. -/
theorem eqConstTy_type (hv : v.WF nv) {Δ : List VExpr} :
    env.HasType nv Δ (.forallE (.sort v) quotRelTy)
      (.sort (.imax (.succ v) (.imax v (.imax v (.succ .zero))))) :=
  .forallEDF (.sortDF hv hv rfl) quotRelTy_type

theorem quotLiftFLift_type {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 6) (.bvar 5)) (.sort (.imax u v)) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))

theorem quotLiftEqAp1_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.const ``Eq [v]) (.bvar 4))
      (.forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))) :=
  VEnv.IsDefEq.appDF (eqConst_type heq hv)
    (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))

theorem quotLiftEqAp1Ty_type {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero)))
      (.sort (.imax v (.imax v (.succ .zero)))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
    (.forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
      (.sortDF trivial trivial rfl))

theorem quotLiftEqAp2_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
      (.forallE (.bvar 4) (.sort .zero)) :=
  VEnv.IsDefEq.appDF (quotLiftEqAp1_type heq hv)
    (quotLiftFAp_type (VEnv.IsDefEq.bvar (.succ (.succ .zero))))

theorem quotLiftEqAp2Ty_type {Δ : List VExpr} :
    env.HasType nv (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy ::
        VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.forallE (.bvar 4) (.sort .zero)) (.sort (.imax v (.succ .zero))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
    (.sortDF trivial trivial rfl)

/-- The hypothesis's inner two nests, needed to see that each is a `Prop`. -/
theorem quotLiftC2_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v :: quotRelTy ::
        VExpr.sort u :: Δ)
      (.forallE (.bvar 4) (.forallE quotLiftRab (quotLiftEqAp v)))
      (.sort (.imax u (.imax .zero .zero))) :=
  .forallEDF (VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
    (.forallEDF quotLiftRab_type (quotLiftEqAp_type heq hv))

theorem quotLiftC3_type (heq : env.constants ``Eq = some eqConst) (hv : v.WF nv)
    {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 4 :: VExpr.bvar 3 :: quotLiftFTy :: VExpr.sort v ::
        quotRelTy :: VExpr.sort u :: Δ)
      (.forallE quotLiftRab (quotLiftEqAp v)) (.sort (.imax .zero .zero)) :=
  .forallEDF quotLiftRab_type (quotLiftEqAp_type heq hv)

/-- The codomain of `α → β`, seen from inside the `a` binder. -/
theorem quotLiftFCod_type {Δ : List VExpr} :
    env.HasType nv (VExpr.bvar 2 :: VExpr.sort v :: quotRelTy :: VExpr.sort u :: Δ)
      (.bvar 1) (.sort v) :=
  VEnv.IsDefEq.bvar (.succ .zero)

end LiftTypingSpine

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

/-! ### `Quot.ind`

`Quot.ind`'s type is a proposition **at every universe**: its innermost body is
`β q` with `β : Quot α r → Prop`, so the codomain sort is `.sort .zero`
*literally* and every `imax` above it collapses without ever looking at `u`.
So the witness is `•` at all five binders — the level-split check that fired on
`Quot.mk`'s witness shape has nothing to say here.

The content is at the bottom of the nest, and it is exactly `quotVal_surj`: the
last binder ranges over an arbitrary element of the quotient, while the
hypothesis binder only speaks about classes of elements of the carrier. -/

section IndMem

variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u : VLevel}

/-- The environment reads for `Quot.ind`'s spine, down to the motive. -/
theorem quotInd_env {α r β : V} (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α))
    (hβ : β ∈ (interp M L [quotRelTy, VExpr.sort u] (quotIndBeta u)).toFun (snoc (snoc ∅ α) r)) :
    (snoc (snoc (snoc ∅ α) r) β) ‘ ((0 : ℕ) : V) = α ∧
    (snoc (snoc (snoc ∅ α) r) β) ‘ ((1 : ℕ) : V) = r ∧
    (snoc (snoc (snoc ∅ α) r) β) ‘ ((2 : ℕ) : V) = β ∧
    snoc (snoc (snoc ∅ α) r) β ∈ interpCtx M L [quotIndBeta u, quotRelTy, VExpr.sort u] := by
  obtain ⟨e0, e1, hρ₂⟩ := quotMk_env (M := M) (L := L) hα hr
  have w0 := snoc_value_of_lt M L (v := β) hρ₂ (j := 0) (by simp)
  have w1 := snoc_value_of_lt M L (v := β) hρ₂ (j := 1) (by simp)
  have w2 := snoc_value_at_len M L (v := β) hρ₂
  simp only [List.length_cons, List.length_nil] at w2
  exact ⟨by rw [w0, e0], by rw [w1, e1], w2,
    (mem_interpCtx_cons M L).mpr ⟨_, hρ₂, β, hβ, rfl⟩⟩

/-- **`Quot α r` denotes `quotVal`, one binder deeper than in `Quot.mk`'s
spine.**  The same two `interp_app_type` steps as `interp_quotMkCod`, with the
carrier and the relation read at indices `3` and `2` instead of `2` and `1`. -/
theorem interp_quotIndQ (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u)
    {α r β h : V} (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α))
    (hβ : β ∈ (interp M L [quotRelTy, VExpr.sort u] (quotIndBeta u)).toFun (snoc (snoc ∅ α) r)) :
    (interp M L [quotIndHyp u, quotIndBeta u, quotRelTy, VExpr.sort u] (quotIndQ u)).toFun
        (snoc (snoc (snoc (snoc ∅ α) r) β) h)
      = quotVal α r (u.eval M.ls) := by
  obtain ⟨e0, e1, -, hρ₃⟩ := quotInd_env (M := M) (L := L) hα hr hβ
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have v1 := snoc_value_at_len M L (v := α) hnil
  rw [List.length_nil] at v1
  have g0 := snoc_value_of_lt M L (v := h) hρ₃ (j := 0) (by simp)
  have g1 := snoc_value_of_lt M L (v := h) hρ₃ (j := 1) (by simp)
  have hnp1 : ¬ L.IsProof M [quotIndHyp u, quotIndBeta u, quotRelTy, VExpr.sort u]
      (.const ``Quot [u]) := by
    rw [isProof_iff hle (quotConst_type hq hu) (quotConstTy_type hu)
      ⟨hu, ⟨hu, hu, trivial⟩, hu⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))
  have hnp2 : ¬ L.IsProof M [quotIndHyp u, quotIndBeta u, quotRelTy, VExpr.sort u]
      (.app (.const ``Quot [u]) (.bvar 3)) := by
    rw [isProof_iff hle (quotIndQuotAp1_type hq hu) (quotIndAppTy_type hu)
      ⟨⟨hu, hu, trivial⟩, hu⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  show (interp M L _ (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2))).toFun _ = _
  rw [interp_app_type M L hnp2, interp_app_type M L hnp1, interp_const, interp_bvar,
    interp_bvar, hcnst]
  show ((quotFn M L u) ‘ ((snoc (snoc (snoc (snoc ∅ α) r) β) h) ‘ ((0 : ℕ) : V))) ‘
    ((snoc (snoc (snoc (snoc ∅ α) r) β) h) ‘ ((1 : ℕ) : V)) = _
  rw [g0, e0, g1, e1, quotFn_value hα, quotFib_value hr, v1]

/-- **`Quot.mk α r a` denotes `quotMkVal`, inside `Quot.ind`'s context.**

Above `Prop` this is three `interp_app_type` steps and then `Quot.mk`'s own
`mkLam_value` chain.  At `Prop` the *partial* application `Quot.mk α r` is
itself proof-sorted, so `interp_app_of_proof_sorted` returns `•` without ever
consulting `M.cnst` — which is exactly the value `quotMkVal` takes there.  The
`Prop` branch therefore needs neither `hcnstMk` nor `Quot.mk`'s value chain,
which is what keeps the level split out of the membership proof below. -/
theorem interp_quotIndMkAp (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst)
    (hqm : env₀.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    (hcnstMk : M.cnst ``Quot.mk [u] = quotMkFn M L u)
    {α r β a : V} (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α))
    (hβ : β ∈ (interp M L [quotRelTy, VExpr.sort u] (quotIndBeta u)).toFun (snoc (snoc ∅ α) r))
    (ha : a ∈ α) :
    (interp M L [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u] (quotIndMkAp u)).toFun
        (snoc (snoc (snoc (snoc ∅ α) r) β) a)
      = quotMkVal α r a (u.eval M.ls) := by
  obtain ⟨e0, e1, -, hρ₃⟩ := quotInd_env (M := M) (L := L) hα hr hβ
  show (interp M L _
    (.app (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2)) (.bvar 0))).toFun _ = _
  by_cases h0 : u.eval M.ls = 0
  · rw [quotMkVal, if_pos h0]
    exact interp_app_of_proof_sorted hle (quotMkAp2_type hqm hu) (quotMkAp2Ty_type hq hu)
      ⟨hu, hu⟩ (imax_eq_zero_iff.2 h0) _ _
  · have hnp1 : ¬ L.IsProof M [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u]
        (.const ``Quot.mk [u]) := by
      rw [isProof_iff hle (quotMkConst_type hqm hu) (quotMkConstTy_type hq hu)
        ⟨hu, ⟨hu, hu, trivial⟩, hu, hu⟩]
      exact fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz)))
    have hnp2 : ¬ L.IsProof M [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u]
        (.app (.const ``Quot.mk [u]) (.bvar 3)) := by
      rw [isProof_iff hle (quotMkAp1_type hqm hu) (quotMkAp1Ty_type hq hu)
        ⟨⟨hu, hu, trivial⟩, hu, hu⟩]
      exact fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))
    have hnp3 : ¬ L.IsProof M [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u]
        (.app (.app (.const ``Quot.mk [u]) (.bvar 3)) (.bvar 2)) := by
      rw [isProof_iff hle (quotMkAp2_type hqm hu) (quotMkAp2Ty_type hq hu) ⟨hu, hu⟩]
      exact fun hz ↦ h0 (imax_eq_zero_iff.1 hz)
    have ha' : a ∈ (interp M L [quotRelTy, VExpr.sort u] (.bvar 1)).toFun (snoc (snoc ∅ α) r) := by
      rw [interp_bvar]
      show a ∈ (snoc (snoc ∅ α) r) ‘ ((0 : ℕ) : V)
      rw [(quotMk_env (M := M) (L := L) hα hr).1]
      exact ha
    have f0 := snoc_value_of_lt M L (v := a) hρ₃ (j := 0) (by simp)
    have f1 := snoc_value_of_lt M L (v := a) hρ₃ (j := 1) (by simp)
    have f3 := snoc_value_at_len M L (v := a) hρ₃
    simp only [List.length_cons, List.length_nil] at f3
    obtain ⟨q0, q1, -⟩ := quotMk_env (M := M) (L := L) hα hr
    rw [interp_app_type M L hnp3, interp_app_type M L hnp2, interp_app_type M L hnp1,
      interp_const, interp_bvar, interp_bvar, interp_bvar, hcnstMk]
    show (((quotMkFn M L u) ‘ ((snoc (snoc (snoc (snoc ∅ α) r) β) a) ‘ ((0 : ℕ) : V))) ‘
      ((snoc (snoc (snoc (snoc ∅ α) r) β) a) ‘ ((1 : ℕ) : V))) ‘
      ((snoc (snoc (snoc (snoc ∅ α) r) β) a) ‘ ((3 : ℕ) : V)) = _
    rw [f0, e0, f1, e1, f3, quotMkFn_value h0 hα, quotMkFibR_value hr, quotMkFibA_value ha',
      q0, q1]

set_option maxHeartbeats 1000000 in
/-- **`Quot.ind`'s `const_type` obligation.**  Five `pt_mem_interp_forallE_prop`
in a row — no level split, and the same witness `•` at every one of them. -/
theorem quotIndFn_mem (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst)
    (hqm : env₀.constants ``Quot.mk = some quotMkConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u)
    (hcnstMk : M.cnst ``Quot.mk [u] = quotMkFn M L u) :
    (pt : V) ∈ (interp M L [] (quotIndConst.type.instL [u])).toFun ∅ := by
  show (pt : V) ∈ (interp M L []
    (.forallE (.sort u) (.forallE quotRelTy (.forallE (quotIndBeta u)
      (.forallE (quotIndHyp u) (.forallE (quotIndQ u) ((VExpr.bvar 2).app (.bvar 0)))))))).toFun ∅
  refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotIndT1_type hq hqm hu)
    ⟨⟨hu, hu, trivial⟩, ⟨hu, trivial⟩, ⟨hu, trivial⟩, hu, trivial⟩
    (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 rfl))))
    fun α hα ↦ ?_
  rw [interp_sort] at hα
  refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotIndT2_type hq hqm hu)
    ⟨⟨hu, trivial⟩, ⟨hu, trivial⟩, hu, trivial⟩
    (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 rfl))) fun r hr ↦ ?_
  refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotIndT3_type hq hqm hu)
    ⟨⟨hu, trivial⟩, hu, trivial⟩ (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 rfl)) fun β hβ ↦ ?_
  refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotIndT4_type hq hu)
    ⟨hu, trivial⟩ (imax_eq_zero_iff.2 rfl) fun h hh ↦ ?_
  refine pt_mem_interp_forallE_prop (env₀ := env₀) hle quotIndBody_type trivial rfl fun q hq5 ↦ ?_
  -- the quotient element is a class, by surjectivity
  rw [interp_quotIndQ hle hq hu hcnst hα hr hβ] at hq5
  obtain ⟨a, ha, rfl⟩ := quotVal_surj hq5
  -- the hypothesis binder, instantiated at that representative
  obtain ⟨e0, -, e2, hρ₃⟩ := quotInd_env (M := M) (L := L) hα hr hβ
  have hprop : L.IsProp M [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u]
      ((VExpr.bvar 1).app (quotIndMkAp u)) :=
    (isProp_iff hle (quotIndHypBody_type hqm hu) trivial).2 rfl
  obtain ⟨rfl, hstep⟩ := (mem_interp_forallE_prop_iff (M := M) (L := L) hprop).1 hh
  have ha' : a ∈ (interp M L [quotIndBeta u, quotRelTy, VExpr.sort u] (.bvar 2)).toFun
      (snoc (snoc (snoc ∅ α) r) β) := by
    rw [interp_bvar]
    show a ∈ (snoc (snoc (snoc ∅ α) r) β) ‘ ((0 : ℕ) : V)
    rw [e0]; exact ha
  have hbody := hstep a ha'
  have hnpβ2 : ¬ L.IsProof M [VExpr.bvar 2, quotIndBeta u, quotRelTy, VExpr.sort u] (.bvar 1) := by
    rw [isProof_iff hle
      (show env₀.HasType nv _ (.bvar 1)
          (.forallE (.app (.app (.const ``Quot [u]) (.bvar 3)) (.bvar 2)) (.sort .zero)) from
        VEnv.IsDefEq.bvar (.succ .zero))
      (quotIndBetaLift2_type hq hu) ⟨hu, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  rw [interp_app_type M L hnpβ2, interp_bvar,
    interp_quotIndMkAp hle hq hqm hu hcnstMk hα hr hβ ha] at hbody
  replace hbody : pt ∈ ((snoc (snoc (snoc (snoc ∅ α) r) β) a) ‘ ((2 : ℕ) : V)) ‘
      (quotMkVal α r a (u.eval M.ls)) := hbody
  have f2 := snoc_value_of_lt M L (v := a) hρ₃ (j := 2) (by simp)
  rw [f2, e2] at hbody
  -- and the goal is that same membership, two binders lower
  have hnpβ : ¬ L.IsProof M
      [quotIndQ u, quotIndHyp u, quotIndBeta u, quotRelTy, VExpr.sort u] (.bvar 2) := by
    rw [isProof_iff hle
      (show env₀.HasType nv _ (.bvar 2)
          (.forallE (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)) (.sort .zero)) from
        VEnv.IsDefEq.bvar (.succ (.succ .zero)))
      (quotIndBetaLift_type hq hu) ⟨hu, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  have hρ₄ : snoc (snoc (snoc (snoc ∅ α) r) β) pt
      ∈ interpCtx M L [quotIndHyp u, quotIndBeta u, quotRelTy, VExpr.sort u] :=
    (mem_interpCtx_cons M L).mpr ⟨_, hρ₃, pt, hh, rfl⟩
  have k2 := snoc_value_of_lt M L (v := quotMkVal α r a (u.eval M.ls)) hρ₄ (j := 2) (by simp)
  have k4 := snoc_value_at_len M L (v := quotMkVal α r a (u.eval M.ls)) hρ₄
  simp only [List.length_cons, List.length_nil] at k4
  have f2' := snoc_value_of_lt M L (v := (pt : V)) hρ₃ (j := 2) (by simp)
  rw [interp_app_type M L hnpβ, interp_bvar, interp_bvar]
  show pt ∈ ((snoc (snoc (snoc (snoc (snoc ∅ α) r) β) pt)
      (quotMkVal α r a (u.eval M.ls))) ‘ ((2 : ℕ) : V)) ‘
    ((snoc (snoc (snoc (snoc (snoc ∅ α) r) β) pt)
      (quotMkVal α r a (u.eval M.ls))) ‘ ((4 : ℕ) : V))
  rw [k2, f2', e2, k4]
  exact hbody

end IndMem

/-! ## `Quot.lift`'s value layer

`Quot.lift : ∀ (α : Sort u) (r : α → α → Prop) (β : Sort v) (f : α → β),
  (∀ a b, r a b → f a = f b) → Quot α r → β`

Two universe parameters, six binders — and, unlike the three constants above, a
**hypothesis binder whose content the value actually needs**.  Without `c` the
image of a class under `f` need not be a singleton, so the witness would not
land in `β` at all.  This is the first place in the development where a `Prop`
argument is *eliminated* rather than merely carried, and it is why `Quot.lift`
is the first `Quot` operation whose type mentions `Eq` (`SetModel/PreludeSpec`).

Everything in this section is about values; the spine and the `const_type`
obligation are not built here. -/

section Lift

/-! ### Eliminating the equivalence closure

`quotEqv` was defined by its universal property — a `Π₁` form, chosen for
definability — rather than as a least fixed point, and the docstring there
records that nothing needed the two to agree.  Something does now, and what it
needs is exactly the `Π₁` form's *elimination* rule: any closed subrelation
contains the closure.  So the least-fixed-point characterisation is still not
needed, and neither is `eqvClosure`: instantiating at the kernel of `f` is a
one-line argument, where going through `eqvClosure_least` would have required
proving the two definitions equal first. -/

theorem mem_quotEqv_iff {A R p : V} :
    p ∈ quotEqv A R ↔ p ∈ (A ×ˢ A : V) ∧
      ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S := by
  rw [quotEqv]; exact mem_sep_iff

/-- **The elimination rule.**  Every `eqvStep`-closed subrelation of `A ×ˢ A`
contains the closure. -/
theorem quotEqv_subset {A R S : V} (hS : S ∈ (℘ (A ×ˢ A) : V))
    (hclosed : eqvStep A R S ⊆ S) : quotEqv A R ⊆ S :=
  fun _ hp ↦ (mem_quotEqv_iff.1 hp).2 S hS hclosed

/-- **The `Π₁` closure really is an equivalence relation on `A`** — proved
directly, without comparing it to `eqvClosure`.  Each field instantiates the
universal property at an arbitrary closed `S` and then applies the matching
clause of `eqvStep`. -/
theorem isEquivalenceOn_quotEqv (A R : V) : IsEquivalenceOn A (quotEqv A R) where
  subset := fun _ hp ↦ (mem_quotEqv_iff.1 hp).1
  refl x hx :=
    mem_quotEqv_iff.2 ⟨kpair_mem_iff.2 ⟨hx, hx⟩, fun S _ hc ↦
      hc _ (mem_eqvStep_iff.2 ⟨kpair_mem_iff.2 ⟨hx, hx⟩, Or.inl ⟨x, hx, rfl⟩⟩)⟩
  symm x y h := by
    obtain ⟨hxy, hall⟩ := mem_quotEqv_iff.1 h
    obtain ⟨hx, hy⟩ := kpair_mem_iff.1 hxy
    exact mem_quotEqv_iff.2 ⟨kpair_mem_iff.2 ⟨hy, hx⟩, fun S hS hc ↦
      hc _ (mem_eqvStep_iff.2 ⟨kpair_mem_iff.2 ⟨hy, hx⟩,
        Or.inr (Or.inr (Or.inl ⟨y, x, rfl, hall S hS hc⟩))⟩)⟩
  trans x y z h₁ h₂ := by
    obtain ⟨hxy, hall₁⟩ := mem_quotEqv_iff.1 h₁
    obtain ⟨hyz, hall₂⟩ := mem_quotEqv_iff.1 h₂
    obtain ⟨hx, -⟩ := kpair_mem_iff.1 hxy
    obtain ⟨-, hz⟩ := kpair_mem_iff.1 hyz
    exact mem_quotEqv_iff.2 ⟨kpair_mem_iff.2 ⟨hx, hz⟩, fun S hS hc ↦
      hc _ (mem_eqvStep_iff.2 ⟨kpair_mem_iff.2 ⟨hx, hz⟩,
        Or.inr (Or.inr (Or.inr ⟨x, y, z, rfl, hall₁ S hS hc, hall₂ S hS hc⟩))⟩)⟩

/-! ### Respect, and its transfer to the closure -/

/-- `f` identifies `R`-related elements of `α`.  This is what the hypothesis
binder `c` of `Quot.lift` says, once `EqSpec` has been used to read it. -/
def Respects (α f R : V) : Prop :=
  ∀ x ∈ α, ∀ y ∈ α, (⟨x, y⟩ₖ : V) ∈ R → f ‘ x = f ‘ y

theorem respectsSet_pred (α f : V) :
    ℒₛₑₜ-predicate[V] (fun p ↦ ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ f ‘ x = f ‘ y) := by
  definability

/-- The kernel of `f` on `α`: the closed subrelation that carries the
transfer. -/
noncomputable def respectsSet (α f : V) : V :=
  sep (α ×ˢ α) (fun p ↦ ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ f ‘ x = f ‘ y)
    (respectsSet_pred α f)

theorem mem_respectsSet_iff {α f p : V} :
    p ∈ respectsSet α f ↔ p ∈ (α ×ˢ α : V) ∧
      ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ f ‘ x = f ‘ y := by
  rw [respectsSet]; exact mem_sep_iff

/-- **Respect passes to the equivalence closure.**  `Quot` closes its relation
up before quotienting, so the hypothesis `c` — which speaks only about `r` — has
to be stretched over the closure before it can be used. -/
theorem Respects.quotEqv {α f R : V} (h : Respects α f R) :
    Respects α f (SetModel.quotEqv α R) := by
  have hclosed : eqvStep α R (respectsSet α f) ⊆ respectsSet α f := by
    intro p hp
    obtain ⟨hpα, hcase⟩ := mem_eqvStep_iff.1 hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.1 hpα
    refine mem_respectsSet_iff.2 ⟨hpα, a, ha, b, hb, rfl, ?_⟩
    rcases hcase with ⟨z, hz, he⟩ | hR | ⟨z, w, he, hs⟩ | ⟨z, w, t, he, h1, h2⟩
    · obtain ⟨rfl, rfl⟩ := kpair_inj he; rfl
    · exact h a ha b hb hR
    · obtain ⟨rfl, rfl⟩ := kpair_inj he
      obtain ⟨-, x, -, y, -, hkp, heq⟩ := mem_respectsSet_iff.1 hs
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      exact heq.symm
    · obtain ⟨rfl, rfl⟩ := kpair_inj he
      obtain ⟨-, x, -, y, -, hkp, heq⟩ := mem_respectsSet_iff.1 h1
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      obtain ⟨-, x', -, y', -, hkp', heq'⟩ := mem_respectsSet_iff.1 h2
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp'
      exact heq.trans heq'
  intro x hx y hy hxy
  have hsub : respectsSet α f ∈ (℘ (α ×ˢ α) : V) := by
    refine mem_power_iff.2 fun p hp ↦ (mem_respectsSet_iff.1 hp).1
  obtain ⟨-, u, -, v, -, hkp, heq⟩ :=
    mem_respectsSet_iff.1 (quotEqv_subset hsub hclosed _ hxy)
  obtain ⟨rfl, rfl⟩ := kpair_inj hkp
  exact heq

/-! ### The value -/

/-- **The denotation of `Quot.lift α r β f c q`.**

Above a `Prop` carrier, `q` is an equivalence class and `c` forces `f`'s image
on it to be a singleton, which `⋃ˢ` reads out.  At a `Prop` carrier the
quotient is degenerate — `q` is `•`, not a class — but there the carrier is a
subset of `{•}`, so it has at most the one element `•` and the value is
`f ‘ •`.

This is the same split as `quotMkVal`'s, in the same place and for the same
reason, and it is the *only* one `Quot.lift`'s value needs: the split on the
codomain level `v` belongs to the witness, not to the value. -/
noncomputable def quotLiftVal (f q : V) (i : ℕ) : V :=
  if i = 0 then f ‘ (pt : V) else ⋃ˢ (image f q)

theorem quotLiftVal_definable (i : ℕ) :
    ℒₛₑₜ-function₂[V] (fun f q ↦ quotLiftVal f q i) := by
  by_cases h : i = 0
  · subst h; simp only [quotLiftVal]; definability
  · simp only [quotLiftVal, if_neg h]; definability

/-- **The image of a class is a singleton.**  This is where `c` is spent. -/
theorem quotLiftVal_class {α f E a : V} (hfun : IsFunction f)
    (hgraph : ∀ x ∈ α, (⟨x, f ‘ x⟩ₖ : V) ∈ f)
    (hE : IsEquivalenceOn α E) (hresp : Respects α f E) (ha : a ∈ α) :
    ⋃ˢ (image f (eqvClass α E a)) = f ‘ a := by
  have := hfun
  have hself : a ∈ eqvClass α E a := mem_eqvClass_iff.2 ⟨ha, hE.refl a ha⟩
  have himg : image f (eqvClass α E a) = ({f ‘ a} : V) := by
    ext y
    rw [image, mem_range_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨hxy, b, hb, c, hbc⟩ := mem_restrict_iff.1 hx
      obtain ⟨rfl, rfl⟩ := kpair_inj hbc
      obtain ⟨hbα, hab⟩ := mem_eqvClass_iff.1 hb
      rw [← value_eq_of_kpair_mem hxy]
      exact (hresp a ha _ hbα hab).symm
    · rintro rfl
      exact ⟨a, mem_restrict_iff.2 ⟨hgraph a ha, a, hself, f ‘ a, rfl⟩⟩
  rw [himg, sUnion_singleton_eq]

/-- **`Quot.lift`'s ι-rule, at the level of values.**  Both branches, and the
degenerate one is not vacuous: at a `Prop` carrier `a` *is* `•`, so the two
sides agree on the nose rather than by an appeal to the class structure. -/
theorem quotLiftVal_quotMkVal {α r f a : V} {i : ℕ} (hfun : IsFunction f)
    (hgraph : ∀ x ∈ α, (⟨x, f ‘ x⟩ₖ : V) ∈ f)
    (h0 : i = 0 → α ⊆ ({pt} : V))
    (hresp : Respects α f (quotRel α r)) (ha : a ∈ α) :
    quotLiftVal f (quotMkVal α r a i) i = f ‘ a := by
  by_cases hi : i = 0
  · subst hi
    rw [quotLiftVal, if_pos rfl, mem_singleton_iff.1 (h0 rfl a ha)]
  · rw [quotLiftVal, if_neg hi, quotMkVal, if_neg hi]
    exact quotLiftVal_class hfun hgraph (isEquivalenceOn_quotEqv _ _) hresp.quotEqv ha

/-- **The witness lands in the codomain.**  `quotVal_surj` reduces the
arbitrary quotient element to a class of a representative, and the ι-rule then
says the value is one of `f`'s. -/
theorem quotLiftVal_mem {α r β f q : V} {i : ℕ} (hfun : IsFunction f)
    (hgraph : ∀ x ∈ α, (⟨x, f ‘ x⟩ₖ : V) ∈ f)
    (hcod : ∀ x ∈ α, f ‘ x ∈ β) (h0 : i = 0 → α ⊆ ({pt} : V))
    (hresp : Respects α f (quotRel α r)) (hq : q ∈ quotVal α r i) :
    quotLiftVal f q i ∈ β := by
  obtain ⟨a, ha, rfl⟩ := quotVal_surj hq
  rw [quotLiftVal_quotMkVal hfun hgraph h0 hresp ha]
  exact hcod a ha

/-! ### `Quot.lift`'s witness

Five nested λs above `Prop`, and `•` when the *codomain* level is `0`.  Note
which level decides: the whole type is a proposition exactly when `imax u v = 0`,
i.e. when `v = 0`.  The carrier level `u` never makes the witness degenerate —
it only changes the value, through `quotLiftVal`'s own split. -/

section LiftFn

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u v : VLevel}

theorem quotLiftFib_fibre_definable (M : ModelData V) (u : VLevel) :
    ℒₛₑₜ-function₂[V] (fun ρ q ↦ quotLiftVal (ρ ‘ ((3 : ℕ) : V)) q (u.eval M.ls)) :=
  definable₂_comp₁ (quotLiftVal_definable _) (value_definable _)

/-- Innermost λ, over the quotient element; `f` is read out of the environment
at index `3`. -/
noncomputable def quotLiftFibQ (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) :
    V → V :=
  mkLam (interp M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (quotLiftQ u)).toFun
    (interp M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (quotLiftQ u)).definable
    (fun ρ q ↦ quotLiftVal (ρ ‘ ((3 : ℕ) : V)) q (u.eval M.ls))
    (quotLiftFib_fibre_definable M u)

theorem quotLiftFibQ_definable : ℒₛₑₜ-function₁[V] (quotLiftFibQ M L u v) :=
  mkLam_definable _ _ _ _

/-- The λ over the hypothesis.  Its domain is a subset of `{•}`, so this λ is a
one-point function — but it is a genuine λ, not `•`, because its *codomain*
`∀ q, β` is not a proposition. -/
noncomputable def quotLiftFibC (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) :
    V → V :=
  mkLam (interp M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] (quotLiftC v)).toFun
    (interp M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] (quotLiftC v)).definable
    (fun ρ c ↦ quotLiftFibQ M L u v (snoc ρ c))
    (by have := quotLiftFibQ_definable (M := M) (L := L) (u := u) (v := v); definability)

theorem quotLiftFibC_definable : ℒₛₑₜ-function₁[V] (quotLiftFibC M L u v) :=
  mkLam_definable _ _ _ _

noncomputable def quotLiftFibF (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) :
    V → V :=
  mkLam (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] quotLiftFTy).toFun
    (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] quotLiftFTy).definable
    (fun ρ f ↦ quotLiftFibC M L u v (snoc ρ f))
    (by have := quotLiftFibC_definable (M := M) (L := L) (u := u) (v := v); definability)

theorem quotLiftFibF_definable : ℒₛₑₜ-function₁[V] (quotLiftFibF M L u v) :=
  mkLam_definable _ _ _ _

noncomputable def quotLiftFibB (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) :
    V → V :=
  mkLam (interp M L [quotRelTy, VExpr.sort u] (.sort v)).toFun
    (interp M L [quotRelTy, VExpr.sort u] (.sort v)).definable
    (fun ρ β ↦ quotLiftFibF M L u v (snoc ρ β))
    (by have := quotLiftFibF_definable (M := M) (L := L) (u := u) (v := v); definability)

theorem quotLiftFibB_definable : ℒₛₑₜ-function₁[V] (quotLiftFibB M L u v) :=
  mkLam_definable _ _ _ _

noncomputable def quotLiftFibR (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) :
    V → V :=
  mkLam (interp M L [VExpr.sort u] quotRelTy).toFun
    (interp M L [VExpr.sort u] quotRelTy).definable
    (fun ρ r ↦ quotLiftFibB M L u v (snoc ρ r))
    (by have := quotLiftFibB_definable (M := M) (L := L) (u := u) (v := v); definability)

theorem quotLiftFibR_definable : ℒₛₑₜ-function₁[V] (quotLiftFibR M L u v) :=
  mkLam_definable _ _ _ _

/-- **The denotation of `Quot.lift` at `[u, v]`.** -/
noncomputable def quotLiftFn (M : ModelData V) (L : LevelAssign envF nv) (u v : VLevel) : V :=
  if v.eval M.ls = 0 then (pt : V)
  else mkLam (interp M L [] (.sort u)).toFun (interp M L [] (.sort u)).definable
    (fun ρ α ↦ quotLiftFibR M L u v (snoc ρ α))
    (by have := quotLiftFibR_definable (M := M) (L := L) (u := u) (v := v); definability) ∅

/-! ### `Quot.lift`'s value chain -/

theorem quotLiftFn_value (h0 : v.eval M.ls ≠ 0) {α : V} (hα : α ∈ U M.κ (u.eval M.ls)) :
    (quotLiftFn M L u v) ‘ α = quotLiftFibR M L u v (snoc ∅ α) := by
  rw [quotLiftFn, if_neg h0]
  exact mkLam_value (by rw [interp_sort]; exact hα)

theorem quotLiftFibR_value {ρ r : V}
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun ρ) :
    (quotLiftFibR M L u v ρ) ‘ r = quotLiftFibB M L u v (snoc ρ r) := by
  unfold quotLiftFibR; exact mkLam_value hr

theorem quotLiftFibB_value {ρ β : V}
    (hβ : β ∈ (interp M L [quotRelTy, VExpr.sort u] (.sort v)).toFun ρ) :
    (quotLiftFibB M L u v ρ) ‘ β = quotLiftFibF M L u v (snoc ρ β) := by
  unfold quotLiftFibB; exact mkLam_value hβ

theorem quotLiftFibF_value {ρ f : V}
    (hf : f ∈ (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] quotLiftFTy).toFun ρ) :
    (quotLiftFibF M L u v ρ) ‘ f = quotLiftFibC M L u v (snoc ρ f) := by
  unfold quotLiftFibF; exact mkLam_value hf

theorem quotLiftFibC_value {ρ c : V}
    (hc : c ∈ (interp M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (quotLiftC v)).toFun ρ) :
    (quotLiftFibC M L u v ρ) ‘ c = quotLiftFibQ M L u v (snoc ρ c) := by
  unfold quotLiftFibC; exact mkLam_value hc

theorem quotLiftFibQ_value {ρ q : V}
    (hq : q ∈ (interp M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (quotLiftQ u)).toFun ρ) :
    (quotLiftFibQ M L u v ρ) ‘ q = quotLiftVal (ρ ‘ ((3 : ℕ) : V)) q (u.eval M.ls) := by
  unfold quotLiftFibQ; exact mkLam_value hq

end LiftFn

/-! ### Reading `Quot.lift`'s binders -/

section LiftMem

variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv} {u v : VLevel}

/-- Reading a longer valuation below the new binder. -/
theorem snoc_read {Γ : List VExpr} {ρ w : V} (hρ : ρ ∈ interpCtx M L Γ) {j : ℕ}
    (hj : j < Γ.length) {x : V} (h : ρ ‘ ((j : ℕ) : V) = x) :
    (snoc ρ w) ‘ ((j : ℕ) : V) = x := (snoc_value_of_lt M L hρ hj).trans h

/-- Reading a longer valuation at the new binder. -/
theorem snoc_top {Γ : List VExpr} {ρ w : V} (hρ : ρ ∈ interpCtx M L Γ) {j : ℕ}
    (hj : Γ.length = j) : (snoc ρ w) ‘ ((j : ℕ) : V) = w := by
  subst hj; exact snoc_value_at_len M L hρ

/-- **`Quot α r`, at `Quot.lift`'s depth.**  Stated from the two environment
reads rather than from a particular valuation, so the same lemma serves the
witness and the defeq. -/
theorem interp_quotLiftQ (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst) (hu : u.WF nv)
    (hcnst : M.cnst ``Quot [u] = quotFn M L u) {ρ α r : V}
    (e0 : ρ ‘ ((0 : ℕ) : V) = α) (e1 : ρ ‘ ((1 : ℕ) : V) = r)
    (hα : α ∈ U M.κ (u.eval M.ls))
    (hr : r ∈ (interp M L [VExpr.sort u] quotRelTy).toFun (snoc ∅ α)) :
    (interp M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
        (quotLiftQ u)).toFun ρ = quotVal α r (u.eval M.ls) := by
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have v1 := snoc_value_at_len M L (v := α) hnil
  rw [List.length_nil] at v1
  have hnp1 : ¬ L.IsProof M [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (.const ``Quot [u]) := by
    rw [isProof_iff hle (quotConst_type hq hu) (quotConstTy_type hu)
      ⟨hu, ⟨hu, hu, trivial⟩, hu⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))
  have hnp2 : ¬ L.IsProof M [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (.app (.const ``Quot [u]) (.bvar 4)) := by
    rw [isProof_iff hle (quotLiftQuotAp1_type hq hu) (quotLiftAppTy_type hu)
      ⟨⟨hu, hu, trivial⟩, hu⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  show (interp M L _ (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3))).toFun _ = _
  rw [interp_app_type M L hnp2, interp_app_type M L hnp1, interp_const, interp_bvar,
    interp_bvar, hcnst]
  show ((quotFn M L u) ‘ (ρ ‘ ((0 : ℕ) : V))) ‘ (ρ ‘ ((1 : ℕ) : V)) = _
  rw [e0, e1, quotFn_value hα, quotFib_value hr, v1]

/-- `r a b` denotes `(r ‘ a) ‘ b`. -/
theorem interp_quotLiftRab (hle : env₀ ≤ envF) (hu : u.WF nv) {ρ r a b : V}
    (e1 : ρ ‘ ((1 : ℕ) : V) = r) (e4 : ρ ‘ ((4 : ℕ) : V) = a) (e5 : ρ ‘ ((5 : ℕ) : V) = b) :
    (interp M L [VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy, VExpr.sort v, quotRelTy,
        VExpr.sort u] quotLiftRab).toFun ρ = (r ‘ a) ‘ b := by
  have hnp1 : ¬ L.IsProof M [VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy, VExpr.sort v,
      quotRelTy, VExpr.sort u] (.bvar 4) := by
    rw [isProof_iff hle
      (show env₀.HasType nv _ (.bvar 4)
          (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) from
        VEnv.IsDefEq.bvar (.succ (.succ (.succ (.succ .zero)))))
      quotLiftRTy_type ⟨hu, hu, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))
  have hnp2 : ¬ L.IsProof M [VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy, VExpr.sort v,
      quotRelTy, VExpr.sort u] (.app (.bvar 4) (.bvar 1)) := by
    rw [isProof_iff hle quotLiftRAp_type quotLiftRApTy_type ⟨hu, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  show (interp M L _ (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))).toFun _ = _
  rw [interp_app_type M L hnp2, interp_app_type M L hnp1]
  simp only [interp_bvar]
  show ((ρ ‘ ((1 : ℕ) : V)) ‘ (ρ ‘ ((4 : ℕ) : V))) ‘ (ρ ‘ ((5 : ℕ) : V)) = _
  rw [e1, e4, e5]

/-- `f a = f b` denotes `Eq`'s value at `β` on the two images.  Needs `v ≠ 0`:
at a `Prop` codomain `f` is itself a proof and `f a` denotes `•`. -/
theorem interp_quotLiftEqAp (hle : env₀ ≤ envF)
    (heq : env₀.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    (h0 : v.eval M.ls ≠ 0) {ρ β f a b : V}
    (e2 : ρ ‘ ((2 : ℕ) : V) = β) (e3 : ρ ‘ ((3 : ℕ) : V) = f)
    (e4 : ρ ‘ ((4 : ℕ) : V) = a) (e5 : ρ ‘ ((5 : ℕ) : V) = b) :
    (interp M L [quotLiftRab, VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy, VExpr.sort v,
        quotRelTy, VExpr.sort u] (quotLiftEqAp v)).toFun ρ
      = (((M.cnst ``Eq [v]) ‘ β) ‘ (f ‘ a)) ‘ (f ‘ b) := by
  have hnp1 : ¬ L.IsProof M [quotLiftRab, VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy,
      VExpr.sort v, quotRelTy, VExpr.sort u] (.const ``Eq [v]) := by
    rw [isProof_iff hle (eqConst_type heq hv) (eqConstTy_type hv) ⟨hv, hv, hv, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _
      (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz)))
  have hnp2 : ¬ L.IsProof M [quotLiftRab, VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy,
      VExpr.sort v, quotRelTy, VExpr.sort u] (.app (.const ``Eq [v]) (.bvar 4)) := by
    rw [isProof_iff hle (quotLiftEqAp1_type heq hv) quotLiftEqAp1Ty_type ⟨hv, hv, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))
  have hnp3 : ¬ L.IsProof M [quotLiftRab, VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy,
      VExpr.sort v, quotRelTy, VExpr.sort u]
      (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2))) := by
    rw [isProof_iff hle (quotLiftEqAp2_type heq hv) quotLiftEqAp2Ty_type ⟨hv, trivial⟩]
    exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)
  have hnpf : ¬ L.IsProof M [quotLiftRab, VExpr.bvar 4, VExpr.bvar 3, quotLiftFTy,
      VExpr.sort v, quotRelTy, VExpr.sort u] (.bvar 3) := by
    rw [isProof_iff hle
      (show env₀.HasType nv _ (.bvar 3) (.forallE (.bvar 6) (.bvar 5)) from
        VEnv.IsDefEq.bvar (.succ (.succ (.succ .zero))))
      quotLiftFLift_type ⟨hu, hv⟩]
    exact fun hz ↦ h0 (imax_eq_zero_iff.1 hz)
  show (interp M L _ (.app (.app (.app (.const ``Eq [v]) (.bvar 4))
    (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1)))).toFun _ = _
  rw [interp_app_type M L hnp3, interp_app_type M L hnp2, interp_app_type M L hnp1]
  simp only [interp_app_type M L hnpf, interp_const, interp_bvar]
  show (((M.cnst ``Eq [v]) ‘ (ρ ‘ ((2 : ℕ) : V))) ‘
      ((ρ ‘ ((3 : ℕ) : V)) ‘ (ρ ‘ ((4 : ℕ) : V)))) ‘
    ((ρ ‘ ((3 : ℕ) : V)) ‘ (ρ ‘ ((5 : ℕ) : V))) = _
  rw [e2, e3, e4, e5]

/-- **What the `f` binder gives, above a `Prop` codomain.**  There the
denotation of `α → β` is a genuine set function, and its three consequences are
exactly `quotLiftVal_mem`'s hypotheses. -/
theorem quotLift_f_props (hle : env₀ ≤ envF) (hv : v.WF nv) (h0 : v.eval M.ls ≠ 0)
    {ρ α β f : V} (hρ : ρ ∈ interpCtx M L [VExpr.sort v, quotRelTy, VExpr.sort u])
    (e0 : ρ ‘ ((0 : ℕ) : V) = α) (e2 : ρ ‘ ((2 : ℕ) : V) = β)
    (hf : f ∈ (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] quotLiftFTy).toFun ρ) :
    IsFunction f ∧ (∀ x ∈ α, (⟨x, f ‘ x⟩ₖ : V) ∈ f) ∧ (∀ x ∈ α, f ‘ x ∈ β) := by
  have hnp : ¬ L.IsProp M (VExpr.bvar 2 :: [VExpr.sort v, quotRelTy, VExpr.sort u])
      (.bvar 1) := by
    rw [isProp_iff hle quotLiftFCod_type hv]; exact h0
  replace hf : f ∈ (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u]
      (VExpr.forallE (.bvar 2) (.bvar 1))).toFun ρ := hf
  rw [interp_forallE_type M L hnp, mem_mkForallType_iff] at hf
  obtain ⟨hfn, hval⟩ := hf
  have hdom : (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] (.bvar 2)).toFun ρ = α := by
    rw [interp_bvar]; exact e0
  have hcodv : ∀ w : V, (interp M L (VExpr.bvar 2 :: [VExpr.sort v, quotRelTy, VExpr.sort u])
      (.bvar 1)).toFun (snoc ρ w) = β := by
    intro w; rw [interp_bvar]; exact snoc_read (M := M) (L := L) hρ (by simp) e2
  rw [hdom] at hfn hval
  have hfun : IsFunction f := IsFunction.of_mem hfn
  have hgraph : ∀ x ∈ α, (⟨x, f ‘ x⟩ₖ : V) ∈ f := by
    intro x hx
    obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hfn).2 x hx
    rw [value_eq_of_kpair_mem hy]; exact hy
  refine ⟨hfun, hgraph, fun x hx ↦ ?_⟩
  have := hval x hx (f ‘ x) (hgraph x hx)
  rwa [hcodv] at this

/-- **Reading the hypothesis binder.**  Three `Prop`-codomain eliminations and
then `EqSpec`.  This is the only place in the whole `Quot` block where a `Prop`
argument is *eliminated* rather than carried, and the only place where `Eq`'s
denotation is consumed — which is why `Quot.lift` is the first of the four whose
type mentions a second constant. -/
theorem quotLift_respects (hle : env₀ ≤ envF)
    (heq : env₀.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    (h0 : v.eval M.ls ≠ 0) (hEq : EqSpec M v) {ρ α r β f c : V}
    (hρ : ρ ∈ interpCtx M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u])
    (e0 : ρ ‘ ((0 : ℕ) : V) = α) (e1 : ρ ‘ ((1 : ℕ) : V) = r)
    (e2 : ρ ‘ ((2 : ℕ) : V) = β) (e3 : ρ ‘ ((3 : ℕ) : V) = f)
    (hβ : β ∈ U M.κ (v.eval M.ls)) (hcod : ∀ x ∈ α, f ‘ x ∈ β)
    (hc : c ∈ (interp M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (quotLiftC v)).toFun ρ) :
    Respects α f (quotRel α r) := by
  intro x hx y hy hxy
  -- what membership in `quotRel` says
  simp only [quotRel, mem_sep_iff] at hxy
  obtain ⟨-, x', -, y', -, hkp, hrxy⟩ := hxy
  obtain ⟨rfl, rfl⟩ := kpair_inj hkp
  -- the outermost binder of the hypothesis
  have hp1 : L.IsProp M (VExpr.bvar 3 :: [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u])
      (.forallE (.bvar 4) (.forallE quotLiftRab (quotLiftEqAp v))) :=
    (isProp_iff hle (quotLiftC2_type heq hv) ⟨hu, trivial, trivial⟩).2
      (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 rfl))
  obtain ⟨rfl, hstep1⟩ := (mem_interp_forallE_prop_iff (M := M) (L := L) hp1).1 hc
  have hxdom : x ∈ (interp M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]
      (.bvar 3)).toFun ρ := by
    rw [interp_bvar]
    show x ∈ ρ ‘ ((0 : ℕ) : V)
    rw [e0]; exact hx
  have hρ₅ : snoc ρ x ∈ interpCtx M L
      (VExpr.bvar 3 :: [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]) :=
    (mem_interpCtx_cons M L).mpr ⟨_, hρ, x, hxdom, rfl⟩
  -- the second
  have hp2 : L.IsProp M (VExpr.bvar 4 :: VExpr.bvar 3 ::
      [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u])
      (.forallE quotLiftRab (quotLiftEqAp v)) :=
    (isProp_iff hle (quotLiftC3_type heq hv) ⟨trivial, trivial⟩).2 (imax_eq_zero_iff.2 rfl)
  obtain ⟨-, hstep2⟩ :=
    (mem_interp_forallE_prop_iff (M := M) (L := L) hp2).1 (hstep1 x hxdom)
  have hydom : y ∈ (interp M L (VExpr.bvar 3 ::
      [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]) (.bvar 4)).toFun (snoc ρ x) := by
    rw [interp_bvar]
    show y ∈ (snoc ρ x) ‘ ((0 : ℕ) : V)
    rw [snoc_read (M := M) (L := L) hρ (by simp) e0]; exact hy
  have hρ₆ : snoc (snoc ρ x) y ∈ interpCtx M L (VExpr.bvar 4 :: VExpr.bvar 3 ::
      [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]) :=
    (mem_interpCtx_cons M L).mpr ⟨_, hρ₅, y, hydom, rfl⟩
  -- the environment reads at the two extra binders
  have g1 : (snoc (snoc ρ x) y) ‘ ((1 : ℕ) : V) = r :=
    snoc_read (M := M) (L := L) hρ₅ (by simp) (snoc_read (M := M) (L := L) hρ (by simp) e1)
  have g2 : (snoc (snoc ρ x) y) ‘ ((2 : ℕ) : V) = β :=
    snoc_read (M := M) (L := L) hρ₅ (by simp) (snoc_read (M := M) (L := L) hρ (by simp) e2)
  have g3 : (snoc (snoc ρ x) y) ‘ ((3 : ℕ) : V) = f :=
    snoc_read (M := M) (L := L) hρ₅ (by simp) (snoc_read (M := M) (L := L) hρ (by simp) e3)
  have g4 : (snoc (snoc ρ x) y) ‘ ((4 : ℕ) : V) = x :=
    snoc_read (M := M) (L := L) hρ₅ (by simp) (snoc_top (M := M) (L := L) hρ (by simp))
  have g5 : (snoc (snoc ρ x) y) ‘ ((5 : ℕ) : V) = y :=
    snoc_top (M := M) (L := L) hρ₅ (by simp)
  -- the third, and the relation's denotation
  have hp3 : L.IsProp M (quotLiftRab :: VExpr.bvar 4 :: VExpr.bvar 3 ::
      [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]) (quotLiftEqAp v) :=
    (isProp_iff hle (quotLiftEqAp_type heq hv) trivial).2 rfl
  have hrel : (pt : V) ∈ (interp M L (VExpr.bvar 4 :: VExpr.bvar 3 ::
      [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u]) quotLiftRab).toFun
        (snoc (snoc ρ x) y) := by
    rw [interp_quotLiftRab (env₀ := env₀) hle hu g1 g4 g5]; exact hrxy
  obtain ⟨-, hstep3⟩ :=
    (mem_interp_forallE_prop_iff (M := M) (L := L) hp3).1 (hstep2 y hydom)
  have h3 := hstep3 pt hrel
  rw [interp_quotLiftEqAp (env₀ := env₀) hle heq hu hv h0
    (snoc_read (M := M) (L := L) hρ₆ (by simp) g2)
    (snoc_read (M := M) (L := L) hρ₆ (by simp) g3)
    (snoc_read (M := M) (L := L) hρ₆ (by simp) g4)
    (snoc_read (M := M) (L := L) hρ₆ (by simp) g5),
    hEq β hβ (f ‘ x) (hcod x hx) (f ‘ y) (hcod y hy)] at h3
  by_contra hne
  rw [if_neg hne] at h3
  exact absurd h3 (by simp)

set_option maxHeartbeats 2000000 in
/-- **`Quot.lift`'s `const_type` obligation**, in both branches.

Which level decides the branch is worth noticing: the whole type is a
proposition exactly when `imax u v = 0`, i.e. when the *codomain* level `v` is
`0`.  The carrier level `u` never degenerates the witness — it only changes the
value, inside `quotLiftVal`. -/
theorem quotLiftFn_mem (hle : env₀ ≤ envF)
    (hq : env₀.constants ``Quot = some quotConst)
    (heq : env₀.constants ``Eq = some eqConst) (hu : u.WF nv) (hv : v.WF nv)
    (hEq : EqSpec M v) (hcnst : M.cnst ``Quot [u] = quotFn M L u) :
    quotLiftFn M L u v ∈ (interp M L [] (quotLiftConst.type.instL [u, v])).toFun ∅ := by
  show quotLiftFn M L u v ∈ (interp M L []
    (.forallE (.sort u) (.forallE quotRelTy (.forallE (.sort v)
      (.forallE quotLiftFTy (.forallE (quotLiftC v)
        (.forallE (quotLiftQ u) (.bvar 3)))))))).toFun ∅
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  rw [quotLiftFn]
  split
  · -- `Prop` codomain: the whole type is a proposition, so the witness is `•`
    rename_i h0
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotLiftT1_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2
        (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 h0))))) fun α hα ↦ ?_
    rw [interp_sort] at hα
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotLiftT2_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2
        (imax_eq_zero_iff.2 h0)))) fun r hr ↦ ?_
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotLiftT3_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 h0))) fun β hβ ↦ ?_
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotLiftT4_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (imax_eq_zero_iff.2 (imax_eq_zero_iff.2 h0)) fun f hf ↦ ?_
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle (quotLiftT5_type hq hu)
      (by simp [VLevel.WF, hu, hv]) (imax_eq_zero_iff.2 h0) fun c hc ↦ ?_
    refine pt_mem_interp_forallE_prop (env₀ := env₀) hle quotLiftT6_type hv h0 fun q hq5 ↦ ?_
    -- the context, and its reads
    have hw₁ : snoc ∅ α ∈ interpCtx M L [VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨∅, hnil, α, by rw [interp_sort]; exact hα, rfl⟩
    have hw₂ : snoc (snoc ∅ α) r ∈ interpCtx M L [quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₁, r, hr, rfl⟩
    have hw₃ : snoc (snoc (snoc ∅ α) r) β ∈
        interpCtx M L [VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₂, β, hβ, rfl⟩
    have hw₄ : snoc (snoc (snoc (snoc ∅ α) r) β) f ∈
        interpCtx M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₃, f, hf, rfl⟩
    have hw₅ : snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c ∈
        interpCtx M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₄, c, hc, rfl⟩
    have b0 : (snoc ∅ α) ‘ ((0 : ℕ) : V) = α := snoc_top (M := M) (L := L) hnil (by simp)
    have c0 : (snoc (snoc ∅ α) r) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₁ (by simp) b0
    have c1 : (snoc (snoc ∅ α) r) ‘ ((1 : ℕ) : V) = r :=
      snoc_top (M := M) (L := L) hw₁ (by simp)
    have d0 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₂ (by simp) c0
    have d1 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₂ (by simp) c1
    have d2 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((2 : ℕ) : V) = β :=
      snoc_top (M := M) (L := L) hw₂ (by simp)
    have e0' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₃ (by simp) d0
    have e1' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₃ (by simp) d1
    have f0 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e0'
    have f1 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e1'
    -- the quotient element supplies a representative
    rw [interp_quotLiftQ (env₀ := env₀) hle hq hu hcnst f0 f1 hα hr] at hq5
    obtain ⟨a, ha, -⟩ := quotVal_surj hq5
    -- and the `f` binder, being propositional, already asserts `• ∈ β`
    have hprop : L.IsProp M (VExpr.bvar 2 :: [VExpr.sort v, quotRelTy, VExpr.sort u])
        (.bvar 1) := (isProp_iff hle quotLiftFCod_type hv).2 h0
    replace hf : f ∈ (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u]
        (VExpr.forallE (.bvar 2) (.bvar 1))).toFun (snoc (snoc (snoc ∅ α) r) β) := hf
    obtain ⟨rfl, hstep⟩ := (mem_interp_forallE_prop_iff (M := M) (L := L) hprop).1 hf
    have hadom : a ∈ (interp M L [VExpr.sort v, quotRelTy, VExpr.sort u] (.bvar 2)).toFun
        (snoc (snoc (snoc ∅ α) r) β) := by
      rw [interp_bvar]; show a ∈ (snoc (snoc (snoc ∅ α) r) β) ‘ ((0 : ℕ) : V)
      rw [d0]; exact ha
    have hβpt := hstep a hadom
    rw [interp_bvar] at hβpt
    replace hβpt : (pt : V) ∈ (snoc (snoc (snoc (snoc ∅ α) r) β) a) ‘ ((2 : ℕ) : V) := hβpt
    rw [snoc_read (M := M) (L := L) hw₃ (by simp) d2] at hβpt
    show (pt : V) ∈ (interp M L [quotLiftQ u, quotLiftC v, quotLiftFTy, VExpr.sort v,
      quotRelTy, VExpr.sort u] (.bvar 3)).toFun _
    rw [interp_bvar]
    show (pt : V) ∈ (snoc (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) pt) c) q) ‘ ((2 : ℕ) : V)
    rw [snoc_read (M := M) (L := L) hw₅ (by simp)
      (snoc_read (M := M) (L := L) hw₄ (by simp)
        (snoc_read (M := M) (L := L) hw₃ (by simp) d2))]
    exact hβpt
  · -- above `Prop`: five λs, and the value layer at the bottom
    rename_i h0
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotLiftT1_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1
        (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz)))))) _ fun α hα ↦ ?_
    rw [interp_sort] at hα
    unfold quotLiftFibR
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotLiftT2_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1
        (imax_eq_zero_iff.1 hz))))) _ fun r hr ↦ ?_
    unfold quotLiftFibB
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotLiftT3_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))))
      _ fun β hβ ↦ ?_
    unfold quotLiftFibF
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotLiftT4_type hq heq hu hv)
      (by simp [VLevel.WF, hu, hv])
      (fun hz ↦ h0 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))) _ fun f hf ↦ ?_
    unfold quotLiftFibC
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle (quotLiftT5_type hq hu)
      (by simp [VLevel.WF, hu, hv]) (fun hz ↦ h0 (imax_eq_zero_iff.1 hz)) _ fun c hc ↦ ?_
    unfold quotLiftFibQ
    refine mkLam_mem_interp_forallE' (env₀ := env₀) hle quotLiftT6_type hv h0 _ fun q hq5 ↦ ?_
    -- the context, and its reads
    have hw₁ : snoc ∅ α ∈ interpCtx M L [VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨∅, hnil, α, by rw [interp_sort]; exact hα, rfl⟩
    have hw₂ : snoc (snoc ∅ α) r ∈ interpCtx M L [quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₁, r, hr, rfl⟩
    have hw₃ : snoc (snoc (snoc ∅ α) r) β ∈
        interpCtx M L [VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₂, β, hβ, rfl⟩
    have hw₄ : snoc (snoc (snoc (snoc ∅ α) r) β) f ∈
        interpCtx M L [quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₃, f, hf, rfl⟩
    have hw₅ : snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c ∈
        interpCtx M L [quotLiftC v, quotLiftFTy, VExpr.sort v, quotRelTy, VExpr.sort u] :=
      (mem_interpCtx_cons M L).mpr ⟨_, hw₄, c, hc, rfl⟩
    have b0 : (snoc ∅ α) ‘ ((0 : ℕ) : V) = α := snoc_top (M := M) (L := L) hnil (by simp)
    have c0 : (snoc (snoc ∅ α) r) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₁ (by simp) b0
    have c1 : (snoc (snoc ∅ α) r) ‘ ((1 : ℕ) : V) = r :=
      snoc_top (M := M) (L := L) hw₁ (by simp)
    have d0 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₂ (by simp) c0
    have d1 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₂ (by simp) c1
    have d2 : (snoc (snoc (snoc ∅ α) r) β) ‘ ((2 : ℕ) : V) = β :=
      snoc_top (M := M) (L := L) hw₂ (by simp)
    have e0' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₃ (by simp) d0
    have e1' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₃ (by simp) d1
    have e2' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((2 : ℕ) : V) = β :=
      snoc_read (M := M) (L := L) hw₃ (by simp) d2
    have e3' : (snoc (snoc (snoc (snoc ∅ α) r) β) f) ‘ ((3 : ℕ) : V) = f :=
      snoc_top (M := M) (L := L) hw₃ (by simp)
    have g0 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((0 : ℕ) : V) = α :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e0'
    have g1 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((1 : ℕ) : V) = r :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e1'
    have g2 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((2 : ℕ) : V) = β :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e2'
    have g3 : (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((3 : ℕ) : V) = f :=
      snoc_read (M := M) (L := L) hw₄ (by simp) e3'
    -- what the two content-carrying binders give
    rw [interp_sort] at hβ
    obtain ⟨hfun, hgraph, hcod⟩ := quotLift_f_props (env₀ := env₀) hle hv h0 hw₃ d0 d2 hf
    have hresp := quotLift_respects (env₀ := env₀) hle heq hu hv h0 hEq hw₄ e0' e1' e2' e3'
      hβ hcod hc
    have hsub : u.eval M.ls = 0 → α ⊆ ({pt} : V) := by
      intro hi; rw [hi, U_zero] at hα; exact mem_UProp_iff.1 hα
    rw [interp_quotLiftQ (env₀ := env₀) hle hq hu hcnst g0 g1 hα hr] at hq5
    -- and the value lands in the codomain
    show quotLiftVal ((snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) ‘ ((3 : ℕ) : V)) q
      (u.eval M.ls) ∈ _
    rw [g3]
    show _ ∈ (interp M L [quotLiftQ u, quotLiftC v, quotLiftFTy, VExpr.sort v,
      quotRelTy, VExpr.sort u] (.bvar 3)).toFun _
    rw [interp_bvar]
    show _ ∈ (snoc (snoc (snoc (snoc (snoc (snoc ∅ α) r) β) f) c) q) ‘ ((2 : ℕ) : V)
    rw [snoc_read (M := M) (L := L) hw₅ (by simp) g2]
    exact quotLiftVal_mem hfun hgraph hcod hsub hresp hq5

end LiftMem

end Lift

end Interp

end Lean4Lean.SetModel
