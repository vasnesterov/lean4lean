import Lean4Lean.Theory.SetModel.Inaccessible

/-!
# The universe sequence `U i`, `Prop`, and the three axioms

This is the set-theoretic half of Carneiro, *The Type Theory of Lean*, §6.2:
the sequence of universes interpreting `Sort 0, Sort 1, …`, the two-element
universe of propositions with its proof irrelevance, and the internal data
validating `propext`, `Classical.choice` and `Quot.sound`.

Nothing here mentions Lean syntax; the interpretation `⟦Γ ⊢ e⟧` itself is *not*
attempted (it needs Carneiro's proof-splitting, hence `lvl`/`sort`, hence unique
typing).

## The picture

* `U κ 0 = UProp = ℘ {•}` with `• = ∅` — the two truth values `∅` ("false")
  and `{•}` ("true").  Proof irrelevance is the statement that these are the
  *only* elements, and `propext_of_mem_UProp` is `propext`.
* `U κ (i+1) = Vset (κ i)` for `κ` an `∈`-increasing chain of inaccessibles.

## Where each hypothesis is spent

| Fact | Needs |
|---|---|
| `piProp_mem_UProp` (impredicative `∀`) | **nothing** — no bound on `A` at all |
| `propext_of_mem_UProp` | nothing |
| `sUnion_mem_U`, `lfp_mem_U`, `acc_mem_U` | nothing |
| pairing, `℘`, `×ˢ`, `^`, `Pi`, `Sigma`, `disjUnion`, `setQuotient` at `U (i+1)` | `i < n` |
| `piFun_mem_U`, `sigmaFun_mem_U`, `repl_mem_U` | `i < n`, and regularity of `κ i` |
| `eqvClosure_mem_U`, `quot_mem_U` (`Quot.sound`) | `i < n` |
| `exists_choiceFunction_mem_U` (`Classical.choice`) | `i < n` and `𝗔𝗖` |

So a derivation whose largest universe index is `m` needs exactly `m`
inaccessibles: `U 0, …, U m` are all available and closed as soon as `m ≤ n`.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## The universe of propositions -/

section UProp

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- The unique inhabitant `• = ∅` of the "true" proposition. -/
noncomputable def pt : V := ∅

lemma pt_def : (pt : V) = ∅ := rfl

/-- The universe of propositions `U₀ = ℘ {•} = {∅, {•}}`. -/
noncomputable def UProp : V := ℘ ({pt} : V)

/-- **`U₀` is exactly the set of subsets of `{•}`.** -/
@[simp] lemma mem_UProp_iff {p : V} : p ∈ (UProp : V) ↔ p ⊆ ({pt} : V) := mem_power_iff

lemma subset_singleton_iff {a p : V} : p ⊆ ({a} : V) ↔ p = ∅ ∨ p = {a} := by
  constructor
  · intro h
    by_cases ha : a ∈ p
    · exact Or.inr (subset_antisymm h (by simpa using ha))
    · refine Or.inl (subset_empty_iff_eq_empty.mp fun z hz ↦ ?_)
      rcases mem_singleton_iff.mp (h z hz) with rfl
      exact absurd hz ha
  · rintro (rfl | rfl) <;> simp

/-- **Proof irrelevance: `U₀` has exactly two elements.** -/
theorem eq_empty_or_eq_true_of_mem_UProp {p : V} (h : p ∈ (UProp : V)) :
    p = ∅ ∨ p = ({pt} : V) := subset_singleton_iff.mp (mem_UProp_iff.mp h)

@[simp] lemma empty_mem_UProp : (∅ : V) ∈ (UProp : V) := by simp

@[simp] lemma true_mem_UProp : ({pt} : V) ∈ (UProp : V) := by simp

/-- A proposition is true iff it contains `•`. -/
lemma pt_mem_iff_eq_true {p : V} (h : p ∈ (UProp : V)) : pt ∈ p ↔ p = ({pt} : V) := by
  constructor
  · intro hp
    rcases eq_empty_or_eq_true_of_mem_UProp h with rfl | rfl
    · exact absurd hp not_mem_empty
    · rfl
  · rintro rfl; simp

/-- **The validation of `propext`.**  Two propositions with the same truth value
are equal.  This is the whole justification for `propext` in the model. -/
theorem propext_of_mem_UProp {p q : V} (hp : p ∈ (UProp : V)) (hq : q ∈ (UProp : V))
    (h : pt ∈ p ↔ pt ∈ q) : p = q := by
  ext z
  constructor
  · intro hz
    rcases mem_singleton_iff.mp (mem_UProp_iff.mp hp z hz) with rfl
    exact h.mp hz
  · intro hz
    rcases mem_singleton_iff.mp (mem_UProp_iff.mp hq z hz) with rfl
    exact h.mpr hz

end UProp

/-! ## Impredicativity is free

The interpretation of `∀ x : A, B x` when `B` lands in `Prop` is
`{•} ∩ ⋂_{x ∈ A} B x`.  It lies in `U₀` for **any** `A` whatsoever — there is
no hypothesis bounding the universe level of `A`, and no large cardinal is
involved.  The `{•} ∩` is what makes the empty case work: `⋂_{x ∈ ∅}` is the
whole universe, which is not a set.
-/

section Impredicative

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- `{•} ∩ ⋂_{x ∈ A} B x` — the interpretation of an impredicative `∀`. -/
noncomputable def piProp (A : V) (B : V → V) (hB : ℒₛₑₜ-function₁ B := by definability) : V :=
  {z ∈ ({pt} : V) ; ∀ x ∈ A, z ∈ B x}

lemma mem_piProp_iff {A z : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    z ∈ piProp A B hB ↔ z = pt ∧ ∀ x ∈ A, z ∈ B x := by simp [piProp]

/-- **Impredicativity costs nothing.**  Note the hypotheses: `A` is an
arbitrary set, of arbitrary rank, and no inaccessible is mentioned. -/
theorem piProp_mem_UProp (A : V) (B : V → V) (hB : ℒₛₑₜ-function₁ B) :
    piProp A B hB ∈ (UProp : V) := mem_UProp_iff.mpr sep_subset

/-- The empty case: `⋂` over nothing is everything, so the answer is `True`.
This is where the `{•} ∩` does real work. -/
@[simp] theorem piProp_empty (B : V → V) (hB : ℒₛₑₜ-function₁ B) :
    piProp (∅ : V) B hB = ({pt} : V) := by
  ext z; simp [mem_piProp_iff]

lemma pt_mem_piProp_iff {A : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    pt ∈ piProp A B hB ↔ ∀ x ∈ A, pt ∈ B x := by simp [mem_piProp_iff]

/-- `∀ x : A, B x` is true exactly when every `B x` is. -/
theorem piProp_eq_true_iff {A : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B}
    (h : ∀ x ∈ A, B x ∈ (UProp : V)) :
    piProp A B hB = ({pt} : V) ↔ ∀ x ∈ A, B x = ({pt} : V) := by
  rw [← pt_mem_iff_eq_true (piProp_mem_UProp A B hB), pt_mem_piProp_iff]
  exact forall₂_congr fun x hx ↦ pt_mem_iff_eq_true (h x hx)

end Impredicative

/-! ## The universe sequence -/

section Sequence

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The universe sequence attached to a chain `κ` of inaccessibles:
`U κ 0` is the universe of propositions, `U κ (i+1) = Vset (κ i)`. -/
noncomputable def U (κ : ℕ → V) : ℕ → V
  | 0 => UProp
  | i + 1 => vsetV (κ i)

@[simp] lemma U_zero (κ : ℕ → V) : U κ 0 = (UProp : V) := rfl

@[simp] lemma U_succ (κ : ℕ → V) (i : ℕ) : U κ (i + 1) = vsetV (κ i) := rfl

variable {n : ℕ} {κ : ℕ → V}

lemma UProp_mem_vsetV {k : V} (hk : IsInaccessible k) : (UProp : V) ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have h : (UProp : V) ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    power_mem_Vset hk.isLimitOrdinal
      (singleton_mem_Vset hk.isLimitOrdinal (empty_mem_Vset hk.isLimitOrdinal))
  exact h

/-- **`U i ∈ U (i+1)`** — the form the universe rule `Sort i : Sort (i+1)`
needs. -/
theorem U_mem_succ (hκ : IsInaccessibleChain n κ) {i : ℕ} (hi : i < n) :
    U κ i ∈ U κ (i + 1) := by
  cases i with
  | zero => exact UProp_mem_vsetV (hκ.inaccessible 0 hi)
  | succ j =>
    have hj : j < n := by omega
    have hkj : IsOrdinal (κ j) := (hκ.inaccessible j hj).isOrdinal
    have hkj1 : IsOrdinal (κ (j + 1)) := (hκ.inaccessible (j + 1) hi).isOrdinal
    have hmem : κ j ∈ κ (j + 1) := hκ.mem j (j + 1) (by omega) hi
    have h1 : rank (Vset (IsOrdinal.toOrdinal (κ j) : Ordinal V))
        < (IsOrdinal.toOrdinal (κ (j + 1)) : Ordinal V) := by
      rw [rank_Vset]
      exact lt_def.mpr hmem
    have h2 : Vset (IsOrdinal.toOrdinal (κ j) : Ordinal V)
        ∈ Vset (IsOrdinal.toOrdinal (κ (j + 1)) : Ordinal V) := mem_Vset_iff_rank_lt.mpr h1
    exact h2

/-- **`U i ⊆ U (i+1)`** — the form the `Π`/`Σ`/inductive formation rules need.
This is a genuinely different fact from `U_mem_succ`; it holds because every
`Vset` is a transitive set. -/
theorem U_subset_succ (hκ : IsInaccessibleChain n κ) {i : ℕ} (hi : i < n) :
    U κ i ⊆ U κ (i + 1) := by
  have hko : IsOrdinal (κ i) := (hκ.inaccessible i hi).isOrdinal
  have hmem : U κ i ∈ Vset (IsOrdinal.toOrdinal (κ i) : Ordinal V) := U_mem_succ hκ hi
  have h : U κ i ⊆ Vset (IsOrdinal.toOrdinal (κ i) : Ordinal V) :=
    subset_Vset_of_mem_Vset hmem
  exact h

theorem U_mono (hκ : IsInaccessibleChain n κ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    U κ i ⊆ U κ j := by
  induction j with
  | zero =>
    rcases Nat.le_zero.mp hij with rfl
    exact subset_refl _
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
    · exact subset_trans (ih (by omega) (by omega)) (U_subset_succ hκ (by omega))
    · rcases h with rfl
      exact subset_refl _

theorem U_mem_of_lt (hκ : IsInaccessibleChain n κ) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    U κ i ∈ U κ j :=
  U_mono hκ (show i + 1 ≤ j by omega) hj (U κ i) (U_mem_succ hκ (by omega))

/-- `U κ n` is the top of the sequence, and by `U_mono` it contains every
earlier stage.  There is no `U_ω` inside the model — its rank would be the
supremum of the `κ i`, which is not below any of them — but none is needed:
each schema instance fixes a finite `n`, and `U κ n` serves as the ambient
universe for every derivation whose largest universe index is `≤ n`. -/
theorem U_subset_top (hκ : IsInaccessibleChain n κ) {i : ℕ} (hi : i ≤ n) :
    U κ i ⊆ U κ n := U_mono hκ hi le_rfl

end Sequence

/-! ## Closure of `U (i+1)`

Each restatement records exactly what it needs.  All of these are `i < n`, i.e.
"`κ i` is inaccessible", except the three that need nothing at all.
-/

section UClosure

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {n : ℕ} {κ : ℕ → V} {i : ℕ}

/-- These five need *only* that `κ i` be an ordinal — which is merely what
makes `U κ (i+1)` a well-formed stage — and not that it be inaccessible, a
limit, or anything else.  The `IsOrdinal (κ i)` hypothesis is bookkeeping to
name the stage, not a mathematical assumption. -/
theorem mem_U_of_subset_of_mem (hko : IsOrdinal (κ i)) {x y : V} (hyx : y ⊆ x)
    (hx : x ∈ U κ (i + 1)) : y ∈ U κ (i + 1) := by
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx ⊢
  exact mem_Vset_of_subset_of_mem hyx hx

theorem sUnion_mem_U (hko : IsOrdinal (κ i)) {x : V} (hx : x ∈ U κ (i + 1)) :
    ⋃ˢ x ∈ U κ (i + 1) := by
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx ⊢
  exact sUnion_mem_Vset hx

theorem sep_mem_U (hko : IsOrdinal (κ i)) {x : V} (hx : x ∈ U κ (i + 1))
    {P : V → Prop} (hP : ℒₛₑₜ-predicate P) : sep x P hP ∈ U κ (i + 1) := by
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx ⊢
  exact sep_mem_Vset hx hP

/-- Least fixed points never leave the stage their carrier lives in: no
inaccessibility, no limit-ness. -/
theorem lfp_mem_U (hko : IsOrdinal (κ i)) {d : V} {Φ : V → V} {hΦ : ℒₛₑₜ-function₁ Φ}
    (h : IsMonotoneOn d Φ) (hd : d ∈ U κ (i + 1)) : lfp d Φ hΦ ∈ U κ (i + 1) := by
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hd ⊢
  exact lfp_mem_Vset h hd

theorem acc_mem_U (hko : IsOrdinal (κ i)) {A R : V} (hA : A ∈ U κ (i + 1)) :
    acc A R ∈ U κ (i + 1) := by
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hA ⊢
  exact acc_mem_Vset hA

variable (hκ : IsInaccessibleChain n κ) (hi : i < n)

include hκ hi

theorem power_mem_U {x : V} (hx : x ∈ U κ (i + 1)) : ℘ x ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx ⊢
  exact power_mem_Vset hk.isLimitOrdinal hx

theorem doubleton_mem_U {x y : V} (hx : x ∈ U κ (i + 1)) (hy : y ∈ U κ (i + 1)) :
    doubleton x y ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx hy ⊢
  exact doubleton_mem_Vset hk.isLimitOrdinal hx hy

theorem prod_mem_U {x y : V} (hx : x ∈ U κ (i + 1)) (hy : y ∈ U κ (i + 1)) :
    (x ×ˢ y : V) ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx hy ⊢
  exact prod_mem_Vset hk.isLimitOrdinal hx hy

theorem function_mem_U {x y : V} (hx : x ∈ U κ (i + 1)) (hy : y ∈ U κ (i + 1)) :
    (y ^ x : V) ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hx hy ⊢
  exact function_mem_Vset hk.isLimitOrdinal hx hy

/-- `Π` for an internal (set) family: needs only that `κ i` be inaccessible,
and in fact only that it be a limit ordinal. -/
theorem pi_mem_U {A B : V} (hA : A ∈ U κ (i + 1)) (hB : B ∈ U κ (i + 1)) :
    Pi A B ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hA hB ⊢
  exact pi_mem_Vset hk.isLimitOrdinal hA hB

/-- `Σ` for an internal (set) family. -/
theorem sigma_mem_U {A B : V} (hA : A ∈ U κ (i + 1)) (hB : B ∈ U κ (i + 1)) :
    Sigma A B ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hA hB ⊢
  exact sigma_mem_Vset hk.isLimitOrdinal hA hB

theorem disjUnion_mem_U {A B : V} (hA : A ∈ U κ (i + 1)) (hB : B ∈ U κ (i + 1)) :
    disjUnion A B ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hA hB ⊢
  exact disjUnion_mem_Vset hk.isLimitOrdinal hA hB

theorem setQuotient_mem_U {A R : V} (hA : A ∈ U κ (i + 1)) :
    setQuotient A R ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  rw [U_succ, mem_vsetV_iff_mem_Vset] at hA ⊢
  exact setQuotient_mem_Vset hk.isLimitOrdinal hA

/-- **Replacement at stage `i+1`.**  This is the one that spends regularity of
`κ i`; the index set must be an ordinal `a ∈ κ i`. -/
theorem repl_mem_U {a : V} (ha : a ∈ κ i) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hFa : ∀ x ∈ a, F x ∈ U κ (i + 1)) : repl F hF a ∈ U κ (i + 1) := by
  rw [U_succ]
  exact repl_mem_vsetV (hκ.inaccessible i hi) ha F hF (by simpa using hFa)

/-- `Π` for an externally given (definable) family over an index set `a ∈ κ i`.
Spends regularity. -/
theorem piFun_mem_U {a : V} (ha : a ∈ κ i) (B : V → V) (hB : ℒₛₑₜ-function₁ B)
    (hBa : ∀ x ∈ a, B x ∈ U κ (i + 1)) : PiFun a B hB ∈ U κ (i + 1) := by
  rw [U_succ]
  exact piFun_mem_vsetV (hκ.inaccessible i hi) ha B hB (by simpa using hBa)

/-- `Σ` for an externally given (definable) family.  Spends regularity. -/
theorem sigmaFun_mem_U {a : V} (ha : a ∈ κ i) (B : V → V) (hB : ℒₛₑₜ-function₁ B)
    (hBa : ∀ x ∈ a, B x ∈ U κ (i + 1)) : SigmaFun a B hB ∈ U κ (i + 1) := by
  rw [U_succ]
  exact sigmaFun_mem_vsetV (hκ.inaccessible i hi) ha B hB (by simpa using hBa)

end UClosure

/-! ## The choice function

`Classical.choice` is validated by a *choice function on a single set*: every
type of the model lives in some `U i`, so ordinary `𝗔𝗖` applied to `U i`
suffices and no global choice principle is needed.  We produce the choice
function as an **internal set** (an element of `U (i+1)`), not as a Lean-level
`V → V`: a Lean-level function would not be an object of the model and could
not be the denotation of `Classical.choice`.
-/

section Choice

/-- `f ‘ x = y` whenever `⟨x, y⟩ₖ ∈ f`.  Foundation proves `value_mem_range`
but never this. -/
lemma value_eq_of_kpair_mem [V↓[ℒₛₑₜ] ⊧* 𝗭] {f x y : V} [IsFunction f]
    (h : ⟨x, y⟩ₖ ∈ f) : f ‘ x = y := by
  ext z
  constructor
  · intro hz
    have hz' : z ∈ ⋃ˢ (range f) ∧ ∃ w, z ∈ w ∧ ⟨x, w⟩ₖ ∈ f := by simpa [value] using hz
    obtain ⟨-, w, hzw, hxw⟩ := hz'
    have hw : w = y := IsFunction.unique hxw h
    exact hw ▸ hzw
  · intro hz
    have hu : z ∈ ⋃ˢ (range f) := mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem h, hz⟩
    have h' : z ∈ ⋃ˢ (range f) ∧ ∃ w, z ∈ w ∧ ⟨x, w⟩ₖ ∈ f := ⟨hu, y, hz, h⟩
    simpa [value] using h'

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Foundation's axiom of choice, read inside the model. -/
lemma internal_choice (𝓧 : V) (hne : ∀ X ∈ 𝓧, IsNonempty X)
    (hdisj : ∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z ∈ X, z ∈ Y) → X = Y) :
    ∃ C : V, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X := by
  have h : ∀ 𝓧 : V, (∀ X ∈ 𝓧, IsNonempty X) →
      (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z ∈ X, z ∈ Y) → X = Y) →
      ∃ C : V, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X := by
    simpa [models_iff, Axiom.choice] using
      Theory.models V 𝗔𝗖 (show Axiom.choice ∈ (𝗔𝗖 : SetTheory) from rfl)
  exact h 𝓧 hne hdisj

/-- **A choice function on an arbitrary set `S`, as an internal set.**
`c` is a function; it is defined at every nonempty member of `S`; and all its
values are members.  Only `𝗔𝗖` for the single family built from `S` is used. -/
theorem exists_choiceFunction (S : V) :
    ∃ c : V, IsFunction c ∧ (∀ x ∈ S, IsNonempty x → ∃ y ∈ x, ⟨x, y⟩ₖ ∈ c) ∧
      (∀ x y : V, ⟨x, y⟩ₖ ∈ c → x ∈ S ∧ y ∈ x) := by
  obtain ⟨S', hS'⟩ : ∃ S' : V, ∀ x : V, x ∈ S' ↔ x ∈ S ∧ IsNonempty x :=
    ⟨sep S (fun x ↦ IsNonempty x), fun _ ↦ mem_sep_iff⟩
  have hdef : ℒₛₑₜ-function₁[V] (fun x : V ↦ ({x} : V) ×ˢ x) := by definability
  obtain ⟨𝓧, h𝓧⟩ : ∃ 𝓧 : V, ∀ X : V, X ∈ 𝓧 ↔ ∃ x ∈ S', X = ({x} : V) ×ˢ x :=
    ⟨repl _ hdef S', fun _ ↦ repl_spec hdef⟩
  -- the family `{ {x} ×ˢ x | x ∈ S, x ≠ ∅ }` is nonempty and pairwise disjoint
  have hne : ∀ X ∈ 𝓧, IsNonempty X := by
    intro X hX
    obtain ⟨x, hx, rfl⟩ := (h𝓧 X).mp hX
    obtain ⟨-, hxne⟩ := (hS' x).mp hx
    obtain ⟨y, hy⟩ := hxne.nonempty
    exact ⟨⟨x, y⟩ₖ, kpair_mem_iff.mpr ⟨by simp, hy⟩⟩
  have hdisj : ∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z ∈ X, z ∈ Y) → X = Y := by
    rintro X hX Y hY ⟨z, hzX, hzY⟩
    obtain ⟨x, hx, rfl⟩ := (h𝓧 X).mp hX
    obtain ⟨y, hy, rfl⟩ := (h𝓧 Y).mp hY
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hzX
    obtain ⟨a', ha', b', hb', he⟩ := mem_prod_iff.mp hzY
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    rcases mem_singleton_iff.mp ha with rfl
    rcases mem_singleton_iff.mp ha' with rfl
    rfl
  obtain ⟨C, hC⟩ := internal_choice 𝓧 hne hdisj
  -- cut `C` down to the graph of a choice function
  obtain ⟨c, hc⟩ : ∃ c : V, ∀ p : V, p ∈ c ↔ p ∈ C ∧ ∃ x ∈ S', ∃ y ∈ x, p = ⟨x, y⟩ₖ := by
    refine ⟨sep (S' ×ˢ (⋃ˢ S)) (fun p ↦ p ∈ C ∧ ∃ x ∈ S', ∃ y ∈ x, p = ⟨x, y⟩ₖ),
      fun p ↦ ?_⟩
    rw [mem_sep_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    obtain ⟨-, x, hx, y, hy, rfl⟩ := h
    exact kpair_mem_iff.mpr ⟨hx, mem_sUnion_iff.mpr ⟨x, ((hS' x).mp hx).1, hy⟩⟩
  have hckpair : ∀ x y : V, ⟨x, y⟩ₖ ∈ c ↔ ⟨x, y⟩ₖ ∈ C ∧ x ∈ S' ∧ y ∈ x := by
    intro x y
    rw [hc]
    refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
    · rintro ⟨x', hx', y', hy', he⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj he
      exact ⟨hx', hy'⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x, hx, y, hy, rfl⟩
  have hexist : ∀ x ∈ S', ∃ y ∈ x, ⟨x, y⟩ₖ ∈ c := by
    intro x hx
    have hX : (({x} : V) ×ˢ x) ∈ 𝓧 := (h𝓧 _).mpr ⟨x, hx, rfl⟩
    obtain ⟨p, ⟨hpC, hpX⟩, -⟩ := hC _ hX
    obtain ⟨a, ha, y, hy, rfl⟩ := mem_prod_iff.mp hpX
    rcases mem_singleton_iff.mp ha with rfl
    exact ⟨y, hy, (hckpair a y).mpr ⟨hpC, hx, hy⟩⟩
  have huniq : ∀ x y₁ y₂ : V, ⟨x, y₁⟩ₖ ∈ c → ⟨x, y₂⟩ₖ ∈ c → y₁ = y₂ := by
    intro x y₁ y₂ h₁ h₂
    obtain ⟨h₁C, hx, hy₁⟩ := (hckpair x y₁).mp h₁
    obtain ⟨h₂C, -, hy₂⟩ := (hckpair x y₂).mp h₂
    have hX : (({x} : V) ×ˢ x) ∈ 𝓧 := (h𝓧 _).mpr ⟨x, hx, rfl⟩
    have hu := hC _ hX
    have e : (⟨x, y₁⟩ₖ : V) = ⟨x, y₂⟩ₖ :=
      hu.unique ⟨h₁C, kpair_mem_iff.mpr ⟨by simp, hy₁⟩⟩
        ⟨h₂C, kpair_mem_iff.mpr ⟨by simp, hy₂⟩⟩
    exact (kpair_inj e).2
  have hIsFun : IsFunction c := by
    refine isFunction_iff.mpr (mem_function.intro (fun p hp ↦ ?_) (fun x hx ↦ ?_))
    · obtain ⟨-, x, hx, y, hy, rfl⟩ := (hc p).mp hp
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
    · obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
      exact ExistsUnique.intro y hy fun y' hy' ↦ huniq x y' y hy' hy
  refine ⟨c, hIsFun, fun x hx hxne ↦ hexist x ((hS' x).mpr ⟨hx, hxne⟩), fun x y hxy ↦ ?_⟩
  obtain ⟨-, hx, hy⟩ := (hckpair x y).mp hxy
  exact ⟨((hS' x).mp hx).1, hy⟩

/-- The same, packaged with `value`. -/
theorem exists_choiceFunction_value (S : V) :
    ∃ c : V, IsFunction c ∧ c ⊆ S ×ˢ (⋃ˢ S) ∧ ∀ x ∈ S, IsNonempty x → c ‘ x ∈ x := by
  obtain ⟨c, hfun, hex, hmem⟩ := exists_choiceFunction S
  refine ⟨c, hfun, fun p hp ↦ ?_, fun x hx hxne ↦ ?_⟩
  · obtain ⟨a, b, rfl⟩ := IsFunction.mem_eq_kpair hp
    obtain ⟨haS, hba⟩ := hmem a b hp
    exact kpair_mem_iff.mpr ⟨haS, mem_sUnion_iff.mpr ⟨a, haS, hba⟩⟩
  · obtain ⟨y, hy, hcy⟩ := hex x hx hxne
    rw [value_eq_of_kpair_mem hcy]
    exact hy

variable {n : ℕ} {κ : ℕ → V}

/-- **The validation of `Classical.choice`.**  A choice function for the whole
of `U i`, living one stage up in `U (i+1)`.  Only `𝗔𝗖` applied to the single
set `U i` is used — no global choice. -/
theorem exists_choiceFunction_mem_U (hκ : IsInaccessibleChain n κ) {i : ℕ} (hi : i < n) :
    ∃ c : V, c ∈ U κ (i + 1) ∧ IsFunction c ∧
      ∀ x ∈ U κ i, IsNonempty x → c ‘ x ∈ x := by
  obtain ⟨c, hfun, hsub, hval⟩ := exists_choiceFunction_value (U κ i)
  have hko : IsOrdinal (κ i) := (hκ.inaccessible i hi).isOrdinal
  have hUi : U κ i ∈ U κ (i + 1) := U_mem_succ hκ hi
  refine ⟨c, mem_U_of_subset_of_mem hko hsub
    (prod_mem_U hκ hi hUi (sUnion_mem_U hko hUi)), hfun, hval⟩

end Choice

/-! ## Prerequisites for `Quot.sound`

Lean's `Quot` does **not** require `R` to be an equivalence relation, so the
model must quotient by the *equivalence closure* of `R`.  That closure is a
least fixed point, so by `lfp_mem_U` it costs nothing: the quotient lands in the
same stage as `A`.
-/

section Quot

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {A R : V}

/-- `E` is an equivalence relation on `A`. -/
structure IsEquivalenceOn (A E : V) : Prop where
  subset : E ⊆ A ×ˢ A
  refl : ∀ x ∈ A, ⟨x, x⟩ₖ ∈ E
  symm : ∀ x y : V, ⟨x, y⟩ₖ ∈ E → ⟨y, x⟩ₖ ∈ E
  trans : ∀ x y z : V, ⟨x, y⟩ₖ ∈ E → ⟨y, z⟩ₖ ∈ E → ⟨x, z⟩ₖ ∈ E

/-- One step of the equivalence-closure operator for `R` on `A`. -/
noncomputable def eqvStep (A R S : V) : V :=
  {p ∈ A ×ˢ A ;
    (∃ x ∈ A, p = ⟨x, x⟩ₖ) ∨ p ∈ R ∨
      (∃ x y : V, p = ⟨x, y⟩ₖ ∧ ⟨y, x⟩ₖ ∈ S) ∨
      (∃ x y z : V, p = ⟨x, z⟩ₖ ∧ ⟨x, y⟩ₖ ∈ S ∧ ⟨y, z⟩ₖ ∈ S)}

lemma mem_eqvStep_iff {S p : V} :
    p ∈ eqvStep A R S ↔ p ∈ A ×ˢ A ∧
      ((∃ x ∈ A, p = ⟨x, x⟩ₖ) ∨ p ∈ R ∨
        (∃ x y : V, p = ⟨x, y⟩ₖ ∧ ⟨y, x⟩ₖ ∈ S) ∨
        (∃ x y z : V, p = ⟨x, z⟩ₖ ∧ ⟨x, y⟩ₖ ∈ S ∧ ⟨y, z⟩ₖ ∈ S)) := mem_sep_iff

lemma eqvStep_definable (A R : V) : ℒₛₑₜ-function₁[V] (eqvStep A R) := by
  suffices ℒₛₑₜ-relation[V] (fun T S ↦ T = eqvStep A R S) by exact this
  have e : ∀ T S : V, T = eqvStep A R S ↔ ∀ p, p ∈ T ↔ p ∈ A ×ˢ A ∧
      ((∃ x ∈ A, p = ⟨x, x⟩ₖ) ∨ p ∈ R ∨
        (∃ x y : V, p = ⟨x, y⟩ₖ ∧ ⟨y, x⟩ₖ ∈ S) ∨
        (∃ x y z : V, p = ⟨x, z⟩ₖ ∧ ⟨x, y⟩ₖ ∈ S ∧ ⟨y, z⟩ₖ ∈ S)) := by
    intro T S
    rw [mem_ext_iff]
    simp [eqvStep]
  simp only [e]
  definability

lemma eqvStep_isMonotoneOn (A R : V) : IsMonotoneOn (A ×ˢ A) (eqvStep A R) where
  mono S T hST p hp := by
    rw [mem_eqvStep_iff] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rcases hp.2 with h | h | ⟨x, y, he, hs⟩ | ⟨x, y, z, he, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨x, y, he, hST _ hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x, y, z, he, hST _ h1, hST _ h2⟩))
  maps := sep_subset

/-- The equivalence closure of `R` on `A`, as a least fixed point. -/
noncomputable def eqvClosure (A R : V) : V :=
  lfp (A ×ˢ A) (eqvStep A R) (eqvStep_definable A R)

theorem eqvClosure_subset (A R : V) : eqvClosure A R ⊆ A ×ˢ A :=
  lfp_subset (eqvStep_isMonotoneOn A R)

lemma eqvStep_eqvClosure (A R : V) :
    eqvStep A R (eqvClosure A R) = eqvClosure A R := apply_lfp (eqvStep_isMonotoneOn A R)

/-- The closure contains `R` (restricted to `A`). -/
theorem subset_eqvClosure {p : V} (hp : p ∈ R) (hA : p ∈ A ×ˢ A) : p ∈ eqvClosure A R := by
  rw [← eqvStep_eqvClosure A R, mem_eqvStep_iff]
  exact ⟨hA, Or.inr (Or.inl hp)⟩

/-- **The equivalence closure really is an equivalence relation on `A`.** -/
theorem isEquivalenceOn_eqvClosure (A R : V) : IsEquivalenceOn A (eqvClosure A R) where
  subset := eqvClosure_subset A R
  refl x hx := by
    rw [← eqvStep_eqvClosure A R, mem_eqvStep_iff]
    exact ⟨kpair_mem_iff.mpr ⟨hx, hx⟩, Or.inl ⟨x, hx, rfl⟩⟩
  symm x y h := by
    have hxy : x ∈ A ∧ y ∈ A := kpair_mem_iff.mp (eqvClosure_subset A R _ h)
    rw [← eqvStep_eqvClosure A R, mem_eqvStep_iff]
    exact ⟨kpair_mem_iff.mpr ⟨hxy.2, hxy.1⟩, Or.inr (Or.inr (Or.inl ⟨y, x, rfl, h⟩))⟩
  trans x y z h₁ h₂ := by
    have hxy : x ∈ A ∧ y ∈ A := kpair_mem_iff.mp (eqvClosure_subset A R _ h₁)
    have hyz : y ∈ A ∧ z ∈ A := kpair_mem_iff.mp (eqvClosure_subset A R _ h₂)
    rw [← eqvStep_eqvClosure A R, mem_eqvStep_iff]
    exact ⟨kpair_mem_iff.mpr ⟨hxy.1, hyz.2⟩,
      Or.inr (Or.inr (Or.inr ⟨x, y, z, rfl, h₁, h₂⟩))⟩

/-- **…and it is the least one.** -/
theorem eqvClosure_least {E : V} (hE : IsEquivalenceOn A E)
    (hR : ∀ p ∈ R, p ∈ A ×ˢ A → p ∈ E) : eqvClosure A R ⊆ E := by
  refine lfp_subset_of_prefixed (eqvStep_isMonotoneOn A R) hE.subset fun p hp ↦ ?_
  rw [mem_eqvStep_iff] at hp
  rcases hp.2 with ⟨x, hx, rfl⟩ | h | ⟨x, y, rfl, hs⟩ | ⟨x, y, z, rfl, h1, h2⟩
  · exact hE.refl x hx
  · exact hR p h hp.1
  · exact hE.symm y x hs
  · exact hE.trans x y z h1 h2

/-- Equality of classes is the relation, for an equivalence relation. -/
theorem eqvClass_eq_iff {E x y : V} (hE : IsEquivalenceOn A E) (hx : x ∈ A) (_hy : y ∈ A) :
    eqvClass A E x = eqvClass A E y ↔ ⟨x, y⟩ₖ ∈ E := by
  constructor
  · intro h
    have hxx : x ∈ eqvClass A E x := mem_eqvClass_iff.mpr ⟨hx, hE.refl x hx⟩
    rw [h] at hxx
    exact hE.symm y x (mem_eqvClass_iff.mp hxx).2
  · intro h
    ext z
    simp only [mem_eqvClass_iff]
    refine and_congr_right fun _ ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · exact hE.trans y x z (hE.symm x y h) hz
    · exact hE.trans x y z h hz

/-- **`Quot.lift`'s ι-rule.**  A function on `A` that respects `E` factors
through the quotient: there is a function `g` on `setQuotient A E` with
`g ‘ [x] = f ‘ x` for every `x ∈ A`. -/
theorem exists_quotient_lift {E f : V} (hE : IsEquivalenceOn A E) [IsFunction f]
    (hdom : ∀ x ∈ A, ∃ y : V, ⟨x, y⟩ₖ ∈ f)
    (hresp : ∀ x ∈ A, ∀ y ∈ A, ⟨x, y⟩ₖ ∈ E → f ‘ x = f ‘ y) :
    ∃ g : V, IsFunction g ∧ g ⊆ setQuotient A E ×ˢ range f ∧
      ∀ x ∈ A, g ‘ (eqvClass A E x) = f ‘ x := by
  have hgraph : ∀ x ∈ A, ⟨x, f ‘ x⟩ₖ ∈ f := by
    intro x hx
    obtain ⟨y, hy⟩ := hdom x hx
    rw [value_eq_of_kpair_mem hy]
    exact hy
  obtain ⟨g, hg⟩ : ∃ g : V, ∀ p : V, p ∈ g ↔ ∃ x ∈ A, p = ⟨eqvClass A E x, f ‘ x⟩ₖ := by
    refine ⟨sep (setQuotient A E ×ˢ range f)
      (fun p ↦ ∃ x ∈ A, p = ⟨eqvClass A E x, f ‘ x⟩ₖ), fun p ↦ ?_⟩
    rw [mem_sep_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    obtain ⟨x, hx, rfl⟩ := h
    exact kpair_mem_iff.mpr ⟨mem_setQuotient_iff.mpr ⟨x, hx, rfl⟩,
      mem_range_of_kpair_mem (hgraph x hx)⟩
  have hsub : g ⊆ setQuotient A E ×ˢ range f := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := (hg p).mp hp
    exact kpair_mem_iff.mpr ⟨mem_setQuotient_iff.mpr ⟨x, hx, rfl⟩,
      mem_range_of_kpair_mem (hgraph x hx)⟩
  -- well-definedness
  have huniq : ∀ c y₁ y₂ : V, ⟨c, y₁⟩ₖ ∈ g → ⟨c, y₂⟩ₖ ∈ g → y₁ = y₂ := by
    intro c y₁ y₂ h₁ h₂
    obtain ⟨x₁, hx₁, e₁⟩ := (hg _).mp h₁
    obtain ⟨x₂, hx₂, e₂⟩ := (hg _).mp h₂
    obtain ⟨hc₁, rfl⟩ := kpair_inj e₁
    obtain ⟨hc₂, rfl⟩ := kpair_inj e₂
    exact hresp x₁ hx₁ x₂ hx₂ ((eqvClass_eq_iff hE hx₁ hx₂).mp (hc₁ ▸ hc₂))
  have hIsFun : IsFunction g := by
    refine isFunction_iff.mpr (mem_function.intro (fun p hp ↦ ?_) (fun c hc ↦ ?_))
    · obtain ⟨x, hx, rfl⟩ := (hg p).mp hp
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
    · obtain ⟨y, hy⟩ := mem_domain_iff.mp hc
      exact ExistsUnique.intro y hy fun y' hy' ↦ huniq c y' y hy' hy
  exact ⟨g, hIsFun, hsub, fun x hx ↦ value_eq_of_kpair_mem ((hg _).mpr ⟨x, hx, rfl⟩)⟩

end Quot

/-! ### The quotient lands in the same stage -/

section QuotStage

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {n : ℕ} {κ : ℕ → V} {i : ℕ}
variable (hκ : IsInaccessibleChain n κ) (hi : i < n)

include hκ hi

/-- The equivalence closure stays in the stage: it is a least fixed point
inside `A ×ˢ A`, so only the closure of the stage under `×ˢ` is used. -/
theorem eqvClosure_mem_U {A R : V} (hA : A ∈ U κ (i + 1)) :
    eqvClosure A R ∈ U κ (i + 1) :=
  lfp_mem_U (hκ.inaccessible i hi).isOrdinal (eqvStep_isMonotoneOn A R)
    (prod_mem_U hκ hi hA hA)

/-- **The full `Quot` package at stage `i+1`**: for an arbitrary relation `R`
(not assumed to be an equivalence), the equivalence closure and the quotient by
it both live in `U (i+1)`. -/
theorem quot_mem_U {A R : V} (hA : A ∈ U κ (i + 1)) :
    eqvClosure A R ∈ U κ (i + 1) ∧ setQuotient A (eqvClosure A R) ∈ U κ (i + 1) :=
  ⟨eqvClosure_mem_U hκ hi hA, setQuotient_mem_U hκ hi hA⟩

end QuotStage




end Lean4Lean.SetModel
