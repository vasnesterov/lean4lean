import Lean4Lean.Theory.SetModel.Rank
import Foundation.FirstOrder.SetTheory.InaccessibleCardinal

/-!
# Inaccessible cardinals inside a model, and closure of `Vset κ`

`Foundation.FirstOrder.SetTheory.InaccessibleCardinal` defines only *syntax*:
the `ℒₛₑₜ`-formulas `IsCardinal.dfn`, `IsRegular.dfn`, `IsStrongLimit.dfn`,
`IsInaccessible.dfn`, the chain formulas `inaccessibleChain n`, and the theory
`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`.  This file reflects that syntax into Lean-level predicates on a
model `V`, extracts *internal objects* from the axiom schema, and then derives
the closure properties of `Vset κ` that the Carneiro model needs.

## Main results

* `IsCardinal`, `IsRegular`, `IsStrongLimit`, `IsInaccessible`, `InaccChain` —
  Lean-level predicates, each paired with a `Defined … via …` instance against
  the *same* formula Foundation uses, so the reflection is by construction
  faithful.
* `exists_inaccessibleChain` — from `[V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]`, for each
  meta-level `n : ℕ` there are `κ 0 ∈ κ 1 ∈ … ∈ κ (n-1)` in `V`, all
  inaccessible.  This turns the syntactic schema into usable internal objects.
* `IsInaccessible.isLimitOrdinal` — inaccessibles are limit ordinals; uses
  `IsCardinal` and `IsStrongLimit`, **not** regularity.
* `rankV_of_isOrdinal` / `mem_vsetV_of_mem` — `rank α = α` for ordinals, hence
  `a ∈ κ → a ∈ Vset κ`.

### Where each hypothesis is spent

| Construction | Needs |
|---|---|
| `sUnion_mem_Vset` (Rank.lean) | nothing |
| `lfp_mem_Vset`, `acc_mem_Vset` | nothing |
| pairing, `℘`, `×ˢ`, `^`, `disjUnion`, `setQuotient` | `IsLimitOrdinal α` |
| `sigma_mem_Vset`, `pi_mem_Vset` (family `B` an internal *set*) | `IsLimitOrdinal α` |
| `repl_mem_vsetV`, `sigmaFun_mem_vsetV`, `piFun_mem_vsetV` (family a *definable function*) | `IsRegular κ` + limit-ness |

`IsStrongLimit` is used exactly once, to prove limit-ness; `IsRegular` is used
exactly once, in `exists_rank_bound_of_regular`.

## Gap

`repl_mem_vsetV` takes its index set to be an element `a ∈ κ`.  Upgrading it to
an arbitrary `A ∈ Vset κ` requires `∀ β < κ, ∃ a ∈ κ, Vset β ≤# a` (i.e.
`|V_β| < κ`), whose usual proof needs infinite cardinal arithmetic
(`|α × β| = max` for infinite cardinals, monotonicity of `℘` under injections,
a choice of injections at limit stages).  Foundation's `SetTheory/Function.lean`
supplies only `CardLE`/`CardLT`/`CardEQ`, `cardLE_of_subset` and
`cardLT_power`, so that is out of reach here and is left out deliberately.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Reflecting the syntax into Lean predicates -/

section Predicates

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- `k` is a cardinal: an ordinal that does not inject into any of its elements.
This is the Lean-level reading of `SetTheory.IsCardinal.dfn`. -/
def IsCardinal (k : V) : Prop := IsOrdinal k ∧ ∀ a ∈ k, ¬k ≤# a

instance IsCardinal.defined : ℒₛₑₜ-predicate[V] IsCardinal via SetTheory.IsCardinal.dfn :=
  ⟨fun v ↦ by simp [IsCardinal, SetTheory.IsCardinal.dfn]⟩

instance IsCardinal.definable : ℒₛₑₜ-predicate[V] IsCardinal := IsCardinal.defined.to_definable

/-- `k` is regular: every function from an element of `k` into `k` has range
bounded by an element of `k`.  Lean-level reading of `SetTheory.IsRegular.dfn`. -/
def IsRegular (k : V) : Prop := ∀ a ∈ k, ∀ f ∈ (k ^ a : V), ∃ b ∈ k, range f ⊆ b

instance IsRegular.defined : ℒₛₑₜ-predicate[V] IsRegular via SetTheory.IsRegular.dfn :=
  ⟨fun v ↦ by simp [IsRegular, SetTheory.IsRegular.dfn]⟩

instance IsRegular.definable : ℒₛₑₜ-predicate[V] IsRegular := IsRegular.defined.to_definable

/-- `k` is a strong limit: the power set of any element injects into some
element.  Lean-level reading of `SetTheory.IsStrongLimit.dfn`. -/
def IsStrongLimit (k : V) : Prop := ∀ a ∈ k, ∃ b ∈ k, ℘ a ≤# b

instance IsStrongLimit.defined : ℒₛₑₜ-predicate[V] IsStrongLimit via SetTheory.IsStrongLimit.dfn :=
  ⟨fun v ↦ by simp [IsStrongLimit, SetTheory.IsStrongLimit.dfn]⟩

instance IsStrongLimit.definable : ℒₛₑₜ-predicate[V] IsStrongLimit :=
  IsStrongLimit.defined.to_definable

/-- `k` is an inaccessible cardinal: an uncountable regular strong-limit
cardinal.  Lean-level reading of `SetTheory.IsInaccessible.dfn`. -/
def IsInaccessible (k : V) : Prop :=
  IsCardinal k ∧ IsRegular k ∧ IsStrongLimit k ∧ (ω : V) ∈ k

instance IsInaccessible.defined :
    ℒₛₑₜ-predicate[V] IsInaccessible via SetTheory.IsInaccessible.dfn :=
  ⟨fun v ↦ by simp [IsInaccessible, SetTheory.IsInaccessible.dfn]⟩

instance IsInaccessible.definable : ℒₛₑₜ-predicate[V] IsInaccessible :=
  IsInaccessible.defined.to_definable

/-- `InaccChain n x`: below and including `x` there is a strictly
`∈`-descending chain of `n` inaccessible cardinals.  Lean-level reading of
`SetTheory.inaccessibleChain n`. -/
def InaccChain : ℕ → V → Prop
  | 0, _ => True
  | n + 1, x => IsInaccessible x ∧ ∃ y ∈ x, InaccChain n y

instance InaccChain.defined (n : ℕ) :
    ℒₛₑₜ-predicate[V] (InaccChain n) via SetTheory.inaccessibleChain n := by
  induction n with
  | zero => exact ⟨fun v ↦ by simp [InaccChain, SetTheory.inaccessibleChain]⟩
  | succ n _ => exact ⟨fun v ↦ by simp [InaccChain, SetTheory.inaccessibleChain]⟩

instance InaccChain.definable (n : ℕ) : ℒₛₑₜ-predicate[V] (InaccChain n) :=
  (InaccChain.defined n).to_definable

end Predicates

/-! ## Extracting internal inaccessibles from the axiom schema -/

section Schema

/-- A model of `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` is a model of `𝗭𝗙𝗖` (and hence of `𝗭𝗙`, `𝗭`). -/
instance models_zfc_of_models_zfcInacc [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 :=
  models_of_ss inferInstance zfc_subset_zfcInacc

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]

/-- The axiom schema, read inside the model: for each meta-level `n` there is a
set `x` carrying a descending chain of `n` inaccessibles. -/
theorem exists_inaccChain (n : ℕ) : ∃ x : V, InaccChain n x := by
  have h := Theory.models V 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 (ZermeloFraenkelChoiceOmegaInaccessibles.inaccessibles n)
  simpa [models_iff, SetTheory.Axiom.atLeastInaccessibles] using h

end Schema

/-! ### Turning the schema into a chain of internal objects -/

section Chain

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- `κ 0 ∈ κ 1 ∈ … ∈ κ (n-1)` is a strictly `∈`-increasing chain of `n`
inaccessible cardinals of `V`. -/
structure IsInaccessibleChain (n : ℕ) (κ : ℕ → V) : Prop where
  inaccessible : ∀ i < n, IsInaccessible (κ i)
  mem : ∀ i j, i < j → j < n → κ i ∈ κ j

lemma IsInaccessible.isOrdinal {k : V} (h : IsInaccessible k) : IsOrdinal k := h.1.1

lemma IsInaccessible.not_cardLE {k a : V} (h : IsInaccessible k) (ha : a ∈ k) : ¬k ≤# a :=
  h.1.2 a ha

lemma IsInaccessible.regular {k : V} (h : IsInaccessible k) : IsRegular k := h.2.1

lemma IsInaccessible.strongLimit {k : V} (h : IsInaccessible k) : IsStrongLimit k := h.2.2.1

lemma IsInaccessible.omega_mem {k : V} (h : IsInaccessible k) : (ω : V) ∈ k := h.2.2.2

private lemma chain_of_inaccChain (n : ℕ) : ∀ x : V, InaccChain n x →
    ∃ κ : ℕ → V, IsInaccessibleChain n κ ∧ ∀ i < n, κ i ∈ x ∨ κ i = x := by
  induction n with
  | zero =>
    intro x _
    exact ⟨fun _ ↦ ∅, ⟨fun i hi ↦ absurd hi (by omega), fun i j _ hj ↦ absurd hj (by omega)⟩,
      fun i hi ↦ absurd hi (by omega)⟩
  | succ n ih =>
    intro x hx
    obtain ⟨hxi, y, hyx, hy⟩ := hx
    obtain ⟨κ', hκ', hlast⟩ := ih y hy
    have hxo : IsOrdinal x := hxi.isOrdinal
    have hsub : ∀ i < n, κ' i ∈ x := by
      intro i hi
      rcases hlast i hi with h | h
      · exact hxo.transitive y hyx _ h
      · exact h ▸ hyx
    refine ⟨fun i ↦ if i < n then κ' i else x, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      by_cases h : i < n
      · simpa [h] using hκ'.inaccessible i h
      · simpa [h] using hxi
    · intro i j hij hj
      by_cases hjn : j < n
      · have hin : i < n := by omega
        simpa [hin, hjn] using hκ'.mem i j hij hjn
      · have hin : i < n := by omega
        simpa [hin, hjn] using hsub i hin
    · intro i _
      by_cases h : i < n
      · exact Or.inl (by simpa [h] using hsub i h)
      · exact Or.inr (by simp [h])

/-- **The large-cardinal hypothesis, made internal.**  For every meta-level `n`
the model contains a strictly `∈`-increasing chain of `n` inaccessible
cardinals. -/
theorem exists_inaccessibleChain [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] (n : ℕ) :
    ∃ κ : ℕ → V, IsInaccessibleChain n κ := by
  obtain ⟨x, hx⟩ := exists_inaccChain (V := V) n
  obtain ⟨κ, hκ, -⟩ := chain_of_inaccChain n x hx
  exact ⟨κ, hκ⟩

/-- In particular the model contains at least one inaccessible cardinal. -/
theorem exists_inaccessible [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : ∃ k : V, IsInaccessible k := by
  obtain ⟨κ, hκ⟩ := exists_inaccessibleChain (V := V) 1
  exact ⟨κ 0, hκ.inaccessible 0 (by omega)⟩

end Chain

/-! ## Inaccessibles are limit ordinals -/

section Limit

variable [V↓[ℒₛₑₜ] ⊧* 𝗭] {k : V}

/-- For an ordinal `β`, `succ β ⊆ ℘ β`: every element of `succ β` is an ordinal
`≤ β`, hence a subset of `β`. -/
lemma succ_subset_power (β : V) [hβ : IsOrdinal β] : succ β ⊆ ℘ β := by
  intro γ hγ
  rw [mem_power_iff]
  rcases mem_succ_iff.mp hγ with rfl | h
  · exact subset_refl _
  · exact hβ.transitive γ h

/-- **Strong limit + cardinal ⟹ limit ordinal.**  If `β ∈ κ` then `succ β ∈ κ`. -/
lemma IsInaccessible.succ_mem (hk : IsInaccessible k) {β : V} (hβ : β ∈ k) : succ β ∈ k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hβo : IsOrdinal β := IsOrdinal.of_mem hβ
  by_contra hcon
  have hsβ : IsOrdinal (succ β) := IsOrdinal.succ
  have hsub : k ⊆ succ β := by
    rcases IsOrdinal.mem_trichotomy (succ β) k with h | h | h
    · exact absurd h hcon
    · exact subset_of_eq h.symm
    · exact hsβ.transitive _ h
  obtain ⟨b, hb, hpb⟩ := hk.strongLimit β hβ
  refine hk.not_cardLE hb ?_
  exact CardLE.trans (CardLE.trans (cardLE_of_subset hsub)
    (cardLE_of_subset (succ_subset_power β))) hpb

lemma IsInaccessible.empty_mem (hk : IsInaccessible k) : (∅ : V) ∈ k :=
  hk.isOrdinal.transitive _ hk.omega_mem _ empty_mem_ω

end Limit

section LimitOrdinal

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {k : V}

/-- An inaccessible cardinal is a limit ordinal.  Uses `IsCardinal` and
`IsStrongLimit` (via `IsInaccessible.succ_mem`), **not** regularity. -/
lemma IsInaccessible.isLimitOrdinal [IsOrdinal k] (hk : IsInaccessible k) :
    IsLimitOrdinal (IsOrdinal.toOrdinal k : Ordinal V) where
  pos := lt_def.mpr hk.empty_mem
  succ_lt _ hβ := lt_def.mpr (hk.succ_mem (lt_def.mp hβ))

end LimitOrdinal

/-! ## The rank of an ordinal is itself

This identifies the ordinals of `V` sitting inside `Vset κ` with the elements
of `κ`, which is what lets `a ∈ κ` be used as an index set for `Vset κ`.
-/

section RankOrdinal

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankV_of_isOrdinal : ∀ a : V, IsOrdinal a → rankV a = a := by
  apply mem_induction (fun a : V ↦ IsOrdinal a → rankV a = a) (by definability)
  intro a ih ha
  have h1 : a ⊆ Vset (IsOrdinal.toOrdinal a) := by
    intro b hb
    have hbo : IsOrdinal b := IsOrdinal.of_mem hb
    have hrb : rankV b = b := ih b hb hbo
    refine mem_Vset_iff_rank_lt.mpr ?_
    show rankV b ∈ a
    rw [hrb]; exact hb
  have h2 : rankV a ⊆ a := le_def.mp (rank_le_of_subset h1)
  have h3 : rankV a ∉ a := by
    intro hr
    have hro : IsOrdinal (rankV a) := IsOrdinal.of_mem hr
    have hrr : rankV (rankV a) = rankV a := ih _ hr hro
    have hmem : rankV a ∈ Vset (rank a) := subset_Vset_rank a _ hr
    have hlt := mem_Vset_iff_rank_lt.mp hmem
    simp only [lt_def, rank_val, hrr] at hlt
    exact mem_irrefl _ hlt
  rcases IsOrdinal.subset_iff.mp h2 with h | h
  · exact h
  · exact absurd h h3

@[simp] theorem rank_toOrdinal (a : V) [IsOrdinal a] :
    rank a = (IsOrdinal.toOrdinal a : Ordinal V) :=
  Ordinal.ext (rankV_of_isOrdinal a inferInstance)

/-- An element of an ordinal `k` is a member of the stage `Vset k`. -/
theorem mem_vsetV_of_mem {k a : V} [IsOrdinal k] (ha : a ∈ k) : a ∈ vsetV k := by
  have hao : IsOrdinal a := IsOrdinal.of_mem ha
  show a ∈ Vset (IsOrdinal.toOrdinal k)
  refine mem_Vset_iff_rank_lt.mpr ?_
  rw [rank_toOrdinal]
  exact lt_def.mpr ha

end RankOrdinal

/-! ## Dependent products and sums of an internal family

An *internal family* is a set `B` (a function in the sense of
`SetTheory.Function`); `B ‘ x` is its value at `x`.  Both `Σ` and `Π` land in
`Vset α` as soon as `α` is a **limit** ordinal: no regularity, no
strong-limitness, no large cardinal.  The large-cardinal hypothesis is needed
only when the family is given *externally*, by a definable function — see the
section on regularity below.
-/

section PiSigma

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem range_mem_Vset {α : Ordinal V} {B : V} (hB : B ∈ Vset α) : range B ∈ Vset α := by
  refine mem_Vset_of_subset_of_mem (fun y hy ↦ ?_) (sUnion_mem_Vset (sUnion_mem_Vset hB))
  obtain ⟨x, hx⟩ := mem_range_iff.mp hy
  exact mem_sUnion_sUnion_of_kpair_mem_right hx

theorem domain_mem_Vset {α : Ordinal V} {B : V} (hB : B ∈ Vset α) : domain B ∈ Vset α := by
  refine mem_Vset_of_subset_of_mem (fun y hy ↦ ?_) (sUnion_mem_Vset (sUnion_mem_Vset hB))
  obtain ⟨x, hx⟩ := mem_domain_iff.mp hy
  exact mem_sUnion_sUnion_of_kpair_mem_left hx

/-- `⋃_{x} B ‘ x`, the union of all values of the internal family `B`. -/
noncomputable def famUnion (B : V) : V := ⋃ˢ (range B)

theorem famUnion_mem_Vset {α : Ordinal V} {B : V} (hB : B ∈ Vset α) : famUnion B ∈ Vset α :=
  sUnion_mem_Vset (range_mem_Vset hB)

lemma value_subset_famUnion (B x : V) : B ‘ x ⊆ famUnion B := by
  intro z hz
  have h : z ∈ ⋃ˢ (range B) ∧ ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ B := by simpa [value] using hz
  exact h.1

/-- The dependent sum `Σ_{x ∈ A} B ‘ x`. -/
noncomputable def Sigma (A B : V) : V :=
  {p ∈ A ×ˢ famUnion B ; ∃ x ∈ A, ∃ y, p = ⟨x, y⟩ₖ ∧ y ∈ B ‘ x}

lemma mem_Sigma_iff {A B p : V} :
    p ∈ Sigma A B ↔ ∃ x ∈ A, ∃ y, p = ⟨x, y⟩ₖ ∧ y ∈ B ‘ x := by
  suffices ∀ x ∈ A, ∀ y, p = ⟨x, y⟩ₖ → y ∈ B ‘ x → p ∈ A ×ˢ famUnion B by simpa [Sigma]
  rintro x hx y rfl hy
  exact kpair_mem_iff.mpr ⟨hx, value_subset_famUnion B x y hy⟩

/-- The dependent product `Π_{x ∈ A} B ‘ x`: functions on `A` whose value at
`x` lies in `B ‘ x`. -/
noncomputable def Pi (A B : V) : V :=
  {f ∈ ((famUnion B) ^ A : V) ; ∀ x ∈ A, ∀ y : V, ⟨x, y⟩ₖ ∈ f → y ∈ B ‘ x}

lemma mem_Pi_iff {A B f : V} :
    f ∈ Pi A B ↔ f ∈ ((famUnion B) ^ A : V) ∧ ∀ x ∈ A, ∀ y : V, ⟨x, y⟩ₖ ∈ f → y ∈ B ‘ x :=
  mem_sep_iff

/-- **Σ-closure of a limit stage.**  Needs only `IsLimitOrdinal α`. -/
theorem sigma_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {A B : V}
    (hA : A ∈ Vset α) (hB : B ∈ Vset α) : Sigma A B ∈ Vset α := by
  refine mem_Vset_of_subset_of_mem ?_ (prod_mem_Vset h hA (famUnion_mem_Vset hB))
  exact sep_subset

/-- **Π-closure of a limit stage.**  Needs only `IsLimitOrdinal α`; the internal
family `B` is itself a member of `Vset α`, so its values are already bounded. -/
theorem pi_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {A B : V}
    (hA : A ∈ Vset α) (hB : B ∈ Vset α) : Pi A B ∈ Vset α := by
  refine mem_Vset_of_subset_of_mem ?_ (function_mem_Vset h hA (famUnion_mem_Vset hB))
  exact sep_subset

end PiSigma

/-! ## Least fixed points

For a **definable monotone** operator `Φ` mapping `℘ d` into itself, the least
fixed point exists by Knaster–Tarski (an intersection, hence pure separation)
and stays inside `Vset α` whenever `d` does.  This needs *no* hypothesis on `α`
whatsoever — in particular no inaccessibility and not even limit-ness.  It is
the interpretation of an inductive type as a least fixed point of a monotone
operator, and `acc` below is the accessibility predicate.
-/

section Lfp

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `Φ` is monotone and sends `℘ d` into `℘ d`. -/
structure IsMonotoneOn (d : V) (Φ : V → V) : Prop where
  mono : ∀ S T : V, S ⊆ T → Φ S ⊆ Φ T
  maps : Φ d ⊆ d

/-- The set of `Φ`-pre-fixed points contained in `d`. -/
noncomputable def prefixedPoints (d : V) (Φ : V → V)
    (hΦ : ℒₛₑₜ-function₁ Φ := by definability) : V := {S ∈ ℘ d ; Φ S ⊆ S}

lemma mem_prefixedPoints_iff {d S : V} {Φ : V → V} {hΦ : ℒₛₑₜ-function₁ Φ} :
    S ∈ prefixedPoints d Φ hΦ ↔ S ⊆ d ∧ Φ S ⊆ S := by simp [prefixedPoints]

/-- The least fixed point of `Φ` below `d`. -/
noncomputable def lfp (d : V) (Φ : V → V) (hΦ : ℒₛₑₜ-function₁ Φ := by definability) : V :=
  ⋂ˢ (prefixedPoints d Φ hΦ)

variable {d : V} {Φ : V → V} {hΦ : ℒₛₑₜ-function₁ Φ}

lemma self_mem_prefixedPoints (h : IsMonotoneOn d Φ) : d ∈ prefixedPoints d Φ hΦ :=
  mem_prefixedPoints_iff.mpr ⟨subset_refl d, h.maps⟩

lemma lfp_subset_of_prefixed (h : IsMonotoneOn d Φ) {S : V} (hSd : S ⊆ d) (hS : Φ S ⊆ S) :
    lfp d Φ hΦ ⊆ S := by
  have : IsNonempty (prefixedPoints d Φ hΦ) := ⟨d, self_mem_prefixedPoints h⟩
  exact sInter_subset_of_mem_of_nonempty (mem_prefixedPoints_iff.mpr ⟨hSd, hS⟩)

lemma lfp_subset (h : IsMonotoneOn d Φ) : lfp d Φ hΦ ⊆ d :=
  lfp_subset_of_prefixed h (subset_refl d) h.maps

lemma apply_lfp_subset (h : IsMonotoneOn d Φ) : Φ (lfp d Φ hΦ) ⊆ lfp d Φ hΦ := by
  have hne : IsNonempty (prefixedPoints d Φ hΦ) := ⟨d, self_mem_prefixedPoints h⟩
  show Φ (lfp d Φ hΦ) ⊆ ⋂ˢ (prefixedPoints d Φ hΦ)
  refine subset_sInter_iff_of_nonempty.mpr fun S hS ↦ ?_
  obtain ⟨hSd, hSΦ⟩ := mem_prefixedPoints_iff.mp hS
  exact subset_trans (h.mono _ _ (lfp_subset_of_prefixed h hSd hSΦ)) hSΦ

lemma lfp_subset_apply (h : IsMonotoneOn d Φ) : lfp d Φ hΦ ⊆ Φ (lfp d Φ hΦ) :=
  lfp_subset_of_prefixed h (subset_trans (apply_lfp_subset h) (lfp_subset h))
    (h.mono _ _ (apply_lfp_subset h))

/-- **Knaster–Tarski.** `lfp d Φ` is a fixed point of `Φ`. -/
theorem apply_lfp (h : IsMonotoneOn d Φ) : Φ (lfp d Φ hΦ) = lfp d Φ hΦ :=
  subset_antisymm (apply_lfp_subset h) (lfp_subset_apply h)

/-- **Least fixed points stay in the stage.**  No hypothesis on `α` at all. -/
theorem lfp_mem_Vset {α : Ordinal V} (h : IsMonotoneOn d Φ) (hd : d ∈ Vset α) :
    lfp d Φ hΦ ∈ Vset α := mem_Vset_of_subset_of_mem (lfp_subset h) hd

end Lfp

/-! ### The accessible part of a relation -/

section Acc

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- One step of the accessibility operator for the relation `R` on `A`:
`x` is added once all its `R`-predecessors in `A` are present. -/
noncomputable def accStep (A R S : V) : V := {x ∈ A ; ∀ y ∈ A, ⟨y, x⟩ₖ ∈ R → y ∈ S}

lemma mem_accStep_iff {A R S x : V} :
    x ∈ accStep A R S ↔ x ∈ A ∧ ∀ y ∈ A, ⟨y, x⟩ₖ ∈ R → y ∈ S := mem_sep_iff

lemma accStep_definable (A R : V) : ℒₛₑₜ-function₁[V] (accStep A R) := by
  suffices ℒₛₑₜ-relation[V] (fun T S ↦ T = accStep A R S) by exact this
  have e : ∀ T S : V, T = accStep A R S ↔
      ∀ z, z ∈ T ↔ z ∈ A ∧ ∀ y ∈ A, ⟨y, z⟩ₖ ∈ R → y ∈ S := by
    intro T S
    rw [mem_ext_iff]
    simp [accStep]
  simp only [e]
  definability

lemma accStep_isMonotoneOn (A R : V) : IsMonotoneOn A (accStep A R) where
  mono S T hST x hx := by
    rw [mem_accStep_iff] at hx ⊢
    exact ⟨hx.1, fun y hy hR ↦ hST _ (hx.2 y hy hR)⟩
  maps := sep_subset

/-- The accessible part of the relation `R` on the set `A`. -/
noncomputable def acc (A R : V) : V := lfp A (accStep A R) (accStep_definable A R)

theorem acc_subset (A R : V) : acc A R ⊆ A := lfp_subset (accStep_isMonotoneOn A R)

/-- The `ι`-rule for `acc`: it is the fixed point of its defining operator. -/
theorem mem_acc_iff {A R x : V} :
    x ∈ acc A R ↔ x ∈ A ∧ ∀ y ∈ A, ⟨y, x⟩ₖ ∈ R → y ∈ acc A R := by
  have h : accStep A R (acc A R) = acc A R := apply_lfp (accStep_isMonotoneOn A R)
  conv_lhs => rw [← h]
  exact mem_accStep_iff

/-- The recursor for `acc`: well-founded induction along `R`. -/
theorem acc_induction {A R S : V} (hSA : S ⊆ A)
    (hS : ∀ x ∈ A, (∀ y ∈ A, ⟨y, x⟩ₖ ∈ R → y ∈ S) → x ∈ S) : acc A R ⊆ S :=
  lfp_subset_of_prefixed (accStep_isMonotoneOn A R) hSA fun x hx ↦ by
    rw [mem_accStep_iff] at hx
    exact hS x hx.1 hx.2

theorem acc_mem_Vset {α : Ordinal V} {A R : V} (hA : A ∈ Vset α) : acc A R ∈ Vset α :=
  lfp_mem_Vset (accStep_isMonotoneOn A R) hA

end Acc

/-! ## Where the large cardinal is spent: regularity and replacement

Everything above needed at most that `κ` be a limit ordinal.  The genuinely
large-cardinal content is **replacement**: if a family is given *externally*, by
a definable function `F` on an index set `a ∈ κ`, the values `F x` may a priori
have ranks cofinal in `κ`.  Regularity of `κ` rules this out.
-/

section Regularity

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {k : V}

lemma mem_vsetV_iff_mem_Vset {k z : V} [IsOrdinal k] :
    z ∈ vsetV k ↔ z ∈ Vset (IsOrdinal.toOrdinal k) := Iff.rfl

/-- **The regularity step.**  If `a ∈ κ` and `F` is a definable function taking
each element of `a` into `Vset κ`, then the ranks of the values `F x` are
uniformly bounded by a single `b ∈ κ`.  This is the *only* place `IsRegular` is
used. -/
theorem exists_rank_bound_of_regular (hk : IsInaccessible k) {a : V} (ha : a ∈ k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFa : ∀ x ∈ a, F x ∈ vsetV k) :
    ∃ b ∈ k, ∀ x ∈ a, F x ⊆ vsetV b := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hrk : ∀ x ∈ a, rankV (F x) ∈ k := by
    intro x hx
    have h1 : rank (F x) < (IsOrdinal.toOrdinal k : Ordinal V) :=
      mem_Vset_iff_rank_lt.mp (mem_vsetV_iff_mem_Vset.mp (hFa x hx))
    have h2 : (rank (F x)).val ∈ (IsOrdinal.toOrdinal k : Ordinal V).val := lt_def.mp h1
    exact h2
  have hgdef : ℒₛₑₜ-function₁[V] (fun x ↦ rankV (F x)) := by definability
  -- the internal function `x ↦ rank (F x)` from `a` to `k`
  obtain ⟨g, hmemg⟩ : ∃ g : V, ∀ p : V, p ∈ g ↔ ∃ x ∈ a, p = ⟨x, rankV (F x)⟩ₖ := by
    refine ⟨sep (a ×ˢ k) (fun p ↦ ∃ x ∈ a, p = ⟨x, rankV (F x)⟩ₖ), fun p ↦ ?_⟩
    rw [mem_sep_iff]
    refine ⟨fun h ↦ h.2, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨kpair_mem_iff.mpr ⟨hx, hrk x hx⟩, x, hx, rfl⟩
  have hkpair : ∀ x y : V, ⟨x, y⟩ₖ ∈ g ↔ x ∈ a ∧ y = rankV (F x) := by
    intro x y
    rw [hmemg]
    refine ⟨?_, ?_⟩
    · rintro ⟨x', hx', he⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj he
      exact ⟨hx', rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hg : g ∈ (k ^ a : V) := by
    refine mem_function.intro (fun p hp ↦ ?_) (fun x hx ↦ ?_)
    · obtain ⟨x, hx, rfl⟩ := (hmemg p).mp hp
      exact kpair_mem_iff.mpr ⟨hx, hrk x hx⟩
    · exact ExistsUnique.intro (rankV (F x)) ((hkpair x _).mpr ⟨hx, rfl⟩)
        fun y hy ↦ ((hkpair x y).mp hy).2
  obtain ⟨b, hb, hrange⟩ := hk.regular a ha g hg
  have hbo : IsOrdinal b := IsOrdinal.of_mem hb
  refine ⟨b, hb, fun x hx ↦ ?_⟩
  have hmb : rankV (F x) ∈ b :=
    hrange _ (mem_range_of_kpair_mem ((hkpair x (rankV (F x))).mpr ⟨hx, rfl⟩))
  have hlt : rank (F x) < (IsOrdinal.toOrdinal b : Ordinal V) := lt_def.mpr hmb
  have hsub : F x ⊆ Vset (IsOrdinal.toOrdinal b : Ordinal V) :=
    subset_trans (subset_Vset_rank (F x)) (Vset_mono (le_of_lt hlt))
  exact hsub

/-- **Replacement inside `Vset κ`.**  Uses regularity (through
`exists_rank_bound_of_regular`) and limit-ness. -/
theorem repl_mem_vsetV (hk : IsInaccessible k) {a : V} (ha : a ∈ k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFa : ∀ x ∈ a, F x ∈ vsetV k) :
    repl F hF a ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  obtain ⟨b, hb, hbound⟩ := exists_rank_bound_of_regular hk ha F hF hFa
  have hbo : IsOrdinal b := IsOrdinal.of_mem hb
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_iff.mpr ⟨(IsOrdinal.toOrdinal b : Ordinal V).succ,
    hk.isLimitOrdinal.succ_lt _ (lt_def.mpr hb), fun z hz ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := (repl_spec hF).mp hz
  exact mem_Vset_succ_iff.mpr (hbound x hx)

/-- The union of a `κ`-small definable family stays inside `Vset κ`. -/
theorem sUnion_repl_mem_vsetV (hk : IsInaccessible k) {a : V} (ha : a ∈ k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFa : ∀ x ∈ a, F x ∈ vsetV k) :
    ⋃ˢ (repl F hF a) ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  exact sUnion_mem_Vset (mem_vsetV_iff_mem_Vset.mp (repl_mem_vsetV hk ha F hF hFa))

end Regularity

/-! ### Dependent products and sums of an externally given family -/

section PiSigmaFun

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {k : V}

/-- `Σ_{x ∈ A} B x` for a definable family `B : V → V`. -/
noncomputable def SigmaFun (A : V) (B : V → V) (hB : ℒₛₑₜ-function₁ B := by definability) : V :=
  {p ∈ A ×ˢ (⋃ˢ (repl B hB A)) ; ∃ x ∈ A, ∃ y ∈ B x, p = ⟨x, y⟩ₖ}

lemma mem_SigmaFun_iff {A p : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    p ∈ SigmaFun A B hB ↔ ∃ x ∈ A, ∃ y ∈ B x, p = ⟨x, y⟩ₖ := by
  suffices ∀ x ∈ A, ∀ y ∈ B x, p = ⟨x, y⟩ₖ → p ∈ A ×ˢ (⋃ˢ (repl B hB A)) by
    simpa [SigmaFun] using this
  rintro x hx y hy rfl
  exact kpair_mem_iff.mpr
    ⟨hx, subset_sUnion_of_mem ((repl_spec hB).mpr ⟨x, hx, rfl⟩) y hy⟩

/-- `Π_{x ∈ A} B x` for a definable family `B : V → V`. -/
noncomputable def PiFun (A : V) (B : V → V) (hB : ℒₛₑₜ-function₁ B := by definability) : V :=
  {f ∈ ((⋃ˢ (repl B hB A)) ^ A : V) ; ∀ x ∈ A, ∀ y : V, ⟨x, y⟩ₖ ∈ f → y ∈ B x}

lemma mem_PiFun_iff {A f : V} {B : V → V} {hB : ℒₛₑₜ-function₁ B} :
    f ∈ PiFun A B hB ↔ f ∈ ((⋃ˢ (repl B hB A)) ^ A : V) ∧
      ∀ x ∈ A, ∀ y : V, ⟨x, y⟩ₖ ∈ f → y ∈ B x := mem_sep_iff

/-- **Σ-closure of `Vset κ` for a definable family over an index set `a ∈ κ`.**
Uses regularity (via `repl_mem_vsetV`) and limit-ness. -/
theorem sigmaFun_mem_vsetV (hk : IsInaccessible k) {a : V} (ha : a ∈ k)
    (B : V → V) (hB : ℒₛₑₜ-function₁ B) (hBa : ∀ x ∈ a, B x ∈ vsetV k) :
    SigmaFun a B hB ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_of_subset_of_mem sep_subset (prod_mem_Vset hk.isLimitOrdinal ?_ ?_)
  · exact mem_vsetV_iff_mem_Vset.mp (mem_vsetV_of_mem ha)
  · exact mem_vsetV_iff_mem_Vset.mp (sUnion_repl_mem_vsetV hk ha B hB hBa)

/-- **Π-closure of `Vset κ` for a definable family over an index set `a ∈ κ`.**
Uses regularity (via `repl_mem_vsetV`) and limit-ness. -/
theorem piFun_mem_vsetV (hk : IsInaccessible k) {a : V} (ha : a ∈ k)
    (B : V → V) (hB : ℒₛₑₜ-function₁ B) (hBa : ∀ x ∈ a, B x ∈ vsetV k) :
    PiFun a B hB ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_of_subset_of_mem sep_subset (function_mem_Vset hk.isLimitOrdinal ?_ ?_)
  · exact mem_vsetV_iff_mem_Vset.mp (mem_vsetV_of_mem ha)
  · exact mem_vsetV_iff_mem_Vset.mp (sUnion_repl_mem_vsetV hk ha B hB hBa)

end PiSigmaFun

/-! ## Disjoint unions and quotients need only limit-ness

Per Carneiro, `+` and quotients are "free": they are interpreted inside any
limit stage, with no appeal to the large cardinal.  Concretely they are built
from the `Rank.lean` closure lemmas `singleton_mem_Vset`, `prod_mem_Vset`,
`union_mem_Vset`, `power_mem_Vset` and `sep_mem_Vset`, all of which have
`IsLimitOrdinal α` as their only hypothesis (`sUnion_mem_Vset` needs not even
that).
-/

section Free

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {α : Ordinal V} {A B R : V}

theorem empty_mem_Vset (h : IsLimitOrdinal α) : (∅ : V) ∈ Vset α := by
  refine mem_Vset_iff_rank_lt.mpr ?_
  rw [rank_toOrdinal]
  exact h.pos

theorem zero_mem_Vset (h : IsLimitOrdinal α) : (0 : V) ∈ Vset α := empty_mem_Vset h

theorem one_mem_Vset (h : IsLimitOrdinal α) : (1 : V) ∈ Vset α := by
  have hs : (1 : V) = succ (∅ : V) := rfl
  have hmem : succ (∅ : V) ∈ α.val := lt_def.mp (h.succ_lt ⊥ h.pos)
  have _ : IsOrdinal (succ (∅ : V)) := IsOrdinal.succ
  rw [hs]
  refine mem_Vset_iff_rank_lt.mpr ?_
  rw [rank_toOrdinal]
  exact lt_def.mpr hmem

/-- Binary disjoint union, tagged by `0` and `1`. -/
noncomputable def disjUnion (A B : V) : V := (({0} : V) ×ˢ A) ∪ (({1} : V) ×ˢ B)

lemma mem_disjUnion_iff {p : V} :
    p ∈ disjUnion A B ↔ (∃ y ∈ A, p = ⟨0, y⟩ₖ) ∨ (∃ y ∈ B, p = ⟨1, y⟩ₖ) := by
  simp [disjUnion, mem_prod_iff]

/-- **Disjoint unions live in every limit stage.** -/
theorem disjUnion_mem_Vset (h : IsLimitOrdinal α) (hA : A ∈ Vset α) (hB : B ∈ Vset α) :
    disjUnion A B ∈ Vset α :=
  union_mem_Vset h
    (prod_mem_Vset h (singleton_mem_Vset h (zero_mem_Vset h)) hA)
    (prod_mem_Vset h (singleton_mem_Vset h (one_mem_Vset h)) hB)

/-- The `R`-class of `x` inside `A`. -/
noncomputable def eqvClass (A R x : V) : V := {y ∈ A ; ⟨x, y⟩ₖ ∈ R}

lemma mem_eqvClass_iff {x y : V} : y ∈ eqvClass A R x ↔ y ∈ A ∧ ⟨x, y⟩ₖ ∈ R := mem_sep_iff

instance eqvClass.definable (A R : V) : ℒₛₑₜ-function₁[V] (eqvClass A R) := by
  suffices ℒₛₑₜ-relation[V] (fun c x ↦ c = eqvClass A R x) by exact this
  have e : ∀ c x : V, c = eqvClass A R x ↔ ∀ z, z ∈ c ↔ z ∈ A ∧ ⟨x, z⟩ₖ ∈ R := by
    intro c x
    rw [mem_ext_iff]
    simp [eqvClass]
  simp only [e]
  definability

/-- The quotient of `A` by the relation `R`, as the set of `R`-classes. -/
noncomputable def setQuotient (A R : V) : V := {c ∈ ℘ A ; ∃ x ∈ A, c = eqvClass A R x}

lemma mem_setQuotient_iff {c : V} :
    c ∈ setQuotient A R ↔ ∃ x ∈ A, c = eqvClass A R x := by
  suffices ∀ x ∈ A, c = eqvClass A R x → c ∈ ℘ A by simpa [setQuotient] using this
  rintro x _ rfl
  exact mem_power_iff.mpr sep_subset

/-- **Quotients live in every limit stage.** -/
theorem setQuotient_mem_Vset (h : IsLimitOrdinal α) (hA : A ∈ Vset α) :
    setQuotient A R ∈ Vset α :=
  mem_Vset_of_subset_of_mem sep_subset (power_mem_Vset h hA)

end Free

end Lean4Lean.SetModel
