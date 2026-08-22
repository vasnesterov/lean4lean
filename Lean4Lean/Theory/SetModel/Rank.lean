import Foundation.FirstOrder.SetTheory.Recursion

/-!
# The cumulative hierarchy and rank, inside a model of ZF

This file develops, *internally to an arbitrary model* `V` of first-order `𝗭𝗙`,
the von Neumann cumulative hierarchy `Vset : Ordinal V → V` and the rank
function `rank : V → Ordinal V`.

Everything is phrased in Foundation's idiom for internal set theory:

```
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
```

so that `x ∈ y` is the model's membership relation, and each definition that is
fed to separation or replacement carries a definability instance.

## Main definitions

* `transrec F` — transfinite recursion packaged as a function `V → V`,
  built from Foundation's `IsAttempt` / `attemptOrEmpty` machinery.
* `Vset α` — the cumulative hierarchy.
* `tc a` — the transitive closure of `{a}`, used to derive `∈`-induction from
  the axiom of foundation.
* `rank x` — the least ordinal `α` with `x ⊆ Vset α`.
* `IsLimitOrdinal α` — `α` is a limit ordinal (Foundation has no such notion).

## Main results

* `Vset_bot`, `Vset_succ`, `Vset_limit` — the three defining equations.
* `mem_Vset_iff` — the workhorse: `z ∈ Vset α ↔ ∃ β < α, z ⊆ Vset β`.
* `Vset_mono`, `isTransitive_Vset`, `Vset_mem_Vset_succ`.
* `mem_induction` — `∈`-induction for definable predicates.
* `hasRank` — every set has a rank.
* `mem_Vset_iff_rank_lt`, `rank_lt_of_mem`.
* `doubleton_mem_Vset`, `sUnion_mem_Vset`, `power_mem_Vset` — closure of
  `Vset α` under pairing, union and power set; also `sep_mem_Vset`,
  `kpair_mem_Vset`, `prod_mem_Vset`, `function_mem_Vset`.  Everything except
  union needs `α` to be a limit ordinal; nothing needs a large cardinal.

## Implementation notes

The development lives in `Lean4Lean.SetModel` rather than inside
`LO.FirstOrder.SetTheory`: Foundation is a pinned dependency that we may not
edit, so keeping our additions in our own namespace avoids any risk of clashing
with future upstream names. `open LO.FirstOrder.SetTheory` activates the scoped
instances (`∅`, `{·}`, `insert`, `∪`, `⊆`, …) that the idiom needs, and
instance resolution for the definability side conditions works unchanged.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ## Ordinal arithmetic missing from Foundation -/

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

section OrdinalLemmas

variable {α β : Ordinal V}

lemma succ_le_of_lt (h : β < α) : β.succ ≤ α := by
  have hβα : β.val ∈ α.val := lt_def.mp h
  refine le_def.mpr fun z hz ↦ ?_
  rcases mem_succ_iff.mp hz with rfl | hz
  · exact hβα
  · exact α.ordinal.transitive _ hβα _ hz

lemma le_of_lt_succ (h : β < α.succ) : β ≤ α := by
  rcases mem_succ_iff.mp (lt_def.mp h) with h' | h'
  · exact le_of_eq (Ordinal.ext h')
  · exact le_of_lt (lt_def.mpr h')

lemma succ_lt_omega (h : β < Ordinal.ω) : β.succ < (Ordinal.ω : Ordinal V) :=
  lt_def.mpr (ω_succ_closed (lt_def.mp h))

lemma bot_lt_omega : (⊥ : Ordinal V) < Ordinal.ω := lt_def.mpr empty_mem_ω

end OrdinalLemmas

/-- `α` is a limit ordinal. Foundation defines no such notion. -/
structure IsLimitOrdinal (α : Ordinal V) : Prop where
  pos : ⊥ < α
  succ_lt : ∀ β < α, β.succ < α

theorem isLimitOrdinal_omega : IsLimitOrdinal (Ordinal.ω : Ordinal V) :=
  ⟨bot_lt_omega, fun _ h ↦ succ_lt_omega h⟩

/-! ## Transfinite recursion, packaged as a function

Foundation's `Recursion.lean` produces, for each ordinal `α`, an *attempt*
function of length `α`; `attemptOrEmpty F α` is the (unique) such attempt.
The value of the recursion at `α` is then `F` applied to that attempt.
This section packages that up and proves the recursion equation in the form we
need: the range of the attempt of length `α` is exactly the set of values at
ordinals `< α`.
-/

open Classical in
/-- The transfinite recursion on `F`: `transrec F α = F ⟨transrec F β | β < α⟩`. -/
noncomputable def transrec (F : V → V) (a : V) : V := F (attemptOrEmpty F a)

open Classical in
/-- `attemptOrEmpty F` is a definable function. (Foundation proves this inline
inside `Replacement.replAttemptOrEmpty` but does not export it.) -/
lemma attemptOrEmpty_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₁[V] (attemptOrEmpty F) := by
  suffices ℒₛₑₜ-relation[V] (· = attemptOrEmpty F ·) by exact this
  simp only [attemptOrEmpty, Classical.choose!_eq_iff_right]
  unfold IsAttempt.Exists
  have : ℒₛₑₜ-relation (IsAttempt F) := IsAttempt.definable hF
  definability

lemma transrec_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₁[V] (transrec F) := by
  have := attemptOrEmpty_definable F hF
  unfold transrec
  definability

lemma isAttempt_attemptOrEmpty (F : V → V) (hF : ℒₛₑₜ-function₁ F) (α : Ordinal V) :
    IsAttempt F α.val (attemptOrEmpty F α.val) := by
  have hex : IsAttempt.Exists F α.val := Replacement.attempt_function_exists F hF α
  have h : (IsAttempt.Exists F α.val ∧ IsAttempt F α.val (attemptOrEmpty F α.val)) ∨
      (¬IsAttempt.Exists F α.val ∧ attemptOrEmpty F α.val = ∅) :=
    Classical.choose!_spec (attemptOrEmpty_existsUnique F α.val)
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hex h

lemma attemptOrEmpty_restrict (F : V → V) (hF : ℒₛₑₜ-function₁ F) {α β : Ordinal V}
    (h : β ≤ α) : (attemptOrEmpty F α.val) ↾ β.val = attemptOrEmpty F β.val := by
  have hf := isAttempt_attemptOrEmpty F hF α
  have hg := isAttempt_attemptOrEmpty F hF β
  have hf' : IsFunction (attemptOrEmpty F α.val) := hf.2.1
  have hg' : IsFunction (attemptOrEmpty F β.val) := hg.2.1
  exact IsAttempt.isAttempt_restrict_eq_of_le F h hf hg

/-- The recursion equation, in the form "the attempt of length `α` enumerates
exactly the values at ordinals `< α`". -/
lemma mem_range_attemptOrEmpty (F : V → V) (hF : ℒₛₑₜ-function₁ F) {α : Ordinal V} {y : V} :
    y ∈ range (attemptOrEmpty F α.val) ↔ ∃ β : Ordinal V, β < α ∧ y = transrec F β.val := by
  obtain ⟨hα, hfun, hdom, hspec⟩ := isAttempt_attemptOrEmpty F hF α
  constructor
  · intro hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    have hxα : x ∈ α.val := hdom ▸ mem_domain_of_kpair_mem hxy
    have hxo : IsOrdinal x := IsOrdinal.of_mem hxα
    refine ⟨IsOrdinal.toOrdinal x, hxα, ?_⟩
    have hval := (hspec x hxα y).mp hxy
    have hle : (IsOrdinal.toOrdinal x : Ordinal V) ≤ α :=
      le_def.mpr (α.ordinal.transitive x hxα)
    have hres : (attemptOrEmpty F α.val) ↾ x = attemptOrEmpty F x :=
      attemptOrEmpty_restrict F hF (β := IsOrdinal.toOrdinal x) hle
    rw [hval, hres]
    rfl
  · rintro ⟨β, hβ, rfl⟩
    refine mem_range_of_kpair_mem (x := β.val) ?_
    refine (hspec β.val (lt_def.mp hβ) _).mpr ?_
    rw [attemptOrEmpty_restrict F hF (le_of_lt hβ)]
    rfl

/-! ## The cumulative hierarchy -/

/-- The image of `X` under the power set operation, `{℘ x | x ∈ X}`. -/
noncomputable def powImage (X : V) : V := repl power power.definable X

@[simp] lemma mem_powImage_iff {X y : V} : y ∈ powImage X ↔ ∃ x ∈ X, y = ℘ x :=
  repl_spec power.definable

instance powImage.definable : ℒₛₑₜ-function₁[V] powImage := by
  unfold powImage; definability

/-- One step of the cumulative hierarchy: given the sequence `f` of the stages
already built, the next stage is `⋃ {℘ x | x ∈ range f}`. -/
noncomputable def vsetStep (f : V) : V := ⋃ˢ (powImage (range f))

instance vsetStep.definable : ℒₛₑₜ-function₁[V] vsetStep := by
  unfold vsetStep; definability

/-- The cumulative hierarchy as a function on all of `V` (junk outside the
ordinals). This is the form needed for separation and replacement. -/
noncomputable def vsetV : V → V := transrec vsetStep

instance vsetV.definable : ℒₛₑₜ-function₁[V] vsetV :=
  transrec_definable vsetStep vsetStep.definable

/-- The von Neumann cumulative hierarchy `V_α`. -/
noncomputable def Vset (α : Ordinal V) : V := vsetV α.val

lemma Vset_def (α : Ordinal V) : Vset α = transrec vsetStep α.val := rfl

/-- **The workhorse.** `z ∈ V_α` iff `z ⊆ V_β` for some `β < α`. -/
theorem mem_Vset_iff {α : Ordinal V} {z : V} :
    z ∈ Vset α ↔ ∃ β : Ordinal V, β < α ∧ z ⊆ Vset β := by
  constructor
  · intro hz
    have hz' : z ∈ ⋃ˢ (powImage (range (attemptOrEmpty vsetStep α.val))) := hz
    rw [mem_sUnion_iff] at hz'
    obtain ⟨w, hw, hzw⟩ := hz'
    rw [mem_powImage_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨β, hβ, rfl⟩ := (mem_range_attemptOrEmpty vsetStep vsetStep.definable).mp hu
    exact ⟨β, hβ, mem_power_iff.mp hzw⟩
  · rintro ⟨β, hβ, hz⟩
    show z ∈ ⋃ˢ (powImage (range (attemptOrEmpty vsetStep α.val)))
    rw [mem_sUnion_iff]
    refine ⟨℘ (Vset β), ?_, mem_power_iff.mpr hz⟩
    rw [mem_powImage_iff]
    exact ⟨Vset β, (mem_range_attemptOrEmpty vsetStep vsetStep.definable).mpr ⟨β, hβ, rfl⟩, rfl⟩

/-- The hierarchy is monotone. -/
theorem Vset_mono {α β : Ordinal V} (h : α ≤ β) : Vset α ⊆ Vset β := fun z hz ↦ by
  obtain ⟨γ, hγ, hzγ⟩ := mem_Vset_iff.mp hz
  exact mem_Vset_iff.mpr ⟨γ, lt_of_lt_of_le hγ h, hzγ⟩

/-! ### The three defining equations -/

@[simp] theorem Vset_bot : Vset (⊥ : Ordinal V) = ∅ := by
  ext z
  simp only [not_mem_empty, iff_false]
  intro hz
  obtain ⟨β, hβ, -⟩ := mem_Vset_iff.mp hz
  exact absurd hβ not_lt_bot

theorem Vset_succ (α : Ordinal V) : Vset α.succ = ℘ (Vset α) := by
  ext z
  rw [mem_Vset_iff, mem_power_iff]
  constructor
  · rintro ⟨β, hβ, hz⟩
    exact subset_trans hz (Vset_mono (le_of_lt_succ hβ))
  · intro hz
    exact ⟨α, lt_succ α, hz⟩

/-- `{V_β | β < α}`, as an element of `V`. -/
noncomputable def VsetImage (α : Ordinal V) : V := repl vsetV vsetV.definable α.val

@[simp] lemma mem_VsetImage_iff {α : Ordinal V} {y : V} :
    y ∈ VsetImage α ↔ ∃ β : Ordinal V, β < α ∧ y = Vset β := by
  rw [VsetImage, repl_spec vsetV.definable]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxo : IsOrdinal x := IsOrdinal.of_mem hx
    exact ⟨IsOrdinal.toOrdinal x, hx, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β.val, lt_def.mp hβ, rfl⟩

theorem Vset_limit {α : Ordinal V} (h : IsLimitOrdinal α) :
    Vset α = ⋃ˢ (VsetImage α) := by
  ext z
  rw [mem_sUnion_iff, mem_Vset_iff]
  constructor
  · rintro ⟨β, hβ, hz⟩
    refine ⟨Vset β.succ, mem_VsetImage_iff.mpr ⟨β.succ, h.succ_lt β hβ, rfl⟩, ?_⟩
    exact mem_Vset_iff.mpr ⟨β, lt_succ β, hz⟩
  · rintro ⟨w, hw, hzw⟩
    obtain ⟨β, hβ, rfl⟩ := mem_VsetImage_iff.mp hw
    obtain ⟨γ, hγ, hz⟩ := mem_Vset_iff.mp hzw
    exact ⟨γ, lt_trans hγ hβ, hz⟩

/-! ### Basic properties -/

instance isTransitive_Vset (α : Ordinal V) : IsTransitive (Vset α) := by
  refine ⟨fun x hx y hy ↦ ?_⟩
  obtain ⟨β, hβ, hxβ⟩ := mem_Vset_iff.mp hx
  obtain ⟨γ, hγ, hyγ⟩ := mem_Vset_iff.mp (hxβ y hy)
  exact mem_Vset_iff.mpr ⟨γ, lt_trans hγ hβ, hyγ⟩

theorem mem_Vset_succ_iff {α : Ordinal V} {z : V} : z ∈ Vset α.succ ↔ z ⊆ Vset α := by
  rw [Vset_succ, mem_power_iff]

theorem Vset_mem_Vset_succ (α : Ordinal V) : Vset α ∈ Vset α.succ :=
  mem_Vset_succ_iff.mpr (subset_refl _)

theorem subset_Vset_of_mem_Vset {α : Ordinal V} {z : V} (h : z ∈ Vset α) : z ⊆ Vset α :=
  (isTransitive_Vset α).transitive z h

/-! ## Transitive closure and `∈`-induction

Foundation's `foundation` is the axiom in the "every nonempty set has an
`∈`-minimal element" form; to get `∈`-induction over the whole model we apply it
to the transitive closure of `{a}`, which we build with the same transfinite
recursion machinery: `S_α = {a} ∪ ⋃_{β<α} ⋃ˢ S_β`, and `tc a = S_ω`.
-/

/-- One step of the transitive-closure recursion. -/
noncomputable def tcStep (a f : V) : V := insert a (⋃ˢ (⋃ˢ (range f)))

instance tcStep.definable (a : V) : ℒₛₑₜ-function₁[V] (tcStep a) := by
  unfold tcStep; definability

/-- The `α`-th approximation to the transitive closure of `{a}`. -/
noncomputable def tcSeq (a : V) (α : Ordinal V) : V := transrec (tcStep a) α.val

lemma mem_tcSeq_iff {a : V} {α : Ordinal V} {z : V} :
    z ∈ tcSeq a α ↔ z = a ∨ ∃ β : Ordinal V, β < α ∧ z ∈ ⋃ˢ (tcSeq a β) := by
  show z ∈ insert a (⋃ˢ (⋃ˢ (range (attemptOrEmpty (tcStep a) α.val)))) ↔ _
  rw [mem_insert]
  refine or_congr Iff.rfl ?_
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨u, hu, hzu⟩
    rw [mem_sUnion_iff] at hu
    obtain ⟨w, hw, huw⟩ := hu
    obtain ⟨β, hβ, rfl⟩ := (mem_range_attemptOrEmpty (tcStep a) (tcStep.definable a)).mp hw
    exact ⟨β, hβ, mem_sUnion_iff.mpr ⟨u, huw, hzu⟩⟩
  · rintro ⟨β, hβ, hz⟩
    rw [mem_sUnion_iff] at hz
    obtain ⟨u, hu, hzu⟩ := hz
    refine ⟨u, ?_, hzu⟩
    rw [mem_sUnion_iff]
    exact ⟨tcSeq a β, (mem_range_attemptOrEmpty (tcStep a) (tcStep.definable a)).mpr
      ⟨β, hβ, rfl⟩, hu⟩

lemma self_mem_tcSeq (a : V) (α : Ordinal V) : a ∈ tcSeq a α :=
  mem_tcSeq_iff.mpr (Or.inl rfl)

lemma tcSeq_mono {a : V} {α β : Ordinal V} (h : α ≤ β) : tcSeq a α ⊆ tcSeq a β := by
  intro z hz
  rcases mem_tcSeq_iff.mp hz with rfl | ⟨γ, hγ, hzγ⟩
  · exact self_mem_tcSeq _ _
  · exact mem_tcSeq_iff.mpr (Or.inr ⟨γ, lt_of_lt_of_le hγ h, hzγ⟩)

lemma sUnion_tcSeq_subset {a : V} {α β : Ordinal V} (h : β < α) :
    ⋃ˢ (tcSeq a β) ⊆ tcSeq a α := fun _ hz ↦ mem_tcSeq_iff.mpr (Or.inr ⟨β, h, hz⟩)

/-- The transitive closure of `{a}`. -/
noncomputable def tc (a : V) : V := tcSeq a Ordinal.ω

lemma self_mem_tc (a : V) : a ∈ tc a := self_mem_tcSeq a _

instance isTransitive_tc (a : V) : IsTransitive (tc a) := by
  refine ⟨fun z hz y hy ↦ ?_⟩
  -- first: `z` already lies in `tcSeq a δ` for some `δ < ω`
  have key : ∃ δ : Ordinal V, δ < Ordinal.ω ∧ z ∈ tcSeq a δ := by
    rcases mem_tcSeq_iff.mp hz with rfl | ⟨β, hβ, hzβ⟩
    · exact ⟨⊥, bot_lt_omega, self_mem_tcSeq _ _⟩
    · exact ⟨β.succ, succ_lt_omega hβ,
        sUnion_tcSeq_subset (lt_succ β) z hzβ⟩
  obtain ⟨δ, hδ, hzδ⟩ := key
  have hy' : y ∈ ⋃ˢ (tcSeq a δ) := mem_sUnion_iff.mpr ⟨z, hzδ, hy⟩
  exact tcSeq_mono (le_of_lt (succ_lt_omega hδ)) y
    (sUnion_tcSeq_subset (lt_succ δ) y hy')

/-- **`∈`-induction** for definable predicates, derived from the axiom of
foundation. -/
theorem mem_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ x : V, (∀ y ∈ x, P y) → P x) (x : V) : P x := by
  by_contra hx
  obtain ⟨S, hmem⟩ : ∃ S : V, ∀ z : V, z ∈ S ↔ z ∈ tc x ∧ ¬P z :=
    ⟨sep (tc x) (fun z ↦ ¬P z), fun _ ↦ mem_sep_iff⟩
  have hxS : x ∈ S := (hmem x).mpr ⟨self_mem_tc x, hx⟩
  have hne : IsNonempty S := ⟨x, hxS⟩
  obtain ⟨m, hmS, hmin⟩ := foundation S
  obtain ⟨hmtc, hmP⟩ := (hmem m).mp hmS
  refine hmP (ih m fun y hy ↦ ?_)
  by_contra hPy
  exact hmin y ((hmem y).mpr ⟨(isTransitive_tc x).mem_trans hy hmtc, hPy⟩) hy

/-! ## Rank -/

/-- `IsRankOf x a`: `a` is the least ordinal `α` such that `x ⊆ V_α`. -/
def IsRankOf (x a : V) : Prop :=
  IsOrdinal a ∧ x ⊆ vsetV a ∧ ∀ b : V, IsOrdinal b → x ⊆ vsetV b → a ⊆ b

instance IsRankOf.definable : ℒₛₑₜ-relation[V] IsRankOf := by
  unfold IsRankOf; definability

/-- `x` has a rank. This is the statement proved by `∈`-induction. -/
def HasRank (x : V) : Prop := ∃ a : V, IsOrdinal a ∧ x ⊆ vsetV a

instance HasRank.definable : ℒₛₑₜ-predicate[V] HasRank := by
  unfold HasRank; definability

lemma hasRank_iff {x : V} : HasRank x ↔ ∃ α : Ordinal V, x ⊆ Vset α := by
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨IsOrdinal.toOrdinal a, h⟩
  · rintro ⟨α, h⟩; exact ⟨α.val, α.ordinal, h⟩

lemma isRankOf_existsUnique_of_hasRank {x : V} (h : HasRank x) : ∃! a : V, IsRankOf x a := by
  obtain ⟨α, hα⟩ := hasRank_iff.mp h
  obtain ⟨β, hβ, hmin⟩ :=
    exists_minimal (V := V) (fun a ↦ x ⊆ vsetV a) (by definability) ⟨α, hα⟩
  refine ⟨β.val, ⟨β.ordinal, hβ, ?_⟩, ?_⟩
  · intro b hb hxb
    exact le_def.mp (hmin (IsOrdinal.toOrdinal b) hxb)
  · rintro a ⟨ha, hxa, hle⟩
    exact subset_antisymm (hle β.val β.ordinal hβ)
      (le_def.mp (hmin (IsOrdinal.toOrdinal a) hxa))

/-- **Every set has a rank**: `∀ x, ∃ α, x ⊆ V_α`. -/
theorem hasRank (x : V) : HasRank x := by
  refine mem_induction HasRank inferInstance (fun x ih ↦ ?_) x
  have huniq : ∀ y ∈ x, ∃! a : V, IsRankOf y a :=
    fun y hy ↦ isRankOf_existsUnique_of_hasRank (ih y hy)
  -- by replacement, collect the ranks of the elements of `x`
  obtain ⟨Y, hmemY⟩ : ∃ Y : V, ∀ a : V, a ∈ Y ↔ ∃ y ∈ x, IsRankOf y a :=
    ⟨replRelOverSet x IsRankOf huniq IsRankOf.definable,
      fun _ ↦ replRelOverSet_spec IsRankOf.definable⟩
  have hordY : ∀ a ∈ Y, IsOrdinal a := by
    intro a ha
    obtain ⟨y, -, hr⟩ := (hmemY a).mp ha
    exact hr.1
  have hs : IsOrdinal (⋃ˢ Y) := IsOrdinal.sUnion hordY
  have hsub : x ⊆ Vset (IsOrdinal.toOrdinal (⋃ˢ Y) : Ordinal V).succ := by
    intro y hy
    obtain ⟨a, ha⟩ := (huniq y hy).exists
    have hao : IsOrdinal a := ha.1
    have haY : a ∈ Y := (hmemY a).mpr ⟨y, hy, ha⟩
    have hle : (IsOrdinal.toOrdinal a : Ordinal V) ≤ IsOrdinal.toOrdinal (⋃ˢ Y) :=
      le_def.mpr (subset_sUnion_of_mem haY)
    have hy1 : y ⊆ Vset (IsOrdinal.toOrdinal a : Ordinal V) := ha.2.1
    have hy2 : y ⊆ Vset (IsOrdinal.toOrdinal (⋃ˢ Y) : Ordinal V) :=
      subset_trans hy1 (Vset_mono hle)
    exact mem_Vset_iff.mpr ⟨IsOrdinal.toOrdinal (⋃ˢ Y), lt_succ _, hy2⟩
  exact hasRank_iff.mpr ⟨_, hsub⟩

lemma isRankOf_existsUnique (x : V) : ∃! a : V, IsRankOf x a :=
  isRankOf_existsUnique_of_hasRank (hasRank x)

open Classical in
/-- The rank of `x`, as an element of `V`. -/
noncomputable def rankV (x : V) : V := Classical.choose! (isRankOf_existsUnique x)

lemma isRankOf_rankV (x : V) : IsRankOf x (rankV x) :=
  Classical.choose!_spec (isRankOf_existsUnique x)

instance isOrdinal_rankV (x : V) : IsOrdinal (rankV x) := (isRankOf_rankV x).1

instance rankV.definable : ℒₛₑₜ-function₁[V] rankV := by
  suffices ℒₛₑₜ-relation[V] (· = rankV ·) by exact this
  simp only [rankV, Classical.choose!_eq_iff_right]
  definability

/-- **The rank of `x`**: the least ordinal `α` with `x ⊆ V_α`. -/
noncomputable def rank (x : V) : Ordinal V := IsOrdinal.toOrdinal (rankV x)

@[simp] lemma rank_val (x : V) : (rank x).val = rankV x := rfl

theorem subset_Vset_rank (x : V) : x ⊆ Vset (rank x) := (isRankOf_rankV x).2.1

theorem rank_le_of_subset {x : V} {α : Ordinal V} (h : x ⊆ Vset α) : rank x ≤ α :=
  le_def.mpr ((isRankOf_rankV x).2.2 α.val α.ordinal h)

theorem subset_Vset_iff_rank_le {x : V} {α : Ordinal V} : x ⊆ Vset α ↔ rank x ≤ α :=
  ⟨rank_le_of_subset, fun h ↦ subset_trans (subset_Vset_rank x) (Vset_mono h)⟩

/-- **`x ∈ V_α` iff `rank x < α`.** -/
theorem mem_Vset_iff_rank_lt {x : V} {α : Ordinal V} : x ∈ Vset α ↔ rank x < α := by
  rw [mem_Vset_iff]
  constructor
  · rintro ⟨β, hβ, hx⟩
    exact lt_of_le_of_lt (rank_le_of_subset hx) hβ
  · intro h
    exact ⟨rank x, h, subset_Vset_rank x⟩

theorem mem_Vset_rank_succ (x : V) : x ∈ Vset (rank x).succ :=
  mem_Vset_iff_rank_lt.mpr (lt_succ _)

/-- **Rank strictly decreases along `∈`.** -/
theorem rank_lt_of_mem {x y : V} (h : y ∈ x) : rank y < rank x :=
  mem_Vset_iff_rank_lt.mp (subset_Vset_rank x y h)

theorem rank_mono {x y : V} (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_of_subset (subset_trans h (subset_Vset_rank y))

@[simp] theorem rank_Vset (α : Ordinal V) : rank (Vset α) = α := by
  refine le_antisymm (rank_le_of_subset (subset_refl _)) ?_
  by_contra h
  have h' : rank (Vset α) < α := lt_of_not_ge h
  exact mem_irrefl _ (mem_Vset_iff_rank_lt.mpr h')

/-! ## Closure properties of `V_α`

None of these needs a large cardinal; the exact hypothesis is stated in each
case.
-/

/-- Unordered pairs: needs `α` to be a limit ordinal, since `{x, y}` has rank
one more than `max (rank x) (rank y)`. -/
theorem doubleton_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : doubleton x y ∈ Vset α := by
  have hδα : max (rank x) (rank y) < α :=
    max_lt (mem_Vset_iff_rank_lt.mp hx) (mem_Vset_iff_rank_lt.mp hy)
  refine mem_Vset_iff.mpr ⟨(max (rank x) (rank y)).succ, h.succ_lt _ hδα, fun z hz ↦ ?_⟩
  rcases mem_doubleton_iff.mp hz with rfl | rfl
  · exact mem_Vset_iff_rank_lt.mpr (lt_of_le_of_lt (le_max_left _ _)
      (lt_succ _))
  · exact mem_Vset_iff_rank_lt.mpr (lt_of_le_of_lt (le_max_right _ _)
      (lt_succ _))

theorem singleton_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x : V}
    (hx : x ∈ Vset α) : ({x} : V) ∈ Vset α := by
  rw [singleton_def]; exact doubleton_mem_Vset h hx hx

theorem pair_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : ({x, y} : V) ∈ Vset α := by
  rw [pair_eq_doubleton]; exact doubleton_mem_Vset h hx hy

/-- Kuratowski pairs, hence products, live in every limit stage. -/
theorem kpair_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : (⟨x, y⟩ₖ : V) ∈ Vset α := by
  have hk : (⟨x, y⟩ₖ : V) = doubleton ({x} : V) ({x, y} : V) := pair_eq_doubleton _ _
  rw [hk]
  exact doubleton_mem_Vset h (singleton_mem_Vset h hx) (pair_mem_Vset h hx hy)

/-- Union: **no** hypothesis on `α` is needed, because `rank (⋃ˢ x) ≤ rank x`. -/
theorem sUnion_mem_Vset {α : Ordinal V} {x : V} (hx : x ∈ Vset α) : ⋃ˢ x ∈ Vset α := by
  obtain ⟨β, hβ, hxβ⟩ := mem_Vset_iff.mp hx
  refine mem_Vset_iff.mpr ⟨β, hβ, fun z hz ↦ ?_⟩
  obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
  exact (isTransitive_Vset β).mem_trans hzy (hxβ y hy)

theorem union_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : x ∪ y ∈ Vset α := by
  rw [union_def]
  exact sUnion_mem_Vset (doubleton_mem_Vset h hx hy)

/-- Power set: needs `α` to be a limit ordinal, since `rank (℘ x) = rank x + 1`. -/
theorem power_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x : V}
    (hx : x ∈ Vset α) : ℘ x ∈ Vset α := by
  obtain ⟨β, hβ, hxβ⟩ := mem_Vset_iff.mp hx
  refine mem_Vset_iff.mpr ⟨β.succ, h.succ_lt β hβ, fun z hz ↦ ?_⟩
  exact mem_Vset_succ_iff.mpr (subset_trans (mem_power_iff.mp hz) hxβ)

/-- A subset of a member of `V_α` is a member of `V_α`; no hypothesis on `α`. -/
theorem mem_Vset_of_subset_of_mem {α : Ordinal V} {x y : V} (hyx : y ⊆ x)
    (hx : x ∈ Vset α) : y ∈ Vset α := by
  obtain ⟨β, hβ, hxβ⟩ := mem_Vset_iff.mp hx
  exact mem_Vset_iff.mpr ⟨β, hβ, subset_trans hyx hxβ⟩

/-- Separation: subsets stay in the same stage; no hypothesis on `α`. -/
theorem sep_mem_Vset {α : Ordinal V} {x : V} (hx : x ∈ Vset α)
    {P : V → Prop} (hP : ℒₛₑₜ-predicate P) : sep x P hP ∈ Vset α :=
  mem_Vset_of_subset_of_mem sep_subset hx

theorem insert_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : insert x y ∈ Vset α := by
  rw [insert_def]
  exact union_mem_Vset h (singleton_mem_Vset h hx) hy

lemma prod_subset_power_power_union (x y : V) : (x ×ˢ y : V) ⊆ ℘ ℘ (x ∪ y) := sep_subset

/-- Cartesian products live in every limit stage. -/
theorem prod_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : (x ×ˢ y : V) ∈ Vset α :=
  mem_Vset_of_subset_of_mem (prod_subset_power_power_union x y)
    (power_mem_Vset h (power_mem_Vset h (union_mem_Vset h hx hy)))

/-- Function spaces live in every limit stage. No large cardinal is needed:
`rank (y ^ x) ≤ rank x + rank y + 4`, so a limit stage already absorbs it. -/
theorem function_mem_Vset {α : Ordinal V} (h : IsLimitOrdinal α) {x y : V}
    (hx : x ∈ Vset α) (hy : y ∈ Vset α) : (y ^ x : V) ∈ Vset α :=
  mem_Vset_of_subset_of_mem (function_subset_power_prod x y)
    (power_mem_Vset h (prod_mem_Vset h hx hy))

end Lean4Lean.SetModel
