import Lean4Lean.Theory.SetModel.Universe

/-!
# Enough cardinal arithmetic for full replacement inside `Vset κ`

The target is

```
∀ β < κ, ∃ a ∈ κ, Vset β ≤# a          -- "|V_β| < κ"
```

for `κ` inaccessible.  With it, `repl_mem_vsetV` generalises from an *ordinal*
index set to an arbitrary `A ∈ Vset κ`, which is the last model-side
obstruction: it unblocks both general replacement inside the stage and the
carrier construction for inductive families.

## The route, and what it avoids

The textbook proof of `|V_β| < κ` at limit stages goes through
`|α × β| = max (|α|, |β|)` for infinite cardinals, i.e. Gödel pairing or
Hessenberg's theorem — a large development, and Foundation supplies none of it.
That is avoidable.  At a limit stage one needs `|α × b| < κ` for `α, b < κ`, and
since `α ×ˢ b ⊆ ℘ ℘ (α ∪ b)` (Foundation's own bound for `prod`) and `α ∪ b` is
just `max α b` for ordinals, **two applications of strong-limitness plus
monotonicity of `℘` under injections** suffice.  So:

* no Cantor–Schröder–Bernstein (every step is a chain of `≤#`, never a
  two-sided squeeze);
* no cardinal multiplication;
* no cardinal *numbers* at all — everything is stated with Foundation's `≤#`.

What is genuinely needed is `power_cardLE_power` (`X ≤# Y → ℘ X ≤# ℘ Y`) and, at
the limit stage, a **uniform choice of injections**, which is where `𝗔𝗖` enters
through `exists_choiceFunction`.

## Main results

* `cardLE_of_definable_injOn` — build `X ≤# Y` from a definable meta-level
  injection.  This is the workhorse; it removes the need to hand-build an
  internal function of Kuratowski pairs each time.
* `power_cardLE_power` — `℘` is monotone under injections.
* `Vset_cardLE_prod` — the limit-stage bound `Vset α ≤# α ×ˢ b`.
* `prod_cardLE_mem_of_inaccessible` — `α, b ∈ κ → ∃ c ∈ κ, α ×ˢ b ≤# c`.
* **`exists_cardLE_of_mem`** — the target: `β ∈ κ → ∃ a ∈ κ, vsetV β ≤# a`.
* **`repl_mem_vsetV'`** — replacement inside `Vset κ` along an arbitrary
  `A ∈ Vset κ`, and `sUnion_repl_mem_vsetV'`, `range_mem_vsetV`.

## What this unblocks

`range_mem_vsetV` is the statement the inductive-family carrier construction
needs (`SetModel/Inductive.lean`, `IsIndCarrier`): a stage-valued function on
any `B ∈ Vset κ` has its range inside the stage.  What remains there is the
closure-ordinal argument, which needs no further prerequisite.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Basic `≤#` machinery -/

section Basic

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

lemma value_mem_of_mem_function {f X Y x : V} (hf : f ∈ (Y ^ X : V)) (hx : x ∈ X) :
    f ‘ x ∈ Y := range_subset_of_mem_function hf _ (value_mem_range hf hx)

/-- **The workhorse.**  A definable meta-level function that is injective on `X`
and maps `X` into `Y` yields `X ≤# Y`.  Without this every cardinality argument
has to hand-build an internal set of Kuratowski pairs. -/
theorem cardLE_of_definable_injOn {X Y : V} (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hmap : ∀ x ∈ X, F x ∈ Y) (hinj : ∀ x ∈ X, ∀ y ∈ X, F x = F y → x = y) : X ≤# Y := by
  obtain ⟨f, hf⟩ : ∃ f : V, ∀ p : V, p ∈ f ↔ ∃ x ∈ X, p = ⟨x, F x⟩ₖ := by
    refine ⟨sep (X ×ˢ Y) (fun p ↦ ∃ x ∈ X, p = ⟨x, F x⟩ₖ), fun p ↦ ?_⟩
    rw [mem_sep_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    obtain ⟨x, hx, rfl⟩ := h
    exact kpair_mem_iff.mpr ⟨hx, hmap x hx⟩
  have hkp : ∀ x y : V, (⟨x, y⟩ₖ : V) ∈ f ↔ x ∈ X ∧ y = F x := by
    intro x y
    rw [hf]
    refine ⟨?_, fun h ↦ ⟨x, h.1, by rw [h.2]⟩⟩
    rintro ⟨x', hx', he⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    exact ⟨hx', rfl⟩
  refine ⟨f, mem_function.intro (fun p hp ↦ ?_) (fun x hx ↦ ?_), ?_⟩
  · obtain ⟨x, hx, rfl⟩ := (hf p).mp hp
    exact kpair_mem_iff.mpr ⟨hx, hmap x hx⟩
  · exact ExistsUnique.intro (F x) ((hkp x (F x)).mpr ⟨hx, rfl⟩) fun y hy ↦ ((hkp x y).mp hy).2
  · intro x₁ x₂ y h₁ h₂
    obtain ⟨hx₁, hy₁⟩ := (hkp x₁ y).mp h₁
    obtain ⟨hx₂, hy₂⟩ := (hkp x₂ y).mp h₂
    exact hinj x₁ hx₁ x₂ hx₂ (by rw [← hy₁, ← hy₂])

lemma mem_image_iff {f A y : V} : y ∈ (f “ A) ↔ ∃ x ∈ A, (⟨x, y⟩ₖ : V) ∈ f := by
  rw [image, mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    rw [kpair_mem_restrict_iff] at hx
    exact ⟨x, hx.2, hx.1⟩
  · rintro ⟨x, hxA, hxf⟩
    exact ⟨x, kpair_mem_restrict_iff.mpr ⟨hxf, hxA⟩⟩

/-- **`℘` is monotone under injections.**  Not in Foundation, and needed at
every successor stage. -/
theorem power_cardLE_power {X Y : V} (h : X ≤# Y) : ℘ X ≤# ℘ Y := by
  obtain ⟨f, hf, hinj⟩ := h
  have hfun : IsFunction f := IsFunction.of_mem hf
  have key : ∀ S T : V, S ⊆ X → T ⊆ X → (f “ S) = (f “ T) → S ⊆ T := by
    intro S T hS _ he x hxS
    obtain ⟨y, -, hxy⟩ := exists_of_mem_function hf x (hS x hxS)
    have hy : y ∈ (f “ S) := mem_image_iff.mpr ⟨x, hxS, hxy⟩
    rw [he] at hy
    obtain ⟨x', hx'T, hx'f⟩ := mem_image_iff.mp hy
    rcases hinj x' x y hx'f hxy
    exact hx'T
  refine cardLE_of_definable_injOn (fun S ↦ f “ S) (by definability) (fun S hS ↦ ?_) ?_
  · rw [mem_power_iff]
    intro y hy
    obtain ⟨x, -, hxf⟩ := mem_image_iff.mp hy
    exact (mem_of_mem_functions hf hxf).2
  · intro S hS T hT he
    rw [mem_power_iff] at hS hT
    exact subset_antisymm (key S T hS hT he) (key T S hT hS he.symm)

/-- The set of injections from `X` into `Y`. -/
noncomputable def InjSet (Y X : V) : V := {f ∈ (Y ^ X : V) ; Injective f}

lemma mem_InjSet_iff {Y X f : V} : f ∈ InjSet Y X ↔ f ∈ (Y ^ X : V) ∧ Injective f := mem_sep_iff

lemma isNonempty_InjSet_iff {X Y : V} : IsNonempty (InjSet Y X) ↔ X ≤# Y := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (mem_InjSet_iff.mp hf).1, (mem_InjSet_iff.mp hf).2⟩
  · rintro ⟨f, hf, hinj⟩
    exact ⟨f, mem_InjSet_iff.mpr ⟨hf, hinj⟩⟩

instance InjSet_definable : ℒₛₑₜ-function₂[V] InjSet := by
  suffices ℒₛₑₜ-relation₃[V] (fun T Y X ↦ T = InjSet Y X) by exact this
  have e : ∀ T Y X : V, T = InjSet Y X ↔ ∀ f, f ∈ T ↔ f ∈ (Y ^ X : V) ∧ Injective f := by
    intro T Y X
    rw [mem_ext_iff]
    simp [InjSet]
  simp only [e]
  definability

end Basic

/-! ## The least ordinal of a given cardinality bound -/

section LeastCard

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `a` is the least ordinal that `X` injects into. -/
def IsLeastCard (X a : V) : Prop :=
  IsOrdinal a ∧ X ≤# a ∧ ∀ a' : V, IsOrdinal a' → X ≤# a' → a ⊆ a'

instance IsLeastCard.definable : ℒₛₑₜ-relation[V] IsLeastCard := by
  unfold IsLeastCard; definability

lemma isLeastCard_existsUnique {X : V} (h : ∃ α : Ordinal V, X ≤# α.val) :
    ∃! a : V, IsLeastCard X a := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨β, hβ, hmin⟩ :=
    exists_minimal (V := V) (fun a ↦ X ≤# a) (by definability) ⟨α, hα⟩
  refine ⟨β.val, ⟨β.ordinal, hβ, fun a' ha' h' ↦ ?_⟩, ?_⟩
  · exact le_def.mp (hmin (IsOrdinal.toOrdinal a') h')
  · rintro a ⟨ha, hXa, hle⟩
    exact subset_antisymm (hle β.val β.ordinal hβ)
      (le_def.mp (hmin (IsOrdinal.toOrdinal a) hXa))

/-- The least ordinal bound is itself below any witness, hence stays inside an
inaccessible `κ`. -/
lemma isLeastCard_mem_of_mem {X a a₀ k : V} [IsOrdinal k] (h : IsLeastCard X a)
    (ha₀ : a₀ ∈ k) (hX : X ≤# a₀) : a ∈ k := by
  have ha₀o : IsOrdinal a₀ := IsOrdinal.of_mem ha₀
  have hsub : a ⊆ a₀ := h.2.2 a₀ ha₀o hX
  have ho : IsOrdinal a := h.1
  rcases IsOrdinal.subset_iff.mp hsub with rfl | hlt
  · exact ha₀
  · exact ‹IsOrdinal k›.transitive a₀ ha₀ a hlt

end LeastCard

/-! ## The limit-stage bound: `Vset α ≤# α ×ˢ b`

This is where `𝗔𝗖` is used, and it is used exactly once: to choose, uniformly
in `γ < α`, an injection of `℘ (Vset γ)` into `b`.
-/

section LimitStage

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- Given a single `b` into which every `℘ (Vset γ)`, `γ < α`, injects,
`Vset α` injects into `α ×ˢ b`: send `x` to its rank together with its image
under the chosen injection at that rank. -/
theorem Vset_cardLE_prod {α : Ordinal V} {b : V}
    (hb : ∀ γ : Ordinal V, γ < α → ℘ (Vset γ) ≤# b) :
    Vset α ≤# (α.val ×ˢ b : V) := by
  -- the family of nonempty sets of injections, indexed by `γ < α`
  have hIdef : ℒₛₑₜ-function₁[V] (fun γ : V ↦ InjSet b (℘ (vsetV γ))) := by definability
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : V, ∀ Z : V, Z ∈ 𝒮 ↔ ∃ γ ∈ α.val, Z = InjSet b (℘ (vsetV γ)) :=
    ⟨repl _ hIdef α.val, fun _ ↦ repl_spec hIdef⟩
  obtain ⟨c, hcfun, -, hcval⟩ := exists_choiceFunction_value 𝒮
  -- the chosen injection at rank `γ`
  have hchoice : ∀ γ : V, γ ∈ α.val →
      (c ‘ (InjSet b (℘ (vsetV γ)))) ∈ InjSet b (℘ (vsetV γ)) := by
    intro γ hγ
    have hZ : InjSet b (℘ (vsetV γ)) ∈ 𝒮 := (h𝒮 _).mpr ⟨γ, hγ, rfl⟩
    have hne : IsNonempty (InjSet b (℘ (vsetV γ))) := by
      have hγo : IsOrdinal γ := IsOrdinal.of_mem hγ
      exact isNonempty_InjSet_iff.mpr (hb (IsOrdinal.toOrdinal γ) hγ)
    exact hcval _ hZ hne
  -- `x` lies in `℘ (Vset (rank x))`, and `rank x < α`
  have hmemP : ∀ x ∈ Vset α, x ∈ ℘ (vsetV (rankV x)) := fun x _ ↦
    mem_power_iff.mpr (subset_Vset_rank x)
  have hrk : ∀ x ∈ Vset α, rankV x ∈ α.val := fun x hx ↦ lt_def.mp (mem_Vset_iff_rank_lt.mp hx)
  refine cardLE_of_definable_injOn
    (fun x ↦ ⟨rankV x, (c ‘ (InjSet b (℘ (vsetV (rankV x))))) ‘ x⟩ₖ)
    (by definability) (fun x hx ↦ ?_) (fun x hx y hy he ↦ ?_)
  · refine kpair_mem_iff.mpr ⟨hrk x hx, ?_⟩
    exact value_mem_of_mem_function (mem_InjSet_iff.mp (hchoice _ (hrk x hx))).1 (hmemP x hx)
  · obtain ⟨hr, hv⟩ := kpair_inj he
    -- same rank, and equal images under the injection at that rank
    have hxP : x ∈ ℘ (vsetV (rankV x)) := hmemP x hx
    have hyP : y ∈ ℘ (vsetV (rankV x)) := hr ▸ hmemP y hy
    obtain ⟨hgf, hginj⟩ := mem_InjSet_iff.mp (hchoice _ (hrk x hx))
    have hgfun : IsFunction (c ‘ (InjSet b (℘ (vsetV (rankV x))))) := IsFunction.of_mem hgf
    have hx' := kpair_value_mem hgf hxP
    have hy' := kpair_value_mem hgf hyP
    rw [← hr] at hv
    rw [hv] at hx'
    exact hginj x y _ hx' hy'

end LimitStage

/-! ## `κ` is closed under products of its members -/

section Products

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {k : V}

/-- The union of two ordinals is the larger of them, hence again a member of any
ordinal containing both. -/
lemma union_mem_of_isOrdinal [IsOrdinal k] {x y : V} (hx : x ∈ k) (hy : y ∈ k) :
    x ∪ y ∈ k := by
  have hxo : IsOrdinal x := IsOrdinal.of_mem hx
  have hyo : IsOrdinal y := IsOrdinal.of_mem hy
  rcases IsOrdinal.subset_or_supset x y with h | h
  · rw [union_eq_iff_left.mpr h]; exact hy
  · rw [union_eq_iff_right.mpr h]; exact hx

/-- **Strong limit, twice.**  `℘ ℘ d` injects into a member of `κ` whenever
`d ∈ κ`. -/
lemma power_power_cardLE_mem (hk : IsInaccessible k) {d : V} (hd : d ∈ k) :
    ∃ c ∈ k, ℘ (℘ d) ≤# c := by
  obtain ⟨e, he, hpe⟩ := hk.strongLimit d hd
  obtain ⟨c, hc, hpc⟩ := hk.strongLimit e he
  exact ⟨c, hc, CardLE.trans (power_cardLE_power hpe) hpc⟩

/-- **`κ` is closed under products**, with no cardinal multiplication: the
product is a subset of `℘ ℘ (x ∪ y)` and strong-limitness does the rest. -/
theorem prod_cardLE_mem_of_inaccessible (hk : IsInaccessible k) {x y : V}
    (hx : x ∈ k) (hy : y ∈ k) : ∃ c ∈ k, (x ×ˢ y : V) ≤# c := by
  have hko : IsOrdinal k := hk.isOrdinal
  obtain ⟨c, hc, hpc⟩ := power_power_cardLE_mem hk (union_mem_of_isOrdinal hx hy)
  exact ⟨c, hc, CardLE.trans (cardLE_of_subset (prod_subset_power_power_union x y)) hpc⟩

end Products

/-! ## The main theorem: `|V_β| < κ` -/

section Main

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V}

/-- **`|V_β| < κ` for every `β < κ`.**

The induction is uniform in `β`: `Vset β = ⋃_{γ<β} ℘ (Vset γ)`, so there is no
case split on zero / successor / limit.  Regularity produces a single bound `b`
for all the `℘ (Vset γ)`, `𝗔𝗖` chooses the injections, and strong-limitness
absorbs the resulting product. -/
theorem exists_cardLE_of_mem (hk : IsInaccessible k) :
    ∀ β : Ordinal V, β.val ∈ k → ∃ a ∈ k, vsetV β.val ≤# a := by
  have hko : IsOrdinal k := hk.isOrdinal
  refine transfinite_induction (fun c ↦ c ∈ k → ∃ a ∈ k, vsetV c ≤# a) (by definability) ?_
  intro α ih hα
  -- (1) each `℘ (Vset γ)`, `γ < α`, injects into a member of `k`
  have hstep : ∀ γ : V, γ ∈ α.val → ∃ a ∈ k, ℘ (vsetV γ) ≤# a := by
    intro γ hγ
    have hγk : γ ∈ k := hko.transitive α.val hα γ hγ
    have hγo : IsOrdinal γ := IsOrdinal.of_mem hγ
    obtain ⟨a, hak, ha⟩ := ih (IsOrdinal.toOrdinal γ) hγ hγk
    obtain ⟨a', ha'k, ha'⟩ := hk.strongLimit a hak
    exact ⟨a', ha'k, CardLE.trans (power_cardLE_power ha) ha'⟩
  -- (2) the least such bounds form a function `α → k`; regularity bounds them
  have hex : ∀ γ : V, γ ∈ α.val → ∃! a : V, IsLeastCard (℘ (vsetV γ)) a := by
    intro γ hγ
    obtain ⟨a, hak, ha⟩ := hstep γ hγ
    have hao : IsOrdinal a := IsOrdinal.of_mem hak
    exact isLeastCard_existsUnique ⟨IsOrdinal.toOrdinal a, ha⟩
  obtain ⟨g, hg⟩ : ∃ g : V, ∀ p : V, p ∈ g ↔ ∃ γ ∈ α.val, ∃ a : V,
      p = ⟨γ, a⟩ₖ ∧ IsLeastCard (℘ (vsetV γ)) a := by
    refine ⟨sep (α.val ×ˢ k) (fun p ↦ ∃ γ ∈ α.val, ∃ a : V,
      p = ⟨γ, a⟩ₖ ∧ IsLeastCard (℘ (vsetV γ)) a), fun p ↦ ?_⟩
    rw [mem_sep_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    obtain ⟨γ, hγ, a, rfl, hla⟩ := h
    obtain ⟨a₀, ha₀k, ha₀⟩ := hstep γ hγ
    exact kpair_mem_iff.mpr ⟨hγ, isLeastCard_mem_of_mem hla ha₀k ha₀⟩
  have hgkp : ∀ γ a : V, (⟨γ, a⟩ₖ : V) ∈ g ↔ γ ∈ α.val ∧ IsLeastCard (℘ (vsetV γ)) a := by
    intro γ a
    rw [hg]
    refine ⟨?_, fun h ↦ ⟨γ, h.1, a, rfl, h.2⟩⟩
    rintro ⟨γ', hγ', a', he, hla⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    exact ⟨hγ', hla⟩
  have hgmem : g ∈ (k ^ α.val : V) := by
    refine mem_function.intro (fun p hp ↦ ?_) (fun γ hγ ↦ ?_)
    · obtain ⟨γ, hγ, a, rfl, hla⟩ := (hg p).mp hp
      obtain ⟨a₀, ha₀k, ha₀⟩ := hstep γ hγ
      exact kpair_mem_iff.mpr ⟨hγ, isLeastCard_mem_of_mem hla ha₀k ha₀⟩
    · obtain ⟨a, hla, huniq⟩ := hex γ hγ
      exact ExistsUnique.intro a ((hgkp γ a).mpr ⟨hγ, hla⟩)
        fun a' ha' ↦ huniq a' ((hgkp γ a').mp ha').2
  obtain ⟨b, hbk, hbrange⟩ := hk.regular α.val hα g hgmem
  have hbo : IsOrdinal b := IsOrdinal.of_mem hbk
  have hbound : ∀ γ : Ordinal V, γ < α → ℘ (Vset γ) ≤# b := by
    intro γ hγ
    obtain ⟨a, hla, -⟩ := hex γ.val (lt_def.mp hγ)
    have hab : a ∈ b := hbrange _ (mem_range_of_kpair_mem ((hgkp γ.val a).mpr
      ⟨lt_def.mp hγ, hla⟩))
    exact CardLE.trans hla.2.1 (cardLE_of_subset (hbo.transitive a hab))
  -- (3) assemble
  obtain ⟨c, hck, hc⟩ := prod_cardLE_mem_of_inaccessible hk hα hbk
  exact ⟨c, hck, CardLE.trans (Vset_cardLE_prod hbound) hc⟩

/-- Every member of `Vset κ` injects into a member of `κ` — the form in which
the bound is used. -/
theorem exists_cardLE_of_mem_vsetV (hk : IsInaccessible k) {A : V} (hA : A ∈ vsetV k) :
    ∃ a ∈ k, A ≤# a := by
  have hko : IsOrdinal k := hk.isOrdinal
  obtain ⟨β, hβ, hAβ⟩ := mem_Vset_iff.mp (mem_vsetV_iff_mem_Vset.mp hA)
  obtain ⟨a, hak, ha⟩ := exists_cardLE_of_mem hk β (lt_def.mp hβ)
  exact ⟨a, hak, CardLE.trans (cardLE_of_subset hAβ) ha⟩

/-! ## The payoff: full replacement inside `Vset κ` -/

/-- **Regularity along an arbitrary index set.**  The generalisation of
`IsRegular` from an ordinal index set to any `B` that injects into a member of
`κ`: transport the family along the injection and apply regularity there.  This
is the workhorse behind everything below. -/
theorem exists_bound_of_cardLE (hk : IsInaccessible k) {A a : V} (hak : a ∈ k)
    (hAa : A ≤# a) (G : V → V) (hgdef : ℒₛₑₜ-function₁[V] G)
    (hrk : ∀ x ∈ A, G x ∈ k) : ∃ b ∈ k, ∀ x ∈ A, G x ∈ b := by
  have hko : IsOrdinal k := hk.isOrdinal
  obtain ⟨f, hf, hinj⟩ := hAa
  -- transport `x ↦ rank (F x)` along the injection `f : A → a`
  obtain ⟨g, hgsub, hg⟩ : ∃ g : V, g ⊆ a ×ˢ k ∧ ∀ t v : V, (⟨t, v⟩ₖ : V) ∈ g ↔ t ∈ a ∧
      ((∀ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f → v = G x) ∧
        ((¬∃ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f) → v = ∅)) := by
    refine ⟨sep (a ×ˢ k) (fun p ↦ ∃ t ∈ a, ∃ v : V, p = ⟨t, v⟩ₖ ∧
      ((∀ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f → v = G x) ∧
        ((¬∃ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f) → v = ∅))), sep_subset, fun t v ↦ ?_⟩
    rw [mem_sep_iff]
    constructor
    · rintro ⟨-, t', ht', v', he, hP⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj he
      exact ⟨ht', hP⟩
    · rintro ⟨ht, hP⟩
      refine ⟨kpair_mem_iff.mpr ⟨ht, ?_⟩, t, ht, v, rfl, hP⟩
      by_cases hex : ∃ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f
      · obtain ⟨x, hx, hxt⟩ := hex
        rw [hP.1 x hx hxt]
        exact hrk x hx
      · rw [hP.2 hex]
        exact hk.empty_mem
  have hgmem : g ∈ (k ^ a : V) := by
    refine mem_function.intro hgsub (fun t ht ↦ ?_)
    · by_cases hex : ∃ x ∈ A, (⟨x, t⟩ₖ : V) ∈ f
      · obtain ⟨x, hx, hxt⟩ := hex
        have huniq : ∀ x' ∈ A, (⟨x', t⟩ₖ : V) ∈ f → x' = x := fun x' _ hx't ↦
          hinj x' x t hx't hxt
        refine ExistsUnique.intro (G x)
          ((hg t _).mpr ⟨ht, fun x' hx' hx't ↦ by rw [huniq x' hx' hx't], fun hn ↦
            absurd ⟨x, hx, hxt⟩ hn⟩) fun v hv ↦ ?_
        exact ((hg t v).mp hv).2.1 x hx hxt
      · refine ExistsUnique.intro ∅
          ((hg t _).mpr ⟨ht, fun x' hx' hx't ↦ absurd ⟨x', hx', hx't⟩ hex, fun _ ↦ rfl⟩)
          fun v hv ↦ ?_
        exact ((hg t v).mp hv).2.2 hex
  obtain ⟨b, hbk, hbrange⟩ := hk.regular a hak g hgmem
  refine ⟨b, hbk, fun x hx ↦ ?_⟩
  have hxt : (⟨x, f ‘ x⟩ₖ : V) ∈ f := kpair_value_mem hf hx
  have hta : f ‘ x ∈ a := value_mem_of_mem_function hf hx
  have hmem : (⟨f ‘ x, G x⟩ₖ : V) ∈ g :=
    (hg _ _).mpr ⟨hta, fun x' hx' hx't ↦ by rw [hinj x' x (f ‘ x) hx't hxt],
      fun hn ↦ absurd ⟨x, hx, hxt⟩ hn⟩
  exact hbrange _ (mem_range_of_kpair_mem hmem)

/-- Regularity along any index set that is a member of the stage. -/
theorem exists_bound_of_mem_vsetV (hk : IsInaccessible k) {A : V} (hA : A ∈ vsetV k)
    (G : V → V) (hG : ℒₛₑₜ-function₁[V] G) (hGA : ∀ x ∈ A, G x ∈ k) :
    ∃ b ∈ k, ∀ x ∈ A, G x ∈ b := by
  obtain ⟨a, hak, hAa⟩ := exists_cardLE_of_mem_vsetV hk hA
  exact exists_bound_of_cardLE hk hak hAa G hG hGA

/-- The rank form: the ranks of a stage-valued definable family over an index
set in the stage are uniformly bounded below `κ`. -/
theorem exists_rank_bound_of_mem_vsetV (hk : IsInaccessible k) {A : V} (hA : A ∈ vsetV k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFA : ∀ x ∈ A, F x ∈ vsetV k) :
    ∃ b ∈ k, ∀ x ∈ A, F x ⊆ vsetV b := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hrk : ∀ x ∈ A, rankV (F x) ∈ k := by
    intro x hx
    have h1 : rank (F x) < (IsOrdinal.toOrdinal k : Ordinal V) :=
      mem_Vset_iff_rank_lt.mp (mem_vsetV_iff_mem_Vset.mp (hFA x hx))
    have h2 : (rank (F x)).val ∈ (IsOrdinal.toOrdinal k : Ordinal V).val := lt_def.mp h1
    exact h2
  obtain ⟨b, hbk, hbound⟩ :=
    exists_bound_of_mem_vsetV hk hA (fun x ↦ rankV (F x)) (by definability) hrk
  have hbo : IsOrdinal b := IsOrdinal.of_mem hbk
  refine ⟨b, hbk, fun x hx ↦ ?_⟩
  have hlt : rank (F x) < (IsOrdinal.toOrdinal b : Ordinal V) := lt_def.mpr (hbound x hx)
  have hsub : F x ⊆ Vset (IsOrdinal.toOrdinal b : Ordinal V) :=
    subset_trans (subset_Vset_rank (F x)) (Vset_mono (le_of_lt hlt))
  exact hsub

/-- **Full replacement inside `Vset κ`.**  The index set is an arbitrary member
of the stage — this is the generalisation of `repl_mem_vsetV`, and the last
model-side obstruction removed. -/
theorem repl_mem_vsetV' (hk : IsInaccessible k) {A : V} (hA : A ∈ vsetV k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFA : ∀ x ∈ A, F x ∈ vsetV k) :
    repl F hF A ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  obtain ⟨b, hbk, hbound⟩ := exists_rank_bound_of_mem_vsetV hk hA F hF hFA
  have hbo : IsOrdinal b := IsOrdinal.of_mem hbk
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_iff.mpr ⟨(IsOrdinal.toOrdinal b : Ordinal V).succ,
    hk.isLimitOrdinal.succ_lt _ (lt_def.mpr hbk), fun z hz ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := (repl_spec hF).mp hz
  exact mem_Vset_succ_iff.mpr (hbound x hx)

/-- Unions of stage-sized definable families stay in the stage. -/
theorem sUnion_repl_mem_vsetV' (hk : IsInaccessible k) {A : V} (hA : A ∈ vsetV k)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hFA : ∀ x ∈ A, F x ∈ vsetV k) :
    ⋃ˢ (repl F hF A) ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  exact sUnion_mem_Vset (mem_vsetV_iff_mem_Vset.mp (repl_mem_vsetV' hk hA F hF hFA))

/-- **The range of any stage-valued function is in the stage** — the statement
that was out of reach before, and the one the inductive-family carrier
construction needs. -/
theorem range_mem_vsetV (hk : IsInaccessible k) {B g : V} (hB : B ∈ vsetV k)
    (hg : g ∈ ((vsetV k) ^ B : V)) : range g ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hval : ∀ x ∈ B, g ‘ x ∈ vsetV k := fun x hx ↦ value_mem_of_mem_function hg hx
  have hrepl := repl_mem_vsetV' hk hB (fun x ↦ g ‘ x) (by definability) hval
  rw [mem_vsetV_iff_mem_Vset] at hrepl ⊢
  refine mem_Vset_of_subset_of_mem (fun y hy ↦ ?_) hrepl
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  have hxB : x ∈ B := (mem_of_mem_functions hg hxy).1
  have : IsFunction g := IsFunction.of_mem hg
  exact (repl_spec (by definability)).mpr ⟨x, hxB, (value_eq_of_kpair_mem hxy).symm⟩

end Main
