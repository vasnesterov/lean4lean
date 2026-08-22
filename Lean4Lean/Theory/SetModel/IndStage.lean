import Lean4Lean.Theory.SetModel.Inductive
import Lean4Lean.Theory.SetModel.Cardinal

/-!
# The carrier: inductive families at an inaccessible stage

`SetModel/Inductive.lean` develops the interpretation of an inductive family
relative to an assumed carrier `D` (`IsIndCarrier S D`).  This file discharges
that assumption.

The observation that makes it cheap is that **the stage itself is a carrier**.
With full replacement inside `Vset κ` available (`Cardinal.lean`'s
`range_mem_vsetV`), a function `f : Pos q a → Vset κ` has its range inside the
stage, hence `f ⊆ Pos q a ×ˢ range f ∈ Vset κ`, hence `f ∈ Vset κ` and so
`⟨q, ⟨a, f⟩ₖ⟩ₖ ∈ Vset κ`.  So `IsIndCarrier S (vsetV κ)` holds outright for any
signature whose components live in the stage, and every theorem of
`Inductive.lean` — formation, constructors, no-junk, no-confusion, the induction
principle, the recursor, the ι-rule, the subsingleton analysis — applies with no
carrier hypothesis left over.

What is *not* settled here is `Ind S (vsetV κ) ∈ Vset κ` — the family as a
*member* of the stage rather than a subset of it.  Two clean reductions are
proved (`Ind_mem_vsetV_of_carrier`, `Ind_mem_vsetV_of_cardLE`) and the residue is
stated precisely at the end of the file.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

section Stage

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}

/-- The components of the signature all live in the stage `Vset κ`.  This is what
a real inductive declaration supplies: the index set, the constructor tags, and
each constructor's non-recursive data and recursive positions are all sets of the
model below the universe being interpreted in. -/
structure IsStageSignature (k : V) (S : IndSignature V) : Prop where
  idx_mem : S.Idx ∈ vsetV k
  q_mem : S.Q ∈ vsetV k
  fld_mem : ∀ q ∈ S.Q, S.Fld q ∈ vsetV k
  pos_mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, S.Pos q a ∈ vsetV k

/-- **The stage is a carrier.**  This is the theorem that discharges
`IsIndCarrier` everywhere; it is exactly what `range_mem_vsetV` buys. -/
theorem isIndCarrier_vsetV (hk : IsInaccessible k) (hS : IsStageSignature k S) :
    IsIndCarrier S (vsetV k) := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hlim := hk.isLimitOrdinal
  refine ⟨fun q hq a ha f hf ↦ ?_⟩
  have hqm : q ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    subset_Vset_of_mem_Vset (mem_vsetV_iff_mem_Vset.mp hS.q_mem) q hq
  have ham : a ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    subset_Vset_of_mem_Vset (mem_vsetV_iff_mem_Vset.mp (hS.fld_mem q hq)) a ha
  have hposm : S.Pos q a ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    mem_vsetV_iff_mem_Vset.mp (hS.pos_mem q hq a ha)
  have hrng : range f ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    mem_vsetV_iff_mem_Vset.mp (range_mem_vsetV hk (hS.pos_mem q hq a ha) hf)
  have hfsub : f ⊆ S.Pos q a ×ˢ range f :=
    subset_prod_of_mem_function (mem_function_range_of_mem_function hf)
  have hfm : f ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    mem_Vset_of_subset_of_mem hfsub (prod_mem_Vset hlim hposm hrng)
  have hres : (⟨q, ⟨a, f⟩ₖ⟩ₖ : V) ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    kpair_mem_Vset hlim hqm (kpair_mem_Vset hlim ham hfm)
  exact hres

/-- The total space of the family is contained in the stage. -/
theorem Ind_subset_prod_vsetV : Ind S (vsetV k) ⊆ S.Idx ×ˢ (vsetV k) :=
  Ind_subset S (vsetV k)

end Stage

/-! ## Everything from `Inductive.lean`, with the carrier discharged

Each of these is the corresponding theorem of `Inductive.lean` with
`D := vsetV κ` and `IsIndCarrier` supplied by `isIndCarrier_vsetV`.  These are
the forms the interpretation cites.
-/

section Discharged

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}
  {R : V} {e : V → V → V → V → V} {he : ℒₛₑₜ-function₄[V] e}
  (hk : IsInaccessible k) (hS : IsStageSignature k S) (hWF : S.WF)

include hk hS hWF

/-- **Constructors land in the family.** -/
theorem ctor_mem_Ind_stage {q a f : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q)
    (hf : f ∈ ((vsetV k) ^ S.Pos q a : V))
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S (vsetV k)) :
    indCtor S q a f ∈ Ind S (vsetV k) :=
  ctor_mem_Ind hWF (isIndCarrier_vsetV hk hS) hq ha hf hrec

/-- **No junk.** -/
theorem mem_Ind_iff_stage {p : V} :
    p ∈ Ind S (vsetV k) ↔ ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ ((vsetV k) ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S (vsetV k)) ∧
        p = indCtor S q a f :=
  mem_Ind_iff hWF (isIndCarrier_vsetV hk hS)

variable (hE : IsMinorPremise S (vsetV k) R e)

include hE

/-- **The recursor's graph is single-valued.** -/
theorem recGraph_unique_stage : ∀ x i₁ i₂ v₁ v₂ : V,
    (⟨⟨i₁, x⟩ₖ, v₁⟩ₖ : V) ∈ recGraph S (vsetV k) R e he →
    (⟨⟨i₂, x⟩ₖ, v₂⟩ₖ : V) ∈ recGraph S (vsetV k) R e he → v₁ = v₂ :=
  recGraph_unique hWF (isIndCarrier_vsetV hk hS) hE

/-- **The recursor is total on the family.** -/
theorem recGraph_total_stage :
    ∀ p ∈ Ind S (vsetV k), ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph S (vsetV k) R e he :=
  recGraph_total hWF (isIndCarrier_vsetV hk hS) hE

theorem isFunction_recGraph_stage : IsFunction (recGraph S (vsetV k) R e he) :=
  isFunction_recGraph hWF (isIndCarrier_vsetV hk hS) hE

theorem indRec_mem_stage {p : V} (hp : p ∈ Ind S (vsetV k)) :
    indRec S (vsetV k) R e he p ∈ R :=
  indRec_mem hWF (isIndCarrier_vsetV hk hS) hE hp

/-- **The ι-rule**, outright: `F (ctor q a f) = e q a f (F ∘ f)`. -/
theorem indRec_indCtor_stage {q a f : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q)
    (hf : f ∈ ((vsetV k) ^ S.Pos q a : V))
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S (vsetV k)) :
    indRec S (vsetV k) R e he (indCtor S q a f) =
      e q a f (indRecTuple S (vsetV k) R e he q a f) :=
  indRec_indCtor hWF (isIndCarrier_vsetV hk hS) hE hq ha hf hrec

theorem indRecTuple_value_stage {q a f b : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S (vsetV k))
    (hb : b ∈ S.Pos q a) :
    (indRecTuple S (vsetV k) R e he q a f) ‘ b =
      indRec S (vsetV k) R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ) :=
  indRecTuple_value hWF (isIndCarrier_vsetV hk hS) hE hrec hb

omit hE

/-- **Subsingleton families**, outright. -/
theorem Ind_subsingleton_stage (hSub : IsSubsingletonSignature S) :
    ∀ x i y : V, (⟨i, x⟩ₖ : V) ∈ Ind S (vsetV k) → (⟨i, y⟩ₖ : V) ∈ Ind S (vsetV k) → x = y :=
  Ind_subsingleton hWF (isIndCarrier_vsetV hk hS) hSub

/-- **Large elimination for a subsingleton family**, outright. -/
theorem indRec_indep_of_proof_stage (hSub : IsSubsingletonSignature S) {i x y : V}
    (hx : (⟨i, x⟩ₖ : V) ∈ Ind S (vsetV k)) (hy : (⟨i, y⟩ₖ : V) ∈ Ind S (vsetV k)) :
    indRec S (vsetV k) R e he (⟨i, x⟩ₖ) = indRec S (vsetV k) R e he (⟨i, y⟩ₖ) :=
  indRec_indep_of_proof hWF (isIndCarrier_vsetV hk hS) hSub hx hy

end Discharged

/-! ## The family as a *member* of the stage

`Ind S (vsetV κ)` is a subset of `Idx ×ˢ vsetV κ`; for the interpretation it must
be an element of `Vset κ`.  Two reductions.
-/

section Membership

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}

/-- If a function into the stage has all its values in `D`, it is a function
into `D`. -/
lemma mem_function_of_values {B D f : V} (hf : f ∈ ((vsetV k) ^ B : V))
    (hval : ∀ b ∈ B, f ‘ b ∈ D) : f ∈ (D ^ B : V) := by
  have hfun : IsFunction f := IsFunction.of_mem hf
  refine mem_function.intro (fun p hp ↦ ?_) (exists_unique_of_mem_function hf)
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
  have hx : x ∈ B := (mem_of_mem_functions hf hp).1
  have : f ‘ x = y := value_eq_of_kpair_mem hp
  exact kpair_mem_iff.mpr ⟨hx, this ▸ hval x hx⟩

variable (hk : IsInaccessible k) (hS : IsStageSignature k S) (hWF : S.WF)

include hk hS hWF

/-- **The interpretation does not depend on the carrier.**  Any carrier
contained in the stage gives the same family. -/
theorem Ind_eq_of_isIndCarrier {D : V} (hDsub : D ⊆ vsetV k) (hD : IsIndCarrier S D) :
    Ind S (vsetV k) = Ind S D := by
  refine subset_antisymm ?_ ?_
  · refine Ind_induction (S := S) (D := vsetV k) (P := Ind S D) ?_ ?_
    · exact subset_trans (Ind_subset S D)
        (prod_subset_prod_of_subset (subset_refl _) hDsub)
    · intro q hq a ha f hf hrec
      have hval : ∀ b ∈ S.Pos q a, f ‘ b ∈ D := fun b hb ↦
        (kpair_mem_iff.mp (Ind_subset S D _ (hrec b hb))).2
      exact ctor_mem_Ind hWF hD hq ha (mem_function_of_values hf hval) hrec
  · have hsub : Ind S D ⊆ Ind S (vsetV k) ∩ (S.Idx ×ˢ D) := by
      refine Ind_induction (S := S) (D := D) (P := Ind S (vsetV k) ∩ (S.Idx ×ˢ D))
        (fun z hz ↦ (mem_inter_iff.mp hz).2) ?_
      intro q hq a ha f hf hrec
      refine mem_inter_iff.mpr ⟨?_, kpair_mem_iff.mpr
        ⟨hWF.resIdx_mem q hq a ha, hD.ctor_mem q hq a ha f hf⟩⟩
      exact ctor_mem_Ind hWF (isIndCarrier_vsetV hk hS) hq ha
        (mem_function_of_mem_function_of_subset hf hDsub)
        (fun b hb ↦ (mem_inter_iff.mp (hrec b hb)).1)
    exact fun z hz ↦ (mem_inter_iff.mp (hsub z hz)).1

/-- **Reduction 1**: a carrier that is a member of the stage puts the family in
the stage. -/
theorem Ind_mem_vsetV_of_carrier {D : V} (hDsub : D ⊆ vsetV k) (hD : IsIndCarrier S D)
    (hDmem : D ∈ vsetV k) : Ind S (vsetV k) ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hlim := hk.isLimitOrdinal
  rw [Ind_eq_of_isIndCarrier hk hS hWF hDsub hD, mem_vsetV_iff_mem_Vset]
  refine mem_Vset_of_subset_of_mem (Ind_subset S D) (prod_mem_Vset hlim ?_ ?_)
  · exact mem_vsetV_iff_mem_Vset.mp hS.idx_mem
  · exact mem_vsetV_iff_mem_Vset.mp hDmem

omit hWF in
/-- **Reduction 2**: a *cardinality* bound suffices — if the family injects into
a member of `κ`, its elements' ranks are bounded by regularity
(`exists_bound_of_cardLE`) and it is a member of the stage. -/
theorem Ind_mem_vsetV_of_cardLE {c : V} (hc : c ∈ k)
    (hcard : Ind S (vsetV k) ≤# c) : Ind S (vsetV k) ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hlim := hk.isLimitOrdinal
  have hidx : S.Idx ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
    mem_vsetV_iff_mem_Vset.mp hS.idx_mem
  -- every element of the family already has rank below `κ`
  have hmemk : ∀ p ∈ Ind S (vsetV k), p ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) := by
    intro p hp
    obtain ⟨i, hi, x, hx, rfl⟩ := mem_prod_iff.mp (Ind_subset S (vsetV k) p hp)
    exact kpair_mem_Vset hlim (subset_Vset_of_mem_Vset hidx i hi)
      (mem_vsetV_iff_mem_Vset.mp hx)
  have hrk : ∀ p ∈ Ind S (vsetV k), rankV p ∈ k := by
    intro p hp
    have h1 : rank p < (IsOrdinal.toOrdinal k : Ordinal V) :=
      mem_Vset_iff_rank_lt.mp (hmemk p hp)
    have h2 : (rank p).val ∈ (IsOrdinal.toOrdinal k : Ordinal V).val := lt_def.mp h1
    exact h2
  obtain ⟨b, hbk, hbound⟩ :=
    exists_bound_of_cardLE hk hc hcard rankV (by definability) hrk
  have hbo : IsOrdinal b := IsOrdinal.of_mem hbk
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_iff.mpr ⟨(IsOrdinal.toOrdinal b : Ordinal V).succ,
    hlim.succ_lt _ (lt_def.mpr hbk), fun p hp ↦ ?_⟩
  refine mem_Vset_succ_iff.mpr ?_
  have hlt : rank p < (IsOrdinal.toOrdinal b : Ordinal V) := lt_def.mpr (hbound p hp)
  have hsub : p ⊆ Vset (IsOrdinal.toOrdinal b : Ordinal V) :=
    subset_trans (subset_Vset_rank p) (Vset_mono (le_of_lt hlt))
  exact hsub

end Membership

/-!
## Status

**Discharged outright**, for any `S` with `IsStageSignature k S` and `S.WF` at an
inaccessible `κ`: `isIndCarrier_vsetV`, and with it every theorem of
`Inductive.lean` — `ctor_mem_Ind_stage`, `mem_Ind_iff_stage`, `Ind_induction`
(which never needed a carrier), `recGraph_unique_stage`, `recGraph_total_stage`,
`isFunction_recGraph_stage`, `indRec_mem_stage`, **`indRec_indCtor_stage`** (the
ι-rule), `indRecTuple_value_stage`, `Ind_subsingleton_stage`,
`indRec_indep_of_proof_stage`.  Also `Ind_eq_of_isIndCarrier`: the family does
not depend on which carrier inside the stage is used, so the construction is
canonical.

**Open — one statement.**  `Ind S (vsetV κ) ∈ Vset κ`, i.e. the family as a
*member* of the stage.  Reduced here to either

* a carrier `D ∈ Vset κ` (`Ind_mem_vsetV_of_carrier`), or
* a cardinality bound `Ind S (vsetV κ) ≤# c ∈ κ` (`Ind_mem_vsetV_of_cardLE`).

Both reductions are proved; what neither reduction supplies is the bound itself,
and the reason is worth recording because it is *not* the same obstruction as
before.  The transfinite iteration
`T γ = ⋃_{β<γ} {⟨q,⟨a,f⟩ₖ⟩ₖ | f ∈ (T β) ^ Pos q a}` stays inside `Vset κ` at
every stage (that is `repl_mem_vsetV'` and is now available), but it stabilises
at some `λ < κ` only if `cf λ` exceeds every `|Pos q a|` — and producing such a
`λ` below an inaccessible needs a *cardinal successor*, i.e. Hartogs' theorem:
that the ordinals injecting into a set `X` form an ordinal not injecting into
`X`.  That in turn needs the Mostowski collapse of well-orderings onto ordinals,
which Foundation does not have and which is a development in its own right —
comparable in size to `Cardinal.lean`.

Equivalently, via `Ind_mem_vsetV_of_cardLE`: bound `|Ind|` directly.  Every node
of a well-founded tree sits at *finite* depth from the root, so `Ind` injects
into the partial labelled functions on finite sequences from `⋃_{q,a} Pos q a`,
giving `|Ind| ≤ 2^{|Seq 𝒫|} < κ` by strong-limitness.  This route needs finite
sequences (an `ω`-recursion, available via `transrec`) and the tree-to-path
encoding, but **no** Hartogs.  It is the cheaper of the two and is the
recommended next step.

Note the practical consequence of the gap being *only* this: the family is a
well-defined set with all its constructors, its recursor and its ι-rule, and the
interpretation can be written against the theorems above.  What is missing is
solely the bound needed to place the family one universe lower.
-/

end Lean4Lean.SetModel
