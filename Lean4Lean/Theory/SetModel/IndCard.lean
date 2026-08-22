import Lean4Lean.Theory.SetModel.IndStage

/-!
# The family is a member of the stage

This closes `Ind S (vsetV κ) ∈ Vset κ`, the last open statement on the model
side, by the cardinality route: `IndStage.Ind_mem_vsetV_of_cardLE` reduces it to
`Ind S (vsetV κ) ≤# c` for some `c ∈ κ`, and this file supplies the injection.

## The idea

Every node of a well-founded tree sits at **finite** depth from the root — that
is the one fact about the fixed point that does not require a cofinality
argument, and it is why this route needs no Hartogs' theorem.  So a tree is
determined by the function

```
finite path  ↦  the constructor tag and non-recursive data at that node
```

which is an element of `℘ (Seq 𝒫 ×ˢ Sig)`, where `Sig` is the set of valid
`⟨q, a⟩ₖ` pairs and `𝒫` is the union of all the recursive-position sets.  Both
are members of `Vset κ`, so `Seq 𝒫 ×ˢ Sig` is too, and strong-limitness bounds
its power set below `κ`.

## Why the recursor, not an auxiliary fixed point

The obvious way to build the path-labelling is a least fixed point on
`Seq 𝒫 ×ˢ D` ("the set of (path, subtree) pairs"), but then one has to prove it
is *functional* in the path, which is a separate induction on path length.
Building the labelling with the **recursor** instead (`indRec`) makes
functionality automatic — a recursor is a function by construction — and reduces
injectivity to one rank induction.

Paths are extended at the *end* (`snoc`), so that a child's code is the parent's
code restricted to paths ending in that child.  Extending at the front would
need an index shift on `ω`; extending at the end needs nothing but `insert`.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Finite sequences -/

section Seq

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Extend the sequence `s` by one entry `b`.  A sequence of length `n` is a
function with domain `n`, so this is a single `insert`. -/
noncomputable def snoc (s b : V) : V := insert (⟨domain s, b⟩ₖ : V) s

instance snoc_definable : ℒₛₑₜ-function₂[V] snoc := by unfold snoc; definability

@[simp] lemma mem_snoc_iff {s b p : V} : p ∈ snoc s b ↔ p = ⟨domain s, b⟩ₖ ∨ p ∈ s :=
  mem_insert

lemma snoc_ne_empty (s b : V) : snoc s b ≠ ∅ := by
  intro h
  have : (⟨domain s, b⟩ₖ : V) ∈ snoc s b := by simp
  rw [h] at this
  exact not_mem_empty this

lemma domain_snoc (s b : V) : domain (snoc s b) = succ (domain s) := by
  rw [snoc, domain_insert]
  rfl

/-- A sequence of length `n` extended by an entry has length `n + 1`. -/
lemma snoc_mem_function {P s b n : V} [IsOrdinal n] (hs : s ∈ (P ^ n : V)) (hb : b ∈ P) :
    snoc s b ∈ (P ^ succ n : V) := by
  have hdom : domain s = n := domain_eq_of_mem_function hs
  have hnn : ∀ y : V, (⟨n, y⟩ₖ : V) ∉ s := by
    intro y hy
    have : n ∈ domain s := mem_domain_of_kpair_mem hy
    rw [hdom] at this
    exact mem_irrefl n this
  refine mem_function.intro (fun p hp ↦ ?_) (fun m hm ↦ ?_)
  · rcases mem_snoc_iff.mp hp with rfl | hps
    · rw [hdom]
      exact kpair_mem_iff.mpr ⟨mem_succ_self n, hb⟩
    · have := subset_prod_of_mem_function hs p hps
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp this
      exact kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hx), hy⟩
  · rcases mem_succ_iff.mp hm with rfl | hmn
    · refine ExistsUnique.intro b (by simp [hdom]) fun y hy ↦ ?_
      rcases mem_snoc_iff.mp hy with he | hs'
      · exact (kpair_inj he).2
      · exact absurd hs' (hnn y)
    · obtain ⟨y, hy, huniq⟩ := exists_unique_of_mem_function hs m hmn
      refine ExistsUnique.intro y (by simp [hy]) fun y' hy' ↦ ?_
      rcases mem_snoc_iff.mp hy' with he | hs'
      · have hm2 : m = domain s := (kpair_inj he).1
        rw [hdom] at hm2
        rw [hm2] at hmn
        exact absurd hmn (mem_irrefl n)
      · exact huniq y' hs'

lemma succ_inj {n m : V} [IsOrdinal n] [IsOrdinal m] (h : succ n = succ m) : n = m := by
  have h1 : n ∈ succ m := h ▸ mem_succ_self n
  have h2 : m ∈ succ n := h ▸ mem_succ_self m
  rcases mem_succ_iff.mp h1 with he | h1'
  · exact he
  · rcases mem_succ_iff.mp h2 with he | h2'
    · exact he.symm
    · exact absurd h2' (mem_asymm h1')

/-- `snoc` is injective on sequences. -/
lemma snoc_inj {P s b s' b' n n' : V} [IsOrdinal n] [IsOrdinal n']
    (hs : s ∈ (P ^ n : V)) (hs' : s' ∈ (P ^ n' : V)) (h : snoc s b = snoc s' b') :
    s = s' ∧ b = b' := by
  have hdom : domain s = n := domain_eq_of_mem_function hs
  have hdom' : domain s' = n' := domain_eq_of_mem_function hs'
  have hnn : ∀ y : V, (⟨n, y⟩ₖ : V) ∉ s := by
    intro y hy
    have hd : n ∈ domain s := mem_domain_of_kpair_mem hy
    rw [hdom] at hd
    exact mem_irrefl n hd
  have hnn' : ∀ y : V, (⟨n', y⟩ₖ : V) ∉ s' := by
    intro y hy
    have hd : n' ∈ domain s' := mem_domain_of_kpair_mem hy
    rw [hdom'] at hd
    exact mem_irrefl n' hd
  have hlen : n = n' := by
    have := congrArg domain h
    rw [domain_snoc, domain_snoc, hdom, hdom'] at this
    exact succ_inj this
  subst hlen
  have hb : b = b' := by
    have hmem : (⟨n, b⟩ₖ : V) ∈ snoc s' b' := by
      rw [← h]
      exact mem_snoc_iff.mpr (Or.inl (by rw [hdom]))
    rcases mem_snoc_iff.mp hmem with he | hs''
    · rw [hdom'] at he
      exact (kpair_inj he).2
    · exact absurd hs'' (hnn' b)
  subst hb
  refine ⟨subset_antisymm (fun p hp ↦ ?_) (fun p hp ↦ ?_), rfl⟩
  · have : p ∈ snoc s' b := h ▸ mem_snoc_iff.mpr (Or.inr hp)
    rcases mem_snoc_iff.mp this with rfl | hp'
    · rw [hdom'] at hp
      exact absurd hp (hnn b)
    · exact hp'
  · have : p ∈ snoc s b := h.symm ▸ mem_snoc_iff.mpr (Or.inr hp)
    rcases mem_snoc_iff.mp this with rfl | hp'
    · rw [hdom] at hp
      exact absurd hp (hnn' b)
    · exact hp'

/-- The set of finite sequences from `P`. -/
noncomputable def Seq (P : V) : V := ⋃ˢ (repl (fun n ↦ (P ^ n : V)) (by definability) ω)

lemma mem_Seq_iff {P s : V} : s ∈ Seq P ↔ ∃ n ∈ (ω : V), s ∈ (P ^ n : V) := by
  rw [Seq, mem_sUnion_iff]
  constructor
  · rintro ⟨w, hw, hsw⟩
    obtain ⟨n, hn, rfl⟩ := (repl_spec _).mp hw
    exact ⟨n, hn, hsw⟩
  · rintro ⟨n, hn, hsn⟩
    exact ⟨(P ^ n : V), (repl_spec _).mpr ⟨n, hn, rfl⟩, hsn⟩

lemma empty_mem_Seq (P : V) : (∅ : V) ∈ Seq P := by
  refine mem_Seq_iff.mpr ⟨0, zero_mem_ω, ?_⟩
  refine mem_function.intro (by simp) (fun x hx ↦ ?_)
  rw [zero_def] at hx
  exact absurd hx not_mem_empty

lemma snoc_inj_Seq {P s b s' b' : V} (hs : s ∈ Seq P) (hs' : s' ∈ Seq P)
    (h : snoc s b = snoc s' b') : s = s' ∧ b = b' := by
  obtain ⟨n, hn, hsn⟩ := mem_Seq_iff.mp hs
  obtain ⟨n', hn', hsn'⟩ := mem_Seq_iff.mp hs'
  have hno : IsOrdinal n := IsOrdinal.nat hn
  have hno' : IsOrdinal n' := IsOrdinal.nat hn'
  exact snoc_inj hsn hsn' h

lemma snoc_mem_Seq {P s b : V} (hs : s ∈ Seq P) (hb : b ∈ P) : snoc s b ∈ Seq P := by
  obtain ⟨n, hn, hsn⟩ := mem_Seq_iff.mp hs
  have hno : IsOrdinal n := IsOrdinal.nat hn
  exact mem_Seq_iff.mpr ⟨succ n, ω_succ_closed hn, snoc_mem_function hsn hb⟩

end Seq

/-! ## The ambient sets: labels, positions, paths, codes -/

section Ambient

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}

/-- All non-recursive data of all constructors. -/
noncomputable def fldSet (S : IndSignature V) : V := ⋃ˢ (repl S.Fld S.Fld_definable S.Q)

lemma mem_fldSet {q a : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q) : a ∈ fldSet S :=
  mem_sUnion_iff.mpr ⟨S.Fld q, (repl_spec _).mpr ⟨q, hq, rfl⟩, ha⟩

/-- The valid `⟨q, a⟩ₖ` pairs — the labels of the tree encoding. -/
noncomputable def sigSet (S : IndSignature V) : V :=
  {p ∈ S.Q ×ˢ fldSet S ; ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, p = ⟨q, a⟩ₖ}

lemma mem_sigSet {q a : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q) : (⟨q, a⟩ₖ : V) ∈ sigSet S :=
  mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hq, mem_fldSet hq ha⟩, q, hq, a, ha, rfl⟩

lemma sigSet_spec {p : V} (hp : p ∈ sigSet S) : ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, p = ⟨q, a⟩ₖ :=
  (mem_sep_iff.mp hp).2

/-- All recursive positions of all constructors. -/
noncomputable def posSet (S : IndSignature V) : V :=
  ⋃ˢ (repl (fun p ↦ S.Pos (kpair.π₁ p) (kpair.π₂ p)) (by definability) (sigSet S))

lemma mem_posSet {q a b : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q) (hb : b ∈ S.Pos q a) :
    b ∈ posSet S := by
  refine mem_sUnion_iff.mpr ⟨S.Pos q a, (repl_spec _).mpr ⟨⟨q, a⟩ₖ, mem_sigSet hq ha, ?_⟩, hb⟩
  simp

/-- The codes: partial labellings of finite paths. -/
noncomputable def codeSet (S : IndSignature V) : V := ℘ (Seq (posSet S) ×ˢ sigSet S)

lemma mem_codeSet_iff {c : V} : c ∈ codeSet S ↔ c ⊆ Seq (posSet S) ×ˢ sigSet S := mem_power_iff

variable (hk : IsInaccessible k) (hS : IsStageSignature k S)

include hk hS

lemma fldSet_mem_vsetV : fldSet S ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  exact sUnion_mem_Vset (mem_vsetV_iff_mem_Vset.mp
    (repl_mem_vsetV' hk hS.q_mem S.Fld S.Fld_definable hS.fld_mem))

lemma sigSet_mem_vsetV : sigSet S ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  refine mem_Vset_of_subset_of_mem sep_subset (prod_mem_Vset hk.isLimitOrdinal ?_ ?_)
  · exact mem_vsetV_iff_mem_Vset.mp hS.q_mem
  · exact mem_vsetV_iff_mem_Vset.mp (fldSet_mem_vsetV hk hS)

lemma posSet_mem_vsetV : posSet S ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hval : ∀ p ∈ sigSet S, S.Pos (kpair.π₁ p) (kpair.π₂ p) ∈ vsetV k := by
    intro p hp
    obtain ⟨q, hq, a, ha, rfl⟩ := sigSet_spec hp
    simpa using hS.pos_mem q hq a ha
  rw [mem_vsetV_iff_mem_Vset]
  exact sUnion_mem_Vset (mem_vsetV_iff_mem_Vset.mp
    (repl_mem_vsetV' hk (sigSet_mem_vsetV hk hS) _ (by definability) hval))

omit hS in
lemma Seq_mem_vsetV (P : V) (hP : P ∈ vsetV k) : Seq P ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hω : (ω : V) ∈ vsetV k := mem_vsetV_of_mem hk.omega_mem
  have hval : ∀ n ∈ (ω : V), (P ^ n : V) ∈ vsetV k := by
    intro n hn
    have hnm : n ∈ Vset (IsOrdinal.toOrdinal k : Ordinal V) :=
      subset_Vset_of_mem_Vset (mem_vsetV_iff_mem_Vset.mp hω) n hn
    rw [mem_vsetV_iff_mem_Vset]
    exact function_mem_Vset hk.isLimitOrdinal hnm (mem_vsetV_iff_mem_Vset.mp hP)
  rw [mem_vsetV_iff_mem_Vset]
  exact sUnion_mem_Vset (mem_vsetV_iff_mem_Vset.mp
    (repl_mem_vsetV' hk hω _ (by definability) hval))

lemma codeSet_mem_vsetV : codeSet S ∈ vsetV k := by
  have hko : IsOrdinal k := hk.isOrdinal
  rw [mem_vsetV_iff_mem_Vset]
  refine power_mem_Vset hk.isLimitOrdinal (prod_mem_Vset hk.isLimitOrdinal ?_ ?_)
  · exact mem_vsetV_iff_mem_Vset.mp (Seq_mem_vsetV hk _ (posSet_mem_vsetV hk hS))
  · exact mem_vsetV_iff_mem_Vset.mp (sigSet_mem_vsetV hk hS)

end Ambient

/-! ## The code of a tree, built with the recursor -/

section Code

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}

/-- The children's codes, each with the child's position appended to every
path. -/
noncomputable def shiftCodes (S : IndSignature V) (h : V) : V :=
  {p ∈ Seq (posSet S) ×ˢ sigSet S ;
    ∃ b ∈ domain h, ∃ s l : V, (⟨s, l⟩ₖ : V) ∈ h ‘ b ∧ p = ⟨snoc s b, l⟩ₖ}

lemma mem_shiftCodes_iff {h p : V} :
    p ∈ shiftCodes S h ↔ p ∈ Seq (posSet S) ×ˢ sigSet S ∧
      ∃ b ∈ domain h, ∃ s l : V, (⟨s, l⟩ₖ : V) ∈ h ‘ b ∧ p = ⟨snoc s b, l⟩ₖ := mem_sep_iff

instance shiftCodes_definable (S : IndSignature V) : ℒₛₑₜ-function₁[V] (shiftCodes S) := by
  suffices ℒₛₑₜ-relation[V] (fun T h ↦ T = shiftCodes S h) by exact this
  have e : ∀ T h : V, T = shiftCodes S h ↔ ∀ p, p ∈ T ↔ p ∈ Seq (posSet S) ×ˢ sigSet S ∧
      ∃ b ∈ domain h, ∃ s l : V, (⟨s, l⟩ₖ : V) ∈ h ‘ b ∧ p = ⟨snoc s b, l⟩ₖ := by
    intro T h
    rw [mem_ext_iff]
    simp [shiftCodes]
  simp only [e]
  definability

/-- The minor premise of the coding recursor: the label at the root, together
with the children's codes shifted by their positions. -/
noncomputable def codeMinor (S : IndSignature V) (q a _f h : V) : V :=
  insert (⟨(∅ : V), (⟨q, a⟩ₖ : V)⟩ₖ : V) (shiftCodes S h)

instance codeMinor_definable (S : IndSignature V) : ℒₛₑₜ-function₄[V] (codeMinor S) := by
  unfold codeMinor; definability

lemma isMinorPremise_codeMinor : IsMinorPremise S (vsetV k) (codeSet S) (codeMinor S) := by
  refine ⟨fun q hq a ha f hf h hh ↦ mem_codeSet_iff.mpr fun p hp ↦ ?_⟩
  rcases mem_insert.mp hp with rfl | hsh
  · exact kpair_mem_iff.mpr ⟨empty_mem_Seq _, mem_sigSet hq ha⟩
  · exact (mem_shiftCodes_iff.mp hsh).1

/-- The code of a tree. -/
noncomputable def Code (S : IndSignature V) (k : V) : V → V :=
  indRec S (vsetV k) (codeSet S) (codeMinor S) (codeMinor_definable S)

/-- Appending a position is injective, so the shift is invertible. -/
lemma mem_shiftCodes_snoc_iff {h b s l : V} (hb : b ∈ domain h) (hbP : b ∈ posSet S)
    (hcod : ∀ b' ∈ domain h, h ‘ b' ⊆ Seq (posSet S) ×ˢ sigSet S)
    (hs : s ∈ Seq (posSet S)) (hl : l ∈ sigSet S) :
    (⟨snoc s b, l⟩ₖ : V) ∈ shiftCodes S h ↔ (⟨s, l⟩ₖ : V) ∈ h ‘ b := by
  constructor
  · intro hmem
    obtain ⟨-, b', hb', s', l', hsl', he⟩ := mem_shiftCodes_iff.mp hmem
    obtain ⟨hsn, rfl⟩ := kpair_inj he
    have hs' : s' ∈ Seq (posSet S) := (kpair_mem_iff.mp (hcod b' hb' _ hsl')).1
    obtain ⟨rfl, rfl⟩ := snoc_inj_Seq hs hs' hsn
    exact hsl'
  · intro hmem
    exact mem_shiftCodes_iff.mpr
      ⟨kpair_mem_iff.mpr ⟨snoc_mem_Seq hs hbP, hl⟩, b, hb, s, l, hmem, rfl⟩

end Code

/-! ## The code is injective, and the family is a member of the stage -/

section Main

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {k : V} {S : IndSignature V}

instance Code_definable (S : IndSignature V) (k : V) : ℒₛₑₜ-function₁[V] (Code S k) := by
  unfold Code; infer_instance

lemma fst_ne_empty_of_mem_shiftCodes {h l s : V}
    (hmem : (⟨s, l⟩ₖ : V) ∈ shiftCodes S h) : s ≠ ∅ := by
  obtain ⟨-, b, -, s', l', -, he⟩ := mem_shiftCodes_iff.mp hmem
  rw [(kpair_inj he).1]
  exact snoc_ne_empty s' b

variable (hk : IsInaccessible k) (hS : IsStageSignature k S) (hWF : S.WF)

include hk hS hWF

/-- **The code determines the tree.**  One rank induction: the root labels agree
because the empty path occurs only at the root, and the children's codes agree
because `snoc` is injective. -/
theorem Code_inj : ∀ x i j y : V,
    (⟨i, x⟩ₖ : V) ∈ Ind S (vsetV k) → (⟨j, y⟩ₖ : V) ∈ Ind S (vsetV k) →
    Code S k (⟨i, x⟩ₖ) = Code S k (⟨j, y⟩ₖ) → x = y := by
  have hD : IsIndCarrier S (vsetV k) := isIndCarrier_vsetV hk hS
  have hE : IsMinorPremise S (vsetV k) (codeSet S) (codeMinor S) := isMinorPremise_codeMinor
  refine rank_induction (fun x ↦ ∀ i j y : V,
    (⟨i, x⟩ₖ : V) ∈ Ind S (vsetV k) → (⟨j, y⟩ₖ : V) ∈ Ind S (vsetV k) →
    Code S k (⟨i, x⟩ₖ) = Code S k (⟨j, y⟩ₖ) → x = y) (by definability) ?_
  intro x ih i j y hx hy hcode
  obtain ⟨q, hq, a, ha, f, hf, hrec, hex⟩ := (mem_Ind_iff_stage hk hS hWF).mp hx
  obtain ⟨q', hq', a', ha', f', hf', hrec', hey⟩ := (mem_Ind_iff_stage hk hS hWF).mp hy
  obtain ⟨-, hxv⟩ := kpair_inj hex
  obtain ⟨-, hyv⟩ := kpair_inj hey
  simp only [Code] at hcode
  rw [hex, hey, indRec_indCtor hWF hD hE hq ha hf hrec,
    indRec_indCtor hWF hD hE hq' ha' hf' hrec'] at hcode
  -- the root labels agree
  have hlab : (⟨q, a⟩ₖ : V) = ⟨q', a'⟩ₖ := by
    have h1 : (⟨(∅ : V), (⟨q, a⟩ₖ : V)⟩ₖ : V) ∈ codeMinor S q a f
        (indRecTuple S (vsetV k) (codeSet S) (codeMinor S) (codeMinor_definable S) q a f) :=
      mem_insert.mpr (Or.inl rfl)
    rw [hcode] at h1
    rcases mem_insert.mp h1 with he | hsh
    · exact (kpair_inj he).2
    · exact absurd rfl (fst_ne_empty_of_mem_shiftCodes hsh)
  obtain ⟨rfl, rfl⟩ := kpair_inj hlab
  set T := indRecTuple S (vsetV k) (codeSet S) (codeMinor S) (codeMinor_definable S) q a f
    with hTdef
  set T' := indRecTuple S (vsetV k) (codeSet S) (codeMinor S) (codeMinor_definable S) q a f'
    with hT'def
  -- the shifted children's codes agree
  have hshift : shiftCodes S T = shiftCodes S T' := by
    refine subset_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · have h2 : z ∈ codeMinor S q a f T := mem_insert.mpr (Or.inr hz)
      rw [hcode] at h2
      rcases mem_insert.mp h2 with rfl | h3
      · exact absurd rfl (fst_ne_empty_of_mem_shiftCodes hz)
      · exact h3
    · have h2 : z ∈ codeMinor S q a f' T' := mem_insert.mpr (Or.inr hz)
      rw [← hcode] at h2
      rcases mem_insert.mp h2 with rfl | h3
      · exact absurd rfl (fst_ne_empty_of_mem_shiftCodes hz)
      · exact h3
  -- hence the children's codes agree pointwise
  have hTmem : T ∈ (codeSet S ^ S.Pos q a : V) := indRecTuple_mem_function hWF hD hE hrec
  have hT'mem : T' ∈ (codeSet S ^ S.Pos q a : V) := indRecTuple_mem_function hWF hD hE hrec'
  have hdomT : domain T = S.Pos q a := domain_eq_of_mem_function hTmem
  have hdomT' : domain T' = S.Pos q a := domain_eq_of_mem_function hT'mem
  have hcodT : ∀ b' ∈ domain T, T ‘ b' ⊆ Seq (posSet S) ×ˢ sigSet S := by
    intro b' hb'
    rw [hdomT] at hb'
    exact mem_codeSet_iff.mp (value_mem_of_mem_function hTmem hb')
  have hcodT' : ∀ b' ∈ domain T', T' ‘ b' ⊆ Seq (posSet S) ×ˢ sigSet S := by
    intro b' hb'
    rw [hdomT'] at hb'
    exact mem_codeSet_iff.mp (value_mem_of_mem_function hT'mem hb')
  have hval : ∀ b ∈ S.Pos q a, T ‘ b = T' ‘ b := by
    intro b hb
    have hbT : b ∈ domain T := hdomT ▸ hb
    have hbT' : b ∈ domain T' := hdomT' ▸ hb
    have hbP : b ∈ posSet S := mem_posSet hq ha hb
    refine subset_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · obtain ⟨s, hs, l, hl, rfl⟩ := mem_prod_iff.mp (hcodT b hbT _ hz)
      have h1 := (mem_shiftCodes_snoc_iff hbT hbP hcodT hs hl).mpr hz
      rw [hshift] at h1
      exact (mem_shiftCodes_snoc_iff hbT' hbP hcodT' hs hl).mp h1
    · obtain ⟨s, hs, l, hl, rfl⟩ := mem_prod_iff.mp (hcodT' b hbT' _ hz)
      have h1 := (mem_shiftCodes_snoc_iff hbT' hbP hcodT' hs hl).mpr hz
      rw [← hshift] at h1
      exact (mem_shiftCodes_snoc_iff hbT hbP hcodT hs hl).mp h1
  -- and so the recursive components agree, by the induction hypothesis
  have hff : ∀ b ∈ S.Pos q a, f ‘ b = f' ‘ b := by
    intro b hb
    have hcb : Code S k (⟨S.posIdx q a b, f ‘ b⟩ₖ) = Code S k (⟨S.posIdx q a b, f' ‘ b⟩ₖ) := by
      have e1 : T ‘ b = Code S k (⟨S.posIdx q a b, f ‘ b⟩ₖ) := by
        simp only [Code, hTdef]
        exact indRecTuple_value hWF hD hE hrec hb
      have e2 : T' ‘ b = Code S k (⟨S.posIdx q a b, f' ‘ b⟩ₖ) := by
        simp only [Code, hT'def]
        exact indRecTuple_value hWF hD hE hrec' hb
      rw [← e1, ← e2]
      exact hval b hb
    have hrk : rank (f ‘ b) < rank x := by
      rw [hxv]
      exact rank_lt_indCtorVal (kpair_value_mem hf hb)
    exact ih (f ‘ b) hrk (S.posIdx q a b) (S.posIdx q a b) (f' ‘ b)
      (hrec b hb) (hrec' b hb) hcb
  have hfeq : f = f' := by
    refine function_ext hf hf' fun b hb z hz hzf ↦ ?_
    have hfun : IsFunction f := IsFunction.of_mem hf
    have : f ‘ b = z := value_eq_of_kpair_mem hzf
    rw [← this, hff b hb]
    exact kpair_value_mem hf' hb
  rw [hxv, hyv, hfeq]

/-- **The family injects into the codes.** -/
theorem Ind_cardLE_codeSet : Ind S (vsetV k) ≤# codeSet S := by
  refine cardLE_of_definable_injOn (Code S k) (by definability) (fun p hp ↦ ?_)
    (fun p hp p' hp' he ↦ ?_)
  · exact indRec_mem hWF (isIndCarrier_vsetV hk hS) isMinorPremise_codeMinor hp
  · obtain ⟨q, hq, a, ha, f, hf, hrec, hep⟩ := (mem_Ind_iff_stage hk hS hWF).mp hp
    obtain ⟨q', hq', a', ha', f', hf', hrec', hep'⟩ := (mem_Ind_iff_stage hk hS hWF).mp hp'
    have hep2 : p = ⟨S.resIdx q a, indCtorVal q a f⟩ₖ := hep
    have hep2' : p' = ⟨S.resIdx q' a', indCtorVal q' a' f'⟩ₖ := hep'
    have hxy : indCtorVal q a f = indCtorVal q' a' f' := by
      refine Code_inj hk hS hWF (indCtorVal q a f) (S.resIdx q a) (S.resIdx q' a')
        (indCtorVal q' a' f') (hep2 ▸ hp) (hep2' ▸ hp') ?_
      rw [← hep2, ← hep2']
      exact he
    obtain ⟨rfl, hrest⟩ := kpair_inj hxy
    obtain ⟨rfl, rfl⟩ := kpair_inj hrest
    rw [hep2, hep2']

omit hWF in
lemma codeSet_cardLE_mem : ∃ c ∈ k, codeSet S ≤# c := by
  have hko : IsOrdinal k := hk.isOrdinal
  have hprod : (Seq (posSet S) ×ˢ sigSet S : V) ∈ vsetV k := by
    rw [mem_vsetV_iff_mem_Vset]
    refine prod_mem_Vset hk.isLimitOrdinal ?_ ?_
    · exact mem_vsetV_iff_mem_Vset.mp (Seq_mem_vsetV hk _ (posSet_mem_vsetV hk hS))
    · exact mem_vsetV_iff_mem_Vset.mp (sigSet_mem_vsetV hk hS)
  obtain ⟨a, hak, ha⟩ := exists_cardLE_of_mem_vsetV hk hprod
  obtain ⟨c, hck, hc⟩ := hk.strongLimit a hak
  exact ⟨c, hck, CardLE.trans (power_cardLE_power ha) hc⟩

/-- **The inductive family is a member of the stage.**  The last open statement
on the model side. -/
theorem Ind_mem_vsetV : Ind S (vsetV k) ∈ vsetV k := by
  obtain ⟨c, hck, hc⟩ := codeSet_cardLE_mem hk hS
  exact Ind_mem_vsetV_of_cardLE hk hS hck (CardLE.trans (Ind_cardLE_codeSet hk hS hWF) hc)

end Main

/-! ### In the universe sequence -/

section U

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] {n : ℕ} {κ : ℕ → V} {i : ℕ}
  {S : IndSignature V}

/-- **Formation, outright**: an inductive family whose components live in
`U (i+1)` is itself an element of `U (i+1)`. -/
theorem Ind_mem_U_stage (hκ : IsInaccessibleChain n κ) (hi : i < n)
    (hS : IsStageSignature (κ i) S) (hWF : S.WF) :
    Ind S (U κ (i + 1)) ∈ U κ (i + 1) :=
  Ind_mem_vsetV (hκ.inaccessible i hi) hS hWF

end U

end Lean4Lean.SetModel
