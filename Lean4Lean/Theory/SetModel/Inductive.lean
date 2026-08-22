import Lean4Lean.Theory.SetModel.Universe

/-!
# The set-theoretic interpretation of an indexed inductive family

This is the model-side counterpart of `docs/design-inductive.md` §10, done
**signature-agnostically**: there is no syntax and no `VExpr` here.  The input is
a purely set-theoretic datum `IndSignature` describing one indexed (non-mutual)
inductive family after its parameters have been fixed, and everything is a
theorem about that datum.

## The datum

`docs/design-inductive.md` §2.2 describes a constructor by a *dependent
telescope* of fields, each field either non-recursive or of the shape
`∀ ξ, I p π`.  Semantically that telescope collapses (see §10) to:

* `Fld q` — the set of joint interpretations of the **non-recursive** fields of
  constructor `q` (an iterated dependent sum);
* `Pos q a` — the set of **recursive positions**, i.e. the disjoint union over
  the recursive fields `⟨ξ, π⟩` of the interpretations of their binders `ξ`;
* `posIdx q a b ∈ Idx` — the index `⟦π⟧` at which position `b` recurses;
* `resIdx q a ∈ Idx` — the result index `⟦C.args⟧`.

So the operator of §10 becomes the *polynomial / container* operator

```
Φ(W)(i) = { ⟨q, ⟨a, f⟩ₖ⟩ₖ  |  q ∈ Q, a ∈ Fld q, f : Pos q a → D,
                              (∀ b, f b ∈ W (posIdx q a b)), resIdx q a = i }
```

and elements are **Kuratowski tuples**, as §10 requires for structure eta.

Mutual families are the special case where `Idx` is a disjoint union
`Σ_t Idx_t` and `resIdx`/`posIdx` land in the appropriate summand; nothing below
changes, so the non-mutual indexed treatment already covers the mutual one via
`disjUnion`.

## The one place this does not match §2.2

Design item **F8** allows a later *non-recursive* field's type to mention an
earlier *recursive* field's value.  In that case `Fld q` itself depends on the
family being defined, and the datum above cannot express it: `Fld : V → V` is
`W`-independent by construction.  Everything else in §2.2 — dependent
non-recursive telescopes, recursive fields with binders `ξ` and index arguments
`π`, arbitrarily many constructors, arbitrary index sets — is covered.  See the
module note at the end for what F8 would require.

## The carrier

The construction is stated relative to a **carrier** `D` closed under the
constructor operation (`IsIndCarrier`).  Producing such a `D` for an arbitrary
signature is the transfinite-iteration argument of §10 and needs full
replacement inside `V_κ`, which is blocked on the cardinal-arithmetic gap
recorded in `Inaccessible.lean`.  See `IsIndCarrier` for the precise statement.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

/-!
Foundation registers `DefinableFunction₁.comp` … `DefinableFunction₃.comp` with
the `definability` tactic but stops there, so a definable function of four or
five set arguments is out of the tactic's reach.  The minor premises of a
recursor take four (`q`, `a`, `f`, `h`), so we register the missing rules.
This is a pure `aesop` rule-set addition; Foundation itself is untouched.
-/
attribute [aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp
  Language.DefinableFunction₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Rank of the pieces of a Kuratowski tuple

These are the inequalities that make the recursor's recursion well-founded
(`docs/design-inductive.md` §10: "`rank (f y) < rank f < rank x`").
-/

section RankAux

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

lemma rank_lt_kpair_left (x y : V) : rank x < rank (⟨x, y⟩ₖ : V) :=
  lt_trans (rank_lt_of_mem (show x ∈ ({x} : V) by simp))
    (rank_lt_of_mem (show ({x} : V) ∈ (⟨x, y⟩ₖ : V) by simp [kpair]))

lemma rank_lt_kpair_right (x y : V) : rank y < rank (⟨x, y⟩ₖ : V) :=
  lt_trans (rank_lt_of_mem (show y ∈ ({x, y} : V) by simp))
    (rank_lt_of_mem (show ({x, y} : V) ∈ (⟨x, y⟩ₖ : V) by simp [kpair]))

/-- A value of an internal function has strictly smaller rank than the
function. -/
lemma rank_lt_of_kpair_mem {f b y : V} (h : (⟨b, y⟩ₖ : V) ∈ f) : rank y < rank f :=
  lt_trans (rank_lt_kpair_right b y) (rank_lt_of_mem h)

/-- **Rank induction**, derived from Foundation's transfinite induction on
ordinals.  External well-founded recursion on `V` is *not* available (a model of
`𝗭𝗙` need not be externally well-founded), so this internal form is what the
recursor is built on. -/
theorem rank_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ x : V, (∀ y : V, rank y < rank x → P y) → P x) : ∀ x : V, P x := by
  have key : ∀ α : Ordinal V, ∀ x : V, rankV x = α.val → P x := by
    refine transfinite_induction (fun c ↦ ∀ x : V, rankV x = c → P x) (by definability) ?_
    intro α ihα x hx
    refine ih x fun y hy ↦ ?_
    have hy' : rank y < α := by
      have : rank y < rank x := hy
      have hxe : rank x = α := Ordinal.ext hx
      exact hxe ▸ this
    exact ihα (rank y) hy' y rfl
  intro x
  exact key (rank x) x rfl

end RankAux

/-! ## The signature -/

/-- A set-theoretic constructor signature for one indexed inductive family,
after the parameters have been fixed.  See the module docstring for how this
lines up with `docs/design-inductive.md` §2.2. -/
structure IndSignature (V : Type*) [SetStructure V] where
  /-- The set of indices (the interpretation of the index telescope). -/
  Idx : V
  /-- The set of constructor tags. -/
  Q : V
  /-- `Fld q`: the joint interpretation of the non-recursive fields of `q`. -/
  Fld : V → V
  /-- `Pos q a`: the recursive positions, `Σ_j ⟦ξ_j⟧`. -/
  Pos : V → V → V
  /-- `posIdx q a b ∈ Idx`: the index `⟦π⟧` at which position `b` recurses. -/
  posIdx : V → V → V → V
  /-- `resIdx q a ∈ Idx`: the result index `⟦C.args⟧`. -/
  resIdx : V → V → V
  Fld_definable : ℒₛₑₜ-function₁[V] Fld
  Pos_definable : ℒₛₑₜ-function₂[V] Pos
  posIdx_definable : ℒₛₑₜ-function₃[V] posIdx
  resIdx_definable : ℒₛₑₜ-function₂[V] resIdx

attribute [instance] IndSignature.Fld_definable IndSignature.Pos_definable
  IndSignature.posIdx_definable IndSignature.resIdx_definable

namespace IndSignature

variable (S : IndSignature V)

/-- The index maps land in `Idx`. -/
structure WF : Prop where
  resIdx_mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, S.resIdx q a ∈ S.Idx

end IndSignature

/-! ## The carrier -/

/-- `D` is a **carrier** for `S`: it is closed under the constructor operation.

Producing such a `D` inside `Vset κ` for an arbitrary signature is the
transfinite iteration of `docs/design-inductive.md` §10.  It amounts to full
replacement inside `V_κ` (the recursive-position sets `Pos q a` are arbitrary
members of `V_κ`, so bounding `range f` for `f : Pos q a → V_κ` is exactly the
replacement instance that `repl_mem_vsetV` cannot supply for a non-ordinal index
set).  It is therefore left as a hypothesis; see the note at the end of the
file. -/
structure IsIndCarrier [V↓[ℒₛₑₜ] ⊧* 𝗭] (S : IndSignature V) (D : V) : Prop where
  ctor_mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ f ∈ (D ^ S.Pos q a : V),
    (⟨q, ⟨a, f⟩ₖ⟩ₖ : V) ∈ D

/-! ## The operator and the family -/

section Operator

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (S : IndSignature V) (D : V)

/-- One step of the inductive operator, `Φ` of `docs/design-inductive.md` §10.
The total space of the family is `Idx ×ˢ D`; the fibre over `i` is the family at
index `i`. -/
noncomputable def indStep (W : V) : V :=
  {p ∈ S.Idx ×ˢ D ;
    ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
      p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ}

lemma mem_indStep_iff' {W p : V} :
    p ∈ indStep S D W ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := mem_sep_iff

/-- The bound in `indStep` is redundant once the signature is well-formed and
`D` is a carrier. -/
lemma mem_indStep_iff (hS : S.WF) (hD : IsIndCarrier S D) {W p : V} :
    p ∈ indStep S D W ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := by
  rw [mem_indStep_iff']
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨q, hq, a, ha, f, hf, -, rfl⟩ := h
  exact kpair_mem_iff.mpr ⟨hS.resIdx_mem q hq a ha, hD.ctor_mem q hq a ha f hf⟩

lemma indStep_definable : ℒₛₑₜ-function₁[V] (indStep S D) := by
  suffices ℒₛₑₜ-relation[V] (fun T W ↦ T = indStep S D W) by exact this
  have e : ∀ T W : V, T = indStep S D W ↔ ∀ p, p ∈ T ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := by
    intro T W
    rw [mem_ext_iff]
    simp [indStep]
  simp only [e]
  definability

lemma indStep_isMonotoneOn : IsMonotoneOn (S.Idx ×ˢ D) (indStep S D) where
  mono W₁ W₂ h p hp := by
    rw [mem_indStep_iff'] at hp ⊢
    obtain ⟨hb, q, hq, a, ha, f, hf, hrec, he⟩ := hp
    exact ⟨hb, q, hq, a, ha, f, hf, fun b hbp ↦ h _ (hrec b hbp), he⟩
  maps := sep_subset

/-- **The inductive family**, as the least fixed point of `Φ` inside
`Idx ×ˢ D`.  Formation is free: `lfp_mem_Vset` needs no hypothesis on the
universe level at all. -/
noncomputable def Ind : V := lfp (S.Idx ×ˢ D) (indStep S D) (indStep_definable S D)

theorem Ind_subset : Ind S D ⊆ S.Idx ×ˢ D := lfp_subset (indStep_isMonotoneOn S D)

theorem indStep_Ind : indStep S D (Ind S D) = Ind S D :=
  apply_lfp (indStep_isMonotoneOn S D)

end Operator

/-! ## Constructors, no confusion, and the induction principle -/

section Ctors

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D : V}

/-- The untagged element of the carrier built by constructor `q`: the
Kuratowski tuple `⟨q, ⟨a, f⟩ₖ⟩ₖ`.  §10 insists on a *tuple* here (not an
arbitrary tagged set) so that surjective pairing, hence structure eta, holds on
the nose. -/
noncomputable def indCtorVal (q a f : V) : V := ⟨q, ⟨a, f⟩ₖ⟩ₖ

/-- The constructor application, tagged with its result index. -/
noncomputable def indCtor (S : IndSignature V) (q a f : V) : V :=
  ⟨S.resIdx q a, indCtorVal q a f⟩ₖ

instance indCtorVal_definable : ℒₛₑₜ-function₃[V] (indCtorVal : V → V → V → V) := by
  unfold indCtorVal; definability

instance indCtor_definable (S : IndSignature V) : ℒₛₑₜ-function₃[V] (indCtor S) := by
  unfold indCtor; definability

/-- **Constructors land in the family.** -/
theorem ctor_mem_Ind (hS : S.WF) (hD : IsIndCarrier S D)
    {q a f : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q) (hf : f ∈ (D ^ S.Pos q a : V))
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) :
    indCtor S q a f ∈ Ind S D := by
  rw [← indStep_Ind S D, mem_indStep_iff S D hS hD]
  exact ⟨q, hq, a, ha, f, hf, hrec, rfl⟩

/-- **No junk**: every element of the family is a constructor application whose
recursive components are again in the family. -/
theorem mem_Ind_iff (hS : S.WF) (hD : IsIndCarrier S D) {p : V} :
    p ∈ Ind S D ↔ ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) ∧
        p = indCtor S q a f := by
  conv_lhs => rw [← indStep_Ind S D]
  exact mem_indStep_iff S D hS hD

/-- **Constructors are injective.** -/
theorem indCtor_inj {q a f q' a' f' : V}
    (h : indCtor S q a f = indCtor S q' a' f') : q = q' ∧ a = a' ∧ f = f' := by
  obtain ⟨-, h⟩ := kpair_inj h
  obtain ⟨hq, h⟩ := kpair_inj h
  obtain ⟨ha, hf⟩ := kpair_inj h
  exact ⟨hq, ha, hf⟩

@[simp] theorem indCtor_eq_iff {q a f q' a' f' : V} :
    indCtor S q a f = indCtor S q' a' f' ↔ q = q' ∧ a = a' ∧ f = f' := by
  refine ⟨indCtor_inj, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  rfl

/-- **No confusion**: the images of distinct constructors are disjoint. -/
theorem indCtor_ne_of_tag_ne {q a f q' a' f' : V} (h : q ≠ q') :
    indCtor S q a f ≠ indCtor S q' a' f' := fun he ↦ h (indCtor_inj he).1

/-- **The induction principle** (elimination into a `Prop`-valued motive,
i.e. into a subset): `Ind S D` is the least set closed under the
constructors. -/
theorem Ind_induction {P : V} (hP : P ⊆ S.Idx ×ˢ D)
    (hstep : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ f ∈ (D ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ P) → indCtor S q a f ∈ P) :
    Ind S D ⊆ P := by
  refine lfp_subset_of_prefixed (indStep_isMonotoneOn S D) hP fun p hp ↦ ?_
  rw [mem_indStep_iff'] at hp
  obtain ⟨-, q, hq, a, ha, f, hf, hrec, rfl⟩ := hp
  exact hstep q hq a ha f hf hrec

/-- The family at a single index. -/
noncomputable def IndFiber (S : IndSignature V) (D i : V) : V :=
  {x ∈ D ; (⟨i, x⟩ₖ : V) ∈ Ind S D}

lemma mem_IndFiber_iff {i x : V} :
    x ∈ IndFiber S D i ↔ x ∈ D ∧ (⟨i, x⟩ₖ : V) ∈ Ind S D := mem_sep_iff

lemma mem_IndFiber_of_mem_Ind {i x : V} (h : (⟨i, x⟩ₖ : V) ∈ Ind S D) :
    x ∈ IndFiber S D i :=
  mem_IndFiber_iff.mpr ⟨(kpair_mem_iff.mp (Ind_subset S D _ h)).2, h⟩

end Ctors

/-! ### The family lives in the stage -/

section Stage

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {n : ℕ} {κ : ℕ → V} {i : ℕ} {S : IndSignature V} {D : V}

/-- **Formation is free.**  `lfp_mem_U` needs nothing about the universe level,
so the only cost is having `Idx ×ˢ D` in the stage. -/
theorem Ind_mem_U (hκ : IsInaccessibleChain n κ) (hi : i < n)
    (hIdx : S.Idx ∈ U κ (i + 1)) (hD : D ∈ U κ (i + 1)) : Ind S D ∈ U κ (i + 1) :=
  lfp_mem_U (hκ.inaccessible i hi).isOrdinal (indStep_isMonotoneOn S D)
    (prod_mem_U hκ hi hIdx hD)

theorem IndFiber_mem_U (hko : IsOrdinal (κ i)) (hD : D ∈ U κ (i + 1)) {x : V} :
    IndFiber S D x ∈ U κ (i + 1) := sep_mem_U hko hD _

end Stage

/-! ## The recursor, by ∈-rank recursion

`docs/design-inductive.md` §10: "Recursor: by ∈-rank recursion on the fixed
point.  Total because every element is `(q, φ)` with the recursive components of
`φ` of strictly smaller rank."  Carneiro's equation is `F(a,f) = e(a)(f)(F ∘ f)`.

External well-founded recursion is unavailable (a model of `𝗭𝗙` need not be
externally well-founded), so the recursor is built **internally**: its graph is
another least fixed point, single-valued by `rank_induction` and total by
`Ind_induction`.
-/

section Recursor

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D R : V}
  {e : V → V → V → V → V}

/-- The minor premises are bounded by `R`, the codomain of the recursor. -/
structure IsMinorPremise (S : IndSignature V) (D R : V) (e : V → V → V → V → V) : Prop where
  mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ f ∈ (D ^ S.Pos q a : V), ∀ h ∈ (R ^ S.Pos q a : V),
    e q a f h ∈ R

/-- One step of the recursor's graph. -/
noncomputable def recStep (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (g : V) : V :=
  {p ∈ (S.Idx ×ˢ D) ×ˢ R ;
    ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), ∃ h ∈ (R ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
      p = ⟨indCtor S q a f, e q a f h⟩ₖ}

lemma mem_recStep_iff' {he : ℒₛₑₜ-function₄[V] e} {g p : V} :
    p ∈ recStep S D R e he g ↔ p ∈ (S.Idx ×ˢ D) ×ˢ R ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), ∃ h ∈ (R ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor S q a f, e q a f h⟩ₖ := mem_sep_iff

lemma mem_recStep_iff (hS : S.WF) (hD : IsIndCarrier S D) (hE : IsMinorPremise S D R e)
    {he : ℒₛₑₜ-function₄[V] e} {g p : V} :
    p ∈ recStep S D R e he g ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), ∃ h ∈ (R ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor S q a f, e q a f h⟩ₖ := by
  rw [mem_recStep_iff']
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨q, hq, a, ha, f, hf, h, hh, -, rfl⟩ := h
  exact kpair_mem_iff.mpr
    ⟨kpair_mem_iff.mpr ⟨hS.resIdx_mem q hq a ha, hD.ctor_mem q hq a ha f hf⟩,
      hE.mem q hq a ha f hf h hh⟩

lemma recStep_definable (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : ℒₛₑₜ-function₁[V] (recStep S D R e he) := by
  suffices ℒₛₑₜ-relation[V] (fun T g ↦ T = recStep S D R e he g) by exact this
  have eq : ∀ T g : V, T = recStep S D R e he g ↔ ∀ p, p ∈ T ↔ p ∈ (S.Idx ×ˢ D) ×ˢ R ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), ∃ h ∈ (R ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor S q a f, e q a f h⟩ₖ := by
    intro T g
    rw [mem_ext_iff]
    simp [recStep, indCtor, indCtorVal]
  simp only [eq]
  definability

lemma recStep_isMonotoneOn (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : IsMonotoneOn ((S.Idx ×ˢ D) ×ˢ R) (recStep S D R e he) where
  mono g₁ g₂ hg p hp := by
    rw [mem_recStep_iff'] at hp ⊢
    obtain ⟨hb, q, hq, a, ha, f, hf, h, hh, hrec, heq⟩ := hp
    exact ⟨hb, q, hq, a, ha, f, hf, h, hh, fun b hbp ↦ hg _ (hrec b hbp), heq⟩
  maps := sep_subset

/-- The graph of the recursor. -/
noncomputable def recGraph (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : V :=
  lfp ((S.Idx ×ˢ D) ×ˢ R) (recStep S D R e he) (recStep_definable S D R e he)

theorem recGraph_subset {he : ℒₛₑₜ-function₄[V] e} :
    recGraph S D R e he ⊆ (S.Idx ×ˢ D) ×ˢ R := lfp_subset (recStep_isMonotoneOn S D R e he)

theorem recStep_recGraph {he : ℒₛₑₜ-function₄[V] e} :
    recStep S D R e he (recGraph S D R e he) = recGraph S D R e he :=
  apply_lfp (recStep_isMonotoneOn S D R e he)

lemma mem_recGraph_iff (hS : S.WF) (hD : IsIndCarrier S D) (hE : IsMinorPremise S D R e)
    {he : ℒₛₑₜ-function₄[V] e} {p : V} :
    p ∈ recGraph S D R e he ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), ∃ h ∈ (R ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a,
          (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ recGraph S D R e he) ∧
        p = ⟨indCtor S q a f, e q a f h⟩ₖ := by
  conv_lhs => rw [← recStep_recGraph (S := S) (D := D) (R := R) (e := e) (he := he)]
  exact mem_recStep_iff hS hD hE

end Recursor

/-! ### The recursor is a total function, and its ι-rule -/

section RecursorTotal

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D R : V} {e : V → V → V → V → V}
  {he : ℒₛₑₜ-function₄[V] e}

/-- The rank inequality that drives the recursion: a recursive component of a
constructor application has strictly smaller rank than the application. -/
lemma rank_lt_indCtorVal {q a f b y : V} (h : (⟨b, y⟩ₖ : V) ∈ f) :
    rank y < rank (indCtorVal q a f) :=
  lt_trans (rank_lt_of_kpair_mem h)
    (lt_trans (rank_lt_kpair_right a f) (rank_lt_kpair_right q (⟨a, f⟩ₖ : V)))

lemma kpair_value_mem {X Y g b : V} (hg : g ∈ (Y ^ X : V)) (hb : b ∈ X) :
    (⟨b, g ‘ b⟩ₖ : V) ∈ g := by
  obtain ⟨y, -, hy⟩ := exists_of_mem_function hg b hb
  have : IsFunction g := IsFunction.of_mem hg
  rw [value_eq_of_kpair_mem hy]
  exact hy

variable (hS : S.WF) (hD : IsIndCarrier S D) (hE : IsMinorPremise S D R e)

include hS hD hE

/-- **Single-valuedness of the recursor's graph**, by `rank_induction`.  The
index component of the pair is *not* what the recursion is on — its rank is
uncontrolled — so the induction is on the raw element of the carrier. -/
theorem recGraph_unique : ∀ x i₁ i₂ v₁ v₂ : V,
    (⟨⟨i₁, x⟩ₖ, v₁⟩ₖ : V) ∈ recGraph S D R e he →
    (⟨⟨i₂, x⟩ₖ, v₂⟩ₖ : V) ∈ recGraph S D R e he → v₁ = v₂ := by
  refine rank_induction (fun x ↦ ∀ i₁ i₂ v₁ v₂ : V,
    (⟨⟨i₁, x⟩ₖ, v₁⟩ₖ : V) ∈ recGraph S D R e he →
    (⟨⟨i₂, x⟩ₖ, v₂⟩ₖ : V) ∈ recGraph S D R e he → v₁ = v₂) (by definability) ?_
  intro x ih i₁ i₂ v₁ v₂ h₁ h₂
  obtain ⟨q, hq, a, ha, f, hf, h, hh, hrec, heq⟩ := (mem_recGraph_iff hS hD hE).mp h₁
  obtain ⟨q', hq', a', ha', f', hf', h', hh', hrec', heq'⟩ := (mem_recGraph_iff hS hD hE).mp h₂
  obtain ⟨hc, rfl⟩ := kpair_inj heq
  obtain ⟨hc', rfl⟩ := kpair_inj heq'
  obtain ⟨-, hx⟩ := kpair_inj hc
  obtain ⟨-, hx'⟩ := kpair_inj hc'
  -- `x` determines `q`, `a`, `f`
  obtain ⟨rfl, hp⟩ := kpair_inj (hx ▸ hx' : (indCtorVal q a f : V) = indCtorVal q' a' f')
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  -- the recursive results agree
  suffices hhh : h = h' by rw [hhh]
  refine function_ext hh hh' fun b hb y hy hyh ↦ ?_
  have hfun : IsFunction h := IsFunction.of_mem hh
  have hval : h ‘ b = y := value_eq_of_kpair_mem hyh
  have hrk : rank (f ‘ b) < rank x := by
    rw [hx]
    exact rank_lt_indCtorVal (kpair_value_mem hf hb)
  have := ih (f ‘ b) hrk (S.posIdx q a b) (S.posIdx q a b) (h ‘ b) (h' ‘ b)
    (hrec b hb) (hrec' b hb)
  rw [hval] at this
  rw [this]
  exact kpair_value_mem hh' hb

/-- **Totality**: the recursor's graph is defined on all of the family. -/
theorem recGraph_total : ∀ p ∈ Ind S D, ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph S D R e he := by
  have key : Ind S D ⊆
      {p ∈ S.Idx ×ˢ D ; ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph S D R e he} := by
    refine Ind_induction sep_subset ?_
    intro q hq a ha f hf hrec
    -- assemble the tuple of recursive results by separation (no choice needed:
    -- `recGraph_unique` makes the value unique)
    obtain ⟨h, hmemh⟩ : ∃ h : V, ∀ p : V, p ∈ h ↔ ∃ b ∈ S.Pos q a, ∃ v : V,
        p = ⟨b, v⟩ₖ ∧ (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, v⟩ₖ : V) ∈ recGraph S D R e he := by
      refine ⟨sep (S.Pos q a ×ˢ R) (fun p ↦ ∃ b ∈ S.Pos q a, ∃ v : V,
        p = ⟨b, v⟩ₖ ∧ (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, v⟩ₖ : V) ∈ recGraph S D R e he),
        fun p ↦ ?_⟩
      rw [mem_sep_iff]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      obtain ⟨b, hb, v, rfl, hv⟩ := h
      exact kpair_mem_iff.mpr ⟨hb, (kpair_mem_iff.mp (recGraph_subset _ hv)).2⟩
    have hkp : ∀ b y : V, (⟨b, y⟩ₖ : V) ∈ h ↔ b ∈ S.Pos q a ∧
        (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, y⟩ₖ : V) ∈ recGraph S D R e he := by
      intro b y
      rw [hmemh]
      refine ⟨?_, fun hy ↦ ⟨b, hy.1, y, rfl, hy.2⟩⟩
      rintro ⟨b', hb', v, hev, hv⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj hev
      exact ⟨hb', hv⟩
    have hhmem : h ∈ (R ^ S.Pos q a : V) := by
      refine mem_function.intro (fun p hp ↦ ?_) (fun b hb ↦ ?_)
      · obtain ⟨b, hb, v, rfl, hv⟩ := hmemh p |>.mp hp
        exact kpair_mem_iff.mpr ⟨hb, (kpair_mem_iff.mp (recGraph_subset _ hv)).2⟩
      · obtain ⟨-, v, hv⟩ := mem_sep_iff.mp (hrec b hb)
        refine ExistsUnique.intro v ((hkp b v).mpr ⟨hb, hv⟩) fun v' hv' ↦ ?_
        exact recGraph_unique hS hD hE (f ‘ b) _ _ v' v ((hkp b v').mp hv').2 hv
    refine mem_sep_iff.mpr ⟨kpair_mem_iff.mpr
      ⟨hS.resIdx_mem q hq a ha, hD.ctor_mem q hq a ha f hf⟩,
      e q a f h, (mem_recGraph_iff hS hD hE).mpr
        ⟨q, hq, a, ha, f, hf, h, hhmem, fun b hb ↦ ?_, rfl⟩⟩
    exact ((hkp b (h ‘ b)).mp (kpair_value_mem hhmem hb)).2
  intro p hp
  exact (mem_sep_iff.mp (key p hp)).2

theorem isFunction_recGraph : IsFunction (recGraph S D R e he) := by
  refine isFunction_iff.mpr (mem_function.intro (fun p hp ↦ ?_) (fun x hx ↦ ?_))
  · obtain ⟨q, hq, a, ha, f, hf, h, hh, hrec, rfl⟩ := (mem_recGraph_iff hS hD hE).mp hp
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
  · obtain ⟨v, hv⟩ := mem_domain_iff.mp hx
    refine ExistsUnique.intro v hv fun v' hv' ↦ ?_
    obtain ⟨i, -, y, -, rfl⟩ :=
      mem_prod_iff.mp (kpair_mem_iff.mp (recGraph_subset _ hv)).1
    exact recGraph_unique hS hD hE y i i v' v hv' hv

/-- **The recursor.** -/
noncomputable def indRec (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (p : V) : V := (recGraph S D R e he) ‘ p

theorem indRec_kpair_mem {p : V} (hp : p ∈ Ind S D) :
    (⟨p, indRec S D R e he p⟩ₖ : V) ∈ recGraph S D R e he := by
  obtain ⟨v, hv⟩ := recGraph_total hS hD hE p hp
  have : IsFunction (recGraph S D R e he) := isFunction_recGraph hS hD hE
  rw [indRec, value_eq_of_kpair_mem hv]
  exact hv

theorem indRec_mem {p : V} (hp : p ∈ Ind S D) : indRec S D R e he p ∈ R :=
  (kpair_mem_iff.mp (recGraph_subset _ (indRec_kpair_mem hS hD hE hp))).2

end RecursorTotal

/-! ### The ι-rule -/

section Iota

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D R : V} {e : V → V → V → V → V}
  {he : ℒₛₑₜ-function₄[V] e}

instance indRec_definable (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : ℒₛₑₜ-function₁[V] (indRec S D R e he) := by
  unfold indRec; definability

/-- `F ∘ f`: the internal tuple of recursive results. -/
noncomputable def indRecTuple (S : IndSignature V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (q a f : V) : V :=
  {p ∈ S.Pos q a ×ˢ R ;
    ∃ b ∈ S.Pos q a, p = ⟨b, indRec S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ)⟩ₖ}

variable (hS : S.WF) (hD : IsIndCarrier S D) (hE : IsMinorPremise S D R e)

include hS hD hE

lemma mem_indRecTuple_iff {q a f b y : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) :
    (⟨b, y⟩ₖ : V) ∈ indRecTuple S D R e he q a f ↔
      b ∈ S.Pos q a ∧ y = indRec S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ) := by
  rw [indRecTuple, mem_sep_iff]
  constructor
  · rintro ⟨-, b', hb', hev⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj hev
    exact ⟨hb', rfl⟩
  · rintro ⟨hb, rfl⟩
    exact ⟨kpair_mem_iff.mpr ⟨hb, indRec_mem hS hD hE (hrec b hb)⟩, b, hb, rfl⟩

lemma indRecTuple_mem_function {q a f : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) :
    indRecTuple S D R e he q a f ∈ (R ^ S.Pos q a : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun b hb ↦ ?_)
  · obtain ⟨-, b, hb, rfl⟩ := mem_sep_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hb, indRec_mem hS hD hE (hrec b hb)⟩
  · refine ExistsUnique.intro (indRec S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ))
      ((mem_indRecTuple_iff hS hD hE hrec).mpr ⟨hb, rfl⟩) fun y hy ↦ ?_
    exact ((mem_indRecTuple_iff hS hD hE hrec).mp hy).2

lemma indRecTuple_value {q a f b : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) (hb : b ∈ S.Pos q a) :
    (indRecTuple S D R e he q a f) ‘ b = indRec S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ) := by
  have hfun : IsFunction (indRecTuple S D R e he q a f) :=
    IsFunction.of_mem (indRecTuple_mem_function hS hD hE hrec)
  exact value_eq_of_kpair_mem ((mem_indRecTuple_iff hS hD hE hrec).mpr ⟨hb, rfl⟩)

/-- **The ι-rule.**  `F (ctor q a f) = e q a f (F ∘ f)`, exactly Carneiro's
`F(a,f) = e(a)(f)(F ∘ f)`. -/
theorem indRec_indCtor {q a f : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld q)
    (hf : f ∈ (D ^ S.Pos q a : V))
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S D) :
    indRec S D R e he (indCtor S q a f) = e q a f (indRecTuple S D R e he q a f) := by
  have hfun : IsFunction (recGraph S D R e he) := isFunction_recGraph hS hD hE
  refine value_eq_of_kpair_mem ((mem_recGraph_iff hS hD hE).mpr
    ⟨q, hq, a, ha, f, hf, _, indRecTuple_mem_function hS hD hE hrec, fun b hb ↦ ?_, rfl⟩)
  rw [indRecTuple_value hS hD hE hrec hb]
  exact indRec_kpair_mem hS hD hE (hrec b hb)

end Iota

/-! ## Large versus small elimination

`indRec` above eliminates into an **arbitrary** codomain `R` with an arbitrary
definable minor premise `e`: there is no hypothesis anywhere restricting the
universe level of `R`.  That is the large-eliminating case, and it is free.

The restriction appears only when the family is interpreted in `Prop`.  A
`Prop`-valued inductive is interpreted by `IndProp` below as an element of
`UProp`, which remembers only *whether* the fibre is inhabited, not *which*
element inhabits it — so a recursor into a large motive has no well-defined
value in general.  It does have one exactly when the fibre is a **subsingleton**,
which is `docs/design-inductive.md` §10's `LECond` second disjunct and is why
`Eq` and `Acc` are the exceptions: for both, the single constructor's
non-recursive data is determined by the result index.
-/

section Elimination

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D R : V} {e : V → V → V → V → V}
  {he : ℒₛₑₜ-function₄[V] e}

/-- The set-theoretic form of `docs/design-inductive.md` §10's subsingleton
condition: one constructor, whose non-recursive data is determined by the result
index.  `Eq` and `Acc` both satisfy it — their only non-recursive field is the
index itself. -/
structure IsSubsingletonSignature (S : IndSignature V) : Prop where
  /-- a single constructor -/
  single : ∀ q ∈ S.Q, ∀ q' ∈ S.Q, q = q'
  /-- the non-recursive data is determined by the result index: proof fields are
  subsingletons, and index-determined fields appear in the result arguments -/
  fld_det : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ a' ∈ S.Fld q,
    S.resIdx q a = S.resIdx q a' → a = a'

variable (hS : S.WF) (hD : IsIndCarrier S D)

include hS hD

/-- **The fixed point is a subsingleton at every index**, by ∈-rank induction:
equal constructors, equal non-recursive data (determined by the index), and
equal recursive fields by the induction hypothesis. -/
theorem Ind_subsingleton (hSub : IsSubsingletonSignature S) :
    ∀ x i y : V, (⟨i, x⟩ₖ : V) ∈ Ind S D → (⟨i, y⟩ₖ : V) ∈ Ind S D → x = y := by
  refine rank_induction (fun x ↦ ∀ i y : V,
    (⟨i, x⟩ₖ : V) ∈ Ind S D → (⟨i, y⟩ₖ : V) ∈ Ind S D → x = y) (by definability) ?_
  intro x ih i y hx hy
  obtain ⟨q, hq, a, ha, f, hf, hrec, hex⟩ := (mem_Ind_iff hS hD).mp hx
  obtain ⟨q', hq', a', ha', f', hf', hrec', hey⟩ := (mem_Ind_iff hS hD).mp hy
  obtain ⟨hi, hxv⟩ := kpair_inj hex
  obtain ⟨hi', hyv⟩ := kpair_inj hey
  rcases hSub.single q' hq' q hq
  have haa : a = a' := hSub.fld_det q hq a ha a' ha' (by rw [← hi, ← hi'])
  rcases haa
  suffices hff : f = f' by rw [hxv, hyv, hff]
  refine function_ext hf hf' fun b hb z hz hzf ↦ ?_
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hval : f ‘ b = z := value_eq_of_kpair_mem hzf
  have hrk : rank (f ‘ b) < rank x := by
    rw [hxv]
    exact rank_lt_indCtorVal (kpair_value_mem hf hb)
  have := ih (f ‘ b) hrk (S.posIdx q a b) (f' ‘ b) (hrec b hb) (hrec' b hb)
  rw [hval] at this
  rw [this]
  exact kpair_value_mem hf' hb

/-- **Large elimination is sound for a subsingleton family**: the recursor's
value depends only on the index, not on which proof inhabits the fibre.  This is
exactly what makes `Eq.rec` and `Acc.rec` legal. -/
theorem indRec_indep_of_proof (hSub : IsSubsingletonSignature S) {i x y : V}
    (hx : (⟨i, x⟩ₖ : V) ∈ Ind S D) (hy : (⟨i, y⟩ₖ : V) ∈ Ind S D) :
    indRec S D R e he (⟨i, x⟩ₖ) = indRec S D R e he (⟨i, y⟩ₖ) := by
  rw [Ind_subsingleton hS hD hSub x i y hx hy]

end Elimination

/-! ### The `Prop`-valued interpretation -/

section IndProp

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V} {D : V}

/-- The interpretation of a `Prop`-valued inductive family at index `i`:
`{•}` if the fibre is inhabited, `∅` otherwise (`docs/design-inductive.md` §10,
the `ℓ = 0` case). -/
noncomputable def IndProp (S : IndSignature V) (D i : V) : V :=
  {z ∈ ({pt} : V) ; IsNonempty (IndFiber S D i)}

/-- Formation in `Prop` needs nothing at all: no inaccessible, no limit, not
even the carrier condition. -/
theorem IndProp_mem_UProp (S : IndSignature V) (D i : V) :
    IndProp S D i ∈ (UProp : V) := mem_UProp_iff.mpr sep_subset

theorem IndProp_eq_true_iff {i : V} :
    IndProp S D i = ({pt} : V) ↔ IsNonempty (IndFiber S D i) := by
  rw [← pt_mem_iff_eq_true (IndProp_mem_UProp S D i)]
  simp [IndProp]

end IndProp

/-! ### Non-vacuity: recursion-free families have an explicit carrier

For a family with no recursive fields the carrier is written down directly, so
the whole apparatus above applies with **no** hypotheses left over.  This covers
enumerations, structures, and — relevantly — `Eq`, one of the two subsingleton
eliminators.
-/

section NoRecursion

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {S : IndSignature V}

lemma eq_empty_of_mem_function_empty {Y f : V} (hf : f ∈ (Y ^ (∅ : V) : V)) : f = ∅ := by
  have h := subset_prod_of_mem_function hf
  rw [empty_prod] at h
  exact subset_empty_iff_eq_empty.mp h

/-- A signature with no recursive positions has an explicit carrier. -/
theorem isIndCarrier_of_no_recursion (𝒜 : V)
    (hPos : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, S.Pos q a = ∅)
    (hFld : ∀ q ∈ S.Q, S.Fld q ⊆ 𝒜) :
    IsIndCarrier S (S.Q ×ˢ (𝒜 ×ˢ ({∅} : V))) := by
  refine ⟨fun q hq a ha f hf ↦ ?_⟩
  rw [hPos q hq a ha] at hf
  rcases eq_empty_of_mem_function_empty hf
  exact kpair_mem_iff.mpr ⟨hq, kpair_mem_iff.mpr ⟨hFld q hq a ha, by simp⟩⟩

/-- …and that carrier lives in any limit stage containing the ingredients, so
the family, its constructors and its recursor are all available there. -/
theorem noRecursion_carrier_mem_U {n : ℕ} {κ : ℕ → V} {i : ℕ}
    (hκ : IsInaccessibleChain n κ) (hi : i < n) {𝒜 : V}
    (hQ : S.Q ∈ U κ (i + 1)) (h𝒜 : 𝒜 ∈ U κ (i + 1)) :
    (S.Q ×ˢ (𝒜 ×ˢ ({∅} : V)) : V) ∈ U κ (i + 1) := by
  have hko : IsOrdinal (κ i) := (hκ.inaccessible i hi).isOrdinal
  have hlim := (hκ.inaccessible i hi).isLimitOrdinal
  refine prod_mem_U hκ hi hQ (prod_mem_U hκ hi h𝒜 ?_)
  rw [U_succ, mem_vsetV_iff_mem_Vset]
  exact singleton_mem_Vset hlim (empty_mem_Vset hlim)

end NoRecursion

/-!
## Status, and what remains

**Done, for one indexed (non-mutual) family, signature-agnostically.**
`indStep` / `Ind` (formation, free by `lfp_mem_U`), `indCtor` with `ctor_mem_Ind`,
`mem_Ind_iff` (no junk), `indCtor_inj` and `indCtor_ne_of_tag_ne` (no confusion),
`Ind_induction`, `indRec` with `recGraph_unique` / `recGraph_total` /
`isFunction_recGraph`, the ι-rule `indRec_indCtor`, `Ind_subsingleton` and
`indRec_indep_of_proof`, and `IndProp`.

**Mutual families** are covered as they stand: take `Idx` to be the disjoint
union `disjUnion` of the per-type index sets and have `resIdx`/`posIdx` land in
the appropriate summand.  Nothing in this file assumes `Idx` is indecomposable.

**Not covered — design item F8.**  `IndSignature.Fld : V → V` does not depend on
the family being constructed, so a later non-recursive field whose *type*
mentions an earlier *recursive* field is inexpressible here.  Supporting it
means replacing `Fld q` by a monotone `Fld q : V → V` (a function of the
current approximation `W`) and `Pos`/`posIdx`/`resIdx` by maps defined on the
resulting dependent sum.  `indStep` stays monotone, so formation and the
induction principle survive unchanged; what needs redoing is the rank argument
for the recursor, since the "non-recursive data" `a` would itself contain
elements of the family.  Flagging this now, as requested: **if the syntactic
side really intends to allow F8, this datum must change.**

**Not covered — existence of the carrier `D`.**  Everything is relative to
`IsIndCarrier S D`.  Producing such a `D` inside `Vset κ` is the transfinite
iteration of §10, and it needs to bound `range f` for `f : Pos q a → Vset β`
with `Pos q a` an arbitrary member of `Vset κ` — i.e. full replacement inside
`V_κ`, which is the cardinal-arithmetic gap recorded in `Inaccessible.lean`
(`∀ β < κ, ∃ a ∈ κ, Vset β ≤# a`).  `repl_mem_vsetV` only supplies replacement
along an *ordinal* index set.  This is the single remaining obstruction on the
model side of inductive types, and it is the same obstruction as before.
-/

end Lean4Lean.SetModel
