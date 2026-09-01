import Lean4Lean.Theory.SetModel.AxiomsValidatedAudit

/-!
# The `hκ` gap, closed: one `κ` good for **every** finite length

`SetModel/Inaccessible.lean`'s `exists_inaccessibleChain` gives, for each meta-level `n`,
*some* `κ : ℕ → V` with `IsInaccessibleChain n κ` — **one `κ` per `n`**.  Every consumer of
the model wants the reordered form

    hκ : ∀ m : ℕ, IsInaccessibleChain m κ

for a **single** `κ`.  `CnstRecursion.InaccModelInput`'s docstring flags the reordering as
"a real gap, not bookkeeping", `AxiomsValidatedAudit.lean`'s header records that
`AxiomsValidated.axioms` — alone among the obligations in `InterpSound.lean` — is stated
without the `Above M` truncation and so depends on exactly this input, and
`docs/soundness-ledger.md` carries it as open.

**This file closes it.**  `exists_inaccessibleChain_omega` produces one `κ` with
`∀ m, IsInaccessibleChain m κ` from `[V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]` and nothing else.

## Why it is not merely bookkeeping, and why it is nevertheless true

The naive attempt — diagonalise the family `n ↦ κ_n` — fails: the chains `exists_inaccessibleChain`
returns for different `n` are unrelated, and there is no choice principle over `V` that glues
them.  The schema also does **not** say the inaccessibles are unbounded in `V`; a model may
have all of them below a single ordinal, so "pick an inaccessible above `κ i`" is not
directly available either.

What *is* available is that `IsInaccessible` is **internally definable**
(`Inaccessible.lean`'s `IsInaccessible.defined` against `SetTheory.IsInaccessible.dfn`), so
Foundation's `exists_minimal` applies to it: a nonempty definable class of ordinals of `V`
has a **least** element.  So define `κ i` externally as the `(i+1)`-st *least* inaccessible
(`inaccSeq`).  Each step needs one inaccessible above the previous value, and that comes
from a **pigeonhole against the schema**: `inaccSeq V 0, …, inaccSeq V i` are, by leastness,
*all* the inaccessibles `≤ inaccSeq V i` (`inaccSeq_spec`), so `i+1` of them; if none lay
above `inaccSeq V i` they would be all the inaccessibles of `V`, and the `(i+2)`-chain the
schema supplies would inject `i+2` distinct inaccessibles into them
(`exists_inacc_above_inaccSeq`).

So the answer to "is `hκ` exactly what `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` buys?" is **yes**: the
single-`κ` form is equivalent to the schema over any one model, and
`inaccModelInput_of_modelExists` reduces `InaccModelInput` to pure model existence with no
chain condition at all — Foundation's `small_satisfiable_of_consistent` half, which is the
only thing left in that input.

## Contents

* `OInacc`, `nextInacc`, `inaccSeq` — the least-inaccessible enumeration.
* `inaccSeq_spec` — `inaccSeq V i` is inaccessible **and** exhausts the inaccessibles below
  it.  The second conjunct is what makes the induction go through; it is the invariant a
  bare "there is an inaccessible above" statement cannot carry.
* `exists_inaccessibleChain_omega` — the result.
* `ModelExistsInput` / `inaccModelInput_of_modelExists` — the residual input, chain-free.
* Bounds, per `docs/vacuity-ledger.md` §5: `inaccSeq_zero_le` (the enumeration is not junk —
  `inaccSeq V 0` really is the least inaccessible) and `not_isInaccessibleChain_const`
  (the conclusion is not trivially true: a constant `κ` has no chain of length 2).
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 1. The least-inaccessible enumeration -/

section Least

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-- Inaccessibility as a predicate on `Ordinal V`, so that Foundation's `LinearOrder
(Ordinal V)` is available.  Every argument below is order-theoretic on `Ordinal V`; nothing
uses external well-foundedness of `∈`, which an arbitrary model of `𝗭` need not have. -/
def OInacc (α : Ordinal V) : Prop := IsInaccessible α.val

/-- **The least inaccessible strictly above `a`, when there is one.**  This is where internal
definability of `IsInaccessible` is spent: `exists_minimal` needs the class to be
`ℒₛₑₜ`-definable, and `IsInaccessible.definable` supplies it (with `a` as a parameter). -/
theorem exists_least_inacc_above (a : Ordinal V) (h : ∃ β : Ordinal V, OInacc β ∧ a < β) :
    ∃ β : Ordinal V, (OInacc β ∧ a < β) ∧ ∀ ξ : Ordinal V, OInacc ξ → a < ξ → β ≤ ξ := by
  obtain ⟨β, hβ, hmin⟩ :=
    exists_minimal (V := V) (fun x ↦ IsInaccessible x ∧ a.val ∈ x) (by definability)
      (h.imp fun _ hb ↦ ⟨hb.1, Ordinal.lt_def.1 hb.2⟩)
  exact ⟨β, ⟨hβ.1, Ordinal.lt_def.2 hβ.2⟩, fun ξ hξ hlt ↦ hmin ξ ⟨hξ, Ordinal.lt_def.1 hlt⟩⟩

open Classical in
/-- The least inaccessible strictly above `a`, or `⊥` when there is none.  The `⊥` branch is
never taken at any value the construction visits (`inaccSeq_spec`). -/
noncomputable def nextInacc (a : Ordinal V) : Ordinal V :=
  if h : ∃ β : Ordinal V, OInacc β ∧ a < β then (exists_least_inacc_above a h).choose else ⊥

theorem nextInacc_spec {a : Ordinal V} (h : ∃ β : Ordinal V, OInacc β ∧ a < β) :
    OInacc (nextInacc a) ∧ a < nextInacc a ∧
      ∀ ξ : Ordinal V, OInacc ξ → a < ξ → nextInacc a ≤ ξ := by
  rw [nextInacc, dif_pos h]
  obtain ⟨⟨h1, h2⟩, h3⟩ := (exists_least_inacc_above a h).choose_spec
  exact ⟨h1, h2, h3⟩

/-- **The candidate chain**: `inaccSeq V i` is the `(i+1)`-st least inaccessible of `V`.
Defined by *external* recursion on `i`; no internal recursion, no choice over `V`. -/
noncomputable def inaccSeq (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] :
    ℕ → Ordinal V
  | 0 => nextInacc ⊥
  | i + 1 => nextInacc (inaccSeq V i)

end Least

/-! ## 2. The pigeonhole against the schema -/

section Chain

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]

/-- Every inaccessible is `> ⊥`: it contains `ω`, hence is nonempty, hence contains `∅`. -/
theorem exists_inacc_above_bot : ∃ β : Ordinal V, OInacc β ∧ ⊥ < β := by
  obtain ⟨k, hk⟩ := exists_inaccessible (V := V)
  exact ⟨⟨k, hk.isOrdinal⟩, hk, Ordinal.pos_iff_nonempty.2 ⟨_, hk.omega_mem⟩⟩

/-- **The pigeonhole step.**  If the inaccessibles `≤ inaccSeq V i` are exactly the `i+1`
values `inaccSeq V 0, …, inaccSeq V i`, then there *is* an inaccessible strictly above
`inaccSeq V i` — for otherwise those `i+1` values would be all the inaccessibles of `V`, and
the `(i+2)`-chain the axiom schema supplies (`exists_inaccessibleChain`) injects `i+2`
distinct inaccessibles into them.

This is the step that the schema — as opposed to an unboundedness axiom — is exactly strong
enough for, and it is why no *bounded* fragment of `𝗜𝗻𝗮𝗰𝗰` would do: the argument at index
`i` consumes the `(i+2)`-nd sentence of the schema. -/
theorem exists_inacc_above_inaccSeq (i : ℕ)
    (H : ∀ ξ : Ordinal V, OInacc ξ → ξ ≤ inaccSeq V i → ∃ j ≤ i, ξ = inaccSeq V j) :
    ∃ β : Ordinal V, OInacc β ∧ inaccSeq V i < β := by
  classical
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨κ, hκ⟩ := exists_inaccessibleChain (V := V) (i + 2)
  set g : Fin (i + 2) → Ordinal V := fun j ↦
    ⟨κ j, (hκ.inaccessible j j.isLt).isOrdinal⟩ with hg
  have hgi : ∀ j : Fin (i + 2), OInacc (g j) := fun j ↦ hκ.inaccessible j j.isLt
  have hglt : ∀ j₁ j₂ : Fin (i + 2), j₁ < j₂ → g j₁ < g j₂ := fun j₁ j₂ h ↦
    Ordinal.lt_def.2 (hκ.mem j₁ j₂ h j₂.isLt)
  have hginj : Function.Injective g := by
    intro j₁ j₂ he
    rcases lt_trichotomy j₁ j₂ with h | h | h
    · exact absurd he (ne_of_lt (hglt _ _ h))
    · exact h
    · exact absurd he.symm (ne_of_lt (hglt _ _ h))
  have hmem : ∀ j : Fin (i + 2),
      g j ∈ (Finset.range (i + 1)).image (fun k ↦ inaccSeq V k) := by
    intro j
    obtain ⟨k, hk, hek⟩ := H (g j) (hgi j) (not_lt.1 (hcon (g j) (hgi j)))
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), hek.symm⟩
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (i + 2)))) g
    (fun j _ ↦ hmem j) hginj.injOn
  have h1 : (Finset.univ : Finset (Fin (i + 2))).card = i + 2 := by simp
  have h2 : ((Finset.range (i + 1)).image (fun k ↦ inaccSeq V k)).card ≤ i + 1 :=
    le_trans Finset.card_image_le (by simp)
  omega

/-! ## 3. The invariant, and the chain -/

/-- **The invariant.**  `inaccSeq V i` is inaccessible, *and* the inaccessibles `≤ inaccSeq V i`
are exactly `inaccSeq V 0, …, inaccSeq V i`.

Both conjuncts are needed at once: the second is what feeds `exists_inacc_above_inaccSeq` at
the next index, and the first is what the second's proof needs from `nextInacc_spec`.  A
statement of the first conjunct alone is not provable by this induction, which is the precise
sense in which the reordering is not bookkeeping. -/
theorem inaccSeq_spec : ∀ i : ℕ, OInacc (inaccSeq V i) ∧
    ∀ ξ : Ordinal V, OInacc ξ → ξ ≤ inaccSeq V i → ∃ j ≤ i, ξ = inaccSeq V j
  | 0 => by
    obtain ⟨h1, _, h3⟩ := nextInacc_spec (exists_inacc_above_bot (V := V))
    refine ⟨h1, fun ξ hξ hle ↦ ⟨0, le_refl _, le_antisymm hle ?_⟩⟩
    exact h3 ξ hξ (Ordinal.pos_iff_nonempty.2 ⟨_, hξ.omega_mem⟩)
  | i + 1 => by
    obtain ⟨_, hex⟩ := inaccSeq_spec i
    obtain ⟨h1, h2, h3⟩ := nextInacc_spec (exists_inacc_above_inaccSeq i hex)
    refine ⟨h1, fun ξ hξ hle ↦ ?_⟩
    rcases le_or_gt ξ (inaccSeq V i) with hle' | hgt
    · obtain ⟨j, hj, hej⟩ := hex ξ hξ hle'
      exact ⟨j, by omega, hej⟩
    · exact ⟨i + 1, le_refl _, le_antisymm hle (h3 ξ hξ hgt)⟩

theorem oInacc_inaccSeq (i : ℕ) : OInacc (inaccSeq V i) := (inaccSeq_spec (V := V) i).1

theorem inaccSeq_lt_succ (i : ℕ) : inaccSeq V i < inaccSeq V (i + 1) :=
  (nextInacc_spec (exists_inacc_above_inaccSeq i (inaccSeq_spec (V := V) i).2)).2.1

theorem inaccSeq_strictMono : StrictMono (inaccSeq V) :=
  strictMono_nat_of_lt_succ inaccSeq_lt_succ

/-- **The result: one `κ` carrying an inaccessible chain of every finite length.**  This is
the `hκ` that `CnstRecursion.leanTTConsistent_of`, `CnstRecursion.consistent_of` and
`AxiomsValidatedAudit.axiomsValidated_of_coherentOn` take as a hypothesis. -/
theorem exists_inaccessibleChain_omega :
    ∃ κ : ℕ → V, ∀ m : ℕ, IsInaccessibleChain m κ :=
  ⟨fun i ↦ (inaccSeq V i).val, fun _ ↦
    { inaccessible := fun i _ ↦ oInacc_inaccSeq i
      mem := fun _ _ hij _ ↦ Ordinal.lt_def.1 (inaccSeq_strictMono hij) }⟩

end Chain

/-! ## 4. What is left of `InaccModelInput`

`CnstRecursion.InaccModelInput` bundles two things: model existence from consistency, and a
`κ` with `∀ m, IsInaccessibleChain m κ`.  §3 supplies the second outright, so the input
reduces to the first — with **no** chain condition. -/

section Reduce

/-- **Model existence alone**, with nothing about inaccessible chains.  Foundation's
`small_satisfiable_of_consistent` together with
`QuotNormalize`/`standardStructure` is meant to supply this; neither is applied here, and
this is now the *only* content of `CnstRecursion.InaccModelInput`. -/
def ModelExistsInput : Prop :=
  ∀ P : Prop, (∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰], P) →
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → P

instance models_zf_of_models_zfcInacc {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  models_of_ss (U := 𝗭𝗙𝗖) inferInstance Set.subset_union_left

instance models_ac_of_models_zfcInacc {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
  models_of_ss (U := 𝗭𝗙𝗖) inferInstance Set.subset_union_right

/-- **`InaccModelInput` needs no chain input.**  The `hκ` half is discharged by
`exists_inaccessibleChain_omega`; what remains is `ModelExistsInput`. -/
theorem inaccModelInput_of_modelExists (h : ModelExistsInput) : InaccModelInput := by
  intro P hP hc
  refine h P (fun V _ _ _ ↦ ?_) hc
  obtain ⟨κ, hκ⟩ := exists_inaccessibleChain_omega (V := V)
  exact hP V κ hκ

/-- **`hκ` is no longer a hypothesis of the top-level reduction.**  `CnstRecursion`'s
`leanTTConsistent_of` takes both `κ` and `hκ : ∀ m, IsInaccessibleChain m κ`; in a model of
`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` both are *produced*, so the only remaining hypothesis is `ModelFits` — which is
where the residual and the proof-split input live. -/
theorem leanTTConsistent_of_modelFits {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]
    (H : ∀ κ : ℕ → V, (∀ m : ℕ, IsInaccessibleChain m κ) → ∀ (env : VEnv) (ds : List VDecl),
      VEnv.WF' ds env → (∀ d ∈ ds, d.noUnsafe) → ModelFits κ env ds) :
    leanTTConsistent := by
  obtain ⟨κ, hκ⟩ := exists_inaccessibleChain_omega (V := V)
  exact leanTTConsistent_of κ hκ (H κ hκ)

/-- **And the same for `AxiomsValidated`.**  `AxiomsValidatedAudit.axiomsValidated_of_coherentOn`
is the one obligation stated without `Above M`, and `hκ` was the only thing bridging it to
`CoherentOn.const_type`; at a model data whose chain is the one §3 builds, that bridge is
free. -/
theorem axiomsValidated_of_coherentOn_omega {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv}
    {ls : List ℕ} {c : Name → List VLevel → V} {env : VEnv} {ds : List VDecl}
    (hC : ∀ κ : ℕ → V, (∀ m : ℕ, IsInaccessibleChain m κ) → CoherentOn ⟨κ, ls, c⟩ L env)
    (hwf : VEnv.WF' ds env) :
    ∃ κ : ℕ → V, (∀ m : ℕ, IsInaccessibleChain m κ) ∧ AxiomsValidated ⟨κ, ls, c⟩ L ds := by
  obtain ⟨κ, hκ⟩ := exists_inaccessibleChain_omega (V := V)
  exact ⟨κ, hκ, axiomsValidated_of_coherentOn hκ (hC κ hκ) hwf⟩

end Reduce

/-! ## 5. Bounds

Per `docs/vacuity-ledger.md` §5 check 2: the conclusion must be neither junk nor trivial. -/

section Bounds

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]

/-- **Not junk.**  `inaccSeq V 0` really is the least inaccessible of `V`, so the `⊥` branch
of `nextInacc` is not what is being measured. -/
theorem inaccSeq_zero_le (ξ : Ordinal V) (hξ : OInacc ξ) : inaccSeq V 0 ≤ ξ :=
  (nextInacc_spec (exists_inacc_above_bot (V := V))).2.2 ξ hξ
    (Ordinal.pos_iff_nonempty.2 ⟨_, hξ.omega_mem⟩)

/-- **Not trivially true.**  `IsInaccessibleChain m κ` is real information for `m ≥ 2`: a
constant `κ` has none, because `mem` would force `κ 0 ∈ κ 0`. -/
theorem not_isInaccessibleChain_const (k : V) (hk : IsInaccessible k) :
    ¬ IsInaccessibleChain 2 (fun _ ↦ k) := by
  intro h
  have hm : k ∈ k := h.mem 0 1 (by omega) (by omega)
  have ho : (⟨k, hk.isOrdinal⟩ : Ordinal V) < ⟨k, hk.isOrdinal⟩ := Ordinal.lt_def.2 hm
  exact absurd ho (lt_irrefl _)

end Bounds

end Lean4Lean.SetModel
