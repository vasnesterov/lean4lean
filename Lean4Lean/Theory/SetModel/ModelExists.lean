import Lean4Lean.Theory.SetModel.ModelFitsVacuous
import Foundation.FirstOrder.Completeness.CounterModel

/-!
# Input A, discharged: `ModelExistsInput` is a theorem

`InaccChainOmega.lean` reduced `CnstRecursion.InaccModelInput` (Input A of the §7
reduction) to

    ModelExistsInput : Prop :=
      ∀ P : Prop, (∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰], P) →
        Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → P

— "pure model existence from consistency, chain-free" — and recorded it as *provable from
Foundation but not applied anywhere*.  `docs/vacuity-ledger.md` row 11c′ carries the same
claim.  **The claim is correct, and this file applies it**: `modelExistsInput` is a proof,
so Input A is no longer an input.

## The glue, in three steps

1. `LO.FirstOrder.Theory.small_satisfiable_of_consistent : Consistent T → Satisfiable T`.
   For `T : SetTheory = Theory ℒₛₑₜ` and `ℒₛₑₜ : Language.{0}` this is `Satisfiable.{0}`,
   so `satisfiable_iff` hands back a model in `Type 0` — exactly the `V : Type` that
   `ModelExistsInput` quantifies over.  No `ULift` is needed and none is available: the
   downstream statement is `Type`-specific.
2. That model is a bare `Structure ℒₛₑₜ M`, in which `=` is an arbitrary congruence rather
   than equality.  `QuotNormalize M` quotients by it; it carries a `SetStructure` instance
   (hence Foundation's `standardStructure`), is `Nonempty`, is universe-preserving
   (`QuotNormalize M : Type u` for `M : Type u`), and is elementarily equivalent to `M`
   (`QuotNormalize.elementary_equiv`), so it models `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` too.
3. Forming `QuotNormalize M` needs `M↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ`, which is *not* automatic for a
   bare structure — it comes from the theory, via `𝗘𝗤 ℒₛₑₜ ⊆ 𝗭𝗙 ⊆ 𝗭𝗙𝗖 ⊆ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`
   (`eq_subset_zfcInacc`).

## What this closes

Composing with `InaccChainOmega.inaccModelInput_of_modelExists` and
`ModelFitsVacuous.upper_bound_of_omega`:

    upper_bound_of_modelFits (hB : ModelFitsLeanInput) :
      Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent

**The whole model-side reduction now rests on one input**, `ModelFitsLeanInput`, whose two
known unknowns (`PropSplit env 0` with `Stable`, and the `.induct` residual
`InductOracleOK`) are recorded in `ModelFitsVacuous.lean` and `InductOracleAudit.lean`.
Nothing here touches either.

## Bounds, both ways (`docs/vacuity-ledger.md` §5)

The danger this file has to rule out is the Row-24 one: a hypothesis that is satisfied
because the class it quantifies over is *empty*.  `ModelExistsInput`'s premise
`(∀ (V : Type) [SetStructure V] …, P)` is exactly such a binder, so the two-way check is:

* **Not vacuous** — `not_forall_model_false`: under `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` the binder's
  class of models is *inhabited*, so `∀ V …, P` is not satisfiable for free.  (Instantiating
  `P := False` is exactly the Row-24 test; `sortInvSupply_vacuous` failed it.)
* **Not stronger than consistency** — `consistent_of_setModel`: any one model returns
  `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` (soundness).  So `ModelExistsInput`'s content is *equivalent* to
  consistency, not to anything above it — `modelExists_iff_consistent`.
* **The consistency hypothesis is load-bearing** — `consistent_of_unconditional`: deleting
  it yields a statement that *implies* `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, hence (Gödel) is not
  provable.  So the proof below is not an accident of a trivially true statement.

## Note before importing this

§5 installs three **global instances** (`rawModel_models_inst`, `rawModel_models_eq`,
`zfcInaccModel_models`), all indexed by an explicit `hc : Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, so they
only fire at `RawModel hc` / `ZFCInaccModel hc` and cannot be triggered by anything else.
This file also imports `Foundation.FirstOrder.Completeness.CounterModel`, which is new to
the `SetModel/` cone — it is where `small_satisfiable_of_consistent` lives, and it pulls in
Foundation's `LK` derivation machinery.  `InaccChainOmega.lean`'s two global `models_*`
instances come in transitively via `ModelFitsVacuous.lean`.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. `𝗘𝗤` is available inside `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`

Needed to form `QuotNormalize`.  Foundation has `𝗘𝗤 _ ⪯ 𝗭𝗙𝗖` (a provability statement) and
`𝗭𝗙𝗖 ⊆ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, but `models_of_ss` wants a genuine subset, so it is spelled out. -/

theorem eq_subset_zfcInacc : (𝗘𝗤 ℒₛₑₜ : SetTheory) ⊆ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  fun _ h ↦ ZermeloFraenkelChoiceOmegaInaccessibles.zfc _
    (Or.inl (ZermeloFraenkel.axiom_of_equality _ h))

/-- Any structure modelling `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` models the equality axioms. -/
theorem models_eq_of_models_zfcInacc {M : Type*} [Nonempty M] [Structure ℒₛₑₜ M]
    (hM : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ : SetTheory) :=
  models_of_ss hM eq_subset_zfcInacc

/-! ## 2. Input A is a theorem -/

/-- **`ModelExistsInput` holds.**  Foundation's completeness theorem plus `QuotNormalize`;
this is the whole of what `InaccChainOmega.lean` left of `CnstRecursion.InaccModelInput`. -/
theorem modelExistsInput : ModelExistsInput := by
  intro P hP hc
  obtain ⟨M, hne, s, hM⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hc)
  let _ := hne
  let _ := s
  have : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ : SetTheory) := models_eq_of_models_zfcInacc hM
  have : (QuotNormalize M)↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
    (QuotNormalize.elementary_equiv (M := M)).modelsTheory.mpr hM
  exact hP (QuotNormalize M)

/-- **And therefore Input A of `CnstRecursion.lean` §7 outright**: `InaccModelInput` is a
theorem, not a hypothesis.  The chain half is `InaccChainOmega.exists_inaccessibleChain_omega`
and the model half is `modelExistsInput`. -/
theorem inaccModelInput : InaccModelInput :=
  inaccModelInput_of_modelExists modelExistsInput

/-! ## 3. The reduction with Input A gone -/

/-- **The model side, on one input.**  `ModelFitsVacuous.upper_bound_of_omega` with its
first hypothesis discharged. -/
theorem upper_bound_of_modelFits (hB : ModelFitsLeanInput) :
    Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) → leanTTConsistent :=
  upper_bound_of_omega modelExistsInput hB

/-- The same for the pre-narrowing packaging, for completeness.  Note `ModelFitsInput` is
*false* (`ModelFitsVacuous.not_modelFitsInput`), so this statement is vacuous and only
`upper_bound_of_modelFits` above is usable; it is recorded so that no reader mistakes the
discharge of Input A for a repair of Input B. -/
theorem upper_bound_of_modelFits_unnarrowed (hB : ModelFitsInput) :
    Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) → leanTTConsistent :=
  upper_bound_of inaccModelInput hB

/-! ## 4. Bounds -/

section Bounds

/-- **Soundness half.**  One `SetStructure` model of `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` gives consistency back, so
`ModelExistsInput` is not secretly stronger than `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`. -/
theorem consistent_of_setModel (V : Type) [SetStructure V] [Nonempty V]
    (hV : V↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) :
    Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  LO.Sound.consistent_of_satisfiable (M := Struc.{0, 0} ℒₛₑₜ)
    (satisfiable_intro (T := (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) V hV)

/-- **Not vacuous** (the Row-24 test).  Under consistency the class `ModelExistsInput`
quantifies over is inhabited: there is *no* uniform proof of `False` from
`[SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]`.  Had the class been empty,
`modelExistsInput` would have been true for the wrong reason and useless. -/
theorem not_forall_model_false (hc : Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) :
    ¬ ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)],
        False :=
  fun h ↦ modelExistsInput False h hc

/-- **The consistency hypothesis is load-bearing.**  Drop it from `ModelExistsInput` and the
result implies `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, so it is not provable.  This is what separates
`modelExistsInput` from a triviality. -/
theorem consistent_of_unconditional
    (h : ∀ P : Prop,
      (∀ (V : Type) [SetStructure V] [Nonempty V]
        [V↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)], P) → P) :
    Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  h _ (fun V _ _ hV ↦ consistent_of_setModel V hV)

/-- **Exactly consistency, both ways.**  The *consistency-free* form of the input — the
eliminator with `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` deleted from the antecedent — is equivalent to
`Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`.  Read `←`, this is `modelExistsInput`; read `→`, it is soundness.
So Input A asked for precisely consistency: nothing weaker would have sufficed (`→`) and
nothing stronger was needed (`←`).

Stating the bound at the consistency-free form is the point.  `ModelExistsInput ↔ _` would
be uninformative now that the left side is a theorem; this version is not, since neither
side is provable. -/
theorem modelExists_iff_consistent :
    (∀ P : Prop, (∀ (V : Type) [SetStructure V] [Nonempty V]
        [V↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)], P) → P)
      ↔ Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  ⟨consistent_of_unconditional, fun hc P hP ↦ modelExistsInput P hP hc⟩

end Bounds

/-! ## 5. A named model

Consumers that want to *fix* a model rather than eliminate into an arbitrary `P` can use
this.  It is noncomputable (Foundation's `ModelOfSat` is `Classical.choose`) and lives in
`Type 0`, which is what `ModelFits` and `CnstRecursion` need. -/

section Named

variable (hc : Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory))

/-- A bare `Structure ℒₛₑₜ`-model of `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` in `Type 0`. -/
noncomputable abbrev RawModel : Type :=
  ModelOfSat (T := (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) (Theory.small_satisfiable_of_consistent hc)

theorem rawModel_models : (RawModel hc)↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  ModelOfSat.models _

noncomputable instance : Nonempty (RawModel hc) := inferInstance

instance rawModel_models_inst : (RawModel hc)↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  rawModel_models hc

instance rawModel_models_eq : (RawModel hc)↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ : SetTheory) :=
  models_eq_of_models_zfcInacc (rawModel_models hc)

/-- **The model**: a `SetStructure` in `Type 0` satisfying `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, in which `=` really
is equality. -/
noncomputable abbrev ZFCInaccModel : Type := QuotNormalize (RawModel hc)

instance zfcInaccModel_models : (ZFCInaccModel hc)↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) :=
  (QuotNormalize.elementary_equiv (M := RawModel hc)).modelsTheory.mpr (rawModel_models hc)

/-- The named model carries the `∀ m`-chain of `InaccChainOmega.lean`, so it is a complete
`InaccModelInput` witness on its own. -/
theorem zfcInaccModel_chain :
    ∃ κ : ℕ → ZFCInaccModel hc, ∀ m : ℕ, IsInaccessibleChain m κ :=
  exists_inaccessibleChain_omega

end Named

end Lean4Lean.SetModel
