import Lean4Lean.Theory.SetModel.InterpSound

/-!
# Zero-field surjective pairing is forced in the set model

**This file exists to fix a layering inversion, not to change a proof.**  Its whole content was
moved verbatim out of `Theory/Typing/StructEtaPrice.lean` §8 on 2026-09-04.  That file imports
`Lean4Lean.Verify.TypeChecker.EtaUnitRefute` — it has to, because pricing the fourteenth
`IsDefEq` constructor means measuring against `EtaUnitRefute`'s counterexample environment — and
`Theory/SetModel/RecTypePeel.lean` was importing it *solely* for
`Lean4Lean.SetModel.eq_singleton_of_recProp`.  That made the deepest layer of the refinement
chain (`Verify/` → `Theory/` → `Theory/SetModel/` → Foundation) reach back up into `Verify/`:
46 `Verify.*` modules in `RecTypePeel.lean`'s import closure, every one of them arriving through
that single edge, and none of them used by any declaration in the file.

The move is sound because the dependency set was *measured* rather than assumed
(`docs/handoff-layering.md` §M2): the cone of `eq_singleton_of_recProp` is 5826 constants over
219 defining modules, of which exactly **five** are `Lean4Lean` modules —
`Theory.SetModel.Universe` (`UProp`, `pt`, `mem_UProp_iff`), `Theory.SetModel.Interp` (`mkLam`,
`mem_mkLam_iff`), `Theory.SetModel.InterpSound` (`mkLam_value`, `mkLam_mem_function`),
`Theory.SetModel.Rank` (`value_eq_of_kpair_mem`), and `StructEtaPrice.lean` itself for the six
helpers below.  **Zero `Verify.*` constants.**  A single
`import Lean4Lean.Theory.SetModel.InterpSound` carries all four dependency modules and its own
closure is 21 modules with no `Verify/` in it, so this is the lowest point the block can sit at.

Left behind in `StructEtaPrice.lean` §8: `SetModel.mkForallType_const_eq_pow`, which is not in
this theorem's cone (it is the general form of `UnitAudit.mkForallType_singleton_const` and has
no users at all), and the surrounding prose, which is about the *price* of structure eta rather
than about the model.

`Theory/SetModel/RecTypePeel.lean` §8 composes the theorem below with its own recursor-type peel
to get surjective pairing for a general zero-field structure; that is the only consumer.
-/

namespace Lean4Lean

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The body of the characteristic family: `{•}` at `mkv`, `∅` elsewhere.  Written with `sep`
rather than an `if` because `definability` does not see through `ite`. -/
noncomputable def charBody (mkv : V) : V → V → V := fun _ v ↦ {_z ∈ ({pt} : V) ; v = mkv}

theorem charBody_definable (mkv : V) : ℒₛₑₜ-function₂[V] (charBody mkv) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T _ v ↦ T = charBody mkv ∅ v) by exact this
  have e : ∀ T ρ v : V, T = charBody mkv ρ v ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ v = mkv) := by
    intro T ρ v; rw [mem_ext_iff]; simp [charBody, mem_sep_iff]
  simp only [e]; definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem constDom_definable (Sv : V) : ℒₛₑₜ-function₁[V] (fun _ : V ↦ Sv) := by definability

/-- **The characteristic family of `{mkv}` over `Sv`, as an element of `UProp ^ Sv`.**  This is
the motive the recursor's type obligation cannot survive unless `Sv = {mkv}`.  It is a legal
motive because `interp`'s `forallE` clause is the *full* function space. -/
noncomputable def charFam (Sv mkv : V) : V :=
  mkLam (fun _ ↦ Sv) (constDom_definable Sv) (charBody mkv) (charBody_definable mkv) ∅

theorem charFam_value {Sv mkv v : V} (hv : v ∈ Sv) :
    (charFam Sv mkv) ‘ v = {_z ∈ ({pt} : V) ; v = mkv} :=
  mkLam_value (G := fun _ ↦ Sv) hv

theorem charFam_mem_pow {Sv mkv : V} : charFam Sv mkv ∈ ((UProp : V) ^ Sv : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hv, mem_UProp_iff.mpr sep_subset⟩
  · exact ⟨charBody mkv ∅ v, mem_mkLam_iff.mpr ⟨v, hv, rfl⟩, fun y hy ↦ by
      obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
      obtain ⟨rfl, rfl⟩ := kpair_inj he; rfl⟩

/-- **Zero-field surjective pairing is *forced* in the set model.**

`H` is what `OracleOK.type` says at the recursor of a zero-field, index-free, one-constructor
block, with `interp`'s binders peeled: for every motive `m` in the motive space, every inhabitant
of `m mk`, and every `x` in the type former's denotation, the recursor's value lands in `m x`.
(At `elimLvl = .zero` the whole `recType` is propositional and the value is `•` itself, which is
the shape written here; at a large eliminator the value is a function and `pt` is replaced by
"some element of", with the same proof.)

The conclusion is that the denotation is the *singleton* `{mk}` — so any two inhabitants are
equal in the model, which is exactly what `isDefEqUnitLike` reports and what
`VEnv.UnitEta.unitLike` states in the spec.

**No `Above`, no `κ`, no chain of inaccessibles**: the argument is finite and uses only
Replacement and Power. -/
theorem eq_singleton_of_recProp {Sv mkv : V} (hmk : mkv ∈ Sv)
    (H : ∀ m ∈ ((UProp : V) ^ Sv : V), pt ∈ m ‘ mkv → ∀ x ∈ Sv, pt ∈ m ‘ x) :
    Sv = ({mkv} : V) := by
  rw [mem_ext_iff]
  intro x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (mem_singleton_iff.mp hx) ▸ hmk⟩
  have h1 : pt ∈ (charFam Sv mkv) ‘ mkv := by
    rw [charFam_value hmk]; exact mem_sep_iff.mpr ⟨by simp, rfl⟩
  have h2 := H _ charFam_mem_pow h1 x hx
  rw [charFam_value hx] at h2
  exact mem_singleton_iff.mpr (mem_sep_iff.mp h2).2

/-- **The bound the other way: the hypothesis is not vacuous and not trivially true.**  Drop the
`pt ∈ m ‘ mkv` premise and `H` becomes false at every `Sv` with an element (take `m` to be the
characteristic family of a *different* point); keep it and `H` is satisfied at `Sv = {mkv}`
itself.  So `eq_singleton_of_recProp` is a real implication at a satisfiable hypothesis. -/
theorem recProp_at_singleton {mkv : V} :
    ∀ m ∈ ((UProp : V) ^ ({mkv} : V) : V), pt ∈ m ‘ mkv → ∀ x ∈ ({mkv} : V), pt ∈ m ‘ x :=
  fun _ _ h _x hx => (mem_singleton_iff.mp hx) ▸ h

end SetModel

end Lean4Lean

/-! ## Axiom bar

Nothing here introduces an axiom.  These lines moved with the block out of
`Theory/Typing/StructEtaPrice.lean` §9, unchanged: the point of the move is that the axiom set
does not change. -/

#print axioms Lean4Lean.SetModel.charFam_mem_pow
#print axioms Lean4Lean.SetModel.eq_singleton_of_recProp
#print axioms Lean4Lean.SetModel.recProp_at_singleton
