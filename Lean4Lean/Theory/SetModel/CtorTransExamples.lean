import Lean4Lean.Theory.SetModel.CtorTrans
import Lean4Lean.Theory.Inductive.DeclExamples

/-!
# The translation, at the declarations that have `WF` witnesses

`Theory/Inductive/DeclExamples.lean` carries four `VInductDecl'.WF` witnesses,
three of them with recursive fields.  This file exercises
`SetModel/CtorTrans.lean` against them, for the reason
`docs/soundness-ledger.md` gives for the witnesses themselves: a side condition
that is only *stated* is worth much less than one an instance satisfies.

Two things are checked, and they are different:

* **the hypothesis is inhabited** — `ctorDataOf` takes a `VIndCtor.WF`, and
  `accIntro_WF` supplies one, so the translation is applied rather than merely
  applicable;
* **the position bookkeeping is right** — `slotDoms` names the *absolute*
  position of each recursive field in a valuation, which is `np + i`, and the
  examples below pin it at declarations whose `np` and field layout differ.
  This is the arithmetic the whole file turns on and it is a closed
  computation, so it is checked by `rfl` rather than argued.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.InductiveDeclExamples

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit envF nv)

/-! ## `Acc` -/

/-- The staged environment the constructors of `accDecl` are checked in. -/
theorem accIndTypes_isSome : (VEnv.empty.addIndTypes accDecl).isSome := by decide

/-- **The constructor well-formedness the translation consumes is inhabited.** -/
theorem accIntro_WF_inst : ∃ env₁, VEnv.empty.addIndTypes accDecl = some env₁ ∧
    accIntro.WF env₁ accDecl 0 accType := by
  obtain ⟨env₁, he⟩ := Option.isSome_iff_exists.1 accIndTypes_isSome
  exact ⟨env₁, he, accDecl_WF.ctors env₁ he 0 accType rfl accIntro (by simp [accType])⟩

/-- The translation, applied. -/
noncomputable def accCtorData (Dcar params : V) : CtorData₃ V :=
  ctorDataOf M L accDecl accIntro_WF_inst.choose_spec.2 Dcar params

/-- `Acc.intro` has one recursive field, so `Pos` has one summand. -/
example (Dcar params : V) : (accCtorData M L Dcar params).poss.length = 1 := rfl

/-- …at absolute position `np + i = 2 + 1`, the last of the four slots of a
valuation `⟨α, r, x, h⟩`. -/
example : ((slotDoms M L accDecl accIntro).map (·.1) : List ℕ) = [3] := rfl

/-- The result index is tagged with the block member it builds — here the only
one. -/
example : accIntro.recFields.length = 1 := rfl

/-! ## `W'`, the configuration with two recursive fields

`wDecl` is `inductive W' (β : Prop) : Prop | mk : W' β → (β → W' β) → W' β`: one
parameter, both fields recursive.  Its slots are therefore `1` and `2`, and the
second field's `ξ` is non-empty — the configuration `binders_indep` was written
for, and the one where a *blanking* layout would have had to consult it. -/

example : ((slotDoms M L wDecl wMk).map (·.1) : List ℕ) = [1, 2] := rfl

example : wMk.recFields.length = 2 := rfl

/-! ## `Tree'`/`Forest'`, the mutual case

`Forest'.cons` has two recursive fields recursing into *different* members of
the block, and no parameters, so the slots are `0` and `1`. -/

example : ((slotDoms M L mutDecl forestCons).map (·.1) : List ℕ) = [0, 1] := rfl

/-- The two summands carry different member tags, which is what makes `Idx` a
tagged union rather than a plain set. -/
example : (forestCons.recFields.map (·.2.idx) : List ℕ) = [0, 1] := rfl

end Lean4Lean.SetModel
