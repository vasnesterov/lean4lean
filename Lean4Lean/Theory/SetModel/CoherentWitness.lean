import Lean4Lean.Theory.SetModel.Cnst

/-!
# `CoherentOn` is satisfiable — a witness with every field firing

`CoherentOn` matched the audit's danger signature exactly: six producers, all
six taking a `CoherentOn` as input, so no declaration ever forced its fields to
be jointly satisfied.  That is the signature under which `LevelAssign` turned out
to be contradictory (`SetModel/LevelAssignUnsat.lean`), and the suspicion here
was sharpened by `const_congr`, `const_type`, `defeq` and `defeq_type` all
carrying a `∀ l ∈ ls, l.WF nv` guard that was added late — late-added guards
being where the previous defect hid.

**The answer is that `CoherentOn` is fine.**  Below is a witness, and it is
chosen so that *none* of the four fields is vacuous:

* the environment declares one constant, so `const_type` fires;
* it carries one defining equation, so `defeq` and `defeq_type` fire;
* `const_congr` fires at every pair of level lists.

A witness over `VEnv.empty` alone would have proved much less: there
`const_type`, `defeq` and `defeq_type` are all vacuously true, and only
`const_congr` would have been tested.  That weaker witness is what "build one at
`.empty`" would have produced, and it would have left three of the four fields
exactly as untested as before.

## What the witness does and does not show

It is *conditional on a `LevelAssign`*: `CoherentOn M L env` mentions `L` through
`interp M L`, so no unconditional witness is possible while `LevelAssign` is
blocked on `sort_inv`.  But the witness holds for an **arbitrary** `L`, which is
the point — `CoherentOn` adds no obstruction of its own. It becomes inhabited
the moment `LevelAssign` does.

The constant is declared at type `Prop` and interpreted as `∅`, the "false"
truth value; `∅ ∈ ℘{•} = U κ 0` is what makes `const_type` come out.  Nothing
here depends on the chain of inaccessibles, so both `Above` wrappers are
discharged by `Above.pure`.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- One constant, declared at `Prop`. -/
def witConst : VConstant := ⟨0, .sort .zero⟩

/-- Its reflexive defining equation, so `defeq` and `defeq_type` are not
vacuous. -/
def witDefEq (c : Name) : VDefEq := ⟨0, .const c [], .const c [], .sort .zero⟩

/-- The environment: one constant and one defeq. -/
def witEnv (c : Name) : VEnv :=
  ({ VEnv.empty with
      constants := fun n => if c = n then some witConst else none } : VEnv).addDefEq (witDefEq c)

theorem witEnv_constants {c d : Name} :
    (witEnv c).constants d = if c = d then some witConst else none := rfl

theorem witEnv_defeqs {c : Name} {df : VDefEq} :
    (witEnv c).defeqs df ↔ df = witDefEq c := by
  simp [witEnv, VEnv.addDefEq, VEnv.empty]

/-- **`CoherentOn` is satisfiable, with all four fields non-vacuous.**  Holds for
an arbitrary `LevelAssign`, so `CoherentOn` adds no obstruction beyond the one
`LevelAssign` already carries. -/
theorem coherentOn_witness {envF : VEnv} {nv : ℕ} (L : LevelAssign envF nv)
    (κ : ℕ → V) (ls : List ℕ) (c : Name) :
    CoherentOn (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L (witEnv c) := by
  have hsort : ∀ (us : List VLevel) (ρ : V),
      (interp (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L [] ((VExpr.sort .zero).instL us)).toFun ρ
        = (UProp : V) := by
    intro us ρ
    show (interp (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L [] (.sort .zero)).toFun ρ = _
    rw [interp_sort]
    rfl
  refine ⟨fun _ _ _ ↦ Above.pure rfl, fun {d ci us} hd _ _ ↦ ?_,
    fun {df us} hd _ _ ↦ ?_, fun {df us} hd _ _ ↦ ?_⟩
  · -- `const_type`: the declared constant is interpreted as `∅ ∈ ℘{•}`
    rw [witEnv_constants] at hd
    split at hd
    · cases hd
      refine Above.pure ?_
      show (∅ : V) ∈ (interp (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L []
        ((VExpr.sort .zero).instL us)).toFun ∅
      rw [hsort]
      exact empty_mem_UProp
    · exact absurd hd nofun
  · -- `defeq`: both sides are the same constant
    rw [witEnv_defeqs] at hd
    subst hd
    exact Above.pure rfl
  · -- `defeq_type`: that constant inhabits `Prop`
    rw [witEnv_defeqs] at hd
    subst hd
    refine Above.pure ?_
    show (interp (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L [] ((VExpr.const c []).instL us)).toFun ∅
      ∈ (interp (V := V) ⟨κ, ls, fun _ _ ↦ ∅⟩ L [] ((VExpr.sort .zero).instL us)).toFun ∅
    rw [show (VExpr.const c []).instL us = .const c [] from rfl, interp_const, hsort]
    exact empty_mem_UProp

end Lean4Lean.SetModel
