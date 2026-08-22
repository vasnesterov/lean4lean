import Lean4Lean.Theory.SetModel.InterpSound
import Lean4Lean.Theory.Typing.Strong

/-!
# Assembling the thirteen cases

`SetModel/InterpSound.lean` proves each rule's obligation as a standalone lemma.
This file runs the induction that ties them together.

## Two design decisions, both forced

**The induction is on `IsDefEqStrong`, not `IsDefEq`.**  Several cases need the
sort derivations for *intermediate* types — `appDF` needs `A::Γ ⊢ B : .sort v`
to know whether `B` is a proposition, which is the branch `interp` takes.  From
plain `IsDefEq.appDF` that is `forallE_inv`, one of the injectivity `sorry`s.
`IsDefEqStrong` carries it as a premise, and `IsDefEq.strong`
(`Theory/Typing/Strong.lean`, sorry-free) converts, needing only `Ordered env`
and a well-formed context.  So the assembly costs **no** injectivity beyond
`sort_inv`, which is spent on `LevelAssign` and nothing else.

**The universe bound is a threshold, not a property of the judgement.**  The
original `SoundBound` bounded the levels appearing in the *conclusion*.  That
does not work: in `appDF` the domain `A` does not occur in the conclusion at
all, so `f : A → B` with `A : Sort 100` and `B : Prop` has a conclusion whose
levels are all `≤ 1` and a subderivation that needs the 100th inaccessible.  No
bound on the conclusion can be inherited by the premises.

Nor can the bound be moved onto `L`: `L.lvl Γ (.sort k) = k+1` for every `k`, so
no single `n` bounds a fixed environment's assignment.

What is true is that a *derivation* mentions finitely many levels.  `SoundAbove`
says exactly that: there is a threshold `m`, produced by the induction from the
derivation, such that any chain of `m` inaccessibles validates the judgement.
The `∃` is over derivations and comes *before* the model is quantified, so this
is the schema form and not an `∃ k` about the model.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign env nv}

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- A chain of `n` inaccessibles is a chain of `m` inaccessibles for `m ≤ n`.
This is what lets the induction take the maximum of its premises' thresholds. -/
theorem IsInaccessibleChain.le {m n : ℕ} {κ : ℕ → V} (h : m ≤ n)
    (H : IsInaccessibleChain n κ) : IsInaccessibleChain m κ where
  inaccessible i hi := H.inaccessible i (Nat.lt_of_lt_of_le hi h)
  mem i j hij hj := H.mem i j hij (Nat.lt_of_lt_of_le hj h)

/-- **Soundness above a threshold.**  There is an `m`, determined by the
derivation, such that any chain of `m` inaccessibles validates the judgement. -/
def SoundAbove (M : ModelData V) (L : LevelAssign env nv)
    (Γ : List VExpr) (e₁ e₂ A : VExpr) : Prop :=
  ∃ m : ℕ, IsInaccessibleChain m M.κ → Sound M L Γ e₁ e₂ A

theorem SoundAbove.of_le {Γ : List VExpr} {e₁ e₂ A : VExpr} {m : ℕ}
    (h : IsInaccessibleChain m M.κ → Sound M L Γ e₁ e₂ A) : SoundAbove M L Γ e₁ e₂ A := ⟨m, h⟩

/-! ### The proof-splitting decisions, read off the judgement

`interp` branches on `L.IsProp`/`L.IsProof`, which are total functions of the
syntax.  On *well-typed* input they are pinned by `lvl_sound`/`srt_sound`, and
these two lemmas are how every case discharges its `hsplit` hypothesis. -/

/-- A type is a proposition exactly when its sort evaluates to `0`. -/
theorem isProp_iff {Γ : List VExpr} {A : VExpr} {u : VLevel} (hA : env.HasType nv Γ A (.sort u)) :
    L.IsProp M Γ A ↔ u.eval M.ls = 0 := by
  rw [LevelAssign.IsProp, VLevel.equiv_def.mp (L.lvl_sound hA) M.ls]

/-- A term is a proof exactly when the sort of its type evaluates to `0`. -/
theorem isProof_iff {Γ : List VExpr} {e A : VExpr} {u : VLevel} (he : env.HasType nv Γ e A)
    (hA : env.HasType nv Γ A (.sort u)) : L.IsProof M Γ e ↔ u.eval M.ls = 0 := by
  rw [LevelAssign.IsProof, VLevel.equiv_def.mp (L.srt_sound he) M.ls,
    VLevel.equiv_def.mp (L.lvl_sound hA) M.ls]

end

end Lean4Lean.SetModel
