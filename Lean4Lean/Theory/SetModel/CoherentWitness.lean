import Lean4Lean.Theory.SetModel.Cnst
import Lean4Lean.Theory.SetModel.Inductive
import Lean4Lean.Theory.Typing.Lemmas

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

/-! ## `CtxInvariant` paired with `hRd` is consistent — and *why* is the point

`CtxInvariant L R` is trivially satisfiable alone (take `R := Eq`), so testing
the field in isolation proves nothing.  It is always used together with a second
hypothesis relating defeq-differing contexts,

```
hRd : env.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ)
```

and "two constraints on one object" is exactly the shape that broke
`LevelAssign`.  So the pair is what must be tested.

**It is consistent, and for a structural reason worth stating**, because it is
the diagnostic that separates this case from the two refutations:

> The defect signature is a structure quantifying over a relation **parameter**
> that the relation's own constructors never constrain.

* `IsDefEq.bvar` places no condition on the context — so `LevelAssign`'s two
  fields could be pointed at a context holding an ill-formed level.
* `Ctx.InstN` declares `e₀` as a parameter its `zero` constructor never mentions
  — so `Stable`'s `lvl_instN` could be pointed at an arbitrary substituted term.
* `hRd`'s `A` and `A'` are **not** free: they come with a derivation
  `Γ ⊢ A ≡ A' : .sort u`.  That derivation is exactly what makes the two demands
  agree, via context conversion (`IsDefEq.defeqDFC`, proved).

`ctxInvariant_lvl_agrees` below is that argument, machine-checked: on every
well-typed `B` — which is where `CtxInvariant.lvl` has content — the level
demanded in `A :: Γ` and the level demanded in `A' :: Γ` are the same. -/

theorem ctxInvariant_lvl_agrees {env : VEnv} {nv : ℕ} (L : LevelAssign env nv)
    (henv : env.Ordered) {Γ : List VExpr} {A A' B : VExpr} {u w : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) (hww : w.WF nv)
    (hB : env.HasType nv (A :: Γ) B (.sort w)) :
    L.lvl (A :: Γ) B ≈ L.lvl (A' :: Γ) B := by
  have hctx : VEnv.IsDefEqCtx env nv Γ (A :: Γ) (A' :: Γ) := .succ .zero h
  have hB' : env.HasType nv (A' :: Γ) B (.sort w) := hB.defeqDFC henv hctx
  exact (L.lvl_sound hww hB).trans (L.lvl_sound hww hB').symm

/-! ## The three inductive-side structures pass the declaration check

Applying the test to `IndSignature`, `IsStageSignature` and
`IsSubsingletonSignature`: **none of them quantifies over syntax at all.**

That is the sharper form of the diagnostic. `LevelAssign` and
`LevelAssign.Stable` broke because they quantified over `List VExpr` and
`VExpr` — objects the *syntax* side supplies, at a generality it never intends
to produce. These three quantify only over their own set-theoretic data: every
binder is bounded by `S.Q` or `S.Fld q`, which the structure itself provides.
There is no external relation whose parameters could be left free, so the defect
signature cannot fire.

`IndSignature` is plain data plus four definability facts about the very
functions it supplies. `IsStageSignature` is four membership conditions bounded
by `S.Q`/`S.Fld`. `IsSubsingletonSignature` is two conditions likewise bounded.

Witnesses below for the two that need no side conditions, chosen so the fields
do real work rather than being vacuous: two distinct field values, so
`fld_det` is a genuine injectivity requirement rather than a statement about a
one-element set. `IsStageSignature` additionally needs `S.Q`, `S.Idx` and the
`Fld`/`Pos` values to sit below a given stage, so a witness for it is relative
to a choice of `k`; it is the least exposed of the three by the criterion above
and is left at the declaration check. -/

/-- A one-constructor signature with two non-recursive field values and no
recursive positions.  `resIdx` is the identity on fields, which is what makes
`fld_det` non-vacuous. -/
noncomputable def witSig : IndSignature V where
  Idx := insert (∅ : V) {({∅} : V)}
  Q := {(∅ : V)}
  Fld _ := insert (∅ : V) {({∅} : V)}
  Pos _ _ := ∅
  posIdx _ _ _ := ∅
  resIdx _ a := a
  Fld_definable := by definability
  Pos_definable := by definability
  posIdx_definable := by definability
  resIdx_definable := by definability

/-- **`IsSubsingletonSignature` is satisfiable**, with `fld_det` doing real work:
the field set has two elements and they are separated by `resIdx`. -/
theorem witSig_subsingleton : IsSubsingletonSignature (witSig (V := V)) where
  single q hq q' hq' := by
    rw [mem_singleton_iff.1 hq, mem_singleton_iff.1 hq']
  fld_det _ _ _ _ _ _ h := h

end Lean4Lean.SetModel
