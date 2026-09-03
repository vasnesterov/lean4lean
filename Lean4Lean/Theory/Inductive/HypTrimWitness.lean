import Lean4Lean.Theory.Inductive.RestoreBridge
import Lean4Lean.Theory.Inductive.ParamRedex
import Lean4Lean.Theory.Inductive.CtorBeta

/-!
# The `substC_tyAppR` trim, instantiated where the untrimmed form could not go

`VIndRestore.substC_tyAppR` (`Theory/Inductive/RestoreBridge.lean`) sat inside a
`variable … include hp hnd hown hlw hcl` group and so carried five hypotheses its proof never
uses, `hp : D.params = []` among them.  The five were invisible in the source: Lean's
`linter.unusedSectionVars` reports automatically-included section variables that go unused, but
an **explicit `include` suppresses it**, which is exactly why an `include` group can over-supply
undetected.

This file is the anti-vacuity check on the trim, and it is deliberately not the weak form of it.
The weak form would exhibit *some* instance of the trimmed statement.  The strong form, done
here, exhibits an instance at a block where the **removed** hypothesis is provably false, so that

* the trimmed lemma applies, and
* the untrimmed lemma provably could not have.

The block is `MRedex.MPWit.mpAux mpAuxNodeB` — a real nested block with `np = 1`, transcribed
against Lean's own environment there, whose companion spine mentions the parameter.

Nothing here is a hypothesis of anything downstream; this file is a witness, and every statement
in it is either arity-0 or universally quantified over `j`, `k`, `args` alone.
-/

namespace Lean4Lean
namespace HypTrimWitness

open MRedex.MPWit
open Lean (Name)

/-! ## 1  The removed hypothesis is FALSE at this block -/

/-- `mpAux mpAuxNodeB` has a parameter, so `hp : D.params = []` is refuted here. **This is what
makes the trim load-bearing rather than cosmetic**: with `hp` still in the signature,
`substC_tyAppR` had no instance at this block at all. -/
theorem mp_hp_false : ¬ (mpAux mpAuxNodeB).params = [] := by
  simp [mpAux]

/-- …and `np = 1`, not `0`. -/
theorem mp_np_eq_one : (mpAux mpAuxNodeB).np = 1 := rfl

/-! ## 2  The two hypotheses that survive are inhabited at that same block -/

/-- `hnn` at `mpRestore`: the presented heads are `MDep` and `MP`, and `mpK` is
`[_nested.MDep_1]`, so neither is in `csubstTy`'s domain. -/
theorem mp_hnn (i : Nat) :
    mpRestore.csubstTy (mpAux mpAuxNodeB) mpK (mpRestore.tyName i) = none := by
  refine VIndRestore.csubstTy_eq_none ?_
  show mpRestore.tyName i ∉ mpK
  by_cases h : i = 1 <;> simp [mpRestore, mpK, mpNestedName, h]

/-- `hna` at `mpRestore`: the presented spines mention only `MP`, which is likewise off the
domain.  Note that the spine at `i = 1` **does** mention a constant — this is not the vacuous
"no constants at all" case. -/
theorem mp_hna (i : Nat) : ∀ a ∈ mpRestore.tyArgs i,
    a.NoCSubst (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK) := by
  have hMP : mpRestore.csubstTy (mpAux mpAuxNodeB) mpK ``MP = none :=
    VIndRestore.csubstTy_eq_none (by simp [mpK, mpNestedName])
  intro a ha
  by_cases h : i = 1
  · subst h
    have ha' : a = .sort .zero ∨
        a = .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1)) := by
      simpa [mpRestore] using ha
    rcases ha' with rfl | rfl
    · exact trivial
    · exact ⟨trivial, hMP, trivial⟩
  · simp only [mpRestore, if_neg h, List.mem_singleton] at ha
    subst ha; exact trivial

/-- The spine at `i = 1` really is constant-bearing — recorded so that `mp_hna` cannot be read
as holding for the trivial reason. -/
theorem mp_tyArgs_one_mentions_MP :
    mpRestore.tyArgs 1 = [.sort .zero, .lam (.sort .zero) (.app (.const ``MP []) (.bvar 1))] :=
  rfl

/-- **The substitution is not the empty one.**  If `csubstTy` were everywhere `none`, `hnn` and
`hna` would hold for a trivial reason and everything below would be an unremarkable identity.  It
is not: `_nested.MDep_1` is in its domain. -/
theorem mp_csubstTy_at_companion :
    mpRestore.csubstTy (mpAux mpAuxNodeB) mpK mpNestedName
      = some (mpRestore.tyVal (mpAux mpAuxNodeB) 1) := rfl

theorem mp_csubstTy_nontrivial :
    mpRestore.csubstTy (mpAux mpAuxNodeB) mpK mpNestedName ≠ none := by
  rw [mp_csubstTy_at_companion]; exact nofun

/-! ## 3  The trimmed lemma, applied -/

/-- **`substC_tyAppR` at a block with a parameter.**  Its only hypotheses after the trim are the
two above; before the trim this statement had no proof, because `hp` is `mp_hp_false`. -/
theorem mp_substC_tyAppR (j k : Nat) (args : List VExpr) :
    ((mpAux mpAuxNodeB).tyAppR mpRestore j k args).substC
        (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)
      = (mpAux mpAuxNodeB).tyAppR mpRestore j k
          (args.map (VExpr.substC · (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK))) :=
  VIndRestore.substC_tyAppR mp_hnn mp_hna j k args

/-- **Arity 0.**  A closed instance with no hypotheses and no free variables, at the companion
member `j = 1` and a non-empty argument spine — so the conclusion is not the reflexivity of an
empty `mkApp`. -/
theorem mp_substC_tyAppR_closed :
    ((mpAux mpAuxNodeB).tyAppR mpRestore 1 0 [.sort .zero]).substC
        (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK)
      = (mpAux mpAuxNodeB).tyAppR mpRestore 1 0
          ([.sort .zero].map (VExpr.substC · (mpRestore.csubstTy (mpAux mpAuxNodeB) mpK))) :=
  mp_substC_tyAppR 1 0 [.sort .zero]

/-! ## 3b  `substC_tyAppR_free` is now literally redundant

`VIndRestore.substC_tyAppR_free` (`Theory/Inductive/CtorBeta.lean`) was written *because* the
untrimmed `substC_tyAppR` was unusable.  After the trim the two statements coincide, and this
`rfl` is the machine check of that — it typechecks only if the two types are definitionally
equal (proof irrelevance then closes it).  `CtorBeta.lean` is not this stream's file, so the
duplicate is reported, not deleted. -/

theorem free_eq_trimmed :
    @VIndRestore.substC_tyAppR_free = @VIndRestore.substC_tyAppR := rfl

/-! ## 4  …and the same for the cascaded trim

`ctorType_substC_eq_typeR_substC` lost `hcl` as a *consequence* of the two trims above.  That one
is only redundant, not false: `hcl0` (which the statement keeps) implies it.  Recorded as a
one-line derivation so the claim "redundant" is machine-checked rather than asserted. -/

theorem hcl_of_hcl0 {R : VIndRestore} {D : VInductDecl'}
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) :
    ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np :=
  fun i a ha => (hcl0 i a ha).mono (Nat.zero_le _)

#print axioms Lean4Lean.HypTrimWitness.mp_hp_false
#print axioms Lean4Lean.HypTrimWitness.mp_hnn
#print axioms Lean4Lean.HypTrimWitness.mp_hna
#print axioms Lean4Lean.HypTrimWitness.mp_substC_tyAppR
#print axioms Lean4Lean.HypTrimWitness.mp_substC_tyAppR_closed
#print axioms Lean4Lean.HypTrimWitness.mp_csubstTy_at_companion
#print axioms Lean4Lean.HypTrimWitness.mp_csubstTy_nontrivial
#print axioms Lean4Lean.HypTrimWitness.free_eq_trimmed
#print axioms Lean4Lean.HypTrimWitness.hcl_of_hcl0

end HypTrimWitness
end Lean4Lean
