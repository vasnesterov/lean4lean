import Lean4Lean.Verify.Soundness
import Lean4Lean.Verify.SoundnessAssembly

/-!
# Are `Verify/Bridge.lean`'s mirrors really equal to the frozen definitions?

`Verify/Bridge.lean` cannot import the frozen `Verify/Soundness.lean` (the frozen file will
eventually import Bridge), so it *mirrors* four definitions and its docstring asserts they are
"definitionally equal to the frozen ones, so the frozen statement can be discharged by `exact`".

That assertion is load-bearing for `Bridge.kernel_sound_of` — and until this script existed it
was only prose.  This file may import both, because it is a scratch script and not part of the
build, so no import cycle arises.  Run:

    ~/.elan/bin/lake env lean scripts/mirror-defeq.lean

Silence (no output, no errors) means all four mirrors check, `syntactically` by `rfl`.
-/

open Lean Lean4Lean
open LO LO.FirstOrder LO.FirstOrder.SetTheory

example : @Lean4Lean.foldAddDecl = @Lean4Lean.Bridge.foldAddDecl := rfl
example : @Lean4Lean.Declaration.IsAxiomFree = @Lean4Lean.Bridge.Declaration.IsAxiomFree := rfl
example : Lean4Lean.falseExpr = Lean4Lean.Bridge.falseExpr := rfl
example : @Lean4Lean.ContainsSafeProofOfFalse = @Lean4Lean.Bridge.ContainsSafeProofOfFalse := rfl

/-- The real test: the frozen `kernel_sound` goal, verbatim, closed by `exact` from the
assembly. Stated with the two gaps as hypotheses, exactly as `kernel_sound_of` has them. -/
theorem frozen_goal_discharges
    (hpre : Bridge.PreludeBridge Lean4Lean.stdPrelude)
    (hub : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent)
    (ds : List Declaration) (fuel : FuelConfig)
    (env : Kernel.Environment)
    (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  Bridge.kernel_sound_of hpre hub ds fuel env hok hax hfalse

#print axioms frozen_goal_discharges
