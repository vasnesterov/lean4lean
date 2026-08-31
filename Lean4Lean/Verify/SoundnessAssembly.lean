import Lean4Lean.Verify.Bridge
import Lean4Lean.Theory.Equiconsistency

/-!
# The `kernel_sound` assembly

`Lean4Lean.kernel_sound` (in the frozen `Verify/Soundness.lean`) is a `sorry`.  This file
proves the whole of it *except* two named hypotheses, so that the remaining work on the main
theorem is exactly: inhabit those two, then apply `kernel_sound_of`.

The two hypotheses are

* `Bridge.PreludeBridge pre` — the refinement-side gap.  See its doc comment in
  `Verify/Bridge.lean`: it needs `AddInduct`'s constructors (that inductive is currently
  empty, so `TrEnv` provably contains no inductive at all, while `stdPrelude` is mostly
  `.inductDecl`s) plus a `foldAddDecl`-level invariant recording that the first `pre.length`
  steps were exactly the prelude.
* `Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent` — the model-side gap: the `←`
  half of `leanTT_equiconsistent_zfc_omega_inaccessibles`, whose remaining obligation
  (per `docs/soundness-ledger.md`) is the outer recursion building `ModelData.cnst` and
  `Coherent` by induction along the declaration list.

Everything between those two — the fold of `addDecl.WF`, the `TrEnv` transport, the `False`
witness, and the contraposition into `Inconsistent` — is proved.

## Why this file does not `import Lean4Lean.Verify.Soundness`

The frozen file will eventually import *this* one, so importing it here would be a cycle.
Consequently `kernel_sound_of` cannot mention `stdPrelude` (defined in the frozen file) and is
instead stated for an arbitrary prelude `pre`; at the frozen call site `pre := stdPrelude`.
For the same reason it uses `Bridge`'s mirrors of `foldAddDecl`, `Declaration.IsAxiomFree` and
`ContainsSafeProofOfFalse` rather than the frozen originals.  Those mirrors have bodies
identical to the frozen definitions, hence are definitionally equal to them, so `exact` closes
the frozen goal; `scripts/mirror-defeq.lean` machine-checks that (it may import both files
because it is a scratch script, not part of the build).

## The exact frozen edit this enables

None yet, and deliberately so: while `PreludeBridge stdPrelude` and the upper bound are
un-inhabited there is nothing to apply, and the frozen `sorry` must stay.  When both are
discharged, the edit to `Verify/Soundness.lean` is

    import Lean4Lean.Verify.SoundnessAssembly          -- added
    ...
    theorem kernel_sound ... :=
      Bridge.kernel_sound_of <prelude proof> <upper bound proof> ds fuel env hok hax hfalse

and it needs explicit human approval for that specific change before any agent makes it.
-/

namespace Lean4Lean.Bridge

open Lean hiding Environment Exception
open Kernel
open Lean4Lean
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- **The `kernel_sound` assembly.**  Modulo the two hypotheses `hpre` and `hub` described in
the module doc, this *is* `Lean4Lean.kernel_sound` — same conclusion, same premises, with
`pre` in place of `stdPrelude`.

Note both hypotheses are genuinely necessary rather than bookkeeping: `hub` is the direction of
the equiconsistency that carries the ZFC model, and `hpre` is the only link the refinement layer
cannot supply today. -/
theorem kernel_sound_of
    {pre : List Declaration} (hpre : PreludeBridge pre)
    (hub : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent)
    (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment)
    (hok : foldAddDecl fuel (pre ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  inconsistent_of_upper_bound hub
    (not_leanTTConsistent_of_kernel_proves_false hpre ds fuel env hok hax hfalse)

/-- The same, taking the full equiconsistency instead of just the upper bound. -/
theorem kernel_sound_of_equiconsistent
    {pre : List Declaration} (hpre : PreludeBridge pre)
    (heq : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent)
    (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment)
    (hok : foldAddDecl fuel (pre ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  kernel_sound_of hpre (upper_bound_of_equiconsistent heq) ds fuel env hok hax hfalse

end Lean4Lean.Bridge
