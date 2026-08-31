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

## CORRECTION (2026-08-31): this route is blocked, and H1 above is vacuous

The reading at the top of this file — "the remaining work is exactly: inhabit those two" — is
wrong, and `Verify/PreludeVacuity.lean` proves why.  Two facts, both machine-checked there:

* `foldAddDecl_tr` (`Verify/Bridge.lean:172`), which `not_leanTTConsistent_of_kernel_proves_false`
  uses to obtain `TrEnv .safe env venv`, is a **false statement**.  `TrEnv .safe` is
  unsatisfiable once the environment holds one safe inductive
  (`TrEnv.not_safe_inductInfo`), and check B evaluates the checker to show `stdPrelude` leaves
  `Eq` exactly that.  The falsity comes from `addDecl.WF`, whose `inductDecl` branch is itself
  refuted (`Verify/Inductive/AddDeclWF.lean` §4), and both trace to `AddInduct` having no
  constructors.
* Therefore `Bridge.PreludeBridge stdPrelude` — H1 — is **vacuously true** at the instances used
  (`preludeBridge_vacuous_at_nil`).  It assumes the unsatisfiable `TrEnv .safe env venv`.
  Inhabiting it as stated buys the main theorem nothing.

`kernel_sound_of` below is still a correctly-proved theorem, and the assembly's *shape* is still
the shape the frozen edit will take.  What is not true is that applying it to two proofs would
finish the job: `Bridge.AddDeclWF` must first be reshaped to `AddDeclPost`
(`Verify/Inductive/AddDeclWF.lean` §5, `addDecl.WF_honest` already proved from the single
obligation `AddInductiveStepWF`), and `foldAddDecl_tr` re-derived from a fold-level invariant
that does not claim `TrEnv .safe`.  **Not** assumed as a hypothesis: §5.4 item 3 suggests that,
and `anything_of_foldAddDecl_tr_hypothesis` shows assuming it proves any proposition at all,
which would make guard 2 report "proof COMPLETE" over an empty proof.

`docs/critical-path.md` corrections 3 and 4 carry the full reading.
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
