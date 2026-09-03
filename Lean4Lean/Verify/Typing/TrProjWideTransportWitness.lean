import Lean4Lean.Verify.Typing.TrProjWideTransport
import Lean4Lean.Verify.Typing.TrProjWideWitness

/-!
# Firing tests for the three transports

A transport lemma needs a **firing** test, not a statement: apply it to a real `TrProjG`
derivation and exhibit the result.  The derivation used is `MutField.declEnv_trProjG`
(`Verify/Typing/TrProjWideWitness.lean`) — the two-type mutual block where `VEnv.IsStructure` is
outright false — and every side condition of the transport is discharged here, not assumed.

**The honest limit of these firings, stated up front.**  `MutField.decl` has `uvars = 0`,
`params = []` and `bTy.indices = []`, so at *this* derivation `us = ps = ιs = []`.  Consequently:

* `instL` at the only available `ls` (`[]`) is a level-substitution **no-op**;
* `instN` can only substitute for a variable that the derivation's terms do not contain, so the
  weaken-then-instantiate composite is a **round trip**.

Both still exercise every side condition of the transport lemma (that is what a firing test is
for), and the *non-degenerate* halves are fired elsewhere at richer blocks:
`Rich.projTermG_instN_fires` and `Poly.projTermG_instL_fires`
(`Verify/Typing/ProjGenInstWitness.lean:152, 251`) run the term-level commutation these
transports are built on, at `us = [.param 0]`, `ls = [.succ .zero]` and a non-empty parameter
spine.  I did not find, and do not claim there is, a `TrProjG` derivation anywhere in the tree
over a block with `uvars > 0` — searched: every `TrProj`/`TrProjG` derivation over a concrete
environment, i.e. `barEnv_TrProj` (`Verify/Typing/ProjWfWitness.lean`) and
`MutField.declEnv_trProjG`, both of which have `uvars = 0`.

`defeqDFC`'s firing is the one that is **not** degenerate: §3 moves the major premise from `x` to
its η-expansion `B.mk x.f`, a genuinely different subject.
-/

namespace Lean4Lean
namespace MutField

open VExpr

/-! ## 1. `instN` -/

/-- `Prop : Type`, in the witness context.  This is the term `instN` substitutes. -/
theorem prop_hasType : declEnv.HasType 0 bCtx (.sort .zero) (.sort (.succ .zero)) :=
  .sort trivial

/-- **`weakN` fired**, pushing the derivation under a fresh `Type` variable.  (Restated here
because it is `instN`'s input; `TrProjG.weakN` itself was landed in `TrProjWide.lean`.) -/
theorem declEnv_trProjG_weakN (hwf : VEnv.WF declEnv) :
    TrProjG declEnv 0 (VExpr.sort (.succ .zero) :: bCtx) `MutField.B 0
      ((VExpr.bvar 0).liftN 1 0)
      ((decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)).liftN 1 0) :=
  (declEnv_trProjG hwf).weakN hwf.ordered .one

/-- **`instN` fired**, on that derivation, substituting `Prop` for the fresh variable.

Every side condition is discharged: `VEnv.Ordered declEnv` from `hwf`, the `Ctx.InstN` by
`.zero`, and the substituted term's typing by `prop_hasType`.  The *conclusion* is the original
derivation back, because — as the module docstring says — this witness's terms do not mention
the substituted variable.  What it establishes is that `TrProjG.instN` **applies**, eleventh
field included, at a real derivation over a genuinely mutual block. -/
theorem declEnv_trProjG_instN (hwf : VEnv.WF declEnv) :
    TrProjG declEnv 0 bCtx `MutField.B 0 (.bvar 0)
      (decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)) := by
  have h := (declEnv_trProjG_weakN hwf).instN hwf.ordered (W := .zero) prop_hasType
  rwa [VExpr.inst_liftN, VExpr.inst_liftN] at h

/-! ## 2. `instL` -/

/-- **`instL` fired**, at the only level substitution the block admits (`decl.uvars = 0`, so
`us = []` and `ls = []`).  Degenerate as a level move — see the module docstring — but it does
discharge the lemma's one hypothesis (`∀ l ∈ ls, l.WF U'`, here `nofun`) and it does carry the
eleventh field through. -/
theorem declEnv_trProjG_instL (hwf : VEnv.WF declEnv) :
    TrProjG declEnv 0 (bCtx.map (VExpr.instL [])) `MutField.B 0 ((VExpr.bvar 0).instL [])
      ((decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)).instL []) :=
  (declEnv_trProjG hwf).instL nofun

/-- …and the context and subject really are unchanged by it, so the previous theorem is a
`TrProjG` at `bCtx` and `.bvar 0` on the nose. -/
theorem instL_nil_ctx_eq : bCtx.map (VExpr.instL []) = bCtx ∧ (VExpr.bvar 0).instL [] = .bvar 0 :=
  ⟨rfl, rfl⟩

/-! ## 3. `defeqDFC`, at a subject that genuinely changes -/

/-- **`defeqDFC` fired at the reflexive context and a reflexive defeq.**  Fully discharged
except `VEnv.WF declEnv`. -/
theorem declEnv_trProjG_defeqDFC_refl (hwf : VEnv.WF declEnv) :
    ∃ e'', TrProjG declEnv 0 bCtx `MutField.B 0 (.bvar 0) e'' :=
  (declEnv_trProjG hwf).defeqDFC hwf (.refl bCtx_onCtx)
    ⟨_, .bvar (.zero ..)⟩

/-- **`defeqDFC` fired at a subject that actually moves**: from the variable `x : B` to its
η-expansion `B.mk x.f`, using `declEnv_structEtaG` (`Verify/TypeChecker/EtaStructG.lean:504`).

This is the non-degenerate firing of the three.  It carries **two** open hypotheses and both are
named: `VEnv.WF declEnv` (this tree's keystone, open for everybody) and `declEnv.StructEtaG`.
The latter is *inhabited somewhere* — `VEnv.empty.StructEtaG` is proved
(`Verify/TypeChecker/EtaStructG.lean:339`) — and **not** proved at `declEnv`; it is the eta rule
as an assumption on the environment, exactly as `declEnv_structEtaG` itself takes it. -/
theorem declEnv_trProjG_defeqDFC_eta (hwf : VEnv.WF declEnv) (hSE : declEnv.StructEtaG) :
    ∃ e'', TrProjG declEnv 0 bCtx `MutField.B 0
      (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) e'' :=
  (declEnv_trProjG hwf).defeqDFC hwf (.refl bCtx_onCtx) ⟨_, declEnv_structEtaG hSE⟩

end MutField

end Lean4Lean
