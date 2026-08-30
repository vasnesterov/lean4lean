import Lean4Lean.Verify.Typing.ProjGenLift
import Lean4Lean.Verify.Typing.ProjClosedGWitness

/-!
# Non-vacuity for block A's `lift'` family

`ProjGenLift.lean` proves `projCoreG_lift'`/`projArgsG_lift'`/`projTermG_lift'` under a
`VInductDecl'.ProjClosedG` hypothesis.  Two things have to be checked before that counts:

* the hypothesis is **satisfiable at a block the generalisation is for** — a recursive one,
  where `minorBinders` really does splice a recursive field's `ξ` and `π` in.  `Rich`
  (`ProjClosedGWitness.lean`) is such a block, and `projCoreG_lift'_fires` runs the whole
  chain there;
* the hypothesis is **not vacuously true** — `ProjClosedGap.badCtor_not_projClosedG` and
  `argsCtor_not_projClosedG` (same file) are two blocks at which it is *false*, one for each
  conjunct of the fourth field;
* the conclusion is **not an identity** — `padMinor_lift_moves` below shows the lift moves
  four distinct variables of the padding minor at `Rich`, two of them inside the induction
  hypothesis.
-/

namespace Lean4Lean

open VExpr

namespace Rich

/-- **`projCoreG_lift'` fired end to end**, at a block with a parameter, an index, and a
recursive field whose `ξ` and `π` are both non-empty.  Every premise is discharged: the
`ProjClosedG` from `richBlock_projClosedG`, the two length side conditions and the
field-index bound by `rfl`/arithmetic. -/
theorem projCoreG_lift'_fires :
    (richBlock.projCoreG richTy richCtor [] [.bvar 0] [.bvar 1] 0 0 [] (.bvar 2)).lift'
        (.skip .refl)
      = richBlock.projCoreG richTy richCtor [] [.bvar 1] [.bvar 2] 0 0 [] (.bvar 3) :=
  richBlock.projCoreG_lift' richTy richCtor [] richBlock_projClosedG
    (ρ := .skip .refl) rfl rfl rfl rfl rfl (show (0:Nat) < 2 from by omega)

/-- …and `projTermG_lift'` too, which is the entry `TrProj.weak'` would run on. -/
theorem projTermG_lift'_fires :
    (richBlock.projTermG richTy richCtor [] [.bvar 0] [.bvar 1] 0 0 (.bvar 2)).lift'
        (.skip .refl)
      = richBlock.projTermG richTy richCtor [] [.bvar 1] [.bvar 2] 0 0 (.bvar 3) :=
  richBlock.projTermG_lift' richTy richCtor [] richBlock_projClosedG
    (ρ := .skip .refl) rfl rfl rfl rfl (show (0:Nat) < 2 from by omega)

/-- The padding minor at `Rich`, computed, before and after the lift.  **Four distinct
variables move** — the field type `.bvar 0 → .bvar 1`, the induction hypothesis's own `ξ`
binder `.bvar 2 → .bvar 3`, the motive it applies `.bvar 4 → .bvar 5`, and the padding
type `.bvar 5 → .bvar 6` — so `padMinor_lift'` is not an identity here, and neither is
anything built on it. -/
theorem padMinor_at_rich :
    richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor
      = .lam (.bvar 0)
          (.lam (.const `Rich.Dummy [])
            (.lam (.forallE (.bvar 2)
                (((VExpr.bvar 4).app (.bvar 0)).app ((VExpr.bvar 1).app (.bvar 0))))
              (.lam (.bvar 5) (.bvar 0)))) := rfl

theorem padMinor_at_rich_lifted :
    (richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor).lift' (.skip .refl)
      = .lam (.bvar 1)
          (.lam (.const `Rich.Dummy [])
            (.lam (.forallE (.bvar 3)
                (((VExpr.bvar 5).app (.bvar 0)).app ((VExpr.bvar 1).app (.bvar 0))))
              (.lam (.bvar 6) (.bvar 0)))) := rfl

/-- **The lift is not the identity on the padding minor.**  Machine-checked, not read off
the two computations above: the inequality is decided from the constructors' `injEq`. -/
theorem padMinor_lift_moves :
    (richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor).lift' (.skip .refl)
      ≠ richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor := by
  rw [padMinor_at_rich_lifted, padMinor_at_rich]
  simp

end Rich

end Lean4Lean
