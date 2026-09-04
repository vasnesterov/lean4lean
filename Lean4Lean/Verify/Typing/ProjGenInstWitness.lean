import Lean4Lean.Theory.Inductive.ProjGenInst
import Lean4Lean.Verify.Typing.ProjGenBeta
import Lean4Lean.Verify.Typing.ProjClosedGWitness
import Lean4Lean.Verify.Typing.ProjGenLiftWitness

/-!
# Non-vacuity for block A's `inst` and `instL` families

`ProjGenInst.lean` proves the `instN` family under `VInductDecl'.ProjClosedG` and the `instL`
family under **no** hypothesis at all.  Four different things have to be checked, and this
file keeps them apart.

1. **The refutation is re-run against the fix — at the conclusion, not just the predicate.**
   `ProjClosedGap.badCtor_not_projClosedG` (`ProjClosedGWitness.lean`) showed that block A's
   hypothesis *fails* at `blockOf badCtor`.  `padMinor_instN_false_at_badCtor` below is
   stronger: at that block — which satisfies all three `ProjClosed` fields — the *conclusion*
   of `padMinor_instN` is **false**.  So the hypothesis is not decoration.
2. **The second conjunct is not a passenger.**  `argsCtor` moves only the stored `π`, with
   `ξ` empty; `padMinor_instN_false_at_argsCtor` shows the conclusion still fails, and
   `padMinor_at_argsCtor_*` locates the discrepancy at the `π`-derived variable.
3. **The consumer fires where the closedness bound is exactly saturated.**  `Rich` is the
   block of `ProjClosedGWitness.lean`, whose `minorBinders` is closed at `np + nm + q = 2`
   and **not** at `1` (`Rich.minorBinders_not_closed_at_1`).  `projCoreG_instN_fires` and
   `projTermG_instN_fires` run the whole `instN` chain there, and `padMinor_inst_moves`
   shows the substitution moves **four distinct** positions of the padding minor.
4. **The `instL` family is not vacuous.**  `Rich` has no universe parameters, so `instL` is
   the identity on it and a firing there would test nothing.  `Poly` is a block with one
   universe parameter and `isLE := true`, so that `projLvls` really reads the projected
   field's level; `projMotive_instL_moves` and `projLvls_moves` are the disequalities.

Two negative controls, neither an arity error, are in §5: the `i < C'.fields.length` of
`realMinor_instN` and the `1 ≤ k` of `projArgsG_instN` are each shown load-bearing by a
block/offset at which the conclusion is false.
-/

namespace Lean4Lean

open VExpr

/-! ## 1–2. The refutation, re-run at the conclusion -/

namespace ProjClosedGap

/-- The padding minor at `blockOf badCtor`, at a spine of the right arity (`np + nm + q = 1`),
computed.  The stored `ξ` reached past the spine, so the second binder's type still mentions
`.bvar 1`, which is *inside* the substitution's window. -/
theorem padMinor_at_badCtor :
    (blockOf badCtor).padMinor [] [.bvar 0] (.bvar 0) 0 badCtor
      = .lam qty
          (.lam (.forallE (.bvar 1) ((VExpr.bvar 2).app ((VExpr.bvar 1).app (.bvar 0))))
            (.lam (.bvar 2) (.bvar 0))) := rfl

/-- Substituting first. -/
theorem padMinor_at_badCtor_inst :
    ((blockOf badCtor).padMinor [] [.bvar 0] (.bvar 0) 0 badCtor).inst
        (.const `ProjClosedGap.W []) 0
      = .lam qty
          (.lam (.forallE (.const `ProjClosedGap.W [])
              ((VExpr.const `ProjClosedGap.W []).app ((VExpr.bvar 1).app (.bvar 0))))
            (.lam (.const `ProjClosedGap.W []) (.bvar 0))) := rfl

/-- Substituting into the spine instead. -/
theorem padMinor_at_badCtor_spine :
    (blockOf badCtor).padMinor [] [.const `ProjClosedGap.W []] (.const `ProjClosedGap.W [])
        0 badCtor
      = .lam qty
          (.lam (.forallE (.bvar 1)
              ((VExpr.const `ProjClosedGap.W []).app ((VExpr.bvar 1).app (.bvar 0))))
            (.lam (.const `ProjClosedGap.W []) (.bvar 0))) := rfl

/-- **The refutation, re-run against this round's lemma.**  At `blockOf badCtor` — a block
satisfying all three `ProjClosed` fields — the *conclusion* of `padMinor_instN` is false.
The discrepancy is at the induction hypothesis's own binder, i.e. at the stored `ξ`: `.bvar 1`
on one side, the substituted constant on the other. -/
theorem padMinor_instN_false_at_badCtor :
    ((blockOf badCtor).padMinor [] [.bvar 0] (.bvar 0) 0 badCtor).inst
        (.const `ProjClosedGap.W []) 0
      ≠ (blockOf badCtor).padMinor []
          ([(.bvar 0 : VExpr)].map (·.inst (.const `ProjClosedGap.W []) 0))
          ((VExpr.bvar 0).inst (.const `ProjClosedGap.W []) 0) 0 badCtor := by
  rw [padMinor_at_badCtor_inst,
    show ((blockOf badCtor).padMinor []
        ([(.bvar 0 : VExpr)].map (·.inst (.const `ProjClosedGap.W []) 0))
        ((VExpr.bvar 0).inst (.const `ProjClosedGap.W []) 0) 0 badCtor)
      = (blockOf badCtor).padMinor [] [.const `ProjClosedGap.W []]
          (.const `ProjClosedGap.W []) 0 badCtor from rfl,
    padMinor_at_badCtor_spine]
  simp

/-! ### The `args` conjunct, separately -/

theorem padMinor_at_argsCtor_inst :
    ((blockOf argsCtor).padMinor [] [.bvar 0] (.bvar 0) 0 argsCtor).inst
        (.const `ProjClosedGap.W []) 0
      = .lam qty
          (.lam (((VExpr.const `ProjClosedGap.W []).app (.const `ProjClosedGap.W [])).app
              (.bvar 0))
            (.lam (.const `ProjClosedGap.W []) (.bvar 0))) := rfl

theorem padMinor_at_argsCtor_spine :
    (blockOf argsCtor).padMinor [] [.const `ProjClosedGap.W []] (.const `ProjClosedGap.W [])
        0 argsCtor
      = .lam qty
          (.lam (((VExpr.const `ProjClosedGap.W []).app (.bvar 1)).app (.bvar 0))
            (.lam (.const `ProjClosedGap.W []) (.bvar 0))) := rfl

/-- **The second conjunct is not a passenger here either.**  `argsCtor`'s `ξ` is empty and
all three `ProjClosed` fields hold; the conclusion of `padMinor_instN` still fails, and the
position it fails at is the one the stored `π` contributed. -/
theorem padMinor_instN_false_at_argsCtor :
    ((blockOf argsCtor).padMinor [] [.bvar 0] (.bvar 0) 0 argsCtor).inst
        (.const `ProjClosedGap.W []) 0
      ≠ (blockOf argsCtor).padMinor []
          ([(.bvar 0 : VExpr)].map (·.inst (.const `ProjClosedGap.W []) 0))
          ((VExpr.bvar 0).inst (.const `ProjClosedGap.W []) 0) 0 argsCtor := by
  rw [padMinor_at_argsCtor_inst,
    show ((blockOf argsCtor).padMinor []
        ([(.bvar 0 : VExpr)].map (·.inst (.const `ProjClosedGap.W []) 0))
        ((VExpr.bvar 0).inst (.const `ProjClosedGap.W []) 0) 0 argsCtor)
      = (blockOf argsCtor).padMinor [] [.const `ProjClosedGap.W []]
          (.const `ProjClosedGap.W []) 0 argsCtor from rfl,
    padMinor_at_argsCtor_spine]
  simp

end ProjClosedGap

/-! ## 3. The `instN` family, fired at `Rich` -/

namespace Rich

/-- **`padMinor_instN` fired** at the exactly-saturated bound: `Rich.minorBinders_closed`
is `ClosedTele … (np + nm + q) = … 2`, and the spine here has length `2`.
`Rich.minorBinders_not_closed_at_1` is the matching negative control. -/
theorem padMinor_instN_fires :
    (richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor).inst
        (.const `Rich.W []) 0
      = richBlock.padMinor [] [.const `Rich.W [], .bvar 0] (.bvar 1) 0 richCtor :=
  richBlock.padMinor_instN [] (spine := [.bvar 0, .bvar 1]) (X := .bvar 2)
    (e₀ := .const `Rich.W []) (k := 0) minorBinders_closed

/-- **`projCoreG_instN` fired end to end**, at a block with a parameter, an index and a
recursive field whose `ξ` and `π` are both non-empty.  Every premise is discharged. -/
theorem projCoreG_instN_fires :
    (richBlock.projCoreG richTy richCtor [] [.bvar 1] [.bvar 2] 0 0 [] (.bvar 3)).inst
        (.const `Rich.W []) 1
      = richBlock.projCoreG richTy richCtor [] [.const `Rich.W []] [.bvar 1] 0 0 []
          (.bvar 2) :=
  richBlock.projCoreG_instN richTy richCtor [] richBlock_projClosedG
    (e₀ := .const `Rich.W []) (k := 1) rfl rfl rfl rfl rfl (show (0:Nat) < 2 from by omega)

/-- …and `projTermG_instN` too, which is the entry `TrProj.instN` would run on. -/
theorem projTermG_instN_fires :
    (richBlock.projTermG richTy richCtor [] [.bvar 1] [.bvar 2] 0 0 (.bvar 3)).inst
        (.const `Rich.W []) 1
      = richBlock.projTermG richTy richCtor [] [.const `Rich.W []] [.bvar 1] 0 0 (.bvar 2) :=
  richBlock.projTermG_instN richTy richCtor [] richBlock_projClosedG
    (e₀ := .const `Rich.W []) (k := 1) rfl rfl rfl rfl (show (0:Nat) < 2 from by omega)

/-- The padding minor at `Rich` after the substitution.  Compare `Rich.padMinor_at_rich`
(`ProjGenLiftWitness.lean`): **four distinct positions move** — the field type
`.bvar 0 ↦ W`, the induction hypothesis's own `ξ` binder `.bvar 2 ↦ W`, the motive it
applies `.bvar 4 ↦ .bvar 3`, and the padding type `.bvar 5 ↦ .bvar 4`.  Two of the four are
replacements and two are renumberings, so this is not the same test the lift witness ran. -/
theorem padMinor_at_rich_inst :
    (richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor).inst
        (.const `Rich.W []) 0
      = .lam (.const `Rich.W [])
          (.lam (.const `Rich.Dummy [])
            (.lam (.forallE (.const `Rich.W [])
                (((VExpr.bvar 3).app (.bvar 0)).app ((VExpr.bvar 1).app (.bvar 0))))
              (.lam (.bvar 4) (.bvar 0)))) := rfl

/-- **The substitution is not the identity on the padding minor.**  Machine-checked from the
constructors' `injEq`, not read off the two computations. -/
theorem padMinor_inst_moves :
    (richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor).inst
        (.const `Rich.W []) 0
      ≠ richBlock.padMinor [] [.bvar 0, .bvar 1] (.bvar 2) 0 richCtor := by
  rw [padMinor_at_rich_inst, padMinor_at_rich]
  simp

end Rich

/-! ## 4. The `instL` family, at a block whose levels actually move

`Rich` and `blockOf _` both have `uvars = 0` and only closed levels, so `instL` is the
identity on them: the `instL` lemmas would fire there and test nothing.  `Poly` has one
universe parameter, and `isLE := true` so that `projLvls` reads the projected field's own
level rather than just `us`. -/

namespace Poly

def polyCtor : VIndCtor where
  name := `Poly.Q.mk
  params := [.sort (.param 0)]
  fields := [{ type := .bvar 0, lvl := .param 0, recArg := none }]
  args := []

def polyTy : VIndType where
  name := `Poly.Q
  type := .sort (.succ (.param 0))
  indices := []
  ctors := [polyCtor]

def polyBlock : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0)]
  lvl := .param 0
  isLE := true
  types := [polyTy]

/-- The recursor's level arguments here are `[u, u]` — the `isLE` branch, so the projected
field's own level is the head.  A block with `isLE := false` would give `[u]` and the head
would carry no field data at all. -/
theorem projLvls_at_poly :
    polyBlock.projLvls polyCtor [.param 0] 0 = [.param 0, .param 0] := rfl

/-- **`projLvls_inst` fired**, and both sides are the substituted list. -/
theorem projLvls_inst_fires :
    (polyBlock.projLvls polyCtor [.param 0] 0).map (VLevel.inst [.succ .zero])
      = polyBlock.projLvls polyCtor [.succ .zero] 0 :=
  polyBlock.projLvls_inst polyCtor [.param 0] [.succ .zero] 0

/-- **The level substitution is not the identity** on the recursor's level arguments. -/
theorem projLvls_moves :
    (polyBlock.projLvls polyCtor [.param 0] 0).map (VLevel.inst [.succ .zero])
      ≠ polyBlock.projLvls polyCtor [.param 0] 0 := by
  rw [projLvls_at_poly]
  simp [VLevel.inst]

theorem projMotive_at_poly :
    polyTy.projMotive polyCtor [.param 0] [.sort (.param 0)] [] 0 []
      = .lam ((VExpr.const `Poly.Q [.param 0]).app (.sort (.param 0)))
          (.sort (.param 0)) := rfl

theorem projMotive_at_poly_instL :
    (polyTy.projMotive polyCtor [.param 0] [.sort (.param 0)] [] 0 []).instL [.succ .zero]
      = .lam ((VExpr.const `Poly.Q [.succ .zero]).app (.sort (.succ .zero)))
          (.sort (.succ .zero)) := rfl

/-- **The level substitution is not the identity** on the real motive either: it moves both
the block constant's level list and the stored field type's sort. -/
theorem projMotive_instL_moves :
    (polyTy.projMotive polyCtor [.param 0] [.sort (.param 0)] [] 0 []).instL [.succ .zero]
      ≠ polyTy.projMotive polyCtor [.param 0] [.sort (.param 0)] [] 0 [] := by
  rw [projMotive_at_poly_instL, projMotive_at_poly]
  simp [VLevel.inst]

/-- **`projTermG_instL` fired end to end** at that block.  It takes no hypothesis, which is
the point of the `instL` half: `instL` moves no de Bruijn index, so no `ProjClosedG`. -/
theorem projTermG_instL_fires :
    (polyBlock.projTermG polyTy polyCtor [.param 0] [.sort (.param 0)] [] 0 0
        (.bvar 0)).instL [.succ .zero]
      = polyBlock.projTermG polyTy polyCtor [.succ .zero] [.sort (.succ .zero)] [] 0 0
          (.bvar 0) :=
  polyBlock.projTermG_instL polyTy polyCtor [.param 0] [.succ .zero]
    [.sort (.param 0)] [] 0 0 (.bvar 0)

end Poly

/-! ## 5. Two negative controls, neither an arity error -/

namespace InstControls

/-- A nullary constructor: no fields, no induction hypotheses, so `minorBinders` is empty
and `realMinor`'s body is `.bvar 0` in the *ambient* context. -/
def nullCtor : VIndCtor where
  name := `InstControls.N.mk
  params := []
  fields := []
  args := []

def nullBlock : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types := [{ name := `InstControls.N, type := .sort (.succ .zero), indices := [],
              ctors := [nullCtor] }]

/-- The `ClosedTele` hypothesis of `realMinor_instN` holds vacuously here — the telescope is
empty — so the only premise standing between this block and the conclusion is
`i < C'.fields.length`. -/
theorem nullCtor_hcl :
    VExpr.ClosedTele ((nullBlock.minorBinders 0 nullCtor).map (VExpr.instL []))
      ([(.bvar 0 : VExpr)].length) := trivial

theorem realMinor_at_nullCtor :
    nullBlock.realMinor [] [.bvar 0] 0 0 nullCtor = .bvar 0 := rfl

/-- **Negative control 1: `i < C'.fields.length` is not slack.**  At a nullary constructor
the hypothesis is the only one that fails, and the conclusion of `realMinor_instN` is false:
the body is a variable of the *ambient* context, which the substitution replaces on the left
and leaves alone on the right.  This is not an arity error — both sides are the same
`realMinor` at the same block, spine length and minor index. -/
theorem realMinor_instN_false_without_hi :
    (nullBlock.realMinor [] [.bvar 0] 0 0 nullCtor).inst (.const `InstControls.W []) 0
      ≠ nullBlock.realMinor []
          ([(.bvar 0 : VExpr)].map (·.inst (.const `InstControls.W []) 0)) 0 0 nullCtor := by
  rw [realMinor_at_nullCtor,
    show (nullBlock.realMinor []
        ([(.bvar 0 : VExpr)].map (·.inst (.const `InstControls.W []) 0)) 0 0 nullCtor)
      = .bvar 0 from rfl]
  simp [VExpr.inst, VExpr.instVar, VExpr.liftN]

/-- The major premise of the innermost `projCoreG` inside `projArgsG` is `.bvar 0`, which is
what the `1 ≤ k` of `projArgsG_instN` protects. -/
theorem projArgsG_one_at_rich :
    (Rich.richBlock.projArgsG Rich.richTy Rich.richCtor [] [.bvar 0] [.bvar 1] 0 1).length
      = 1 := Rich.richBlock.length_projArgsG _ _ _ _

/-- The last argument of an application spine.  `projCoreG`'s spine ends with the major
premise, so this reads it off without computing the rest of the term. -/
def lastArg : VExpr → VExpr
  | .app _ a => a
  | e => e

/-- Substituting at `k = 0` replaces the major premise. -/
theorem lastArg_lhs :
    lastArg (((Rich.richBlock.projArgsG Rich.richTy Rich.richCtor [] [.bvar 0] [.bvar 1] 0 1).map
      (·.inst (.const `Rich.W []) 0)).getD 0 default) = .const `Rich.W [] := rfl

/-- Substituting into the data leaves it alone. -/
theorem lastArg_rhs :
    lastArg ((Rich.richBlock.projArgsG Rich.richTy Rich.richCtor []
      ([(.bvar 0 : VExpr)].map (·.inst (.const `Rich.W []) 0))
      ([(.bvar 1 : VExpr)].map (·.inst (.const `Rich.W []) 0)) 0 1).getD 0 default)
      = .bvar 0 := rfl

/-- **Negative control 2: `1 ≤ k` is not slack.**  At `k = 0` the substitution reaches the
major-premise binder `.bvar 0` that `projArgsG` puts under the index binders, and the
conclusion of `projArgsG_instN` is false.  Not an arity error: `length_projArgsG` says both
sides are one-element lists (`projArgsG_one_at_rich`), and the block, the spine lengths and
the field index are the same on both sides. -/
theorem projArgsG_instN_false_at_zero :
    (Rich.richBlock.projArgsG Rich.richTy Rich.richCtor [] [.bvar 0] [.bvar 1] 0 1).map
        (·.inst (.const `Rich.W []) 0)
      ≠ Rich.richBlock.projArgsG Rich.richTy Rich.richCtor []
          ([(.bvar 0 : VExpr)].map (·.inst (.const `Rich.W []) 0))
          ([(.bvar 1 : VExpr)].map (·.inst (.const `Rich.W []) 0)) 0 1 := by
  intro h
  have h2 := lastArg_lhs
  rw [h, lastArg_rhs] at h2
  simp at h2

end InstControls

/-! ## 6. Ingredient (b) of `realMinor_hasType_gen`, fired

`ProjGenBeta.lean` generalises `projMotiveBody_instAll` and its three callees to an arbitrary
block index.  Three checks: it fires at a **recursive** block (`Rich`); it fires where the
substitution it performs is **visible in the result** (`DepPair`, whose second field's type
mentions the first field); and its `hps` premise is **not slack** (`§7`). -/

namespace Rich

/-- `projArgsG_eq_map` at `Rich`: the earlier-projection list really is the list of
generalised projections of the major-premise binder. -/
theorem projArgsG_eq_map_fires :
    richBlock.projArgsG richTy richCtor [] [.bvar 0] [.bvar 1] 0 1
      = (List.range 1).map fun k =>
          richBlock.projTermG richTy richCtor [] [.bvar 0] [.bvar 1] k 0 (.bvar 0) :=
  richBlock.projArgsG_eq_map richTy richCtor [] [.bvar 0] [.bvar 1] 0 1

/-- `projTermG_instAll` at `Rich`, over a two-element spine. -/
theorem projTermG_instAll_fires :
    VExpr.instAll (richBlock.projTermG richTy richCtor [] [.bvar 1] [.bvar 2] 0 0 (.bvar 3))
        [.const `Rich.W [], .const `Rich.V []]
      = richBlock.projTermG richTy richCtor []
          ([(.bvar 1 : VExpr)].map (VExpr.instAll · [.const `Rich.W [], .const `Rich.V []]))
          ([(.bvar 2 : VExpr)].map (VExpr.instAll · [.const `Rich.W [], .const `Rich.V []]))
          0 0 (VExpr.instAll (.bvar 3) [.const `Rich.W [], .const `Rich.V []]) :=
  richBlock.projTermG_instAll richTy richCtor [] richBlock_projClosedG rfl rfl
    (show (0:Nat) < 2 from by omega) rfl rfl

/-- **`projMotiveBodyG_instAll` fired at a recursive block**, at the projected field. -/
theorem projMotiveBodyG_instAll_fires :
    VExpr.instAll
      (VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
        ([(.bvar 0 : VExpr)].map (·.liftN (richTy.indices.length+1))
          ++ richBlock.projArgsG richTy richCtor []
              ([(.bvar 0 : VExpr)].map (·.liftN (richTy.indices.length+1)))
              (VExpr.bvars 1 richTy.indices.length) 0 0))
      ([(.bvar 1 : VExpr)] ++ [.bvar 2])
      = VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
          ([(.bvar 0 : VExpr)] ++ (List.range 0).map fun k =>
            richBlock.projTermG richTy richCtor [] [.bvar 0] [.bvar 1] k 0 (.bvar 2)) :=
  richBlock.projMotiveBodyG_instAll richTy richCtor [] richBlock_projClosedG rfl rfl
    (show (0:Nat) < 2 from by omega) rfl rfl

end Rich

/-! ### A block where the substituted projection is visible in the result

`Rich`'s field types are a parameter and a constant, so at `Rich` the `(List.range i)` block
of `projMotiveBodyG_instAll`'s right-hand side is substituted into a type that does not
mention it.  `DepPair`'s second field type *does*, so the projection appears in the result
and the equation has content. -/

namespace DepPair

def depCtor : VIndCtor where
  name := `DepPair.S.mk
  params := []
  fields :=
    [ { type := .const `DepPair.A [], lvl := .succ .zero, recArg := none },
      { type := .app (.const `DepPair.B []) (.bvar 0), lvl := .succ .zero, recArg := none } ]
  args := []

def depTy : VIndType where
  name := `DepPair.S
  type := .sort (.succ .zero)
  indices := []
  ctors := [depCtor]

def depBlock : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types := [depTy]

/-- The second field's stored type mentions the first field. -/
theorem field1_type : (depCtor.fields.getD 1 default).type = .app (.const `DepPair.B []) (.bvar 0) :=
  rfl

theorem depBlock_projClosedG : depBlock.ProjClosedG where
  params := trivial
  indices := by
    rintro (_ | t) T' hT
    · obtain rfl : depTy = T' := Option.some.inj hT
      exact trivial
    · exact absurd hT (by simp [depBlock])
  fields := by
    rintro (_ | t) T' hT C' hC
    · obtain rfl : depTy = T' := Option.some.inj hT
      obtain rfl : C' = depCtor := List.mem_singleton.1 hC
      exact ⟨trivial, ⟨trivial, Nat.zero_lt_one⟩, trivial⟩
    · exact absurd hT (by simp [depBlock])
  recArgs := by
    rintro (_ | t) T' hT C' hC i r hr
    · obtain rfl : depTy = T' := Option.some.inj hT
      obtain rfl : C' = depCtor := List.mem_singleton.1 hC
      exact absurd hr (by simp [VIndCtor.recFields, depCtor])
    · exact absurd hT (by simp [depBlock])

/-- **`projMotiveBodyG_instAll` fired at the dependent field.** -/
theorem projMotiveBodyG_instAll_fires :
    VExpr.instAll
      (VExpr.instAll ((depCtor.fields.getD 1 default).type.instL [])
        (([] : List VExpr).map (·.liftN (depTy.indices.length+1))
          ++ depBlock.projArgsG depTy depCtor []
              (([] : List VExpr).map (·.liftN (depTy.indices.length+1)))
              (VExpr.bvars 1 depTy.indices.length) 0 1))
      (([] : List VExpr) ++ [.const `DepPair.E []])
      = VExpr.instAll ((depCtor.fields.getD 1 default).type.instL [])
          (([] : List VExpr) ++ (List.range 1).map fun k =>
            depBlock.projTermG depTy depCtor [] [] [] k 0 (.const `DepPair.E [])) :=
  depBlock.projMotiveBodyG_instAll depTy depCtor [] depBlock_projClosedG rfl rfl
    (show (1:Nat) < 2 from by omega) rfl rfl

/-- The right-hand side, computed: field `1`'s type with `.bvar 0` replaced by the
**generalised projection of field 0** out of the major premise. -/
theorem rhs_computed :
    VExpr.instAll ((depCtor.fields.getD 1 default).type.instL [])
        (([] : List VExpr) ++ (List.range 1).map fun k =>
          depBlock.projTermG depTy depCtor [] [] [] k 0 (.const `DepPair.E []))
      = .app (.const `DepPair.B [])
          (depBlock.projTermG depTy depCtor [] [] [] 0 0 (.const `DepPair.E [])) := rfl

/-- **The substitution is visible**: the result is not the stored type.  So
`projMotiveBodyG_instAll` is not an identity here, and the `(List.range i)` block on its
right-hand side is load-bearing rather than an unused spine. -/
theorem rhs_moves :
    VExpr.instAll ((depCtor.fields.getD 1 default).type.instL [])
        (([] : List VExpr) ++ (List.range 1).map fun k =>
          depBlock.projTermG depTy depCtor [] [] [] k 0 (.const `DepPair.E []))
      ≠ (depCtor.fields.getD 1 default).type.instL [] := by
  rw [rhs_computed, show ((depCtor.fields.getD 1 default).type.instL [])
    = .app (.const `DepPair.B []) (.bvar 0) from rfl]
  intro h
  injection h with _ h2
  exact absurd h2 (by rintro ⟨⟩)

end DepPair

/-! ## 7. A third negative control: `hps` in `projMotiveBodyG_instAll` -/

namespace InstControls

open Rich

/-- The two sides of `projMotiveBodyG_instAll` at `Rich` with the parameter spine **empty**
(`ps.length = 0`, but `richBlock.np = 1`): the left collapses to the major premise and the
right to the escaped parameter variable. -/
theorem motiveBody_lhs_without_hps :
    VExpr.instAll
      (VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
        (([] : List VExpr).map (·.liftN (richTy.indices.length+1))
          ++ richBlock.projArgsG richTy richCtor []
              (([] : List VExpr).map (·.liftN (richTy.indices.length+1)))
              (VExpr.bvars 1 richTy.indices.length) 0 0))
      ([(.bvar 1 : VExpr)] ++ [.const `Rich.W []])
      = .const `Rich.W [] := rfl

theorem motiveBody_rhs_without_hps :
    VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
        (([] : List VExpr) ++ (List.range 0).map fun k =>
          richBlock.projTermG richTy richCtor [] [] [.bvar 1] k 0 (.const `Rich.W []))
      = .bvar 0 := rfl

/-- **Negative control 3: `ps.length = D.np` is not slack.**  Drop it and the conclusion of
`projMotiveBodyG_instAll` is false at `Rich`: the stored field type is the parameter
`.bvar 0`, which the left-hand side's shortened `instAll` no longer covers, so the major
premise reaches it.  Not an arity error — both sides are single `VExpr`s at the same block,
constructor, field index and index spine. -/
theorem projMotiveBodyG_instAll_false_without_hps :
    VExpr.instAll
      (VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
        (([] : List VExpr).map (·.liftN (richTy.indices.length+1))
          ++ richBlock.projArgsG richTy richCtor []
              (([] : List VExpr).map (·.liftN (richTy.indices.length+1)))
              (VExpr.bvars 1 richTy.indices.length) 0 0))
      ([(.bvar 1 : VExpr)] ++ [.const `Rich.W []])
      ≠ VExpr.instAll ((richCtor.fields.getD 0 default).type.instL [])
          (([] : List VExpr) ++ (List.range 0).map fun k =>
            richBlock.projTermG richTy richCtor [] [] [.bvar 1] k 0 (.const `Rich.W [])) := by
  rw [motiveBody_lhs_without_hps, motiveBody_rhs_without_hps]
  simp

end InstControls

end Lean4Lean
