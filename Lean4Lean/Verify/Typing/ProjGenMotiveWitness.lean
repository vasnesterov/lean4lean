import Lean4Lean.Verify.Typing.ProjGenMotive
import Lean4Lean.Verify.Typing.ProjGenMinorWitness
import Lean4Lean.Verify.Typing.ProjClosedGWitness

/-!
# Non-vacuity for the generalised motive

`ProjGenMotive.lean` and `ProjGenSwap.lean` generalise the motive half of
`projMinor_hasType`'s chain along the **block index** `j`.  Two things have to be checked, and
they are different checks:

* that the generalisation *meets* the narrow theorem — done in `ProjGenSwapNarrow.lean`, by
  re-deriving `projMotiveTerm_hasType_swapped` and `projMotiveBody_hasType_guarded` verbatim;
* that `j` is **not a passenger** — that the generalised statements actually say something
  different at `j ≠ 0`.  A `j`-independent "generalisation" would pass every collapse test
  and every arity check, and would then be a statement about the *wrong motive slot*.  That
  is this file.

`RecDep` (`ProjGenMinorWitness.lean`) is the block: two types, the projected one at index
`j = 1`, three fields with the middle one dependent, and a recursive last field.  Its other
member is named `RA` and the projected one `RP`, so a term that reads the wrong motive slot
is visibly a different term.

## The negative controls, each re-run outside the tree and its error text recorded

1. **The `j = 0` reading of the block's type at motive slot 1.**
   `declRP.types.getD 1 default = declRP.types.getD 0 default` — rejected,
   *"Type mismatch: rfl has type ?m = ?m but is expected to have type
   declRP.types.getD 1 default = declRP.types.getD 0 default"*.  Not an arity error: both
   sides are `VIndType`s of the same block.
2. **The motive prefix is exactly saturated.**  `motiveTypeG_at_recdep`'s first conjunct with
   `ms := []` instead of `[m0]` — rejected at `hms`,
   *"the argument rfl … is expected to have type `[].length = 1`"*.  So the `j` earlier
   motives are load-bearing in the conclusion's type, not decoration.
3. **The narrow collapse is unavailable here.**  `projMotiveTermG_eq_projMotiveTerm` at
   `declRP`/`treal`/`rpmk` — rejected at `hrec`,
   *"the argument rfl … is expected to have type `rpmk.recFields = []`"* (the elaborator
   reaches `hrec` before `htypes`; `declRP.types = [treal]` is false too).
4. **The field index is exactly saturated.**  `3 < rpmk.fields.length` is *proved false* by
   `decide`, so the firings below at `i = 1` are at the largest index the dependent field
   occupies and `i = 3 = nf` is out of range.

None of the four is an arity error.
-/

namespace Lean4Lean

namespace RecDep

open VExpr

/-! ## The motive block reads slot `j` -/

/-- The padding motive at the block's *other* member, computed. -/
theorem padMotive_at_recdep_0 (X : VExpr) :
    declRP.padMotive (declRP.types.getD 0 default) [] [] X
      = .lam (.const `Lean4Lean.RecDep.RA []) (.forallE (X.liftN 1) (X.liftN 2)) := rfl

/-- The real motive at the projected member, computed. -/
theorem projMotive_at_recdep :
    treal.projMotive rpmk [] [] [] 0 []
      = .lam (.const `Lean4Lean.RecDep.RP []) (.const `Lean4Lean.RecDep.Q []) := rfl

/-- The motive block, both slots, at either reading of `j`. -/
theorem padMotives_at_recdep (j : Nat) (X : VExpr) :
    declRP.padMotives treal rpmk [] [] [] 0 j [] X
      = [(if 0 = j then treal.projMotive rpmk [] [] [] 0 []
          else declRP.padMotive (declRP.types.getD 0 default) [] []
            ((treal.projMotive rpmk [] [] [] 0 []).mkApp ([] ++ [X]))),
         (if 1 = j then treal.projMotive rpmk [] [] [] 0 []
          else declRP.padMotive (declRP.types.getD 1 default) [] []
            ((treal.projMotive rpmk [] [] [] 0 []).mkApp ([] ++ [X])))] := rfl

theorem ctorsAll_at_recdep : declRP.ctorsAll = [(0, ramk), (1, rpmk)] := rfl

/-- **Slot 0 of the motive block moves with `j`**: at `j = 1` it is the `RA` padding motive,
at `j = 0` the real `RP` motive. -/
theorem padMotives_j_moves :
    (declRP.padMotives treal rpmk [] [] [] 0 1 [] (.bvar 0))[0]?
      ≠ (declRP.padMotives treal rpmk [] [] [] 0 0 [] (.bvar 0))[0]? := by
  rw [declRP.padMotives_getElem_ne treal rpmk [] [] [] 0 1 [] (.bvar 0) (by decide) (by decide),
    declRP.padMotives_getElem_eq treal rpmk [] [] [] 0 0 [] (.bvar 0) (by decide),
    padMotive_at_recdep_0, projMotive_at_recdep]
  simp

set_option linter.unusedSimpArgs false in
/-- …and therefore so does the whole recursor application. -/
theorem projCoreG_j_moves :
    declRP.projCoreG treal rpmk [] [] [] 0 1 [] (.bvar 0)
      ≠ declRP.projCoreG treal rpmk [] [] [] 0 0 [] (.bvar 0) := by
  simp only [VInductDecl'.projCoreG, padMotives_at_recdep, VExpr.mkApp,
    padMotive_at_recdep_0, projMotive_at_recdep,
    VInductDecl'.padMinors, VInductDecl'.padMinorsAux, ctorsAll_at_recdep,
    List.cons_append, List.nil_append, List.append_nil,
    ne_eq, VExpr.app.injEq, VExpr.lam.injEq, VExpr.const.injEq,
    if_pos, if_neg, reduceIte, Nat.reduceEqDiff]
  simp

/-! ## The generalised motive term itself -/

/-- **`projMotiveTermG` at `RecDep`, computed.**  Three fields, the middle one dependent, so
the motive's body is `Bd` applied to the *earlier projection* — which is where `j` enters.
The `liftN 0` is not cosmetic: `VExpr.instVar 0 e 0 = e.liftN 0`, and `liftN 0` on a term
that is not a literal does not reduce, which is why the computed form carries it. -/
theorem projMotiveTermG_at_recdep (j : Nat) :
    projMotiveTermG declRP treal rpmk [] [] 1 j
      = .lam (.const `Lean4Lean.RecDep.RP [])
          (.app (.const `Lean4Lean.RecDep.Bd [])
            (VExpr.liftN 0 (declRP.projCoreG treal rpmk [] [] [] 0 j [] (.bvar 0)))) := rfl

/-- **The move test: `j` is not a passenger in `projMotiveTermG`.** -/
theorem projMotiveTermG_j_moves :
    projMotiveTermG declRP treal rpmk [] [] 1 1
      ≠ projMotiveTermG declRP treal rpmk [] [] 1 0 := by
  rw [projMotiveTermG_at_recdep, projMotiveTermG_at_recdep, VExpr.liftN_zero, VExpr.liftN_zero]
  simp only [ne_eq, VExpr.lam.injEq, VExpr.app.injEq, true_and]
  exact projCoreG_j_moves

/-- **Negative control: at `i = 0` the block index is invisible**, because `projArgsG … 0` is
empty.  So the move test above has to be at `i ≥ 1`, and a firing at field `0` would have
tested nothing — which is exactly the degeneracy this file exists to avoid. -/
theorem projMotiveTermG_j_invisible_at_0 (j j' : Nat) :
    projMotiveTermG declRP treal rpmk [] [] 0 j
      = projMotiveTermG declRP treal rpmk [] [] 0 j' := rfl

/-! ## The conclusion's *type* reads slot `j` too

This is the half the collapse test cannot see.  `projMotiveTermG_hasType_swapped` concludes
at `VExpr.instAll ((D.motiveType j).instL lvls) (ps ++ ms)`; if that `j` were a `0`, the
lemma would type the generalised motive against the *wrong* recursor binder and would still
collapse correctly at `j = 0`. -/

/-- The declared type of motive `1` names `RP`; the declared type of motive `0` names `RA`.
Both computed through `motiveType_instL_instAll_gen`, i.e. through the lemma the typing
proof actually uses. -/
theorem motiveTypeG_at_recdep (m0 : VExpr) (i : Nat) :
    VExpr.instAll ((declRP.motiveType 1).instL (declRP.projLvls rpmk [] i)) ([] ++ [m0])
        = .forallE (.const `Lean4Lean.RecDep.RP [])
            (.sort (declRP.elimLvl.inst (declRP.projLvls rpmk [] i))) ∧
    VExpr.instAll ((declRP.motiveType 0).instL (declRP.projLvls rpmk [] i))
          ([] ++ ([] : List VExpr))
        = .forallE (.const `Lean4Lean.RecDep.RA [])
            (.sort (declRP.elimLvl.inst (declRP.projLvls rpmk [] i))) :=
  ⟨motiveType_instL_instAll_gen declRP treal rpmk rfl rfl rfl rfl,
   motiveType_instL_instAll_gen declRP _ rpmk rfl rfl rfl rfl⟩

/-- …so the two are different types. -/
theorem motiveTypeG_j_moves (m0 : VExpr) (i : Nat) :
    VExpr.instAll ((declRP.motiveType 1).instL (declRP.projLvls rpmk [] i)) ([] ++ [m0])
      ≠ VExpr.instAll ((declRP.motiveType 0).instL (declRP.projLvls rpmk [] i))
          ([] ++ ([] : List VExpr)) := by
  rw [(motiveTypeG_at_recdep m0 i).1, (motiveTypeG_at_recdep m0 i).2]
  simp

end RecDep

/-! ## The `liftN` commutation, fired where the lift moves something

`RecDep` has `np = 0`, so `projMotiveG_liftN` is vacuous there — the parameter spine is
empty and both sides are the same term.  `Rich` (`ProjClosedGWitness.lean`) has one
parameter, one index and a *proved* `ProjClosedG`, so the lemma can be fired with a spine
the lift actually reaches. -/

namespace Rich

open VExpr

/-- `projMotiveG_liftN` at `Rich`, field `0`, with a one-entry parameter spine. -/
theorem projMotiveG_liftN_fires (us : List VLevel) (p : VExpr) (n : Nat) :
    (projMotiveTermG richBlock richTy richCtor us [p] 0 0).liftN n
      = projMotiveTermG richBlock richTy richCtor us [(p.liftN n)] 0 0 :=
  projMotiveG_liftN richBlock richTy richCtor us richBlock_projClosedG rfl rfl
    (by decide) rfl

/-- …and the spine really moves, so the two sides of the firing above are stated at
different parameter spines: the lemma is not `x = x`. -/
theorem projMotiveG_liftN_moves : (VExpr.bvar 0).liftN 1 = VExpr.bvar 1 := rfl

end Rich

end Lean4Lean
