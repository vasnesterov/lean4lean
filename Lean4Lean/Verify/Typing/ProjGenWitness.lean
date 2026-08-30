import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.Typing.ProjGen

/-!
# The refutation, re-run against the generalisation

`MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) is the machine-checked
refutation of weakening `VEnv.IsStructure.types` from `D.types = [T]` to `T ∈ D.types`: at
`MutNonRec.decl2` — a two-type, non-recursive block, the abstract image of a block Lean's own
kernel accepts `.proj` on and performs structure eta at — `projCore`'s argument spine has
**3** entries between the head and the end while `recType` demands `recArity = 5`.

A repair that does not visibly kill its own witness has not been shown to work.  This file
fires the same measurement at `projCoreG` (`Verify/Typing/ProjGen.lean`), **at `decl2`
itself**, and the mismatch is gone: the spine has 5 entries, `recArity` is 5, and the
`nm + nmin = 2` side condition that `recArity_eq_projCore_iff` makes the whole thing turn on
is *not* needed — `decl2` fails it (`¬ decl2.nm + decl2.nmin = 2` is one of
`projCore_arity_wrong`'s own conjuncts) and the generalised spine saturates anyway.
-/

set_option maxHeartbeats 2000000

namespace Lean4Lean
namespace MutNonRec

open VExpr

/-- **The generalised spine saturates the recursor at the refutation's own witness.**

Read against `projCore_arity_wrong`'s conjuncts: there, spine length `3` against
`recArity = 5`, with `¬ decl2.nm + decl2.nmin = 2`.  Here, spine length `5` against
`recArity = 5`, with the same block and the same `nm`/`nmin`. -/
theorem projCoreG_arity_right (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    -- the motive block is full length…
    (decl2.padMotives T C us [] [] i j earlier e).length = 2 ∧
    -- …and so is the minor block…
    (decl2.padMinors (decl2.projLvls C us i) []
      (decl2.padMotives T C us [] [] i j earlier e)
      ((T.projMotive C us [] [] i earlier).mkApp ([] ++ [e])) i j).length = 2 ∧
    -- …so the spine `projCoreG` hands the recursor has five entries…
    (([] : List VExpr) ++ decl2.padMotives T C us [] [] i j earlier e ++
      decl2.padMinors (decl2.projLvls C us i) []
        (decl2.padMotives T C us [] [] i j earlier e)
        ((T.projMotive C us [] [] i earlier).mkApp ([] ++ [e])) i j ++ [] ++ [e]).length = 5 ∧
    -- …which is exactly what the recursor binds.
    decl2.recArity (decl2.types.getD 0 default) = 5 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact (VInductDecl'.length_padMotives ..).trans rfl
  · exact (VInductDecl'.length_padMinors ..).trans rfl
  · exact (VInductDecl'.length_projCoreG_spine decl2 T C us rfl).trans rfl

/-- …and the identity holds at `decl2` for the same reason it holds anywhere: no
`nm + nmin = 2` side condition is involved.  `decl2` **fails** that side condition, which is
what made the weakening false. -/
theorem projCoreG_arity_right' (C : VIndCtor) (us : List VLevel)
    (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    (([] : List VExpr) ++
        decl2.padMotives (decl2.types.getD 0 default) C us [] [] i j earlier e ++
      decl2.padMinors (decl2.projLvls C us i) []
        (decl2.padMotives (decl2.types.getD 0 default) C us [] [] i j earlier e)
        (((decl2.types.getD 0 default).projMotive C us [] [] i earlier).mkApp ([] ++ [e]))
        i j ++ [] ++ [e]).length
      = decl2.recArity (decl2.types.getD 0 default) ∧
    ¬ decl2.nm + decl2.nmin = 2 :=
  ⟨VInductDecl'.recArity_eq_projCoreG decl2 (decl2.types.getD 0 default) C us rfl rfl,
    by decide⟩

end MutNonRec
end Lean4Lean
