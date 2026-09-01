import Lean4Lean.Verify.Typing.ProjGenBlock
import Lean4Lean.Verify.Typing.ProjGenMinorWitness

/-!
# Non-vacuity for the minor block's two readings

`padMinors_getElem_eq`/`_ne` (`ProjGenBlock.lean`) read `projCoreG`'s minor block at a slot.
The narrow collapse test in `ProjGenBlock.lean` (`padMinors_narrow_of_getElem`) fires only the
`_eq` reading, at `q = 0`, where the accumulator is `[]` — so it cannot see either a wrong
branch or a wrong accumulator.  This file fires both readings at `RecDep`
(`ProjGenMinorWitness.lean`): **two** types, the projected one at `j = 1`, so

* slot 0 is a constructor of the *other* member (`t = 0 ≠ 1`) and must be the **padding**
  minor — the `_ne` reading, which has no other firing in the tree;
* slot 1 is the projected member's constructor and must be the **real** minor, at a
  **non-empty** accumulator `[padMinor … 0 ramk]` — which is the arithmetic
  `padMinorsAux_getElem` exists for, and the one a narrow block cannot exercise.

`padMinors_at_recdep` computes the block by `rfl`, independently of either lemma; the two
firings then have to agree with it.
-/

namespace Lean4Lean

namespace RecDep

open VExpr

/-- The minor block at `RecDep`, projected member `j = 1`, field `i = 1`, computed. -/
theorem padMinors_at_recdep (lvls : List VLevel) (mots : List VExpr) (X : VExpr) :
    declRP.padMinors lvls [] mots X 1 1
      = [declRP.padMinor lvls ([] ++ mots ++ []) X 0 ramk,
         declRP.realMinor lvls
           ([] ++ mots ++ [declRP.padMinor lvls ([] ++ mots ++ []) X 0 ramk]) 1 1 rpmk] :=
  rfl

/-- **`padMinors_getElem_ne` fires**, at the block member that is not the projected one. -/
theorem padMinors_getElem_ne_at_recdep (lvls : List VLevel) (mots : List VExpr) (X : VExpr) :
    (declRP.padMinors lvls [] mots X 1 1)[0]?
      = some (declRP.padMinor lvls ([] ++ mots ++ []) X 0 ramk) := by
  rw [declRP.padMinors_getElem_ne lvls [] mots X 1 1 0 0 ramk rfl (by decide)]
  rfl

/-- **`padMinors_getElem_eq` fires at a non-empty accumulator**: minor 1 is the real minor at
the spine the *padding* minor 0 extends.  This is `iota_law_gen`'s `hminor` at a member of a
mutual block, which is the case the narrow route has no statement for. -/
theorem padMinors_getElem_eq_at_recdep (lvls : List VLevel) (mots : List VExpr) (X : VExpr) :
    (declRP.padMinors lvls [] mots X 1 1)[1]?
      = some (declRP.realMinor lvls
          ([] ++ mots ++ [declRP.padMinor lvls ([] ++ mots ++ []) X 0 ramk]) 1 1 rpmk) := by
  rw [declRP.padMinors_getElem_eq (C := rpmk) lvls [] mots X 1 1 1 rfl]
  rfl

/-! ## What is *not* claimed here

An "accumulator is not a passenger" lemma — `(padMinors …)[1]? ≠ some (realMinor … at the
empty accumulator)` — would need the two `realMinor` terms to differ, and at `RecDep` that is
an **unproved negative**: `realMinor`'s spine reaches the field telescope through
`instAllTele`, and whether the extra entry is read depends on the constructor's field types.
`docs/vacuity-ledger.md` §0's fourth overstatement is exactly asserting such a thing without a
proof, so it is not asserted.

What *is* checked, and is enough: `padMinors_at_recdep` computes the block by `rfl` — no
appeal to either reading — and the two firings above agree with it **at a non-empty
accumulator**.  A version of `padMinorsAux_getElem` that dropped the `acc.length` offset would
name a different list in its conclusion and could not meet that. -/

end RecDep

end Lean4Lean
