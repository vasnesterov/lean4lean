import Lean.Declaration

namespace Lean4Lean
open Lean

/--
Pointer equality is not a safe function, but the kernel uses it anyway for some fast paths.
We cannot use `withPtrEq` because it is not a mere optimization before a true equality test -
the kernel actually has different behavior (will reject some inputs that it would not otherwise)
if identical objects spontaneously get different addresses.

We use this function to try to isolate uses of pointer equality in the kernel,
and type-restrict it to avoid thorny questions about equality of closures or the like.
-/
opaque ptrEqExpr (a b : Expr) : Bool := unsafe ptrAddrUnsafe a == ptrAddrUnsafe b

/-- See `ptrEqExpr`. -/
opaque ptrEqConstantInfo (a b : ConstantInfo) : Bool := unsafe ptrAddrUnsafe a == ptrAddrUnsafe b

/-!
The two axioms `ptrEqExpr_eq` and `ptrEqConstantInfo_eq` — "pointer equality
implies propositional equality" — used to be declared here, next to the opaques
they constrain. They now live in `Lean4Lean/Verify/Axioms.lean`, which imports
this file, so that **every frozen axiom of this project is declared in one
file** and `Verify/Guard.lean`'s check 1 can see them.

That layering matters: the checker itself (`Lean4Lean/EquivManager.lean`) imports
this file for the *functions* and never sees the axioms. See
`docs/axiom-audit.md` §14.
-/
