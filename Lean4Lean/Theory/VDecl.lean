import Lean4Lean.Theory.Inductive.Decl

namespace Lean4Lean

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

/-- A declaration step of the abstract theory.

`induct` carries `VInductDecl'` (`Lean4Lean/Theory/Inductive/Decl.lean`), the *structured*
inductive declaration that keeps the parameter/index/field telescopes explicitly. The
earlier flat `VInductDecl`, which stored only the closed types of the block, could not work:
the kernel `whnf`s at every step of an inductive's pi-spine, so the telescopes the recursor
is built from are not recoverable from the stored types, and no `addInduct` could be written
against it. -/
inductive VDecl where
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl')
  | mutualDef (_ : List VDefVal)
