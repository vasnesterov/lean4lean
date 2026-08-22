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
against it.

`unsafeDef` is the **impure** step, and the only one: it models a kernel
`mutualDefnDecl` block, which both the C++ kernel and `Lean4Lean.addMutual`
accept *only* when tagged `partial` or `unsafe`. Its members are typechecked in
the environment that already carries the block's own constants, so
`def f : (∀ p : Prop, p) := f` is a well-formed step (see
`Theory/MutualDefUnsound.lean`) and any environment containing one is
inconsistent. That is faithful — Lean's `partial`/`unsafe` constants really do
inhabit any type — and it is why `VDecl.isPure` is `False` here and why
`TrEnv'.unsafeDef` (`Verify/Environment/Basic.lean`) is gated on at least one
member carrying a non-`safe` `DefinitionSafety` tag, which makes the rule
unfireable at `safety := .safe`. The safe fragment therefore never sees it. -/
inductive VDecl where
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl')
  | unsafeDef (_ : List VDefVal)
