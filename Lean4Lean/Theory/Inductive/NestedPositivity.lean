import Lean4Lean.Theory.Inductive.NestedBuild

/-!
# Nested positivity: the reduction, and a rejection witness

**Layering.**  The *executable* half of this development -- actually running
`Lean4Lean.addDecl` on the declaration that must be refused -- lives in
`Lean4Lean/Tests/NestedInductive.lean`, not here.  `Theory/` is the abstract specification the
implementation is refined *against*, so it must not import the implementation: otherwise a
defect in the checker could in principle make a `Theory/` statement vacuous, which is the exact
failure mode this file exists to rule out.  The abstract content below stands on its own; the
run is the empirical control for it.

`docs/handoff-nested-restore.md` §5's second open item, verbatim:

> **Positivity for a nested head.**  Read off `Add.lean`, *not* machine-checked: the nested
> positivity question reduces to the auxiliary block's *ordinary* `checkPositivity`. …
> **The rejection direction has no witness** — building one needs
> `¬ ∃ A, NoBlock A ∧ IsDefEqType …`, i.e. defeq reasoning, so it was not attempted.

This file closes the *rejection* half at the level where it can be closed, and says exactly
what is left.

## Three levels, one declaration

`inductive BadNest | mk : Neg BadNest → BadNest`, where `Neg (α : Type) : Type` has the single
field `α → False`.  `Neg` is a perfectly good inductive — a parameter may occur negatively —
but nesting it puts `BadNest` in that negative position.

1. **Lean's own kernel rejects it**, and its message names the *auxiliary* constructor:
   `arg #1 of '_nested.…Neg_1.mk' has a non positive occurrence of the datatypes being
   declared`.  So the reduction is not a reading of `Add.lean`; it is what the kernel says.
2. **This development rejects it**, by the same message, from a hand-built `Declaration` that
   never touches the elaborator (`bad_rejected` / `ok_accepted` below).  That is the
   machine-checked negative the handoff asks for.
3. **The abstract construction produces exactly the field the kernel refuses.**
   `VNestedOcc.ctor` applied to `Neg`'s constructor and the instantiation `[BadNest]` yields
   the stored field type `BadNest → False` (`badAuxMk_field_type`), on which
   `VIndRestore.recog` returns `none` (`badAuxMk_recog_none`) and which is not block-free
   (`badAuxMk_field_not_noBlock`).

## What is still open, stated exactly

`VIndField.WF.pos`'s `none` branch asks for `∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ
F.type A` — *definitional* block-freeness, deliberately (`Decl.lean`'s
`(fun _ : T => Nat) r` example).  Items 1–3 close every **syntactic** route to satisfying it:
the `some` branch is unavailable because the recogniser fails, and the obvious `none`-branch
witness `A := F.type` is unavailable because `F.type` mentions a block constant.  What is not
closed is that *no other* `A` works, i.e. `badAux_pos_open` below.  That is an injectivity /
whnf-inversion statement about the staged environment, and it is downstream of
`IsDefEqU.forallE_inv` exactly as `VIndRecArg.exists_indep` is.

The honest summary: **the reduction is machine-checked at the implementation, the rejection is
machine-checked at the implementation, and at the abstract level everything but one defeq
non-existence is machine-checked.**
-/

namespace Lean4Lean
namespace InductiveDeclExamples

open VExpr (mkPi)

/-! ## Part 1: the history block

`Neg` is accepted: a *parameter* may occur negatively.  It is the nesting that is bad. -/

inductive Neg (α : Type) : Type where
  | mk : (α → False) → Neg α

/-- A strictly positive companion, for the accept control. -/
inductive Wrap (α : Type) : Type where
  | mk : α → Wrap α

def negMk : VIndCtor where
  name := ``Neg.mk
  params := [.sort (.succ .zero)]
  fields := [{ type := .forallE (.bvar 0) (.const ``False []),
               lvl := .imax (.succ .zero) .zero, recArg := none }]
  args := []

def negType : VIndType where
  name := ``Neg
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  indices := []
  ctors := [negMk]

def negDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types := [negType]

example : negType.type = (vconst(type_of% @Neg)).type := rfl
example : negMk.type negDecl 0 = (vconst(type_of% @Neg.mk)).type := rfl

/-! ## Part 2: the abstract construction, at the declaration that must be refused

`BadNest` is not a Lean constant — it cannot be, that is the point — so it appears here as a
bare `Name`.  The auxiliary block's *header* is all the construction needs. -/

def badHeader : VIndHeader where
  uvars := 0
  params := []
  nm := 2
  names j := if j = 1 then `_nested.Neg_1 else `BadNest

def badRestore : VIndRestore where
  tyName j := if j = 1 then ``Neg else `BadNest
  tyLvls _ := []
  tyArgs j := if j = 1 then [.const `BadNest []] else []
  ctorName n := if n = `_nested.Neg_1.mk then ``Neg.mk else n
  recName n := if n = `_nested.Neg_1.rec then `BadNest.rec_1 else n

def negOcc : VNestedOcc where
  decl := negDecl
  idx := 0
  lvls := []
  args := [.const `BadNest []]
  auxName := `_nested.Neg_1
  ctorName n := if n = ``Neg.mk then `_nested.Neg_1.mk else n

/-- **The auxiliary constructor the construction produces**, `_nested.Neg_1.mk`. -/
def badAuxMk : VIndCtor := negOcc.ctor badHeader badRestore negMk

/-- Its one field is `BadNest → False` — the block constant in a negative position.  This is
the field Lean's kernel names in its rejection message. -/
theorem badAuxMk_field_type :
    (badAuxMk.fields.getD 0 default).type
      = .forallE (.const `BadNest []) (.const ``False []) := rfl

/-- **The recogniser refuses it.**  `BadNest → False` is not `∀ ξ, I params π` for any member
of the block, so no `VIndRecArg` is produced and `VIndField.WF.pos`'s `some` branch is
unavailable. -/
theorem badAuxMk_recog_none :
    badRestore.recog badHeader.nm 0
        (VExpr.instAll ((negMk.fields.getD 0 default).type.instL negOcc.lvls) negOcc.args 0)
      = none := rfl

theorem badAuxMk_field_recArg_none : (badAuxMk.fields.getD 0 default).recArg = none := rfl

/-- The block's constants, as `VInductDecl'.blockNames` would compute them. -/
def badBlockNames : List Lean.Name := [`BadNest, `_nested.Neg_1]

/-- **…and the obvious `none`-branch witness is unavailable too**: the stored field type is
not block-free, so `A := F.type` does not discharge `pos`. -/
theorem badAuxMk_field_not_noBlock :
    ¬ VExpr.NoConsts badBlockNames (badAuxMk.fields.getD 0 default).type := by
  rintro ⟨h, -⟩; exact h (by decide)

/-- **What is left open**, named.  Every *syntactic* route to `VIndField.WF.pos` is closed
above; this is the defeq non-existence that would close the last one, and it is the same
`IsDefEqU.forallE_inv`-shaped statement `VIndRecArg.exists_indep` records. -/
def badAux_pos_open (env : VEnv) (Γ : List VExpr) : Prop :=
  ¬ ∃ A, VExpr.NoConsts badBlockNames A ∧
    env.IsDefEqType 0 Γ (badAuxMk.fields.getD 0 default).type A

/-! ### The accept control, through the same construction

`Wrap` nested at `OkNest` is strictly positive, and there the recogniser *does* fire — so the
`none` above is a discrimination, not a failure of the recogniser to ever succeed. -/

def wrapMk : VIndCtor where
  name := ``Wrap.mk
  params := [.sort (.succ .zero)]
  fields := [{ type := .bvar 0, lvl := .succ .zero, recArg := none }]
  args := []

def wrapType : VIndType where
  name := ``Wrap
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  indices := []
  ctors := [wrapMk]

def wrapDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types := [wrapType]

example : wrapType.type = (vconst(type_of% @Wrap)).type := rfl
example : wrapMk.type wrapDecl 0 = (vconst(type_of% @Wrap.mk)).type := rfl

def okHeader : VIndHeader where
  uvars := 0
  params := []
  nm := 2
  names j := if j = 1 then `_nested.Wrap_1 else `OkNest

def okRestore : VIndRestore where
  tyName j := if j = 1 then ``Wrap else `OkNest
  tyLvls _ := []
  tyArgs j := if j = 1 then [.const `OkNest []] else []
  ctorName n := if n = `_nested.Wrap_1.mk then ``Wrap.mk else n
  recName n := if n = `_nested.Wrap_1.rec then `OkNest.rec_1 else n

def wrapOcc : VNestedOcc where
  decl := wrapDecl
  idx := 0
  lvls := []
  args := [.const `OkNest []]
  auxName := `_nested.Wrap_1
  ctorName n := if n = ``Wrap.mk then `_nested.Wrap_1.mk else n

def okAuxMk : VIndCtor := wrapOcc.ctor okHeader okRestore wrapMk

/-- The good nesting *is* recognised, as a recursive position into member 0. -/
theorem okAuxMk_field_recArg :
    (okAuxMk.fields.getD 0 default).recArg = some { binders := [], idx := 0, args := [] } := rfl

/-- …and its stored type is the block-headed canonical form. -/
theorem okAuxMk_field_type :
    (okAuxMk.fields.getD 0 default).type = .const `OkNest [] := rfl

end InductiveDeclExamples
end Lean4Lean
