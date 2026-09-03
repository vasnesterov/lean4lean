import Lean4Lean.Theory.Typing.ShapeVar

/-!
# `SpineVarClosed`: the `ClosedN`-of-`spineHead` step, and the rule-table fact it buys

`docs/handoff-shapevar.md` §8.4/§9.1 names one missing ingredient for the variable-headed
**spine** entry: a `ClosedN`-of-`spineHead` lemma, so that the `extra` case of the
`IsDefEqStrong` induction closes from `VDefEq.WF`'s empty-context typing rather than from head
shape (`IsDeclRule.lhs_shape` permits an `.app` left-hand side, so head shape cannot close it).

This file supplies it.  §1 is the pure `VExpr` fact; §2 cashes it in at the rule table.
-/

namespace Lean4Lean

/-! ## §1 The pure syntactic fact -/

/-- **A closed term has a closed spine head.**  The missing ingredient, and it is three lines:
`spineHead` only ever descends into the *function* part of an `.app`, and `ClosedN` of an `.app`
is `ClosedN` of both parts. -/
theorem VExpr.ClosedN.spineHead {k : Nat} : ∀ {e : VExpr}, e.ClosedN k → e.spineHead.ClosedN k
  | .bvar _, h | .sort _, h | .const .., h | .lam .., h | .forallE .., h => h
  | .app f _, h => VExpr.ClosedN.spineHead (e := f) h.1

/-- **A closed term's spine head is not a variable.**  This is the form the `extra` case wants:
it rules out an `.app`-shaped left-hand side by *scope*, where `IsDeclRule.lhs_shape` cannot. -/
theorem VExpr.spineHead_ne_bvar_of_closed {e : VExpr} {i : Nat} (h : e.ClosedN 0) :
    e.spineHead ≠ .bvar i := by
  intro he
  have := h.spineHead
  rw [he] at this
  exact absurd this (Nat.not_lt_zero i)

/-- The `mkApp` form of the same. -/
theorem VExpr.ne_bvar_mkApp_of_closed {e : VExpr} {i : Nat} {as : List VExpr}
    (h : e.ClosedN 0) : e ≠ (VExpr.bvar i).mkApp as := by
  intro he
  refine VExpr.spineHead_ne_bvar_of_closed (i := i) h ?_
  rw [he, VExpr.spineHead_mkApp]; rfl

/-! ## §2 The rule-table fact: no rule rewrites a variable-headed **spine**

`WF.instL_lhs_ne_bvar` (`ShapeVar.lean` §4) says no rule rewrites a bare variable, and it comes
from `lhs_shape` alone.  The spine version cannot: `lhs_shape` explicitly allows
`df.lhs = .app f a`.  What closes it is that a rule's two sides are typed in the **empty**
context (`VDefEq.WF`), hence closed, hence have closed spine heads — §1.

Both sides, not just the left: `df.rhs` is typed in the empty context too, so the analogue holds
for it, and that is a small strengthening over `instL_lhs_ne_bvar`'s one-sidedness. -/

namespace VEnv

variable {env : VEnv} {df : VDefEq}

/-- A rule's left-hand side is closed. -/
theorem WF.defeq_lhs_closed (henv : env.WF) (h : env.defeqs df) : df.lhs.ClosedN 0 :=
  (henv.ordered.defEqWF h).1.closedN henv.ordered trivial

/-- A rule's right-hand side is closed. -/
theorem WF.defeq_rhs_closed (henv : env.WF) (h : env.defeqs df) : df.rhs.ClosedN 0 :=
  (henv.ordered.defEqWF h).2.closedN henv.ordered trivial

/-- **No rule rewrites a variable-headed spine.**  The `extra` ingredient the spine entry needs,
and the one thing `docs/handoff-shapevar.md` §8.4 measured as absent from the tree. -/
theorem WF.instL_lhs_spineHead_ne_bvar (henv : env.WF) (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) : (df.lhs.instL ls).spineHead ≠ .bvar i :=
  VExpr.spineHead_ne_bvar_of_closed (henv.defeq_lhs_closed h).instL

/-- …and neither is a rule's right-hand side a variable-headed spine.  `instL_lhs_ne_bvar` has
no right-hand sibling because it did not need one; this one has. -/
theorem WF.instL_rhs_spineHead_ne_bvar (henv : env.WF) (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) : (df.rhs.instL ls).spineHead ≠ .bvar i :=
  VExpr.spineHead_ne_bvar_of_closed (henv.defeq_rhs_closed h).instL

/-- The `mkApp` forms, for consumers phrased over an explicit spine. -/
theorem WF.instL_lhs_ne_bvar_mkApp (henv : env.WF) (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) (as : List VExpr) :
    df.lhs.instL ls ≠ (VExpr.bvar i).mkApp as :=
  VExpr.ne_bvar_mkApp_of_closed (henv.defeq_lhs_closed h).instL

@[inherit_doc WF.instL_lhs_ne_bvar_mkApp]
theorem WF.instL_rhs_ne_bvar_mkApp (henv : env.WF) (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) (as : List VExpr) :
    df.rhs.instL ls ≠ (VExpr.bvar i).mkApp as :=
  VExpr.ne_bvar_mkApp_of_closed (henv.defeq_rhs_closed h).instL

/-- **Regression: §1 subsumes `ShapeVar.lean` §4.**  The bare-variable case is `as = []`, so the
new lemma re-proves `WF.instL_lhs_ne_bvar` — by a different route (scope, not head shape).  Both
routes are kept: the shape route is cheaper and has no `VDefEq.WF` detour. -/
theorem WF.instL_lhs_ne_bvar' (henv : env.WF) (h : env.defeqs df) (ls : List VLevel) (i : Nat) :
    df.lhs.instL ls ≠ .bvar i := henv.instL_lhs_ne_bvar_mkApp h ls i []

end VEnv

section Audit
#print axioms Lean4Lean.VExpr.ClosedN.spineHead
#print axioms Lean4Lean.VExpr.spineHead_ne_bvar_of_closed
#print axioms Lean4Lean.VExpr.ne_bvar_mkApp_of_closed
#print axioms Lean4Lean.VEnv.WF.defeq_lhs_closed
#print axioms Lean4Lean.VEnv.WF.instL_lhs_spineHead_ne_bvar
#print axioms Lean4Lean.VEnv.WF.instL_rhs_spineHead_ne_bvar
#print axioms Lean4Lean.VEnv.WF.instL_lhs_ne_bvar'
end Audit

end Lean4Lean
