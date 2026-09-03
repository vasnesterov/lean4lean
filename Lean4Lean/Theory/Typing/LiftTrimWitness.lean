import Lean4Lean.Theory.Typing.StrengthenAxiom
import Lean4Lean.Theory.Typing.ConstSubstNested
import Lean4Lean.Theory.Inductive.NestedHead

/-!
# Witnesses for two trimmed hypotheses

`lake build` has been reporting a class of warnings — "automatically included section
variable(s) unused in theorem" — in every build of this repo.  On 2026-09-03 there were
**20** of them, one in the `Foundation` dependency and 19 in `Lean4Lean/`.  Two are now gone,
and this file is the part of that work that is not bookkeeping: **the trimmed statements are
instantiated at environments where the removed hypothesis is refuted**, so the trim really did
enlarge the set of instances rather than restate the same lemma.

A note on why the class was invisible in source.  `Lean4Lean/Std/VariableBang.lean` expands

    variable! (henv : Ordered env) in thm    ↦    variable (henv : Ordered env) in
                                                 include henv in thm

and it was believed that the explicit `include` **suppresses** the linter.  It does not:
`Ctx.LiftN.exists_instN_typed` was reported under exactly that expansion.  The warnings were
readable from `lake build` all along.

## Contents

* §1 `badEnv`, and the refutation of `VEnv.Ordered` at it.
* §2 `Ctx.LiftN.exists_instN_typed` (`Theory/Typing/StrengthenAxiom.lean`) at `badEnv` — the
  `henv : Ordered env` it used to carry has **no instance** there.
* §3 `InductiveDeclExamples.ntreeAux_WF'` (`Theory/Inductive/NestedHead.lean`) at `badEnv` —
  the `h : VEnv.empty.addInduct' listDecl = some env₁` it used to carry has **no instance**
  there either, and `VInductDecl'.WF badEnv` is not a vacuously true predicate.

Nothing here is a `sorry`, and nothing here closes a census hole; the census is unchanged at
13 by this file's landing.
-/

namespace Lean4Lean
open Lean (Name)

/-! ## 1. An environment that is not `Ordered`

`VEnv.Ordered` is built by `Ordered.const`, which requires `ci.WF env` — in particular that a
declared constant's type is *typeable*, hence closed (`Ordered.closedC`).  So one junk
constant, whose type is a loose `bvar`, puts an environment outside `Ordered` for good. -/

/-- One constant, `bad : #0` — a type with a loose de Bruijn variable. -/
def badEnv : VEnv where
  constants n := if n = `bad then some ⟨0, .bvar 0⟩ else none
  defeqs _ := False

theorem badEnv_bad : badEnv.constants `bad = some ⟨0, .bvar 0⟩ := rfl

/-- **`badEnv` is not `Ordered`.**  `Ordered.closedC` would give `VExpr.ClosedN (.bvar 0) 0`,
which unfolds to `0 < 0`. -/
theorem not_ordered_badEnv : ¬ badEnv.Ordered :=
  fun H => Nat.not_lt_zero 0 (H.closedC badEnv_bad)

/-- `badEnv` still admits well-formed contexts: `Sort 0` is a type at every environment,
because the `sort` rule of `IsDefEq` consults no constant. -/
theorem badEnv_onCtx : OnCtx [(.sort .zero : VExpr)] (badEnv.IsType 0) :=
  ⟨trivial, _, by type_tac⟩

/-! ## 2. `exists_instN_typed` where `Ordered env` is refuted

Before the trim the statement was

    (henv : Ordered env) → Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) → ∃ Γ₀ A₀, …

and at `env := badEnv` its first argument cannot be supplied at all (§1).  The trimmed form
applies, and delivers the existential with its witnesses on the nose: stripping the single
entry `Sort 0` from `[Sort 0]` leaves the empty context and hands back `Sort 0` itself. -/

theorem exists_instN_typed_badEnv :
    ∃ Γ₀ A₀, (∀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 [(.sort .zero : VExpr)] []) ∧
      OnCtx Γ₀ (badEnv.IsType 0) ∧ badEnv.IsType 0 Γ₀ A₀ :=
  Ctx.LiftN.exists_instN_typed (Γ := []) (Γ' := [(.sort .zero : VExpr)]) .one badEnv_onCtx

/-- The same instance with the witnesses named, so the existential is not merely inhabited by
something unexamined: `Γ₀ = []` and `A₀ = Sort 0`. -/
theorem exists_instN_typed_badEnv_sharp :
    (∀ e₀, Ctx.InstN [] e₀ (.sort .zero) 0 [(.sort .zero : VExpr)] []) ∧
      OnCtx ([] : List VExpr) (badEnv.IsType 0) ∧ badEnv.IsType 0 [] (.sort .zero) := by
  have := Ctx.LiftN.exists_instN_typed (env := badEnv) (U := 0)
    (Γ := []) (Γ' := [(.sort .zero : VExpr)]) .one badEnv_onCtx
  obtain ⟨Γ₀, A₀, hI, h1, h2⟩ := this
  -- `Ctx.InstN` at `k = 0` pins both witnesses.
  cases hI (.sort .zero)
  exact ⟨hI, h1, h2⟩

/-- **The untrimmed statement had no instance here.**  Stated separately from the instance
above: this is the refutation, not the inhabitation. -/
theorem exists_instN_typed_hyp_refuted : ¬ badEnv.Ordered := not_ordered_badEnv

/-! ## 3. `ntreeAux_WF'` where the staging hypothesis is refuted

`InductiveDeclExamples.ntreeAux_WF` carried
`h : VEnv.empty.addInduct' listDecl = some env₁`.  At `env₁ := badEnv` that equation is
false, because `listEnv_ordered` turns it into `badEnv.Ordered`.  The trimmed
`ntreeAux_WF'` nevertheless gives the block's well-formedness there. -/

theorem not_addInduct_badEnv :
    ¬ (VEnv.empty.addInduct' InductiveDeclExamples.listDecl = some badEnv) :=
  fun h => not_ordered_badEnv (InductiveDeclExamples.listEnv_ordered h)

/-- **`ntreeAux` is a well-formed block at `badEnv`.** -/
theorem ntreeAux_WF_badEnv : InductiveDeclExamples.ntreeAux.WF badEnv :=
  InductiveDeclExamples.ntreeAux_WF'

/-- Non-vacuity of the conclusion: `VInductDecl'.WF badEnv` does **not** hold of every
declaration, so §3's instance is not the trivial consequence of a degenerate predicate.  A
block with no types fails `types_ne` at every environment, `badEnv` included. -/
def noTypesDecl : VInductDecl' :=
  { uvars := 0, params := [], lvl := .zero, types := [], isLE := false }

theorem not_wf_noTypesDecl : ¬ noTypesDecl.WF badEnv := fun H => H.types_ne rfl

/-! ## 4. What is *not* claimed

* Neither trim moves the hole census; both lemmas were and remain `sorry`-free.
* `badEnv` is a probe, not a model: it is deliberately outside `Ordered`, so nothing about
  the kernel's soundness follows from anything proved at it.  Its only job is to be a place
  where the deleted hypotheses are **false**, which is what distinguishes a real trim from a
  hypothesis that was merely inert (true at every well-formed environment, and therefore
  costless to keep). -/

/-! ## 5. Hole-freeness, stated separately from inhabitation

Every result above, and the two trimmed lemmas themselves.  `sorryAx` must not appear. -/

#print axioms Lean4Lean.Ctx.LiftN.exists_instN_typed
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_WF'
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_WF
#print axioms Lean4Lean.not_ordered_badEnv
#print axioms Lean4Lean.exists_instN_typed_badEnv
#print axioms Lean4Lean.exists_instN_typed_badEnv_sharp
#print axioms Lean4Lean.not_addInduct_badEnv
#print axioms Lean4Lean.ntreeAux_WF_badEnv
#print axioms Lean4Lean.not_wf_noTypesDecl

end Lean4Lean
