import Lean4Lean.Theory.Typing.PatternDecode
import Lean4Lean.Theory.Inductive.Lemmas

/-!
# `Pat`: which patterns an environment's rules are

`Theory/Typing/PatternDecode.lean` builds the pattern machinery without knowing what a rule
*is*: the right-hand side is parameterised by where to cut the two matched argument lists,
the check by its clause lists.  This file supplies the inductive vocabulary — `iotaRule`,
`iotaLam`, `iotaLhs` — and defines the `Pat` relation that `VEnv.Params` asks for.

## Why `Pat` is an inductive family

`Params.Pat` has type `(p : Pattern) → p.RHS × p.Check → Prop`, so the datum `r` is
*dependent* on the pattern.  Stating `Pat p r` as `∃ df, env.defeqs df ∧ r = derive df`
therefore drags in dependent equality between `p.RHS × p.Check` at two syntactically
different patterns, which is painful and buys nothing.  An inductive family indexed by `p`
and `r`, with one constructor per rule shape, sidesteps it entirely: each constructor fixes
`p` and `r` simultaneously, and `pat_simple` falls out by `cases`.

## What the constructors carry

`computed` and `pairs` — the check's index-agreement right-hand sides and its level-index
pairs — are constructor *parameters* rather than derived, because they only affect the
`Check`, and the `Check` is only consumed by `extra_pat` and `pat_wf`.  The orthogonality
fields (`pat_uniq`, `pat_app_l_uniq`, `pat_app_uniq`) and `pat_simple` are statements about
the *pattern* alone and are indifferent to them.  Whoever builds the instance supplies them
together with the proofs that they are correct for the rule at hand; see the checks section
of `PatternDecode.lean` for why they must not be dropped.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars)

namespace VInductDecl'

variable (D : VInductDecl')

/-- The pattern of the ι-rule for constructor `C` of block type `T`: the recursor applied to
its parameters, motives, minors and indices, then to the constructor applied to its
parameters and fields. -/
def iotaPat (T : VIndType) (C : VIndCtor) : Pattern :=
  (SimplePattern.iota (Lean.mkRecName T.name) (D.np + D.nm + D.nmin + T.indices.length)
    C.name (D.np + C.fields.length)).toPattern

theorem iotaPat_eq (T : VIndType) (C : VIndCtor) :
    D.iotaPat T C
      = (SimplePattern.iota (Lean.mkRecName T.name)
          (D.np + D.nm + D.nmin + T.indices.length) C.name (D.np + C.fields.length)).toPattern :=
  rfl

/-- The ι-rule's right-hand side: `iotaLam` applied to the parameters, motives and minors
taken from the *recursor's* matched arguments, then the fields from the *constructor's*.

The cut points are exactly `iotaLhs`'s: the recursor's spine is `np + nm + nmin` variable
blocks followed by the index terms, and the constructor's is `np` parameters followed by
`nf` fields.  Taking the parameters from the recursor's side and dropping the constructor's
copy is sound because `iotaParamsCheck` relates them. -/
def iotaRHSOf (_j q : Nat) (T : VIndType) (C : VIndCtor) (h : (D.iotaLam q C).Closed) :
    (D.iotaPat T C).RHS :=
  iotaRHS (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
    (D.np + C.fields.length) (D.iotaLam q C) h (D.np + D.nm + D.nmin) D.np

/-- The ι-rule's check: parameter agreement, index agreement, level agreement. -/
def iotaCheckOf (T : VIndType) (C : VIndCtor)
    (computed : List (D.iotaPat T C).RHS) (pairs : List (Nat × Nat)) :
    (D.iotaPat T C).Check :=
  iotaCheck (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
    (D.np + C.fields.length) D.np (D.np + D.nm + D.nmin) computed pairs

end VInductDecl'

/-- **The `Pat` relation.**  One constructor per rule shape; see the module docstring for why
this is an inductive family rather than an existential. -/
inductive Pat (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop
  | delta {c : Lean.Name} {u : Nat} {v t : VExpr} (h : v.Closed) :
      env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩ →
      Pat env (.const c) (deltaRHS c v h, Pattern.Check.true)
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
      {computed : List (D.iotaPat T C).RHS} {pairs : List (Nat × Nat)}
      (h : (D.iotaLam q C).Closed) :
      D.types[j]? = some T → C ∈ T.ctors → env.defeqs (D.iotaRule j q C) →
      Pat env (D.iotaPat T C) (D.iotaRHSOf j q T C h, D.iotaCheckOf T C computed pairs)

/-- **`Params.pat_simple`.**  Immediate from the shape of the family: every constructor's
pattern index is a `SimplePattern.toPattern` by construction. -/
theorem Pat.simple {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} (h : Pat env p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases h with
  | delta => exact ⟨.defn _, rfl⟩
  | iota => exact ⟨.iota .., rfl⟩

end Lean4Lean
