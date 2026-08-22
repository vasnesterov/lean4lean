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

## Method: work backwards from each obligation, not forwards from the definition

Both defects found in this file were invisible from the definition's side and obvious from a
field's side, so this is worth stating as a technique rather than as two anecdotes.

Reading a definition asks *is this well-formed?*  Working backwards from each obligation the
definition must discharge asks *what does this actually have to supply?* — and only the
second finds **under-recording**, which is invisible from the definition's side by
construction: a constructor that fails to record something still elaborates, still typechecks,
and still looks complete.

The two instances here:

* `Params.pat_uniq` concludes `r ≍ r'`, so it is *not* a statement about the pattern alone.
  Instantiated at `p₁ = p₂ = p₃` with `Pattern.inter_self` it forces the datum to be a
  function of the pattern — which an earlier version, taking the check's `computed` and
  `pairs` as free constructor parameters, violated outright.  That version was not merely
  loose; it made `pat_uniq` false.
* `Params.pat_app_uniq` bottoms out in `(.const r).inter (.const c) = none` across *different*
  registered patterns, i.e. a cross-block name fact.  Deriving it needs the two constants to
  be declared, which `env.defeqs (D.iotaRule …)` does not give — hence the two
  `env.constants … = some …` hypotheses on `Pat.iota`.

Neither is visible by reading `Pat`.  Both are visible immediately from the field.

The same reading explains two earlier findings on this project: `ParamsExtra.ctor_ty` was
unsatisfiable and went unnoticed because *no instance existed to work backwards from*, and
`VEnv.HasPrimitives` was missing a `Nat.pred` field for the same reason.  A class with no
instance has never had this check applied to it.

## What the constructors carry

Every component of `r` is *derived* from `D`, `T`, `C`, and the constructors carry only
`Prop`-valued side conditions (closedness of `iotaLam`, and of each result index abstracted
over the constructor's binders).

That is forced, not stylistic.  `pat_uniq` concludes `r ≍ r'` whenever two registered
patterns intersect; instantiated at `p₁ = p₂ = p₃` with `Pattern.inter_self` it says the
datum is a *function of the pattern*.  An earlier version took the check's `computed` and
`pairs` as free constructor parameters — which would have let one pattern carry two
different checks and made `pat_uniq` false.  Because the remaining side conditions are
`Prop`, `List.pmap` over different proofs yields equal lists and uniqueness survives.
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

/-- The matched constructor arguments, as right-hand sides. -/
def ctorArgRHS (T : VIndType) (C : VIndCtor) : List (D.iotaPat T C).RHS :=
  (Pattern.argPaths (.const C.name) (D.np + C.fields.length)).map fun y =>
    Pattern.RHS.var (p := D.iotaPat T C) (Sum.inr y)

/-- The level-index pairs relating the recursor leaf's list to the constructor leaf's.  The
block's own universes sit at `i` on the constructor's side and, when `isLE` prepends a fresh
elimination universe, at `i + 1` on the recursor's. -/
def iotaLevelPairs : List (Nat × Nat) :=
  (List.range D.uvars).map fun i => (if D.isLE then i + 1 else i, i)

/-- The constructor's result indices, as right-hand sides: each `a ∈ C.args` abstracted over
the constructor's own binders — a *closed* term, as `RHS.fixed` demands — and applied back to
the matched constructor arguments.

Derived rather than taken as a parameter.  It has to be: `pat_uniq` concludes `r ≍ r'`
whenever two registered patterns intersect, and with `p₁ = p₂ = p₃` and `Pattern.inter_self`
that forces the datum to be a *function of the pattern*.  A free `computed` parameter would
let one pattern carry two different checks and make `pat_uniq` false.  The closedness proofs
are `Prop`, so `pmap` over different proofs yields equal lists and uniqueness survives. -/
def iotaComputed (T : VIndType) (C : VIndCtor)
    (h : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
    List (D.iotaPat T C).RHS :=
  C.args.pmap (fun a ha =>
    Pattern.RHS.mkApp
      (Pattern.RHS.fixed (p := D.iotaPat T C)
        (mkLams (C.params ++ C.fields.map (·.type)) a)
        (iotaLeafCtor (Lean.mkRecName T.name) C.name
          (D.np + D.nm + D.nmin + T.indices.length) (D.np + C.fields.length)) ha)
      (D.ctorArgRHS T C)) h

/-- The ι-rule's check: parameter agreement, index agreement, level agreement. -/
def iotaCheckOf (T : VIndType) (C : VIndCtor)
    (h : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
    (D.iotaPat T C).Check :=
  iotaCheck (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
    (D.np + C.fields.length) D.np (D.np + D.nm + D.nmin)
    (D.iotaComputed T C h) D.iotaLevelPairs

end VInductDecl'

/-- **The `Pat` relation.**  One constructor per rule shape; see the module docstring for why
this is an inductive family rather than an existential. -/
inductive Pat (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop
  | delta {c : Lean.Name} {u : Nat} {v t : VExpr} (h : v.Closed) :
      env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩ →
      Pat env (.const c) (deltaRHS c v h, Pattern.Check.true)
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
      (h : (D.iotaLam q C).Closed)
      (hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
      D.types[j]? = some T → C ∈ T.ctors → env.defeqs (D.iotaRule j q C) →
      -- the two constants the pattern's leaves name are really declared, at the types
      -- `addInduct'` gave them.  Not decoration: see `Pat.rec_ne_ctor`.
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      Pat env (D.iotaPat T C) (D.iotaRHSOf j q T C h, D.iotaCheckOf T C hargs)

/-! ## The global name-distinctness side condition

`pat_app_uniq` bottoms out in `(.const r).inter (.const c) = none` where `r` is one
registered pattern's *recursor* leaf and `c` another's *constructor* leaf — patterns that may
come from different blocks.  So it needs: no recursor name is any constructor name, anywhere
in the environment.

Within a block that is `addInduct'`'s freshness (`allNames` is added by `addConstList`, which
fails on a duplicate).  Across blocks it is **not** derivable from `addConstList_fresh`, which
only gives freshness against the environment as it stood when *that* block was added.

What makes it derivable is `VEnv.addConst` rejecting duplicates outright: a name declared
twice is impossible in any environment built by declarations, so if a recursor name equalled
a constructor name they would be the *same constant*, and their stored types would be equal.
Those types are syntactically distinguishable — a recursor's, under its binders, is a motive
application with a `bvar` head, a constructor's is `I p args` with a `const` head.

That argument needs the two constants to be *present*, which `env.defeqs (D.iotaRule …)` does
not give: a rule being in `defeqs` says nothing about `constants`.  Hence the two
`env.constants … = some …` hypotheses on `Pat.iota` above.  They are discharged where the
evidence exists — `VInductDecl'.WF.iotaCtx` supplies exactly these from `addInduct'` — rather
than assumed globally. -/

/-- A recursor's stored type, under its binders, is a *motive application* — a `bvar` head. -/
theorem VInductDecl'.piBodyHead_recType (D : VInductDecl') (j : Nat) {T : VIndType}
    (hT : D.types[j]? = some T) :
    VExpr.piBodyHead (D.recType j)
      = .bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j)) := by
  rw [VInductDecl'.recType, getD_types hT,
    show ∀ A B : VExpr, VExpr.forallE A B = mkPi [A] B from fun _ _ => rfl,
    ← VExpr.mkPi_append]
  exact VExpr.piBodyHead_mkPi_mkApp _ (by nofun) (by nofun) _

/-- A constructor's stored type, under its binders, is `I p args` — a `const` head. -/
theorem VIndCtor.piBodyHead_type (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    VExpr.piBodyHead (C.type D j) = .const (D.types.getD j default).name D.ownLvls := by
  rw [VIndCtor.type, VIndCtor.canonResult, VInductDecl'.tyApp]
  exact VExpr.piBodyHead_mkPi_mkApp _ (by nofun) (by nofun) _

/-- So the two stored types are never equal. -/
theorem recType_ne_ctorType {D D' : VInductDecl'} {j j' : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) : D.recType j ≠ C.type D' j' := fun h => by
  have h2 := congrArg VExpr.piBodyHead h
  rw [D.piBodyHead_recType j hT, C.piBodyHead_type D' j'] at h2
  exact absurd h2 (by nofun)

/-- **The global name-distinctness fact.**  A recursor name is never a constructor name — in
*any* environment, because `VEnv.addConst` rejects duplicates, so the two would be the same
constant and their stored types would have to agree.  This is what `pat_app_uniq` bottoms out
in; see the section above for why it needs the constants to be present. -/
theorem rec_ne_ctor {env : VEnv} {D D' : VInductDecl'} {j j' : Nat} {T : VIndType}
    {C : VIndCtor} (hT : D.types[j]? = some T)
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hctor : env.constants C.name = some ⟨D'.uvars, C.type D' j'⟩) :
    Lean.mkRecName T.name ≠ C.name := fun h => by
  rw [h, hctor, Option.some_inj] at hrec
  exact recType_ne_ctorType hT (congrArg VConstant.type hrec).symm

/-- **`Params.pat_simple`.**  Immediate from the shape of the family: every constructor's
pattern index is a `SimplePattern.toPattern` by construction. -/
theorem Pat.simple {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} (h : Pat env p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases h with
  | delta => exact ⟨.defn _, rfl⟩
  | iota => exact ⟨.iota .., rfl⟩

end Lean4Lean
