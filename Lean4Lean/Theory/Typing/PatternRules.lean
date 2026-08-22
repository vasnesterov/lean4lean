import Lean4Lean.Theory.Typing.PatternDecode
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.DeltaUnique

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

**Work backwards from `pat_uniq` first.**  It is the only field whose conclusion mentions
`r`, so it is the only one that constrains the *data* rather than the pattern — and it has
now produced three under-recordings in this file, while the three genuinely pattern-only
fields produced none.  If a class has one field that constrains the encoding, that field is
where the whole audit should start.

The instances here:

* `Params.pat_uniq` concludes `r ≍ r'`, so it is *not* a statement about the pattern alone.
  Instantiated at `p₁ = p₂ = p₃` with `Pattern.inter_self` it forces the datum to be a
  function of the pattern — which an earlier version, taking the check's `computed` and
  `pairs` as free constructor parameters, violated outright.  That version was not merely
  loose; it made `pat_uniq` false.
* `Params.pat_app_uniq` bottoms out in `(.const r).inter (.const c) = none` across *different*
  registered patterns, i.e. a cross-block name fact.  Deriving it needs the two constants to
  be declared, which `env.defeqs (D.iotaRule …)` does not give — hence the two
  `env.constants … = some …` hypotheses on `Pat.iota`.
* `pat_uniq` again, on the δ side: at `p₁ = p₂ = p₃ = .const c` it forces `v = v'`, so the
  rule's *value* must be determined by its head constant.  `env.defeqs` alone does not give
  that; it needs `VEnv.WF`'s declaration history, since `addConst` is what rejects a second
  δ-rule for the same name.

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

/-! ## `Params.pat_uniq`

The case analysis is driven entirely by the two hypotheses `Subpattern p₃ p₁` and
`p₂.inter p₃ = some p₄`, inverted by the lemmas at the end of `PatternDecode.lean`.  Because
`Subpattern.varN_const_inv` says a subpattern of a `varN` chain over a constant is a *shorter
chain over the same constant*, and `Pattern.inter_varN_const` says two such chains intersect
only when both name and depth agree, every one of the nine (constructor × constructor ×
which-leaf) cases reduces to a statement about *names*:

| `p₁` | `p₂` | `p₃` | what closes it |
|---|---|---|---|
| δ | δ | `.const c` | `Pat.uniq_delta`, i.e. `VEnv.WF.delta_uniq` |
| δ | ι | `.const c` | shape: `(.app _ _).inter (.const _) = none` |
| ι | δ | `.const` at depth `>0` | shape: `(.const _).inter (.var _) = none` |
| ι | δ | recursor leaf | **`Pat.deltaHead_ne_recName`** |
| ι | δ | constructor leaf | **`Pat.deltaHead_ne_ctorName`** |
| ι | ι | recursor chain, short | `Pat.rec_arity_uniq` |
| ι | ι | constructor chain, short | `rec_ne_ctor` (already proved above) |
| ι | ι | all of `p₁` | **`Pat.iota_data_uniq`** |

The three bold entries are the ones that need what this file's header calls a `VEnv.Sig`
(design §7.7, ledger I1) and are stated as separate obligations below.  Everything else is
proved here. -/

/-- The number of leading Πs of a recursor's stored type: `params ++ motives ++ minors ++
indices`, then the major premise.  What makes this usable is that `np`, `nm` and `nmin` are
`abbrev`s for list lengths, so the count is definitional and needs no `VInductDecl'.WF`. -/
theorem VInductDecl'.length_peelPis_recType (D : VInductDecl') (j : Nat) :
    (VExpr.peelPis (D.recType j)).1.length
      = D.np + D.nm + D.nmin + (D.types.getD j default).indices.length + 1 := by
  rw [VInductDecl'.recType, VExpr.peelPis_mkPi, VExpr.peelPis_forallE]
  simp [VExpr.mkApp_concat, VExpr.peelPis, VInductDecl'.length_atRecTele, VInductDecl'.motives,
    VInductDecl'.minors, VInductDecl'.np, VInductDecl'.nm, VInductDecl'.nmin]
  omega

/-- **Same recursor name ⇒ same recursor arity.**  Two registered ι-patterns whose recursor
leaves carry the same name name the *same constant*, hence the same stored type, and a
recursor's arity is the number of leading Πs of that type.  This is what rules out one
ι-pattern's recursor chain being a strict prefix of another's — the case where `p₃` sits
below `p₁`'s recursor leaf but `p₂` is shorter. -/
theorem Pat.rec_arity_uniq {env : VEnv} {D D' : VInductDecl'} {j j' : Nat}
    {T T' : VIndType} (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hrec' : env.constants (Lean.mkRecName T'.name) = some ⟨D'.recUvars, D'.recType j'⟩)
    (hname : Lean.mkRecName T'.name = Lean.mkRecName T.name) :
    D'.np + D'.nm + D'.nmin + T'.indices.length = D.np + D.nm + D.nmin + T.indices.length := by
  rw [hname, hrec, Option.some_inj] at hrec'
  have h := congrArg (fun e => (VExpr.peelPis (VConstant.type e)).1.length) hrec'
  simp only [VInductDecl'.length_peelPis_recType, D.getD_types hTj, D'.getD_types hTj'] at h
  omega

/-- **`pat_uniq` at a δ-pattern.**  A δ-rule's value is determined by its head constant
(`VEnv.WF.delta_uniq`), and everything else in the datum is derived from the head, so the
datum is a function of the pattern.  This is the consumer the whole of
`Theory/Typing/DeltaUnique.lean` exists to supply. -/
theorem Pat.uniq_delta {env : VEnv} (henv : env.WF) {c : Lean.Name}
    {r r' : (Pattern.const c).RHS × (Pattern.const c).Check}
    (h : Pat env (.const c) r) (h' : Pat env (.const c) r') : r = r' := by
  cases h with
  | delta hv hdf =>
    cases h' with
    | delta hv' hdf' => obtain ⟨-, -, rfl, -⟩ := henv.delta_uniq hdf hdf'; rfl

/-! ### The three remaining obligations

All three are *provenance* facts: they say that a rule which is syntactically an ι-rule of a
block really was contributed by that block's declaration.  `env.defeqs` is a bare predicate
with no memory of which declaration produced a rule, so none of them follows from the data
`Pat` carries; they need the declaration history, i.e. `VEnv.Sig` (design §7.7, ledger I1) or
per-fact slices of it proved by induction on `VEnv.WF'` in the style of
`Theory/Typing/DeltaUnique.lean`.

`DeltaUnique.lean` is exactly such a slice for the δ×δ case, and it is the reason the first
row of the table above is closed.  These three are the remaining ones. **Do not discharge any
of them by adding a hypothesis to `Pat`**: `Pat.iota`'s two `env.constants` fields were added
for `pat_app_uniq` because a *stored-type* argument (`rec_ne_ctor`) could finish the job from
them; there is no such argument here, since a `def` may legitimately be declared at a
recursor's or a constructor's type. -/

/-- **Obligation 1 (needs `VEnv.Sig`; ledger I1).**  A δ-rule's head is never the recursor
name of a registered ι-rule.

Route: within `VEnv.WF' ds env`, the ι-rule was added by an `.induct D''` step whose
`addConstList D''.allConsts` succeeded, so `Lean.mkRecName T.name` was undeclared before that
step; the δ-rule was added by a `.def`/`.unsafeDef` step whose `addConst` succeeded, so `c`
was undeclared before *that* step.  `VEnv.addConst` rejects duplicates, so the later of the
two steps would have failed.  Making that argument needs an invariant recording the head and
major-premise names of every rule's λ-peeled left-hand side (`VExpr.peelLams`/`VExpr.spine`,
already in `PatternDecode.lean`) together with their declaredness — the same seven-arm
`VEnv.WF'` induction as `DefEqHeadsDeclared`/`DefEqHeadsUnique`.  Estimated 350–450 lines,
shared with Obligation 2. -/
theorem Pat.deltaHead_ne_recName {env : VEnv} (henv : env.WF)
    {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hTj : D.types[j]? = some T)
    {c : Lean.Name} {u : Nat} {v t : VExpr}
    (hdf' : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩) :
    c ≠ Lean.mkRecName T.name := sorry

/-- **Obligation 2 (needs `VEnv.Sig`; ledger I1).**  A δ-rule's head is never the constructor
name of a registered ι-rule.  Same route as Obligation 1, reading the *major premise's* head
instead of the spine's: `VInductDecl'.iotaLhs` ends in `D.ctorApp' C …`, whose spine head is
`.const C.name D.selfLvls`. -/
theorem Pat.deltaHead_ne_ctorName {env : VEnv} (henv : env.WF)
    {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hTj : D.types[j]? = some T) (hCT : C ∈ T.ctors)
    {c : Lean.Name} {u : Nat} {v t : VExpr}
    (hdf' : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩) :
    c ≠ C.name := sorry

/-- **Obligation 3 (needs `VEnv.Sig`; ledger I1, and G4).**  Two registered ι-rules with the
same pattern carry the same datum.

This is the strongest of the three, and it is `pat_uniq`'s real content on the ι side: the
pattern records only `(recName, recArity, ctorName, ctorArity)`, while the datum depends on
`D.iotaLam q C`, `D.np`, `D.nm + D.nmin`, `C.args`, `C.params`, `C.fields`, `D.uvars` and
`D.isLE`.  So it asks that the *block be recoverable from the constructor's name* — ledger G4
("a name belongs to at most one block"), which the design doc lists as needing `VEnv.Sig`.

Two of the eight components do come for free from the fields `Pat.iota` already carries:
`D.uvars = D'.uvars` from the two `env.constants C.name` facts, and then `D.isLE = D'.isLE`
because `recUvars = if isLE then uvars + 1 else uvars` and the two `recUvars` agree.  The rest
does not: recovering `C.params`/`C.fields`/`C.args` from `C.type D j` would need injectivity
of `VIndCtor.type`, and splitting its telescope at `np` needs `C.params.length = D.np`, which
lives in `VInductDecl'.WF` and is not available here. -/
theorem Pat.iota_data_uniq {env : VEnv} (henv : env.WF)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    {hcl : (D.iotaLam q C).Closed} {hcl' : (D'.iotaLam q' C').Closed}
    {hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed}
    {hargs' : ∀ a ∈ C'.args, (mkLams (C'.params ++ C'.fields.map (·.type)) a).Closed}
    (h : Pat env (D.iotaPat T C) (D.iotaRHSOf j q T C hcl, D.iotaCheckOf T C hargs))
    (h' : Pat env (D'.iotaPat T' C') (D'.iotaRHSOf j' q' T' C' hcl', D'.iotaCheckOf T' C' hargs'))
    (hp : D.iotaPat T C = D'.iotaPat T' C') :
    (D.iotaRHSOf j q T C hcl, D.iotaCheckOf T C hargs)
      ≍ (D'.iotaRHSOf j' q' T' C' hcl', D'.iotaCheckOf T' C' hargs') := sorry

/-- **`Params.pat_uniq`**, reduced to the three obligations above.  Six of the nine cases are
closed outright; see the table in the section header for which lemma closes which. -/
theorem Pat.uniq {env : VEnv} (henv : env.WF) {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (h : Pat env p₁ r) (h' : Pat env p₂ r') (hs : Subpattern p₃ p₁)
    (hi : p₂.inter p₃ = some p₄) : p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases h with
  | @delta c u v t hv hdf =>
    cases hs.const_inv
    cases h' with
    | @delta c' u' v' t' hv' hdf' =>
      obtain ⟨rfl, rfl⟩ := Pattern.inter_const_const hi
      exact ⟨rfl, rfl, heq_of_eq (Pat.uniq_delta henv (.delta hv hdf) (.delta hv' hdf'))⟩
    | iota => exact absurd hi Pattern.inter_app_const
  | @iota D j q T C hcl hargs hTj hCT hdf hrec hctor =>
    simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hs ⊢
    cases hs with
    | refl =>
      cases h' with
      | delta => exact absurd hi Pattern.inter_const_app
      | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
        simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
        obtain ⟨x, y, hx, hy, rfl⟩ := Pattern.inter_app_app hi
        obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hx
        obtain ⟨hK, hN, -⟩ := Pattern.inter_varN_const hy
        have hp : D.iotaPat T C = D'.iotaPat T' C' := by
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern, hR, hM, hK, hN]
        exact ⟨hp, hp.symm, Pat.iota_data_uniq henv (.iota hcl hargs hTj hCT hdf hrec hctor)
          (.iota hcl' hargs' hTj' hCT' hdf' hrec' hctor') hp⟩
    | appL hsl =>
      obtain ⟨k, hk, rfl⟩ := hsl.varN_const_inv
      cases k with
      | zero =>
        cases h' with
        | @delta c' u' v' t' hv' hdf' =>
          obtain ⟨hc, -⟩ := Pattern.inter_const_const hi
          exact absurd hc (Pat.deltaHead_ne_recName henv hdf hTj hdf')
        | iota =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hx
          have := Pat.rec_arity_uniq hTj hTj' hrec hrec' hR
          omega
    | appR hsr =>
      obtain ⟨k, hk, rfl⟩ := hsr.varN_const_inv
      cases k with
      | zero =>
        cases h' with
        | @delta c' u' v' t' hv' hdf' =>
          obtain ⟨hc, -⟩ := Pattern.inter_const_const hi
          exact absurd hc (Pat.deltaHead_ne_ctorName henv hdf hTj hCT hdf')
        | iota =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (rec_ne_ctor hTj' hrec' hctor)

end Lean4Lean
