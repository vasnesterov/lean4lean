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
recursor's arity is the number of leading Πs of that type. -/
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

/-! ## `Params.pat_app_l_uniq` and `Params.pat_app_uniq`

**Neither needs any provenance.**  Both quantify over `Subpattern (.app p₁ p₂) p`, and the
only `.app` subpattern of a registered pattern is an ι-pattern *in full* — a δ-pattern has
none at all, and a `varN` chain's subpatterns are chains, never applications.  So both fields
reduce to `varN`-chain arithmetic plus one name fact each, and both name facts are already
in the tree: `rec_ne_ctor` (a recursor name is never a constructor name, by stored-type
shapes) and `Pat.rec_arity_uniq` (same recursor name ⇒ same arity, by the Π-count of the
stored type).  This is worth stating because the ledger routes all of group I through I1;
these two do not touch it. -/

theorem Subpattern.not_app_varN {q1 q2 : Pattern} {c n}
    (h : Subpattern (.app q1 q2) ((Pattern.const c).varN n)) : False := by
  obtain ⟨k, -, hk⟩ := h.varN_const_inv
  cases k <;> exact absurd hk nofun

/-- The only `.app` subpattern of an ι-pattern is the pattern itself. -/
theorem Pat.app_sub_iota {D : VInductDecl'} {T C} {p₁ p₂ : Pattern}
    (h : Subpattern (.app p₁ p₂) (D.iotaPat T C)) :
    p₁ = (Pattern.const (Lean.mkRecName T.name)).varN (D.np + D.nm + D.nmin + T.indices.length)
      ∧ p₂ = (Pattern.const C.name).varN (D.np + C.fields.length) := by
  rw [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at h
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | appL h => exact absurd h Subpattern.not_app_varN
  | appR h => exact absurd h Subpattern.not_app_varN

/-- A δ-pattern has no `.app` subpattern, so both `Pat`s in the `pat_app_*` fields are ι. -/
theorem Pat.app_sub_inv {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} {p₁ p₂}
    (h : Pat env p r) (hs : Subpattern (.app p₁ p₂) p) :
    ∃ (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor),
      D.types[j]? = some T ∧
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ ∧
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ ∧
      p₁ = (Pattern.const (Lean.mkRecName T.name)).varN
             (D.np + D.nm + D.nmin + T.indices.length) ∧
      p₂ = (Pattern.const C.name).varN (D.np + C.fields.length) := by
  cases h with
  | delta => exact absurd hs.const_inv nofun
  | @iota D j q T C _ _ hTj hCT hdf hrec hctor =>
    obtain ⟨rfl, rfl⟩ := Pat.app_sub_iota hs
    exact ⟨D, j, T, C, hTj, hrec, hctor, rfl, rfl⟩

/-- **`Params.pat_app_l_uniq`.**  One ι-pattern's recursor chain, cut short, cannot intersect
another's: same recursor name forces same arity (`Pat.rec_arity_uniq`), and the cut chain is
strictly shorter. -/
theorem Pat.app_l_uniq {env : VEnv} {p p' p₁ p₂ p₁' p₂' p₃ : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    (h : Pat env p r) (h' : Pat env p' r') (hs : Subpattern (.app p₁ p₂) p)
    (hs' : Subpattern (.app p₁' p₂') p') (hv : Subpattern (.var p₃) p₁) :
    p₁'.inter p₃ = none := by
  obtain ⟨D, j, T, C, hTj, hrec, hctor, rfl, rfl⟩ := h.app_sub_inv hs
  obtain ⟨D', j', T', C', hTj', hrec', hctor', rfl, rfl⟩ := h'.app_sub_inv hs'
  obtain ⟨k, hk, hkk⟩ := hv.varN_const_inv
  cases k with
  | zero => exact absurd hkk nofun
  | succ k =>
    cases (Pattern.var.injEq .. ▸ hkk : _ = _)
    cases hn : ((Pattern.const (Lean.mkRecName T'.name)).varN
        (D'.np + D'.nm + D'.nmin + T'.indices.length)).inter
        ((Pattern.const (Lean.mkRecName T.name)).varN k) with
    | none => rfl
    | some x =>
      obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hn
      have := Pat.rec_arity_uniq hTj hTj' hrec hrec' hR
      omega

/-- **`Params.pat_app_uniq`.**  One pattern's recursor leaf against another's constructor
leaf: `rec_ne_ctor`. -/
theorem Pat.app_uniq {env : VEnv} {p p' p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    (h : Pat env p r) (h' : Pat env p' r') (hs : Subpattern (.app p₁ p₂) p)
    (hs' : Subpattern (.app p₁' p₂') p')
    (h3 : Subpattern p₃ p₁) (h3' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  obtain ⟨D, j, T, C, hTj, hrec, hctor, rfl, rfl⟩ := h.app_sub_inv hs
  obtain ⟨D', j', T', C', hTj', hrec', hctor', rfl, rfl⟩ := h'.app_sub_inv hs'
  obtain ⟨k, -, rfl⟩ := h3.varN_const_inv
  obtain ⟨k', -, rfl⟩ := h3'.varN_const_inv
  cases hn : ((Pattern.const (Lean.mkRecName T.name)).varN k).inter
      ((Pattern.const C'.name).varN k') with
  | none => rfl
  | some x =>
    obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hn
    exact absurd hR (rec_ne_ctor hTj hrec hctor')

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
| ι | δ | recursor leaf | `Pat.deltaHead_ne_recName` (`KeyHeadDelta`) |
| ι | δ | constructor leaf | `Pat.deltaHead_ne_ctorName` (`KeyHeadDelta`) |
| ι | ι | recursor chain, short | `Pat.rec_arity_uniq` |
| ι | ι | constructor chain, short | `rec_ne_ctor` (already proved above) |
| ι | ι | all of `p₁` | `Pat.iota_data_uniq` (`KeyMajorUnique`) |

The three bold entries are provenance facts — a rule that is syntactically an ι-rule of a
block really was contributed by that block's declaration.  `env.defeqs` is a bare predicate
with no memory of which declaration produced a rule, so none of them follows from the data
`Pat` carries; they need the declaration history.  All three are now discharged by the *key*
invariants of `Theory/Typing/DeltaUnique.lean` — `KeyHeadDelta` for the first two,
`KeyMajorUnique` for the third — **without** a `VEnv.Sig` (design §7.7, ledger I1) and
without ledger G4: the block is never recovered from a name, only the rule is. -/

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
    c ≠ Lean.mkRecName T.name := by
  rintro rfl
  have := henv.keyHeadDelta _ _ (Lean.mkRecName T.name) hdf' hdf VEnv.IsDeltaRule.const
    (by rw [VInductDecl'.key_iotaRule, D.getD_types hTj]; exact List.mem_cons_self)
  exact VEnv.not_isDeltaRule_iotaRule D j q C _ (this ▸ VEnv.IsDeltaRule.const)

/-- **Obligation 2 (needs `VEnv.Sig`; ledger I1).**  A δ-rule's head is never the constructor
name of a registered ι-rule.  Same route as Obligation 1, reading the *major premise's* head
instead of the spine's: `VInductDecl'.iotaLhs` ends in `D.ctorApp' C …`, whose spine head is
`.const C.name D.selfLvls`. -/
theorem Pat.deltaHead_ne_ctorName {env : VEnv} (henv : env.WF)
    {D : VInductDecl'} {j q : Nat} {C : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C))
    {c : Lean.Name} {u : Nat} {v t : VExpr}
    (hdf' : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩) :
    c ≠ C.name := by
  rintro rfl
  have := henv.keyHeadDelta _ _ C.name hdf' hdf VEnv.IsDeltaRule.const
    (by rw [VInductDecl'.key_iotaRule]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact VEnv.not_isDeltaRule_iotaRule D j q C _ (this ▸ VEnv.IsDeltaRule.const)

/-- Reading the two leaf names off an ι-pattern. -/
theorem VInductDecl'.iotaPat_inj {D D' : VInductDecl'} {T T' : VIndType} {C C' : VIndCtor}
    (h : D.iotaPat T C = D'.iotaPat T' C') :
    Lean.mkRecName T.name = Lean.mkRecName T'.name ∧
      D.np + D.nm + D.nmin + T.indices.length = D'.np + D'.nm + D'.nmin + T'.indices.length ∧
      C.name = C'.name ∧ D.np + C.fields.length = D'.np + C'.fields.length := by
  rw [VInductDecl'.iotaPat_eq, VInductDecl'.iotaPat_eq, SimplePattern.toPattern,
    SimplePattern.toPattern] at h
  obtain ⟨hf, ha⟩ := (Pattern.app.injEq ..).mp h
  obtain ⟨h1, h2⟩ := Pattern.varN_const_inj hf
  obtain ⟨h3, h4⟩ := Pattern.varN_const_inj ha
  exact ⟨h1, h2, h3, h4⟩

/-- **The payoff of `KeyMajorUnique`.**  Two registered ι-rules with the same pattern are the
*same rule*: the pattern pins the constructor's name, the key's last entry is that name, and
a rule is determined by it.  No block recovery — hence no ledger G4 — is involved.

This is what reduces Obligation 3 below to a statement with no environment in it. -/
theorem Pat.iota_rule_uniq {env : VEnv} (henv : env.WF)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hp : D.iotaPat T C = D'.iotaPat T' C') :
    D.iotaRule j q C = D'.iotaRule j' q' C' := by
  obtain ⟨-, -, hname, -⟩ := VInductDecl'.iotaPat_inj hp
  refine henv.keyMajorUnique _ _ C.name hdf hdf' ?_ ?_ <;>
    rw [VInductDecl'.key_iotaRule] <;> simp [hname]

/-! ### Reading the block's shape back out of the rule -/

@[simp] theorem VInductDecl'.length_iotaCtx (D : VInductDecl') (C : VIndCtor) :
    (D.iotaCtx C).length = D.np + D.nm + D.nmin + C.fields.length := by
  simp [VInductDecl'.iotaCtx, VInductDecl'.length_atRecTele, VInductDecl'.motives,
    VInductDecl'.minors, VInductDecl'.np, VInductDecl'.nm, VInductDecl'.nmin]
  omega

theorem VInductDecl'.lamArity_iotaLhs (D : VInductDecl') (j : Nat) (C : VIndCtor) :
    (D.iotaLhs j C).lamArity = 0 :=
  VExpr.lamArity_mkApp _ _ (by simp)

theorem VInductDecl'.lamArity_iotaRhsBody (D : VInductDecl') (q : Nat) (C : VIndCtor) :
    ((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).lamArity = 0 := by
  cases h : (D.iotaCtx C).length with
  | zero =>
    rw [VExpr.bvars_zero, VExpr.mkApp_nil, VInductDecl'.iotaLam, VExpr.lamArity_mkLams, h,
      Nat.zero_add]
    exact VExpr.lamArity_mkApp_bvar _ _
  | succ n => exact VExpr.lamArity_mkApp _ _ (by simp)

/-- The gap is nonzero: `hTj` forces the block to have at least one type, hence at least one
motive. -/
theorem VInductDecl'.zero_lt_off {D : VInductDecl'} {j : Nat} {T : VIndType}
    (hTj : D.types[j]? = some T) : 0 < D.nm + D.nmin := by
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 hTj
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le j) hj) (Nat.le_add_right _ _)

/-- **Reading the block's shape off the rule.**  `iotaLhs`'s major premise applies the
constructor to the parameters *and* to its own fields, with the motives and minors in
between; that gap separates `np` from `nf`.  The two `iotaCtx`s then give `nm + nmin`, and
the rule's right-hand side gives `iotaLam`. -/
theorem VInductDecl'.iotaRule_inj {D D' : VInductDecl'} {j q j' q' : Nat}
    {T T' : VIndType} {C C' : VIndCtor}
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (hN : D.np + C.fields.length = D'.np + C'.fields.length)
    (h : D.iotaRule j q C = D'.iotaRule j' q' C') :
    D.np = D'.np ∧ C.fields.length = C'.fields.length ∧
      D.nm + D.nmin = D'.nm + D'.nmin ∧ D.iotaLam q C = D'.iotaLam q' C' := by
  obtain ⟨hctx, hlhs⟩ := VExpr.mkLams_inj_of_arity (D.lamArity_iotaLhs j C)
    (D'.lamArity_iotaLhs j' C') (congrArg VDefEq.lhs h)
  have hL : (D.iotaCtx C).length = (D'.iotaCtx C').length := congrArg List.length hctx
  rw [VInductDecl'.length_iotaCtx, VInductDecl'.length_iotaCtx] at hL
  rw [VInductDecl'.iotaLhs, VInductDecl'.iotaLhs] at hlhs
  obtain ⟨-, hargs⟩ := VExpr.mkApp_inj_of_arity rfl rfl hlhs
  obtain ⟨-, hX⟩ := List.append_singleton_inj.mp hargs
  rw [VInductDecl'.ctorApp', VInductDecl'.ctorApp'] at hX
  obtain ⟨-, hcargs⟩ := VExpr.mkApp_inj_of_arity rfl rfl hX
  have hnp := VExpr.bvars_append_np_eq (VInductDecl'.zero_lt_off hTj)
    (VInductDecl'.zero_lt_off hTj') hN hcargs
  refine ⟨hnp, by omega, by omega, ?_⟩
  obtain ⟨-, hbody⟩ := VExpr.mkLams_inj_of_arity (D.lamArity_iotaRhsBody q C)
    (D'.lamArity_iotaRhsBody q' C') (congrArg VDefEq.rhs h)
  rw [show (D.iotaCtx C).length = (D'.iotaCtx C').length from congrArg List.length hctx] at hbody
  exact (VExpr.mkApp_inj rfl hbody).1

/-- **Reading the constructor off its stored type.**  `VIndCtor.type` is
`∀ params fields, I_j p args` with *raw* `params`, `fields` and `args` — no `atRec`, no
`instL`.  This is why the datum needs no level-well-formedness side conditions on `Pat.iota`:
everything `VInductDecl'.iotaComputed` mentions is recoverable from the constant that
`Pat.iota` already requires to be declared, not from the `atRec`-ed copies inside the rule. -/
theorem VIndCtor.type_inj {D D' : VInductDecl'} {j j' : Nat} {C C' : VIndCtor}
    (hnp : D.np = D'.np) (hnf : C.fields.length = C'.fields.length)
    (h : C.type D j = C'.type D' j') :
    C.params = C'.params ∧ C.fields.map (·.type) = C'.fields.map (·.type) ∧
      C.args = C'.args := by
  rw [VIndCtor.type, VIndCtor.type, VIndCtor.canonResult, VIndCtor.canonResult,
    VInductDecl'.tyApp, VInductDecl'.tyApp] at h
  obtain ⟨htel, hbody⟩ := VExpr.mkPi_inj_of_arity (VExpr.piArity_mkApp_const ..)
    (VExpr.piArity_mkApp_const ..) h
  obtain ⟨hp, hf⟩ := List.append_inj' htel (by simp [hnf])
  refine ⟨hp, hf, ?_⟩
  obtain ⟨-, hargs⟩ := VExpr.mkApp_inj_of_arity rfl rfl hbody
  rw [hnf, hnp] at hargs
  exact List.append_cancel_left hargs

/-! ### The datum, from the rule

`Pat.iota_rule_uniq` turned the shared pattern into an equation between two closed terms;
`VInductDecl'.iotaRule_inj` and `VIndCtor.type_inj` read the block's shape and the
constructor's telescopes back out of it.  What is left is to see that the datum is a
*function* of exactly those pieces — which `iotaDatum` says, `rfl`.

**The level-well-formedness side conditions on `Pat.iota` turned out to be unnecessary, and
were not added.**  The plan had been to recover `C.params`, `C.fields.map (·.type)` and
`C.args` from their `D.atRec`-ed copies inside `iotaCtx`/`iotaLhs`, which needs
`VExpr.instL D.selfLvls` to be injective and hence needs the terms' level parameters to be in
range.  But those three are also carried, *raw*, by the constructor's stored type
(`VIndCtor.type` is `∀ params fields, I_j p args` with no `instL` anywhere), and `Pat.iota`
already requires that constant to be declared — for `pat_app_uniq`.  Reading them from there
costs nothing and needs no side condition.  The `atRec`-ed copies were simply the wrong place
to look. -/

/-- The ι-datum as a function of the pattern's own parameters and the constructor's raw
telescope data.  `Pat.iota`'s datum is this on the nose (`iotaDatum_eq`, by `rfl`), which is
what turns `pat_uniq`'s heterogeneous conclusion into ten `Eq`s and a `subst`. -/
def iotaDatum (R K : Lean.Name) (M N : Nat) (v : VExpr) (hv : v.Closed) (P np : Nat)
    (args tel : List VExpr) (hargs : ∀ a ∈ args, (mkLams tel a).Closed)
    (lp : List (Nat × Nat)) :
    (SimplePattern.iota R M K N).toPattern.RHS × (SimplePattern.iota R M K N).toPattern.Check :=
  (iotaRHS R K M N v hv P np,
   iotaCheck R K M N np P
     (args.pmap (fun a ha => Pattern.RHS.mkApp
        (Pattern.RHS.fixed (p := (SimplePattern.iota R M K N).toPattern)
          (mkLams tel a) (iotaLeafCtor R K M N) ha)
        ((Pattern.argPaths (.const K) N).map fun y =>
          Pattern.RHS.var (p := (SimplePattern.iota R M K N).toPattern) (Sum.inr y))) hargs)
     lp)

theorem iotaDatum_eq (D : VInductDecl') (j q : Nat) (T : VIndType) (C : VIndCtor)
    (hcl : (D.iotaLam q C).Closed)
    (hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) :
    (D.iotaRHSOf j q T C hcl, D.iotaCheckOf T C hargs)
      = iotaDatum (Lean.mkRecName T.name) C.name
          (D.np + D.nm + D.nmin + T.indices.length) (D.np + C.fields.length)
          (D.iotaLam q C) hcl (D.np + D.nm + D.nmin) D.np
          C.args (C.params ++ C.fields.map (·.type)) hargs D.iotaLevelPairs := rfl

theorem iotaDatum_congr {R K R' K' : Lean.Name} {M N M' N' : Nat} {v v' : VExpr}
    {hv : v.Closed} {hv' : v'.Closed} {P np P' np' : Nat}
    {args tel args' tel' : List VExpr}
    {ha : ∀ a ∈ args, (mkLams tel a).Closed} {ha' : ∀ a ∈ args', (mkLams tel' a).Closed}
    {lp lp' : List (Nat × Nat)}
    (hR : R = R') (hK : K = K') (hM : M = M') (hN : N = N') (hvv : v = v')
    (hP : P = P') (hnp : np = np') (haa : args = args') (htt : tel = tel') (hll : lp = lp') :
    iotaDatum R K M N v hv P np args tel ha lp
      ≍ iotaDatum R' K' M' N' v' hv' P' np' args' tel' ha' lp' := by
  subst hR hK hM hN hvv hP hnp haa htt hll; rfl

/-- **The ι side of `pat_uniq`.**  Two registered ι-rules with the same pattern carry the
same datum.  The hypotheses are exactly `Pat.iota`'s fields; `D.uvars = D'.uvars` comes from
the two constructor constants and `D.isLE = D'.isLE` then from the two recursor constants,
which is what settles `iotaLevelPairs`. -/
theorem Pat.iota_data_uniq {env : VEnv} (henv : env.WF)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    {hcl : (D.iotaLam q C).Closed} {hcl' : (D'.iotaLam q' C').Closed}
    {hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed}
    {hargs' : ∀ a ∈ C'.args, (mkLams (C'.params ++ C'.fields.map (·.type)) a).Closed}
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hrec' : env.constants (Lean.mkRecName T'.name) = some ⟨D'.recUvars, D'.recType j'⟩)
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hctor' : env.constants C'.name = some ⟨D'.uvars, C'.type D' j'⟩)
    (hp : D.iotaPat T C = D'.iotaPat T' C') :
    (D.iotaRHSOf j q T C hcl, D.iotaCheckOf T C hargs)
      ≍ (D'.iotaRHSOf j' q' T' C' hcl', D'.iotaCheckOf T' C' hargs') := by
  obtain ⟨hR, hM, hK, hN⟩ := VInductDecl'.iotaPat_inj hp
  rw [hK, hctor', Option.some_inj] at hctor
  have huv : D.uvars = D'.uvars := (congrArg VConstant.uvars hctor).symm
  have hty : C.type D j = C'.type D' j' := (congrArg VConstant.type hctor).symm
  rw [hR, hrec', Option.some_inj] at hrec
  have hru : D.recUvars = D'.recUvars := (congrArg VConstant.uvars hrec).symm
  have hle : D.isLE = D'.isLE := by
    rw [VInductDecl'.recUvars, VInductDecl'.recUvars, huv] at hru
    cases hb : D.isLE <;> cases hb' : D'.isLE <;> rw [hb, hb'] at hru <;> simp at hru ⊢
  obtain ⟨hnp, hnf, hoff, hlam⟩ :=
    VInductDecl'.iotaRule_inj hTj hTj' hN (Pat.iota_rule_uniq henv hdf hdf' hp)
  obtain ⟨hpar, hfld, harg⟩ := VIndCtor.type_inj hnp hnf hty
  rw [iotaDatum_eq, iotaDatum_eq]
  refine iotaDatum_congr hR hK hM hN hlam (by omega) hnp harg (by rw [hpar, hfld]) ?_
  rw [VInductDecl'.iotaLevelPairs, VInductDecl'.iotaLevelPairs, huv, hle]

/-- **`Params.pat_uniq`**.  See the table in the section header for which lemma closes which
of the nine cases. -/
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
        exact ⟨hp, hp.symm,
          Pat.iota_data_uniq henv hTj hTj' hdf hdf' hrec hrec' hctor hctor' hp⟩
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
          exact absurd hc (Pat.deltaHead_ne_ctorName henv hdf hdf')
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
