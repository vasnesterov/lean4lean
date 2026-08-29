import Lean4Lean.Theory.Typing.PatternDecode
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.StructureClosed

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

/-- Instantiating the identity level substitution at a full list returns the list.  This is
what turns a δ-rule's stored `.const c (params u)` into `.const c ls`. -/
theorem VLevel.map_inst_params {u : Nat} {ls : List VLevel} (h : ls.length = u) :
    (VLevel.params u).map (VLevel.inst ls) = ls := by
  subst h
  refine List.ext_getElem (by simp [VLevel.params]) fun i h1 h2 => ?_
  simp [VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## The typing layer

A `Check.defeq` clause between two *syntactically equal* matched arguments is still a
judgement, not an equation: `IsDefEqU e e` demands that `e` be well typed.  For a rule's own
match those arguments are `bvar`s pointing into the rule's λ-telescope, and `IsDefEq.bvar`
assumes nothing beyond the lookup — so the whole obligation is that the index is in range.

This layer is small but it is *not* free, and it is easy to miss: "the two sides are the same
expression" settles the equality and leaves the judgement untouched. -/

theorem Lookup.exists_of_lt : ∀ {Δ : List VExpr} {i : Nat}, i < Δ.length → ∀ Γ,
    ∃ A, Lookup (Δ ++ Γ) i A
  | _ :: _, 0, _, _ => ⟨_, .zero⟩
  | _ :: Δ, i+1, h, Γ => by
    obtain ⟨B, hB⟩ := Lookup.exists_of_lt (Δ := Δ) (i := i) (by simpa using h) Γ
    exact ⟨B.lift, hB.succ⟩

theorem VEnv.isDefEqU_bvar {env : VEnv} {U : Nat} {Δ Γ : List VExpr} {i : Nat}
    (h : i < Δ.length) : env.IsDefEqU U (Δ ++ Γ) (.bvar i) (.bvar i) :=
  let ⟨_, hA⟩ := Lookup.exists_of_lt h Γ; ⟨_, .bvar hA⟩

/-! ### The quotient rule's argument lists and paths, computed -/

def quotLiftArgs : List VExpr := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]
def quotMkArgs : List VExpr := [.bvar 5, .bvar 4, .bvar 0]

theorem argPaths5 (c : Lean.Name) : Pattern.argPaths (.const c) 5
    = [some (some (some (some none))), some (some (some none)), some (some none), some none,
       none] := rfl

theorem argPaths3 (c : Lean.Name) : Pattern.argPaths (.const c) 3
    = [some (some none), some none, none] := rfl

theorem instL_peelLams_quotDefEq_lhs {ls : List VLevel} (hlen : ls.length = 2) :
    (VExpr.peelLams quotDefEq.lhs).2.instL ls
      = (VExpr.const ``Quot.lift ls).mkApp
          (quotLiftArgs ++ [(VExpr.const ``Quot.mk [ls.getD 0 .zero]).mkApp quotMkArgs]) := by
  show ((VExpr.const ``Quot.lift (VLevel.params 2)).mkApp
      (quotLiftArgs ++ [(VExpr.const ``Quot.mk [.param 0]).mkApp quotMkArgs])).instL ls = _
  simp only [VExpr.instL_mkApp, VExpr.instL, VLevel.map_inst_params hlen, quotLiftArgs,
    quotMkArgs, List.map_cons, List.map_nil, List.map_append]
  rfl

theorem instL_quotDefEq_lhs {ls : List VLevel} (hlen : ls.length = 2) :
    quotDefEq.lhs.instL ls
      = mkLams ((VExpr.peelLams quotDefEq.lhs).1.map (VExpr.instL ls))
          ((VExpr.const ``Quot.lift ls).mkApp
            (quotLiftArgs ++ [(VExpr.const ``Quot.mk [ls.getD 0 .zero]).mkApp quotMkArgs])) := by
  have h := congrArg (VExpr.instL ls) (VExpr.mkLams_peelLams quotDefEq.lhs)
  rw [VExpr.instL_mkLams] at h
  rw [← h, instL_peelLams_quotDefEq_lhs hlen]

/-- The two sides share their λ-telescope, so a single `Δ` serves both — which `extra_pat`
requires and the `vdefeq` elaborator happens to deliver. -/
theorem instL_quotDefEq_rhs {ls : List VLevel} :
    quotDefEq.rhs.instL ls
      = mkLams ((VExpr.peelLams quotDefEq.lhs).1.map (VExpr.instL ls))
          ((VExpr.bvar 2).mkApp [.bvar 0]) := by
  have h := congrArg (VExpr.instL ls) (VExpr.mkLams_peelLams quotDefEq.rhs)
  rw [VExpr.instL_mkLams] at h
  rw [← h]
  rfl

/-! ## `extra_pat`, one rule shape at a time -/

/-! ## The quotient rule's pattern, datum and check

`Theory/Quot.lean`'s rule is `fun α r β f c a => Quot.lift α r β f c (Quot.mk r a) ≡ f a`.
Its λ-peeled left-hand side is `iota`-shaped — measured, not inferred: six binders, a
six-long recursor spine and a three-long major-premise spine, so the pattern is
`SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3`.  But it comes from no `VInductDecl'`, and
`Pat.iota` cannot be bent to fit it because `Lean.mkRecName n = ``Quot.lift` is impossible
(`Name.str` injectivity).  Hence a third constructor.

This is `PLAN.md`'s "`extra_pat` is unsatisfiable" finding one layer down: λ-peeling fixed
the *shape* mismatch, but the quot pattern's *provenance* was never given a home. -/

/-- The quotient rule's pattern. -/
def quotPat : Pattern := (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern

/-- The quotient rule's right-hand side, `f a`.

`f` is the matched *recursor* argument at index 3 of 5, whose path is `some none`
(`Pattern.argPath`'s outermost `.var` holds the last argument), and `a` is the matched
*constructor* argument at index 2 of 3, reached as `drop 2` of that side's paths.  The head
is therefore a matched argument, not a closed term — which is exactly why `iotaRHS` was
generalised to `spineRHS`. -/
def quotRHS : quotPat.RHS :=
  spineRHS ``Quot.lift ``Quot.mk 5 3 (Pattern.RHS.var (Sum.inl (some none))) 0 2

/-- The quotient rule's check.  **Not `Check.true`** — each clause exists for a specific
`pat_wf` obligation, and `Theory/Typing/PatternDecode.lean`'s header explains why dropping
them would make `pat_wf` unprovable by anyone rather than merely unproved:

* the two `defeq` clauses (`np = 2`) pair the recursor leaf's first two arguments with the
  constructor leaf's — `α` and `r`.  Both leaves bind them, and an arbitrary match
  `Quot.lift α r β f c (Quot.mk α' r' a)` would otherwise fire the rule with `r ≠ r'`, at
  which point `f a` need not even be well-typed.  In the rule itself they are literally the
  same variables (`bvar 5` and `bvar 4` on both sides), so the clauses hold by reflexivity
  where `extra_pat` discharges them.
* no index clauses (`k = 5`, `computed = []`): `Quot` has no indices, so
  `(argPaths _ 5).drop 5` is empty and the block is vacuous.
* the level clause `(0, 0)`: the rule stores `Quot.lift.{p0, p1}` against `Quot.mk.{p0}`, so
  `pat_wf` must bridge a matched `Quot.mk.{u'}` to the `Quot.mk.{u}` the left-hand side
  expects, which needs `u ≈ u'`. -/
def quotCheck : quotPat.Check :=
  iotaCheck ``Quot.lift ``Quot.mk 5 3 2 5 [] [(0, 0)]

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
      -- F3.  Recorded because `Pat.isCtorLeaf_piArity` has to reconcile the pattern's
      -- constructor arity, which `iotaPat` states as `D.np + |C.fields|`, with the Π-count of
      -- the *stored* type, which binds `C.params`.  Every construction site holds it
      -- (`VEnv.RuleShape.iota` carries it, from `VIndCtor.WF.params_len`).
      C.params.length = D.np →
      Pat env (D.iotaPat T C) (D.iotaRHSOf j q T C h, D.iotaCheckOf T C hargs)
  /-- The quotient rule.  `env.constants ``Quot.lift` is not decoration: it is what
  `Pat.quotLift_ne_ctor` needs, exactly as `Pat.iota`'s two constant fields feed
  `rec_ne_ctor`.

  `Quot.mk`'s constant was deliberately *not* recorded here for as long as nothing consumed
  it.  `Pat.isCtorLeaf_piArity` now does — it reads every constructor leaf's arity off the
  stored type, and `Quot.mk` is a constructor leaf — so the field is added.  The earlier
  absence was correct at the time and is exactly the discipline the module docstring asks
  for: a field with no consumer hides which premises are load-bearing. -/
  | quot : env.defeqs quotDefEq → env.constants ``Quot.lift = some quotLiftConst →
      env.constants ``Quot.mk = some quotMkConst →
      Pat env quotPat (quotRHS, quotCheck)

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

/-- No recursor name is `Quot.lift` or `Quot.mk`: `mkRecName n` ends in the segment `"rec"`.
Pure `Name.str` injectivity — no environment, no provenance. -/
theorem mkRecName_ne_quotLift (n : Lean.Name) : Lean.mkRecName n ≠ ``Quot.lift := by
  intro h; simp [Lean.mkRecName] at h

theorem mkRecName_ne_quotMk (n : Lean.Name) : Lean.mkRecName n ≠ ``Quot.mk := by
  intro h; simp [Lean.mkRecName] at h

/-- `Quot.lift` is never a registered constructor's name.  Same argument as `rec_ne_ctor`,
and it needs the constants for the same reason: under its binders `Quot.lift`'s stored type
is a `bvar` (its result is the motive-free `β`), while a constructor's is `I p args`, a
`const`. -/
theorem quotLift_ne_ctor {env : VEnv} {D : VInductDecl'} {j : Nat} {C : VIndCtor}
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩) :
    (``Quot.lift : Lean.Name) ≠ C.name := fun h => by
  rw [h, hctor, Option.some_inj] at hlift
  have h2 := congrArg VExpr.piBodyHead (congrArg VConstant.type hlift)
  rw [C.piBodyHead_type D j, show VExpr.piBodyHead quotLiftConst.type = .bvar 3 from rfl] at h2
  exact absurd h2 (by nofun)

/-! ## `RuleShape`: what a rule of a well-formed environment looks like

`extra_pat` quantifies over an arbitrary `df` with `env.defeqs df` and must produce a `Pat`,
so it needs to know that `df` is a δ-rule, the quotient rule, or an ι-rule — together with
the data each `Pat` constructor asks for.

**This is the one piece of design §7.7's `VEnv.Sig` that survives.**  The key invariants of
`Theory/Typing/DeltaUnique.lean` replaced `Sig`'s `kind`, `sound` and `coherent`; `Sig.defeqs`
— "every defeq is a δ-rule of a `def`, an ι-rule of a `rec`, or the quot rule" — is real and
cannot be routed around, because nothing else can tell `extra_pat` what shape a rule has.

It is also the natural home for the two families of side conditions `Pat` needs, both of
which are facts about "what a rule in a well-formed environment looks like": closedness of
the δ-value and of `iotaLam`, and `C.args.length = T.indices.length`. -/

/-- Closedness of a `def`'s value: it is typed in the empty context. -/
theorem VDefVal.value_closed {env : VEnv} {ci : VDefVal} (henv : env.Ordered) (h : ci.WF env) :
    ci.value.Closed := (h.closedN' henv.closed trivial).1

/-- Closedness of `iotaLam`: `iotaLam_hasType` types it in the empty context. -/
theorem VInductDecl'.iotaLam_closed {env : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (hI : D.IotaCtx env) {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) (hj : j < D.nm) (hC : C ∈ T.ctors)
    (hqC : D.ctorsAll[q]? = some (j, C)) : (D.iotaLam q C).Closed :=
  ((VInductDecl'.iotaLam_hasType hI hT hj hC hqC).closedN' henv.closed trivial).1

/-- Closedness of each result index abstracted over the constructor's binders.  Read off the
constructor's *stored type*, which is `∀ params fields, I_j p args` — so its telescope and
its arguments are closed together, and neither needs a separate argument. -/
theorem VIndCtor.args_closed {env : VEnv} {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} (henv : env.Ordered) (hC : C.WF env D j T) :
    ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed := by
  obtain ⟨u, hty⟩ := hC.isType henv
  have h0 := (hty.closedN' henv.closed trivial).1
  rw [VIndCtor.type, VExpr.closedN_mkPi, VIndCtor.canonResult, VInductDecl'.tyApp,
    VExpr.closedN_mkApp] at h0
  intro a ha
  exact VExpr.closedN_mkLams.2 ⟨h0.1, h0.2.2 a (List.mem_append_right _ ha)⟩

/-- **Every rule of a well-formed environment has one of three shapes**, carrying exactly what
the corresponding `Pat` constructor asks for. -/
inductive VEnv.RuleShape (env : VEnv) : VDefEq → Prop
  | delta (ci : VDefVal) : ci.value.Closed → RuleShape env ci.toDefEq
  | quot : env.constants ``Quot.lift = some quotLiftConst →
      env.constants ``Quot.mk = some quotMkConst → RuleShape env quotDefEq
  /-- `args_len` is the R3 field: `iotaPat` reports the recursor arity as
  `np + nm + nmin + T.indices.length` while the rule's spine carries `|C.args|` index
  arguments, and nothing in `Pat.iota`'s data relates them.  It is discharged from
  `VIndCtor.WF.args_len` in `WF'.ruleShape` below; the obligation lands on whoever builds a
  `RuleShape`, it does not disappear.

  The last five premises are the **staging data**: the environments the block was
  declared over, together with `env₃ ≤ env`.  They are what `VInductDecl'.WF.recCtx` needs,
  and `RuleShape.iotaCtx` below turns them into `D.IotaCtx env` — which is what the index
  clauses of `extra_pat` need in order to reach `VInductDecl'.onCtxIota`.

  **Why not carry `D.IotaCtx env` directly.**  `RuleShape.mono` would then need an
  `IotaCtx.mono`, and none exists — `IotaCtx` is not monotone in `env` (`RecCtx.ordered`
  is, but `VIndCtor.WF.params_eq` and friends are monotone only because *every* field of
  `RecCtx` happens to be, which is a theorem nobody has stated).  The staging data is
  monotone for free: only the last premise mentions `env`, and it is an `≤`.  This works
  because `WF.recCtx`'s signature already takes `env₂ ≤ env₃` and `env₃.Ordered` and
  concludes `RecCtx env₃`: the monotonicity is built into the constructor rather than
  stated as a lemma, which is why no name or shape search finds it. -/
  | iota {env₀ env₁ env₂ env₃ : VEnv}
      (D : VInductDecl') (j q : Nat) (T : VIndType) (C : VIndCtor) :
      (D.iotaLam q C).Closed →
      (∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed) →
      C.args.length = T.indices.length →
      C.params.length = D.np →
      D.types[j]? = some T → C ∈ T.ctors →
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      D.WF env₀ → env₀.addIndTypes D = some env₁ → env₁.addIndCtors D = some env₂ →
      env₂.addIndRecs D = some env₃ → env₃ ≤ env →
      RuleShape env (D.iotaRule j q C)

theorem VEnv.RuleShape.mono {env env' : VEnv} (hle : env ≤ env') {df} :
    env.RuleShape df → env'.RuleShape df
  | .delta ci h => .delta ci h
  | .quot h h' => .quot (hle.constants h) (hle.constants h')
  | .iota D j q T C h1 h2 h3 h8 h4 h5 h6 h7 hD s1 s2 s3 s4 =>
      .iota D j q T C h1 h2 h3 h8 h4 h5 (hle.constants h6) (hle.constants h7)
        hD s1 s2 s3 (s4.trans hle)

/-- **The staging data, cashed in.**  `WF.recCtx` gives `RecCtx env` from any environment
above `env₂`, and `addIndRecs` supplies the recursor constants; together that is exactly
`IotaCtx env`.  The only thing not carried by `RuleShape` is `env.Ordered`, which every
consumer holds anyway (`VEnv.WF.ordered`). -/
theorem VInductDecl'.iotaCtx_of_staged {env env₀ env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (hD : D.WF env₀) (s1 : env₀.addIndTypes D = some env₁)
    (s2 : env₁.addIndCtors D = some env₂) (s3 : env₂.addIndRecs D = some env₃)
    (s4 : env₃ ≤ env) : D.IotaCtx env where
  toRecCtx := hD.recCtx s1 s2 ((VEnv.addIndRecs_le s3).trans s4) henv
  recConsts j T hT := s4.constants <|
    VEnv.addConstList_constants s3 (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
      (List.mem_map_of_mem (List.mk_mem_zipIdx_iff_getElem?.2 hT))

/-! ### The four substantial arms

Separate lemmas rather than `cases` branches, so that unification fixes each step's data
instead of the proof depending on the order in which `VDecl.WF`'s auto-bound implicits are
generalised — the same reason `WF'.keys` is written this way. -/

theorem VEnv.ruleShape_def {env env' : VEnv} {ci : VDefVal} (henv : env.Ordered)
    (hci : ci.WF env) (h : env.addConst ci.name ci.toVConstant = some env')
    (ih : ∀ df, env.defeqs df → env.RuleShape df) :
    ∀ df, (env'.addDefEq ci.toDefEq).defeqs df → (env'.addDefEq ci.toDefEq).RuleShape df := by
  intro df hdf
  rcases (hdf : _ ∨ _) with rfl | hdf
  · exact .delta _ (VDefVal.value_closed henv hci)
  · rw [VEnv.addConst_defeqs h] at hdf
    exact (ih df hdf).mono ((VEnv.addConst_le h).trans VEnv.addDefEq_le)

theorem VEnv.ruleShape_unsafeDef {env env' : VEnv} {cis : List VDefVal} (henv : env.Ordered)
    (hcon : ∀ ci ∈ cis, ci.toVConstant.WF env) (h : env.addConsts cis = some env')
    (hval : ∀ ci ∈ cis, ci.WF env') (ih : ∀ df, env.defeqs df → env.RuleShape df) :
    ∀ df, (env'.addDefEqs cis).defeqs df → (env'.addDefEqs cis).RuleShape df := by
  have henv₁ := VEnv.addConsts_ordered henv hcon h
  intro df hdf
  rcases VEnv.addDefEqs_defeqs hdf with ⟨ci, hci, rfl⟩ | hdf
  · exact .delta _ (VDefVal.value_closed henv₁ (hval ci hci))
  · rw [VEnv.addConsts_defeqs h] at hdf
    exact (ih df hdf).mono ((VEnv.addConsts_le h).trans VEnv.addDefEqs_le)

theorem VEnv.ruleShape_quot {env env' : VEnv} (h : env.addQuot = some env')
    (ih : ∀ df, env.defeqs df → env.RuleShape df) :
    ∀ df, env'.defeqs df → env'.RuleShape df := by
  obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := VEnv.addQuot_stages h
  have hlift : e4.constants ``Quot.lift = some quotLiftConst :=
    (VEnv.addConst_le h4).constants (VEnv.addConst_self h3)
  have hmk : e4.constants ``Quot.mk = some quotMkConst :=
    ((VEnv.addConst_le h3).trans (VEnv.addConst_le h4)).constants (VEnv.addConst_self h2)
  intro df hdf
  rcases (hdf : _ ∨ _) with rfl | hdf
  · exact .quot hlift hmk
  · rw [VEnv.addConst_defeqs h4, VEnv.addConst_defeqs h3, VEnv.addConst_defeqs h2,
      VEnv.addConst_defeqs h1] at hdf
    refine (ih df hdf).mono (VEnv.LE.trans ?_ VEnv.addDefEq_le)
    exact ((VEnv.addConst_le h1).trans (VEnv.addConst_le h2)).trans
      ((VEnv.addConst_le h3).trans (VEnv.addConst_le h4))

theorem VEnv.ruleShape_induct {env env' : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (hdecl : D.WF env) (h : env.addInduct' D = some env')
    (ih : ∀ df, env.defeqs df → env.RuleShape df) :
    ∀ df, env'.defeqs df → env'.RuleShape df := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := VEnv.addInduct'_stages h
  have hI := hdecl.iotaCtx henv h1 h2 h3
  have he1 := VInductDecl'.addIndTypes_ordered henv hdecl h1
  have hle : env ≤ e3 := ((VEnv.addConstList_le h1).trans (VEnv.addConstList_le h2)).trans
    (VEnv.addConstList_le h3)
  intro df hdf
  rcases VEnv.addDefEqList_mem _ hdf with hdf | hdf
  · obtain ⟨j, q, C, hqC, rfl⟩ := VInductDecl'.mem_iotaRules hdf
    have hCall : (j, C) ∈ D.ctorsAll := List.mem_of_getElem? hqC
    obtain ⟨T, hT, hCT⟩ := VInductDecl'.mem_ctorsAll hCall
    have hj : j < D.nm := by
      obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 hT; exact hj
    have hCwf := hdecl.ctors e1 h1 j T hT C hCT
    exact .iota D j q T C
      (VInductDecl'.iotaLam_closed hI.toRecCtx.ordered hI hT hj hCT hqC)
      (VIndCtor.args_closed he1 hCwf) hCwf.args_len hCwf.params_len hT hCT
      ((VEnv.addDefEqList_le _ _).constants (VEnv.addConstList_constants h3 _
        (List.mem_map.2 ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)))
      ((VEnv.addDefEqList_le _ _).constants ((VEnv.addConstList_le h3).constants
        (VEnv.addConstList_constants h2 _ (List.mem_map.2 ⟨(j, C), hCall, rfl⟩))))
      hdecl h1 h2 h3 (VEnv.addDefEqList_le _ _)
  · rw [VEnv.addConstList_defeqs h3, VEnv.addConstList_defeqs h2,
      VEnv.addConstList_defeqs h1] at hdf
    exact (ih df hdf).mono (hle.trans (VEnv.addDefEqList_le _ _))

/-- **`Params`' half of `Sig.defeqs`.**  Seven arms, same shape as `WF'.keys`. -/
theorem VEnv.WF'.ruleShape {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ df, env.defeqs df → env.RuleShape df := by
  induction H with
  | empty => nofun
  | @decl _ _ _ _ hd hds ih =>
    have henv := VEnv.WF.ordered ⟨_, hds⟩
    cases hd with
    | «axiom» _ h | «opaque» _ h =>
      exact fun df hdf => (ih df (VEnv.addConst_defeqs h ▸ hdf)).mono (VEnv.addConst_le h)
    | «example» _ => exact ih
    | «def» hci h => exact VEnv.ruleShape_def henv hci h ih
    | unsafeDef hcon h hval => exact VEnv.ruleShape_unsafeDef henv hcon h hval ih
    | quot _ h => exact VEnv.ruleShape_quot h ih
    | induct hdecl h => exact VEnv.ruleShape_induct henv hdecl h ih

theorem VEnv.WF.ruleShape {env : VEnv} (h : env.WF) {df} (hdf : env.defeqs df) :
    env.RuleShape df := WF'.ruleShape h.choose_spec df hdf

/-- **`Params.pat_simple`.**  Immediate from the shape of the family: every constructor's
pattern index is a `SimplePattern.toPattern` by construction. -/
theorem Pat.simple {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} (h : Pat env p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases h with
  | delta => exact ⟨.defn _, rfl⟩
  | iota => exact ⟨.iota .., rfl⟩
  | quot => exact ⟨.iota .., rfl⟩

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

/-- **What a registered pattern's two leaves supply.**  Both `pat_app_*` fields need exactly
two facts about the recursor leaf `R`, the constructor leaf `K` and the recursor arity `M`:
that `R` is never another pattern's `K`, and that `R` determines `M`.  Naming the pair keeps
the two `Pat` shapes from being spelled out four times in each field. -/
inductive Pat.Leaves (env : VEnv) : Lean.Name → Lean.Name → Nat → Prop
  | iota (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor) :
      D.types[j]? = some T →
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      Leaves env (Lean.mkRecName T.name) C.name (D.np + D.nm + D.nmin + T.indices.length)
  | quot : env.constants ``Quot.lift = some quotLiftConst →
      Leaves env ``Quot.lift ``Quot.mk 5

/-- No pattern's recursor leaf is any pattern's constructor leaf. -/
theorem Pat.Leaves.rec_ne_ctor {env : VEnv} {R K M R' K' M'}
    (h : Pat.Leaves env R K M) (h' : Pat.Leaves env R' K' M') : R ≠ K' := by
  cases h with
  | iota D j T C hTj hrec hctor =>
    cases h' with
    | iota D' j' T' C' hTj' hrec' hctor' => exact _root_.Lean4Lean.rec_ne_ctor hTj hrec hctor'
    | quot => exact mkRecName_ne_quotMk _
  | quot hlift =>
    cases h' with
    | iota D' j' T' C' hTj' hrec' hctor' => exact quotLift_ne_ctor hlift hctor'
    | quot => exact by decide

/-- A recursor leaf determines its pattern's arity. -/
theorem Pat.Leaves.arity {env : VEnv} {R K M R' K' M'}
    (h : Pat.Leaves env R K M) (h' : Pat.Leaves env R' K' M') (hR : R = R') : M = M' := by
  cases h with
  | iota D j T C hTj hrec hctor =>
    cases h' with
    | iota D' j' T' C' hTj' hrec' hctor' => exact Pat.rec_arity_uniq hTj' hTj hrec' hrec hR
    | quot => exact absurd hR (mkRecName_ne_quotLift _)
  | quot hlift =>
    cases h' with
    | iota D' j' T' C' hTj' hrec' hctor' => exact absurd hR.symm (mkRecName_ne_quotLift _)
    | quot => rfl

/-- A δ-pattern has no `.app` subpattern, so both `Pat`s in the `pat_app_*` fields are ι or
quot; either way the `.app` subpattern is the whole pattern, and its leaves are `Leaves`. -/
theorem Pat.app_sub_inv {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} {p₁ p₂}
    (h : Pat env p r) (hs : Subpattern (.app p₁ p₂) p) :
    ∃ R K M N, p₁ = (Pattern.const R).varN M ∧ p₂ = (Pattern.const K).varN N ∧
      Pat.Leaves env R K M := by
  cases h with
  | delta => exact absurd hs.const_inv nofun
  | @iota D j q T C _ _ hTj hCT hdf hrec hctor =>
    obtain ⟨rfl, rfl⟩ := Pat.app_sub_iota hs
    exact ⟨_, _, _, _, rfl, rfl, .iota D j T C hTj hrec hctor⟩
  | quot hdf hlift =>
    rw [quotPat, SimplePattern.toPattern] at hs
    cases hs with
    | refl => exact ⟨_, _, _, _, rfl, rfl, .quot hlift⟩
    | appL h => exact absurd h Subpattern.not_app_varN
    | appR h => exact absurd h Subpattern.not_app_varN

/-- **`Params.pat_app_l_uniq`.**  One pattern's recursor chain, cut short, cannot intersect
another's: the same recursor leaf forces the same arity (`Pat.Leaves.arity`), and the cut
chain is strictly shorter. -/
theorem Pat.app_l_uniq {env : VEnv} {p p' p₁ p₂ p₁' p₂' p₃ : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    (h : Pat env p r) (h' : Pat env p' r') (hs : Subpattern (.app p₁ p₂) p)
    (hs' : Subpattern (.app p₁' p₂') p') (hv : Subpattern (.var p₃) p₁) :
    p₁'.inter p₃ = none := by
  obtain ⟨R, K, M, N, rfl, rfl, hL⟩ := h.app_sub_inv hs
  obtain ⟨R', K', M', N', rfl, rfl, hL'⟩ := h'.app_sub_inv hs'
  obtain ⟨k, hk, hkk⟩ := hv.varN_const_inv
  cases k with
  | zero => exact absurd hkk nofun
  | succ k =>
    cases (Pattern.var.injEq .. ▸ hkk : _ = _)
    cases hn : ((Pattern.const R').varN M').inter ((Pattern.const R).varN k) with
    | none => rfl
    | some x =>
      obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hn
      have := hL.arity hL' hR.symm
      omega

/-- **`Params.pat_app_uniq`.**  One pattern's recursor leaf against another's constructor
leaf: `Pat.Leaves.rec_ne_ctor`. -/
theorem Pat.app_uniq {env : VEnv} {p p' p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    (h : Pat env p r) (h' : Pat env p' r') (hs : Subpattern (.app p₁ p₂) p)
    (hs' : Subpattern (.app p₁' p₂') p')
    (h3 : Subpattern p₃ p₁) (h3' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  obtain ⟨R, K, M, N, rfl, rfl, hL⟩ := h.app_sub_inv hs
  obtain ⟨R', K', M', N', rfl, rfl, hL'⟩ := h'.app_sub_inv hs'
  obtain ⟨k, -, rfl⟩ := h3.varN_const_inv
  obtain ⟨k', -, rfl⟩ := h3'.varN_const_inv
  cases hn : ((Pattern.const R).varN k).inter ((Pattern.const K').varN k') with
  | none => rfl
  | some x =>
    obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hn
    exact absurd hR (hL.rec_ne_ctor hL')

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

/-- A δ-rule's head is none of the quotient rule's leaves: `KeyHeadDelta` identifies the two
rules, and a δ-rule's left-hand side is a bare constant while `quotDefEq`'s is a lam. -/
theorem Pat.deltaHead_ne_quot {env : VEnv} (henv : env.WF)
    (hdf : env.defeqs quotDefEq) {c : Lean.Name} {u : Nat} {v t : VExpr}
    (hdf' : env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩) (hmem : c ∈ quotDefEq.key) :
    False :=
  VEnv.not_isDeltaRule_quotDefEq c
    (henv.keyHeadDelta _ _ c hdf' hdf VEnv.IsDeltaRule.const hmem ▸ VEnv.IsDeltaRule.const)

/-- **`Params.pat_uniq`**.  See the table in the section header for which lemma closes which
case. -/
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
    | quot => exact absurd hi Pattern.inter_app_const
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
      | quot hdf' hlift' =>
        obtain ⟨x, y, hx, hy, rfl⟩ := Pattern.inter_app_app hi
        obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
        exact absurd hR.symm (mkRecName_ne_quotLift _)
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
        | quot => exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hx
          have := Pat.rec_arity_uniq hTj hTj' hrec hrec' hR
          omega
        | quot hdf' hlift' =>
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR.symm (mkRecName_ne_quotLift _)
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
        | quot => exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, hM, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (rec_ne_ctor hTj' hrec' hctor)
        | quot hdf' hlift' =>
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (quotLift_ne_ctor hlift' hctor)
  | quot hdf hlift =>
    simp only [quotPat, SimplePattern.toPattern] at hs ⊢
    cases hs with
    | refl =>
      cases h' with
      | delta => exact absurd hi Pattern.inter_const_app
      | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
        simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
        obtain ⟨x, y, hx, hy, rfl⟩ := Pattern.inter_app_app hi
        obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
        exact absurd hR (mkRecName_ne_quotLift _)
      | quot => exact ⟨rfl, rfl, HEq.rfl⟩
    | appL hsl =>
      obtain ⟨k, hk, rfl⟩ := hsl.varN_const_inv
      cases k with
      | zero =>
        cases h' with
        | @delta c' u' v' t' hv' hdf' =>
          obtain ⟨rfl, -⟩ := Pattern.inter_const_const hi
          exact absurd (Pat.deltaHead_ne_quot henv hdf hdf'
            (by rw [VEnv.key_quotDefEq]; exact List.mem_cons_self)) not_false
        | iota =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          exact absurd hi Pattern.inter_app_const
        | quot => exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (mkRecName_ne_quotLift _)
        | quot =>
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨-, hM, -⟩ := Pattern.inter_varN_const hx
          omega
    | appR hsr =>
      obtain ⟨k, hk, rfl⟩ := hsr.varN_const_inv
      cases k with
      | zero =>
        cases h' with
        | @delta c' u' v' t' hv' hdf' =>
          obtain ⟨rfl, -⟩ := Pattern.inter_const_const hi
          exact absurd (Pat.deltaHead_ne_quot henv hdf hdf'
            (by rw [VEnv.key_quotDefEq]; exact List.mem_cons_of_mem _ List.mem_cons_self))
            not_false
        | iota =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          exact absurd hi Pattern.inter_app_const
        | quot => exact absurd hi Pattern.inter_app_const
      | succ k =>
        cases h' with
        | delta => exact absurd hi Pattern.inter_const_var
        | @iota D' j' q' T' C' hcl' hargs' hTj' hCT' hdf' hrec' hctor' =>
          simp only [VInductDecl'.iotaPat_eq, SimplePattern.toPattern] at hi
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (mkRecName_ne_quotMk _)
        | quot =>
          obtain ⟨x, hx, rfl⟩ := Pattern.inter_app_var hi
          obtain ⟨hR, -, -⟩ := Pattern.inter_varN_const hx
          exact absurd hR (by decide)

/-! ### The ι-rule's substitution identity

The ι index clauses compare the recursor's index arguments — stored in the rule as
`(atRec a).liftN off nf` — against `iotaComputed`'s entries, which are `mkLams tel a` applied
to the *matched constructor arguments*.  β-reducing the latter (`VEnv.IsDefEq.betaMkLams`)
leaves an `instAll`, and these two lemmas say that `instAll` is the `liftN` the rule already
performed.

The statement was machine-checked on three probes *before* being proved: a hand derivation
of the offsets gave `bvar 2` where the identity needs `bvar 3`, because `instVar` lifts its
argument by `k` at `i = k`, which is easy to miss.  The check is cheap and it catches the
error in both directions — a false statement believed true, and a true statement about to be
abandoned as false. -/

/-- Substituting a *displaced* variable block: the `n` variables at levels `k … k+n-1`
replaced by the run sitting `R` binders above the bottom is exactly a lift by `R` above `k`.

Induction on `X`, not on `n`: the substituted list is fixed and only `k` moves, which is what
makes the binder cases line up.  Inducting on `n` fails — the intermediate term is no longer
closed at the level the induction hypothesis wants. -/
theorem VExpr.instAll_bvars_shift : ∀ {X : VExpr} {k n R : Nat}, X.ClosedN (k + n) →
    instAll X (bvars R n) k = X.liftN R k := by
  intro X
  induction X with
  | bvar i =>
    intro k n R h
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [VExpr.instAll_bvar_lt' hik]
      simp [VExpr.liftN, liftVar, hik]
    · have hlt : i < k + n := h
      rw [VExpr.instAll_bvar_get (t := k + n - i - 1) (a := .bvar (R + i - k))
        (by rw [VExpr.getElem?_bvars, if_pos (by omega)]; congr 2; omega) (by simp; omega)]
      simp only [VExpr.liftN]
      congr 1
      rw [liftVar_le (Nat.zero_le _), liftVar_le hik]
      omega
  | sort => intro k n R h; simp [VExpr.instAll_sort, VExpr.liftN]
  | const => intro k n R h; simp [VExpr.instAll_const, VExpr.liftN]
  | app f a ih1 ih2 =>
    intro k n R h
    rw [VExpr.instAll_app, ih1 h.1, ih2 h.2]; rfl
  | lam A b ih1 ih2 =>
    intro k n R h
    rw [VExpr.instAll_lam, ih1 h.1, ih2 (show b.ClosedN (k+1+n) by
      have := h.2; simpa [Nat.add_right_comm] using this)]
    rfl
  | forallE A b ih1 ih2 =>
    intro k n R h
    rw [VExpr.instAll_forallE, ih1 h.1, ih2 (show b.ClosedN (k+1+n) by
      have := h.2; simpa [Nat.add_right_comm] using this)]
    rfl

/-- **The ι-rule's substitution identity.**  Substituting a constructor telescope's own
variables — the parameters displaced `off` binders up by the motives and minors, the fields
at the bottom — is exactly `liftN off nf`, which is how the rule stores them. -/
theorem VExpr.instAll_bvars₂ {X : VExpr} {np nf off : Nat} (h : X.ClosedN (nf + np)) :
    instAll X (bvars (nf + off) np ++ bvars 0 nf) 0 = X.liftN off nf := by
  rw [← VExpr.map_liftN_bvars_lo (m := nf) (lo := off) (n := np) (Nat.zero_le _),
    VExpr.instAll_map_liftN_bvars (by simpa using h),
    VExpr.instAll_bvars_shift (by simpa using h)]

/-- The telescope version of `instAll_bvars_shift`: entry `i` is closed at `k + i + n`, so
each is shifted independently.  This is what turns the ι-rule's field telescope, saturated at
the parameter variables, into the lifted copy the rule's own context carries. -/
theorem VExpr.instAllTele_bvars_shift : ∀ {As : List VExpr} {k n R : Nat},
    VExpr.ClosedTele As (k + n) → instAllTele As (bvars R n) k = liftTele R As k
  | [], _, _, _, _ => rfl
  | A :: As, k, n, R, h => by
    rw [VExpr.instAllTele_cons, VExpr.liftTele_cons, VExpr.instAll_bvars_shift h.1,
      instAllTele_bvars_shift (As := As) (k := k + 1) (n := n) (R := R)
        (by have := h.2; simpa [Nat.add_right_comm] using this)]

/-- A spine's entries are individually well-typed.  `HasArgs` threads the substitution, which
hides the plain fact that each argument has *some* type in the ambient context. -/
theorem VEnv.HasArgs.hasType_of_mem {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As as : List VExpr}, env.HasArgs U Γ As as → ∀ a ∈ as, ∃ A, env.HasType U Γ a A
  | _, _, .nil => by simp
  | _, _, .cons h1 h2 => by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, h1⟩
    · exact h2.hasType_of_mem a ha

/-- `HasArgs` across a definitionally equal context.  Pure bookkeeping — it is `HasType`
entrywise — but without it the F3 transport (`C.params` against `D.params`) cannot be done on
a spine, only on a single application as `ctorApp'_hasType` does it. -/
theorem VEnv.HasArgs.defeqDFC {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (henv : env.Ordered) (W : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As as : List VExpr}, env.HasArgs U Γ₁ As as → env.HasArgs U Γ₂ As as
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h1.defeqDFC henv W) (h2.defeqDFC henv W)

/-! ### The ι-rule's shape after level instantiation -/

/-- The ι-rule's left-hand side after level instantiation: a recursor spine whose last
argument is a constructor spine — exactly `matches_iota_paths`' shape. -/
theorem VInductDecl'.instL_iotaLhs (D : VInductDecl') (j : Nat) (C : VIndCtor)
    {ls : List VLevel} (hlen : ls.length = D.recUvars) :
    (D.iotaLhs j C).instL ls
      = (VExpr.const (Lean.mkRecName (D.types.getD j default).name) ls).mkApp
          ((bvars (C.fields.length + (D.nm + D.nmin)) D.np
              ++ bvars (C.fields.length + D.nmin) D.nm ++ bvars C.fields.length D.nmin
              ++ C.args.map fun a =>
                   ((D.atRec a).liftN (D.nm + D.nmin) C.fields.length).instL ls)
            ++ [(VExpr.const C.name (D.selfLvls.map (VLevel.inst ls))).mkApp
                  (bvars (C.fields.length + (D.nm + D.nmin)) D.np
                    ++ bvars 0 C.fields.length)]) := by
  rw [VInductDecl'.iotaLhs, VExpr.instL_mkApp]
  simp only [VExpr.instL, VLevel.map_inst_params hlen, List.map_append, List.map_map,
    VExpr.map_instL_bvars, List.map_cons, List.map_nil, VInductDecl'.ctorApp',
    VExpr.instL_mkApp]
  rfl

/-- The recursor's spine is one contiguous `bvars` run followed by the index arguments: the
parameter, motive and minor blocks sit immediately above the fields. -/
theorem VInductDecl'.iotaLhs_args_split (D : VInductDecl') (C : VIndCtor) (rest : List VExpr) :
    bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars (C.fields.length + D.nmin) D.nm
        ++ bvars C.fields.length D.nmin ++ rest
      = bvars C.fields.length (D.np + D.nm + D.nmin) ++ rest := by
  rw [VExpr.bvars_add₃, ← Nat.add_assoc]

/-- **The parameter-clause helper.**  If two matched lists have the same image, every zipped
pair maps to the same term.  Simultaneous induction, so no indexing — the structural form of
what would otherwise be a positional argument about `take` and `zip`. -/
theorem List.zip_map_eq {α β : Type _} {P : List α} {Q : List β}
    {f : α → VExpr} {g : β → VExpr} (h : P.map f = Q.map g) :
    ∀ xy ∈ P.zip Q, f xy.1 = g xy.2 := by
  induction P generalizing Q with
  | nil => simp
  | cons a P ih =>
    cases Q with
    | nil => simp
    | cons b Q =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [List.zip_cons_cons]
      intro xy hxy
      rcases List.mem_cons.1 hxy with rfl | hxy
      · exact h.1
      · exact ih h.2 xy hxy

/-- The relational form of `List.zip_map_eq`, for the index block — where the two sides are
not equal, only definitionally so. -/
theorem List.forall₂_map_map {α : Type _} {l : List α} {F G : α → VExpr}
    {R : VExpr → VExpr → Prop} (h : ∀ a ∈ l, R (F a) (G a)) :
    List.Forall₂ R (l.map F) (l.map G) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a (.head _)) (ih fun b hb => h b (.tail _ hb))

theorem List.zip_map_rel {α β : Type _} {P : List α} {Q : List β}
    {f : α → VExpr} {g : β → VExpr} {R : VExpr → VExpr → Prop}
    (h : List.Forall₂ R (P.map f) (Q.map g)) : ∀ xy ∈ P.zip Q, R (f xy.1) (g xy.2) := by
  induction P generalizing Q with
  | nil => simp
  | cons a P ih =>
    cases Q with
    | nil => simp
    | cons b Q =>
      simp only [List.map_cons] at h
      cases h with
      | cons hab hrest =>
        rw [List.zip_cons_cons]
        intro xy hxy
        rcases List.mem_cons.1 hxy with rfl | hxy
        · exact hab
        · exact ih hrest xy hxy

/-- `pmap` whose function ignores its proof argument only up to unfolding.  `iotaComputed`'s
entries store the closedness proof inside `RHS.fixed`, and `RHS.apply` drops it — so the
image is a plain `map`, but not syntactically. -/
theorem List.map_pmap_eq_map {α β γ : Type _} {p : α → Prop} (k : β → γ) (f : ∀ a, p a → β)
    (g : α → γ) (H : ∀ a (ha : p a), k (f a ha) = g a) :
    ∀ (l : List α) (h : ∀ a ∈ l, p a), (l.pmap f h).map k = l.map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.pmap, List.map_cons, List.map_cons, H, map_pmap_eq_map k f g H l]

/-- **`Params.extra_pat` for a δ-rule.**  No λ-peeling (the left-hand side is already a bare
constant), no check clauses, and the datum's value is the rule's own. -/
theorem Pat.extra_delta {env : VEnv} {U : Nat} {Γ : List VExpr}
    {ci : VDefVal} {ls : List VLevel} (hcl : ci.value.Closed)
    (hdf : env.defeqs ci.toDefEq) (hlen : ls.length = ci.uvars) :
    ∃ Δ L R p r m1 m2,
      (ci.toDefEq).lhs.instL ls = mkLams Δ L ∧ (ci.toDefEq).rhs.instL ls = mkLams Δ R ∧
      Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
      (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2 := by
  refine ⟨[], .const ci.name ls, ci.value.instL ls, .const ci.name,
    (deltaRHS ci.name ci.value hcl, .true), _, _, ?_, rfl, .delta hcl hdf,
    .const, trivial, rfl⟩
  show VExpr.const ci.name ((VLevel.params ci.uvars).map (VLevel.inst ls)) = _
  rw [VLevel.map_inst_params hlen]; rfl

/-- **`Params.extra_pat` for the quotient rule.**  Six binders peel off, the body matches
`quotPat`, and the two parameter clauses are reflexivity *plus* the typing layer: `α` and `r`
are literally `bvar 5` and `bvar 4` on both leaves, but each clause is still an `IsDefEqU`. -/
theorem Pat.extra_quot {env : VEnv} {U : Nat} {Γ : List VExpr} {ls : List VLevel}
    (hdf : env.defeqs quotDefEq) (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlen : ls.length = quotDefEq.uvars) :
    ∃ Δ L R p r m1 m2,
      quotDefEq.lhs.instL ls = mkLams Δ L ∧ quotDefEq.rhs.instL ls = mkLams Δ R ∧
      Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
      (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2 := by
  have hlen2 : ls.length = 2 := hlen
  obtain ⟨m1, m2, hm, hml, hmr, hpa, hpb⟩ :=
    matches_iota_paths ``Quot.lift ``Quot.mk ls [ls.getD 0 .zero] (m := 5) (n := 3)
      quotLiftArgs quotMkArgs rfl rfl
  have ea := hpa; have eb := hpb
  rw [argPaths5] at ea; rw [argPaths3] at eb
  simp only [quotLiftArgs, quotMkArgs, List.map, List.cons.injEq, and_true] at ea eb
  have hΔ : ((VExpr.peelLams quotDefEq.lhs).1.map (VExpr.instL ls)).reverse.length = 6 := by
    simp [show (VExpr.peelLams quotDefEq.lhs).1.length = 6 from rfl]
  refine ⟨_, _, _, quotPat, (quotRHS, quotCheck), m1, m2,
    instL_quotDefEq_lhs hlen2, instL_quotDefEq_rhs, .quot hdf hlift hmk, hm, ?_, ?_⟩
  · show (quotCheck).OK _ m1 m2
    rw [quotCheck, iotaCheck_OK]
    refine ⟨?_, by simp, ?_⟩
    · rw [argPaths5, argPaths3]
      simp only [List.take, List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false]
      rintro xy (rfl | rfl | ⟨⟩)
      · rw [ea.1, eb.1]; exact VEnv.isDefEqU_bvar (by omega)
      · rw [ea.2.1, eb.2.1]; exact VEnv.isDefEqU_bvar (by omega)
    · rintro ij hij
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hij
      cases hij
      rw [show (Pattern.LPath.head (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern)
          = Sum.inl (Pattern.LPath.head _) from rfl, hml,
        show iotaLeafCtor ``Quot.lift ``Quot.mk 5 3 = Sum.inr (Pattern.LPath.head _) from rfl,
        hmr]
      exact rfl
  · show _ = (quotRHS).apply m1 m2
    rw [quotRHS, spineRHS_apply hpa hpb]
    exact congrArg (fun e => e.mkApp [VExpr.bvar 0]) ea.2.2.2.1.symm

/-! ### The ι-rule's own match, and the three clause blocks it discharges -/

/-- **The index clause, at the rule's own match.**  `iotaComputed` abstracts a result index
over the constructor's whole binder telescope and re-applies it to the *matched* constructor
arguments; in the rule's own match those arguments are the rule's parameter and field
variables, so the redex β-reduces (`betaMkLams`) to the substitution `instAll_bvars₂`
identifies with the `liftN off nf` the rule stores.

Everything here is at the recursor's universe numbering and in the rule's own binder context;
`extra_pat` moves it to `ls` and over `Γ` with `IsDefEqU.instL` and `IsDefEq.weakR`.

The F3 transport is what costs: `iotaComputed`'s telescope binds `C.params` (it is read off
the constructor's *stored* type) while `iotaCtx` carries `D.params`, so the `HasArgs` for the
variable spine is built over `C.params` and moved across — the spine analogue of what
`ctorApp'_hasType` does with `appBVars₂` for a single application. -/
theorem VInductDecl'.iota_index_clause {env : VEnv} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} (henv : env.Ordered) (hR : D.RecCtx env)
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors) {a : VExpr} (ha : a ∈ C.args) :
    env.IsDefEqU D.recUvars (D.iotaCtx C).reverse
      ((D.atRec a).liftN (D.nm + D.nmin) C.fields.length)
      ((mkLams (D.atRecTele (C.params ++ C.fields.map (·.type))) (D.atRec a)).mkApp
        (bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars 0 C.fields.length)) := by
  have hCwf : VIndCtor.WF env D j T C := hR.ctors j T hT C hC
  have hΓι : OnCtx ((D.iotaCtx C).reverse) (env.IsType D.recUvars) := by
    rw [D.iotaCtx_reverse' C]; exact VInductDecl'.onCtxIota hR hT hC
  -- the F3 context defeq, at the recursor's universe numbering
  have hpar : VEnv.IsDefEqCtx env D.recUvars [] (D.atRecTele D.params).reverse
      (D.atRecTele C.params).reverse := by
    have := VEnv.IsDefEqCtx.instL (ls := D.selfLvls) D.selfLvls_wf (hCwf.params_eq.symm henv)
    simpa [VInductDecl'.atRecTele] using this
  have hAs0 : OnCtx (D.atRecTele C.params).reverse (env.IsType D.recUvars) := by
    have := D.atRec_onCtx hCwf.params_eq.isType
    rwa [VInductDecl'.atRecCtx, List.map_reverse] at this
  have hBsD : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) := by
    have := D.atRec_onCtx (hCwf.onCtxAllFields henv)
    rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this
  have hBs0 : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele C.params).reverse) (env.IsType D.recUvars) := by
    have W := hCwf.defeqCtx henv (Δ := (C.fields.map (·.type)).reverse)
      (hCwf.onCtxAllFields henv)
    have := D.atRec_onCtx ((W.symm henv).isType)
    rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this
  have hrev : (D.atRecTele (C.params ++ C.fields.map (·.type))).reverse
      = (D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele C.params).reverse := by
    rw [VInductDecl'.atRecTele_append, List.reverse_append]
  have hcc : CtxClosed ((D.atRecTele (C.params ++ C.fields.map (·.type))).reverse) := by
    rw [hrev]; exact OnCtx.ctxClosed henv hBs0
  have hOn : OnCtx ((D.atRecTele (C.params ++ C.fields.map (·.type))).reverse
      ++ (D.iotaCtx C).reverse) (env.IsType D.recUvars) :=
    OnCtx.appendR henv hΓι hcc (by rw [hrev]; exact hBs0)
  -- the body: `a` is typed under the constructor's own telescope
  obtain ⟨A, hA⟩ := hCwf.args_ty.hasType_of_mem a ha
  have hACl : (D.atRec a).ClosedN (C.fields.length + D.np) := by
    have h0 := hA.closedN henv (OnCtx.ctxClosed henv (hCwf.onCtxAllFields henv))
    simp only [List.length_append, List.length_reverse, List.length_map] at h0
    exact VExpr.ClosedN.instL h0
  have hb : env.HasType D.recUvars
      ((D.atRecTele (C.params ++ C.fields.map (·.type))).reverse ++ (D.iotaCtx C).reverse)
      (D.atRec a) (D.atRec A) := by
    have h1 := D.atRec_hasType hA
    rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at h1
    have h2 := VEnv.HasType.defeqDFC henv (hpar.append hBsD) h1
    rw [← hrev] at h2
    exact VEnv.IsDefEq.weakR henv hcc h2 _
  -- the variable spine, built over `C.params` and moved across
  have hΔlen : ((VExpr.liftTele (D.nm + D.nmin)
        (D.atRecTele (C.fields.map (·.type))) 0).reverse
      ++ D.minors.reverse ++ D.motives.reverse).length
      = C.fields.length + (D.nm + D.nmin) := by
    simp only [List.length_append, List.length_reverse, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, List.length_map, VInductDecl'.length_minors,
      VInductDecl'.length_motives]
    omega
  have hiotaR : (D.iotaCtx C).reverse
      = (VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ (D.motives.reverse ++ (D.atRecTele D.params).reverse)) := by
    simp [VInductDecl'.iotaCtx]
  have hDC : VEnv.IsDefEqCtx env D.recUvars [] ((D.iotaCtx C).reverse)
      ((VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ (D.motives.reverse ++ (D.atRecTele C.params).reverse))) := by
    have h := hpar.append (Δ := (VExpr.liftTele (D.nm + D.nmin)
        (D.atRecTele (C.fields.map (·.type))) 0).reverse
      ++ D.minors.reverse ++ D.motives.reverse)
      (by simp only [List.append_assoc]; rw [← hiotaR]; exact hΓι)
    simp only [List.append_assoc] at h
    rw [hiotaR]
    exact h
  have hP : env.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ (D.motives.reverse ++ (D.atRecTele C.params).reverse)))
      (D.atRecTele C.params) (bvars (C.fields.length + (D.nm + D.nmin)) D.np) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := D.recUvars)
      (Δ := (VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ D.minors.reverse ++ D.motives.reverse)
      (As := D.atRecTele C.params) (Γ₀ := [])
    have hPcl : VExpr.ClosedTele (D.atRecTele C.params) 0 :=
      VExpr.ClosedTele.of_onCtx (Γ := []) henv (by simpa using hAs0)
    rw [hΔlen, VInductDecl'.length_atRecTele, hCwf.params_len,
      hPcl.liftTele_eq (Nat.le_refl 0), List.append_nil] at h
    simp only [List.append_assoc] at h
    exact h
  have hFcl : VExpr.ClosedTele (D.atRecTele (C.fields.map (·.type))) D.np := by
    have := VExpr.ClosedTele.of_onCtx henv hBs0
    simpa [VInductDecl'.length_atRecTele, hCwf.params_len] using this
  have hF : env.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ (D.motives.reverse ++ (D.atRecTele C.params).reverse)))
      (VExpr.instAllTele (D.atRecTele (C.fields.map (·.type)))
        (bvars (C.fields.length + (D.nm + D.nmin)) D.np) 0) (bvars 0 C.fields.length) := by
    rw [VExpr.instAllTele_bvars_shift (by simpa using hFcl)]
    have h := VEnv.HasArgs.bvars (env := env) (U := D.recUvars) (Δ := [])
      (As := VExpr.liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0)
      (Γ₀ := D.minors.reverse ++ (D.motives.reverse ++ (D.atRecTele C.params).reverse))
    simp only [List.length_nil, Nat.zero_add, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, List.length_map, List.nil_append] at h
    rw [VExpr.liftTele_collapse₂,
      show D.nm + D.nmin + C.fields.length = C.fields.length + (D.nm + D.nmin) from by omega] at h
    exact h
  have hspine : env.HasArgs D.recUvars ((D.iotaCtx C).reverse)
      (D.atRecTele (C.params ++ C.fields.map (·.type)))
      (bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars 0 C.fields.length) := by
    rw [VInductDecl'.atRecTele_append]
    exact VEnv.HasArgs.defeqDFC henv (hDC.symm henv) (VEnv.HasArgs.append hP hF)
  have hbeta := VEnv.IsDefEq.betaMkLams henv hOn hspine hb
  rw [VExpr.instAll_bvars₂ hACl] at hbeta
  exact ⟨_, hbeta.symm⟩

/-! ### The ι-rule's own match, and the three clause blocks it discharges -/

/-- Every entry of a variable block inside the rule's telescope is a well-typed variable.
The `defeq` clauses of a rule's *own* match are between syntactically equal `bvar`s, so this
plus `List.zip_map_eq` is the whole parameter block. -/
theorem VEnv.isDefEqU_of_mem_bvars {env : VEnv} {U : Nat} {Δ Γ : List VExpr} {lo n : Nat}
    (h : lo + n ≤ Δ.length) {e : VExpr} (he : e ∈ bvars lo n) :
    env.IsDefEqU U (Δ ++ Γ) e e := by
  obtain ⟨i, hi, rfl⟩ := VExpr.mem_bvars.1 he
  exact VEnv.isDefEqU_bvar (by omega)

/-- **`Params.extra_pat` for an ι-rule.**  The rule's binder context peels off whole
(`iotaRule` stores both sides as `mkLams (iotaCtx C) _`), the body is `iotaLhs`, and
`instL_iotaLhs` puts it in `matches_iota_paths`' shape.

**`OnCtx Γ` is not needed — and the standing claim that it is, is wrong.**
`Params.extra_pat`'s docstring (`Theory/Typing/ChurchRosser.lean`, the paragraph beginning
"`hΓ` is not optional") argues: the ι index clauses β-reduce a `mkLams`, `IsDefEq.beta` needs
the function typed, typing a `mkLams` needs `OnCtx` of its telescope *over `Γ`*, and that
unfolds to include `OnCtx Γ`.  Every step of that is true and the conclusion still does not
follow, because it assumes the β-reduction is performed over `Γ`.  It need not be: the redex
is the rule's *own* left-hand side, so the reduction is done in `(D.iotaCtx C).reverse`, which
is closed, and `IsDefEq.weakR` then carries the finished `IsDefEqU` over an arbitrary `Γ` on
`CtxClosed` alone.  See `VInductDecl'.iota_index_clause`, which is stated in exactly that
closed context, and the two lines of `Pat.extra_iota` that transport it (`IsDefEqU.instL`,
then `IsDefEq.weakR`).

So: no case of `extra_pat` consumes `hΓ` — `Pat.extra_delta`, `Pat.extra_quot`,
`Pat.extra_iota` and `Pat.extra` all do without it.  The field keeps the hypothesis (it makes
the field *weaker*, hence easier for an instance, and its one caller holds it), but nobody
should infer from that docstring that an `extra_pat` proof must have `OnCtx Γ` available.
This is not a refutation of the field, only of the necessity argument for its hypothesis.

The companion claim about `pat_wf`'s own `hΓ` is a *different* argument — it goes through
`HasType.app_inv` and `H.strong henv hΓ`, which really do need a well-formed context — and is
untouched by this. -/
theorem Pat.extra_iota {env : VEnv} {U : Nat} {Γ : List VExpr}
    {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor} {ls : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env)
    (hcl : (D.iotaLam q C).Closed)
    (hargs : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed)
    (hal : C.args.length = T.indices.length) (hplen : C.params.length = D.np)
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hdf : env.defeqs (D.iotaRule j q C))
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hlsWF : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = (D.iotaRule j q C).uvars) :
    ∃ Δ L R p r m1 m2,
      (D.iotaRule j q C).lhs.instL ls = mkLams Δ L ∧
      (D.iotaRule j q C).rhs.instL ls = mkLams Δ R ∧
      Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
      (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2 := by
  have hlen : ls.length = D.recUvars := hlslen
  -- the two matched argument lists of the rule's own left-hand side
  obtain ⟨m1, m2, hm, hml, hmr, hpa, hpb⟩ :=
    matches_iota_paths (Lean.mkRecName T.name) C.name ls (D.selfLvls.map (VLevel.inst ls))
      (m := D.np + D.nm + D.nmin + T.indices.length) (n := D.np + C.fields.length)
      (bvars (C.fields.length + (D.nm + D.nmin)) D.np
        ++ bvars (C.fields.length + D.nmin) D.nm ++ bvars C.fields.length D.nmin
        ++ C.args.map fun a => ((D.atRec a).liftN (D.nm + D.nmin) C.fields.length).instL ls)
      (bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars 0 C.fields.length)
      (by simp only [List.length_append, VExpr.length_bvars, List.length_map, hal])
      (by simp)
  -- step 1: the two `mkLams` forms.  `iotaRule` stores both sides over the *same* telescope.
  have hL : (D.iotaRule j q C).lhs.instL ls
      = mkLams ((D.iotaCtx C).map (VExpr.instL ls)) ((D.iotaLhs j C).instL ls) := by
    show (mkLams (D.iotaCtx C) (D.iotaLhs j C)).instL ls = _
    rw [VExpr.instL_mkLams]
  have hR : (D.iotaRule j q C).rhs.instL ls
      = mkLams ((D.iotaCtx C).map (VExpr.instL ls))
        (((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls) := by
    show (mkLams (D.iotaCtx C) ((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length))).instL ls
      = _
    rw [VExpr.instL_mkLams]
  -- step 2: the match
  have hM : Pattern.Matches (D.iotaPat T C) ((D.iotaLhs j C).instL ls) m1 m2 := by
    rw [D.instL_iotaLhs j C hlen, VInductDecl'.getD_types hT]; exact hm
  -- step 6: the right-hand side, at the rule's own match
  have hRHS : ((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls
      = (D.iotaRHSOf j q T C hcl).apply m1 m2 := by
    rw [VInductDecl'.iotaRHSOf, iotaRHS_apply hpa hpb,
      show (Pattern.LPath.head (SimplePattern.iota (Lean.mkRecName T.name)
          (D.np + D.nm + D.nmin + T.indices.length) C.name
          (D.np + C.fields.length)).toPattern) = Sum.inl (Pattern.LPath.head _) from rfl, hml,
      VExpr.instL_mkApp, VExpr.map_instL_bvars, D.iotaLhs_args_split C,
      List.take_left' (by simp), List.drop_left' (by simp),
      VInductDecl'.length_iotaCtx,
      VExpr.bvars_add (lo := 0) (m := D.np + D.nm + D.nmin) (n := C.fields.length),
      Nat.zero_add]
  refine ⟨_, _, _, _, _, m1, m2, hL, hR,
    .iota hcl hargs hT hC hdf hrec hctor hplen, hM, ?_, hRHS⟩
  show (D.iotaCheckOf T C hargs).OK
    (env.IsDefEqU U (((D.iotaCtx C).map (VExpr.instL ls)).reverse ++ Γ)) m1 m2
  rw [VInductDecl'.iotaCheckOf]
  refine iotaCheck_OK.2 ⟨?_, ?_, ?_⟩
  · -- step 3: the parameter clauses.  Both leaves' first `np` matched arguments are the
    -- *same* list, so `List.zip_map_eq` settles the equation and `isDefEqU_of_mem_bvars`
    -- the judgement — two obligations, not one.
    have hA : ((Pattern.argPaths (.const (Lean.mkRecName T.name))
          (D.np + D.nm + D.nmin + T.indices.length)).take D.np).map (fun p => m2 (Sum.inl p))
        = bvars (C.fields.length + (D.nm + D.nmin)) D.np := by
      rw [List.map_take, hpa, List.append_assoc, List.append_assoc,
        List.take_left' (by simp)]
    have hB : ((Pattern.argPaths (.const C.name) (D.np + C.fields.length)).take D.np).map
          (fun p => m2 (Sum.inr p)) = bvars (C.fields.length + (D.nm + D.nmin)) D.np := by
      rw [List.map_take, hpb, List.take_left' (by simp)]
    have heq := List.zip_map_eq (hA.trans hB.symm)
    intro xy hxy
    rw [← heq xy hxy]
    refine VEnv.isDefEqU_of_mem_bvars (Δ := ((D.iotaCtx C).map (VExpr.instL ls)).reverse)
      (lo := C.fields.length + (D.nm + D.nmin)) (n := D.np)
      (by simp only [List.length_reverse, List.length_map, VInductDecl'.length_iotaCtx]; omega) ?_
    rw [← hA]
    exact List.mem_map_of_mem (List.of_mem_zip hxy).1
  · -- step 4: the index clauses.  Both matched lists are `C.args`-indexed, so the block is
    -- one `iota_index_clause` per result index, moved to `ls` and over `Γ`.
    have hIdx : ((Pattern.argPaths (.const (Lean.mkRecName T.name))
          (D.np + D.nm + D.nmin + T.indices.length)).drop (D.np + D.nm + D.nmin)).map
          (fun p => m2 (Sum.inl p))
        = C.args.map (fun a =>
            ((D.atRec a).liftN (D.nm + D.nmin) C.fields.length).instL ls) := by
      rw [List.map_drop, hpa, D.iotaLhs_args_split C, List.drop_left' (by simp)]
    have hCmp : (D.iotaComputed T C hargs).map (Pattern.RHS.apply m1 m2)
        = C.args.map (fun a =>
            ((mkLams (C.params ++ C.fields.map (·.type)) a).instL
                (D.selfLvls.map (VLevel.inst ls))).mkApp
              (bvars (C.fields.length + (D.nm + D.nmin)) D.np
                ++ bvars 0 C.fields.length)) := by
      rw [VInductDecl'.iotaComputed]
      refine List.map_pmap_eq_map _ _ _ (fun a hcla => ?_) _ _
      refine (Pattern.RHS.apply_mkApp _ _).trans ?_
      rw [VInductDecl'.ctorArgRHS]
      refine congr (congrArg VExpr.mkApp ?_) ((List.map_map ..).trans hpb)
      exact congrArg (fun l => VExpr.instL l (mkLams (C.params ++ C.fields.map (·.type)) a))
        (hmr (Pattern.LPath.head _))
    refine List.zip_map_rel (f := fun p => m2 (Sum.inl p)) (g := Pattern.RHS.apply m1 m2) ?_
    rw [hIdx, hCmp]
    refine List.forall₂_map_map fun a ha => ?_
    have he2 : ((mkLams (D.atRecTele (C.params ++ C.fields.map (·.type))) (D.atRec a)).mkApp
          (bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars 0 C.fields.length)).instL ls
        = ((mkLams (C.params ++ C.fields.map (·.type)) a).instL
              (D.selfLvls.map (VLevel.inst ls))).mkApp
            (bvars (C.fields.length + (D.nm + D.nmin)) D.np ++ bvars 0 C.fields.length) := by
      rw [VExpr.instL_mkApp, List.map_append, VExpr.map_instL_bvars, VExpr.map_instL_bvars,
        VExpr.instL_mkLams, VExpr.instL_mkLams, VInductDecl'.atRecTele, List.map_map]
      simp only [Function.comp_def, VExpr.instL_instL, VInductDecl'.atRec]
    have hbase := (VInductDecl'.iota_index_clause henv hI.toRecCtx hT hC ha).instL
      (U' := U) hlsWF
    rw [List.map_reverse, he2] at hbase
    have hccΔ : CtxClosed (((D.iotaCtx C).map (VExpr.instL ls)).reverse) := by
      rw [← List.map_reverse]
      refine OnCtx.ctxClosed henv (OnCtx.instL (U := D.recUvars) hlsWF ?_)
      rw [D.iotaCtx_reverse' C]; exact VInductDecl'.onCtxIota hI.toRecCtx hT hC
    obtain ⟨B, hB⟩ := hbase
    exact ⟨B, VEnv.IsDefEq.weakR henv hccΔ hB Γ⟩
  · -- step 5: the level clauses.  The recursor leaf's list is `ls` and the constructor
    -- leaf's is `selfLvls` instantiated at `ls`, and `iotaLevelPairs` pairs the entries that
    -- are literally the same level — so every clause is reflexivity of `≈`.
    rintro ij hij
    simp only [VInductDecl'.iotaLevelPairs, List.mem_map, List.mem_range] at hij
    obtain ⟨i, hi, rfl⟩ := hij
    rw [show (Pattern.LPath.head (SimplePattern.iota (Lean.mkRecName T.name)
          (D.np + D.nm + D.nmin + T.indices.length) C.name
          (D.np + C.fields.length)).toPattern) = Sum.inl (Pattern.LPath.head _) from rfl, hml,
      show iotaLeafCtor (Lean.mkRecName T.name) C.name
          (D.np + D.nm + D.nmin + T.indices.length) (D.np + C.fields.length)
        = Sum.inr (Pattern.LPath.head _) from rfl, hmr,
      show ((D.selfLvls.map (VLevel.inst ls)).getD i .zero)
        = ls.getD (if D.isLE then i + 1 else i) .zero from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, VInductDecl'.selfLvls,
            List.getElem?_map, List.getElem?_range hi]
          rfl]
    exact rfl

/-- **`Params.extra_pat`, whole.**  `VEnv.WF.ruleShape` says every rule of a well-formed
environment is a δ-rule, the quotient rule or an ι-rule, and carries exactly what the
corresponding case needs; this dispatches on it.

The `OnCtx Γ` the field offers is unused — see `Pat.extra_iota`'s docstring. -/
theorem Pat.extra {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {df : VDefEq} {ls : List VLevel}
    (hdf : env.defeqs df) (hlsWF : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars) :
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = mkLams Δ L ∧ df.rhs.instL ls = mkLams Δ R ∧
      Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
      (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2 := by
  have ho := VEnv.WF.ordered henv
  cases henv.ruleShape hdf with
  | delta ci hcl => exact Pat.extra_delta hcl hdf hlen
  | quot hlift hmk => exact Pat.extra_quot hdf hlift hmk hlen
  | iota D j q T C hcl hargs hal hplen hT hC hrec hctor hD s1 s2 s3 s4 =>
    exact Pat.extra_iota ho (VInductDecl'.iotaCtx_of_staged ho hD s1 s2 s3 s4)
      hcl hargs hal hplen hT hC hdf hrec hctor hlsWF hlen

/-! ## The leaf roles: what a `classify` function has to be told

`Lean4Lean.Params` (the shape model's class, `Experimental/SExpr.lean`) carries a field
`classify : Name → Option Classification` and a field
`pat_wf : Pat p r → Pattern.WF classify p`.  Unfolding `Pattern.WF` at the two registered
shapes leaves exactly three demands on `classify`:

* the recursor leaf `R` of an ι- or quot-pattern of recursor arity `M` must get `.symb (M+1)`,
* the constructor leaf `K` of arity `N` must get `.ctor N`,
* a δ-rule's head `c` must get `.symb 0`.

so `classify` is a three-way cascade and its correctness is: the three roles are **mutually
exclusive**, and each name's arity is recoverable.  Both are settled here, in a form that
mentions no `Classification` — `Theory/` must not import `Experimental/`, so the shim that
actually builds the instance lives downstream of both and should be thin.

**The arities are read off the stored constants, not off the patterns.**  That is the
design choice that makes the cascade cheap: a `classify` computing `.ctor N` from the
*pattern* would need "same constructor name ⇒ same `N`" across all registered patterns, and
the `Quot.mk`-versus-a-block-constructor instance of that is not available (it needs the
`VEnv.WF'` declaration history to see that `addQuot` and `addInduct'` are different steps).
Computing it as `(env.constants K).type.piArity` sidesteps the question entirely: if two
patterns did share a constructor leaf, they would share its *constant*, hence its Π-count,
hence agree.  Uniqueness stops being an obligation and becomes a consequence.

Two facts had to be *recorded* to make that work, both found by working backwards from the
obligation, which is the method the module docstring is about:

* `C.params.length = D.np` on `Pat.iota`, because the pattern states the constructor arity as
  `D.np + |C.fields|` while the stored type binds `C.params`;
* `env.constants ``Quot.mk` on `Pat.quot`, because `Quot.mk` is a constructor leaf and its
  arity now has to be read off its constant.  That field was deliberately absent while nothing
  consumed it, and its absence was right at the time.

**The downstream shim.**  `classify` and `pat_wf` mention `Classification` and `Pattern.WF`,
which live in `Experimental/SExpr.lean`; `Theory/` must not import `Experimental/`, so they
belong in a module downstream of both.  That shim is **written and machine-checked** (65
lines, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`), and it is short because
everything above is done:

    noncomputable def VEnv.classify (env : VEnv) (c : Name) : Option Classification :=
      if ∃ n, Pat.IsRecLeaf env c n then
        some (.symb ((env.constants c).elim 0 (·.type.piArity)))
      else if ∃ n, Pat.IsCtorLeaf env c n then
        some (.ctor ((env.constants c).elim 0 (·.type.piArity)))
      else if Pat.IsDeltaHead env c then some (.symb 0) else none

with one auxiliary (`Pattern.WF cl ((Pattern.const c).varN n) top k ↔ cl c = some …`, a
four-line induction), the three cascade equations from the exclusivity lemmas below, and

    noncomputable def paramsOfWF {e : VEnv} (henv : e.WF) (U : Nat) : Params :=
      Params.mk e henv.ordered U (Pat e) e.classify Pat.simple
        (e.classify_pat_wf henv) (Pat.uniq henv)

So **all eight fields of the shape model's `Params` are discharged for an arbitrary
`VEnv.WF env`**.  What remains for the shape-model route is `SExpr.ParamsExtra`, whose
`extra_pat` is refuted as stated (see the closing section) and whose `ctor_ty` is satisfiable.
`Classical.choice` enters exactly once, in the cascade's decidability, and nowhere else. -/

/-- `piArity` counts what `peelPis` peels. -/
theorem VExpr.piArity_eq_length_peelPis : ∀ e : VExpr, e.piArity = (peelPis e).1.length
  | .forallE _ B => by rw [VExpr.piArity, VExpr.peelPis, piArity_eq_length_peelPis B]; rfl
  | .bvar .. | .sort .. | .const .. | .app .. | .lam .. => rfl

theorem VInductDecl'.recType_piArity (D : VInductDecl') (j : Nat) :
    (D.recType j).piArity
      = D.np + D.nm + D.nmin + (D.types.getD j default).indices.length + 1 := by
  rw [VExpr.piArity_eq_length_peelPis, VInductDecl'.length_peelPis_recType]

/-- `c` is the **recursor leaf** of a registered pattern, at recursor arity `n`. -/
inductive Pat.IsRecLeaf (env : VEnv) : Lean.Name → Nat → Prop
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor} :
      D.types[j]? = some T → env.defeqs (D.iotaRule j q C) →
      env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ →
      IsRecLeaf env (Lean.mkRecName T.name) (D.np + D.nm + D.nmin + T.indices.length)
  | quot : env.defeqs quotDefEq → env.constants ``Quot.lift = some quotLiftConst →
      IsRecLeaf env ``Quot.lift 5

/-- `c` is the **constructor leaf** of a registered pattern, at constructor arity `n`. -/
inductive Pat.IsCtorLeaf (env : VEnv) : Lean.Name → Nat → Prop
  | iota {D : VInductDecl'} {j q : Nat} {C : VIndCtor} :
      env.defeqs (D.iotaRule j q C) →
      env.constants C.name = some ⟨D.uvars, C.type D j⟩ →
      C.params.length = D.np →
      IsCtorLeaf env C.name (D.np + C.fields.length)
  | quot : env.defeqs quotDefEq → env.constants ``Quot.mk = some quotMkConst →
      IsCtorLeaf env ``Quot.mk 3

/-- `c` heads a δ-rule of `env`. -/
def Pat.IsDeltaHead (env : VEnv) (c : Lean.Name) : Prop :=
  ∃ u v t, env.defeqs ⟨u, .const c (VLevel.params u), v, t⟩

/-- **Every registered pattern, in role form.**  This is the case split the shim's `pat_wf`
does; `Pattern.WF` then unfolds against the cascade. -/
theorem Pat.roles {env : VEnv} {p : Pattern} {r : p.RHS × p.Check} (h : Pat env p r) :
    (∃ c, p = .const c ∧ Pat.IsDeltaHead env c) ∨
    ∃ R M K N, p = (SimplePattern.iota R M K N).toPattern ∧
      Pat.IsRecLeaf env R M ∧ Pat.IsCtorLeaf env K N := by
  cases h with
  | delta _ hdf => exact .inl ⟨_, rfl, _, _, _, hdf⟩
  | @iota D j q T C _ _ hTj _ hdf hrec hctor hplen =>
    exact .inr ⟨_, _, _, _, rfl, .iota hTj hdf hrec, .iota hdf hctor hplen⟩
  | quot hdf hlift hmk => exact .inr ⟨_, _, _, _, rfl, .quot hdf hlift, .quot hdf hmk⟩

/-- The recursor leaf's arity is the Π-count of its stored type, minus the major premise. -/
theorem Pat.IsRecLeaf.piArity {env : VEnv} {c : Lean.Name} {n : Nat}
    (h : Pat.IsRecLeaf env c n) :
    ∃ ci, env.constants c = some ci ∧ ci.type.piArity = n + 1 := by
  cases h with
  | @iota D j q T C hTj _ hrec =>
    exact ⟨_, hrec, by rw [show (VConstant.type ⟨D.recUvars, D.recType j⟩) = D.recType j from rfl,
      VInductDecl'.recType_piArity, VInductDecl'.getD_types hTj]⟩
  | quot _ hlift => exact ⟨_, hlift, rfl⟩

/-- The constructor leaf's arity is the Π-count of its stored type — *because* the pattern
states it as `D.np + |C.fields|` while the stored type binds `C.params`, which is what the
recorded `C.params.length = D.np` reconciles. -/
theorem Pat.IsCtorLeaf.piArity {env : VEnv} {c : Lean.Name} {n : Nat}
    (h : Pat.IsCtorLeaf env c n) :
    ∃ ci, env.constants c = some ci ∧ ci.type.piArity = n := by
  cases h with
  | @iota D j q C _ hctor hplen =>
    exact ⟨_, hctor, by rw [show (VConstant.type ⟨D.uvars, C.type D j⟩) = C.type D j from rfl,
      VIndCtor.type_piArity, hplen]⟩
  | quot _ hmk => exact ⟨_, hmk, rfl⟩

/-- **Role exclusivity, 1 of 3.**  A recursor leaf is never a constructor leaf — the same
fact `pat_app_uniq` bottoms out in, restated on the roles. -/
theorem Pat.IsRecLeaf.ne_ctorLeaf {env : VEnv} {R K : Lean.Name} {m n : Nat}
    (h : Pat.IsRecLeaf env R m) (h' : Pat.IsCtorLeaf env K n) : R ≠ K := by
  cases h with
  | @iota D j q T C hTj _ hrec =>
    cases h' with
    | iota _ hctor' _ => exact _root_.Lean4Lean.rec_ne_ctor hTj hrec hctor'
    | quot => exact mkRecName_ne_quotMk _
  | quot _ hlift =>
    cases h' with
    | iota _ hctor' _ => exact quotLift_ne_ctor hlift hctor'
    | quot => exact by decide

theorem Pat.IsRecLeaf.not_ctorLeaf {env : VEnv} {c : Lean.Name} {m n : Nat}
    (h : Pat.IsRecLeaf env c m) (h' : Pat.IsCtorLeaf env c n) : False :=
  h.ne_ctorLeaf h' rfl

/-- **Role exclusivity, 2 of 3.** -/
theorem Pat.IsDeltaHead.ne_recLeaf {env : VEnv} (henv : env.WF) {c R : Lean.Name} {n : Nat}
    (h : Pat.IsDeltaHead env c) (h' : Pat.IsRecLeaf env R n) : c ≠ R := by
  obtain ⟨u, v, t, hdf'⟩ := h
  cases h' with
  | iota hTj hdf _ => exact Pat.deltaHead_ne_recName henv hdf hTj hdf'
  | quot hdf _ => exact fun hc => Pat.deltaHead_ne_quot henv hdf (hc ▸ hdf') (by decide)

theorem Pat.IsDeltaHead.not_recLeaf {env : VEnv} (henv : env.WF) {c : Lean.Name} {n : Nat}
    (h : Pat.IsDeltaHead env c) (h' : Pat.IsRecLeaf env c n) : False :=
  h.ne_recLeaf henv h' rfl

/-- **Role exclusivity, 3 of 3.** -/
theorem Pat.IsDeltaHead.ne_ctorLeaf {env : VEnv} (henv : env.WF) {c K : Lean.Name} {n : Nat}
    (h : Pat.IsDeltaHead env c) (h' : Pat.IsCtorLeaf env K n) : c ≠ K := by
  obtain ⟨u, v, t, hdf'⟩ := h
  cases h' with
  | iota hdf _ _ => exact Pat.deltaHead_ne_ctorName henv hdf hdf'
  | quot hdf _ => exact fun hc => Pat.deltaHead_ne_quot henv hdf (hc ▸ hdf') (by decide)

theorem Pat.IsDeltaHead.not_ctorLeaf {env : VEnv} (henv : env.WF) {c : Lean.Name} {n : Nat}
    (h : Pat.IsDeltaHead env c) (h' : Pat.IsCtorLeaf env c n) : False :=
  h.ne_ctorLeaf henv h' rfl

/-! ### The fourth role: a block type's name

`classify` must report `.indTy` for a block type's name, and its cascade tests the three roles
above first — so it needs `T.name` to play none of them.  Every other name-disjointness fact
in this file distinguishes *stored types* (`rec_ne_ctor` compares `piBodyHead`), and that route
is closed here by **F1**: `VIndType.WF` makes `T.type` only *definitionally* a Π-telescope
ending in a sort, hence syntactically anything — it could be a `recType`.

`VEnv.WF.iotaTypeNotKey` (`Theory/Typing/DeltaUnique.lean`, Part III) supplies it by
provenance instead, and a single clause covers all three roles at once because `VDefEq.key`
already names them: a recursor leaf is a key's head, a constructor leaf its last, a δ-head the
whole key. -/

/-- `c` is the name of a block type of a registered ι-pattern, with `rel` recording whether the
block is `Type`-valued — the `rel` of `SExpr.ParamsExtra.ctor_ty`. -/
inductive Pat.IsIndTyName (env : VEnv) : Lean.Name → Nat → Bool → Prop
  | iota {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor} {rel : Bool} :
      D.types[j]? = some T → env.defeqs (D.iotaRule j q C) →
      (rel = true ↔ D.lvl ≠ .zero) →
      IsIndTyName env T.name (D.np + T.indices.length) rel

/-- Each of the three roles exhibits a rule whose key contains the name.  This is the whole
bridge between the roles and `IotaTypeNotKey`. -/
theorem Pat.IsRecLeaf.mem_key {env : VEnv} {c : Lean.Name} {n : Nat}
    (h : Pat.IsRecLeaf env c n) : ∃ df, env.defeqs df ∧ c ∈ df.key := by
  cases h with
  | @iota D j q T C hTj hdf _ =>
    exact ⟨_, hdf, by rw [VInductDecl'.key_iotaRule, VInductDecl'.getD_types hTj]
                      exact List.mem_cons_self ..⟩
  | quot hdf _ => exact ⟨_, hdf, by rw [VEnv.key_quotDefEq]; exact List.mem_cons_self ..⟩

theorem Pat.IsCtorLeaf.mem_key {env : VEnv} {c : Lean.Name} {n : Nat}
    (h : Pat.IsCtorLeaf env c n) : ∃ df, env.defeqs df ∧ c ∈ df.key := by
  cases h with
  | @iota D j q C hdf _ _ =>
    exact ⟨_, hdf, by rw [VInductDecl'.key_iotaRule]
                      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
  | quot hdf _ =>
    exact ⟨_, hdf, by rw [VEnv.key_quotDefEq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩

theorem Pat.IsDeltaHead.mem_key {env : VEnv} {c : Lean.Name}
    (h : Pat.IsDeltaHead env c) : ∃ df, env.defeqs df ∧ c ∈ df.key := by
  obtain ⟨u, v, t, hdf⟩ := h
  exact ⟨_, hdf, by rw [VEnv.key_of_isDeltaRule VEnv.IsDeltaRule.const]
                    exact List.mem_cons_self ..⟩

/-- **Role exclusivity for the fourth role.**  One lemma covers all three, because all three
reduce to "some rule's key contains `c`". -/
theorem Pat.IsIndTyName.not_key {env : VEnv} (henv : env.WF) {c : Lean.Name} {n : Nat}
    {rel : Bool} (h : Pat.IsIndTyName env c n rel)
    (h' : ∃ df, env.defeqs df ∧ c ∈ df.key) : False := by
  obtain ⟨df, hdf, hmem⟩ := h'
  cases h with
  | @iota D j q T C rel hTj hiota _ =>
    exact VEnv.WF.iotaTypeNotKey henv D j q C hiota df hdf
      (by rw [VInductDecl'.getD_types hTj]; exact hmem)

theorem Pat.IsIndTyName.not_recLeaf {env : VEnv} (henv : env.WF) {c n rel m}
    (h : Pat.IsIndTyName env c n rel) (h' : Pat.IsRecLeaf env c m) : False :=
  h.not_key henv h'.mem_key

theorem Pat.IsIndTyName.not_ctorLeaf {env : VEnv} (henv : env.WF) {c n rel m}
    (h : Pat.IsIndTyName env c n rel) (h' : Pat.IsCtorLeaf env c m) : False :=
  h.not_key henv h'.mem_key

theorem Pat.IsIndTyName.not_deltaHead {env : VEnv} (henv : env.WF) {c n rel}
    (h : Pat.IsIndTyName env c n rel) (h' : Pat.IsDeltaHead env c) : False :=
  h.not_key henv h'.mem_key

/-! ## `Params.extra_pat` — done, and what it cost

All three cases are proved: `Pat.extra_delta`, `Pat.extra_quot`, `Pat.extra_iota`, dispatched
by `Pat.extra`.  `Params`' six fields are now five proved (`pat_simple`, `pat_uniq`,
`pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`) and one open (`pat_wf`, which needs
`IsDefEqU.forallE_inv` and is deliberately left as the interface obligation).

### What the ι case is made of

* **Step 0** — the staging data on `RuleShape.iota`, cashed in by
  `VInductDecl'.iotaCtx_of_staged`.  Carrying `D.IotaCtx env` directly would have needed an
  `IotaCtx.mono`; the staging data is monotone for free because only its last premise mentions
  `env`.  `VInductDecl'.WF.recCtx` does the work, and its monotonicity is *in its signature*
  (`env₂ ≤ env₃ → env₃.Ordered → RecCtx env₃`), not in a lemma — no name or shape search finds
  that, only reading it.
* **Steps 1, 2, 6** — `VExpr.instL_mkLams` (both sides of `iotaRule` share one telescope, so
  no `peelLams` is needed at all), `VInductDecl'.instL_iotaLhs` into `matches_iota_paths`, and
  `iotaRHS_apply` + `iotaLhs_args_split` + `VExpr.bvars_add`.
* **Step 3** — `List.zip_map_eq` for the equation, `VEnv.isDefEqU_of_mem_bvars` for the
  judgement.  Two obligations, and the note below is why that is written twice.
* **Step 4** — `VInductDecl'.iota_index_clause`, then `IsDefEqU.instL` and `IsDefEq.weakR`.
* **Step 5** — `iotaLevelPairs` against `selfLvls`, entry by entry; both sides are the same
  level, so each clause is `rfl`.

### Is instantiating `VEnv.Params` circular?  No — and the reason is a name collision

The worry: `pat_wf` needs `IsDefEqU.forallE_inv`; the only proof of `forallE_inv` is
`Experimental/Reflect/Capstone.lean`'s `forallE_inv_params`, which is stated `[Params]`-relative;
so instantiating `Params` would need `Params`.

**There are two classes called `Params`, and Capstone consumes the other one.**

* `Lean4Lean.VEnv.Params` (`Theory/Typing/ChurchRosser.lean`) — the mainline class this file
  instantiates.  Ten fields; `pat_wf` is the semantic one (`Matches` + `HasType` + `Check.OK`
  ⟹ `IsDefEqU`), and it is what needs `forallE_inv`.
* `Lean4Lean.Params` (`Experimental/SExpr.lean`) — the shape model's class.  Eight fields;
  its `pat_wf` is `Pat p r → Pattern.WF classify p`, a **purely syntactic** condition (the
  recursor leaf is a `.symb` of the right arity, the constructor leaf a `.ctor`).  The
  mainline's semantic `pat_wf`, `pat_app_*` and `extra_pat` are present in that file only as
  commented-out fields, with a note saying they are deliberately not fields there.

Capstone sits in `namespace Lean4Lean` and does not `open VEnv`, so its bare `Params` is the
second one.  Three independent checks, all machine-run rather than read off:

1. `#print Lean4Lean.Params` shows the eight fields and the syntactic `pat_wf`.
2. `#check @VEnv.IsDefEqU.forallE_inv_params` shows its instance arguments are
   `[Params] [SExpr.ParamsExtra]`, i.e. the shape-model pair.
3. `Theory/Typing/ChurchRosser.lean` is **not in Capstone's import cone** (27 modules; this
   file, `Injectivity.lean` and `ChurchRosser.lean` are all absent), so `VEnv.Params.pat_wf`
   is not even nameable there.

So the dependency is `VEnv.Params.pat_wf` → `forallE_inv` → `Lean4Lean.Params` +
`SExpr.ParamsExtra`, and it terminates.  It is not a cycle, and it is not a stratification
either — the two classes are simply different.  The module order also works: this file's cone
(42 modules) and Capstone's (27) each exclude the other and both exclude `ChurchRosser.lean`,
so one new module can import both, build the shape-model instance, obtain `forallE_inv`, prove
`pat_wf`, and build the mainline instance.

Two things this does *not* say.  The shape-model instance is real work in its own right —
`classify` has to be produced for an arbitrary `VEnv.WF env`, and `SExpr.ParamsExtra` also
carries `ctor_ty` — and Capstone's results are still `sorryAx`-tainted through
`SExpr.forallE_inv`, `SExpr.sort_inv`, `SExpr.HasTypeS.uniq` and `SExpr.IsDefEq.toHasTypeS`,
which is the shape-model stream's own frontier, not a `Params` obligation.

### `SExpr.ParamsExtra.extra_pat` is unsatisfiable as stated — the λ-peeling defect, uncured

`PLAN.md`'s original finding was that `extra_pat` cannot hold for any environment with a
λ-abstracted rule, because `Pattern.Matches` walks only `const`/`app` spines.  The mainline
field was fixed by peeling (`∃ Δ L R, df.lhs.instL ls = mkLams Δ L ∧ …`), which is why
`Pat.extra` above exists at all.  **The `SExpr` copy was not fixed.**
`SExpr.ParamsExtra.extra_pat` still asks for `p.MatchesS (.instL ls (.mk df.lhs)) m1 m2` on
the unpeeled left-hand side, and `Pattern.MatchesS.not_lam` (proved, in the same file) says a
pattern never matches a `lam`.  `SExpr.mk` and `SExpr.instL` are both structural on `lam`, so
the `lam` survives both.

Hence: **no `SExpr.ParamsExtra` instance exists for any environment carrying the quotient rule
or any ι-rule** — `quotDefEq.lhs` is a six-binder `mkLams`, and `iotaRule`'s is a
`mkLams (iotaCtx C)` whose telescope is never empty (`D.motives` has one entry per type and
`D.types ≠ []`).  Machine-checked; the witness derives `False` from
`[Params] [SExpr.ParamsExtra]` plus `env.defeqs quotDefEq`, and again from `env.defeqs
(D.iotaRule j q C)`, with no `sorryAx` and no `Classical.choice`.  It lives with the stream
that owns `Experimental/SExpr.lean`, since this file must not import `Experimental/`.

So the route `pat_wf` → `forallE_inv` → shape-model instance is **not blocked by circularity
but by an unsatisfiable field one step further out**, and the fix is the same peel the
mainline already took.

`ctor_ty`, by contrast, *is* satisfiable — traced, not assumed.  Note what it does not say,
though: it requires only `VIndCtor.Interface env D j T C`, and asks neither for `D.WF env` nor
for `D` to have been added to `env`.  `pat_simple` forces the quotient rule's pattern to be
`SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3` (a six-argument application cannot be a
`.defn`, whose `toPattern` is a bare `.const`), so `Pattern.WF` forces
`classify ``Quot.mk = some (.ctor 3)`, and `ctor_ty` then demands a block with a constructor
named `Quot.mk`.  No such block is in any environment — `addQuot` is a separate extension —
and the obligation is dischargeable only by *fabricating* a `VInductDecl'` describing `Quot`
(`uvars := 1`, `params := [Sort u, α → α → Prop]`, one field, no indices), which every field of
`Interface` then accepts against `addQuot`'s stored types.  That works, and it means `ctor_ty`
records less provenance than its name suggests: a consumer reading it as "this constructor
came from a real declaration" is relying on something it does not say.

### Two findings

**`extra_pat`'s `OnCtx Γ` is not needed by any case.**  Its docstring argues that the ι index
clauses need it, because they β-reduce a `mkLams` and `IsDefEq.beta` needs the function typed.
The premise is right and the conclusion is wrong: the β-reduction happens in the rule's *own*
binder context, which is closed, and `IsDefEq.weakR` carries the result over an arbitrary `Γ`
on `CtxClosed` alone.  The field's hypothesis is harmless — its one caller holds it — but
nothing consumes it, and `Pat.extra` ignores it.

**The F3 transport is the whole cost of step 4.**  `iotaComputed` abstracts a result index
over `C.params ++ fields` — the *constructor's* stored telescope — while `iotaCtx` carries
`D.params`.  `iota_law`, the template, never meets this: it types its constructor spine with
`ctorApp'_hasType`, which packages the transport through `appBVars₂` for a *single*
application.  `betaMkLams` instead wants a `HasArgs` for the spine, and no spine-level
analogue of that transport existed — hence `VEnv.HasArgs.defeqDFC`, `VEnv.HasArgs.hasType_of_mem`,
`VExpr.instAllTele_bvars_shift`, and the two-block `HasArgs.bvars`/`HasArgs.append`
construction inside `iota_index_clause`.

### The accounting note, and its recurrence

The estimate was 40 + 250 = 290 lines; the measurement is 41 + 369 = 410.  Steps 0, 1, 2, 3, 5
and 6 came in at or under their numbers.  All of the overrun is step 4: priced at ~80, it cost
~190 (113 for `iota_index_clause`, 63 for the four helpers it needed, ~15 for the block that
consumes it).

The previous stream left this warning:

> Every line you name gets its own number.  A named line folded into another's estimate is
> functionally unenumerated.

Step 4's line named `betaMkLams`'s "three hypotheses" and then priced two of them — the
`OnCtx` and the `HasType` — leaving the `HasArgs` named but unnumbered.  The warning was
correct, was read, and was violated on the very line that carries it.  A prose list of
dependencies is not an enumeration; **turn each named dependency into a row with a number
before totalling**, and treat a dependency you have not located in the tree as its own row
even when the lemma that consumes it is already priced.

Corollary, unchanged: a heuristic that prices listed lines is not a check that the list is
complete, and a correct total is not evidence that it was. -/

end Lean4Lean
