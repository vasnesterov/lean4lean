import Lean4Lean.Theory.Inductive.StructureClosed
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Structure eta, in the spec

`Lean4Lean/TypeChecker.lean`'s `tryEtaStructCore` (`:656`) and `isDefEqUnitLike` (`:849`) —
mirroring the C++ kernel's `try_eta_struct_core` (`type_checker.cpp:889`) and
`is_def_eq_unit_like` (`:1159`) — both conclude `t ≡ s` from facts that do **not** entail it
in the abstract theory.  What they rest on is *surjective pairing*,

```
e ≡ S.mk ps (proj 0 e) … (proj (n-1) e)      for  e : S ps
```

and `VEnv.IsDefEq`'s thirteen constructors do not give it: `beta`/`eta` need a λ, and `extra`'s
ι-rules fire only at a *constructor application*, whereas here `e` is arbitrary.
`docs/design-inductive.md` §6.3 established that it also cannot be added as a `VDefEq`, because
`Pattern.Matches` only matches `const`-headed spines and the rule's left-hand side is a
variable.

This file states the rule.  It is stated as a **property of an environment**,
`VEnv.StructEta`, rather than as a new `VEnv.IsDefEq` constructor, for one reason: adding a
constructor edits `Theory/Typing/Basic.lean` and forces a new case into every induction over
`IsDefEq` across `Theory/Typing/{Lemmas,Strong,UniqueTyping,ChurchRosser}.lean` and `Verify/`
— a coordinated change across files this stream does not own.  The predicate form is what a
consumer needs *now* (it is exactly the hypothesis the two `WF` obligations are missing), it
is the statement the constructor would have, and when the constructor lands `StructEta` becomes
a one-line theorem (`fun hS _ _ _ _ _ he _ => .structEta hS … he`) rather than being discarded.

## What the rule says, and why each side condition is there

Read off the two call sites (**[source]**, `~/lean4/src/kernel/type_checker.cpp` and
`Lean4Lean/TypeChecker.lean`), gate for gate:

| gate in the checker | clause here |
|---|---|
| `env.isNonRecStructure I` — `isRec := false`, one constructor | `env.IsStructure S D T C` (`types = [T]`, `ctors = [C]`, `recFields = []`) |
| `numIndices = 0` | `T.indices = []` |
| the projections `.proj I k t` must typecheck (`inferProj`, F17) | `D.isLE = true ∨ ∀ k < n, (C.fields.getD k _).lvl.inst us ≈ .zero` |
| `inferType t ≡ inferType s`, giving `t : S ps` | `env.HasType U Γ e ((const S us).mkApp ps)` |

**There is no `IsNeverZero` side condition, and there must not be one.**
`docs/design-inductive.md`'s proposed `structEta` carried `(D.lvl.inst ls).IsNeverZero`,
imported from `toCtorWhenStruct`'s F16 guard.  Neither `tryEtaStructCore` nor
`isDefEqUnitLike` tests the structure's universe — checked gate-for-gate against both kernels
— so both fire on `Prop` structures (`And`, `True`), and a rule carrying `IsNeverZero` would
not cover them.  Since the `Prop` case is independently derivable (`structEta_of_prop` below,
via `proofIrrel`), keeping the condition would not have been *unsound*, only useless at two of
its three call sites; dropping it is what makes the rule cover them.  `docs/design-inductive.md`
has been corrected.

**The F17 clause is not optional.**  `IsDefEq` implies both sides are well typed, so a rule
whose right-hand side is not well typed is not merely useless but false.  For a
small-eliminating structure (`isLE = false`) the projections `projTerm … k e` are recursor
applications at elimination level `(C.fields.getD k _).lvl`, and those are legal only when that
level is `≈ .zero`.  This is the same clause `TrProj` records (`Verify/Typing/Expr.lean`),
minus its "unused fields are exempt" guard: eta projects *every* field, so every field is in
scope for the condition.  `Verify/Typing/ProjLevelWitness.lean`'s `barDecl` — a two-field
`Prop` structure whose field 0 has level `.succ .zero` — is exactly the configuration this
clause must exclude, and it does.

## What is *not* claimed here

`VEnv.StructEta` is not proved for any environment, and it cannot be: a proof would have to be
an induction over the thirteen `IsDefEq` constructors producing a rule none of them has.  Nor
is it *refuted* — the set model (`Theory/SetModel/`) validates surjective pairing, so it cannot
separate the two sides, and the only other route (Church–Rosser) runs through
`NormalEq.descend`, which is machine-checked **false** (`Theory/Typing/DescendRefute.lean`).
The rule is an addition to the theory, to be discharged by the model construction, exactly as
`quotDefEq` is.

`StructureExamples.lean` checks `etaExpansion` against Lean's own elaborator at four
structures, including two-field and dependent-field ones, so the *term* the rule produces is
machine-checked even though the rule itself is an assumption.

## The zero-field case is stated elsewhere, over a **wider** class of blocks

`VEnv.StructEta`'s `IsStructure` hypothesis has a `types : D.types = [T]` field, so the rule
below says nothing about a member of a *mutual* block — and `isDefEqUnitLike` fires at one
(`Verify/TypeChecker/FiringWitness.lean`), which is why `isDefEqUnitLike.WF`'s residual
`UnitLikeBridge` is **false** rather than merely unproved once `AddInduct` is non-empty
(`docs/vacuity-ledger.md` row 99c).

The zero-field repair is `VEnv.UnitEta` in `Lean4Lean/Verify/TypeChecker/UnitEta.lean`: the same
rule at `C.fields = []`, stated over `VEnv.IsStructureG`, together with the widened bridge
`UnitLikeBridgeG` and `isDefEqUnitLike.WF_of_unitEta`.  It lives under `Verify/` **only** because
`VEnv.IsStructureG` is declared in `Verify/Typing/ProjGen.lean` and nothing under `Theory/`
imports `Verify/`; `IsStructureG` mentions nothing outside `Theory/`, so moving it here would let
`UnitEta` be stated in this file, and that move is a pending design decision, not an oversight.

`VEnv.UnitEta.structEta_at_no_fields` there proves that `UnitEta` delivers everything
`StructEta` delivers at zero fields, so the two do not overlap redundantly: what remains for
`StructEta` is the **positive-field** case, whose analogous widening needs `projTermG` and the
`ProjGen` swap, because with fields present a recursor is back in the statement.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

/-- `[proj 0 e, …, proj (n-1) e]`, the field projections of `e` in declaration order.

The index list is `[]`: structure eta applies only to a block with no indices
(`isNonRecStructure` tests `numIndices = 0`), which is `VEnv.StructEta`'s `T.indices = []`
clause. -/
def projAll (ps : List VExpr) (e : VExpr) : List VExpr :=
  (List.range C.fields.length).map fun i => D.projTerm T C us ps [] i e

@[simp] theorem length_projAll {ps e} : (D.projAll T C us ps e).length = C.fields.length := by
  simp [projAll]

@[simp] theorem projAll_nil {ps e} (h : C.fields = []) : D.projAll T C us ps e = [] := by
  simp [projAll, h]

/-- The η-expansion of `e` at a structure: `S.mk ps (proj 0 e) … (proj (n-1) e)`.

This is the right-hand side of the surjective-pairing rule, and it is the term the checker
compares against: `tryEtaStructCore` runs `isDefEq (.proj I k t) args[k]` for every field of
`s = S.mk ps args`, i.e. it checks `etaExpansion … t` against `s` argument by argument. -/
def etaExpansion (ps : List VExpr) (e : VExpr) : VExpr :=
  (VExpr.const C.name us).mkApp (ps ++ D.projAll T C us ps e)

/-- At zero fields — `isDefEqUnitLike`'s case — the η-expansion is the bare constructor applied
to the parameters, with no projection anywhere in it.  This is why that check needs no `TrProj`
machinery at all. -/
theorem etaExpansion_of_no_fields {ps e} (h : C.fields = []) :
    D.etaExpansion T C us ps e = (VExpr.const C.name us).mkApp ps := by
  simp [etaExpansion, projAll_nil _ _ _ _ h]

theorem projAll_instL {ps e} :
    (D.projAll T C us ps e).map (VExpr.instL ls) =
      D.projAll T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls)) (e.instL ls) := by
  simp [projAll, List.map_map, Function.comp_def, projTerm_instL]

theorem etaExpansion_instL {ps e} :
    (D.etaExpansion T C us ps e).instL ls =
      D.etaExpansion T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls)) (e.instL ls) := by
  simp [etaExpansion, VExpr.instL_mkApp, VExpr.instL, List.map_append, projAll_instL]

end VInductDecl'

/-- **Structure eta (surjective pairing), as a property of an environment.**

`env.StructEta` says: whenever `env` declares `S` as an index-free structure whose fields are
all projectable, every inhabitant of `S ps` is definitionally equal to its own η-expansion.

Every binder is pinned by a hypothesis — `S`, `D`, `T`, `C` by `IsStructure`, `us` and `ps` by
the length and `HasArgs` clauses, `e` by the `HasType` clause — so the conclusion mentions
nothing the premises leave free.  (That audit is the one that caught `NormalEq.descend`; run
it on anything added here.) -/
def VEnv.StructEta (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr},
    env.IsStructure S D T C →
    T.indices = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps)

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'}
  {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e e₁ e₂ : VExpr}

/-- **The `Prop` half of the rule is already derivable.**  For a structure living in `Prop`,
`IsDefEq.proofIrrel` gives surjective pairing outright, with no new rule — *provided* the
η-expansion is well typed, which is the same obligation the general rule carries and is what
`Theory/Inductive/StructureClosed.lean`'s projection-typing chain supplies.

This is why `VEnv.StructEta` must not carry an `IsNeverZero` side condition and equally why
carrying one would not have been unsound: the excluded cases are the ones that are free.
`isDefEqUnitLike.WF_prop` (`Verify/TypeChecker/IsDefEq.lean`) is this argument run at the
checker level, where it does not even need the η-expansion — `proofIrrel` relates the two
inhabitants directly. -/
theorem structEta_of_prop
    (hprop : env.HasType U Γ ((VExpr.const S us).mkApp ps) (.sort .zero))
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hmk : env.HasType U Γ (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps) :=
  .proofIrrel hprop he hmk

namespace StructEta

/-- **What `isDefEqUnitLike` needs.**  At zero fields the η-expansion is the same closed term
`S.mk ps` for every inhabitant, so any two inhabitants of `S ps` are definitionally equal.

Note the shape: the two `HasType`s are at the *same* type, which is what the checker's
`isDefEq (inferType t) (inferType s)` establishes.  Nothing about projections, `TrProj`, or
unique typing enters. -/
theorem unitLike (H : env.StructEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = []) (hnf : C.fields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he₁ : env.HasType U Γ e₁ ((VExpr.const S us).mkApp ps))
    (he₂ : env.HasType U Γ e₂ ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e₁ e₂ ((VExpr.const S us).mkApp ps) := by
  have hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero := .inr (by simp [hnf])
  have h1 := H hS hidx hus husWF hps hpsA he₁ hF17
  have h2 := H hS hidx hus husWF hps hpsA he₂ hF17
  rw [D.etaExpansion_of_no_fields T C us hnf] at h1 h2
  exact h1.trans h2.symm

/-- **What `tryEtaStructCore` needs.**  The checker compares `proj k t` against `args[k]` for
every field and, on success, reports `t ≡ S.mk ps args`.  This is that step: eta, then spine
congruence.

The constructor's telescope and result are taken as hypotheses rather than derived from
`IsStructure`, because reading them off the environment is the separate `VIndCtor.type`
chain; `hB` is the statement that the spine's result type is `S ps`, which for a structure's
own constructor is `VIndCtor.canonResult` at no indices.

**Nothing here compares parameter lists.**  The `HasArgsDF` is built at the *single* spine
`ps`, shared by both sides, so no injectivity of `S` as a constant application is needed —
correcting `docs/research-structeta.md` §5, which scheduled this behind `TrProj.uniq`. -/
theorem congrSpine (H : env.StructEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    {Tel : List VExpr} {B : VExpr} {args : List VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us) (VExpr.mkPi Tel B))
    (hargs : env.HasArgsDF U Γ Tel (ps ++ D.projAll T C us ps e) (ps ++ args))
    (hB : VExpr.instAll B (ps ++ D.projAll T C us ps e) = (VExpr.const S us).mkApp ps) :
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp (ps ++ args))
      ((VExpr.const S us).mkApp ps) := by
  have h1 := H hS hidx hus husWF hps hpsA he hF17
  have h2 := VEnv.IsDefEq.mkAppDF hargs hctor
  rw [hB] at h2
  exact h1.trans h2

/-- **The step `tryEtaStructCore` actually performs, assembled.**

The checker does not hand `congrSpine` a `HasArgsDF`; it compares the projections against the
constructor's arguments *one field at a time* and reports success only if every comparison
succeeds.  This lemma is that shape: `hdef` is the loop's output — one `IsDefEqU` per field —
and the `HasArgsDF` is built here, by `VEnv.HasArgsDF.ofMap` over the field telescope, and fed
to `congrSpine`.

`hprojty` is `ProjHasType` at each field, i.e. exactly what `Verify/Typing/Lemmas.lean`'s
`projTerm_hasType` delivers from `IsStructure` plus the F17 clause.  It is a hypothesis here
rather than a premise derived on the spot only because `projTerm_hasType` lives in `Verify/`;
`tryEtaStructCore.WF_of_structEta` discharges it there and does **not** assume it.

`hctor`/`hB` are the constructor's declared telescope and result, split at the parameter/field
boundary — the two facts about the block's declaration that this assembly needs and that
`IsStructure` alone does not spell out.

Note which spine the telescope is instantiated at: `ofMap` instantiates by the **left** spine,
which is the projection list, so no comparison of parameter lists occurs anywhere — the same
point `congrSpine`'s docstring makes, now carried through the field-by-field form. -/
theorem congrProj (H : env.StructEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    {args : List VExpr} (hargl : args.length = C.fields.length)
    (hprojty : ∀ k, k < C.fields.length →
      env.HasType U Γ (D.projTerm T C us ps [] k e)
        (VExpr.instAll ((C.fields.getD k default).type.instL us)
          (ps ++ (List.range k).map fun m => D.projTerm T C us ps [] m e)))
    (hdef : ∀ k, k < C.fields.length →
      env.IsDefEqU U Γ (D.projTerm T C us ps [] k e) (args.getD k default))
    {B : VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us)
      (VExpr.mkPi (D.params.map (VExpr.instL us) ++
        C.fields.map (fun F => F.type.instL us)) B))
    (hB : VExpr.instAll B (ps ++ D.projAll T C us ps e) = (VExpr.const S us).mkApp ps)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp (ps ++ args))
      ((VExpr.const S us).mkApp ps) := by
  have hgetD : ∀ k, k < C.fields.length →
      (C.fields.map fun F => VExpr.instL us F.type).getD k default
        = VExpr.instL us (C.fields.getD k default).type := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have hargsEq : (List.range C.fields.length).map (fun k => args.getD k default) = args := by
    refine List.ext_getElem (by simp [hargl]) fun n h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]
  have hfields := VEnv.HasArgsDF.ofMap (env := env) (U := U) (Γ := Γ)
    (As := C.fields.map fun F => VExpr.instL us F.type) (as := ps)
    (f := fun k => D.projTerm T C us ps [] k e) (g := fun k => args.getD k default)
    (i := C.fields.length) (by simp) (fun k hk => by
      rw [hgetD k hk]; exact (hdef k hk).of_l henv hΓ (hprojty k hk))
  rw [List.take_of_length_le (by simp), hargsEq] at hfields
  exact H.congrSpine hS hidx hus husWF hps hpsA he hF17 hctor
    (VEnv.HasArgsDF.append hpsA.toDF hfields) hB

/-- **Round-trip check on `congrProj`'s assembly.**

At the identity spine — comparing every projection against *itself* — `congrProj` must
reproduce exactly the rule it is assembled from, `e ≡ D.etaExpansion T C us ps e`.  It does.

This is a consistency check on the bookkeeping, not a new result: the `HasArgsDF` is built by
`ofMap` over the field telescope instantiated at the projection spine, and a misalignment
there (wrong telescope, wrong instantiation spine, off-by-one in the `range`) would make this
statement fail while leaving `congrProj` itself type-correct.  It is the cheapest available
test that the assembly is not vacuous *as an assembly*. -/
theorem congrProj_at_projAll (H : env.StructEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    (hprojty : ∀ k, k < C.fields.length →
      env.HasType U Γ (D.projTerm T C us ps [] k e)
        (VExpr.instAll ((C.fields.getD k default).type.instL us)
          (ps ++ (List.range k).map fun m => D.projTerm T C us ps [] m e)))
    {B : VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us)
      (VExpr.mkPi (D.params.map (VExpr.instL us) ++
        C.fields.map (fun F => F.type.instL us)) B))
    (hB : VExpr.instAll B (ps ++ D.projAll T C us ps e) = (VExpr.const S us).mkApp ps)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps) := by
  have hgetD : ∀ k, k < C.fields.length →
      (D.projAll T C us ps e).getD k default = D.projTerm T C us ps [] k e := by
    intro k hk
    have hk' : k < (List.range C.fields.length).length := by simpa using hk
    simp only [VInductDecl'.projAll, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some, List.getElem_range]
  refine H.congrProj hS hidx hus husWF hps hpsA he hF17 (D.length_projAll T C us)
    hprojty (fun k hk => ?_) hctor hB henv hΓ
  rw [hgetD k hk]
  exact ⟨_, hprojty k hk⟩

end StructEta

end VEnv

/-! ## Satisfiability, and non-vacuity

Two acceptance criteria, in opposite directions.

*The assumption is consistent*: `empty_structEta` exhibits an environment satisfying it, so
`StructEta` is not a disguised `False` and a theorem taking it as a hypothesis is not
vacuously true for that reason.

*The premises are jointly satisfiable at a **two-field** structure*: `bazEnv_structEta_premises`
discharges every clause at once, at `structure Baz : Prop where (a : ∀ p : Prop, p)
(b : ∀ p : Prop, p)`.  This is the criterion a one-field or zero-field witness would not
meet — and it is not automatic: `Verify/Typing/ProjLevelWitness.lean`'s `barDecl`, the tree's
other two-field structure, **fails** the F17 clause, because its field 0 has level
`.succ .zero`. -/

/-- `StructEta` is satisfiable: the empty environment declares no structure, so every instance
of the rule is vacuous there.  Read together with `bazEnv_structEta_premises`, which shows the
premises are *not* vacuous in general. -/
theorem VEnv.empty_structEta : VEnv.empty.StructEta := by
  intro U Γ S D T C us ps e hS _ _ _ _ _ _ _
  obtain ⟨env₀, env₁, _, hadd, hle⟩ := hS.decl
  have h := hle.constants (VEnv.addInduct'_types (T := T) hadd (by simp [hS.types]))
  simp [VEnv.empty] at h

/-! ### `structure Baz : Prop where (a : ∀ p : Prop, p) (b : ∀ p : Prop, p)`

Two non-recursive fields, both with level `imax 1 0 ≈ 0`, so the F17 clause holds in its
small-elimination form; `isLE = false`, which `VInductDecl'.WF` permits unconditionally
(`WF.isLE` constrains `isLE` only in the `true` direction).  `Prop` is used for the field
types only because the empty environment has no other closed type. -/

/-- `∀ p : Prop, p`, with level `imax 1 0`.  Used for both fields: it has no loose variable
beyond its own binder, so the same expression is well typed in both field contexts. -/
def bazField : VIndField where
  type := .forallE (.sort .zero) (.bvar 0)
  lvl := .imax (.succ .zero) .zero
  recArg := none

def bazCtor : VIndCtor where
  name := `Baz.mk
  params := []
  fields := [bazField, bazField]
  args := []

def bazType : VIndType where
  name := `Baz
  type := .sort .zero
  indices := []
  ctors := [bazCtor]

def bazDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .zero
  types := [bazType]
  isLE := false

theorem bazField_hasType {env : VEnv} {Γ : List VExpr} :
    env.HasType 0 Γ bazField.type (.sort bazField.lvl) :=
  .forallEDF (.sortDF trivial trivial (.refl _)) (.bvar (.zero ..))

theorem bazDecl_WF : bazDecl.WF .empty where
  types_ne := by simp [bazDecl]
  params := trivial
  types := by
    intro T hT
    simp [bazDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [bazDecl] at hT
      subst hT
      simp [bazType] at hC
      subst hC
      have hc : env₁.constants `Baz = some ⟨0, VExpr.sort .zero⟩ := by
        simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, bazDecl, bazType,
          VEnv.addConst, VEnv.empty] at he
        subst he; simp
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp [bazCtor], args_ty := .nil,
               result := .constDF hc nofun nofun rfl .nil }
      intro i F hF
      have hpos : ∃ A, bazDecl.NoBlock A ∧
          env₁.IsDefEqType bazDecl.uvars
            (((bazCtor.fields.take i).map (·.type)).reverse ++ bazDecl.params.reverse)
            bazField.type A :=
        ⟨bazField.type, by simp [VInductDecl'.NoBlock, VExpr.NoConsts, bazField],
          _, bazField_hasType⟩
      match i, hF with
      | 0, hF =>
        simp [bazCtor] at hF
        subst hF
        exact { hasType := bazField_hasType
                level := fun ls => by simp [VLevel.eval, bazDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := hpos }
      | 1, hF =>
        simp [bazCtor] at hF
        subst hF
        exact { hasType := bazField_hasType
                level := fun ls => by simp [VLevel.eval, bazDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := hpos }
  isLE := by simp [bazDecl]

theorem bazEnv_eq : ∃ e, VEnv.empty.addInduct' bazDecl = some e := ⟨_, rfl⟩

noncomputable def bazEnv : VEnv := bazEnv_eq.choose

theorem bazEnv_IsStructure : bazEnv.IsStructure `Baz bazDecl bazType bazCtor where
  types := rfl
  name := rfl
  ctors := rfl
  noRec := rfl
  decl := ⟨.empty, bazEnv, bazDecl_WF, bazEnv_eq.choose_spec, VEnv.LE.rfl⟩

theorem bazEnv_Baz_const : bazEnv.constants `Baz = some ⟨0, .sort .zero⟩ :=
  VEnv.addInduct'_types (T := bazType) bazEnv_eq.choose_spec (by simp [bazDecl])

/-- The context `(x : Baz)`. -/
def bazCtx : List VExpr := [.const `Baz []]

/-- Both fields of `Baz` are proofs, so `StructEta`'s F17 clause holds in its
small-elimination form.  (`bazDecl.isLE` is `false`, so the `.inl` disjunct is unavailable —
this is the branch that has to be discharged.) -/
theorem bazCtor_fields_prop : ∀ k, k < bazCtor.fields.length →
    (bazCtor.fields.getD k default).lvl.inst [] ≈ .zero := by
  intro k hk
  match k, hk with
  | 0, _ =>
    simp [bazCtor, bazField, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
  | 1, _ =>
    simp [bazCtor, bazField, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]

/-- **Every premise of `VEnv.StructEta`, satisfied at once, at a two-field structure.**

The last conjunct is the point: the witness has *two* fields, so the rule is not being
exercised only in its degenerate zero-field (`isDefEqUnitLike`) shape. -/
theorem bazEnv_structEta_premises :
    bazEnv.IsStructure `Baz bazDecl bazType bazCtor ∧
    bazType.indices = [] ∧
    ([] : List VLevel).length = bazDecl.uvars ∧
    (∀ l ∈ ([] : List VLevel), l.WF 0) ∧
    ([] : List VExpr).length = bazDecl.np ∧
    bazEnv.HasArgs 0 bazCtx (bazDecl.params.map (VExpr.instL [])) [] ∧
    bazEnv.HasType 0 bazCtx (.bvar 0) ((VExpr.const `Baz []).mkApp []) ∧
    (bazDecl.isLE = true ∨ ∀ k, k < bazCtor.fields.length →
      (bazCtor.fields.getD k default).lvl.inst [] ≈ .zero) ∧
    bazCtor.fields.length = 2 :=
  ⟨bazEnv_IsStructure, rfl, rfl, nofun, rfl, .nil, .bvar (.zero ..),
    .inr bazCtor_fields_prop, rfl⟩

/-- The rule, fired at that witness: `x ≡ Baz.mk x.a x.b` for `x : Baz`. -/
theorem bazEnv_structEta (H : bazEnv.StructEta) :
    bazEnv.IsDefEq 0 bazCtx (.bvar 0)
      (bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 0)) (.const `Baz []) :=
  H bazEnv_IsStructure rfl rfl nofun rfl .nil (.bvar (.zero ..)) (.inr bazCtor_fields_prop)

/-- …and the term it produces: `Baz.mk` applied to the two field projections, which are
distinct terms.  Nothing here is a one-field structure in disguise. -/
theorem bazEnv_etaExpansion_eq :
    bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 0)
      = (VExpr.const `Baz.mk []).mkApp
          [bazDecl.projTerm bazType bazCtor [] [] [] 0 (.bvar 0),
           bazDecl.projTerm bazType bazCtor [] [] [] 1 (.bvar 0)] := rfl

theorem bazEnv_projMinors_distinct :
    bazCtor.projMinor [] [] 0 ≠ bazCtor.projMinor [] [] 1 := by
  simp [VIndCtor.projMinor, bazCtor]

end Lean4Lean
