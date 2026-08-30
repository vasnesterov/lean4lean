# Structure eta: `structEta` in the spec, and what it unblocks

Stream owning `Verify/TypeChecker/{IsDefEq,Basic,Reduce,WHNF}.lean`,
`Theory/Inductive/Structure{,Closed,Examples}.lean`, `docs/design-inductive.md`.

Every claim is tagged **[checked]** (machine-checked this session; the file and declaration
name are given, and `lake env lean <file>` reproduces it) or **[source]** (read off C++ or Lean
source, not machine-checked).  Nothing is tagged from memory.

Census **19 → 19**.  No `sorry` added, none removed; this stream's file still holds exactly
its two, by name (`isDefEqUnitLike.WF`, `tryEtaStructCore.WF`).  **[checked]**,
`lake env lean scripts/sorry-census.lean`.

---

## Bottom line

1. **`structEta` is in the spec.**  `Theory/Inductive/StructureEta.lean` (new) carries
   `VEnv.StructEta`, `VInductDecl'.etaExpansion`, and the two consequences the checker needs
   (`StructEta.unitLike`, `StructEta.congrSpine`).  The η-expansion term is checked against
   Lean's own elaborator at four structures, two of them with a dependent second field.
   **[checked]**
2. **The relay's residual — "supply `IsStructure` from `isNonRecStructure = true`, that is the
   single step" — is wrong twice over, and both corrections are machine-checked.**
   * It is **not derivable from `AddInduct`'s intended definition either**, so it is not merely
     blocked on `AddInduct` being empty.  `AddIndConsts`' shape predicates and `TrConstant`
     never mention `InductiveVal.isRec`/`.ctors`/`.numIndices` or `ConstructorVal.numFields` —
     the six fields the eta checks read.  `Verify/StructureBridge.lean` proves this at the
     tree's existing `AddInductStages` witness. §3. **[checked]**
   * It is **not the only** step for `tryEtaStructCore`: the loop's *second* argument,
     `s.getAppArgs[i]`, also needs a translation before `isDefEq.WF` fires, and the loop needed
     a `break`-allowing `forIn'` rule that did not exist. §4. **[checked]**
3. **Both of this stream's holes now have real, non-vacuous conditional theorems**, each
   proved through the live gate arm rather than the dead one, so both survive the `AddInduct`
   flip verbatim:
   * `isDefEqUnitLike.WF_of_structEta` — the **whole** statement, from `c.venv.StructEta` plus
     one named bridge.  **[checked]**
   * `tryEtaStructCore.WF_prop` — the `Prop` half, **including the loop**, which the previous
     round reported as the exact failing step.  It no longer fails.  **[checked]**
4. **`design-inductive.md` §6.3 rewritten.**  The `IsNeverZero` side condition is gone (wrong
   for two of three call sites), and it is replaced by the condition the rule actually needs,
   which is F17, not F16 — without it the rule's right-hand side can be ill-typed, which would
   make it *false*, not merely useless. §2.
5. **Non-vacuity, both directions, machine-checked.**  `VEnv.empty_structEta` shows the
   assumption is satisfiable (not a disguised `False`); `bazEnv_structEta_premises` satisfies
   *every* premise at once at a **two-field** structure.  The tree's other two-field structure,
   `barDecl`, **fails** the F17 clause — so the clause is not decorative and the witness is not
   free. §5. **[checked]**

**Kernel Arena not run, and not required**: no executable code was touched.  The four edited
files are `Theory/Inductive/StructureEta.lean` (new, spec only),
`Theory/Inductive/StructureExamples.lean` (`example … := rfl` only),
`Verify/StructureBridge.lean` (new, proofs only) and `Verify/TypeChecker/IsDefEq.lean`
(theorems only, no `@[implemented_by]`, no `partial`, nothing in `Lean4Lean.addDecl`'s cone),
plus `docs/design-inductive.md`.  Baseline to hold remains 185 correct / 6 either / 0 incorrect.

---

## 1. `VEnv.StructEta` — what the rule says

`Theory/Inductive/StructureEta.lean`:

```lean
def VEnv.StructEta (env : VEnv) : Prop :=
  ∀ {U Γ S D T C us ps e},
    env.IsStructure S D T C →                            -- includes C.recFields = []
    T.indices = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) → ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps)
```

with

```lean
def VInductDecl'.projAll (ps e) : List VExpr :=
  (List.range C.fields.length).map fun i => D.projTerm T C us ps [] i e
def VInductDecl'.etaExpansion (ps e) : VExpr :=
  (VExpr.const C.name us).mkApp (ps ++ D.projAll T C us ps e)
```

**Why a predicate and not an `IsDefEq` constructor.**  The content is identical — this is
exactly the constructor's statement — but adding the constructor edits
`Theory/Typing/Basic.lean` and forces a new case into every induction over `IsDefEq` across
`Theory/Typing/{Lemmas,Strong,UniqueTyping,ChurchRosser}.lean` and `Verify/`, files this
stream does not own.  The predicate is what a consumer can use *today* (§4 uses it), and when
the constructor lands `StructEta` becomes a one-line theorem rather than being discarded.

**Gate-for-gate correspondence with the two checks** (`~/lean4/src/kernel/type_checker.cpp`
`try_eta_struct_core` `:889`, `is_def_eq_unit_like` `:1159`; `Lean4Lean/TypeChecker.lean:656`
and `:849`): **[source]**

| checker gate | clause |
|---|---|
| `isNonRecStructure`: `isRec = false`, `ctors = [_]` | `env.IsStructure S D T C` |
| `numIndices = 0` | `T.indices = []` |
| the projections must typecheck (`inferProj`, F17) | the `isLE = true ∨ …` disjunction |
| `inferType t ≡ inferType s`, giving `t : S ps` | `env.HasType U Γ e ((const S us).mkApp ps)` |

**Information-flow audit** (the check the method note demands): the conclusion mentions
`S D T C us ps e Γ U`; `S D T C` are pinned by `IsStructure`, `us` and `ps` by the length and
`HasArgs` clauses, `e` by the `HasType` clause.  No binder is left free by the premises.

**Derived, machine-checked:** **[checked]**

* `VEnv.structEta_of_prop` — for a `Prop`-valued structure the rule is `IsDefEq.proofIrrel`,
  given that the η-expansion is well typed.  So the `Prop` case needs no new rule.
* `VEnv.StructEta.unitLike` — the zero-field consequence: two inhabitants of `S ps` are
  definitionally equal.  This is exactly what `isDefEqUnitLike` claims, and it needs no
  `TrProj`, no projections, no injectivity.
* `VEnv.StructEta.congrSpine` — eta then spine congruence: `e ≡ C.mk ps args` from the field
  comparisons.  **Nothing in it compares parameter lists** — the `HasArgsDF` is built at the
  single spine `ps`, shared by both sides — confirming the previous round's correction to
  `research-structeta.md` §5 in the form of a proved lemma.

---

## 2. The `IsNeverZero` correction, and the condition that replaces it

`docs/design-inductive.md` §6.3 proposed `(D.lvl.inst ls).IsNeverZero` as a side condition,
imported from `toCtorWhenStruct`'s F16 guard.  Two things are now recorded there.

**It is wrong for these call sites.**  Neither `tryEtaStructCore` nor `isDefEqUnitLike` tests
the structure's universe at all; both therefore fire on `Prop` structures (`And`, `True`),
which an `IsNeverZero` rule would not cover.  **[source]**, re-read gate for gate this round.
It would not have been *unsound* — the `Prop` case is independently free — only useless at two
of three sites.

**But a side condition is needed, and it is F17.**  `IsDefEq` implies both sides are well
typed, so a rule whose right-hand side is ill-typed is **false**, not merely useless.  For a
small-eliminating block the η-expansion's projections are recursor applications at elimination
level `(C.fields.getD k _).lvl`, legal only when that level is `≈ .zero`.  `StructEta`
therefore carries `TrProj`'s F17 clause **minus its "unused fields are exempt" guard**: eta
projects every field, so every field is in scope.

That difference is not hypothetical.  `Verify/Typing/ProjLevelWitness.lean`'s `barDecl` — a
two-field `Prop` structure whose field 0 has level `.succ .zero` and is *unused* — is
admissible for `TrProj` at `i = 1` (`barEnv_TrProj`) and **inadmissible** for structure eta.
The F17 clause is what separates them. **[checked]**, `barField0_lvl_ne_zero`.

---

## 3. The bridge is not derivable from the intended `AddInduct` either  **[checked]**

`Verify/StructureBridge.lean` (new).

`StructureBridge` names the step the relay identified.  The finding is about `AddInduct`'s
intended definition, `AddInductStages` (`Verify/Environment/Basic.lean`) and its nested-aware
replacement `AddInductStagesR` (`Verify/Environment/InductR.lean`).  Both relate the constant
map to the abstract block through `AddIndConsts` at the shape predicates

```
fun ci => ∃ v, ci = .inductInfo v      fun ci => ∃ v, ci = .ctorInfo v      … .recInfo …
```

and through `TrConstant`, which is `safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
TrExprS env … ci.type ci'.type`.  **Neither mentions `InductiveVal.isRec`, `.ctors`,
`.numIndices` or `.numParams`, or `ConstructorVal.numFields`, `.numParams` or `.induct`** — and
those six fields are exactly what `Environment.isNonRecStructure` and the two eta checks read.

> **SUPERSEDED — this section describes the state before the shape predicates were
> strengthened.  See `docs/handoff-inductive-add.md` §§I–L for the current state.**  `IndShape`
> and `CtorShape` **landed**: they are now the shape predicates of `AddInductStages` and
> `AddInductStagesR`, `addInductStages_with` was replaced by the `↔`
> `R10.Wit.addInductStages_pinned`, `addInductStages_bookkeeping_free` is gone, and
> `isNonRecStructure_not_determined` survives only in its `isRec` component — a residue that
> `R10.Wit.isNonRecStructure_one_sided` shows can only make the checker *refuse* eta.  The
> bridge is still not provable, but the blocker moved: it is now `VEnv.IsStructure.types`
> (`D.types = [T]`), which is **false** for a member of a mutual non-recursive block on which
> `isNonRecStructure` answers `true` (`MutNonRec.indShapeOf_not_singleton`).

Proved, at the tree's own `AddInductStages` witness `R10.Wit.decl` (state before the repair):

* `R10.Wit.addInductStages_with` — `AddInductStages m VEnv.empty decl m' env'` holds with the
  map's `InductiveVal` carrying *any* `numIndices`, `ctors` and `isRec`.  The proof is
  `addInductStages_wit`'s with `uInd` replaced by a parameterised `uIndWith`; that the
  replacement goes through untouched **is** the finding.
* `R10.Wit.addInductStages_bookkeeping_free` — two runs, same block, same map and environment
  in, **same `VEnv` out**, different bookkeeping.
* `R10.Wit.isNonRecStructure_not_determined` — the consequence: one run makes
  `isNonRecStructure` say `true`, the other `false`, with the abstract side identical.

So no lemma of the form `isNonRecStructure I = true → (anything about venv)` could be proved
from `AddInductStages`/`AddInductStagesR` **as they then stood**.  `IndShape` and `CtorShape`
were written out in that file as the strengthened shape predicates `AddIndConsts` must be
instantiated at, so the eventual edit would be a substitution rather than a redesign; it was.

**Note what is *not* claimed.**  A refutation of the bridge itself (`∃ D T C, IsStructure …`) is
*not* given, and would be expensive: `IsStructure` quantifies over all blocks, so ruling it out
needs the G4 uniqueness that `Verify/Typing/StructureUniq.lean` splits and does not close.  What
is proved is the information-flow statement, which is what settles derivability.

The vacuous route is also unavailable: `TrEnv.not_inductInfo` needs the name to be one the
`VEnv` already holds, which `isNonRecStructure I = true` alone does not give.

---

## 4. What closed in `Verify/TypeChecker/IsDefEq.lean`  **[checked]**

Three new declarations, all sorry-free in their own right, all with the *same borrowed* hole
cone as `isDefEqUnitLike.WF_prop`: `{IsDefEqU.forallE_inv_stratified, IsDefEqU.weakN_iff,
TrProj.uniq}` — every one entering through `inferType.WF`'s appeal to unique typing.  **No
structure-eta content is borrowed.**  (Measured by a transitive `getUsedConstantsAsSet` sweep
intersected with the 19 census names, with the `.thmInfo` trap handled; note `TrProj.wf` has
dropped out of the cone since it was proved, and `weakN_iff` has entered.)

### `isDefEqUnitLike.WF_of_structEta` — the whole statement

```lean
theorem isDefEqUnitLike.WF_of_structEta
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.StructEta) (hbr : UnitLikeBridge c) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂'
```

`Prop` case included — this subsumes `WF_prop`.  The route is `StructEta.unitLike`: at zero
fields the η-expansion is the same closed term `C.mk ps` for both inhabitants, so the two
`HasType`s the checker establishes at a common type give `e₁' ≡ e₂'` by `trans`.  When
`StructEta` and the bridge become theorems, `isDefEqUnitLike.WF` is this lemma applied to them.

`UnitLikeBridge` is stated at the exact gate the function tests (`.inductInfo` with
`isRec = false`, `ctors = [cn]`, `numIndices = 0`; `.ctorInfo` with `numFields = 0`) and
bundles the typing side conditions `StructEta` needs, which come from the same place — the
block's declaration — and have no cheaper source today.

### `tryEtaStructCore.WF_prop` — the `Prop` half, loop included

The previous round's report ended at the loop, with the residual named as `IsStructure`.  The
loop is now done:

* `RecM.WF.forIn'Break` (new, in the same file) — a loop rule allowing `break`.
  `M.WF.forIn` (`Verify/TypeChecker.lean`) requires the body to `yield` every iteration, which
  **none** of `tryEtaStructCore`'s, `isDefEqApp`'s or `isDefEqArgs`' loops do.  The invariant is
  not indexed by the remaining list (a `break` skips it); what it carries is the state
  discipline, which is what `RecM.WF` demands beyond the postcondition and which *is* the loop
  obligation.  Reusable.
* `Std.Legacy.Range.forIn'_eq_forIn'_range'` converts `forIn' [np:args.size]` into a
  `List.forIn'` over `List.range'`, which is what makes the rule applicable.  This step was not
  in the previous round's account.
* `EtaStructBridge c t s` — the bridge, in the form the loop consumes: for each field index,
  *two* translations, `c.TrExprS (.proj I (i - np) t) _` **and** `c.TrExprS s.getAppArgs[i] _`.

That second translation is the correction to the relay.  `TrProj.mk`'s `IsStructure` is why the
first is blocked, but `isDefEq.WF` needs both arguments translated before it fires, so the
residual per iteration is two facts, not one.

**Honest note on today's satisfiability.**  `EtaStructBridge c e₁ e₂` is currently provable for
every `c`: its premise asks for a `.ctorInfo` under the head of a translated term, and
`TrEnv.not_ctorInfo` forbids that.  So the theorem is instantiable today but the instantiation
is empty.  What it buys is that the conclusion is derived from `proofIrrel` and the loop rule
rather than from the vacuity, so it keeps working when the bridge stops being free — the same
standard `WF_prop` was held to.

### What remains for the full `tryEtaStructCore.WF`

The non-`Prop` case, and it is now a precisely shaped job: carry the per-iteration
`c.IsDefEqU (proj_i e₁') args_i'` through `forIn'Break`'s invariant instead of discarding it,
assemble them into a `VEnv.HasArgsDF` over the constructor's field telescope, and close with
`VEnv.StructEta.congrSpine`, which is proved and waiting.  Two ingredients are missing: the
invariant has to be indexed by the fields processed so far (`forIn'Break`'s deliberately is
not — a `break` version indexed by a prefix is a second lemma), and `e₂'` has to be decomposed
as `(.const C.name us).mkApp (ps ++ args')`, which is `AppStack.build` plus `TrExprS.const`
inversion.  Neither was attempted.

---

## 5. Non-vacuity  **[checked]**

*The assumption is consistent.*  `VEnv.empty_structEta` — the empty environment declares no
structure, so `StructEta` holds there.  A theorem taking `StructEta` as a hypothesis is
therefore not vacuous for want of a model of the hypothesis.

*The premises are jointly satisfiable at a two-field structure.*
`Theory/Inductive/StructureEta.lean` builds
`structure Baz : Prop where (a : ∀ p : Prop, p) (b : ∀ p : Prop, p)` as `bazDecl`, proves
`bazDecl.WF VEnv.empty` outright, derives `bazEnv_IsStructure`, and
`bazEnv_structEta_premises` discharges **every** clause of `StructEta` at once, with
`bazCtor.fields.length = 2` as the last conjunct.  `bazEnv_structEta` fires the rule at that
witness; `bazEnv_etaExpansion_eq` spells out the resulting term as `Baz.mk` applied to the two
projections and `bazEnv_projMinors_distinct` shows they really are two.

The acceptance criterion the method note asks for is met in the strong form: this is not a
one-field structure, and the F17 clause is discharged in its **small-elimination** branch
(`bazDecl.isLE = false`, so the `.inl` disjunct is unavailable), which is the branch `barDecl`
refutes.

*The η-expansion term is the right term.*  `Theory/Inductive/StructureExamples.lean` adds five
`rfl` checks against Lean's own elaborator: `Prod`, `Sigma` (dependent second field), `And`
(a `Prop` structure — the case `IsNeverZero` would have excluded), `Subtype` (dependent `Prop`
field), plus the F17 clause in its non-trivial disjunct at `And`.  All four are two-field.

---

## 6. Corrections to the incoming relay

* "**The residual is: supply `IsStructure` from `isNonRecStructure = true`.  That is the single
  step blocking `tryEtaStructCore.WF`.**"  Two errors.  It is not a single step (§4: the loop
  also needs the argument translations, and needed a `break` loop rule that did not exist), and
  it is not merely waiting on `AddInduct` gaining constructors (§3: it does not follow from
  `AddInduct`'s intended definition either).
* "**`design-inductive.md`'s `IsNeverZero` side condition is wrong for these two call sites.**"
  Correct, and now fixed — but incomplete: dropping it is not enough, because a *different*
  side condition (F17) is needed to keep the rule's right-hand side well typed. §2.
* "**`TrProj.wf` is now proved.**"  Confirmed independently: it has dropped out of the measured
  hole cone of everything in this corner. `IsDefEqU.weakN_iff` has entered it.
* Everything else in the relay that this round touched checked out: the `Prop` half of
  `isDefEqUnitLike` does enter the live gate arm; `TrProj.mk` reads its parameter list off a
  `HasType` premise so no injectivity is needed (now a proved lemma, `StructEta.congrSpine`);
  neither C++ function tests the structure's universe.

---

## 7. What to pick up first

1. ~~**`AddInduct`'s shape predicates.**  §3's `IndShape`/`CtorShape`.~~  **DONE** — landed in
   `AddInductStages` and `AddInductStagesR`; see `docs/handoff-inductive-add.md` §§I–K.  What
   replaces it as the first item is **`VEnv.IsStructure.types`**: `D.types = [T]` is not
   attainable and is not true of what `isNonRecStructure` accepts, so it must weaken to
   `T ∈ D.types` (`docs/handoff-inductive-add.md` §L has the exact edit and its dependents).
2. **The non-`Prop` half of `tryEtaStructCore.WF`** — §4's closing paragraph names the two
   missing ingredients and the lemma (`StructEta.congrSpine`) that is already proved and waiting.
3. **`structEta` as an `IsDefEq` constructor.**  `VEnv.StructEta` is the statement; promoting it
   is the coordinated multi-file change §1 describes.  Doing it turns `StructEta` from a
   hypothesis into a fact and both §4 theorems into halves of the real ones.
4. **Do not** close either hole vacuously, and do not weaken or build on
   `tryEtaStructCore_never_true` / `isDefEqUnitLike_never_true`.  Unchanged from last round.
