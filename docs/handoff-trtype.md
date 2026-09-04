# handoff-trtype — `TrIndDeclN.trType`, the general producer

Field under attack: `Lean4Lean.TrIndDeclN.trType`
(`Lean4Lean/Verify/Environment/InductR.lean:294`), whose statement as written is

```
trType : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T
```

I own exactly this file and `Lean4Lean/Verify/Inductive/TrTypeProducer.lean`.

## §0 PRIORS — written before the first measurement

Recorded so they can be scored. Numbered so a successor can say which were wrong.

P1. `Lean4Lean.TrIndType` will be a structure (or a `∧` of clauses) whose real content is
    a **`TrExprS`** of the member's type expression at the **pre-block** environment `env`
    (the block's own type constants NOT yet declared), plus a name equation
    `t.name = T.name`, plus possibly a `VEnv.IsType`/level-bound side condition.
    Confidence: high on the `TrExprS`, medium on the name equation, low on `IsType`.

P2. The `shape.lean` scan reported in the brief (10 constants, all projections/recursors,
    nothing concluding `TrIndType`) will **re-verify**. I expect the field to be genuinely
    open absolutely — no producer under any name. Confidence: medium-high. The brief's
    *numbers* have been reliable; this one is a number.
    Counter-scenario I must actually check: a producer stated over `TrIndDecl` (the
    non-nested predicate) rather than `TrIndDeclN`, whose conclusion head is therefore
    `TrIndType` too and which `shape.lean` would have listed. If it lists only
    projections, that scenario is dead.

P3. Why the block case is free: `Lean4Lean.InductiveDeclExamples.tr_ntreeType` takes no
    hypotheses because at the concrete example block the member's type is a **closed
    literal `Expr`** and the target `VExpr` is a closed literal too, so `TrExprS` is
    provable by a finite tower of constructor applications (`.sort`, `.forallE`, `.const`
    with an explicit `env.constants ... = some ...` discharged by `rfl`/`decide` against the
    concrete `env`). Nothing needs to be *derived* — it is exhibited. Generality breaks
    exactly where the concrete `env` disappears: for arbitrary `types` the `Expr` is an
    unknown open term, and no closed term of `TrExprS` exists; the fact must come from the
    checker run that accepted the block.

P4. What a general producer needs: a `TrExprS env Us [] t.type T.type` for each member,
    which I expect is **not** currently recorded by the run data
    (`AddInductStagesR` / whatever `Result` structure the nested path carries). I expect
    the run only records `VEnv`-level typing (`HasType`/`IsType`) of the *translated*
    `VIndType.type`, never the *correspondence* to the surface `Expr`. So I predict:
    **genuinely new obligation**, and the honest deliverable is an `↔` reduction, not a
    proof. Confidence: medium. This is the prediction most likely to be wrong, because
    `TrIndDeclN`'s sibling field `trCtors` already carries a `TrIndCtorR`, which must
    contain a `TrExprS` of the constructor type — if the run can supply that, it can
    supply this, and then the obligation is *derivable*, not new.

P5. Statability trap: the new obligation, if new, must be statable in
    `Verify/Environment/InductR.lean`'s import cone. Since `TrIndType` itself is already
    named there, anything phrased in terms of `TrIndType` is trivially statable; a clause
    phrased in terms of the *checker's monadic run* may not be. I predict statability is
    NOT the binding constraint here (unlike the earlier rejected proposal), because the
    obligation can be phrased purely as a `TrExprS`, and `TrExprS` is plainly in scope
    wherever `TrIndType` is.

P6. Vacuity trap: `∃ D K R, TrIndDeclN …` closed existentially was proved vacuous before —
    I predict the vacuity there came from `∃`-closing over `D`, letting a degenerate `D`
    satisfy everything. My arity-0 witness must therefore fix `D`'s types to the real
    `ntreeAux` data and existentially close over **nothing structural**, or close only
    over the proof, and must route through the general lemma I prove rather than through
    `ntreeAux_trIndDeclN`. Confidence: high that this is the shape of the trap.

P7. `Lean4Lean.TrIndType`'s arity: I predict 4 explicit arguments (`env Us t T`) — read off
    the field, so this is not really a prediction. What I do predict: it is a `structure`
    with 2 or 3 fields, so `shape.lean`'s "10 constants, all projections or recursors" is
    consistent with 1 structure + ~3 fields + recursor + `.mk` + `casesOn`/`noConfusion`
    padding. If shape returns 10 and I count fewer than ~3 field projections, my model of
    the definition is wrong.

## §1 MEASUREMENTS (appended one per call, before the next call)

### M1 `HEADS="Lean4Lean.TrIndType" shape.lean` — the brief's scan, REFUTED IN DETAIL

population 440 built modules. **12** constants, not the briefed 10. Full list:

FIELDS (2): `Lean4Lean.TrIndDecl.trType` (arity 12, `Verify.Environment.Induct`),
`Lean4Lean.TrIndDeclN.trType` (arity 15, `Verify.Environment.InductR`).

plain (10): `Lean4Lean.TrIndDecl.{rec,casesOn,recOn}` (arity 9),
`Lean4Lean.TrIndDeclN.{casesOn,rec,recOn}` (arity 12), `Lean4Lean.TrIndDecl.mk` (13),
`Lean4Lean.trIndDeclN_of_ownId` (21, `Verify.Inductive.TrIndDeclNProducer`),
`Lean4Lean.TrIndDeclN.mk` (21), `Lean4Lean.trIndDeclN_of_restoreData` (21,
`Verify.Inductive.TrIndDeclNProducer`).

Reading: the brief's *number* is wrong by 2 and its *characterisation* is wrong in kind —
two of the ten plain declarations are **not** projections or recursors, they are
`TrIndDeclNProducer`'s two producers. They mention `TrIndType` because they take the
`trType` clause as a **hypothesis**, which is the very thing under attack: so the field is
open in the sense that matters (nothing *concludes* `TrIndType` itself), but the scan as
briefed did not establish that. P2 scored: the conclusion survives, the stated evidence
did not.

Note what is NOT in the list: no declaration whose conclusion head is `TrIndType` alone.
So `TrIndType` has **zero producers**, confirmed structurally.

### M2 (a) what `trType` requires, fully unfolded (source read, `Verify/Environment/Induct.lean:86`)

```
def TrIndType (env : VEnv) (Us : List Name) (t : InductiveType) (T : VIndType) : Prop :=
  t.name = T.name ∧ TrExprS env Us [] t.type T.type
```

so the field is, with nothing hidden:

```
∀ (j : Nat) (t : Lean.InductiveType) (T : Lean4Lean.VIndType),
  types[j]? = some t → D.types[j]? = some T →
    t.name = T.name ∧ Lean4Lean.TrExprS env Us [] t.type T.type
```

`env` is the **pre-block** environment (`TrIndDeclN`'s first explicit argument), the empty
local context, `Us` the block's universe parameters, `t.type` the surface `Lean.Expr` as the
user wrote it and `T.type` the `VExpr` stored *verbatim* in `VIndType` (the docstring:
"the type **as stored**; F1 bites on its decomposition, not on the type itself").

P1 scored **right on content, wrong on form**: name equation + `TrExprS`, no `IsType`
side condition — but it is a `def` returning an `And`, not a structure, so P7 is **wrong**:
`TrIndType` has *no* field projections at all, and the two `FIELD` hits in M1 are the
projections of the two containing structures. That also explains why M1 found 12 and not the
briefed 10 with a different composition than either of us assumed.

### M3 `exists.lean` on the six names I need (one call, all six recorded)

```
Lean4Lean.TrExprS.unique                             FOUND  Verify.Typing.Lemmas          arity 9  cone 3644  hole false  sorryAx false  watched: none of 6
Lean4Lean.TrExprS.IsUnique                           FOUND  Verify.Typing.Lemmas          arity 1  cone   39  hole false  sorryAx false  watched: none of 6
Lean4Lean.TrIndType                                  FOUND  Verify.Environment.Induct     arity 4  cone   21  hole false  sorryAx false  watched: none of 6
Lean4Lean.InductiveDeclExamples.tr_ntreeType         FOUND  Verify.Inductive.FlipConstruct arity 1 cone  737  hole false  sorryAx false  watched: none of 6
Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN  FOUND  Verify.Inductive.TrIndDeclNProducer arity 0 cone 5958 hole false sorryAx false watched: none of 6
Lean4Lean.trIndDeclN_of_ownId                        FOUND  Verify.Inductive.TrIndDeclNProducer arity 21 cone 1154 hole false sorryAx false watched: none of 6
```

The brief's figures for `ntreeAux_trIndDeclN` (arity 0, cone 5958, clean) are **exact**.
`tr_ntreeType` has **arity 1** (the implicit `{env : VEnv}`), i.e. no hypotheses — the brief is
right, and M4 explains why.

### M4 (b) WHY THE BLOCK CASE IS FREE — read off `tr_ntreeType` (`FlipConstruct.lean:121`)

```
theorem tr_ntreeType : TrExprS env [`u] []
    (exprOf% NTree) (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  trS_tac
```

`env` is a section `variable` and **none** of the section's five `env.constants …` hypotheses
(`hList`/`hNil`/`hCons`/`hNTree`/`hNode`) is `include`d. So the statement holds at **every**
`VEnv` whatsoever. The reason is entirely syntactic: `NTree`'s arity is `Type u → Type u`,
whose translation `.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))` is built from
`TrExprS.forallE` and `TrExprS.sort` **only**. `TrExprS.const` is the sole constructor that
consults `env.constants`, and `TrExprS.fvar`/`bvar` the sole ones consulting the local context;
a sort-and-pi-only type touches neither. `trS_tac` therefore closes it structurally with
`type_tac` side goals that are level arithmetic, not environment lookups.

**So the block case is free because the member's arity is constant-free and closed** — and it
is free *uniformly in `env`*, which is a much stronger statement than "free at this block".
That is precisely what does not generalise: the instant a member's arity mentions one constant
(`inductive Vec (α : Type) : Nat → Type` — `Nat`), the derivation needs
`env.constants ``Nat = some ⟨0, T⟩` with `T` the *translated* type, plus a level-arity check,
i.e. it needs facts about the pre-block environment; and for an *arbitrary* block `t.type` is an
opaque `Expr` and `T.type` an opaque `VExpr`, so there is no structural derivation at all.
P3 scored **right**, with the mechanism sharper than I wrote it (constant-freeness, not merely
"closed literal": literalness alone would not have made it uniform in `env`).

### M5 the route, decided from M1–M4 (source reads, no new scan)

* `TrExprS.unique` (`Verify/Typing/Lemmas.lean:2648`)
  `(H : IsUnique e) (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂`
  — translation is **functional** wherever the surface term has no `.proj`. So `T.type` is not
  a free choice: it is *determined* by `t.type`. That kills the "pick a friendlier `D`" escape
  and makes an `↔` possible.
* `D` is existentially quantified at the assembly point (`AddInductiveRunRealises`,
  `Verify/Inductive/AddInductiveStep.lean:405`: `∃ D : VInductDecl', TrIndDecl … D ∧ …`), so
  *satisfiability* of the field is a construction, not a derivation — and by the previous point
  the construction is forced.
* `TrExprS.const` is the only constructor reading `env.constants`; `bvar`/`fvar` the only ones
  reading the context. Hence the env-uniform fragment: arities built from `.sort`, `.forallE`
  and `.mdata` alone.
* Import discipline for the witness: `Verify.Inductive.FlipConstruct` is imported by exactly two
  modules (`TrIndDeclNProducer`, `Environment.AddDeclPath`). My file imports
  `Verify.Environment.InductR` + `Verify.Inductive.ValAtParam`, so **`tr_ntreeType` is not even
  in scope** — the witness cannot borrow the block lemma, by module structure rather than by
  promise.

### M6 (c) IS THE `TrExprS` AVAILABLE? — `exists.lean` on the general route, and it is NOT clean

```
Lean4Lean.TypeChecker.checkType.WF  FOUND  Verify.TypeChecker      arity  4  cone 18795  hole false  sorryAx TRUE
   holes: [TrProj.weak'_inv, TypeChecker.Inner.isDefEqUnitLike.WF, TypeChecker.Inner.tryEtaStructCore.WF,
           VEnv.IsDefEqU.weakN_iff, VEnv.IsDefEqU.forallE_inv_stratified, VEnv.WF.rigidShapeUniqNS,
           VEnv.NormalEq.descend, TypeChecker.Inner.inferProj.WF]
   *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
Lean4Lean.TrExprS.weakFV_inv        FOUND  Verify.Typing.Lemmas    arity 16  cone  8653  hole false  sorryAx TRUE
   holes: [TrProj.weak'_inv, VEnv.IsDefEqU.weakN_iff, VEnv.IsDefEqU.forallE_inv_stratified,
           VEnv.WF.rigidShapeUniqNS, VEnv.NormalEq.descend]
   *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
Lean4Lean.TrExprS.mono              FOUND  Verify.Typing.Lemmas    arity  8  cone  3814  hole false  sorryAx false  watched: none of 6
Lean4Lean.TrExprS.defeqDFC          FOUND  Verify.Typing.Lemmas    arity  9  cone  8486  hole false  sorryAx TRUE
   holes: [VEnv.IsDefEqU.weakN_iff, VEnv.IsDefEqU.forallE_inv_stratified, VEnv.WF.rigidShapeUniqNS,
           VEnv.NormalEq.descend]
   *** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***
Lean4Lean.TrIndDecl.trType          FOUND  Verify.Environment.Induct arity 12 cone 559  hole false  sorryAx false  watched: none of 6
```

**Answer to (c)'s question, and it has three parts.**

1. `trType` needs the `TrExprS` at the **pre-block** environment and the **empty** local
   context — *not* at the staged one. That is forced and correct: the members' arities are
   type-checked before any of the block's constants exist (`Inductive/Add.lean:210`,
   `_ ← checkType type` inside `checkInductiveTypes`, before `declareInductiveTypes`), and
   `TrExprS.const` on a block member would be unsatisfiable at `env`. So unlike `trCtors`,
   this field must stay unstaged, and the "staged environment" premise the brief asked about is
   the wrong premise for it.
2. It is **available, not new**: `TypeChecker.checkType.WF` (`Verify/TypeChecker.lean:197`)
   yields `∃ e' ty', c.TrTyping e ty e' ty'`, whose first component is
   `TrExprS venv c.lparams c.vlctx t.type e'`, at exactly that check. For member `j = 0` the
   local context is empty and this *is* the obligation; for `j ≥ 1` the check happens inside the
   earlier members' `withLocalDecl` scopes (`loopInd (dIdx+1)` is called under them), so it needs
   `TrExprS.weakFV_inv` to strengthen the earlier params/indices away — legitimate, since
   `checkNoMVarNoFVar` has already established the arity is fvar-free.
3. **But that route is not clean**, and this is the measured finding: `checkType.WF` has 8 holes
   and both watched `IsDefEq.uniq`/`uniqU` in its cone (18795), and `weakFV_inv` has 5 holes and
   the same two watched statements (8653). So "derivable" here means *derivable from
   contaminated machinery*. The fragment route below (§1–§3 of my file) reaches the same field
   with cone in the hundreds and **nothing watched, no holes** — because it never calls the
   checker at all. P4 scored: I predicted "genuinely new obligation, medium confidence" — that is
   **wrong**, it is derivable; but the interesting fact is the one I did not predict, that
   derivability costs the two watched statements while a nontrivial general class does not.

### M7 what I proved — `exists.lean` on every new declaration (all in
`Lean4Lean/Verify/Inductive/TrTypeProducer.lean`, all `hole false`, all `sorryAx false`,
all `watched: none of 6`)

```
Lean4Lean.sortPiTr?                                     arity 2  cone  578
Lean4Lean.trExprS_of_sortPiTr                           arity 6  cone  797
Lean4Lean.trIndType_iff_of_sortPiTr                     arity 6  cone 3689
Lean4Lean.trType_of_sortPiTr                            arity 10 cone 3692
Lean4Lean.trType_iff_of_sortPiTr                        arity 5  cone 3693
Lean4Lean.TrIndType.rigid                               arity 8  cone 3652
Lean4Lean.trType_iff_exists_trans                       arity 4  cone  558
Lean4Lean.exists_indTypes_of_trExprS                    arity 4  cone  657
Lean4Lean.no_trIndType_of_undeclared                    arity 6  cone 3609
Lean4Lean.InductiveDeclExamples.ntreeAux_trType_uniform arity 6  cone 3714
Lean4Lean.InductiveDeclExamples.ntreeAux_trType_witness arity 0  cone 4006
```
(also in the file, not separately measured: `sortPiTr?_isType`, `isUnique_of_sortPiTr`,
`trType_congr_prefix`, `exists_indTypes_append`, `sortPiTr?_none_of_const`,
`no_trExprS_of_undeclared`, `InductiveDeclExamples.ntreeIndType_sortPi`, and §7's two
shape-check `example`s.)

`exists.lean`'s population reads 442 built modules here against `sorry-census-all.lean`'s 445
in-population; that 3-module difference is the census's pass-B `Replay` closure and predates this
round (it was 440 vs 445 before my module existed).

### M8 round-close

* whole-tree `lake build`: **green**, 1628 jobs, `Built Lean4Lean.Verify.Inductive.TrTypeProducer`.
* `scripts/sorry-census-all.lean`: **HOLES 13**, **in population but NOT BUILT 0** (BUILT 445).
  The 13 are unchanged: `TrProj.weak'_inv`, `TypeChecker.Inner.inferProj.WF`,
  `TypeChecker.Inner.isDefEqUnitLike.WF`, `TypeChecker.Inner.tryEtaStructCore.WF`,
  `VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.IsDefEqU.weakN_iff`, `VEnv.NormalEq.descend`,
  `VEnv.WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`, `addDecl.WF`, `kernel_complete`,
  `kernel_sound`, `leanTT_equiconsistent_zfc_omega_inaccessibles`.
* three guards: `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`;
  `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`;
  `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`.
* section-variable warnings: **0 in-repo**. The build emits exactly one
  "automatically included section variable(s) unused" warning and it is in the dependency
  (`Foundation/FirstOrder/SetTheory/Z.lean:35`). `TrTypeProducer.lean` emits **no** warning of
  any kind. (For the record, 66 pre-existing "Variable name … is not explicitly referenced"
  warnings live in read-only `Lean4Lean/Theory/*` files; none is mine and none is new.)

## §2 PRIORS SCORED

* **P1 right on content, wrong on form.** `TrIndType` is name-equation + `TrExprS`, no `IsType`
  — but it is a `def` returning `And`, not a structure.
* **P2 conclusion right, evidence refuted.** Nothing concludes `TrIndType`; but the briefed scan
  (10 constants, all projections/recursors) is wrong on both counts — 12 constants, two of them
  `TrIndDeclNProducer`'s producers, which mention `TrIndType` as a *hypothesis*.
* **P3 right, and sharper than I wrote it.** Free because the arity is **constant-free**, hence
  uniform in `env` — not merely because it is a closed literal.
* **P4 wrong in the interesting direction.** I predicted a genuinely new obligation. It is
  derivable (`TypeChecker.checkType.WF` + `TrExprS.weakFV_inv`), but derivability drags both
  watched statements and 8/5 holes into the cone, which I did not predict; the fragment route
  reaches a nontrivial general class with a clean cone instead.
* **P5 right.** Statability was not the binding constraint: everything I needed is phrasable as
  `TrExprS`/`sortPiTr?` and `TrTypeProducer.lean` imports only `InductR` + `ValAtParam`.
* **P6 right in shape.** The vacuity risk is in what gets existentially closed. My witness closes
  over `env₁` only (pinned by `VEnv.empty.addInduct' listDecl = some env₁`), keeps `ntreeAux`,
  `[ntreeIndType]`, `ntreeK` concrete, asserts `uvars = 1`, `params = [.sort (.succ (.param 0))]`,
  `types.length = 2`, and carries two extra conjuncts — the block-level `↔` (tightness) and an
  explicit inhabited-pair conjunct (`∃ T, ntreeAux.types[0]? = some T ∧ T.name = ``NTree ∧
  TrIndType env₁ [`u] ntreeIndType T`) so the clause cannot be true by having no matching index.
* **P7 wrong.** `TrIndType` is a `def`, so it has zero field projections; my explanation of M1's
  count was wrong even though the count itself surprised me in the right direction.
