# handoff-trexprsgeneral

Target: the last open field of `Lean4Lean.TrIndDeclN`, namely `trCtors`, which needs
`TrIndCtorR env₁ Us D R j c C` = `c.name = R.ctorName C.name ∧ TrExprS env Us [] c.type (C.typeR D R j)`.
The `TrExprS` half is the job. Owned files: `Lean4Lean/Verify/Inductive/TrExprSGeneral.lean` (new),
this doc (new). Everything else read-only.

## PRIORS (written before the first measurement of this round)

P1. The class. I expect the right syntactic class is an inductive predicate over `Expr`
    with exactly five constructors mirroring `trS_tac`'s five cases: `sort`, `bvar`,
    `const`, `app`, `forallE`. I predict I will NOT be able to make it purely syntactic:
    the brief's "hard floor" says `TrExprS.app` carries two `env.HasType` premises and
    `.forallE`/`.lam` carry `env.IsType`. Prediction: the class must carry the target
    `VExpr` and the typing side-conditions as *fields of the class itself*, i.e. the
    class is really a "TrExprS-without-the-inductive-hypotheses" relation, and then the
    theorem is near-trivial (a fold), which would be a WEAK result. Confidence 0.6.
    The alternative and much better outcome: carry the *VExpr* along but derive typing
    from a wellformedness hypothesis on the environment (`VEnv.WF` + each constant's
    `VConstant` being typed), so typing is PRODUCED, not assumed. Confidence 0.3 this
    is achievable this round.

P2. Consequence I predict and must report plainly: the obligation I assume will be of
    comparable strength to what I produce, UNLESS `env.HasType`/`env.IsType` for the
    relevant pieces is derivable from `VEnv.WF env` plus the `VConstant` lookups. My
    prior is that for `forallE` it is derivable-ish (sort typing is cheap) but for `app`
    the two `HasType` premises need the function's type to be a `forallE` matching the
    argument, which is exactly a typing derivation. So: prediction 0.75 that a genuinely
    typing-free general theorem is impossible and I will report the floor as a finding.

P3. Environment hypothesis shape. I predict: a hypothesis of the form
    `∀ n ls, n ∈ constNames e → ∃ ci, env.constants n = some (some ci) ∧ ...`,
    i.e. quantified over the const leaves. Prediction 0.7 that I instead find it cleaner
    to make the class *carry* the `VConstant` at each const leaf (a "decorated" class),
    which sidesteps a separate `constNames` function. Cheaper, and matches how the four
    existing bridges' hand content is described (a `VConstant` for each `Expr.const` leaf).

P4. Arity-0 witness at `Lean4Lean.InductiveDeclExamples.ntreeAux`. I predict the arity-0
    constructor type is a closed `Expr` that is a bare `const`/`app` spine with no
    `forallE`, so the class instance is small. Risk flagged in the brief: do not let it
    become `nfnAux`-degenerate. Prediction 0.5 that "arity 0" here still means a nonempty
    parameter telescope (params are `forallE`s even at arity 0 for the *fields*), so the
    witness is non-degenerate. Non-borrowing structurally: do NOT import FlipConstruct.

P5. Which blocks `trCtors` gets discharged for. Prediction: only blocks whose every
    constructor type lies in the five-case fragment, i.e. no `lam`, no `letE`, no `proj`,
    no literals, no `mdata`. Real Lean constructor types in this repo's examples are
    plausibly all in the fragment. Prediction 0.65 that the examples' ctor types are all
    in-fragment, so the instantiation covers all example blocks with arity-0/1 ctors.

P6. Cones. Priors: the general theorem lands with cone in the 3000-5000 band (comparable
    to `trType_of_sortPiTr` at 3692) if I stay off `checkType.WF` (18795) and
    `TrExprS.weakFV_inv` (8653). Prediction 0.6 that I stay under 6000 and both
    cleanliness lines come back clean. Risk: any `VEnv.HasType` plumbing may drag in
    `IsDefEq` machinery; if `IsDefEq.uniq` shows up, the route is poisoned and I pivot to
    carrying typing as a hypothesis.

P7. Round-close numbers: census 13 / NOT BUILT 0, three guards, zero in-repo
    section-variable warnings. Prediction 0.8 achievable; the main risk is a name
    collision (census has caught two this session).

## MEASUREMENTS (appended one line per instrument call, before the next call)
M1. `Verify/Inductive/ExprConstructionScope.lean` read: it contains ONLY §1 (`bvarCtx`,
    `bvarCtx_toCtx`, `bvarCtx_cons`, `bvarCtx_find?_zero`, `bvarCtx_find?_succ`,
    `bvarCtx_find?`). Its docstring, however, already lays out a full PLAN for §2-§6 that
    nobody has built: a *function* `ctorTr?` on the fragment
    `.sort | .bvar | .const | .app | .forallE | .mdata` that returns the translation AND
    ITS TYPE (a type inferencer), so the `.app` case can discharge its two `HasType`
    premises because on this fragment the function's inferred type is *syntactically* a
    `∀` -- no whnf, no `IsDefEq`, no checker contact. Environment enters as a
    `Name → Option VConstant` argument with side condition
    `∀ c ci, Γc c = some ci → env.constants c = some ci`.
    => This CONFIRMS prior P3's alternative (decorated/computed rather than a
    `constNames` predicate) and REFUTES prior P1's main branch (the class is not an
    inductive predicate at all; it is a partial function). Adopting this plan.
M2. `TrExprS` read at `Lean4Lean/Verify/Typing/Expr.lean:153`. Confirms the floor exactly:
    `.app` has `env.HasType Us.length Δ.toCtx f' (.forallE A B)` and
    `env.HasType Us.length Δ.toCtx a' A`; `.forallE` has TWO `env.IsType` (the domain, and
    the body over the extended ctx). `.sort`/`.bvar`/`.const` are premise-free apart from
    lookups. So an inferencer that returns `(e', type')` plus a `HasType e' type'` proof
    can supply all four.
M3. `TrIndCtorR` at `Verify/Environment/InductR.lean:255` confirmed verbatim:
    `c.name = R.ctorName C.name ∧ TrExprS env Us [] c.type (C.typeR D R j)`.
    `TrIndDeclN.trCtors` is staged over `env.addIndTypesC D K = some env₁` -- so the
    environment in which the `TrExprS` must hold ALREADY has the block's type constants,
    which is exactly what the `.const` leaves of a constructor type need.
M4. `trS_tac` read at `Verify/Environment/InductR.lean:777-787`. Exactly five alternatives,
    confirmed: `TrExprS.sort rfl`, `TrExprS.bvar rfl`, `TrExprS.const (by assumption) rfl rfl`,
    `.forallE` (with FOUR `type_tac` subgoals: `⟨?_,?_⟩ ⟨?_,?_⟩`), `.app` (two `type_tac`).
    NO `lam`/`letE`/`proj`/`lit`/`mdata`/`fvar`. It is `first | ... ` on a concrete literal:
    reflection, as the brief said. The typing obligations are handed to `type_tac`, which is
    the separate reflection engine I must replace with a real inference.
M5. `type_tac` at `Theory/Typing/Meta.lean:37` is ALSO reflection ("TODO: write an actual
    tactic"): `HasType.forallE`/`.sort`+decide/`.bvar`+lookup_tac/`.app'`/`.const'`/`.lam`.
    So the general theorem must replace TWO reflection engines at once -- `trS_tac` and
    `type_tac` -- which is why the inferencer design (return translation + type + HasType)
    is the right shape: one induction discharges both.
M6. `TrExprS` binders: `variable (env : VEnv) (Us : List Name) in inductive TrExprS`, so
    env/Us are explicit leading args. `HasType env U Γ e A := IsDefEq env U Γ e e A`
    (`Theory/Typing/Basic.lean:60`); the five IsDefEq constructors I need are `.bvar`
    (from `Lookup`), `.sortDF`, `.constDF`, `.appDF`, `.forallEDF`. Available level lemmas:
    `Lean4Lean.VLevel.WF.of_ofLevel` (`Theory/VLevel.lean:178`) and
    `Lean4Lean.VLevel.WF.of_mapM_ofLevel` (:185). No `DecidableEq VExpr` instance found in
    `Theory/VExpr.lean` -- the `.app` case's `A = argType` check may need one (or I derive it).
M7. `Verify/Inductive/TrTypeProducer.lean` §1 read: `Lean4Lean.sortPiTr? : List Name -> Expr ->
    Option VExpr` plus `sortPiTr?_isType`, `trExprS_of_sortPiTr`, `isUnique_of_sortPiTr`.
    This is the exact template to generalise -- swap `Option VExpr` for
    `Option (VExpr x VExpr)` (translation + inferred type) and thread a constants map.
    Its `.sort` case proof is `⟨_, .sortDF (VLevel.WF.of_ofLevel hu) (VLevel.WF.of_ofLevel hu)
    (.refl _)⟩`, so `VLevel.instances`' `.refl` is available for `≈`.
M8. `ntreeAux` (`Theory/Inductive/NestedHead.lean:624`): `uvars = 1`,
    `params = [.sort (.succ (.param 0))]`, two members (`NTree`, `_nested.List_1`),
    `ntreeK = [`_nested.List_1]`. `ntreeIndType` (`Verify/Inductive/ValAtParam.lean:189`) is
    `{ name := ``NTree, type := exprOf% NTree, ctors := [{name := ``NTree.node,
    type := exprOf% NTree.node}] }`. `NTree.node : {α : Type u} → α → List (NTree α) → NTree α`
    -- forallE/sort/bvar/const/app only, so IN FRAGMENT. Its const leaves are ``List and
    ``NTree, both available at the `addIndTypesC` stage.
M9. `tr_ntreeNodeType` (`FlipConstruct.lean:126`, MUST NOT IMPORT) takes exactly
    `hList : env.constants ``List = some ⟨1, listType.type⟩` and
    `hNTree : env.constants ``NTree = some ⟨1, .forallE (.sort (.succ (.param 0)))
    (.sort (.succ (.param 0)))⟩`. So the `Γc` for my arity-0 witness is a two-entry map.
    Reusable staged lookups already exist in `Theory/Typing/ConstSubstNested.lean`:
    `ntreeF₂_list` (:2117), `ntreeF₂_ntree` (:2127), plus `ntree_stage₂_exists` (:1848)
    which hands `env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁`.
M10. `VEnv.addIndTypesC env D K = env.addConstList (D.typeConstsC K)`
     (`Theory/Inductive/Companion.lean:132`) -- DEFINITIONALLY, so `ntree_stage₂_exists`'s
     `hF₁` IS the `addIndTypesC` premise with no bridge. `VIndCtor.typeR C D R j =
     mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)`
     (`Theory/Inductive/Restore.lean:623`). `list_const` at `Theory/Inductive/NestedHead.lean:835`.
     PLAN FIXED: `ctorTr? : (Name -> Option VConstant) -> List Name -> Expr -> List VExpr ->
     Option (VExpr x VExpr)`, six cases (sort/bvar/const/app/forallE/mdata), soundness
     `TrExprS env Us (bvarCtx Γ) e e' ∧ env.HasType Us.length Γ e' t'`.
M11. All five typing helpers already exist and are premise-free:
     `Lean4Lean.VEnv.HasType.bvar/.sort/.const/.app/.forallE`
     (`Theory/Typing/Lemmas.lean:221-234`) and `Lean4Lean.VEnv.IsType.forallE` (:240).
     `DecidableEq VExpr`/`VLevel` already derived at `Theory/Inductive/Decl.lean:247-248`,
     so the `.app` case's domain check needs no new instance. Writing the file now.
M12. **§2-§4 COMPILE CLEAN, zero errors, zero warnings.** Proven:
     `Lean4Lean.piOf?`, `Lean4Lean.sortOf?`, `Lean4Lean.piOf?_eq_some`,
     `Lean4Lean.sortOf?_eq_some`, `Lean4Lean.ctorTr?`, `Lean4Lean.ConstLookup`,
     `Lean4Lean.ctorTr?_sound`, `Lean4Lean.trExprS_of_ctorTr`, `Lean4Lean.ctorTr?_hasType`,
     `Lean4Lean.isUnique_of_ctorTr`, `Lean4Lean.trIndCtorR_of_ctorTr`,
     `Lean4Lean.trIndCtorR_iff_of_ctorTr`, `Lean4Lean.trCtors_of_ctorTr`,
     `Lean4Lean.trCtors_iff_of_ctorTr`.
     PRIOR P1 SCORED: its main branch (inductive predicate, near-trivial fold) is REFUTED;
     the alternative branch (typing PRODUCED, not assumed) is what happened. Prior P2's
     0.75 that a typing-free theorem is impossible is REFUTED TOO: the hypothesis is
     `ConstLookup` alone -- pure `VEnv.constants` lookups, no `HasType`, no `IsType`, no
     `Ordered`, no `VEnv.WF` -- and `HasType` comes out. Two `List.Forall₂.length_eq` /
     dot-notation gotchas (the lemma is `Lean4Lean.List.Forall₂.length_eq`, so dot notation
     on a root `List.Forall₂` fails) were the only friction.
M13. **§5 COMPILES CLEAN.** `Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr` is `rfl`:
     `ctorTr? ntreeGc [`u] (exprOf% NTree.node) [] = some (ntreeNode.typeR ntreeAux
     ntreeRestore 0, .sort (.imax (.succ (.succ (.param 0))) (.imax (.succ (.param 0))
     (.imax (.succ (.param 0)) (.succ (.param 0))))))`. Also
     `ntreeGc`, `ntree_typeConstsC`, `ntreeNode_ctorName`, `ntree_constLookup`,
     `ntreeAux_trCtors` (arity 1: only `h`), `ntreeAux_trCtors_witness` (ARITY 0).
     Plus four §5a computations: with `Γc = fun _ => none` the inferencer returns `none`,
     and with `List` alone it STILL returns `none` -- so both lookups are load-bearing and
     the `addIndTypesC` staging is necessary, not decorative. PRIOR P4 SCORED CORRECT
     (arity-0 reachable, non-degenerate: uvars = 1, params non-empty, 2 fields).
M14. **WHOLE FILE COMPILES CLEAN** (§2-§8), zero errors, zero warnings. Added §6 boundary
     (six `rfl` non-fragment computations, `ctorTr?_none_of_nonSyntacticPi`,
     `trExprS_lam_outside_fragment`), §7 (`ntreeNode_typeR_hasType`,
     `ntreeNode_constant_wf` -- `VConstant.WF` of the declared constructor constant from
     two lookups alone: STRICTLY more than `TrIndCtorR` asked for), §8 two field-shape
     `example`s against `TrIndDeclN.trCtors` itself.
M15. `lake build`: **`Lean4Lean.Verify.Inductive.TrExprSGeneral` BUILT (2.1s)**. The build as
     a whole FAILS, but not on anything of mine: `Lean4Lean/Theory/Typing/PatSig.lean` is an
     UNTRACKED file from a CONCURRENT stream (`docs/handoff-patsig.md`, also untracked, plus
     `Theory/Typing/CommutationLemmas.lean`, `Theory/SetModel/RecTypePeel.lean`) and it has
     three `ParRedR`/`ParRed` application type mismatches at lines 281-283. The tree changed
     under me mid-round (the files dirty at round start are gone). Recording so the
     round-close number is attributed correctly and not to me.
M16. `exists.lean` on the twelve general names (population 447 built modules, 6 watched):
     ALL FOUND, all `own value is a hole: false`, all `cone reaches sorryAx: false`,
     ALL `watched declarations in cone: none of 6`.
     Cones: ctorTr? 912 (arity 4) | ConstLookup 8 (2) | ctorTr?_sound 1147 (9) |
     trExprS_of_ctorTr 1148 (8) | ctorTr?_hasType 1148 (9) | isUnique_of_ctorTr 936 (6) |
     trIndCtorR_of_ctorTr 1222 (12) | trIndCtorR_iff_of_ctorTr 3907 (12) |
     trCtors_of_ctorTr 1257 (21) | trCtors_iff_of_ctorTr 3936 (10) |
     piOf?_eq_some 402 (4) | sortOf?_eq_some 391 (3).
     PRIOR P6 SCORED: predicted 3000-5000 band and under 6000 -- the producer route came in
     at 1257, well UNDER prediction; only the two `↔` statements reach 3907/3936 (that is
     `TrExprS.unique`'s cone, entering solely through the completeness direction, which the
     producer does not use).
M17. `exists.lean` on the eleven witness/boundary names: ALL FOUND, all hole-free, all
     `cone reaches sorryAx: false`, ALL `watched declarations in cone: none of 6`.
     Cones: ntreeGc 349 (arity 1) | ntreeNode_ctorTr 1011 (ARITY 0) |
     ntree_constLookup 1071 (4) | ntreeAux_trCtors 1468 (14) |
     **ntreeAux_trCtors_witness 1533 (ARITY 0)** | ntreeNode_typeR_hasType 1391 (4) |
     ntreeNode_constant_wf 1393 (4) | ctorTr?_none_of_nonSyntacticPi 915 (0) |
     trExprS_lam_outside_fragment 945 (1) | ntree_typeConstsC 387 (0) |
     ntreeNode_ctorName 347 (0).
M18. **NON-BORROWING CONFIRMED BY MEASUREMENT, not just by imports.** Re-ran `exists.lean`
     with `WATCH` extended to include `Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType`,
     `tr_ntreeType`, `ntreeAux_trIndDeclN`, `Lean4Lean.TypeChecker.checkType.WF`,
     `Lean4Lean.TrExprS.weakFV_inv`, plus the three standing bans. All six of my headline
     names report `watched declarations in cone: none of 8`. So the arity-0 witness reaches
     `TrExprS` of `NTree.node`'s stored type WITHOUT the hand-built bridge and without the
     checker, and the two poisoned routes are absent from every cone.
M19. `scripts/sorry-census-all.lean` (with `--run`; without it the script prints nothing --
     worth knowing): on disk 474, population 450, BUILT 449, **NOT BUILT 1**, and the one
     is `Lean4Lean.Theory.SetModel.RecTypePeel` -- the CONCURRENT stream's untracked file,
     not mine. **HOLES over the whole built population: 13** (pass A 13, pass B 0), the
     expected list, unchanged. `Lean4Lean.Verify.Inductive.TrExprSGeneral` is BUILT and
     listed as an orphan, exactly as `TrTypeProducer` is. Zero in-repo
     "automatically included section variable" warnings (the single one in the whole build
     log is in `Foundation/FirstOrder/SetTheory/Z.lean`, a dependency).
M20. Three guards, run directly (`lake env lean Lean4Lean/Verify/Guard.lean`, no edit):
     guard 1 "Axioms.lean declares exactly the 24 frozen axioms ✓";
     guard 2 "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)";
     guard 3 "checker cone implementation gaps within frozen list (2/2 remaining) ✓".
M21. `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone".
     Stronger: `sorry-census-all.lean` pass A imported 446 modules INCLUDING mine into one
     environment and succeeded, which is the whole-population collision check, and it passed.
     No name collisions.
M22. Added §4a (`Lean4Lean.CtorsInFragment`, `Lean4Lean.trCtors_iff_of_fragment`), §4b
     (`Lean4Lean.InductiveDeclExamples.ntree_ctorsInFragment`,
     `Lean4Lean.NestedWit.nfn_ctorsInFragment`, `Lean4Lean.NestedWit.nfnNode_ctorTr`) and the
     two BRIDGE-RECOVERY theorems `Lean4Lean.NestedWit.tr_nodeType_general` and
     `Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType_general`. All compile.
     `exists.lean` with WATCH = 11 (the three standing bans + the three watched-route
     declarations + `tr_ntreeNodeType`, `tr_ntreeType`, `NestedWit.tr_nodeType`): ALL EIGHT
     names hole-free, sorryAx-free, `watched declarations in cone: none of 11`.
     Cones: CtorsInFragment 917 (3) | trCtors_iff_of_fragment 3938 (10) |
     ntree_ctorsInFragment 1023 (0) | nfn_ctorsInFragment 1019 (0) | nfnNode_ctorTr 1006 (0) |
     tr_nodeType_general 1249 (3) | tr_ntreeNodeType_general 1240 (3) |
     ntreeAux_trCtors_witness 1533 (0).
     So BOTH hand bridges' constructor cases are re-derived from the same hypotheses without
     the hand bridge being in the cone: the general theorem SUBSUMES `trS_tac` there.
M23. `#print axioms` on the six headline names: every one is
     `[propext, Classical.choice, Quot.sound]` -- the three standard axioms, no `sorryAx`,
     nothing from `Verify/Axioms.lean`'s frozen 24.
M24. Structural non-borrowing, checked by walking the import closure (163 modules):
     `Verify/Inductive/FlipConstruct`, `TrIndDeclNProducer`, `CtorPointwise`,
     `TrTypeProducer`, `Verify/Soundness`, `Verify/Guard` are **not** in it. The only
     `import` line is `Lean4Lean.Verify.Inductive.ExprConstructionScope`. All 11
     occurrences of `trS_tac`/`type_tac` in the file are prose in docstrings; zero in proofs.
     651 lines.
M25. ROUND-CLOSE, on the tree as it stands: `lake build` **"Build completed successfully
     (1633 jobs)"**; census **HOLES 13, NOT BUILT 0**, BUILT 450/450; three guards
     (24 frozen axioms ✓ / kernel_sound within whitelist ✓ INCOMPLETE / 2-of-2 impl gaps ✓);
     in-repo "automatically included section variable" warnings **0** (one in the whole log,
     in `Foundation/FirstOrder/SetTheory/Z.lean`).
     Earlier in the round the build was red twice, both times on untracked files from
     CONCURRENT streams (`Theory/Typing/PatSig.lean`, then `Theory/SetModel/RecTypePeel.lean`);
     both were fixed by their owners while I measured. Nothing of mine was ever red.

## SCORING THE PRIORS

* **P1 REFUTED in its main branch (0.6 confidence, wrong).** The class is not an inductive
  predicate carrying typing as fields, and the theorem is not a near-trivial fold. It is a
  *partial function* -- a type inferencer -- and the theorem is a real six-case induction.
  P1's alternative branch (0.3) is what happened.
* **P2 REFUTED (0.75 confidence, wrong).** I predicted a genuinely typing-free general
  theorem was impossible and that I would have to report the floor as a first-class finding
  in the negative. The opposite is true and is the round's main result: see below.
* **P3 CORRECT in its alternative (0.7).** No `constNames` predicate; the environment is a
  `Name -> Option VConstant` argument and the lookups are collected in `ConstLookup`.
* **P4 CORRECT (0.5 on non-degeneracy).** Arity-0 reached, at `uvars = 1`, non-empty
  parameter telescope, two fields, one of them the nested `_nested.List_1 α` one.
* **P5 CORRECT (0.65).** Both nested example blocks are in the fragment (§4b).
* **P6 WRONG IN THE CONSERVATIVE DIRECTION.** Predicted 3000-5000; the producer route came
  in at **1257** and the whole general core at 912-1533. Only the completeness `↔`s reach
  3907-3938, and that is `TrExprS.unique`'s cone entering through the direction the producer
  never uses. Cleanliness prediction (0.6) correct: clean on all 11 watched names.
* **P7 CORRECT (0.8).** 13 / 0 / three guards / zero section-variable warnings.

## THE FINDING, STATED PLAINLY

The brief asked me to say plainly if the typing floor forces an obligation of comparable
strength to what the theorem produces. **It does not, and the reason is worth recording.**

The floor is real: `TrExprS.app` carries two `VEnv.HasType`s and `.forallE` two `VEnv.IsType`s,
so no `Expr -> VExpr` translation function can be sound with a typing-free hypothesis. The
inference I (and the priors) drew from that -- that a general construction must *assume* typing
-- is wrong. The floor is discharged by making the function return the type as well, so that
typing is **an output of the same induction**, not an input to it. Concretely:

* the hypothesis is `ConstLookup Γc env`, i.e. `∀ c ci, Γc c = some ci → env.constants c = some ci`
  -- a conjunction of `VEnv.constants` equations, decidable at a concrete environment, with no
  `HasType`, no `IsType`, no `VEnv.Ordered`, no `VEnv.WF`;
* the conclusion is `TrExprS env Us (bvarCtx Γ) e e' ∧ env.HasType Us.length Γ e' t'`.

And the gap is not rhetorical. `Lean4Lean.InductiveDeclExamples.ntreeNode_constant_wf` derives
`VConstant.WF F₁ ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩` -- well-formedness of the
constructor constant the nested step declares -- from those two lookups alone. That is strictly
more than `TrIndCtorR` asked for.

What makes it work is that the fragment never needs to *compare* two types up to conversion,
only to *read one off*: `piOf?`/`sortOf?` require the inferred type to be syntactically a `∀` or
a sort. That is exactly the property `trS_tac` was exploiting without saying so, and it is why
neither `VEnv.IsDefEq.uniq` nor `uniqU` nor `TypeChecker.checkType.WF` nor `TrExprS.weakFV_inv`
appears in any cone here. The price is recorded as `ctorTr?_none_of_nonSyntacticPi`: an
application whose function's type is a `∀` only up to conversion is outside the fragment even
when well typed. For constructor types that never happens.

## WHAT REMAINS

* `TrIndDeclN.trCtors` is discharged **as a field producer, in general** (`trCtors_of_ctorTr`),
  for any block satisfying `CtorsInFragment` plus a per-stage `ConstLookup`. It is *not* yet
  wired into `trIndDeclN_of_ownId` (`TrIndDeclNProducer.lean`) -- that file is not mine, and §8
  checks the shape fit against the structure field by elaboration instead.
* The `ConstLookup` obligation at a general block still has to be met from the step's own data
  (`AddInductStagesR`'s first stage). At `ntreeAux` I met it in four lines
  (`ntree_constLookup`); the general version wants a lemma of the form "every `.const` leaf of a
  constructor type is either a pre-block constant or one of `D.typeConstsC K`", which is
  `Verify/Inductive/StageMono.lean` territory and belongs to whoever owns that file.
* `.lam`/`.letE`/`.proj`/`.lit`/`.fvar` remain outside; §6 says per constructor what each costs.
  None occurs in a constructor type, so none blocks `trCtors`.
* The remaining 13 holes are untouched by this round.
