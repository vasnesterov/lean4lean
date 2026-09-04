# handoff-patsig — feasibility of a `PatSig` signature below `ChurchRosser`

Round scope: **feasibility build only.** I own exactly `Lean4Lean/Theory/Typing/PatSig.lean`
(new) and this file. No edits to `ChurchRosser.lean`, `ParamsBuild.lean`,
`PatternRules.lean`, or any other existing file.

## Priors (written BEFORE the first measurement)

P1. `Lean4Lean.VEnv.Params` has 10 fields and exactly 2 mention the judgment
    (`pat_wf`, `extra_pat`) — as the incoming plan claims. **Prior: 60%.** Field
    counts in this repo have been reported accurately before, but "10 fields"
    is a scan summary, and scan summaries from the orchestrator have been wrong
    5 times. I expect the count to be right ±1 and the *identity* of the
    judgment-mentioning fields to be the risky part: a field can mention the
    judgment indirectly (through a `Params`-level abbreviation or through a
    type like `VExpr.WF` that unfolds to the judgment), and a naive grep for
    the judgment head symbol would miss that.

P2. `PatSig` with 8 fields = 10 − 2 is exactly the right shape. **Prior: 45%.**
    The arithmetic is too clean. The likely failure mode is that one of the 8
    "judgment-free" fields is *stated* without the judgment but its intended
    use inside `ChurchRosser` needs a judgment-side side-condition, so the
    honest split is 7 + 1-weakened or 8 + a new glue field.

P3. "`PatternRules` proves all 8 fields, zero new proofs." **Prior: 30%.**
    This is the load-bearing claim and the one I trust least. Even when the
    mathematical content is present, signature-level packaging almost always
    costs *something*: an argument-order/implicit-binder adapter, a
    `∀`-vs-curried mismatch, or a field stated over a different but equivalent
    relation. I expect ≥1 field to need a genuinely new (if short) proof, and
    I would not be surprised by 2–3.

P4. The parts of `ChurchRosser` not mentioning the judgment can be restated
    over `PatSig` alone. **Prior: 55%.** Parametricity over `Params` is
    already established (that part I believe: it is a cone-style structural
    fact). The risk is that `ChurchRosser` destructures a `Params` value, or
    passes the whole `Params` to a helper in another module, so a `PatSig`-only
    restatement cannot call that helper.

P5. The residual — 4 downstream modules (`DescendRefute`, `KDescend`,
    `KSite7App`, `ParRedPropRefute`) referencing the inductives directly, so
    case names need re-pointing. **Prior: 50% that the module list is exactly
    right.** Orchestrator attributions have been wrong 5 times; a set of
    exactly 4 named modules is an attribution. I expect the *phenomenon* to be
    real (direct constructor/case-name references do happen) and the *list* to
    be incomplete or to contain a module that only references a wrapper.

P6. Round-close is green as stated (census 13 / NOT BUILT 0, three guards,
    zero section-variable warnings), since I am only adding one new file.
    **Prior: 85%.** The 15% is my own new file introducing a section-variable
    warning — the classic failure when writing a `variable`-heavy signature
    file.

## Measurements (appended one line per instrument call, as made)

M1. `Lean4Lean.VEnv.Params` = `Lean4Lean/Theory/Typing/ChurchRosser.lean:12`, `class Params where`.
    **Exactly 10 fields**, in order: `env`, `henv`, `univs`, `Pat`, `pat_simple`, `pat_uniq`,
    `pat_wf`, `pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`. Field count claim CONFIRMED (10).
M2. Syntactic judgment mentions among the 10: `pat_wf` (`IsType`/`HasType`/`IsDefEqU`) and
    `extra_pat` (`IsType`/`env.defeqs`/`IsDefEqU`). The other 8 are, *as written*, free of the
    judgment: `env`/`univs`/`Pat` are data, `pat_simple`/`pat_uniq`/`pat_app_l_uniq`/
    `pat_app_uniq` are pure pattern combinatorics (`Subpattern`, `Pattern.inter`, `HEq`).
    Remaining question flagged by prior P1: `henv : env.WF` -- does `VEnv.WF` unfold to the
    judgment? Checking next.
M3. `henv : env.WF` DOES mention the judgment transitively: `VEnv.WF env = ∃ ds, VEnv.WF' ds env`
    (`Theory/Typing/Env.lean:132,136`), and `VEnv.WF'` threads `VDecl.WF`, whose leaves are
    `VDefVal.WF = HasType` (`Env.lean:8`), `VConstant.WF = IsType`, `VDefEq.WF = HasType ∧ HasType`
    (`Basic.lean:73,75`). So: **2 of 10 fields mention the judgment in their own statement
    (`pat_wf`, `extra_pat`); 3 of 10 mention it if transitive unfolding counts (`henv` too).**
    This does *not* block the split -- `Env.lean` is below `ChurchRosser` -- but it means
    "judgment-free" for `PatSig` must be read as "does not mention the *confluence-layer*
    judgment vocabulary in its own statement", not "independent of typing".
M4. Import-closure fact, exact: `ChurchRosser` closure = 47 modules, `PatternRules` closure = 46,
    and **neither imports the other** (siblings). `PatternRules \ ChurchRosser` = 6 modules
    (`Inductive.RecApp`, `Inductive.Structure`, `Inductive.StructureClosed`,
    `Inductive.TelescopeLift`, `Typing.DeltaUnique`, `Typing.PatternDecode`). So a `PatSig`
    module can sit below BOTH, and `PatternRules` itself could carry the instance.
M5. **`pat_app_l_uniq` and `pat_app_uniq` have ZERO uses inside `ChurchRosser`** (only their
    field declarations, lines 39/41). Their only real consumers tree-wide are
    `Theory/Typing/HeadReduction.lean:158,160` (inside `VEnv.WHNF.subpattern`) and
    `Theory/Typing/KMeasure.lean:167`. `pat_simple` is used twice (`pat_not_var`, l.94), and
    `pat_uniq` once (l.1199, inside `ParRed.triangle`). So of the 5 non-data `PatSig`
    candidates, only 2 are consumed inside `ChurchRosser` at all.
M6. **The obstacle to a big `PatSig` payoff, found by reading the inductives.**
    `ChurchRosser`'s three core inductives each carry an `extra` constructor that mentions the
    judgment directly: `VEnv.ParRed.extra` and `VEnv.CParRed.extra` both have
    `r.2.OK (IsDefEqU env univs Γ) m1 m2` (lines 757-758, 796-797), and `VEnv.NonNeutral`
    (l.783) is defined with `IsDefEqU`. So every statement about `ParRed`/`CParRed`/
    `NonNeutral`/`NormalEq` -- i.e. nearly all of the file after line 163 -- mentions the
    judgment through its own subject, not through `pat_wf`/`extra_pat`. The judgment-free
    residue of `ChurchRosser` is therefore small; measuring it exactly next.
M7. Classifier bug caught before recording a number: seeding the statement-closure from
    `ci.type` alone leaves a `def`'s own body unexpanded, so `VEnv.NonNeutral`, `VEnv.ParRed`,
    `VEnv.NormalEq`, `VEnv.CParRed`, `VEnv.ParRedS`, `VEnv.CRDefEq` were all mis-reported as
    judgment-free on the first run (their *types* are `List VExpr → VExpr → VExpr → Prop`).
    Confirmed by hand: `Lean4Lean.VEnv.ParRed.extra`'s type contains
    `Lean4Lean.VEnv.IsDefEqU`, and `Lean4Lean.VEnv.NonNeutral`'s value does too. Re-seeding
    from `stepDeps` (value for defs, ctors for inductives). First-run numbers DISCARDED.
M8. **Exact judgment-free census** (statement closure expanded through def bodies and inductive
    constructors, with the class `Params` itself held opaque; marker = `Lean4Lean.VEnv.IsDefEq`,
    `Params.pat_wf`, `Params.extra_pat`):
      `Theory/Typing/ChurchRosser.lean`   judgment-FREE 82 / judgment-dependent 348
      `Theory/Typing/HeadReduction.lean`  judgment-FREE 36 / judgment-dependent 167
      `Theory/Typing/KMeasure.lean`       judgment-FREE 34 / judgment-dependent  87
    After dropping compiler-generated entries, the judgment-free hand-written declarations of
    `ChurchRosser` are exactly 7 + the class itself: `Lean4Lean.Pattern.RHS.apply_lift'`,
    `Lean4Lean.Pattern.RHS.apply_liftN`, `Lean4Lean.VEnv.IsApp`, `Lean4Lean.VEnv.ParRedExt`
    (with `.apply`, `.depth`, `.meas`, `.isApp`), `Lean4Lean.VEnv.Params.pat_not_var`,
    `Lean4Lean.VLevel.forall₂_equiv_refl`, `Lean4Lean.VLevel.forall₂_inst_congr`.
M9. **Of those, only ONE consumes a `Params` field at all**: `Lean4Lean.VEnv.Params.pat_not_var`
    (uses `pat_simple`). The other six are `Params`-independent outright. The only other
    declarations in the whole `[Params]` layer whose PROOF consumes a pattern-combinatorial
    field are `Lean4Lean.VEnv.ParRed.triangle` (judgment-dependent statement),
    `Lean4Lean.VEnv.Params.simple_app`, `Lean4Lean.VEnv.WHNF.subpattern`,
    `Lean4Lean.VEnv.WHRed.determ` (HeadReduction) and
    `Lean4Lean.VEnv.Params.pat_app_arity_uniq`, `Lean4Lean.VEnv.Params.pat_app_depth_uniq`
    (KMeasure). The last two have judgment-FREE statements -- they are the real `PatSig`
    content in the tree, and they are NOT in `ChurchRosser`.
M10. `scripts/exists.lean`, population **445 built modules**, watching 6 declarations. All 18
     names I need FOUND, every one `own value is a hole: false`, `cone reaches sorryAx: false`,
     `watched declarations in cone: none of 6`:
     `Lean4Lean.VEnv.Params` (cone 1, NO PROOF TERM), `Lean4Lean.VEnv.Params.pat_not_var` (73),
     `Lean4Lean.VEnv.Params.simple_app` (133), `Lean4Lean.VEnv.Params.pat_app_arity_uniq` (656),
     `Lean4Lean.VEnv.Params.pat_app_depth_uniq` (1559), `Lean4Lean.Pat.simple` (816),
     `Lean4Lean.Pat.uniq` (4350), `Lean4Lean.Pat.app_l_uniq` (3838), `Lean4Lean.Pat.app_uniq`
     (3833), `Lean4Lean.Pat.extra` (4517), `Lean4Lean.VEnv.paramsOfWF` (6391),
     `Lean4Lean.VEnv.ParRed` (4, NO PROOF TERM), `Lean4Lean.Subpattern.varN_le` (124),
     `Lean4Lean.VEnv.Subpattern.varN_const` (115), `Lean4Lean.Pattern.inter_self` (617),
     `Lean4Lean.Pattern.depth_varN` (1373), `Lean4Lean.Pattern.headName_varN` (40),
     `Lean4Lean.Pattern.Check.OK` (634).
M11. Import fact that makes the feasibility file cheap: `Theory/Typing/KMeasure.lean`'s closure
     is 64 modules and already contains `HeadReduction`, `ChurchRosser`, `PatternRules` AND
     `ParamsBuild`. One import suffices.
