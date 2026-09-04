# handoff-fragmentwiden — is `Lean4Lean.CtorsInFragment` a real restriction?

Owner of this round: exactly `Lean4Lean/Verify/Inductive/FragmentWiden.lean` (new) and this file.
Everything else read-only. Frozen: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

## §0 Priors, written before the first instrument call

Brief-supplied facts I have NOT yet verified (all get an instrument line below):
- `Lean4Lean.trIndDeclN_of_ownId` — arity 22, cone 1445, hole-free.
- `Lean4Lean.ctorTr?` — inferencer over the syntactic fragment
  `.sort | .bvar | .const | .app | .forallE | .mdata`.
- `Lean4Lean.CtorsInFragment` — checkable predicate, machine-checked at both nested blocks
  (`ntreeAux`, `nfnAux`).
- `Lean4Lean.constLookup_iff_split` — arity 6, cone 521.
- `Lean4Lean.ctorTr?_none_of_nonSyntacticPi` — records the price of leaving the fragment.

My priors on the verdict (a), stated so they can be scored:

P1 (60%) **`CtorsInFragment` is very nearly not a restriction, but not literally provable as
stated.** Reasoning: a constructor type as *stored in the environment* is whatever the elaborator
put there, and the kernel's `Lean4Lean` add-inductive path does not normalise it. `.mdata` is in
the fragment already, so annotation is not the issue. The four genuinely dangerous heads are
`.lam`, `.letE`, `.proj`, `.lit`, plus `.fvar`. Of these:
  - `.fvar` — a stored constructor type is a *closed* term (no free variables), so `.fvar`
    cannot occur. This one I expect to be provable outright from a closedness invariant, and it
    is the cheapest of the five.
  - `.lit` — `Nat`/`String` literals. I expect these CAN occur: nothing stops a constructor type
    mentioning `Fin 3` where `3` is `.lit (.natVal 3)`. **This is my main worry, and if it holds
    the fragment IS a restriction.** `OfNat` elaboration usually produces `.lit`.
  - `.lam` — can occur in an *argument* position of an application inside a constructor type
    (e.g. `Vector (fun i => α) n`, or any type-level function applied to a lambda). Not in a
    head position. So `.lam` is reachable.
  - `.letE` — the elaborator zeta-reduces most, but `let` in a type is representable; I expect
    reachable in principle, rare in practice.
  - `.proj` — structure projections in types: `S.fst x`-as-`.proj`. Reachable if a constructor
    type mentions a projection of a structure. Note `Verify/Inductive/ProjNoNested.lean` exists,
    which suggests a previous round already fenced `.proj` off for nested blocks.
So P1's shape: **`.fvar` excludable by a real theorem; `.lit`/`.lam` NOT excludable; hence the
fragment is a real restriction and (b) is the live branch.**

P2 (70%) The widening that goes through without a conversion check is: **add `.lit` and `.lam`
and `.letE` as *inert carriers* — terms the inferencer never needs to look inside, only to
translate structurally.** The reason the current fragment stops where it does is that
`.forallE`/`.app`/`.const`/`.sort`/`.bvar` are exactly the heads whose *translation* is
determined by their own shape. `.lam` and `.letE` are equally determined structurally (`TrExprS`
has lam/letE cases). So my prior is the real boundary is NOT lam/letE/lit at all — it is
`.proj`, because `TrExprS`'s proj case needs the structure's field type, which needs a lookup
that in turn wants a conversion (`TrProj.weak'_inv` is named as contaminated, which fits).
Predicted boundary: **fragment widens to everything except `.proj` and `.fvar`; `.fvar` is
vacuous, so the honest statement is "everything except `.proj`".**

P3 (50%) The `.proj` exclusion is itself vacuous *for constructor types of nested blocks*,
because `Verify/Inductive/ProjNoNested.lean` sounds like it already proves nested blocks have no
`.proj`. If so (a) resolves positively for the nested case, which is the case that matters for
the flip.

P4 (80%) Cones: a widened `ctorTr?` will keep the cone near 1445 provided I do not touch
`IsDefEq.uniq`, `uniqU`, `checkType.WF`, `TrExprS.weakFV_inv`. My arity-0 `ntreeAux` witness
should land under ~1600.

P5 (40%) Round-close will be clean first try. Census 13 / NOT BUILT 0 is the stated target; I
have not yet seen the current census, so 13 is the brief's number, not mine.

Calibration note carried in from the orchestrator: its **cone figures have been exact all
session; its attributions have been wrong seven times.** So: trust the cone numbers below,
independently verify every "X is proved by Y" claim.

## §1 Measurements (append-only, one line per instrument call)

M01 `exists.lean` (population 450 built modules, watching 6 declarations):
  - `Lean4Lean.trIndDeclN_of_ownId` FOUND, module `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`,
    arity 22, cone 1445, hole false, cone-reaches-sorryAx false, watched in cone: none of 6.
    -> brief's 22/1445 EXACT.
  - `Lean4Lean.ctorTr?` FOUND, module `Lean4Lean.Verify.Inductive.TrExprSGeneral`, arity 4,
    cone 912, hole false, sorryAx false, watched: none of 6.
  - `Lean4Lean.CtorsInFragment` FOUND, same module, arity 3, cone 917, hole false, sorryAx false,
    watched: none of 6.
  - `Lean4Lean.constLookup_iff_split` FOUND, module `Lean4Lean.Verify.Inductive.FlipWiring`,
    arity 6, cone 521, hole false, sorryAx false, watched: none of 6. -> brief's 6/521 EXACT.
  - `Lean4Lean.ctorTr?_none_of_nonSyntacticPi` FOUND, same module as ctorTr?, arity 0, cone 915.
  - `Lean4Lean.ConstLookup` FOUND, arity 2, cone 8.
  - `Lean4Lean.InductiveDeclExamples.ntreeAux` FOUND, module `Lean4Lean.Theory.Inductive.NestedHead`,
    arity 0, cone 43, hole false, sorryAx false, watched: none of 6.
  Calibration: cone figures exact again (2/2 checkable).

M02 read `Lean4Lean/Verify/Inductive/TrExprSGeneral.lean` (651 lines) in full. Facts:
  - fragment is exactly `.sort | .bvar | .const | .app | .forallE | .mdata`, catch-all `| _,_ => none`.
  - §6 costing (the brief told me to read rather than redo), verbatim summary:
    `.lam` "needs the body's inferred type abstracted back into a `.forallE`, which is fine; the
      reason it is omitted is that a constructor type never has one, and adding it would need no
      new idea";
    `.letE` "translates to the *substituted* body, so the inferencer would have to instantiate...
      the `VLCtx` stops being an all-`vlam` one, so §1's free lookups are lost";
    `.proj` "needs `TrProj`"; `.lit` "needs `VEnv.ContainsLits`"; `.fvar` "needs a non-`vlam`
      context entry". "These three are genuine additions, not bookkeeping, and none of them
      occurs in a constructor type."
  - **The last sentence is the claim I must test, and I already doubt it (prior P1: `.lit`).**
  - **A SECOND, independent restriction the brief did not name**: `ctorTr?`'s `.app` case uses
    `piOf?`, which matches `.forallE` *syntactically*. `ctorTr?_none_of_nonSyntacticPi` is
    exactly this. So even a term built ONLY from the six allowed heads can be outside the
    fragment. Any verdict on (a) that only enumerates `Expr` heads is incomplete.
  - Existing §6 `example`s already machine-check `ctorTr? _ _ (.fvar/.mvar/.lam/.letE/.lit/.proj) _ = none`
    by `rfl`, at arbitrary `Γc Us Γ` — so head-exclusion is already environment-independent for
    a term whose ROOT is outside. What is missing is the same for a head *nested inside*.

M03 `lean_run_code`: elaborated five candidate declarations and printed the STORED constructor
  type plus the set of `Expr` head constructors occurring anywhere in it. Result (verbatim):
    `FooLit.mk       : Fin 3 → FooLit`            heads = [app, forallE, const, **lit**]
    `FooLam.mk       : { n // n = n } → FooLam`   heads = [bvar, app, forallE, const, **lam**]
    `FooLet.mk       : (let n := 3; Fin n) → FooLet` heads = [**letE**, bvar, app, forallE, const, **lit**]
    `FooProj.mk      : p.car → FooProj`           heads = [app, forallE, const]   (no `.proj`)
    `FooNonSynPi.mk  : myf 0 = 0 → FooNonSynPi`   heads = [app, forallE, const, **lit**]
  **VERDICT ON (a) IS SETTLED NEGATIVELY, AND CONTRADICTS EXISTING REPO PROSE.**
  `TrExprSGeneral.lean:55` says of `.proj`/`.lit`/`.fvar` "none of them occurs in a constructor
  type", and line 48-49 says of `.lam` "a constructor type never has one". Both are FALSE:
  `.lit` occurs in `Fin 3 → FooLit`, `.lam` occurs in `{ n // n = n } → FooLam`, and `.letE`
  survives elaboration un-zeta-reduced in `(let n := 3; Fin n) → FooLet`. All three declarations
  are accepted by Lean's own C++ kernel (they are in the compiled environment).
  I do not own `TrExprSGeneral.lean`; I record the correction and do not edit it.
  `.proj` NOT exhibited: `p.car` elaborates to `.app (.const Pack.car) (.const p)`, since a
  structure projection is a *function*; `Expr.proj` is what that function's body uses.

M04 wrote `Lean4Lean/Verify/Inductive/FragmentWiden.lean` §1 (fragment as a `Bool` predicate
  `Lean4Lean.inFragment` + the escape theorem) — `lean_diagnostic_messages`: **0 errors,
  0 warnings, first try.** Key general theorems now proved with bodies:
  - `Lean4Lean.inFragment_of_ctorTr?` : `ctorTr? Γc Us e Γ = some p → inFragment e = true`
    (success forces syntactic membership; environment-quantified).
  - `Lean4Lean.ctorTr?_eq_none_of_not_inFragment` : `inFragment e = false → ∀ Γc Us Γ,
    ctorTr? Γc Us e Γ = none`.  **This is what makes non-membership environment-independent.**
  - `Lean4Lean.not_ctorsInFragment_of_ctor` : one bad constructor type kills `CtorsInFragment`
    at every `Γc`/`Us`.

M05 appended §2 (three real `inductive` blocks + verdict). `lean_diagnostic_messages`: **0 errors,
  0 warnings** after two name-resolution fixes (`NFn.node` resolves only as
  `InductiveDeclExamples.NFn.node`; `nfnIndType` is not in this import closure).
  Machine-checked by `rfl`:
  - `Lean4Lean.FragEx.withLit_not_inFragment`, `...withLam_not_inFragment`,
    `...withLet_not_inFragment` — all `= false`.
  - `Lean4Lean.FragEx.ntreeNode_inFragment`, `...nfnNode_inFragment` — both `= true`, so the
    predicate is not one that fails on everything.
  And the verdict theorems, general in `Γc` and `Us`:
  - `Lean4Lean.FragEx.withLit_not_ctorsInFragment`
  - `Lean4Lean.FragEx.withLam_not_ctorsInFragment`
  - `Lean4Lean.FragEx.withLet_not_ctorsInFragment`
  **(a) IS SETTLED: `CtorsInFragment` IS A REAL RESTRICTION.** The brief's most-wanted outcome
  ("the fragment is not a restriction") is FALSE and now machine-refuted. (b) is the live branch.

M06 `exists.lean` on the literal route (population 452):
  - `Lean4Lean.TrExprS.trLiteral` FOUND, `Lean4Lean.Verify.Typing.Lemmas`, arity 7, cone 4938,
    hole false, sorryAx false, **watched: none of 6** — i.e. CLEAN, not poisoned.
  - `Lean4Lean.VExpr.trLiteral` arity 1, cone 3425, clean.
  - `Lean4Lean.VEnv.HasPrimitives` arity 1, cone 2 [NO PROOF TERM].
  - `Lean4Lean.VEnv.Ordered` arity 1, cone 2 [NO PROOF TERM].
  - `Lean4Lean.TrExprS.natLit` arity 6, cone 3581, clean.
  Reading: `trLiteral` would give BOTH literal kinds, but its hypotheses are `VEnv.Ordered` +
  `VEnv.HasPrimitives` + `ContainsLits`, i.e. strictly more than `ConstLookup`. Since §7 of
  `TrExprSGeneral` boasts that the inferencer's premise is weaker than what it produces, taking
  `Ordered` would destroy that property. **Decision: derive the nat-literal case directly from
  `ConstLookup` by induction on `n`, and do not use `trLiteral`.** Prior P2 (which predicted the
  boundary was `.proj` only) is WRONG about `.lit`: `.lit` is free after all, but only for
  `.natVal`, and only by not reusing `trLiteral`.

M07 §3 + §3a written: `Lean4Lean.natLitOk?`, `Lean4Lean.ctorTrW?`, `Lean4Lean.inFragmentW`,
  `Lean4Lean.inFragmentW_of_inFragment`, `Lean4Lean.trExprS_natLit`.
  `lean_diagnostic_messages`: one error first pass (`VConstant` has no `DecidableEq`, so the
  pinned-stored-type check had to be spelled component-wise on `uvars`/`type`), then
  **0 errors, 0 warnings**. `trExprS_natLit` takes exactly `ConstLookup` + `natLitOk?`, with
  `VEnv.Ordered` and `VEnv.HasPrimitives` nowhere.

M08 §3b + §4 written and green (`lean_diagnostic_messages`: **0 errors, 0 warnings**, both first
  try after one missing-lemma stub I then supplied). New general theorems with bodies:
  `Lean4Lean.ctorTrW?_sound`, `Lean4Lean.trExprS_of_ctorTrW`, `Lean4Lean.ctorTrW?_hasType`,
  `Lean4Lean.isUnique_of_ctorTrW`, `Lean4Lean.inFragmentW_of_ctorTrW?`,
  `Lean4Lean.ctorTrW?_of_ctorTr?` (conservativity, as a computation),
  `Lean4Lean.trIndCtorR_of_ctorTrW`, `Lean4Lean.trIndCtorR_iff_of_ctorTrW`,
  `Lean4Lean.trCtorsW_of_ctorTrW`, `Lean4Lean.CtorsInFragmentW`,
  `Lean4Lean.trCtorsW_iff_of_fragmentW`, `Lean4Lean.ctorsInFragmentW_of_ctorsInFragment`.

M09 `lean_run_code`: built the FOURTH escape and printed its stored `Expr` with `repr`.
    `def Arr : Type 1 := Type → Type` ; `def idf : Arr := fun α => α`
    `inductive WithConv | mk : idf Nat → WithConv`
  Stored: `WithConv.mk : .forallE _ (.app (.const `idf []) (.const `Nat [])) (.const `WithConv [])`
          `idf : .const `Arr []`   (NOT syntactically a `∀`)
  **This constructor type is inside the ORIGINAL fragment's head set** (`app`, `forallE`, `const`
  only) **and the inferencer still returns `none`**, at the faithful environment, because
  `piOf? (.const `Arr []) = none`. So the head enumeration was never the whole story, and
  `ctorTr?_none_of_nonSyntacticPi`'s artificial `F`/`G` example has a real-declaration counterpart.
  **This is the conversion boundary, and it cannot be widened without `VEnv.IsDefEq`:** closing it
  means delta-unfolding `Arr` and then transporting `HasType f' (.const Arr [])` to
  `HasType f' (.forallE .nat .nat)`, which is `HasType.defeq` — a conversion check by definition.

M10 §5, §6, §7, §8 written. Three small fixes total across the three appends (a numeral instance
  for `idf Nat`, a structure-projection `rw` replaced by a general lemma, a `.lit` case that needed
  splitting on the `Literal`). Final `lean_diagnostic_messages` on the whole file:
  **0 errors, 0 warnings.** New named content:
  §5a  `Lean4Lean.FragEx.natGc`, `...lam_before_after`, `...lam_trExprS`, `...lit_before_after`,
       `...lit_trExprS`, `...withLit_inFragmentW`, `...withLam_inFragmentW`,
       `...withLet_not_inFragmentW`
  §5b  `Lean4Lean.FragEx.Arr`, `...idf`, `...WithConv`, `...convGc`, `...withConv_inFragment`,
       `...withConv_inFragmentW`, `...withConv_ctorTr?_none`, `...withConv_ctorTrW?_none`,
       `...withConvIndType`, `...withConv_not_ctorsInFragmentW`,
       `Lean4Lean.ctorTrW?_app_eq_none_of_not_piOf`, `Lean4Lean.ctorTr?_app_eq_none_of_not_piOf`
  §6   `Lean4Lean.inFragmentFM`, `Lean4Lean.inFragmentFM_eq_inFragmentW`,
       `Lean4Lean.letE_still_out`, `Lean4Lean.not_isUnique_proj`, `Lean4Lean.proj_still_out`,
       `Lean4Lean.strVal_still_out`, `Lean4Lean.not_ctorsInFragmentW_of_ctor`
  §7   `Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTrW`, `...ntree_ctorsInFragmentW`,
       `...ntreeAux_trCtorsW`, `...ntreeAux_trCtorsW_witness` (the arity-0 witness)

## §2 Round-close numbers (all measured after the final edit)

M11 whole-tree `lake build`: **Build completed successfully (1639 jobs)**, exit 0.
  (`grep -c error` = 3, all three are the word "error" inside pre-existing witness *messages* in
  `RunIdentity.lean` and `ClosednessPropagation.lean`, not diagnostics.)
M12 `lake env lean --run scripts/sorry-census-all.lean`:
  **BUILT: 456; in population but NOT BUILT: 0** and **HOLES ... : 13**. -> 13 / NOT BUILT 0 ✓
M13 `lake build Lean4Lean.Verify.Guard`, all three guards:
  guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
  guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
  guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
M14 in-repo section-variable warnings: **0** (`grep "automatically included section variable"`
  over the full build log, filtered to `Lean4Lean/`: zero hits; the only hit in the log is
  `Foundation/FirstOrder/SetTheory/Z.lean`, which is the dependency, not this repo).
M15 `python3 scripts/layer-check.py`: HARD RULE ok, 65 SetModel modules checked, none reaches
  Verify/. **exit 0** ✓. Soft report unchanged (4 pre-existing `Theory/`->`Verify/` edges, none
  mine).
M16 import-closure check (python, same walk as `layer-check.py`): closure of
  `Lean4Lean.Verify.Inductive.FragmentWiden` = **198 modules**, single direct import
  `Lean4Lean.Verify.Inductive.TrExprSGeneral`. **OUT of closure:**
  `Lean4Lean.Verify.Inductive.FlipConstruct`, `Lean4Lean.Verify.Inductive.TrTypeProducer`,
  `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`, `Lean4Lean.Verify.Soundness`,
  `Lean4Lean.Verify.Guard`. So `tr_ntreeNodeType` is not in scope and the §7 witness cannot use it.
M17 `exists.lean` on the round's deliverables (population 453, watching 6). Every row:
  hole **false**, cone-reaches-sorryAx **false**, **watched declarations in cone: none of 6**.
    `Lean4Lean.inFragment`                                   arity 1  cone  391
    `Lean4Lean.inFragment_of_ctorTr?`                        arity 6  cone  938
    `Lean4Lean.ctorTr?_eq_none_of_not_inFragment`            arity 5  cone  939
    `Lean4Lean.FragEx.withLit_not_ctorsInFragment`           arity 2  cone  957
    `Lean4Lean.FragEx.withLam_not_ctorsInFragment`           arity 2  cone  955
    `Lean4Lean.FragEx.withLet_not_ctorsInFragment`           arity 2  cone  957
    `Lean4Lean.ctorTrW?`                                     arity 4  cone  927
    `Lean4Lean.ctorTrW?_sound`                               arity 9  cone 3790
    `Lean4Lean.trExprS_natLit`                               arity 7  cone 3642
    `Lean4Lean.CtorsInFragmentW`                             arity 3  cone  932
    `Lean4Lean.trCtorsW_of_ctorTrW`                          arity 21 cone 3888
    `Lean4Lean.trCtorsW_iff_of_fragmentW`                     arity 10 cone 3955
    `Lean4Lean.ctorTrW?_app_eq_none_of_not_piOf`             arity 8  cone  929
    `Lean4Lean.inFragmentFM_eq_inFragmentW`                  arity 2  cone  431
    `Lean4Lean.not_isUnique_proj`                            arity 3  cone   42
    `Lean4Lean.FragEx.withConv_ctorTrW?_none`                arity 0  cone  932
    `Lean4Lean.FragEx.withConv_not_ctorsInFragmentW`         arity 0  cone  945
    `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtorsW_witness` arity **0** cone 4093
  Negative control that fired: `Lean4Lean.FragEx.withLit_not_ctorsInFragmentW` **NOT FOUND** —
  I only built the W-version of the *conversion* counterexample, not of the `.lit` one (the `.lit`
  one is no longer a counterexample after §3, which is the point).
M18 baselines for the cone delta, same run:
    `Lean4Lean.ctorTr?_sound`             arity 9  cone 1147  ->  `ctorTrW?_sound`  3790  (+2643)
    `Lean4Lean.trCtors_of_ctorTr`         arity 21 cone 1257  ->  `trCtorsW_of_ctorTrW` 3888
    `Lean4Lean.trCtors_iff_of_fragment`   arity 10 cone 3938  ->  `trCtorsW_iff_of_fragmentW` 3955 (+17)
    `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtors_witness` arity 0 cone 1533 -> mine 4093
  Reading: the whole +2643 is the nat-literal typing chain (`TrExprS.lit`, `VEnv.ContainsLits`,
  `VEnv.HasType.const/.app`). The `↔` route was already at 3938, so on that route `.lam` + `.lit`
  cost **17 constants**. Prior P4 (witness under ~1600) is WRONG: 4093. But nothing is poisoned —
  every row is clean and watched-free, so the growth is size, not contamination.
M19 `lean_verify Lean4Lean.InductiveDeclExamples.ntreeAux_trCtorsW_witness`:
  axioms **[propext, Classical.choice, Quot.sound]** — no `sorryAx`, no frozen axiom.

## §3 Prior scoring
- P1 (60%, "fragment is very nearly not a restriction but not literally provable"): **the
  direction was right, the reasons were half wrong.** `.fvar` vacuous ✓ (and I proved it, together
  with `.mvar`, from `FVarsIn`). `.lit` occurs ✓. `.lam` occurs ✓ (P1 guessed argument position —
  correct, `Subtype`'s predicate). `.letE` occurs ✓ (P1 said "rare in practice" — it survives
  elaboration verbatim). `.proj` NOT exhibited — P1 over-predicted it.
- P2 (70%, "boundary is `.proj` only"): **WRONG on both halves.** `.lit` was widenable after all
  (but only by *not* using `TrExprS.trLiteral`), and the real boundary is `piOf?`, which P2 did not
  consider at all. `.proj` is a boundary too, but for a reason P2 missed: `IsUnique` is `False`
  there, so the `↔` dies, not just the cost.
- P3 (50%, "`ProjNoNested` already makes `.proj` vacuous for nested blocks"): **not tested.** I
  never needed it; `.proj` never appeared in any constructor type I could construct.
- P4 (80%, "witness under ~1600"): **WRONG**, 4093. Clean, but big.
- P5 (40%, "round-close clean first try"): **right** — build, census, guards, layer-check and
  section-variable count were all clean on the first attempt after the file went green.
