# handoff-checkerroute — pricing the checker route for `TrIndDeclN.trCtors`

Owner of this round: exactly `docs/handoff-checkerroute.md` (this file) and, if a claim needs
Lean, `Lean4Lean/Verify/Inductive/CheckerRouteScope.lean` (new). Everything else READ-ONLY.
Frozen and untouched: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.
Concurrent streams own `Verify/Inductive/SurfaceMap.lean`, `Theory/Typing/SEReduce.lean`,
`Theory/SetModel/OracleObligations.lean` — a red build there is theirs, not mine.

Round opened 2026-09-04.

## §0 Priors, written BEFORE the first instrument call

Inputs so far: CLAUDE.md, the brief, `docs/handoff-fragmentwiden.md` (predecessor), the header
prose of `Verify/Inductive/TrTypeProducer.lean`, §8 of `Verify/Inductive/FragmentWiden.lean`,
and grep hits for `checkType.WF` / `weakFV_inv`. Nothing below is measured.

Brief-supplied figures I have NOT verified (each gets an instrument line in §1):
- `Lean4Lean.TypeChecker.checkType.WF` — arity 4, cone 18795, 8 holes, watched
  `VEnv.IsDefEq.uniq` + `uniqU`.
- `Lean4Lean.TrExprS.weakFV_inv` — cone 8653, 5 holes, same two watched.
- `Lean4Lean.FragEx.withConv_ctorTr?_none` — arity 0, cone 918.
- census 13 holes / NOT BUILT 0.

### The predictions

**P1 (85%) The marginal cost of the checker route, measured at the top of the assembled
producer's eventual consumer (the `addDecl` WF path), is ZERO or near-zero.** Reasoning, and it
is a grep fact not a guess: `Verify/Environment.lean:213`, `Verify/Environment/Checker.lean:91`
and `:136` already cite `TypeChecker.checkType.WF`, and those are on the `addDecl`
well-formedness path, i.e. downstream of wherever `TrIndDeclN` gets assembled. If so the checker
is *already paid for* and "the checker route contaminates the producer" is a statement about the
producer in isolation, not about the artifact.

**P2 (85%) The marginal cost measured at `trIndDeclN_of_ownId` itself is LARGE — the whole gross
18795 minus its 1445, i.e. ~17k new constants and 8 new holes.** So the answer to (a) is
route-dependent, and the honest report must give *both* numbers with their measurement points
named. I expect the two numbers to differ by more than an order of magnitude.

**P3 (60%) At least 6 of `checkType.WF`'s 8 holes are already in the `addDecl` path's cone.**
I expect the 8 to be `IsDefEq`/`whnf`-flavoured (uniqueness of types, `whnf` correctness), and
those are exactly what any typing-based path needs. RISK: if the census's 13 include holes that
are *only* reachable through `checkType.WF`, the marginal hole count at the top is > 0 and P1's
"zero" is wrong in the way that matters.

**P4 (70%) A narrow conversion lemma of the asked shape EXISTS or is provable cleanly.** The
transport half — `HasType f' A` and `IsDefEqU A B` gives `HasType f' B` — is certainly already
in the tree (`HasType.defeqU_r`-shaped; `scripts/cone-measure.lean` names
`Lean4Lean.VEnv.HasType.defeqU_l` / `defeqU_r` explicitly, so both exist). The delta half —
`.const c ls` is defeq to its unfolding — must also exist, since `VEnv.IsDefEq` has to have a
delta rule for definitions to be usable at all. So the *lemma* is cheap. My prior is that it is
CLEAN: neither `defeqU_r` nor a delta rule should need `uniq`/`uniqU`.

**P5 (60%) …but the narrow lemma is NOT the whole gap, and this is the trap in (b).** Making
`piOf?` succeed on `.const c ls` needs the inferencer to *find* the unfolding, i.e. `ConstLookup`
must be strengthened from "stored type" to "stored type + stored value", and then the inferencer
must prove its own delta step sound. My prior: a **delta-only** `piOf?` (unfold `.const` heads
against a value-carrying lookup, no beta, no whnf, no recursion into arguments) is enough for the
`withConv` counterexample and stays clean, because delta is a single `IsDefEq` rule and needs no
confluence. Confidence that this specific design works and stays watched-free: 65%. Confidence
that a *full* whnf-based `piOf?` would be clean: 10% — that is the checker.

**P6 (55%) The recommendation I expect to land on is (iii): delta-widened `piOf?`, keeping the
inferencer, not the checker route.** Because it is clean, and because the checker route's only
advantage (already paid for) is an advantage about the *final* artifact and not about the
producer, which is the object streams are actually assembling. But I hold this loosely: if P1
measures as literal zero marginal holes at the top, the checker route becomes very attractive and
I should say so.

**P7 (75%) Nothing I do bears on the concurrent `SurfaceMap` stream's `trCtors` obligation except
by supplying a *different* source for the same field.** Its `M3` records that `trCtors` wants
`ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')` — the same inferencer call. So a delta-widened
inferencer would compose with its map for free (same shape, weaker side condition), whereas the
checker route would NOT: it produces `TrExprS` directly and bypasses `ctorTr?`, so its map's
`trCtors` route would be dead weight there. I expect this to be the single most useful thing I
can tell the orchestrator.

**P8 (85%) Round-close: census 13 / NOT BUILT 0, three guards pass, layer-check exit 0, zero
in-repo section-variable warnings.** I intend at most one small new file with no sorries.

Calibration carried in: the orchestrator's **cone figures have been exact for six rounds**; its
**attributions and relayed prose have been wrong nine times**. So: trust 18795/8653/918/13,
independently verify every "X is proved by Y" and every ownership claim.

## §1 Measurements (append-only, one line per instrument call)

M01 `exists.lean` (population **453** built modules, watching 6 declarations). Verbatim rows:
  - `Lean4Lean.TypeChecker.checkType.WF` — module `Lean4Lean.Verify.TypeChecker`, arity **4**,
    cone **18795**, own value hole false, cone reaches sorryAx **true**, **8 holes**:
    `TrProj.weak'_inv`, `TypeChecker.Inner.isDefEqUnitLike.WF`,
    `TypeChecker.Inner.tryEtaStructCore.WF`, `VEnv.IsDefEqU.weakN_iff`,
    `VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.WF.rigidShapeUniqNS`,
    `VEnv.NormalEq.descend`, `TypeChecker.Inner.inferProj.WF`.
    **WATCHED IN CONE: [`Lean4Lean.VEnv.IsDefEq.uniq`, `Lean4Lean.VEnv.IsDefEq.uniqU`]**.
    -> brief's arity 4 / cone 18795 / 8 holes / 2 watched **EXACT**.
  - `Lean4Lean.TrExprS.weakFV_inv` — module `Lean4Lean.Verify.Typing.Lemmas`, arity **16** (brief
    gave no arity), cone **8653**, **5 holes** (`TrProj.weak'_inv`, `IsDefEqU.weakN_iff`,
    `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `NormalEq.descend`),
    **WATCHED IN CONE: [`IsDefEq.uniq`, `IsDefEq.uniqU`]**. -> brief's 8653 / 5 / 2 **EXACT**.
    Note: its 5 holes are a **subset** of `checkType.WF`'s 8.
  - `Lean4Lean.FragEx.withConv_ctorTr?_none` — arity **0**, cone **918**, hole false, sorryAx
    false, watched none of 6. -> brief's 0 / 918 **EXACT**. (7 exact figures, 7 checkable.)
  - `Lean4Lean.trIndDeclN_of_ownId` — arity 22, cone **1445**, clean, watched none of 6.
  - `Lean4Lean.trCtors_of_ctorTr` — arity 21, cone 1257, clean, watched none of 6.
  - `Lean4Lean.trCtorsW_of_ctorTrW` — arity 21, cone 3888, clean, watched none of 6.
  - `Lean4Lean.addDecl.WF` — module `Lean4Lean.Verify.Environment`, arity 5, cone **20365**,
    **own value IS A HOLE**, holes in cone = `checkType.WF`'s **exact 8, plus itself**,
    **WATCHED IN CONE: [`IsDefEq.uniq`, `IsDefEq.uniqU`]**.
    **THIS IS THE HEADLINE.** The checker's whole contaminated neighbourhood — all 8 holes and
    both watched statements — is *already inside `addDecl.WF`'s cone today*, with no inductive
    producer wired at all.
  - `Lean4Lean.kernel_sound` — arity 6, cone **7915**, own value IS A HOLE, holes in cone =
    **only itself**, watched **none of 6**. **CAVEAT that kills the naive reading:** `kernel_sound`
    is a `sorry`, so its cone is its *statement*'s constants plus the hole — it says nothing about
    what a proof would drag in. Any "marginal cost at `kernel_sound`" figure is meaningless until
    that proof exists. The honest top-of-route measurement point is `addDecl.WF`.
  - `Lean4Lean.VEnv.HasType.defeqU_r` — module `Lean4Lean.Theory.Typing.UniqueTyping`, arity 10,
    cone **3478**, hole in cone `VEnv.IsDefEqU.forallE_inv_stratified`,
    **WATCHED IN CONE: [`Lean4Lean.VEnv.IsDefEq.uniq`]**.
  - `Lean4Lean.VEnv.HasType.defeqU_l` — same module, arity 10, cone 3477, same hole, same watched.
  **P4 IS ALREADY HALF-WRONG**: the obvious transport lemma is *not* clean. It lives in
  `UniqueTyping.lean` and carries `IsDefEq.uniq` plus a hole. A narrow conversion lemma must
  therefore avoid `defeqU_l`/`defeqU_r` entirely, or it inherits exactly what the round is
  trying to dodge.

M02 `lake env lean --run scripts/sorry-census-all.lean`: `on disk: 481; in default-target
  population: 457; Experimental: 24`; **BUILT: 457; in population but NOT BUILT: 0**;
  **HOLES ... : 13** (pass A 13, pass B 0). The 13, verbatim:
    `Lean4Lean.TrProj.weak'_inv` [Verify.Typing.Lemmas]
    `Lean4Lean.TypeChecker.Inner.inferProj.WF` [Verify.TypeChecker.InferType]
    `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` [Verify.TypeChecker.IsDefEq]
    `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` [Verify.TypeChecker.IsDefEq]
    `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` [Theory.Typing.Injectivity]
    `Lean4Lean.VEnv.IsDefEqU.weakN_iff` [Theory.Typing.UniqueTyping]
    `Lean4Lean.VEnv.NormalEq.descend` [Theory.Typing.ChurchRosser]
    `Lean4Lean.VEnv.WF.rigidShapeUniqNS` [Theory.Typing.Injectivity]
    `Lean4Lean.VIndRecArg.exists_indep` [Theory.Inductive.Decl]
    `Lean4Lean.addDecl.WF` [Verify.Environment]
    `Lean4Lean.kernel_complete` [Verify.Soundness]
    `Lean4Lean.kernel_sound` [Verify.Soundness]
    `Lean4Lean.leanTT_equiconsistent_zfc_omega_inaccessibles` [Theory.Equiconsistency]
  **`checkType.WF`'s 8 holes are exactly the first 8 of these** — i.e. the checker's hole set is
  the whole "machinery" half of the census; the other 5 are three top-level goals, one
  inductive-theory lemma with no users, and the equiconsistency bound.

M03 `shape.lean VEnv.defeqs VEnv.HasType VExpr.forallE` (population 454): **6 hits**, of which
  five are `IsDefEqRaw`'s auto-generated recursors and **one is real**:
  `Lean4Lean.VEnv.isDefEq_annotationHead`, arity 9, module **`Lean4Lean.Verify.Inductive.Add`**.
  Reading its source (`Add.lean:822-842`): it proves `outParam A ≡ A` **at a sort** from the
  environment's defining equation alone, by `.extra` (delta) → `.appDF` → `.beta` → `.trans`.
  **That is a delta-unfolding conversion step already in the tree, on the inductive path, proved
  from the `IsDefEq` constructors and nothing else.** Its own docstring says: "what could have
  been unavailable is the conversion, and it is not." So a precedent for (b) exists and (b) is
  not a search for something absent.

M04 `exists.lean` on the conversion pieces (population 454, watching 6):
  - `Lean4Lean.VEnv.IsDefEq.defeq` — `Theory.Typing.Lemmas`, arity 9, cone **10**, hole false,
    sorryAx false, **watched none of 6**. Source (`Lemmas.lean:235`) is literally `.defeqDF h1 h2`,
    i.e. a constructor application. **This is the transport, and it is cone 10 and clean.**
  - `Lean4Lean.VEnv.IsDefEq.extra` — `Theory.Typing.Basic`, arity 8, cone 590 [constructor, no
    proof term], clean. The delta rule itself.
  - `Lean4Lean.VEnv.isDefEq_annotationHead` — arity 9, cone **715**, hole false, sorryAx false,
    **watched none of 6**.
  - `Lean4Lean.VEnv.IsDefEq.extra0` — arity 4, cone 985, clean.
  - `Lean4Lean.piOf?` — arity 1, cone 380, clean. `Lean4Lean.ctorTr?` arity 4 cone 912,
    `Lean4Lean.ConstLookup` arity 2 cone 8, both clean.
  **THE PREDECESSOR'S COSTING OF (b) IS REFUTED.** `FragmentWiden.lean:690-694` says the repair
  "needs `HasType f' (.const c us) → HasType f' (.forallE A B)`, i.e. `VEnv.IsDefEq.defeq` at a
  delta step — a conversion check, by definition. That is why the widening stops here" and, at
  line 920, that it "touches the contaminated `IsDefEq.uniq` / `uniqU` / `checkType.WF` /
  `TrExprS.weakFV_inv` neighbourhood". The named lemma has **cone 10, zero holes, zero watched**,
  and an existing delta instance on the very same path has cone 715, likewise clean. "A conversion
  check by definition" is true and irrelevant: `IsDefEq` *is* the conversion relation, and using
  one of its constructors is not the same as invoking the checker's `isDefEq` procedure.
  (Not my file; I record the correction and do not edit `FragmentWiden.lean`.)

M05 the marginal-cost measurement (throwaway script in `/tmp`, same population walk as
  `exists.lean`; population 455 — it grows under me, concurrent streams are landing files).
  Cone sizes, census-hole membership and watched membership, all measured:

  | seed set | size | census holes | watched |
  | --- | --- | --- | --- |
  | `trIndDeclN_of_ownId` (producer alone) | 1445 | 0/13 | 0/6 |
  | producer + `trCtorsW_of_ctorTrW` + `trIndType_of_ctorTr` + `trCtorsLen_of_skelPrefix` | **3994** | **0/13** | **0/6** |
  | `TypeChecker.checkType.WF` | 18795 | **8**/13 | **2**/6 |
  | `checkType.WF` + `TrExprS.weakFV_inv` | **18795** | 8/13 | 2/6 |
  | `addMutual.WF` | 19027 | 8/13 | 2/6 |
  | `addDefinition.WF` | 19680 | 8/13 | 2/6 |
  | `addDecl.WF` | 20365 | 9/13 | 2/6 |
  | `addDecl.WF_honest` | 20433 | 8/13 | 2/6 |
  | `Bridge.kernel_sound_of` | **20447** | 9/13 | 2/6 |
  | `VEnv.IsDefEq.defeq` | 10 | 0/13 | 0/6 |
  | `VEnv.isDefEq_annotationHead` | 715 | 0/13 | 0/6 |

  First surprise, and it decides (a) on its own: **`cone(weakFV_inv) ⊆ cone(checkType.WF)`
  exactly** — the union is 18795, the same number. So the two contaminated names the brief lists
  are one cost, not two.

  The marginal figures, with the subset test printed:

  | marginal | base | union | NEW constants | NEW holes | NEW watched | add ⊆ base? |
  | --- | --- | --- | --- | --- | --- | --- |
  | checker on producer alone | 1445 | 18899 | **+17454** | **+8** | **+2** | no |
  | checker(+weakFV) on producer+W | 3994 | 18929 | **+14935** | **+8** | **+2** | no |
  | checker(+weakFV) on `addDecl.WF` | 20365 | 20365 | **0** | **0** | **0** | **YES** |
  | checker(+weakFV) on `Bridge.kernel_sound_of` | 20447 | 20447 | **0** | **0** | **0** | **YES** |
  | producer+W on `addDecl.WF` | 20365 | 20459 | **+94** | 0 | 0 | no |
  | `IsDefEq.defeq` on `Bridge.kernel_sound_of` | 20447 | 20447 | **0** | 0 | 0 | **YES** |

  **(a) IS ANSWERED, AND THE ANSWER IS "ZERO".** `cone(checkType.WF) ∪ cone(TrExprS.weakFV_inv)`
  is a **subset** of `cone(Bridge.kernel_sound_of)` — machine-verified containment, not a size
  coincidence. So sourcing `trCtors` from the checker's own inference run adds, *at the assembled
  artifact*, **0 constants, 0 census holes and 0 watched statements**. All 8 holes and both
  watched names are already there.
  And the reason is structural, not accidental: `addDefinition.WF` alone (19680, 8 holes, 2
  watched) and `addMutual.WF` alone (19027, 8 holes, 2 watched) each carry the whole set, because
  `Verify/Environment.lean:213` calls `TypeChecker.checkType.WF` in the **definition** branch.
  `addDecl.WF`'s only `sorry` is `| inductDecl _ _ _ _ => sorry` (`Environment.lean:271`); every
  other branch is proved and already goes through the checker. **`checkType.WF` is on the
  critical path to `kernel_sound` whatever happens to inductives, because `addDecl` must check
  ordinary definitions.**
  Second surprise, and it cuts the other way: **the clean route is not free at the top either.**
  The fragment producer adds **+94** new constants on top of `addDecl.WF` (0 holes, 0 watched) —
  it is a *net addition* to the artifact's cone, whereas the checker route is a net addition of
  nothing. Measured at the artifact, the fragment route is the one with a positive footprint.
  (This does not make it worse: +94 clean is cheaper than +0 that is already contaminated only
  if you are counting contamination you were going to pay anyway. §3 states the choice.)

M06 wrote `Lean4Lean/Verify/Inductive/CheckerRouteScope.lean` (single import:
  `Lean4Lean.Verify.Inductive.FragmentWiden`; `set_option autoImplicit false` at the top, because
  the brief names an `autoImplicit`-induced hole as a past failure). `lake build` on the module:
  **green**, `Built Lean4Lean.Verify.Inductive.CheckerRouteScope`, after three fixes — `≈` is
  `VLevel.instHasEquiv` not a `Setoid` (so `VLevel.equiv_def'.2 rfl`, not `Setoid.refl`), two
  `hsort0 (Γ := …)` instantiations, and `VLevel.WF _ (.imax a b)` is a pair, not `True`.
  New content:
  §1  `Lean4Lean.hasType_delta_sort` — δ at a sort-typed rule, transported into `HasType`.
      `Lean4Lean.hasType_forallE_of_delta_const` — **the exact shape the brief asks for**.
      `Lean4Lean.hasType_app_of_delta_const` — the `.app` case's conclusion.
  §2  `Lean4Lean.FragEx.arrRule`, `...convEnv`, `...convEnv_constants`,
      `...convEnv_defeqs_arrRule`, `...convEnv_arrRule_wf`, `...idf_hasType_const`,
      `...idf_hasType_forallE`, `...withConv_field_isType`, `...withConv_ctorType_isType`,
      `...withConv_conversion_witness` (the **arity-0** witness).
  The whole of §1 is **three constructor applications**: `VEnv.IsDefEq.extra` (δ) then
  `VEnv.IsDefEq.defeq` (= `.defeqDF`). No `VEnv.WF`, no `Ordered`, no `IsType`, no uniqueness.

M07 `#print axioms` on **every** declaration added (the brief's rule; run from a scratch file):
  `hasType_delta_sort` [propext]; `hasType_forallE_of_delta_const` [propext];
  `hasType_app_of_delta_const` [propext]; `FragEx.arrRule` **no axioms**;
  `FragEx.convEnv`, `convEnv_constants`, `convEnv_defeqs_arrRule`, `convEnv_arrRule_wf`,
  `idf_hasType_const`, `idf_hasType_forallE`, `withConv_field_isType`,
  `withConv_ctorType_isType`, `withConv_conversion_witness` — all **[propext, Quot.sound]**.
  **No `sorryAx` anywhere, no frozen axiom anywhere, no `Classical.choice`.** No hole silently
  elaborated.

M08 `exists.lean` on §1/§2 (population 457, watching 6). **Every row: hole false, cone reaches
  sorryAx false, watched declarations in cone none of 6.**
    `Lean4Lean.hasType_delta_sort`                  arity 16  cone  **595**
    `Lean4Lean.hasType_forallE_of_delta_const`      arity 18  cone  **596**
    `Lean4Lean.hasType_app_of_delta_const`          arity 20  cone  **608**
    `Lean4Lean.FragEx.convEnv_arrRule_wf`           arity  0  cone 1641
    `Lean4Lean.FragEx.idf_hasType_forallE`          arity  0  cone  804
    `Lean4Lean.FragEx.withConv_field_isType`        arity  0  cone  818
    `Lean4Lean.FragEx.withConv_ctorType_isType`     arity  0  cone  824
    `Lean4Lean.FragEx.withConv_conversion_witness`  arity **0**  cone 1858
  Compare: `FragEx.withConv_ctorTr?_none` (the failure) is cone **918**; the conversion that
  repairs it costs **596** in total and adds **nothing** watched or holed.
  **(b) IS ANSWERED AFFIRMATIVELY.** The narrow conversion lemma did not exist under any name
  (M03 found only `isDefEq_annotationHead`, a different instance of the same technique); it is
  **provable in three lines**; and it is **clean**.

M09 `lean_run_code`: elaborated two further candidate blocks and printed the stored types/values
  with `repr`. Both are accepted by Lean's own kernel.
  - `def Arr3 : Type 1 := id (Type → Type)`; `def g3 : Arr3 := fun α => α`;
    `inductive WithBeta | mk : g3 Nat → WithBeta`.
    `WithBeta.mk`'s stored type: `.forallE _ (.app (.const g3 []) (.const Nat [])) (.const WithBeta [])`
    — heads `app`, `forallE`, `const` only, i.e. **inside the original fragment**.
    `g3`'s stored type: `.const Arr3 []`. `Arr3`'s stored **value**:
    `.app (.app (.const id [3]) (.sort 2)) (.forallE (.sort 1) (.sort 1))` — an **application**,
    not a `∀`. **So one δ step does not expose the product: it needs δ on `id` then two β steps.**
  - `structure Box where fld : Type 1`; `def bx : Box := ⟨Type → Type⟩`;
    `def g5 : bx.fld := fun (α : Type) => α`; `inductive WithProj | mk : g5 Nat → WithProj`.
    `g5`'s stored type: `.app (.const Box.fld []) (.const bx [])` — **not a `.const` at all**, so
    the narrow lemma does not even apply in shape. Reducing it needs δ on `Box.fld`, β, and then
    a **projection reduction**; and `TrProj.weak'_inv`, the translated-world projection
    inversion, is one of the thirteen census holes.
  **This is the finding that decides (c).** Each widening of `piOf?` closes one reduction rule and
  exposes the next; the fixpoint of the process is `whnf`, and a *verified* `whnf` is
  `TypeChecker`. The δ widening is a **third** finite widening, not a general solution.

M10 §3 + §3a written into `CheckerRouteScope.lean`, machine-checking M09 at the real stored types.
  `lean_diagnostic_messages` on the whole file after the final edit: **0 errors, 0 warnings**
  (one intermediate error — a forward reference to `g5Type` — briefly turned the §3 witness into a
  `sorry`; the warning `declaration uses 'sorry'` caught it, which is exactly why the round-close
  demands the diagnostics and not just the exit code).
  New content, all `rfl`/`rintro` and all arity 0 or 2:
    `Lean4Lean.DeltaBoundary.{Arr3, g3, WithBeta, Box, bx, g5, WithProj, betaGc, projGc}`
    `...g3_storedType`, `...g5_storedType` — **faithfulness against Lean's own stored type**
      (`exprOf% g3 = .const ``Arr3 []`, `exprOf% g5 = .app (.const ``Box.fld []) (.const ``bx [])`)
    `...withBeta_inFragment/inFragmentW/ctorTr?_none/ctorTrW?_none`
    `...withProj_inFragment/inFragmentW/ctorTr?_none/ctorTrW?_none`
    `...arr3Rule`, `...arr3Rule_rhs_not_forallE`, `...piOf?_arr3Rule_rhs`
    `...g5Type`, `...g5Type_not_const`, `...piOf?_g5Type`
    §3a positive controls (so a `= none` is not vacuous by an inadequate table):
    `...betaGc_g3_infers`, `...betaGc_nat_infers`, `...projGc_g5_infers`, `...projGc_nat_infers`
    `...delta_not_general_witness` — the **arity-0** conjunction of all of it.
  `exists.lean` (population 456): `delta_not_general_witness` arity **0** cone **968**;
  `withBeta_ctorTrW?_none` arity 0 cone 932; `withProj_ctorTrW?_none` arity 0 cone 933;
  `arr3Rule_rhs_not_forallE` arity 2 cone 71; `g5Type_not_const` arity 2 cone 61.
  **All five: hole false, sorryAx false, watched none of 6.**
  `#print axioms` on all 28 declarations of the file: `propext` and/or `Quot.sound` only, seven
  with **no axioms at all**; **no `sorryAx`, no frozen axiom, no `Classical.choice`**.

M11 `scripts/can-cite.py` — the availability question the cone instruments cannot answer:
  - consumer `Lean4Lean.Verify.Inductive.TrExprSGeneral` (closure 197): `VEnv.IsDefEq.extra` **YES**,
    `VEnv.IsDefEq.defeq` **YES**, `TypeChecker.checkType.WF` **YES**.
  - consumer `Lean4Lean.Verify.Inductive.TrIndDeclNProducer` (closure 207):
    `TypeChecker.checkType.WF` **YES**, `TrExprS.weakFV_inv` **YES**,
    `Lean4Lean.hasType_delta_sort` **NO** (it lives in my leaf module).
  - consumer `Lean4Lean.Verify.Inductive.AddInductiveStep` (closure 173):
    `TypeChecker.checkType.WF` **YES**, `VEnv.IsDefEq.defeq` **YES**.
  Two consequences, and the second is the one that surprised me:
  1. **Route (ii) needs no migration at all.** `checkType.WF` is already citable at the producer's
     module and at the assembly point.
  2. **The inferencer's own module already imports the checker.** `TrExprSGeneral` can cite
     `checkType.WF` today. So the "clean route" was never clean by *module separation* — it is
     clean by **not citing**, which is a cone fact, not an import fact. `Verify/Inductive/*` files
     that describe themselves as avoiding the checker neighbourhood are avoiding it in the cone,
     with the module already in scope. Nothing is wrong; the distinction just has to be stated,
     because "we don't import the checker there" would be false.
  3. For route (i), §1's lemmas would have to move upstream. That is cheap and the direction is
     *down*, not up: `hasType_delta_sort`'s statement mentions only `VEnv`, `VDefEq`, `VExpr`,
     `HasType` — all in `Theory/` — so it belongs next to `VEnv.IsDefEq.defeq` in
     `Theory/Typing/Lemmas.lean` (or a new `Theory/Typing/` module), not in `Verify/`.

## §2 The two answers, stated once

### (a) The checker route's price

**Gross**: `cone(TypeChecker.checkType.WF) = 18795`, carrying **8 of the 13 census holes** and
**both** watched statements (`VEnv.IsDefEq.uniq`, `VEnv.IsDefEq.uniqU`). Adding
`TrExprS.weakFV_inv` changes nothing: its 8653-cone is a **subset**, and the union is still 18795.

**Marginal — and this is the whole point of the question:**

| measured at | NEW constants | NEW census holes | NEW watched |
| --- | --- | --- | --- |
| `trIndDeclN_of_ownId` alone | +17454 | +8 | +2 |
| assembled producer (ownId + `trCtorsW_of_ctorTrW` + `trIndType_of_ctorTr` + `trCtorsLen_of_skelPrefix`) | +14935 | +8 | +2 |
| `addDecl.WF` | **0** | **0** | **0** |
| `Bridge.kernel_sound_of` | **0** | **0** | **0** |

The last two rows are **containments**, not size coincidences: the script's subset test prints
`true`, i.e. `cone(checkType.WF) ∪ cone(weakFV_inv) ⊆ cone(Bridge.kernel_sound_of)`.

Which of the 13 enter: the 8 are `TrProj.weak'_inv`, `TypeChecker.Inner.inferProj.WF`,
`TypeChecker.Inner.isDefEqUnitLike.WF`, `TypeChecker.Inner.tryEtaStructCore.WF`,
`VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.IsDefEqU.weakN_iff`, `VEnv.NormalEq.descend`,
`VEnv.WF.rigidShapeUniqNS`. **All 8 are already entailed elsewhere in the assembled artifact's
cone**, and the entailing consumers are `addDefinition.WF` (19680, 8 holes) and `addMutual.WF`
(19027, 8 holes) — the *definition* branches, which call `TypeChecker.checkType.WF` at
`Verify/Environment.lean:213`. `addDecl.WF`'s only `sorry` is `| inductDecl _ _ _ _ => sorry`.
So the checker is on the critical path to `kernel_sound` **whatever is done about inductives**,
because `addDecl` must check ordinary definitions before it ever reaches a block.

So the answer the brief offered as first-class is the true one: **the marginal cost is zero,
because the checker is already in the cone.** The 8 holes are not a price the inductive route
would pay; they are a price the artifact has already paid and cannot avoid.

The mirror-image number, which no previous document states: **the fragment route is the one with a
positive footprint at the artifact.** `PRODUCER+W` adds **+94** constants on top of `addDecl.WF`
(0 holes, 0 watched). "Clean" here means "adds no contamination", not "adds nothing".

### (b) Is there a narrower conversion step? YES, and it is three lines

It did not exist under any name (`shape.lean` over `VEnv.defeqs` + `VEnv.HasType` + `VExpr.forallE`
returns six hits: five auto-generated `IsDefEqRaw` recursors and `VEnv.isDefEq_annotationHead`,
which is a *different* instance of the same technique, not this statement). It is now proved:

`Lean4Lean.hasType_forallE_of_delta_const` (arity 18, cone **596**, 0 holes, 0 watched) —
`env.defeqs df`, levels WF and of the right length, `df.lhs.instL ls = .const c ls'`,
`df.rhs.instL ls = .forallE A B`, `df.type.instL ls = .sort u`, and `HasType f (.const c ls')`
give `HasType f (.forallE A B)`. Proof: `VEnv.IsDefEq.extra` (the δ **constructor**) then
`VEnv.IsDefEq.defeq` (which is `.defeqDF`, another **constructor**). No `VEnv.WF`, no `Ordered`,
no uniqueness of types, hence none of `uniq`/`uniqU`/`checkType.WF`/`weakFV_inv`.

Two things are load-bearing and must be said plainly, because the cheap cone number invites
over-reading:

1. **The side condition `df.type.instL ls = .sort u` cannot be relaxed to `IsType`.** `IsType`
   gives `HasType lhs (.sort u)` for *some* `u` while `.extra` gives the equation at
   `df.type.instL ls`; identifying the two **is** uniqueness of types, i.e. `IsDefEq.uniq`. So the
   syntactic-sort condition is precisely the fence between the clean route and the watched one.
   It is decidable, so this is a checkable side condition, not a new obligation.
2. **The lemma closes the exhibited counterexample and not the class.** M09/M10 exhibit two more
   real blocks, both inside the *original* fragment, both rejected by both inferencers, and neither
   reachable by one δ step: `WithBeta` (δ exposes an application — needs δ+β+β) and `WithProj`
   (the type to convert is `Box.fld bx`, not a `.const` at all — needs δ+β+**projection
   reduction**, whose translated-world inversion `TrProj.weak'_inv` is a census hole).

### (c) The design choice, with costs on both sides

**(i) Fragment + the narrow conversion lemma.**
*Gains*: cone 596, zero holes, zero watched; closes `FragEx.WithConv`; composes with itself for δ
chains (`hasType_delta_sort`'s hypothesis and conclusion have the same shape) with no confluence
and no fuel-correctness argument; the lemmas belong in `Theory/Typing/`, i.e. *below* the checker
in the layering.
*Costs*: (α) the inferencer's premise must grow from `ConstLookup` (stored **types**) to something
exposing stored **values** — strictly stronger than the premise `TrExprSGeneral.lean` §7 boasts
about, and a successor must build its staged-environment split, the analogue of
`constLookup_iff_split`; (β) `piOf?` becomes recursive, so it needs fuel or a well-founded measure;
(γ) **it is the third finite widening, and M09 shows the fourth and fifth escapes already**. β and
projection reduction come next, and projection reduction lands on `TrProj.weak'_inv` — a census
hole — so the "clean" route reaches contamination too, just later and by a longer road. The fixpoint
of widening `piOf?` is `whnf`; the verified `whnf` in this repo is `TypeChecker`.
*Effect on the assembled producer's cleanliness*: keeps it at 0 holes / 0 watched **today**, and
adds +94 constants to the artifact's cone. The cleanliness survives only as long as the class stays
short of β and projections.

**(ii) The full checker route** — take `trCtors` from `TypeChecker.checkType.WF`'s output at the
check `checkInductiveTypes`/`checkConstructors` already performs.
*Gains*: **general** — no side condition on the block, no fragment, no widening treadmill; marginal
cost at the artifact **0 constants / 0 holes / 0 watched** (measured containment); `checkType.WF` is
**already citable** at `TrIndDeclNProducer` and at `AddInductiveStep` (M11), so no migration; it is
also what the C++ kernel does, so it is the route that keeps the implementation close to upstream.
*Costs*: the *producer in isolation* stops being clean — +17454 constants, +8 holes, +2 watched
measured at `trIndDeclN_of_ownId`. That is a real loss of a **local** property: every clean result
in this area was obtained by not citing these names, and a producer that cites them can no longer be
audited in isolation with `exists.lean`'s watched line. It also couples the inductive translation to
five open theorems (`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend`,
`TrProj.weak'_inv`) whose proofs are other streams' work — a scheduling cost, not a soundness one.

**(iii) Split the difference, which is what I recommend.** Keep (i) as the *decision procedure* for
the class it settles and use (ii) as the *fallback*, i.e. the field is discharged by "either the
inferencer succeeds (clean, decidable, and then the `↔` holds) **or** the checker's run supplies the
translation existential". `Verify/Inductive/TrTypeProducer.lean` §4 already has exactly this shape
for `trType`: `trType_iff_exists_trans` reduces the field to "the arity translates at the pre-block
environment, and `D` stores that translation", and `exists_indTypes_of_trExprS` takes the
translation existential **as a hypothesis**, so the contamination is confined to whoever supplies it.
Doing the same for `trCtors` costs nothing new and makes the choice a *deployment* decision rather
than an architectural one.

**Recommendation: (iii), with (ii) as the general supplier and (i) kept only where it already
pays.** Concretely, in priority order:
1. State `trCtors_iff_exists_trans` — the `trCtors` analogue of `trType_iff_exists_trans` — taking
   the translation existential as a hypothesis. Clean, no new premise, and it makes the checker
   route a one-line instantiation later.
2. Supply that existential from `checkType.WF` at the assembly point. Marginal cost 0 at the
   artifact; do **not** re-measure the producer in isolation afterwards and call it a regression,
   because the number that matters is the artifact's.
3. Do **not** invest in a δ-widened `piOf?` as a route to generality. Invest in it only if a
   *decidable* fast path is wanted for the common case, and then price it as an optimisation, not
   as a proof route. M09's two escapes are the reason.

## §3 What this bears on for the concurrent `SurfaceMap` stream

Precise, because composing wrongly is the expensive mistake here.

- That stream's `M3` records `trCtors`'s ask as
  `ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')` — i.e. its map must hit the **inferencer's**
  output. Nothing in this round changes that statement, and nothing here duplicates its map: I built
  no `Result.types → VInductDecl'` map and no name-skeleton anything.
- **Where it composes:** route (i) keeps that exact shape. A δ-widened `ctorTrD?` would have the
  same `some (VExpr × VExpr)` signature, so the stream's map and its `trCtorsLen`/`trType` halves
  are untouched, and only the side condition weakens. Its work is *not* invalidated by (i).
- **Where it does NOT compose, and this is the warning:** route (ii) produces `TrExprS` **directly**
  from `checkType.WF` and never calls `ctorTr?`. If the orchestrator adopts (ii) for `trCtors`, that
  stream's `trCtors` arm becomes dead weight — while its `trType` and `trCtorsLen` arms stay valuable
  (both are names-only / sort-pi and already have clean general routes).
- **So the composable instruction is my recommendation (iii)'s step 1**: ask that stream to target
  a `trCtors_iff_exists_trans`-shaped statement — "`D` stores *the* translation" — rather than
  "`ctorTr?` returns it". That form is satisfied by the inferencer *and* by the checker, so its map
  survives either decision. It is also strictly easier: `TrExprS` is functional off `.proj`
  (`TrExprS.unique`), so "stores the translation" is rigid, exactly as
  `TrTypeProducer.lean` §2's `TrIndType.rigid` already establishes for `trType`.

## §4 Prior scoring

- **P1 (85%, "marginal cost at the top is zero or near-zero"): RIGHT, and literally zero** — a
  measured set containment, not an approximation. My stated reason (the `Environment.lean:213`
  grep) was also the right reason.
- **P2 (85%, "marginal at the producer is ~17k and +8 holes"): RIGHT** — +17454 / +8 / +2 at
  `trIndDeclN_of_ownId`, +14935 / +8 / +2 at the assembled producer.
- **P3 (60%, "≥6 of the 8 already in the `addDecl` path"): RIGHT and under-confident** — all 8.
- **P4 (70%, "a narrow conversion lemma exists or is provable cleanly"): RIGHT on the conclusion,
  WRONG on the route.** I predicted `HasType.defeqU_l`/`defeqU_r` would serve; they are **cone
  3478/3477 with `IsDefEq.uniq` in cone and a hole** — exactly the contamination to avoid. The
  clean route is `IsDefEq.extra` + `IsDefEq.defeq` (cone 10), which I did not name in advance.
- **P5 (60%, "the narrow lemma is not the whole gap; δ-only is enough for the counterexample and
  stays clean"): RIGHT on both halves, and the "not the whole gap" half is much stronger than I
  predicted** — I expected the gap to be about *finding* the rule (premise strengthening). It is
  also that, but M09's β and projection escapes are a second, independent reason, and I had not
  thought of them.
- **P6 (55%, "I will recommend (iii) delta-widening, keeping the inferencer"): WRONG in the
  direction that matters.** I recommend the checker as the general supplier and the inferencer only
  as a fast path, because (α) the marginal cost is literally zero and (β) M09 shows the widening
  treadmill does not terminate short of `whnf`. My own P6 reasoning ("the checker's advantage is
  about the artifact and not the producer") was the error: the artifact **is** the goal.
- **P7 (75%, "bears on `SurfaceMap` only by supplying a different source"): RIGHT, and §3 makes it
  actionable** — the composable ask is the `_iff_exists_trans` shape.
- **P8 (85%, round-close clean): RIGHT**, though it took two attempts because a concurrent stream's
  `SurfaceMap.lean` was red mid-round (see §5).

## §5 Round-close numbers (all measured after the final edit)

R1 whole-tree `lake build`: **exit 0, "Build completed successfully (1643 jobs)"**,
  `grep -c "^error"` = **0**.
  *First attempt was red, and not mine*: `Lean4Lean/Verify/Inductive/SurfaceMap.lean:592,593`
  (`Application type mismatch`) — the concurrent stream's file in flight, and for a while its
  `.olean` was absent so the census aborted with
  `object file ... SurfaceMap.olean ... does not exist`. Re-polled until it built; green after.
R2 `lake env lean --run scripts/sorry-census-all.lean`: `BUILT: 460; in population but NOT BUILT:
  **0**`; **HOLES ... : 13** (pass A 13, pass B 0). Same 13 names as M02 — my file added none.
  -> **13 / NOT BUILT 0 ✓**
R3 `lake build Lean4Lean.Verify.Guard`, all three:
  guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
  guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
  guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
R4 in-repo section-variable warnings: **0** (`grep "automatically included section variable"` over
  the full build log has exactly one hit, `Foundation/FirstOrder/SetTheory/Z.lean:35`, which is the
  dependency; filtered to `Lean4Lean/` it is zero).
R5 `python3 scripts/layer-check.py`: HARD RULE ok, **66** SetModel modules checked, none reaches
  `Verify/`. **exit 0 ✓**. Soft report unchanged (the same 4 pre-existing `Theory/`→`Verify/` edges;
  none mine).
R6 `lean_diagnostic_messages` on `Lean4Lean/Verify/Inductive/CheckerRouteScope.lean`:
  **0 errors, 0 warnings.** Single direct import: `Lean4Lean.Verify.Inductive.FragmentWiden`.
R7 frozen files untouched: `git status` shows only untracked additions
  (`Verify/Inductive/CheckerRouteScope.lean`, `docs/handoff-checkerroute.md`) plus other streams'
  files. `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are **unmodified**.
