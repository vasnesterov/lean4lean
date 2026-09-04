# handoff-telewf — bridging `TeleWF` from `RecCtx` (OnCtx + level well-formedness)

Owner of this round: exactly `Lean4Lean/Theory/SetModel/TeleWFBridge.lean` (new) and this file.
Read-only everywhere else; `Theory/SetModel/RecTypePeel.lean` and `Theory/Typing/StructEtaPrice.lean`
are being refactored by a concurrent stream — red inside those is not mine.

## 1. Priors (written BEFORE the first instrument call)

Target claim under test: `TeleWF env (D.recPiTele j)` follows from `D.RecCtx env`, and the only
gap is that the four existing typings (`RecCtx.onCtxParams`, `onCtxMotives`, `onCtxMinors`,
`recType_isType`) are phrased as `OnCtx`, which does not record level well-formedness, while
`PropSplit`'s two fields need it. Proposed bridge: `IsDefEq.levelWF` / `CtxStrong.levelWF`.

My priors, with the calibration note applied (cone figures exact all session; scan summaries
and attributions wrong repeatedly — so I will verify by shape, and distrust my own first-pass
attributions):

P1. **All five names exist, in some spelling.** 0.72. Six already-done assignments were caught
    by shape scan this session and one name search invented an absence yesterday, so my prior
    on "something is genuinely missing" is low. But `IsDefEq.levelWF` / `CtxStrong.levelWF`
    smells like a *proposed* name rather than an observed one — the prompt phrases it as
    "the proposed bridge", not "the existing lemma". So:
    - the four typings exist essentially as claimed: 0.80
    - `IsDefEq.levelWF` exists under that exact name: 0.35
    - *some* lemma of that shape (`IsDefEq …  → level well-formedness of the levels involved`)
      exists somewhere in the tree: 0.65
    - `CtxStrong.levelWF` under that exact name: 0.25

P2. **"Bookkeeping" is roughly right this time.** 0.55. Twice this session "bookkeeping" turned
    out to be a refutation, which is exactly why I am told to check. The specific danger I
    expect: `OnCtx` quantifies a *predicate over each prefix*, and if the predicate it carries
    is `IsType`/`HasType` at the prefix, then level well-formedness of the *sort levels* that
    appear inside those types is recoverable only if the typing judgement itself is
    level-sound — i.e. only if there is an inversion lemma taking `HasType Γ e (.sort u)` to
    `u.WF`. If the judgement is defined without a level-WF side condition on `.sort`
    introduction, that inversion is FALSE and the finding is structural. I put:
    - bridge provable with no changes outside my file: 0.55
    - bridge needs a lemma that must live in a file I do not own (statable, but not by me): 0.25
    - genuinely not derivable — `OnCtx` loses the information irrecoverably: 0.20

P3. **The `.sort` introduction rule carries a level-WF hypothesis.** 0.6. This is the crux of P2.
    If yes, `levelWF` is an induction over the typing derivation and is real bookkeeping.
    If the levels are unconstrained (e.g. `Level` is already a WF-by-construction type in this
    tree, or WF is defined as `∀ v ∈ u.vars, v < n` with `n` from the context), then the bridge
    might be *trivial* rather than hard — a third outcome I should watch for. Probability that
    `TeleWF` turns out to be derivable by a `constructor`-level argument because level WF is
    a structural property of the syntax and not a typing fact: 0.30.

P4. **What it unlocks (part c).** The peel's declaration-quantified surjective-pairing theorem
    currently carries `interp` equations as hypotheses. My prior on *which* hypotheses the
    bridge discharges: the `TeleWF`/`PropSplit`-shaped ones only, and I expect there to be
    1–3 of them. Probability that the bridge discharges *literally all* remaining hypotheses so
    that the theorem is hypothesis-free: 0.45 (the prompt reports it, and cone figures have been
    exact, but this is a scan-summary-shaped claim, so I discount it).

P5. **Firing instance (part d).** `ntreeAux_recPiTele_length = 7` will reproduce: 0.85 (a cone
    figure, and those have been exact). Probability the nested example is too heavy to
    elaborate the bridge at and I must fall back to a simpler declaration: 0.40.

P6. **Round close.** census 13 / NOT BUILT 0 reachable: 0.75. Zero new section-variable
    warnings: 0.85.

## 2. Measurements (appended one line per instrument call, as made)

M1 (grep, 5 names): all four typings exist, fully qualified as
  `Lean4Lean.VInductDecl'.RecCtx.onCtxParams`   — Theory/Inductive/Lemmas.lean:1086
  `Lean4Lean.VInductDecl'.onCtxMotives`         — Theory/Inductive/Lemmas.lean:1148
  `Lean4Lean.VInductDecl'.onCtxMinors`          — Theory/Inductive/Lemmas.lean:2575
  `Lean4Lean.VInductDecl'.recType_isType`       — Theory/Inductive/Lemmas.lean:1627
  NOTE the prompt says all four are `RecCtx.*`; only `onCtxParams` is in the `RecCtx` namespace.
  The other three are `VInductDecl'.*` taking `(hR : D.RecCtx env)`. Prior P1 (0.80) confirmed
  in substance, corrected in spelling.
M2 (grep, TeleWF): `Lean4Lean.TeleWF` at Theory/SetModel/RecTypePeel.lean:106, ctor `cons` carries
  `u.WF nv → env.HasType nv Γ A (.sort u)`. So TeleWF = OnCtx-with-named-level + level WF.
  Confirms the diagnosis's shape exactly.
M3 (grep+read): both proposed bridge lemmas EXIST, contra prior P1's 0.35/0.25:
  `Lean4Lean.VEnv.IsDefEq.levelWF`  — Theory/Typing/Lemmas.lean:487
     `(H : env.IsDefEq U Γ e1 e2 A) (W : OnCtx Γ fun _ A => A.LevelWF U) :
        e1.LevelWF U ∧ e2.LevelWF U ∧ A.LevelWF U`
  `Lean4Lean.VEnv.CtxStrong.levelWF` — Theory/Typing/Strong.lean:348
     `CtxStrong env U Γ → OnCtx Γ fun _ A => A.LevelWF U`
  My priors on these two were BOTH too low. Note however CtxStrong.levelWF is the WRONG one for
  this job (it needs `IsDefEqStrong`, which `RecCtx` does not give). The one that matters is
  `onCtx_levelWF`, which exists TWICE already:
  `Lean4Lean.onCtx_levelWF` — Theory/Typing/StrengthenVerdict.lean:108 and, re-proved locally,
  Theory/SetModel/StablePrelude.lean:371. Signature `OnCtx Γ (env.IsType U) → OnCtx Γ (fun _ A =>
  A.LevelWF U)`. THIS is the real bridge component; the prompt named a lemma that works but is
  over-strong.
M4 (read, `VExpr.LevelWF`, Theory/VExpr.lean:169): `(.sort l).LevelWF U` is *by definition*
  `l.WF U`. So `(IsDefEq.levelWF hA W).2.2 : u.WF nv` whenever the type is `.sort u`.
  => the bridge is bookkeeping in the strong sense: it is `onCtx_levelWF` + `.2.2` + a
  prefix-extraction on `OnCtx (Δ ++ Γ)`. NO new mathematics. Prior P2's "provable, 0.55" holds,
  and P3's worry (a missing level-WF side condition on `.sort` introduction) is MOOT: the level
  WF is not read off the introduction rule, it is read off the *type* by `IsDefEq.levelWF`,
  which is an induction over the derivation already proved.
M5 (grep): the OnCtx prefix lemma the generic half needs already exists:
  `Lean4Lean.VEnv.OnCtx.append_right` — Theory/Inductive/Lemmas.lean:204,
  `OnCtx (Δ ++ Γ) P → OnCtx Γ P`. (Also `OnCtx.head_of_append` at :208.)
M6 (read, Theory/Inductive/Lemmas.lean:1627-1670): `recType_isType`'s OWN PROOF already builds
  the two facts the telescope-OnCtx needs, at exactly the right contexts:
    `hI  := VEnv.OnCtx.weakTele hR.ordered W hmin (hR.onCtxIndices hmem)`
           : OnCtx (I.reverse ++ (Min.reverse ++ M.reverse ++ P.reverse)) (env.IsType D.recUvars)
    `hdom := VInductDecl'.tyApp'_hasType hR hT W hmin`
           : the major premise's typing at that same context.
  And `(D.recPiTele j).reverse = [major] ++ I.reverse ++ Min.reverse ++ M.reverse ++ P.reverse`.
  So `OnCtx ((D.recPiTele j).reverse) (env.IsType D.recUvars)` is `⟨hI, ⟨_, hdom⟩⟩` modulo
  associativity — NO inversion of `mkPi` typing is needed, which was the one thing that could
  have made this real mathematics. Bridge confirmed as bookkeeping.
M7 (`lean_run_code` probe, imports `RecTypePeel` + `Inductive/Lemmas`): every piece is ALREADY
  reachable from those two imports — no third copy of `onCtx_levelWF` needed, contra my plan:
    `Lean4Lean.onCtx_levelWF` : ∀ {env U Γ}, OnCtx Γ (env.IsType U) → OnCtx Γ fun _ A => A.LevelWF U
    `Lean4Lean.OnCtx.append_right` (NOT `VEnv.OnCtx.append_right` — my M5 spelling was wrong)
    `Lean4Lean.VEnv.IsDefEq.levelWF`, `Lean4Lean.SetModel.TeleWF`,
    `Lean4Lean.VExpr.tele_ctx_cons`, `Lean4Lean.VEnv.OnCtx.weakTele`,
    `Lean4Lean.VInductDecl'.tyApp'_hasType`, `Lean4Lean.VInductDecl'.onCtxMinors`.
  ALSO: `Lean4Lean.SetModel.InductiveDeclExamples.ntreeAux_recPiTele_length :
  (Lean4Lean.InductiveDeclExamples.ntreeAux.recPiTele 0).length = 7` — reproduced, prior P5 (0.85)
  confirmed. NB the *declaration* is `Lean4Lean.InductiveDeclExamples.ntreeAux`; only the *lemma*
  about it lives in `SetModel.InductiveDeclExamples`.
M8 (read, RecTypePeel §4/§5/§8, lines 155-250 & 400-478): the `TeleWF`-consuming lemmas are
  exactly `SetModel.exists_sort_mkPi`, `SetModel.isProp_mkPi_iff`,
  `SetModel.not_isProof_of_typeFormer`, `SetModel.not_isProof_bvar_of_typeFormer`
  (and `not_isProof_motive_bvar`, which builds its `TeleWF` by hand as `.cons hww hty .nil`).
  `SetModel.eq_singleton_of_mem_interp_mkPi3`'s hypothesis bundle is
  hpm/hpp/hpx (three `IsProp` facts) + hmot/hmin/hmaj/hbody (four `interp` EQUATIONS) + hmk/hf.
  The bridge feeds `isProp_mkPi_iff`, hence hpm/hpp/hpx. It says NOTHING about hmot/hmin/hmaj/
  hbody — those are `interp` computations, not typing facts. FLAG: RecTypePeel's own §"What is
  not here" says the bridge is "the one thing between §7 and a D-quantified surjective-pairing
  theorem with no interp equations left as hypotheses". That last clause looks like an
  over-claim; checking next whether a general `interp` equation for the recursor telescope exists.
M9 (grep + probe): the per-declaration `interp` equations of the hmot shape exist ONLY at three
  fixed declarations — `SetModel.UnitOracleLarge.interpL_motTyU` (unitDeclLE),
  `SetModel.EqRecLarge.motSet_eq_interp_motTyE` (eqIndDecl, under `EqSpec M v`),
  `SetModel.IffRecLarge.motSetI_eq_interp_motTyI` (iffIndDecl, under `IffSpec M`). There is NO
  general `interp (mkPi …) = _ ^ _` equation in `Theory/SetModel/`. So the "no interp equations
  left as hypotheses" half of the target's characterisation is NOT what the bridge buys.
M10 (probe): staging pieces for a real firing all reachable from my two imports —
  `Lean4Lean.VInductDecl'.addIndTypes_ordered`, `addIndCtors_ordered`, `WF.recCtx`.
  `ntreeAux.types.length = 2`, matching `nm = 2` in the 7 = 1+2+3+0+1 cross-check.
  Namespace correction: the WF lemma is `Lean4Lean.InductiveDeclExamples.ntreeAux_WF'`.
  NOTE the probe also reported "Imports are out of date and should be rebuilt" — consistent with
  the concurrent stream's in-flight edits to RecTypePeel/StructEtaPrice.
M11 (`lean_diagnostic_messages`): §1 + §2 of `Theory/SetModel/TeleWFBridge.lean` compile CLEAN
  (success, zero errors, zero warnings). Proved:
    `Lean4Lean.SetModel.TeleWF.of_onCtx`      (converse of the existing `TeleWF.onCtx`)
    `Lean4Lean.SetModel.teleWF_iff_onCtx`
    `Lean4Lean.SetModel.TeleWF.split_right` / `.split_left`
    `Lean4Lean.VInductDecl'.recPiTele_reverse`
    `Lean4Lean.VInductDecl'.recPiTele_onCtx`
    `Lean4Lean.VInductDecl'.recPiTele_teleWF`   <- THE BRIDGE
    `Lean4Lean.VInductDecl'.recPiTele_teleWF'`
  IMPORT CORRECTION to M7: `Lean4Lean.onCtx_levelWF` (StrengthenVerdict) is NOT in RecTypePeel's
  closure — the earlier probe read a stale closure ("imports out of date"). Used
  `Lean4Lean.SetModel.StablePrelude.onCtx_levelWF` instead, via a 1-line import of
  `Theory/SetModel/StablePrelude` (whose only import is StableGuarded). No third copy written.
M12 (`lean_diagnostic_messages`, full file): CLEAN — zero errors, ZERO warnings (so zero
  section-variable warnings), and every `#print axioms` line reports only
  `[propext, Classical.choice, Quot.sound]` subsets. NO `sorryAx` anywhere. Added in §3-§5:
    `Lean4Lean.VInductDecl'.recPiBody_hasType`
    `Lean4Lean.SetModel.isProp_recType_iff` / `isProp_recType_iff'`   <- THE UNLOCK
    `Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF`        <- THE FIRING (member 0)
    `Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF₁`       (member 1, the nested
                                                                       `_nested.List_1` companion)
    `Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF_length` (= 7, cross-check)
    `Lean4Lean.InductiveDeclExamples.ntreeAux_isProp_recType_iff`
M13 (side finding, from the unusedVariables linter): `recPiBody_hasType` does NOT need `RecCtx`
  at all — only `j` naming a member. `recType_isType` threads `hR` through this step and never
  uses it (`lookup_motive` and `HasArgs.bvars` are both env-free). So the recursor BODY's typing
  is cheaper than the tree's use of it suggests; only the TELESCOPE needs `RecCtx`.
M14 (side lemma, proved): `Lean4Lean.VInductDecl'.recPiTele_length_eq_three` — a block with
  `np = 0`, `nm = 1`, `nmin = 1`, no indices has `(D.recPiTele j).length = 3`. This closes a hole
  in my own §3 story: `eq_singleton_of_mem_interp_mkPi3` is a THREE-binder composition, so a
  D-quantified surjective-pairing theorem on it can only quantify over blocks of that shape — and
  that is exactly the shape `eq_singleton_of_recProp` is about, so the restriction is free and the
  bridge's telescope IS that theorem's `[Am, Ap, Ax]`.
M15 (round close, all four instruments):
  * `lake build` (whole tree): **Build completed successfully (1636 jobs)**, zero errors.
  * `lake env lean --run scripts/sorry-census-all.lean`:
      `BUILT: 453; in population but NOT BUILT: 0`
      `HOLES over the WHOLE built population, unioned across both passes: 13`
    => census **13**, **NOT BUILT 0**, unchanged by this round.
  * guards (`lake build Lean4Lean.Verify.Guard`), all three ✓:
      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
  * in-repo `automatically included section variable` warnings: **0**
    (the only such warning in the build is `Foundation/FirstOrder/SetTheory/Z.lean:35`, a
    dependency, not in-repo).
M16 (`exists.lean`, all 16 new names): every one FOUND in
  `Lean4Lean.Theory.SetModel.TeleWFBridge`, and for every one both lines are clean:
      `own value is a hole: false; cone reaches sorryAx: false`
      `watched declarations in cone: none of 6`
  Cones: of_onCtx 880, teleWF_iff_onCtx 890, split_right 892, split_left 892,
  recPiTele_reverse 680, recPiTele_onCtx 2742, recPiTele_teleWF 2773, recPiTele_teleWF' 2774,
  recPiBody_hasType 1824, recPiTele_length_eq_three 1546, isProp_recType_iff 3557,
  isProp_recType_iff' 3558, ntreeAux_recPiTele_teleWF 3384, ntreeAux_recPiTele_teleWF₁ 3205,
  ntreeAux_recPiTele_teleWF_length 1557, ntreeAux_isProp_recType_iff 3854.
  NOTE `Theory/SetModel/TeleWFBridge` is in the census's ORPHAN list (51 modules) — nothing
  imports it yet, which is expected for a fresh leaf and is the reason `exists.lean`'s
  filesystem-walk population, not a fixed import list, is the right instrument here.

## 3. Scoring my priors

P1 (all five names exist, 0.72): **CORRECT, and I was too pessimistic on the two bridge lemmas.**
  0.35 for `IsDefEq.levelWF` and 0.25 for `CtxStrong.levelWF` were both badly low — both exist
  under exactly those names. But my instinct that the *named* bridge was not the *right* bridge
  was sound: `CtxStrong.levelWF` needs `IsDefEqStrong`, which `RecCtx` does not supply;
  the lemma that actually pays is `onCtx_levelWF`, which the target did not name and which exists
  TWICE. Also: the target attributes all four typings to the `RecCtx` namespace; only one is
  there. Net: the target's *shape* claims were right, its *names* were half wrong — consistent
  with the calibration note.
P2 (bookkeeping, provable, 0.55): **CORRECT.** No new mathematics; ~40 lines of real content.
P3 (the `.sort` rule carries a level-WF hypothesis, 0.6): **MOOT, and I mis-framed the risk.**
  Level WF is not read off an introduction rule at all — `IsDefEq.levelWF` reads it off the
  *type*, and `(VExpr.sort u).LevelWF nv` is `u.WF nv` by definition. My "0.30 that it is
  trivial for a structural reason" was closer to the truth than my main line.
P4 ("no interp equations left", 0.45): **REFUTED, and this is the round's finding.** The bridge
  discharges the three `IsProp` hypotheses and nothing else. See §4.
P5 (`ntreeAux` length 7 reproduces, 0.85): **CORRECT**, and the nested block was not too heavy —
  no fallback to a simpler declaration was needed (I fired at BOTH members).
P6 (census 13 / NOT BUILT 0, 0.75; zero section-var warnings, 0.85): **both CORRECT.**

## 4. The one correction to the target's characterisation

`RecTypePeel.lean` §"What is not here" says the bridge is "the one thing between §7 and a
`D`-quantified surjective-pairing theorem with **no `interp` equations left as hypotheses**".
The first half is right; **the italicised half is an over-claim.** Measured:

* the bridge (+ `recPiBody_hasType`) discharges the `TeleWF` side condition of `exists_sort_mkPi`,
  `isProp_mkPi_iff`, `not_isProof_of_typeFormer`, `not_isProof_bvar_of_typeFormer`, and hence —
  via the new `SetModel.isProp_recType_iff` — the three `IsProp` hypotheses
  `hpm`/`hpp`/`hpx` of `SetModel.eq_singleton_of_mem_interp_mkPi3`. That is 3 of its 9 hypotheses.
* it discharges **none** of `hmot`/`hmin`/`hmaj`/`hbody`. Those are `interp` *equations*; typing
  facts cannot produce them. The tree has them only at three fixed declarations
  (`UnitOracleLarge.interpL_motTyU`, `EqRecLarge.motSet_eq_interp_motTyE`,
  `IffRecLarge.motSetI_eq_interp_motTyI`), and no general `interp (mkPi …) = _ ^ _` equation
  exists anywhere in `Theory/SetModel/`.
* `hmk`/`hf` are the instance's own data and are not the bridge's business either.

So the remaining distance to a fully declaration-quantified surjective-pairing theorem is a
SECOND item, not zero items: a general `interp` computation for the recursor telescope's entries.
Its hardest sub-part is `hmin`, which ties the free parameter `mkv` to the constructor's
denotation — an oracle datum, not a typing consequence. Recommended next round: build
`interp (D.motiveType j) = UProp ^ ⟦D.tyApp' j j []⟧` in general (the `hmot` shape), for which the
inputs are `interp_forallE_type`, the bridge's not-a-prop side condition, and a
`mkForallType`-with-constant-codomain = exponential equation which I did not find in the tree.
