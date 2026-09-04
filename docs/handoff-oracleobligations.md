# handoff-oracleobligations

Round target: the model side's remaining work — the two `InductOracleOK` obligations
`hmk : M.cnst cc cus ∈ M.cnst tc tus` and `hf` (naming `M.cnst cc cus` concretely).

I own exactly `Lean4Lean/Theory/SetModel/OracleObligations.lean` (new) and this file.

## Priors, recorded BEFORE the first measurement

These are guesses. Each is confirmed/refuted below with a measurement appended as it is made.

P1. `Lean4Lean.SetModel.cnst_eq_singleton_of_mem_interp_recTyG` exists, arity 32, cone 6487,
    hole-free, "none of 6". Expect: CONFIRMED (orchestrator's cone figures exact for six rounds).
P2. `Lean4Lean.SetModel.eq_singleton_of_recProp` exists in `Theory/SetModel/RecPropSingleton.lean`,
    arity 8, cone 5826, hole-free. Expect: CONFIRMED.
P3. `Lean4Lean.SetModel.soundAbove` hole-free. Expect: CONFIRMED.
P4. `hmk` has NO route from typing. Reasoning: the interpretation of a constant is whatever the
    oracle handed us; a typing derivation `Γ ⊢ mkApp : tyApp` is interpreted through `M.cnst`, so
    any membership fact about `M.cnst cc cus` must already be an oracle hypothesis or be derived
    from one. Expect: CONFIRMED, so (b) applies and I owe an `↔`.
P5. The `InductOracleOK` fragment that supplies `hmk` is a per-constructor typing/soundness field.
    Expect: an `↔` against exactly that field, i.e. `hmk` is EQUIVALENT to it (not merely implied),
    so no smaller fragment suffices.
P6. `hf` is NOT derivable at all in general — "which set" is oracle-chosen, so `hf` must be a
    hypothesis of any consumer. Expect: for the *unit-like* block specifically, `hf` IS derivable
    from `hmk` + the recursor obligation, because a singleton has only one element. That would
    make `hf` collapse into `hmk` at the arities that matter.
P7. Firing declaration: the unit-like block (existing `InductOracleOK` witness). `ntreeAux` will
    NOT be reachable (7 telescope binders vs 3). Expect: CONFIRMED.
P8. Round-close numbers reproduce: census 13 / NOT BUILT 0, three guards, layer-check exit 0.
P9. Foundation supplies everything needed; I will need no new Foundation lemma, because the
    obligations are membership facts in the oracle's own data, not set-theoretic constructions.

## Measurements (appended as made)

M1 (exists.lean, population 454 built modules, watching 6):
  Lean4Lean.SetModel.cnst_eq_singleton_of_mem_interp_recTyG
    module Lean4Lean.Theory.SetModel.InterpMkPi, arity 32, cone 6487
    own value is a hole: false; cone reaches sorryAx: false; watched: none of 6
  Lean4Lean.SetModel.eq_singleton_of_recProp
    module Lean4Lean.Theory.SetModel.RecPropSingleton, arity 8, cone 5826
    own value is a hole: false; cone reaches sorryAx: false; watched: none of 6
  Lean4Lean.SetModel.soundAbove
    module Lean4Lean.Theory.SetModel.SoundInduction, arity 23, cone 7163
    own value is a hole: false; cone reaches sorryAx: false; watched: none of 6
  Lean4Lean.SetModel.InductOracleOK
    module Lean4Lean.Theory.SetModel.CnstRecursion, arity 13, cone 678
    [NO PROOF TERM: cone is type-constants only] hole: false; sorryAx: false; watched: none of 6
  => P1 CONFIRMED, P2 CONFIRMED, P3 CONFIRMED (arity 23, cone 7163, hole-free).

M2 (read of `cnst_eq_singleton_of_mem_interp_recTyG`, `InterpMkPi.lean:300-372`):
  the two residual hypotheses are, VERBATIM:
    (hmk : M.cnst cc cus ∈ M.cnst tc tus)
    (hf  : f ∈ (interp M L Γ (recTyG tc cc tus cus w)).toFun ρ)
  **ATTRIBUTION CORRECTION to the brief.** The brief said obligation 2 is "`hf` — naming
  `M.cnst cc cus` concretely". That merges two distinct things. `hf` is NOT the naming problem:
  it is *inhabitation of the recursor's type*, and the file's own docstring says so
  ("`hf`, which is `InductOracleOK.type` at the recursor"). The naming problem is a THIRD,
  separate item, listed separately in the same docstring ("Naming `M.cnst cc cus` concretely"),
  and it is a *consumer convenience*, not a hypothesis of the theorem at all — the theorem's
  conclusion `M.cnst tc tus = {M.cnst cc cus}` is already closed without it.
  => calibration held: attribution wrong (9th time), cone figures exact (7th round).

M3 (definitions, `Cnst.lean:181`, `CnstRecursion.lean:504`):
  `OracleOK` has exactly two fields, `congr` and `type`; `type` is
    `∀ {us}, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
       Above ⟨κ,ls,c⟩ (o n us ∈ (interp ⟨κ,ls,c⟩ L [] (ci.type.instL us)).toFun ∅)`
  `InductOracleOK` has exactly two fields, `consts : ∀ p ∈ D.allConsts, OracleOK …` and
  `rules : ∀ df ∈ D.iotaRules, DefEqOK …`.
  PREDICTION now sharpened (supersedes P5): BOTH residuals are instances of the SAME field,
  `OracleOK.type`, at two different names — `hmk` at the constructor, `hf` at the recursor.
  Neither needs `congr`; neither needs `rules`. So the smallest supplying fragment is
  `InductOracleOK.consts` restricted to two names, and specifically only its `.type` half.

M4 (baseline `lake build`, BEFORE I wrote anything): **NOT green.**
  `error: Lean4Lean/Theory/Typing/SEReduce.lean:482/483: failed to synthesize Inhabited VDefEq`
  (3 errors) plus a noConfusion type error. `git status` shows `SEReduce.lean` as an UNTRACKED
  new file, i.e. a *concurrent stream's* in-progress work; it is not mine and not in my import
  closure (`SEReduce` imports ConstAppInvSIProof + ConfluenceRebuildPrice, neither of which is
  SetModel). Recorded here so the round-close figure is not attributed to me.

M5 (module written, `lake build Lean4Lean.Theory.SetModel.OracleObligations`):
  compiles with ZERO errors and ZERO warnings. Imports: `InterpMkPi` + `TeleWFBridge`
  (TeleWFBridge's 117-module closure supplies AboveAudit/CoherentConstShape's
  `above_iff_of_chain`, UnitOracleLarge's `inductOracleOKL`, CnstRecursion's `InductOracleOK`).
  Neither imports the other, so no cycle; both are in Theory/SetModel so no Verify reach.
  => P9 CONFIRMED: no Foundation lemma needed anywhere in the file.
  => P5 REFUTED as stated and REPLACED: the supplying fragment is not "a per-constructor
     typing/soundness field"; it is `OracleOK.type` — ONE field — at TWO names.

M6 (file complete, 16 declarations, `lake build` of the module): ZERO errors, ZERO warnings.
  Every one of the 16 `#print axioms` lines reads exactly
  `[propext, Classical.choice, Quot.sound]` (two read less: `mem_allNames_of_mem_allConsts`
  is `[propext, Quot.sound]`, `ntreeAux_not_three_binder` "does not depend on any axioms").
  No `sorryAx` anywhere. This is the local hole-detector the process rules require.

M7 (the characterisation, settled):
  * `hmk` IS the constructor's `OracleOK.type` cell. `mem_cnst_iff_oracleTypeCell` is an `↔`;
    both sides are the same proposition modulo (i) `interp_const`, (ii) `c cc cus = o cc cus`,
    (iii) `above_iff_of_chain`. => P4 CONFIRMED (no route from typing) and the `↔` is delivered.
  * `hf` is *inhabitation of the recursor's type*, supplied by the recursor's cell with witness
    `o rc rus`. It is STRICTLY WEAKER than the cell: `f` occurs in no other hypothesis and not
    in the conclusion, so only nonemptiness is consumed
    (`cnst_eq_singleton_of_nonempty_interp_recTyG`). Hence deliberately NO `↔` for `hf`.
  * P6 REFUTED: `hf` is not the naming problem, so "for the unit block hf collapses into hmk"
    was answering the wrong question. The naming problem is a third item and is not a
    hypothesis of the eta theorem at all.

M8 (exists.lean on all 16 new declarations, population 455, watching 6). Every one:
  `own value is a hole: false; cone reaches sorryAx: false; watched declarations in cone: none of 6`.
  module = Lean4Lean.Theory.SetModel.OracleObligations throughout.
    OracleTypeCell                                    arity 15, cone 6291
    OracleOK.cell                                     arity 18, cone 6297
    oracleOK_iff_congr_and_cells                      arity 14, cone 6303
    mem_cnst_iff_oracleTypeCell                       arity 20, cone 6299
    mem_cnst_of_oracleTypeCell                        arity 21, cone 6300
    cnst_eq_singleton_of_nonempty_interp_recTyG       arity 31, cone 6489
    exists_mem_interp_of_oracleTypeCell               arity 19, cone 6295
    mem_interpCtx_nil                                 arity  9, cone 6294
    cnst_eq_singleton_of_inductOracleOK               arity 44, cone 6590
    cnstOf_induct_eq_oracle                           arity 16, cone 6477
    mem_allNames_of_mem_allConsts                     arity  3, cone  752
    cnst_eq_singleton_of_oracleFits                   arity 43, cone 6705
    UnitAudit.unitL_denot_eq_singleton_of_inductOracleOK     arity 15, cone 8413
    UnitAudit.unitL_denot_eq_singleton_pt_of_inductOracleOK  arity 15, cone 8414
    UnitAudit.unitL_denot_eq_singleton_of_oracleFits         arity 15, cone 8458
    InductiveDeclExamples.ntreeAux_not_three_binder   arity  0, cone  149

M9 (can-cite.py, four candidate consumers): **NO for all four** —
  `Theory.Equiconsistency` (closure 153), `Theory.SetModel.CnstRecursion` (65),
  `Verify.Soundness` (38), `Theory.SetModel.PreludeOracle` (101) would each have to GAIN
  `Lean4Lean.Theory.SetModel.OracleObligations`. Stated up front so this document does not
  repeat the "listed as available, uncitable at the consumer" failure: the content is a NEW
  LEAF. `CnstRecursion` in particular is *upstream* of the eta machinery and can never cite it;
  a consumer must be downstream of `InterpMkPi` + `TeleWFBridge`, which any general
  `InductOracleOK` witness will be anyway.
  Side effect worth recording: `InterpMkPi.lean` and `TeleWFBridge.lean` were imported by
  NOTHING before this round (checked by grep across `Lean4Lean/`); this file is their first
  consumer, so it de-orphaned both. It is itself now an orphan (52 orphans, mine included).

M10 (round-close):
  whole-tree `lake build`: **green**, "Build completed successfully (1641 jobs)", exit 0.
    (The baseline failure of M4 was a concurrent stream's `SEReduce.lean`; that stream fixed it.)
  census `lake env lean --run scripts/sorry-census-all.lean --run`:
    `BUILT: 458; in population but NOT BUILT: 0` and `HOLES ... : 13` (pass A 13, pass B 0).
  three guards (`lake build Lean4Lean.Verify.Guard`):
    guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
    guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
    guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
  `python3 scripts/layer-check.py`: exit 0, "ok - 66 module(s) checked, none reaches Verify/".
  section-variable warnings: **66 in-repo, ALL pre-existing, 0 in my file.** The brief asked for
  "zero in-repo section-variable warnings"; that target is not reachable from a round that owns
  one new file. They sit in 24 files I do not own, the largest being
  `Theory/SetModel/StableAudit.lean` (14) and `Theory/Inductive/StructureClosed.lean` (9).
  => P8 CONFIRMED for census/guards/layer-check; the section-variable clause is not achievable
     by this round and is reported rather than claimed.

M11 (the model's remaining debt, classified):
  The 13 census holes contain exactly ONE model-side entry:
  `Lean4Lean.leanTT_equiconsistent_zfc_omega_inaccessibles [Lean4Lean.Theory.Equiconsistency]`.
  I did NOT touch `Theory/Equiconsistency.lean` and I did NOT touch Foundation (no `lake update`,
  no pin change, no Foundation lemma used).
  `InductOracleOK` is NOT a hole: `coherentOn_cnstOf` takes it as a hypothesis, so the residual
  is NAMED, not hidden. The model's remaining debt is therefore **ordinary open work**: a general
  `InductOracleOK` witness (both fields, arbitrary `D`), of which this round supplies the
  consumer side — what the `consts` field is *for* at two of the names — and none of the
  producer side.

M12 (added after M8, so measured separately):
  §4b `cnstOf_induct_eq_oracle` / `cnst_eq_singleton_of_oracleFits` — structure eta from
  `OracleFits`, the form `coherentOn_cnstOf` quantifies over; `hco` is free there.
  §5 `UnitAudit.unitL_denot_eq_singleton_of_oracleFits` (cone 8458) and
  `UnitAudit.unitL_denot_eq_singleton_omegaChain` (arity 12, cone 8766, hole-free, sorryAx-free,
  none of 6) — the latter discharges `hκ` outright at `InaccChainOmega.omegaChain V`, so no
  hypothesis in the whole chain is left unsatisfiable. 17 declarations total.

M13 (round-close, FINAL, after two concurrent-stream breakages cleared):
  Two other streams broke the tree during this round and both fixed it:
  `Theory/Typing/SEReduce.lean` (M4) and `Verify/Inductive/SurfaceMap.lean`
  (`BUILT: 459; NOT BUILT: 1` at that moment). Neither is mine; neither is in my closure.
  Final, on a green tree:
    whole-tree `lake build`: "Build completed successfully (1643 jobs)", 0 errors.
    census: `BUILT: 460; in population but NOT BUILT: 0`; `HOLES ... : 13`.
    guard 1 ✓ (24 frozen axioms), guard 2 ✓ (whitelist; proof INCOMPLETE: sorryAx present),
    guard 3 ✓ (2/2 remaining).
    `scripts/layer-check.py` exit 0.
    warnings from `OracleObligations.lean` in the whole-tree pass: 0.
    section-variable warnings: 66 in-repo, all pre-existing, 0 mine (see M10).

## Priors scoreboard
  P1 CONFIRMED   P2 CONFIRMED   P3 CONFIRMED   P4 CONFIRMED
  P5 REFUTED and replaced (one field, two names — not a per-constructor field)
  P6 REFUTED (wrong question: `hf` is not the naming problem)
  P7 CONFIRMED   P8 CONFIRMED except the section-variable clause, which is unreachable
  P9 CONFIRMED (no Foundation lemma used; pin untouched)
