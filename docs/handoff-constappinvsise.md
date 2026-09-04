# handoff — `ConstAppInvSISE`: is the SE-relation eta guard actually sufficient?

Stream owns exactly `Lean4Lean/Theory/Typing/ConstAppInvSISEProof.lean` (new) and this file.
Everything else read-only. Process rule for this stream: priors first, then **one appended line
per instrument call, as the call is made**. Sixteen crashes here; batching loses everything.

## §0 PRIORS (written before the first measurement of this round)

Stated as falsifiable guesses, so the measurements can contradict them and be seen to.

- **P0 — the brief's arity/cone figures.** Brief says `Lean4Lean.VEnv.ConstAppInvSISE` is arity 2,
  cone 634; the previous round's handoff (`docs/handoff-constappinvsi.md` §P3b) instead names
  `Lean4Lean.ConstAppInvSISEFromWF` (arity 0, cone 638) as "the obligation that is actually left".
  Prior: **both exist**, one is the relation-level `def` and the other the closed `Prop`, and the
  brief has conflated them. Cone figures are calibrated-exact, so I expect 634 and 638 to both
  reproduce, at the two different names. Confidence 0.8.

- **P1 — is `ConstAppInvSISE` true?** Prior: **true but not provable by transport**, and quite
  possibly **not provable at all in this round** without the `NotStructInhabSEOfIsTypeStmt` gap.
  Reasoning: the thirteen-constructor analogue `VEnv.IsDefEq.constApp_inv` is a theorem, and
  `structEta` is the *only* extra constructor of `IsDefEqSE`; `structEta_lhs_structInhabSE` is
  reported to block that one case in one line. So the induction should close **if and only if**
  every other constructor's IH can be re-run over `IsDefEqSE` — and the two suspicious ones are
  `trans` (which is what `guard_rejects_an_axiom` says manufactures violating pairs) and the
  `proofIrrel`/type-level cases that in the 13-ctor proof went through `WF.uniq'`.
  Confidence 0.55 that it is true; confidence 0.3 that I can close it hole-free this round.

- **P2 — where the transport fails (part b).** Prior: `notStructInhab_of_isType` routes through
  `VEnv.WF.uniq'` and `VEnv.const_sort_inv_of_wf`, both of which are *statements about*
  `VEnv.IsDefEq`, not schemas over a relation parameter. Over `IsDefEqSE` uniqueness-of-types is
  not available as a theorem (it would need the whole `UniqueTyping` development redone with
  `structEta`), so the transport failure is **not** a missing lemma but a missing *development*:
  the SE relation has no uniqueness theory. Confidence 0.75. Falsifier: a relation-generic
  `uniq` already in the tree.

- **P3 — vacuity at positive-field shape (part c).** Prior: the previous round already did the
  13-ctor vacuity at both shapes (`MutField.bigEnv_structInhabSE_bar` etc. are named as
  hole-free), and its own §P4 confesses the honest gap is **non-triviality of the SE guard at an
  environment that HAS a structure**. So my new content at (c) should be exactly that gap:
  an SE-guard *satisfaction* fact at `bigEnv`. Prior: satisfiable, because `bigEnv`'s axioms are
  not structure-applications and `StructInhabSE` should fail at them for the same reason as the
  13-ctor guard. Confidence 0.6.

- **P4 — the guard cannot be dropped and cannot be head-name-based.** Taken as measured
  (`guard_rejects_an_axiom` cone 382; `VEnv.structInhabOnlyNoConf_false` cone 3815). Prior: I will
  reproduce both cones and NOT attempt to weaken either. Confidence 0.95 they reproduce.

- **P5 — taint.** Prior: anything I prove that goes through `patWF_of_wf` / `constApp_inv` inherits
  the same four census holes as `spine_inv`, so it is **tainted, re-derived at the same taint**,
  not hole-free. I will say so at each name rather than at the end. Confidence 0.9.

- **P6 — layer.** Prior: my file needs **no** `Verify/` import (all content is `Theory/`-level:
  `NoConfRepair`, `StructEtaPrice`, `MutField`), so `layer-check.py` should not soft-report it.
  Confidence 0.85.

## §1 MEASUREMENTS (append-only, one line per instrument call)

- M1 `exists.lean` × 10 names, population **450 built modules**, watching 6 declarations.
  **P0 CONFIRMED exactly, both figures, at two different names** — the brief conflated a `def`
  with a closed `Prop`:
  - `Lean4Lean.VEnv.ConstAppInvSISE` — FOUND, `Lean4Lean.Theory.Typing.ConstAppInvSIProof`,
    arity **2**, cone **634**, own value a hole: false, cone reaches sorryAx: **false**,
    watched declarations in cone: **none of 6**.
  - `Lean4Lean.ConstAppInvSISEFromWF` — FOUND, same module, arity **0**, cone **638**,
    hole: false, sorryAx: **false**, watched in cone: **none of 6**.
  - `Lean4Lean.VEnv.StructInhabSE` — arity **4**, cone **83**, sorryAx false, watched none of 6.
  - `Lean4Lean.VEnv.structEta_lhs_structInhabSE` — arity **15** (brief/handoff said 15), cone **87**,
    sorryAx false, watched none of 6.
  - `Lean4Lean.NotStructInhabSEOfIsTypeStmt` — arity **0**, cone **97**, sorryAx false, watched none.
  - `Lean4Lean.guard_rejects_an_axiom` — `Lean4Lean.Theory.Typing.NoConfRepair`, arity **7**,
    cone **382**, sorryAx false, watched none of 6.  (brief's 382 exact)
  - `Lean4Lean.VEnv.structInhabOnlyNoConf_false` — `Lean4Lean.Theory.Typing.EtaGuardLand`,
    arity **0**, cone **3815**, sorryAx false, watched none of 6.  (brief's 3815 exact)
  - `Lean4Lean.MutField.unitEnv_noSI_true_but_SE_false` — arity 0, cone **7886**, sorryAx **true**,
    holes `[VEnv.IsDefEqU.weakN_iff, VEnv.IsDefEqU.forallE_inv_stratified, VEnv.WF.rigidShapeUniqNS,
    VEnv.NormalEq.descend]`, **WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq,
    Lean4Lean.VEnv.IsDefEq.uniqU]**.
  - `Lean4Lean.constAppInvSIFromWF` — arity 0, cone **7494**, sorryAx **true**, same four holes,
    **WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]**.
  - `Lean4Lean.constAppInvNoSIFromWF` — arity 0, cone **7491**, sorryAx **true**, same four holes,
    **WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]**.
  Note for P5: the SE-side statements are *hole-free as statements* (634/638/83/87/97) precisely
  because nothing proves them yet; the 13-ctor side is tainted at four holes AND at two watched.
- M2 read `Theory/Typing/ConstAppInvSIProof.lean` (read-only, prior stream's). Confirms P0's split:
  `VEnv.ConstAppInvSISE` is the arity-2 `def` (line 192), `ConstAppInvSISEFromWF` the arity-0 `Prop`
  (line 201). `VEnv.StructInhabSE` (171) = `StructInhabAt (fun e A => IsDefEqSE U Γ e e A)`.
- M3 read `Theory/Typing/StructEtaPrice.lean`: `IsDefEqSE` is 14 ctors (163-214); `structEta`'s
  eighth premise is `IsDefEqSE Γ e e ((const S us).mkApp ps)`; **`IsDefEq.toSE` (237) gives the
  inclusion 13 ⊆ 14 only**, never the converse.
- M4 read `Verify/Typing/ConstSpine.lean:248` — `VEnv.IsDefEq.constApp_inv`'s proof is
  `church_rosser` → `ParRedS.constApp_inv` ×2 → `NormalEq.constApp_inv` → `spine_args_parRedS_defeq`.
  So an SE-native proof needs `NormalEqSE`/`ParRedSE`/`church_rosserSE`, i.e. the whole confluence
  layer. **P1's "not provable by transport" upheld: there is no relation-generic version.**
- M5 read `Theory/Typing/NoConfRepair.lean:127-135` — `notStructInhab_of_isType`'s proof is
  **exactly two steps**: `VEnv.WF.uniq'` then `VEnv.const_sort_inv_of_wf`. **P2 CONFIRMED at the
  proof text**, and sharper than the prior: step 2 is fact (A), which `ConstSpine.lean` proves "by
  the same route" as fact (D) = `constApp_inv`. So the further gap is a *sibling* of
  `ConstAppInvSISE`, not downstream of it — both wait on SE-Church–Rosser.
- M6 grep: **`VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs` already exists**
  (`Theory/Typing/ConfluenceRebuildPrice.lean:302`), collapsing 14→13 at defeq-free environments,
  with `isDefEqSE_iff_of_no_defeqs` (336). **Falsifies nothing in the priors but redirects the
  plan**: my collapse should generalise its side condition from "no defeqs" to "no eta-eligible
  structure", which is strictly weaker and is what an `↔` reduction of (a) needs.
- M7 grep: **gap (i) of `NoConfRepair.lean` §6 is CLOSED** — `VEnv.WF.isStructureG_ruleFreeHead`
  exists (`EtaGuardLand.lean:110`), so the `hrf` premise of `notStructInhab_of_isType` is now
  derivable from `VEnv.WF` and I need not carry it. (Prior did not anticipate this; it makes the
  conditional transport in (b) premise-free apart from the two genuinely SE-level statements.)
- M8 read `Theory/Typing/ConfluenceRebuildPrice.lean` outline. Two findings that reshape (a):
  (i) `VEnv.NormalEqSE` (371) and `VEnv.ParRedSE` (417) already exist — the confluence layer IS
  erected over the 14-ctor relation, with **two** new `NormalEqSE` structure-eta rules and **one**
  new `ParRedSE` rule; but there is **no `church_rosserSE`**, and worse:
  (ii) `Lean4Lean.descendSE_uniq_sortUniq_not_all` (604) and
  `Lean4Lean.not_parRedStatementSE_of_propMajor` (628) say the descent statement and the
  `ParRedStatement` shape stay **refuted** when re-erected over `IsDefEqSE`. So an SE-native
  `constApp_inv` cannot be had by re-erecting `ParRedStatement`; the SE side inherits the 13-ctor
  side's own open/refuted confluence obligations on top of the new constructor.
  **Consequence for P1: proving `ConstAppInvSISE` outright this round is out of reach; the
  deliverable is the `↔` reduction the brief's option (a) allows.**
- M9 note (duplication worth recording): `VEnv.IsDefEqUSE` (`ConstAppInvSIProof.lean:158`) and
  `VEnv.IsDefEqSEU` (`ConfluenceRebuildPrice.lean:294`) are the *same definition* under two names,
  in two files, both reachable. I use `IsDefEqUSE` (the one `ConstAppInvSISE` is stated with) and
  flag the other. Not mine to delete.
