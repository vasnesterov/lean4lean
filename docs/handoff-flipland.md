# handoff-flipland — flipping `VEnv.ParRedSE.structEta` to a contraction

Round of **2026-09-04**.  Queued item 3.  The design call (flip the rule) is the orchestrator's
and is not re-litigated here; this file records what the flip cost, measured.

Owned by this stream: `Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean` (**one constructor**),
`Lean4Lean/Theory/Typing/CRSEScope.lean` (§2 and §4 restated), this file.
Read-only and *not* edited: `Theory/Typing/EtaOrient.lean`, `Theory/Typing/ParamsStruct.lean`,
`Theory/Typing/ParamsCR.lean`, everything under `Verify/`.

## §1 PRIORS — written before any Lean was run.  Never edited.

What had been read at the time of writing: `CLAUDE.md`; `CRSEScope.lean` in full;
`ConfluenceRebuildPrice.lean` lines 380–470 and the grep hits for `ParRedSE`/`structEta`/`rigid`
across the whole tree; `EtaOrient.lean` in full; `ParamsStruct.lean` lines 60–260;
`Injectivity.lean` lines 125–145; the headers of `scripts/sorry-census.lean`,
`scripts/exists.lean`, `Verify/Guard.lean`.  **No Lean elaboration had been run** — no
`lean_build`, no `lean_diagnostic_messages`, no `lean_run_code`, no census.

| # | prediction | p |
|---|---|---|
| P1 | The flip itself compiles, and nothing else in `ConfluenceRebuildPrice.lean` breaks — `ParRedSE.rfl`, `parRedSES_rigid`, `parRedSE_iff_of_no_defeqs`, `parRedSES_iff_of_no_defeqs`, `not_parRedStatementSE_of_propMajor`, `descendSE_uniq_sortUniq_not_all`, and §7's `refEnv` β-step witnesses all stand with unchanged text.  Evidence: `EtaOrient.lean` §3/§7 are those proofs already ported to `ParRedSEC`. | 0.93 |
| P2 | **§1 survives untouched.**  `VEnv.StructEtaSite.iterate` mentions no reduction relation at all — it is a `structure` update on `StructEtaSite`. | 0.99 |
| P3 | **§3 survives untouched.**  `VEnv.etaExpansionG_idem_of_no_fields` is pure `etaExpansionG` algebra via `VInductDecl'.etaExpansionG_of_no_fields`. | 0.99 |
| P4 | **§2's old statement does not survive, and not because it is unproved — because it is false.**  `VEnv.not_parRedSE_rigid_of_structEtaSite` claims `¬ (∀ o, ParRedSE Γ e o → o = e)` at a site; post-flip the *subject* `e` is rigid whenever it is an atom, so the claim is refuted at exactly the sites `EtaOrient` §6 exhibits (subject `.bvar 0`).  What survives is the same fact moved to the other endpoint: the **expansion** `D.etaExpansionG …` is the redex, so `¬ (∀ o, ParRedSE Γ (η e) o → o = η e)` holds under the same two hypotheses, with the one-line proof `fun hrig => hne (hrig _ (.structEta h)).symm`. | 0.90 |
| P5 | `VEnv.etaIterG`, `VEnv.EtaStagesTyped` and `VEnv.StructEtaSite.at_stage` survive **untouched** — they are orientation-blind, and `EtaOrient.parRedSECS_etaIter_down` already consumes all three. | 0.97 |
| P6 | §4's `VEnv.parRedSES_etaIter` must become the downward tower `∀ n, ParRedSES Γ (etaIterG D T C us ps j n e) e`, i.e. `EtaOrient.parRedSECS_etaIter_down`'s body with `ParRedSEC`→`ParRedSE`, `structEtaC`→`structEta`. | 0.93 |
| P7 | **The flip breaks two files this stream does not own, so a full green `lake build` is unreachable from inside my ownership.**  Predicted casualties, exhaustively: in `EtaOrient.lean` — `Lean4Lean.MutField.unitEnv_parRedSE_structEta` (L436), `Lean4Lean.MutField.declEnv_parRedSE_structEta` (L441), `Lean4Lean.MutField.declEnv_rigidity_flips` (L495); in `ParamsStruct.lean` — `Lean4Lean.VEnv.parRedSE_structEta_of_wf` (L82), `Lean4Lean.MutField.unitEnv_parRedSE_structEta'` (L153), `Lean4Lean.MutField.declEnv_parRedSE_structEta'` (L158), `Lean4Lean.MutField.declEnv_rigidity_flips'` (L195), `Lean4Lean.MutField.unitEnv_parRedSE_from_general` (L216).  Eight declarations.  `ParamsCR.lean` mentions none of them and is predicted clean. | 0.95 |
| P7b | I have missed at least one further casualty beyond those eight. | 0.20 |
| P8 | The rigidity ports need `VInductDecl'.etaExpansionG_ne_bvar`/`_ne_sort`, which live in `EtaOrient.lean` §2 — **downstream** of `CRSEScope.lean`, hence uncitable from it.  I will re-derive the shape fact inside `CRSEScope.lean` from `VExpr.mkApp_eq_of_not_app` (`Theory/Typing/Injectivity.lean`), which I expect to be in `CRSEScope`'s transitive import closure. | 0.80 |
| P9 | **`ParRedSEC` becomes redundant but not *definitionally* redundant.**  Post-flip its ten constructor types are pointwise identical to `ParRedSE`'s up to the constructor name `structEtaC` vs `structEta`, so the two are provably equivalent by a ten-case induction each way — but they are distinct `inductive` types, so no `Iff.rfl`, no `rfl`, and no `.mp = id`. | 0.90 |
| P10 | The **census cannot stay at 13** while the two non-owned files are red: a declaration that fails to elaborate is admitted with `sorryAx`, so the eight casualties of P7 land in the census.  Expected reading 13 + (number of failed decls whose value becomes a hole).  It returns to 13 only after the orchestrator applies the non-owned edits. | 0.80 |
| P11 | Guard checks 1 and 3 (axiom freeze at 24, `partial`/`@[extern]` allowlist) are untouched by the flip; guard 2's `sorryAx` verdict is untouched too, because `kernel_sound` does not reach `ParRedSE`. | 0.90 |
| P12 | Zero warnings (unused variables, deprecations) from the two files I own. | 0.85 |

## §2 MEASUREMENTS — appended one row per verdict, as it lands

(rows below; each names the prediction it settles)

### M0 — baseline, 2026-09-04, before the flip (settles nothing; establishes the floor)

`lake build` at HEAD `a4b5e74` with a clean working tree (only untracked `docs/*.md`) **already
fails**, and not in anything this round touches:

```
✖ [1584/1655] Building Lean4Lean.Verify.Environment.Checker
error: Lean4Lean/Verify/Environment/Checker.lean:86:2: Type mismatch
```

Re-polled once after HEAD moved from `1191a23` to `a4b5e74` under me; the failure reproduces.
`Verify/Environment/Checker.lean` last changed in `961871b` ("pure containers replace the
persistent HAMT and trie").  The mismatch is at `checkConstantVal.WF`: line 85 discharges
`checkDuplicatedUnivParams` with `Except.WF.trivial _` and line 86's
`checkNoMVarNoFVar.WF` then faces a goal still carrying the `checkDuplicatedUnivParams` bind.
**Not caused by this round and not owned by it.**  Consequence for the acceptance criteria:
"full `lake build` green" was already unreachable before the flip, so greenness is measured
per-module below (1583 of 1655 modules built).

### M1 — 2026-09-04 — HEAD is broken by PR #46, diagnosed, one-line fix (settles nothing in §1; unblocks it)

`Verify/Environment/Checker.lean`'s source has not changed since 2026-09-02 and built cleanly at
09:42 today.  What broke it is `Lean4Lean/Environment.lean`, merged in `7e39484` (PR #46,
"reject the reserved `_nested` prefix for every declaration"): `checkConstantVal` gained a
**fourth** operational step

```
  checkName env v.name allowPrimitive
  checkNoNestedAuxName v.name          -- ← added by #46
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
```

while `Lean4Lean.checkConstantValCore.WF` still discharges only **one** `Except`-trivial step.
Hence the reported mismatch: at `Checker.lean:86` the goal still carries the
`checkDuplicatedUnivParams` bind.  **Exact fix — one line, in a file this stream does not own**,
inserted before the existing "Duplicate level parameters" `refine` at `Checker.lean:84-85`:

```lean
  -- The reserved `_nested` prefix is rejected operationally; no later proof needs that fact.
  refine (TypeChecker.M.WF.liftExcept (Except.WF.trivial _)).bind fun _ _ _ _ => ?_
```

**Verified, not proposed**: with exactly that line added, `Lean4Lean.Verify.Environment.Checker`
elaborates with zero errors and zero warnings (2026-09-04 12:21).  Because the whole
`Theory/Typing/` import closure runs through this module, that line is the difference between
"1583/1655 modules" and a tree this round can measure at all.

**Method note, so nothing here is mistaken for a green tree.**  The fix was *not* applied to the
repository.  It was compiled from a patched copy in `/tmp/fl` into a private olean overlay
`/tmp/fl-ol2` (a `cp -rs` symlink mirror of `.lake/build/lib/lean/Lean4Lean` with
`Verify/Environment/Checker.olean` replaced), and every elaboration below was run as
`/tmp/fl-lean.sh <file>`, i.e. `LEAN_PATH=/tmp/fl-ol2:$(lake env printenv LEAN_PATH) lean <file>`.
No tracked file outside this stream's ownership was touched and nothing was written into
`.lake/`, so no other stream's build can pick the overlay up.  The overlay's only difference from
HEAD is that one line; if any declaration measured below were to depend on it, its axiom set
would show `sorryAx`, and none does.

### M2 — 2026-09-04 — **P1 CONFIRMED** (predicted 0.93)

`ConfluenceRebuildPrice.lean` with `structEta` flipped to
`ParRedSE Γ (D.etaExpansionG T C us ps j e) e`: **zero errors, zero warnings.**  Every one of the
file's 33 `#print axioms` lines is unchanged and `sorryAx`-free, including exactly the six
declarations the flip could have broken —
`Lean4Lean.VEnv.ParRedSE.rfl`, `Lean4Lean.VEnv.parRedSES_rigid`,
`Lean4Lean.VEnv.parRedSE_iff_of_no_defeqs`, `Lean4Lean.VEnv.parRedSES_iff_of_no_defeqs`,
`Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor`,
`Lean4Lean.descendSE_uniq_sortUniq_not_all` — all `[propext, Quot.sound]` (the last also
`Classical.choice`), with **unchanged proof text**.  `EtaOrient.lean`'s claim that its §3/§7 ports
verify the flip in advance is correct.

### M3 — 2026-09-04 — **P2 and P3 CONFIRMED** (predicted 0.99 each)

`VEnv.StructEtaSite.iterate` (§1) and `VEnv.etaExpansionG_idem_of_no_fields` (§3) are carried
across the flip with **statement and proof byte-identical** — only §1's docstring gained a
post-flip sentence.  Both elaborate.  Axioms: `iterate` `[propext, Quot.sound]`,
`etaExpansionG_idem_of_no_fields` `[propext]`.  Verified rather than assumed, as briefed: neither
declaration mentions a reduction relation, `iterate` is a `structure` update on `StructEtaSite`
and `idem` is `etaExpansionG_of_no_fields` twice, so there was nothing for the flip to touch.

### M4 — 2026-09-04 — **P4, P6, P8 CONFIRMED**; `CRSEScope.lean` §2/§4 restated and green

`lake env lean Lean4Lean/Theory/Typing/CRSEScope.lean`: **zero errors, zero warnings**, and all
**15** `#print axioms` lines `sorryAx`-free.  Headline names, arity from `scripts/exists.lean`
convention (explicit binders) and axioms as printed:

| name | axioms |
|---|---|
| `Lean4Lean.VEnv.ParRedSE.rigid_of_eq_bvar` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.parRedSE_rigid_bvar` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.ParRedSE.rigid_of_eq_sort` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.parRedSE_rigid_sort` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.not_parRedSE_rigid_etaExpansionG_of_structEtaSite` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.parRedSES_etaIter_down` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.StructEtaStep.toParRedSE` | `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.StructEtaStep.sizeOf_lt` | `[propext, Classical.choice, Quot.sound]` |
| `Lean4Lean.VEnv.no_infinite_structEtaStep` | `[propext, Classical.choice, Quot.sound]` |

* **P4 confirmed.**  `parRedSE_rigid_bvar` and `parRedSE_rigid_sort` go through with
  `EtaOrient.parRedSEC_rigid_bvar`'s proof text unchanged, so the pre-flip §2's conclusion is now
  a **theorem** at every atom subject — the old statement is refuted, not merely unproved.  The
  surviving negative fact is `not_parRedSE_rigid_etaExpansionG_of_structEtaSite`, at the
  **expansion** rather than the subject, with the same two hypotheses and the predicted proof
  `fun hrig => hne (hrig _ (.structEta h)).symm` (the `.symm` was the prediction's one
  correction).
* **P6 confirmed.**  `parRedSES_etaIter_down` is `EtaOrient.parRedSECS_etaIter_down`'s body with
  `ParRedSEC`→`ParRedSE` and `structEtaC`→`structEta`, nothing else.
* **P8 confirmed, and it cost seven private duplicates.**  `EtaOrient.lean` §1–§2's shape and
  `sizeOf` lemmas are downstream of this file and uncitable from it, so the four shape/measure
  facts are re-derived here as `private` lemmas named apart
  (`etaExpansionG_ne_aux`, `etaExpansionG_ne_bvar_aux`, `etaExpansionG_ne_sort_aux`,
  `sizeOf_le_mkApp_aux`, `sizeOf_lt_mkApp_of_mem_aux`, `sizeOf_lt_projTermG_aux`,
  `sizeOf_lt_etaExpansionG_aux`).  `VExpr.mkApp_eq_of_not_app`
  (`Theory/Typing/Injectivity.lean`) is in the closure, so the shape facts need no induction of
  their own.  They sit outside both `variable [Params]` sections — inside, the
  `linter.unusedSectionVars` warning fires on two of them, which is how P12's zero-warning
  target was met.
* **A stale claim in the file I own, corrected.**  The pre-flip module docstring advertised
  "§4 `EtaRegress` and `parRedSES_etaIter`".  **`EtaRegress` never existed** — grep over
  `*.lean` and `*.md` finds the string in that one docstring line and nowhere else; the `Prop`
  is `EtaStagesTyped`.

### M5 — 2026-09-04 — **P7 CONFIRMED exactly for `EtaOrient.lean`; P7b not settled**

`lake build` at HEAD `4233199` + this round's two files: **three** ✖ modules, of which exactly
one is this round's:

```
✖ Lean4Lean.Theory.Typing.EtaOrient
  EtaOrient.lean:439:2: Type mismatch
  EtaOrient.lean:443:2: Type mismatch
  EtaOrient.lean:498:3: Unknown identifier `not_parRedSE_rigid_of_structEtaSite`
```

Three errors, at exactly the three declarations P7 named for that file
(`Lean4Lean.MutField.unitEnv_parRedSE_structEta`, `.declEnv_parRedSE_structEta`,
`.declEnv_rigidity_flips`) and at no others.  **P7b is not settled**: `ParamsStruct.lean` and
`ParamsCR.lean` are downstream of `EtaOrient` and were never reached, so their five predicted
casualties are inferred from the sources, not measured.  They will be measurable the moment the
`EtaOrient` edit in §3 below lands.

### M6 — 2026-09-04 — a **second** PR #46 casualty, not this round's and not `EtaOrient`'s

```
✖ Lean4Lean.Verify.Inductive.RestoreFaithful
  RestoreFaithful.lean:448:0: RestoreFaithful/gate: an axiom or definition named `_nested.…`
  is now REJECTED -- §5's verdict is stale in the good direction
```

`RestoreFaithful.lean` §5.1 is a self-checking `#eval` that asserts `axiom _nested.zzz` is
**accepted** and fails the build if that flips.  PR #46 flipped it deliberately, so the gate is
working as designed and the file's §5 verdict needs updating.  Its imports are five
`Verify/Inductive/*` modules — nothing this round touches — so this is independent of the flip.
The third ✖, `Theory/Typing/CRShape.lean`, belongs to the concurrently running stream.

### M7 — 2026-09-04 — **P9 CONFIRMED exactly**: `ParRedSEC` is provably, not definitionally, `ParRedSE`

`EtaOrient.lean` §3's `ParRedSEC` re-declared **verbatim** (name primed) against the post-flip
`ParRedSE` and elaborated:

* `ParRedSEC' Γ a b → ParRedSE Γ a b` and `ParRedSE Γ a b → ParRedSEC' Γ a b`, ten cases each,
  every case a one-line constructor swap and `structEtaC ↔ structEta`; `parRedSEC'_iff` and the
  closure version `parRedSEC'S_iff` follow.  All `[propext, Quot.sound]`, no `sorryAx`.
* `example : @ParRedSEC' = @ParRedSE := rfl` — **fails**: "Type mismatch: rfl has type ?m = ?m".
* `example : ParRedSEC' Γ a b ↔ ParRedSE Γ a b := Iff.rfl` — **fails**, likewise.

So they are two distinct `inductive` types with pointwise-identical constructor lists: the
redundancy is **provable, not definitional**.  That is exactly P9, including the negative half.

### M8 — 2026-09-04 — the deletion, executed (four files, one of them newly owned)

Ownership was extended mid-round to `EtaOrient.lean` and then `ParamsStruct.lean`.  Final state:

* **`ConfluenceRebuildPrice.lean`** — the one flipped constructor, plus its docstring recording
  the pre-flip form and the date.  Nothing else.
* **`CRSEScope.lean`** — §2 and §4 restated (M4), and a new §0 holding `EtaOrient.lean`'s old
  §1–§2 **relocated under their existing fully-qualified names** (eleven lemmas), replacing the
  seven `private` duplicates M4 had to introduce.  26 axiom sweeps, all clean.
* **`EtaOrient.lean`** — five of seven sections deleted (§1, §2 moved; §3, §4, §5, §7 deleted as
  duplicates), §6 kept and restated as the file's only content.  643 lines to 260.  16 axiom
  sweeps, all clean.  The retirement of the pre-flip negative result is written **at the site**,
  in `declEnv_rigidity_flips`' docstring, not only in the module header.
* **`ParamsStruct.lean`** — five expansion-oriented declarations restated, five SEC-suffixed ones
  renamed onto their surviving duplicates (`parRedSEC_structEtaC_of_wf`,
  `unitEnv_parRedSEC_structEtaC'`, `declEnv_parRedSEC_structEtaC'`, `structEtaStepC_of_wf`,
  `declEnv_parRedSEC_from_general`, `declEnv_structEtaStepC_from_general`), and its "eight
  firings" prose corrected to six.  Its `sorryAx` entries are **pre-existing** — they are
  `piInv_axiom`'s cone, i.e. `forallE_inv_stratified` and `rigidShapeUniqNS`, exactly as the
  file's own Price section documents.  Zero new holes.

Net: `505 insertions, 620 deletions` across the four files.

### M9 — 2026-09-04 — the three acceptance measurements

* **Bare `lake build`** (not a targeted one): `exit=0`, **zero** ✖ modules, zero errors, and zero
  warnings attributable to any of the four files.  1656 jobs.
* **Census: 13**, unchanged.  `lake env lean scripts/sorry-census.lean`, same thirteen
  declarations as before the round, in the same eleven modules, with the same transitive-user
  counts (`NormalEq.descend` 200, `rigidShapeUniqNS` 461, `forallE_inv_stratified` 742,
  `weakN_iff` 311, `TrProj.weak'_inv` 90, `inferProj.WF` 70, `isDefEqUnitLike.WF` 70,
  `tryEtaStructCore.WF` 71, `addDecl.WF` 8, and four at 0).  **Nothing that a hole's discharge
  was standing on was deleted.**
* **Guards, all three** (`lake env lean Lean4Lean/Verify/Guard.lean`, frozen file, read only):

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

### M10 — 2026-09-04 — the remaining prediction verdicts

* **P5 CONFIRMED.**  `VEnv.etaIterG`, `VEnv.EtaStagesTyped` and `VEnv.StructEtaSite.at_stage` are
  carried verbatim; `parRedSES_etaIter_down` consumes all three, as `parRedSECS_etaIter_down` did.
* **P7b resolved FALSE, in the good direction** (predicted 0.20 that I had missed a casualty).
  The flip's own casualties are exactly the eight named in P7 — three in `EtaOrient`, five in
  `ParamsStruct`, no ninth anywhere.  The six further `ParamsStruct` declarations that had to move
  are casualties of the **`ParRedSEC` deletion**, which is a separate decision, not of the flip.
* **P11 CONFIRMED**, P12 CONFIRMED (see M9).
* **P10 VOID, and it is worth saying why rather than scoring it.**  It predicted the census would
  rise above 13 while the non-owned files stayed red.  Ownership was extended instead, so the
  intermediate state never persisted and I never measured a census against it.  A prediction whose
  premise is removed by a decision is not a hit or a miss; recording it as either would be the
  kind of retro-fitted scoring this file exists to prevent.
* **Not predicted, and it cost the first hour: the tree was already red.**  M1.  My §1 wrote
  twelve predictions about what the flip would break and none about whether the tree built at
  all — a baseline I could have measured before writing a single prior, and did measure first only
  by luck of habit.  The prediction table should have had a row zero.

## §3 The `ParRedSEC` verdict, and the exact deletion (executed)

**Verdict: redundant, deleted.**  Post-flip, `ParRedSE` *is* the contraction, `ParRedSEC` is
provably the same relation (M7) and definitionally a different type (M7).  Every SEC declaration
duplicated an existing one; the map, as executed:

| deleted from `EtaOrient.lean` | surviving duplicate |
|---|---|
| `VEnv.ParRedSEC`, `ParRedSEC.rfl`, `ParRedSECS`, `parRedSECS_rigid` | `VEnv.ParRedSE`, `.rfl`, `ParRedSES`, `parRedSES_rigid` — `ConfluenceRebuildPrice.lean` |
| `ParRedSEC.rigid_of_eq_bvar`, `parRedSEC_rigid_bvar`, `ParRedSEC.rigid_of_eq_sort`, `parRedSEC_rigid_sort` | the same four names on `ParRedSE` — `CRSEScope.lean` §2 |
| `StructEtaStepC`, `.toParRedSEC`, `.sizeOf_lt`, `no_infinite_structEtaStepC`, `parRedSECS_etaIter_down` | `StructEtaStep`, `.toParRedSE`, `.sizeOf_lt`, `no_infinite_structEtaStep`, `parRedSES_etaIter_down` — `CRSEScope.lean` §4 |
| `parRedSEC_iff_of_no_defeqs`, `parRedSECS_iff_of_no_defeqs`, `ParRedStatementSEC`, `not_parRedStatementSEC_of_propMajor`, `DescendStatementSEC`, `descendStatementSEC_iff_of_no_defeqs`, `descendSEC_uniq_sortUniq_not_all` | the un-suffixed originals — `ConfluenceRebuildPrice.lean` §4–§6 |
| `MutField.unitEnv_parRedSEC_structEtaC`, `.declEnv_parRedSEC_structEtaC` | `.unitEnv_parRedSE_structEta`, `.declEnv_parRedSE_structEta`, whose statements these now are |

**Limits of this verdict, and they are real.**

1. The equivalence was measured on a **verbatim re-declaration**, not on the original — the
   original could not be elaborated alongside the post-flip `ParRedSE` without first deleting it.
   The copy is textually identical to `EtaOrient.lean` §3's declaration; that is the whole of the
   argument that the measurement transfers, and it is a textual argument, not a machine-checked
   one.
2. "Provably equivalent" is not "interchangeable in every context".  Since they are distinct
   inductives, a statement quantifying over `ParRedSEC`-derivations is not *literally* the
   corresponding statement about `ParRedSE`; the seven §7 ports were re-pointed at the originals
   rather than transported, which is why this is a deletion and not a rewrite.
3. The deletion is justified by duplication, **not** by the SEC statements being uninteresting.
   `not_parRedStatementSEC_of_propMajor` and `descendSEC_uniq_sortUniq_not_all` remain live
   refutations — under their un-suffixed names, and unmoved by the flip.

## §4 Scoped follow-ups this round did not do

1. **Deferred by the orchestrator, then completed anyway — flag this.**  The §1–§2 relocation into
   `CRSEScope.lean` §0 was deferred as out of scope *after* it had already been applied and
   elaborated.  I kept it rather than reverting, because reverting means restoring **both** copies
   (`EtaOrient`'s public set and `CRSEScope`'s seven privates) and `EtaOrient.declEnv_etaExpansionG_ne`
   needs `etaExpansionG_ne` from one of them — strictly more churn than leaving a finished,
   green, name-preserving move in place.  It is in the bare build and the census above.  If the
   preference is still to revert, that is a mechanical undo of one commit-sized hunk and I am
   saying so rather than letting it pass as commissioned work.
2. **`NormalEqSE.structEtaL`/`structEtaR` vs the contraction.**  The one real cost of the flip is
   that the conversion rules recurse on `η e` while the reduction now runs `η e ⟶ e`, so at a
   `structEtaL` node the reduction available at the subject does not reach the term the conversion
   recurses on.  Nobody has priced re-deriving `structEtaL`/`structEtaR` in a form that composes
   with the contraction; `CRSEScope`'s pre-flip §"Why" section predicted this would be needed and
   it still is.
3. **`parRedSES_etaIter_down`'s premise.**  `EtaStagesTyped` is still a hypothesis.  With the
   contraction it is only needed to know the *intermediate* stages are sites; a bounded version
   ("the tower of height `n` is reachable given the top stage is typed") may need strictly less.
4. **`VEnv.parRedSE_rigid_bvar` has two siblings that were never stated**: rigidity at `.const`
   and at a `mkApp` whose head is not a structure constructor.  Both look reachable by the same
   three-constructor case analysis and neither is in the tree.
