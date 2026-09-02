# Documentation audit: claims vs. the tree (2026-09-02)

*Auditor: documentation-audit stream, 2026-09-02. Deliverable: claims in this repo's `docs/`
that are **false or stale relative to the tree**, each with machine-checked evidence, plus an
explicit statement of which claims were checked and found **correct**.*

**Scope.** `docs/critical-path.md` (priority 1), `docs/soundness-ledger.md` (priority 2), and the
difficulty/status claims only in `handoff-injectivity.md`, `handoff-projections.md`,
`handoff-weakn.md`, `handoff-confluence.md`, `handoff-addinduct.md`. Mathematics in the handoffs
was **not** audited.

**Instruments used, and what each one proves.**

| Instrument | Backing | Strength |
|---|---|---|
| `~/.elan/bin/lake env lean scripts/kernel-sound-path.lean` | forward cone walk over built `.olean`s | proof: the cone and its hole set |
| `/tmp/audit/*.lean` via `lake env lean` (reverse-reachability, same algorithm as `scripts/sorry-census.lean`) | built `.olean`s | proof: hole existence + transitive user counts |
| `lean_run_code` / `#print axioms` | elaboration | proof: a named declaration exists, its statement, and whether it carries `sorryAx` |
| `lean_references` (LSP) | LSP index | proof of use-sites; `total` is exact |
| `grep` over sources | text | **floor only** — never proof of absence |

**Caveat carried forward.** `lean_local_search` and `lean_hammer_premise` are broken in this tree
(`rg` is not installed). Every "does not exist" claim below is backed by an elaboration failure
(`unknown identifier`) or an LSP result, never by grep alone.

---

## Summary table

*(appended as findings are confirmed; see evidence sections below)*

*Line numbers are as the files stood **before** this audit's edits (2026-09-02, pre-edit), since
inserting corrections shifts them. Each finding below names the section too.*

| # | File | Line(s) | Claim | Verdict |
|---|---|---|---|---|
| F1 | `critical-path.md` | 186–196 | hole table's "Current" user counts | **STALE on 4 of 7 filled rows, 2 rows never filled, `descend` never tabulated** |
| F2 | `critical-path.md` | 205 | "Five of the 14 census holes are outside the cone" | **STALE** — four of 13 |
| F3 | `critical-path.md` | 116–122, 666–672 | (B)/(C) need a `csubstList` toolkit and a `ctorApp'` head equation that "do not exist"; three obligations "open" | **FALSE** — both exist; all three closed at `params = []` and hypothesis-free at a parameterised block |
| F4 | `critical-path.md` | 67–73 | ruling 116d "execution in progress"; `Built` false at `Lean.Json` | **STALE** (landed) + **refuted as stated** (`Built` alone is not false) |
| F5 | `critical-path.md` | 41–42 | census 13, guards 1 ✓ (24) / 2 ✓ / 3 ✓ (2/2) | **CORRECT** |
| F6 | `critical-path.md` | 495–498 | `weakN_iff` has 12 direct users | **STALE by one** — 13 |
| F7 | `critical-path.md` | 549 | `addQuot.WF` proved and sorry-free | **CORRECT** |
| F8 | `critical-path.md` | 503–507 | `checkStrengthening_iff_target` has no `sorryAx` | **CORRECT** |
| F9 | `critical-path.md` | 54, 318, 412 | injectivity corner collapsed "seven" times | **STALE** — nine |
| F10 | `critical-path.md` | 541, 645 | flip price "census 14 → 17" | **STALE** base figure — 13 → 16 |
| — | `critical-path.md` | 198–201, 215–225 | `hasType_falseProp` cone 7244/0 holes; `descend` is ON the cone, hole set 9 | **CORRECT, verbatim** |
| L1 | `soundness-ledger.md` | 2791–2792 | "`IsDefEqU.sort_inv` — single `sorry`, highest value in the project" | **FALSE** — it is a proved theorem |
| L2 | `soundness-ledger.md` | 50–52 | "the other two `sorry`s … `forallE_inv` and `sort_forallE_inv`" | **FALSE** — neither is a `sorry` |
| L3 | `soundness-ledger.md` | 3 | thirteen constructors of `VEnv.IsDefEq` | **CORRECT** |
| L4 | `soundness-ledger.md` | 228 | open: a block "with recursive fields **or with parameters/indices**" | **STALE** — the parameters half is closed hole-free at `nonemptyIndDecl` |
| L5 | `soundness-ledger.md` | 3406 | "`InstDescendUp` remains open" | **CORRECT**, but silent on the `.bvar k` closure |
| P1 | `handoff-projections.md` | 1796–1803 (+338, 574, 809) | `PatWF` open / `WeakNorm` "no route in the tree" / G4 "has no statement in the tree" | **ALL THREE STALE** — `WeakNorm` is **refuted**, G4's residual is **proved**, `PatWF` follows from `VEnv.WF` modulo existing holes |
| A1 | `handoff-addinduct.md` | 313 | `TrEnv'.quot` branch "the one repair that is not yet in hand" | **FALSE** — landed; contradicted by §7.1 of the same file |
| A2 | `handoff-addinduct.md` | 339, 369 | flip costs "nine sorry-free declarations" | **STALE** — three on-path; census 13 → 16 |
| A3 | `handoff-addinduct.md` | §8 table | `addQuot.WF` still vacuous; `AddInduct` still empty | **CORRECT** |
| W1 | `handoff-weakn.md` | 440 | `weakN_iff`'s "111 transitive users" | **STALE** — 312 |
| W2 | `handoff-weakn.md` | 686 | "`forallE_inv` (a `sorry` with 105 users)" | **FALSE** — proved theorem, tainted |
| W3 | `handoff-weakn.md` | 668 | "anything a brief tells you is 'not available' about level congruence is stale" | **CORRECT** |
| C1 | `handoff-confluence.md` | 158, 312, 331, 390 | `descend` has "193 users" | **STALE** — 200 |
| C2 | `handoff-confluence.md` | 312 | all users pass through one chokepoint | **CORRECT** (2 direct users, 1 on-cone) |
| I1 | `handoff-injectivity.md` | 1751 | `weakN_iff` at "100 census users" | **STALE** — 312 (third generation of this figure in one file) |
| I2 | `handoff-injectivity.md` | 1606 | `weakN_iff` "has never been reduced to anything smaller than `PiDescend`" | **CORRECT / not refuted** |
| I3 | `handoff-injectivity.md` | 1649 | "`sort_inv` is **proved**" | **CORRECT** — and it contradicts L1 |
| I4 | `handoff-injectivity.md` | 1600 vs `critical-path.md` 223 | `descend` "machine-checked false" vs "conditionally refuted, not unfillable" | **UNRESOLVED CONFLICT**, flagged not settled |

### Shape of the result

**Twelve stale-or-false findings, ten claims confirmed correct, one unresolved conflict, one
mathematics claim declined.** Two patterns account for almost all the failures:

1. **A count measured once and never re-measured.** Every user-count figure in every audited
   document except `critical-path.md` line 41 was wrong, and `handoff-injectivity.md` carries
   three generations of the same one (169 → 100 → 312).
2. **"X does not exist" / "no route" / "not in hand", written before the thing landed, then
   copied forward.** Five instances: F3's two ingredients, A1's repair, P1's `WeakNorm` (which is
   not merely routeless — it is *refuted*, so the advice inverts) and P1's G4 statement (not only
   stated, **proved**). This is the class the brief asked for, and it is the expensive one,
   because a reader spends the round looking for something the tree already settled.

The three *dangerous* ones, if I had to rank: **P1's `WeakNorm`** (sends a stream after a proof of
a refuted statement), **F3** (sends a stream to write two lemmas that exist), and **L1** (points
the model workstream at a theorem instead of at `forallE_inv_stratified`).

### Coverage: what I checked and found CORRECT

Recorded because a failures-only list says nothing about coverage.

* `critical-path.md`: the guard/census line (F5); `hasType_falseProp`'s 7244/0-hole cone; the
  2026-09-01 `descend` correction, verbatim, including "that cone's hole set is 9"; the nine-hole
  cone itself and its exact membership; `addQuot.WF` proved and sorry-free (F7);
  `checkStrengthening_iff_target` sorry-free (F8); `addDecl.WF`'s user count (8, unchanged);
  `TrProj.uniq` recorded as closed; `descend`'s single on-cone direct user
  (`appDF_extra_of_descend`); `AddInduct` still having no constructors, which H1's row depends on.
  Also checked and found **defensible but ambiguous**: line 514's *"`patWF` (3892), `patWF_iota`,
  `patWF_quot`, `patWF_of_wf`, `piInv_axiom` are all **clean**"* — under the reading the sentence
  forces (clean *of `weakN_iff`*) it is right; read as "sorry-free" it is wrong, since
  `patWF` carries `[forallE_inv_stratified]` and `patWF_of_wf` carries that plus
  `rigidShapeUniqNS`. Cone sizes there have drifted by 7 (`constApp_inv_of_patWF` 7303→7296,
  `constApp_inv_of_wf` 7465→7458, `const_app_inv_of_wf` 7468→7461); `patWF`'s 3892 is exact.
* `soundness-ledger.md`: the thirteen `IsDefEq` constructors (L3); `InductOracleOK` really being a
  two-field structure; `InaccChainOmega.exists_inaccessibleChain_omega` existing, hence
  "`AxiomsValidated` is no longer open"; `InstDescendUp` still open as a structure (L5).
* `handoff-addinduct.md`: §8's correction table where testable (A3); `AddInduct` empty.
* `handoff-weakn.md`: W3's level-congruence note.
* `handoff-confluence.md`: the one-chokepoint claim (C2).
* `handoff-injectivity.md`: I2 (no reduction below `PiDescend` found) and I3 (`sort_inv` proved).

### Not audited, and why

* The mathematics of any handoff (out of remit).
* `docs/vacuity-ledger.md` (owned by the orchestrator this session).
* Cone-size *numbers* quoted in passing where the substantive claim did not turn on them
  (`checkStrengthening_iff_target`'s "790", `etaKDDiamondAt_of_kDiamond`'s "235",
  `sort_inv`'s "233 users").
* `scripts/kernel-sound-path.lean`'s docstring, which still says "`NormalEq.descend` (47 users)"
  and lists it among five off-cone holes — **the stale twin of the line `critical-path.md` already
  corrected at its line 215.** It is a `.lean` file and outside my edit scope; flagging it for the
  orchestrator, because it is the docstring of the instrument everyone reproduces the cone with.

## Evidence

### `docs/critical-path.md`

#### F1 — the hole table's "Current" column is stale on every row (line 186–196). **STALE**

Claim as written (line 181–184 preamble: *"Current figures at the last quiescent run are in the
right-hand column"*), then:

| Hole | doc "Current" | measured 2026-09-02 |
|---|---|---|
| `addDecl.WF` | **8** | 8 ✓ |
| `TypeChecker.Inner.inferProj.WF` | **68** | **70** |
| `TypeChecker.Inner.isDefEqUnitLike.WF` | **68** | **70** |
| `TypeChecker.Inner.tryEtaStructCore.WF` | **69** | **71** |
| `TrProj.weak'_inv` | **88** | **90** |
| `TrProj.uniq` | *closed* | closed ✓ (absent from the census) |
| `VEnv.IsDefEqU.weakN_iff` | **296** | **312** |
| `VEnv.WF.rigidShapeUniqNS` | *(cell empty)* | **460** |
| `VEnv.IsDefEqU.forallE_inv_stratified` | *(cell empty)* | **736** |
| `VEnv.NormalEq.descend` | *(not in table)* | **200** |

Evidence: `/tmp/audit/census.lean` — the reverse-reachability algorithm of
`scripts/sorry-census.lean` verbatim, run over the built `.olean`s via
`lake env lean` (`importModules #[Lean4Lean.Verify.Guard, Lean4Lean.Experimental.ConeJoin]`, so
the guard's `run_cmd` is *not* re-executed). Full output: 13 holes, with
`forallE_inv_stratified 736 / rigidShapeUniqNS 460 / weakN_iff 312 / descend 200 /
TrProj.weak'_inv 90 / inferProj.WF 70 / isDefEqUnitLike.WF 70 / tryEtaStructCore.WF 71 /
addDecl.WF 8 / kernel_sound 0 / kernel_complete 0 /
leanTT_equiconsistent_zfc_omega_inaccessibles 0 / VIndRecArg.exists_indep 0`.

Note also lines 98–100, which give `forallE_inv_stratified 534 / rigidShapeUniqNS 311 /
weakN_iff 198 / descend 145 / TrProj.weak'_inv 30` — those are explicitly dated
"as of the end of 2026-08-31" and so are history, not error; but the file's own
2026-09-02 header does not carry the current figures anywhere, so a reader gets no live number.

**Corrected in place.**

#### F2 — "Five of the 14 census holes are outside `kernel_sound_of`'s cone" (line 205). **STALE**

Actually **four of 13**. The census total is 13, the cone's hole set is 9, and the four off-cone
holes are `kernel_sound`, `kernel_complete`,
`leanTT_equiconsistent_zfc_omega_inaccessibles` and `VIndRecArg.exists_indep`.

Evidence: `lake env lean scripts/kernel-sound-path.lean`, 2026-09-02 —

```
Lean4Lean.Bridge.kernel_sound_of: cone 20431, holes (9) [TrProj.weak'_inv,
  isDefEqUnitLike.WF, tryEtaStructCore.WF, IsDefEqU.weakN_iff,
  IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS, NormalEq.descend,
  inferProj.WF, addDecl.WF]
Lean4Lean.Bridge.hasType_falseProp: cone 7244, holes (0) []
```

plus the 13-hole census above. Set difference gives exactly those four.

**Two sub-claims in the same section are CORRECT and worth recording as checked:**

* The 2026-09-01 correction at lines 215–225 — *"`descend` is ON `Bridge.kernel_sound_of`'s
  cone today, and in every branch lemma of `addDecl.WF`"*, and *"that cone's hole set is 9 and
  contains `NormalEq.descend`"* — **holds**, verbatim, in the run above. The struck-through
  older verdict is correctly struck.
* Line 198–201: *"`Bridge.hasType_falseProp` … has a cone of 7244 declarations and **zero**
  holes"* — **exactly right**, cone 7244, holes 0.

Note for the orchestrator, outside my edit scope: `scripts/kernel-sound-path.lean`'s own
docstring still says "`NormalEq.descend` (47 users)" and lists it among the five off-cone holes.
That docstring is the stale twin of the line this document already corrected. I cannot edit
`.lean` files.

**Corrected in place.**

#### F3 — obligations (B) and (C) of `VEnv.addInductR_ordered'`: two named "does not exist" ingredients now exist, and both obligations are closed at two witnesses (lines 116–122, 666–672). **FALSE / STALE — highest-value finding**

Claims as written:

* line 116–119: *"**(C)** in general — the head-by-head equation over
  `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`. Strictly harder than (A)'s: `csubst`'s
  domain holds the companion's *constructor* and *recursor* names, outside `D.blockNames`, so no
  `NoBlock` clause of `VIndCtor.WF` covers them, **and the `csubstList` lookup lemmas do not
  exist**."*
* line 120–122: *"**(B)** — a strict *sub-problem* of (C) … **The one ingredient both need is a
  `ctorApp' → ctorAppR` head equation mirroring `substC_tyApp_eq_tyAppR_map`.**"*
* line 666–672: *"The nested flip … is blocked on four ordinary open obligations … **Three** of
  them are open theorems: the hypotheses `hctors` / `hrecs` / `hrules` of
  `VEnv.addInductR_ordered'`."*

What is actually true:

1. **The `csubstList` lookup toolkit exists.** `Lean4Lean/Theory/Inductive/NestedRules.lean`
   §7.1 is headed *"a `lookup` toolkit for `csubstList`"* and contains
   `VIndRestore.csubstList_eq` (`:131`), `mem_csubstList` (`:137`) and the three
   `lookup`-at-a-companion-member lemmas (`:176`, `:183`, `:189`).
   `#print axioms Lean4Lean.VIndRestore.csubstList_eq` → `[propext, Quot.sound]`. No `sorryAx`.
2. **The `ctorApp' → ctorAppR` head equation exists,** under exactly the name and description the
   document says is missing: `NestedRules.lean:438-441`,
   `/-- **The `ctorApp'` head equation** — the ingredient (B) and (C) share. -/`
   `theorem VIndRestore.substC_ctorApp'_eq_ctorAppR`.
   `#print axioms` → `[propext, Quot.sound]`.
3. **(B) and (C) are closed in general for `D.params = []`**: `VEnv.recConstsR_wf_of_np_zero`
   (`NestedRules.lean:869`, docstring *"Obligation (B) of `VEnv.addInductR_ordered'`, closed for a
   parameterless nested block"*) and `VEnv.iotaRulesRS_wf_of_np_zero` (`:887`, same for (C)). Both
   `[propext, Quot.sound]`.
4. **All three obligations are hypothesis-free theorems at a *parameterised* nested block.**
   `InductiveDeclExamples.ntreeAux_obligationB` and `ntreeAux_obligationC` are closed existential
   statements with **no premises** (statements printed by `#check` — see below), and
   `ntreeAux_addInductR_ordered : ∃ env₁ env', VEnv.empty.addInduct' listDecl = some env₁ ∧
   env₁.addInductR ntreeAux ntreeK ntreeRestore = some env' ∧ env'.Ordered` — i.e.
   `addInductR_ordered'` applied with all three obligations supplied. All three print
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
   `ntreeAux` really is parameterised: `example : ntreeAux.np = 1 := by decide` elaborates, as
   does `example : ntreeAux.params ≠ [] := by decide`; `nfnAux.params = []` by `decide`, so
   `nfnAux_addInductR_ordered` is the `np = 0` witness and `ntreeAux` is the new one.

So of the three obligations the document calls "open theorems", the honest current statement is:
**all three hold in general at `D.params = []`, and all three hold with no hypotheses at a
parameterised nested block; what is open is the general parameterful case.** The two ingredients
the document names as unavailable are both in the tree, in a file (`NestedRules.lean`) that did
not exist when the document was last written.

Provenance: landed in `6a570b1` (09-02 14:10) and `f444bac` (09-02 14:59);
`docs/critical-path.md` was last committed in `55240ca` (09-02 05:11), i.e. **20 commits ago**.

**Corrected in place.**

#### F4 — "Execution in progress" for ruling 116d, and "`Built`, `AddNestedB` and `AddNested` are false at `Lean.Json`" (lines 67–73). **STALE, and the refutation was narrower than stated**

Claim as written (lines 67–73): *"`Built`, `AddNestedB` and `AddNested` are **false at
`Lean.Json`** … **Ruling in force (row 116d): reparameterise the restoration to target the
*stored* type and drop the canonicity predicate** … **Execution in progress.**"*

Two things are now wrong with this.

1. **Execution is complete, not in progress.** `Theory/Inductive/MemberRedex.lean`'s header
   §"The repair, and its price — **LANDED**" records the finished state, and the tree agrees:
   `VEnv.AddNestedB` (`Theory/Inductive/NestedBuild.lean:806`) is
   `D.WF env ∧ D.Built R K env occ ∧ env.addInductR D K R = some env'` — no canonicity conjunct —
   and its docstring says *"`D.CanonicalOwn K` was the second conjunct and **is gone too**
   (ruling 116d): `AddNested` no longer has a canonicity conjunct for it to discharge, and
   `VInductDecl'.Built.canonical` … is used by nothing in `Theory/` any more."*
   `VIndCtor.Canonical` survives only as a side condition on user-written members
   (`VInductDecl'.CanonicalOwn`, `NestedBuild.lean:786`).
   Commits: `e2c56d2` (09-02 01:49) "ruling 116d executed", `823a026` (05:12) "ruling 116d
   landed", `b59f569` (08:28) "ruling 122e executed — D.Canonical gone from the run spec".
   `docs/critical-path.md` was last committed at `55240ca`, 09-02 **05:11** — one minute before
   `823a026`.
2. **"`Built` … false at `Lean.Json`" is refuted as stated.**
   `Theory/Inductive/MemberRedex.lean:12` — *"**`VInductDecl'.Built` alone is NOT false**, at
   `Lean.Json` or anywhere else"*, with the mechanism (a caller may take `D.types[j]` to *be* the
   built member, so `member` holds by `rfl`) and the witness `mr_member_built`
   (`#print axioms` → `[propext, Quot.sound]`, no `sorryAx`). The failing object is
   `AddNestedB`'s first two conjuncts *jointly* — `Built.member` together with
   `VIndField.WF.pos`'s `none` branch — plus a second, unconditional refutation about the
   companion **recursor**'s minor-premise arity. At the repaired witness the residue of
   `VIndField.WF.pos` is one `IsDefEq.beta` (`mr_pos_beta`, `#print axioms` → `[propext]`).

**Corrected in place.**

#### F5 — the guard line (line 41–42). **CORRECT**

*"Census steady at **13** holes; guards `1 ✓ (24 axioms) / 2 ✓ (INCOMPLETE) / 3 ✓ (2/2)`."*

All four figures check out, without running the guards:

* census 13 — the census-equivalent run above, `TOTAL: 13`;
* 24 axioms — `Verify/Guard.lean:169` comment *"Check 1: the frozen axiom file declares exactly
  the 24 whitelisted axioms"*, and `1191a23` "drop the now-unused frozen axiom
  `Expr.replace_eq` (25 -> 24)" is `HEAD~`-side history consistent with it;
* 2/2 — `implGapWhitelist` (`Guard.lean:165-167`) has exactly two entries,
  `ptrEqConstantInfo.unsafe_impl_2` and `ptrEqExpr.unsafe_impl_2`;
* guard 2 INCOMPLETE — `kernel_sound` is in the census with 0 users, i.e. still a hole.

#### F6 — "`IsDefEqU.weakN_iff` has **12** direct users" (line 495–498). **STALE by one**

Thirteen, as of 2026-09-02. The document's twelve are all still direct users; the addition is
**`Lean4Lean.VEnv.typingStrengthening_of_weakN_iff`**.

Evidence: `/tmp/audit/probe4.lean` — every `Lean4Lean.*` constant whose type-or-value
`getUsedConstantsAsSet` contains the target. Same run also gives, for the record (none of these
figures appears in the document):

* `NormalEq.descend` — 2 direct users: `NormalEq.appDF_extra_of_descend`, `descendStatement_holds`.
  The document's line 218 claim *"the single direct user inside it \[the cone] is
  `NormalEq.appDF_extra_of_descend`"* is consistent: `descendStatement_holds` is off-cone.
* `IsDefEqU.forallE_inv_stratified` — 2: `IsDefEq.uniq`, `piInvStrat_axiom`.
* `WF.rigidShapeUniqNS` — 2: `IsDefEqU.forallE_inv`, `WF.rigidShapeUniq`.

**Corrected in place.**

#### F7 — "`Environment.addQuot.WF` is proved and sorry-free" (line 549). **CORRECT**

`Lean4Lean.addQuot.WF` (`Verify/Environment.lean:140`, proved by `addQuot.WF'`) —
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` plus seven whitelisted frozen
`Lean.Expr`/`Lean.Level`/`Lean.Syntax` axioms. **No `sorryAx`.** The document's accompanying
caveat (*"`addQuot.WF` is still vacuous, because its hypothesis `ves.WF env` cannot hold at an
environment carrying an `.inductInfo`"*) is also consistent with `Verify/QuotConsts.lean:718`,
which says the same thing in its own docstring.

#### F8 — "`checkStrengthening_iff_target` … no `sorryAx` at all" (line 503–507). **CORRECT**

`#print axioms Lean4Lean.VEnv.checkStrengthening_iff_target` → `[propext, Quot.sound]`. The
cone-size figure "790" was not re-measured.

#### F9 — "the injectivity corner collapsed **seven** times" (lines 54, 318, 412). **STALE**

**Nine**, as of 2026-09-02.

* **Collapse eight** — `ce58e65` (09-02 12:13), `Theory/Typing/SortInvIndep.lean`:
  `shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn` makes the sort/Π corner the sole
  remaining residual, and `sortLinkInvUC_iff_sortUniq` / `sortMidNonSortC_iff_sortUniq` make that
  residual `SortUniq`, i.e. `forallE_inv_stratified` itself.
  `#print axioms` on all three → `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
* **Collapse nine** — `8fa3e6d` (09-02 13:32): `propTypeAgreeN_and_propUniqN_of` derives both
  ∀-n targets from five hypotheses and `propUniqN_iff_appCase_all` proves the fifth hypothesis
  *is* the second conclusion, so both targets' content is one statement, ∀-n `AppUniqLvl`.
  (`5238f67`, 09-02 15:12, then shows that statement is **false** at `Ordered`.)

`midShapeless_vacuous`'s explanation (line 314–319) is unaffected — it still explains why — but
the tally is two short. The related line 412's *"the injectivity corner collapsed **seven** times"*
and line 54's *"**seven** localisation attempts collapsed into their own targets"* both need the
same bump.

**Corrected in place.**

#### F10 — "the price recorded above (census 14 → 17) is still the price" (lines 541, 645). **STALE**

The census is **13**, not 14, so the flip's price in census terms is 13 → 16. The *content* of the
claim (three declarations with no replacement in hand — `reduceProjCore_none`,
`reduceProjCore.WF`, `inductiveReduceRec_eq_none`) was not re-audited; only the base figure is
wrong. Same base figure appears at lines 93, 152, 159, 205, 660 — all in dated-2026-08-31
sections, and the file's own line 41 gives 13.

**Corrected in place at lines 541 and 645** (the live claims); the dated sections are left as
history per this document's convention.

---

### `docs/soundness-ledger.md`

#### L1 — "`IsDefEqU.sort_inv` … **Single `sorry`, highest value in the project**" (line 2791–2792). **FALSE**

`IsDefEqU.sort_inv` is a **proved theorem**, not a `sorry`.
`Theory/Typing/Injectivity.lean:565` declares it; the section heading at `:168` reads
*"## `IsDefEqU.sort_inv` is now proved"*, and `:170` says *"`VEnv.IsDefEqU.sort_inv` used to be
the first theorem of this file, `sorry`-backed in its statement"*. `:529` (`SortUniq`'s section)
repeats *"Formerly `Theory/Typing/Injectivity.lean`'s first theorem, where it was `sorry`-backed"*.

Evidence: `#print axioms Lean4Lean.VEnv.IsDefEqU.sort_inv` →
`[propext, sorryAx, Classical.choice, Quot.sound]` — it is `sorryAx`-**tainted** but is not
itself a hole, and the census (13 holes, listed above) does **not** contain it. The taint comes
from `IsDefEqU.forallE_inv_stratified`, which the file's own §"`SortUniq` and
`IsDefEqU.sort_inv`, from `forallE_inv_stratified` alone" states as the route
(`forallE_inv_stratified ⟹ uniqAux ⟹ SortUniq ⟹ sort_inv`, `:280`).

Consequence for the ranking this item is part of: the model's top item is not a separate
`sorry`, it is **`forallE_inv_stratified`** — the same 736-user hole the injectivity corner is
about, which is a sharper statement of the same priority, not a weaker one.

**Corrected in place.**

#### L2 — "The other two `sorry`s in `Theory/Typing/Injectivity.lean` — `IsDefEqU.forallE_inv` and `IsDefEqU.sort_forallE_inv`" (line 50–52). **FALSE**

Neither is a `sorry`. Both are proved theorems, `sorryAx`-tainted through
`WF.rigidShapeUniqNS` / `forallE_inv_stratified`:

* `#print axioms Lean4Lean.VEnv.IsDefEqU.forallE_inv` → `[propext, sorryAx, Classical.choice, Quot.sound]`;
* `#print axioms Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv` → the same;
* the census puts exactly **two** holes in `Theory.Typing.Injectivity`:
  `VEnv.WF.rigidShapeUniqNS` and `VEnv.IsDefEqU.forallE_inv_stratified`
  (source sites `Injectivity.lean:1046` and `:261-268`).

The *substance* of the surrounding paragraph — that no injectivity fact beyond `sort_inv`
appears in any soundness case — was **not** disturbed; only the names of the file's holes.

**Corrected in place.**

#### L3 — "the thirteen constructors of `VEnv.IsDefEq`" (line 3). **CORRECT**

`Theory/Typing/Basic.lean:18` declares `inductive IsDefEq`, and it has exactly 13 constructors.

#### L4 — line 228's `SetModel.CoherentOn` row: "what is open is a block with recursive fields … **or with parameters/indices**". **STALE**

The parameters half is closed. `InductOracleOK` is now discharged, hole-free, at
`nonemptyIndDecl` — a block with **np = 1** (`example : nonemptyIndDecl.np = 1 := by decide`
elaborates) — and at `preludeEnv`:

| declaration | cone | holes |
|---|---|---|
| `SetModel.NEAudit.inductOracleOK_NE` | 8304 | **[]** |
| `SetModel.NEAudit.inductOracleOK_NE_at_preludeEnv` | 8398 | **[]** |
| `SetModel.NEAudit.nonemptyEnv_le_preludeEnv` | 1121 | **[]** |

(measured by `/tmp/audit/probe11.lean`: forward cone + `sorryAx` filter, same walker as
`scripts/hole-cone.lean`). `inductOracleOK_NE_at_preludeEnv`'s type is
`∀ … (L : PropSplit preludeEnv nv) κ ls, InductOracleOK … preludeEnv nv L κ ls (neOracle …)
(neOracle …) nonemptyIndDecl` — no `hle` premise, it is supplied by the theorem above.
Landed in `6bf3b5e` (09-02 09:54), i.e. **after** this file's last commit `38dfc6d` (08:19).

Related, and it removes the same row's implicit caveat about `PropSplit`:
`SetModel.NEAudit.nonempty_propSplit_preludeEnv : Nonempty (PropSplit preludeEnv 0)` is a
**theorem** whose hole cone is exactly `[VEnv.IsDefEqU.forallE_inv_stratified]` — so the whole
oracle layer's non-vacuity is now pinned to the same single hole as L1, not to an
unconstructed class.

Sub-claims in the same row that **check out**: `InductOracleOK` really is a *two*-field
structure (`SetModel/CnstRecursion.lean:504-507`, fields `consts` and `rules`), and
`InaccChainOmega.exists_inaccessibleChain_omega` really exists
(`Theory/SetModel/InaccChainOmega.lean:211`), so *"`AxiomsValidated` is no longer open"* is
supported.

**Corrected in place.**

#### L5 — "`InstDescendUp` remains open; the recorded *reason* is gone." (line 3406). **CORRECT, but incomplete**

Still literally true — `InstDescendUp` as a structure is open, because the `.forallE` / `.app` /
`.lam` cases need inversion (`Theory/SetModel/InstDescendBvar.lean:52-55`: *"No refutation.
`InstDescendUp` as literally stated … the `.forallE` / `.app` / `.lam` cases still need
inversion"*). What the line does not say, and a reader sequencing from it would want, is that
the `.bvar k` case is **closed at every `k`** (`InstDescendBvar.lean`, `prop_inst_bvar` /
`proof_inst_bvar`, landed `37b4958`, 09-02 13:46), and that the item had been named "the
sharpest open mathematics on the model side" for six consecutive handoff sections before being
measured as a one-line consequence of `env.WF`. I add a pointer rather than change the verdict.

---

### `docs/handoff-projections.md` — status claims only

#### P1 — §0‴.6's three "structural blockers" (lines 1796–1803, repeated at 338, 574, 809). **ALL THREE STALE; two badly**

Claim as written: *"Both lemmas need facts that are **not census holes** and therefore cannot be
consumed without adding a `sorry` (forbidden) or an axiom (forbidden): `VEnv.PatWF` … **open**.
Proved only on the δ fragment. … `VEnv.WeakNorm` … stated, **no route in the tree**. … ledger
**G4** / `RecTypeResidual` — **has no statement in the tree**."*  Conclusion drawn: *"neither
lemma could close this session regardless of effort."*

| leg | claim | actually |
|---|---|---|
| `VEnv.PatWF` | open hypothesis, not a census hole | `VEnv.patWF_of_wf` derives it from `VEnv.WF`; cone 4025, hole cone `[IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]` — **two existing census holes**, which the same paragraph calls permissible to consume |
| `VEnv.WeakNorm` | "no route in the tree" | **REFUTED.** `ConstSpine.lean:59` *"`VEnv.WeakNorm` below is **refuted**, not open"*; `WeakNormRefute.lean` `not_weakNorm` / `not_weakNorm'` at two independent `Params` instances, and `not_forall_weakNorm_of_wf` (*"No proof of `WeakNorm` from `VEnv.WF`"*). `#print axioms` on both → `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** |
| G4 / `RecTypeResidual` | "has no statement in the tree" | **Stated and PROVED.** `VEnv.RecTypeResidual` at `Verify/Typing/StructureUniq.lean:586`; `VEnv.structureUniq_of` reduces G4 to it at `:594`; `VEnv.recTypeResidual_of_wf` (`Verify/Typing/RecTypePeel.lean:189`) proves it from `VEnv.WF`, `[propext, Classical.choice, Quot.sound]`, **sorry-free**. That file's header: *"`VEnv.RecTypeResidual`, proved: ledger G4 closes"* |

Also stale in the same three summary lines: **`TrProj.uniq` is closed** (absent from the
2026-09-02 census), and `TrProj.weak'_inv` has **90** transitive users, not the "28" quoted.

The `WeakNorm` leg is the expensive one: a document telling a stream a statement has "no route"
invites it to look for one, when the tree already proves there is none and the consumer must be
restated instead.

Instrument: forward cone + `sorryAx` filter (`/tmp/audit/probe12.lean`, same walker as
`scripts/hole-cone.lean`), `#print axioms` (`/tmp/audit/probe13.lean`), and source reads.

**Corrected in place at all four sites** (canonical block at §0‴.6, dated pointers at 338, 574,
809) — this repo's own rule that "a claim repaired in N places needs a grep, not a count".

### `docs/handoff-addinduct.md` — status claims only

#### A1 — §6(3): "`addQuot.WF`'s second branch must build `TrEnv'.quot` … **This is the one repair that is not yet in hand**" (line 313). **FALSE, and contradicted by §7.1 of the same file**

`Verify/Environment.lean:140-143` is `theorem addQuot.WF … := addQuot.WF' wf`, and
`addQuot.WF'` (`Verify/QuotConsts.lean:683`) builds `TrEnv'.quot` via `trEnv_addQuot`, drawing
`QuotReady` from `checkEqType.WF_quotReady_closed` — exactly the repair this item specifies.
`#print axioms Lean4Lean.addQuot.WF` → `[propext, Classical.choice, Quot.sound]` + seven
whitelisted frozen axioms, **no `sorryAx`**. §7.1 already carries a struck-through
*"~~`addQuot.WF`'s `AddQuot` construction~~ **DONE**"*; §6(3) was never updated to match.

**Corrected in place.**

#### A2 — "**Net axiom-cone effect of the flip:** nine sorry-free declarations become `sorry`" (line 339), and §7.2's "whether to take nine `sorry`s" (line 369). **STALE — this is the figure the decision gets quoted from**

`docs/critical-path.md` §"Re-pricing the `AddInduct` flip" measured the cost **to the main
theorem** as **three** declarations with no replacement in hand (`reduceProjCore_none`,
`reduceProjCore.WF`, `inductiveReduceRec_eq_none`), the other on-cone casualties having proved
replacement arms; and the census base is 13, so the census price is **13 → 16**. The handoff has
carried "nine" since `a836863` (08-31 14:41) and is the document a stream reads when pricing the
flip.

**Corrected in place** (a re-pricing note at line 339; the "nine" is struck).

#### A3 — §8's correction table. **CHECKED, and it is accurate where I could test it**

The two entries I verified — *"`addQuot.WF` … **And the original claim was right after all**:
with the construction done, what remains is exactly `AddInduct`"* and *"the construction landed
and `addQuot.WF` is *still* vacuous, because `VEnvs.WF env` in the hypothesis needs the flip"* —
both match the tree (`Verify/QuotConsts.lean:718` says the same thing in its own docstring, and
`AddInduct` still has **no constructors**: `Verify/Environment/Basic.lean:149-151`,
`inductive AddInduct … : Prop` followed by `-- TODO`). No correction needed.

### `docs/handoff-weakn.md` — status claims only

#### W1 — "`weakN_iff`'s **111** transitive users has not been asked" (line 440). **STALE**

312. **Corrected in place.** The *substance* — that the `noUnsafe` question has not been priced
for this statement — was not tested and is left standing.

#### W2 — "`forallE_inv` (a `sorry` with 105 users)" (line 686). **FALSE**

`IsDefEqU.forallE_inv` is a proved theorem, `sorryAx`-tainted through `WF.rigidShapeUniqNS`
(`#print axioms` → `[propext, sorryAx, Classical.choice, Quot.sound]`); it is not in the census.
Same error class as ledger L2. Note the row's own verdict — *"Abandoned as tainted, not as
wrong"* — is unaffected, because the taint is real; only "a `sorry`" is wrong.

**Corrected in place.**

#### W3 — "**Anything a brief tells you is 'not available' about level congruence is stale.**" (line 668). **CORRECT, and worth promoting**

`IsDefEq.instL_r` exists (`Theory/Typing/Strong.lean`), and this is the same failure mode as P1's
`WeakNorm` leg and F3's two "missing ingredients". Three independent instances in one audit.

### `docs/handoff-confluence.md` — status claims only

#### C1 — "all **193** users" (lines 158, 312, 390) and the correction table's "**193** (census)" (line 331). **STALE**

`NormalEq.descend` has **200** transitive users. Note the *shape* of line 331 is right — it is
itself a correction of an earlier "145" — it has simply aged. **Corrected in place at all four
sites.**

#### C2 — "so all 193 users pass through one chokepoint" (line 312). **CHOKEPOINT CLAIM CHECKED, CORRECT**

`descend` has exactly **2** direct users, `NormalEq.appDF_extra_of_descend` and
`descendStatement_holds`; of those, only the first is on `Bridge.kernel_sound_of`'s cone
(`/tmp/audit/probe4.lean` plus the cone run). So the chokepoint claim holds; only the count moved.

### `docs/handoff-injectivity.md` — status claims only

#### I1 — "`weakN_iff` … at **100** census users with an empty cone" (line 1751). **STALE**

312. **Corrected in place.** Note this file already carries, at line 1503, *"§8 item 4 of this
file is stale: it prices `weakN_iff` at '169 users (census)'"* — so this is the **third**
generation of the same stale figure in one document.

#### I2 — "`weakN_iff` … has never been reduced to anything smaller than `PiDescend`" (line 1606). **CHECKED, NOT REFUTED**

The nearest candidates are not counterexamples: `checkStrengthening_iff_target`
(`[propext, Quot.sound]`) is an *equivalence*, not a reduction, and
`Theory/Typing/StrengthenInhabGate.lean`'s gate covers only part of the user set (its own
docstring says "46 of the hole's 296"). I found nothing in the tree that reduces `weakN_iff`
below `PiDescend`. Recorded as **correct** with the user figure annotated.

#### I3 — line 1649's correction row: "`sort_inv` is **proved**. Its 233 users are real but its cone is `[forallE_inv_stratified]`." **CORRECT**

`#print axioms Lean4Lean.VEnv.IsDefEqU.sort_inv` → `[propext, sorryAx, Classical.choice,
Quot.sound]`, and `Injectivity.lean:168` is headed *"`IsDefEqU.sort_inv` is now proved"*. **This
row is right and `docs/soundness-ledger.md`'s item 1 (L1 above) contradicted it** — the same fact
was recorded correctly in one document and wrongly in another, which is why L1 cost rounds. I did
not re-measure "233".

#### I4 — line 1600: "**`NormalEq.descend` is machine-checked false**" and line 1740's "The one thing in this corner that has never been tried and is now *stateable*". **NOT AUDITED**

Both are mathematics claims, outside my remit. Flagging only that line 1600's "false" and
`docs/critical-path.md` line 223's grading of `descend` as *"**conditionally** refuted, not
unfillable"* are different verdicts about the same object, in two documents I was asked to audit.
Someone should reconcile them; I have no measurement that settles it.
