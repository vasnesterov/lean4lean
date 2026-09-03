# Handoff: obligation (A)'s β-gap at `D.np > 0` (`CtorBeta`)

**Written 2026-09-03.**  Files, both mine and both new:

* `Lean4Lean/Theory/Inductive/CtorBeta.lean` — the proofs (§1–§7b below);
* `Lean4Lean/Theory/Inductive/CtorBetaScan.lean` — a structural query over the **compiled
  environment**, so the ABSENCE claims here are not grep claims.

Nothing frozen was read for editing, written, or touched.  I did **not** make the flip; per the
brief that is the orchestrator's to sequence with the user, and (A) is a reduction, not a discharge.

## 0. What is claimed, and what "hole-free" does not mean

Every `#print axioms` line below is *hole-free* and nothing more.  Non-vacuity is asserted
separately and only where §4/§7b actually check it.  Two of the thirteen census holes print clean
over an empty domain (ledger row 197), which is why the two are stated apart.

## 1. Headline

Obligation **(A)** at `D.np > 0` is now reduced twice, both hole-free, both general:

| theorem | what it reduces (A) to | axioms | arity |
| --- | --- | --- | --- |
| `VEnv.ctorConstsCR_wf_of_fieldsD` | **one typed defeq per recursive field that names a companion constant** | `[propext, Classical.choice, Quot.sound]` | 7 |
| `VEnv.ctorConstsCR_wf_of_betaD` | §8.8's β data (`hbv`/`hbody`/`hpi`/`hAs`/`hsort`), at *canonical* companion-pointing recursive fields | `[propext, Classical.choice, Quot.sound]` | 13 |

Compare `VEnv.ctorConstsCR_wf_of_np_zero'` (`Theory/Inductive/RestoreBridge.lean:595`), which is
(A) in general **only at `D.params = []`** and carries arity 20.

**The substantive claim.**  `docs/handoff-flipprice.md` §6 prices (A)'s residual as

> its telescope-defeq hypothesis: `TeleDefEq` on `C.params ++ fieldTypes` against
> `C.params ++ fieldTypesR`, plus one `IsDefEq` on the canonical result.

Of that, the following are now discharged **in general, with no bound on `D.np`**:

* the **result** conjunct — entirely (`VIndRestore.ctorResult_defeq`, §2);
* the **`C.params`** block of the telescope — `VEnv.TeleDefEq.rfl`, which carries no typing;
* every **non-recursive** field — `VIndField.typeR`'s `none` branch is `F.type` on the nose;
* every **recursive** field whose stored type names no companion — `VIndRestore.restore_noK`;
* the per-field **`OnCtx`** (§6c) and, at a canonical field, the reduction of the field defeq to the
  **head** defeq (§6).

What is left is §8.8's `hbody`/`hAs` — which §8.8's own docstring identifies as §8.7's `hargs`, the
`val` clause of `(R.csubst D K).WF`, shown to be genuinely *data* by
`VIndRestore.instAt_indep_of_tyArgs`.  **So (A) at `np > 0` bottoms out in the same datum that (B)
and (C) do.**  `docs/handoff-flipprice.md` §6's "three items, all the same shape" is right about the
shape and understates the sharing: after this file the three share one datum, not three of a kind.

## 2. Full declaration list (measured — `lake build`, my module job 1569/1571, exit 0 on it)

| declaration | axioms |
| --- | --- |
| `VIndRestore.substC_fieldTypes_defeq'` | `[propext, Quot.sound]` |
| `VIndRestore.substC_fieldTypes_defeq` | `[propext, Quot.sound]` |
| `VIndRestore.substC_fieldTypes_defeq_of_noK` | `[propext, Quot.sound]` |
| `VIndRestore.ctorResult_defeq` | `[propext, Quot.sound]` |
| **`VEnv.ctorConstsCR_wf_of_fieldsD`** | `[propext, Classical.choice, Quot.sound]` |
| `InductiveDeclExamples.ntree_fld_premise_fires` | `[propext, Quot.sound]` |
| `InductiveDeclExamples.ntree_field0_free` | `[propext]` |
| `InductiveDeclExamples.ntree_ctorConstsCR_ne_nil` | `[propext, Quot.sound]` |
| `InductiveDeclExamples.ntreeRestore_tyVal_levelWF` / `_tyArgs_closed` / `_csubstTy_tyName` / `_tyArgs_noCSubst` | `[propext, Quot.sound]` |
| **`InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_fieldsD`** | `[propext, Classical.choice, Quot.sound]` |
| `VIndRestore.field_defeq_of_canonical` | `[propext, Quot.sound]` |
| `VIndRestore.substC_tyAppR_free` | `[propext, Quot.sound]` |
| `VIndRestore.head_defeq_of_beta` | `[propext, Quot.sound]` |
| `VIndRestore.head_defeq_of_own` | `[propext, Quot.sound]` |
| `VIndRestore.ctorFieldEntry_onCtx` | `[propext, Quot.sound]` |
| `VIndRestore.ctorFieldCtx_bvars_in_scope` | `[propext, Quot.sound]` |
| **`VEnv.ctorConstsCR_wf_of_betaD`** | `[propext, Classical.choice, Quot.sound]` |
| **`InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_betaD`** | `[propext, Classical.choice, Quot.sound]` |

## 3. Hole-free vs non-vacuous, stated separately

**Hole-free**: all of the above, measured; no `sorryAx` anywhere.

**Non-vacuous**, and here is how I know — which is *not* the axiom line:

* `ntreeAux_ctorConstsCR_wf_of_fieldsD` exhibits **all seven** hypotheses of
  `ctorConstsCR_wf_of_fieldsD` holding *simultaneously* at `ntreeAux` — the `NTree`/`List` block,
  `D.np = 1`, a real nested declaration Lean's own kernel runs the nested elimination on.  So §3 is
  not empty above `np = 0`, which is the regime it claims.
* `ntreeAux_ctorConstsCR_wf_of_betaD` does the same for §7 — **including `hbeta`**, i.e. §8.8's five
  inputs, discharged at that block (`As := []`, `B = B' := Sort (u+1)`, the three typing components
  by `type_tac`).  §7 is a long conjunction and a conjunction of individually satisfiable
  hypotheses can still be jointly empty; this is that check, not an assumption.
* `ntree_fld_premise_fires` checks the **premise** of §3's `hfld` is non-empty at that block:
  `ntreeNode`'s field 1 names `_nested.List_1 ∈ ntreeK`, so §3 really does charge one defeq there.
  Without this the reduction could be "free" only because nothing satisfies its premise.
  `ntree_field0_free` checks field 0 is *not* charged (`recArg = none`).
* `ntree_ctorConstsCR_ne_nil` checks the **conclusion** is not vacuous: `ctorConstsCR` is non-empty
  at that block, so `∀ c ∈ …` is not a statement about `[]`.
* **The §T4 failure mode is checked, not assumed.**  `NestedTele.lean` §T4 records that the
  *motive*-block analogue of §7's `hbv` — `substC_motiveType_defeq` — is **vacuous exactly above
  `D.np = 0`**, because it types the spine `bvars (ni + t) D.np` in a context of length `ni`.  §7's
  `hbv` is the same shape, so `ctorFieldCtx_bvars_in_scope` proves the analogous inequality holds
  here: a constructor's parameter binders sit at the **bottom** of its field context and
  `VIndCtor.WF.params_len` says there are exactly `D.np` of them, so the spine's top index is
  exactly one below the context length.  Independently confirmed by §7b actually building `hbv`.

**Reduction, not discharge** (graded the way `docs/vacuity-ledger.md` §0 asks): both headline
theorems leave a hypothesis that *is* the open obligation. §3 leaves the per-companion-field defeq;
§7 leaves §8.8's `hbody`/`hAs`, i.e. `hargs`.  I do **not** claim (A) is closed.

**Where §7 does not reach.**  `hcan` demands the companion-pointing recursive field be stored
*canonically*.  Block-level `VIndCtor.Canonical` is machine-checked **false** for real declarations
(`Lean.Json`, `Lean.PrefixTreeNode`, `MRedex.MRWit.MJ`), so this needs saying precisely: the known
non-canonical fields are the β-redexes `ElimNestedInductive` manufactures, and those point at the
block's **own** member, so `restore_noK` makes §3 charge *nothing* for them.  At `MRedex`'s
non-canonical block the one companion-pointing field *is* canonical (`mrObj_canonical`,
`Theory/Inductive/StoredIota.lean` §5.2) — read off, not re-measured by me.  A field that both names
a companion **and** is stored non-canonically is not covered by §7 and I did not determine whether
one exists.  §3 covers it if the caller can supply its defeq directly.

## 4. Corrections to the brief and to the documents

Each of these I checked myself.

1. **`ctorConstsCR_wf_of_substC'` is not in `Theory/Inductive/RestoreBridge.lean`.**
   `docs/handoff-flipprice.md` §6's table (row 1) and the brief both give that file; the theorem is
   at **`Theory/Typing/ConstSubstNested.lean:208`**.  `RestoreBridge.lean` holds the `np = 0`
   route (`ctorConstsCR_wf_of_np_zero'`, `:595`).
2. **The `mr_pos_beta` lead is a red herring for (A), and the tree already says so.**  The brief
   flagged it as a guess; the guess is refutable.  `Theory/Inductive/StoredIota.lean` §5's
   docstring states outright: *"`mr_pos_beta` is not the missing producer, and no join to it is
   required"* — because at a redex field the restoration is the **identity** (`restore_noK`), so
   `TeleDefEq.rfl` applies and no defeq is asked for.  Where a real obligation survives (a
   companion-pointing field) the producer is `substC_atRec_stored_defeq_of_canonical` ∘ §T16.1, not
   `mr_pos_beta`.  The same holds one layer down for (A): §3 charges nothing at a redex field.
3. **The machinery (A) needed already existed one level over, at `atRec`, and nobody had brought it
   down.**  `NestedTele.lean` §T15.7 has `substC_atRec_fieldTypes_defeq'` / `_defeq` /
   `_defeq_of_noK` and `VEnv.TeleDefEq.of_entries'` — exactly §1's statements at the *recursor's*
   level numbering, which is what (B)/(C) consume.  §1 is those three with `D.atRec` deleted.  The
   environment scan (`CtorBetaScan.lean`, Q1/Q2/Q4) is how I found them; none of the four is
   mentioned in `docs/handoff-flipprice.md`, and Q4 also turns up `teleDefEq_fld_of_fields`,
   `teleDefEq_fld_of_np_zero`, `teleDefEq_fld_iota_of_fields` and
   `substC_atRec_stored_defeq_of_canonical`, also unmentioned.  **The brief's method note was
   right and the previous stream's grep-shaped survey of (A) was incomplete.**
4. **`VIndRestore.substC_tyAppR` (`RestoreBridge.lean:530`) carries five hypotheses its proof never
   uses** — `hp : D.params = []`, `hnd`, `hown`, `hlw`, `hcl` — because it sits inside a
   `variable … include hp hnd hown hlw hcl` section.  That unused `hp` is one reason the
   parameterful route could not reach it.  `VIndRestore.substC_tyAppR_free` (§6a) is the same
   statement with only `hnn`/`hna`, and its proof body is character for character the original's.
   **Reported, not fixed**: `RestoreBridge.lean` is not mine.  Recommended edit for whoever owns it:
   move `substC_tyAppR` out of that `include` group (or drop `hp` from it) — it is used by the
   `np = 0` chain and would then serve the parameterful one too.
5. **The brief's `nfnAuxDirty_obligationA` correction is right** (arity 9, proves (A) there, refutes
   (C)); I reproduced its axiom line and arity from the scan and did not inherit the earlier
   version.
6. **`Theory/Inductive/MemberRedex.lean:743`** is a *table row* recording that
   `ctorConstsCR_wf_of_np_zero'`'s hypothesis was weakened to `CanonicalOwn K`, not the theorem's
   definition site (`RestoreBridge.lean:595`).  The claim itself checks out.
7. `docs/handoff-flipprice.md` §6's row 1 should now read: (A)'s residual is
   `hbeta`/`hargs` at companion-pointing recursive fields, **not** "the telescope defeq plus one
   `IsDefEq` on the canonical result".  The result conjunct is closed (§2).
8. `docs/handoff-flipprice.md` §8's ordering (do (C) first, then (A)) is defensible, but the two are
   now the *same* datum through §8.8/§8.9, so whichever is done first should be done as a lemma
   about `hargs`, not per-obligation.

## 5. What to pick up first

1. **`hargs`, once, for all three obligations.** §8.7's `tyVal_hasType_of_faithful` residual, i.e.
   `hsplit` + `hargs` on the presented head.  `instAt_indep_of_tyArgs` says no
   restoration-independent argument produces it, so it enters as data — the question is *where* it
   is supplied from in `AddInductStagesR`, not whether it can be proved.  Feeding it discharges
   §7's `hbeta`, (B)'s motive/minor blocks, and (C)'s `IotaHargs` alike.
2. **`VEnv.HasArgs.congr_tele` + `VEnv.TeleDefEq.inst`.**  `NestedTele.lean` §T15 names this pair as
   *the whole remaining obstruction* to (B)'s assembly.  It is also what stands between §7's `hbeta`
   and a *derivation* of `hbv` rather than a hypothesis: the field context carries
   `C.params.map (·.substC σ)` and §8.8 asks for `D.params`, and F3 (`VIndCtor.WF.params_eq`) relates
   them only definitionally.  One lemma, two obligations, and it is `PiInv`-free.
3. **Bring §1's three lemmas and `TeleDefEq.of_entries'` under one statement.**  §1 is
   `NestedTele.lean` §T15.7 with `D.atRec` deleted; a version generic in the entrywise
   transformation `φ` (with `φ := D.atRec` and `φ := id` the two instances) would replace six
   theorems with three.  I did not do it because `NestedTele.lean` is not mine and a generic-`φ`
   statement belongs there, next to its other consumer.
4. **Non-canonical companion-pointing fields.**  Determine whether one exists.  If not, §7's `hcan`
   is not a restriction and should be recorded as such; if one does, §3 is the form to use and its
   per-field defeq needs a producer that does not go through `restore_canonType_noK`.

## 6. Verification record

* `lake build Lean4Lean.Theory.Inductive.CtorBeta Lean4Lean.Theory.Inductive.CtorBetaScan`:
  **92 jobs**, exit 0, no warnings, axiom lines as §2.
* `lake build`: **1571 jobs**; `Lean4Lean.Theory.Inductive.CtorBeta` built as job **1569/1571**,
  `CtorBetaScan` at 1377/1571.  The build's overall exit was **1**, on a **foreign** file:
  `Lean4Lean/Theory/Inductive/RecTyped.lean:423:28` ("Application type mismatch … `OnCtx.entry_inv`
  … expected `OnCtx (… ++ ?m)`"), which is the concurrent blocker-(B) stream's in-flight file.  Not
  touched, not fixed, per instruction.  By the time of the census it was building.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**, `BUILT: 388; in population but
  NOT BUILT: 0`.  My two files appear in the orphan list (imported by nothing), which is what a
  reduction/measurement file should be, and they add no holes.
* `lake env lean --run scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the
  joined cone".
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.  `CtorBeta.lean`
  imports one module (`Theory.Inductive.NestedTele`); `CtorBetaScan.lean` imports nine, all `Theory`.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not touched.
* Files owned by other streams (`Theory/Inductive/IotaHargs*`, `Theory/Inductive/RecTyped*`,
  `Theory/Typing/SpineVar*`): read only where cited, never edited.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 6a. Measured vs read off

**Measured by me this session:** every axiom line in §2; the environment-scan populations of
`CtorBetaScan.lean` Q1–Q5 (so §4 item 3's ABSENCE/PRESENCE claims are environment facts, not greps);
the census (13, NOT BUILT 0); dup-names; the layering check; the build's job numbers and the
foreign failure's file and line; `substC_tyAppR`'s five unused hypotheses (by re-proving it from
two); and every non-vacuity fact in §3.

**Read off source or documents, not independently re-measured:** that `VIndCtor.Canonical` is false
at `Lean.Json` / `Lean.PrefixTreeNode` / `MRedex.MRWit.MJ` (from `Restore.lean:560`'s docstring and
`StoredIota.lean` §5); that `mrObj_canonical` holds at the non-canonical block (from
`StoredIota.lean` §5.2's docstring); §8.8's identification of its own residual with §8.7's `hargs`
(from `NestedRules.lean` §8.8's docstring); §T15's identification of `HasArgs.congr_tele` as (B)'s
remaining obstruction (from `NestedTele.lean` §T15's prose); and the ι-context measurements at
`ntreeAux` quoted in `docs/handoff-flipprice.md`.
