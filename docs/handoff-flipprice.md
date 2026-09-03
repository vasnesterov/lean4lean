# Handoff: re-pricing the nested `AddInduct` flip (`FlipPrice`)

**Written 2026-09-03, at commit `b7bf5b6`.**  Instruments:
`Lean4Lean/Verify/Inductive/FlipPrice.lean` (axiom prints on declarations that already exist)
and `Lean4Lean/Verify/Inductive/FlipPriceScan.lean` (a structural query over the *compiled
environment*, so an ABSENCE claim cannot be defeated by a theorem hiding under another name).
Both are mine; neither proves anything new.

This file exists because `docs/critical-path.md` Correction 5 and `docs/vacuity-ledger.md` §6
price the nested flip against a state of the tree that no longer holds.  A predecessor stream
did the measurement and died before writing it up; this is the missing write-up, re-measured
from scratch (I did not trust the relayed numbers, and §5 below is where they were wrong).

## 0. What "hole-free" does and does not mean here

Every `#print axioms` line quoted below is **hole-free** and nothing more.  It is not evidence
of non-vacuity.  Where I call an obligation discharged I state the two facts separately:
whether it is hole-free, and whether it is non-vacuous *and how I know*.  The relevant
precedent is ledger row 197: two of the thirteen census holes print clean over an empty domain.

## 1. Measured axiom lines (`lake build` on `FlipPrice.lean`, 75 jobs, exit 0)

| declaration | axioms | arity |
| --- | --- | --- |
| `VEnv.addInductR_ordered'` | `[propext, Quot.sound]` | 12 |
| `VEnv.addInductR_ordered_nil` | `[propext, Classical.choice, Quot.sound]` | 8 |
| `VEnv.ctorConstsCR_wf_of_np_zero'` — (A) at `np = 0` | `[propext, Classical.choice, Quot.sound]` | 20 |
| `VEnv.recConstsR_wf_of_np_zero` — (B) at `np = 0` | `[propext, Quot.sound]` | 15 |
| `VEnv.iotaRulesRS_wf_of_np_zero` — (C) at `np = 0` | `[propext, Quot.sound]` | 15 |
| `VEnv.ctorConstsCR_wf_of_substC` / `_of_substC'` | `[propext, Classical.choice, Quot.sound]` | 14 / 15 |
| `VEnv.recConstsR_wf_of_substC` / `_of_substC'` | `[propext, Quot.sound]` | — / 8 |
| `VEnv.iotaRulesRS_wf_of_substC` | `[propext, Quot.sound]` | 11 |
| `VEnv.iotaRulesRS_wf_of_components` | `[propext, Quot.sound]` | 7 |
| **`InductiveDeclExamples.ntreeAux_obligationA`** | `[propext, Classical.choice, Quot.sound]` | **0** |
| **`InductiveDeclExamples.ntreeAux_obligationB`** | `[propext, Classical.choice, Quot.sound]` | **0** |
| **`InductiveDeclExamples.ntreeAux_obligationC`** | `[propext, Classical.choice, Quot.sound]` | **0** |
| `InductiveDeclExamples.ntreeAux_addInductR_ordered` | `[propext, Classical.choice, Quot.sound]` | **0** |
| `InductiveDeclExamples.nfnAux_addInductR_ordered` | `[propext, Classical.choice, Quot.sound]` | **0** |
| `InductiveDeclExamples.ntree_iotaRules_bridge_false` | `[propext, Quot.sound]` | 0 |
| `InductiveDeclExamples.nfnAuxDirty_obligationA` | `[propext, Classical.choice, Quot.sound]` | **9** |
| `InductiveDeclExamples.nfn_csubst_dom_escapes_blockNames` | `[propext, Quot.sound]` | 0 |
| `VEnv.keysR_induct` | `[propext, Classical.choice, Quot.sound]` | — |
| **`VExpr.NoConstIn.noCSubst`** | **does not depend on any axioms** | — |
| `IsNestedName.mkRecName` | `[propext, Quot.sound]` | — |

Arities are from the environment scan, not from reading source.

## 2. Per-item verdict against `docs/critical-path.md` Correction 5

Correction 5 lists two flips and says the nested one is blocked on the four obligations of
ledger §6.

* **The non-nested flip** (`AddInduct := ∃ …, AddInductStages …`) — still available, still a
  decision, still a *partial* result.  **It does not discharge the nested case**: `AddInductStages`
  is refuted for a nested block (`Verify/Environment/Basic.lean:108`), so `TrEnv'` stays
  unsatisfiable there and nested blocks stay vacuous.  I am not proposing it as a substitute and
  CLAUDE.md forbids narrowing `kernel_sound` to make it one.
* **The nested flip** (`AddInduct := ∃ K R, AddInductStagesR …`) — see §3.

## 3. Per-item verdict against `docs/vacuity-ledger.md` §6's four obligations

| §6 item | ledger's verdict | verdict now | what closed it |
| --- | --- | --- | --- |
| 1. `hctors` — obligation **(A)** | "FALSE, not open" (rows 26–27) | **no longer false; closed at `np = 0`; open in general at `np > 0`** | the substitution moved to the declaration sites `ctorConstsCR`/`recConstsR`. `ctorConstsCR_wf_of_np_zero'` is unconditional at `D.params = []`. The witness that refuted it now **proves** it: `nfnAuxDirty_obligationA` |
| 2. `hrecs` — obligation **(B)** | open; "cleanliness condition mis-stated against `csubstTy`" (row 28) | **closed at `np = 0`; the row-28 obstruction is CLOSED outright; open in general at `np > 0`** | `recConstsR_wf_of_np_zero` (`Theory/Inductive/NestedRules.lean:875`). Row 28 is closed by restating against `VIndRestore.SubstFree` — see §5 |
| 3. `hrules` — obligation **(C)** | open; same row-28 mis-statement | **closed at `np = 0`; row-28 obstruction CLOSED; open in general at `np > 0`; and the ledger's own route for it is REFUTED above `np = 0`** | `iotaRulesRS_wf_of_np_zero` (`NestedRules.lean:889`). See §4 for the refutation |
| 4. the `induct` arm of `VEnv.WF'.keys` | already marked done in §6 itself | **done and landed** (`8942782`); `keysR_induct` hole-free | `Theory/Inductive/NestedKeys.lean` |

**§6 is stale on items 2 and 3.**  It records only "(A) proved for parameterless blocks" and
says (B)/(C) "need their cleanliness condition restated".  Both restatements happened, and both
parameterless theorems exist: `VEnv.recConstsR_wf_of_np_zero` and
`VEnv.iotaRulesRS_wf_of_np_zero`, `Theory/Inductive/NestedRules.lean:875` / `:889`, both
`[propext, Quot.sound]`.

*Correction to the brief I was given*: I was told `NestedRules.lean` was "untracked at the start
of this session".  It is **tracked**, and has been since `b4d6e21` (2026-09-01 09:06); (B)/(C) at
`np = 0` landed in `146ce97` (2026-09-01 09:34).  What is true is the substantive half: the
ledger's §6 text predates them and does not mention either name.  `docs/critical-path.md`'s
item 2 (around line 200) *does* already cite both, so critical-path is ahead of the ledger here.

## 4. (C)'s syntactic route is refuted above `np = 0` — use the componentwise one

`InductiveDeclExamples.ntree_iotaRules_bridge_false` (`Theory/Typing/ConstSubstNested.lean:2717`)
refutes by `decide`, at `ntreeAux` with `np = 1`, the **syntactic list** equation

    D.iotaRules.map (·.substC σ) = D.iotaRulesRS R K

which is exactly `hbridge` of `VEnv.iotaRulesRS_wf_of_substC` and exactly the form ledger §6
quotes as (C)'s bridge.  So:

* **the route ledger §6 prints for (C) is dead above `np = 0`**, and
* `Theory/Inductive/NestedOrdered.lean`'s STATUS entry (third entry, 2026-08-31) points at the
  same dead route.

The live route is componentwise typed defeq: `VEnv.iotaRulesRS_wf_of_components`
(`Theory/Inductive/NestedTele.lean:2452`, arity 7, `[propext, Quot.sound]`) — no environment
hypotheses at all, three typed conversions per ι-rule.  Its general parameterful consumer is
`VEnv.iotaRulesRS_wf_of_hargsD` (`NestedTele.lean:3903`).

## 5. §12's composition: attempted, and it was **already in the tree**

The brief asked whether `VExpr.NoConstIn.noCSubst` at `P := IsNestedName` — composed against
`IsNestedName` being a *prefix* test, so that it reaches a companion's constructor and recursor
names and not only its type name — discharges the `csubst`-domain obstruction of row 28.

**It does. And the composition had already been made, before this stream started.**  The brief's
"never composed against (B)/(C)" is wrong, and this is the most important correction in this
file, because it means §12 was not the next piece of work.

Where it lives: `VIndRestore.NameBarrier`, `Verify/Inductive/NestedRestore.lean` §2.

* `NameBarrier.dom` (`:116`) is `VIndRestore.csubst_dom` (`Theory/Inductive/NestedRules.lean:145`,
  no hypotheses) plus the barrier's three `aux*` clauses — i.e. exactly `noCSubst`'s `hdom`,
  *"every name in `csubst`'s domain satisfies `P`"*.  Note the three clauses: `auxTy`, `auxRec`,
  `auxCtor`.  Those are the three name kinds `csubstList` inserts and `blockNames` does not
  reach, which is the brief's own analysis — correct, and already implemented.
* `NameBarrier.substFree` (`:126`) is the composition spelled out; its `tyArgs` field reads
  `(h.resArgs j a ha).noCSubst fun _ _ => h.dom`.
* `NestedBarrier := NameBarrier … IsNestedName` (`:149`) is the instance at the prefix test, and
  `RestoreData.mkRestore_nestedBarrier`'s `auxRec` clause is `IsNestedName.mkRecName_iff.2` — the
  prefix-test half of §12's pair, used exactly where the brief predicted.

And row 28's obstruction is discharged because **(B)/(C) were restated to take
`hfr : R.SubstFree D (R.csubst D K)`** rather than a `blockNames`-based `NoBlock` clause.
`SubstFree` *is* the csubst-domain condition; `NameBarrier.substFree` supplies it from name
discipline alone — no `env`, no `Faithful`, no `Canonical`, no `Nodup`.

### 5a. What was actually missing, and is now in the tree

Nobody had written (B) or (C) down *with the barrier in place of `SubstFree`*, so "the obstruction
is discharged" was an argument about docstrings rather than something checkable.  I did that, in
`Lean4Lean/Verify/Inductive/FlipPriceCompose.lean` (mine, new).  Seven declarations, every one a
single application — which is the honest measure of how much of §12 was left.

| declaration | what it shows | axioms |
| --- | --- | --- |
| `VEnv.recConstsR_wf_of_np_zero_of_barrier` | (B) at `np = 0` from `NestedBarrier` | `[propext, Quot.sound]` |
| `VEnv.iotaRulesRS_wf_of_np_zero_of_barrier` | (C) at `np = 0` from `NestedBarrier` | `[propext, Quot.sound]` |
| `…_of_barrier'` (both) | …and with `DomSep` also gone, via `domSep_of_allNames_nodup` | `[propext, Quot.sound]` |
| **`VEnv.iotaRulesRS_wf_of_hargsD_of_barrier`** | **(C) at `np > 0`**, every name-discipline input discharged, leaving `hdata` alone | `[propext, Classical.choice, Quot.sound]` |
| **`RestoreData.mkRestore_iotaRulesRS_wf_of_hargsD`** | the same for the restoration the **checker itself builds** — no barrier hypothesis at all | `[propext, Classical.choice, Quot.sound]` |
| `InductiveDeclExamples.nfn_barrier_route_inhabited` | the non-vacuity check, §5b | `[propext, Quot.sound]` |

The last two are the ones that are not redundant with §1 of that file: they say the barrier
discharge works at `D.np > 0` too, which is where the flip is actually blocked.

### 5b. Hole-free vs non-vacuous, stated separately

* **Hole-free**: all seven, measured (`lake build`, 160 jobs, exit 0; axiom lines above).
* **Non-vacuous** — and here is how I know, which is *not* the axiom line:
  * `NestedBarrier` is bounded **both** ways at the `NFn`/`PFn` witness, field by field:
    `nfnRestore_nestedBarrier` holds; each of the four `res*` fields is separately *refuted* by a
    junk restoration (`nfnBarrierJunkTy/Rec/Ctor/Args_not_barrier`); the `aux*` group is refuted
    by a wrong `K` (`nfnBadK_not_barrier`); and `not_nestedBarrier_nil` shows it is not
    `K`-vacuous.  That is `NestedRestore.lean` §7, not my work, and it is the discipline §5a of
    the vacuity ledger asks for.
  * `nfnRestore_substFree'` re-derives the *hand* proof's conclusion through
    `NameBarrier.substFree`, so the barrier route is not weaker than the witness-by-witness one.
  * `nfn_barrier_route_inhabited` (mine) exhibits **all six** non-environment hypotheses of §1's
    (C) holding *simultaneously* at `nfnAux`/`nfnRestore`/`nfnK`.  I deliberately did **not**
    include `hsrc`/`hσ`: those are environment-shaped and belong to the staging argument, and
    faking them at a witness is the exact defect this check exists to catch.
* **`iotaRulesRS_wf_of_hargsD_of_barrier` and `mkRestore_iotaRulesRS_wf_of_hargsD` are
  reductions, not discharges.** Their `hdata : R.IotaHargs …` *is* the open obligation at
  `np > 0`. I have no witness for it at `np > 0`, so I do not claim their hypothesis set is known
  satisfiable there. What *is* known: (C) is achievable at `np = 1` by some route, because
  `ntreeAux_obligationC` is hypothesis-free.

### 5c. A second `critical-path.md` item closed by the same barrier

`docs/critical-path.md` item 2 lists `VIndRestore.KeysFree` as something that "must stop being a
hypothesis", with the note that it is **not** derivable from `Faithful` + `OwnId` + freshness.
`NameBarrier.keysFree` and `RestoreData.mkRestore_keysFree` derive it — both
`[propext, Quot.sound]`. The note is not contradicted: the derivation runs off *name discipline*,
a different premise, and does so for the restoration the implementation constructs. So that
bullet is closed too, by the ingredient §12 named.

## 6. Is the nested flip available?

**No.** It is closer than either document says, and the shape of what is left has changed, but it
is not available.

Available (measured, all hole-free):

* every arm of `AddInductStagesR` — `.le`, `.map_wf`, `.find?_shape`, `.defeqs`,
  `.to_addInductR`, `.find?_type_head` (`Verify/Environment/InductR.lean`), and
  `AddInductStagesR` has witnesses;
* all three obligations of `VEnv.addInductR_ordered'` **in general at `D.params = []`**;
* all three obligations **hypothesis-free at a parameterised (`np = 1`) nested block** —
  `ntreeAux_obligationA/B/C`, arity 0 each, confirmed by the environment scan;
* the keys arm (`keysR_induct`), and now `KeysFree` and `SubstFree` from name discipline.

**Still blocking: three items, all the same shape — the general parameterful case of one
obligation each.** All three are ordinary open theorems, and the census reads 0 at all three
because they are *hypotheses* of proved theorems (the fourth instrument blindness).

| # | obligation | live general route (owner file) | residual |
| --- | --- | --- | --- |
| 1 | **(A)** `hctors` at `D.np > 0` | `VEnv.ctorConstsCR_wf_of_substC'` — `Theory/Inductive/RestoreBridge.lean` | its telescope-defeq hypothesis: `TeleDefEq` on `C.params ++ fieldTypes` against `C.params ++ fieldTypesR`, plus one `IsDefEq` on the canonical result. The syntactic bridge holds **iff** `D.params = []` — above that `substC` leaves a saturated `D.np`-fold β-redex where `tyAppR` is the contractum. One-block instance in hand: `ntreeNode_beta_bridge` |
| 2 | **(B)** `hrecs` at `D.np > 0` | `VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` — `Theory/Inductive/NestedTele.lean:2200/2236` | the per-block / per-entry typed data those take |
| 3 | **(C)** `hrules` at `D.np > 0` | `VEnv.iotaRulesRS_wf_of_hargsD` — `NestedTele.lean:3903`, and now `…_of_hargsD_of_barrier` with the name half discharged | `hdata : R.IotaHargs D (R.csubst D K) e₃ j C` per constructor: a `TeleDefEq` on the ι-context plus three typed conversions. At `ntreeAux` this is measured as **nine** conversions, all of which **move** (`ntree_iota_components_ne`, `decide`), so no `rfl` discount applies |

I am **not** making the flip. Per the brief this is the orchestrator's to sequence with the user,
and it is not available anyway.

### 6a. Not a substitute

The **non-nested** flip is still available and still a decision (price census **13 → 16**, the
three being `reduceProjCore_none`, `reduceProjCore.WF`, `inductiveReduceRec_eq_none`). It
**does not discharge the nested case**: `AddInductStages` is refuted at a nested block, so
nested blocks stay vacuous under it. CLAUDE.md forbids narrowing `kernel_sound` to make it
suffice, and I am not proposing that.

### 6b. Two holes that must stay open

Ledger row 197: `tryEtaStructCore.WF` and `isDefEqUnitLike.WF` are vacuously true today
*because* `AddInduct` is empty, and closing them would move the census 13 → 11 while proving
nothing. Untouched here, deliberately.

## 7. Corrections to what I was told, and to the documents

**To the brief I was given** (each of these I checked myself):

1. **"§12 names an uncomposed two-ingredient pair … never composed against (B)/(C)"** — wrong.
   The composition is `VIndRestore.NameBarrier` and it predates this stream (§5). The *analysis*
   in §12 is right in every other respect, including which three name kinds matter.
2. **"`NestedRules.lean`, a file that was untracked at the start of this session"** — wrong; it
   has been tracked since `b4d6e21` (2026-09-01 09:06), and (B)/(C) at `np = 0` landed in
   `146ce97` (2026-09-01 09:34). The substantive half stands: ledger §6 does not mention either
   theorem.
3. **"`nfnAuxDirty_obligationA` hole-free"** — true, but it has **arity 9**: it *proves* (A) at
   that block under nine hypotheses. "The block that used to refute (A) now refutes nothing" is
   right about (A); note it refutes **(C)** instead (`nfnNodeDirty_fieldTypesR_dirty` +
   `nfnAuxDirty_iotaCtxR_eq`).
4. Everything else relayed to me reproduced exactly, including `addInductR_ordered'` at
   `[propext, Quot.sound]`, the three arity-0 `ntreeAux_obligation*`, `NoConstIn.noCSubst`
   depending on **no axioms at all**, and the `decide` refutation of (C)'s syntactic bridge.

**To the documents** (I have not edited them — they are not mine):

* `docs/vacuity-ledger.md` §6 item 1 still says (A) is "FALSE, not open". Rows 26–28 already
  correct this in the registry, but §6's own prose does not.
* `docs/vacuity-ledger.md` §6 items 2 and 3 do not know about `VEnv.recConstsR_wf_of_np_zero` /
  `VEnv.iotaRulesRS_wf_of_np_zero`, and print for (C) a bridge that is **refuted** at `np = 1`.
* `docs/vacuity-ledger.md` row 28 ("mis-stated") should be marked **closed**: the restatement
  against `SubstFree` happened and the barrier discharges it (§5).
* `Theory/Inductive/NestedOrdered.lean`'s third STATUS entry (2026-08-31) still gives the
  `csubst`-domain escape as the reason (C) is "strictly harder", and points at the refuted
  syntactic bridge. Both halves are now stale.
* `docs/critical-path.md` Correction 5's "four obligations" framing should become **three**, all
  of one shape: the general parameterful case. Its `KeysFree` bullet is closed (§5c).

## 8. Pick up first

1. **(C) at `np > 0`**: discharge `R.IotaHargs` — the only remaining input to
   `VEnv.iotaRulesRS_wf_of_hargsD_of_barrier`. Nine concrete conversions at `ntreeAux`
   (`ntreeAux_iotaRulesRS_wf_of_nine`), none of them an identity. This is the sharpest-edged of
   the three: the reduction is free (`iotaRulesRS_wf_of_components` has *no* environment
   hypotheses) and `ntreeAux_obligationC` proves the target is reachable at `np = 1`.
2. **(A) at `np > 0`**: the β-gap. `ctorConstsCR_wf_of_substC'`'s telescope defeq, with
   `ntreeNode_beta_bridge` as the one-block instance to generalise.
3. **(B) at `np > 0`**: `recConstsR_wf_of_blocksD` / `_of_entriesD`'s typed data. Likely the
   easiest of the three, since (B) has no `ihValues` layer.
4. **Cheap and worth doing before any of them**: re-mark ledger §6 and `NestedOrdered.lean`'s
   STATUS entry per §7. Both currently point a reader at the refuted route for (C), which is the
   direction of drift the ledger's own process notes call the one that wastes work.

## 9. Verification record

* `lake build` on `FlipPrice.lean` + `FlipPriceScan.lean`: **75 jobs**, exit 0.
* `lake build Lean4Lean.Verify.Inductive.FlipPriceCompose`: **160 jobs**, exit 0.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**, `in population but NOT
  BUILT: 0`. My three files appear as orphan modules (imported by nothing), as measurement files
  should, and add no holes.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not touched.
* **Foreign build failures seen and not fixed** (other streams' files, per instruction): a full
  `lake build` mid-session failed at `Theory/Typing/SpineVar.lean:589` ("Missing cases: Eq.refl"),
  which cascaded into a missing `Verify/Inductive/ProjNoNested.olean`; and the census's first run
  aborted on a missing `Theory/SetModel/InterpSound.olean`. `InterpSound` built on a direct
  `lake build` of that target, and by the time of the census run `SpineVar` was building too — so
  both resolved without intervention from me, and neither is in a file I own.

### 9a. Measured vs read off

**Measured by me this session** (built, then the axiom line / arity read from the build output or
from `FlipPriceScan.lean`'s environment walk):

* every axiom line in §1 and in §5a's table;
* every arity in §1 — from the environment scan, so a general result cannot hide under another
  name. In particular the scan finds **exactly five** declarations whose type mentions both
  `VEnv.addInductR` and `VEnv.Ordered`, and the three general ones all carry hypotheses
  (`addInductR_ordered'` 12, `addInductR_ordered` 11, `addInductR_ordered_nil` 8) while the only
  arity-0 ones are the two witnesses. **So there is no hypothesis-free general `Ordered`-after-a-
  nested-step in the tree**, and that is an environment fact, not a grep;
* the three live general parameterful routes of §6's table — `FlipPrice.lean` §13, all hole-free;
* the census (13) and the layering check (empty);
* the seven new declarations of `FlipPriceCompose.lean`;
* the git history behind correction 2 of §7.

**Read off documents or source, not independently measured:**

* the non-nested flip's price **13 → 16** and its three declarations
  (`reduceProjCore_none`, `reduceProjCore.WF`, `inductiveReduceRec_eq_none`) — from
  `docs/critical-path.md:645`, which itself says "the three declarations themselves were not
  re-audited";
* that `AddInductStages` is refuted at a nested block (`Verify/Environment/Basic.lean:108`) — read
  from Correction 5, not re-run;
* row 197's claim that `scripts/empty-inductives.lean` still reports `AddInduct` as a vacuity
  source — read from the ledger; I did not re-run that script;
* the ι-context lengths 8/6/8 at `ntreeAux` — read from `NestedTele.lean` §T16.12's docstring,
  which says they were measured there.
