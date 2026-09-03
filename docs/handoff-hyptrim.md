# Handoff: the `include`-group over-supply defect, and two documents that read as complete

2026-09-03. Files this round owns: `Theory/Inductive/RestoreBridge.lean`,
`Theory/Inductive/NestedTele.lean`, `docs/vacuity-ledger.md`, plus the new
`Theory/Inductive/HypTrimWitness.lean`.

## Summary

| item | status |
| --- | --- |
| `VIndRestore.substC_tyAppR` trimmed to the two hypotheses it uses | **proved** |
| a second instance in the same group (`substC_tyApp_eq_tyAppR_map`, `hcl`) | **proved** |
| a third, cascading (`ctorType_substC_eq_typeR_substC`, `hcl`) | **proved** |
| `substC_tyAppR_free` is now exactly redundant | **proved**, by `rfl` |
| `NestedTele.lean` §T15.8's (B) list marked non-exhaustive | **done** (comment-only) |
| ledger 152d / row 143d re-marked for (B) | **done**, + rows 206/206b/206c |
| the same pattern elsewhere: swept, 785 theorems | **measured**, 12 candidates, 7 real |

Full `lake build`: **1575 jobs**, green. Census: **13 before, 13 after**, and the hole *list* is
identical, not merely the count. All **240** `#print axioms` lines over
`RestoreBridge` + `CtorBeta` + `NestedTele`: **byte-identical** before and after.

## 1. The defect

`VIndRestore.substC_tyAppR` (was `RestoreBridge.lean:531`; the brief said `:530`, accurate to one
line) sat under `include hp hnd hown hlw hcl` followed by `include hnn hna`, and so took **seven**
hypotheses. Its proof is four lines and uses `hnn j` and `hna j` only.

**The brief's "five hypotheses" count was a guess, and it is correct** — `hp`, `hnd`, `hown`,
`hlw`, `hcl`. Established two ways: a textual scan of the `include` scope, then by the trim
elaborating.

**`lean_minimal_hypotheses` cannot see this class.** It drops explicit `(h : T)` binders from the
theorem's own signature; these hypotheses are section `variable`s pulled in by `include` and
appear nowhere in the source of the theorem. That is *why* the defect was invisible, and it is
worth knowing before the next brief points a stream at that tool for this purpose.

### The mechanism, which is the transferable part

Lean has a linter for exactly this — `linter.unusedSectionVars` — and **an explicit `include`
suppresses it.** It fires only for *automatically* included variables. Evidence, unplanned: the
moment my first two trims broke the group, the linter itself reported the third instance
(`ctorType_substC_eq_typeR_substC`, `hcl`) with no prompting from me. So an `include` group is a
blind spot with a working detector sitting directly behind it.

Two mechanical notes for whoever does the next one:

* `omit … in` must go **above** the docstring, not between docstring and `theorem`. Between them
  it is a parse error (`unexpected token 'omit'`), because the docstring binds to the declaration.
* After editing, **rebuild before probing.** My first instantiation attempt failed with
  `substC_tyAppR mp_hnn` expecting `D.params = []` — the stale `.olean`. That is the seventh such
  incident recorded.

### What changed

```
substC_tyApp_eq_tyAppR_map   omit hcl                    (5 section hyps -> 4)
substC_tyAppR                omit hp hnd hown hlw hcl    (7 -> 2)
ctorType_substC_eq_typeR_substC  omit hcl                (cascade, 7 -> 6)
```

The third is a cascade, not an independent observation: `hcl` reached it only through the other
two. It was redundant anyway — the statement keeps `hcl0 : … ClosedN 0`, which implies the
`ClosedN D.np` that `hcl` asserted (`HypTrimWitness.hcl_of_hcl0`).

**Ripple: zero outside `RestoreBridge.lean`.** All five call sites of the three lemmas are in that
file. Re-pointed by dropping the arguments; every proof term accepted unchanged; axioms identical.
This meets the bar the brief set.

## 2. Anti-vacuity, done the strong way

`Theory/Inductive/HypTrimWitness.lean` (10 declarations, no `sorryAx`).

Removing a hypothesis *strengthens* a `Prop`-hypothesis statement, so it cannot turn a true
statement false — the risk is the other one, that what remains is vacuous. The weak check would
exhibit some instance. The strong check, done here, exhibits an instance **at a block where the
removed hypothesis is refuted**:

* `mp_hp_false` — `(mpAux mpAuxNodeB).params ≠ []`, so `hp` is **false** at this block and the
  untrimmed `substC_tyAppR` had **no instance here at all**. This is what makes the trim
  load-bearing rather than tidy.
* `mp_np_eq_one` — `np = 1`, by `rfl`.
* `mp_hnn`, `mp_hna` — the two surviving hypotheses, discharged at that same block.
* `mp_tyArgs_one_mentions_MP` — the presented spine really does carry a constant, so `mp_hna` is
  not the empty-quantification case.
* `mp_csubstTy_at_companion` (`rfl`) — the substitution is **not** the everywhere-`none` one;
  `_nested.MDep_1` is in its domain. This is the trap that would have made `hnn`/`hna` hold for a
  trivial reason.
* `mp_substC_tyAppR` — the trimmed lemma applied at `np = 1`.
* `mp_substC_tyAppR_closed` — **arity 0**, at the companion member with a non-empty spine.

Stated separately, as asked: **inhabited** (the arity-0 witness) and **hole-free** (no `sorryAx`
in any of the ten). Axioms are `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`
except `hcl_of_hcl0`, which is axiom-free.

The block is `MRedex.MPWit.mpAux mpAuxNodeB` — a real nested block with a parameter, transcribed
against Lean's own environment in `ParamRedex.lean`, not a degenerate construction of mine.

### `substC_tyAppR_free` is now exactly redundant

`HypTrimWitness.free_eq_trimmed` is

```lean
theorem free_eq_trimmed : @VIndRestore.substC_tyAppR_free = @VIndRestore.substC_tyAppR := rfl
```

which typechecks only if the two types are definitionally equal (proof irrelevance then closes
it). It typechecks. `CtorBeta.lean` is not this stream's file, so the duplicate is **reported, not
deleted**; `CtorBeta.lean:433`'s use of it can become `substC_tyAppR hnn hna` verbatim.

## 3. The sweep, and an honest characterisation of the instrument

Scan: every theorem under an `include` group in `Lean4Lean/Theory`, checking each active
hypothesis for textual absence from the theorem's signature and proof, honouring `omit … in` and
`include … in` and skipping block comments. **Population: 785 theorems.** (An earlier version that
ignored `omit … in` reported 50-odd hits, almost all of them already-fixed; the corrected
population is the one to quote.)

**12 candidates. Each then elaborated with the hypotheses actually omitted**, and the error
location attributed to the theorem's own span versus its consumers:

| file | theorem(s) | verdict |
| --- | --- | --- |
| `Inductive/RestoreBridge.lean` | the 3 above | **real — fixed this round, zero external ripple** |
| `SetModel/IndStage.lean` | `Ind_subsingleton_stage`, `indRec_indep_of_proof_stage` (`hE`) | **real, and zero ripple** — a one-line fix each |
| `Inductive/NestedHead.lean` | `ntree_const_staged`, `nlist_const_staged` (`h`) | **real in the proof, ripple at 2 in-file consumers** |
| `Typing/ConstSubstNested.lean` | `nfnF₂_ordered` (`hE₂`) | **real in the proof, ripple at 2 consumers** |
| `Inductive/ParamRedex.lean` | `mpVal_hasTypeF`, `mpValNode_hasTypeF`, `mp_obj_const_defeq`, `mpBetaV`, `mpBetaN` | **FALSE POSITIVES — all 5** |

**The false-positive class, named:** in `ParamRedex.lean` the hypotheses are consumed *implicitly*
by an automation tactic reading the local context (`type_tac` and friends), so textual absence is
not absence of use. Omitting them errors **inside the theorem's own span**. All five have the same
cause and all five are in one file. So the scan's measured precision is **7 of 12**, and a textual
`include` scan must never be reported without the elaboration step behind it — this is the same
lesson as ledger row 205b one level down.

**Severity is not uniform, and only one of the twelve is in the class the brief cares about.**
`hp : D.params = []` is a *specialisation* — it gates a general statement behind `np = 0` and so
makes a route look unavailable. The rest (`hcl`, `hE`, `hE₂`, the staging `h`s) are incidental. So
the count of "unused hypothesis that actively blocked work" this round is **one**, and it is
fixed. Note also that the staging hypotheses (`h`, `hE`, `hE₂`) may be *deliberate*: they make the
statement about a real staged environment rather than about arbitrary data. Dropping them is safe
but costs documentation value. **I do not recommend blanket trimming there** — the IndStage two
are the only ones I would trim on sight, being zero-ripple and carrying no such role.

**`NestedTele.lean`: zero instances.** Absence claim, with its population stated: **13** theorems
in `include` scope — its two `include hown hat hfr` groups (lines 3023, 3182) plus its seven
`include … in` declarations — and all 13 use every hypothesis they are given. (The figure is 13
from the corrected scanner; an earlier version of it said 10, and 10 is wrong.) Definition site
`Lean4Lean/Theory/Inductive/NestedTele.lean`; tree covered `Lean4Lean/Theory/**`; compiled
environment the full `lake build` at 1575 jobs with the module's `.olean` confirmed newer than its
source. The brief's expectation that NestedTele would hold more of these is **not borne out.**

## 4. Where the brief was wrong, and where it was right

**Right, and verified rather than taken:**

* "five hypotheses, `hp` among them" — correct, all five named correctly.
* `substC_tyAppR` at `RestoreBridge.lean:530` — the `theorem` keyword is at 531. Accurate.
* `substC_tyAppR_free` in `Theory/Inductive/CtorBeta.lean`, committed, same proof body,
  `[propext, Quot.sound]` — correct on every count (line 390).
* Both `substC_motiveType_defeq'` and `substC_minorType_defeq` carry `hK : T.name ∈ K` —
  correct, at `NestedTele.lean:328` and `:643`.
* `motiveEntry_defeq_off_K`, `VIndRestore.minorEntry_defeq_off_K`, `recBody_defeq_off_K` in
  `RecTyped.lean`, **the first and third with no `VIndRestore.` prefix** — correct, and worth
  saying that this awkward detail was right: 407 and 434 fall outside the `namespace VIndRestore`
  that spans 468–663, and 638 falls inside.

**Wrong or incomplete:**

* **"Look for the same pattern in that file and in `NestedTele.lean`" pointed at the wrong second
  file.** `NestedTele.lean` has none. The second and third instances were both in
  `RestoreBridge.lean` itself, in the very same `include` group, and one of them only became
  visible *after* the first two trims. The instances outside my ownership are in `IndStage.lean`,
  `NestedHead.lean` and `ConstSubstNested.lean`.
* **`lean_minimal_hypotheses` was the wrong instrument for the job it was assigned.** It cannot
  reach `include`d section variables at all. The brief's instruction to use it rather than trust
  the count would have produced nothing.
* The brief did not anticipate the cascade: trimming two lemmas freed a third.

## 5. Pick up first

1. **Delete `VIndRestore.substC_tyAppR_free`** from `Theory/Inductive/CtorBeta.lean` and point
   `CtorBeta.lean:433` at `VIndRestore.substC_tyAppR hnn hna`. Proved redundant by `rfl`; one
   consumer; not this stream's file.
2. **`IndStage.lean`'s two `hE`** — measured unused with zero ripple, one line each.
3. `NestedHead.lean`'s two and `ConstSubstNested.lean`'s one — real, but each ripples to two
   consumers, so they need a decision on whether the staging hypothesis is carrying documentation
   weight rather than proof weight.
4. **Do not re-run the textual scan without the elaboration step.** `/tmp` copies are gone; the
   two scripts are worth rebuilding as one instrument in `scripts/` if this is to recur, with the
   `omit … in` handling and the per-case attribution both in it, because without attribution it
   cannot tell "unused with ripple" from "used implicitly".
5. §T15.8's own-head gap is marked but the *marking* now asserts the entries are free off `K`.
   That rests on `RecTyped.lean`'s three `_off_K` theorems, which is checked; what is **not**
   checked here is that (B)'s closures consume them in the shape they are stated in. That
   composition is the next thing someone will assume and should not.

## 6. Not done, and deliberately

`tryEtaStructCore.WF` and `isDefEqUnitLike.WF` untouched; no `AddInduct` flip; frozen files not
read, not written, not `touch`ed; `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` empty;
no `git` state changed.
