# Ruling 122e executed: the iota layer restated over the STORED telescope

Written 2026-09-02 by the stream that did the work, on commit `9c182aa` + this diff.
Everything marked **measured** was run on this tree and the figure is quoted from the tool
output. Everything marked *read off source* is a claim about text I read, not a measurement.

---

## 0. Bottom line

| question | answer |
|---|---|
| Is `hcanon : D.Canonical` / `C.Canonical D` gone from the iota layer? | **Yes**, from all **eighteen** statements that carried it (11 in `NestedRules.lean`, 7 in `NestedTele.lean`). Conclusions unchanged. |
| Is `D.Canonical` gone from the `AddInductive.run` spec? | **Yes**, all four sites (`RunIdentity.lean` ×3, `AddInductiveStep.lean` ×1). |
| Did `ClosednessPropagation.lean` break? | **No, and the gate was open** — it consumes nothing whose statement carried the conjunct. Measured: it builds green (§5). |
| Is the result non-vacuous at a redex block? | **Yes**, `Theory/Inductive/StoredIota.lean` (new) discharges every remaining hypothesis at `mrAux mrAuxNodeB` and instantiates the three bridges there. |
| Anything that *became* vacuous? | **One thing, and it is recorded as a theorem rather than glossed** — see §4.2, the finding that at a redex field the restoration is the **identity**. |
| New `sorry`? New frozen axiom? | **None.** Census TOTAL still **13**, unchanged. Every new/changed declaration `[propext, Quot.sound]` or a subset (§6). |
| Was the ruling right? | **Yes, and it was *cheaper* than costed** — plus two things the ruling did not predict: the conjunct it removes from the run spec was **already dead** (§3.2), and `hpos`'s index bound came out with it, so **obligation (B) at `D.params = []` now carries no per-field side condition at all** (§1.2). |
| Was the ruling's *scope* right? | **Yes, measured.** Obligation (A) (`RestoreBridge.lean`, which I do not own) keeps `hcanon` and is **not** vacuous at the redex block, because its consumer asks for `D.CanonicalOwn K` and `CanonicalOwn` holds there (`mrAuxB_canonicalOwn`). Only (B)/(C) needed the restatement. |

---

## 1. What the repair is, mechanically

The engine is one new lemma, `VIndRestore.substC_atRec_restore`
(`Theory/Inductive/NestedRules.lean`, in §7.5's section):

    (D.atRec (R.restore D k e)).substC σ = (D.atRec e).substC σ     -- for every k, e

with **no side condition on `e` at all** beyond the section's `hp/hnd/hown/hat/hcl0/hfr`. It is
the one-layer-out analogue of `VIndRestore.restore_id`: where the trigger `uniformOcc?` fires,
the trigger's own soundness says the subterm *was* `D.tyApp j k rest`, so §7.4's two head
equations apply and the two sides meet at `tyAppR'`; where it does not fire, the recursion is
congruence.

The one missing ingredient was `hT : D.types[j]? = some T` at a firing site. It comes **free**:
`uniformOcc?` reads its index off `memberIdx`, a lookup in `D.blockNames`. New lemma
`VInductDecl'.uniformOcc?_types` (plus `VInductDecl'.atRec_tyAppR`, an instance of
`atRec_tyAppH`).

That is why the cost is lower than row 122e priced it: **`hpos`'s index bound was not needed
either** in the field telescope. `VIndRestore.substC_atRec_fieldTypes` now takes *neither*
`hcanon` nor `hpos` and its statement is byte-identical.

### 1.1 Exactly what changed, statement by statement

`Theory/Inductive/NestedRules.lean` — `hcanon` dropped, conclusions unchanged:

| declaration | explicit hypotheses before | after |
|---|---|---|
| `VIndRestore.substC_atRec_fieldTypes` | `hcanon : C.Canonical D`, `hpos` (ctor-level) | **none** |
| `VIndRestore.substC_minors` | `hσ`, `hcanon`, `hpos` | `hσ` |
| `VIndRestore.substC_recType_eq` | `hσ`, `hcanon`, `hpos`, `hT` | `hσ`, `hT` |
| `VIndRestore.substC_iotaCtx` | `hσ`, `hcanon`, `hpos`, `hT`, `hC` | `hσ`, `hT`, `hC` |
| `VIndRestore.iotaCtx_length_eq` | idem | idem |
| `VIndRestore.substC_iotaLam` | `hσ`, `hcanon`, `hpos`, `hT`, `hC`, `q` | `hσ`, **`hpos`**, `hT`, `hC`, `q` |
| `VIndRestore.substC_iotaRule_eq` | idem | idem — **`hpos` kept**, it is real here |
| `VIndRestore.csubst_recType_eq` | §7.7 section vars incl. `hcanon`, `hpos` | both dropped (`omit hpos in`) |
| `VIndRestore.csubst_iotaRules_eq` | idem | `hcanon` dropped, **`hpos` kept** |
| `VEnv.recConstsR_wf_of_np_zero` | `hcanon : D.Canonical`, `hpos` | **both dropped** |
| `VEnv.iotaRulesRS_wf_of_np_zero` | idem | `hcanon` dropped, `hpos` kept |

New in that file: `VInductDecl'.uniformOcc?_types`, `VInductDecl'.atRec_tyAppR`,
`VIndRestore.substC_atRec_uniformOcc`, `VIndRestore.substC_atRec_restore`.

`Theory/Inductive/NestedTele.lean`:

| declaration | change |
|---|---|
| `VIndRestore.teleDefEq_fld_of_np_zero` | `hcanon`, `hpos` dropped |
| `VIndRestore.iotaCtx_teleDefEq_of_np_zero` | `hcanon`, `hpos` dropped |
| `VEnv.recConstsR_wf_of_np_zero_via_blocks` | `hcanon`, `hpos` dropped |
| `VIndCtor.fieldTypesR_closedTele` | `hnd`, `hcanon`, `hpos` dropped; proof rerouted through the new `VIndRestore.restore_closedN` instead of `canonTypeR_closedN`+`typeR_canonical` |
| `VIndCtor.atRecTele_fieldTypesR_closedTele` | same three dropped |
| `VEnv.iotaRulesRS_wf_of_np_zero_via_components` | `hcanon` dropped, `hpos` kept |
| `VIndRestore.substC_atRec_fieldTypes_defeq` | `hnd`/`hcanon`/`hpos` dropped **and `hrec` restated** — see §2 |

New in that file: `VIndRestore.tyAppR_closedN`, `VIndRestore.restore_closedN`,
`VIndRestore.substC_atRec_stored_defeq_of_canonical`.

New file: `Theory/Inductive/StoredIota.lean` (~370 lines, no `sorry`) — the anti-vacuity
certificate, §4.

### 1.2 `hpos` fell out too, and that is a real strengthening

Once the field telescope stopped reading a recursive field's `recArg`, `hpos` became **dead** in
the whole (B) chain — the Lean linter said so (`Variable name 'hpos' is not explicitly
referenced`) and I removed it: `substC_minors`, `substC_recType_eq`, `substC_iotaCtx`,
`iotaCtx_length_eq`, `csubst_recType_eq` (via `omit hpos in`), `VEnv.recConstsR_wf_of_np_zero`,
and NestedTele's `recConstsR_wf_of_np_zero_via_blocks` and `iotaCtx_teleDefEq_of_np_zero`.

So: **obligation (B) of `VEnv.addInductR_ordered'` for a parameterless nested block now needs
`hp`, `hnd`, `hown`, `hsep`, `hcl0`, `hfr` and nothing per-field whatever.** (C) still needs
`hpos`, through `substC_ihValues` — whose heads are the renamed recursors of the recursive fields'
*targets*, so the index bound there is genuine.

---

## 2. The one statement whose *hypothesis* moved, and why that is the honest form

`substC_atRec_fieldTypes_defeq` (§T15.7) is the **parameterised** (`D.np > 0`) route: it builds
the field-telescope `TeleDefEq` from one defeq per recursive field. Its `hrec` used to be stated
between `r.canonType D i` and `r.canonTypeR D R i`, and the theorem bridged to the *stored* entry
through `typeR_canonical`, i.e. **through `C.Canonical D`**. So the whole statement was vacuous at
a redex block.

`hrec` is now stated between `(D.atRec F.type).substC σ` and
`(D.atRec (R.restore D i F.type)).substC σ` — the field as **stored** against the field as
**restored**. That is the obligation the checker actually has to justify, and it is *statable* at
a redex field.

The old producer is not lost. `VIndRestore.substC_atRec_stored_defeq_of_canonical` converts
§T16.1's `substC_atRec_canonType_defeq` output into the new shape given
**`hct : F.type = r.canonType D i`** — canonicity **per field**, not per block and not per
declaration. That is the point of the level change: at the three redex blocks the block-level form
is false while the per-field form holds at every field but one, so the hypothesis is now
discharged where it is true instead of being vacuous everywhere. The remaining field needs the β
step, which is `MRedex.MRWit.mr_pos_beta`'s business.

**Stated-but-open:** nothing in this tree produces `hrec` at the redex field. I did not attempt
it; `mr_pos_beta` gives the `IsDefEqType` at the field but §T16.1's shape wants a sorted
`IsDefEq` at the recursor numbering under `σ`, and joining them is a separate piece of work.

---

## 3. The spec side

### 3.1 What `ClosednessPropagation.lean` consumes (the thing I was told to check first)

It imports `Verify/Inductive/RunIdentity.lean` and uses, *read off source*:

- `BlockClosed`, `BlockNoFVar`, `BlockClosedMembers` (defs), `BlockClosedFull` is its own;
- `AddInductiveStepWFClosed`, `RejectsNonClosed`, `addInductiveStepWF_of_reject`;
- `LooseBVarWitness.fooBad*`/`fooGood*`, `not_inductStepNested_of_looseBVar`,
  `not_addInductPost_of_looseBVar`;
- `addInductive_WF_blockClosedFull`, `guardLoop_*`, `checkNoLooseBVars.WF`.

**None of those statements mentions `D.Canonical`.** The three sites in `RunIdentity.lean` that
did — `AddInductiveRunRealisesClosed` (def), `addInductiveRunRealises_of_closed`,
`not_trIndDecl_step_of_looseBVar` — have consumers only *inside* `RunIdentity.lean`
(`addInductiveStepWFClosed_of_run`, `LooseBVarWitness.not_addInductiveRunRealises`), plus one
prose mention in `Verify/Inductive/CanonGapMeasure.lean`'s `#eval` message string, which is text,
not a statement. **Measured:** `lake build Lean4Lean.Verify.ClosednessPropagation` after the
change → **1301 jobs, exit 0**, its three `#eval` guards still firing (`reject:`, `member:`,
`guard cost: 4187 inductives / 6773 constructors / ZERO with a loose bvar`).

So the gate was open, and the re-plumbing stayed inside the four files named in the ruling plus
one new file.

### 3.2 A correction to the spec's own docstring — the conjunct was ALREADY dead

`Verify/Inductive/AddInductiveStep.lean` §6 said, of `AddInductiveRunRealises`:

> `D.Canonical` appears explicitly because the conservativity bridges `TrIndDecl.toN` and
> `AddInductStages.toR` both need it, and `InductStepNested` hides `D` under an existential, so
> it cannot be recovered afterwards.

**Both halves are false, measured.** `TrIndDecl.toN` (`Verify/Environment/InductR.lean:390`)
takes `h : TrIndDecl …` and `hst : ∃ et, env.addIndTypes D = some et`; `AddInductStages.toR`
(`:198`) takes `H` alone. Neither mentions `Canonical`. And `addInductiveStepWF_of_run` — the only
consumer — destructured the conjunct into `hc` and then **never used it**: its closing term is
`⟨D, [], D.idRestore, htr.toN hadd.addIndTypes, hadd.addIndTypes, hwf, hadd.toR⟩`.

So the run spec carried an **unsatisfiable** conjunct that nothing consumed. Dropping it needed
exactly four binder deletions and two destructuring patterns (`⟨D, htr, -, -, hadd⟩` →
`⟨D, htr, -, hadd⟩`, `⟨D, htr, hwf, hc, hadd⟩` → `⟨D, htr, hwf, hadd⟩`). The docstring is
replaced by the measurement.

That makes ruling 122e's *spec* half strictly a deletion of dead unsatisfiable text — no proof
obligation moved anywhere.

---

## 4. Anti-vacuity: `Theory/Inductive/StoredIota.lean`

This is the part the ruling said was the entire point, so it is spelled out.

### 4.1 The hypotheses are jointly satisfiable at a redex block — machine-checked

Witness: **`mrAux mrAuxNodeB`** (`MemberRedex.lean` §5) — `MRWit`'s reproduction of `MJ`'s
auxiliary block, i.e. one of the three blocks row 122d names, and the one at which
`mr_auxNodeB_block_not_canonical : ¬ (mrAux mrAuxNodeB).Canonical` is proved. I reused the
existing witness apparatus rather than building a new block, as instructed; `DgWit`/`QNWit` were
read and are the wrong shape for this (they are about `Built.member`'s `none` branch, not about
the substitution bridges).

Discharged at that block, each a theorem in the new file:

| hypothesis | theorem |
|---|---|
| `D.params = []` | `mrAuxB_params_nil` (`rfl`) |
| `D.blockNames.Nodup` | `mrAuxB_blockNames_nodup` (`decide`) |
| `R.OwnId D K` | `mrRestore_ownId` (5 fields) |
| `∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0` | `mrRestore_tyArgs_closed0` |
| `R.DomSep D K` | `mrRestore_domSep`, via `mrAuxB_allNames_nodup` + `mrRestore_domNodup` |
| `R.SubstFree D (R.csubst D K)` | `mrRestore_substFree`, **field by field** (4 separate theorems) |
| `hpos` (the index bound) | `mrAuxB_pos` |
| ~~`D.Canonical`~~ | `mrAuxB_not_canonical` — **FALSE** here |

`mr_csubstList_dom` records that the substitution's domain is the three auxiliary names and is
**not empty**, so `SubstAt`'s `some` clauses have something to say at this block.

Then the restated statements are instantiated: `mr_fieldTypes_bridge_nodeB`,
`mr_fieldTypes_bridge_obj`, `mr_recTypeR_bridge` (obligation (B)), `mr_iotaRules_bridge`
(obligation (C)), `mr_teleDefEq_fld` (§T6's `hfld`), `mr_iotaCtx_teleDefEq` (§T15.4's `htele`),
`mr_fieldTypesR_closedTele` (§T12.1's side condition 1). **Every one of these was vacuous at this
block before the change and is a fact about it now.**

### 4.2 …and one of them is DEGENERATE, which I did not expect and is worth having

I first wrote `mrAuxNodeB.fieldTypesR ≠ mrAuxNodeB.fields.map (·.type)` as the non-triviality
check. **`decide` refuted it.** The reason generalises and is now a theorem
(`mr_auxFieldTypesR_eq_fields`):

> At a redex field the restoration is the **identity**.

`ElimNestedInductive` manufactures the redex as `β k` where the nested instance supplies
`β := fun _ => I` with `I` the block's **own** member. `OwnId` freezes the own member, so
`uniformOcc?` fires inside the redex (at `k = 2`, `D.np = 0`, `bvars 2 0 = []`) and `tyAppR` at
member `0` rebuilds `const MJ []` unchanged. `Lean.Json` and `Lean.PrefixTreeNode` are the same
shape (*read off* `Restore.lean`'s `VIndCtor.Canonical` docstring and `CGMNestWit`), so this is
not an artefact of the witness.

Consequence, stated in the file: **a redex block does not witness that
`substC_atRec_restore`'s `some` branch carries content.** The non-degenerate instance is at the
*same* block's **user** constructor `MJ.obj`, whose recursive field is stored as the companion
constant `_nested.MDep_1` and restored to `MDep Prop (fun _ => MJ)` —
`mr_objFieldTypesR_ne_fields` (`decide`), and `mr_fieldTypes_bridge_obj` is the bridge there.

Obligations (B) and (C) are **not** identities at this block either:
`mr_recTypeR_ne_recType : recTypeR mrRestore 1 ≠ recType 1` and
`mr_iotaRules_keys_move : iotaRules.map key ≠ (iotaRulesRS …).map key`, both `decide`.

### 4.3 Obligation (A) needed no restatement, and that is measured too

`StoredIota.lean` §4 adds `mrObj_canonical : mrObj.Canonical (mrAux mrAuxNodeB)` and
`mrAuxB_canonicalOwn : (mrAux mrAuxNodeB).CanonicalOwn mrK`. Both hold **at the block where
`Canonical` fails**, because the redex lives in the *companion* constructor and `CanonicalOwn`
quantifies only over the members outside `K` — the ones the step declares. Since
`RestoreBridge.lean`'s (A) bridge (`ctorType_substC_eq_typeR_substC`, which still carries
`hcanon : C.Canonical D`) is consumed only through `VEnv.ctorConstsCR_wf_of_np_zero'`, which asks
for `CanonicalOwn`, **(A) is not vacuous at a redex block and did not need the restatement**. So
ruling 122e's scope — (B)/(C) and the run spec — was exactly right, and I did not touch
`RestoreBridge.lean` (which I do not own anyway).

### 4.4 What the certificate does NOT say

- It says nothing about `mrAux mrAuxNodeB` being **well-formed** (`D.WF env`) or about its
  `Built` clauses. Those are `MemberRedex.lean` §5/§8's business, and `Built.fields_noK` still
  has no producer but `decide` (row 117c) — untouched, as the ruling directed.
- It does not produce §T15.7's `hrec` at the redex field (§2).
- It is about the **syntactic** side conditions of the iota layer, which is exactly where
  `hcanon` sat.

---

## 5. Build state, verbatim

- `lake build`: **1502 jobs, exit 0**, zero errors anywhere (final run; 1501 before the new file
  was added). An intermediate run failed with **7 errors, all in
  `Lean4Lean/Theory/SetModel/UpperBound.lean`** — another live stream's file, mid-edit; not
  diagnosed, not touched, and green again by the final run. **Zero errors in any file I own, in
  every run.**
- Warnings in files I own: **one new**, `NestedRules.lean:609` — "automatically included section
  variable(s) unused in theorem `substC_atRec_uniformOcc`: `hnd`", which is §8's finding and is
  the same class as the three that were already there (`substC_motives`, `substC_iotaLhs`,
  `substC_iotaType`). Everything else is pre-existing.
- `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: **1426 jobs, exit 0**, and
  all three guards printed, verbatim and unmoved:

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

- `lake build Lean4Lean.Verify.Inductive.MemberRedexScan`: **1428 jobs**, exit 0; the guarded
  coverage `#eval` unmoved — **48 safe blocks with a nested-shaped field, 793 auxiliary
  constructor fields, 3 defects in 3 blocks (`MRedex.MRWit.MJ`, `Lean.Json`,
  `Lean.PrefixTreeNode`), 3 of 3 covered, residual 0**.

---

## 6. Axioms and `sorry`

`#print axioms` on **all 27** new-or-materially-changed Theory declarations and **all 32** in
`StoredIota.lean`: every one is `[propext, Quot.sound]` or a subset
(`mrAuxB_pos`, `mr_fieldTypesR_hits_some_branch` and `mrObj_canonical` are `[propext]`;
`mrAuxB_params_nil`, `mrAuxB_np_zero`, `mrAuxB_blockNames`, `mrAuxB_ctorsAll_eq` depend on none).
**No frozen axiom, no `Classical.choice`, no `sorryAx`.**

Verify side, and the point is that these are **unchanged** from what
`RunIdentity.lean`'s own "Frozen axioms" section records:

| declaration | axioms | matches recorded? |
|---|---|---|
| `addInductiveStepWF_of_run` | `[propext, Classical.choice, Quot.sound]` | yes — no frozen axiom |
| `not_trIndDecl_step_of_looseBVar` | `[propext, Classical.choice, Quot.sound]` | yes |
| `LooseBVarWitness.not_addInductiveRunRealises` | `[propext, Classical.choice, Quot.sound]` | yes |
| `addInductiveRunRealises_of_closed` | + `Expr.abstractRange_eq`, `abstract_eq`, `hasLooseBVar_eq`, `instantiate1_eq`, `lowerLooseBVars_eq` | yes — exactly the five of bullet 1 |
| `addInductiveStepWFClosed_of_run` | those five + `mkAppData_eq`, `mkData_eq`, `Level.hasMVar_eq` | yes — "reaches all eight" |
| `addDecl.WF_honest_of_run` | all eight + `sorryAx` + `ptrEq*_eq`, `eqv_eq`, `instantiate*`, `Level.*`, `Syntax.structEq_eq` | yes — inherited from `addDecl.WF_honest`'s six non-inductive branches |

**No new frozen-axiom dependency.**

`scripts/sorry-census.lean`: **TOTAL declarations directly containing sorryAx: 13** — unchanged,
and every entry is where it was (`Equiconsistency` 1, `Inductive/Decl` 1, `ChurchRosser` 1,
`Injectivity` 2, `UniqueTyping` 1, `Verify/Environment` 1, `Verify/Soundness` 2,
`TypeChecker/InferType` 1, `TypeChecker/IsDefEq` 2, `Verify/Typing/Lemmas` 1). **No `sorry`
added, none traded.**

---

## 7. What I tried that failed, and the step it failed at

1. **`mrAuxNodeB.fieldTypesR ≠ mrAuxNodeB.fields.map (·.type)`** — `decide` **proved the
   negation**. Failure step: I had assumed the restoration moves the redex field. It does not; see
   §4.2. This is the substantive one, and it changed what the certificate claims.
2. **`(mrAux mrAuxNodeB).iotaRulesRS mrRestore mrK ≠ (mrAux mrAuxNodeB).iotaRules` by `decide`** —
   `failed to synthesize Decidable`; there is no `DecidableEq VDefEq`. Fixed by comparing
   `.map VDefEq.key`, mirroring `nfnAux_iotaRules_keys_move`.
3. **`substC_atRec_uniformOcc` closed with `simp only [atRecTele, atRec]`** — left
   `List.map (fun x => instL selfLvls x) rest = List.map D.atRec rest`. `simp only [atRec]` cannot
   rewrite an *unapplied* `D.atRec` under `List.map`. Fixed by ending with `rfl`.
4. **`rw [VIndField.typeR, hr]` inside `fieldTypesR_closedTele`** — *"Failed to rewrite using
   equation theorems for `VIndField.typeR`"*: the goal still carried the un-β-reduced
   `((fun x => x.fst.typeR D R x.snd) ∘ fun a => (a, 0 + i)) F` from `List.getElem?_zipIdx`. Fixed
   with `simp only [Function.comp_def, Nat.zero_add]` first. Note `show` does **not** work here:
   `0 + i` is not defeq to `i` for a variable `i`.
5. **`ClosedTele … 0` by `exact ⟨trivial, ⟨trivial, trivial⟩, trivial⟩`** — nesting wrong (the
   redex is an `.app` of a `.lam`, so the entry unfolds three levels). `decide` is unavailable
   (no `Decidable (ClosedTele …)`); `simp [VExpr.ClosedTele, VExpr.ClosedN, mrAuxNodeB, mrRedex]`
   works.

Not attempted, deliberately: `Built.fields_noK` (out of scope by the ruling), and any
implementation file.

---

## 8. A measured bonus, not acted on

**`hnd : D.blockNames.Nodup` is now dead in `NestedRules.lean` §7.5–§7.7.** *Measured*: the
statement of `substC_atRec_restore` re-proves in a scratch file with `hnd` deleted from the
binder list (`lean_run_code`, green). *Read off source*: after the change `hnd` appears in that
section only as an argument being threaded — no proof step uses it. It was used by exactly one
step before, `R.typeR_canonical hnd …`, which is gone.

I did **not** remove it. Doing so ripples to ~15 call sites across `NestedRules.lean`,
`NestedTele.lean` and `StoredIota.lean`, and `hnd` is *true at every block* (forced by
`addConstList`'s success), so it is not a vacuity risk — only clutter. Orchestrator's call.

---

## 9. Ledger rows that need writing (I have not edited `docs/vacuity-ledger.md` — it is yours)

1. **122e should be marked EXECUTED**, with three amendments to its own costing:
   - `hpos`'s index bound came out with `hcanon` — **obligation (B) at `D.params = []` now has no
     per-field side condition at all** (§1.2). The cost was *lower*, not higher;
   - the re-plumbing did **not** balloon: four files as predicted, plus one new witness file, and
     `ClosednessPropagation.lean` needed no change at all;
   - the ruling's *scope* is confirmed by measurement, not by argument: obligation (A) keeps
     `hcanon` and is not vacuous, via `CanonicalOwn` (§4.3).
2. **A new row for §3.2**: the `D.Canonical` conjunct of `AddInductiveRunRealises` was **already
   unused by its only consumer**, and the docstring's stated reason for its presence
   (`TrIndDecl.toN` / `AddInductStages.toR` "both need it") was **false** — measured against both
   signatures. This is ledger blindness kind 4 (a false claim in a source file that stops people
   looking) sitting inside a *specification*, which is the worst place for it.
3. **A new row for §4.2**: *at a redex field the restoration is the identity*, because the redex's
   head is the block's own member and `OwnId` freezes it. Consequence for future anti-vacuity
   work: **a redex block is not a witness for the `some` branch of any restoration lemma.** The
   witness for that is a field pointing at a **companion** member — at the same block, `MJ.obj`.
4. **Row 119e's verdict line** for `hcanon` in `NestedRules`/`NestedTele` can be closed: the
   hypothesis is gone, and `StoredIota.lean` is the certificate that what replaced it has content
   at the block that refuted it.

---

## 10. What I would pick up first

1. **§T15.7's `hrec` at the redex field.** It is now *statable* there, which is the whole gain,
   and nothing produces it. `MRedex.MRWit.mr_pos_beta` has the β step as an `IsDefEqType` at the
   field's own context; §T16.1's consumers want a sorted `IsDefEq` at the recursor numbering under
   `σ`. That join is the next real obligation on the parameterised nested path, and it is now the
   *only* thing standing between §T15's assembly and a redex block.
2. **`Built.fields_noK`** — still no producer but `decide` (row 117c). Unchanged by this round, as
   the ruling said.
3. **Decide whether to drop `hnd` from the iota section** (§8). Cheap, mechanical, cosmetic —
   this is the only hypothesis left in §7.5–§7.7 with no use; `hpos` is already gone from (B)
   (§1.2) and is genuine in (C).
4. **`VIndCtor.Canonical` / `VInductDecl'.Canonical` are now used by fewer things.** Surviving
   users after this round, *read off source*: `Verify/Inductive/CanonGapMeasure.lean` (which
   *refutes* it), `TrIndDeclNCtorOwn.lean`, `NestedRestoreWit.lean`,
   `Verify/Environment/Basic.lean`, `Theory/Inductive/NestedOrdered.lean`, plus the positive
   witness theorems (`nfnAux_canonical`, `ntreeAux_Canonical`, `eqIndDecl_Canonical`) and
   `CanonicalOwn`. `Restore.lean`'s docstring says "the remaining deletion is those sites plus
   these two definitions" — that is now a smaller job than it was, and worth re-costing.

---

# Round 2 (2026-09-02, second stream): §T15.7's `hrec` CLOSED, and `hnd` removed

Written by the stream that took §10 items 1 and 3.  Same convention: **measured** means the figure
is quoted from tool output on this tree; *read off source* means I read text, not a measurement.

## 11. Bottom line, and three corrections to §10

| question | answer |
|---|---|
| §10 item 1 — is §T15.7's `hrec` at the redex field closed? | **Yes, and not the way §10 said.** At a redex field the obligation is **empty**, not hard: the restoration is the *identity* there, so `VEnv.TeleDefEq.of_entries'` charges nothing. §2/§10 predicted a join from `mr_pos_beta` to §T16.1's shape; **no join is needed.** |
| Is the `mr_pos_beta` route nonetheless available? | **Yes — measured, three lines** (`mr_hrec_redex_via_beta`). So the route §10 named is not *closed*, it is *unnecessary*, and it costs a typing that `TeleDefEq.rfl` does not charge. §10's "the only thing standing between §T15's assembly and a redex block" was **not standing there**. |
| Was §10's description of the shape mismatch right? | **No.** It said `mr_pos_beta` gives "an `IsDefEqType` at the field's own context" while consumers want "a sorted `IsDefEq`". `VEnv.IsDefEqType` *is* `∃ u, IsDefEq … (.sort u)` (`Theory/Inductive/Decl.lean:278`) — the same shape. The real differences were the target (`canonType` vs `restore`), `U = 0`, and the `atRec`/`substC` wrappers, all three of which are identities or one rewrite at this block. |
| Is the companion-pointing field's `hrec` produced? | **Yes** (`mr_hrec_obj`), from §T16.1 through `substC_atRec_stored_defeq_of_canonical`, with the environment premises discharged in an actually constructed `Ordered` environment (`mr_env_exists`, `mr_hrec_obj_closed`). |
| …and is *that* instance non-degenerate? | **No, and this is the finding worth carrying.** Measured (`mr_obj_entry_substC_eq`, `decide`): at `D.np = 0` the two sides of `hrec` are the **same `VExpr`** after `σ`. So `mr_hrec_obj` proves a *typing*, not a conversion. `hrec` is a genuine conversion only at `D.np > 0`, and **no block in this tree is both a redex block and parameterised** (§13). |
| §10 item 3 — was `hnd` really unused? | **Yes.** Removed from **20** statements across `NestedRules.lean` and `NestedTele.lean`; **four** "automatically included section variable(s) unused" warnings disappeared, which is the measurement that it was dead. |
| New `sorry`? New frozen axiom? | **None.** Census TOTAL still **13**, every entry where it was. Every new or changed declaration is `[propext, Quot.sound]` or a subset (§14). |
| Anything weakened? | Two *hypotheses* weakened (which strengthens the theorems) — §12.1. Nothing's conclusion weakened. Non-vacuity of the weakened forms is exhibited at named fields. |

## 12. What is proved

### 12.1 `Theory/Inductive/NestedTele.lean` §T15.7 — three forms instead of one

The obligation is now stated only where the telescope entry actually *moves*, which is what
`TeleDefEq.of_entries'` needs and what its own docstring is built around.

| declaration | `hrec` demanded at a recursive field when… | status |
|---|---|---|
| `substC_atRec_fieldTypes_defeq'` (**new**) | `(D.atRec F.type).substC σ ≠ (D.atRec (R.restore D i F.type)).substC σ` — the substituted entries differ | sharpest; the other two are corollaries |
| `substC_atRec_fieldTypes_defeq` (**hypothesis weakened**) | `R.restore D i F.type ≠ F.type` — the restoration moves the stored type | the caller-checkable form |
| `substC_atRec_fieldTypes_defeq_of_noK` (**new**) | `¬ VExpr.NoConsts K F.type` — the field points at a **companion** | needs `hown : R.OwnId D K` |

Conclusions are byte-identical to before in all three. The engine of the third is
**`VIndRestore.restore_noK`, which has been in `Theory/Inductive/Restore.lean` all along** — "the
restoration is the identity on anything free of companion constants". Nobody had connected it to
§T15.7; that connection is the whole of item 1.

**Why the redex field is free, generally and not just at the witness.** The redex
`ElimNestedInductive` manufactures is `(fun _ => I) k` with `I` the block's **own** member. The own
member is not in `K`, so the stored type is `NoConsts K`, so `restore_noK` applies. That is a
one-line derivation of §4.2's `decide`, and it means §4.2's finding generalises to `Lean.Json` and
`Lean.PrefixTreeNode` for a *reason* rather than by inspection of their shape.

### 12.2 `Theory/Inductive/StoredIota.lean` §5 (new, ~180 lines) — the instances

| theorem | what it says |
|---|---|
| `mr_redex_noK` | the redex field's stored type is companion-free |
| `mr_restore_redex_id` | …so `restore_noK` gives the identity there — §4.2's `decide` from a general lemma (and an `example` re-checks it by `decide`) |
| `mr_hrec_nodeB_vacuous` | every recursive field of `mrAuxNodeB` is companion-free, so `_of_noK`'s `hrec` has a false premise |
| `mr_teleDefEq_fld_stored` | §T15.7's field-telescope `TeleDefEq` at the redex constructor **with no input at all**, for every `env`, `U`, `Γ` |
| `mr_objField_not_noK` | `MJ.obj`'s field *does* point at a companion, so §5.1's escape is unavailable there |
| `mr_tyBody_hasType` | §T16.1's `hbody`: `MDep Prop (fun _ => MJ)` is a type, from two constant lookups |
| `mr_hrec_obj` | **§T15.7's `hrec` produced at the companion-pointing field**, from §T16.1 |
| `mr_teleDefEq_fld_obj` | …and the field telescope assembled at `MJ.obj` from it |
| `mr_redex_defeq_own`, `mr_hrec_redex_via_beta` | the β route: `mr_pos_beta` generalised off `U = 0`, and `hrec` at the redex field in §10's requested shape |
| `mr_MJ_constant_wf`, `mr_MDep_type_hasType`, `mr_MDep_constant_wf`, `mr_env_exists`, `mr_hrec_obj_closed` | a **constructed** `Ordered` environment holding `MJ` and `MDep`, and §5.2's conclusion with every premise discharged |
| `mr_obj_entry_substC_eq` | **the honesty measurement**: the two sides of §5.2's `hrec` are the same `VExpr` |
| `mr_teleDefEq_fld_obj_free` | …so the *sharpest* §T15.7 form is free at `MJ.obj` too |
| `mrAuxB_np_not_pos` | the only transcribed redex block has `np = 0` |

**Anti-vacuity, per the brief's two kinds.** `mr_teleDefEq_fld_stored` and
`mr_teleDefEq_fld_obj_free` are at a **redex** field / an identity-after-`σ` field: *degenerate by
construction*, and said so in the file. `mr_hrec_obj` / `mr_teleDefEq_fld_obj` are at the
**companion-pointing** field `MJ.obj` — the kind row 127f says is the real instance — and its
`hrec` premise (`¬ NoConsts mrK F.type`) is **true** there, so the hypothesis is not vacuous and the
producer really runs. Its *conclusion* is nonetheless degenerate at `np = 0` (§13).

### 12.3 `hnd` removed from 20 statements (§10 item 3)

`hnd : D.blockNames.Nodup` was threaded through §7.5–§7.7 and the `np = 0` route of §T6/§T12/§T15
and **used by no proof step** — its one consumer, `R.typeR_canonical`, died with ruling 122e.

* `NestedRules.lean` §7.5/§7.6, 12 statements: `substC_atRec_uniformOcc`, `substC_atRec_restore`,
  `substC_atRec_fieldTypes`, `substC_motives`, `substC_minors`, `substC_recType_eq`,
  `substC_iotaCtx`, `iotaCtx_length_eq`, `substC_iotaLhs`, `substC_iotaType`, `substC_iotaLam`,
  `substC_iotaRule_eq` (`substC_ihValues` already `omit`ted it);
* §7.7, 2: `csubst_recType_eq`, `csubst_iotaRules_eq`;
* the two obligations, 2: `VEnv.recConstsR_wf_of_np_zero`, `VEnv.iotaRulesRS_wf_of_np_zero`;
* `NestedTele.lean`, 4: `teleDefEq_fld_of_np_zero`, `iotaCtx_teleDefEq_of_np_zero`,
  `VEnv.recConstsR_wf_of_np_zero_via_blocks`, `VEnv.iotaRulesRS_wf_of_np_zero_via_components`.

**So obligation (B) of `VEnv.addInductR_ordered'` at `D.params = []` now needs `hp`, `hown`,
`hsep`, `hcl0`, `hfr` — five hypotheses, none per-field.** (C) adds `hpos`, which is genuine.
`hnd` survives in the tree where it is *used*: `restore_canonType`, hence
`substC_atRec_stored_defeq_of_canonical`, hence §5.2 — so `mrAuxB_blockNames_nodup` is still
load-bearing in `StoredIota.lean` and its docstring now says why.

**Measured**: four `automatically included section variable(s) unused` warnings in
`NestedRules.lean` (for `substC_atRec_uniformOcc`, `substC_motives`, `substC_iotaLhs`,
`substC_iotaType`) are **gone**; the only warnings left in the three files I touched are two
pre-existing `This simp argument is unused` at `NestedRules.lean:1024`/`:1028`.

## 13. What is refuted, and the limit this exposes

1. **§10 item 1's costing is refuted.** The redex field carries no obligation. Machine-checked
   twice: `mr_restore_redex_id` (general route) and an `example … := by decide`.
2. **§2's shape claim is refuted**: `IsDefEqType` and "a sorted `IsDefEq`" are the same predicate.
3. **`mr_hrec_obj` is degenerate as a conversion** — `mr_obj_entry_substC_eq` (`decide`) shows the
   two sides are one expression. The reason is §7.4's strict head equation
   `substC_tyApp'_eq_tyAppR'`, whose `hcl0` *is* available at `D.params = []`. So:

   > **§T15.7's `hrec` can be a genuine conversion only at a block that is both a redex block and
   > parameterised, and this tree contains no such block.**

   `Verify/Inductive/MemberRedexScan.lean` finds exactly three redex blocks
   (`MRedex.MRWit.MJ`, `Lean.Json`, `Lean.PrefixTreeNode`); only `MJ` is transcribed as a
   `VInductDecl'`, with `np = 0` (`mrAuxB_np_not_pos`). The parameterised nested witness that *is*
   transcribed, `ntreeAux`, satisfies `ntreeAux_Canonical` (`NestedHead.lean:646`, *read off
   source*), so it stores no redex. **The next step on this path is a witness, not a proof**:
   transcribing `Lean.PrefixTreeNode`'s auxiliary block, which has parameters.

## 14. Measurements, verbatim

* `lake build`: **1503 jobs, exit 0**. **Zero errors in any file, in every run**; zero in files I
  own. (1502 at the time §1–§10 was written; the extra job is another stream's
  `Theory/SetModel/PreludeOracle.lean`, untracked in this tree — not mine, not touched.)
* `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: **1429 jobs, exit 0**
  (1426 before that stream's commit `107751a`), and the guards **unmoved**:

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

* `lake build Lean4Lean.Verify.Inductive.MemberRedexScan`: **1430 jobs**, exit 0, guarded coverage
  **unmoved** — `48 safe blocks with a nested-shaped field, 793 auxiliary constructor fields`,
  `DEFECT … 3 field(s) in 3 block(s) [Lean4Lean.MRedex.MRWit.MJ, Lean.Json, Lean.PrefixTreeNode]`,
  `COVERED by one head-β step … 3`, `RESIDUAL after the repair: 0 in 0 block(s) []`.
* `scripts/sorry-census.lean`: **TOTAL declarations directly containing sorryAx: 13** — unchanged,
  every entry where it was. **No `sorry` added, none traded.**
* `#print axioms` on **all 51** new-or-materially-changed declarations — the **20** that lost `hnd`,
  the **2** `nfn*` bridges whose call sites changed with them, the **3** §T15.7 forms, the **19**
  new theorems in `StoredIota.lean` §5, and the **7** `StoredIota` bridges whose proof terms
  changed: every one is `[propext, Quot.sound]` or a subset (`mrAuxB_np_not_pos` depends on none).
  **No frozen axiom, no `Classical.choice`, no `sorryAx`.**
  (`mr_env_exists`/`mr_hrec_obj_closed` reached `Classical.choice` in a first version, through two
  `simp`s in the environment construction; replacing them with `if_pos`/`if_neg` removed it.)

## 15. What I tried that failed, and the step it failed at

1. **`⟨_, .sortDF trivial trivial rfl⟩` for `VConstant.WF` inside `Ordered.const`** — *"Application
   type mismatch: `trivial` has type `True` but is expected to have type `VLevel.WF ?m ?m`"*.
   Failure step: `.const`'s implicit `env`/`ci` are fixed only by its **third** argument, so the
   second argument elaborates against a fully-meta expected type and `VLevel.WF`'s `l` is unknown.
   Fixed by hoisting `mr_MJ_constant_wf` / `mr_MDep_constant_wf` into named theorems. The same
   failure hit `.beta (.constDF hMJ nofun nofun rfl .nil) …` (`nofun` reported "Missing cases:
   _, _" because `ls` was a metavariable) — fixed the same way, with a `have`.
2. **`VExpr.NoConsts mrK mrRedex := ⟨⟨trivial, by decide⟩, trivial⟩`** — *"failed to synthesize
   `Decidable (VExpr.NoConsts mrK (VExpr.const MJ []))`"*. `NoConsts` is a `Prop`-valued match with
   no `Decidable` instance; `decide` cannot see through it to the `∉`. Fixed with
   `show ``MJ ∉ mrK from by decide`. (Worth knowing: **`NoConsts` is not `decide`-able**, so a
   "check it at the block by `decide`" reflex fails here.)
3. **`rw [c2, if_neg …]`** after `VEnv.addConst_constants_eq` — *"Did not find an occurrence of the
   pattern"*: `rw [c2]` leaves a β-redex `(fun n => if … ) ``MJ` and `rw` will not enter it. Fixed
   by `exact (if_neg …).trans hMJ`, which only needs defeq.
4. **Not a failure but a near-miss worth recording.** My first §5.2 docstring said the two sides are
   "different expressions and `σ` identifies them up to defeq". `decide` says they are the *same*
   expression (§13.3). I wrote the claim before checking it; the file now carries the measurement
   and the docstring points at it. This is the fourth mis-attribution in this corner — the pattern
   is asserting non-degeneracy of a *conclusion* from non-degeneracy of a *hypothesis*.

Not attempted, deliberately: `Built.fields_noK` (out of scope), any implementation file, any
frozen file, `Theory/SetModel/*` and `Theory/Equiconsistency.lean` (another stream's).

## 16. Ledger rows this round needs (I did not edit `docs/vacuity-ledger.md`)

1. **127g must be rewritten, not just closed.** Its claim — "nothing produces §T15.7's restated
   `hrec` at the redex field … that join is the only thing between §T15's assembly and a redex
   block" — is wrong in both halves: there is nothing to produce (the entry does not move), and the
   join it names is three lines when you do want it. Blindness kind 4 (an unproved negative that
   stops people looking), committed in a *handoff* and copied into a ledger row.
2. **A new row for §13.3**, and it is the substantive one: **a redex block with `np = 0` cannot
   witness §T15.7's `hrec` non-degenerately either**, because at `D.params = []` §7.4's strict head
   equation makes the two sides equal on the nose. Row 127f said "a redex block is not a witness for
   any restoration lemma's `some` branch"; this is the same lesson one layer out, and it says the
   *companion-pointing* field is not enough either — you need `np > 0`. **Instrument: the residual
   on this path is now a missing witness (a parameterised redex block), not a missing proof.**
3. **A new row for §12.1**: `VIndRestore.restore_noK` existed and answered the question. Three
   rounds priced a β join for an obligation a pre-existing lemma deletes. Guard: before costing a
   restoration obligation, grep `Restore.lean` for `restore_no*`.
4. **A row for §12.3**: `hnd` removed from 20 statements, measured by four vanished linter
   warnings; (B) at `np = 0` is down to five hypotheses, none per-field.

## 17. What I would pick up first

1. **Transcribe `Lean.PrefixTreeNode`'s auxiliary block as a `VInductDecl'`** (it has two
   parameters and is one of the three redex blocks). That is the only thing that can make §T15.7's
   `hrec`, §T16.1's typing bundle, and `hcl0`'s failure meet at one block — and until it exists,
   every statement on the parameterised nested path is being certified at a block where the
   parameterised case is invisible. This is now the top item on this path, ahead of any proof.
2. **`Built.fields_noK`** — still no producer but `decide` (row 117c). Untouched again.
3. **`substC_atRec_canonType_defeq`'s typing bundle at `np > 0`** — at `np = 0` it collapsed to two
   constant lookups (§12.2). What it costs when `r.binders`/`r.args` are non-empty and `D.np > 0`
   is unmeasured, and item 1 is the prerequisite for measuring it.

---

# Round 3 (2026-09-02, third stream): the parameterised redex block BUILT, and row 129b corrected

Written by the stream that took §17 item 1 — with one change of target, argued below.  Same
convention: **measured** means the figure is quoted from tool output on this tree; *read off source*
means I read text, not a measurement.  New file: `Theory/Inductive/ParamRedex.lean` (~760 lines,
56 theorems, no `sorry`).

## 18. Bottom line, and the correction that matters most

| question | answer |
|---|---|
| Is there now a block that is **both** a redex block **and** parameterised? | **Yes**: `MRedex.MPWit.mpAux mpAuxNodeB`, `np = 1` (`mpAuxB_np_one`), `¬ Canonical` (`mpAuxB_not_canonical`), transcribed from a real Lean declaration whose `MP.rec_1` stores `(fun x => MP α) k`. |
| Is §T15.7's `hrec` a genuine **conversion** there? | **Yes, measured.** `mp_obj_entry_substC_ne` (`decide`): the two sides differ. Both sides are computed (`mp_obj_entry_stored`, `mp_obj_entry_restored`, both `rfl`) and the difference is exactly one β step (`mp_obj_entry_betaHead`, `rfl`). |
| Does §T16.1 produce it? | **Yes**, `mp_hrec_obj`, every premise discharged, and closed in a constructed `Ordered` environment (`mp_hrec_obj_closed`). `hbv` — `HasArgs.nil` at `np = 0` — is a real lookup here (`mp_hbv`). |
| **Was the brief's claim right that this needed a redex block?** | **NO, and this is the substantive correction.** `hrec` is a conversion at **any** block with `np > 0`; redex-ness is orthogonal. Measured: `ntree_obj_entry_substC_ne` (`decide`) — the same `≠` holds at `InductiveDeclExamples.ntreeAux`, which is parameterised **and `Canonical`**. So the tree *already contained* a witness for the conversion half and nobody checked it. Row 129b's "there is no proof to find until [such a block] exists" is wrong. |
| So what is the new block actually for? | The **joint** property: it is the first block that is *simultaneously* a block where `hcanon` is false (so ruling 122e's deletion has content) *and* parameterised (so §T15.7's obligation is a conversion). Not the only witness of either half. |
| Do obligations (B) and (C) go through there? | **No — and not because their hypotheses are unavailable: their `np = 0` conclusions are FALSE.** Measured, three `decide`s: `mp_fieldTypes_bridge_obj_false`, `mp_recTypeR_bridge_false`, `mp_iotaRules_bridge_false`. So `hp`/`hcl0` are load-bearing, not conservative. |
| Where does the assembly stop, then? | At the **environment**, not the telescope layer: `recConstsR_wf_of_entries`'s `hσ : (R.csubst D K).WF E₂ e₂ D.recUvars`. **And the apparatus for it exists** — `nfnSubstAll_WF₂`/`₃` at the parameterless `nfnAux`, with `nfnAux_recConstsR_wf` instantiating (B) off it — so what is missing is that template at `np = 1`. (My first draft said no such witness existed anywhere; §24.5 records the correction.) |
| Anything the general theory says cannot be derived, and that this witness supplies? | **Yes**: `hargs`. `instAt_indep_of_tyArgs` shows `Faithful` cannot produce it when the head's type body is closed after splitting — and `MDep`'s is (`mp_split_body_closed`). `mp_hargs` supplies it by hand. |
| New `sorry`? New frozen axiom? | **None.** Census TOTAL still **13**, every entry where it was. All **54** new theorems `[propext, Quot.sound]` or a subset. |

## 19. What is proved — `Theory/Inductive/ParamRedex.lean`

`MP (α : Type)` is `MRWit.MJ` with one phantom parameter, nesting through the **same**
`MRWit.MDep`, so every coordinate row 127f/129b measured at `MJ` is comparable and **only `np`
moves**.  Lean's own kernel runs the elimination: `MP.rec_1`'s companion minor premise has the
field domain `(fun x => MP α) k` and carries an induction hypothesis — the same defect as at `MJ`,
`Lean.Json` and `Lean.PrefixTreeNode`.

**Reused rather than rebuilt** (the brief asked): `MRWit.MDep` and its transcription `mrNode` /
`mrDepDecl` / `mrDepType` verbatim; `MRWit.mr_MDep_constant_wf` for the environment; the whole
`StoredIota.lean` §1 template for the side conditions; `VIndRestore.restore_noK`,
`substC_atRec_fieldTypes_defeq'` / `_of_noK`, `substC_atRec_canonType_defeq`,
`substC_atRec_stored_defeq_of_canonical`, `domSep_of_allNames_nodup`.  `DgWit` and `QNWit` were
read and are the wrong shape (as `StoredIota.lean` already recorded): they are about
`Built.member`'s `none` branch, not about the substitution bridges.  Nothing was copied that could
be instantiated.

### 19.1 The transcription is anchored three ways, all `rfl`

* `((mpAux mpAuxNodeB).types.getD 0 default).type = (vconst(type_of% @MP)).type`;
* `mp_obj_declared`: `(mpObj.typeR … ).substC (mpRestore.csubstTy …) = (vconst(type_of% @MP.obj)).type`;
* `mpAuxNodeB_built`: `mpOcc.ctor (mpAux mpAuxNodeB).header mpRestore mrNode = mpAuxNodeB`, and
  `mpAux_member_built` for the member.  So the block is **what the construction computes** from
  `MDep`'s own constructor, not a hand-written guess.

(The recursor cannot be anchored — `vconst(type_of% ·)` β-reduces the redex away, which is
`MemberRedexScan.lean`'s standing caveat and why that file exists.)

### 19.2 The side conditions

`mpAuxB_blockNames_nodup`, `mpAuxB_allNames_nodup`, `mpRestore_ownId` (five clauses; the `tyArgs`
clause now has content — `bvars 0 1 = [#0]`, not `[]`), `mpRestore_substFree` (four separate
theorems, per `StoredIota`'s blindness-7 note), `mpRestore_domNodup` / `mpRestore_domSep`,
`mp_csubstList_dom`, `mpAuxB_pos`, `mpObj_canonical`, `mpAuxB_canonicalOwn` — so obligation (A)'s
consumer still has its hypothesis at this block, exactly as at `MJ`.

Two are **false** here and are stated as such rather than omitted:

* `mpAuxB_params_ne_nil` — `hp : D.params = []` fails;
* `mp_not_tyArgs_closed0` — `hcl0` fails, the same refutation `ntree_not_tyArgs_closed0` makes at
  the canonical parameterised witness.  What *does* hold is closedness at `D.np`
  (`mpRestore_tyArgs_closedNp`), which is what §T16.1 asks for.

### 19.3 The conversion, and both routes to it

| theorem | content |
|---|---|
| `mp_obj_entry_stored` | the substituted entry is `(fun α : Type => MDep Prop (fun _ => MP α)) #0` — a β-redex, because `substC` must substitute a *closed* term and the occurrence's own parameter argument stays put |
| `mp_obj_entry_restored` | the restored entry is its contractum |
| `mp_obj_entry_betaHead` | …and the head β-contraction of the first **is** the second (`rfl`) |
| `mp_obj_entry_substC_ne` | **the headline measurement** (`decide`): the two differ. Contrast `MRWit.mr_obj_entry_substC_eq`, the same statement with `=` at `np = 0` |
| `mp_hrec_obj` | §T15.7's `hrec` produced from §T16.1, premises discharged; the context must begin with the block's parameter, which `hbv` forces |
| `mp_hrec_obj_beta` | the same conversion as one `IsDefEq.beta`, with **no** `Ordered` environment — the cheap route, recorded for the cost comparison |
| `mp_teleDefEq_fld_obj` | the field telescope at `MP.obj`, assembled through `of_entries'`'s **right** disjunct (contrast `MRWit.mr_teleDefEq_fld_obj_free`, which takes the left) |
| `mp_env_exists`, `mp_hrec_obj_closed` | a constructed `Ordered` environment holding `MP` and `MDep`, and the conversion in it at `Γ = [Type]` |

### 19.4 …and row 127f is confirmed to be `np`-independent

`mp_redex_noK`, `mp_restore_redex_id` (from `restore_noK`, plus an `example … := by decide`),
`mp_auxFieldTypesR_eq_fields`, `mp_hrec_nodeB_vacuous`, `mp_teleDefEq_fld_stored`: at the **redex**
field the restoration is still the identity and §T15.7 still charges nothing.  So the two findings
separate cleanly — row 127f is about redex-ness and holds at every `np`; row 129b's degeneracy was
about `np` and holds at no redex-ness.

## 20. What is refuted

1. **Row 129b's conjunction.** `hrec` is a genuine conversion at any `np > 0` block; a redex block
   is not needed.  `ntree_obj_entry_substC_ne` (`decide`) at `ntreeAux` — parameterised and
   `ntreeAux_Canonical`.  This is blindness kind 4 for the third time in this corner: an unproved
   negative ("the next step is a witness, not a proof") that suppressed a three-line check.
   The general reason was already in the tree in two places —
   `VIndRestore.substC_tyApp_comp` ("a companion head becomes a saturated `D.np`-fold redex") and
   `VIndRestore.instAll_tyBody` ("the contractum of a substituted companion head is the restored
   head, exactly") — and `ntreeNode_substC_ne_typeR` is the same β-gap measured one layer over, at
   the same canonical witness, and has been in `Theory/Typing/ConstSubstNested.lean` all along.
2. **The `np = 0` route is not "unavailable pending work" above `np = 0`; its conclusions are
   false.**  Three `decide`s: the strict field-telescope equation `substC_atRec_fieldTypes`
   (`mp_fieldTypes_bridge_obj_false`), obligation (B)'s `csubst_recType_eq`
   (`mp_recTypeR_bridge_false`), obligation (C)'s `csubst_iotaRules_eq`
   (`mp_iotaRules_bridge_false`, compared on `VDefEq.type` — there is still no `DecidableEq VDefEq`
   — with `mp_iotaRules_length_eq` to show it is not a length artefact).  So `hp` and `hcl0` are
   load-bearing and §7.5–§7.7 are `np = 0` statements by necessity, not by convenience.

## 21. Where the assembly stops, named — §8 of the new file

`hfld` is closed at both constructors of a parameterised redex block, so §T15.8's three-item
residual for (B)/(C) at `np > 0` loses its second item **at this block**.  What remains, *read off
the signatures* of `VEnv.recConstsR_wf_of_entries` and `VEnv.iotaRulesRS_wf_of_components`:

1. `hsrc` / `hσ` / `he₂` — a **staged environment pair** with `(R.csubst D K).WF E₂ e₂ D.recUvars`.
   `NestedRules.lean` §8.6's `csubst_WF` reduces it to five staging successes, obligation (A)'s
   bridge, and the `val` clause.  **My first draft of this line said "nothing in the tree constructs
   such a pair at any witness"; that is FALSE and I caught it while checking my own §21.**
   `Theory/Typing/ConstSubstNested.lean`'s `nfnSubstAll_WF₂` / `nfnSubstAll_WF₃` are exactly such a
   pair (identified with the general `R.csubst` by `nfn_csubst`), and `nfnAux_recConstsR_wf`
   instantiates obligation (B) off it.  The true statement is narrower and more useful: **`nfnAux`
   has `np = 0`, so (B)/(C) have an instance at a parameterless block and none at any parameterised
   block**, and the residual is *instantiating the `nfnSubstAll_WF` template at `np = 1`* — a
   template that exists — rather than inventing an environment.
2. `hmot` / `hmin` — §T5's and §T6's entry defeqs.  `hmin`'s `hfld` is what this file supplies.
3. `hbody` — a head defeq under the recursor telescope.

Of the `val` clause's residual, `tyVal_hasType_of_faithful` leaves `hsplit` + `hargs`, and
`instAt_indep_of_tyArgs` proves `Faithful` cannot supply `hargs` when the presented head's type
body is closed after splitting.  `MDep`'s **is** closed (`mp_split_body_closed`), so this block is
exactly that configuration — and `mp_hargs` supplies the datum anyway.  So the residual on this
path is `hσ`'s *environment*, and that is once again **apparatus, not proof**: the fourth time this
corner has run out of witness machinery (rows 122b, 129b, and now twice over).

## 22. Measurements, verbatim

* `lake build`: **1505 jobs, exit 0**, zero errors anywhere; zero warnings in the new file.  (1503
  when §11–§17 was written; +1 is `ParamRedex.lean`, +1 is another stream's commit `ecc4602`.)
* `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: **1431 jobs, exit 0**, guards
  **unmoved**:

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

* `lake build Lean4Lean.Verify.Inductive.MemberRedexScan` **after `touch`ing it, i.e. recompiled
  from source rather than replayed**: **1432 jobs**, exit 0, guarded coverage **unmoved** —
  `48 safe blocks with a nested-shaped field, 793 auxiliary constructor fields`,
  `DEFECT … 3 field(s) in 3 block(s) [Lean4Lean.MRedex.MRWit.MJ, Lean.Json, Lean.PrefixTreeNode]`,
  `COVERED by one head-β step … 3`, `RESIDUAL after the repair: 0 in 0 block(s) []`.
  **Why the counts did not move**, since the brief flagged this: `MemberRedexScan.lean` imports
  only `Verify/Inductive/CanonGapMeasure.lean` and `Theory/Inductive/MemberRedex.lean`, and nothing
  imports `ParamRedex.lean`, so `MP` is not in the scanned environment.  That is a fact about the
  import graph, not a loosened guard: `MP` *would* be a fourth defect covered by one head-β step
  (residual still 0) if it were in the cone, and it is not there because I own no file in that cone
  that could import it without changing what the scan measures.
* `scripts/sorry-census.lean`: **TOTAL declarations directly containing sorryAx: 13** — unchanged,
  every entry where it was.  **No `sorry` added, none traded.**  (`ParamRedex.lean` contains the
  string `sorry` zero times; it is not in the census's cone either, since the census imports
  `Experimental/ConeJoin.lean` and I may not edit that file.)
* `#print axioms` on **all 56** theorems of `ParamRedex.lean`: **45** are `[propext, Quot.sound]`,
  **6** are `[propext]` (`mpAuxB_pos`, `mpObj_canonical`, `mp_MP_type_hasType`,
  `mp_MP_constant_wf`, `mp_hbv`, `ntree_canonical_and_parameterised`), **5** depend on none (`mpAuxB_np_one`, `mpAuxB_params`,
  `mpAuxB_params_ne_nil`, `mpAuxB_ctorsAll_eq`, `mpAuxB_blockNames`).  **No frozen axiom, no
  `Classical.choice`, no `sorryAx`.**  Nothing outside the new file changed, so no existing axiom
  set moved.
* **One pre-existing defect observed and not mine**: recompiling `MemberRedexScan.lean` prints
  `PANIC at Lean.Meta.whnfEasyCases … loose bvar in expression` **nine times** during its `#eval`.
  It is non-fatal (all four `throwError` guards pass, exit 0) and it cannot be caused by this round
  — `ParamRedex.lean` is in no import cone of that file.  Not diagnosed, not touched; recorded
  because no previous round's measurements mention it and it looks like the scan calling `whnf` on
  a stored field type that still has loose bvars.

## 23. What I tried that failed, and the step it failed at

1. **`(mrRedex`-style`) NoConsts` term with `MJ`'s nesting** — `⟨⟨trivial, show ``MP ∉ mpK …⟩, trivial⟩`
   was rejected: *"Type mismatch … expected `VExpr.NoConsts mpK ((const MP []).app (bvar 2))`"*.
   `mpRedex`'s inner body is an **application** (`MP #2`, because the own member is now applied to
   the parameter) where `mrRedex`'s is a bare constant, so the conjunction is one level deeper.
   Fixed by adding the layer.  Worth knowing: the redex's *shape* changes with `np`, so `MRWit`
   proof terms do not transplant even when the statements do.
2. **`(a.ClosedN n)` by `decide`** — *"failed to synthesize `Decidable ((VExpr.bvar 1).ClosedN …)`"*.
   `ClosedN` on a `.bvar` is `i < k` under a `Nat` that is not a literal after `simp`, so there is
   no instance.  Fixed with `Nat.lt_succ_self` / `Nat.zero_lt_one`, and the *refutation*
   (`mp_not_tyArgs_closed0`) with `simp [VExpr.ClosedN] at this` — `decide` fails on the negation
   too.
3. **`.constDF hMP nofun nofun rfl .nil` inline inside `HasArgs.cons`** — *"Missing cases: _, _"*,
   twice.  Exactly failure 1 of §15: the level list is a metavariable at that position, so `nofun`
   cannot see it is empty.  Fixed by hoisting the constant typing into a `have` with an explicit
   type — the same fix, in the same place, for the second round running.
4. **Not a failure, but the near-miss worth recording, and it is the same one §15.4 records.**  I
   was briefed that the conversion needed a block that was *both* a redex block and parameterised,
   and I built one.  Only when writing §8 did I check whether the redex half was needed — it is
   not (§20.1), and the check is one `decide` at a witness that has been in the tree since
   `NestedHead.lean` was written.  **The block was still worth building** (the *joint* property is
   real and is what ruling 122e's non-vacuity needs), but "you need a new witness" was half false,
   and I nearly reported it as wholly true.  The pattern is now five for five in this corner:
   every claim of the form "no witness exists" has been narrower than stated.

Not attempted, deliberately: `Built.fields_noK` (out of scope by row 117c); any implementation
file; any frozen file; `Theory/SetModel/*` and `Theory/Equiconsistency.lean` (another stream's);
adding `ParamRedex.lean` to `Experimental/ConeJoin.lean` (not mine to edit).

## 24. Ledger rows this round needs (I did not edit `docs/vacuity-ledger.md`)

1. **A new row for the correction, and it should be graded harder than the achievement.**  Row
   129b's "`hrec` is a genuine conversion only at a block that is BOTH a redex block AND
   parameterised" is **over-conjoined**: `np > 0` alone suffices, measured at the *canonical*
   parameterised witness (`ntree_obj_entry_substC_ne`).  The general reason was already stated
   twice in the tree (`substC_tyApp_comp`, `instAll_tyBody`) and measured once one layer over
   (`ntreeNode_substC_ne_typeR`).  Blindness kind 4, and the guard is specific: **before recording
   "no witness exists", instantiate the statement at every witness in
   `Theory/Inductive/NestedHead.lean` and `DeclExamples.lean` — there are only a handful and each
   test is one `decide`.**
2. **A row for what the new block does establish**: `MRedex.MPWit.mpAux mpAuxNodeB` is the first
   block that is simultaneously a redex block (`mpAuxB_not_canonical`) and parameterised
   (`mpAuxB_np_one`), transcribed from a real Lean declaration and checked against the construction
   (`mpAuxNodeB_built`).  §T15.7's `hrec` is a **conversion** there (`mp_obj_entry_substC_ne`),
   produced from §T16.1 (`mp_hrec_obj`) and closed in a constructed environment
   (`mp_hrec_obj_closed`).  So ruling 122e's layer is now certified non-vacuous **and**
   non-degenerate at one block.
3. **A row for the three refutations**: at `np ≥ 1` the `np = 0` route's *conclusions* are false —
   `substC_atRec_fieldTypes`, `csubst_recType_eq`, `csubst_iotaRules_eq`, each by `decide`.  Anyone
   costing "lift §7.5 off `np = 0`" should read this first: there is nothing to lift, the
   `TeleDefEq` forms are the only ones available, and that is by design.
4. **A row for `hargs`**: `instAt_indep_of_tyArgs` says `Faithful` cannot supply it, and `MDep`'s
   split body is closed so this block is that configuration — yet `mp_hargs` supplies it by hand.
   So the un-derivable residual is *witness-supplyable*, which changes its grade from "open" to
   "data, and we can produce the data".
5. **A row for the residual's new location**: (B)/(C) at `np > 0` stop at
   `hσ : (R.csubst D K).WF E₂ e₂ D.recUvars`.  The witness apparatus for it **exists** at the
   parameterless block `nfnAux` (`nfnSubstAll_WF₂`/`₃`, `nfn_csubst`, `nfnAux_recConstsR_wf`), so
   this is a *template instantiation* at `np = 1`, not missing apparatus — and my own first draft of
   §21 said the opposite, which is the fifth instance in this corner of an over-broad "no witness
   exists" and the second by me in one round.  **Guard: `grep` for `Subst.*_WF` in
   `Theory/Typing/ConstSubstNested.lean` before writing that sentence.**

## 25. What I would pick up first

1. **`(R.csubst D K).WF E₂ e₂ D.recUvars` at `mpAux mpAuxNodeB`**, by instantiating the
   `nfnSubstAll_WF₂`/`₃` template at `np = 1`.  Every part is present: `csubst_WF` reduces it to
   five staging successes + (A)'s bridge + `val`; `csubst_val_cases` +
   `tyVal_hasType_of_faithful` + **`mp_hargs`** (this round) reduce `val`; `QNWit` shows how the
   `addIndTypes` half is built.  Why it is the top item: §20.2 shows the `np = 0` strict route is
   **false** above `np = 0`, and the only `hσ` witness in the tree is at `np = 0`, so **(B) and (C)
   currently have no instance at any parameterised block at all** — a sharper gap than `hargs`
   ever was.
2. **`hmot` / `hbody` at `mpAux mpAuxNodeB`.**  §T16.1's premises came out free here at `k = 0`;
   the motive block needs the same head datum at larger `k`, where `hbv` is `bvars k 1` and the
   lookup is deeper.  Cheap to try, and it would leave `hσ` as the single blocker.
3. **`Built.fields_noK`** — still no producer but `decide` (row 117c).  Untouched for the third
   round.
4. **The `MemberRedexScan` PANIC** (§22, last bullet).  Pre-existing, non-fatal, undocumented.

## 26. Bottom line: the brief's premise is REFUTED, and the repair is proved instead

I was told to *"instantiate the `(R.csubst D K).WF` template at `np = 1`"*, and told to treat
"not new apparatus, just instantiation" as a claim to test.  **It is false.**  The template's
conclusion is not merely unproved at `np = 1` — it is **false**, for every constant substitution,
and the failing clause is not the one anybody was looking at.

| question | answer |
|---|---|
| Does `nfnSubstAll_WF₂` instantiate at `np = 1`? | **No. `(R.csubst D K).WF E₂ F₂ U` is FALSE at `ntreeAux`, for every `U`** — `ntree_csubst_WF₂_false`, two staging equations and a `decide`. |
| Which hypothesis fails? | None of them. The **conclusion's `const` clause** fails. `CSubst.WF.const` demands, of every constant of `E₂` outside σ's domain, that `F₂` hold it at `ci.type.substC σ`; `F₂` holds `NTree.node` at `(typeR …).substC (csubstTy …)`, because that is what `VInductDecl'.ctorConstsCR` declares. **So `const` *is* obligation (A)'s syntactic bridge** — the one `ctorConstsCR_wf_of_substC'` exists because it is false above `np = 0` (`ntreeNode_substC_ne_typeR`, in the tree since it was written). (A) was given a defeq-tolerant bridge; (B) was too (§A of `ConstSubstNested.lean`) but **kept the strict `hσ`**, which re-imposes (A)'s refuted equation through the back door.  (C)' dropped `hσ` entirely, so what is refuted is (B)' and the *strict* (C) route. |
| Is it a matter of picking a better σ? | **No.** `ntree_node_no_substC`: for *every* `σ`, the two differ. `substC` replaces a constant in **head** position, so the third pi-domain of the stored type is `.app t (.bvar 1)` for whatever `t`, while the declared one is `.app (const List) (.app (const NTree) (.bvar 1))`. Matching them needs `substC` to re-associate an application. |
| Is it an artefact of the canonical witness `ntreeAux`? | **No** — the same inequality holds at the parameterised **redex** block: `mp_const_clause_ne` (`ParamRedex.lean` §10), and there the right-hand side is `type_of% @MP.obj`, i.e. what Lean's own kernel declares. |
| Is there a cheap repair by changing what the step declares? | **Refuted**: `ntree_node_redex_ne_declared` — the substituted stored type is **not** `type_of% @NTree.node`, so that repair buys (B) by giving up faithfulness (`ntreeNode_typeR` is `rfl` against Lean's own type). |
| So what does work? | **`CSubst.WFD`**: `CSubst.WF` with `const` weakened to "at that type **or at any type definitionally equal to it**". `CSubst.WF.wfd` shows it is a weakening (so it inherits every `np = 0` instance), and `VEnv.IsDefEq.substCD` is the same induction as `IsDefEq.substC` with **one** case changed in substance (`constDF`, one extra `defeqDF`). |
| Is `WFD` inhabited where `WF` is refuted? | **Yes, proved**: `ntree_csubst_WFD₂ : (ntreeRestore.csubst ntreeAux ntreeK).WFD E₂ F₂ 2` — the corrected `hσ` at a **parameterised** block, every clause discharged. Exactly one clause uses the new freedom (`const` at `NTree.node`); the other six constants take the old disjunct verbatim. |
| Does that move obligation (B)? | **Yes.** `ntreeAux_recConstsR_wf_of_bridge`: (B) at `ntreeAux` now follows from **`hbridge` alone** — `hsrc` (`ntree_recConsts_wf`), `hσ` (`ntree_csubst_WFD₂`) and `he₂` (`ntreeF₂_ordered`) are all discharged. The environment-level residual §21/§25 named is **gone**; what remains is the telescope bridge (§T5/§T6/§T15's `hmot`/`hmin`/`hbody`). |
| New `sorry`? New frozen axiom? | **None.** All **46** new theorems (47 declarations; the 47th is the `structure CSubst.WFD`) are `[propext, Quot.sound]` or a subset, except six that also carry `Classical.choice` — and those six are exactly the ones that go through `listEnv_ordered`/`ntreeAux_ctorConstsCR_wf`, which **already** carry it (`nfnSubstAll_WF₂` does too). No `sorryAx` anywhere. |

### 26.1 Verdict on each thing the brief asserted (it asked to be checked)

| briefed assertion | verdict |
|---|---|
| `ParamRedex.lean` landed a parameterised redex block at which `hrec` is a genuine conversion (`mp_obj_entry_substC_ne`, `decide`) | **true** — file rebuilds, theorem is `by decide`, §T15.7/§T16.1 assembly present |
| (B)'s `csubst_recType_eq` and (C)'s `csubst_iotaRules_eq` are **false** at `np ≥ 1` | **true** (`mp_recTypeR_bridge_false`, `mp_iotaRules_bridge_false`) |
| the `np`-free route "stops at" `hσ : (R.csubst D K).WF E₂ e₂ D.recUvars` | **true but understated**: it does not stop there, it is **refuted** there |
| `nfnSubstAll_WF₂`/`₃` + `nfn_csubst` + `nfnAux_recConstsR_wf` construct such a `WF` at `np = 0` | **true** |
| "so the residual is instantiating that template at `np = 1`, not new apparatus" | **FALSE** — the headline correction; see §26.  New apparatus (`CSubst.WFD` + `substCD`) is exactly what is needed, and it is now here |
| `np > 0` alone gives the conversion, redex-ness orthogonal (row 132b) | **true**, unchallenged (`ntree_obj_entry_substC_ne` in the tree) |
| guard 1 = 24 frozen axioms, guard 3 = 2/2, guard 2 prints INCOMPLETE | **true, all three verified verbatim this round** |
| census TOTAL 13 and `MemberRedexScan` 49/796/4/4/0 | **could not be verified** — see §30; both instruments are unrunnable while `Theory/SetModel/*` is broken |
| `lean_local_search` / `lean_hammer_premise` broken in this tree | **not exercised** (I used `grep` and `lake env lean`).  **One caveat to add**: `lean_run_code` also became unusable after my first edit — *"Imports are out of date and must be rebuilt"* — with no way to restart the LSP from a Bash-only session.  `lake env lean` on a scratch file under `/tmp` is the working substitute and is what every measurement here used |
| out of scope: `Built.fields_noK` | respected, untouched |

## 27. What is proved

### 27.1 `Theory/Typing/ConstSubstNested.lean` §B — the refutation (8 theorems)

* `VEnv.subst_WF_false_of_const_ne` — **the minimal form**: one constant carried at a different
  type refutes `σ.WF E F U` outright, because `const` is an *equation*.  Four lines; everything
  else in §B is this plus a computation.
* `VEnv.csubst_WF_staged_false` — **general**: at the staging pair `E₂ = E₁.addIndCtors D`,
  `F₂ = F₁.addConstList (D.ctorConstsCR R K)` (the pair `VEnv.addInductR_ordered'` fixes), if one
  *declared* constructor has `(C.type D j).substC σ ≠ (C.typeR D R j).substC (R.csubstTy D K)`
  then `¬ σ.WF E₂ F₂ U`.  Two `addConstList_constants` and one `injection`; no `Ordered`, no `np`.
* `ntree_const_clause_ne` (`decide`) — that inequality at `NTree.node`, with the *full*
  substitution on the left and the type `ctorConstsCR` really declares on the right.
* `ntree_node_no_substC` — …and for **every** `σ`, by peeling the pi-telescope.
* `ntree_csubst_WF₂_false`, `ntree_any_WF₂_false` — the two instances, at every `U` (in
  particular `U = ntreeAux.recUvars = 2`).
* `ntree_csubst_WF₃_false` — the same refutation at the **ι-rule stage** `E₃`/`F₃`, which is where
  the *strict* (C) route `iotaRulesRS_wf_of_substC` asks for `hσ`.  (C)'s defeq-tolerant route has
  no `hσ`, so (C) is blocked on one route of two, not both.
* `ntree_stage₂_exists` — the staging pair the refutation is about **exists** (anti-vacuity: the
  refutation is not about an empty configuration).

### 27.2 §C — the repair, as apparatus (1 structure + 9 theorems)

`CSubst.WFD` (structure), `CSubst.WF.wfd` (the weakening), `IsDefEq.substCD_constDF`,
`IsDefEq.substCD_extra`, `IsDefEq.substCD`, `HasType.substCD`, `IsType.substCD`,
`VConstant.WF.substCD`, `VDefEq.WF.substCD`, `VEnv.recConstsR_wf_of_substCD'`.

`substCD`'s induction is `substC`'s **byte for byte** except two lines: `constDF`, which gains one
`defeqDF`, and `extra`, which only names a renamed helper whose proof is identical.  That is the
measurement that this is a weakening and not a new system.  `Theory/Typing/ConstSubst.lean` is
another stream's file, so `WFD` lives in `ConstSubstNested.lean`; **if it survives, it belongs next
to `CSubst.WF`, and `recConstsR_wf_of_blocks`/`_of_entries` in `NestedTele.lean` want the same
restatement** (they factor through `recConstsR_wf_of_substC'`, so it is one hypothesis swap each).

### 27.3 §D — the instance at `np = 1` (22 theorems)

`ntree_csubst_closed`, `ntree_csubst_ne`, `ntree_csubst_fresh`; **`ntree_node_const_defeq`** (the
datum `WF` cannot have: `typeR` and the redex form are definitionally equal in `F₂` at every level
instantiation — one `IsDefEq.beta` under two `forallEDF`s); the five constant-typing helpers and
the three value typings `ntreeVal_hasType` / `nlistNil_val_hasType` / `nlistCons_val_hasType` (the
last two are `defeqDF` through the β-redexes, which is where `np = 1` costs something);
`ntreeF₁_ordered`, `ntreeF₂_ordered` and the five `F₂` lookups; **`ntree_csubst_WFD₂`**;
`ntree_node_redex_ne_declared`; `ntree_recConsts_wf`; **`ntreeAux_recConstsR_wf_of_bridge`**.

### 27.4 `Theory/Inductive/ParamRedex.lean` §10 (5 theorems)

`mp_const_clause_ne` (`decide`, against `type_of% @MP.obj`), plus the other four hypotheses of
`VEnv.csubst_WF_staged_false` at `MP.obj` (`mp_ctorName_id`, `mp_own_not_K`,
`mp_csubst_obj_none`, `mp_obj_mem`).  The combined refutation is *stated* at `ntreeAux` and not at
`MP`, because `mpAux mpAuxNodeB` has no `VInductDecl'.WF` and hence no staging pair; `ntreeAux`
has one, through `listDecl_WF`.  (I did **not** add an import of `ConstSubstNested.lean` to
`ParamRedex.lean` — `ConeJoin.lean` imports `ParamRedex.lean`, so that would change the census's
and the scan's cone, and I may not edit `ConeJoin.lean`.)

## 28. Anti-vacuity, per obligation, as the brief demanded

| statement | genuine conversion content, or identity/typing? | established by |
|---|---|---|
| `ntree_const_clause_ne` / `ntree_node_no_substC` | a **refutation**; the two sides differ by one β step per parameter | `decide`, and a structural `injection` argument for the `∀σ` form |
| `ntree_node_const_defeq` | **genuine conversion**: its proof *is* an `IsDefEq.beta`, and `ntree_node_no_substC` proves the two sides are never equal, so it cannot be a `rfl` in disguise | the two theorems together |
| `ntree_csubst_WFD₂`'s `const` clause | **one** of seven constants takes the defeq disjunct; the other six take the strict one | the proof's case split, and `ntree_csubst_WF₂_false` shows the defeq disjunct is *necessary* |
| `nlistNil_val_hasType` / `nlistCons_val_hasType` | **conversion**: each is `defeqDF` through one (resp. two) `IsDefEq.beta`s; at `np = 0` the analogous obligations are `CSubst.val_zero' … (by type_tac)` with no defeq at all (`nfnSubstAll_WF₂`) | compare the two proofs |
| `CSubst.WF.wfd` | an **identity** instance, deliberately: it is the theorem that `WFD` costs nothing at `np = 0` | `.inl rfl` |
| `ntreeAux_recConstsR_wf_of_bridge` | not vacuous in `hσ` any more; **still hypothetical in `hbridge`**, which I did **not** prove and do not claim | stated as a hypothesis, named |

**The one thing I could not close and will not dress up**: `hbridge` at `ntreeAux`.  (B) is now
"telescope defeqs ⇒ done" at a parameterised block, and the telescope defeqs are §T5/§T6/§T15's
business.  `mp_recTypeR_bridge_false` and `ntreeNode_substC_ne_typeR` say the *equation* form is
false there, so **the correct `np ≥ 1` form of `csubst_recType_eq` is not a patched equation: it is
`hbridge`, a telescope defeq**, and that answers the brief's second question — (B)'s and (C)'s
`np ≥ 1` forms are the primed bridges' `hbridge`/`hbridge`-analogue, not a repair of the equations.
(C)'s `iotaRulesRS_wf_of_substC'` already has **no** `hσ` at all — §A's note explains why — so
**(C)'s defeq-tolerant route never had this blocker**; (B) and the *strict* (C) route did, and
`ntree_csubst_WF₃_false` measures the latter.  That is a correction to
§21's list: of its three residual items, item 1 was two-thirds mine to fix and one-third not there.

## 29. What I tried that failed, and the step it failed at

1. **Instantiating `nfnSubstAll_WF₂` at `ntreeAux` directly, as briefed.**  Failed at the `const`
   clause, and *before* writing any proof: computing what `F₂` holds for `NTree.node` and what the
   clause demands showed they were the two sides of `ntreeNode_substC_ne_typeR`, a theorem sitting
   30 lines below in the same file.  **This is the fourth "the residual is just an
   instantiation" in this corner that was wrong** (rows 128c, 129c, 132b), and the first where the
   claim was wrong in the *pessimistic-for-the-tree* direction: the residual was **bigger** than
   briefed, not smaller.  The cheap check that would have caught it: *for each clause of the
   template's conclusion, write down what the two environments actually hold at each constant.*
2. **`∀ σ, ¬ σ.WF E₂ F₂ U` with no side condition** — **false as stated**, and I nearly landed it.
   If `σ` substitutes `NTree.node` itself the `const` clause does not apply and the `val` clause
   might conceivably be met.  The honest statement carries `σ NTree.node = none`, which every
   substitution the nested step could mean satisfies (`R.csubst` is guarded by `K`).  Caught by
   the `?_` that would not close.
3. **`decide` on `(0, ntreeNode) ∈ ntreeAux.ctorsAll`** — *"failed to synthesize `Decidable`"*.
   `ctorsAll` is a `flatMap` over `zipIdx`, so membership is not an instance target; fixed with
   `rw [show ctorsAll = … from rfl]; exact List.Mem.head _` (the same fix `ParamRedex.lean` uses).
4. **`.sortDF … : … (.sort ?u)` inside `forallEDF` inside `defeqDF`** — *"expected `VLevel.WF 1 ?m`"*
   twice.  The result level is unconstrained when the whole defeq sits under `defeqDF`, so the
   `sortDF`'s own level is a metavariable; fixed with `(l := …) (l' := …)`.  **Third round running
   that a `VLevel` metavariable in a `constDF`/`sortDF` position is the failure** (§15.1, §23.3).
5. **Doc-comment between `include … in` and `theorem`** — a parse error; in this file the order is
   `include … in` **then** the doc comment.  And a regex that moved two `include` lines to the top
   of the file, which broke obligation (A)'s statement for one build; caught by the build, reverted.
6. **Not attempted, deliberately**: `Built.fields_noK` (out of scope, row 117c); restating
   `recConstsR_wf_of_blocks`/`_of_entries` over `WFD` (`NestedTele.lean` is mine, but the
   restatement is mechanical and the *interesting* content is `WFD` itself — and I would rather
   the human decide whether `WFD` belongs in `ConstSubst.lean` first); any implementation or frozen
   file; `Theory/SetModel/*` and `Theory/Typing/*` other than `ConstSubstNested.lean`.

## 30. Measurements, and what I could NOT measure

* `lake build`: **1506 jobs**, and it **fails throughout the round in `Theory/SetModel/*` only** —
  another stream's files, mid-flight, and the failing file moved three times while I worked
  (`AboveAudit.lean` + `UnitOracleWitness.lean`, 34 errors → `UnitOracleLarge.lean`, 14 →
  `PreludeOracle.lean`, 61).  **Zero errors in any file I own, at every one of those snapshots**;
  `lake build Lean4Lean.Theory.Typing.ConstSubstNested` and
  `lake build Lean4Lean.Theory.Inductive.ParamRedex` are green (64 and 72 jobs), with **no new
  warnings** — the only warning either file emits is the pre-existing unused-section-variable one at
  `ConstSubstNested.lean:1164` (`nfnF₂_ordered`, untouched).
* `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: the **guards ran and are
  unmoved**, verbatim —

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

  The build as a whole still exits non-zero, on `Theory/SetModel/UnitOracleLarge.lean` (another
  stream's file, mid-flight); the three guard lines are emitted before that target fails.
* **`scripts/sorry-census.lean` and `MemberRedexScan`'s coverage could NOT be run**, and this is the
  one place I cannot give the brief what it asked for.  Both transitively import the broken
  `Theory/SetModel/*` file of the moment, so both die with *"object file … .olean … does not
  exist"* — three different filenames over the round, as the other stream moved.  I did **not** work around it, did not touch those files, and did not weaken anything to
  make a number appear.  **What must be re-run once the SetModel stream is green:**
  `lake env lean scripts/sorry-census.lean` (expect TOTAL 13) and
  `touch Lean4Lean/Verify/Inductive/MemberRedexScan.lean && lake build
  Lean4Lean.Verify.Inductive.MemberRedexScan` (expect 49 / 796 / 4 defects in 4 blocks / 4 covered /
  residual 0).  My grounds for expecting both unmoved, stated as reasoning and **not** as
  measurement: I added no `sorry` (the string does not occur in either file I touched), no axiom,
  no implementation file, and no import — the scan's population is fixed by
  `ConeJoin.lean`'s import list, which I did not edit.
* `#print axioms` on **all 46** new theorems (47 new declarations, the 47th being the `structure`):
  **40** `[propext, Quot.sound]` or a subset (2 on none at all), **6** also `Classical.choice` — `ntreeF₁_ordered`, `ntreeF₂_ordered`, `ntree_csubst_WFD₂`,
  `ntree_recConsts_wf`, `ntreeAux_recConstsR_wf_of_bridge`, and (through `listEnv_ordered`) nothing
  else.  Those six route through `listEnv_ordered` / `ntreeAux_ctorConstsCR_wf`, **measured to
  carry `Classical.choice` already**, as does the template `nfnSubstAll_WF₂`.  **No frozen axiom,
  no `sorryAx`, none traded.**
* Search-tool provenance, per the brief's caveat: `lean_local_search` and `lean_hammer_premise`
  were **not used** (broken in this tree).  Everything located here came from `grep`/`sed` over the
  tree and from `lake env lean` on scratch files; `lean_run_code` returned
  *"Imports are out of date"* after my first edit and I switched to `lake env lean` for the rest.

## 31. Ledger rows this round needs (I did not edit `docs/vacuity-ledger.md`)

1. **A row that supersedes 132b's last sentence.**  132b records "the residual is *instantiating
   that template at `np = 1`*, not new apparatus".  **Refuted**: the template's conclusion is
   **false** at `np = 1` (`ntree_csubst_WF₂_false`), for every substitution
   (`ntree_node_no_substC`), and the failing clause is `CSubst.WF.const`, which *is* obligation
   (A)'s refuted syntactic bridge.  Grade this harder than the two achievements below: it is the
   fifth costing in this corner refuted by a check that cost three lines, and the **first** in the
   direction "the residual is larger than briefed".  *Guard:* before recording a residual as
   "instantiate template T at witness W", write down, for each clause of T's **conclusion**, what
   the two environments hold at each constant.  A hypothesis-by-hypothesis audit would have missed
   this — the hypotheses are all fine.
2. **A row for the general obstruction**: `VEnv.csubst_WF_staged_false`.  `CSubst.WF` between the
   two staging environments of `addInductR_ordered'` is unsatisfiable as soon as one declared
   constructor's stored type is not literally its restored type under σ — so **every** consumer
   with a strict `hσ` (`recConstsR_wf_of_substC'`, `_of_blocks`, `_of_entries`, and the strict (C)
   route) is **vacuous at every parameterised block**, while §A.1 was checking only that their
   `hbridge` was not.  *This is a new kind for §0's list: a lemma non-vacuous in the hypothesis
   everyone audited and vacuous in the one nobody did.*
3. **A row for the repair**: `CSubst.WFD` + `IsDefEq.substCD` (one case changed in substance out of fifteen) +
   `ntree_csubst_WFD₂`, the corrected `hσ` **proved at a parameterised block**, and
   `ntreeAux_recConstsR_wf_of_bridge`, which reduces obligation (B) at `ntreeAux` to `hbridge`
   alone.  Also worth a line: the *other* candidate repair (declare the substituted stored type)
   is refuted by faithfulness, `ntree_node_redex_ne_declared`.
4. **A row for (C)**: `iotaRulesRS_wf_of_substC'` has **no** `hσ`, so obligation (C) never had this
   blocker; §21's three-item residual over-counted.  (C)'s `np ≥ 1` form is its `hbridge`, and it
   needs `htype` — data the strict route never had to produce (§A.1's own note).
5. **A row for the measurement outage**: the census and `MemberRedexScan` were unrunnable this
   round because they transitively import `Theory/SetModel/UnitOracleLarge.lean`, which another
   stream had left broken (and before that, `AboveAudit.lean`); the guards ran only because their
   output precedes the failing target.  **Every stream's verification block depends on every other stream's
   file compiling**, and no instrument warns you of that before you have finished the work.

## 32. What I would pick up first

1. **`hbridge` at `ntreeAux`** — obligation (B)'s last input at a parameterised block, and now its
   *only* one.  Feed `recConstsR_wf_of_blocks`/`_of_entries` (restated over `WFD` — one hypothesis
   swap each) with §T5's `substC_motiveType_defeq'`, §T6's `substC_minorType_defeq` (whose `hfld`
   `ParamRedex.lean` §5 supplies) and `hbody`.  This is now the *whole* of (B) at `np ≥ 1`.
2. **Decide where `CSubst.WFD` lives.**  It belongs beside `CSubst.WF` in
   `Theory/Typing/ConstSubst.lean` (another stream's file).  Better still: ask whether `CSubst.WF`
   should simply *be* `WFD` — nothing in the tree needs the strict `const`, `CSubst.WF.wfd` shows
   the `np = 0` witnesses survive, and the strict version is provably unusable at `np ≥ 1`.
3. **Re-run the census and the scan** once `Theory/SetModel/UnitOracleLarge.lean` compiles (§30
   lists the commands and the expected numbers).  Do not take my expectations on trust.  The three
   guards *did* run and are unmoved.
4. **`Built.fields_noK`** — still no producer but `decide` (row 117c), fourth round untouched.
