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
