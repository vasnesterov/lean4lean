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

## 33. The brief's premise is REFUTED again: `hbridge` was ALREADY discharged in HEAD

I was briefed to *"discharge `hbridge`"*, told that *"`hbridge` is NOT discharged and no handoff
section was written, so treat none of it as a completed result — read it, verify it does what its
names suggest, and say so if it does not"*.  **It does more than its names suggest.**  Commit
`8867876` ("salvage 503 green lines … hbridge is NOT discharged") in fact salvaged the *whole* of
§E: `rhbridge` — `hbridge` at both recursors of `ntreeAux` — and
`ntreeAux_recConstsR_wf`, i.e. **obligation (B) discharged at a parameterised nested block**, plus
§F's measurement of what (C) needs.  The crashed stream died *after* landing its result and
*before* writing its handoff; the commit message describes only the apparatus (`rV`, `rbetaL`, …)
because that is all its author could see in the diff summary.

Verified, not read off:

| check | result |
|---|---|
| `lake build Lean4Lean.Theory.Typing.ConstSubstNested` at HEAD | **green, 64 jobs**, one pre-existing unused-section-variable warning at `:1164` |
| `grep sorry` in `ConstSubstNested.lean` / `ParamRedex.lean` / `NestedTele.lean` | **zero occurrences** |
| `#print axioms rhbridge` | `[propext, Quot.sound]` |
| `#print axioms ntreeAux_recConstsR_wf` | `[propext, Classical.choice, Quot.sound]` — the `Classical.choice` is inherited from `listEnv_ordered`/`ntree_csubst_WFD₂`, measured in §30 as already there |
| `#print axioms rTeleDefEq`, `ntree_csubst_WFD₂`, `ntree_stage₂_exists`, `recConstsR_wf_of_substCD'` | `[propext, Quot.sound]` (+`Classical.choice` for `WFD₂`) |

**So the first item of §32's pick-up list was already done when I was handed it.**  That is the
sixth refuted costing in this corner and the second in the "smaller than briefed" direction.
*Guard, for the orchestrator:* a crashed stream's commit message is written from the diff by
someone who did not do the work — before briefing the next stream on "what is left", `#print
axioms` the target theorem and see whether it exists.  That check cost two minutes here and would
have redirected the whole round.

### 33.1 What I added: (B) with no hypotheses left (§G)

`ntreeAux_recConstsR_wf` is hypothetical in five staging equations, and "hole-free is not
discharged" applies to it exactly.  `ntree_stage₂_exists` (§D, already in the tree) supplies those
five.  **`InductiveDeclExamples.ntreeAux_obligationB`** composes them, so obligation (B) at the
parameterised block now holds with **nothing assumed** — the (B) counterpart of
`ntreeAux_obligationA`.  Green, `[propext, Classical.choice, Quot.sound]`, no new hypothesis.

### 33.2 The correction that matters most: (C) **was** blocked by the refuted `hσ`, one layer down

The brief handed me a standing correction to record and act on:

> **(C)′ has no `hσ` at all**, so (C) was never blocked by the `csubst` residual and my earlier
> three-item residual count over-counted.

**True of the bridge, false of the route, and the difference is the whole of (C)'s cost.**
`VEnv.iotaRulesRS_wf_of_substC'` and `VEnv.iotaRulesRS_wf_of_components` indeed carry no `hσ`
(verified: `#check`, and `iotaRulesRS_wf_of_components` has *no* environment hypothesis whatever).
But every **producer** of the components it consumes does carry it, at exactly the pair
`ntree_csubst_WF₃_false` refutes:

| statement (`Theory/Inductive/NestedTele.lean`) | § | hypothesis |
|---|---|---|
| `VInductDecl'.iotaCtx_substC_onCtx` — advertised in §T15.4 as *"a cheaper route, and it is free"* | T15.4 | `hσ : σ.WF env e D.recUvars` |
| `VIndRestore.substC_iotaLam_defeq` | T16.3 | same |
| `VIndRestore.substC_iotaRhs_defeq` | T16.3 | same |
| `VIndRestore.substC_iotaLhsPre_hasType` | T16.5 | same |
| `VIndRestore.substC_iotaLhs_defeq_of_hargs` | T16.4/5 | same |
| `VIndRestore.substC_iotaLhs_defeq_of_conv` | T16.7 | same |
| `VIndRestore.iotaRule_components_of_hargs` — **the** composed (C) statement | T16.8 | same |

Seven, found by `grep -rn` over `Lean4Lean/Theory/{Inductive,Typing}` for `σ.WF`-shaped
hypotheses (tool provenance: `grep`; `lean_local_search` and `lean_hammer_premise` are broken in
this tree as briefed — I did not use them, and `lean_references`-equivalent evidence is the `grep`
consumer scan reported in §33.4).  None of the seven is *literally* vacuous — `env`/`e` are free
variables, so `env = e`, `σ = id` satisfies them — but **at the configuration obligation (C) needs**
(`env` the block environment, `e` the declared one, `σ = R.csubst D K`) `hσ` is refuted at every
parameterised block.  §T16.9's instrument-7 audit walked every hypothesis of these statements
**except `hσ`**, which is the same failure mode §31 item 2 named for (B) — *"non-vacuous in the
hypothesis everyone audited and vacuous in the one nobody did"* — recurring at a different lemma
in the same file, and this time at the one labelled *free*.

So §21's residual list did **not** over-count for (C); it mis-*located* the item.  My brief was
wrong in the optimistic direction here, and this is the answer to "tell me plainly where I am
wrong".

### 33.3 The repair, landed: (C)'s whole route over `CSubst.WFD`

`Theory/Inductive/NestedTele.lean`, **10 new declarations**, all green:

* **§T1a** — `VEnv.OnCtx.substCD`, `VEnv.HasArgs.substCD`, `VEnv.OnCtx.substCD_tele`: §T1's
  transports over `WFD`.
* **§T15.4** — `VInductDecl'.iotaCtx_substC_onCtxD`: (C)'s `hOn`, free *and* non-vacuous.
* **§T16.11** — `VIndRestore.substC_iotaLhsPre_hasTypeD`, `substC_iotaLhs_defeq_of_convD`,
  `substC_iotaLam_defeqD`, `substC_iotaRhs_defeqD`, and **`iotaRule_components_of_hargsD`**: the
  whole §T16 chain for (C), so obligation (C) at `D.np ≥ 1` now stands on a hypothesis a
  parameterised block can actually meet.
* **§T16.11a** — `VIndRestore.IotaHargs` (the per-rule data, bundled) and
  **`VEnv.iotaRulesRS_wf_of_hargsD`**: the composition §T16.10 asserts *in prose* and never wrote.
  Writing it mattered: `hT`/`hj`/`hC` are **derived** from `hqC` (`VInductDecl'.mem_ctorsAll` +
  a `getElem?` bound), which a prose composition hides, and `iotaRule_components_of_hargs` turns
  out to have had **no consumer anywhere in the tree** — every other occurrence of the name is
  prose (`grep`).  So the top of (C)'s assembly had never been connected to `iotaRulesRS`.
* **§T16.12** — `rIotaComp`, `ntreeAux_ctorsAll_eq`, **`ntreeAux_iotaRulesRS_wf_of_nine`**:
  obligation (C) at `ntreeAux` reduced, **with nothing assumed**, to nine concrete conversions.

Each of the five §T16.11 statements is its original with `HasType.substCD` / `OnCtx.substCD` in
place of the strict transport and nothing else changed — the same measurement §27.2 offered for
`substCD` itself.  `CSubst.WF.wfd` carries every `D.np = 0` instance over unchanged, so nothing is
lost; and the weakening is used by exactly one clause at exactly one constant
(`ntree_csubst_WFD₂`'s `NTree.node`), which is the brief's "a weakening everything suddenly
satisfies is suspect" check, answered: **one** instance uses the slack, six take the old disjunct.

### 33.4 §H: the recursor-type conversion in `WFD.const`'s shape — and a costing of my own, refuted

`Theory/Typing/ConstSubstNested.lean` §H, **10 new declarations**.  Obligation (C)'s §T16 route
needs `(R.csubst D K).WFD E₃ F₃ ntreeAux.recUvars`, the ι-stage counterpart of §D.5.  Measured
(not read off), stage 3 adds exactly **two** clauses §D.5 did not have:

    ntreeAux.recConsts             = [(NTree.rec, ⟨2, recType 0⟩), (_nested.List_1.rec, ⟨2, recType 1⟩)]
    ntreeAux.recConstsR R K        = [(NTree.rec, ⟨2, (recTypeR 0).substC σ⟩), (NTree.rec_1, ⟨2, (recTypeR 1).substC σ⟩)]
    σ NTree.rec = none,  σ _nested.List_1.rec = some (const NTree.rec_1 [param 0, param 1])

(both list equations `rfl`: `ntree_recConsts_eq`, `ntree_recConstsR_eq`; the two `σ` values `rfl`.)
So `NTree.rec` needs `const`'s **defeq** disjunct — `ntree_recTypeR_bridge_false_0` refutes the
strict one — and `_nested.List_1.rec` needs the `val` clause, which at stage 2 was discharged by
`exfalso` because the constant was not yet in `E₂`.

**I costed the `const` clause at ~200 lines of level-generic rewrite of §E, and that was wrong.**
`WFD.const` asks for the defeq *at every level instantiation and in every context*, and both
generalisations are already theorems: `VEnv.IsDefEq.instL` and `VEnv.IsDefEq.weak0`
(`Theory/Typing/Lemmas.lean`).  So the work is: glue `rhbridge`'s two halves into one whole-pi
defeq with `IsDefEq.mkPi_congrU`, then `instL`, then `weak0`.  What that gluing needs over
`rhbridge` is exactly one new input — `OnCtx rTele.reverse (F.IsType 2)` — and **five of its six
entries come free from §E's own `rE2`/`rE3`/`rE4`/`rE5` via `IsDefEq.hasType`**, leaving two
one-liners.  Landed:

* `rIsTypeA0`, `rIsTypeA1`, **`rOnCtx`** — §H.1, the recursor telescope is a context;
* **`rRecPi0`**, **`rRecPi1`** — §H.2, the whole-pi conversions at both recursors, at `Γ = []`;
* **`rRecConstClause0`**, **`rRecConstClause1`** — §H.3, the same level- and context-generic, i.e.
  literally `CSubst.WFD.const`'s right disjunct;
* **`rNestedRecVal`** — §H.4, the `val` clause's datum at `_nested.List_1.rec ↦ NTree.rec_1`: one
  `constDF` plus one `defeqDF` along §H.3;
* `ntree_recConstsR_eq`, `ntree_recConsts_eq` — §H.5, the anti-vacuity certificates above.

**This is the third mis-costing of the round and the second of mine**: a generalisation assumed to
need new mathematics when the transport lemma was already in the tree.  The cheap check that
catches it: before pricing a "generic in X" version, `grep` for `instL`/`weakN`/`weak0` on the
judgement you already have.

### 33.5 Measured, not read off

| quantity | value | how |
|---|---|---|
| `ntreeAux.ctorsAll` | `[(0, NTree.node), (1, _nested.List_1.nil), (1, _nested.List_1.cons)]` | `rfl` (`ntreeAux_ctorsAll_eq`) |
| (C)'s rule count / uvars | 3 rules, all `uvars = 2` | `rfl` / `decide` (pre-existing §F) |
| ι-context lengths, per rule | **8, 6, 8** | `#eval` |
| (C)'s nine components, `esize` (source-substituted) | type 117/107/125, lhs 129/119/137, rhs 253/205/273 | `#eval` with a local `esize` |
| (C)'s nine components, `esize` (registered) | type 93/83/97, lhs 105/95/109, rhs 205/165/225 | `#eval` |
| (B)'s whole substituted recursor type, for scale | 103 (`j = 0`), 109 (`j = 1`) | `#eval` |
| all nine (C) components move | yes | `decide` (pre-existing `ntree_iota_components_ne`) |
| statements carrying the refuted `σ.WF` on (C)'s route | **7** | `grep` |
| consumers of `iotaRule_components_of_hargs` before this round | **0** (prose only) | `grep` |

§F's "83–273 against 93–253" is close but mispaired; the table above is the measurement.  **(C) is
about 3× (B)'s job on terms 1.2–2.6× the size, and none of the nine is free.**

Per-module builds, this round's final state — **no tree-wide build, no guards, no census, no
`MemberRedexScan`**, as instructed (another stream is mid-flight in `Theory/SetModel/*`; it
committed `InstDescendBvar.lean` while I worked, and HEAD moved under me twice):

    lake build Lean4Lean.Theory.Typing.ConstSubstNested                → 64 jobs, green
    lake build Lean4Lean.Theory.Inductive.NestedTele                   → 69 jobs, green
    lake build …NestedTele …ConstSubstNested …ParamRedex (together)     → 72 jobs, green

Diff for the round: `NestedTele.lean` +305, `ConstSubstNested.lean` +172, this document +313; no
other file touched, nothing deleted.

The only warning any of the three emits is the pre-existing unused-section-variable one at
`ConstSubstNested.lean:1164` (`nfnF₂_ordered`), untouched.  `grep -c sorry` = **0** in both files I
edited.  `#print axioms` on **all 25** declarations added (23 theorems plus the two
`Prop`-valued defs `VIndRestore.IotaHargs` and `rIotaComp`): 18 are `[propext, Quot.sound]` or a
subset (three on `[propext]` alone, one on none at all), 7 also carry `Classical.choice` — and every one of
those 7 inherits it from a pre-existing lemma measured to carry it already
(`iotaLhsPre_hasType`, `iotaLamBody_hasType`, `listEnv_ordered`, `ntree_csubst_WFD₂`; the
non-`D` counterparts `substC_iotaLhsPre_hasType`, `iotaRule_components_of_hargs`,
`iotaCtx_substC_onCtx` print the identical axiom set).  **No frozen axiom, no `sorryAx`, none
traded, no new `sorry`.**  `ParamRedex.lean` was **not edited** this round.

### 33.6 Anti-vacuity, per obligation, to the standard the brief set

| statement | genuine conversion content, or identity/typing? | established by |
|---|---|---|
| `rhbridge` (inherited, verified) | **genuine**: four of six telescope entries move by one β step each, the `j = 1` body moves, and the *equation* form is false at both recursors (`ntree_recTypeR_bridge_false_0/_1`) | the `decide`s in §E.5, re-run this round as part of the module build |
| `ntreeAux_obligationB` (new, §G) | **not an identity, and no longer hypothetical**: the conversion content is `rhbridge`'s, and the five staging hypotheses are discharged by `ntree_stage₂_exists` | composition; `#print axioms` |
| `rRecPi0` / `rRecPi1` (new, §H.2) | **genuine**: each *is* `mkPi_congrU` over four moving entries, and the strict equation is refuted at the same pair | `ntree_recTypeR_bridge_false_0/_1` + the derivation |
| `rRecConstClause0/1` (new, §H.3) | **the same content**, transported: `instL` + `weak0` add no conversion but are what makes it usable as `WFD.const` | `IsDefEq.instL`, `IsDefEq.weak0` |
| `rNestedRecVal` (new, §H.4) | **conversion**: one `defeqDF` along §H.3 — at `np = 0` the analogous `val` obligation is `CSubst.val_of_hasType` with no defeq at all (`nfnSubstAll_WF₃`) | compare the two proofs |
| `rOnCtx`, `rIsTypeA0`, `rIsTypeA1` (new, §H.1) | **typings, not conversions** — reported as such: five of six entries are `IsDefEq.hasType` of §E's existing defeqs, so this is bookkeeping | the proof is five projections and two one-liners |
| the six `WFD` restatements (§T1a, §T15.4, §T16.11) | **weakenings, deliberately**: each is its original with one transport swapped, and `CSubst.WF.wfd` shows nothing is lost at `np = 0`. **Not another identity instance** — they change which blocks can satisfy the hypothesis, which is measured: `σ.WF` is *refuted* at both parameterised staging pairs and `WFD` is *proved* at one of them | `ntree_csubst_WF₂_false` / `WF₃_false` versus `ntree_csubst_WFD₂` |
| `VEnv.iotaRulesRS_wf_of_hargsD` (§T16.11a) | **a composition, no new content** — its value is that it did not exist and that `hT`/`hj`/`hC` turn out to be derivable from `hqC` | the proof |
| `ntreeAux_iotaRulesRS_wf_of_nine` (§T16.12) | **a free reduction**: no environment hypothesis at all.  Its nine remaining inputs all move (`decide`) | `ntree_iota_components_ne` |

**Stated as open, not as discharged**: `(R.csubst ntreeAux ntreeK).WFD E₃ F₃ 2` is **not** proved.
§H supplies the two clauses stage 3 adds over §D.5; the rest is §D.5's bookkeeping re-done one
`addConstList` layer up.  And **the weakening count the brief asked for**: across the whole tree
exactly **one** clause at **one** constant uses `WFD`'s new freedom in a *proved* instance
(`ntree_csubst_WFD₂`'s `const` at `NTree.node`); §H.3 would add a second (`NTree.rec`) when `WFD₃`
is built.  Everything else takes the strict disjunct.  So `WFD` is not a weakening everything
suddenly satisfies — `σ.WF` remains refuted at exactly the pairs where `WFD` is needed.

### 33.7 What I tried that failed, and the step it failed at

1. **`⟨_, (by simpa using h.instL hls).weak0 henv⟩`** for §H.3 — *"invalid 'by' tactic, expected type
   has not been provided"* plus *"unsolved goals"*.  The anonymous constructor leaves the existential
   witness (a `VLevel`) as a metavariable, so the `by` block has no expected type.  Fixed by an
   `obtain ⟨v, h2⟩ : ∃ v, … := ⟨_, h.instL hls⟩` ascription.  **Fourth round running that an
   unconstrained `VLevel` metavariable in a defeq position is the failure** (§15.1, §23.3, §29.4) —
   the pattern is now: *if a `VLevel` is existentially bound, ascribe the type before tacticking.*
2. **`hll.length_eq`** on `hll : List.Forall₂ (· ≈ ·) ls ls'` — *"the environment does not contain
   `List.Forall₂.length_eq`"*.  It **does** exist, at `Lean4Lean/Std/Basic.lean:99` — but that file
   declares it *inside* `namespace Lean4Lean` (lines 20–232), so its real name is
   `Lean4Lean.List.Forall₂.length_eq` and **dot notation on a root-`List.Forall₂` hypothesis can
   never find it**.  `List.Forall₂.length_eq hll` (resolved through the open namespace) works.
   Worth a line in the ledger: a helper mis-namespaced this way is invisible to exactly the idiom
   people reach for first.
3. **`rw [← List.Forall₂.length_eq hll] at hlen ⊢`** — *"did not find an occurrence of the pattern"*;
   wrong direction and wrong location, `hlen : ls.length = 2` has no `ls'.length` in it.  Replaced
   by `List.Forall₂.length_eq hll ▸ hlen`.
4. **Mis-costed `WFD.const`'s level-genericity as a rewrite of §E** — see §33.4.  Caught by looking
   for a transport lemma before starting, which is the only reason it cost minutes rather than hours.
5. **Not attempted, deliberately**: `Built.fields_noK` (out of scope, row 117c — fifth round
   untouched); `ntree_csubst_WFD₃` itself (§33.9 item 1); the nine (C) components; any implementation
   or frozen file; `Theory/SetModel/*`; `Theory/Typing/*` other than `ConstSubstNested.lean`;
   `Experimental/ConeJoin.lean`.  No `implGapWhitelist` change, no git operation, no network.

### 33.8 `hbridge` at `MP`: it does **not** reach, and the missing input is not the bridge

The brief asked for `hbridge` "at the parameterised redex block `MP` if it reaches".  **It does not,
and the obstruction is upstream of the bridge**: obligation (B) at `MP` needs `hsrc`
(`∀ c ∈ D.recConsts, VConstant.WF E₂ c.2`), which `ntree_recConsts_wf` gets from
`VInductDecl'.recType_isType` off `D.RecCtx E₂` — and `RecCtx` comes from `VInductDecl'.WF`.
`mpAux mpAuxNodeB` **has no `VInductDecl'.WF`**, which `ParamRedex.lean:797` already records as the
reason §10's refutation instance is stated at `ntreeAux` rather than at `MP`.  So at `MP` there is
no staging pair, no `hsrc`, and no `hσ`/`WFD` either.

The *bridge itself* could be stated at `MP` over an abstract `F` the way `rhbridge` is (its content
is pure data plus `IsDefEq`), but it would close nothing: (B) at `MP` would remain hypothetical in
`hsrc`.  **I did not state it**, on the ground that a bridge with no consumer is exactly the kind of
statement this corner keeps mistaking for progress.  *Verdict, so the next brief does not re-ask:*
the next thing `MP` needs is `VInductDecl'.WF (mpAux mpAuxNodeB)` — a whole block well-formedness
proof at a **non-canonical** block — not another bridge.

### 33.9 Ledger rows this round needs (I did **not** edit `docs/vacuity-ledger.md` — another stream
committed to it while I worked)

1. **A row that corrects row 135c, in the pessimistic direction.**  135c records *"(C)′ has no `hσ`
   at all, so (C) was never blocked here"*.  **Half right, and the half that is wrong is the
   expensive half**: the *bridge* has no `hσ`, but **all seven producers of its components in
   `NestedTele.lean` §T15.4/§T16.3/§T16.5/§T16.7/§T16.8 do**, at the pair `ntree_csubst_WF₃_false`
   refutes.  So (C)'s route *was* blocked by the refuted `CSubst.WF`, one layer below where anyone
   looked, and the lemma advertised as *"a cheaper route, and it is free"*
   (`iotaCtx_substC_onCtx`) is the clearest case.  Repaired: six `WFD` restatements plus
   `iotaRulesRS_wf_of_hargsD`.  *Guard:* when a bridge is shown free of a refuted hypothesis, walk
   its **producers** — "the statement does not carry `hσ`" says nothing about what will be plugged
   into it.  This is the same shape as §31 item 2 and the third occurrence of "vacuous in the
   hypothesis nobody audited" in this corner.
2. **A row for the salvage-commit gap.**  Commit `8867876` says *"hbridge is NOT discharged"*; the
   commit in fact contains `rhbridge` **and** `ntreeAux_recConstsR_wf`, i.e. obligation (B)
   discharged at a parameterised nested block.  A crashed stream's commit message is written from the
   diff by someone who did not do the work, and the next brief inherits it as fact.  *Guard:*
   `#print axioms` the target theorem before briefing anyone on "what is left" — two minutes here
   would have redirected a whole round.  Pair with row 131f (a tool silently unavailable) and 133
   (a tool silently lying): this is a **document** silently lying, and it is the cheapest of the
   three to check.
3. **A row for the `instL`/`weak0` mis-costing** (§33.4): `WFD.const`'s "at every level
   instantiation and in every context" was priced by me as a level-generic rewrite of §E and is
   **two existing transport lemmas**.  Third time in this project the answer has been *"the
   generalisation is a lemma you already have"*.  *Guard:* before pricing "generic in X", grep for
   the transport of X on the judgement you already hold.
4. **A row for the (C) measurement** (§33.5's table): three rules, ι-contexts of 8/6/8, nine
   components of `esize` 83–273, **all nine move**.  (C) is ~3× (B) on larger terms, and
   `ntreeAux_iotaRulesRS_wf_of_nine` reduces it to exactly those nine with **no environment
   hypothesis**.
5. **A row for the mis-namespaced helper**: `List.Forall₂.length_eq` lives inside
   `namespace Lean4Lean` (`Std/Basic.lean:20–232`), so it is really
   `Lean4Lean.List.Forall₂.length_eq` and **dot notation on a `List.Forall₂` hypothesis cannot find
   it** — the idiom everyone tries first fails with "the environment does not contain", which reads
   like the lemma is missing.  Cheap fix if anyone wants it: move the `List.*` helpers out of the
   `Lean4Lean` namespace in `Std/Basic.lean` (not my file to change this round).
6. **A row for the verification gap, again** (row 135d's rule, third round): I ran **per-module
   builds only**, as briefed.  HEAD moved under me twice mid-round (another stream committed
   `InstDescendBvar.lean` and 10 ledger lines).  Nothing tree-wide was run: no guards, no census, no
   `MemberRedexScan`.  Grounds for expecting them unmoved, stated as reasoning and **not** as
   measurement: I added no `sorry` (`grep -c` = 0 in both files), no axiom, no import, no
   implementation file, and did not touch `ConeJoin.lean`, which fixes the scan's population.

### 33.10 What I would pick up first

1. **`ntree_csubst_WFD₃ : (ntreeRestore.csubst ntreeAux ntreeK).WFD E₃ F₃ 2`.**  This is now the
   single highest-value item and it is **bookkeeping plus two pieces that already exist**: §H.3
   gives `const` at `NTree.rec` (the only genuinely new `const` clause), §H.4 gives `val` at
   `_nested.List_1.rec`, `ntree_node_const_defeq` gives `NTree.node` (weaken `F₂ ≤ F₃` with
   `VEnv.addConstList_le`), and everything else is §D.5's proof one `addConstList` layer up.  It
   also needs `ntreeF₃_*` lookups, `Ordered F₃`, and a `ntree_stage₃_exists` (extend
   `ntree_stage₂_exists` by two `addConstList`s).  **Estimate: ~150 lines, no new mathematics** —
   and note that this estimate is the fourth of its kind in this corner, three of which were wrong,
   so verify it by writing the `const` case first.
2. **Then obligation (C) at `ntreeAux` through `VEnv.iotaRulesRS_wf_of_hargsD`**, whose remaining
   inputs are, per §T16.10 and now with a non-vacuous `hσ`: `hargs` twice (`hmaj`, `hconv`),
   `htele` (= `hmot` + `hmin` + `hfld`), and `hfunM`.  §E's `rbetaL`/`rbetaNil`/`rbetaCons` are the
   same three β-steps `hmot`/`hmin` need at the ι-telescope, so §E is reusable — the ι-context adds
   the field block on top of the recursor telescope.  The **alternative** route
   (`ntreeAux_iotaRulesRS_wf_of_nine`, nine hand-built typed defeqs) needs no `WFD` at all but shares
   nothing between rules; prefer route 1 unless `WFD₃` fights back.
3. **Decide where `CSubst.WFD` lives** — unchanged from §32 item 2, and now more pressing: there are
   **23** declarations whose signature mentions `CSubst.WFD` across two files (11 + 12, counted by
   script) (`ConstSubstNested.lean` §C/§D/§H, `NestedTele.lean`
   §T1a/§T15.3a/§T15.4/§T16.11/§T16.11a) and the strict `CSubst.WF` is provably unusable at every
   parameterised staging pair.  The question to put to the human is still: should `CSubst.WF`
   simply **be** `WFD`?  Nothing in the tree needs the strict `const`, and `CSubst.WF.wfd` shows the
   `np = 0` witnesses survive.  That is a `Theory/Typing/ConstSubst.lean` edit, another stream's
   file.
4. **`VInductDecl'.WF (mpAux mpAuxNodeB)`** if anyone wants (B)/(C) at the *redex* block — §33.8.
   Not a bridge problem.
5. **Re-run the tree-wide suite** (§30 lists the commands and expected numbers) once
   `Theory/SetModel/*` settles.  Do not take my §33.9 item 6 reasoning on trust.
6. **`Built.fields_noK`** — still out of scope, fifth round untouched (row 117c).

# Round 5 (2026-09-02, fifth stream): `ntree_csubst_WFD₃` PROVED, and the ~150-line estimate refuted

*Written incrementally, as briefed.*

## 34. `#print axioms` FIRST — §33's claims all check out

The brief made this mandatory after last round's discovery.  Result: **§33 is accurate in every
particular I checked**, so unlike the last two rounds the premise I was handed is *not* refuted.
Verified before proving anything (per-module build first: `lake build
Lean4Lean.Theory.Typing.ConstSubstNested Lean4Lean.Theory.Inductive.NestedTele` → **69 jobs,
green**; then `#print axioms` in a scratch file outside the tree):

| declaration | axioms | matches §33? |
|---|---|---|
| `rhbridge` | `[propext, Quot.sound]` | yes |
| `ntreeAux_recConstsR_wf` | `[propext, Classical.choice, Quot.sound]` | yes |
| `ntreeAux_obligationB` | `[propext, Classical.choice, Quot.sound]` | yes |
| `VEnv.iotaRulesRS_wf_of_hargsD` | `[propext, Classical.choice, Quot.sound]` | yes |
| `ntreeAux_iotaRulesRS_wf_of_nine` | `[propext, Quot.sound]` | yes — and **no** `Classical.choice`, i.e. the reduction really is free |
| `rRecConstClause0/1`, `rNestedRecVal` | `[propext, Quot.sound]` | yes |
| `ntree_stage₂_exists` | `[propext, Quot.sound]` | yes |
| `ntreeAux_ctorsAll_eq` | **no axioms at all** | yes |
| `ntree_csubst_WFD₂`, `ntreeAux_obligationA` | `[propext, Classical.choice, Quot.sound]` | yes |

No `sorryAx`, no frozen axiom, on any of them.  Nothing in §33 was over-claimed and nothing was
already-done-but-reported-open.  **So the standing advice paid off by confirming rather than
redirecting this time — which is still worth two minutes.**

## 35. `ntree_csubst_WFD₃` is PROVED — and the ~150-line estimate was too pessimistic *for the wrong reason*

`ConstSubstNested.lean` §I, and it went in on the **first** attempt with no failed tactic step.

* **`CSubst.WFD.mono`** (new, in §C beside `CSubst.WF.wfd`) — `WFD` is monotone in its *target*
  environment along `VEnv.LE`.  10 lines.  `[propext]` only.
* **§I.1** — `ntreeF₃_ordered`, `ntreeF₃_list/_nil/_cons/_ntree/_node` (weakenings of the §D.4
  lookups along `addConstList_le hF₃`), and the two new ones: **`ntreeF₃_rec`** (`NTree.rec` at the
  *restored* type) and **`ntreeF₃_rec1`** (`NTree.rec_1`, `rNestedRecVal`'s `hrec1`).
* **§I.2 `ntree_csubst_WFD₃ : (ntreeRestore.csubst ntreeAux ntreeK).WFD E₃ F₃ 2`** — obligation
  (C)'s environment hypothesis at the canonical parameterised block, where
  `ntree_csubst_WF₃_false` refutes the strict `CSubst.WF`.
* **§I.3 `ntree_stage₃_exists`** and **`ntreeAux_WFD₃_exists`** — the third staging pair exists, so
  §I.2 is **not hypothetical**: `WFD₃` holds with nothing assumed.

`#print axioms`: `CSubst.WFD.mono` `[propext]`; `ntreeF₃_rec`, `ntreeF₃_rec1`,
`ntree_stage₃_exists` `[propext, Quot.sound]`; `ntree_csubst_WFD₃`, `ntreeF₃_ordered`,
`ntreeAux_WFD₃_exists` `[propext, Classical.choice, Quot.sound]` — the `Classical.choice` inherited
from `listEnv_ordered`/`ntree_csubst_WFD₂`/`ntreeAux_recConstsR_wf`, all measured as carrying it
already in §30/§33.5.  `grep -c sorry` in `ConstSubstNested.lean` = **0**.  Per-module build after
each landing: **64 jobs, green**, the only warning the pre-existing unused-section-variable one at
`:1164`.

### 35.1 The costing, corrected — and the reason matters more than the number

§33.10 priced this as *"~150 lines, no new mathematics … §D.5's bookkeeping re-done one
`addConstList` layer up"*, with the honest warning that three of the previous four such estimates
were wrong.  **Measured: the §I section is 105 lines of which `ntree_csubst_WFD₃` itself is 55**,
plus 10 for `CSubst.WFD.mono` and 55 for §I.3's existence proof (which §33.10 named as extra work
and I have also done).  So the *theorem* came in at about a third of the estimate.

But the interesting part is **why**, and it is not "the estimate was padded": §33.10's plan —
re-do §D.5's case analysis one layer up — would indeed have cost ~150 lines.  It is the wrong plan.
`CSubst.WFD.mono` carries **the whole of `ntree_csubst_WFD₂`** from `F₂` to `F₃`, so every constant
and every value stage 2 already handled is *reused verbatim*, and the stage-3 proof only has to
name the cases that are genuinely new.  There are exactly **two**:

| new case | witness | why it is new |
|---|---|---|
| `const` at `NTree.rec` | §H.3 `rRecConstClause0` (defeq disjunct) | `E₃` is the first environment holding `NTree.rec` |
| `val` at `_nested.List_1.rec` | §H.4 `rNestedRecVal` | at stage 2 this case is `exfalso`; `E₃` declares it |

Everything else routes through `hσ₂ := (ntree_csubst_WFD₂ …).mono (VEnv.addConstList_le hF₃)`.
**This is the same lesson as §33.4 in a new place**: the generalisation ("the same `WFD` one layer
up") is a *transport*, not a re-proof — and the transport had to be written (10 lines), but writing
it collapsed the job.  Fourth occurrence in this project of *"the generalisation is a lemma you
already have, or a ten-line lemma you don't"*.  **Guard, sharpened:** before re-doing a staged proof
one layer up, ask whether the hypothesis is monotone in the layer being added; if it is, the delta
is only the constants the layer *declares*.

### 35.2 Anti-vacuity for §I, to the standard the brief set

* **`ntree_csubst_WFD₃` carries genuine conversion content.**  Not asserted: its `const` clause at
  `NTree.rec` takes the **defeq** disjunct, and the strict alternative is refuted by
  `decide` (`ntree_recTypeR_bridge_false_0`, §E.5).  Its `val` clause at `_nested.List_1.rec` is a
  `defeqDF` along §H.3 (`rNestedRecVal`), not a `CSubst.val_of_hasType`.  And the whole statement is
  unavailable in strict form: `ntree_csubst_WF₃_false` refutes `σ.WF E₃ F₃ U` for every `U`.
* **The weakening count the brief demands.**  §33.6 reported **one** proved instance using `WFD`'s
  new freedom (`WFD₂`'s `const` at `NTree.node`) and predicted §H.3 would add a second when `WFD₃`
  was built.  Measured now: **exactly two**, `NTree.node` (inherited through `.mono`) and
  `NTree.rec` (new).  Every other constant in both instances takes the strict `.inl` disjunct.  So
  `WFD` is still not a weakening everything suddenly satisfies.
* **`CSubst.WFD.mono` is pure transport — reported as such, not as content.**  Its only non-trivial
  line is `VEnv.IsDefEq.mono` on the `const` clause's defeq disjunct.
* **`ntree_stage₃_exists` is a typing/bookkeeping result, not a conversion** — reported as such.
  Its value is anti-vacuity: without it `WFD₃` would be "hole-free but not discharged".

## 36. Obligation (C) at `ntreeAux`: reduced to `hdata` alone, and `hdata` is much smaller than §33.5 read

### 36.1 `ntreeAux_obligationC_of_hdata` — eight of nine hypotheses discharged

`NestedTele.lean` §T16.13.  `VEnv.iotaRulesRS_wf_of_hargsD` has nine hypotheses; with §I's `WFD₃`
in hand, **eight are now theorems at `ntreeAux`** and the residual is exactly `hdata`:

| hypothesis | discharged by |
|---|---|
| `hown` | `ntreeRestore_ownId` (`NestedHead.lean`) |
| `hat` | **new**: `ntreeRestore_domSep.substAt`, via `ntreeRestore_domNodup` + `ntreeAux_allNames_nodup` (both `decide`) |
| `hfr` | `ntreeRestore_substFree` (`NestedRules.lean` §7) |
| `hσc` | `ntree_csubst_closed` |
| **`hσ`** | **`ntree_csubst_WFD₃` (§I) — this is what was missing** |
| `hI` | `(ntreeAux_WF h).iotaCtx (listEnv_ordered h) hE₁ hE₂ hE₃` |
| `henv` | `ntreeF₃_ordered` (§I.1) |
| `hpos` | **new**: `ntreeAux_recArg_lt` |
| `hdata` | **OPEN** — three `IotaHargs`, one per constructor |

`#print axioms`: `ntreeAux_obligationC_of_hdata` `[propext, Classical.choice, Quot.sound]`;
`ntreeRestore_domSep` `[propext, Quot.sound]`; `ntreeAux_recArg_lt` `[propext]`.  Per-module build
`lake build Lean4Lean.Theory.Inductive.NestedTele` → **69 jobs, green**.  `grep -c sorry` = 0 in both
files.

**One failure to record, with the step it failed at.** `hpos` stated as written in
`iotaRulesRS_wf_of_hargsD` — `∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll → ∀ (i : Nat) …` —
is **not `decide`-able**: *"failed to synthesize `Decidable`"*, because `t` and `i` are unbounded
`Nat`s even though every witness that matters is bounded.  Fix: prove the list-quantified form
`∀ p ∈ ntreeAux.ctorsAll, ∀ Fl ∈ p.2.fields, ∀ r ∈ Fl.recArg, r.idx < ntreeAux.nm` by `decide` (all
three quantifiers are `List`/`Option` membership, hence decidable) and derive the `getElem?` form
through `List.mem_of_getElem?`.  **Guard:** a `decide`-shaped side condition in a general lemma may
need re-indexing over list membership before `decide` will look at it; the obstruction is the
*quantifier's domain*, not the proposition.

### 36.2 §J: `htele` PROVED at all three rules — and the ι-context is §E's telescope

`ConstSubstNested.lean` §J, 15 declarations, all green, all `[propext, Quot.sound]`.  Measured with
`#eval` first, then each equation landed as a `decide`:

| rule | ι-ctx length | entries that move | substituted entry sizes (L → R) |
|---|---|---|---|
| `NTree.node` | 8 | **5** | `[1,5,11,25,11,37,1,9]` → `[1,5,7,21,7,29,1,5]` |
| `_nested.List_1.nil` | 6 | **4** | `[1,5,11,25,11,37]` → `[1,5,7,21,7,29]` |
| `_nested.List_1.cons` | 8 | **5** | `[1,5,11,25,11,37,3,9]` → `[1,5,7,21,7,29,3,5]` |

The **first six entries of all three ι-contexts are literally `rTele`/`rTeleR`**, and at the nil rule
the ι-context *is* §E's recursor telescope on the nose:

    rIotaCtx_nil_eq  : (ntreeAux.iotaCtx nlistNil).map (·.substC σ)                = rTele    -- decide
    rIotaCtxR_nil_eq : (ntreeAux.iotaCtxR ntreeRestore nlistNil).map (·.substC σ)  = rTeleR   -- decide

`node`/`cons` add two entries each; the first does not move, the second is **one `rbetaL` step at
`k = 6`** — the same lemma §E already has.  So:

* **`rTeleDefEq_ext`** — `rTeleDefEq` with its `.nil` replaced by an arbitrary tail (the shared
  six-entry prefix, proved once);
* **`rIotaTele_nil`, `rIotaTele_node`, `rIotaTele_cons`** — `htele` at each of the three ι-rules.

All three went in on the first attempt.

### 36.3 The correction to §33.5 that matters: **one of `hdata`'s pieces is FREE**

§33.5 measured *"all nine (C) components move — `decide`"* and §33.6 concluded *"none of the nine is
free"*.  That is true **of route 2's nine** (`type`/`lhs`/`rhs` per rule, `ntree_iota_components_ne`).
It is **false of route 1's**, and I measured the counterexample:

    rMaj_node_eq : (ntreeAux.ctorApp' ntreeNode …).substC σ = (ntreeAux.ctorAppR ntreeRestore 0 ntreeNode …).substC σ   -- decide

**`hmaj` at `NTree.node` is the identity** — the block's own constructor, where the restoration is
`ntreeRestore_ownId`; it still needs the constructor application's *typing*, but no conversion.  At
both companion constructors it does move (`rMaj_nil_ne`, `rMaj_cons_ne`, `decide`; esize 9→5 and
13→9).  **Reported as the negative result the brief asks for**, and it is the third instance in this
corner of the pattern *"at the block's own member the restoration is the identity"* (`rBody0_eq` for
(B) at `j = 0`, `mr_auxFieldTypesR_eq_fields` at a redex field, this one for (C)'s major premise).

**So my predecessor's "(C) is ~3× (B) and none of it is free" is right about route 2 and wrong about
route 1**, and the difference is not marginal: route 1's `htele` is §E plus one β step per rule, and
one of its three `hmaj`s is `decide`-free.  *Guard:* a size measurement of a bundled component
(`type`/`lhs`/`rhs` of a whole rule) does **not** transfer to a decomposition of the same content —
`IotaHargs` prices per telescope entry, and the discount lives in the entries.

## 37. OBLIGATION (C) IS DISCHARGED at `ntreeAux` — and with it `Ordered` at a parameterised nested block

This went further than the brief asked, because the measurement in §36.2/§36.3 said it could.

### 37.1 The three residual triples are §E's β-steps and nothing else (`NestedTele.lean` §T16.15)

Measured with `#eval` *before* proving (the numbers are in §37.3), and the measurement is the whole
content.  At each rule the substituted `tyApp'` is the **redex** `(λ α, List (NTree α)) #k` and the
substituted `ctorApp'` is the same redex at `List.nil`/`List.cons`, while the restored `ctorAppR` is
its **contraction**.  So, choosing `A₀` to be the *contracted* type:

| piece | nil | cons | node |
|---|---|---|---|
| `hfunM` | one `Lookup` (index 3) | one `Lookup` (index 5) | one `Lookup` (index 6) |
| `hconv` | `(rbetaL … k:=5).symm` | `(rbetaL … k:=7).symm` | `appDF (rNC hN) (bvar …)` |
| `hmaj` | **`rbetaNil … k:=5`**, verbatim | `appDF (appDF (rbetaCons … k:=7) …) (defeqDF (rbetaL …) …)` | `appDF³ (rNodeC hnode) …` — *no conversion*, `rMaj_node_eq` |

`rIotaRest_nil`, `rIotaRest_cons`, `rIotaRest_node`: **3, 5 and 5 lines of proof term**.  Every β-step
is one of §E's three; nothing new was proved about conversion.

A free measurement fell out of tightening the `include` lists (Lean's unused-section-variable warning
is the instrument): each rule needs **exactly the constants its own β-step mentions** — nil needs
`hL`/`hN`/`hnil`, cons needs `hL`/`hN`/`hcons`, node needs `hL`/`hN`/`hnode`, and none needs the other
two.  That is a check on the decomposition being the right one: if a rule had needed a constant from
another rule's minor, the split would have been leaking.  Both files now emit **no new warnings** (the
only one left in either is the pre-existing unused-section-variable at `ConstSubstNested.lean:1164`).

### 37.2 The composition, all the way up

* **`ntreeAux_iotaRulesRS_wf`** — `∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.WF F₃ df`:
  **obligation (C), discharged at the canonical parameterised nested block**, the `np ≥ 1`
  counterpart of `nfnAux_iotaRulesR_wf`.
* **`ntreeAux_obligationC`** — the same with **nothing assumed** (staging supplied by
  `ntree_stage₃_exists`), the (C) counterpart of `ntreeAux_obligationA`/`_obligationB`.
* **`ntreeAux_stages`** — the E-chain exists for any `env₁` holding `List` (modelled on
  `nfnAux_stages`).
* **`ntreeAux_addInductR_ordered`** —

      ∃ env₁ env', VEnv.empty.addInduct' listDecl = some env₁ ∧
        env₁.addInductR ntreeAux ntreeK ntreeRestore = some env' ∧ env'.Ordered

  **the nested declaration step preserves `VEnv.Ordered` at a PARAMETERISED nested block.**  All
  three of `VEnv.addInductR_ordered'`'s obligations are now theorems at `ntreeAux`: `hctors` =
  `ntreeAux_ctorConstsCR_wf` (A), `hrecs` = `ntreeAux_recConstsR_wf` (B), `hrules` =
  `ntreeAux_iotaRulesRS_wf` (C).  Until this round the only block with all three was `nfnAux`, at
  `np = 0`.

`#print axioms` on all nine new declarations of §T16.15/§T16.16: `[propext, Quot.sound]` for the three
`rIotaRest`s and `ntreeAux_hdata_of_rest`; `[propext, Classical.choice, Quot.sound]` for
`ntreeAux_obligationC_of_rest`, `ntreeAux_iotaRulesRS_wf`, `ntreeAux_obligationC`, `ntreeAux_stages`
and **`ntreeAux_addInductR_ordered`**.  **No `sorryAx`, no frozen axiom, none traded** — the
`Classical.choice` is the same inherited one measured in §30/§33.5 (`listEnv_ordered`,
`ntree_csubst_WFD₂`, `ntreeAux_recConstsR_wf`).  `grep -c sorry` = **0** in both files I touched.

### 37.3 Anti-vacuity for (C), to the standard the brief set

* **The block really is parameterised and really is nested**: `ntreeAux_np : ntreeAux.np = 1`
  (`decide`, pre-existing) and `ntree_csubstList_dom` gives a **four-name** substitution domain, so
  `K ≠ []`.
* **(C) has genuine conversion content at this block, established by `decide`, not asserted**: the
  strict bridge is refuted (`ntree_iotaRules_bridge_false`), all nine route-2 components move
  (`ntree_iota_components_ne`), five of eight ι-context entries move at node/cons and four of six at
  nil (§J), and the substitution's own `const` clause needs the defeq disjunct
  (`ntree_recTypeR_bridge_false_0`) while the strict `CSubst.WF` is outright false at the pair
  (`ntree_csubst_WF₃_false`).  There are exactly **three** identity pieces in the whole of (C), all
  three measured and reported: `hmaj` at `NTree.node` (`rMaj_node_eq`) and the two non-moving
  telescope prefix entries `rA0`/`rA1`.
* **`ntreeAux_addInductR_ordered` is hypothesis-free** — an existential with constructed witnesses,
  not a conditional.  It is not an "identity instance": `nfnAux_addInductR_ordered` is the `np = 0`
  case and its (C) went through `CSubst.WF` (`nfnSubstAll_WF₃`), which is **provably unavailable**
  here.
* **The `WFD` weakening count, final for this round**: `WFD` is used in **two** proved instances
  (`ntree_csubst_WFD₂`, `ntree_csubst_WFD₃`) and the new freedom is taken at exactly **two**
  constants — `NTree.node` and `NTree.rec`.  Every other constant in both takes the strict `.inl`
  disjunct.  So the brief's "a weakening everything suddenly satisfies is suspect" check still
  passes.

## 38. What I tried that failed, and the exact step it failed at

1. **`hor.imp id …`** in `CSubst.WFD.mono` — *"Application type mismatch: the argument `id` has type
   `CSubst`"*.  Inside `namespace CSubst` the identifier `id` resolves to **`CSubst.id`**, not
   `_root_.id`.  Fixed with `(fun x => x)`.  Cheap, but worth a line: inside a namespace that has its
   own `id`/`comp`/`map`, the `Or.imp id` idiom silently retargets.
2. **`hpos` by `decide`** — *"failed to synthesize `Decidable`"*.  `iotaRulesRS_wf_of_hargsD`'s `hpos`
   quantifies `∀ (t : Nat) … ∀ (i : Nat) …`; both are unbounded even though only finitely many
   witnesses exist.  Fixed by proving the list/option-membership form
   (`∀ p ∈ ntreeAux.ctorsAll, ∀ Fl ∈ p.2.fields, ∀ r ∈ Fl.recArg, …`) by `decide` and transporting
   with `List.mem_of_getElem?`.  See §36.1.
3. **`?hk7` inside `exact`** — *"don't know how to synthesize placeholder"* + *"Case tag `hk7` not
   found"*.  Named holes only survive `refine`; under `exact` they are ordinary placeholders.  Fixed
   by inlining the seven-`succ` `Lookup` term at each of its three occurrences.
4. **Inserting a theorem after a section's `end`** — 30 *"Unknown identifier `h`"* errors in one
   build.  My own scripted edit put `ntreeAux_iotaRulesRS_wf` (which needs the section variables)
   after the `end` that closes them.  Mechanical, but it is the failure mode of scripted insertion
   into a 4000-line file: **anchor on the last line of the block you mean to extend, not on the
   `end`.**
5. **`#eval` with `(L.zip R).filter fun p => p.1 != p.2`** — *"Invalid projection: type of `p` is not
   known"*, three times running, including with an explicit `(p : VExpr × VExpr)` ascription.  Used
   `L.zipWith (fun a b => a != b) R` instead.  A measurement instrument that will not elaborate is
   the same hazard as one that lies (row 133); the fix was to change idiom, not to force it.
6. **Not attempted, deliberately**: `Built.fields_noK` (out of scope, row 117c — sixth round
   untouched); `MP`'s (B)/(C) (out of scope per the brief; §33.8's verdict stands — it needs
   `VInductDecl'.WF (mpAux mpAuxNodeB)`, and I did not touch it); any implementation or frozen file;
   `Theory/SetModel/*`; `Theory/Typing/*` other than `ConstSubstNested.lean`;
   `Experimental/ConeJoin.lean`.  I also did **not** edit the untracked
   `Theory/Inductive/NestedRules.lean` even though it is in my area and I used its lemmas
   (`ntreeRestore_substFree`, `VIndRestore.domSep_of_allNames_nodup`) — it is uncommitted work whose
   author I cannot identify, so I put `ntreeRestore_domNodup`/`_domSep` in `NestedTele.lean` instead
   of beside `nfnRestore_domSep` where they belong.  **Someone should commit or delete that file**;
   it is 1923 green lines that no commit contains.

## 39. Ledger rows this round needs (I did **not** edit `docs/vacuity-ledger.md`)

1. **(C) IS DISCHARGED at a parameterised nested block**, and so is `Ordered`:
   `ntreeAux_iotaRulesRS_wf`, `ntreeAux_obligationC` (nothing assumed),
   `ntreeAux_addInductR_ordered`.  Non-vacuity evidence in §37.3 — three identity pieces out of the
   whole of (C), all three named and `decide`-established.
2. **A row correcting §33.5/§33.6 in the optimistic direction.**  *"All nine components move, none
   is free, (C) is ~3× (B)"* is true of **route 2**'s nine (whole-rule `type`/`lhs`/`rhs`) and
   **false of route 1**'s.  Route 1's `htele` is §E's `rTeleDefEq` plus one β step per rule (the nil
   rule's ι-context **is** `rTele`, `decide`), and `hmaj` at `NTree.node` is the **identity**
   (`rMaj_node_eq`).  *Guard:* a size/movement measurement of a **bundled** component does not
   transfer to a **decomposition** of the same content; measure the decomposition you intend to use.
3. **A row for the monotonicity mis-plan** (§35.1): §33.10 priced `WFD₃` as "§D.5's bookkeeping one
   `addConstList` layer up, ~150 lines".  The theorem is **55 lines** because `CSubst.WFD.mono` (10
   lines) carries stage 2 wholesale and only the constants the layer *declares* are new — two of
   them.  *Guard:* before re-doing a staged proof one layer up, ask whether the hypothesis is
   **monotone in the layer**; if it is, the delta is only what the layer declares.  Fourth
   occurrence of "the generalisation is a transport you already have (or a ten-line lemma you
   don't)".
4. **A row for `decide`'s quantifier domain** (§38 item 2): a finite-in-practice side condition
   stated over `∀ (n : Nat)` is not `Decidable`; re-index it over `List`/`Option` membership first.
   This is a *different* failure from row 131f (tool unavailable) and row 133 (tool lying): the tool
   works and is honest, the *statement* is in the wrong shape.
5. **A row for the namespace-shadowed combinator** (§38 item 1): `Or.imp id` inside
   `namespace CSubst` picks up `CSubst.id`.  Pairs with §33.7 item 2 (a helper invisible to dot
   notation because it is inside `namespace Lean4Lean`): **name resolution in this tree has bitten
   two rounds running, in opposite directions.**
6. **A row for the uncommitted file** (§38 item 6): `Theory/Inductive/NestedRules.lean` is 1923
   green lines, untracked, and load-bearing — `NestedTele.lean` imports it and this round's (C)
   depends on its `ntreeRestore_substFree` and `domSep_of_allNames_nodup`.  A `git clean` would
   delete obligation (C).  This is the same class as row for the salvage commit (§33.9 item 2): work
   that exists but that the repository does not record.
7. **A row for the verification gap** (row 135d's rule, fourth round): **per-module builds only**, as
   briefed — `ConstSubstNested` (64 jobs), `NestedTele` (69 jobs), `StoredIota` (71 jobs), all green.
   No tree-wide build, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`.  Grounds
   for expecting them unmoved, stated as **reasoning, not measurement**: `grep -c sorry` = 0 in both
   files, no axiom and no import added, no implementation or frozen file touched, `ConeJoin.lean`
   untouched, and I checked all nine new top-level names for tree-wide collisions (`grep`, one
   occurrence each).  HEAD did **not** move under me this round (`6a570b1` throughout).

## 40. What I would pick up first

1. **Commit or delete `Theory/Inductive/NestedRules.lean`** (§38 item 6).  Cheapest highest-risk item
   in the tree right now: obligation (C) at `ntreeAux` depends on an untracked file.
2. **The same programme at the *redex* block `MP`** — but §33.8's verdict is unchanged and I did not
   touch it: what `MP` needs is `VInductDecl'.WF (mpAux mpAuxNodeB)`, a block well-formedness proof
   at a non-canonical block, not more substitution machinery.  Everything §I–§T16.16 did at
   `ntreeAux` is now a template for it once that exists.
3. **Ask the human the `CSubst.WF` question** — unchanged from §33.10 item 3 and now sharper: with
   `WFD₂` **and** `WFD₃` proved and `CSubst.WF` **refuted** at both staging pairs, nothing in the
   tree needs the strict `const` clause, and `CSubst.WF.wfd` shows the `np = 0` witnesses survive.
   Should `CSubst.WF` simply *be* `WFD`?  That is a `Theory/Typing/ConstSubst.lean` edit — another
   stream's file — and the count of `WFD`-mentioning signatures is now ~35 across two files.
4. **A second parameterised block**, to test whether §T16.15's "the residual is `rbetaL`/`rbetaNil`/
   `rbetaCons` and one `Lookup`" is about nested restoration in general or about `NTree`/`List` in
   particular.  My honest read: the *shape* generalises (the substituted `tyApp'`/`ctorApp'` are
   always redexes and the restored ones always their contractions — that is what `SubstAt` says), and
   the per-block cost is one β-lemma per companion constructor.  **Stated as a conjecture, not a
   measurement.**
5. **Re-run the tree-wide suite** once `Theory/SetModel/*` settles (§30 lists the commands).  Do not
   take §39 item 7's reasoning on trust.
6. **`Built.fields_noK`** — still out of scope, sixth round untouched (row 117c).

## 41. `#print axioms` FIRST — the brief's premise CHECKS OUT, and §11 of `ParamRedex.lean` now supplies what it named

Verified before proving anything (baseline per-module build
`lake build Lean4Lean.Theory.Inductive.ParamRedex Lean4Lean.Theory.Typing.ConstSubstNested
Lean4Lean.Theory.Inductive.NestedTele` → **72 jobs, green**; then `#print axioms` in a standalone
snippet):

| declaration (by NAMESPACE) | axioms | matches the brief / §33–§40? |
|---|---|---|
| `MRedex.MPWit.mp_obj_entry_substC_ne` | `[propext, Quot.sound]` | yes — `hrec` at `MP` really is a conversion, by `decide` |
| `MRedex.MPWit.mp_hargs`, `mpRestore_ownId`, `mpRestore_substFree`, `mpRestore_domSep`, `mpAuxB_canonicalOwn` | `[propext, Quot.sound]` | yes |
| `MRedex.MPWit.mpAuxB_pos` | `[propext]` | yes |
| `MRedex.MPWit.mp_recTypeR_bridge_false`, `mp_iotaRules_bridge_false`, `mp_const_clause_ne` | `[propext, Quot.sound]` | yes |
| `InductiveDeclExamples.ntreeAux_obligationB` / `_obligationC` / `_addInductR_ordered` | `[propext, Classical.choice, Quot.sound]` | yes — all three obligations really are theorems at `ntreeAux` |

And the premise itself, checked structurally rather than read off: **`VInductDecl'.WF (mpAux
mpAuxNodeB)` did not exist.**  `grep -rn 'mpAux\|MPWit'` over `Lean4Lean/` returns hits only in
`Theory/Inductive/ParamRedex.lean` and one `import` line in `Experimental/ConeJoin.lean` — no other
module mentions the block at all.  So §33.8/§40 item 2 and ledger row 141d were accurate.

### 41.1 `MRedex.MPWit.mpAuxB_WF` — PROVED, and hypothesis-free over an ARBITRARY environment

    theorem mpAuxB_WF : ∀ {env : VEnv}, VInductDecl'.WF env (mpAux mpAuxNodeB)

`[propext, Quot.sound]`, no `sorryAx`, no frozen axiom.  Module green at **72 jobs**.  It is
*stronger* than the brief asked for: not "at some staged environment", but at **every** `env`.

**Why it goes through, and why the reader of §10 might have expected it not to.**  Two facts, both
load-bearing:

1. **`VInductDecl'.WF` does not require `Canonical`.**  Its positivity clause (`VIndField.WF.pos`,
   `some` branch, last conjunct) asks for `env.IsDefEqType D.uvars Γ F.type (r.canonType D i)` — a
   **definitional** equation.  A stored redex is therefore admissible provided it *contracts* to the
   canonical application.  At `mpAuxNodeB`'s field 1 the contraction is **exactly one β step**.
2. **The constructor clause is staged over `env.addIndTypes D`**, which declares both `MP` and
   `_nested.MDep_1`.  So no history environment is needed — unlike `ntreeAux_WF`, whose *restoration*
   story (not its `WF`) needs `listDecl`.  Reading `ntreeAux_WF` closely, its `h : addInduct'
   listDecl = some env₁` is carried by the enclosing `include h` and never used in the `WF` proof
   either; the two staged-constant lemmas it calls need only `hs`.  **So `ntreeAux_WF` is also
   environment-generic and the section variable hides it.**  Stated as an observation about the
   existing proof, not a change to it.

New names, all in namespace `Lean4Lean.MRedex.MPWit` (file `Theory/Inductive/ParamRedex.lean` §11):

| name | what | axioms |
|---|---|---|
| `mpAuxB_params_WF` | `OnCtx params.reverse (IsType)` | `[propext]` |
| `mp_const_staged` / `mpNested_const_staged` | the two block constants in `addIndTypes` | `[propext, Quot.sound]` |
| `mp_redex_ne_canonType` | **the stored redex ≠ its canonical type** (`decide`) | `[propext, Quot.sound]` |
| `mp_redex_pos_defeq` | …and it contracts in **one β step** — the whole content of `WF` here | `[propext, Quot.sound]` |
| `mp_binders_indep` | `BindersIndep` for empty `ξ` (generic; mirrors `InductiveDeclExamples.ntreeAux_binders_indep`) | `[propext]` |
| **`mpAuxB_WF`** | **`VInductDecl'.WF env (mpAux mpAuxNodeB)`** | `[propext, Quot.sound]` |

### 41.2 Anti-vacuity for `mpAuxB_WF`

* **Genuine conversion content, established by `decide` not asserted**: `mp_redex_ne_canonType`
  shows `mpRedex ≠ ({binders := [], idx := 0, args := []} : VIndRecArg).canonType (mpAux
  mpAuxNodeB) 1`, i.e. the positivity clause at the redex field is **not** an identity.  It is
  discharged by `VEnv.IsDefEq.beta` — one β step, the same contraction `mp_obj_entry_betaHead`
  measures one layer out at `hrec`.  So this is the **fourth** place in this corner where the
  content is a single β step at a companion-pointing position, and the **first** that is not an
  identity-at-the-block's-own-member (row 143d's rule is not contradicted: the redex field belongs
  to the *companion* member `_nested.MDep_1`, not to `MP`).
* **Every other clause is a typing or bookkeeping**, and reported as such: `params`, `types`
  (`isType`/`canon` both `type_tac`), `mpObj`'s field (its stored type **is** `tyApp 1 0 []`, so its
  `pos` defeq is `rfl`-shaped — an identity, reported as one), `args_ty`, `result`, `isLE` (`lvl =
  .succ .zero` is `IsNeverZero`, so `LECond`'s first disjunct).
* **One failed step, recorded**: `⟨_, .beta (by type_tac) (by type_tac)⟩` as a term does **not**
  elaborate — ten errors of the form *"don't know how to synthesize implicit argument `B`"*, because
  the anonymous-constructor metavariable defers unification and `.beta`'s `.app (.lam A e) e'`
  pattern never gets matched against the `def mpRedex`.  Fixed by `refine ⟨.succ .zero, ?_⟩` then
  `exact VEnv.IsDefEq.beta (A := …) (B := …) (e := …) (e' := …) …` with all four implicits given.
  *Guard:* when the conclusion's head must be matched against a `def`, supply the constructor's
  implicits explicitly; `exact` will unfold the `def`, but unification with a postponed
  metavariable will not.

## 42. `MP`'s environment chain: history, `hsrc`, obligation (A), and `hσ` — all four PROVED

Everything in this section is `Theory/Inductive/ParamRedex.lean` §§12–14, namespace
`Lean4Lean.MRedex.MPWit`.  Module green at **72 jobs** after each landing.

### 42.1 §12 — the history block and `hsrc`

| name | statement | axioms |
|---|---|---|
| `mrDepDecl_WF` | `MRWit.mrDepDecl.WF VEnv.empty` — `MDep`'s own block, the counterpart of `listDecl_WF` | `[propext, Quot.sound]` |
| `mpEnv_ordered` | the history environment of the `MP` step is `Ordered` | `[propext, Classical.choice, Quot.sound]` |
| `mp_fresh'`, `mpAuxB_stagedE₁`, `mpAuxB_stagedF₁`, `mpAuxB_stagedE₂`, `mpAuxB_stagedF₂` | the four staging environments **exist** | `[propext, Quot.sound]` |
| **`mp_recConsts_wf`** | **`hsrc` at `MP`**: `∀ c ∈ (mpAux mpAuxNodeB).recConsts, VConstant.WF E₂ c.2` | `[propext, Classical.choice, Quot.sound]` |

`mp_recConsts_wf` is `ntree_recConsts_wf`'s proof **verbatim** — `RecCtx` off `WF`, then
`recType_isType`.  Nothing about redex-ness enters.  **So §33.8's verdict is now discharged, not
merely restated: (B) at `MP` no longer dies on `hsrc`.**

### 42.2 §13 — obligation (A) at the parameterised REDEX block

`mpVal := λ α, MDep Prop (λ _, MP α)` and `mpValNode := λ α, MDep.node Prop (λ _, MP α)` are the
two lambdas the restoration presents; `mp_csubstTy_eq` identifies the general `csubstTy` with
`CSubst.one mpNestedName mpVal` (`funext` + computation, no hypothesis).

| name | statement | axioms |
|---|---|---|
| `mpVal_hasTypeF`, `mpValNode_hasTypeF`, `mp_obj_const_defeq` | the two values and the `const`-clause datum, over any `F` holding `MDep`/`MDep.node`/`MP` | `[propext, Quot.sound]` |
| `mpSubst_WF` | `mpSubst.WF E₁ F₁ 0` — the **strict** `CSubst.WF`, available at the *type* stage | `[propext, Classical.choice, Quot.sound]` |
| **`mpAuxB_ctorConstsCR_wf`** | **obligation (A)** at `mpAux mpAuxNodeB` | `[propext, Classical.choice, Quot.sound]` |
| `mpF₁_ordered`, `mpF₂_ordered` | `he₁`/**`he₂`**, (B)'s third input | `[propext, Classical.choice, Quot.sound]` |

The block-specific input is **one `IsDefEq.beta`**, exactly as at `ntreeAux`.

### 42.3 §14 — `hσ` at `MP`: `CSubst.WFD` at the second staging pair

    theorem mp_csubst_WFD₂ : (mpRestore.csubst (mpAux mpAuxNodeB) mpK).WFD E₂ F₂ 1

`[propext, Classical.choice, Quot.sound]`.  Supporting: `mp_csubst_closed`, `mp_csubst_ne`, `mp_csubst_fresh`,
`mpF₂_mdep/_mdepNode/_mp/_obj`.

**The weakening count the brief demands, measured not asserted.**  Of the five constants the
`const` clause sees at this pair — `MP`, `MP.obj`, `MDep`, `MDep.node`, `MDep.rec` — **exactly
one** (`MP.obj`) takes `WFD`'s new defeq disjunct; the other four take `CSubst.WF`'s clause
verbatim (`.inl rfl`).  At `ntreeAux` the count was one of seven (`NTree.node`).  So across the
two proved `WFD₂` instances the new freedom is used at **two** constants and nowhere else — `WFD`
is still not a weakening everything suddenly satisfies.

Of the three σ-domain names, `_nested.MDep_1` and `_nested.MDep_1.node` supply real `val`
witnesses and `_nested.MDep_1.rec` is `exfalso` (not yet declared at stage 2) — the same 2+1 split
as `ntreeSubstAll_WF₂`'s 3+1.

### 42.4 Failures, with the step each failed at

1. **`⟨_, .beta (by type_tac) (by type_tac)⟩` as a term** (§11) — ten *"don't know how to
   synthesize implicit argument"* errors.  The anonymous constructor defers unification, so
   `.beta`'s `.app (.lam A e) e'` pattern is never matched against the `def mpRedex`.  Fixed by
   `refine ⟨.succ .zero, ?_⟩` + `exact VEnv.IsDefEq.beta (A := …) (B := …) (e := …) (e' := …)`.
2. **`type_tac` under a *variable* `U`** — *"Expected type must not contain free variables
   `VLevel.WF U VLevel.zero.succ`"*, six times.  `type_tac` discharges `VLevel.WF U l` by
   `decide`, which needs `U` closed.  Fixed by stating the generic value lemmas at the **concrete**
   `U` each consumer uses (`0` for `val`, `1` for `const`) — not by generalising the tactic.
   *Guard:* `type_tac` is usable only at closed universe counts; a genuinely `U`-generic lemma must
   be built by hand from `sortDF`/`constDF`, as `ntree_node_const_defeq` is.
3. **`refine ⟨_, ?_, .inl ?_⟩` in the `const` clause** — *"don't know how to synthesize implicit
   argument `b`"*: with the equation deferred, `?A` stays unknown.  `.inl rfl` (which *assigns*
   `?A`) then `rw` in the remaining goal is the order that works — as `ntree_csubst_WFD₂` already
   had it; I deviated and paid for it.
4. **`simp` on a membership goal naming `mpNestedName`** — left `¬ _nested.MDep_1.rec =
   mpNestedName` unsolved, because `mpNestedName` is a `def` and `simp` will not unfold it to
   compare literals.  Fixed by writing the literal name and using `decide`.  Same family as row
   143's *"name resolution in this tree has bitten two rounds running"*.
5. **`⟨trivial, trivial, trivial, Nat.lt_succ_self 1⟩` for `csubst_closed`'s `hp`** — its first
   hypothesis is `VExpr.ClosedTele D.params 0`, not the value's closedness; I had read the wrong
   argument.  Fixed to `⟨trivial, trivial⟩` (the `ntreeAux` shape) plus `mpRestore_tyArgs_closedNp`,
   which already existed.

**Where `Classical.choice` comes from, since half the table carries it and half does not.**  The
split is exactly at `mpEnv_ordered`: everything downstream of `VInductDecl'.addInduct'_ordered_final`
or `recType_isType` inherits it, everything purely syntactic or purely `IsDefEq` does not.  Same
provenance as at `ntreeAux` (§30/§33.5).  **No `sorryAx`, no frozen axiom, on any of the 52 new
declarations (49 theorems + 3 `def`s, 772 added lines); `grep -c sorry` in `ParamRedex.lean` = 0.**

## 43. Obligation (B) at `MP` is now reduced to `hbridge` ALONE — and §10's refutation is cashed in

`ParamRedex.lean` §15.

| name | statement | axioms |
|---|---|---|
| `mp_stage₂_exists` | all four staging environments exist **together** — nothing below is hypothetical | `[propext, Quot.sound]` |
| `mp_any_WF₂_false` | **no** `σ` leaving `MP.obj` alone is `CSubst.WF E₂ F₂ U`, for any `U` | `[propext, Quot.sound]` |
| `mp_csubst_WF₂_false` | …in particular the block's own `csubst` | `[propext, Quot.sound]` |
| **`mpAuxB_recConstsR_wf_of_bridge`** | **(B) at `MP`, with `hsrc`/`hσ`/`he₂` all discharged and `hbridge` the only premise** | `[propext, Classical.choice, Quot.sound]` |

`mp_csubst_WF₂_false` completes a sentence §10 of `ParamRedex.lean` had to leave open — *"the
remaining hypotheses hold at `MP.obj`, so the refutation applies here verbatim **once a staging
pair for this block exists**.  (It does not yet: `mpAux mpAuxNodeB` has no `VInductDecl'.WF` …)"*.
It does now.  So at `MP` the strict `CSubst.WF` is **false**, not merely unavailable, and
`mp_csubst_WFD₂` is the only thing that can play `hσ` — the same picture as at `ntreeAux`, now at
the redex block too.

### 43.1 What the residual `hbridge` is — measured with `#eval` first, then landed as `decide`

| measurement | `MP.rec` (j = 0) | `MP.rec_1` (j = 1) | theorem |
|---|---|---|---|
| π-entries, both sides | **6** | **6** | `mp_recTele_len` |
| entries that move | **3** (`[F,F,T,T,T,F]`) | **4** (`[F,F,T,T,T,T]`) | `mp_recTele_moved` |
| body | **identity** | **identity** | `mp_recBody_eq` |
| substituted entry sizes L → R | `[1,5,15,25,33,3]` → `[1,5,11,21,29,3]` | (same first five) | `#eval`, not landed |

Read against `ntreeAux`'s §E (`rTele`, 6 entries, 4 moving, `rBody0` free and `rBody1` moving):
`MP`'s bridge is **one entry shorter in effect and one identity richer**.  Both non-moving prefix
entries are the parameter and the first motive; the sixth entry — the major premise's domain — is
the identity at `MP.rec` and moves at `MP.rec_1`, which is **row 143d's rule for a fifth time**:
*anything indexed by the block's own member restores trivially; the content lives at
companion-pointing positions.*

**And every moving entry moves by the same two β-steps**, read off the `#eval`:

* `mpVal k = (λ α, MDep Prop (λ _, MP α)) k  ⟶  MDep Prop (λ _, MP k)` — at entries 3, 4 and (at
  `MP.rec_1`) 6;
* `mpValNode k = (λ α, MDep.node Prop (λ _, MP α)) k  ⟶  MDep.node Prop (λ _, MP k)` — inside
  entry 5's minor premise only.

So the residual is **two β-lemmas** against §E's three (`rbetaL`/`rbetaNil`/`rbetaCons`), because
`MP`'s substitution has three values to `NTree`'s four and one of them (`MP.rec_1`) is a bare
constant rather than a lambda (`mp_csubst_rec_val`) and therefore never produces a redex.

**I did not attempt `hbridge`.**  Stated as a conjecture, not a measurement: it is §E's job with
one fewer β-lemma and one more identity, i.e. **smaller** than §E — but §E cost a full round, and
three of the six costings in this corner were wrong in the optimistic direction, so treat "smaller
than §E" as an ordering, not a number.

### 43.2 Anti-vacuity, to the standard the brief set

* **`mpAuxB_WF` carries genuine conversion content** — `mp_redex_ne_canonType` (`decide`) plus one
  `IsDefEq.beta`.  Reported above; it is the first `VInductDecl'.WF` in the tree whose positivity
  clause is not `rfl`-shaped at some field.
* **`mp_csubst_WFD₂` carries genuine conversion content** — its `const` clause at `MP.obj` takes
  the defeq disjunct, and the strict alternative is `decide`-refuted (`mp_const_clause_ne`, §10)
  *and* the whole strict statement is now refuted (`mp_csubst_WF₂_false`).  Its `val` clause at
  `_nested.MDep_1.node` is a `defeqDF` (one β), not a bare `val_of_hasType`.
* **Obligation (A) at `MP` carries genuine conversion content** — one `IsDefEq.beta` at the field
  type, with the strict equation refuted by `mp_const_clause_ne`.
* **Negative results, reported as such** (five identities): `mpObj`'s own field `pos` clause is
  `rfl`-shaped; both recursor **bodies** are identities (`mp_recBody_eq`); the parameter and first
  motive entries never move; and `MP.rec`'s major-premise domain never moves.
* **The `WFD` weakening count**: two proved `WFD₂` instances in the tree now, using the new
  freedom at exactly **two** constants total (`NTree.node`, `MP.obj`).  Eleven other constants
  across the two instances take the strict disjunct.

## 44. Where I disagree with the brief, and the verification gap

### 44.1 Two corrections, both in the "smaller than briefed" direction

1. **The brief said "(B) at `MP` dies on `hsrc`, which wants `VInductDecl'.WF (mpAux
   mpAuxNodeB)`, and that is absent … a well-formedness proof, not more substitution machinery."**
   The premise is **correct** (checked structurally: no `mpAux` outside `ParamRedex.lean`).  But
   the framing under-sold it in one direction and over-sold it in another:
   * **Under-sold**: the `WF` is not merely available, it is available **over an arbitrary
     environment** — `mpAuxB_WF : ∀ {env}, VInductDecl'.WF env (mpAux mpAuxNodeB)`.  There is no
     history obligation in it at all, because `VInductDecl'.WF.ctors` is staged over
     `addIndTypes`, which declares both block members.  Reading `ntreeAux_WF` again with that in
     mind, **its `h : addInduct' listDecl = some env₁` looks like dead weight too** — it is
     carried by an enclosing `include`, and the two staged-constant lemmas it calls use only
     `hs`.  *Flagged as a reading of the source, NOT machine-checked*: the hypothesis is a section
     variable, so `lean_minimal_hypotheses` (which matches explicit binders in the theorem's own
     source) cannot decide it, and I did not restate `ntreeAux_WF` to find out.  If it is dead
     weight, the fact is about the *predicate*, not about either witness.
   * **Over-sold**: `hsrc` was **not** the only thing missing.  `he₂` needed obligation (A), and
     `hσ` needed a whole `CSubst.WFD` instance.  The brief's sentence reads as though `WF` were
     the single blocker; it was one of three, and the other two were about half the work.  Both
     came out of the same template, though, so the "not more substitution machinery" half was
     wrong in letter and right in spirit: **no new apparatus was needed, but the `ntreeAux`
     apparatus had to be instantiated three times.**
2. **`VInductDecl'.WF` does not require `Canonical`, and that is why a redex block passes it.**
   Nothing in the brief said otherwise, but §10 of `ParamRedex.lean` reads as though the redex
   were an obstruction to well-formedness; it is not, because `pos`'s last conjunct is an
   `IsDefEqType`.  Worth stating flatly so nobody re-derives it: **a stored redex is admissible
   in `WF` exactly when it contracts to the canonical application**, and at every block this
   corner has produced that is one β step.

### 44.2 The verification gap, stated as reasoning and not as measurement (row 135d's rule)

* **Per-module builds only, as briefed**: `lake build Lean4Lean.Theory.Inductive.ParamRedex
  Lean4Lean.Theory.Typing.ConstSubstNested Lean4Lean.Theory.Inductive.NestedTele` → **72 jobs,
  green**, both at baseline and after every landing.  `ParamRedex.lean` emits **no warnings**.
* **No tree-wide build, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`** — two
  other streams are editing (`git status` shows `Theory/Equiconsistency.lean` modified and
  `Theory/SetModel/EqOracle.lean` untracked, neither mine).
* **`MemberRedexScan`: not run, and I am confident it is unmoved, but that is an argument.**
  It imports `Experimental/ConeJoin.lean`, i.e. the whole tree including the two files another
  stream is mid-edit in, so running it would build their work in progress.  Grounds for expecting
  **49 blocks / 796 fields / 4 defects in 4 blocks / 4 covered / residual 0** unchanged: I added
  **no `inductive` declaration** and no new block; `ParamRedex.lean` was already listed in
  `ConeJoin.lean` (row 133c), so the population already saw it; my 52 additions are 49 theorems
  plus three `def`s of type `VExpr`/`CSubst`.  The scan's population is Lean inductive blocks, which I
  did not touch.
* **No `sorry` added, none traded, no new frozen-axiom dependency**: `grep -c sorry` in
  `ParamRedex.lean` = **0**; every new declaration prints `[propext, Quot.sound]` or
  `[propext, Classical.choice, Quot.sound]`, the `Classical.choice` inherited from
  `addInduct'_ordered_final`/`recType_isType` exactly as at `ntreeAux`.
* **No collisions**: all 52 new top-level names checked tree-wide by `grep -E "^(theorem|def)
  <name>"`; each occurs exactly once.  All live in namespace `Lean4Lean.MRedex.MPWit`.
* **Files touched**: `Lean4Lean/Theory/Inductive/ParamRedex.lean` (810 → 1582 lines) and this
  document.  Nothing else — no frozen file, no implementation, no `Experimental/ConeJoin.lean`, no
  `Theory/SetModel/*`, no `Theory/Typing/*`, no `implGapWhitelist`, no git operation, no network.
* **Which tool backs which search claim**: `lean_local_search` and `lean_hammer_premise` are
  broken here as the brief says, and I did not use them.  Structural claims about what does and
  does not exist in the tree (`VInductDecl'.WF (mpAux mpAuxNodeB)` absent; no name collisions;
  who imports `ConstSubstNested`) are `grep -rn --include=*.lean` over `Lean4Lean/`.  Everything
  else is `lean_diagnostic_messages` on the open file, `lake build`, `#print axioms`, `#eval` and
  `decide`.

## 45. Ledger rows this round needs (I did **not** edit `docs/vacuity-ledger.md`)

1. **`VInductDecl'.WF` holds at the parameterised REDEX block, over an arbitrary environment** —
   `MRedex.MPWit.mpAuxB_WF`.  The thing five rounds of handoffs named as the blocker (§33.8, §40
   item 2, row 141d) is one `IsDefEq.beta`, because `WF`'s positivity clause is a defeq, not an
   equation.  Non-vacuity: `mp_redex_ne_canonType` (`decide`).
2. **…and with it `hsrc`, obligation (A), `he₂` and `hσ` at `MP`** — `mp_recConsts_wf`,
   `mpAuxB_ctorConstsCR_wf`, `mpF₂_ordered`, `mp_csubst_WFD₂` — so **(B) at the redex block is
   reduced to `hbridge` alone** (`mpAuxB_recConstsR_wf_of_bridge`), the position `ntreeAux` was in
   after `ConstSubstNested.lean` §D.  Every one of these is the `ntreeAux` proof re-instantiated;
   **no new apparatus was needed**, which is the half of row 141d's verdict that was right.
3. **A row correcting row 141d in the optimistic direction, and the brief with it.** *"(B) there
   dies on `hsrc` … so the next block needs a well-formedness proof, not more substitution
   machinery."*  True of `hsrc`; but `hσ` and `he₂` were **also** missing and were about half the
   work.  *Guard:* when a route has three environment inputs, "which one is missing" is a
   three-way question; naming one and stopping reads as naming all three.
4. **A row for `mp_csubst_WF₂_false`** — §10 of `ParamRedex.lean` said the refutation *"applies
   here verbatim once a staging pair for this block exists (it does not yet)"*.  It exists now
   (`mp_stage₂_exists`), so the strict `CSubst.WF` is **false** at the redex block's staging pair
   too, for every `U` and every `σ` fixing `MP.obj`.  Second block at which `WFD` is not a
   convenience.
5. **A row for `type_tac`'s universe limitation** (§42.4 item 2): `type_tac` discharges
   `VLevel.WF U l` by `decide`, so it cannot be used under a **variable** `U`; a `U`-generic lemma
   must be built by hand.  Six errors, all from one cause.  Different from row 141b (a hypothesis
   nobody audited) and from row 143's `decide`-domain row: the tool works and is honest, and its
   *precondition* is undocumented.
6. **A fifth instance of the identity trap** (rows 127f, 129b, 143d): at `MP` **both** recursor
   bodies are identities (`mp_recBody_eq`) and `MP.rec`'s major-premise domain never moves, while
   `MP.rec_1`'s does.  The rule now has five confirmations and no counterexample: *anything
   indexed by the block's own member restores trivially.*
7. **A row for `VInductDecl'.WF`'s environment-genericity**: `mpAuxB_WF` needs **no** history
   environment, and `ntreeAux_WF`'s history hypothesis *appears* (read, not machine-checked) to be
   dead weight carried by an `include`.  Not a bug, but it made two handoffs read as though block
   well-formedness needed a history, which is part of why §33.8's residual looked larger than it
   was.

## 46. What I would pick up first

1. **`hbridge` at `MP`** — the single remaining premise of `mpAuxB_recConstsR_wf_of_bridge`, and
   then (B) at a **redex** block.  §43.1 is the measurement to work from: 6 entries, 3 and 4
   moving, both bodies free, two β-lemmas (`mpVal k` and `mpValNode k`).  Model it on
   `ConstSubstNested.lean` §E (`rA0`–`rA5`, `rTele`/`rTeleR`, `rE2`–`rE5`, `rTeleDefEq`,
   `rhbridge`) — the shape is identical and one entry shorter.
2. **Then (C) at `MP`**, which needs `E₃`/`F₃`, `mp_csubst_WFD₃` (`CSubst.WFD.mono` carries
   `WFD₂` wholesale — §35.1's lesson), and the `iotaRulesRS_wf_of_hargsD` route.  §36/§37 at
   `ntreeAux` is the template, and `MP` has **two** ι-rules to `NTree`'s three.
3. **Move `mrDepDecl_WF` beside `mrDepDecl`** in `Theory/Inductive/MemberRedex.lean`.  I put it in
   `ParamRedex.lean` to avoid touching the file `MemberRedexScan` reads while another stream was
   working; it belongs with the block it is about, and `MRWit.MJ`'s own development will want it.
4. **Ask the human the `CSubst.WF` question** — unchanged from §40 item 3 and now sharper by one
   block: `CSubst.WF` is refuted at **both** proved staging pairs (`ntree_csubst_WF₃_false`,
   `mp_csubst_WF₂_false`) and `WFD` is proved at both, using its new freedom at exactly two
   constants.  Nothing in the tree needs the strict `const` clause.
5. **Run the tree-wide suite** once `Theory/SetModel/*` settles — do not take §44.2 on trust.
6. **`Built.fields_noK`** — still out of scope, seventh round untouched (row 117c).

# Round 7 (2026-09-02, seventh stream): `hbridge` at `MP` PROVED, (B) discharged at a REDEX block — and the brief's β-lemma count was one short

*Written incrementally, as briefed.*

## 47. `#print axioms` FIRST — the brief's premise CHECKS OUT in every particular

Baseline per-module build before touching anything: `lake build Lean4Lean.Theory.Inductive.ParamRedex
Lean4Lean.Theory.Typing.ConstSubstNested Lean4Lean.Theory.Inductive.NestedTele` → **72 jobs,
green** (HEAD `b5eee60`, working tree clean — the two files the last two rounds saw as
mid-edit/untracked are both committed now, including `Theory/Inductive/NestedRules.lean`, so
row 143e's residual worry is closed).

Everything the brief named, by **namespace**.  All in `Lean4Lean.MRedex.MPWit` unless stated:

| declaration | axioms | matches the brief? |
|---|---|---|
| `mpAuxB_recConstsR_wf_of_bridge` | `[propext, Classical.choice, Quot.sound]` | yes — (B) at `MP` with `hbridge` its only premise |
| `mpAuxB_WF` | `[propext, Quot.sound]` | yes — hypothesis-free, environment-generic |
| `mp_recConsts_wf` (`hsrc`) | `[propext, Classical.choice, Quot.sound]` | yes |
| `mpAuxB_ctorConstsCR_wf` (obligation (A)) | `[propext, Classical.choice, Quot.sound]` | yes |
| `mpF₂_ordered` (`he₂`) | `[propext, Classical.choice, Quot.sound]` | yes |
| `mp_csubst_WFD₂` (`hσ`) | `[propext, Classical.choice, Quot.sound]` | yes |
| `mp_recTele_len`, `mp_recTele_moved`, `mp_recBody_eq` | `[propext, Quot.sound]` | yes — 6/6 entries, `[F,F,T,T,T,F]` and `[F,F,T,T,T,T]`, both bodies identities |
| `mp_csubst_rec_val` | `[propext, Quot.sound]` | yes — `_nested.MDep_1.rec ↦ MP.rec_1` really is a bare constant |
| `mp_stage₂_exists`, `mp_csubst_WF₂_false` | `[propext, Quot.sound]` | yes |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_iotaRulesRS_wf_of_nine` | `[propext, Quot.sound]` | yes — the (C) template, and free of `Classical.choice` |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_obligationC_of_hdata` / `_obligationC` / `_addInductR_ordered` | `[propext, Classical.choice, Quot.sound]` | yes |
| `Lean4Lean.VEnv.iotaRulesRS_wf_of_hargsD` | `[propext, Classical.choice, Quot.sound]` | yes |
| `Lean4Lean.InductiveDeclExamples.rhbridge`, `rTeleDefEq` | `[propext, Quot.sound]` | yes — §E is the template it is said to be |

No `sorryAx` and no frozen axiom on any of them.  **Nothing in §§41–46 was over-claimed and
nothing was already-done-but-reported-open.**  Also checked structurally (`grep -rn` over
`Lean4Lean/`, since `lean_local_search`/`lean_hammer_premise` are broken here as briefed): no
`hbridge`-at-`MP` statement existed anywhere — the only `hbridge` occurrences outside
`ConstSubstNested.lean`'s own general lemmas are `rhbridge` and `..._of_bridge`.

## 48. `hbridge` at `MP` is PROVED, and obligation (B) is DISCHARGED at the parameterised REDEX block

`Theory/Inductive/ParamRedex.lean` §16, namespace `Lean4Lean.MRedex.MPWit`, module green at
**72 jobs** after every landing.  **56 new declarations** (32 theorems + 24 `def`s), `grep -c sorry`
= 0, no new import.

| name | statement | axioms |
|---|---|---|
| `mpNt`/`mpDt`/`mpNdt`, `mpVc`/`mpNc`/`mpFd` | the three constants and the three redex/contractum families | no axioms (defs) |
| `mpA0`–`mpA5₁'`, `mpTele₀/R₀/₁/R₁`, `mpBody₀/₁` | the two substituted telescopes, written out | no axioms (defs) |
| `mprecType_eq_0/_1`, `mprecTypeR_eq_0/_1` | the four `mkPi` decompositions `hbridge` asks for — all **`rfl`** | `[propext, Quot.sound]` |
| `mpPC`, `mpObjC` | `MP` and `MP.obj` as self-defeqs at the types the environment holds | `[propext]` |
| **`mpBetaV`** | β-step 1: `mpVal #k ⟶ MDep Prop (λ _, MP #(k+1))` | `[propext, Quot.sound]` |
| **`mpBetaN`** | β-step 2: `mpValNode #k ⟶ …` (needs `hP`/`hNd` only — **not** `hD`) | `[propext, Quot.sound]` |
| **`mpBetaF`** | β-step 3: the block's **stored** field redex — the one §15.1's count missed | `[propext]` |
| `mpE2`, `mpE3`, `mpE4`, `mpE5₁` | the four moving telescope entries | `[propext, Quot.sound]` |
| `mpTeleDefEq₀`, `mpTeleDefEq₁` | `F.TeleDefEq 1 [] mpTele mpTeleR` at both recursors | `[propext, Quot.sound]` |
| `mpB₀`, `mpB₁` | the two bodies — identities, and needing **no** environment hypothesis | `[propext]` |
| **`mphbridge`** | **`hbridge` at `MP`, both recursors** | `[propext, Quot.sound]` |
| `mp_objType_eq` | `MP.obj`'s declared type written out (`rfl`) | `[propext, Quot.sound]` |
| **`mpAuxB_recConstsR_wf`** | **obligation (B) at the parameterised REDEX block** | `[propext, Classical.choice, Quot.sound]` |
| **`mpAuxB_obligationB`** | …**with nothing assumed** (staging from `mp_stage₂_exists`) | `[propext, Classical.choice, Quot.sound]` |
| §16.4's ten certificates | anti-vacuity, all `decide`/`rfl` | `[propext, Quot.sound]` or none |

The `Classical.choice` on the last two is inherited, and only there: it comes through
`mpF₂_ordered`/`mp_recConsts_wf` from `mpEnv_ordered`, i.e. from
`VInductDecl'.addInduct'_ordered_final`/`recType_isType`, exactly the provenance §42.4 measured.
**Nothing else in §16 carries it** — the whole bridge is `[propext, Quot.sound]` or less, and three
of its pieces (`mpB₀`, `mpB₁`, `mpBetaF`, `mpPC`, `mpObjC`) are `[propext]` alone.

### 48.1 Where the brief is WRONG, machine-checked: **three** β-lemmas, not two

§15.1 / row 150c / the brief all say *"two β-lemmas suffice (`mpVal k`, `mpValNode k`) against §E's
three, because `_nested.MDep_1.rec ↦ MP.rec_1` is a bare constant"*.  The **reason** is right and
the **count is one short.**

Two β-lemmas suffice for the entries that *move*.  They do not suffice for the derivation, because
entry 4 — the companion constructor's minor premise — contains the block's own **stored field
redex** `(λ _ : Prop, MP #(m+1)) #k`.  It is *identical on both sides* of the bridge (it is indexed
by member `0`, i.e. `MP` itself — row 143d), so it contributes nothing to `TeleDefEq`; but the
induction hypothesis `#4 #0` of that minor premise cannot be **typed** without contracting it,
because the motive for `MP` expects `MP α` and the field is declared at the redex.  So `mpBetaF`
exists, is used twice inside `mpE4` (once for the binder's own self-defeq via `.trans … .symm`,
once as the `defeqDF` on the IH's argument), and moves nothing.

Machine-checked, not argued:

* `mpA4_field_shared` (`rfl`) — the redex `mpFd 4 0` occurs, unchanged, in **both** `mpA4` and
  `mpA4'`;
* `mpFd_ne` (`decide`) — and it is a redex, not already its own contractum.

**This is the first place in this corner where being a *redex block* costs the bridge anything**,
and it is exactly the cost row 129b predicted in a different place: `ntreeAux` has no such entry
because it is `Canonical`.  *Guard for the next brief:* a β-lemma count read off "which entries
move" undercounts by the redexes the restoration **preserves** — moving and needing-a-conversion
are different questions, and a redex block has entries in the second class that are not in the
first.

### 48.2 A second, smaller correction, in the optimistic direction

§15.1 records "both bodies are identities" as a negative result.  Measured: they are *freer* than
that — `mpB₀` and `mpB₁` need **no environment hypothesis at all** (Lean's unused-section-variable
linter is the instrument: it rejected `include hP`).  Each is two `Lookup`s and one `appDF`.  So
the two identity bodies cost nothing even in hypotheses, where `ntreeAux`'s `rB0`/`rB1` both need
constant lookups (`rB0` needs `hN`, `rB1` needs `hL`/`hN`) because *their* bodies mention `NTree`
and `List`.

### 48.3 Anti-vacuity for `hbridge` at `MP`, to the standard the brief set

**Genuine conversion content, established by `decide`:**

* four of six telescope entries move at `MP.rec_1` and three of six at `MP.rec`: `mpA2_ne`,
  `mpA3_ne`, `mpA4_ne`, `mpA5₁_ne`, and the whole lists differ (`mpTele₀_ne`, `mpTele₁_ne`) — so
  `TeleDefEq.cons`, the disjunct that costs a real `IsDefEq`, is taken three and four times and
  the free `TeleDefEq.rfl` three and two times;
* the **equation** form of the bridge is false at *both* recursors — `mp_recTypeR_bridge_false`
  (§6, `j = 0`, pre-existing) and **`mp_recTypeR_bridge_false_1`** (new, `j = 1`) — so `mphbridge`
  cannot come from `VEnv.recConstsR_wf_of_substC_of_eq`, and (B) at `MP` is not an identity in
  disguise;
* and the whole route's `hσ` is *refuted* in strict form at this pair (`mp_csubst_WF₂_false`,
  §15), so `mp_csubst_WFD₂`'s defeq disjunct is load-bearing.

**Negative results, reported as such — three of them, and one is new:**

1. `MP.rec`'s major-premise domain never moves (`mpA5₀_eq`) — row 143d's rule, **sixth**
   confirmation, no counterexample yet.
2. Both recursor bodies are identities (`mp_recBody_eq`, pre-existing; `mpBody_eq`), and §48.2
   sharpens this to "identities that need no hypotheses".
3. **New**: the stored field redex is preserved by the restoration (`mpA4_field_shared`) — so the
   third β-lemma is pure typing, not conversion content.  That is a *fourth* identity-at-the-
   block's-own-member instance in this file alone.

**The `WFD` weakening count, unchanged by this round**: `WFD` is used in three proved instances
tree-wide (`ntree_csubst_WFD₂`, `ntree_csubst_WFD₃`, `mp_csubst_WFD₂`) and the new freedom is
taken at exactly **three** constants (`NTree.node`, `NTree.rec`, `MP.obj`).  §16 adds no `WFD`
instance and no use of the slack, so the brief's "a weakening everything suddenly satisfies is
suspect" check still passes with the same margin.

## 49. …and then obligation (C) too, and `Ordered` AT A NON-CANONICAL BLOCK

The brief named (C) as the follow-on and told me to establish what it needs from source first.  I
did (§49.1), found the residual smaller than the `ntreeAux` analogue in three places, and closed it.

`ParamRedex.lean` §§17–18.  **Both new obligations are theorems with nothing assumed, and all three
of `VEnv.addInductR_ordered'`'s obligations now hold at a block that is provably not `Canonical`.**

| name (namespace `Lean4Lean.MRedex.MPWit`) | statement | axioms |
|---|---|---|
| `mpTeleP`/`mpTelePR`, `mpTeleDefEq_ext` | the five-entry prefix every telescope and ι-context shares | `[propext, Quot.sound]` |
| `mpIotaCtx_obj_eq`/`_R_obj_eq` | **the `MP.obj` ι-context IS `mpTele₁`/`mpTeleR₁`** (`decide`) | `[propext, Quot.sound]` |
| `mpIotaCtx_node_eq`/`_R_node_eq` | the companion rule's = prefix ++ `[Prop, mpFd 5 0]` (`decide`) | `[propext, Quot.sound]` |
| `mpAuxB_recArg_lt` | `hpos`, by `decide` over list membership | `[propext]` |
| **`mpIotaTele_obj`, `mpIotaTele_node`** | **`htele` at both ι-rules** | `[propext, Quot.sound]` |
| **`mpIotaHargs_obj`, `mpIotaHargs_node`** | the two residual `∃ A₀ v` triples | `[propext, Quot.sound]` |
| `mp_recConsts_eq`, `mp_recConstsR_eq` | the two lists the recursor stage folds (`rfl`) | `[propext]` / `[propext, Quot.sound]` |
| `mpIsTypeA0/A1`, `mpOnCtx₀`, `mpOnCtx₁` | the two recursor telescopes are contexts | `[propext]` / `[propext, Quot.sound]` |
| `mpRecPi0`, `mpRecPi1` | the whole-pi conversions (`mkPi_congrU` over §16) | `[propext, Quot.sound]` |
| `mpRecConstClause0/1`, `mpNestedRecVal` | …in `WFD.const`'s and `WFD.val`'s exact shapes | `[propext, Quot.sound]` |
| `mp_fresh₃`, `mpAuxB_stagedE₃`, `mpAuxB_stagedF₃`, **`mp_stage₃_exists`** | the third staging pair exists | `[propext, Quot.sound]` |
| `mpF₃_ordered`, `mpF₃_mdep/_mdepNode/_mp/_obj/_rec/_rec1` | the ι-stage environment | `[propext(,Classical.choice), Quot.sound]` |
| **`mp_csubst_WFD₃`** | **`hσ` at the ι-rule staging pair** | `[propext, Classical.choice, Quot.sound]` |
| `mpAuxB_hdata` | `hdata` at both rules | `[propext, Quot.sound]` |
| **`mpAuxB_iotaRulesRS_wf`** | **OBLIGATION (C) at the parameterised REDEX block** | `[propext, Classical.choice, Quot.sound]` |
| **`mpAuxB_obligationC`** | …with nothing assumed | `[propext, Classical.choice, Quot.sound]` |
| `mpAuxB_admitted`, `mpAuxB_stages` | the step is admissible and its three stages exist | `[propext, Classical.choice, Quot.sound]` |
| **`mpAuxB_addInductR_ordered`** | **the nested declaration step preserves `VEnv.Ordered` at a NON-CANONICAL block** | `[propext, Classical.choice, Quot.sound]` |
| `mp_csubst_WF₃_false` | the strict `CSubst.WF` is false at the ι-rule pair too | `[propext, Quot.sound]` |

### 49.1 What (C) at `MP` needed, established from source before starting (as briefed)

`VEnv.iotaRulesRS_wf_of_hargsD`'s nine hypotheses, walked one by one — **all nine, because a
per-hypothesis audit that skips one is not an audit**:

| hypothesis | at `MP`, before this round |
|---|---|
| `hown` | `mpRestore_ownId` — **already in HEAD** (§3) |
| `hat` | `mpRestore_domSep.substAt` — **already in HEAD** (§3), off `mpAuxB_allNames_nodup` + `mpRestore_domNodup`, both `decide` |
| `hfr` | `mpRestore_substFree` — **already in HEAD** (§3) |
| `hσc` | `mp_csubst_closed` — **already in HEAD** (§14) |
| `hσ` | **MISSING**: `WFD` at the *third* staging pair.  Needs the §H analogue (`const` at `MP.rec`) + the §I analogue (`val` at `_nested.MDep_1.rec`, `exfalso` at stage 2) + `E₃`/`F₃` |
| `hI` | `mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃` — free once `hE₃` exists |
| `henv` | **MISSING**: `mpF₃_ordered`, which needs obligation (B) — i.e. §16 had to land first |
| `hpos` | **MISSING but trivial**: `decide` over list membership |
| `hdata` | **MISSING**: `htele` + one `∃ A₀ v` triple per rule, **two** rules |

So the honest count was **five** missing, of which two are one-liners.  Measured before proving
(`#eval`), then landed as `decide` — and the residual came out *smaller* than the `ntreeAux`
analogue in three separate places:

1. **`MP` has two ι-rules to `NTree`'s three** (`iotaRules.length = 2`), and `mpAuxB_ctorsAll_eq`
   makes the `∀ q j C` collapse to two named instances.
2. **`htele` is free beyond §16.**  The `MP.obj` rule's substituted ι-context *is* `mpTele₁` on the
   nose (`mpIotaCtx_obj_eq`, `decide`), and the companion rule's two extra entries — the block's own
   `Prop` field and its **stored** field redex — **do not move**, so they are two `TeleDefEq.rfl`s.
   At `ntreeAux` the node and cons rules each needed one extra `rbetaL`.
3. **Both `hfunM`s are a single `Lookup`**, both `hconv`s are one `mpBetaV` (or its `symm`), and
   `hmaj` is **free at `MP.obj`** — `mpMaj_obj_eq` (`decide`), the block's own constructor.  The two
   residual triples came to **4 and 4 lines of proof term**, against `ntreeAux`'s 3, 5 and 5.

And `mp_csubst_WFD₃` went in at **~45 lines on the first attempt**, for exactly the reason §35.1
recorded: `CSubst.WFD.mono` carries the whole of `mp_csubst_WFD₂` from `F₂` to `F₃`, so only the two
constants stage 3 *declares* are new.  That guard has now paid twice.

### 49.2 Anti-vacuity for (C) at `MP`, to the standard the brief set

* **The block really is a redex block and really is parameterised**: `mpAuxB_not_canonical` and
  `mpAuxB_np_one`, both pre-existing, both `decide`/`rfl`.  This is the coordinate that separates
  `mpAuxB_addInductR_ordered` from `ntreeAux_addInductR_ordered`; `nfnAux`'s is `np = 0`.
* **Genuine conversion content, by `decide` not asserted**: the strict ι-rule bridge is refuted
  (`mp_iotaRules_bridge_false`, §6, with `mp_iotaRules_length_eq` ruling out a length artefact);
  both substituted ι-contexts move (`mpIotaCtx_obj_ne`, `mpIotaCtx_node_ne`); `hmaj` moves at the
  companion constructor (`mpMaj_node_ne`); the `const` clause at `MP.rec` takes `WFD`'s **defeq**
  disjunct with the strict alternative refuted (`mp_recTypeR_bridge_false`, §6, and
  `mp_recTypeR_bridge_false_1`, new); and the whole strict `CSubst.WF` is **false** at the ι-rule
  pair (`mp_csubst_WF₃_false`, new) as well as the constructor pair (`mp_csubst_WF₂_false`).
* **Negative results, reported as such — and (C) at `MP` has MORE of them than (C) at `ntreeAux`.**
  `ntreeAux`'s (C) had three identity pieces (`rMaj_node_eq`, `rA0`, `rA1`); `MP`'s has **six**:
  the two non-moving prefix entries (`mpA0`, `mpA1`), `hmaj` at `MP.obj` (`mpMaj_obj_eq`), and the
  companion rule's two extra ι-context entries — of which one is the stored field redex, i.e. row
  143d yet again.  **This is a negative result about the block, and it is the honest half of
  §49.1's "smaller than `ntreeAux`":** a redex block's *own* positions are cheap, and the whole
  cost sits at the companion.
* **The `WFD` weakening count, updated and still honest.**  `WFD` is now proved at **four** staging
  pairs (`ntree_csubst_WFD₂/₃`, `mp_csubst_WFD₂/₃`), and the new freedom is taken at exactly
  **four** constants: `NTree.node`, `NTree.rec`, `MP.obj`, `MP.rec`.  Every other constant in all
  four instances takes the strict `.inl` disjunct — that is one use per instance, and the strict
  `CSubst.WF` is now *refuted* at all four pairs.  So the brief's "a weakening everything suddenly
  satisfies is suspect" check passes with the margin unchanged, and the case for asking the human
  whether `CSubst.WF` should simply **be** `WFD` is now four-for-four.

## 50. What I tried that failed, and the exact step it failed at

1. **`⟨_, .beta … (by type_tac) (.bvar hk)⟩` with `simpa [mpVal, mpVc, VExpr.inst]`** — *"Type
   mismatch: after simplification, term `h` has type … `(VExpr.bvar k).lift` … but is expected to
   have type … `(VExpr.bvar (k+1))`"*, twice.  `VExpr.inst` alone does not discharge the `lift` that
   `.beta` introduces when the substituted variable sits under a binder (`.bvar 1`, not `.bvar 0`).
   Fixed by adding `VExpr.lift, VExpr.liftN` to the simp set — the same fix `rbetaCons` already
   carries and `rbetaL` does not need.  *Guard:* a β-lemma whose redex body mentions the bound
   variable **below** the top level needs the `lift` simp lemmas; one whose body mentions it at
   depth 0 does not, which is why §E's three β-lemmas do not all look alike.
2. **`.const hP nofun rfl` for the head of the field redex** — *"Unknown constant
   `Lean4Lean.VEnv.IsDefEq.const`"*.  `HasType.const` exists (`HasType` is a `def` over `IsDefEq`),
   `IsDefEq.const` does not; the constructor is `constDF`.  Fixed by a named helper `mpPC`
   (`.constDF hP nofun nofun rfl .nil`), mirroring `rNC`.  *Guard:* dot-notation `.const` inside an
   `IsDefEq` goal silently resolves to nothing; the constructor is always `constDF`.
3. **`.defeqDF (.symm (mpBetaV …)))` with one paren too many** in `mpE4` — *"Application type
   mismatch: the argument `VEnv.IsDefEq.defeqDF (…)` has type `… → …`"*, i.e. `defeqDF` was applied
   to the `bvar` as its *only* argument.  Mechanical, but worth the line because the error names
   `appDF` and not `defeqDF`, which sends you to the wrong term.
4. **`hh.trans mp_obj_declared` in `mp_csubst_WF₃_false`** — application type mismatch.
   `VEnv.subst_WF_false_of_const_ne`'s `hne` is `A ≠ ci.type.substC σ`, i.e. **F's type on the
   left**, while `csubst_WF_staged_false` passes it as `fun hh => hne hh.symm`.  I copied the
   `ntreeAux` call site (which has the `.symm` inside its own `hne`) and dropped the flip.  Fixed to
   `hh.symm.trans mp_obj_declared`.  *Guard:* the two refutation lemmas take `hne` in **opposite**
   orientations; check which one you are calling.
5. **`#eval` with `fun p => (p.1, p.2.name)` over `ctorsAll`** — *"Invalid projection: type of `p`
   is not known"*, exactly §38 item 5's trap in a new place.  Fixed by binding `let j : Nat := jC.1`
   / `let C : VIndCtor := jC.2` with explicit ascriptions.  **Third round running that the
   measurement instrument, not the mathematics, is what will not elaborate.**
6. **`lean_run_code` against a just-edited module** — the snippet reported *"Imports are out of
   date"* and then a cascade of *"Function expected at `mpVc`"* / *"unknown identifier `mpNt`"*
   caused by `autoImplicit` turning the missing names into implicit variables.  The diagnostics were
   entirely misleading (they blamed my `nofun`s and my `constDF`, which were fine).  Fixed by
   working **in the file** and reading `lean_diagnostic_messages` instead.  *Guard:* after editing a
   module, `lean_run_code` snippets that import it test the *stale* olean; a stale-import warning at
   line 1 invalidates every error below it.
7. **Not attempted, deliberately**: `Built.fields_noK` (out of scope, row 117c — **seventh** round
   untouched); any frozen file; any implementation file; `Experimental/ConeJoin.lean`;
   `Theory/SetModel/*`; `Theory/Typing/*` (I did **not** need to touch `ConstSubstNested.lean` at
   all this round — everything went into my own `ParamRedex.lean`); `implGapWhitelist`; git, network,
   `lake update`.

## 51. The verification gap, stated as reasoning and not as measurement (row 135d / 150d's rule)

* **Per-module builds only, as briefed.**  `lake build Lean4Lean.Theory.Inductive.ParamRedex
  Lean4Lean.Theory.Typing.ConstSubstNested Lean4Lean.Theory.Inductive.NestedTele` → **72 jobs,
  green**, at baseline and after every landing.  `ParamRedex.lean` emits **no warnings** (the only
  warnings in the three modules are the pre-existing ones in `NestedRules.lean` and the
  unused-section-variable at `ConstSubstNested.lean:1164`, neither touched).
* **No tree-wide build, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`** — as
  instructed.  `MemberRedexScan` imports `Experimental/ConeJoin.lean`, i.e. the whole tree.
  **Labelled as reasoning, not as a run**: I expect its figures unmoved because I added **no
  `inductive` declaration** and no new block (the Lean-level `inductive MP` was already there), and
  `ParamRedex.lean` was already in the scan's population (row 133c).  All 102 additions are 76
  theorems and 26 `def`s of type `VExpr`/`List VExpr`/`Prop`.
* **No `sorry` added, none traded, no new frozen-axiom dependency.**  `grep -c sorry` in
  `ParamRedex.lean` = **0**.  `#print axioms` was run on **all 102** new names (76 theorems +
  26 `def`s), and the tally is exact: **28** depend on no axioms at all (all 26 `def`s plus
  `mpBody_eq` and `mpA4_field_shared`), **10** on `[propext]`, **55** on `[propext, Quot.sound]`,
  and **9** on `[propext, Classical.choice, Quot.sound]` — those nine being
  `mpAuxB_recConstsR_wf`, `mpAuxB_obligationB`, `mpF₃_ordered`, `mp_csubst_WFD₃`,
  `mpAuxB_iotaRulesRS_wf`, `mpAuxB_obligationC`, `mpAuxB_admitted`, `mpAuxB_stages`,
  `mpAuxB_addInductR_ordered`, every one of which inherits `Classical.choice` from
  `mpEnv_ordered` / `recType_isType` / `Exists.choose`, all measured as carrying it already in
  §42.4 and §30.  **`grep -c sorryAx` over the 102 prints = 0; no frozen axiom on any of them.**
* **No collisions**: all 102 new top-level names checked tree-wide with
  `grep -rhoE "^(theorem|def) <name>( |$|\{|\()"` over `Lean4Lean/`; each occurs exactly once.  All
  live in namespace `Lean4Lean.MRedex.MPWit`.
* **Files touched**: `Lean4Lean/Theory/Inductive/ParamRedex.lean` (1582 → 2523 lines, +941) and this
  document.  Nothing else — **not even `ConstSubstNested.lean`**, which I own but did not need.
* **HEAD did not move under me** (`b5eee60` throughout), and the working tree was clean when I
  started — so, unlike rounds 4 and 5, no other stream's files were in flight.
* **Which tool backs which search claim.**  `lean_local_search` and `lean_hammer_premise` are broken
  here as briefed; I did not use them.  Structural claims about what exists in the tree (no
  `hbridge` at `MP`; no name collisions; which module defines `CSubst.WFD` and whether
  `ParamRedex.lean` can see it through `NestedTele → NestedRules → RestoreBridge →
  ConstSubstNested`) are `grep -rn --include=*.lean` over `Lean4Lean/`.  Everything else is
  `lean_diagnostic_messages` on the open file, `lake build`, `lake env lean` for `#print axioms`,
  `#eval` and `decide`.

## 52. Ledger rows this round needs (I did **not** edit `docs/vacuity-ledger.md`)

1. **ALL THREE of `addInductR_ordered'`'s obligations now hold at a NON-CANONICAL (REDEX) block**, so
   `VEnv.Ordered` is preserved by the nested declaration step there: `mpAuxB_recConstsR_wf` (B),
   `mpAuxB_iotaRulesRS_wf` (C), `mpAuxB_addInductR_ordered`, each also in a hypothesis-free form
   (`mpAuxB_obligationB`, `mpAuxB_obligationC`).  Until now the blocks with all three were `nfnAux`
   (`np = 0`) and `ntreeAux` (`np = 1`, **`Canonical`**); `mpAux mpAuxNodeB` is neither
   (`mpAuxB_np_one`, `mpAuxB_not_canonical`).  Non-vacuity in §48.3/§49.2, all by `decide`.
2. **The brief's β-lemma count was one short, and the reason generalises.**  Row 150c says *"two
   β-lemmas suffice against §E's three"*.  Two suffice for the entries that **move**; a third
   (`mpBetaF`) is needed for the block's own **stored** field redex, which the restoration
   *preserves* (`mpA4_field_shared`, `rfl`) but which must still be contracted for the companion
   minor premise's induction hypothesis to be typed (`mpFd_ne`, `decide`).  **Guard: a β-lemma count
   read off "which entries move" undercounts by the redexes the restoration preserves.**  Moving and
   needing-a-conversion are different questions, and only a *redex* block has entries in the second
   class that are not in the first — which is why `ntreeAux` did not show it.  Pairs with row 143c:
   there a bundled measurement was transferred to a decomposition; here a *movement* measurement was
   transferred to a *derivation*.
3. **A row correcting row 150c in the optimistic direction as well**: the two identity bodies are
   *freer* than "identities" — `mpB₀`/`mpB₁` need **no environment hypothesis at all** (Lean's
   unused-section-variable linter refused `include hP`), where `ntreeAux`'s `rB0`/`rB1` both need
   constant lookups.  Two corrections to one row, in opposite directions, from the same measurement.
4. **A row for (C) at `MP` being smaller than (C) at `ntreeAux`, with the reason.**  Two ι-rules to
   three; the `MP.obj` ι-context **is** the `MP.rec_1` telescope on the nose (`mpIotaCtx_obj_eq`,
   `decide`); the companion rule's two extra entries **do not move** (against one moving `rbetaL`
   each at `ntreeAux`'s node and cons); `hmaj` free at `MP.obj`; residual triples of **4 and 4**
   lines against **3, 5 and 5**.  *And the honest half:* that is because a redex block's own
   positions are cheap — **six** identity pieces in (C) at `MP` against three at `ntreeAux`.
5. **A row for `CSubst.WFD.mono` paying twice** (row 143c's third item): `mp_csubst_WFD₃` went in at
   ~45 lines on the first attempt, because `.mono` carries `WFD₂` from `F₂` to `F₃` wholesale and
   only the two constants stage 3 declares are new.  Second confirmation of *"before re-doing a
   staged proof one layer up, ask whether the hypothesis is monotone in the layer."*
6. **A row for the `WFD`-versus-`WF` question, now four-for-four.**  `CSubst.WF` is **refuted** at
   all four staging pairs where `WFD` is proved (`ntree_csubst_WF₂_false`/`WF₃_false`,
   `mp_csubst_WF₂_false`/**`WF₃_false`** new), and `WFD`'s new freedom is used at exactly **four**
   constants across the four instances — one each.  Nothing in the tree needs the strict `const`
   clause; `CSubst.WF.wfd` shows the `np = 0` witnesses survive.  The question for the human is
   unchanged and now has four data points instead of two.
7. **A seventh confirmation of row 143d, and it is starting to look like a theorem rather than a
   pattern.**  `mpA5₀_eq` (the major premise at `MP.rec`), `mpMaj_obj_eq` (`hmaj` at `MP.obj`),
   `mpA4_field_shared` (the stored field) and the companion ι-rule's two extra entries all restore
   trivially, and every one of them is indexed by the block's own member.  Seven instances, no
   counterexample.  **Someone should try to prove it** — `VIndRestore.OwnId` plus
   `substC_tyApp_comp` look like the ingredients — because it is now doing real predictive work in
   every costing in this corner.
8. **A row for the two tool traps** (§50 items 5 and 6): `#eval`'s tuple projections still need
   explicit ascriptions (third round), and **`lean_run_code` against a just-edited module tests the
   stale olean** and then produces a cascade of `autoImplicit`-manufactured errors that blame the
   wrong terms.  The instrument was misleading in a way that would have cost hours if I had believed
   it; the fix was to work in the file and read diagnostics.
9. **A row for the verification gap** (fifth round): per-module builds only, everything tree-wide
   deferred, grounds in §51 labelled as reasoning.

## 53. What I would pick up first

1. **Try to prove the identity rule as a theorem** (§52 item 7).  It has seven machine-checked
   instances, no counterexample, and it is what every costing in this corner now leans on.  Shape:
   *at a position indexed by a member the block itself declares, `VIndRestore.OwnId` makes
   `ctorAppR`/`tyApp'`/`fieldTypesR` equal to their unrestored forms.*  If it is true, the per-block
   cost of (A)/(B)/(C) becomes "one β-lemma per companion constructor" and can be **predicted**
   instead of measured each time.  If it is false, the counterexample is worth more.
2. **A third parameterised block, to test §40 item 4's conjecture.**  Two are now done — `ntreeAux`
   (canonical) and `mpAux mpAuxNodeB` (redex) — and the residual at both is "one β-lemma per
   companion constructor, plus one per *stored* redex".  My honest read, **stated as a conjecture,
   not a measurement**: the shape generalises, the count is `(number of companion constructors) +
   (number of stored redexes)`, and the second summand is what round 6's brief missed.  A block with
   **two** companion members or **two** parameters would test both halves.
3. **Ask the human the `CSubst.WF` question** — §52 item 6.  Four-for-four now.  It is a
   `Theory/Typing/ConstSubst.lean` edit, another stream's file, and it would delete four `.mono`/
   `.wfd` transports and ~40 `WFD`-mentioning signatures.
4. **Move `mrDepDecl_WF` beside `mrDepDecl`** in `Theory/Inductive/MemberRedex.lean` — unchanged from
   §46 item 3, still not done, still one `git mv`-sized edit.  `MRWit.MJ`'s own development will want
   it, and `MemberRedexScan`'s file is no longer being edited by anyone.
5. **Run the tree-wide suite** — guards, `sorry-census`, `dup-names`, `MemberRedexScan`.  Do not take
   §51 on trust.
6. **`Built.fields_noK`** — still out of scope, **seventh** round untouched (row 117c).

## 54. The empirical rule is now a THEOREM — "heads decide", and `NoConsts` was the wrong test

Assignment: turn *"anything indexed by the block's own member restores trivially; the content lives
at companion-pointing positions"* — seven confirmations, no counterexample — into a theorem, at
whatever generality it holds, with the side condition named and tested.

**Result: proved, at a generality strictly greater than the seven confirmations use.**  Nothing was
refuted; but the brief's recommended route is **not** what the theorem needs, and I say where below
(§54.3).

### 54.1 The statement, and why the two existing lemmas both fell short

`Theory/Inductive/Restore.lean`, new block after `restore_noK` (all four in `VIndRestore`, plus one
inductive in `VInductDecl'`):

| name | content |
|---|---|
| `VIndRestore.uniformOcc?_spec_head` | the trigger's success identifies the *head*: `∃ T ls, D.types[j]? = some T ∧ e.spineFn = .const T.name ls` (this was inline inside `uniformOcc?_tyAppR_eq`'s proof and is now a lemma) |
| `VIndRestore.restore_ownOcc` | **the rule at one occurrence**: `D.uniformOcc? k e = some (j, rest) → D.types[j]? = some T → T.name ∉ K → R.restore D k e = e`, given `R.OwnId D K`. **No hypothesis whatever on `e`'s residual arguments.** |
| `VInductDecl'.OwnHeads D K : Nat → VExpr → Prop` | the rule closed under the congruences: an inductive predicate with `own` (trigger fires, member off `K` — and the walk **stops there**), `const` (a bare constant off `K`), and `app`/`lam`/`forallE` congruences carrying the depth |
| `VIndRestore.restore_ownHeads` | **the theorem**: `R.OwnId D K → D.OwnHeads K k e → R.restore D k e = e` |
| `VIndRestore.ownHeads_of_noConsts` | `VExpr.NoConsts K e → D.OwnHeads K k e`, so `restore_noK` is a corollary — the implication is recorded between the *hypotheses*, not just the conclusions |

The reason `restore_noK` (the brief's "closest existing general statement" — correct) is not the
rule: it asks `VExpr.NoConsts K` of the **whole** subterm, i.e. of every constant occurring in it.
The rule as used only ever looks at **heads**.  `restore`'s `some` branches hand the residual
arguments to `tyAppR` *unrestored* — "the operator does not descend into a replacement", which the
file's own docstring says about `restore` but which no lemma had cashed in — so at an own-member
uniform occurrence the restoration is the identity *whatever the arguments contain*, companion
constants included.  That is the whole content of `restore_ownOcc`, and it is where the generality
comes from.

**Side condition, named:** the occurrence must be *uniform* — `D.uniformOcc?` must fire, i.e. the
head is a block member at level list `D.ownLvls` and its **first `D.np` arguments are exactly
`bvars k D.np`**.  If the head is the block's own member but the parameters are not passed through,
the trigger returns `none`, `restore` descends, and a companion constant deeper inside **does**
move.  So the rule is not "own head ⇒ trivial"; it is "own head *at a uniform occurrence* ⇒
trivial".  `OwnHeads.app`'s `D.uniformOcc? k (.app f a) = none` premise is exactly that book-keeping,
and it is what makes the predicate a certificate rather than a wish.

Build: `lake build Lean4Lean.Theory.Inductive.Restore` — **34 jobs, completed successfully**, 2.7s.
Axioms (`#print axioms`, by name, run in a scratch snippet importing the module):
`Lean4Lean.VIndRestore.uniformOcc?_spec_head`, `.restore_ownOcc`, `.restore_ownHeads`,
`.ownHeads_of_noConsts` and `Lean4Lean.VInductDecl'.OwnHeads.rec` each depend on exactly
`[propext, Quot.sound]`.  No `sorryAx`, no frozen axiom, no new `sorry` anywhere.

### 54.2 The seven confirmations classified — and one of them is NOT an instance of the rule

They are not seven instances of one statement.  They split into **two faces**, and one of the seven
belongs to neither:

| # | confirmation | face | now derived from the theorem? |
|---|---|---|---|
| 1 | `MRWit.mr_auxFieldTypesR_eq_fields` (`StoredIota.lean`, `decide`) | restore | yes — `MPWit.mr_auxFieldTypesR_eq_fields'` (§19.2) |
| 2 | `MRWit.mr_obj_entry_substC_eq` — "the `hrec` conversion" | **neither** | see below |
| 3 | `rMaj_node_eq` (`ConstSubstNested.lean`, `decide`) | head | by `VIndRestore.OwnId.ctorAppR_eq`, which already existed |
| 4 | `MPWit.mp_auxFieldTypesR_eq_fields` (`decide`) | restore | yes — `mp_auxFieldTypesR_eq_fields'` (§19.1) |
| 5 | `MPWit.mp_restore_redex_id` (row 127f) | restore | yes — `mp_restore_redex_id'` (§19.1) |
| 6 | `MPWit.mpA5₀_eq` (§16.4 negative result 1) | head | `mp_maj0_head_eq` (§19.5), `rfl` not `decide` |
| 7 | `MPWit.mpMaj_obj_eq` (§17.1, `decide`) | head | `mpMaj_obj_head_eq` + `mpMaj_obj_eq'` (§19.5), a `congrArg` |

* **restore face** = the whole-expression rewrite is the identity: `restore_ownHeads`, this round.
* **head face** = the *constructions* `tyAppR'`/`ctorAppR` collapse to `tyApp'`/`ctorApp'`:
  `VIndRestore.OwnId.tyAppR'_eq` and `.ctorAppR_eq`, which **already exist**, in
  `Theory/Inductive/NestedRules.lean` (untracked, this corner's in-flight file).  They are not
  about `restore` at all, and I did not touch that file.

**Where the brief is wrong (1): confirmation 2 is not a confirmation.**
`MRWit.mr_obj_entry_substC_eq` is at `MJ.obj` — a **companion**-pointing position, where the
restoration genuinely *moves* (`MRWit.mr_objFieldTypesR_ne_fields`).  What makes its two sides equal
is `σ` at `D.np = 0`: `substC_tyApp_comp` produces a `D.np`-fold β-redex, and at `np = 0` that redex
is empty — §4 of `ParamRedex.lean` says so in as many words ("an artefact of `np = 0` alone", and
`mp_obj_entry_substC_ne` is the same statement turning into `≠` at `np = 1`).  Filing it under
*"anything indexed by the block's own member restores trivially"* is a misattribution: it is a
companion position collapsing for an unrelated reason, and it does **not** survive `np = 1`.  The
rule's confirmation count in this corner is **six**, not seven.

**Where the brief is wrong (2): the recommended route is not what the theorem needs.**  The brief
recommended "`OwnId` plus `substC_tyApp_comp`".  `OwnId` is right and is the only hypothesis
`restore_ownHeads` takes.  `substC_tyApp_comp` plays **no part**: it is the β-gap lemma about `σ`,
and the rule is a fact about `restore` *before* any substitution — the restore face never mentions
`σ`, and the head face uses `OwnId.ctorAppR_eq`, not `substC_tyApp_comp`.  Where
`substC_tyApp_comp` does belong is confirmation 2, i.e. the one that is not an instance of the rule.

### 54.3 The side condition, named and TESTED

Named: **the occurrence must be uniform** (`D.uniformOcc?` fires).  Satisfied at every confirmation
site — each `own` premise in §19 is exactly that, `decide`d at the position, at `D.np = 1` (`MP`) and
at `D.np = 0` (`MRWit.MJ`), so it is not an artefact of either value of `np`.

Tested, at the same block, by the sharpest pair I could build (§19.3):

| witness | shape | uniform? | restoration |
|---|---|---|---|
| `mpOwnComp` | `MP #0 _nested.MDep_1` | yes | **identity** (`mp_ownComp_restore_id`) |
| `mpOwnNonUnif` | `MP #5 (_nested.MDep_1 #0)` | no (`mp_ownNonUnif_not_uniform`) | **moves** (`mp_ownNonUnif_restore_ne`) |

Same two constants, same own head; only the parameter run differs.  Drop the uniformity condition
and the rule is **false at this very block** — so the condition is load-bearing and is not one I
invented to make a statement go through.

### 54.4 Anti-vacuity, to the standard this corner sets

`OwnHeads` is not a predicate everything satisfies.  Three refutations, all obtained *from* the
theorem contrapositively (restoration moves ⇒ not `OwnHeads`), so they cannot be an artefact of a
weak predicate:

* `mp_not_ownHeads_objField` — `MP.obj`'s stored field `_nested.MDep_1 #0`, the companion-pointing
  position, `np = 1`; `mp_objField_restore_ne` is the movement.
* `mr_not_ownHeads_objField` — the same at `MRWit.MJ`, `np = 0`.
* `mp_not_ownHeads_ownNonUnif` — the non-uniform own head of §54.3.

**Hole-free vs discharged, reported separately as required.**  Everything in §54 is *discharged*:
no `sorry`, no new hypothesis, no `axiom`, every statement closed against the definitions already in
the tree.  Nothing here is merely hole-free-but-assumed.  What is *not* discharged is anything about
whether the extra generality is ever used — see §54.5, which is a negative measurement, not a hole.

### 54.5 Where the strengthening is UNEXERCISED — the honest limit of "cost is now predictable"

`restore_ownHeads` is strictly stronger than `restore_noK`: `mpOwnComp` satisfies `OwnHeads`,
**fails** `VExpr.NoConsts mpK` (`mp_ownComp_not_noConsts`, so `restore_noK` does not apply), and the
restoration is the identity on it.  But `mpOwnComp` is a hand-built `VExpr`, not a term the `MP`
block contains: `MP` takes nothing beyond its parameter, so its uniform occurrences have **empty**
residual argument lists — and the same holds of `MJ`, `NTree`, `nfnAux` and every other member in
the witness cone.

So: at all six genuine confirmation sites, `restore_noK` would have sufficed.  The strengthening
becomes load-bearing exactly at an **indexed** nested block — a member one of whose *indices*
mentions the container it nests through (`inductive Foo : List Foo → Type`-shaped) — and this
repository has **no such witness**.  That is the honest form of the brief's "cost predictable instead
of measured": the *criterion* is now a theorem and is head-local, which is what makes it predictable;
but for the blocks currently in the tree the cheaper criterion was already adequate, and I cannot
claim this round removed a measurement anyone was actually doing.

### 54.6 What I tried that failed, and the exact step

1. **`restore_ownOcc` by `split` on the `restore` match, contradiction branch by
   `rw [hu] at hu'; exact absurd hu' nofun`** — failed at the `exact`, "no goals to be solved": `rw`
   at the hypothesis already closes the goal in the `.const` branch (and, asymmetrically, does not in
   the `.app` branch).  Fixed by not splitting at all: `rw [restore, hu]` reduces the matcher on the
   scrutinee directly, and both branches become one line.
2. **`ownHeads_of_noConsts` reusing `uniformOcc?_tyAppR_eq`'s inlined inversion** — failed at
   `exact .own (by rw [VInductDecl'.uniformOcc?]; exact hu) …` with a type mismatch: after
   `split at hu` the hypothesis is the *if*-expression, and re-folding it to `D.uniformOcc? k e` is
   not a `rw`.  Fixed by extracting the inversion once as `uniformOcc?_spec_head`, which is a
   strictly better factoring — `uniformOcc?_tyAppR_eq` had that argument inline and can now be
   rewritten to use it (I did not, to keep the diff additive).
3. **Doc comment on an inductive constructor placed *before* the `|`** — parse error
   "unexpected token '/--'".  Constructor docstrings go after the bar.
4. **Citing `OwnId.ctorAppR_eq` from `ParamRedex.lean`** — impossible, not merely awkward:
   `NestedRules.lean` → `RestoreBridge.lean` → `ConstSubstNested.lean` → `ParamRedex.lean`, so the
   head-face lemma is strictly *downstream* of the block it would be applied to.  §19.5 therefore
   records the two head equations as `rfl` at the block and says where the citation belongs.

### 54.7 Measured vs read off

* **Measured (per-module `lake build`, this round):**
  `Lean4Lean.Theory.Inductive.Restore` — **34 jobs**, success, 2.7s.
  `Lean4Lean.Theory.Inductive.ParamRedex` — **72 jobs**, success, 5.4s warm (39.8s on the first
  rebuild after the `Restore.lean` edit).
* **Measured (axioms):** all **30** new declarations printed individually (5 in `Restore.lean`, 25 in `ParamRedex.lean`); `[propext, Quot.sound]`, or
  `[propext]` / none for the four `def`/`rfl` ones.  No `sorryAx`, no `Classical.choice`, no frozen
  axiom.  The only `sorry` warning anywhere in these builds is the pre-existing
  `Theory/Inductive/Decl.lean:405`, which I did not touch.
* **Read off, not run:** that the guards, `sorry-census`, `dup-names` and `MemberRedexScan` figures
  are unmoved.  **Reasoning, not a run:** every edit is purely additive (two new blocks; no existing
  declaration's statement or proof changed), the new names are fresh in their namespaces, and no
  `partial`/`@[extern]`/`@[implemented_by]` or `axiom` was introduced.
* **A rule I broke, reported:** I called the MCP `lean_build` tool once, to refresh a stale LSP
  import cache after a `#print axioms` snippet failed with "imports are out of date".  That tool runs
  a **full `lake build`** — 1517 jobs — which the brief told me not to do, and it therefore also ran
  `MemberRedexScan`, which printed `mr/cov: GUARDED … residual 0`.  It completed successfully with no
  errors, so nothing is broken, but the figure above is the one it printed and I did not intend to run
  it.  Use a scratch `#print axioms` block inside the module and `lake build <module>` instead; that
  is what produced every axiom line in this section.

### 54.8 What to pick up first

1. **Move the head face's citations to where they can be made.**  `NestedRules.lean` has both
   `OwnId.ctorAppR_eq`/`tyAppR'_eq` **and** (transitively) the `MP`/`MJ`/`NTree` names, so
   `rMaj_node_eq`, `mpA5₀_eq` and `mpMaj_obj_eq` can be re-proved there as instances rather than by
   `decide`, deleting three `decide`s. I deliberately did not edit that file — it is untracked and
   looked in-flight. Ask whoever owns it.
2. **An indexed nested witness** — the one thing that would exercise §54.5.  A two-member block whose
   own member carries an index mentioning the companion (`Foo : Aux Foo → Type`) would be the first
   place `restore_noK` is genuinely insufficient and `restore_ownHeads` is needed, and it would also
   test whether `uniformOcc?`'s `take D.np` book-keeping is right when indices follow the parameters.
3. **Rewrite `uniformOcc?_tyAppR_eq` over `uniformOcc?_spec_head`** — one-lemma cleanup, deletes the
   duplicated inversion.  Kept out of this round to keep the `Restore.lean` diff additive.
4. **Row 143d in `docs/vacuity-ledger.md`** now has a theorem to point at; the row should say
   *six* confirmations and name the two faces, with confirmation 2 reclassified as `np = 0`
   degeneracy (§54.2).  I did not edit the ledger.

## 55. §54.8's item 2 built: an INDEXED nested block — and the strengthening is *still* unexercised, provably

New file, mine end to end: **`Lean4Lean/Theory/Inductive/IndexedNested.lean`**
(namespace `Lean4Lean.MRedex.TQWit`, 100 declarations, no `sorry`).  §54.8 asked for "an indexed
nested witness … the first place `restore_noK` is genuinely insufficient".  The witness is built.
The conclusion is **negative**, and the negative is now a theorem rather than a failure to find one.

### 55.1 The block

```
inductive MI (α : Type) (β : α → Type) : Type → Type | node : (k : α) → β k → MI α β Prop
inductive TQ (α : Type) : Type → Type            | obj : MI Prop (fun _ => TQ α Prop) Prop → TQ α Prop
```

`MRWit.MJ` with **two** coordinates moved: a parameter (as at `MPWit.MP`, `np = 1`) *and* an index
— and the container `MI` is itself indexed, which is what makes **both** faces carry a residual:

| | own-head occurrence | companion-pointing occurrence |
|---|---|---|
| `MRWit.MJ` (`np=0`) | `MJ`, residual `[]` | `_nested.MDep_1`, residual `[]` |
| `MPWit.MP` (`np=1`) | `MP α`, residual `[]` | `_nested.MDep_1 α`, residual `[]` |
| **`TQWit.TQ`** (`np=1`, 1 index) | `TQ α Prop`, residual **`[Prop]`** | `_nested.MI_1 α Prop`, residual **`[Prop]`** |

Still a *redex* block (`tq_auxNodeB_not_canonical`): the companion's stored field is
`(fun x : Prop => TQ #2 Prop) #0`, exactly the `MJ`/`MP`/`Lean.Json` shape.  So the indices are the
only coordinate that moves.  `tq_cone_unindexed` (`decide`) records that every member of
`mrAux`, `mpAux` and `ntreeAux` has `indices = []`; the only prior indexed object in the tree is
`InductiveDeclExamples.ntreeAuxI`, which is the deliberately-wrong negative control of
`ntreeAuxI_not_built`.

Anchored to the `MP` standard, five ways, all `rfl`: `type_of% @TQ`, `type_of% @TQ.obj` (through
`typeR` + `σ`), `type_of% @TQ.rec`'s `uvars`, plus `tqOcc.ctor … miNode = tqAuxNodeB` and
`types[1]? = some (tqOcc.member …)` — i.e. the companion constructor *and* member are what
`VNestedOcc` computes, not hand-written.  The container is anchored too (`type_of% @MI`,
`@MI.node`, `@MI.rec`).  **Every anchor passed on the first attempt**; the transcription needed no
iteration, which was not what I expected of an indexed block.

### 55.2 Proved: the strengthening exercised at a non-empty residual (§4 of the file)

* `tq_uniformOcc_redexBody` (`decide`): at depth 2 the trigger fires on the redex's body and
  reports `some (0, [.sort .zero])` — `rest ≠ []` (`tq_redexBody_residual_ne_nil`).
  **Self-correction, caught while writing this section:** §19.3's `mp_ownComp_ownHeads` *already*
  instantiates `own` at a non-empty `rest`, so "first non-empty residual in the tree" — which I had
  written both here and in the file — is false.  The narrow true claim, and the one now in the file:
  first non-empty residual at an occurrence the block **contains**, at a member that genuinely takes
  the argument.  `grep -rn "rest :=" Lean4Lean/` is what caught it.
* `tq_restore_redexBody_id` = `VIndRestore.restore_ownOcc` at that occurrence;
  `tq_ownHeads_redex` = `OwnHeads.own (rest := [.sort .zero])` under the two congruences;
  `tq_restore_redex_id` = `restore_ownHeads`; `tq_auxFieldTypesR_eq_fields` the collapse.
  So `OwnHeads.own`'s residual-blindness is now *exercised*, not merely stated.

### 55.3 …and refuted: `restore_noK` still suffices, for a reason that generalises

The three questions the brief asked me to answer, answered:

1. **Restoration at own-head positions with non-empty residuals** — identical to the empty-residual
   case: the identity, and `restore_noK` gets it too (`tq_redex_noK`,
   `tq_restore_redex_id_noK`).  A non-empty residual is **not** what separates the two lemmas; a
   residual containing a member of `K` is, and `[Prop]` is a sort.
2. **Companion-pointing positions** — `OwnHeads` fails and the restoration moves them, as at `MJ`
   and `MP`; what the index adds is *arity bookkeeping*, and it is visible:
   `tq_objField_restore_eq` (`rfl`) shows `_nested.MI_1 #0 Prop` restoring to
   `MI Prop (fun x => TQ #1 Prop) Prop` — presented spine of length 2, then the residual index
   appended **unrestored**, so the restored occurrence has `2+1` arguments where the stored one had
   `1+1`.  That path was untested before, because every companion residual in the cone was `[]`.
3. **Does `restore_noK` genuinely fail where `restore_ownHeads` succeeds?**  Exhibited, at
   `tqOwnComp = TQ #0 (_nested.MI_1 #0 Prop)`: `OwnHeads` holds
   (`uniformOcc?_tyApp`), `NoConsts tqK` is **false** (`tq_ownComp_not_noConsts`), restoration is
   the identity (`tq_ownComp_restore_id`).  Better than §19.3's `mpOwnComp` in one respect only:
   the residual now fills a real **index slot** whose sort is `Type`, and the residual is literally
   `tqObj`'s stored field type (`tq_ownComp_residual_is_objField`), where `mpOwnComp` applied `MP`
   to an argument it has no slot for.  **`tq_index_slot` is arity-and-sort agreement by `rfl`, NOT
   a typing derivation** — no environment in the file holds `_nested.MI_1`.
   Sharpness kept in view: `tqOwnNonUnif = TQ #5 (_nested.MI_1 #0 Prop)` — same constants, own head,
   parameter run `#5` — is **not** uniform and **moves** (`decide`), so `¬ OwnHeads` there.

**And why (3) cannot be upgraded to a position the block contains — the theorem (§6 of the file).**
`VIndField.WF.pos` (F7) requires `∀ a ∈ r.args, D.NoBlock a` of a recursive field's index
arguments, and `VIndCtor.WF.args_fresh` (F5) the same of a constructor's result indices.  `K` listing members of
the block is a *hypothesis* (`hKB`, discharged at the witness by `tq_K_sub_blockNames`) and not a
framework invariant — I checked, and nothing in `Restore.lean`/`NestedBuild.lean` imposes it; the
nearest thing is `RestoreBridge.csubstTy_dom_blockNames`.  Given it, block-free ⇒ companion-free.
Hence:

* `tq_ownOcc_noConsts_of_WF` — for an **arbitrary** block: a uniform occurrence of a member off `K`
  with block-free residual arguments is `VExpr.NoConsts K` outright;
* `tq_restore_id_of_WF` — so the restoration is the identity there **by `restore_noK`**;
* `tq_restore_redexBody_id_of_WF` + `tq_nt_eq_tyApp` — the instance at §4's own position, making
  §4's `restore_ownOcc` route demonstrably redundant *at this witness*.

Three general helpers came with it (`noConsts_mono`, `noConsts_mkApp`, `noConsts_bvars`), kept local
in `TQWit`; they belong beside `restore_noK` in `Restore.lean` when a second consumer appears.

**Left open, precisely** — and this is the one door still ajar for a future positive result:
`pos`'s last conjunct pins a *stored* field type only up to `IsDefEqType` against `r.canonType`, so
the theorem covers **canonical** own-head occurrences (and stored ones only where
`VIndCtor.Canonical` holds, e.g. `ntreeAux`).  Whether a WF *stored* type can put a companion
inside a uniform own occurrence's residual is **not settled**.  My guess is no — the residual would
have to be defeq to a block-free index while syntactically naming a freshly declared inductive —
but that is a guess, not a measurement, and §54.5's "unexercised" should now read "unexercised, and
provably unreachable at canonical occurrences; open for stored ones".

### 55.4 What I tried that failed, and the step it failed at

1. **`Foo : Aux Foo → Type` literally, as the brief wrote it** — failed at *stating* it: the shape is
   circular (the index type mentions the block), so no Lean declaration and no `VInductDecl'`
   corresponds.  What the brief meant, and what §55.1 builds, is a block whose **index value** can
   mention the container.
2. **`inductive T1 : Nat → Type | obj : (n : Nat) → Aux (T1 n) → T1 (n+1)`** — failed at the
   kernel: *"invalid nested inductive datatype 'Aux', nested inductive datatypes parameters cannot
   contain local variables"*.  A nesting argument may mention block **parameters** but not
   constructor-bound locals, so the indexed nesting has to be at a *closed* index (`TQ α Prop`).
   That is also why I indexed over `Type` with the value `Prop` rather than over `Nat` with `0`:
   `Nat` literals have no `VExpr` transcription in this theory, sorts do.
3. **Result index mentioning the container** (`| obj : … → TR α (MI Prop (fun _ => TR α Prop) Prop)`)
   — failed at the kernel: *"invalid return type for 'TR.obj'"*.
4. **Index of a recursive field mentioning it** (`| obj : TS α (MI Prop … Prop) → TS α Prop`) —
   *"arg #2 of 'TS.obj' contains a non valid occurrence of the datatypes being declared"*.
5. **The on-point one — the nesting argument's own index mentioning the container**
   (`MI Prop (fun _ => TT α (MI Prop (fun _ => TT α Prop) Prop)) Prop`), which would have put a
   companion in the residual of exactly the field §55.2 exercises — *"arg #3 of
   '_nested.Lean4Lean.MRedex.TQWit.MI_1.node' contains a non valid occurrence of the datatypes being
   declared"*.
6. **Machine-checking 3–5 in the repo with `#guard_msgs`** — written, all three **passed**, then
   **removed**: a rejected `inductive` still adds constants, and `#print axioms` on `TR`/`TS`/`TT`
   reports **`sorryAx`**.  Keeping them would have imported three new `sorry`-dependent constants
   into the build.  *This is worth remembering: `#guard_msgs` over a failing `inductive` is not
   sorry-free.*  §6 of the file therefore quotes the three messages as out-of-repo measurements and
   proves the spec-level theorem instead — which is stronger anyway, being about `VIndField.WF`
   rather than about the C++ kernel.
7. **`decide` on `VExpr.NoConsts`** — no `Decidable` instance; the two `NoConsts` facts are by
   anonymous-constructor terms (`tq_redex_noK`, `tq_ownComp_not_noConsts`), as at `mp_redex_noK`.
8. **`noConsts_mkApp` / `noConsts_mono` by merged `|` alternatives** — "expected type … is not an
   inductive type": with implicit `{f}` or merged patterns the `NoConsts` application stays a
   metavariable and never unfolds to the `And`.  Fixed with `(f := …)` + `show`, and one branch per
   constructor.

### 55.5 Corrections to the brief I was given

* **"shape `Foo : Aux Foo → Type`"** is not a shape any block can have (55.4.1).  The reachable
  shape is *index value* mentioning the container, which is what I built and which Lean then rejects
  at every position (55.4.3–5).
* **"the theorem becomes load-bearing only at an indexed nested block"** — half right and the
  interesting half is wrong: an indexed block is what makes the residual **non-empty**, and I
  confirm that, but non-empty is not enough.  Load-bearing needs a **companion inside the residual**,
  which F7/F5 forbid at canonical occurrences.  So the brief's framing predicted a positive result
  where the specification already contains its refutation.
* **"expect the construction, not the instantiation, to be the work"** — wrong here: the
  construction was ~40 minutes and every `rfl`/`decide` landed first time.  The work was **finding
  which shape Lean accepts** (five rejections, 55.4.2–5) and then noticing that F7 says the same
  thing the kernel does.
* **`_nested.MI_1` is a naming *convention*, not Lean's internal name**: for a container inside a
  namespace, Lean generates `_nested.Lean4Lean.MRedex.TQWit.MI_1` (visible in 55.4.5's message).
  `MRWit`/`MPWit` have the same discrepancy with `_nested.MDep_1`; it is harmless because the
  auxiliary constants never reach the environment, but nothing in the tree says so and I nearly
  claimed the names matched.

### 55.6 Measured vs read off

* **Measured (per-module `lake build`):** `Lean4Lean.Theory.Inductive.IndexedNested` —
  **73 jobs**, success, **1.7s** for the module (the other 72 replayed from cache).  Run twice, same
  figure.  No full build, no guard run, no `sorry-census`, no `dup-names`, no `MemberRedexScan`.
  **I did not call the MCP `lean_build` tool at any point** (the trap §54.7 reported).
* **Measured (axioms, by namespace):** all **100** declarations of `Lean4Lean.MRedex.TQWit`
  enumerated with `collectAxioms` under `lake env lean`: 53 with **no** axioms, 13 `[propext]`,
  34 `[propext, Quot.sound]`, **0** with `sorryAx`, **0** with `Classical.choice`, 0 frozen.
  Baseline check: `MPWit.mp_restore_redex_id'` prints the same `[propext, Quot.sound]`, so this is
  the corner's normal footprint and not something my file introduces.
  *First run of the same census read three `sorryAx` declarations — that was the pre-removal olean
  of §55.4.6, and it is why the removal happened; the figure above is from a clean rebuild.*
* **Hole-free vs discharged:** everything in §55.2–55.3 is **discharged** — no new hypothesis, no
  `sorry`, no admitted side condition.  The two things that are *not* discharged are named as such:
  the stored-type case in §55.3 (open, stated in the file's §6) and `tq_index_slot`'s sort agreement,
  which is **not** a typing derivation and says so in its own docstring.
* **Read off, not run — reasoning, not a run:** that guard 1/2/3, `sorry-census`, `dup-names` and
  `MemberRedexScan` figures are unmoved.  The file is new and imported by nothing; it adds no
  `axiom`, no `partial`, no `@[extern]`, no `@[implemented_by]`, and touches no existing
  declaration.  `MemberRedexScan` scans the *running* environment's blocks, and `TQ`/`MI` are
  declared inside `Theory/`, which that scan does not import.
* **Searches:** `lean_local_search` and `lean_hammer_premise` are broken here (no `rg`), as briefed.
  Every "there is no such lemma" claim in this section is backed by `grep`/`rg`-free `grep -rn`
  over `Lean4Lean/`, and the `VNestedOcc.member`/`ctor`/`fieldTypesR`/`WF` readings by `sed` on the
  source.  No `lean_references` call was needed.

### 55.7 What to pick up first

1. **Close or refute the stored-type case** (§55.3, "left open").  If a WF stored field type can put
   a companion inside a uniform own occurrence's residual, `restore_ownHeads` becomes load-bearing
   after all; if not, the honest move is to *retire* the strengthening's marketing and keep it as
   the clean statement of a rule that `restore_noK` happens to cover.  Concretely: try to build a
   stored type defeq to `TQ α Prop` that syntactically reads `TQ α X` with `X` mentioning
   `_nested.MI_1` — I believe `IsDefEqType` refuses, and that refusal is the missing theorem.
2. **Move `noConsts_mono`/`_mkApp`/`_bvars` and `tq_ownOcc_noConsts_of_WF` into `Restore.lean`**
   under general names (`VIndRestore.restore_id_of_WF`?).  The last is a fact about the whole
   specification and reads oddly with a `tq_` prefix in a witness file; I kept it local rather than
   touch `Restore.lean` in a round that did not otherwise need to.
3. **`ntreeAuxI` deserves a companion note**: it is an *indexed* block that is `¬ Built`, and now
   `tqAux tqAuxNodeB` is an indexed block that **is** `Built`.  The pair is the positive/negative
   control for `Built.member`'s index clause, and `NestedBuild.lean`'s §5 should cite it.
4. **`tq_cone_unindexed` is the anti-vacuity measurement row 143d's ledger entry needs** — the row
   should now say the strengthening is *exercised at a non-empty residual* and *unreachable at a
   companion-bearing one*, with `tq_ownOcc_noConsts_of_WF` as the reason.  I did not edit
   `docs/vacuity-ledger.md`.

---

## 56 The stored-type case is **CLOSED, affirmatively** — and the briefing's guess about why was backwards

*Written incrementally as the round ran; each subsection landed before the next was started.*

**Verdict up front: CLOSED, not refuted.**  §55.7 item 1 says *"try to build a stored type defeq to
`TQ α Prop` that syntactically reads `TQ α X` with `X` mentioning `_nested.MI_1` — I believe
`IsDefEqType` refuses, and that refusal is the missing theorem."*  **`IsDefEqType` does not refuse,
and there is no such theorem to find.**  Take `X := (fun y : Type => Prop) (_nested.MI_1 α Prop)`.
One `VEnv.IsDefEq.beta` step makes `X` defeq to `Prop`; one `appDF` lifts that to
`TQ α X ≡ TQ α Prop`.  The whole obstruction the briefing expected costs two constant lookups —
`TQ` and `_nested.MI_1`, both of which the staged environment of `VIndCtor.WF` *already holds*,
because `VInductDecl'.WF.ctors` checks constructors in `env.addIndTypes D`, the environment
extended by **all** the block's type constants, companions included.  The residual of a stored
occurrence may therefore mention a companion freely, and F7 cannot see it: F7 constrains
`r.args`, which is the *canonical* residual.

`VIndRestore.restore_ownOcc`/`restore_ownHeads` are therefore **load-bearing**, at a stored field
type, and §55.5's negative headline is confined to canonical occurrences exactly as it was stated.

### 56.1 Proved (all in `Lean4Lean/Theory/Inductive/IndexedNested.lean` §8, module green)

`tqHostile := TQ #1 ((fun y : Type => Prop) (_nested.MI_1 #1 Prop))`, stored as the **second**
field of `TQ.obj` in `tqAuxH` — §1's block with one extra stored field, the genuine nesting field
of §1.2 unchanged as field `0` (`tq_objH_field0`, `rfl`).

| what | how |
| --- | --- |
| `tq_hostile_uniformOcc` | trigger fires, member `0` (own), residual `[tqHostileArg]` — `decide` |
| `tq_hostile_not_noConsts` | `restore_noK`'s hypothesis is **false** |
| `tq_hostile_args_not_noBlock` | §6's `tq_ownOcc_noConsts_of_WF` fails **at its `hargs`**, not at its conclusion — the stored residual is not block-free |
| `tq_hostile_ownHeads` / `tq_hostile_restore_id` | `OwnHeads` holds; restore is the identity **by `restore_ownOcc`** |
| `example … := by decide` | the same identity computed, independently of the rule |
| `tqRestore_ownId_H`, `tq_auxH_{blockNames,np,types0,…}` | §3's invariants transfer to `tqAuxH` (`rfl`/`decide`) |

Measured: `lake build Lean4Lean.Theory.Inductive.IndexedNested` — **73 jobs**, green, no new
warnings from §8.

### 56.2 …and the stored type is `VIndField.WF`, in the environment the spec itself supplies

The closure would be worthless if the hostile stored type were merely a `VExpr`.  It is not: the
**whole** of `VIndField.WF` holds of it.

* `tq_hostile_field_WF` — every clause: `hasType`, `level`, `pos`'s eight conjuncts,
  `binders_indep`.  `pos`'s block-freeness conjuncts are satisfied *as stated*, because they are
  conditions on the `VIndRecArg` record (`binders = []`, `args = [Prop]`) and the record is clean.
  That is the entire mechanism of the closure.
* `tq_staged_env_exists` — the two constant lookups it takes are **not** a convenient pair:
  `tqAuxH.typeConsts = [(TQ, ⟨0, tqMemberType⟩), (_nested.MI_1, ⟨0, tqMemberType⟩)]` (`rfl`), so the
  two `addConst` steps *are* `VEnv.empty.addIndTypes tqAuxH`, which is exactly the environment
  `VInductDecl'.WF.ctors` hands to `VIndCtor.WF`.
* `tq_hostile_field_WF_staged` — the two combined: `∃ env, VEnv.empty.addIndTypes tqAuxH = some env
  ∧ env.Ordered ∧ VIndField.WF env …`.  Nothing assumed.
* `tq_auxH_faithful` — `VIndRestore.Faithful` transfers from §1's block to `tqAuxH`, because every
  one of its three clauses is guarded by `T.name ∈ K` and only `TQ`'s constructors moved.  So the
  restoration obligations of `VEnv.AddNested` do not see the hostile field either.

**Boundary, stated because it is the one place to attack this result.**  What is proved is the
*field* clause, `VIndField.WF`.  `VIndCtor.WF env tqAuxH 0 T₀ tqObjH` and
`VInductDecl'.WF env tqAuxH` are **not attempted** — not holed, not `sorry`, just absent.  Reading
the remaining clauses (`params_eq`, `args_ty`, `result`, the sibling field's `pos`, `VIndType.WF`,
`LECond` at `lvl = 1`), I see nothing the hostile field's *shape* obstructs — the hostile field is
last, so it enters only the context of `args_ty`/`result`, where it needs to be a type and is one
(`tq_hostile_hasType`) — but that is **reasoning, not a run**.

### 56.3 Load-bearing at an existing consumer, not just as a fact about `restore`

`VIndRestore.substC_atRec_fieldTypes_defeq_of_noK` (§T15.7) is the form ruling 122e's payoff is
used in: it charges the field-telescope obligation at fields whose **stored** type mentions a
companion.  At `tqObjH`'s field `1` that premise **fires**.  The sharper form
`substC_atRec_fieldTypes_defeq'` charges it only where the substituted entries differ, and there
they do not — `tq_hostile_entry_substC_eq`, for every `σ`, by rewriting with
`tq_hostile_restore_id`.  `tq_hostile_obligation_split` states both halves in one theorem.

So the two forms of §T15.7 separate *exactly here*, and the cost of not having the strengthening is
concrete: `_of_noK` becomes the best available and the hostile field carries an obligation that is
in fact empty.

### 56.4 Anti-vacuity, measured: **no block in this tree has such a stored type**

`storedCleanB D K` (new, decidable) decides *at every constructor field, if the trigger fires on the
**stored** type, is the residual `K`-free?* — i.e. exactly "`restore_noK` covers every stored
occurrence".  `hasConstB_eq_false_iff` anchors its constant test to `VExpr.NoConsts` (which has no
`Decidable` instance), and `noConsts_of_storedCleanB` is the bridge from `= true` to the `Prop`, so
the `decide`s below are statements about the specification and not about a `Bool`.

| block | `storedCleanB` |
| --- | --- |
| `tqAuxH` (§8) | **false** |
| `tqAux tqAuxNodeB` (§1 — same members, same `K`, same restoration; only the stored field differs) | true |
| `MRWit.mrAux mrAuxNodeB`, `MPWit.mpAux mpAuxNodeB`, `ntreeAux`, `nfnAux` | true |
| `tqAux (tqOcc.ctor … miNode)` — the **constructed** companion constructor | true |

The last row is the one that matters most: the construction cannot produce a flagged block, because
`VNestedOcc.ctor` builds the recursive field as the head-β redex `(fun x => I p π) k`, whose residual
is a `bvar` run and a sort.  The scan is **not** vacuously true on the cone — the trigger does fire
inside it, at `tqObj`'s stored field (`tq_uniformOcc_objField`, `some (1, [Prop])`).

**So: the closure is about what the specification admits.  Every block anything in this tree builds
is clean, and the hostile block is one I wrote for the purpose.**  Quoting §56 as "the strengthening
is exercised by a real declaration" would be false.

### 56.5 What the real kernel does — and the ruling this now asks for

Measured with `lean_run_code` on scratch snippets **outside the repository**, for §55.5's reason (a
rejected `inductive` still lands `sorryAx`-carrying constants, so a `#guard_msgs` control would
import them into the build).  Proxy: a plain **mutual** block, because the kernel's positivity check
does not distinguish a companion from any other member being declared.  Four declarations across two
runs:

| field type | verdict |
| --- | --- |
| `TT Prop` (clean) | accepted |
| `TT ((fun _ : Type => Prop) Nat)` — β redex in the index, no block constant in it | accepted |
| `TT ((fun _ : Type => Prop) (SS Prop))` — a *sibling* member under the redex | rejected: `(kernel) arg #1 of 'TT.hostile' contains a non valid occurrence of the datatypes being declared` |
| `TT ((fun _ : Type => Prop) (TT Prop))` — the **own** member under the redex | rejected, same message |

The redex is not what offends; a block constant *anywhere* in a stored index argument is, whether it
survives `whnf` or not.  **Lean's kernel is strictly stricter here than `VIndField.WF.pos` is.**
That is slack, not unsoundness — refinement runs *checker ⇒ spec*, and a permissive spec is
discharged by a stricter check — but it turns the corner into a ruling:

1. **Keep F7 as it is** ⇒ `restore_ownOcc`/`restore_ownHeads` are load-bearing, §8 is the witness,
   nothing further is owed.
2. **Tighten F7's `some` branch** to require the stored type's own-head residual to be block-free
   ⇒ §8's witness stops being well-formed, the stored-type case is *refuted* after all,
   `restore_noK` suffices everywhere, and `restore_ownOcc` can be retired to a curiosity.  Cost: one
   new spec conjunct, whose refinement obligation the four measurements above suggest the checker
   already discharges.

I have **not** taken that decision; §8.8 records both options.  Note the asymmetry: option 2 is the
only route by which the strengthening dies, and it is a *spec change*, not a theorem — which is why
§55.5's "no witness in this theory" and §56's "load-bearing" are both true, of different objects.

### 56.6 Where the briefing is wrong — four places

1. **"I believe `IsDefEqType` refuses, and that refusal is the missing theorem" (§55.7 item 1).**
   Backwards.  `IsDefEqType` is *one `beta`* away from accepting; there is no theorem to find, and
   the round spent its time proving the opposite of what was predicted.
2. **The suggested refutation route — "F7/F5 reach the stored form too, e.g. because the relevant
   well-formedness is stated over the stored telescope after ruling 122e" — is structurally
   unavailable.**  Ruling 122e moved the **iota layer** onto the stored telescope; F7 and F5 are
   clauses of `VIndField.WF`/`VIndCtor.WF` about `r.args`/`C.args`, i.e. about the `VIndRecArg` and
   `VIndCtor` *records*, and 122e did not touch them and could not have.  If anything 122e makes the
   stored-type case more pressing, because the layer that now reads stored types is bigger.
3. **"Lean's kernel independently rejects the shape that would be needed, three ways" was used in §6
   to support the negative result; it does not support it.**  Kernel rejection is evidence about the
   *checker*, and the specification is what `kernel_sound` quantifies over.  The measurement is
   nonetheless the most useful thing in the round — see §56.5 — because it is what makes option 2
   cheap.  (I re-measured rather than trusting the read: the fourth row, the **own** member under a
   redex, was not among §6's three.)
4. **"exhibit a stored type … making the strengthening genuinely load-bearing" and "say whether any
   block in the tree has one" were posed as one question; they are two, with opposite answers.**
   The spec admits one (§56.2); nothing in the tree has one (§56.4).  A round that reported only the
   first would be the over-claim you have been fighting all day.

### 56.7 What failed, and at which step

Six failures, all in elaboration rather than in mathematics; recorded because each cost a build
cycle and each will recur.

1. **`section` + `variable (hTQ : …)` for the two constant lookups.**  Lean includes a section
   variable only in declarations that *mention* it, so the first lemma that did not name `hMI`
   silently lost it and every later `… hMI` failed with `Function expected`.  Failed at
   elaboration of the second declaration in the section.  Fix: explicit binders per theorem.  (This
   is why `StoredIota.lean` §5.2 spells its hypotheses out — that is not a style choice.)
2. **`.constDF hMI nofun nofun rfl .nil` inline inside a nested `.appDF`.**  `Missing cases: _, _` —
   `nofun` was handed `∀ l ∈ ?ls, …` with `?ls` still a metavariable.  Failed at unification.  Fix:
   a fully annotated `have` for every intermediate typing.
3. **`.appDF`/`.beta` do not determine their `B`.**  The conclusion is `B.inst a`, so a target of
   `.sort (.succ .zero)` leaves `B` open and `.sortDF trivial trivial rfl` fails with
   `VLevel.WF ?m ?m`.  Failed at unification.  Same fix as 2 — this is the whole reason
   `mr_tyBody_hasType` is written as four `have`s.
4. **`Lookup` at index 1.**  `.bvar (.succ .zero)` cannot be elaborated against
   `.sort (.succ .zero)`: it needs `?ty.lift ≡ .sort …`, which unification will not solve.  Failed
   at implicit-argument synthesis.  Fix: `Lookup.zero (ty := …) (Γ := …)`, then `lift` computes.
5. **`liftTele` unqualified.**  `IndexedNested.lean` does not `open VExpr`, so `autoImplicit`
   swallowed it and reported `Function expected at liftTele`.  A one-character fix that reads like a
   type error.
6. **`tq_auxH_faithful.ctor_agree`.**  `exact h.ctor_agree 1 _ rfl hK` fails: the conclusions differ
   by `C.typeR tqAuxH …` vs `C.typeR (tqAux tqAuxNodeB) …`, which are defeq only once `C` is
   *specialised* — with `C` a bound variable neither side computes.  And the obvious repair,
   `simp only [List.mem_cons] at hC`, made **no progress**, because
   `((tqAux tqAuxNodeB).types.getD 1 default).ctors` is not syntactically a cons.  Fix: `rw [show … =
   [tqAuxNodeB] from rfl] at hC`, `subst`, then `rfl` closes it.  `ty_agree` and `ctors_complete`
   needed none of this — their conclusions do not mention `typeR`.

### 56.8 Measured versus read-off; hole-free versus discharged

**Measured (runs):** `lake build Lean4Lean.Theory.Inductive.IndexedNested` — **73 jobs**, green, no
new warnings, at every one of the eight increments.  **63** new declarations (53 theorems, 9 defs, 1
`example`), 598 lines, all in `Theory/Inductive/IndexedNested.lean` §8.  `#print axioms` on all **62**
named declarations: **29 `[propext]`, 26 `[propext, Quot.sound]`, 7 axiom-free**; **0 `sorryAx`, 0
`Classical.choice`**, no frozen axiom.  No new `sorry` in the file (its only two occurrences are the
pre-existing §6 prose).  The four kernel verdicts of §56.5.  Nothing else was built: no full `lake
build`, no guards, no census, no `dup-names`, no `MemberRedexScan`, no MCP `lean_build`.

**Read-off / reasoning, labelled as such:** that no clause of `VInductDecl'.WF` other than
`VIndField.WF` reads a stored field type except through the field contexts (from reading `Decl.lean`
§4, not from a proof); that the remaining `VIndCtor.WF`/`VInductDecl'.WF` clauses are satisfiable at
`tqAuxH`; that guards/census are **unmoved** — I did not run them, and §8 adds no axiom and no
`sorry`, so I expect no movement, but that is an expectation.

**Hole-free versus discharged.**  §8 is both: no `sorry`, no holes, and every hypothesis of every
new theorem is either universally quantified over environments or discharged in a constructed
`Ordered` environment (`tq_staged_env_exists`).  The one *conditional* result is
`tq_auxH_faithful`, whose premise (`Faithful` at §1's block) is **not discharged anywhere in the
tree** — no `Faithful` instance exists for any `TQ` block — so read it as a transfer, not as a fact.

Search tooling: `lean_local_search` and `lean_hammer_premise` are indeed broken here (`rg` absent).
Every "where does X live" claim above is backed by `grep`/`sed` over the tree, except
`substC_atRec_fieldTypes_defeq'`/`_of_noK`'s signatures, which I read from `NestedTele.lean`
directly, and the four kernel verdicts, which are `lean_run_code`.

### 56.9 What to pick up first

1. **Take the §56.5 ruling.**  Everything else in this corner is downstream of it.  Keep F7 and
   `restore_ownOcc` is load-bearing with a witness; tighten F7 and the strengthening can be retired.
   The tightening is the *only* remaining route to the refutation you asked for, and it is a spec
   edit, not a theorem.
2. **If F7 stays: promote §6's and §8.6's helpers into `Restore.lean`** — `noConsts_mono`,
   `noConsts_mkApp`, `noConsts_bvars`, `tq_ownOcc_noConsts_of_WF`, `tq_restore_id_of_WF`,
   `hasConstB`, `hasConstB_eq_false_iff`, `storedCleanB`, `noConsts_of_storedCleanB`.  Nine general
   declarations now sit in a witness file with `tq_` prefixes.  `storedCleanB` in particular deserves
   to be run over every transcribed block as a standing check, the way `MemberRedexScan` is.
3. **If F7 is tightened: the first casualty list is short and known** — `restore_ownOcc`,
   `restore_ownHeads`, `VInductDecl'.OwnHeads`, `ownHeads_of_noConsts`, and the §4/§5/§7
   instantiations here and in `ParamRedex.lean` §19.3.  Everything else in the redex corner already
   goes through `restore_noK`.
4. **`VIndCtor.WF env tqAuxH 0 T₀ tqObjH` is the honest next proof** if anyone wants the closure at
   block level rather than field level.  From §8.2–§8.4 it is bookkeeping: the sibling field's `pos`
   is *reflexivity* (`r.canonType` **is** its stored type — measured, `tq_objH_field0_canonical`,
   `rfl`), and `args_ty`/`result` need only
   `Prop : Type` and the parameter, in a three-entry context whose entries §8.3 already types.

## 57 Ruling 159e INSTALLED: F7 now constrains the **stored** residual — and §8 flipped sign instead of being retired

Written incrementally, each change landed and re-proved before the next. Nothing was composed in
memory. Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) were not
opened for edit; `Experimental/ConeJoin.lean` and `implGapWhitelist` untouched; no implementation
file changed; no git operation performed.

### 57.1 What changed

**The clause.** `VIndField.WF.pos`'s `some` branch (`Theory/Inductive/Decl.lean`) gained a ninth
conjunct, appended last:

```
      D.ResidualClean (r.binders.length + i) F.type
```

where, new in the same file,

```
def VInductDecl'.ResidualClean (D : VInductDecl') (k : Nat) (e : VExpr) : Prop :=
  ∀ j rest, D.uniformOcc? k e = some (j, rest) → ∀ a ∈ rest, D.NoBlock a
```

This is §4 of `docs/audit-f7-radius.md` **verbatim**, at the depth `VIndRecArg.canonResult`
itself uses. The clause is statable and it is right; the ruling is not retired on that account.

**Two things §4 did not say, and both cost real work.**

1. **The clause has no home where `VIndField.WF` lives.** `uniformOcc?` is defined in
   `Theory/Inductive/Restore.lean`, which **imports** `Decl.lean`. §4 gives the clause but no
   module that can state it. I moved into `Decl.lean`: `VExpr.spineFn` (+ its two `rfl` lemmas),
   `VInductDecl'.memberIdxFrom`, `VInductDecl'.memberIdx`, `VInductDecl'.uniformOcc?`, and the two
   `deriving instance DecidableEq` lines (`VLevel`, `VExpr`); and moved `VExpr.spineArgs` (+ its two
   lemmas) earlier *within* `Decl.lean`, above `VIndField.WF`. Every lemma about these stayed in
   `Restore.lean`. **Zero call sites changed** — `Restore` imports `Decl`, so all consumers still
   see the same fully-qualified names — but this is six declarations relocated across the boundary
   of the most-imported module in the tree, and the audit costed it at zero.
2. **`VExpr.NoConsts` had no `Decidable` instance**, which the audit's "21 `decide`s" presupposes
   (`Theory/Inductive/StoredIota.lean`:412 says so in as many words). I added, in `Decl.lean`:
   `VExpr.hasConstB`, `VExpr.hasConstB_eq_false_iff`, `VExpr.decidableNoConsts`,
   `VInductDecl'.decidableNoBlock`, `VInductDecl'.residualClean_of_uniformOcc_none`,
   `VInductDecl'.residualClean_of_uniformOcc_some`, `VInductDecl'.decidableResidualClean`.
   `MRedex.TQWit.hasConstB` (§8.6) was left alone — different namespace, arbitrary `K`.

### 57.2 Measured versus predicted

| item | audit predicted | measured | verdict |
|---|---|---|---|
| `VIndField.WF.pos` records (1 def + usages) | 1 + 52 | **1 + 52** | ✔ exact |
| `some`-branch producers / blocks | 22 / 11 | **22 / 11** | ✔ exact |
| `none`-branch producers touched | 0 | **0** | ✔ |
| producers discharged by `decide` | 21 | **21** | ✔ exact |
| producer *sites* needing a second, unpredicted edit | 0 | **18** | ✘ see 57.3 |
| consumer sites edited | 4 | **2** | ✘ over-counted by 2 |
| statements needing downstream re-proof | 0 | **0** | ✔ |
| theorems that die | 1 + 2 wrappers | **exactly those 3** | ✔ |
| blocks failing the clause | 1 (`tqAuxH`), 13 of 14 true | **1, 13 of 14 true** | ✔ exact |
| files outside my ownership needing edits | 1 implied (`Verify/Typing/ProjClosedG`) | **0** | ✔ better |

Census provenance: `python3` over **377** `.ilean` files (the audit had 374; the tree has grown —
`Theory/Inductive/NestedRules.lean` is untracked in git but *is* built and *is* in the scan, and it
contains no `pos` producer, only `recArg_noBlock` consumers in docstrings). `lean_references` was
not used for any count. `lean_local_search`/`lean_hammer_premise` remain broken (`rg` absent).
Treat every count as a floor; the floor is now backed by a source-level `grep` cross-check that
found **no** file mentioning `VIndField.WF` without a fresh `.ilean`.

### 57.3 The three places the audit's cost model was wrong

**(a) Anonymous-constructor flattening does not re-associate — 18 extra edits.** The `some` branch
is an **8**-fold conjunction, not the 9-fold one the audit reports; it reads as 9
anonymous-constructor slots because its trailing `IsDefEqType` is an `∃ u` that the flattener
absorbs. 18 of the 21 surviving producer sites therefore ended `…, _, by type_tac⟩`. Appending a
tenth slot makes the flattener hand `_` to the `∃` and `⟨by type_tac, by decide⟩` to the new
conjunct, and elaboration fails with `Invalid ⟨...⟩ notation`. Every one of those sites needed the
`∃` **re-nested** — `…, ⟨_, by type_tac⟩, by decide⟩` — a second mechanical edit per site.
(The remaining three sites were free: `accIntro_WF` and `ro_field_WF` discharge `pos` by
`refine` and took a bare extra `?_`/bullet, and `mpAuxB_WF`'s second site ends in a named term
(`mp_redex_pos_defeq ht`) rather than a flattened `∃`.)

**(b) Only 2 consumer sites needed editing, not 4.** Appending at the end leaves projection-style
consumers alone, and leaves an `obtain` with *n* patterns against an *n+1*-fold nesting alone too,
because its last pattern simply binds the pair:

* `VIndField.WF.recArg_noBlock` (`RestoreBridge.lean`:384) — uses `hp.1, hp.2.2.1, hp.2.2.2.1`.
  **Zero edits.**
* `VInductDecl'.projClosedG_of_wf` (`Verify/Typing/ProjClosedG.lean`:141) — `obtain ⟨-,-,-,-,honctx,hres,-,-⟩`;
  the trailing `-` now clears `h8 ∧ h9`. **Zero edits**, and this is the one file outside my
  ownership the audit implied would need touching. It did not. Built clean, 39 jobs.
* `VInductDecl'.recField_facts` (`Lemmas.lean`) — the 8th pattern **binds** (`hFdefeq`), so it
  needed `, -`. **1 edit.**
* `VIndField.WF.mono` (`Lemmas.lean`) — needed the 9th slot and the carry. `ResidualClean` mentions
  no environment, so the carry is `h9` itself, `id`, exactly as the audit predicted for the only
  structural consumer. **1 edit.**

**(c) The ruling's *second* payoff is also largely absent.** The audit (§2, §3c) and the briefing
both frame the cost as "§8 is retired". **§8 was not retired — it flipped sign.** Of §8's
declarations exactly **three** died: `tq_hostile_field_WF`, `tq_hostile_field_WF_closed`,
`tq_hostile_field_WF_staged`. Everything else survives *verbatim*, because none of it went through
`VIndField.WF`: `tq_hostile_uniformOcc`, `tq_hostile_args_not_noBlock`, `tq_hostile_not_noConsts`,
`tq_hostile_ownHeads`, `tq_hostile_restore_id`, §8.2's `tq_hostile_defeq_canon` and the three typing
lemmas §8.3 was built from, §8.4's `tq_env_exists`/`tq_staged_env_exists`/`tq_typeConsts_eq`, §8.5
entire, §8.6 entire, and — flagged specifically because the audit §3c said it would be lost —
**§8.7's `tq_hostile_obligation_split` survives untouched.** The separation measurement between
`substC_atRec_fieldTypes_defeq'` and `_of_noK` is *not* lost.

So the honest ledger for ruling 159e is: it buys **specification fidelity in one position**, and it
buys **nothing else at all**. Not `restore_noK` sufficing everywhere (audit §3b, and I add a
confirmation below), and not the retirement of a section either.

### 57.4 What died, what replaced it, what survived

Dead, and **unprovable** rather than merely unproved:

* `MRedex.TQWit.tq_hostile_field_WF` — refuted outright by `tq_hostile_field_not_WF`;
* `tq_hostile_field_WF_closed`, `tq_hostile_field_WF_staged` — a fortiori.

Nothing outside `IndexedNested.lean` ever used any of the three (measured: zero `.ilean` usages
outside the module; `grep` confirms only the two internal wrapper call sites).

What replaced them, all `sorry`-free and all in `IndexedNested.lean` §8.3:

* `tq_hostile_not_residualClean : ¬ tqAuxH.ResidualClean 1 tqHostile` — one `decide`;
* `tq_hostile_field_not_WF : ∀ {env}, ¬ VIndField.WF env tqAuxH …` — **stronger than the old
  theorem's negation**: it holds in every environment, with no hypothesis on the constant lookups
  at all, where the old acceptance needed two;
* `tq_hostile_field_not_WF_staged` — the same in the environment `VInductDecl'.WF.ctors` itself
  supplies, so the rejection is not green by an unsatisfiable hypothesis;
* the `decide`-level shape facts that used to be inline in the dead proof, kept as facts so that the
  rejection is *located*: `tq_hostileRec_idx_lt`, `tq_hostileRec_args_len`,
  `tq_hostileRec_binders_noBlock`, `tq_hostileRec_bindersIndep`. Together with the four surviving
  typing lemmas these show every clause of `pos` except the new one still holds at the hostile
  field, so the only reason it fails is ruling 159e's conjunct.

§8's headline prose was rewritten, not deleted, and it now records what was lost: §8 no longer
supplies a witness that `restore_ownOcc`'s strengthening is *exercised*, and no other block in the
tree does either. The strengthening is still a theorem; it is now unexercised.

### 57.5 The two things the edit must not do — both confirmed

**(1) `VIndField.WF` is not unsatisfiable at any block the tree builds.** Confirmed twice over,
and the second is stronger than the audit's `#eval`:

* All 21 surviving producer sites now *discharge* the clause by `decide` inside a real
  `VIndField.WF` proof, at all 10 surviving blocks that carry a `some`-branch producer
  (`nfnAux`, `nfnAuxDirty`, `ntreeAux`, `mpAux mpAuxNodeB`, `accDecl`, `mutDecl`, `wDecl`, `qnAux`,
  `listDecl`, `roDecl`). Satisfied, not merely satisfiable.
* New in §8.6b, `residualCleanAllB` is the **installed** clause (right depth, right name set —
  `NoBlock` is `NoConsts D.blockNames`) scanned over a whole block, with
  `tq_cone_residualCleanAll` reading `true` at `tqAux tqAuxNodeB`, `mrAux mrAuxNodeB`,
  `mpAux mpAuxNodeB`, `ntreeAux`, `nfnAux`, and the *built* block
  `tqAux (tqOcc.ctor … miNode)`, and `tq_auxH_not_residualCleanAll` reading `false` at `tqAuxH`.
  §8.6's older `storedCleanB` differs from the clause in three ways (all fields not just recursive
  ones; depth `q.2` not `r.binders.length + q.2`; arbitrary `K` not `blockNames`) and is kept as the
  historical instrument.

Union: **13 blocks true, `tqAuxH` false**, exactly the audit's re-run. (`pfnDecl`, the 14th, has
only `none`-branch fields, so the clause is vacuous there and needs no producer.)

**(2) Nothing on `kernel_sound`'s path narrowed.** The edit *strengthens* `VIndField.WF`, hence
`VIndCtor.WF` and `VInductDecl'.WF`. Census of `VInductDecl'.WF`: 83 usages, and **every single one
under `Verify/` is in prose except one hypothesis-position use in
`Verify/ClosednessPropagation`** — there is no theorem anywhere in the tree that *concludes*
`VInductDecl'.WF` from checker success. So a strengthened `VIndField.WF` is a strengthened
**hypothesis** everywhere it appears on the soundness path, which is free, and no statement narrowed.
Verified by building, with **zero edits**: `Verify/Typing/ProjClosedG` (39 jobs),
`Verify/Typing/ProjLevelWitness` (36), `Verify/Typing/StructureUniq` (60),
`Verify/TypeChecker/EtaStructG` (142), and 11 of the 14 `Verify/Inductive/*` modules (182 jobs).

**The honest debit.** The refinement obligation "checker success ⟹ `VInductDecl'.WF`" is not stated
anywhere yet, so this edit adds no burden to any existing proof — but it does add one to that future
proof. That is a real cost, deferred, not avoided.

### 57.6 The kernel-fidelity premise, re-measured — and where the audit is wrong about the pi domain

Probes run with `lean_run_code` on scratch snippets, **no `#guard_msgs`, nothing written into the
repository**, for the reason §8.8 gives.

| probe | shape | kernel |
|---|---|---|
| A | `TQ ((fun _ => Nat) (MI Nat))` — firing trigger, residual names a **sibling** | **REJECTS**: "arg #2 of 'TQ.obj' contains a non valid occurrence of the datatypes being declared" |
| B | `TQ2 ((fun _ => Nat) (TQ2 Nat))` — residual names the block's **own** member | **REJECTS**: "arg #1 of 'TQ2.obj' …" |
| C | `TQ3 ((fun _ => Nat) Nat)` — same redex, **block-free** residual | **ACCEPTS** |
| D | `T4.mk : (r : T4) → (fun _ : T4 => Nat) r → T4` — the `none`-branch docstring's example | **ACCEPTS** |
| E | `T5.mk : ((_ : (fun _ => Nat) T5) → T5) → T5` — the **pi-domain** shape | inconclusive, see below |

A and B confirm the briefing's premise **in both cases** — the kernel refuses both a sibling and the
block's own member under such a redex. C confirms the clause must be *conditional on the trigger*
and vacuous off it, which is how it is written. D confirms the `none`-branch design note survives.

**E failed at the elaborator, not the kernel.** Surface Lean beta-reduces a binder-domain redex
before the kernel sees it: `#print T5.mk` reports `(Nat → T5) → T5`. I could not present the
pi-domain shape to the kernel through surface syntax at all, so **audit §4's claim that the
implementation rejects `tqBinderHostile` remains a source reading, not a run** — the same status
the audit gave it. I did verify the source independently, and it does say what the audit says:
`checkConstructors` calls `checkPositivity stats dom n i` on **every** field domain
(`Lean4Lean/Inductive/Add.lean`:382), and `checkPositivity` throws on `hasIndOcc stats.indConsts dom`
with **no `whnf` on `dom`** (`:335-338`). So the spec still over-accepts at the pi domain, the
residual half of the gap is now closed and the binder half is not, and audit §3b's conclusion — that
`restore_noK` does **not** suffice everywhere — stands. Note the distinction that makes this
consistent with `VIndRecArg.exists_indep`: `BindersIndep` is about a binder mentioning an earlier
recursive **field variable** (a `bvar`), which the implementation permits freely because `isRecArg`
strips pi binders without ever looking at their domains; the pi-domain gap is about a binder
mentioning a block **constant**, which `checkPositivity` rejects. Those are different positions and
only the second is a fidelity gap.

### 57.7 What I tried that failed, and the step it failed at

1. **`decidableResidualClean` via `decidable_of_iff` + a `residualClean_iff` proved by
   `cases h : D.uniformOcc? k e`.** Failed at `rw [h] at h'`: `cases h :` had already substituted
   the scrutinee, so the rewrite pattern no longer occurred, and for the same reason `H j rest h`
   was an application type mismatch (`H`'s type had been substituted too). Replaced by a direct
   `match h : … with` instance.
2. **`simp only [Option.some.injEq, Prod.mk.injEq] at h'`** on
   `some (j, rest) = some (j', rest')`. Failed — `rewrite` reported no occurrence of the pattern in
   that target. Replaced by `congrArg Prod.snd (Option.some.inj h')`, which pins the residual
   without touching the index; that is all the clause needs.
3. **First DeclExamples patch: appending `, by decide` inside the existing `⟨…⟩`.** Failed at
   elaboration, `Invalid ⟨...⟩ notation`, at 5 of the 6 sites — the flattening problem of 57.3(a).
   Fixed by re-nesting the trailing `∃` as `⟨_, by type_tac⟩`.
4. **`tq_hostileRec_binders_noBlock … := by simp`.** Failed, "`simp` made no progress", as a
   standalone theorem — inside the old `refine` the goal had already been reduced by unification.
   Needed `by simp [tqHostileRec]`.
5. **Probe E** — failed at the elaborator, 57.6.
6. **Not attempted, deliberately**: `Verify/Inductive/CanonGapMeasure`, `MemberRedexScan`,
   `UniformOccMeasure`. A closure walk shows all three transitively import the three
   `Theory/SetModel/*` files another stream has live this session (`CnstRecursion`,
   `InductOracleAudit`, `InaccChainOmega`); building them would compile another stream's
   work-in-progress. Their `VIndField.WF.pos` uses are `none`-branch consumers
   (`CGMAbstract.cgm_wf_forces_escape`), which the edit cannot reach. `Theory/SetModel/CtorTrans`
   and `PreludeWitness` likewise unbuilt for the same reason; both are `none`-branch only.
   **This is the one verification gap in this round.** No full `lake build`, no guards, no
   `sorry-census`, no `dup-names`, no `MemberRedexScan`, no MCP `lean_build`, as instructed.

### 57.8 Hygiene

Per-module `lake build` job counts, all green:
`Decl` 31 · `Restore` 34 · `Lemmas` 33 · `DeclExamples` 44 · `NestedHead` 61 · `NestedBuild` 62 ·
`RestoreOpWit` 62 · `MemberRedex` 63 · `RestoreBridge` 65 · `ParamRedex` 72 · `IndexedNested` 73 ·
`ConstSubstNested` 64 · `StructureEta` 61 · all 28 `Theory/Inductive/*` together 85 ·
11 `Verify/Inductive/*` together 182 · `ProjClosedG` 39 · `ProjLevelWitness` 36 ·
`StructureUniq` 60 · `EtaStructG` 142.

`sorry`: **one**, `VIndRecArg.exists_indep` (`Decl.lean`:561), pre-existing and untouched. No new
`sorry`, none traded, and it is the only `declaration uses sorry` warning across every module built.

`#print axioms` **by namespace**, on everything changed or added — 33 declarations across
`Lean4Lean.VExpr`, `Lean4Lean.VInductDecl'`, `Lean4Lean.VIndField.WF`,
`Lean4Lean.InductiveDeclExamples`, `Lean4Lean.MRedex.{QNWit,MPWit,TQWit}`, `Lean4Lean.ROWit`:
**no `sorryAx` anywhere**, and no axiom beyond `propext` / `Quot.sound` / `Classical.choice`.
`Classical.choice` appears at `recField_facts`, `nfnAux_WF`, `nfnAuxDirty_WF`, `mutDecl_WF`,
`wDecl_WF` and is pre-existing — `ntreeAux_WF` and `qnAux_WF` took the identical edit and do not
have it, so it is not coming from the edit. I did not re-measure a baseline (that needs git, which
I did no operations with), so read that last sentence as an argument, not a measurement.

### 57.9 What to pick up first

1. **`VIndCtor.WF env tqAuxH 0 T₀ tqObjH` is now IMPOSSIBLE, and §56.9's item 4 should be struck.**
   The previous round listed it as "the honest next proof". It is refuted by
   `tq_hostile_field_not_WF` composed with `VIndCtor.WF.fields`. Do not spend a session on it.
2. **`restore_ownOcc` / `restore_ownHeads` are now unexercised — decide whether to keep them.**
   `restore_ownOcc` has 3 usages, `restore_ownHeads` 10, none under `Verify/`. Their only witness of
   necessity was `tqAuxH`. They are not *refuted* — the pi-domain gap (57.6) means `restore_noK`
   genuinely does not suffice — but a witness for that would have to be a *recursive field whose
   stored binder domain hides a companion*, and 57.6 shows surface Lean cannot even express it. The
   witness would have to be written directly as a `VInductDecl'`, the way `tqAuxH` was.
   **That is the concrete next construction if anyone wants the strengthening exercised again.**
3. **Promote §8.6's helpers and retire the duplicate.** `VExpr.hasConstB` /
   `hasConstB_eq_false_iff` now live in `Decl.lean` with a `Decidable` instance; `MRedex.TQWit`'s
   local twins are redundant except for their arbitrary `K`. Re-point `storedCleanB` and
   `noConsts_of_storedCleanB` at the `Decl.lean` versions and delete the local copies —
   §56.9's item 2, now half-done by this round.
4. **`StoredIota.lean`:412's docstring is stale.** It says `VExpr.NoConsts` has no `Decidable`
   instance. It now has one, and `MRWit.mr_redex_noK` could be a `decide`.
5. **State the refinement obligation.** 57.5's debit: nothing yet concludes `VInductDecl'.WF` from
   checker success, so the new conjunct has no consumer on the soundness path. When that obligation
   is stated, `isValidIndAppIdx`'s residual loop (`Add.lean`:307) is what discharges it, and the
   `whnf`-is-identity-at-a-firing-trigger step is the one place it will need an argument rather
   than a computation.

---

# §58 `Built.fields_noK` — a producer, and a proof that it cannot be cheaper (round 9)

Assignment: find a producer for `VInductDecl'.Built.fields_noK`, or establish that none can
exist. After eight rounds of "no producer but `decide` at a concrete block" (ledger row 117c),
**both halves are now theorems.** New file, all mine: `Lean4Lean/Theory/Inductive/NestedFresh.lean`
(64 jobs, `lake build Lean4Lean.Theory.Inductive.NestedFresh`, no `sorry`, axioms per namespace
below).

## 58.1 Where the eight-round assessment went wrong

> "A repo-wide grep of every `NoConsts` occurrence found **no lemma anywhere** deriving
> `VExpr.NoConsts` from `HasType`, `VIndCtor.WF`, `Occurs` or `Declared`."

The grep is accurate and the conclusion drawn from it is false. **The fact `fields_noK` needs is
in this repo, stated about a different predicate.** `Theory/SetModel/Consts.lean` defines
`VExpr.ConstsIn : VExpr → (Name → Prop) → Prop` — the same recursion as `VExpr.NoConsts` — and
proves `VEnv.Ordered.constsInC`: *in an ordered environment, a declared constant's type mentions
only declared constants*, plus the weaker staged-environment invariant `VEnv.ConstsClosed` built
for exactly this situation ("`Ordered` is too strong for the *intermediate* stages of a block").
`VEnv.IsDefEq.constsIn` is the `HasType → ConstsIn` bridge the grep was looking for.

So the missing lemma was one `iff` away, and the `iff` is three lines:

```
theorem VExpr.noConsts_iff_constsIn {S : List Name} : ∀ {e}, NoConsts S e ↔ e.ConstsIn (· ∉ S)
```

**Lesson for the ledger, not for this corner only:** the eight-round claim was a grep on a
*predicate name*, not on a *statement shape*, and the corner has two names for one predicate.
`Theory/SetModel/Consts.lean`'s own header says it "would be at home in
`Theory/Typing/Lemmas.lean`" and lives under `SetModel/` only because that is where it was needed
— i.e. the file is filed by consumer, not by content, which is what made it invisible to an
inductive-corner grep.

## 58.2 Proved

All in `Theory/Inductive/NestedFresh.lean`.

* **`VNestedOcc.ctorType_noConsts`** — `env.ConstsClosed` + `Occurs env` + `∀ n ∈ K, ¬env.contains n`
  ⟹ `NoConsts K (C₀.type N.decl N.idx)` for every `C₀ ∈ N.src.ctors`. One environment step:
  `Occurs.ctor_const` says `J`'s constructor is a declared constant, `ConstsClosed` says its type
  mentions only declared constants, `hK` says a companion name is not one.
* **`VNestedOcc.fields_noK_of_occurs`** — the producer. Same three premises plus
  `hargs : ∀ a ∈ N.args, NoConsts K a`, concluding exactly `fields_noK`'s body. **Everything that
  quantifies over `J`'s constructors and fields is discharged**; the residual is the spine.
* **`VInductDecl'.builtFresh_of_occurs`** — `BuiltFresh` assembled from `nodup`, `Built.occurs`
  (which a `Built`-builder has by construction), `hK`, and per-member `hargs`.
* **`VInductDecl'.not_contains_of_mem_blockNames` / `fresh_of_addIndTypes`** — `hK` costs nothing:
  `addIndTypes` is an `addConstList`, `addConst` fails on a duplicate, so every member name of `D`
  (companion names included) was absent from `env`. Same argument as
  `VIndRestore.csubst_freshIn` (`NestedRules.lean` §8.1); the premise is `K ⊆ D.blockNames`, which
  is what `Built`'s own guard `D.types[j]? = some T → T.name ∈ K` presupposes.
* **`VNestedOcc.occurs_args_congr`** — `Occurs env` is invariant under replacing `N.args` by any
  list of the same length. Measured, not read off: `Occurs`'s seven clauses are `hist`, `idx_lt`,
  `lvls_len`, `args_len`, `ty_const`, `ctor_params`, `ctor_const`, and **only `args_len` mentions
  `N.args`, and only its length**.
* **`InductiveDeclExamples.fields_noK_needs_spine`** — the impossibility half, from the repo's own
  witness. `listOccBadSpine := { listOcc with args := [.const `_nested.List_1 [.param 0]] }`
  satisfies `Occurs env₁` (via `occurs_args_congr`), agrees with `listOcc` on `decl`, `idx`,
  `lvls`, `auxName` and spine length, and **refutes `fields_noK`** — because `List.cons`'s first
  field type is the bare parameter `.bvar 0`, so the substituted type is the spine entry verbatim
  (`listOccBadSpine_not_fields_noK`, by `decide`). `listOcc` satisfies it (`ntreeAux_built`).

  Therefore **no theorem whose hypotheses are `Occurs env` plus any facts about `env` and `K` —
  freshness, `ConstsClosed`, `Ordered`, `WF` — can prove `fields_noK`**: it would apply to both
  members of the pair and prove a false statement. A premise reading `N.args` is *necessary*;
  §58.2's producer shows the weakest one (`∀ a ∈ N.args, NoConsts K a`) is *sufficient*.

**So the answer to the assignment is neither "derivable" nor "unproducible" but a sharp
reduction:** `fields_noK`, a clause quantified over all of a foreign block's constructors and
fields, is equivalent — given facts every caller already has — to a statement about
`N.decl.np` expressions, decidable by `VExpr.decidableNoConsts`, and that statement cannot be
eliminated.

Axioms, by namespace (`#print axioms` at the foot of the file):

| namespace | result |
| --- | --- |
| `Lean4Lean.VExpr.*` (3) | `noConsts_iff_constsIn` **no axioms**; other two `[propext]` |
| `Lean4Lean.VNestedOcc.*` (3) | `[propext, Quot.sound]` |
| `Lean4Lean.VInductDecl'.*` (3) | `[propext, Quot.sound]` |
| `Lean4Lean.InductiveDeclExamples.*` (3) | `[propext, Quot.sound]`; `fields_noK_needs_spine` also `Classical.choice` |

No `sorryAx`, no frozen axiom, nothing traded. Whitelist base for all four rows is Guard.lean's
`{propext, Classical.choice, Quot.sound}` (`Verify/Guard.lean`:144).

## 58.3 Also landed: the general bridge, with the residual moved onto checker-visible data

New file, additive, nothing existing touched:
`Lean4Lean/Verify/Inductive/NestedFreshBridge.lean` (152 jobs, `[propext, Quot.sound]`).

`RestoreData.mkRestore_built_of_spine` and `mkRestore_AddNested_of_spine` are
`mkRestore_built` / `mkRestore_AddNested` with the `BuiltFresh` argument replaced by
`D.blockNames.Nodup` + `env.ConstsClosed` + `∀ n ∈ K, ¬env.contains n` +
`∀ j T, D.types[j]? = some T → T.name ∈ K → ∀ a ∈ as j, NoConsts K a`.

**`as` is `RestoreData`'s own parameter** (`h : r.RestoreData types D K as`), and `mkRestore_built`
already takes `ha : as j = (occ j).args`. So §6's note in `NestedRestoreWit.lean` — "nothing in
`RestoreData`, and nothing in `OccData`, mentions them, since both bundles are about the checker's
`Lean.Name`s" — is **half out of date**: after the reduction, the residual *is* about `RestoreData`,
namely about `as`, and `RestoreData` carries it.

## 58.4 Where the brief was wrong

1. **"It is not a fact about the checker's `Result`, so neither the `RestoreData` name facts nor
   the `OccData` ones can see it."** True of `fields_noK` as literally stated; **false of its
   residual.** After §58.2, the residual is `∀ a ∈ as j, NoConsts K a`, and `as` is one of
   `RestoreData`'s parameters — see §58.3.
2. **"A repo-wide grep of every `NoConsts` occurrence found no lemma anywhere deriving
   `VExpr.NoConsts` from `HasType`…"** The grep is a floor (`grep -rn`, mine too) and the
   conclusion drawn from it is false: `VEnv.IsDefEq.constsIn` is exactly that lemma, stated over
   `VExpr.ConstsIn`. See §58.1.
3. **"eight consecutive rounds"** — the *count* is right (eight mentions in this file, at lines
   384, 588, 841, 1075, 1393, 1743, 2088, 2471), but the file's own labels stop at "seventh": the
   last two both say seventh, so the internal numbering is one short of the count. Measured by
   `grep -n "fields_noK" docs/handoff-iota-stored.md`, not read off.
4. **Change #2 (F7's `ResidualClean`) does not reach `fields_noK`, in whole or in part.** Asked
   directly and answered by machine: `ntreeAux_residualClean_badSpine` shows `ResidualClean` is
   **true of the very expression that refutes `fields_noK`**, because `uniformOcc?` needs the
   parameter run and a bare companion constant has none. Structurally it is also the wrong object:
   `ResidualClean` constrains `D`'s *own stored* field types at a firing trigger; `fields_noK`
   constrains `J`'s field types before substitution, unconditionally.
5. **Change #1 (the `Decidable` instance) is real but not load-bearing.** It is accurately
   described — `hasConstB`, `hasConstB_eq_false_iff`, and three instances (`decidableNoConsts`,
   `decidableNoBlock`, `decidableResidualClean`). But the producer is a *proof*, not a decision;
   decidability only makes the residual spine premise cheap at a concrete block, which `simp
   [NoConsts]` already did. Nothing in §58.2 needed it.
6. **Change #3's framing was right about the restoration and wrong about the leverage.**
   `NoConsts` *is* the wrong test for the restoration — and it is **also** wrong-in-the-same-way
   here, but the weakening does not help: `listOccBadSpine_not_ownHeads` refutes the `OwnHeads`
   version of `fields_noK` on the same witness. The heads-only test fails on a bare companion
   constant for exactly the reason `NoConsts` does.

## 58.5 What failed, and the step it failed at — four `decide` refutations of my own claims

The brief's trap "`decide` is the arbiter; streams have asserted restoration behaviour and had
`decide` refute them" caught me four times in one session. All four were the *same* wrong claim:
that `field_typeR`'s conclusion (the restoration is the identity on the substituted field type) is
**false** without `hS`, which would have upgraded §58.2's impossibility from "about the stated
predicate" to "about the goal".

| witness (spine, then field) | failed at | `decide` says |
| --- | --- | --- |
| `[_nested.List_1 α]`, `listCons.fields[0]` | `restore` does not move: `uniformOcc?` needs the parameter run, a bare `.const` has none | equation **holds** |
| `[_nested.List_1 (bvar 0)]` (a firing occurrence), `listCons.fields[0]` | `field`'s recogniser fires, `typeR` canonicalises and restores back | equation **holds** |
| `[NTree (_nested.List_1 (bvar 0))]`, `listCons.fields[0]` | same | equation **holds** |
| `[_nested.List_1 (bvar 0)]`, a hand-made field `∀ (bvar 0), Sort 0` (the pi-domain shape of 57.6) | `VIndField.typeR` is `F.type` **verbatim** when `recArg = none` — the `none/none` branch never restores at all | equation **holds** |

The fifth attempt (a redex field type, aiming at `field`'s middle branch) did not even reach the
branch: both `recog S` and `recog (betaHead S)` were `none` (`#eval`, measured).

**What the four failures taught, and it is the lead worth having:** `hS` can only bite in
`field`'s `some` and middle branches, and those require `recog` to fire. `recog` recognises the
**presented** form (`R.tyName j` applied to `R.tyLvls j`, `R.tyArgs j`), which never carries an
auxiliary name, while `restore` moves only at an **aux-named** `uniformOcc?`. So "recog fires" and
"restore moves" pull in opposite directions, and a witness for `hS`'s necessity in `field_typeR`
needs both at once — which at `ntreeAux`/`ntreeRestore` means the companion has to be smuggled in
through `R.tyArgs` at a companion index, where `OwnId` does not constrain it. That is a
*hand-built restoration*, not one any construction produces, so the witness would be weak
evidence. **I did not build it, and I do not recommend it.**

Kept in the file as the record of the refutation: `listOccBadSpine_field_typeR_holds`.

## 58.6 Measured versus read-off

* **Measured**: all axiom prints (per namespace, at the foot of each new file); the four `decide`
  refutations above; the `#eval` of both `recog` calls; `Occurs`' clause inventory (read all seven
  clauses, `NestedBuild.lean`:646-670 — only `args_len` mentions `args`); the eight-mention count
  in §58.4.3; job counts (64 for `NestedFresh`, 152 for `NestedFreshBridge`); the absence of
  `Ordered env₁`/`ConstsClosed env₁` at the three concrete witness environments
  (`grep -rn "\.Ordered" Theory/Inductive` — one hit, unrelated).
* **Read off, not verified**: that `ElimNestedInductive.run` never puts an auxiliary name into a
  *spine* — I read `replaceIfNested`/`run` (`Lean4Lean/Inductive/Add.lean`:821-900) and the
  argument is that `args` always comes from a term that predates the replacement pass, so the
  spine premise should be *true* of what the checker builds. **Not proved, not even stated in
  Lean.** That is the obligation the producer creates on the checker side.
* **Floors, with the tool named**: every enumeration here is `grep -rn --include=*.lean` over
  `Lean4Lean/`. `lean_local_search` and `lean_hammer_premise` are still broken (`rg` absent) and
  `lean_references` is known incomplete; I used neither. In particular the claim "no other lemma
  derives `NoConsts` from `HasType`" is *now* false, so treat any similar absence claim in this
  file the same way.

## 58.7 Hole-free versus discharged

* **Discharged** (proved outright, no new premise anywhere): `noConsts_iff_constsIn`,
  `noConsts_instL`, `noConsts_mkPi_binders`, `ctorType_noConsts`, `occurs_args_congr`,
  `not_contains_of_mem_blockNames`, `fresh_of_addIndTypes`, and all six witness facts.
* **Hole-free but not discharged**: `fields_noK_of_occurs`, `builtFresh_of_occurs`,
  `mkRestore_built_of_spine`, `mkRestore_AddNested_of_spine`. They are `sorry`-free theorems, but
  they *have* premises, and one of those premises (the spine) is new. **The bill did not vanish;
  it shrank and moved to data the checker produces.** §58.2's impossibility half is what says it
  cannot shrink further.
* **Not shrunk at all**: the four existing `fields_noK :=` production sites
  (`NestedBuild.lean`:1078, 1566; `MemberRedex.lean`:1054; `RestoreBridge.lean`:972) still
  discharge it by computation, and `mkRestore_built_of_spine` has **zero consumers**. I did not
  re-point the witnesses at the producer: it needs `env.ConstsClosed` at each witness environment,
  and those environments are existential (`h : VEnv.empty.addInduct' listDecl = some env₁`) with no
  `Ordered`/`ConstsClosed` fact proven about them. That is a real, measured cost, not a nominal one.

## 58.8 Pick up first

1. **`ConstsClosed` for the witness environments.** `VEnv.ConstsClosed.addConst` already exists and
   is built for staged blocks; what is missing is `env.ConstsClosed → env.addConstList cs = some
   env' → (∀ ci ∈ cs, ci.type.ConstsIn env.contains) → env'.ConstsClosed`, and then
   `addInduct'`-level versions. With that, the three concrete `BuiltFresh` witnesses can be
   re-derived from the producer and the `decide`s deleted — which is the measurement that would
   show the producer is not vacuous.
2. **State the spine obligation on the checker side.** `∀ a ∈ as j, NoConsts K a`, from
   `ElimNestedInductive.run`. The argument (§58.6) is that a spine always predates the replacement
   pass; the Lean statement does not exist. This is now the *whole* of ruling 116d's residual, and
   it is a statement about `Result`, so `NestedOccData.lean`'s `OccData` is the natural home.
3. **Do not** chase a witness for `hS`'s necessity in `field_typeR` (§58.5's last paragraph). Four
   refutations and a structural reason why the fifth would have to be a hand-built restoration.
4. **Re-state ledger row 117c.** It is no longer "no producer but `decide`". The accurate statement
   is: *`fields_noK` is equivalent, given facts every caller has, to companion-freeness of the
   nested spine; and that residual is irreducible (`fields_noK_needs_spine`).* Ruling 116d's cost
   is permanent, but it is one order of magnitude smaller than recorded — from a clause quantified
   over a foreign block's constructors and fields to `D.np` decidable checks on `RestoreData`'s own
   `as`.

# §59 The producer CONNECTED: all four `fields_noK` sites re-pointed, the bridge given a consumer, and the `run`-level spine obligation **refuted** (round 10)

Assignment: connect §58's `fields_noK` producer — (1) re-point the four `fields_noK :=` sites and
give `mkRestore_built_of_spine` a consumer, (2) supply `env.ConstsClosed` at the witness
environments or establish why it cannot be supplied, (3) prove or refute the spine obligation over
`ElimNestedInductive.run`.

**All three are answered, and two of them differently from the way the brief framed them.**

## 59.1 Where the brief is wrong — six places

1. **"The four existing `fields_noK :=` sites still `decide`."**  None of them did.  All four
   discharged the clause by `rintro` over the member index plus `VExpr.noConsts_instAll` and
   `simp [VExpr.NoConsts, VExpr.instL, …]`, 15–19 lines each; the `decide`s inside those blocks were
   on the *side conditions* (`T.name ∈ K` at a non-companion index), never on `fields_noK` itself.
   The distinction is not cosmetic: the re-pointed proofs **do** each end in one `decide`, on the
   spine, so the direction of travel is `simp`-over-`J`'s-fields → `decide`-over-one-spine, not
   `decide` → proof.

2. **"Doing so needs `env.ConstsClosed` at the witness environments, which is unproven there —
   measured last round: no `Ordered`/`ConstsClosed` fact about those environments exists."**  False
   for two of the three witnesses.  `InductiveDeclExamples.listEnv_ordered`
   (`Theory/Typing/ConstSubstNested.lean`:848) and `pfnEnv_ordered` (*ibid.*:608) prove
   `env₁.Ordered` and `env₂.Ordered` **outright**, from `listDecl_WF` / `pfnDecl_WF` in the same
   file, and `VEnv.Ordered.constsClosed` is one step from there.  §58.6's measurement was
   `grep -rn "\.Ordered" Theory/Inductive` — **scoped by directory**, and the facts live in
   `Theory/Typing/`.  That is the §58.1 error (filed by consumer, not by content) repeated one round
   later, by the same stream, having written the lesson down.  The brief inherited it.
   It *is* right about the third witness: `qjDecl` (`MemberRedex.lean` §10) has no `WF` and no
   `Ordered` anywhere — measured, `grep -rn "qjDecl" --include=*.lean Lean4Lean/ | grep -i
   "wf\|ordered"`, empty.

3. **`ConstsClosed` was the wrong thing to ask for.**  The producer applies `hcc.1` at exactly one
   name, so only the *constants* half is used, and that half is obtainable with **no**
   `VInductDecl'.WF`, no `Ordered`, no levels, no positivity — from a premise about `D` alone
   ("every type the block declares mentions only names the block declares"), which is `decide` at a
   concrete block.  §59.3.  So the price was over-quoted at `listDecl`/`pfnDecl` and correctly
   quoted at `qjDecl`, where Route B does not exist and this is the only route.

4. **"A precise 'item 2 is unavailable at these environments because X' is a first-class result."**
   It is not the outcome: item 2 was available at all three environments, twice over at two of them.

5. **The blocker for item 1 was module order, not item 2** — and the brief does not mention it.
   §58's producer sat in `Theory/Inductive/NestedFresh.lean`, which **imports**
   `Theory/Inductive/NestedBuild.lean`, and two of the four sites are *in* `NestedBuild.lean`.  No
   amount of `ConstsClosed` could have re-pointed those two.  Fixed by moving the producer up into
   `NestedBuild.lean` (§F1–§F4 there) at the cost of one added import.

6. **Item 3's recorded reason is insufficient, not merely unproved.**  §58.6 read off that "`args`
   always comes from a term that predates the replacement pass".  That covers aux names introduced
   *by* replacement and says nothing about aux names present in the **input**, and the input is
   where they get in.  §59.5.

The brief's five traps were all accurate.  I hit none of them: I did not chase `field_typeR`'s
conclusion, did not route through F7's `ResidualClean`, ran the `run`-level probe outside the
repository first, and every restoration claim below is `decide`d or built.

## 59.2 Item 1: all four sites re-pointed, in place

The producer moved from `NestedFresh.lean` into `NestedBuild.lean` as **§F1–§F4**, with one new
import (`Lean4Lean.Theory.SetModel.Consts`; its transitive closure adds exactly one module, since
`Theory/Inductive/Decl.lean` already imports `Theory.Typing.Lemmas`).  `NestedFresh.lean` keeps §4
(freshness), §5 (`fields_noK_needs_spine` — the sharpness half) and §6 (the three refutations).
Name-collision check before moving: `grep -rn` for each of the fourteen declarations
`SetModel/Consts.lean` introduces (`VExpr.ConstsIn` and its lemmas, `CtxConstsIn`,
`VEnv.LE.contains`, `VEnv.IsDefEq.constsIn`, `Ordered.constsIn{,C,D}`, `Ordered.constsClosed`,
`ConstsClosed{,.addConst}`) plus the bare-name forms — no duplicate anywhere.

| site | file:line (was) | before | after |
| --- | --- | --- | --- |
| 1 | `NestedBuild.lean`:1078 `ntreeAux_built` | 17 lines, `rintro`+`simp` | 3 lines, `fields_noK_of_occurs` |
| 2 | `NestedBuild.lean`:1566 `nfnAux_builtFresh` | 19 lines | 3 lines |
| 3 | `MemberRedex.lean`:1054 `qnAux_builtFresh` | 19 lines | 3 lines |
| 4 | `RestoreBridge.lean`:972 `nfnAuxDirty_built` | 15 lines | 3 lines |

**And `mkRestore_built_of_spine` has a consumer**: `NestedWit.nfnAux_built'_of_spine`
(`Verify/Inductive/NestedFreshBridge.lean`) proves *the same conclusion* as
`NestedRestoreWit.lean`'s `nfnAux_built'` at the same `Result` and restoration, with `BuiltFresh`
replaced by `env₂.ConstsClosedC` + `nodup` + `nfnK_not_contains` + `nfnAs_noK`.  `nfnAs_noK` is the
residual, and it is one `decide` over `nfnAs`, a `RestoreData` parameter.  That is the measurement
§58.3 claimed and could not exhibit.

**What re-pointing cost, and it is real.**  Sites 2 and 3 were `omit h in` — environment-free
statements, and their docstrings said so.  The producer needs an environment, so both now take
`h : VEnv.empty.addInduct' pfnDecl = some env₂` (resp. `qjDecl`).  Their statements are strictly
weaker than they were.  Measured mitigation: **every consumer already carries `h`** —
`nfnAux_built` (`NestedBuild.lean`), `nfnAux_built'` (`NestedRestoreWit.lean`:704, inside
`include h in`), `qnAux_built` (`MemberRedex.lean`) — so nothing downstream lost generality, and the
three call sites now pass `h`.  If a future caller needs the environment-free form, the old proof is
in this file's git history and should be restored *alongside*, not instead.

## 59.3 Item 2: supplied, three times, and the general lemma is the point

`NestedBuild.lean` §F2, all new:

* **`VEnv.ConstsClosedC`** — the constants half of `VEnv.ConstsClosed`, named so it can be a
  hypothesis on its own.  `ConstsClosed.toC`, `Ordered.constsClosedC`, `empty_constsClosedC`.
  `fields_noK_of_occurs` and `builtFresh_of_occurs` now take *this*, not `ConstsClosed`; so do
  `mkRestore_built_of_spine` and `mkRestore_AddNested_of_spine`.
* **`VEnv.constsClosedC_addConstList`** — the list-extension step.  Unlike
  `ConstsClosed.addConst` it asks each added type to mention only constants of the **final**
  environment, not of the stage it is added at — which is what a block whose constructor types
  mention the block's own type names (i.e. every block) needs.  §58.8 item 1 asked for exactly
  this and guessed the statement one hypothesis too strong.
* **`VInductDecl'.constsClosedC_addInduct'`** (Route A) — `env.ConstsClosedC` +
  `env.addInduct' D = some env'` + *"every type `D` declares mentions only names in `D.allNames`"*
  ⟹ `env'.ConstsClosedC`.  No `WF`, no `Ordered`, no ι-rule obligation at all (`addInduct'_eq`
  factors the ι-rules out, and `addIndRules_contains` is the one line that says they do not move
  `contains`).
* **`VExpr.constsInB` / `constsInB_iff`** and
  **`VInductDecl'.constsClosedC_addInduct'_of_B`** — the side condition as a `Bool`.  Note
  `IndexedNested.lean`'s `hasConstB` decides `NoConsts S = ConstsIn (· ∉ S)`, the *complement*; the
  positive form needed here is a different function, and that file is downstream anyway.

Instantiated: `listDecl_selfConsts`, `listEnv_constsClosedC`, `pfnDecl_selfConsts`,
`pfnEnv_constsClosedC` (`NestedBuild.lean`), `qjDecl_selfConsts`, `qjEnv_constsClosedC`
(`MemberRedex.lean`).  The `selfConsts` premises are `by decide` and **include the recursor types** —
`List.rec`'s type went through without special handling, which was the thing I expected to have to
work around.

## 59.4 What each site's `decide` now is — the honest accounting

`decide` did not disappear; it moved and shrank.  Per block, after re-pointing:

* one `decide` on the **spine** (`listOcc_args_noK`, `pfnOcc_args_noK`, `qnOcc_args_noK`) — one to
  three `VExpr`s;
* one `decide` on the block's **self-containment** (`*_selfConsts`) — a `Bool` over `D.allConsts`;
* the pre-existing `decide`s on `blockNames.Nodup` and on `n ∉ D.allNames`.

What is gone is the `simp` traversal of *every field of every constructor of the foreign block `J`*.
Line count is roughly flat (each block gained ~12 lines of witness lemmas and lost ~15 of proof);
the gain is that the content is now general and the per-block residual is exactly the spine, which
`fields_noK_needs_spine` (§58.2) proves cannot be reduced further.

## 59.5 Item 3: REFUTED at the stated scope, and the missing premise named

§58.6's obligation was "`ElimNestedInductive.run` never puts an auxiliary name into a spine".
**It is false.**  Feed `run` directly

```
inductive T : Type | mk : List (_nested.List_1 T) → T
```

and it returns `aux2nested = [(`_nested.List_1, List (_nested.List_1 T))]` — the key and a constant
inside the stored spine are the same name, so `∀ a ∈ as j, VExpr.NoConsts K a` fails at
`K = [_nested.List_1]`.  Measured, not read off: `env.contains _nested.List_1 = false` at the repo's
own environment, `nextIdx` starts at `1`, so `mkUniqueName (`_nested ++ `List)` generates precisely
the name the input already mentions.  Nothing about the replacement pass is violated — the offending
constant came from the **input**.

So the obligation has **two** premises:

1. *pass ordering* — `replaceNoCacheT` is top-down and does not revisit a replaced node, and
   `newTypes[i]`'s stored constructor types are built before index `i` is processed.  This is what
   §58.6 named; it excludes aux names that replacement introduces.
2. *the gate* — `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean`:1056, called on every member type
   and every constructor type at `Environment.addInductive`:1073,1077, **before** `run`), which
   rejects any input mentioning a `_nested`-prefixed constant.  This is what excludes aux names the
   input supplies, and §58.6 did not name it.

Premise 2 is not a fact about `run`; it is a fact about its caller.  Landed:

* `ElimNestedInductive.Result.spineNoAuxB : Result → List Name → Bool` and `SpineNoAux`, the
  obligation as a decidable name fact about `aux2nested`, in `OccData`'s style (no `VEnv`, no
  `TrExprS`, no typing judgement) — §58.8 item 2's Lean statement, which did not exist.
* a **self-checking `#eval`** (`Verify/Inductive/NestedFreshBridge.lean`) asserting all three of:
  `run` accepts the input and violates `spineNoAuxB`; `checkNoNestedAux` rejects it;
  `Environment.addInductive` rejects it with the reserved-prefix error.  The third assertion is what
  `NestedOccData.lean` §10.1's own note says such a probe must include — without it the test would
  pass with the gate removed.  The build fails if any of the three stops holding.

**Still open** and this is the next round's item: `spineNoAuxB` is about `Lean.Expr`s in
`aux2nested`; `mkRestore_built_of_spine`'s `hspine` is about `VExpr`s in `as`.  Bridging them needs
(a) "translation preserves constant occurrences" at `TrExprS`, and (b) `RestoreData`-level agreement
between `aux2nested`'s stored args and `as j`.  Neither exists.  `nfnAs_noK` discharges `hspine` at
the concrete witness *without* that bridge, by `decide` on the `VExpr` side, so the bridge is not on
the critical path for the witnesses — only for the general theorem.

## 59.6 Files, jobs, axioms

Per-module `lake build`, all green, no `sorry` introduced and none traded (`grep -n sorry` over all
six touched files: clean):

| module | jobs |
| --- | --- |
| `Theory.Inductive.NestedBuild` | 63 (was 62 as a dependency; +1 = `SetModel/Consts`) |
| `Theory.Inductive.NestedFresh` | 64 |
| `Theory.Inductive.MemberRedex` | 64 |
| `Theory.Inductive.RestoreBridge` | 66 |
| `Verify.Inductive.NestedFreshBridge` | 152 |
| downstream sweep: `IndexedNested`, `StoredIota`, `NestedTele`, `NestedKeys`, `ConstSubstNested`, `Verify.Inductive.NestedOccData` | 187 |

`#print axioms`, by namespace, all inside Guard.lean's `{propext, Classical.choice, Quot.sound}`
(`Verify/Guard.lean`:144):

| namespace | result |
| --- | --- |
| `Lean4Lean.VExpr.*` (4) | `noConsts_iff_constsIn` **no axioms**; other three `[propext]` or `[propext, Quot.sound]` |
| `Lean4Lean.VEnv.*` (1) | `[propext, Quot.sound]` |
| `Lean4Lean.VInductDecl'.*` (3) | `[propext, Quot.sound]` |
| `Lean4Lean.InductiveDeclExamples.*` (11, `NestedBuild`) | `*_selfConsts` `[propext]`; rest `[propext, Quot.sound]` |
| `Lean4Lean.MRedex.QNWit.*` (5) | `qjDecl_selfConsts` `[propext]`; rest `[propext, Quot.sound]` |
| `Lean4Lean.InductiveDeclExamples.nfnAuxDirty_built` | `[propext, Quot.sound]` |
| `Lean4Lean.ElimNestedInductive.Result.RestoreData.*` (2) | `[propext, Quot.sound]` |
| `Lean4Lean.NestedWit.*` (2) | `nfnAs_noK` `[propext, Quot.sound]`; `nfnAux_built'_of_spine` also `Classical.choice` (from `nfnResult_occResidue`, as `nfnAux_built'` already was) |

No `sorryAx`, no frozen-axiom dependency, no new entry anywhere near `implGapWhitelist`.

## 59.7 Hole-free versus discharged

* **Discharged** (proved outright, no premise a caller does not already have): all of §F2's
  environment machinery; `ConstsClosedC` at all three witness environments; the four re-pointed
  `fields_noK` clauses; `nfnAs_noK`; the `run`-level refutation.
* **Hole-free but not discharged**: `mkRestore_built_of_spine` / `mkRestore_AddNested_of_spine`
  still carry the spine premise — that is §58.2's irreducible residual, and it has not shrunk, it
  has only been *paid* at one concrete `Result`.  `SpineNoAux` is stated and, for `run`, **cannot**
  be proved (§59.5); the statement that can be proved is about `addInductive`, and it is not proved.
* **Not shrunk at all**: the `Expr` → `VExpr` transfer for the spine (§59.5's "still open").  This is
  now the whole of ruling 116d's general residual.

## 59.8 What I tried that failed, and the step it failed at

| attempt | failed at | fix |
| --- | --- | --- |
| `ConstsClosed` for `addInduct'` including the **defeqs** half | the ι-rules' `lhs`/`rhs`/`type` are `mkLams` over `iotaCtx`; `ConstsIn` of them at a concrete block is a large `simp`, and *nothing uses it* — `ctorType_noConsts` touches `hcc.1` only | dropped the half; `ConstsClosedC` |
| the Route A side condition as `ConstsIn (· ∈ D.allNames)`, proved by `simp only [allConsts, listDecl, typeConsts, ctorConsts, recConsts]` | the goal after `simp only` is a 50-line unfolded `List.map … ++ …` with the block inlined four times; no `Decidable` instance for `ConstsIn` with a `Prop` predicate | `VExpr.constsInB` + `constsInB_iff`, then `by decide` |
| `constsInB_iff`'s `app`/`lam`/`forallE` case by `rw [show ∀ a b, …]` | the rewrite's motive did not match the `Bool.and_eq_true` shape (three identical errors, one per constructor) | `show (a.constsInB S && b.constsInB S) = true ↔ _; rw [Bool.and_eq_true]` |
| `fields_noK := fun _ _ _ _ _ hC₀ _ _ hF₀ => … (by decide) …` at all four sites | `decide` on the spine goal under the bound member index: *"Expected type must not contain free variables"* | named lemma per block (`listOcc_args_noK` etc.), `decide` at closed type |
| `ntreeK_not_contains` by `rintro n hn ⟨ci, hc⟩` then `revert hn; revert n; decide` | `hc` depends on `n`, so `revert n` drags it in and the `decide` goal has `ci` free | `have hnm : n ∉ listDecl.allNames := by revert hn; revert n; decide` **before** destructuring |
| inserting the witness lemmas immediately above `theorem ntreeAux_built` | that position is between a `/-- … -/` docstring and its declaration; `omit` is not a declaration | insert above the docstring; and a `/-- … -/` on a structure-instance *field* and on an `#eval` are both parse errors — use `--` and `/-! … -/` |

## 59.9 Search instruments, named, and treated as floors

* `rg` **absent** (`which rg` empty) — so `lean_local_search` and `lean_hammer_premise` remain dead.
  Not used.
* `lean_references` not used (known incomplete).
* Every enumeration here is `grep -rn --include=*.lean` over `Lean4Lean/`, plus `lean_diagnostic_messages`
  and `lean_goal` for the four failures above.  **Absence claims, with the definition named rather
  than a string:** (i) no declaration in the repo other than `Theory/SetModel/Consts.lean`'s
  declares any of the fourteen names that file introduces — the check was on declaration-line
  prefixes *and* bare-name forms, and it is a floor: a redeclaration inside `namespace VEnv.LE` of a
  short name would evade it; (ii) no theorem anywhere establishes `VInductDecl'.WF` or `VEnv.Ordered`
  at `qjDecl` (definition: `VInductDecl'.WF`, `Theory/Inductive/Decl.lean`; `VEnv.Ordered`,
  `Theory/Typing/Lemmas.lean`:258) — floor, same tool.  §59.1.2 is what a directory-scoped floor
  costs when it is read as a ceiling; do not repeat it.
* The `run`-level probe was developed in `/tmp` with `lake env lean` and only then landed as a
  self-checking `#eval`, per the brief's fifth trap.

## 59.10 Pick up first

1. **The `Expr` → `VExpr` spine transfer** (§59.7's "not shrunk").  Two lemmas: `TrExprS` preserves
   constant occurrences (probably already implied by something in `Verify/Typing/`; I did not look),
   and a `RestoreData`-level clause tying `aux2nested`'s stored args to `as j`.  With those,
   `spineNoAuxB` discharges `mkRestore_built_of_spine`'s `hspine` in general and ruling 116d's
   residual becomes a `Bool` the checker computes.
2. **`SpineNoAux` for `Environment.addInductive`, not for `run`.**  The statement is: gate ⟹
   `(run …).SpineNoAux K`.  Premise 1 of §59.5 is the monadic invariant "`newTypes[i]`'s stored ctor
   types mention no `_nested`-prefixed constant, for every `i` not yet processed", carried through
   `run.loop` and `replaceNoCacheT`.  This is the round's largest unbuilt piece.
3. **Do not** restore the environment-free forms of `nfnAux_builtFresh` / `qnAux_builtFresh` unless a
   consumer needs them (§59.2); all present consumers carry the environment.
4. **Re-state ledger row 117c again.**  Not "no producer but `decide`" (§58 killed that), and no
   longer "producer exists but has zero consumers": *all four production sites cite the producer,
   `mkRestore_built_of_spine` has a consumer, the environment premise is discharged at all three
   witness blocks with no `WF`, and the only remaining gap is the `Expr`/`VExpr` transfer for the
   spine.*
5. **Ledger note on the method.**  Two rounds in a row, a "this fact does not exist" claim was a
   grep scoped by the wrong axis — first by predicate name (§58.1), then by directory (§59.1.2).
   Both times the fact was one file away in `Theory/Typing/` or `Theory/SetModel/`. The cheap
   defence is to grep for the *statement shape* (`grep -rn "Ordered\b"` over all of `Lean4Lean/`,
   then filter) rather than for a name in a directory.
