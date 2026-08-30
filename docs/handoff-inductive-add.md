# Handoff: the inductive side — Wall 2 is closed, and Wall 1 was mis-stated

Successor to the previous revision (which named `VEnv.addInductR_ordered` and "the
`DeltaUnique` freshness argument" as the two remaining walls).  §§0, 1–4 of the previous
revision carry forward **unchanged and still true** and are not repeated in full; §§A–E below
are this round.  Where a previous §-number is cited it is the previous revision's.

Everything below is either **[MC]** machine-checked (a Lean proof in this tree, named), **[EV]**
checked by evaluation (a `#eval` that fails the build on regression — a test, not a proof), or
**[SRC]** read off source without a proof.  **[MC]** and **[SRC]** are never mixed in a row.

**Census.**  `lake env lean scripts/sorry-census.lean` → **19** before this round, **19**
after.  No `sorry` added, none removed, none made vacuous.  (The previous revision said 20;
another stream closed one between rounds.  Never grep for `sorry`.)

**Build state.**  Green on the same commit: `Lean4Lean.Theory` (the full aggregate),
`Verify.{Soundness, SafeFragment, Bridge, InductFlip}`, `Verify.Environment.InductR`,
`Theory.Inductive.{NestedKeys, NestedOrdered, NestedPositivity}`.
`Verify/Inductive/AddDeclWF.lean` went red and green again during the session under *another*
stream's edits; it was not touched here and builds green at the end.

**Files.**  New, owned: **`Lean4Lean/Theory/Inductive/NestedKeys.lean`**.  Edited, owned:
`Theory/Typing/DeltaUnique.lean`, `Theory/Inductive/{Restore,NestedHead,NestedBuild,NestedOrdered}.lean`.
No unowned file was edited; no frozen file was touched.

---

## A. The headline

**Both walls were mis-stated, in the same way, and the correction is machine-checked in both
cases.**  The defect class is the one the brief names: *a statement carrying less information
than its conclusion needs.*

* **Wall 2 was not a proof gap — the invariant is false.**  `Theory/Typing/DeltaUnique.lean`'s
  `VEnv.KeyMajorUnique` ("a rule is determined by the head of its major premise") is **false**
  in an environment holding a nested block, so no repair of `keys_induct`'s freshness argument
  could have worked.  `InductiveDeclExamples.nfn_keyMajorUnique_false` **[MC]** exhibits the
  pair: `PFn`'s own ι-rule, keyed `[PFn.rec, PFn.mk]`, and `NFn`'s companion ι-rule, keyed
  `[NFn.rec_1, PFn.mk]`.  Two rules, one major-premise head.
  **Wall 2 is now closed**: the true statement is `VEnv.KeyUnique` (uniqueness by the *whole*
  key), it is proved for the current tree **[MC]**, its one consumer is re-proved from it
  **[MC]**, and it is proved **preserved by a nested step** **[MC]** — see §B.
* **Wall 1's three obligations were said to be dischargeable "from `Faithful` plus
  `D.WF env`".  They are not, and at the wrong restoration they are false.**
  `VIndRestore.Faithful`'s three clauses are *all* guarded by `T.name ∈ K`: they say nothing
  about the members the step **declares**.  `VIndRestore.faithful_of_nil` **[MC]** — at
  `K = []` every clause is vacuous, so *every* restoration is `Faithful` — and
  `InductiveDeclExamples.pfnJunk_would_have_passed` **[MC]** is the configuration that admits
  at a real block: `PFn` presented as `Nat`, `Faithful` satisfied, `addInductR` succeeding, and
  `PFn.mk` declared at a type whose result is `Nat`.  Obligation (A) is *false* there.
  The other two hypotheses, `D.WF env` and `D.Canonical`, **do not mention `R` at all**, so no
  strengthening of them could have excluded it.
  **The repair has landed**: `VIndRestore.OwnId` **[MC]**, now a conjunct of `VEnv.AddNested`
  and a field of `VInductDecl'.Built`, with both nested witnesses supplying it and
  `AddNested_nil`'s conservativity intact.  Wall 1's three obligations remain **open**, but
  they are now *stateable as true*; §C gives the exact remaining step.

---

## B. Wall 2, closed

### B.1 The refutation

| name | file | statement | tag |
|---|---|---|---|
| `InductiveDeclExamples.pfn_iotaRule_key` | `NestedKeys.lean` | `(pfnDecl.iotaRule 0 0 pfnMk).key = [PFn.rec, PFn.mk]` | **[MC]** |
| `InductiveDeclExamples.nfn_companion_iotaRule_key` | `NestedKeys.lean` | `(nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk).key = [NFn.rec_1, PFn.mk]` | **[MC]** |
| `InductiveDeclExamples.nfn_keyMajorUnique_false` | `NestedKeys.lean` | after the nested step, `¬ env₃.KeyMajorUnique` | **[MC]** |
| `InductiveDeclExamples.nfn_keys_ne` | `NestedKeys.lean` | the same pair has **different** keys — so it does *not* refute `KeyUnique` | **[MC]** |
| `InductiveDeclExamples.nfn_keys_summary` | `NestedKeys.lean` | **hypothesis-free**: `∃ env₂ env₃`, `PFn` declared, a real `VEnv.AddNestedStep` to `env₃`, `¬ KeyMajorUnique env₃`, **and** `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique` preserved | **[MC]** |

`nfn_keys_summary` is the non-vacuity check: the step is `nfnAux_AddNestedStep`, not an
assumption, and `env₂` exists by `rfl`.

### B.2 The replacement, and that it is preserved

```lean
def VEnv.KeysNonempty (env : VEnv) : Prop := ∀ df, env.defeqs df → df.key ≠ []
def VEnv.KeyUnique (env : VEnv) : Prop :=
  ∀ df df', env.defeqs df → env.defeqs df' → df.key = df'.key → df = df'
```

* `VEnv.WF'.keysNonempty`, `VEnv.WF.keysNonempty` **[MC]** — its own seven-arm `WF'` induction,
  in the style Part III of `DeltaUnique.lean` already uses; every rule a declaration produces
  is headed by a constant.
* `VEnv.keyUnique_of_major` **[MC]** — `KeyMajorUnique ∧ KeysNonempty → KeyUnique`.  So
  `VEnv.WF.keyUnique` **[MC]** holds *today*, cheaply, and **nothing in Part II is disturbed
  and no existing proof is re-run**.  The converse fails, which is the whole point.
* `VEnv.keysU_mono`, `keysU_addDefEq_notDelta`, `keysU_addDefEqList_notDelta` **[MC]** — the
  step and fold lemmas for the `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique` triple.  They sit
  beside the `KeyMajorUnique` versions; the difference is one hypothesis, `hkey` (the new
  rule's *whole key* is new) in place of `hmaj` (its *last name* is new).
* **`VEnv.keysR_induct`** **[MC]** — **the nested arm**:

  ```lean
  theorem keysR_induct (hR : env.addInductR D K R = some env')
      (hf : R.Faithful D env K npJ) (hd : R.KeysDistinct D)
      (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
      env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique
  ```
  and `VEnv.keys_addNestedStep` **[MC]**, the same from `VEnv.AddNestedStep`.

### B.3 Why each obligation goes through, and where the old argument died

| obligation | declared member | **companion** member |
|---|---|---|
| `hdecl` (key names declared) | own `ctorConstsCR` / `recConstsR` | **`Faithful.ctor_agree` verbatim** — the environment already holds it |
| `hδ` (no δ-rule head in the new key) | freshness | `ctors_complete` names the block `D₀` the environment holds; `VInductDecl'.Declared` puts `D₀`'s ι-rules in `env`; `KeyHeadDelta` at `env` identifies the δ-rule with one of them; `not_isDeltaRule_iotaRule` forbids it |
| `hkey` (the new key is new) | head is fresh | **head is fresh** — every name in a registered key is declared (`KeysDeclared`), the head is not |
| ~~`hmaj`~~ (the last name is new) | — | **impossible: `iotaRulesR_major_not_fresh` says the last name *is* declared.**  This is the row that killed the old invariant |

The `hδ` companion row is the load-bearing one: **the old invariant discharges the new step's
obligation**; no new invariant is introduced anywhere.

### B.4 The one consumer, and the exact edit `PatternRules.lean` needs

`KeyMajorUnique` has exactly **one** use in the tree: `Pat.iota_rule_uniq`
(`Theory/Typing/PatternRules.lean:839`).  `Pat.deltaHead_ne_recName`, `.deltaHead_ne_ctorName`
and `Pat.deltaHead_ne_quot` use `KeyHeadDelta`, which survives unchanged.

`Pat.iota_rule_uniq_keyUnique` (`NestedKeys.lean`) **[MC]** proves the same conclusion from
`KeyUnique`.  `VInductDecl'.iotaPat_inj` already returns the recursor-name equation — it is
discarded at line 845 — so the whole key is available; the only cost is two extra hypotheses
`D.types[j]? = some T`, `D'.types[j']? = some T'`, needed because the key's head is
`mkRecName (D.types.getD j default).name` while the pattern carries `mkRecName T.name`.

**Those two hypotheses are already in scope at the sole call site** (`Pat.iota_data_uniq`,
`PatternRules.lean:1005`, which passes exactly `hTj` and `hTj'` to `VInductDecl'.iotaRule_inj`
on the very next line) **[SRC]**.  So the edit, when the nested rule lands, is:

* `PatternRules.lean` — `Pat.iota_rule_uniq` gains `(hTj) (hTj')`, and its body's
  `henv.keyMajorUnique` becomes `henv.keyUnique` with the head equation supplied; the call at
  line 1005 passes `hTj hTj'`.  `Pat.iota_rule_uniq_keyUnique'` **[MC]** is the regression:
  today's statement is an instance of the new one, so nothing is lost.
* `DeltaUnique.lean` — `WF'.keys` drops `KeyMajorUnique` and carries `KeyUnique`;
  `keys_induct` becomes `keysU_*` (the four arms are already written), and the `induct`
  arm gains `keysR_induct`.  `KeyMajorUnique` itself can stay as a definition — it is still
  *true* today, and `nfn_keyMajorUnique_false` is what says it stops being.

**This file owns `DeltaUnique.lean`; it does not own `PatternRules.lean`, and did not edit it.**

### B.5 The one side condition, and its non-vacuity

`VIndRestore.KeysDistinct R D` — *no two entries of `D.ctorsAll` get the same (renamed
recursor, restored constructor) pair*.  A purely syntactic property of `R` and `D`, with no
environment in it, and `decide`-able at a concrete block:

* `InductiveDeclExamples.ntreeRestore_keysDistinct`, `nfnRestore_keysDistinct` **[MC]**, both
  by `decide`.  Both witnesses have a companion member whose restored constructor name is one
  the environment already holds (`List.cons`, `PFn.mk`), i.e. exactly the configuration
  `KeyMajorUnique` fails at.
* `InductiveDeclExamples.nfnAux_keys` **[MC]** — `nfnAux` really has *two* rules, keyed
  `[NFn.rec, NFn.node]` and `[NFn.rec_1, PFn.mk]`; the property separates two rules, not one.

**Open, and the only thing left on Wall 2:** `KeysDistinct` is *derivable* rather than
assumed, from the two `addConstList` successes plus `Faithful.ctors_complete` — the renamed
recursor names are `Nodup` because `addConstList (D.recConstsR R)` succeeded, which separates
different members; within a member, a declared member's restored constructor names are `Nodup`
for the same reason, and a companion member's are the constructor names of the block
`ctors_complete` names, `Nodup` because that block was declared.  The derivation is list
combinatorics over a `filterMap` and is **not carried out**.  It is a side condition of
`keysR_induct`, discharged at both witnesses, so nothing downstream is blocked on it — but it
is the honest remaining item.

---

## C. Wall 1, re-stated — and the hole it was hiding

### C.1 What was wrong

The previous revision's §5.2 said the three obligations of `VEnv.addInductR_ordered'` "are to
be discharged **from `Faithful` plus `D.WF env`**".  Machine-checked refutation:

| name | file | statement | tag |
|---|---|---|---|
| `VIndRestore.faithful_of_nil` | `Restore.lean` | `∀ R D env npJ, R.Faithful D env [] npJ` — `Faithful` is **vacuous** at `K = []` | **[MC]** |
| `InductiveDeclExamples.pfnJunkRestore` | `NestedBuild.lean` | a restoration presenting `PFn` — a **declared** member — as `Nat` | (def) |
| `InductiveDeclExamples.pfnJunk_ctorConstsCR` | `NestedBuild.lean` | it declares `PFn.mk` at a type whose **result is `Nat`** | **[MC]** |
| `InductiveDeclExamples.pfn_idRestore_ctorConstsCR` | `NestedBuild.lean` | the contrast: at `idRestore` the same list is `[(PFn.mk, pfnMk.type pfnDecl 0)]` | **[MC]** |
| `InductiveDeclExamples.pfnJunk_admitted` | `NestedBuild.lean` | `VEnv.empty.addInductR pfnDecl [] pfnJunkRestore` **succeeds** | **[MC]** |
| `InductiveDeclExamples.pfnJunk_would_have_passed` | `NestedBuild.lean` | `Faithful` ∧ the step succeeds ∧ `¬ OwnId` | **[MC]** |

`addInductR`'s success is a freshness-and-`Nodup` condition on *names*, which a junk
restoration does not disturb; `D.WF env` and `D.Canonical` do not mention `R`.  So obligation
**(A)** — a declared constructor's restored stored type is a type — is not open at
`pfnJunkRestore`, it is **false**, and had the `inductNested` rule landed with only `Faithful`
in its premise, `VDecl.WF` would have admitted an environment whose constants carry types
nothing relates to the block.

### C.2 The repair, landed

```lean
structure VIndRestore.OwnId (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name) : Prop where
  tyName   : ∀ j T, D.types[j]? = some T → T.name ∉ K → R.tyName j = T.name
  tyLvls   : ∀ j T, D.types[j]? = some T → T.name ∉ K → R.tyLvls j = D.ownLvls
  tyArgs   : ∀ j T, D.types[j]? = some T → T.name ∉ K → R.tyArgs j = bvars 0 D.np
  recName  : ∀ j T, D.types[j]? = some T → T.name ∉ K →
    R.recName (mkRecName T.name) = mkRecName T.name
  ctorName : ∀ j T, D.types[j]? = some T → T.name ∉ K → ∀ C ∈ T.ctors, R.ctorName C.name = C.name
```

*Off `K`, the restoration renames nothing and re-instantiates nothing.*  All **[MC]**:

| item | status |
|---|---|
| `VIndRestore.OwnId.tyAppR_eq` | the payoff: at a declared member `D.tyAppR R j k args = D.tyApp j k args`, via `tyAppH_bvars` |
| `VInductDecl'.idRestore_ownId` | the identity restoration satisfies it for **every** `K` |
| `VEnv.AddNested` | now `D.WF env ∧ D.Canonical ∧ R.OwnId D K ∧ R.Faithful D env K npJ ∧ addInductR … = some env'` — hence `AddNestedStep`, hence the rule's premise |
| `VInductDecl'.Built` | gained an `own : R.OwnId D K` field; `Built.toFaithful` and `AddNestedB.toAddNested` pass it through |
| `ntreeRestore_ownId`, `nfnRestore_ownId` | **both nested witnesses supply it** |
| `VEnv.AddNested_nil` | **conservativity intact**: still `↔ D.WF env ∧ env.addInduct' D = some env'` at `idRestore` |
| `ntreeAux_AddNested`, `ntreeAux_AddNestedStep`, `nfnAux_AddNestedB`, `nfnAux_AddNestedStep` | all re-proved through the new conjunct — **the rule's premise is still inhabited** |
| `VEnv.addInductR_ordered'` | now threads `hown : R.OwnId D K`, recording the intended discharge |

### C.3 What is still open, and the exact failing step

`VEnv.addInductR_ordered` and `addInductR_ordered'` are unchanged in structure: `Ordered env'`
follows from four staged obligations, the first (`addInductR_typeConstsC_wf`) is free, and
three remain.  They are now to be discharged from **`OwnId` + `Faithful` + `D.WF env`**.

**(A)** a declared constructor's restored stored type is a type at `env + typeConstsC K`.
**(B)** each renamed recursor's restored type is a type at `env + typeConstsC K + ctorConstsCR R K`.
**(C)** each restored ι-rule is a well-formed `VDefEq` there.

**The exact failing step, for all three.**  With `OwnId` the result-position heads are
unchanged (`tyAppR_eq`), so the entire remaining content is the *field* positions: a recursive
field of a declared constructor whose `r.idx` is a **companion** member is stored as
`∀ ξ, _nested.PFn_1 params π` and restored to `∀ ξ, PFn A π`, and the staging environment
holds `PFn` but **not** `_nested.PFn_1`.  What `D.WF env` gives is a typing derivation over
`env.addIndTypes D`, which holds `_nested.PFn_1` and not the restored form.  Transporting it
needs:

> **the missing lemma** — if `env.constants J = some ⟨u, τ⟩` and `R.instAt D (npJ j) j τ` is the
> companion member's stored type (which is `Faithful.ty_agree`, exactly), then replacing every
> `.const J_aux` head by `tyAppH (R.tyName j) (R.tyLvls j) (R.tyArgs j)` preserves
> `IsType`/`HasType`.

That is a **substitution-of-a-constant-by-a-term** typing theorem, and **there is nothing of
the kind in `Theory/`** — searched: no `ConstSubst`, no `substConst`, no `replaceConst`; the
only environment-directed transport lemmas are `HasType.mono`/`IsType.mono` (weakening along
`≤`), which does not apply because `_nested.PFn_1` is *removed*, not added **[SRC]**.  So Wall 1
is one named theorem, not three, and that theorem is new machinery rather than a
re-arrangement of existing lemmas.  `VEnv.addInductR_ordered_nil` **[MC]** is unchanged and
still shows the three collapse to what `addInduct'` already proves at `K = []`, `R = idRestore`
— so they remain about the *restoration*, not about inductives.

A second, smaller item noticed while doing C.2: the `_id` chain in `NestedHead.lean`
(`canonResultR_id … recTypeR_id`, ~20 lemmas) is stated at `D.idRestore`.  Under `OwnId D []`
every one of them should generalise, which would upgrade `addInductR_eq_addInduct'` from "at
`idRestore`" to "at any restoration that is the identity off `K`".  Not attempted; mechanical,
and it would make `addInductR_ordered_nil` unconditional in `R`.

---

## D. `VIndRecArg.exists_indep` — inventoried, not in reach

One of the 19, in `Theory/Inductive/Decl.lean` (owned).  Its own docstring names the blocker
and the census confirms it is still there **[MC, by census]**: the proof needs
`VEnv.IsDefEqU.forallE_inv` (`Theory/Typing/Injectivity.lean`) to rule out an ill-formed field
of type `(∀ ξ₀, I p π₀) → Sort u`, and `forallE_inv` is itself one of the 19 and is being
worked by another stream (`Injectivity.lean` gained 269 lines this session, and all six of its
`sorry`s are still present).  **Not attempted.**  It is a strict dependency, not a difficulty
estimate: nothing else in the argument is missing.

---

## E. The flip: the gate list, updated

**Verdict: still not landable, and the gate list is now shorter by one and longer by one.**

| gate | status after this round |
|---|---|
| (i) `VEnv.addInductR_ordered` — the three obligations | **open**, and now correctly stated; one missing theorem, §C.3 |
| (ii) the `DeltaUnique` repair | **CLOSED** — §B.  `KeyUnique` replaces `KeyMajorUnique`, is preserved by `keysR_induct`, and the consumer is re-proved |
| (ii′) `VIndRestore.KeysDistinct` derivable rather than assumed | **open**, list combinatorics, blocks nothing (§B.5) |
| (iii) the `inductNested` rule plus the nine case arms of the previous §5.4 | gated on (i); the four *unowned* sites are unchanged, and `DeltaUnique.lean` is **owned** by this stream, so that row of the previous §5.4's table was wrong |
| (iv) rows 6–9 of the previous §6 — the nine `Verify/TypeChecker/` statements | **the human's decision, unchanged.**  Reported, not acted on |

The previous §5.4's table listed `Theory/Typing/DeltaUnique.lean` and
`Theory/Typing/PatternRules.lean` as "not owned".  `DeltaUnique.lean` **is** owned by this
stream (the brief lists it); `PatternRules.lean` is not, and §B.4 states its exact edit rather
than making it.

**The order is now: (i) the constant-substitution typing theorem of §C.3; then (iii); then
(iv) to the human.**  (ii) is done.

---

## F. Ledger of edits to owned files

| file | change |
|---|---|
| `Theory/Inductive/NestedKeys.lean` | **new**.  §1 the consumer from `KeyUnique`; §2 the refutation at the `NFn`/`PFn` witness; §3 `not_isDeltaRule_iotaRuleR`, `recName_mem_recConstsR`, `ctorName_mem_ctorConstsCR`, `VIndRestore.KeysDistinct`, `iotaRulesR_pairwise_key`, `keysR_induct`, `keys_addNestedStep`; §3.3 the witnesses and `nfn_keys_summary` |
| `Theory/Typing/DeltaUnique.lean` | **Part IV** appended: `KeysNonempty`, `KeyUnique`, `keyUnique_of_major`, the `keysNonempty_*` step lemmas and `WF'.keysNonempty`/`WF.keysNonempty`/`WF.keyUnique`, and `keysU_mono`/`keysU_addDefEq_notDelta`/`keysU_addDefEqList_notDelta`.  **Parts I–III are untouched**; no existing proof was re-run |
| `Theory/Inductive/Restore.lean` | `VIndRestore.faithful_of_nil`; `VIndRestore.OwnId` + `idRestore_ownId` + `OwnId.tyAppR_eq`; `VEnv.AddNested` gained the `OwnId` conjunct |
| `Theory/Inductive/NestedHead.lean` | `ntreeRestore_ownId`; `AddNested_nil` and `AddNested_keys_declared` and `ntreeAux_AddNested` adjusted to the new conjunct |
| `Theory/Inductive/NestedBuild.lean` | `pfnJunkRestore` and its five theorems (§C.1); `nfnRestore_ownId`; `Built` gained `own`; `ntreeAux_built`/`nfnAux_built`/`AddNestedB.toAddNested` supply it |
| `Theory/Inductive/NestedOrdered.lean` | the §C.1 audit as a section docstring; `addInductR_ordered'` threads `hown` |

---

## G. Carried forward from the previous revision, still true

* §§1–4 of the previous revision — `AddInductStagesR` and its invariant, `InductStepNested`
  and its two corrections, the re-run refutation with its four negative controls and checks
  C/C′/D **[EV]**, and the closed model at `NFn`/`PFn` — are **unchanged and untouched**.
* `addDecl.WF`'s `inductDecl` branch is **false, not open** (`addDecl_inductDecl_WF_false`
  **[MC]**).  Unchanged.
* The `.unsafe` hole (`unsafe_induct_unreachable` **[MC]**) is unchanged and independent of
  everything above.
* Not proved and not attempted this round: the flip; `AddInductiveObligation`; the `.unsafe`
  rule; the nine `Verify/TypeChecker/` declarations; any edit to `Theory/Typing/Env.lean`'s
  inductive.

---

<details>
<summary>Previous revision, retained verbatim for §§1–4 and the previous §-numbering</summary>

# Handoff: the inductive side — the nested step is stateable now, and the blocker moved

Successor to the previous revision (which named the declaration history `ds` as the one
remaining blocker).  §§0, 5–8 are this round; §§1–4 carry forward **unchanged** and are still
true.

Everything below is either **[MC]** machine-checked (a Lean proof in this tree, named), **[EV]**
checked by evaluation (a `#eval` that fails the build on regression — a test, not a proof), or
**[SRC]** read off source without a proof.

**Build state.** All 96 `Lean4Lean/Theory/**` modules green, plus `Lean4Lean.Verify.Soundness`,
`.SafeFragment`, `.Bridge`, `.InductFlip`, `.Inductive.AddDeclWF`, `.Environment.*`.
(`Theory/Typing/HeadRedStuck.lean` and `Verify/Typing/{ProjSkip,StructureUniq}.lean` went red
and green again during the session under *other* streams' edits; they were not touched.)
`lake env lean scripts/sorry-census.lean` → **20**, unchanged.  No `sorry` added, no frozen
file touched, no unowned file edited.

**Files.**
New, owned: **`Lean4Lean/Theory/Inductive/Restore.lean`** (360 lines, 39 declarations) and
**`Lean4Lean/Theory/Inductive/NestedOrdered.lean`** (179 lines, 9 declarations); both
`sorryAx`-free, axioms `propext`/`Classical.choice`/`Quot.sound` only.
Edited, owned: `Theory/Inductive/{Decl,Lemmas,Nested,NestedHead,NestedBuild,Companion,CompanionResolve}.lean`,
`Theory/Typing/Env.lean`, `Verify/Environment/{Basic,InductR}.lean`.  §7 has the ledger.

---

## 0. The headline

**The previous handoff's blocker was real but was only half the obstruction, and the half it
named is now gone.**

* **The declaration history is not needed.**  `ds : List VDecl` was threaded through
  `VIndRestore.Faithful`, `VNestedOcc.Occurs`, `VInductDecl'.Built` and `VEnv.AddNested{,B}`
  for exactly one purpose: `hist : VDecl.induct N.decl ∈ ds`, "this block was declared
  earlier".  That is now **`VInductDecl'.Declared`** — `∃ env₀ env₁, env₀.addInduct' D = some
  env₁ ∧ env₁ ≤ env` — a statement about the environment alone, and a history discharges it
  (`VEnv.WF'.declared` **[MC]**).  Every one of those five definitions has lost its `ds`
  parameter, and both end-to-end witnesses were re-proved through the new clause **[MC]**.
* **The step is now nameable at `Theory/Typing/Env.lean`.**  It was not: `VEnv.addInductR` and
  `VIndRestore.Faithful` lived in `Theory/Inductive/NestedHead.lean`, which is *downstream* of
  `Env.lean` (`Env` ← `DeltaUnique` ← `Nested` ← `Companion` ← `CompanionResolve` ←
  `NestedHead`), so the rule could not have been written even with `ds` solved.  The
  definitional core moved **verbatim** upstream into `Theory/Inductive/Restore.lean`; the
  `example` at the end of `Env.lean`'s new section is the machine-checked proof that
  `VEnv.AddNestedStep` elaborates there **[MC]**.
* **`npJ` was an under-constrained parameter, and is now pinned.**  `VEnv.AddNested` takes
  `npJ : Nat → Nat`, the parameter count the companion is presented at; existentially
  quantifying it (which a `VDecl.WF` rule must) would have let a companion be presented at a
  *wrong* instantiation of the block it claims to be, with its recursor's minor premises then
  matching nothing — `fooComp_inconsistent`'s failure mode by another route.
  `Faithful.ctors_complete` now also asserts `npJ j = D₀.np`, `D₀` being the block the
  environment holds, so `VEnv.AddNestedStep := ∃ npJ, AddNested …` gives a caller nothing
  **[MC]**.
* **The rule text is written, machine-checkable, and *not added*** — see §5 for exactly why,
  and `Theory/Typing/Env.lean`'s new section docstring for the text.
* **Two theorems now stand where "the history" used to**, and they are the actual content:
  `VEnv.addInductR_ordered` (the restored types are well typed) and a repair of
  `Theory/Typing/DeltaUnique.lean`'s freshness argument, **which is false for a nested block**
  — `VEnv.iotaRulesR_major_not_fresh` **[MC]**, with a model
  (`nfn_companion_key_not_fresh` **[MC]**).

**Non-vacuity.**  `VEnv.AddNestedStep`, the premise the rule would take, has models at both
nested witnesses: `ntreeAux_AddNestedStep` and `nfnAux_AddNestedStep` **[MC]**, via
`AddNestedB.toAddNestedStep` **[MC]**.  So the rule would not be vacuous, and the two remaining
theorems are the only thing between it and the tree.

---

## 1. `AddInductStagesR` and its invariant

### 1.1 The definition

```lean
def AddInductStagesR (m₁ : ConstMap) (env₁ : VEnv) (D : VInductDecl')
    (K : List Name) (R : VIndRestore) (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  ∃ mt et mc ec e₃,
    AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) (D.typeConstsC K)      m₁ env₁ mt et ∧
    AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v)   (D.ctorConstsCR R K)   mt et mc ec ∧
    AddIndConsts (fun ci => ∃ v, ci = .recInfo v)    (D.recConstsR R)       mc ec m₂ e₃ ∧
    env₂ = e₃.addIndRulesR D R
```

`K` names the auxiliary members: their type constants and constructors are **not** declared
(`typeConstsC`/`ctorConstsCR` filter them out), but their recursors **are**, under
`R.recName (mkRecName ·)` — which is exactly `mkAuxRecNameMap`'s renaming.  That third stage
is the whole repair.

Proved about it, all **[MC]**: `to_addInductR` (discharges into `VEnv.addInductR` as
`AddInductStages.to_addInduct` discharges into `addInduct'`), `.le`, `.map_wf`, `.find?_shape`,
`.defeqs`, `.find?_of_not_mem`, `.addIndTypesC`.

**Conservativity** **[MC]**: `AddInductStages.toR` and `AddInductStagesR.of_addInductStages` —
at `K = []`, `R = D.idRestore`, `D.Canonical`, the new relation *is* the old one.  So nothing
proved about the non-nested case is given up; this is a generalisation, not a rival.

### 1.2 The names, and why they are a function of the declaration

```lean
def auxRecName (types : List InductiveType) (k : Nat) : Name :=
  Lean4Lean.appendIndexAfter' (Lean.mkRecName (types.headD default).name) (k + 1)

def indDeclNamesN (types : List InductiveType) (numNested : Nat) : List Name :=
  indDeclNames types ++ (List.range numNested).map (auxRecName types)
```

That is `mkAuxRecNameMap` (`Lean4Lean/Inductive/Add.lean:898`) read back **[SRC]**: it renames
`mkRecName indName` to `appendIndexAfter' (mkRecName types[0].name) k` for
`k = 1 … numNested`, over `mainInfo.all.drop types.length`.  `indDeclNamesN_zero` **[MC]** says
the list collapses to `indDeclNames` at `numNested = 0`.

The point of the shape: the extra names depend only on `types` and `numNested`, so the
invariant does not go slack.  §3's negative controls check that.

### 1.3 `TrIndDeclN`: the translation, with the name discipline

`TrIndDecl` (`Verify/Environment/Induct.lean`) with three additions, all of them *name*
discipline — the semantic content stays in `VInductDecl'.WF`:

| clause | content |
|---|---|
| `length` | `D.types.length = types.length + numNested` — the auxiliary members are appended after the user's.  `ElimNestedInductive` **pushes** them onto `newTypes`, which starts as `types.toArray` (`Add.lean:855`, `:933`) **[SRC]**, and check C corroborates **[EV]**. |
| `companions` | `∀ j T, D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j)` — **`K` is exactly the auxiliary tail**.  Left-to-right stops a user member being dropped from the map; right-to-left makes the auxiliary members undeclared. |
| `recName_own` | a member the user wrote keeps its recursor name |
| `recName_aux` | `R.recName (mkRecName T.name) = auxRecName types (j - types.length)` — `mkAuxRecNameMap`, as a clause |

plus `TrIndCtorR`, which compares against `R.ctorName C.name` and against the **restored**
stored type `C.typeR D R j` — the type `Environment.addInductive` actually publishes, after
`restoreNested` rewrote the auxiliary heads back.  `trCtors` is staged over
`env.addIndTypesC D K`, which is exactly the environment `AddInductStagesR`'s first stage
produces.

`TrIndDecl.toN` **[MC]**: at `numNested = 0`, `K = []`, `R = D.idRestore` (and `D.Canonical`),
`TrIndDecl` gives `TrIndDeclN`.  Conservativity on the syntactic side.

### 1.4 The invariant, stated

> **Every constant the step adds to the map is one the translated declaration accounts for.**

Two halves, both **[MC]**:

* `AddInductStagesR.find?_of_not_mem` — outside `D.allNamesCR R K`, `m₂.find? n = m₁.find? n`.
  Inherited from `AddIndConsts.find?_of_not_mem`, which is list-generic.  This is what makes
  the relation a **definition of the output map**, not a check on it.
* `TrIndDeclN.mem_indDeclNamesN` — `D.allNamesCR R K ⊆ indDeclNamesN types numNested`.

Composed: `InductStepNested.find?_of_not_mem`.  `InductStepNested.find?_shape` carries the
safety gate (`AddDeclWF.lean` §1) through unchanged: every constant the step declares is one of
the three inductive shapes and is `safe`-tagged.

---

## 2. `InductStepNested`: the obligation, and two corrections it embodies

```lean
def InductStepNested (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) (numNested : Nat) : Prop :=
  ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore),
    TrIndDeclN venv lp np types false numNested D K R ∧
    (∃ et, venv.addIndTypes D = some et) ∧
    D.WF venv ∧
    AddInductStagesR m venv D K R m' venv'
```

**Correction 1 — it is `WF`, not `WFC`.**  The first draft of this obligation used
`VInductDecl'.WFC venv K` (`Theory/Inductive/CompanionResolve.lean`'s G1 re-staging).  That is
**wrong here** and does not typecheck at the witness.  `D` is the *auxiliary* block, and
`AddInductive.run` checks it in a scratch environment where **all** its type constants,
auxiliary ones included, are declared — which is `WF.ctors`' staging (`env.addIndTypes D`), not
`WFC.ctors`' (`addIndTypesC D K`, where a companion member's own constructor type is not even
well-formed).  `WFC` exists for the *other* companion shape: a block re-declaring a type
already in the environment (`fooCompDecl`).  The nested path never does that — `mkUniqueName`
gives the auxiliary members fresh `_nested.*` names.  This matches `VEnv.AddNestedB`, which
also takes `D.WF env`.

**Correction 2 — the vacuity guard has to be a conjunct.**  `WF.ctors`' premise is
`env.addIndTypes D = some env₁`, which is `none` on a name collision; that is precisely the
mechanism by which `fooComp_WF` holds vacuously and `fooComp_inconsistent` bites.
`AddInductStagesR` does **not** supply it (it only declares the non-companion types — that is
the whole point of `typeConstsC`).  So the success is an explicit conjunct, and
`InductStepNested.ctors_nonvacuous` **[MC]** reads it back as an inhabited obligation.  The
non-nested `InductStepSafe` got this for free from `AddInductStages.addIndTypes`; the nested
one does not, and silently keeping the old shape would have re-opened the `fooComp` hole.

Also **[MC]**: `.le`, `.map_wf`, `.find?_of_not_mem`, `.find?_shape`, `.induct_premises`.

---

## 3. The refutation, re-run

`tBlock_not_addInductStages` (now in `InductR.lean`, text unchanged) says: for
`inductive Box (A : Type) | mk : A → Box A` then `inductive T | mk : Box T → T`, no `D` with
`TrIndDecl … [tIndType] false D` stands in `AddInductStages` between a map without `T.rec_1`
and one with it.  **Still true, still proved.**

Its nested-aware counterpart is `TrIndDeclN.not_addInductStagesR`, with side condition
`n ∉ indDeclNamesN types numNested`.  At the block:

| name | statement | verdict |
|---|---|---|
| `trec1_mem_indDeclNamesN` **[MC]** | `T.rec_1 ∈ indDeclNamesN [tIndType] 1` | **the wall is gone** — the side condition is `False`, so the refutation is inapplicable |
| `tBlock_not_refuted_at_trec1` **[MC]** | the same, packaged with every other hypothesis of the refutation available | there is no derivation of `¬ AddInductStagesR` by this route |
| `trec1_not_mem_indDeclNamesN_zero` **[MC]** | `T.rec_1 ∉ indDeclNamesN [tIndType] 0` | **negative control**: at `numNested = 0` the wall is intact.  The repair is gated on `numNested`, not a blanket permission. |
| `trec2_not_mem_indDeclNamesN` **[MC]** | `T.rec_2 ∉ indDeclNamesN [tIndType] 1` | **negative control**: a *second* auxiliary recursor is still refuted at `numNested = 1` |
| `foo_not_mem_indDeclNamesN` **[MC]** | `Foo ∉ indDeclNamesN [tIndType] n`, for every `n` | **negative control**: the auxiliary family does not leak; the map is still pinned outside the block.  Via `auxRecName_tIndType`, which computes the family to `T.rec_1, T.rec_2, …`. |

And against the checker itself:

* **check C** **[EV]** — the set of constants `addDecl` adds for the `T` block is **exactly**
  `indDeclNamesN [tIndType] 1`.  Measured: `added = [T.mk, T.rec_1, T, T.rec]`,
  `expected = [T, T.mk, T.rec, T.rec_1]`.  Both inclusions are checked, so the name list is a
  *definition* of the added set, not a permissive over-approximation.
* **check C′** **[EV]** — and `indDeclNamesN [tIndType] 0` does **not** cover it, so check C is
  not vacuous and the original finding has not regressed.
* **check D** **[EV]** — the shapes: `T ↦ .inductInfo`, `T.mk ↦ .ctorInfo`,
  `T.rec, T.rec_1 ↦ .recInfo`, all `isUnsafe = false`, all with `all = [T]`.  That is
  `find?_shape` plus the safety gate, at a block with an auxiliary recursor.

---

## 4. Non-vacuity: a closed model at a real nested block

The witness is `Theory/Inductive/NestedBuild.lean` §6's block, which already had the
declaration side and Lean-kernel cross-checks and lacked only the constant map:

```
inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α
inductive NFn            | node : PFn NFn → NFn
```

with `nfnAux`/`nfnK`/`nfnRestore` the auxiliary block, restoration and companion list, and
`nfnAux_WF` already proved (in *any* environment, with `binders_indep` discharged by the
substitution theorem rather than by emptiness).

The three constant lists, by `rfl` **[MC]** — read them:

```lean
nfnAux.typeConstsC nfnK          = [(NFn,      ⟨0, Sort 1⟩)]
nfnAux.ctorConstsCR nfnRestore nfnK = [(NFn.node, ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)]
nfnAux.recConstsR nfnRestore     = [(NFn.rec,   ⟨1, recTypeR … 0⟩),
                                    (NFn.rec_1, ⟨1, recTypeR … 1⟩)]
```

One type constant, one constructor constant — the companion `_nested.PFn_1` and its
constructor `_nested.PFn_1.mk` are declared nowhere — and **two** recursors, the second
renamed.  That is the finding, accommodated.

| name | content |
|---|---|
| `tr_nodeType`, `tr_recType0`, `tr_recType1` **[MC]** | Lean's **stored** types for `NFn.node`, `NFn.rec` and `NFn.rec_1` translate (`TrExprS`) to `typeR`/`recTypeR … 0`/`recTypeR … 1`.  The `Expr` side is spliced from the kernel by `exprOf%` — the `Expr`-side counterpart of `Theory/Meta.lean`'s `vconst(type_of% …)` — so it cannot drift from a hand transcription. |
| `trIndDeclN_wit` **[MC]** | the syntactic half, including `recName_aux`: `nfnRestore.recName (mkRecName _nested.PFn_1) = auxRecName [nfnIndType] 0 = NFn.rec_1` |
| `addInductStagesR_wit` **[MC]** | all four stages fire; the output map holds `.recInfo` at `NFn.rec` **and at `NFn.rec_1`**, and holds **nothing** at `_nested.PFn_1` |
| `inductStepNested_wit` **[MC]** | the join: `TrIndDeclN` ∧ `addIndTypes` success ∧ `nfnAux_WF` ∧ `AddInductStagesR`, at one block |
| `inductStepNested_wit_closed` **[MC]** | the same with **no hypotheses on the environment** beyond the declaration history (`VEnv.empty.addInduct' pfnDecl = some env₂`) and any well-formed empty constant map — the freshness side conditions are discharged, not assumed |

So all three conjuncts of `InductStepNested` meet at one nested block, with `NFn.rec_1` in the
output map, and the `WF` conjunct is a real obligation rather than an `absurd`.

---

## 5. The blocker, restated — and it is **not** the declaration history

The previous revision said: *`VDecl.WF.induct`'s hypothesis is `env.addInduct' decl = some
env'`; a nested step gives `addInductR`; the generalisation must be `VEnv.AddNestedB`, which
needs `ds`, which `VDecl.WF` does not carry; that is a design change in another stream's file.*

The first two clauses are still true.  **The rest was wrong or incomplete**, and this is the
correction.

### 5.1 What is now done (owned, green)

| item | status |
|---|---|
| `ds` in `Faithful`/`Occurs`/`Built`/`AddNested`/`AddNestedB` | **gone**, replaced by `VInductDecl'.Declared` **[MC]** |
| a history discharges `Declared` | `VEnv.WF'.declared` **[MC]** |
| `addInductR`/`Faithful` nameable at `Env.lean` | **yes** — moved to `Theory/Inductive/Restore.lean`; `example` in `Env.lean` **[MC]** |
| `npJ` free ⇒ under-constrained | **closed**: `ctors_complete` pins `npJ j = D₀.np` **[MC]** |
| the rule's premise is inhabited | `ntreeAux_AddNestedStep`, `nfnAux_AddNestedStep` **[MC]** |
| conservativity at `K = []` | `VEnv.AddNested_nil` (unchanged), `addInductR_ordered_nil` **[MC]** |

The rule, in full, as it would be added to `VDecl.WF` (the text also sits in `Env.lean`'s
section docstring, where it is next to the two reasons it is not there):

```lean
  | inductNested {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore} :
    VEnv.AddNestedStep env D K R env' →
    VDecl.WF env (.induct D) env'
```

### 5.2 Obstruction 1 — `VEnv.addInductR_ordered`, a theorem nobody had named

`VEnv.WF.ordered` (`Theory/Typing/EnvLemmas.lean`) extracts `Ordered` from `VEnv.WF`, and its
`induct` arm is `addInduct_WF`, i.e. `addInduct'_ordered_final`.  The nested arm needs

    env.Ordered → env.addInductR D K R = some env' → env'.Ordered

and that is **not bookkeeping**.  `Ordered` (`Theory/Typing/Lemmas.lean`) records that every
constant's type was `IsType` at its staging environment and every `defeq` was `WF` when added.
`addInductR` declares a user constructor at `C.typeR D R j` — in which a field the auxiliary
block stored as `_nested.List_1 α` has been rewritten back to `List (Tree α)` — and the
recursors at `D.recTypeR R j`, and emits `D.iotaRulesR R`.  None of that follows from
`D.WF env`, which is about the *auxiliary* block's own stored types.  **This is the nested
soundness theorem**, and it is what actually stands between here and the rule.

`Theory/Inductive/NestedOrdered.lean` does the part that is bookkeeping and names the rest:

* `VEnv.addInductR_stages` **[MC]** — the three constant stages and the rule fold, the
  `addInduct'_stages` analogue (`allConstsCR` is a *left*-associated append of three).
* `VEnv.addInductR_ordered` **[MC]** — `Ordered env'` from four staged obligations, in
  `addInduct'_ordered`'s shape.
* `VEnv.addInductR_typeConstsC_wf` **[MC]** — the first of the four is **free**: `typeConstsC`
  only *removes* members, so the type constants' stored types are covered by `D.WF env`
  verbatim.
* `VEnv.addInductR_ordered'` **[MC]** — hence `Ordered` from exactly **three** obligations:
  **(A)** a declared constructor's *restored* stored type is a type at the environment holding
  the step's type constants; **(B)** each *renamed* recursor's *restored* type is a type at the
  environment holding those and the constructors; **(C)** each *restored* ι-rule is a
  well-formed `VDefEq` there.  They are to be discharged from `Faithful` + `D.WF env`.
* `VEnv.addInductR_ordered_nil` **[MC]** — at `K = []`, `R = idRestore`, `D.Canonical` the three
  collapse to what `addInduct'` already discharges.  So they are about the *restoration*, not
  about inductives, and nothing has been strengthened.

### 5.3 Obstruction 2 — `DeltaUnique`'s freshness argument is **false** for a nested block

`Theory/Typing/DeltaUnique.lean`'s `keys_induct` (the `induct` arm of `VEnv.WF'.keys`) turns on

> `hfresh` — every name in the key of a rule the step emits is absent from `env`.

For `addInduct'` that is immediate: a key is `[I_j.rec, C.name]` and the step declares both.
For a nested step the key of a **companion** member's ι-rule is
`[R.recName I_j.rec, R.ctorName C.name]` (`VInductDecl'.key_iotaRuleR`), and the second
component is the constructor of the block the environment **already holds**.
`VIndRestore.Faithful.ctor_agree` says so in as many words:

* `VEnv.iotaRulesR_major_not_fresh` **[MC]** — under `Faithful`, a companion ι-rule's major
  name is `env.contains`.
* `VEnv.mem_key_iotaRuleR_major` **[MC]** — and it really is in the key.
* `InductiveDeclExamples.nfn_companion_key_not_fresh` **[MC]** — the model: `nfnAux`'s
  companion rule is keyed `[NFn.rec_1, PFn.mk]`, and `env₂` holds `PFn.mk`.

The freshness that *is* available is of the key's **head** (`recName_mem_allNamesCR` puts the
renamed recursor among the step's own constants, and `addConstList` succeeded), so the nested
arm is a different argument, not a transcription.  Whether `KeyMajorUnique`/`KeyHeadDelta`
survive it is **not settled here** and is the next thing to check on that side.

### 5.4 Obstruction 3 — four one-line case additions in two unowned files

Measured, not guessed: a clone constructor was added to `VDecl.WF`, the tree built, every
`Alternative \`inductNested\` has not been provided` collected, patched, rebuilt, until
`Lean4Lean.Theory` (96 modules) and `Verify.{Soundness,SafeFragment,Bridge}` were green again.
The **complete** list is nine sites in five files:

| file | sites | owned? | what the nested case needs |
|---|---|---|---|
| `Theory/Typing/EnvLemmas.lean` | 1 (`VEnv.WF.ordered`) | **yes** | `addInductR_ordered` — §5.2 |
| `Theory/Typing/DeclRules.lean` | 1 (`WF'.defeq_isDeclRule`) | **yes** | `addInductR_defeqs_iff` + `IsDeclRule` for `iotaRulesR` |
| `Theory/Inductive/Nested.lean` | 5 (`VDecl.WF.le`, `WF'.exists_addInduct'`, `WF'.induct_eq_of_type_name` ×2, `WF'.iotaRule_provenance`) | **yes** | `addInductR_le` (exists); the rest are about `addInduct'`-provenance and need restating |
| `Theory/Typing/DeltaUnique.lean` | 3 (`WF'.defEqHeads`, `WF'.keys`, `WF'.iotaTypes`) | **no** | §5.3 |
| `Theory/Typing/PatternRules.lean` | 1 (`WF'.ruleShape`) | **no** | `ruleShape_inductR` |

Nothing in `Verify/` case-splits on `VDecl.WF`; `Verify.Soundness` built green throughout the
probe.  The probe was then **fully reverted** (`git checkout`), including the two unowned
files.

So the ask on the unowned side is four `| inductNested … =>` arms — but they are *not* one-line
until §5.2 and §5.3 are done, which is why the rule is not added.

---

## 6. The flip: current file set, and why it still cannot land

**Verdict: unchanged — not landable, and it is now clear that it is not landable for a second,
independent reason.**

| # | file | owned? | what the flip does to it |
|---|---|---|---|
| 1 | `Verify/Environment/Basic.lean` | **yes** | `inductive AddInduct` → `def AddInduct := ∃ K R, AddInductStagesR …`; `to_addInduct`; the `induct` arms of `TrEnv'.wf`/`.wf_noUnsafe` |
| 2 | `Verify/Environment/Lemmas.lean` | **yes** | `Aligned.addInduct`'s `nomatch H`; `TrEnv'.of_value`'s induct arm |
| 3 | `Theory/Typing/Env.lean` | **yes** (this round) | the `inductNested` rule — blocked by §5.2/§5.3, **not** by ownership |
| 4 | `Verify/SafeFragment.lean` | no | `AddInduct.le`'s `nomatch H` → `AddInductStagesR.le` (one line) |
| 5 | `Verify/Environment/Extension.lean` | **yes** | delete `TrEnv'.no_inductInfo` (becomes false) |
| 6 | `Verify/TypeChecker/Reduce.lean` | no | shape lemmas gain disjuncts; four deletions; two delete-or-`sorry` |
| 7 | `Verify/TypeChecker/WHNF.lean` | no | `inductiveReduceRec_eq_none` dies |
| 8 | `Verify/TypeChecker/InferType.lean` | no | `inferProj_always_throws` dies |
| 9 | `Verify/TypeChecker/IsDefEq.lean` | no | `tryEtaStructCore_never_true`, `isDefEqUnitLike_never_true` die |

**Rows 6–9 are the human's standing ruling** (those nine statements stay as theorems), and they
are proved *by the emptiness of `AddInduct`*.  Giving `AddInduct` constructors makes them
false and their files red, and this stream neither owns them nor may take that decision.  So
the flip is gated on a decision, not only on proofs — and independently on §5.2/§5.3, which
gate row 3.  **The order is: (i) `addInductR_ordered`; (ii) the `DeltaUnique` repair; (iii)
row 3 plus the nine case arms of §5.4, as one commit; (iv) bring rows 6–9 to the human.**

---

## 7. Ledger of edits to owned files

| file | change |
|---|---|
| `Theory/Inductive/Restore.lean` | **new**, 360 lines, 39 declarations.  `VIndRestore`, `idRestore`, `tyAppR`/`tyAppR'`/`ctorAppR`, all of Part 2's restored recursor construction, `iotaRulesR`, `recConstsR`, `ctorConstsCR`, `allConstsCR`, `addIndRulesR`, `addInductR`, `instAt`, `Faithful`, `AddNested`, **moved verbatim** from `NestedHead.lean`; `tyAppH` + its two conservativity lemmas from `CompanionResolve.lean`; `typeConstsC` from `Companion.lean`.  New: `VEnv.AddNestedStep`, and the `npJ j = D₀.np` clause in `Faithful.ctors_complete` |
| `Theory/Inductive/NestedOrdered.lean` | **new**, 179 lines, 9 declarations: §5.2's factoring and §5.3's refutation |
| `Theory/Inductive/Decl.lean` | received `VInductDecl'.Declared`, `.mono` |
| `Theory/Inductive/Lemmas.lean` | received `Declared.constants_type`, `.constants_ctor`, `.allNames_nodup` |
| `Theory/Inductive/Nested.lean` | received `VEnv.WF'.declared` |
| `Theory/Inductive/NestedHead.lean` | the moved declarations removed (a pointer note in their place); `Faithful` lost `ds`, gained the `npJ` clause; `AddNested`/`AddNested_nil`/`AddNested_keys_declared` lost `ds`; `ntreeRestore_faithful` re-proved through `Declared` |
| `Theory/Inductive/NestedBuild.lean` | `Occurs`/`Built`/`AddNestedB` lost `ds`; `Occurs.hist` is now `Declared`; `Built.toFaithful` discharges the `npJ` clause by `rfl`; received `AddNestedB.toAddNestedStep`, `ntreeAux_AddNestedStep`, `nfnAux_AddNestedStep`, `nfn_companion_key_not_fresh` |
| `Theory/Inductive/{Companion,CompanionResolve}.lean` | `typeConstsC` / `tyAppH`+2 removed (moved, with a pointer note); nothing else |
| `Theory/Typing/Env.lean` | imports `Theory.Inductive.Restore`; new section docstring carrying the `inductNested` rule text and the two reasons it is not added; the `example` that machine-checks nameability.  **The inductive itself is unchanged.** |
| `Verify/Environment/{Basic,InductR}.lean` | docstring corrections only: both said the blocker is the declaration history and that it was the *only* one |

No unowned file was edited.  The `VDecl.WF` probe of §5.4 was reverted in full.

---

## 8. Carried forward from the previous revision, still true

* **The `sorry` inventory.** **20** tree-wide, unchanged this round.  The five tainted declarations in
  `Verify/Inductive/Add.lean` (`AddInductive.M.WF.{ensureType,whnf,field_step,elim_field_step,positivity_none}`)
  are tainted *by inheritance* through `Verify/TypeChecker/{InferType,IsDefEq,WHNF}.lean`.
  Nothing in this stream's files adds taint.
* **`addDecl.WF`'s `inductDecl` branch is false, not open.**  `addDecl_inductDecl_post_false`,
  `addDecl_inductDecl_WF_false` **[MC]**, check A **[EV]**.  Unchanged.
* **The `.unsafe` hole.**  `unsafe_induct_unreachable` **[MC]**: `TrEnv' .unsafe` has no rule
  at all for an unsafe inductive, and the flip does not close it.  Independent of everything
  above; still needs a design decision between a `TrEnv'` rule that is the inductive analogue
  of `unsafeDef`, and a `VEnvs.WF` that does not demand a model at `.unsafe`.
* **`Aligned.addInduct`'s statement**, corrected in a previous round (named environments, not
  auto-bound implicits), is unchanged and is what the flip's arm must be proved against.
* **`addDecl.WF` is still false at `inductDecl`.**  It is one of the 20, and closing it
  honestly was contingent on the flip landing.  It did not.  `Verify/Inductive/AddDeclWF.lean`'s
  drafted replacement obligation is untouched.
* **Not proved, and not attempted this round:** the flip; `AddInductiveObligation` /
  its nested counterpart as a refinement of `Environment.addInductive` (nothing in `Verify/`
  refines the top-level wrapper yet, which is why §3's checker-side facts are `[EV]`); the
  `.unsafe` rule; the nine `Verify/TypeChecker/` declarations; `Theory/Typing/Env.lean` (§5).

</details>
