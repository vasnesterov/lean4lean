# Handoff: the nested flip's per-field datum (`hfld`) — collapse confirmed, then reduced

**Owner files:** `Lean4Lean/Verify/Inductive/FldDischarge.lean` (new, mine) and this file.
**Written incrementally from minute one**, per the standing rule.

## 0. Pre-flight — every name the brief names, against the compiled environment

`scripts/exists.lean`, population **428** built modules.

| name | module | arity | cone | own hole | reaches `sorryAx` |
|---|---|---|---|---|---|
| `VIndRestore.csubst_hbridgeD` | `Verify.Inductive.WholeTypeBridge` | 24 | 2468 | false | **false** |
| `VIndRestore.csubst_hbridgeD_iff` | `Verify.Inductive.WholeTypeBridge` | 17 | 2433 | false | **false** |
| `VEnv.ctorConstsCR_wf_of_fieldsD` | `Theory.Inductive.CtorBeta` | 15 | 2529 | false | **false** |
| `VEnv.ctorConstsCR_wf_of_betaD` | `Theory.Inductive.CtorBeta` | 22 | 2973 | false | **false** |
| `VIndRestore.field_defeq_of_canonical` | `Theory.Inductive.CtorBeta` | 19 | 1822 | false | **false** |
| `VIndRestore.head_defeq_of_beta` | `Theory.Inductive.CtorBeta` | 28 | 2332 | false | **false** |
| `VIndRestore.ctorFieldEntry_onCtx` | `Theory.Inductive.CtorBeta` | 15 | 2254 | false | **false** |
| `VIndRestore.substC_tyApp_defeq_tyAppR_comp` | `Theory.Inductive.NestedRules` | 24 | 2325 | false | **false** |
| `VIndCtor.WF.hasArgs_params_bvars_of_wf` | `Theory.Inductive.TeleMove2` | 16 | 2408 | false | **false** |
| `VIndRestore.recTypeBridge_of_blocks` | `Verify.Inductive.WholeTypeBridge` | 11 | 2366 | false | **false** |
| `VEnv.recConstsR_wf_of_blocks` | `Theory.Inductive.NestedTele` | 13 | 2371 | false | **false** |
| `InductiveDeclExamples.ntreeAux` | `Theory.Inductive.NestedHead` | 0 | 43 | false | **false** |
| `InductiveDeclExamples.ntreeAux_wholeTypeBridge_witness` | `Verify.Inductive.WholeTypeBridge` | 0 | 3659 | false | **false** |
| `VEnv.IsDefEq.uniq` | `Theory.Typing.UniqueTyping` | 12 | 3472 | false | **TRUE** (`VEnv.IsDefEqU.forallE_inv_stratified`) |
| `VEnv.AxiomConservativityWF` | `Theory.Typing.ConstVar` | 2 | 362 | false | false |
| `VEnv.HasArgs.of_mkApp` | `Theory.Typing.SpineInv` | 13 | 3620 | false | **TRUE** (`forallE_inv_stratified`, `WF.rigidShapeUniqNS`) |

No false absence.  The brief's forbidden name is `Lean4Lean.VEnv.HasArgs.of_mkApp` (the brief wrote
it without the `VEnv.`); it is confirmed holed **twice over** and is not used here.

### 0a. Is `hfld` already refuted?  No — and it is exhibited satisfied.

`scripts/shape.lean` with
`HEADS="Lean4Lean.VIndRestore.restore Lean4Lean.VEnv.IsDefEq Lean4Lean.VExpr.NoConsts"` → **8 hits,
0 structure fields**.  All eight either *consume* the datum
(`ctorConstsCR_wf_of_fieldsD`, `csubst_hbridgeD`, `substC_ctorType_bridge{,'}`,
`ctorTypeBridge_of_entries`, `field_defeq_of_canonical`) or are the field-telescope lemmas that
package it (`substC_fieldTypes_defeq_of_noK`, `substC_atRec_fieldTypes_defeq_of_noK`).  **Nothing
produces it and nothing refutes it.**  It is exhibited *satisfied* at a parameterised nested block by
`InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_fieldsD`, so the reduction below is not about a
false statement.

Note the substitution: `hfld` is stated at `R.csubstTy D K`, the type-constants-only substitution.
The thing `ConstSubstNested.lean` §B/§D.2 **refutes** at parameterised blocks is `(R.csubst D K).WF`'s
strict `const` clause, a different substitution and a different clause.

## 1. The collapse (brief item (a), first half): **it holds**, and it is machine-checked

`VIndRestore.FldD R D K e₁` (a `def`) is the datum, written once.  Then

* `VEnv.ctorConstsCR_wf_of_fldD` — `FldD` fed to `VEnv.ctorConstsCR_wf_of_fieldsD`'s `hfld`;
* `VIndRestore.csubst_hbridgeD_of_fldD` — the **same** `FldD` fed to
  `VIndRestore.csubst_hbridgeD`'s `hfld`.

Both elaborate with the hypothesis passed through bare — no `fun … => …` repackaging, no `simpa`, no
coercion.  That is the collapse: had the two propositions differed in any binder, in either context
list, or in which `CSubst` they name, one of the two applications would have failed.  So the flip's
leaves (1) and (2) of the brief are **one leaf**, and prose is no longer what says so.

## 2. The reduction chain (brief item (a), second half)

`hfld` is **not discharged** — it cannot be, and §2.4 says why in one sentence.  What it is reduced
to, in general and with no bound on `D.np`:

```
BetaD  --§D-->  FldHead  --§C-->  FldK  <--§B (an ↔)-->  FldD  --§A-->  hbridgeD
                                                              --§A--> (A)'s conclusion
```

### 2.1 §B: the own-pointing fields are free, and that is an `↔`

`CtorBeta` §3's `hfld` charges every recursive field whose stored type names a companion constant
*anywhere* — including fields whose `recArg.idx` points back at the block's **own** member, which
happens when a *binder* or an *index argument* names a companion while the head does not (and is the
shape of the β-redex fields `ElimNestedInductive` manufactures).

* `VIndRestore.FldK` — `FldD` charged only where `D.types[r.idx]?`'s member is **in** `K`.
* `VIndRestore.fldK_of_fldD` — forward, free (quantifier restriction).
* `VIndRestore.fldD_of_fldK` — backward, the direction with content: `head_defeq_of_own` makes the two
  sides of an own-pointing field's datum the *same expression*, and `ctorFieldEntry_onCtx` types it
  off the source constructor's own well-formedness.
* **`VIndRestore.fldD_iff_fldK`** — the `↔`.  So a successor that reduces the flip to `FldK` has
  weakened nothing, and one that re-derives `FldD` from scratch is doing strictly more than the
  problem requires.

`VInductDecl'.CanFld` is the syntactic side condition both directions need — the canonicity half of
`ctorConstsCR_wf_of_betaD`'s `hcan`, with the `∀ a ∈ r.args, a.NoCSubst …` conjunct split off into
`VIndRestore.ArgsNoC` (§D needs it; §B and §C do not, and carrying it would make the `↔` hold under a
strictly stronger hypothesis than it needs).  **`CanFld` does not mention `R`** — the unused-variable
linter said so before the docstring did — so the canonicity half of `hcan` is a property of the
*declaration*, dischargeable once per block with no reference to the restoration.

### 2.2 §C: `FldK` from the head defeq alone — and why this one is *not* an `↔`

`VIndRestore.FldHead` is the same datum with the field's binder telescope stripped: one defeq at the
**head**, `D.tyApp r.idx k r.args` against `D.tyAppR R r.idx k r.args`, both under `substC`.
`VIndRestore.fldK_of_fldHead` is one `mkPi` congruence per charged field (`field_defeq_of_canonical`),
with the `OnCtx` free.

**Why an implication and not an `↔`, and it is recorded at the statement itself.**  The converse —
recovering the head defeq from the whole-`mkPi` defeq over an *identical* telescope — is Π-injectivity
for `IsDefEq`, `VEnv.IsDefEqU.forallE_inv` / `VEnv.PiInv`, whose only proof in the tree is
`VEnv.IsDefEqU.forallE_inv_stratified`: **one of the thirteen holes**, and the one that taints
`VEnv.IsDefEq.uniq` (pre-flight, cone 3472).  So §C is stated as sufficiency, deliberately, and §B is
where the equivalence lives.

### 2.3 §D: `hbridgeD` from `NestedRules` §8.8's β data — a route that did not exist

`VIndRestore.BetaD` is `VEnv.ctorConstsCR_wf_of_betaD`'s `hbeta` verbatim (four typed components and
one syntactic one; `hbv` is absent because `TeleMove2` §3 makes it a theorem).

* `VIndRestore.fldHead_of_betaD` — `FldHead` from `BetaD`, per charged companion-pointing field, via
  `CtorBeta` §6b `head_defeq_of_beta` ∘ `NestedRules` §8.8, with `hbv` discharged inside from
  `VIndCtor.WF.hasArgs_params_bvars_of_wf`.
* `VIndRestore.fldD_of_betaD` — the composition through §C and §B.
* **`VIndRestore.csubst_hbridgeD_of_betaD`** — `ValRestGeneral` §6's `hbridgeD`, free `U`/`Γ`/`ls`,
  from `BetaD` alone.

**This last one is the new reachability fact, not a repackaging.**  `CtorBeta` §7 stops at
`∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2`; `csubst_hbridgeD` consumes `FldD`, which §7 *eats* and
does not emit.  So before §D there was **no general route from §8.8's β data to `hbridgeD`** — the only
way to it was a hand-built `FldD`, block by block, which is exactly what
`InductiveDeclExamples.ntree_hbridgeD` and `ntreeAux_wholeTypeBridge_witness` do.

### 2.4 …and `BetaD` is where it stops, for a reason already proved in the tree

`BetaD`'s substantive component is `hbody`: `e₁.HasType D.uvars (D.params.reverse ++ Δ) (R.tyBody D r.idx) B`.
That is a typing of the *restored* head's body in the *target* environment, i.e. §8.7's `hargs`, i.e.
the `val` clause of `(R.csubst D K).WF`.  `VIndRestore.instAt_indep_of_tyArgs`
(`NestedRules.lean` §8.7) proves that **no restoration-independent argument can produce it**: `instAt`
does not read the presented spine when the split body is closed, so `Faithful`'s `ty_agree` takes the
same value for every spine including untypeable ones.  So `BetaD` is data, and the honest statement of
this round's result is:

> **`hfld` reduces to `BetaD` (§8.8's four components at the companion-pointing canonical fields), the
> reduction is `↔` at the step where an equivalence is available (§B) and sufficiency where the
> converse is a hole (§C), and `BetaD` is not producible because `instAt_indep_of_tyArgs` shows the
> restoration data does not determine it.**

That is the same `hargs` obligations (B) and (C) bottom out in (`CtorBeta` §6b/§7, `HargsShared`), so
the flip's per-field leaf is now *provably* the shared one rather than reportedly so.

## 3. Item (c): the arity-0 witness — `InductiveDeclExamples.ntreeAux_fldDischarge_witness`

**Arity 0, cone 3932.**  At `ntreeAux` (`uvars = 1`, `params = [.sort (.succ (.param 0))]`,
`recUvars = 2`, `np = 1`), existentially closed over the three staging environments
(`addInduct' listDecl`, `addIndTypes ntreeAux`, `addConstList (typeConstsC ntreeK)`).  It exhibits, at
one block simultaneously: `BetaD`, `FldHead`, `FldK`, `FldD`, §B's `↔` between the last two,
`hbridgeD` at every `U`, and the mixed instance `csubst_WFD` consumes
(`U = recUvars = 2` with `ls.length = uvars = 1`).

**The value is the route.**  `ntreeAux_wholeTypeBridge_witness` (arity 0, cone 3659) supplies `FldD` by
hand — one inline `VEnv.IsDefEq.beta` — and then runs §A ∘ §B ∘ §C of `WholeTypeBridge`.  This witness
has **no inline `.beta` at all**: it supplies `BetaD` and reaches `FldD` through `fldD_of_betaD`, so the
β arithmetic is performed by `NestedRules` §8.8's general theorem with `hbv` discharged by
`TeleMove2` §3.  The cone is *larger* than 3659 for exactly that reason — it drags in the general β
machinery instead of a one-line primitive.

Not `nfnAux`: `uvars = 0` would make the level instantiation invisible, `params = []` would empty the
parameter telescope, and `np = 0` would make the β-step §D routes through trivial.  All three of
`ntreeAux`'s numbers are positive/non-degenerate and `InductiveDeclExamples.ntreeAux_uvars_pos`,
`ntreeAux_recUvars_ne_uvars` (`WholeTypeBridge` §F) record two of them as theorems.

Anti-vacuity: the charged field is real —
`InductiveDeclExamples.ntree_fld_premise_fires` (`CtorBeta` §4) shows `ntreeNode`'s second field's
stored type names the companion `_nested.List_1`, and `ntree_field0_free` shows field 0 is not charged.
`ntreeAux_canFld` / `ntreeAux_argsNoC` (both arity 0) discharge §D's two syntactic side conditions at
this block.

## 4. Measurements — `scripts/exists.lean`, population **430** built modules

All 19 declarations: **own value is not a hole; cone does not reach `sorryAx`.**

| name | arity | cone |
|---|---|---|
| `VIndRestore.FldD` (def) | 4 | 890 |
| `VIndRestore.FldK` (def) | 4 | 891 |
| `VIndRestore.FldHead` (def) | 4 | 837 |
| `VIndRestore.BetaD` (def) | 4 | 838 |
| `VIndRestore.ArgsNoC` (def) | 3 | 771 |
| `VInductDecl'.CanFld` (def) | 2 | 619 |
| `VEnv.ctorConstsCR_wf_of_fldD` | 15 | 2531 |
| `VIndRestore.csubst_hbridgeD_of_fldD` | 24 | 2470 |
| `VIndRestore.fldK_of_fldD` | 5 | 893 |
| `VIndRestore.fldD_of_fldK` | 15 | 2559 |
| **`VIndRestore.fldD_iff_fldK`** | 14 | **2561** |
| `VIndRestore.fldK_of_fldHead` | 15 | 2558 |
| `VIndRestore.fldD_of_fldHead` | 15 | 2562 |
| `VIndRestore.fldHead_of_betaD` | 18 | 2621 |
| `VIndRestore.fldD_of_betaD` | 21 | 2931 |
| **`VIndRestore.csubst_hbridgeD_of_betaD`** | 32 | **2955** |
| `InductiveDeclExamples.ntreeAux_canFld` | 0 | 884 |
| `InductiveDeclExamples.ntreeAux_argsNoC` | 0 | 882 |
| **`InductiveDeclExamples.ntreeAux_fldDischarge_witness`** | **0** | **3932** |

**Axiom bar `after ⊆ before`: met.**  `propext`, `Quot.sound`, `Classical.choice` — the last only where
the cone passes through `CtorBeta`'s / `csubst_WF_const`'s own, which already carried it.  Nothing new
relative to `WholeTypeBridge.lean`.  `fldK_of_fldD` and the two `ntreeAux` side conditions carry only
`propext`/`Quot.sound`.

**Zero warnings**: `lake env lean Lean4Lean/Verify/Inductive/FldDischarge.lean` prints only the
`#print axioms` lines.

## 5. Brief items (2) and (3)

### 5.1 Item (2): `hM`/`hQ` reduced to the entrywise data §T5/§T6 actually deliver (§F)

`WholeTypeBridge` §D's `recTypeBridge_of_blocks` takes `hM`/`hQ` as **block-level** `TeleDefEq`s,
because that is how `VEnv.recConstsR_wf_of_blocks` states them.  The producers — `NestedTele.lean`
§T5 `substC_motiveType_defeq'` and §T6 `substC_minorType_defeq` — deliver **one entry at a time**, and
the entrywise-to-block step exists in the tree only in a *fused* form:
`VInductDecl'.recTypeTele_teleDefEq` builds the single appended telescope
`atRecTele params ++ motives ++ minors ++ Is`, from which neither `hM` nor `hQ` can be recovered.

* `VInductDecl'.motives_teleDefEq_of_entries` (arity 5, cone 841) — `hM` from `hmot`.
* `VInductDecl'.minors_teleDefEq_of_entries` (arity 5, cone 1029) — `hQ` from `hmin`.
* `VIndRestore.recTypeBridge_of_entries` (arity 11, cone **2400**) — `RecTypeBridge` from
  `hmot`/`hmin`/`hbody`.

**Not discharged, and honestly so.**  `hmot`/`hmin` remain data; §T5's and §T6's producers are gated on
`hK : T.name ∈ K` (companion entries only) and `NestedTele.lean` records two vacuity facts about their
neighbourhood that a successor must keep in view: §T4 (`substC_motiveType_defeq` is vacuous exactly
above `D.np = 0` — hence the primed version) and the `Γ = []` emptiness of `substC_minorType_defeq`'s
`hfun`.  What §F changes is only that the bridge is now reachable from the *shape the producers emit*.

### 5.2 Item (3): §E's `hnoc` in general (§G) — **discharged**, to syntax

`WholeTypeBridge` §6 note 3 asked for "`substC_tyAppR_free`-style `NoCSubst` facts on `C.params`,
`C.fieldTypesR` and `C.args`".  That is exactly what suffices, and it is now proved.

`VIndCtor.typeR C D R j = mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)`,
so the σ-identity is: both telescope blocks are `σ`-invariant, and the restored head is.  The head
needed `substC_tyAppR_free` at a **general** `σ`; the general form of its two hypotheses is
`VIndRestore.SubstFree` (`NestedRules.lean` §7.4), whose `tyName`/`tyArgs` clauses *are* `hnn`/`hna`.

* `VIndRestore.substC_tyAppR_of_substFree` (arity 7, cone 681) — the unprimed twin of §7.4's
  `substC_tyAppR'`.
* `VIndRestore.substC_typeR_eq_of_noCSubst` (arity 9, cone 931) — §E's `hnoc` at one constructor.
* `VIndRestore.ctorTypeBridge_hnoc_of_noCSubst` (arity 11, cone 967) — the whole `hnoc` family.
* `VIndRestore.ctorTypeBridge_of_entries_noCSubst` (arity 16, cone **2506**) — `CtorTypeBridge` with
  §E's σ-identity gone, so the only per-block data left there are `hfld` at the companions and the
  **live** result-head defeq.

So of the brief's leaf (3), the **`hnoc` half is closed in general** (down to three decidable syntactic
families) and the **result-head half is not** — and `WholeTypeBridge` §E already explains at its own
statement why the result datum cannot be made free the way §B's is (`ctorResult_defeq` needs
`T.name ∉ K`; at a companion the head genuinely moves).

Non-vacuity, per "instantiate, don't admire" (§H):

* `InductiveDeclExamples.ntreeAux_typeR_noCSubst_data` (arity 6, cone 1000) — the three families at
  `ntreeAux`'s two companion constructors, by `decide` each.
* `InductiveDeclExamples.ntreeAux_typeR_noCSubst_general` (arity 6, cone 1090) — the *same statement* as
  the existing `ntree_typeR_noCSubst` (`WholeTypeBridge` §F.1, a bare `decide` on the whole equation),
  obtained through §G's general theorem instead.  Different value, and the value is the point.

## 6. Item (d): which of the thirteen holes this routes through — **NONE**

Measured per declaration with `scripts/exists.lean`, not asserted: all 28 declarations report
`cone reaches sorryAx: false`.

Three were specifically at risk and are recorded **at the statements themselves**:

* **`VEnv.IsDefEqU.forallE_inv_stratified`** (pre-flight: `own value is a hole: TRUE`, cone 48) — the
  natural route to a converse for §C.  §C is therefore stated as an implication, and its docstring says
  so and says why.  `VEnv.PiInv` (cone 31, no proof term) is its type-level twin and is not used.
* **`VEnv.IsDefEq.uniq`** (cone 3472, tainted via `forallE_inv_stratified`) — would be the route to
  reading §B's or §C's converse off two typings.  Not entered; §B's converse is
  `head_defeq_of_own` + `ctorFieldEntry_onCtx`, both syntactic-plus-source-typing.
* **`VEnv.HasArgs.of_mkApp`** — the brief forbade it (writing it without its `VEnv.` prefix).
  Pre-flight confirms it is tainted **twice** (`forallE_inv_stratified` and `WF.rigidShapeUniqNS`).
  Not used; grep-checked in the owner file.  `VEnv.AxiomConservativityWF` and the restriction cycle are
  absent — nothing here enters `RestrictStep`.

## 7. Measurements, part 2 — population **431** built modules

| name | arity | cone |
|---|---|---|
| `VInductDecl'.motives_teleDefEq_of_entries` | 5 | 841 |
| `VInductDecl'.minors_teleDefEq_of_entries` | 5 | 1029 |
| **`VIndRestore.recTypeBridge_of_entries`** | 11 | **2400** |
| `VIndRestore.substC_tyAppR_of_substFree` | 7 | 681 |
| `VIndRestore.substC_typeR_eq_of_noCSubst` | 9 | 931 |
| `VIndRestore.ctorTypeBridge_hnoc_of_noCSubst` | 11 | 967 |
| **`VIndRestore.ctorTypeBridge_of_entries_noCSubst`** | 16 | **2506** |
| `InductiveDeclExamples.ntreeAux_typeR_noCSubst_data` | 6 | 1000 |
| `InductiveDeclExamples.ntreeAux_typeR_noCSubst_general` | 6 | 1090 |

All hole-free.  Axioms: `propext`/`Quot.sound` only, except
`ctorTypeBridge_of_entries_noCSubst` which inherits `Classical.choice` from
`ctorTypeBridge_of_entries`' own cone.

## 8. What remains of the nested flip after this round

1. **`BetaD`** — `§8.8`'s four components at the companion-pointing canonical recursive fields.  This is
   now the *whole* of the flip's per-field leaf, `hbridgeD` included, and it is **not producible from the
   restoration data**: `VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean` §8.7, cone 652,
   hole-free) shows `instAt` does not read the presented spine when the split body is closed, so
   `Faithful`'s equations hold for untypeable spines too.  It is data, and it is the same `hargs`
   obligations (B) and (C) bottom out in (`HargsShared`).  **Do not re-attack `hfld`; attack `hargs`,
   once, for all three.**
2. **`hmot`/`hmin`/`hbody`** for `RecTypeBridge` — reachable from the entrywise form now (§F), still
   data.  `NestedTele.lean` §T15.4/§T16 price them; keep §T4's vacuity note and the `Γ = []` emptiness
   of `substC_minorType_defeq`'s `hfun` in view before restating either.
3. **§E's live result-head defeq** at the companion constructors — the *only* remaining half of leaf (3);
   its `hnoc` companion is closed in general by §G.
4. The `ValAt` monotonicity step (`FlipGeneral.lean` §2a caveat (i)) and `HargsShared`'s two data are
   untouched, and no claim is made about them.
5. `csubst_WFD` is not re-instantiated at `ntreeAux`; that belongs to `ValRestGeneral`'s owner, per its
   §7 note 2.

**Process notes.**  No frozen file was read for editing, let alone edited.  No `sorry`.  No
state-changing git command was run.  `docs/vacuity-ledger.md` was not touched.  Zero warnings — the one
the linter did raise (`CanFld`'s unused `R`) was a real finding and is now recorded in that def's
docstring rather than silenced.
