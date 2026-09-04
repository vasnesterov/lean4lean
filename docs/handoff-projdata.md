# handoff-projdata — attacking `VEnv.ProjDataStrengthen`, the residual of census hole #1

Stream: `projdata`, round of 2026-09-04.  Owns exactly two files:
`Lean4Lean/Verify/Typing/ProjDataAttack.lean` and this document.  Everything else read-only;
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` frozen and untouched.

Target: `Lean4Lean.TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`, census hole #1), via its
claimed exact residual `Lean4Lean.VEnv.ProjDataStrengthen`
(`Verify/Typing/ProjExistClose.lean:66`).

## §1 PRIORS — written before any Lean tool call, never edited

### §1.a Claims in my brief I will verify rather than trust

Every claim relayed to me is on this list; none is assumed.

| id | claim as relayed | how I will check it |
|----|------------------|---------------------|
| V1 | hole #1 is `TrProj.weak'_inv`, arity 13, cone 90, own value is the hole | `exists.lean` |
| V2 | `VEnv.ProjDataStrengthen` arity 2, cone 696, hole-free | `exists.lean` |
| V3 | `ProjExistClose.lean` §1 docstring's claim that `ProjDataStrengthen` is *equivalent to the `sorry`'s statement* | read `projStrengthen_iff` + `TrProj.weak'_inv_of_projStrengthen` types; check `ProjStrengthen` really is the hole's statement ∀-quantified, field by field against the hole's own signature |
| V4 | line 114 proves `ProjStrengthen U ↔ ProjDataStrengthen U` | `exists.lean` on `VEnv.projStrengthen_iff`, plus axioms |
| V5 | `ConstAppTypeStrengthen` is arity 2, cone 619, hole-free (contradicting the audit's "cone 3698 with three holes") | `exists.lean` on both it and every `weak'_inv_of_*`; find which declaration 3698/three-holes actually describes |
| V6 | `ProjExistClose.lean` §2 exhibits a `VEnv.WF` env at which all ten `TrProj` fields hold with no hypotheses | `exists.lean` on `trProj_weak'_inv_fires`, `prjEnv_WF`, `prjEnv_trProj`; `#print axioms` on each |
| V7 | `ProjDataStrengthen`'s own hypotheses are satisfiable (non-vacuity) | `projDataStrengthen_fires` measured, and separately whether it covers the *whole* premise set incl. F17 |
| V8 | all producers of #1 are downstream of `Verify/Typing/Lemmas.lean`, so none is citable in place | `can-cite.py` |

### §1.b My own numbered predictions, with probabilities

Failure predictions included deliberately; §2 records verdicts even where I was wrong.

| # | prediction | p |
|---|-----------|---|
| P1 | V3/V4 hold: the `iff` is real and hole-free | 0.85 |
| P2 | **and therefore `ProjDataStrengthen` is a *repackaging*, not a weakening**: it is exactly as hard as hole #1, so the audit's own verdict on `weak'_inv_of_projStrengthen` ("a textbook admire-don't-instantiate hit") applies verbatim to the route it recommends. Attacking it "directly" = attacking the hole. | 0.80 |
| P3 | the audit's "3698 / three holes" figure describes `TrProj.weak'_inv_of_strengthen` (a *consumer* of `ConstAppTypeStrengthen`), not the predicate; V5's correction stands | 0.90 |
| P4 | I do **not** prove `ProjDataStrengthen` outright this round | 0.95 |
| P5 | the resisting field is `hty` — strengthening the major premise's typing `HasType U Γ' (e.lift' l) ((const S us).mkApp (ps++ιs))` down to `Γ`; the other nine fields are either context-free or follow by `HasArgs` strengthening | 0.75 |
| P6 | it resists because it is **unproved, not false**: I expect `ProjDataStrengthen` to be *true* at every `VEnv.WF env` but to need consistency/normalisation (an uninhabited inserted binder is the hard region, per `ProjInhab.lean`) | 0.60 true-but-hard / 0.15 refutable / 0.25 other |
| P7 | I can prove `ProjDataStrengthen` unconditionally in the **`l = .refl`/depth-zero** case, and reduce the general `Lift` to iterated single `.skip` by induction | 0.50 |
| P8 | I can prove a genuinely *new* reduction: `ProjDataStrengthen` follows from a typing-only strengthening statement (no `TrProj`, no `IsStructure`) plus `HasArgs` strengthening — i.e. isolate the nine free fields and leave one typing obligation | 0.60 |
| P9 | no consumer can cite anything I prove: my file must import `ProjExistClose.lean`, which is downstream of `Verify/Typing/Lemmas.lean` where the hole is | 0.90 |
| P10 | `HasArgs` strengthening at the *same* spine `ps` is **false** in general (the spine mentions the inserted variable), which is why `ProjDataStrengthen` existentially requantifies `ps'`, `ιs'` — I predict I can prove the requantification is *necessary*, not cosmetic | 0.45 |
| P11 | at least one docstring in the projection files conflates "tainted by a hole" with "open" (method rule 5) | 0.50 |
| P12 | `prjEnv`'s consistency is not available anywhere, so §2's witness cannot be pushed to the uninhabited-binder region | 0.85 |

### §1.c What would count as a result, in descending order

1. `ProjDataStrengthen` proved (hole #1 producible; census 13 → 12).
2. A refutation with a witness env (redirects everyone's attack).
3. A sharp partial: named field + named region that resists, with the true/false verdict separated
   and *proved* where possible.
4. Only the corrected chain and the honest price. (This is the floor; P2 says it is likely.)

## §2 MEASUREMENTS — appended in order, never reordered

### §2.1 `exists.lean` sweep (13 names, population 465 built modules)

| name | module | arity | cone | own value a hole | cone→`sorryAx` | holes in cone / watched |
|---|---|---|---|---|---|---|
| `Lean4Lean.TrProj.weak'_inv` | `Verify.Typing.Lemmas` | 13 | 90 | **true** | true | itself |
| `Lean4Lean.VEnv.ProjStrengthen` | `Verify.Typing.ProjExistClose` | 2 | **80** | false | false | none |
| `Lean4Lean.VEnv.ProjDataStrengthen` | `Verify.Typing.ProjExistClose` | 2 | 696 | false | false | none |
| `Lean4Lean.VEnv.projStrengthen_iff` | `Verify.Typing.ProjExistClose` | 2 | 714 | false | **false** | none |
| `Lean4Lean.VEnv.ConstAppTypeStrengthen` | `Verify.Typing.ProjWeakInv` | 2 | **619** | false | **false** | none |
| `Lean4Lean.TrProj.weak'_inv_of_strengthen` | `Verify.Typing.ProjWeakInv` | 14 | **3698** | false | true | **3 holes**: `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`; watched: `HasArgs.of_mkApp`, `IsDefEq.uniq`, `IsDefEq.uniqU` |
| `Lean4Lean.TrProj.weak'_inv_of_projStrengthen` | `Verify.Typing.ProjExistClose` | 14 | 84 | false | false | none |
| `Lean4Lean.TrProj.weak'_inv_of_projDataStrengthen` | `Verify.Typing.ProjExistClose` | 14 | 717 | false | false | none |
| `Lean4Lean.trProj_weak'_inv_fires` | `Verify.Typing.ProjExistClose` | 0 | 4358 | false | **false** | none |
| `Lean4Lean.projDataStrengthen_fires` | `Verify.Typing.ProjExistClose` | 0 | 2042 | false | **false** | none |
| `Lean4Lean.prjEnv_WF` | `Verify.Typing.ProjExistClose` | 0 | 1921 | false | false | none |
| `Lean4Lean.prjEnv_trProj` | `Verify.Typing.ProjExistClose` | 0 | 1954 | false | false | none |
| `Lean4Lean.VEnv.ConstAppTypeStrengthen.projDataStrengthen` | `Verify.Typing.ProjExistClose` | 4 | 3702 | false | true | same 3 holes + same 3 watched |

**Verdicts against §1.**

* V1 ✓ exactly as relayed (13 / 90 / own value the hole).
* V2 ✓ exactly as relayed (2 / 696 / hole-free).
* V4 ✓ `projStrengthen_iff` exists, arity 2, cone 714, **`sorryAx`-free**.
* V5 ✓ **and the brief's suspicion was right**: `ConstAppTypeStrengthen` is arity 2, cone 619,
  hole-free. The audit's "cone 3698 with three holes" is
  `Lean4Lean.TrProj.weak'_inv_of_strengthen` — arity 14, cone **3698**, exactly three holes
  (`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`). That is a *consumer* of the
  predicate, not the predicate. **P3 correct at p=0.90.** The audit's own §M3 row 104 already
  carries the right attribution, so the error is in the relayed prose, not in the audit table.
* Bonus, unpredicted: `ConstAppTypeStrengthen.projDataStrengthen` (the "one side of the bound")
  is 3702 / three holes / three watched names — i.e. **the `ConstAppTypeStrengthen` route is
  holier than the audit's headline suggests even as a bound**, because it routes through
  `weak'_inv_of_strengthen`.
* Note for method rule 5: the three names `HasArgs.of_mkApp`, `IsDefEq.uniq`, `IsDefEq.uniqU`
  are **watched-by-policy, not holes**. Any prose calling that route "three open holes plus
  three unproved lemmas" would be committing exactly the conflation rule 5 warns about.

### §2.2 V3 / the corrected equivalence chain (read at source, `Lemmas.lean:902`)

The hole verbatim:

```
theorem TrProj.weak'_inv (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.Lift' l Γ Γ') (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' := sorry
```

Its 13 binders are `{env U Γ Γ' l s i e e'}` + `henv hΓ' W H`. `VEnv.ProjStrengthen env U`
(arity 2, cone 80) is *literally* those last three hypotheses and that conclusion, ∀-quantified
over `{Γ Γ' l s i e e'}` — **with `henv : VEnv.WF env` dropped**. That one difference is the only
inexactness in the relayed claim, and it matters for the direction of the chain:

| step | statement | status |
|---|---|---|
| a | `ProjStrengthen env U → ProjDataStrengthen env U` | proved, `VEnv.ProjStrengthen.projDataStrengthen`, no `WF` |
| b | `ProjDataStrengthen env U → ProjStrengthen env U` | proved, `VEnv.ProjDataStrengthen.projStrengthen`, no `WF` |
| c | `(∀ env U, ProjStrengthen env U) → ` hole | proved, `TrProj.weak'_inv_of_projStrengthen` (`_henv` **unused**) |
| d | hole `→ ∀ env, WF env → ∀ U, ProjStrengthen env U` | immediate (the hole *is* that, curried) |

So the **corrected chain** is

> hole ⟺ `∀ env, VEnv.WF env → ∀ U, env.ProjStrengthen U` ⟺ `∀ env, VEnv.WF env → ∀ U, env.ProjDataStrengthen U`,

with (a),(b) holding *pointwise and without* `WF`, and `ProjStrengthen` being pointwise
**stronger** than the hole's per-`env` content (it forgoes `WF env`).

**V3 ✓ with a correction; P1 ✓ (p=0.85).** The `ProjExistClose.lean` §1 docstring's "equivalent
to the `sorry`'s statement" is accurate as a statement about the ∀-closed forms.

**P2 ✓ (p=0.80), and this is the round's first substantive finding.** Because the chain is an
*equivalence*, `ProjDataStrengthen` is **not a weakening of hole #1 — it is hole #1 rewritten at
the field level** (`TrProj.mk`'s ten fields spelled out instead of the inductive). Closing it
closes the hole (good), and it is *exactly as hard* as the hole (no free progress). The audit's
own verdict on the sibling — `weak'_inv_of_projStrengthen` at cone 84 is "a repackaging, not a
producer — a textbook admire-don't-instantiate hit" — applies **verbatim** to
`weak'_inv_of_projDataStrengthen` at cone 717, which the audit instead promoted to "#1's
residual". Both are `iff`-repackagings of the same content; the only difference between them is
696 − 80 = 616 constants of *unfolded field data*. The honest statement of what §1 of
`ProjExistClose.lean` achieved is: **it converted the hole from inductive form to data form
hole-free**, which is a genuine service to an attacker (the fields are now visible and
individually addressable) but is **not** a reduction in strength, and "attack the residual"
is therefore "attack the hole".

Consequence for the brief's framing: the comparison "717 with no holes vs 3698 with three" is
**not** a like-for-like improvement. 3698/3-holes is `weak'_inv_of_strengthen`, which discharges
the hole from a *strictly stronger, non-equivalent* hypothesis (`ConstAppTypeStrengthen`); 717/0
discharges it from an *equivalent* one. A hole-free reduction from an equivalent hypothesis is
free by construction — the taint had to leave, because no mathematics crossed.

### §2.3 The instrument the previous rounds did not use: `TrProj.instN`

| name | module | arity | cone | holes |
|---|---|---|---|---|
| `Lean4Lean.TrProj.instN` | **`Verify.Typing.Lemmas`** | 16 | 2340 | **none** |
| `Lean4Lean.VEnv.HasArgs.instN` | `Theory.Inductive.StructureClosed` | 14 | 1849 | none |
| `Lean4Lean.TrProj.weak'` | `Verify.Typing.Lemmas` | 12 | 3263 | none |
| `Lean4Lean.Ctx.InhabLift` | `Verify.Typing.ProjWeakInv` | 5 | 6 (type only) | n/a |
| `Lean4Lean.Ctx.InhabLift.sorts` | `Verify.Typing.ProjWeakInv` | 4 | 638 | none |
| `Lean4Lean.VEnv.ConstAppSkipUninhab` | `Verify.Typing.ProjWeakInv` | 2 | 606 | none |
| `Lean4Lean.constAppTypeStrengthen_of_skipUninhab` | `Verify.Typing.ProjWeakInv` | 4 | 1207 | none |

`TrProj.instN` substitutes a whole `TrProj` derivation through `Ctx.InstN` — it already does, at
`Lemmas.lean:2141`, exactly the per-field work `ProjDataStrengthen` spells out (it is where
`VEnv.HasArgs.instN`, `VExpr.instTele_eq_self` and `VInductDecl'.projTerm_instN` are discharged),
and it is **hole-free and in the hole's own module**. Neither `ProjWeakInv.lean` nor
`ProjWeakInvSplit.lean` nor `ProjExistClose.lean` cites it: all three route the inhabited case
through `HasType.instN` on the *type only* (`hasType_const_mkApp_of_inhabLift`) and then pay
`VEnv.HasArgs.of_mkApp` (→ `rigidShapeUniqNS`, `forallE_inv_stratified`, `IsDefEq.uniq`) to
rebuild the two `HasArgs` fields they discarded.

**Plan (P8's shape, sharpened): redo `ProjWeakInv.lean`'s two Round-2 results at the `TrProj`
level with `TrProj.instN`, so no field is ever discarded and `of_mkApp` is never called.**
Expected deliverables: (i) the inhabited-lift region, hole-free; (ii) `ProjStrengthen` (hence
`ProjDataStrengthen`, hence hole #1) from a **one-uninhabited-binder** residual, hole-free.

### §2.4 First elaboration of `ProjDataAttack.lean` (before any fix)

Five errors, all mechanical (two dot-notation projections through a `def`-unfolded `∀`, one
unresolvable implicit `e'`, one `prjCtx.length`-vs-`1` mismatch). **Zero errors in the three
substantive proofs**: `TrProj.strengthen_inhabLift`,
`projStrengthen_of_allTypesInhabited_aux` and `projStrengthen_of_skipUninhab_aux` all
elaborated on the first pass, i.e. `TrProj.instN` slots into `ProjWeakInv.lean`'s Round-2
inductions with `HasType.instN` swapped out and nothing else changed.

* **P7 ✓ and better than predicted (p=0.50).** Predicted: depth-zero plus a `Lift` induction.
  Obtained: the whole *inhabited* region at every depth, plus `AllTypesInhabited`, plus the
  reduction to one uninhabited binder.
* **P8 ✓ (p=0.60)** in a stronger form than stated: the "typing-only obligation" is isolated
  *without* discarding the nine other fields, so `VEnv.HasArgs.of_mkApp` — and with it
  `rigidShapeUniqNS`, `forallE_inv_stratified`, `IsDefEq.uniq`, `IsDefEq.uniqU` — never enters.
* **P4 ✓ (p=0.95).** `ProjDataStrengthen` is *not* proved; §3's residual is what is left.
* **P5 ✓ (p=0.75).** The field that resists is `hty`, exactly as predicted; the other nine ride
  along inside `TrProj.instN`.

### §2.5 The new declarations, measured (`exists.lean`, population 467)

All twelve: `own value is a hole: false`, `cone reaches sorryAx: false`, **`watched declarations
in cone: none of 6`**.

| name | arity | cone | holes | watched |
|---|---|---|---|---|
| `Lean4Lean.TrProj.strengthen_inhabLift` | 12 | 2346 | none | none |
| `Lean4Lean.TrProj.strengthen_sorts` | 10 | 2358 | none | none |
| `Lean4Lean.VEnv.AllTypesInhabited.projStrengthen` | 4 | 2376 | none | none |
| `Lean4Lean.VEnv.AllTypesInhabited.projDataStrengthen` | 4 | 2379 | none | none |
| `Lean4Lean.VEnv.ProjSkipUninhab` | 2 | **145** | none (def) | none |
| `Lean4Lean.VEnv.ProjSkipUninhab.projStrengthen` | 4 | 2376 | none | none |
| `Lean4Lean.VEnv.ProjSkipUninhab.projDataStrengthen` | 4 | 2379 | none | none |
| **`Lean4Lean.TrProj.weak'_inv_of_skipUninhab`** | 14 | **3412** | **none** | **none** |
| `Lean4Lean.VEnv.ProjStrengthen.skip_step` | 13 | 365 | none | none |
| `Lean4Lean.projSkipUninhab_fires` | 0 | 4354 | none | none |
| `Lean4Lean.trProj_strengthen_inhabLift_fires` | 0 | 4404 | none | none |
| `Lean4Lean.hasType_bvar_length_absurd` | 6 | 898 | none | none |

**The price comparison that matters** (same conclusion — hole #1's exact statement — from a
one-uninhabited-binder residual):

| route | cone | holes | watched-by-policy |
|---|---|---|---|
| `constAppTypeStrengthen_of_skipUninhab` ⨟ `TrProj.weak'_inv_of_strengthen` | 3698 | 3 (`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`) | 3 (`HasArgs.of_mkApp`, `IsDefEq.uniq`, `IsDefEq.uniqU`) |
| **`TrProj.weak'_inv_of_skipUninhab` (this round)** | **3412** | **0** | **0** |

The mechanism of the improvement, stated so it is not mistaken for bookkeeping: the old route
strengthens the major premise's *type* (`HasType.instN`), which forces it to discard the two
`HasArgs` fields of `TrProj.mk` and rebuild them with `VEnv.HasArgs.of_mkApp` — Π-injectivity,
hence `rigidShapeUniqNS` + `forallE_inv_stratified` + `IsDefEq.uniq`/`uniqU`. The new route
substitutes the *whole derivation* (`TrProj.instN`), so no field is ever discarded and
Π-injectivity is never needed.

### §2.6 Axioms, citability, and the migration that would make this discharge the hole

**Axioms** (`lean_verify`, fully qualified): `TrProj.weak'_inv_of_skipUninhab`,
`VEnv.ProjSkipUninhab.projDataStrengthen`, `VEnv.AllTypesInhabited.projStrengthen` and
`projSkipUninhab_fires` each depend on exactly `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no extra axiom.

**Consumer (`can-cite.py`, consumer `Lean4Lean.Verify.Typing.Lemmas`, closure 116 modules).**

| declaration | citable from the hole's module? |
|---|---|
| `Lean4Lean.TrProj.weak'_inv_of_skipUninhab` (mine) | **NO** — `ProjDataAttack` is downstream |
| `Lean4Lean.VEnv.ProjSkipUninhab` (mine) | **NO** — same |
| `Lean4Lean.Ctx.InhabLift` | NO — `Verify.Typing.ProjWeakInv` |
| `Lean4Lean.VEnv.AllTypesInhabited` | NO — `Verify.Typing.ProjInhab` |
| **`Lean4Lean.TrProj.instN`** | **YES** — it is *in* `Verify/Typing/Lemmas.lean` |
| `Lean4Lean.Ctx.LiftN.exists_instN_typed` | YES — `Theory.Typing.StrengthenAxiom` |
| `Lean4Lean.Ctx.InstN.wf` | YES — `Theory.Typing.Lemmas` |

**P9 ✓ (p=0.90)** — my results are downstream and cannot discharge the `sorry` in place. But the
*instrument* is not, and I measured how far that goes. Intra-module order is the only obstacle,
and it is checkable: computing the cone of `TrProj.instN` and filtering to declarations defined
in `Verify/Typing/Lemmas.lean` gives

```
== Lean4Lean.TrProj.instN: 2 deps declared in Verify.Typing.Lemmas
   Lean4Lean.TrProj.instN.match_1_1
   Lean4Lean.TrProj.instN
```

i.e. **`TrProj.instN` (line 2141) depends on nothing else in its own module** — in particular not
on `TrProj.weak'_inv` (line 902) and not on anything between them. So it can be moved above line
902 with no reordering hazard, and §3 of `ProjDataAttack.lean` can then be stated there. §3 below
writes that edit out; it is an edit to a file this stream does not own, so it is stated and not
made.

**Anti-duplication check (method rule 3).** `HEADS="TrProj Ctx.LiftN" shape.lean` over the
467-module population returns **3** declarations, 0 of them structure fields: my two, and
`TrProj.weakN` (the *forward* direction). So the single-binder projection strengthening did not
exist in the tree in any name. `lean_references` on `TrProj.instN` returns 5 real sites: its own
declaration, one internal use at `Lemmas.lean:2176`, and my three — confirming that no file in
the projection family cited it before today.

**P12 ✓ (p=0.85)** — `prjEnv.Consistent` occurs in the tree exactly once, in
`ProjExistClose.lean:265`, as prose saying it "is not proved here or anywhere". So §2's witness
cannot be pushed into the well-formed uninhabited region, and neither can mine.

**P10 — NOT ATTEMPTED, recorded as a miss.** I did not prove that the existential
requantification of `ps'`/`ιs'` is *necessary*; §4.3 of the Lean file argues it from the shape of
`hty` but proves nothing. Whoever picks this up should treat it as open.

**P11 ✓ in the weak sense, ✗ in the strong sense.** No in-tree docstring commits the
hole-vs-watched conflation for these files: `ProjWeakInv.lean` and the audit table both label
`HasArgs.of_mkApp`/`IsDefEq.uniq`/`uniqU` correctly as watched-not-holes. Two smaller doc defects
found instead, both in `Verify/Typing/ProjExistClose.lean`'s header, neither in a file I own:
line 19 cites `TrProj.weak'_inv_of_strengthen` as "(3661, three holes)" where today's measurement
is **3698** (cone drift from concurrent commits, holes unchanged), and line 21 refers to "§1.4",
which does not exist in that file (its sections are §1, §2, §2.5, §2.6, §3). The trade that §1.4
was to state is now stated in `ProjDataAttack.lean`'s §2.5 table.

## §3 The edit this stream does NOT make, written out for the orchestrator

Nothing frozen is involved: `Verify/Soundness.lean`, `Verify/Axioms.lean` and `Verify/Guard.lean`
are untouched by this and were never opened for writing. The file below is owned by another
stream, so the edit is stated and not made.

**File:** `Lean4Lean/Verify/Typing/Lemmas.lean` (read-only for this stream).

**Edit, in two parts.**

1. **Move** the declaration block `TrProj.instN` (currently lines 2141–2154, ending with the
   `rwa [VExpr.inst_instAllTele₀ …]` line) to any point **above** line 902. Verified safe: the
   cone of `TrProj.instN` contains exactly two constants declared in that module — itself and its
   own `match_1_1` auxiliary — so it has no intra-module dependency that would be dragged along,
   and in particular it does not depend on `TrProj.weak'_inv`.

2. **Insert**, immediately before `theorem TrProj.weak'_inv` (line 902), the contents of
   `Lean4Lean/Verify/Typing/ProjDataAttack.lean` §3 — `VEnv.ProjSkipUninhab`,
   `projStrengthen_of_skipUninhab_aux` and one `TrProj.weak'_inv`-shaped corollary — with
   `VEnv.ProjStrengthen`/`VEnv.ProjDataStrengthen` inlined (they live downstream in
   `ProjExistClose.lean`; the corollary should be stated directly in the hole's own shape, which
   needs no definition):

   ```lean
   theorem TrProj.weak'_inv_of_skipUninhab' (henv : VEnv.WF env)
       (hres : ∀ {k : Nat} {Γ Γ' : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
         Ctx.LiftN 1 k Γ Γ' →
         (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
         TrProj env U Γ' s i (e.liftN 1 k) e' → ∃ e'', TrProj env U Γ s i e e'')
       (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
       (H : TrProj env U Γ' s i (e.lift' l) e') : ∃ e'', TrProj env U Γ s i e e''
   ```

   All of its dependencies are citable there: `TrProj.instN` (after the move), `Lift.depth_succ`,
   `Ctx.Lift'.of_cons_skip`, `Ctx.liftN_iff_lift'`, `VExpr.inst_liftN`, `VExpr.lift'_comp`,
   `VExpr.lift'_consN_skipN`, `VExpr.lift'_depth_zero`, `Lift.consN_skip_eq`, `Lift.skipN_one` —
   the last nine all from `Theory/`, verified by `can-cite.py` for the two non-obvious ones
   (`Ctx.InstN.wf`, `Ctx.LiftN.exists_instN_typed`: both YES).

**What the edit buys, and what it does not.** It does not discharge the `sorry`. It replaces the
hole's *documented* best route — `TrProj.weak'_inv_of_strengthen`, which carries three census
holes and three watched names — with an in-module route carrying **neither**, whose only
hypothesis is the one-uninhabited-binder statement. Whoever eventually closes hole #1 then owes
only that statement, and owes it at a shape where nine of `TrProj.mk`'s ten fields are already
discharged.

## §4 Prediction ledger — verdicts against §1.b

| # | p | verdict | note |
|---|---|---|---|
| P1 | 0.85 | ✓ | the `iff` is real, `sorryAx`-free, cone 714 |
| P2 | 0.80 | ✓ | equivalence ⇒ repackaging; the recommended "residual" is the hole in field form |
| P3 | 0.90 | ✓ | 3698/three-holes is `TrProj.weak'_inv_of_strengthen`; `ConstAppTypeStrengthen` is 619/hole-free |
| P4 | 0.95 | ✓ | not proved |
| P5 | 0.75 | ✓ | `hty` resists; the other nine fields ride inside `TrProj.instN` |
| P6 | 0.60 | ✓ (unproved, not false) | see §4.3 of the Lean file; a refutation would need a consistency witness |
| P7 | 0.50 | ✓, exceeded | whole inhabited region at every depth, not just depth zero |
| P8 | 0.60 | ✓, exceeded | the nine free fields are never discarded, so `of_mkApp` never enters |
| P9 | 0.90 | ✓ | downstream; but the migration is verified legal (§2.6, §3) |
| P10 | 0.45 | **not attempted** | recorded as a miss, not as a result |
| P11 | 0.50 | partial | no hole/watched conflation found; two smaller doc defects instead |
| P12 | 0.85 | ✓ | `prjEnv.Consistent` proved nowhere |

Priors that were wrong in *direction*: none. Priors that were too pessimistic: P7, P8. The
prediction that mattered most was P2, and it is the one that changes what the next round should
do: **"attack the residual" and "attack the hole" were the same instruction**, so the round's
value had to come from shrinking the residual rather than from proving it.

## §5 Limits of this round's result, stated as required

1. **The reduction is not a proof.** `VEnv.ProjSkipUninhab` is open. Everything above it in the
   chain is now hole-free, which is exactly why it is worth naming.
2. **It is tight only modulo `OnCtx Γ'`.** `VEnv.ProjStrengthen.skip_step` shows the one-binder
   form is an instance of the hole *given* `OnCtx Γ'`; my residual does not carry that premise, so
   it asks for the strengthening at contexts that need not be well formed. This is exactly the
   position `VEnv.ConstAppSkipUninhab` is already in, so it is parity, not regression. **Why it
   cannot be fixed cheaply:** carrying `OnCtx` down the induction needs `OnCtx Γ₂` *after* the
   uninhabited step, and the only in-tree route to that is `OnCtx.weak'_inv`, which re-imports
   `IsDefEqU.weakN_iff` — the taint the whole exercise removes. An `OnCtx`-carrying variant would
   have to make the residual *return* `OnCtx Γ`, which is strictly more to prove.
3. **The anti-vacuity witness is cheap, and says so.** `projSkipUninhab_fires` has a genuinely
   uninhabited inserted binder — the first in this family — but it is uninhabited because it is an
   *open* expression (`.bvar Γ.length`, killed by `IsDefEq.closedN'`), so `OnCtx Γ'` fails there.
   It witnesses that the residual as stated is non-vacuous; it does **not** witness the
   well-formed uninhabited region, which is `VEnv.Consistent`-flavoured and unexhibited.
4. **`ProjDataStrengthen` is not the right thing to attack, and this round is the evidence.**
   The productive object is `VEnv.ProjSkipUninhab` (cone 145) or, equivalently, the typing
   strengthening `ProjWeakInvSplit.lean` already isolates.

## §6 Method gaps in this round

* I never ran `sorry-census` myself; the "census 13" figure is inherited, and my claim is only
  that the census **does not move** (no `sorry` was discharged), which does not depend on it.
* `can-cite.py` answers import-closure questions but not intra-module *ordering*; I had to write a
  one-off cone/module filter (`/tmp/coneloc.lean`, outside the repo) to check the migration. If a
  later round needs that again it should be a script, not a temp file — the closest existing one
  is `scripts/cone-orphans.py`.
* `scripts/exists.lean` prints no cone *members*, so "which of my deps are local" is not
  answerable with the standard instruments. That is the gap that hid `TrProj.instN` from four
  earlier rounds: every instrument answered "does it exist" and "is it clean", none answered
  "what is already available *right here*".
* I did not attempt P10, and I did not attempt any refutation of `ProjSkipUninhab` — §4.3's
  argument for "unproved, not false" is an argument about what a refutation would have to contain,
  not a proof that none exists.
