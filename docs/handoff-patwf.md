# Handoff: `VEnv.PatWF` — closed

**Question asked (this round):** discharge `VEnv.PatWF`'s ι case, decomposed in the previous
version of this file into eight named obligations; report the measured cone the same way the
quot case was reported, and say plainly if it is larger.

**Answer.**  **The ι case is closed.**  `VEnv.patWF_iota` is `sorry`-free in a new file this
stream owns, and with it

* `VEnv.patWF henv hpi : env.PatWF U` holds at an **arbitrary** `VEnv.WF` environment, and
* `VEnv.paramsOfPiInv henv U hpi : Params` builds the whole ten-field class there,

with `VEnv.PiInv` (Π-injectivity, `Theory/Typing/Injectivity.lean`'s `forallE_inv` type
verbatim) as the *only* extra hypothesis.  The measured hole cone of `patWF_iota` is
**`IsDefEqU.forallE_inv_stratified` alone — identical to `patWF_quot`'s and to
`IsDefEq.uniqU`'s.  The ι case is not larger than the quot case.**

`IotaFree`/`patWF_of_iotaFree` (`PatWF.lean`) are now subsumed and kept only for continuity.

Marks: **[machine-checked]** = a named Lean declaration in this tree with its axiom set or
cone reproduced; **[measured]** = a machine run whose output is reproduced; **[read]** = read
off source; **[analysis]** = neither.

---

## 0. The one correction that matters: a missing field on `Pat.iota`

**`Pat.iota` did not carry `C.args.length = T.indices.length`, and without it the ι case of
`pat_wf` is not merely hard but false-shaped — unprovable by anyone.** **[analysis, with the
mechanism spelled out]**

The pattern `D.iotaPat T C` states the recursor's arity as `np + nm + nmin + |T.indices|`, so
a match hands back an index block of `|T.indices|` terms.  The rule `D.iotaRule j q C` puts
`C.args.map _` in those positions, i.e. `|C.args|` terms.  Relating a matched redex to the
fired rule is a spine congruence, and a spine congruence between lists of different lengths
does not exist.  So the two widths must be tied, and nothing else in `Pat.iota`'s data ties
them.

Deriving it instead is not available: an under- or over-applied recursor's type is a `mkPi`
while `iotaType` is a `bvar`-headed application, so the derivation is a Π-vs-application
discrimination — the open injectivity corner, which is exactly what this line of work is
trying to *avoid* needing.

The field was added (`PatternRules.lean`), with the rationale in a comment beside F3's, which
is the exact precedent: `C.params.length = D.np` is there for the same kind of reason and was
added the same way.

**Audited against consumers, not only producers.**  Adding a field makes `Pat` *smaller*, so
every field of `Params` whose shape is `Pat → …` (`pat_simple`, `pat_uniq`, `pat_app_l_uniq`,
`pat_app_uniq`, `pat_wf`) gets *easier*; the only field that gets harder is `extra_pat`, which
must **produce** a `Pat`.  Its single ι site is `Pat.extra_iota`, and it already had `hal :
C.args.length = T.indices.length` in scope — `VEnv.RuleShape.iota` carries it, from
`VIndCtor.WF.args_len`, exactly as it carries `params_len`.  One argument added; nothing else
in the tree changed.  Every other ι case-split in the tree binds fields positionally up to
`hdf` (5th) or uses `..`, so appending a 9th field shifts nothing — including
`Verify/Typing/Rigidity.lean:337`, which this stream does not own. **[measured: full
`lake build` clean; census unchanged at 19.]**

## 1. What is in the tree now

`Lean4Lean/Theory/Typing/PatWFIota.lean` — **new**, 732 lines, **no `sorry`**, 29 named
declarations.  `Lean4Lean/Theory/Typing/PatternRules.lean` — the `Pat.iota` field of §0 plus
the one-argument fix in `Pat.extra_iota`.  Nothing else changed. **[measured: full `lake
build` clean; `lake env lean scripts/sorry-census.lean` TOTAL 19, same names as before.]**

| name | statement | cone holes **[measured]** |
|---|---|---|
| `VEnv.HasArgs.append_inv` | obligation 2: `HasArgs.append` inverted at an arbitrary split | none |
| `VInductDecl'.preTele`, `iotaCtx_eq`, `peelPis_recType`, `peelPis_recType_body` | obligation 1: `recType j` and `iotaCtx C` share the *syntactic* prefix `atRecTele params ++ motives ++ minors` | none |
| `VIndCtor.peelPis_type` | the constructor's stored type peels to `C.params ++ fields` | none |
| `VExpr.mkPi_peelPis`, `instL_eq_mkPi_peelPis` | `peelPis`' inverse (the `mkLams_peelLams` analogue, which was missing) | none |
| `VEnv.HasArgsDF.ofForall₂` | a `HasArgs` plus entrywise `IsDefEqU` is a `HasArgsDF` | none |
| `VEnv.HasType.mkApp_mem` | **every** argument of a typed spine is typed (`mkApp_arg` gives only the first) | none |
| `VEnv.ctor_type_wf` | the constructor's *stored* type, unpacked: field telescope well-formed, every `C.args` entry typed | none |
| `VEnv.ctor_spine_retyped` | obligations 3+5: the matched major premise moved to the recursor's parameters **and** level numbering | `forallE_inv_stratified` |
| `VEnv.iota_index_clause_at` | **obligation 4**, in the opposite direction from `iota_index_clause` | `forallE_inv_stratified` |
| `VInductDecl'.iotaLhs_instAll'` | obligations 6+7+8: `iotaLhs` at a general concrete spine (`StructureClosed.lean`'s is `nm = nmin = 1`) | none |
| `VInductDecl'.iotaRhsBody_instAll'` | the η-wrapper collapse at general `q` | none |
| `VEnv.patWF_iota` | **the ι case of `PatWF`, in full** | `forallE_inv_stratified` |
| `VEnv.patWF` | **`PatWF` at an arbitrary `VEnv.WF` environment**, from `PiInv` | `forallE_inv_stratified` |
| `VEnv.paramsOfPiInv` | **`VEnv.Params` at an arbitrary `VEnv.WF` environment**, from `PiInv` | `forallE_inv_stratified` |
| `VEnv.patWF_iota_nontrivial` | the ι conclusion is not a reflexivity — §6 | none |
| `VEnv.patWF_iota_fires`, `nvClosed` | …and its hypotheses are jointly satisfiable, closedness **decided** | none |

Axioms, verbatim **[measured]**:

    'Lean4Lean.VEnv.patWF_iota'              [propext, sorryAx, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.patWF'                   [propext, sorryAx, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.paramsOfPiInv'           [propext, sorryAx, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.patWF_iota_nontrivial'   [propext, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.patWF_iota_fires'        [propext, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.nvClosed'                [propext]
    'Lean4Lean.VInductDecl'.iotaLhs_instAll'' [propext, Quot.sound]

The `sorryAx` is `forallE_inv_stratified`'s, inherited through `IsDefEq.uniq`; it is not new
and it is **not** `forallE_inv`'s.

## 2. The measurement

Forward hole cones, transitive over type **and** value (`allowOpaque := true`) **[measured]**:

| seed | cone | `sorry`-carrying declarations reached |
|---|---|---|
| `VEnv.IsDefEq.uniqU` | 3434 | `forallE_inv_stratified` |
| `VEnv.ctor_spine_retyped` | 3481 | `forallE_inv_stratified` |
| `VEnv.iota_index_clause_at` | 3516 | `forallE_inv_stratified` |
| `VEnv.patWF_quot` | 3714 | `forallE_inv_stratified` |
| **`VEnv.patWF_iota`** | **3840** | **`forallE_inv_stratified`** |
| `VEnv.patWF` | 3889 | `forallE_inv_stratified` |
| `VEnv.paramsOfPiInv` | 6788 | `forallE_inv_stratified` |
| `Lean4Lean.Pat.extra` | 4480 | none |
| `VEnv.const_app_inv_of_patWF` | 7268 | `forallE_inv`, `forallE_inv_stratified`, `NormalEq.descend`, `weakN_iff` |

**The answer to the question as asked: the ι case's cone is not larger than the quot case's.**
Both are `forallE_inv_stratified` alone, which equals `IsDefEq.uniqU`'s own cone.  With
Π-injectivity carried as the explicit hypothesis `PiInv` and consumed only through
`HasArgs.of_mkApp'`, the whole const/rule corner is *reducible to* the sort/Π corner and adds
nothing to it.  As the previous round already recorded, that reduction is one-directional:
`PatWF → PiInv` is **false** as an implication, because `PatWF` is vacuous at a rule-free
environment while `PiInv` is not.

## 3. How the ι case goes

The five steps of `patWF_quot` at general telescopes.  Write `σ := D.selfLvls.map (VLevel.inst
ls)` for the constructor's level list in the recursor's numbering, `k := np + nm + nmin`.

1. **Invert the match** (`Pattern.matches_iota_inv`): `e = R.{ls} (ps ++ mid ++ idxs)
   (K.{ls'} (cps ++ fs))` with `|ps| = np`, `|mid| = nm + nmin`, `|idxs| = |T.indices|`,
   `|cps| = np`, `|fs| = nf`.
2. **Invert the recursor's typing** against `peelPis (recType j)` (`HasArgs.of_mkApp'` — this
   is where `PiInv` is spent, once), split off the major premise (`concat_inv`) and split
   `ps ++ mid` off the rest (`append_inv`).  Obligation 1 is what makes the first `k` domains
   of `recType j` *literally* the first `k` domains of `iotaCtx C`, so no transport is needed
   for the parameter/motive/minor block at all.
3. **Move the constructor's spine** (`ctor_spine_retyped`): the check's parameter clauses give
   `cps ≡ ps` and its level clauses give `ls' ≈ σ`, and one `IsDefEq.mkAppDF` moves
   `K.{ls'} (cps ++ fs)` to `K.{σ} (ps ++ fs)`.  Re-inverting *that* with `of_mkApp'` at the
   constant's type instantiated at `σ` yields the field block of `iotaCtx C` on the nose.
   **This is the step that made the F3 transport (`C.params` vs `D.params`) unnecessary**: the
   parameter *telescope* is never compared, only the parameter *terms*, and each spine
   supplies its own typing.
4. **Fire the rule** (`IsDefEq.extra_applied'`) at `ps ++ mid ++ fs` and compute both sides
   (`iotaLhs_instAll'`, `iotaRhsBody_instAll'`).
5. **Bridge back to `e`** by one `IsDefEq.mkAppDF` over the recursor's whole telescope, whose
   index entries are the check's index clauses composed with `iota_index_clause_at`.

Every one of `iotaCheck`'s three clause groups is consumed, each at exactly one place.  The
`PatternDecode.lean` header's warning — that `Check.true` would make `pat_wf` "unprovable by
anyone rather than merely unproved" — is now confirmed for the ι case too, by a proof that
uses all three groups.

## 4. The eight obligations, resolved

| # | obligation (previous §4) | outcome |
|---|---|---|
| 1 | telescope-prefix agreement | `preTele`, `iotaCtx_eq`, `peelPis_recType` — `rfl`-level, as predicted |
| 2 | `HasArgs.append_inv` | proved |
| 3 | field-block transport | **not done as stated.**  `IsDefEq.instAllCongrSort` was *not* used and `VIndCtor.WF` was *not* needed.  Replaced by `ctor_spine_retyped`'s move-then-re-invert (§3 step 3), which costs one extra `of_mkApp'` and no telescope-congruence lemma at all |
| 4 | index clauses, opposite direction | `iota_index_clause_at`.  Predicted "largest single piece"; **it is not** — 70 lines, because §3 step 3 already produced the `HasArgs` its `betaMkLams` needs |
| 5 | level bridging | folded into obligation 3; `IsDefEq.instL_r` (`Strong.lean`) is the lemma, `constDF` is not enough on its own |
| 6 | constructor-side congruence | `iotaLhs_instAll'` + `mkAppDF`; cheap, as predicted |
| 7 | `instAll` at general `bvars` blocks | `iotaLhs_instAll'`'s `e1`/`e2`/`e3`/`e4`; `map_instAll_bvars_top`/`_bot` did all of it |
| 8 | major-premise `appDF` | subsumed: the single `mkAppDF` of §3 step 5 covers head, index block and major premise together |

**The attack order in the previous §4 was wrong in one place and it cost nothing to find out:**
obligation 3 was listed as needing `VIndCtor.WF` recovered from `env.WF` via
`VEnv.WF.ruleShape` / `iotaCtx_of_staged`.  That route is not available — `Pat.iota` does not
carry the block's well-formedness, and `ruleShape` hands back *some* decomposition of the
rule, not this `D`.  The route that works uses only `Ordered.constWF` on the two constants
`Pat.iota` already records.  **A brief that had insisted on the `VIndCtor.WF` route would have
sent the next stream at a dead end.**

## 5. The consumer holes — the `PatWF`-shaped obligation is gone; three others remain

`quotReduceRec.WF` (`Verify/TypeChecker/WHNF.lean:109`), `TrProj.uniq` and `TrProj.weak'_inv`
(`Verify/Typing/Lemmas.lean`) are **still open**, and the census is still 19.  But the reason
has changed, and the change is the point.

`quotReduceRec.WF`'s docstring says its residual is "*forward* (discharge `PatWF`)".  That
input now exists at an arbitrary environment.  The following compiles and typechecks
**[measured]** (kept out of the tree only because it would make a `Theory/` file import
`Verify/`; it belongs in `Verify/Typing/` if the orchestrator wants it landed):

```lean
import Lean4Lean.Theory.Typing.PatWFIota
import Lean4Lean.Verify.Typing.ConstSpine

theorem constAppInv_of_piInv {env : VEnv} (henv : env.WF) (U : Nat) (hpi : env.PiInv U) :
    VEnv.ConstAppInvStmt env U :=
  VEnv.constAppInvStmt_of_patWF henv U (VEnv.patWF henv hpi)
-- and likewise constForallEInvStmt_of_patWF, constSortInvStmt_of_patWF,
-- and IsDefEq.church_rosser at paramsOfPiInv.
```

Its measured cone is **7433, holes `forallE_inv`, `forallE_inv_stratified`, `NormalEq.descend`,
`weakN_iff` — and nothing `PatWF`-shaped.** **[measured]**  So the three constant-application
statements of `Injectivity.lean` are now reduced to those four, at an arbitrary well-formed
environment, by way of Church–Rosser.

**What is *not* claimed:** that those four suffice for `quotReduceRec.WF`, `TrProj.uniq` or
`TrProj.weak'_inv`.  Each is a `Verify/` obligation with its own further content, none of it
inspected here.  The claim is only that the input those files named as their next step is now
available.  Do not report this as "three holes unblocked" — the previous round's brief made
exactly that mistake in the other direction and this file recorded it.

## 6. Non-vacuity

Kept in the same two halves as the quot case.

* **The conclusion is not a reflexivity, and not at one hand-picked block.**
  `patWF_iota_nontrivial` **[machine-checked]** is universally quantified over `D`, `T`, `C`,
  `j`, `q` and over the whole match: whenever the block has at least one motive and
  `|C.fields| ≠ |T.indices| + 1`, the matched term and `(D.iotaRHSOf …).apply m1 m2` have
  different *application arities*, hence are syntactically different.  So `patWF_iota` is not
  discharged by `IsDefEqU.rfl` at its own hypotheses, for any such block.
  `patWF_iota_fires` **[machine-checked]** instantiates it at the smallest block (one type,
  one constructor, no parameters/indices/fields), with the `iotaLam`-closedness side condition
  **decided** rather than assumed (a local `Decidable` instance for `VExpr.ClosedN`).
* **A full witness is still NOT constructed**, for either case.  Nothing builds a `VEnv.WF`
  environment carrying a registered rule *together with a well-typed redex*.  This round did
  **not** build the quot witness the previous handoff pointed at
  (`Verify/QuotConsts.lean`'s `trEnv_addQuot_wit` / `addQuot.WF'`): it lives in `Verify/`,
  which this stream does not own, and the ι case turned out to be the larger prize.  **"No
  witness" is not evidence of truth**; the machine-checked `Params` inhabitation witnesses in
  the tree remain `ParamsWitness.lean`'s `propLoopParams` and `Verify/Typing/Rigidity.lean`'s
  `propLoopEnv2_patWF`, both δ-only.  This is the one acceptance criterion still outstanding
  and it is the first thing a next stream should pick up.

## 7. What a next stream would pick up first

1. **The full-witness gap of §6** — `trEnv_addQuot_wit` for the quot side and an `addInduct'`-
   built environment for the ι side.  It is `Verify/`-owned work and it is the only
   outstanding acceptance criterion on this corner.
2. **Land `constAppInv_of_piInv` and friends in `Verify/Typing/`** (§5), so the reduction is
   in the tree rather than in a handoff snippet.
3. **Nothing else in this corner is open.**  `PatWF`'s three cases are δ (`patWF_delta`), ι
   (`patWF_iota`) and quot (`patWF_quot`); `paramsOfWF` derives the other nine `Params`
   fields.  The next real obstacle is the sort/Π corner itself — `forallE_inv_stratified`,
   and then `forallE_inv`, `NormalEq.descend`, `weakN_iff`.

## 8. Files

* `Lean4Lean/Theory/Typing/PatWFIota.lean` — **new**, 732 lines, no `sorry`.
* `Lean4Lean/Theory/Typing/PatternRules.lean` — one field on `Pat.iota` (§0), one argument in
  `Pat.extra_iota`.
* Everything else — **unchanged**.  `PatWF.lean`, `Pattern.lean`, `PatternDecode.lean`,
  `ParamsBuild.lean`, `ParamsWitness.lean` were not touched, and neither were the frozen files.
