# handoff — `trSpine` producer at `numNested > 0`

Round owner files: `Lean4Lean/Verify/Inductive/TrSpineProducer.lean` (new), this file (new).
Everything else read-only. `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`
FROZEN — not edited, not to be edited.

## §0 — Brief as received (unverified figures, to be re-measured)

The flip's last remaining item. A field `TrIndDeclN.trSpine` was added to the translation
relation; it discharged the datum three obligations bottomed out in:

- `Lean4Lean.TrIndDeclN.hargsAt` — claimed arity 18, cone 835, hole-free — yields `hargs`
  per companion member from the relation.
- `Lean4Lean.InductStepNested.spineHargsC` — claimed arity 9, cone 2775, hole-free — makes
  the nested step predicate imply it.

What remains: a **general producer of `trSpine` at `numNested > 0`**. All three existing
construction sites of `TrIndDeclN` supply the field, but two are concrete witnesses and one is
the non-nested `Lean4Lean.TrIndDecl.toN`; there is claimed to be no general nested producer.

`Verify/Inductive/ValAtParam.lean` §6 reportedly measures the producer as bottoming out at
`Lean4Lean.VEnv.AxiomConservativityWF` ≡ forward direction of
`Lean4Lean.VEnv.IsDefEqU.weakN_iff`, the `sorry` at `Theory/Typing/UniqueTyping.lean:193`.
**To verify, not assume.**

### THE OPEN QUESTION (genuinely open per the brief)

A bypass landed earlier today: `Lean4Lean.VIndRestore.argsTypedK_of_succLevel`
(`Verify/Inductive/StrengthenFamily.lean`, claimed arity 13, cone 3335, hole-free) discharges
the strengthening family without `weakN_iff`, for blocks whose result level is a successor,
plus a companion clause for zero. Mechanism: reduce to the **uninhabited** axiom case
(`Lean4Lean.VEnv.axiomConservativityWF_iff_uninhabWF`) then substitute *any inhabitant*.

Does that bypass cover the `trSpine` producer, or is it silent on it?

**Cheap test, established when the same bypass was silent (not weak) for two neighbouring
obligations: is the value in question PINNED?** The bypass buys exactly the freedom to *choose*
an inhabitant; it buys nothing where the value is determined (there, `WFD.val` pinned it to
specific constructor/recursor values) or where the type is empty.

Also: the bypass's own residue needs a `Sort u`-valued constant in the environment
(`Lean4Lean.VEnv.SortWitness`), which is **refuted** at the environment this corner runs at —
check whether that bites here.

### Constraints
- Forbidden: `Lean4Lean.VEnv.HasArgs.of_mkApp` (reaches `sorryAx` via two holes),
  `Lean4Lean.VEnv.IsDefEq.uniq`, `Lean4Lean.VEnv.AxiomConservativityWF`.
- Arity-0 existentially-closed witness at `Lean4Lean.InductiveDeclExamples.ntreeAux`
  (`Theory/Inductive/NestedHead.lean:624`, `uvars = 1`, `params = [.sort (.succ (.param 0))]`),
  via general theorems not block-specific lemmas. `nfnAux` is degenerate — must not become it.
- Round-close: whole-tree `lake build` green, census **13 / NOT BUILT 0**, three guards, zero
  in-repo section-variable warnings.

## §1 — Findings log (appended live)

(populated below as measurements land)

### Pre-flight (re-measured myself, 2026-09-03, population 435 built modules)

| name | arity | cone | hole |
|---|---|---|---|
| `Lean4Lean.TrIndDeclN.trSpine` | 18 | **826** | no |
| `Lean4Lean.TrIndDeclN.hargsAt` | 18 | 835 | no |
| `Lean4Lean.InductStepNested.spineHargsC` | 9 | 2775 | no |
| `Lean4Lean.TrIndDecl.toN` | 8 | 1932 | no |
| `Lean4Lean.VIndRestore.argsTypedK_of_succLevel` | 13 | 3335 | no |
| `Lean4Lean.VEnv.axiomConservativityWF_iff_uninhabWF` | 3 | 3538 | no |
| `Lean4Lean.VEnv.SortWitness` | 1 | 19 | no |
| `Lean4Lean.VEnv.AxiomConservativityWF` | 2 | 362 | no |
| `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | 11 | 3231 | **YES** |
| `Lean4Lean.InductiveDeclExamples.ntreeAux` | 0 | 43 | no |

Brief's figures correct except `trSpine`'s own cone, which the brief did not give (835 is
`hargsAt`'s; `trSpine` is 826).

### §6 measurement of `ValAtParam.lean` — VERIFIED, and it is an `↔`

`Lean4Lean.VIndRestore.spineHargsC_iff_valStrengthen` (arity 9, cone 3258, hole-free) reads

    RestrictStepCfg D R K env e₂ e₁ occ → D.ArgsTypedK K e₂ occ →
      (R.SpineHargsC D K env e₁ ↔ R.ValStrengthen D K e₂ e₁)

so the producer really is *on* the cycle whose entry `restrictStep_entry` locates at
`AxiomConservativityWF`. The brief's reading of §6 is right.

## §2 — THE PINNED-VALUE VERDICT: **NOT PINNED. The bypass covers the producer.**

`trSpine` = `VIndRestore.SpineHargsN` (definitionally: `SpineClosedLand.lean:163` is
`h.trSpine` with no bridge, `declTele` being an `abbrev`). Its content is a
`VEnv.HasArgs D.uvars D.params.reverse (declTele ci …) (R.tyArgs j)` — a **typing of the
presented spine**. It mentions `R` only through `tyName`/`tyLvls`/`tyArgs`, and mentions **no
`CSubst`, no `R.tyVal`, no `R.ctorVal`, no `R.recVal`, and no `csubstTy`**. There is therefore no
value for `WFD.val` (rows 235/235b's pinning mechanism) to fix, and the type is not empty
(`ntreeAux_spineHargsN` already inhabits it).

The verdict is not prose: the producer below is quantified over **an arbitrary inhabitant**
`b : VIndType → VExpr` of the result sort, so the freedom the bypass buys is *in the statement*,
and the witness runs it at a `b` whose value is provably **≠** the intended `ntreeVal`
(`ntree_junkVal_ne_tyVal`, in-tree, cone 799).

The `SortWitness` refutation does **not** bite: it is a premise of the *fourth* clause
(`resultSortInhab_of_const`) only. `ntreeAux.lvl = .succ (.param 0)`, so the **successor** clause
`resultSortInhab_of_succ` (arity 6, cone 606, hole-free) fires with level side conditions alone
and no environment condition at all.

## §3 — WHAT WAS PRODUCED

New file `Lean4Lean/Verify/Inductive/TrSpineProducer.lean` (330 lines), imports
`StrengthenFamily` + `ValAtParam` + `SpineClosedLand`. All measured by `scripts/exists.lean`,
population 437 built modules; **every one hole-free** (`cone reaches sorryAx: false`).

| name | arity | cone | axioms |
|---|---|---|---|
| `Lean4Lean.VIndRestore.spineHargsC_of_resultSortInhab` | 11 | 3340 | `[propext, Quot.sound]` |
| `Lean4Lean.VIndRestore.spineHargsN_of_resultSortInhab` | 13 | 3344 | `[propext, Quot.sound]` |
| `Lean4Lean.VIndRestore.trSpine_of_resultSortInhab` | 21 | 3345 | `[propext, Quot.sound]` |
| `Lean4Lean.VIndRestore.spineHargsN_of_succLevel` | 15 | 3346 | `[propext, Quot.sound]` |
| `Lean4Lean.VIndRestore.spineHargsN_of_zeroLevel` | 13 | 3346 | `[propext, Quot.sound]` |
| `Lean4Lean.VIndRestore.spineHargsN_iff_valStrengthen` | 11 | 3263 | `[propext, Quot.sound]` |
| `Lean4Lean.trIndDeclN_of_succLevel` | 20 | 3348 | `+ Classical.choice` |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine` | **0** | 5834 | `+ Classical.choice` |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_not_pinned` | **0** | 5837 | `+ Classical.choice` |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_iff_valStrengthen` | **0** | 5765 | `+ Classical.choice` |

The route, three composed hole-free arrows already in the tree:

    ResultSortInhab --argsTypedK_of_resultSortInhab--> ArgsTypedK K e₁ occ   (the bypass)
                    --cyc_datum_to_spine-->           SpineHargsK K e₁ occ
                    --SpineHargsC.of_spineHargsK-->   SpineHargsC D K env e₁
                    --spineHargsN_of_spineHargsC-->   SpineHargsN = the trSpine field

`b : VIndType → VExpr` is universally quantified in `spineHargsN_of_resultSortInhab` — that is the
not-pinned verdict *as a statement*. `trSpine_of_resultSortInhab` states the conclusion as
`InductR.lean` spells the field (`VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1`)
and needs no rewriting, which is the machine check that it is the field text.

## §4 — WHAT REMAINS OF THE PRODUCER (residue, stated at §4 of the Lean file)

1. **`ResultSortInhab`** — sufficient, four clauses. Residue: `D.lvl = .param i`, no telescope
   binder at that level, environment with no `Sort u`-valued constant (that last conjunct is live —
   `SortWitEnv.lean` refutes it here). For such a block §2's `↔` says the cost is exactly the
   strengthening instance, i.e. `weakN_iff`.
2. **`D.ArgsTypedK K e₂ occ`** (datum at `e₂`) — a premise. `RestrictStep.lean` §4(c):
   `D.WF` + `stage₂` is where it comes from, general extraction is
   `VInductDecl'.WF.recField_canonResult`, but the last step to `ArgsTypedH` is per-occurrence
   telescope arithmetic and exists only at the two witnesses.

**Not circular** (cited, not asserted): `RestrictStep.lean` §4(b) audits the nine `RestrictStepCfg`
fields and finds none is a typing at `e₁`.

## §5 — ROUND-CLOSE

* `lake build` whole tree: **green, 1623 jobs**, exit 0.
* Census (`scripts/sorry-census-all.lean`): **13 holes**, on disk 464, population 440,
  **BUILT 440 / NOT BUILT 0**, three runs identical.
* Guards: 1 ✓ (exactly the 24 frozen axioms), 2 ✓ (`kernel_sound` axioms within whitelist,
  proof INCOMPLETE), 3 ✓ (2/2 remaining).
* In-repo `unused section variable` warnings: **0**. The separate
  "Variable name … is not explicitly referenced" class: **66 in `Lean4Lean/`**, unchanged from row
  230d's baseline; **0 of them in the new file**, and 0 warnings of any kind in the new file.
* Frozen files: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` **not touched** —
  empty `git diff`, md5 `570efe63b2a7c567e25b6b89b4057690` / `513849e172cd4a5da9e3db2ce2eff7f3` /
  `006f49ce5b64d7e8d9bf80db50a17a4a`.
* Axiom bar `after ⊆ before`: no existing declaration was edited; only additions.

**Observed and resolved, worth reporting**: my *first* census run reported `BUILT 439 / NOT BUILT 1`.
Cause is a concurrent stream, not this round — `Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean`
appeared untracked mid-round and had no `.olean` until my whole-tree build produced one. It is the
exact blindness `sorry-census-all.lean` was written to expose, caught live.

## §6 — Forbidden-name check, run rather than assumed

Transitive cone membership test (type + value closure, `allowOpaque := true`) over all ten new
declarations, for `VEnv.HasArgs.of_mkApp`, `VEnv.IsDefEq.uniq`, `VEnv.AxiomConservativityWF`,
`VEnv.IsDefEqU.weakN_iff`, `VEnv.StrengtheningTarget`, `VEnv.SortWitness`, `VEnv.IsDefEq.uniqU`,
`VEnv.IsDefEqU.forallE_inv_stratified`, `sorryAx`:

**forbidden hits `[]` for every one of the ten.** Worth noting explicitly that
`AxiomConservativityWF` is itself `sorryAx`-free (cone 362), so hole-freeness alone would not have
ruled it out — this test does.
