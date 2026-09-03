# Handoff: `ValAt` at the parameterised nested block, unconditionally

**Written 2026-09-03.**  Complete.  (Written incrementally; sections appeared as they
were machine-checked.)

Files owned this round: `Lean4Lean/Verify/Inductive/ValAtParam.lean` (new),
`Lean4Lean/Verify/Inductive/SpineClause.lean` (prose + one statement weakening), this file.
Nothing else edited.  Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean`) not read for editing, not written, not `touch`ed.  No `git` commands.

## 0. The brief's finding, confirmed

`SpineClause.lean` §6b said of the parameterised nested block (`ntreeAux`):

> `ValAt` from it additionally needs `OnCtx ntreeAux.params.reverse (env₃.IsType 1)`, which is not
> `trivial` at this block and is **not supplied here** — that is the one hypothesis of §4 still
> open at the parameterised witness.

Confirmed stale, and in **two** independent ways, both machine-checked this round:

1. `Lean4Lean.InductiveDeclExamples.ntreeAux_params_WF`
   (`Theory/Inductive/NestedHead.lean:897`) is that premise verbatim at `env := env₃`
   (`ntreeAux.uvars = 1` literally, and `ntreeAux.params = [.sort (.succ (.param 0))]`).
   `exists.lean`: FOUND, arity 1, cone 617, own value is a hole: false, cone reaches sorryAx:
   false.
2. **Stronger, and general**: the premise is *redundant* in the consumer that has `D.WF env`.
   `VInductDecl'.WF.params` (`Theory/Inductive/Decl.lean:720`) **is**
   `OnCtx D.params.reverse (env.IsType D.uvars)` at the pre-block environment, and
   `OnCtx.mono (·.mono hle)` moves it up any `env ≤ e`.  So §4's
   `csubstTy_WF_of_spineHargsC`, which already takes `hD : D.WF env` and `hle : env ≤ e`, never
   needed `hparams` at all — for **any** block, not only this witness.  This is
   `RestrictStepCfg.params₁`'s argument (`RestrictStep.lean:110`), which existed while §6b was
   being written.

## 1. What is proved

`Lean4Lean/Verify/Inductive/ValAtParam.lean` — new, 325 lines, **13 declarations + 5 `example`s**,
13 `#print axioms` lines, **all hole-free** (`[propext]`, `[propext, Quot.sound]`, or
`+ Classical.choice`; `cone reaches sorryAx: false` for every one, checked with `exists.lean`).

| decl | arity | cone | hole-free |
|---|---|---|---|
| `VInductDecl'.WF.params_le` | 5 | 660 | yes |
| `VIndRestore.valAt_of_spineHargsC_of_wf` | 13 | 2566 | yes |
| `InductiveDeclExamples.ntreeAux_tyLvls_wf` | 6 | 755 | yes |
| **`InductiveDeclExamples.ntreeAux_valAt`** | **0** | **4015** | yes |
| `InductiveDeclExamples.ntreeAux_valAt_of_wf` | 0 | 4018 | yes |
| **`InductiveDeclExamples.ntreeAux_transport_of_clause`** | **0** | **4080** | yes |
| `InductiveDeclExamples.ntreeAux_csubstTy_WF_of_clause` | 0 | 4081 | yes |
| `InductiveDeclExamples.ntreeAux_companions` | 3 | 3509 | yes |
| **`InductiveDeclExamples.ntreeAux_spineHargsN`** | **0** | **5687** | yes |
| `InductiveDeclExamples.ntreeAux_spineHargsC_lookup` | 0 | 4016 | yes |
| `InductiveDeclExamples.ntreeAux_valAt_fires` | 0 | 4017 | yes |
| `VIndRestore.spineHargsC_iff_valStrengthen` | 9 | 3258 | yes |
| `InductiveDeclExamples.ntreeIndType` (def) | 0 | — | no axioms |

### §1 the premise, in general

`VInductDecl'.WF.params_le : D.WF env → env ≤ e → OnCtx D.params.reverse (e.IsType D.uvars)`, and
`VIndRestore.valAt_of_spineHargsC_of_wf` — `SpineClause.lean` §4's consumer with `hparams`
replaced by `D.WF env`.

### §2 the headline: `ValAt` at the parameterised block, unconditionally

`ntreeAux_valAt` (arity **0**, existentially closed):

```
∃ env₁ env₂ env₃, VEnv.empty.addInduct' listDecl = some env₁ ∧
  env₁.addIndTypes ntreeAux = some env₂ ∧ env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
  ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ ∧
  ntreeRestore.ValAt ntreeAux ntreeK env₂ env₃
```

The hypothesis §6b reported open is **gone from the statement, not moved**: it is discharged by
`ntreeAux_params_WF` at `env := env₃`.  `ntreeAux_valAt_of_wf` is the same conclusion with
`ntreeAux_WF'` in place of the witness-specific `ntreeAux_params_WF`, i.e. through §1's general
route.

### §3 what that unlocks

`ntreeAux_transport_of_clause` (arity 0) delivers, at one block / one restoration / one staging:
the checker-side clause, `ValAt`, `(ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ 1`, and the
datum `ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc)`.

**Honest reading of the `WF` conjunct.**  Its *conclusion* was already available at this witness —
`ntreeSubst_WF` (`Theory/Typing/ConstSubstNested.lean:909`) plus `ntree_csubstTy` gives it — so the
new thing is the **route**, not the fact: `csubstTy_WF_of_val` from the clause, rather than
`type_tac` on the concrete spine.  That is the thing `RestrictCompanion.lean` §8 flags in its own
prose ("**Not a route.** … Two witnesses with the transport are still two witnesses").  Recorded as
a statement about provenance, not as a new theorem about `ntreeSubst`.

### §4 the `TrIndDeclN` field text at the parameterised block

`ntreeAux_spineHargsN` — `SpineHargsN` in `TrIndDeclN`'s own guard style (`types.length ≤ j`),
staged over the `addIndTypesC` premise the way `trCtors` is, at `[ntreeIndType]`.
`SpineClause.lean` §6a had this only at the **degenerate** block (`nfnAux_spineHargsN`); this is the
`uvars = 1`, non-empty-telescope one.  `ntreeIndType` is spliced from the real Lean `NTree`
constant with `exprOf%`, as `nfnIndType` is, so it cannot drift.

### §5 vacuity watch (see §3 of this handoff for the audit)

### §6 where the general statement bottoms out

`VIndRestore.spineHargsC_iff_valStrengthen` (general, arity 9): at a `RestrictStepCfg` with the
datum at `e₂`,

```
R.SpineHargsC D K env e₁  ↔  R.ValStrengthen D K e₂ e₁
```

so the **checker-side** clause is also exactly on `RestrictStep.lean` §2's cycle, hence exactly the
strengthening instance and no cheaper than it.  `RestrictStep.lean` proved this for the `occ`-form
`SpineHargsK`; this is the form `TrIndDeclN` can carry.

**The hole, named precisely.**  `RestrictStep.lean`'s `valStrengthen_endpoints_clean` makes node 5
a *plain* instance of `VEnv.AxiomConservativityWF` (`Theory/Typing/ConstVar.lean`), which
`VEnv.axiomConservativityWF_iff_target` proves equivalent to `VEnv.StrengtheningTarget`
(`Theory/Typing/Strengthen.lean`), which is the **forward direction of
`Lean4Lean.VEnv.IsDefEqU.weakN_iff`** — the `sorry` at `Theory/Typing/UniqueTyping.lean:193`
(declaration reported at `UniqueTyping.lean:191`).  I stopped there and did not attempt it.

## 2. The prose corrected in `SpineClause.lean`

Two edits, both mine, no restructuring:

1. **§6b, the stale paragraph.**  The sentence

   > `ValAt` from it additionally needs `OnCtx ntreeAux.params.reverse (env₃.IsType 1)`, which is
   > not `trivial` at this block and is **not supplied here** — that is the one hypothesis of §4
   > still open at the parameterised witness.

   is replaced by a "**Correction (2026-09-03)**" block that quotes the old claim, says it was
   wrong on both counts, names `InductiveDeclExamples.ntreeAux_params_WF`
   (`Theory/Inductive/NestedHead.lean`) as the premise verbatim at `env := env₃`, states the
   general redundancy from `VInductDecl'.WF.params` + `OnCtx.mono`, and points at
   `ValAtParam.lean` §1/§2/§3.  The old claim is quoted rather than deleted, so the defect stays
   on the page.

2. **§4's `csubstTy_WF_of_spineHargsC` weakened**: `hparams` removed (arity 19 → **18**), derived
   inline as `OnCtx.mono (fun h => h.mono hle) hD.params` from the `hD : D.WF env` and
   `hle : env ≤ e` the theorem already took.  Axioms `[propext, Quot.sound]`, cone 3175 → 3176
   (the one added constant is `OnCtx.mono`), hole-free.  `after ⊆ before` holds: the axiom set is
   unchanged and is the minimum `csubstTy_WF_of_val` already carries.  Nothing in the tree used
   the dropped hypothesis (`csubstTy_WF_of_spineHargsC` has no callers), so no other file changed.
   `valAt_of_spineHargsC` keeps `hparams` — it takes no `D.WF`, so there the premise is real.

## 3. Vacuity watch — this is the non-degenerate block, checked by instantiation

`docs/handoff-valat.md` §4 records the sibling `nfnAux` as degenerate (`uvars = 0`, `params = []`,
context hypotheses `trivial`).  §5 of my file checks by computation that the witness used here is
**not** that one, and that the two premises which could make §2 inert have witnesses:

* `ntreeAux.uvars = 1` (`rfl`) — so `IsType 1`, not `IsType 0`;
* `ntreeAux.params = [.sort (.succ (.param 0))]` (`rfl`) — telescope **non-empty**, so
  `ntreeAux_params_WF` is `⟨trivial, _, .sort _⟩`, not `trivial`;
* `ntreeRestore.tyArgs 1 = [.app (.const ``NTree [.param 0]) (.bvar 0)]` (`rfl`) — the spine is
  **parameter-dependent** (`#0` is the block's own bound parameter), so the `HasArgs` is a genuine
  `.cons` against a one-binder telescope, not `.nil`;
* `ntreeK = [`_nested.List_1]` (`rfl`) — non-empty, so `SpineClause.lean` §6's collapse test does
  not apply;
* `nfnAux.uvars = 0 ∧ nfnAux.params = []` (`rfl`) — the contrast, recorded so the reader can see
  the witness did not silently degenerate to it;
* `ntreeAux_spineHargsC_lookup` — the clause's `∀ ci` premise fires: `env₁` really declares the
  presented head `List` at `⟨listOcc.decl.uvars, listOcc.src.type⟩`;
* `ntreeAux_valAt_fires` — `ValAt` is a `∀` over `csubstTy`'s domain, and it is applied at a real
  point: `_nested.List_1 ↦ ntreeVal`, declared at `env₂` as `Type u → Type u`, and §2's `ValAt`
  produces `env₃.HasType 1 [] ntreeVal (Type u → Type u)`.  So `ntreeAux_valAt` moves a real
  judgement, not an empty family.

No statement in the file is true merely because an upstream hypothesis is unsatisfiable: every
theorem with hypotheses is instantiated at this witness with those hypotheses discharged, and the
two arity-0 headlines have none.

## 4. Verification record

* `lake build Lean4Lean.Verify.Inductive.ValAtParam`: exit 0, 202 jobs, **zero `error:`, zero
  warnings from my files** (checked by grepping the full-build log for `ValAtParam.lean` and
  `SpineClause.lean` warning lines — none).
* `lake build` (whole tree): **one failing module, `Lean4Lean.Verify.Inductive.FlipConstruct`**,
  16 errors, **not mine** — a file another stream created during this session (mtime 18:10, not
  present when I started).  It imports only `Verify.Environment.InductR` and
  `Theory.Inductive.NestedTele`, references neither `csubstTy_WF_of_spineHargsC` nor anything I
  touched, and its errors are field-notation/`cases` failures on `AddInductStagesR` / `ConstMap`.
  `SpineClause.lean` is imported by exactly one file in the tree (`ValAtParam.lean`), and both
  build.  Reported rather than fixed: it is not my file.
* `lake env lean --run scripts/exists.lean` on all 13 new names plus the weakened
  `csubstTy_WF_of_spineHargsC`: all FOUND, `own value is a hole: false`,
  `cone reaches sorryAx: false`.
* `scripts/sorry-census-all.lean`: **13 holes**, unchanged; `BUILT: 419`; `in population but NOT
  BUILT: 1` — that one is `FlipConstruct`, the other stream's broken file.
* `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone".
* Guards (`lake build Lean4Lean.Verify.Guard`): `guard 1 ✓ (24 frozen axioms)`,
  `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx present, unchanged)`, `guard 3 ✓ (2/2)`.
* `grep of_mkApp` in my two files: 3 hits, **all prose**.  The corner stays `PiInv`-free.
* `#print axioms` names read off the file's own `namespace` lines, never composed from the path.
* Frozen files untouched.  `docs/vacuity-ledger.md` untouched.  No `git` commands of any kind.
* Files read but never edited: `RestrictCompanion.lean`, `RestrictStep.lean`, `ValAtPrice.lean`,
  `ArgsTypedSupply.lean`, `NestedHead.lean`, `NestedBuild.lean`, `Decl.lean`,
  `ConstSubstNested.lean`, `InductR.lean`, `UniqueTyping.lean`, `docs/handoff-valat.md`.

### 4a. Measured vs read off

**Measured this session:** every axiom line per declaration from the compiler; that
`ntreeAux_params_WF` has the premise's exact statement and `ntreeAux.uvars = 1` by `rfl`; the
arity/cone numbers via `exists.lean`; that `csubstTy_WF_of_spineHargsC` has no callers (grep over
`Lean4Lean/`); the census, dup-names, guards; that `FlipConstruct.lean` does not reference anything
I changed.

**Read off source, not independently re-proved:** that `ntreeSubst_WF`'s `val` clause is a
`type_tac` hand discharge (from `RestrictCompanion.lean` §8's prose and
`ConstSubstNested.lean:909`'s proof text); that `VEnv.axiomConservativityWF_iff_target` is the
equivalence to `StrengtheningTarget` (from `RestrictCompanion.lean` §4's prose — I used neither);
that `VEnv.HasArgs.of_mkApp` is `sorryAx`-tainted.

## 5. Pick up first

1. **The general clause is still open, and it is the hole.**  §6's
   `spineHargsC_iff_valStrengthen` says the checker-side clause *is* the strengthening instance, so
   do **not** look for a cheaper door on that cycle — `RestrictStep.lean` §2 already closed that
   question for the `occ`-form and this closes it for the checker-side form.  The open question
   `RestrictStep.lean` §2 names as "the next worth asking" is unchanged: **is the instance family
   strictly weaker than `VEnv.StrengtheningTarget`?**  Both tree witnesses discharge instances of
   it with no hole, so it is not obviously equivalent pointwise.
2. **`ntreeAux_spineHargsN` is the producer side of the `TrIndDeclN` field at the parameterised
   block.**  The flip itself (adding the field) is still not made; `docs/handoff-spineclause.md`
   §4 is the measured ripple.
3. **A note for whoever owns `SpineClause.lean` next**: the pattern that produced §6b's error is
   worth naming — the paragraph asserted a premise "not supplied here" from the *local* file's
   point of view and the reader took it as "not available anywhere".  Both readings were false
   here.  Prefer "not used in this file; see X" over "not supplied".
4. **Unchanged prohibitions**: do not close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF`
   (`docs/vacuity-ledger.md` row 197), do not use `HasArgs.of_mkApp` in this corner, do not touch
   the frozen files.
