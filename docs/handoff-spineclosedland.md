# Handoff: SpineClosedLand — making `SpineClosedC` a `TrIndDeclN` field

Round start: 2026-09-03T21:19:34+02:00 (agent: spineclosedland)

## Section 1 — Brief as received (written before any Lean interaction)

Task: the nested-flip's last leaf costs **one spec clause**. The clause is

- `Lean4Lean.VIndRestore.SpineClosedC` (`Lean4Lean/Verify/Inductive/HargsAttack.lean`),
  claimed arity 3, cone 571, hole-free, over `R`, `D`, `K` only — no `occ`, no `npJ`,
  no environment, no staging premise.

Four premises to re-verify BEFORE any structural change (stop and report if any fails):
1. `Lean4Lean.VIndRestore.SpineClosedC` — statable in `InductR.lean` scope (arity 3, cone 571, hole-free).
2. `Lean4Lean.VIndRestore.exists_spineClosedC` (cone 582) — proves the *existential* form VACUOUS,
   hence the clause must be a field, not existentially closed.
3. `Lean4Lean.VIndRestore.spineClosedC_of_spineHargsC` — free at the datum.
4. `Lean4Lean.VIndRestore.not_spineHargsC_of_not_spineClosedC` (arity 10, cone 990) — necessity.

Steps: (a) timestamped enumeration of every `TrIndDeclN` construction site; (b) add the field and
supply it everywhere (a site that cannot supply it is a real finding); (c) derive
`Lean4Lean.VIndRestore.HargsAt` where previously assumed, and say exactly which flip obligations
are discharged; (d) arity-0 witness at `Lean4Lean.InductiveDeclExamples.ntreeAux`
(`Theory/Inductive/NestedHead.lean:624`, uvars = 1, params = `[.sort (.succ (.param 0))]`),
via general theorems not a block-specific lemma; `nfnAux` is degenerate and must not be the witness;
(e) hole discipline — forbidden: `Lean4Lean.VEnv.HasArgs.of_mkApp`, `Lean4Lean.VEnv.IsDefEq.uniq`,
`Lean4Lean.VEnv.AxiomConservativityWF`; record reasons at the statement;
(f) round-close: whole-tree `lake build` green, `scripts/sorry-census-all.lean` = 13 / NOT BUILT 0,
three guards pass, zero in-repo section-variable warnings.

Ownership: `Lean4Lean/Verify/Environment/InductR.lean`, `Lean4Lean/Verify/Inductive/SpineClosedLand.lean` (new),
this file (new), plus any file that fails to compile *solely* because of the new field — and there only to
supply the field at a construction site.

FROZEN, never edited by me: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

## Section 2 — Premise verification (2026-09-03T21:22:00+02:00, `scripts/exists.lean`, population 433 built modules)

All four hold. Verbatim from `scripts/exists.lean`:

| name (exactly as printed) | module | arity | cone | hole | sorryAx in cone |
|---|---|---|---|---|---|
| `Lean4Lean.VIndRestore.SpineClosedC` | `Lean4Lean.Verify.Inductive.HargsAttack` | 3 | 571 | false | false |
| `Lean4Lean.VIndRestore.exists_spineClosedC` | same | **2** | 582 | false | false |
| `Lean4Lean.VIndRestore.spineClosedC_of_spineHargsC` | same | 10 | **989** | false | false |
| `Lean4Lean.VIndRestore.not_spineHargsC_of_not_spineClosedC` | same | 10 | 990 | false | false |

Brief's figures corrected: `exists_spineClosedC` has arity **2** (not 3), and
`spineClosedC_of_spineHargsC` cone **989**. `SpineClosedC` arity 3 / cone 571 confirmed exactly.

Statements read (not trusted from prose):
- `SpineClosedC R D K := ∀ j T, D.types[j]? = some T → T.name ∈ K → ∀ a ∈ R.tyArgs j, a.ClosedN D.np`
  — over `R`, `D`, `K` only, confirmed by reading `HargsAttack.lean:379-381`.
- `exists_spineClosedC : ∃ R, R.SpineClosedC D K`, witnessed by the empty presentation. Vacuous: confirmed.
- `spineClosedC_of_spineHargsC` : free at the datum. Confirmed.
- `not_spineHargsC_of_not_spineClosedC` : necessity. Confirmed (it is the contrapositive of the above).

Also confirmed forbidden-hole status: `Lean4Lean.VEnv.HasArgs.of_mkApp` **does** reach `sorryAx`
(holes: `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified`, `Lean4Lean.VEnv.WF.rigidShapeUniqNS`),
so the ban is real, not stylistic.

## Section 3 — THE HEADLINE: the brief's clause is the wrong one

`SpineClosedC` is **necessary** for `hargs` and **free from** `hargs`. Neither makes it
**sufficient**. `HargsAt` is a `VEnv.HasArgs` — a *typing* judgement on each spine argument;
`SpineClosedC` is a *scope* condition. Adding `SpineClosedC` as a `TrIndDeclN` field therefore
CANNOT discharge `hargs`, and no amount of other `TrIndDeclN` data closes the gap without
`VEnv.HasArgs.of_mkApp` (banned, and tainted).

`HargsAttack.lean` §4 itself says this, and the brief misread it:

> **And it is free.** §2 proves `SpineHargsC → SpineClosedC`. So if the flip takes
> `SpineClause.lean` §4's measured `trSpine` field, the scope clause is *not* a second clause:
> the flip's price stays **one**.

i.e. the one clause the flip pays for is the **datum** (`VIndRestore.SpineHargsN`,
`Verify/Inductive/SpineClause.lean` §5 — already written as the field text), and `SpineClosedC`
is a *corollary* of it, not the field. `SpineClosedC`-as-field is strictly dominated: it costs
producers a clause and buys only `hcl`, which the datum field buys anyway.

Decision: add the **datum** field, prove the separation that shows why the scope clause alone
would not have done, and derive both `HargsAt` and `SpineClosedC` from the field.

## Section 4 — Construction-site census

Measured 2026-09-03T21:26:00+02:00, `lean_references` on `TrIndDeclN`
(`Lean4Lean/Verify/Environment/InductR.lean:276:11`) **plus** grep for every other build form
(`TrIndDeclN.mk`, `{ _ with _ }`, `… where$`).

**`total` = 17 references. Construction sites = 3.** Exactly three places build a `TrIndDeclN`
value; every other producer in the tree routes through one of them.

| # | name as `scripts/exists.lean` prints it | file:line of the `where` | can it supply the datum field? |
|---|---|---|---|
| 1 | `Lean4Lean.TrIndDecl.toN` | `/home/vasilii/lean4lean/Lean4Lean/Verify/Environment/InductR.lean:393` | **yes, vacuously** — `K = []`, `numNested = 0`, so `types.length ≤ j` contradicts `D.types[j]? = some T` |
| 2 | `Lean4Lean.NestedWit.trIndDeclN_wit` | `/home/vasilii/lean4lean/Lean4Lean/Verify/Environment/InductR.lean:871` | **yes** — from `hPFn` + `VEnv.addConstList_constants` |
| 3 | `Lean4Lean.NestedWit.trIndDeclN_wit'` | `/home/vasilii/lean4lean/Lean4Lean/Verify/Inductive/NestedRestoreWit.lean:457` | **yes** — same, at `nfnRestore'` |

Indirect producers (they build a `TrIndDeclN` only through the three above, so they need no edit):
`Lean4Lean.TrIndDeclNCtorOwn.trIndDeclN_eq` (via `.toN`),
`memIndDeclNamesN_sat`, `notAddInductStagesR_sat`, `trIndDeclN_wit_without_pfnMk`,
`memIndDeclNamesN_sat_without_pfnMk` (all via `trIndDeclN_wit`),
and the two `InductStepNested` producers `Lean4Lean/Verify/Inductive/RunIdentity.lean:1290`
and `Lean4Lean/Verify/Inductive/AddInductiveStep.lean:429` (both `htr.toN`).

Consumers (`TrIndDeclN` in a hypothesis or a `def`'s conjunct — unaffected by a new field except
that they gain data): `InductR.lean:331, 439, 491, 659`; `RestoreFaithful.lean:241`;
`NestedOccData.lean:908`; `TrIndDeclNCtorOwn.lean:261, 283`.

There is **no general nested producer** of `TrIndDeclN` anywhere in the tree: at `numNested > 0`
the only producers are the two `NFn`/`PFn` witnesses. That is why the field's cost is two concrete
proofs and one vacuity, and why the census is stable under this change.

## Section 5 — Edits made (three files, one of them new; nothing else in the tree needed touching)

1. **`/home/vasilii/lean4lean/Lean4Lean/Verify/Environment/InductR.lean`** (owned) — added the field
   `TrIndDeclN.trSpine` (with its docstring, including the reason it is the datum and not the scope
   clause), and supplied it at the two construction sites this file holds:
   `TrIndDecl.toN` (5 lines, vacuous) and `NestedWit.trIndDeclN_wit` (7 lines).
2. **`/home/vasilii/lean4lean/Lean4Lean/Verify/Inductive/NestedRestoreWit.lean`** (touched *only* to
   supply the new field at `NestedWit.trIndDeclN_wit'` — the same 7 lines; no other change).
3. **`/home/vasilii/lean4lean/Lean4Lean/Verify/Inductive/SpineClosedLand.lean`** (new, owned).
4. **`/home/vasilii/lean4lean/docs/handoff-spineclosedland.md`** (this file, new, owned).

FROZEN files untouched — `git diff --stat` on `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` is empty. (`Guard.lean`'s mtime was `touch`ed twice to force the guards to
re-run; content byte-identical, `git status` clean for it.)

### The field text as landed

```
  trSpine : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        env₁.HasArgs D.uvars D.params.reverse
          (VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j)
```

`VIndRestore.declTele` is an `abbrev`, so this term *is* `VIndRestore.SpineHargsN R D K env types`
and `TrIndDeclN.spineHargsN` is `h.trSpine` with no bridge.

### The two nested sites' proof, verbatim (identical at both restorations)

```
  trSpine := by
    rintro env₁ hst (_ | _ | j) T hT hle ci hci
    · simp at hle
    · cases hT
      cases Option.some.inj (hci.symm.trans hPFn)
      show env₁.HasArgs 0 [] [VExpr.sort (.succ .zero)] [VExpr.const ``NFn []]
      refine .cons (.const (ci := ⟨0, .sort (.succ .zero)⟩) ?_ nofun rfl) .nil
      exact VEnv.addConstList_constants hst (``NFn, ⟨0, .sort (.succ .zero)⟩)
        (by exact List.Mem.head _)
    · simp [nfnAux] at hT
```

No site failed to supply the field.

## Section 6 — What the field buys, and what remains of the flip

Bought (all hole-free, all in `SpineClosedLand.lean`, none reaching the three banned declarations):

| declaration | what it discharges |
|---|---|
| `Lean4Lean.TrIndDeclN.spineHargsN` | the field, under `SpineClause.lean` §5's name |
| `Lean4Lean.TrIndDeclN.spineHargsC` | the checker-side clause at `(env, env₁)` |
| `Lean4Lean.TrIndDeclN.hargsAt` | **`hargs` per companion member — the leaf** |
| `Lean4Lean.TrIndDeclN.spineClosedC` | the scope clause, as a *corollary*, not a field |
| `Lean4Lean.TrIndDeclN.csubstTy_closed` | `(R.csubstTy D K).Closed`, carried separately at 8 sites |
| `Lean4Lean.TrIndDeclN.csubstTy_WF` | the whole nested transport `(R.csubstTy D K).WF` |
| `Lean4Lean.TrIndDeclN.tyVal_hasType` | §8.7's `val` obligation (`Faithful` still explicit) |
| `Lean4Lean.InductStepNested.spineHargsC` | **the step predicate now implies `hargs`** |

Remains of the flip (unchanged by this round, and none of it is `hargs`):

* a **general producer** of `trSpine` at `numNested > 0`. Only the two `NFn`/`PFn` witnesses supply
  it, plus `ntreeAux` for the clause text alone. `ValAtParam.lean` §6 measures where the general one
  bottoms out: `VEnv.AxiomConservativityWF`, equivalently the forward direction of
  `VEnv.IsDefEqU.weakN_iff`, the `sorry` at `Theory/Typing/UniqueTyping.lean:193`.
* `D.Built R K env occ`, `(R.csubstTy D K).FreshIn env` and the `tyLvls` well-formedness, which
  `InductStepNested` does not carry — `RestoreData`/`OccResidue` business.
* `R.Faithful` for `tyVal_hasType` — `RestoreFaithful.lean`'s job, not a `TrIndDeclN` field.

## Section 7 — Round-close numbers (2026-09-03, final)

* whole-tree `lake build`: **green, 1621 jobs** (was 1620; +1 = the new module).
* `scripts/sorry-census-all.lean`: **BUILT 438; NOT BUILT 0; HOLES 13.** Unchanged in both
  directions.
* guard 1: `Axioms.lean` declares exactly the **24** frozen axioms ✓
* guard 2: `kernel_sound` axioms within whitelist ✓ (proof INCOMPLETE: `sorryAx` present — the
  standing state, not a regression)
* guard 3: checker cone implementation gaps within frozen list (**2/2** remaining) ✓
* in-repo section-variable warnings: **zero**. The only `unusedSectionVars` warning in the build is
  `Foundation/FirstOrder/SetTheory/Z.lean:35` — the pinned dependency, not this repo.
* every new declaration: `own value is a hole: false`, `cone reaches sorryAx: false`
  (18 names, `scripts/exists.lean`).
* banned declarations (`Lean4Lean.VEnv.HasArgs.of_mkApp`, `Lean4Lean.VEnv.IsDefEq.uniq`,
  `Lean4Lean.VEnv.AxiomConservativityWF`): all four names (incl. `of_mkApp'`) resolve to real
  constants, and **none appears in the cone of any of the 17 new declarations nor of the three
  construction sites**.
* axiom bar: every new declaration uses only `propext`, `Classical.choice`, `Quot.sound`;
  `after ⊆ before` holds and guard 1's count is unmoved.

### Concurrency note

Another stream landed `Lean4Lean/Theory/Typing/EtaGuardLand.lean` +
`docs/handoff-etaguardland.md` during this round, and the modifications that were in
`git status` at round start (`Theory/SetModel/CnstRecursion.lean`,
`Theory/SetModel/InductOracleAudit.lean`, `Theory/Inductive/NestedRules.lean`,
`Theory/SetModel/InaccChainOmega.lean`) were committed by someone else mid-round. The module
population therefore moved 433 → 438 across this round's `exists.lean` runs; the census figure
(13 / NOT BUILT 0) is from the **final** state and is the one to trust.

