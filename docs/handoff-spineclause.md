# Handoff: the checker-side spine clause — `SpineHargsK` is the right *content* and the wrong *form*

**Written 2026-09-03.**  Written incrementally from the first finding, per the standing rule.

## 0. Status while in progress

Baseline measured before any edit: `lake build` **1595 jobs, exit 0**, `grep -c "automatically
included section variable"` = **1** (and it is `Foundation/FirstOrder/SetTheory/Z.lean`, upstream —
**0** from Lean4Lean).  `scripts/sorry-census-all.lean`: **13 holes**, `BUILT: 412`, `in population
but NOT BUILT: 0`.

## 1. Findings so far (in order found)

### F1. `SpineHargsK` cannot be stated on `TrIndDeclN` — two independent reasons

`TrIndDeclN` lives in `Lean4Lean/Verify/Environment/InductR.lean:276`.

1. **Layering.**  `VInductDecl'.SpineHargsK` is *defined* in
   `Lean4Lean/Verify/Inductive/ValAtPrice.lean:184`, which is **downstream** of `InductR.lean`:
   `ValAtPrice → RestrictCompanion → ArgsTypedSupply → NestedOccData → NestedRestoreWit →
   NestedRestore → Verify/Environment/InductR`.  So `InductR.lean` cannot *name* `SpineHargsK`.
   Its body is pure `Theory` vocabulary (`VEnv.HasArgs`, `VExpr.splitPis`, `VNestedOcc`), so the
   predicate could be re-declared upstream — but that is a second declaration of the same
   statement, which `scripts/dup-names.lean` is there to catch.
2. **`occ` is not a parameter of `TrIndDeclN`, and existentialising it is vacuous.**
   `SpineHargsK D K e occ` quantifies over the *occurrence data* `occ : Nat → VNestedOcc`, which
   `TrIndDeclN (env, Us, nparams, types, isUnsafe, numNested, D, K, R)` does not carry.
   `∃ occ, D.SpineHargsK K e occ` is **trivially true** (choose `(occ j).args = []` and
   `(occ j).decl.np = 0`; `HasArgs.nil`), so the existential form is not a clause at all.
   Adding an `occ` parameter to `TrIndDeclN` is a signature change at every use site.

### F2. `RestoreData` is the wrong home, structurally

`ElimNestedInductive.Result.RestoreData` (`Verify/Inductive/NestedRestore.lean:279`) is
`(r, types, D, K, tyArgs)` and **carries no `VEnv`**.  Every one of its sixteen fields is a
statement about *names* the checker computes, `decide`-able at a concrete block (its own docstring
says so).  A typing judgement cannot be stated there without adding a `VEnv` parameter — i.e. a
signature change, not a field.  So the clause's home is `TrIndDeclN`, not `RestoreData`.

### F3. …and the fix is free: `SpineHargsK`'s only genuinely `occ`-valued input is the spine's own length

`SpineHargsK D K e occ`'s telescope is `(splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1`.
Under `VInductDecl'.Built`:

* `(occ j).src.type` and `(occ j).decl.uvars` are pinned by `VNestedOcc.Occurs.ty_const` to the
  constant `env` declares at `R.tyName j` (`built_ty_const`);
* `(occ j).lvls = R.tyLvls j` and `(occ j).args = R.tyArgs j` (`Built.tyLvls` / `Built.tyArgs`);
* and the split count — the one remaining piece — is `(occ j).decl.np`, which
  **`VNestedOcc.Occurs.args_len` already forces to be `(occ j).args.length = (R.tyArgs j).length`**
  (`built_tyArgs_length`).  `args_len` is a field of `Occurs`, there since it was
  `replaceIfNested`'s `assert! I_nparams ≤ args.size`.

So the clause can be stated over `R.tyName`/`R.tyLvls`/`R.tyArgs` and the two environments alone,
and it is **the same statement**, not a weakening:

`VIndRestore.SpineHargsC R D K env e` ↔ `D.SpineHargsK K e occ` under `Built`
(`spineHargsC_iff_spineHargsK`), hole-free, **no `HasArgs.of_mkApp`**, and — the part that surprised
me — **no length side condition** of the kind `VIndRestore.hargs_of_spineTyped`
(`Theory/Inductive/HargsShared.lean` §2) has to take, because `args_len` supplies it.

### F4. So the brief is right about the content and wrong about the form

The instruction was "state the checker-side clause as `SpineHargsK`".  The *content* is right and
this round changes nothing about it.  The *form* cannot be `SpineHargsK` (F1), and the correction is
not another round's change of mind about the price: `SpineHargsC` is provably the same judgement.
`SpineHargsN` (§5 of the file) is that clause written out in `TrIndDeclN`'s own guard style
(`types.length ≤ j`, staged over the `addIndTypesC` premise exactly as `trCtors` is), and
`spineHargsC_of_spineHargsN` / `spineHargsN_of_spineHargsC` bridge the two guard styles.

### F5. Consumers reached

* `VIndRestore.valAt_of_spineHargsC` — `ValAt` from the clause (`valAt_of_spineHargsK` ∘ F3).
* `VIndRestore.csubstTy_WF_of_spineHargsC` — the *whole* substitution well-formedness
  `(R.csubstTy D K).WF e₂ e D.uvars`, i.e. the hypothesis of `ArgsTypedK.restrict_of_val` and of the
  nested transport, from the clause plus the five hypotheses `csubstTy_WF_of_val` already takes
  (`env.Ordered`, `e.Ordered`, `D.WF env`, `FreshIn`, `Closed`).  **No consumer needed a proof
  change**: outcome 1's consumer half.

## 2. What landed

One file, mine, new: `Lean4Lean/Verify/Inductive/SpineClause.lean` (386 lines, **21 declarations,
21 `#print axioms` lines, all hole-free** — `[propext]`, `[propext, Quot.sound]`, or
`+ Classical.choice`).  It is an orphan leaf, imported by nothing.  No other file is changed in the
final state.  Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) were
not read for editing, not written, not `touch`ed; they do not appear in `git status`.
**No `HasArgs.of_mkApp` in any proof** (2 occurrences in the file, both prose).

| # | claim | grade |
|---|---|---|
| 1 | **The clause, over checker-side data only**: `VIndRestore.SpineHargsC R D K env e` — one `HasArgs` per companion member at the target environment, against the presented head's declared telescope, split count read off the spine.  No `occ`, no `npJ` | **stated** |
| 2 | **It is the same statement as `SpineHargsK`** under `Built`, in *both* directions (`spineHargsC_iff_spineHargsK`), with no length side condition and no `of_mkApp` | **proved** `[propext, Quot.sound]` |
| 3 | **`∃ occ, SpineHargsK` is vacuous**, so `SpineHargsK` is not available as a clause at all (`VInductDecl'.exists_spineHargsK`) | **proved** |
| 4 | Consumers reached: `ValAt` (`valAt_of_spineHargsC`) and the **whole** substitution well-formedness `(R.csubstTy D K).WF e₂ e D.uvars` (`csubstTy_WF_of_spineHargsC`).  **No consumer needed a proof change** | **proved** |
| 5 | The clause in `TrIndDeclN`'s own guard style (`SpineHargsN`, staged over the `addIndTypesC` premise as `trCtors` is) and the two-way bridge to §2's form | **proved** |
| 6 | **Instantiated at the `NFn`/`PFn` block, existentially closed**: the clause, the field-shaped clause, `ValAt` from it, and the `iff` | **proved** (`NestedWit.nfnAux_valAt_of_spineHargsC`, `nfnAux_spineHargsN`, `nfnAux_spineHargsC_iff`, `nfnAux_spineHargsC_lookup`) |
| 7 | **…and at the parameterised `NTree`/`List` block**, closing the degeneracy gap `docs/handoff-valat.md` §4 declared open (`params ≠ []`, `uvars = 1`) | **proved** (`InductiveDeclExamples.ntreeAux_spineHargsC`) |
| 8 | One library lemma the tree lacked: `VExpr.splitPis_length_self` / `splitPis_eq_of_length` — `splitPis` is determined by the telescope length it produces | **proved** |

A library gap worth knowing: `Theory/Inductive/HAsDropValAt.lean` already states `ValAt`'s body over
`R` + an abstract `npJ` (`valAt_of_hargs`).  §3 of my file is what makes that `npJ` unnecessary.

## 3. Inhabitation and inertness, stated separately from hole-freeness

Two ways this clause could have been inert; both are closed.

* **The `∀ ci` premise could have no witness.**  `SpineHargsC` reads "for every `ci` the pre-block
  environment declares at the presented head", vacuously true when the head is undeclared.  Under
  `Built` it never is: `built_ty_const` produces the lookup **in general**, and
  `nfnAux_spineHargsC_lookup` exhibits it at the witness.
* **`K = []`** makes it vacuous (`spineHargsC_nil`, the collapse test).  `nfnK ≠ []` and
  `ntreeK ≠ []`, the spines are `[NFn]` and `[NTree.{u} #0]`, so the `HasArgs` is a genuine `.cons`
  at both.

**Still open at the parameterised witness**: `ValAt` at `ntreeAux` needs
`OnCtx ntreeAux.params.reverse (env₃.IsType 1)`, which is `trivial` at `nfnAux` and is **not**
supplied here.  That is the one hypothesis of §4 still open at the block Lean's own kernel runs the
nested elimination on.

## 4. The ripple of the actual field edit — MEASURED, not performed

Per the brief, the structure-field edit was measured by probe-apply-build-revert and then reverted;
`InductR.lean` and `NestedRestoreWit.lean` are byte-identical to `HEAD` in the final state.

**The probe field** (added to `structure TrIndDeclN`, `Verify/Environment/InductR.lean:276`, right
after `ctorName_own`; `declTele` is a `Theory` abbreviation `InductR.lean` does not import, so it is
spelled out):

```lean
  trSpine : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        env₁.HasArgs D.uvars D.params.reverse
          (VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j)
```

**The ripple is exactly three construction sites**, which is the whole producer set
`Verify/Inductive/TrIndDeclNCtorOwn.lean` §1 enumerates, and **all three were discharged in the
probe with no new premise on any of them**:

| site | file | discharge | lines |
|---|---|---|---|
| `TrIndDecl.toN` (`numNested = 0`) | `Verify/Environment/InductR.lean:398` | the guard `types.length ≤ j` contradicts `j < D.types.length = types.length + 0` | 4 |
| `NestedWit.trIndDeclN_wit` (hand restoration) | `Verify/Environment/InductR.lean:882` | `hPFn` pins `ci`; the telescope is `[Type]` and the spine `[NFn]`, so it is `HasArgs.cons (.const …) .nil` with `NFn` read off `addConstList_constants hst` — the *same* term `trCtors` already uses | 11 |
| `NestedWit.trIndDeclN_wit'` (`mkRestore` restoration) | `Verify/Inductive/NestedRestoreWit.lean:457` | identical, with `nfnRestore'` for `nfnRestore` | 11 |

Note that **no consumer** of `TrIndDeclN` or of `InductStepNested` broke: the field is on a
hypothesis relation, so consumers only gain.  The exact probe patch is reproduced at the end of this
document.

**Probe verification, with my file present and the field added:** `lake build` **1599 jobs,
exit 0**, zero `error:` lines; `sorry-census-all` **13 holes**, `BUILT: 416`, `NOT BUILT: 0`, same
list; `dup-names` clean; guards `1 ✓ (24 frozen axioms)`, `2 ✓ (whitelist; proof INCOMPLETE —
sorryAx present, unchanged)`, `3 ✓ (2/2)`; section-variable warnings **1**, and it is
`Foundation/FirstOrder/SetTheory/Z.lean`, i.e. **0** from Lean4Lean.

So: **the flip's checker-side clause costs three eleven-line-or-less discharges and nothing else.**
It is not a large edit and it is not blocked.  It is still not mine to make — `InductR.lean` and
`NestedRestoreWit.lean` are other streams' files, and the flip is the orchestrator's to sequence.

## 5. Where the brief is wrong

**"State the checker-side clause as `SpineHargsK`."**  Right about the content — this round changes
nothing about the price, and §2 claim 2 is the machine-checked statement that nothing was traded
away.  Wrong about the form, for two reasons that are independent of each other and neither of which
is a matter of taste (F1, F2, and `exists_spineHargsK` for the vacuity).  This is **not** a third
change of mind about what the checker owes: `SpineHargsC ↔ SpineHargsK` is proved.

**"Adding a field to a structure ripples through every construction site."**  True in general and
the measurement was the right call — but here "every construction site" is **three**, and all three
are cheap.  The brief's framing (two rounds measured rather than performed, and it was right) reads
as though the edit were large; the measurement says it is not.  What made it cheap is that
`TrIndDeclN` is a *hypothesis* relation with a small closed producer set, already enumerated by
`TrIndDeclNCtorOwn.lean` when `ctorName_own` was added on 2026-09-01 — that file is the template and
the audit pattern is already established.

**"`TrIndDeclN` / `RestoreData`, where they state their obligations."**  `RestoreData` is not a
candidate: it carries no `VEnv` (F2).  Only `TrIndDeclN` is.

## 6. Verification record (final state)

* `lake build Lean4Lean.Verify.Inductive.SpineClause`: **exit 0, 200 jobs**, no warnings from my
  file.  21/21 declarations hole-free; names read off the file's own `namespace` lines.
* `lake build` (whole tree, final state): **1599 jobs, exit 0, zero `error:` lines.**
  `grep -c "automatically included section variable"`: **1**, and it is
  `Foundation/FirstOrder/SetTheory/Z.lean` — upstream, **0** from Lean4Lean.
  (Mid-round the tree was briefly red on `Theory/Inductive/IndexedWit.lean`, a concurrent stream's
  file, twice; both times it was green again by the next build, and it is not in my file's cone.)
* Guards (final state): `guard 1 ✓ (24 frozen axioms)`, `guard 2 ✓ (whitelist; proof INCOMPLETE —
  sorryAx present, unchanged)`, `guard 3 ✓ (2/2)`.
* `sorry-census-all` (final state): **13 holes**, `BUILT: 416`, `in population but NOT BUILT: 0`,
  same list as the baseline.  `dup-names`: clean.
* `dup-names`: "no duplicate Lean4Lean declarations across the joined cone".
* Baseline before any edit, for comparison: 1595 jobs exit 0; 13 holes; BUILT 412.
* Frozen files: not read for editing, not written, not `touch`ed; absent from `git status`.
* Other streams' files read and imported, never edited in the final state: `ValAtPrice.lean`,
  `RestrictCompanion.lean`, `ArgsTypedSupply.lean`, `HargsShared.lean`, `HAsDropValAt.lean`,
  `NestedBuild.lean`, `Restore.lean`, `Decl.lean`, `NestedRestore.lean`,
  `Verify/Environment/InductR.lean`, `NestedRestoreWit.lean`, `TrIndDeclNCtorOwn.lean`.
  `InductR.lean` and `NestedRestoreWit.lean` were probe-edited and **reverted** (byte-identical to
  `HEAD`; `git diff` on both is empty).
* `IndexedWit*`, `RestrictStep*`, `WFRipple*`, `NestedHead.lean`: untouched (concurrent streams').
* No state-changing `git`, no `lake update`, nothing sent outside this repo.
* `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197): untouched.  **The flip was not made.**

### 6a. Measured vs read off

**Measured this round:** every axiom line, per declaration, from the compiler; the whole of §§1–6 of
`SpineClause.lean`; that the `TrIndDeclN` ripple is exactly three sites and that all three discharge
(by building them); the probe tree's census, guards, dup-names, job count and section-variable count;
the import direction that makes `SpineHargsK` unnameable in `InductR.lean` (by reading the `import`
lines of the six modules on the path).

**Read off source, not independently proved:** that `TrIndDeclNCtorOwn.lean` §1's three-path producer
enumeration is complete (I confirmed it by grep and by the probe's error set, which agreed);
that `VEnv.HasArgs.of_mkApp` is `sorryAx`-tainted (from `HargsShared.lean` §6's docstring and two
handoffs — I use it nowhere); that `IndexedWit.lean`'s breakage is a concurrent stream's (from its
being untracked and outside my cone).

## 7. Pick up first

1. **Make the edit.**  §4's field text plus the three discharges below is the whole thing.  Then
   `spineHargsC_of_spineHargsN` → `valAt_of_spineHargsC` → `csubstTy_WF_of_spineHargsC` is the
   transport, and `ArgsTypedK.restrict_of_val` (`RestrictCompanion.lean` §11) is what consumes it.
   Follow `TrIndDeclNCtorOwn.lean`'s pattern for the consumer audit; the audit is *cheap* here
   because no consumer's proof changes.
2. **The one hypothesis still open at the parameterised block**:
   `OnCtx ntreeAux.params.reverse (env₃.IsType 1)` for `valAt_of_spineHargsC` at `ntreeAux`.
   `RestrictCompanion.lean` §7's `ntreeAux_params_constsIn` is the `ConstsIn` analogue; the `IsType`
   one is not there.
3. **Do not** look for `SpineHargsK` on `TrIndDeclN` (§5), and **do not** try to weaken the clause to
   `ValAt` (`docs/handoff-valat.md` §2(a) closed that).
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF`, and do not make the flip without
   the orchestrator sequencing it.

## 8. The probe patch, verbatim (for re-application)

```diff
--- a/Lean4Lean/Verify/Environment/InductR.lean
+++ b/Lean4Lean/Verify/Environment/InductR.lean
@@ structure TrIndDeclN ... (after `ctorName_own`)
+  trSpine : ∀ env₁, env.addIndTypesC D K = some env₁ →
+    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
+      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
+        env₁.HasArgs D.uvars D.params.reverse
+          (VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j)
@@ theorem TrIndDecl.toN ... where
+  trSpine := by
+    intro _ _ j T hT hj
+    have hjlt : j < D.types.length := List.getElem?_eq_some_iff.1 hT |>.1
+    rw [← h.length] at hjlt
+    omega
@@ theorem trIndDeclN_wit ... where
+  trSpine := by
+    rintro env₁ hst (_ | _ | j) T hT hj ci hci
+    · simp at hj
+    · cases hT
+      rw [show nfnRestore.tyName 1 = ``PFn from rfl] at hci
+      cases Option.some.inj (hPFn.symm.trans hci)
+      have hNFn : env₁.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
+        VEnv.addConstList_constants hst (``NFn, ⟨0, .sort (.succ .zero)⟩)
+          (by exact List.Mem.head _)
+      exact .cons (.const hNFn nofun rfl) .nil
+    · simp [nfnAux] at hT
--- a/Lean4Lean/Verify/Inductive/NestedRestoreWit.lean
+++ b/Lean4Lean/Verify/Inductive/NestedRestoreWit.lean
@@ theorem trIndDeclN_wit' ... where
+  trSpine := by
+    rintro env₁ hst (_ | _ | j) T hT hj ci hci
+    · simp at hj
+    · cases hT
+      rw [show nfnRestore'.tyName 1 = ``PFn from rfl] at hci
+      cases Option.some.inj (hPFn.symm.trans hci)
+      have hNFn : env₁.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
+        VEnv.addConstList_constants hst (``NFn, ⟨0, .sort (.succ .zero)⟩)
+          (by exact List.Mem.head _)
+      exact .cons (.const hNFn nofun rfl) .nil
+    · simp [nfnAux] at hT
```
