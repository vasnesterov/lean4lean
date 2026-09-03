# handoff-constappinvsi

Round owner files: `Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean` (new, mine),
`docs/handoff-constappinvsi.md` (this file, mine).
Read-only: `Verify/Typing/ConstSpine.lean`, `Theory/Typing/NoConfRepair.lean`,
`EtaGuardLand.lean`, `StructEtaPrice.lean`, `Verify/Typing/ProjSpineInv.lean`,
everything under `Verify/Inductive/`. Frozen (never touch): `Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean`. Never touch `docs/vacuity-ledger.md`.

## Section 1 — written BEFORE any Lean interaction (mandatory)

Target handed to me:

    Lean4Lean.ConstAppInvSIFromWF   (Theory/Typing/EtaGuardLand.lean, claimed arity 0, claimed cone 637)
      i.e.  forall env U, env.WF -> env.ConstAppInvSI U

Claims in my brief that I must independently re-verify with `scripts/exists.lean`
(the brief says every figure is unverified, and 15 brief errors have already
occurred this session, three of them transcribed numbers):

  1. `Lean4Lean.ConstAppInvSIFromWF` exists, arity 0, cone 637, and IS a hole.
  2. `Lean4Lean.VEnv.ConstAppInvSI` (NoConfRepair.lean) arity 2, cone 633, hole-free.
  3. `Lean4Lean.VEnv.constApp_inv_of_wf` differs from ConstAppInvSI by exactly one premise.
  4. `Lean4Lean.VEnv.IsStructure.spine_inv_of_si_wf` arity 25, cone 7538, drop-in for spine_inv.
  5. 156 of 187 transitive users re-base; call sites ProjSpineInv.lean:86 and :150, body only.
  6. `Lean4Lean.spine_inv_of_spineInvStmt` cone 597 hole-free;
     `Lean4Lean.spineInvStmt_of_repair` cone 7541.
  7. `Lean4Lean.guard_rejects_an_axiom` cone 382 hole-free (no head-name guards).
  8. `Lean4Lean.VEnv.structInhabOnlyNoConf_false` arity 0 cone 3815 hole-free
     (¬IsProof cannot be dropped).
  9. `Lean4Lean.MutField.unitEnv` / `Lean4Lean.MutField.bigEnv` exist and are WF.
 10. Whether the target is ALREADY REFUTED somewhere in the tree (one of the 13
     holes turned out to be known-false with the refutation already present).

Plan of record, in order:
  P0. Pre-flight: whole-tree `lake build`, `scripts/exists.lean` census (expect 13 / NOT BUILT 0),
      three Guard.lean checks, section-variable warning sweep. Record numbers verbatim.
  P1. Check 10 FIRST — grep for any existing refutation of ConstAppInvSI /
      ConstAppInvSIFromWF before investing in a proof.
  P2. Read the two eta cases of `Verify/Typing/ConstSpine.lean`'s no-confusion
      argument; report exactly what each needs.
  P3. Try to prove; else reduce to smallest sufficient premise with an iff;
      else refute with an explicit counterexample environment.
  P4. Vacuity both ways at unitEnv (zero-field) AND bigEnv (positive-field).
  P5. Round-close numbers.

Risk notes recorded up front, so a crash loses nothing:
  - If the target is false, the counterexample must be a WF environment where the
    ¬StructInhab guard holds yet constApp_inv fails, or (dually) where the guard
    is unsatisfiable at a real structure — the latter would make the repair vacuous
    and is exactly what item (d) tests.
  - `guard_rejects_an_axiom` forbids ANY head-name-phrased guard; so no fix of the
    form "unless the head is `Foo.mk`" is admissible. Do not work around it.
  - `structInhabOnlyNoConf_false` forbids dropping ¬IsProof; the repair ADDS.

## Section 2 — pre-flight results

(filled in below as they are measured; nothing here is trusted until it appears)

### P0 pre-flight (measured 2026-09-03)

- whole-tree `lake build`: **exit 0**, "Build completed successfully (1621 jobs)".
- `scripts/sorry-census-all.lean`: **BUILT 438, NOT BUILT 0, HOLES 13**.
- `scripts/exists.lean` population at pre-flight: 435 built modules.

### P1/P2 — every brief figure re-measured, and where the brief was wrong

All thirteen names FOUND. Figures confirmed exactly as the brief gave them:

| name | arity | cone | holes |
|---|---|---|---|
| `Lean4Lean.ConstAppInvSIFromWF` | 0 | 637 | none (it is a `def` of a `Prop`, **not** one of the 13 holes) |
| `Lean4Lean.VEnv.ConstAppInvSI` | 2 | 633 | none |
| `Lean4Lean.VEnv.constApp_inv_of_wf` | 15 | 7491 | the four |
| `Lean4Lean.VEnv.IsStructure.spine_inv_of_si_wf` | 25 | 7538 | the four |
| `Lean4Lean.VEnv.IsStructure.spine_inv` | 24 | **7538** | the four |
| `Lean4Lean.spine_inv_of_spineInvStmt` | 25 | 597 | none |
| `Lean4Lean.spineInvStmt_of_repair` | 1 | 7541 | the four |
| `Lean4Lean.guard_rejects_an_axiom` | 7 | 382 | none |
| `Lean4Lean.VEnv.structInhabOnlyNoConf_false` | 0 | 3815 | none |
| `Lean4Lean.MutField.unitEnv` | 0 | 928 | none |
| `Lean4Lean.MutField.bigEnv` | 0 | 930 | none |

"the four" = `VEnv.IsDefEqU.weakN_iff`, `VEnv.IsDefEqU.forallE_inv_stratified`,
`VEnv.WF.rigidShapeUniqNS`, `VEnv.NormalEq.descend`.

**Two brief claims are FALSE, and they are the load-bearing ones.**

1. *"the work lives in the two eta cases of `ConstSpine.lean`'s no-confusion argument."*
   No. `ConstSpine.lean:220-221` are `VEnv.NormalEq.etaL`/`etaR` — **function** eta. Both are
   one-liners closed by shape (`VExpr.constApp_ne_lam`: a constant spine is never a λ). They need
   nothing, and they stay free after the repair, because **structure** eta is the case where both
   endpoints are constant spines. `NormalEq`/`ParRed` have **no `structEta` case at all**; the two
   cases the repair owes do not exist yet.

2. *"the whole eta repair reduces to `ConstAppInvSIFromWF`."*
   No. `VEnv.ConstAppInvSI` is stated over `env.IsDefEqU`, i.e. `VEnv.IsDefEq` — the
   **thirteen**-constructor relation, with no `structEta`. `structEta` is a constructor of a
   *different* relation, `VEnv.IsDefEqSE` (`StructEtaPrice.lean:183`), which `ConstAppInvSI` never
   mentions. So the named target is about the pre-repair relation and is **provable today**.
   Corroboration inside the tree: `Lean4Lean.spineInvStmt_today` (arity 0, cone 7540) already
   inhabits `SpineInvStmt` **unconditionally**, so `spineInvStmt_of_repair` reduces a statement
   that was already a theorem.

### P3 — verdict: PROVED, and it does not close the repair

Everything below is in `Lean4Lean/Theory/Typing/ConstAppInvSIProof.lean`.

- `Lean4Lean.constAppInvSIFromWF` (arity 0, cone 7494) — **the target, proved.** Tainted at
  the four census holes; same four as `spine_inv`, so nothing added to the cone it serves.
  Route: `VEnv.IsDefEq.constApp_inv` (Params-level, `¬ IsProof`-guarded, **no `IsType`**) composed
  with `VEnv.patWF_of_wf`. The `¬ StructInhab` argument is bound as `_hsi` and discarded.
- `Lean4Lean.constAppInvNoSIFromWF` (0, 7491) — the same statement with the eta guard **deleted**,
  provable by the identical proof. This is the machine-checked form of "the guard is dead weight
  over `IsDefEqU`". Note the cone is *smaller* than the guarded one.
- `Lean4Lean.constAppInvSIFromWF_iff_unguarded` (0, 7498) — the `↔`. Its information content is
  recorded **at the statement**: both sides are theorems, so the equivalence says only that; the
  informative half is the unguarded one.
- `Lean4Lean.MutField.unitEnv_noSI_true_but_SE_false` (0, 7886) — **the separation.** The same
  premise set is a theorem at `unitEnv` over `IsDefEqU` and **refuted** at `unitEnv` over
  `IsDefEqSE`. Opposite truth values, one environment. This is why §1 cannot bear on the repair.

### P3b — the further defect found: the guard is defined at the wrong relation

`VEnv.StructInhab` = `StructInhabAt` at `env.HasType U Γ`, i.e. at `VEnv.IsDefEq`. The `structEta`
constructor's eighth premise is `env.IsDefEqSE U Γ e e ((const S us).mkApp ps)`. Different
predicates; nothing transports the second to the first. So:

- `Lean4Lean.VEnv.StructInhabSE` (4, 83, hole-free) — the guard at the right relation.
- `Lean4Lean.VEnv.structEta_lhs_structInhabSE` (15, 87, hole-free) — **the `structEta` case is
  blocked, in one line**, by the deliberately `Ty`-generic `VEnv.structEta_lhs_structInhabAt`. The
  guard's *design* is right; its *definition* is at the wrong relation.
- `Lean4Lean.ConstAppInvSISEFromWF` (0, 638, hole-free) — the obligation that is actually left.
- `Lean4Lean.NotStructInhabSEOfIsTypeStmt` (0, 97, hole-free, left as a `def` so it enters no cone
  as a theorem) — the additional gap: "the SE guard is free at every type". The thirteen-ctor proof
  (`notStructInhab_of_isType`) does **not** transport; it runs through `VEnv.WF.uniq'` and
  `VEnv.const_sort_inv_of_wf`, both statements about `VEnv.IsDefEq`.

### P4 — vacuity, both directions, both structure shapes

Restrictive (guard excludes the eta endpoints), all hole-free:
- `Lean4Lean.MutField.unitEnv_structInhabSE_foo` (0, 3882) — zero-field member.
- `Lean4Lean.MutField.bigEnv_structInhabSE_bar` (0, 3901) — **positive-field** member
  (`MutField.bCtor_has_a_field : bCtor.fields.length = 1`), the shape the brief requires.
- `Lean4Lean.MutField.bigEnv_structInhabSE_foo2` (0, 3901) and
  `Lean4Lean.MutField.bigEnv_guard_rejects_both_axioms` (0, 3908) — `guard_rejects_an_axiom`'s
  verdict discharged rather than dodged: the guard rejects **both** axioms, so transitivity cannot
  manufacture a violating pair from the two eta instances.

Non-trivial (guard is satisfiable / refutable):
- `Lean4Lean.MutField.bigEnv_guard_separates_both_shapes` (0, 7616, tainted at the four) — the
  thirteen-ctor guard holds at `A` and `B` (the types) and fails at `foo2` and `bar` (their
  inhabitants), at one `VEnv.WF` environment, at both shapes.
- `Lean4Lean.VEnv.not_structInhabSE_ncPropEnv` (3, 1201, hole-free) — the SE guard is refutable.
- **Honest gap:** non-triviality of the *SE* guard at an environment that HAS a structure is not
  available in the tree — see `NotStructInhabSEOfIsTypeStmt` above. Not papered over.

### P5 — round close (measured after the work)

- whole-tree `lake build`: **exit 0**, "Build completed successfully (1623 jobs)".
- census: **BUILT 440, in population but NOT BUILT 0, HOLES 13**.
- guard 1: "Axioms.lean declares exactly the 24 frozen axioms ✓"
- guard 2: "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)"
- guard 3: "checker cone implementation gaps within frozen list (2/2 remaining) ✓"
- in-repo warnings: **188 before, 188 after** — this file contributes **zero**.
- in-repo section-variable warnings: **0** (the only `section variable` warning in the log is
  `Foundation/FirstOrder/SetTheory/Z.lean:35`, i.e. the dependency, not this repo).
- axiom bar `after ⊆ before`: satisfied trivially — no pre-existing declaration was edited;
  `git status` shows only the two new files this round owns.

### Proposed edits elsewhere — STATED, NOT MADE

Read-only files. Nothing below was touched (`git diff` on all of them is empty).

1. `Lean4Lean/Verify/Typing/ProjSpineInv.lean` — body-only, and **I recommend making neither**,
   because `spine_inv` is already proved and `spineInvStmt_today` already inhabits the target
   `Prop` unconditionally. They become meaningful only once the relation is swapped to
   `IsDefEqSE`, at which point the argument must be `ConstAppInvSISEFromWF`, not
   `ConstAppInvSIFromWF`. For the record:
   - line 86: `obtain ⟨hS, hus, has⟩ := h₁.spine_inv henv hΓ h₂ ht₁ ht₂ H`
     → `obtain ⟨hS, hus, has⟩ := h₁.spine_inv_of_si_wf (constAppInvSIFromWF _ _ henv) henv hΓ h₂ ht₁ ht₂ H`
   - line 150: `exact (hS1.spine_inv henv hΓ₁ hS2 hty1 hty2 H).1`
     → `exact (hS1.spine_inv_of_si_wf (constAppInvSIFromWF _ _ henv) henv hΓ₁ hS2 hty1 hty2 H).1`
   Correction to `EtaGuardLand.lean` §3's prose while I am here: it says a replacement must keep
   "the explicit-argument order `henv, hΓ, h₂, ht₁, ht₂, H` after the receiver" and that
   `spine_inv_of_si_wf` does. It does not — `HSI` is its **first** explicit argument, so it comes
   after the dot-notation receiver and before `henv`. The edits above reflect the real order.

2. `Lean4Lean/Theory/Typing/NoConfRepair.lean` — the substantive one.
   `VEnv.StructInhab` (line 102) is `StructInhabAt` at `env.HasType U Γ`, so `VEnv.ConstAppInvSI`
   (line 292) cannot discharge the `structEta` case of any relation containing that constructor.
   The exact edit I would propose is to make the guard relation-parametric, i.e. replace
   `¬ env.StructInhab U Γ ((VExpr.const c ls).mkApp as)` in `ConstAppInvSI` with
   `¬ env.StructInhabSE U Γ ((VExpr.const c ls).mkApp as)` **and** restate the whole definition over
   `env.IsDefEqUSE` — which is exactly `VEnv.ConstAppInvSISE` in the file I own, so the content is
   already proved-where-provable and does not need to move for anyone to inspect it.
   `NoConfRepair.lean` §6's prose is correct as written; it is the named `Prop` that is not.

3. No frozen file needs any change. `Verify/Soundness.lean`, `Verify/Axioms.lean` and
   `Verify/Guard.lean` were not read for edit and not modified.

### Figure correction: the 187/156 user counts are stale

`scripts/users.lean Lean4Lean.VEnv.IsDefEq.constApp_inv`, measured this round (population 437
modules, 26360 non-internal declarations):

    DIRECT 6 declarations in 4 modules; TRANSITIVE 200 declarations in 35 modules

not the brief's "4 direct / 187 transitive". Two of the 6 direct are this round's own
(`ConstAppInvSIProof`); the rest of the drift is tree movement since the brief's 2026-09-03
17:39–17:46 measurement. The **156** figure is a reverse-graph *cut* (transitive count with
`VEnv.IsStructure.spine_inv` removed), which `scripts/users.lean` does not compute, so I did
**not** independently reproduce it — and it is moot for this round's conclusion, since nothing
needs re-basing until the relation is swapped to `IsDefEqSE`.
