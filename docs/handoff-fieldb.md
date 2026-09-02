# The `fieldB` repair: what landed, and what is still unverified

Written 2026-09-02 **by the orchestrator, not by the stream that did the work.** That stream died
mid-task (API error) while writing this file, and its last action was reading a *different* stream's
file, so nothing it said about its own results survives. Everything below I verified myself by
building and reading the tree; where I could not verify, I say so. Treat the unverified section as
genuinely unknown, not as probably-fine.

## 1. What the repair is

Ruling 116d: **restore the stored type, drop `Canonical`.** The failure being repaired was the
`none` branch of `Built.member ∧ WF.pos` — *not* `VInductDecl'.Built` being false, which was the
third mis-attribution of this bug (ledger row 119c and its neighbours).

## 2. What landed (verified by me)

- **`fieldB` is now the definition of `VNestedOcc.field`.** The pre-repair function was renamed
  `fieldO`. `MemberRedex.lean:228` records that `fieldB` and its four lemmas no longer exist as a
  separate *proposal*; the mapping table at `MemberRedex.lean:234–237` is the rename record:

      MRedex.fieldB                  -> VNestedOcc.field (the definition)
      MRedex.fieldB_eq_field_of_some -> VNestedOcc.field_eq_fieldO_of_some
      MRedex.fieldB_eq_field_of_none -> VNestedOcc.field_eq_fieldO_of_none

- **All three `Canonical` lemmas are deleted**: `VNestedOcc.ctor_Canonical`,
  `VNestedOcc.member_Canonical`, `VInductDecl'.Built.canonical`. I grepped for surviving
  references: every remaining mention is **prose** — struck-through docstrings and explanation. No
  code refers to them. (`VIndCtor.Canonical` is now false at the repaired constructor, which is
  *why* they are gone, per `MemberRedex.lean:249–250`.)
- **The Theory side builds green**: `lake build Lean4Lean.Theory.Inductive.MemberRedex
  Lean4Lean.Theory.Inductive.NestedBuild Lean4Lean.Theory.Inductive.RestoreBridge` → 66 jobs,
  exit 0.
- **No frozen axiom is reached** by the new lemmas: `VNestedOcc.field_eq_fieldO_of_some`,
  `field_eq_fieldO_of_none`, `field_new_branch` all print `[propext, Quot.sound]`.
  `nfnAuxDirty_canonicalOwn` survives the `Canonical` deletion and still proves with
  `[propext, Quot.sound]`.
- Scope: ~815 insertions / ~271 deletions across `Theory/Inductive/MemberRedex.lean` (+479),
  `Theory/Inductive/NestedBuild.lean` (+323), `Theory/Inductive/RestoreBridge.lean`,
  `Verify/Inductive/NestedOccData.lean`, `Verify/Inductive/NestedRestoreWit.lean`,
  `Verify/Inductive/MemberRedexScan.lean`. A snapshot of the Inductive-only diff is at
  `/tmp/fieldb-partial.patch` (ephemeral — do not rely on it after a reboot).

## 3. What is NOT verified, and must be before this is trusted

- ~~**The `Verify/Inductive` half never compiled.**~~ **RESOLVED 2026-09-02**: a full `lake build`
  returned `FULL=0` with guards `1 ✓ (24 axioms) / 2 ✓ (INCOMPLETE) / 3 ✓ (2/2)`, and that build
  includes `NestedRestoreWit.lean`, `NestedOccData.lean` and `MemberRedexScan.lean`. The
  `Invalid field 'canonical'` error an earlier stream saw is gone. So the repair is green
  end-to-end; what remains missing is the *measurement*, not the build.
- **The gate I set was never reported on.** The task was gated on whether the dependent proofs could
  absorb the `Canonical` deletion, and the stream was told to report the consumer list with counts
  (via `lean_references`, not grep) and to stop if the gate was shut. **No such list exists.** The
  deletion is in and the Theory side is green, which is evidence the gate was open, but the
  enumeration that would prove it was never produced.
- **No anti-vacuity measurement was reported.** Nothing exhibits a witness that the repaired
  `Built.member ∧ WF.pos` hypotheses are satisfiable at the degenerate instance, and nothing checks
  whether deleting `Canonical` pushed a burden into a hypothesis. This is the measurement this repo
  cares most about and it is **missing**. The claim "3/3 coverage, no divergence" is from my own
  earlier notes, not from a machine-checked statement I can point at.

## 4. What I would pick up first

1. `lake build Lean4Lean.Verify.Inductive.NestedRestoreWit
   Lean4Lean.Verify.Inductive.NestedOccData Lean4Lean.Verify.Inductive.MemberRedexScan` once
   `Verify/Primitive.lean` is green again, and fix what falls out.
2. Then the two missing measurements in §3: the consumer enumeration, and a satisfiability witness
   for the repaired branch at the degenerate instance (`Γ = []`, nil telescope, zero grade).
3. Do **not** take §2's "no frozen axiom" as covering the `Verify/Inductive` side; re-print axioms
   there once it builds.
