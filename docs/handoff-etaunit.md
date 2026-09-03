# handoff-etaunit — the two eta holes are one hole, and its stated residual is **false**

Round of 2026-09-03.  Target: `TypeChecker.Inner.tryEtaStructCore.WF` and
`TypeChecker.Inner.isDefEqUnitLike.WF` (`Verify/TypeChecker/IsDefEq.lean`).
New file, mine: `Lean4Lean/Verify/TypeChecker/EtaUnitRefute.lean`.
`Verify/TypeChecker/IsDefEq.lean` was **not** edited; the frozen files were not touched.

## Headline

1. **The residual both holes were reduced to is refutable.**  `EtaResidual.lean`'s
   `etaHoles_of_structEtaG` reduces both holes to the single hypothesis `c.venv.StructEtaG`.
   `MutField.unitEnv_not_structEtaG` proves that hypothesis **false** at an environment whose
   `VEnv.WF` is proved.  So the hypothesis cannot be discharged from `c.Ewf`, and structure eta
   must change `VEnv.IsDefEq` (a 14th constructor) rather than be asserted of it.
   Priced below.
2. **`VEnv.WF` at an `addInduct'` output is a one-liner**, and two docstrings say otherwise.
   `MutField.declEnv_wf` and `EtaUnit.barEnv_wf` are three lines each and `sorryAx`-free.
   This discharges hypotheses several existing witnesses carry as open.
3. **Closing either hole alone frees at most one declaration** (measured, below).  They are one
   work item, and `inferProj.WF` is in it.

## 1. Measurement, done myself, reproducing the census exactly

`lake env lean --run scripts/sorry-census.lean` and an independent walk agree:

| hole | users | sole users (other 12 holes cut) |
|---|---|---|
| `tryEtaStructCore.WF` | 71 | **1** (`tryEtaStruct.WF`) |
| `isDefEqUnitLike.WF` | 70 | **0** |
| `inferProj.WF` | 70 | **0** |

* `isDefEqUnitLike.WF`'s 70 users are a **subset** of `tryEtaStructCore.WF`'s 71 (`a-only = 0`);
  the one extra is `tryEtaStruct.WF`.
* `inferProj.WF` shares **69** with each of the other two; it differs by one either way
  (`inferType'.WF` on its side, `isDefEqCore'.WF` on theirs).
* So the eta/proj corner is a single item of three holes with a 69-declaration shared cone.
  Excluding `inferProj.WF` from the pairing is defensible on *route* grounds (it needs
  `D.ihValues` typed, which nothing supplies) but **not** on user-count grounds.

`addDecl.WF`'s forward cone (5724 decls) reaches all three; `kernel_sound`'s does not reach any
hole, because `kernel_sound := sorry` and only its *type* has dependencies.  Use `addDecl.WF`,
not `kernel_sound`, as the critical-path anchor.

**Instrument caution, two hits.**  (i) My first walk excluded internal names as pass-through
nodes and reported 2/1/0 users instead of 71/70/70 — the exact bug `scripts/sorry-census.lean`
documents at line 62.  (ii) My first taint probe reported "no holes in cone" for a theorem that
`#print axioms` calls `sorryAx`-tainted; the cause was a **stale `.olean` for my own module**
(`lake env lean file.lean` does not produce one).  Rebuild before probing; both numbers above
are post-rebuild.

## 2. The refutation

`MutField.unitEnv` = `MutField.declEnv` (the two-type mutual block in `Type` of
`EtaStructG.lean`, member `A` zero-field, member `B` one-field) **plus one axiom**
`foo : A`.  Both `A` and `A.mk` already exist there; the axiom supplies a *second constant*
inhabiting `A`, which is what makes both sides of the eta equation constant-headed.

* `MutField.unitEnv_wf : VEnv.WF unitEnv` — `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* `MutField.unitEnv_not_unitEta : ¬ unitEnv.UnitEta`
* `MutField.unitEnv_not_structEtaG : ¬ unitEnv.StructEtaG` (via `StructEtaG.toUnitEta`)
* `MutField.etaResidual_refuted` — the three together, as one statement.

**How.**  `VEnv.constNoConf_of_notIsProof` (in my file) is `VEnv.constApp_inv_of_patWF`
(`Verify/Typing/ConstSpine.lean`) with the premise `env.IsType U Γ ((const c ls).mkApp as)`
replaced by the `¬ env.IsProof U Γ ((const c ls).mkApp as)` that proof *only ever uses it to
produce* (`IsType.not_isProof`, one call, nothing else reads `hty`).  That is the whole trick:
the (A)–(D) rigidity family reads as type-level only, but no-confusion is available at a
**term** as soon as the term is not a proof.  `foo : A : Type`, so it is not.

**Why `unitEnv` and not `declEnv`.**  `declEnv.StructEtaG` is *not* refutable by this route and
remains open: `declEnv`'s only inhabitants of `A` are `A.mk` and bound variables, and there is
**no bvar-vs-constructor no-confusion anywhere in the tree** — the only no-confusion is
`VEnv.ConstNoConf` / `constNoConf_of_wf` / `constNoConf_of_patWF` (three declarations, verified
by a conclusion-head query over the compiled environment).  A refutation at a *variable*
inhabitant is blocked on that missing lemma, which is confluence-strength.

**Taint, stated separately from hole-freeness.**  `unitEnv_not_unitEta` is
`[propext, sorryAx, Classical.choice, Quot.sound]`.  The `sorryAx` enters through exactly four
census holes and no others (measured on the rebuilt module): `IsDefEqU.forallE_inv_stratified`,
`IsDefEqU.weakN_iff`, `WF.rigidShapeUniqNS`, `NormalEq.descend` — the same four
`isDefEqUnitLike.WF_of_unitEta` already borrows.  **No new hole.**  The named carriers are
`VEnv.WF.uniq'`, `VEnv.HasType.defeqU_l'`, `VEnv.WF.sortUniq'` (inside
`unitEnv_not_isProof_foo`) and `VEnv.IsDefEq.constApp_inv` (inside
`constNoConf_of_notIsProof`); each is independently `sorryAx` by `#print axioms`.

**The geometry is hole-free.**  `MutField.unitEnv_not_unitEta_of` is the same refutation with
those two inputs hypothesised: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  It is
the statement that says *which premises of `UnitEta` are satisfied at `unitEnv` and what the
contradiction is*.  Its two hypotheses are inhabited — by `unitEnv_not_isProof_foo` and
`constNoConf_of_notIsProof` — and **those two inhabitants are tainted**.  Read that as two
facts, not one.

**Negative control, and why it is a control.**  `VEnv.unitEta_instance_of_prop` (`[propext]`,
one line, `IsDefEq.proofIrrel`) proves the *same instance* the refutation kills, at a structure
living in `Prop`.  So the refutation is not an artefact of how `UnitEta` is stated: it is
located exactly at the universe of the structure, and `unitEnv_not_isProof_foo` is the step
that fails when the structure is a proposition.  A refutation attempt at a `Prop`-valued
unit-like block would have to contradict a hole-free theorem.

**Firing test, in the real kernel.**  With the current toolchain, from the repo root:

```lean
structure A : Type where
axiom foo : A
example : foo = A.mk := rfl        -- accepted
example (x y : A) : x = y := rfl   -- accepted
```

Both are accepted.  So the C++ kernel really does identify an axiom-inhabitant of a
`Type`-valued zero-field structure with its constructor — the exact equation `unitEnv` refutes
as a property of the 13-constructor `IsDefEq`, at the exact shape.  The witness is not
artificial; it is a configuration Lean4Lean must eventually validate.
`Verify/TypeChecker/FiringWitness.lean`'s `unitTest`/`gateChecks` are the checker-side
counterpart at the same block shape.

## 3. What this does and does not settle

* It does **not** refute `isDefEqUnitLike.WF` or `tryEtaStructCore.WF`.  Those quantify over
  `VContext`, and no `VContext` has `venv = unitEnv` while `AddInduct` has no constructors
  (`Verify/InductFlip.lean:6`).  Today both holes are vacuously *true* and one-line closable
  (`isDefEqUnitLike_never_true`, `tryEtaStructCore_never_true`, both hole-free); they are open
  by policy.
* It does settle that the route "discharge `c.venv.StructEtaG` / `UnitEta` from `c.Ewf`" is
  dead.  Post-`AddInduct`, either the spec gains a structure-eta constructor or these two `.WF`
  statements are false.
* **Price of the constructor route, measured.**  `VEnv.IsDefEq` has 13 constructors.
  `VEnv.IsDefEq.rec` has **25** direct non-internal users with a **2643**-declaration
  transitive blast radius; `IsDefEq.below` has 16.  The 25 include
  `IsDefEq.church_rosser`, `IsDefEq.strong'`, `IsDefEq.instL`, `IsDefEq.weakN`,
  `IsDefEq.substC`, `IsDefEq.sort_inv'`, `IsDefEq.forallE_inv'`, `Strengthening.of_typing`.
  That is the "cost objection" as a number.
* **Absence claim.**  A conclusion-head query over the compiled environment (all of
  `Lean4Lean.*`, both cones via `Experimental.ConeJoin`) finds exactly five declarations
  concluding `StructEta`/`StructEtaG`/`UnitEta`: `empty_structEta`, `empty_structEtaG`,
  `empty_unitEta` (all at `VEnv.empty`) and the two implications `StructEtaG.toStructEta`,
  `StructEtaG.toUnitEta`.  Before this round the residual hypothesis had **one** witness
  environment in the tree, `VEnv.empty`, where its premises are vacuous.  It now also has one
  environment where it is refuted.

## 4. The stale-docstring finding, and what it unblocks

`Verify/Typing/Rigidity.lean:257` says "`barEnv.WF` is unavailable because `VInductDecl'` is not
yet wired into `VDecl.induct`", and `Verify/Typing/ProjWfWitness.lean` §2.5 is cited as
recording the same gap.  **`VDecl.WF.induct` takes a `VInductDecl'`** (`Theory/Typing/Env.lean`),
so with a proved `VInductDecl'.WF` the environment's `VEnv.WF` is immediate:

* `MutField.declEnv_wf` — from `MutField.decl_WF`.
* `EtaUnit.barEnv_wf` — from `barDeclEq_WF` (`Verify/Typing/StructureUniq.lean`).
* `EtaUnit.barEnv_bar_ne_ctorApp'` — `barEnv_bar_ne_ctorApp` with **both** carried hypotheses
  discharged (`PatWF` follows from `WF` by `VEnv.patWF_of_wf`).

`Verify/Typing/TrProjWideTransportWitness.lean:94` calls `VEnv.WF declEnv` "this tree's
keystone, open for everybody".  It is not open at this witness any more.  The same three lines
should work at `MutNonRec.decl2Env` (`decl2_WF` is proved) and at any other witness with a
proved `VInductDecl'.WF`; I checked `declEnv` and `barEnv` only.

## 5. Pick up first

1. **Re-price the eta corner as one item of three holes**, and stop counting partial credit:
   closing `isDefEqUnitLike.WF` alone frees zero declarations.
2. **Sweep the `VEnv.WF`-carried hypotheses** now dischargeable: grep for `(hwf : VEnv.WF` /
   `(henv : ...WF)` at concrete `addInduct'` witnesses.  Each is three lines.  Correct
   `Rigidity.lean:257` and `ProjWfWitness.lean` §2.5 (not my files).
3. **Decide the constructor question.**  The residual is refuted; the only remaining route for
   these two holes is a 14th `IsDefEq` constructor, whose price is 25 eliminations / 2643
   declarations, plus model validation.  `Theory/SetModel/UnitEtaPairing.lean` already has the
   set-level surjective-pairing facts at zero fields *including at mutual blocks*
   (`mutUnitSig_fibre_zero/one`) and nobody has composed them with the interpretation soundness
   theorem to give "the extended relation has a model".  That composition is the natural next
   round and it is not blocked by `AddInduct`.
4. **The missing lemma**, if someone wants the refutation at a variable rather than an axiom:
   bvar-vs-constructor no-confusion.  It does not exist; the family is type-level only.
5. **Make this file visible to the cone instruments.**  `Verify/TypeChecker/EtaUnitRefute.lean`
   is an ORPHAN (census: 26 orphans) because `Experimental/ConeJoin.lean` is not mine.  One
   `import` line there puts it in scope for `hole-rank`, `cone-measure` and `sorry-census`.

## 6. Where I was wrong, and where the orchestration brief was

* The brief's "roughly 70 transitive users" is right (70/71/70, reproduced twice).
* The brief's `HasTypeStrong` lead **did not bear** on these two holes.  Neither `StructEta`,
  `StructEtaG` nor `UnitEta` mentions `HasTypeStrong`; all three take `env.HasType`, and the
  eta corner's residual turned out to be located in the *universe* of the structure, not in the
  strength of the typing judgement.  `EtaResidual.lean` and `Verify/Typing/ProjGenTerm.lean`
  (wall 2) likewise did not enter the refutation.  Flagged as leads, and they were leads.
* My own two instrument failures are in §1; both would have inverted a stated conclusion.
