# Handoff: repairing const-head no-confusion against structure eta

**File owned by this round:** `Lean4Lean/Theory/Typing/NoConfRepair.lean` (new, 737 lines,
compiles with `lake env lean`, zero warnings).  Nothing else was edited.  This was a **scoping**
round: `IsDefEq` is untouched, `Verify/Typing/ConstSpine.lean` is untouched.

---

## 0. The verdict in five lines

1. What eta kills is the **`¬ IsProof`-guarded** row (`VEnv.IsDefEq.constApp_inv`,
   `VEnv.ConstNoConfNP`).  Refuted, in the tree already.
2. What survives is the **`IsType`-guarded** row (`VEnv.ConstNoConf`) — the eta witness fails that
   guard, machine-checked here (`MutField.unitEnv_not_isType_foo`, `_Amk`).
3. `IsType` is not an induction invariant (a sub-spine has a Π type), so the *proof* needs a third
   guard, `¬ StructInhab`, which threads and is implied by `IsType`.  `VEnv.ConstAppInvSI` is the
   repaired statement; `ConstAppInvSI.of_isType` shows it still delivers `constApp_inv_of_wf`'s
   conclusion.
4. **Re-basing cost: one lemma.**  Of 187 transitive users, 156 reach no-confusion only through
   `VEnv.IsStructure.spine_inv`, which supplies `IsType`; `spine_inv_of_si` re-derives it.  The
   other 31 are the no-confusion family's own restatements and witnesses, in six modules.
5. `addAxiom.WF` needs `IsStructure.spine_inv` and nothing else from this family, and
   `spine_inv`'s no-confusion is applied to *types*, not to structure inhabitants.  So the
   `addAxiom.WF` chain survives with one lemma rewritten.  No narrowing of `kernel_sound` is
   involved or proposed.

---

## 1. (a) Exactly what fails

`VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine.lean:248`) is guarded by `¬ IsProof`, and
its own docstring says why: that is what blocks `NormalEq.proofIrrel`, and it **propagates down the
spine by `IsProof.app'` where `IsType` would not**.  Read that sentence as the design constraint it
is — it is the reason the lemma is not stated with `IsType`, and it is the reason the repair is not
a one-line guard swap.

`StructEtaPrice.lean` §6's refutation runs at exactly that guard: its inputs are
`MutField.unitEnv_not_isProof_foo`, `unitEnv_ruleFreeHead` twice, and one eta instance
(`foo ≡ A.mk`, `foo` an axiom of the zero-field member `A : Type`).

**So the failure is not confined to proof-typed heads** — the opposite: the `¬ IsProof` guard is
*satisfied* at the witness, which is what makes the refutation work.  It is also **not confined to
zero-field structures**: §5 of the new file fires the same rule at `MutField.B`, whose constructor
has one field (`bCtor_has_a_field`), at an axiom inhabitant `bar : B`, and the eta output there is
already a `const`-headed spine `B.mk (projTermG … bar)`.  The mechanism needs only

* a non-recursive, index-free structure member satisfying the F17 level clause, and
* a `const`-headed inhabitant of it whose head is not the constructor.

Any axiom, opaque, or non-constructor definition of a structure type does it, at any arity.

**What survives** is the `IsType`-guarded row.  Both terms in the confusing pair inhabit `A : Type`;
neither *is* a type.  `MutField.unitEnv_not_isType_foo` and `unitEnv_not_isType_Amk` prove that (by
unique typing plus (A)-sort-disjointness, `const_sort_inv_of_wf`), so `VEnv.ConstNoConf`'s guard
excludes the witness from **both** orientations.  Generally: the left endpoint of *every* instance
of the eta rule inhabits a structure type (`structEta_lhs_structInhabAt`, route-independent in
`StructEtaPrice.lean` §6's sense — the typing relation is a parameter), and inhabiting a structure
type is incompatible with being a type.

---

## 2. (b) The weaker statement, and three that do not work

### The one that works: `VEnv.ConstAppInvSI`

`IsDefEq.constApp_inv`'s statement with **one guard added and nothing else changed**:

```
¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →      -- blocks proofIrrel   (as today)
¬ env.StructInhab U Γ ((VExpr.const c ls).mkApp as) →  -- blocks structEta    (new)
```

`VEnv.StructInhab` is the exact analogue of `VEnv.IsProof`: `IsProof e` says `e` inhabits a
proposition, `StructInhab e` says `e` inhabits a (non-recursive, index-free) structure type.  It is
defined through `StructInhabAt`, parametric in the typing relation, so the same guard is statable
against the thirteen-constructor relation, the fourteen-constructor one, and the closed-`VDefEq`
alternative of `StructEtaPrice.lean` §7.

Why this guard and not `IsType`: **`IsType` cannot be threaded through the spine induction.**  A
proper sub-spine of a type-valued spine has a Π type, not a sort.  `¬ StructInhab` threads, and
better than `¬ IsProof` does — at a proper sub-spine it is not inherited but *free*, because a
Π-typed term is not a structure inhabitant (`notStructInhab_of_forallE`).  So the guard costs
nothing at the sub-spines and is discharged from `IsType` at the top
(`notStructInhab_of_isType`).

*Compatibility, proved:* `MutField.etaLink` is a relation satisfying structure eta at `unitEnv`'s
zero-field member (`etaLink_eta`) **and** the `¬ StructInhab`-guarded no-confusion
(`etaLink_guarded_noConf`), while **failing** the `¬ IsProof`-guarded one
(`etaLink_not_notIsProof_guarded`).  One relation, two guards, opposite answers — that is the
sharpest form of "what eta kills is the `¬ IsProof` row", and it shows
`eta_and_constNoConf_incompatible`'s argument does not extend to the guarded statement.

### Three that do not survive — refuted, hole-free

* **`¬ IsProof` alone.**  In the tree: `constNoConf_false_for_IsDefEqSE`.
* **"exempt structure-constructor heads".**  `guard_rejects_an_axiom`: for an *arbitrary* guard
  predicate `G` on head names, any relation with `symm`, `trans` and two eta instances at two
  distinct axiom inhabitants forces `G` to reject one of the axioms.  Transitivity is the trap:
  `foo ≡ A.mk` and `foo2 ≡ A.mk` give `foo ≡ foo2`, and **the constructor does not appear in the
  violating pair at all**.  Instantiated: `exemptingCtorNoConf_false_for_IsDefEqSE`, with
  `RuleFreeHead` in the guard and discharged.
  *Corollary worth keeping:* no condition on the head alone can repair no-confusion; the guard has
  to be about the *type of the term*, which is what `StructInhab` is.
* **"only zero-field / subsingleton structures are the problem".**
  `zeroFieldOnlyNoConf_false_for_IsDefEqSE`, at the one-field member `B`, no transitivity needed.

All of §5 — the environment, its `VEnv.WF`, the three eta firings, `guard_rejects_an_axiom` and
both refutations — is **`sorryAx`-free**, so these refutations are strictly stronger than
`StructEtaPrice.lean` §6's, which is tainted.

Cones and holes (`scripts/exists.lean`, 429-module population, 2026-09-03 18:06 UTC), `after ⊆
before` on every line, `before` = the four holes `IsDefEq.constApp_inv` already reaches
(`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
`NormalEq.descend`):

| declaration | cone | holes |
|---|---|---|
| `StructInhab`, `structEta_lhs_structInhabAt` | 84 | none |
| `ConstAppInvSI` | 633 | none |
| `guard_rejects_an_axiom` | 382 | none |
| `MutField.bigEnv_wf` | 3910 | none |
| `MutField.bigEnv_structEtaSE_bar` | 3944 | none |
| `MutField.etaLink_guarded_noConf` | 3904 | none |
| `zeroFieldOnlyNoConf_false_for_IsDefEqSE` | 3979 | none |
| `exemptingCtorNoConf_false_for_IsDefEqSE` | 4282 | none |
| `notStructInhab_of_isType` | 7479 | the four |
| `notStructInhab_of_forallE`, `ConstAppInvSI.of_isType` | 7481 | the four |
| `IsStructure.spine_inv_of_si` | 7528 | the four |
| `MutField.unitEnv_not_isType_foo` | 7535 | the four |

The load-bearing replacement is *smaller* than what it replaces: the tree's
`VEnv.IsStructure.spine_inv` is cone 7538 at the same four holes, `spine_inv_of_si` is 7528.
`lake build Lean4Lean.Theory.Typing.NoConfRepair` succeeds; no root import edit was needed
(`lakefile.toml` globs `Lean4Lean.Theory.*`).

---

## 3. (c) The re-basing cost, measured 2026-09-03 17:39–17:46 UTC

`scripts/users.lean` plus a reverse-dependency **cut** over the same 427-module population
(scratch script, reverse graph with a node deleted):

| target | direct | transitive |
|---|---|---|
| `VEnv.IsDefEq.constApp_inv` | 4 | **187** |
| … with `VEnv.IsStructure.spine_inv` deleted from the graph | — | **31** |

**All four direct users are re-wrappers of the same statement** — `constNoConfNP_of_patWF`,
`constApp_inv_np_of_patWF` (both `NoConfGuard`), `constApp_inv_of_patWF` (`ConstSpine`),
`constNoConf_of_notIsProof` (`EtaUnitRefute`).  The direct count therefore measures nothing about
need, and should not be quoted as "4 places to fix".

The 31 that survive the cut, by module: `NoConfGuard` 12, `EtaUnitRefute` 5, `EtaUnitClose` 4,
`ConstSpineWF` 4, `Rigidity` 3, `ConstSpine` 3.  Every one is a restatement, a guard-equivalence, a
witness environment, or refutation scaffolding — nothing doing unrelated work.  Note what happens
to five of them: `EtaUnitRefute`/`EtaUnitClose`'s results currently *prove eta is refuted by*
no-confusion; after the repair they change sign and become the counterexample.

**The other 156 reach no-confusion only through `VEnv.IsStructure.spine_inv`**
(`Verify/Typing/ProjSpineInv.lean:57`), whose entire no-confusion use is one application of
`constApp_inv_of_wf` with guard argument `ht₁.isType henv hΓ` — an `IsType`.  It is re-derived from
`ConstAppInvSI` in the new file as `VEnv.IsStructure.spine_inv_of_si`, same type verbatim.

So the re-basing work on the *consumer* side is **one lemma**, plus re-guarding 31 statements in six
modules that are about no-confusion anyway.  The month-versus-week question is decided on the
*producer* side (§5 below), not here.

---

## 4. (d) The `addAxiom.WF` chain

`addAxiom.WF` **is** a transitive user (measured).  Its dependency path, computed rather than
grepped:

```
addAxiom.WF ← checkConstantVal.WF ← checkConstantValCore.WF ← TypeChecker.checkType.WF
  ← RecM.WF.run ← Methods.withFuel.WF ← Inner.isDefEqCore'.WF ← TrExprS.uniq ← TrProj.uniq
  ← TrProj.uniq_of_projTermCongr ← IsStructure.spine_inv ← constApp_inv_of_wf
  ← constApp_inv_of_patWF ← IsDefEq.constApp_inv
```

`addDecl.WF`'s path differs only above `TrExprS.uniq` (it comes in through
`checkPrimitiveDef.WF ← TypeChecker.rhs_val_app2`).  `Theory/Typing/DescendConstSpineK.lean:16`
records this chain as `addAxiom.WF ← … ← constApp_inv_of_patWF ← …`; the measurement fills in the
`…`, and the answer to "what does `addAxiom.WF` actually need" is:

> `IsStructure.spine_inv`, and nothing else from this family.

**And `spine_inv` needs only the surviving row.**  It applies no-confusion to the *types* of two
terms, `(const S₁ us₁).mkApp as₁` and `(const S₂ us₂).mkApp as₂` — type formers applied to
parameters — and it already holds `IsType` of the left one.  The terms structure eta confuses are
*inhabitants* of such types, which the `IsType` guard excludes.  So `addAxiom.WF` survives the
repair with one lemma rewritten, and `ConstAppInvSI` is enough for it: `spine_inv_of_si` is that
rewrite, machine-checked.

For the record, and against speculation: `Lean4Lean.kernel_sound` is **not** a transitive user of
`IsDefEq.constApp_inv` today (measured, same run).  `addDecl.WF` is.  So the exposure of
`kernel_sound` to this family runs through `addDecl.WF` and through nothing else that this
measurement can see.

---

## 5. What the repair still owes — the producer side

Not proved anywhere: `ConstAppInvSI` for a relation containing structure eta.  Two new cases, and
the rest of the Church–Rosser chain unchanged:

1. `ParRed.constApp_inv` gains an eta case, closed by the guard (a top-level eta step's redex is a
   structure inhabitant).  Eta inside an argument is already covered by the pointwise conclusion.
2. `NormalEq.constApp_inv` gains an eta case at the top, and its `appDF` case threads
   `¬ StructInhab` alongside `¬ IsProof` — via `notStructInhab_of_forallE`, which *re-establishes*
   the guard from the sub-spine's Π type instead of inheriting it.  Strictly easier than the
   threading already written.

Three named gaps:

* **(i) `IsStructureG.ruleFreeHead` does not exist.**  `scripts/shape.lean` with heads
  `VEnv.IsStructureG VEnv.RuleFreeHead`: **0 hits**, heads resolved to real constants.  Both §2
  bridges therefore carry `hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S`.
  The fix looks small: `IsStructure.ruleFreeHead`'s proof with `henv.iotaTypeNotKey D 0 0` replaced
  by `henv.iotaTypeNotKey D j 0` — the block index is already a parameter there.  **Do not charge
  this to `VEnv.Sig`.**
* **(ii) `StructInhab` transport along `IsDefEqU`** — three lines (`HasType.defeqU_l'` inside the
  existential), needed by name for step 1's guard transport.
* **(iii) `¬ IsProof` does not go away.**  `NoConfGuard.not_constNoConfUG_ncPropEnv` refutes
  no-confusion with the guards deleted, by `proofIrrel`, at a `VEnv.WF` environment with no rules.
  The repaired statement carries *both* guards.

---

## 6. Corrections to files in view (not edited — owner's call)

* `Theory/Typing/StructEtaPrice.lean` §6 says the 187 users "ha[ve] to be re-derived from a
  *weaker* no-confusion lemma carrying a side condition that excludes structure constructors (or
  excludes unit-like types).  That side condition does not exist anywhere in the tree today."
  Two corrections.  **The side condition that excludes structure constructors does not work** —
  `exemptingCtorNoConf_false_for_IsDefEqSE`, by transitivity; nor does excluding unit-like types —
  `zeroFieldOnlyNoConf_false_for_IsDefEqSE`.  And the side condition that *does* work is in the
  tree today: it is `VEnv.ConstNoConf`'s existing `IsType` guard, which the witness fails.
* Same file, §9: "`structEtaSE_foo` and `eta_and_constNoConf_incompatible` inherit `sorryAx` … 
  through the same four census holes".  Measured (`scripts/exists.lean`, this round):
  `structEtaSE_foo`'s cone **does not reach `sorryAx` at all**, and
  `eta_and_constNoConf_incompatible`'s reaches exactly **one** hole,
  `IsDefEqU.forallE_inv_stratified` — not four.
* Same file, §6, on the estimate: it prices the repair as "*deletes* `VEnv.IsDefEq.constApp_inv` as
  stated … and every one of the 187 transitive users has to be re-derived".  The measurement says
  156 of the 187 are re-derived by rewriting **one** lemma.

## 7. Recommendation

Adopt `ConstAppInvSI`: keep `¬ IsProof`, add `¬ StructInhab`, and leave every `VEnv`-facing
statement (`ConstNoConf`, `constApp_inv_of_wf`, `spine_inv`) exactly as it is.  Sequence:

1. Close gap (i) (`IsStructureG.ruleFreeHead`) — it unconditionalises both §2 bridges and is the
   only thing standing between `notStructInhab_of_isType` and a hypothesis-free statement.
2. Land `spine_inv_of_si` in `Verify/Typing/ProjSpineInv.lean` in place of the current proof, with
   `ConstAppInvSI` as a hypothesis.  At that point the 156 depend on a *statement* nobody has
   refuted, instead of on one that eta refutes.
3. Only then decide the fourteenth-constructor-versus-closed-`VDefEq` question
   (`StructEtaPrice.lean` §7).  It is orthogonal: both routes need `ConstAppInvSI`, and the guard
   in it is the same either way.

Do **not** attempt to save `constApp_inv` by a condition on the head; §5's first refutation closes
that door for every such condition at once.
