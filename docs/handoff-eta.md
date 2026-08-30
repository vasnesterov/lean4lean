# Structure eta: `structEta` in the spec, and what it unblocks

Stream owning `Theory/Inductive/Structure{,Closed,Eta,Examples}.lean`,
`Verify/StructureBridge.lean`, `Verify/TypeChecker/IsDefEq.lean`.

Every claim is tagged **[checked]** (machine-checked this round; the declaration name is given
and `lake build <module>` reproduces it) or **[source]** (read off C++ or Lean source, not
machine-checked).  Nothing is tagged from memory.

Census **19 → 19**.  No `sorry` added, none removed.  This stream's files still hold exactly
two, by name: `tryEtaStructCore.WF`, `isDefEqUnitLike.WF`.  **[checked]**,
`lake env lean scripts/sorry-census.lean`, which now runs green (the `Boundaries.lean` failure
that blocked it mid-round was another stream's in-flight edit and cleared on its own).

---

## Bottom line

1. **The redesign this round was handed — "`types : D.types = [T]` → `T ∈ D.types`, dropping
   `nm_eq`/`nmin_eq`; it is a redesign, not a substitution" — is neither.  It is a
   *refuted* repair.**  `VInductDecl'.projCore` hands the recursor exactly one motive and one
   minor premise; `VInductDecl'.recType` binds `D.nm` motives and `D.nmin` minors.  Weakening
   `types` admits blocks with `nm = nmin = 2`, at which `projTerm` is a recursor **under-applied
   by two arguments** — so `TrProj.mk`'s conclusion would name an ill-typed term and
   `TrProj.wf` (`Verify/Typing/Lemmas.lean`, *proved*) would become false.  §2.
   `MutNonRec.projCore_arity_wrong`.  **[checked]**
2. **The underlying gap is real, bigger than reported, and reachable in Lean's own kernel.**
   `MutNonRec.kernelProjChecks` runs the **kernel** (`Lean.addDecl`, not the elaborator) on three
   hand-built declarations and fails the build if any verdict changes: the kernel accepts
   `.proj` on a member of a two-type block, **performs structure eta on it**, and accepts
   `.proj` on a *recursive* one-constructor inductive.  So `IsStructure` is narrower than
   `inferProj` in **two** fields, not one — `noRec` as well as `types` — and the eta gate is
   reachable at the first.  §2.  **[checked]**
3. **What the repair actually is**: a generalisation of `projCore` to padded motive and minor
   blocks, not a weakening of a field.  §3 gives the design, including the one non-obvious
   ingredient (the dummy motive must land in `Sort ℓ` at the *field's* level and be inhabited by
   a closed term).  It is a `Theory/Inductive` + `Verify/Typing/ProjSkip` job, most of it in
   files this stream does not own.  **Not made.**
4. **The work the repair was supposed to unblock did not need it, and is now done.**
   `tryEtaStructCore.WF_of_structEta` — the **whole** statement, non-`Prop` case included —
   is proved from `c.venv.StructEta` plus one named bridge.  §4.  **[checked]**
5. **Its measured hole cone is identical to `WF_prop`'s**:
   `{TrProj.uniq, IsDefEqU.forallE_inv_stratified, IsDefEqU.weakN_iff}`, every one borrowed
   through `inferType.WF`'s appeal to unique typing.  The two new ingredients
   (`projTerm_hasType`, `StructEta.congrProj`) add **no** hole.  §4.  **[checked]**
6. Both target theorems still enter the **live** `.inductInfo`/`.ctorInfo` arm rather than the
   dead placeholder, so both survive the `AddInduct` flip verbatim; and both bridges are still
   **empty today** for the `TrEnv.not_ctorInfo` reason.  §6 keeps that recorded, unchanged.

**Kernel Arena not run, and not required**: no executable code was touched.  Edited files:
`Theory/Inductive/Structure.lean` (docstrings + four length/arity lemmas),
`Theory/Inductive/StructureEta.lean` (two theorems, one import),
`Verify/StructureBridge.lean` (one theorem, three inductives, one kernel check),
`Verify/TypeChecker/IsDefEq.lean` (one loop rule, one bridge, one theorem, docstrings).
Nothing has an `@[implemented_by]`, a `partial`, or a place in `Lean4Lean.addDecl`'s cone.

---

## 1. The relay's claim, re-audited

The incoming relay stated, correctly and machine-checked last round:

> `VEnv.IsStructure.types` (`D.types = [T]`) is FALSE of what `isNonRecStructure` accepts,
> because `isRec` is computed block-wide.

That much is confirmed (`MutNonRec.indShapeOf_not_singleton`, unchanged) and is now confirmed a
third way, against the kernel rather than the elaborator (§2).  What does **not** follow is the
relay's next sentence — "the repair is `types : D.types = [T]` → `T ∈ D.types`, dropping
`nm_eq`/`nmin_eq`".  The method note this round carried is exactly why: *auditing a statement's
binders does not audit the statements it depends on*.  `IsStructure.types` was audited against
`isNonRecStructure`, which is what it must **describe**; it was not audited against `projCore`,
which is what it must **support**.

---

## 2. Why the proposed repair is refuted  **[checked]**

`Verify/StructureBridge.lean`, `MutNonRec.projCore_arity_wrong`:

| | supplied by `projCore` | demanded by `recType j` |
|---|---|---|
| parameters | `ps` (`D.np`) | `D.np` |
| motives + minors | **2**, the pair `[mot, minor]` | `D.nm + D.nmin` |
| indices | `is` | `T.indices.length` |
| major | `e` | 1 |

`Theory/Inductive/Structure.lean` now carries the two counts as lemmas
(`VInductDecl'.length_motives`, `length_minors`), the spine length
(`length_projCore_spine`), and the recursor's arity (`recArity`,
`recArity_eq_projCore_iff`: they agree **iff** `D.nm + D.nmin = 2`).  At `decl2` — the abstract
image of a two-type non-recursive block — the theorem checks `motives.length = 2`,
`minors.length = 2`, `recArity = 5`, spine length `3`, and `¬ (nm + nmin = 2)`, all by
`rfl`/`decide`.

The consequence is not "a proof gets blocked".  `TrProj.mk`'s conclusion is
`TrProj Γ S i e (D.projTerm T C us ps ιs i e)`, and `TrProj.wf` types that term at the projected
field's type.  An under-applied recursor has a `∀`-type.  So the weakening turns a **proved**
theorem in an unowned file into a false one.

### The gap it was trying to close is real — and reachable

`MutNonRec.kernelProjChecks` (a named `CoreM` check, run by `#eval`; a changed verdict is a build
failure).  Declarations `P`/`Q` are a two-type non-recursive block with a field on `P`; `R` is
`inductive R | mk : Nat → R → R`.  Verdicts:

* `P.isRec = false`, `numIndices = 0`, `ctors = [P.mk]`, `all = [P, Q]`, `isNonRecStructure P`
  is `true`;
* the kernel accepts `fun a : P => .proj P 0 a`;
* the kernel accepts `fun a : P => rfl : ∀ a : P, a = P.mk a.0` — i.e. it **performs structure
  eta at a mutual-block member**.  This is the fact that makes the gap reachable through
  `tryEtaStructCore`, not merely through `inferProj`;
* the kernel accepts `fun a : R => .proj R 0 a`.

`infer_proj` (`~/lean4/src/kernel/type_checker.cpp:247`) never reads `InductiveVal.isRec` and
never checks that the block is a singleton; it checks only `ctors` is a singleton and the spine
length.  **[source]**, re-read this round.

**So `IsStructure` is narrower than `inferProj` in two fields.**  `noRec` was already documented
as a deliberate narrowing at `projCore`; `types` was not, and now is.  Both docstrings in
`Theory/Inductive/Structure.lean` say which side of the kernel each is narrower than, and cite
the check.  The third field, `ctors`, is **not** a narrowing: `infer_proj` and
`is_structure_like` both require a singleton constructor list.  **[source]**

---

## 3. The repair that would work, stated and not made

Generalise `projCore` to pad the motive and minor blocks.  For a projection at `T_j`, field `i`
with level `ℓ = (C.fields.getD i default).lvl.inst us`:

* motive `j` and the minor for `C` are unchanged;
* motive `k ≠ j` must inhabit `∀ ι_k, T_k ι_k → Sort ℓ`.  The obstruction is that a *closed*
  inhabitant of `Sort ℓ` is needed and none exists uniformly.  The available one is the field
  type itself: `Xᵢ := instAll (A_i.instL us) (ps ++ [proj 0 e, …, proj (i-1) e])`, which is in
  `Sort ℓ` by construction.  Take motive `k := fun ι_k x_k => Xᵢ → Xᵢ`, legal because
  `imax ℓ ℓ ≈ ℓ` in `VLevel` for every valuation (including `ℓ = 0`);
* the minor for every constructor of `T_k`, `k ≠ j`, binds its fields **and its induction
  hypotheses** (`D.ihTypes`) and returns `fun z => z`.  This is the same generalisation the
  `noRec` narrowing needs, so one change covers both fields.

Note the earlier projections here are of the ambient `e`, not of the motive's own binder, so the
`projArgs` recursion stays structural in `i` — the property `projCore`'s docstring warns must be
preserved or every `rfl` check in `StructureExamples.lean` breaks.

**Cost, honestly.**  `Theory/Inductive/StructureClosed.lean` (1657 lines, owned) re-derives every
`lift'`/`instN`/`instL` commutation over the new shape; `Verify/Typing/ProjSkip.lean` and
`Verify/Typing/Lemmas.lean` (≈2500 lines, **not owned**) carry the typing chain
(`projMinor_hasType`, `projTerm_hasType`) that would gain `nm - 1` motive and `nmin - 1` minor
obligations.  `Verify/Typing/StructureUniq.lean` (not owned) uses `H.types` in three places.
This is the reason it is stated and not made: it is a multi-file redesign whose bulk is in files
this stream must not edit.

**What it is not.**  It is not a prerequisite for anything in §4.  The eta bridge is a hypothesis
either way; generalising `projCore` changes *which* environments can discharge it, not whether
the checker obligation is proved from it.

---

## 4. What closed: `tryEtaStructCore.WF`'s non-`Prop` half  **[checked]**

The previous round named the exact failing step.  All three of its ingredients are now in the
tree, and the theorem is `tryEtaStructCore.WF_of_structEta`
(`Verify/TypeChecker/IsDefEq.lean`) — the **whole** statement, `Prop` case included.

### 4.1 `RecM.WF.forIn'Prefix` — the loop rule that did not exist

`M.WF.forIn` requires the body to `yield` every iteration; `RecM.WF.forIn'Break` allows a
`break` but deliberately does not index its invariant, so it cannot accumulate anything across
iterations.  `forIn'Prefix` indexes the invariant by the prefix already processed, splits the
body obligation (a `yield` extends the invariant by the element just handled; a `done` lands in
a separate break predicate `Br`), and concludes `Inv (pre ++ xs) ∨ Br`.  Sorry-free, and with
an **empty** hole cone.  Reusable: `isDefEqApp`'s and `isDefEqArgs`' loops have the same shape.

### 4.2 `VEnv.StructEta.congrProj` — the assembly, in the spec

`Theory/Inductive/StructureEta.lean`.  `congrSpine` (last round) wants a `HasArgsDF`; the
checker produces one `IsDefEqU` per field.  `congrProj` bridges them: `VEnv.HasArgsDF.ofMap`
over the constructor's field telescope, `HasArgsDF.append` for the parameter block, then
`congrSpine`.  The telescope is instantiated at the **left** spine — the projections — so, as
with `congrSpine`, no parameter lists are ever compared and no injectivity is needed.

`congrProj_at_projAll` is the round-trip check: at the identity spine, `congrProj` reproduces
`e ≡ D.etaExpansion T C us ps e` exactly.  A misaligned telescope, instantiation spine, or
off-by-one in the `range` would fail it while leaving `congrProj` type-correct.

`StructureEta.lean` gained one import, `Theory.Typing.UniqueTyping` (for `VEnv.WF` and
`IsDefEqU.of_l`).  Checked for cycles: `UniqueTyping`'s transitive imports reach
`Theory.Inductive.{Lemmas, Decl, Telescope, Restore}` and no `Structure*` module.

### 4.3 `EtaStructSpine` — the bridge, strengthened, and one item *removed* from it

`EtaStructBridge` (last round) is what the `Prop` half needs: two translations per iteration.
Outside `Prop` the loop's output is the whole content, so the bridge must additionally say which
abstract terms those translations land on, and supply the block data:

* `IsStructure` and the eta side conditions (`T.indices = []`, universe and parameter data,
  `e₁' : S ps`, F17);
* **the decomposition** `e₂' = (.const C.name us).mkApp (ps ++ args)` — the second ingredient the
  previous round named, supplied rather than recovered by `AppStack` inversion;
* the constructor's declared telescope split at the parameter/field boundary, and its result;
* per iteration, the two translations *pinned* to `D.projTerm … (i - np) e₁'` and
  `args[i - np]`.

A draft also carried the projections' typing.  **It is not assumed**: `projTerm_hasType`
(`Verify/Typing/Lemmas.lean`) derives `ProjHasType` at every field from `IsStructure`, the
universe data and the F17 clause, by the same two-branch level argument `TrProj.wf` uses
(`isLE = true`: `elimLvl.inst (projLvls C us k)` *is* `lvl_k.inst us`; `isLE = false`: both
sides are `.zero`, which is F17's right disjunct).  So the heaviest premise of `congrProj` costs
nothing at this call site.

### 4.4 The measured cone

Transitive `getUsedConstantsAsSet` sweep against the 19 census names, with the `.thmInfo` trap
handled:

| declaration | hole cone |
|---|---|
| `tryEtaStructCore.WF_of_structEta` | `{TrProj.uniq, IsDefEqU.forallE_inv_stratified, IsDefEqU.weakN_iff}` |
| `tryEtaStructCore.WF_prop` | the same three |
| `isDefEqUnitLike.WF_of_structEta` | the same three |
| `RecM.WF.forIn'Prefix` | ∅ |
| `VEnv.StructEta.congrProj` | `{IsDefEqU.forallE_inv_stratified}` |
| `projTerm_hasType` | `{IsDefEqU.forallE_inv_stratified, IsDefEqU.weakN_iff}` |

Every one enters through `inferType.WF`'s single appeal to unique typing.  **No structure-eta
content is borrowed, and the non-`Prop` half added no hole to the `Prop` half's cone.**

---

## 5. Non-vacuity, re-run  **[checked]**

Unchanged from last round and re-verified after the edits:

* `VEnv.empty_structEta` — the assumption is satisfiable, so a theorem taking `StructEta` as a
  hypothesis is not vacuous for want of a model of it.
* `bazEnv_structEta_premises` — **every** premise of `StructEta` at once, at the two-field `Prop`
  structure `bazDecl`, with `bazDecl.WF VEnv.empty` proved from scratch and the F17 clause
  discharged in its **small-elimination** branch (`isLE = false`, so the `.inl` disjunct is
  unavailable).  `barDecl`, the tree's other two-field structure, **fails** that clause
  (`barField0_lvl_ne_zero`), so the clause is not decorative and the witness is not free.
* `bazEnv_structEta`, `bazEnv_etaExpansion_eq`, `bazEnv_projMinors_distinct` — the rule fires,
  and the two projections it produces really are two.
* `StructureExamples.lean`'s `rfl` checks of `etaExpansion` against **Lean's own elaborator** at
  `Prod`, `Sigma` (dependent second field), `And` (a `Prop` structure), `Subtype` (dependent
  `Prop` field), plus the F17 clause in its non-trivial disjunct at `And`.  All still pass.

New this round, and weaker than the above on purpose: `congrProj_at_projAll` (§4.2) is a
consistency check on the *assembly*, not a witness for it.  **No witness is claimed for
`EtaStructSpine`**, and none exists — see §6.

---

## 6. The honest caveat, preserved

`EtaStructBridge` and `EtaStructSpine` are **currently provable for every `c`**: their premise
asks for a `.ctorInfo` under the head of a translated term, and `TrEnv.not_ctorInfo` forbids
that while `AddInduct` has no constructors.  **Today's instantiation is empty.**

What the theorems buy is that their conclusions are derived from `proofIrrel`, `StructEta`,
`congrProj` and the loop rules — never from the vacuity.  Both proofs `split` at each gate,
discharge the `return false` arms by `nofun`, and **enter** the live `.inductInfo`/`.ctorInfo`
arm.  Neither mentions `AddInduct` or `TrEnv.not_*Info`, so both survive the flip verbatim,
unlike `tryEtaStructCore_never_true`/`isDefEqUnitLike_never_true`, which are scheduled to go red
and are kept live as exactly that alarm.

The redesign in §3 does **not** convert any of this into an apparent result: it would change
which environments can supply `EtaStructSpine`, and nothing else.

---

## 7. Corrections to the incoming relay

* "**The repair: `types : D.types = [T]` → `T ∈ D.types`, dropping `nm_eq`/`nmin_eq` … It is a
  redesign, not a substitution.  You own the redesign.  Make it.**"  Refuted.  It is neither a
  substitution nor a redesign but a false step: it makes `projTerm` an under-applied recursor and
  `TrProj.wf` false.  §2.  The redesign that *is* correct is §3, and its bulk is in unowned
  files.
* "**No shape strengthening can fix it.**"  Confirmed, and for a stronger reason than given: the
  problem is not on the shape-predicate side at all, it is that `projCore` cannot express the
  situation.
* "**`isDefEqUnitLike.WF` — one of the 19**" and "**close what it unblocks**" (item 2).  Not
  closed, and it is not unblocked by anything here: `isDefEqUnitLike.WF_of_structEta` already
  had the whole statement last round, and what is missing is the same two hypotheses.  No
  progress is claimed on it.
* "**A false docstring to correct, `UnitLikeBridge` ~line 719: 'the six fields … are free'.**"
  Correct, and fixed — but the correction is not only that the fields are now pinned.  The
  docstring also gave the wrong obstruction; it now names `IsStructure.types`, cites the kernel
  check, and says why weakening it is not available.
* "**The transport lemmas carry every field of `IsStructure` except `types` and `decl` — so
  `types` is exactly the field this redesign is about.**"  True of the transport lemmas, but the
  inference does not follow: `noRec` is a second field the kernel's `inferProj` does not
  respect.  It happens not to be transported because the eta gate *does* test `isRec`; the
  `TrProj` gap is separate and is now recorded.  §2.
* Everything else checked out: `structEta`'s statement, the five `rfl` checks, the two
  non-vacuity directions, and the two `WF_of_structEta` theorems entering the live arm.

---

## 8. What to pick up first

1. **`projCore`'s generalisation** (§3).  It is the only thing standing between
   `StructureBridge` and provability, and it is now a specified job rather than an open
   question.  Needs coordination with the `Theory/Inductive` and `Verify/Typing` owners.
2. **`structEta` as an `IsDefEq` constructor.**  `VEnv.StructEta` is the statement; promoting it
   turns both `WF_of_structEta` theorems into halves of the real ones.  The coordinated
   multi-file change is described at `VEnv.StructEta`'s docstring.
3. **`RecM.WF.forIn'Prefix` at `isDefEqApp`/`isDefEqArgs`.**  Same loop shape, rule already
   proved and hole-free.
4. **Do not** close either hole vacuously, and do not weaken or build on
   `tryEtaStructCore_never_true` / `isDefEqUnitLike_never_true`.  Unchanged from last round.
