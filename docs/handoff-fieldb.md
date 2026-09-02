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

## 3. The two missing measurements, MADE — 2026-09-02, by the fieldB stream

Both gates §3 used to list as unknown are now measured. Everything in this section was run on
this tree; the figures are quoted from the build output, not from notes.

### 3.0 Build state, as required

- `lake build`: **1499 jobs**, exit 1. **Zero errors in `Theory/Inductive/*` or
  `Verify/Inductive/*`** (the files this stream owns). All 6 errors are in
  `Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean`, another live stream's file — not diagnosed, not
  touched.
- `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: **1423 jobs**, exit 0,
  guards verbatim and unmoved:

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

- Every declaration added below prints `[propext, Quot.sound]` or
  `[propext, Classical.choice, Quot.sound]`. **No new frozen-axiom dependency, no `sorryAx`.**

### 3.1 The consumer enumeration — the gate WAS open

The enumeration is complete by construction, not by grep: commit `823a026` touches exactly six
source files, and the post-deletion tree builds, so every consumer of a deleted lemma is inside
that diff. Consumer *sites* were then read at `823a026^` and classified by their enclosing
declaration; `lean_references` was used on the surviving symbols (`VNestedOcc.field`, `fieldO`,
`VInductDecl'.Canonical`, `VInductDecl'.CanonicalOwn`) on the current tree. Note when reading
`lean_references` output here: the LSP reports `_mcp_scratch_0.lean` / `_mcp_serial_0.lean`
duplicates of the file under the cursor; those are **not** call sites and are excluded from every
count below.

| deleted lemma | consumers (pre-deletion) | what happened to each |
|---|---|---|
| `VNestedOcc.ctor_Canonical` (`NestedBuild.lean:485`) | **1** — `VNestedOcc.member_Canonical` (`:496`) | that consumer is itself one of the three deletions |
| `VNestedOcc.member_Canonical` (`NestedBuild.lean:496`) | **3** — `VInductDecl'.Built.canonical` (`:645`), `nfnAux_canonicalOwn` (`:1426`), `nfnAuxDirty_canonicalOwn` (`RestoreBridge.lean:896`) | 1 is itself a deletion; **2 survive with their statements byte-identical**, proofs rerouted to `CanonicalOwn`'s `∉ K` premise |
| `VInductDecl'.Built.canonical` (`NestedBuild.lean:645`) | **4** — `nfnAux_ctorConstsCR_wf_general` (`RestoreBridge.lean:677`), `nfnAuxDirty_obligationA` (`:1062`), `Result.OccData.mkRestore_canonical` (`NestedOccData.lean:485`), `Result.RestoreData.mkRestore_canonical` (`NestedRestoreWit.lean:608`) | **2 survive, statements unchanged**; **2 deleted** |

Row 117d(iv)'s "four consumers" figure is confirmed exactly.

**Verdict: the gate was open.** No surviving statement was weakened. Precisely one *hypothesis*
was weakened — `VEnv.ctorConstsCR_wf_of_np_zero'` went from `hcanon : D.Canonical` to
`hcanon : D.CanonicalOwn K` — and that **strengthens** the theorem, because `CanonicalOwn`
quantifies over strictly fewer constructors (`(D.types.getD j default).name ∉ K`) and the proof
never applied the hypothesis at a companion member: it feeds `hcanon` to
`ctorConstsCR_wf_of_substC`'s bridge, which is quantified over `T.name ∉ K`. Both of its full
instantiations (`nfnAux_ctorConstsCR_wf_general`, `nfnAuxDirty_obligationA`) still go through, so
the weaker hypothesis is satisfiable and not merely weaker.

The two deleted `mkRestore_canonical`s really had **zero consumers**: `git grep mkRestore_canonical`
at `823a026^` across all of `Lean4Lean/` returns their two definitions and one prose line, nothing
else — and grep is sound for this question, since a consumer must name the lemma.

Reference counts on the current tree, for the record (definition included, scratch duplicates
excluded): `VNestedOcc.field` **25** (14 uses in `NestedBuild.lean`, 10 in `MemberRedex.lean` — one
of them added by §3.2 below; **no `Verify/` site**, every downstream read goes through
`fieldsFrom` / `member` / `field_typeR`); `VNestedOcc.fieldO` **13**; `VInductDecl'.Canonical`
**21**; `VInductDecl'.CanonicalOwn` **6**.

### 3.2 The anti-vacuity witness — NEW, and it needed a new block

`MemberRedex.lean` §7 (`DgWit`) already existed and the orchestrator's §3 did not know it: the
dead stream *did* write a degenerate-instance audit, and it survived in the commit. It covers the
`field`-level statements one at a time and is honest about the two whose hypotheses are **not**
satisfiable at the degenerate instance. What it leaves with an **empty witness column** is the row
that matters: `built_wf_forces_escape` / `built_wf_of_escape_false`, whose hypothesis set is
`Built ∧ WF ∧ addIndTypes ∧ hnone ∧ hnone2` **jointly** — i.e. the `none` branch of
`Built.member ∧ WF.pos`, which is the thing the repair is about. Neither existing witness can fill
it: `dgOcc` carries no environment, so `Built.occurs` is unreachable there, and at `MRWit` the
repair makes `hnone2` **false** (`mr_recogB`). So that row was a *claim*, and a green
`built_wf_forces_escape` could have been green for want of an instance.

**`MemberRedex.lean` §8 (`QNWit`) supplies the instance.** `QJ`/`QN` is `NestedBuild.lean`
Part 9's `PFn`/`NFn` with the higher-order field replaced by a `Prop` field — a companion field
whose substituted type is block-free and unrecognised, which is the one shape that lands in the
repaired `none` branch. It is degenerate in every coordinate ledger blindness 7 names, each
pinned by a `rfl` theorem: `qnAux_params_nil` (nil telescope), `qnAux_uvars_zero` (zero grade),
`qn_field0_ctx` (**`Γ = []`** — no parameters, and it is field `0`). And it is *not* degenerate by
emptiness: `qjAuxMk_two_fields` and `qjAuxMk_field1_recArg` show the constructor has a second
field which takes the **`some`** branch, so `fieldsFrom` is not the empty list and `Built.member`
is an equation between two-field constructors.

What is proved:

- `qjAuxMk_built`, `qnAux_member_built` — the construction computes the written-out companion
  (`rfl`), and it is anchored on Lean's own kernel: `qnNode.typeR = vconst(type_of% @QN.node)`,
  `qnAux.recTypeR qnRestore 0 = vconst(type_of% @QN.rec)`, and **`… 1 = vconst(type_of% @QN.rec_1)`**
  — the companion recursor Lean itself generated for the nested block.
- `qn_recog_none`, `qn_recog_betaHead_none`, `qn_field0_none_branch` — both recognitions fail and
  `field` lands in the repaired `none`-`none` branch, at `Γ = []`.
- `qnAux_WF`, `qnAux_builtFresh`, `qnAux_built`, `qnOcc_occurs`, `qnAux_staged_exists` — the full
  `D.WF env₂ ∧ D.Built R K env₂ occ` and the staging step, at the environment `QJ` was just
  declared into (`VEnv.empty.addInduct' qjDecl = some env₂`, discharged by `⟨_, rfl⟩`).
- **`qn_pos_none_forced`** — `built_wf_forces_escape` with **every** hypothesis supplied. So the
  repaired branch's hypothesis set is **inhabited**: the obligation is real, not empty.
- **`qn_pos_none_forced'`** — the same with the environments existentially quantified, so **no
  hypothesis is left at all**.

And the part that would have been easy to leave out:

- **`qn_escape_free`** — at this instance the `none`-branch conclusion is provable outright, for
  *any* environment, with `A := F.type` (the stored type is `Prop`, block-free on the nose). So
  the branch here is **reachable but empty**: it costs nothing.
- **`qn_not_escape_false`** — therefore `built_wf_of_escape_false`'s `hesc` premise is **false**
  at this instance, exactly as `hnone2` is false at `MRWit`. Stated rather than left to be
  inferred: after the repair the two escape theorems are a matched pair of conditionals, and
  **neither has an instance in this tree at which its residue is non-empty.** That is the honest
  reading of §7's "the one honest loss" row, and it is now machine-checked on both sides rather
  than argued on one.

### 3.3 Did deleting `Canonical` push a burden into a hypothesis? — No, and something sharper

The direct answer is **no**. The only hypothesis that moved got **weaker** (§3.1), and nothing
that used to be discharged by a theorem is now assumed. `Built.canonical` fed exactly four places
and none of them were the `hcanon : D.Canonical` hypotheses in
`Theory/Inductive/NestedRules.lean` (one section variable, ~8 consumers) or
`Theory/Inductive/NestedTele.lean` (`:2319`, `:2363`, `:3356`) — those were already hypotheses,
and their only producers were already the concrete-witness theorems `ntreeAux_Canonical`
(`NestedHead.lean:646`), `nfnAux_canonical` (`NestedRules.lean:950`), `eqIndDecl_Canonical`.

The sharper thing, which is what actually hides here:

1. **Two of the four surviving consumers changed their *evidence*, not their statement.**
   `nfnAux_canonicalOwn` / `nfnAuxDirty_canonicalOwn`'s companion-index branch went from a
   positive proof (`member_Canonical`) to `absurd … hK` — **vacuous**. `CanonicalOwn` is still
   non-trivial at those blocks, because index `0` (the user's member) is proved with real content;
   but the companion index now carries none, which is correct and is the point.
2. **`D.Canonical` is machine-checked FALSE at the block class the repair is about**, and now at
   the *block* level, which is the level every downstream hypothesis is stated at:
   **`MRedex.MRWit.mr_auxNodeB_block_not_canonical : ¬ (mrAux mrAuxNodeB).Canonical`** (new,
   `[propext, Quot.sound]`). So at a block whose companion carries a redex-headed recursive field
   — **3 blocks in the running environment**: `Lean.Json`, `Lean.PrefixTreeNode`,
   `MRedex.MRWit.MJ` — every `NestedRules.lean` / `NestedTele.lean` statement carrying
   `hcanon : D.Canonical` is **vacuous**, and the `D.Canonical` conjunct of the
   `AddInductive.run` specification (`Verify/Inductive/RunIdentity.lean:468`, `:487`, `:506`,
   `Verify/Inductive/AddInductiveStep.lean:406`) is **unprovable** for them. (Those four are on
   the `res.aux2nested = []` path, so they are not *reached* by a nested block today — but that is
   a scope limit, not a discharge.) This is not a burden the deletion moved; it is a falsity the
   deletion **revealed**, and the deleted lemma was the thing hiding it.
3. **The deletion removed the only stated bridge from checker data to `D.Canonical`** — both
   `mkRestore_canonical`s. They had zero consumers, so nothing broke; but the consequence is that
   `hcanon` now has *no* route from `Result` / `OccData` / `RestoreData`, before or after.

Ruling 116d's real cost is still where row 117c put it, and it is untouched by this round:
`VInductDecl'.Built.fields_noK` has **no producer except `decide` at a concrete block**.

### 3.4 "3/3 coverage, no divergence" — it did not exist as a statement; it does now

The orchestrator was right to distrust it. `Verify/Inductive/MemberRedexScan.lean` §2's coverage
`#eval` was **`logInfo`-only** — all 7 `throwError`s in the file were in §1 (the ground-truth
read), and both branches of the coverage `if` merely printed. So "47 blocks / 790 fields /
3 defects / 3 covered / 0 residual" was a *report*, exactly the failure ledger row 118f records
against another stream. **Repaired this round**: the coverage `#eval` now carries four
`throwError` guards —

- population non-empty (`tried`, `fields`), and
- `defect ≠ 0` — the anti-vacuity dual, because a scan finding nothing to fix would satisfy the
  other two trivially (row 118d's "a reject-everything check passes every other instrument"), and
- `defect = covered`, and
- `residual = 0`.

Current guarded output (the population grew by one block and three fields because §3.2 added
`QJ`/`QN` to the environment): **48 safe blocks with a nested-shaped field, 793 auxiliary
constructor fields, 3 defects in 3 blocks (`MRedex.MRWit.MJ`, `Lean.Json`,
`Lean.PrefixTreeNode`), 3 of 3 covered, residual 0** — and if any of that moves, the file no
longer builds.

"**No divergence**" is a *different* claim and there is still **no machine-checked statement of
it** — nor can there easily be one, since it is a claim about what the implementation does *not*
do. What supports it is checkable and weaker than a theorem: commit `823a026` touches no
implementation file at all (six source files, all in `Theory/Inductive/` and `Verify/Inductive/`),
so nothing `ElimNestedInductive` writes moved; only what the *recogniser* reads. Treat it as a
diff-level fact, not a proved one.

## 4. What I would pick up first

1. **`Built.fields_noK`.** It is the one hypothesis in this corner with no producer at all
   (row 117c), and §3.3 confirms nothing this round shrank it. Row 117b's ~150-line companion-half
   `Nodup` derivation is the *other* new clause and is at least reachable; `fields_noK` is not.
2. **The two escape theorems now have no instance with a non-empty residue** (`qn_not_escape_false`
   plus `mr_recogB`). Either find a block where a redex sits **under a binder** or needs **δ** —
   the named residue, measured empty in the running environment — or accept that
   `built_wf_forces_escape` / `built_wf_of_escape_false` are now bookkeeping rather than
   obligations, and say so in the ledger.
3. **`hcanon : D.Canonical` in `NestedRules.lean` / `NestedTele.lean` is vacuous at the three
   redex blocks** (§3.3 item 2). Those statements are the iota-rule layer; if the nested path is
   ever to reach them, `Canonical` has to be replaced there the way `typeR` replaced it in
   `NestedHead.lean` — restate over the *stored* telescope. That is ruling 116d applied one layer
   further out, and it is a design question for the orchestrator, not a proof I should make
   unilaterally.
4. **A ledger row.** Rows 119c/119e need amending: 119c's "two of their four consumers stay true
   and just lose their general proof" is right in count but understates the mechanism (the two
   `nfn*_canonicalOwn`s keep their *statements* and lose their *content at the companion index*),
   and 119e's `ctor_Canonical`/`member_Canonical`/`Built.canonical` row should carry
   `mr_auxNodeB_block_not_canonical` as its block-level witness. I have not edited the ledger — it
   is the orchestrator's file.

### What I tried that failed, and where

- **Instantiating `built_wf_forces_escape` at an existing witness.** `nfnAux` and `nfnAuxDirty`
  already carry a full `WF ∧ Built ∧ addIndTypes` at `params = []`, `uvars = 0`, and field `0`'s
  `Γ = []` — they *are* the degenerate instance. It fails at `hnone`: **both** fields of
  `pfnAuxMk` are recognised (`recArg = some`), so the `none` branch is not reached, and
  `nlistNil` has no fields at all while `nlistCons`'s two are both recursive. **No companion
  constructor in the tree had a `none`-branch field**, which is why §3.2 needed a new block rather
  than an instantiation. That is worth knowing before anyone tries the same shortcut.
- **`DgWit` cannot be extended to carry `Built`.** `Built.occurs` needs
  `VNestedOcc.Occurs env`, which needs `N.decl.Declared env` and `env.constants N.tyName = …`;
  `dgOcc` was built without an environment and `dgDecl` is never declared into one. Extending it
  would have amounted to rebuilding `QNWit` inside `DgWit`, so `QNWit` is a separate namespace.
- **Four elaboration failures in `QNWit`**, all shallow and all fixed: the `some`-branch `pos`
  needed `OnCtx ⟨trivial, _, by type_tac⟩` rather than `trivial` (field `1`'s context is
  `[Prop]`, not `[]`); `Built.own` was missing; `qnRestore_ownId` needed `omit h in`; and
  `qn_fresh` / `qnAux_staged_exists` needed the section variable *kept* rather than omitted.
- **`by decide` cannot prove `(1, mrAuxNodeB) ∈ (mrAux mrAuxNodeB).ctorsAll`** (no `Decidable`
  instance reachable); `rw [show … = […] from rfl]` then `List.Mem.tail _ (List.Mem.head _)`
  works.

