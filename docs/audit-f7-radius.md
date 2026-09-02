# Blast radius of tightening `VIndField.WF.pos`'s `some` branch (F7)

**Measurement only.  No `.lean` file was edited**; this file is the only artefact.

Ruling 159e proposes adding, to F7's `some` branch, a conjunct requiring the **stored** residual
— the residual `uniformOcc?` reads off `F.type`, as opposed to the canonical `r.args` — to be
block-free.

Tool provenance is stated per claim.  `lean_local_search` and `lean_hammer_premise` are indeed
broken here (`rg` missing).  `lean_references` works but **under-reports** (see §0), so every
census below is from a direct scan of the 374 built `.ilean` files.

## Summary table

| # | Item | Count | Verdict |
|---|------|-------|---------|
| 0 | `lean_references` records missing vs. ilean ground truth | **1**, and it is the one that matters | measured |
| 1a | `VIndField.WF.pos` usages | **52** (+1 def) | measured |
| 1b | ↳ **`some`-branch producers** — acquire the new obligation | **22**, over **11 blocks** | measured |
| 1c | ↳ **`none`-branch producers** — untouched | **22** | measured |
| 1d | ↳ **consumers** (destructure `pos`) | **8**, of which **4** enter the `some` branch | measured |
| 1e | `VIndField.WF` as a *type* (the "mentions" baseline) | **10** | measured |
| 2 | blocks in the tree whose `VIndField.WF` proof must change | **1** (`tqAuxH`) | measured (`lean_run_code`) |
| 3a | downstream statements needing **re-proof** | **0** | reasoned + census |
| 3b | statements that become **easier** | **0** — see §3, the ruling's payoff does not follow | measured counterexample |
| 3c | `restore_ownOcc` / `restore_ownHeads` consumers in `Verify/` | **0** / **0** | measured |
| 4 | is the tightening statable | **Yes, conditionally** — and it is *not* the row-113 guard | measured |

**Headline: the radius is one theorem wide.**  Exactly one block in the tree fails the tightened
clause, and it is the one written to exhibit the slack.  But **the ruling's stated payoff — that
`restore_noK` would then suffice everywhere — is false**, and I have a measured counterexample
(§3b).  Three further places where the briefing is wrong are flagged inline as **[BRIEF WRONG]**.

---

## §0 Tool fidelity — read this before trusting any count

`lean_references` on `VIndField.WF.pos` (`Lean4Lean/Theory/Inductive/Decl.lean`:335:3) returned
`total: 52`.  A scan of all 374 `.ilean` files under `.lake/build/lib/lean` returned **53**
records: 1 definition + **52** usages.  So `lean_references` returned 1 definition + 51 usages,
and the single record it dropped is

    /home/vasilii/lean4lean/Lean4Lean/Theory/Inductive/IndexedNested.lean:841
      (Lean4Lean.MRedex.TQWit.tq_hostile_field_WF)

**precisely the site ruling 159e is about.**  The module is built and its ilean is fresh (built
3 s after the source).  A stream that used `lean_references` alone here would conclude that
`IndexedNested` contains no `pos` producer, and would then cost the edit at zero.  If that is
one of today's wrong costings, this is the mechanism.

Every count below is from `python3` over the ilean JSON, cross-checked against `sed`-read source
context for each hit.

---

## §1 Consumers and producers of F7's `some` branch

The edit adds a conjunct to the `some` branch.  That makes the population split three ways, and
only one of the three is a cost:

* a **`some`-branch producer** must now discharge one more goal — a real cost;
* a **`none`-branch producer** is untouched — the `none` branch is not being changed;
* a **consumer** receives a *stronger* hypothesis and cannot break.

### 1b — the 22 `some`-branch producers, by block (measured; shape read from source)

| block | file:line | producer theorem |
|---|---|---|
| `nfnAux` | `Theory/Inductive/NestedBuild.lean`:1503, 1522, 1534 | `InductiveDeclExamples.nfnAux_WF` |
| `nfnAuxDirty` | `Theory/Inductive/RestoreBridge.lean`:837, 874, 886 | `InductiveDeclExamples.nfnAuxDirty_WF` |
| `ntreeAux` | `Theory/Inductive/NestedHead.lean`:962, 984, 994 | `InductiveDeclExamples.ntreeAux_WF` |
| `mpAux mpAuxNodeB` | `Theory/Inductive/ParamRedex.lean`:910, 937 | `MRedex.MPWit.mpAuxB_WF` |
| `accDecl` | `Theory/Inductive/DeclExamples.lean`:1624 | `InductiveDeclExamples.accIntro_WF` |
| `mutDecl` | `Theory/Inductive/DeclExamples.lean`:1720, 1741, 1751 | `InductiveDeclExamples.mutDecl_WF` |
| `wDecl` | `Theory/Inductive/DeclExamples.lean`:1807, 1829 | `InductiveDeclExamples.wDecl_WF` |
| `qnAux` | `Theory/Inductive/MemberRedex.lean`:971, 999 | `MRedex.QNWit.qnAux_WF` |
| `listDecl` | `Theory/Typing/ConstSubstNested.lean`:837 | `InductiveDeclExamples.listDecl_WF` |
| `roDecl` | `Theory/Inductive/RestoreOpWit.lean`:159 | `ROWit.ro_field_WF` |
| `tqAuxH` | `Theory/Inductive/IndexedNested.lean`:841 | `MRedex.TQWit.tq_hostile_field_WF` |

Classification method: the `some` branch is a 9-fold conjunction and the `none` branch a 3-fold
one, so an anonymous-constructor `pos := ⟨…⟩` is unambiguous by arity (`some` sites read
`⟨by decide, rfl, nofun, nofun, …, by type_tac, fun T' hT' => …, _, by type_tac⟩`).  The four
`pos := ?_` / `pos := hpos` sites were resolved by reading the discharging tactic block
(`RestoreBridge`:847 → `none`; `DeclExamples`:1624 → `some`; `StructureEta`:627/634 and
`EtaStructG`:443 → `none`, via `binders_indep := nofun`, which is only provable when
`recArg = none`).

### 1c — the 22 `none`-branch producers (untouched, listed for completeness)

`ParamRedex`:928, 989, 998 · `ProjLevelWitness`:117, 133 · `NestedHead`:952 ·
`DeclExamples`:1209, 1599 · `EtaStructG`:443 · `MemberRedex`:989 ·
`PreludeWitness`:136, 147, 208 · `ConstSubstNested`:589, 600, 828 · `CompanionResolve`:584 ·
`StructureEta`:627, 634 · `StructureUniq`:239, 262 · `RestoreBridge`:847.

### 1d — the 8 consumers

| file:line | consumer | branch |
|---|---|---|
| `Theory/Inductive/RestoreBridge.lean`:388 | `VIndField.WF.recArg_noBlock` | **some** |
| `Theory/Inductive/Lemmas.lean`:1009, 1010 | `VIndField.WF.mono` | both |
| `Theory/Inductive/Lemmas.lean`:2261 | `VInductDecl'.recField_facts` | **some** |
| `Verify/Typing/ProjClosedG.lean`:137 | `VInductDecl'.projClosedG_of_wf` | **some** |
| `Theory/SetModel/CtorTrans.lean`:760 | `SetModel.exists_blockFreeTypes` | none |
| `Verify/Inductive/CanonGapMeasure.lean`:678 | `CGMAbstract.cgm_wf_forces_escape` | none |
| `Theory/Inductive/MemberRedex.lean`:201 | `MRedex.built_wf_forces_escape` | none |

**None of these four `some`-branch consumers can break.**  `recArg_noBlock`, `recField_facts` and
`projClosedG_of_wf` all `obtain` a prefix/subset of the existing conjuncts; adding a conjunct at
the end widens the tuple.  In practice the three `obtain` patterns
(`⟨hp.1, hp.2.2.1, hp.2.2.2.1⟩`, `⟨hridx, hargl, -, -, hXi, -, hargs, hFdefeq⟩`,
`⟨-, -, -, -, honctx, hres, -, -⟩`) would need one more `-` or one more `.2` each — three
mechanical edits, not re-proofs.  `WF.mono` (`Lemmas.lean`:1002–1010) is the only structural one:
it rebuilds `pos` under `env.mono`, so it needs the new conjunct carried across a weakening.  If
the conjunct is purely syntactic (no `env`), that is `id` — free.

**Total mechanical cost of the edit, excluding §2: 4 consumer sites, 21 producer sites that
discharge by `decide`, 1 producer that becomes false.**

---

## §2 Which blocks actually rely on the slack — **exactly one**

### [BRIEF WRONG] the briefing mis-describes `storedCleanB`

The briefing says the §8.6 scan "tests `NoConsts` of stored types, which is **not the same** as
the tightened clause".  **The first half is false.**  `TQWit.storedCleanB`
(`IndexedNested.lean`:1035) is

```
D.ctorsAll.all fun p => p.2.fields.zipIdx.all fun q =>
  match D.uniformOcc? q.2 q.1.type with
  | some (_, rest) => rest.all fun a => !hasConstB K a
  | none           => true
```

i.e. **exactly the shape of the tightened clause** — trigger on the stored type, residual must be
clean.  The theorem that tests `NoConsts` of a whole stored type is a *different* one,
`tq_hostile_not_noConsts` (line 691).  The scan is the right instrument.

It is nevertheless the wrong *instantiation*, in one specific way: it is run at `K` (the companion
list, `[_nested.MI_1]`) whereas the tightened clause must be at `D.blockNames` (all members,
`[…TQ, _nested.MI_1]`).  These are not interchangeable — a stored residual mentioning the block's
**own** member passes at `K` and fails at `blockNames`.  So I re-ran it at `blockNames`.

### The right measurement (`lean_run_code`, no file edited)

`storedCleanB D D.blockNames` over every block in the tree that carries a `some`-branch producer,
plus the three cone blocks:

| block | `storedCleanB D D.blockNames` | `storedCleanB D K` |
|---|---|---|
| `nfnAux` | true | true |
| `nfnAuxDirty` | true | true |
| `ntreeAux` | true | true |
| `accDecl` | true | true |
| `mutDecl` | true | true |
| `wDecl` | true | true |
| `listDecl` | true | true |
| `pfnDecl` | true | true |
| `mpAux mpAuxNodeB` | true | true |
| `mrAux mrAuxNodeB` | true | true |
| `qnAux` | true | true |
| `roDecl` | true | true |
| `tqAux tqAuxNodeB` | true | true |
| **`tqAuxH`** | **false** | **false** |

**So: 1.**  The tightened clause is discharged by `decide` at 13 of 14 blocks — including all 11
that carry `some`-branch producers except `tqAuxH` — and is **false at `tqAuxH`**.
The strict name set changed nothing: no block anywhere in the tree stores a residual mentioning
its own member.

What must change is therefore:

* `MRedex.TQWit.tq_hostile_field_WF` (`IndexedNested.lean`:834) — becomes **unprovable**;
* its two wrappers `tq_hostile_field_WF_closed` (:917) and `tq_hostile_field_WF_staged` (:926);
* and with them §8's headline claim, exactly as the ruling's option 2 predicts.

Nothing else.  In particular **the two redex blocks are untouched, and for a reason worth
recording**: at `roRedex` and `mpRedex` the stored type is `.lam`-headed
(`(fun x : Type => roT) Prop`, `(fun x : Prop => MP #2) #0`), so `uniformOcc?` returns `none` and
the tightened clause is **vacuous**, not merely satisfied (measured: both `none`).  The clause
only ever bites when the trigger already fires, which is when the head is a block constant.

---

## §3 What breaks downstream, and what gets easier

### 3a Re-proof needed: none

Adding a conjunct to a structure field can only break producers.  Census of the things the
briefing named:

* **`Canonical`-adjacent.**  `VIndCtor.Canonical` has **15** usages, `VInductDecl'.Canonical`
  **9**, `VInductDecl'.CanonicalOwn` its two.  I could not identify a definitive set of "five"
  and will not invent one.  None of them mention `pos`: `Canonical` is `F.type = r.canonType D i`,
  a statement about the *record*, and the new conjunct is a consequence of it (if the stored type
  *is* `canonType`, its residual *is* `r.args`, which F7 already forces block-free).  So every
  `Canonical` block satisfies the new conjunct **for free** — that is the cheap general argument
  behind the 13 `true`s in §2.
* **`TeleDefEq` certificates.**  `substC_atRec_fieldTypes_defeq_of_noK` has **3** usages
  (`ParamRedex`:530, `StoredIota`:453, 536), all at `mp`/`mr`, where `NoConsts K` of the stored
  type already holds.  Untouched.
* **Obligations (A)/(B)/(C) at `nfnAux` / `ntreeAux` / `mpAuxB`.**  All three blocks read `true`
  in §2, so their `VIndField.WF` proofs gain one `by decide`.  The obligations themselves are
  stated over `VEnv.addInductR_ordered'` and never destructure `pos`. Untouched.
* **The `restore_*` family.**  Measured census: `restore_ownOcc` **3** usages
  (`IndexedNested`:302, `IndexedNested`:702, and `Restore`:1076 inside `restore_ownHeads`);
  `restore_ownHeads` **10** (4 in `IndexedNested`, 6 in `ParamRedex`), of which 5 are
  contrapositive (`*_not_ownHeads_*`).  **Neither name occurs anywhere under `Verify/`.**
  So the strengthening has no consumer on the soundness path at all; it is exercised only by
  witness files.

### 3b [BRIEF WRONG] The payoff does not follow — measured

> "which would become *easier* (the whole point is that `restore_noK` would then suffice
> everywhere)"

**This is false, and it is the most important finding in the audit.**  `restore_noK` requires
`VExpr.NoConsts K e` of the **whole** stored type.  The tightened clause constrains only the
*residual of a firing trigger*.  A companion can sit in the stored type outside any residual —
most simply, in a stored **pi domain**, which F7 does not constrain at all (F7 constrains
`r.binders`, the *canonical* binders; `VIndRecArg.exists_indep`'s entire justification is that the
stored binder telescope may differ from `r.binders`).

Measured witness, built in `lean_run_code` from §8's own pieces — `tqBinderHostile` is
`∀ (x : (fun y : Type => Prop) (_nested.MI_1 #1 Prop)), TQ #2 Prop` with
`r.binders = [Prop]`, and `tqAuxB` is `tqAuxH` with that field in place of the hostile one:

| fact | value | how |
|---|---|---|
| `storedCleanB tqAuxB tqAuxB.blockNames` | **true** — tightened clause **passes** | `#eval` |
| `storedCleanB tqAuxB tqK` | true | `#eval` |
| `hasConstB tqK tqBinderHostile` | **true** — so `restore_noK`'s hypothesis is **false** | `#eval` |
| `canonType … = tqBinderHostile` | false — not `Canonical` | `#eval` |
| `tqRestore.restore tqAuxB 1 tqBinderHostile ≠ tqBinderHostile` | **true** — the restoration *moves* it | `#eval` |

F7's remaining conjuncts at that field are satisfied — `r.binders = [Prop]` and `r.args = [Prop]`
are block-free, and the `IsDefEqType` conjunct is one `beta` in the domain, the same step
`tq_hostile_arg_defeq_prop` already proves. **That last sentence is reasoning, not a run**: I did
not construct `VIndField.WF env tqAuxB …`, and doing so would require editing a `.lean` file,
which this task forbids.  The three `#eval`s above are runs.

So after the tightening: `restore_noK` still does not cover every stored field of every
F7-accepted block, and the last row shows the gap is not even closed by `restore_ownOcc` there.
To get "`restore_noK` suffices everywhere" you would additionally need the stored **binders** to
be block-free — and *that* conjunct is the one the `none`-branch docstring and
`VIndRecArg.exists_indep` exist to forbid: the implementation's `checkPositivity` accepts
`| mk : (r : T) -> (fun _ : T => Nat) r -> T` precisely because a block constant may hide under a
redex, and `exists_indep` needs the freedom to move a binder that mentions an earlier recursive
field.  **A stored-binder conjunct is therefore not available, and without it option 2 buys the
retirement of §8 and nothing else.**

### 3c What is actually lost

§8.7's `tq_hostile_obligation_split` is the tree's only demonstration that
`substC_atRec_fieldTypes_defeq_of_noK` is strictly weaker than
`substC_atRec_fieldTypes_defeq'`.  Retiring §8 retires that separation measurement too.  That is
a loss of information, not of a proof.

---

## §4 Is the tightening statable?  Yes — and it is **not** the guard that row 113 killed

### The clause

The faithful form is **conditional on the trigger**, and that matters:

```
(∀ j rest, D.uniformOcc? (r.binders.length + i) F.type = some (j, rest) →
   ∀ a ∈ rest, D.NoBlock a)
```

It reaches into no `VIndRecArg` field: `uniformOcc?` is a function of `D`, a depth and `F.type`.
So it does **not** disturb the `IsDefEqType` pin's purpose.  Concretely the pin survives: a
stored residual may still be a block-free redex (`TQ #1 ((fun y : Type => Prop) Prop)`) that is
defeq-but-unequal to `r.args`, so the clause does not collapse `IsDefEqType` into an equation.

### Why it is a refinement of what the implementation does (read from source, not run)

`Lean4Lean/Inductive/Add.lean`:

* `checkPositivity` (:328) does `let t ← whnf t`, then `if !hasIndOcc indConsts t then return`,
  then either recurses under a pi (rejecting outright if `hasIndOcc dom`, **with no `whnf` on
  `dom`**) or requires `isValidIndApp? stats t ≠ none`.
* `isValidIndAppIdx` (:299) requires the head to be the block member, the arity to be
  `np + nindices`, the first `np` args to match the parameters **syntactically**, and then
  `if hasIndOcc stats.indConsts args[i]!` for every residual arg — a **purely syntactic** scan.

`whnf` is head-only; it does not normalise arguments.  So when the head of the stored type is a
block constant applied to matching parameters — exactly when `uniformOcc?` fires — `whnf` is the
identity (an `inductInfo` constant has no unfolding rules) and `isValidIndAppIdx`'s residual scan
**is** the proposed clause.  *That `whnf` is the identity there is reasoning, not a run:*
confirming it would need the checker executed on such a block, which is out of scope here.

### [BRIEF WRONG-ADJACENT] the row-113 objection does not apply

`Verify/Inductive/CanonGapMeasure.lean` §3 defines `cgmSynPos` — "`checkPositivity` with its
leading `whnf` deleted" — and §5's `#eval` reports that this guard **rejects the auxiliary block
`ElimNestedInductive.run` builds for `Lean.Json` and `Lean.PrefixTreeNode`**.  That is what killed
the syntactic-guard repair for row 113, and it is the objection one would expect to be raised
against ruling 159e.

**It does not apply.**  `cgmSynPos` deletes the *head* whnf, so it rejects a `.lam`-headed stored
type; ruling 159e's clause is conditional on `uniformOcc?` firing, which a `.lam`-headed type
never does.  Measured: `storedCleanB roDecl roDecl.blockNames = true`, and `roRedex` is exactly
the `cgmT`/`Lean.Json` shape (`(fun x : Type => roT) Prop`).  **Ruling 159e's clause is strictly
weaker than `cgmSynPos` and accepts the real Lean-library blocks that `cgmSynPos` rejects.**

### The one genuine statability limit

The clause is faithful *at the top of the stored type*.  `checkPositivity` also recurses under
stored pi binders, whnf'ing at each step, and rejects a syntactic `hasIndOcc dom`.  The abstract
spec has no `whnf`, so a clause that mirrors the recursion is not available — which is precisely
why §3b's `tqBinderHostile` slips through the tightened spec even though the implementation
rejects it (`hasIndOcc dom` fires on it, no whnf).  So:

* the tightening **is** statable, and closes the residual gap faithfully;
* it does **not** close the binder-domain gap, and no `whnf`-free conjunct can.

---

## Ruling, as measured

Ruling 159e's *direction* is defensible and its *cost* is genuinely small: 22 producer sites of
which 21 gain a `decide`, 4 consumer patterns gain a `-`, and one theorem plus its two wrappers
die.  Nothing under `Verify/` moves; `restore_ownOcc` and `restore_ownHeads` have no consumer
there to begin with.

But the ruling's *justification* is wrong in one load-bearing respect: the edit does **not** make
`restore_noK` suffice everywhere (§3b, measured), because the slack it removes is only the
residual half of a two-part gap and the binder half cannot be removed without contradicting
`exists_indep` and the `none`-branch design note.  So option 2 buys spec fidelity in one position
and the retirement of §8; it does not buy the simplification the ruling is paying for.

**If the simplification was the reason to make the edit, the reason is not there.**  If spec
fidelity is reason enough on its own, the edit is cheap and safe, and §4 gives the exact clause.

## Provenance

| claim | backing |
|---|---|
| all reference counts (§0, §1, §3a) | `python3` over 374 `.ilean` files; `lean_references` used once and found wanting |
| producer/consumer classification | `sed` reads of all 52 sites |
| §2's 14-row table, §2's `uniformOcc?` verdicts, §3b's 5 facts | `lean_run_code` (`#eval`, no file written, nothing built) |
| implementation behaviour (§4) | `sed` read of `Lean4Lean/Inductive/Add.lean`:255–400 |
| `cgmSynPos` rejects `Lean.Json` | quoted from `Verify/Inductive/CanonGapMeasure.lean` §5's own `#eval` error text; **not re-run** |
| "`whnf` is the identity at a firing trigger" | reasoning from the source, **not a run** |
| "F7's other conjuncts hold at `tqBinderHostile`" | reasoning, **not a run** — no `VIndField.WF` was constructed |
| no `lake build`, no guards, no `sorry-census`, no `dup-names`, no `MemberRedexScan`, no `lean_build` | as instructed |
