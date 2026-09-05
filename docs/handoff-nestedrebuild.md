# handoff-nestedrebuild — residual B of `InductiveMapGate`: the nested rebuild branch (`numNested ≠ 0`)

Stream: NestedRebuild. Started 2026-09-05, HEAD `9438e39` (bare build green 1668 jobs, guards 1/2/3 ✓, census 13).

Owned: `Lean4Lean/Verify/Inductive/NestedRebuild.lean` (new), `Lean4Lean/Verify/Inductive/InductMap.lean`
(existing — may discharge its residual), `docs/handoff-nestedrebuild.md` (this file).

Target: `InductMap.lean` reduced `InductiveMapGate` to one residual — the `numNested ≠ 0` (nested
rebuild) branch of `inductDecl`. Five sub-obligations are itemised in `docs/handoff-inductmap.md` §3.2
and characterised there as "all either already proved elsewhere or invariants on loops written out
here". **First act, per the previous round's own words: check that residual B is _satisfiable_ at a
real nested block.** If `numNested ≠ 0` is unreachable/vacuous at every nested block the code path
can present, the ~400–500 lines behind it are not worth writing, and that is the round's result.

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `InductMap.lean`, `docs/handoff-inductmap.md`, `AddInductive`/`Verify/Inductive/*`,
or any `Theory/Inductive/*` in this session.** The only inputs are `CLAUDE.md`, the orchestrator's
brief, and the header of an unrelated handoff (`handoff-binderscan.md`) read solely for this file's
format. Answers are appended below the questions once measured. **Filled answers are never edited;
corrections go in §2.**

### The four shape questions, instantiated

**Q1. Does the target exist — by *conclusion head*, not by obligation name?**
The thing I must prove is not named "residual B". Its conclusion head is whatever `InductiveMapGate`
unfolds to at the `inductDecl` branch: presumably, for every constant `n` that the nested-rebuild
path writes into `env'`, `∃ k, ...` relating `env'.find? n` to a member/ctor/`mkRecName` name plus the
`ci.name = n` well-keying clause. So: **what is the conclusion head of the general theorem**, and does
something with that head already exist — e.g. `AddInductive.WF_run` (arity 5, cone 8746, hole-free)
already says every constant `AddInductive.run` writes is a member name, a ctor name, or `mkRecName` of
a member. If the nested rebuild path *goes through* `AddInductive.run`, residual B may be a corollary
of an existing lemma rather than 500 new lines. If it instead writes constants *outside* `run` (the
"rebuild" — auxiliary recursors, `numNested` unfolding), those extra writes are the whole job.
Does the repo already have a lemma whose conclusion head covers those extra writes?

**Q2. Is the work in the direction I think?**
I am assuming the residual is *unproved but true*, and that the five sub-obligations are real.
Alternatives to rule out, in this order:
(a) **Vacuity** — `numNested ≠ 0` is unsatisfiable on this path (e.g. the checker rejects nested
    declarations earlier, or `numNested` is provably `0` wherever the gate is invoked, or the branch
    is guarded by an error return). Then residual B is discharged by `absurd`/`nomatch` and costs
    ~10 lines, not 500.
(b) **Under-hypothesised** — the residual as *stated* is false / unprovable because it omits a
    hypothesis its six unconditional sibling branches carry (this happened this week). Diff residual
    B's hypotheses against the six unconditional branches' before attempting it.
(c) **Genuinely 500 lines.**
Concretely: **is `numNested ≠ 0` reachable, and what is the smallest witness** — a real nested block
(`Expr`/`InductiveType` data) for which the checker's nested-rebuild branch is actually taken?

**Q3. Measurement or docstring?**
Which of my beliefs come from prose versus from measurement? The brief explicitly warns that
"all either already proved elsewhere or invariants on loops written out here" is **unchecked prose**
of exactly the shape that cost two rounds a target this week. So for each of the five sub-obligations
in `handoff-inductmap.md` §3.2 I must classify: *(i)* a named lemma that compiles today (record name,
arity, cone), *(ii)* a lemma that exists but whose statement does **not** match what the residual
needs (record the mismatch), or *(iii)* prose with no referent. I predict the split before looking.
Also to classify: `elimNoAuxGate` is stated to be top-level and **not** under `AddInductive` —
measured or asserted? And is the gate's `∃ k` really per-name (so auxiliary-recursor count must not
be matched against `numNested`)?

**Q4. What does the implementation compare with, and is it opaque?**
Where does the nested rebuild path branch on a comparison, and is that comparison decidable?
Candidates: `Name` equality (the `ci.name = n` clause is load-bearing precisely because `SMap.WF`
does not forbid mis-keyed entries), `BEq Expr` = `Lean.Expr.eqv` (`@[extern] opaque`, alpha-equivalence
only, never `decide`-able), `PersistentHashMap.containsAux`/`findAux` (`partial`), and the loop that
replaces nested occurrences by the auxiliary type (which surely compares head constants). Per
`CLAUDE.md`'s 2026-09-04 corollary, if the proof stalls on one of these the **preferred** move is to
restate the obligation around it, not to replace the function. So: **which opaque/partial comparisons
does residual B's proof have to route around, and can the statement be restated to avoid each?**
Note also the structural gift: `Lean.SMap.WF.insert`'s freshness hypothesis is unused in its own proof
(the binder is literally `_hn`), so `env'.constants.WF` should be free — measured or asserted?

### Numbered predictions, made cold (to be confirmed or refuted by measurement)

- **P1 (satisfiability — the round's first measurement).** Is `numNested ≠ 0` reachable at a real
  nested block on the path the gate quantifies over?
  Prediction: **yes, satisfiable** — `CLAUDE.md` insists the main theorem covers nested inductives and
  says a real Lean soundness bug lived there, so I expect the checker does implement the rebuild and
  the branch is live. Confidence: medium. Falsifier I will look for: a guard upstream of the branch
  that returns an error (or forces `numNested = 0`) before the gate's hypotheses can hold; or
  `numNested` computed by something that is provably `0` under the gate's hypotheses.
- **P2 (the §3.2 five, classified).** Of the five sub-obligations I predict the split
  (i) already-compiling lemma / (ii) exists-but-mismatched / (iii) prose-only is: **2 / 1 / 2**.
  (Rationale: `AddInductive.WF_run` plausibly covers 2 outright; the brief's warning that this exact
  characterisation was unchecked twice this week makes ≥1 prose-only very likely.)
- **P3 (hypothesis diff).** Residual B carries **the same** hypotheses as the six unconditional
  branches, plus `numNested ≠ 0`. Prediction: same-plus-one, i.e. *not* under-hypothesised —
  confidence low-medium, since the brief flags (b) as a live failure mode. Falsifier: a hypothesis
  present in all six unconditional branches and absent from residual B's context.
- **P4 (extreme instantiation, per Method rule 2).** Instantiating every universally quantified
  numeral at 0 and at the boundary: I predict the **`numNested = 1` case is already the general case**
  (no arithmetic induction on `numNested` is needed beyond a `List`/`Array` fold invariant), and that
  the `k = 0` instantiation of the gate's per-name `∃ k` is the one the rebuild writes use.
  Falsifier: a sub-obligation whose statement is only true for `numNested ≤ 1`.
- **P5 (size).** If P1 says satisfiable and P3 says well-hypothesised, the honest proof cost is
  **≥ 400 lines** and I will finish a fraction of it. Prediction of what I actually land: the
  satisfiability answer + the classified table + the *statement* of `NestedRebuild`'s main lemma with
  its loop invariant, and 1–2 of the five sub-obligations closed. I predict I do **not** discharge
  `InductMap.lean`'s residual this round. Confidence: medium-high.
- **P6 (`env'.constants.WF` is free).** Prediction: confirmed — `_hn` unused, so the `SMap.WF`
  component of residual B costs ~2 lines and the real work is entirely the `ci.name = n` well-keying
  plus the member/ctor/`mkRecName` classification.

### Scorecard (filled at the end)

| # | Prediction | Outcome |
|---|---|---|
| P1 | satisfiable | |
| P2 | 2 / 1 / 2 | |
| P3 | same-plus-one | |
| P4 | `numNested = 1` general | |
| P5 | ≥400 lines, land a fraction | |
| P6 | `constants.WF` free | |

---

## §2 — Measurements and corrections (append-only)

### M1 (2026-09-05) — **P1 CONFIRMED: residual B is satisfiable, and non-vacuously so.**

The round's mandated first act. `#eval`, run against the running kernel environment
(`(← getEnv).toKernelEnv`), on a block that is genuinely nested and whose names are *fresh* in that
environment (the existing `NFn` witness in `Verify/Inductive/NestedRestoreWit.lean` §1.1 cannot be
used here: `NFn` is already declared in that environment, so `addInductive`'s `checkName` would
reject it — that witness only exercises `ElimNestedInductive.run`, which does no name check):

```
inductive NTreeX | node : List NTreeX → NTreeX
  -- name := `NTreeX, type := .sort (.succ .zero)
  -- ctor  := `NTreeX.node : (List.{0} NTreeX) → NTreeX
```

Two facts, both from the same `#eval`:

1. `(ElimNestedInductive.run 1000 0 [ntreeIndType] kenv).run' {lvls := [], newTypes := #[…]}`
   returns `.ok res` with **`res.aux2nested.length = 1`**, keys `[_nested.List_1]`, and
   `res.types = [NTreeX, _nested.List_1]`. So `numNested = 1 ≠ 0` — residual B's third hypothesis
   (`∀ res, … → res.aux2nested ≠ []`) **holds** at this input, and the state is *the one
   `addInductive` itself passes* (`Inductive/Add.lean`:1146–1147), not an approximation.
2. `Lean4Lean.Environment.addInductive kenv [] 0 [ntreeIndType] false false` returns **`.ok env'`** —
   the full nested path, rebuild and both re-check passes included, **accepts**. The names `env'`
   holds that `kenv` did not are exactly

   ```
   NTreeX, NTreeX.node, NTreeX.rec, NTreeX.rec_1
   ```

So residual B's premises are jointly satisfiable at a real nested block: it is **not vacuous**, the
~400–500 lines behind it are not wasted, and the conclusion it must deliver is non-trivial (4 new
names, one of which — `NTreeX.rec_1` — is the *renamed auxiliary recursor*, i.e. exactly the write
that `AddInductive.WF_run`'s member/ctor/`mkRecName` classification does **not** cover).

Corollary measured at the same time, and it is the shape of the whole proof: the auxiliary member
`_nested.List_1` and its constructor/recursor are **not** in `env'`. The `StateT.run (s := env)`
discards the intermediate environment, so the rebuild's writes are *four* names, not seven.

### M2 (2026-09-05) — the five sub-obligations of `handoff-inductmap.md` §3.2, classified. **P2 REFUTED (2 / 1 / 2 predicted; measured 1 / 1 / 3), and one item is graded wrong in the source doc.**

Legend: **(i)** a named lemma that compiles today; **(ii)** a lemma exists but its statement does not
match what residual B needs; **(iii)** prose with no referent.

| §3.2 item | class | measured |
|---|---|---|
| 1. the branch discards `AddInductive.run`'s env and rebuilds from `env` | **(i)** | true, and now *doubly* measured: `Inductive/Add.lean`:1156 is literally `StateT.run (s := env)`, and M1's new-name list contains **no** `_nested.List_1*` constant — the auxiliary member, its ctor and its recursor are in the discarded environment only. |
| 2. the last two `add` sites "budgeted by inspection" | **(iii)** with a gap | half of it *is* inspection: `mkAuxRecNameMap` (`Add.lean`:901–918) writes `newRecName := appendIndexAfter' (mkRecName mainName) nextIdx` with `nextIdx` running `1,2,…`, and `auxRecName types k = appendIndexAfter' (mkRecName (types.headD default).name) (k+1)`, so range ⊆ budget by `rfl` once `mainName = (types.headD default).name`. The other half is **not** inspection: `processRec` is also run over `recNames'`, whose elements are `mkRecName` of the *auxiliary* members, i.e. `_nested.…​.rec` — **outside** `indDeclNamesN` for every `k`. Their budget-safety depends on `recNameMap'.lookup` **succeeding** at every element of `recNames'`; a `lookup` miss writes `_nested.….rec` itself and refutes the gate. That is a two-clause loop invariant of `mkAuxRecNameMap` (`recMap`'s domain ⊇ `oldRecNames`; `recMap`'s range ⊆ `auxRecName types '' ℕ`), not an inspection. ~40 lines. |
| 3. `ind.name = indType.name` and `ind.ctors = …` "have to be derived", from `DeclareStages`' positive clauses + `run_prefix` | **(ii)** | the three lemmas exist and are unconditional: `Lean4Lean.AddInductive.M.WF.declareInductiveTypes`, `Lean4Lean.r113e_ctorOuter_WF` (used via `Lean4Lean.AddInductive.WF_declareConstructors`), `Lean4Lean.ElimNestedInductive.run_prefix`. But the two halves are **not symmetric**, contra §3.2's wording: `r113e_ctorOuter_WF`'s freshness clause is `∀ t ∈ ts, ∀ ctor ∈ t.ctors, env.find? ctor.name = none` — quantified over `ts` **directly, no zip**, so the constructor half needs nothing from item 4. The member half is `AddInductive.M.WF.declareInductiveTypes`, whose per-`j` clause is guarded by `stats.nindices[j]? = some ni`. So item 4 is owed by *one* of the two halves, not both. |
| 4. `stats.nindices.size = its.size` | **(iii)** | prose-only, no lemma anywhere (`grep nindices Lean4Lean/Verify` finds `r113eIndInfos`, `r113e_indInfos_getElem?`, `r113eIndInfos_name`, and nothing about the size). The invariant is `stats.nindices.size = dIdx` on `checkInductiveTypes.loopInd` (`Add.lean`:205–256, one `nindices.push` per member at :248 from `default.nindices = #[]`), needing an `M`-level frame lemma that the inner `loop` (:211–236) hands its continuation a `stats` with `nindices` unchanged — `nindices` there is a *separate* `Nat` accumulator, so the frame is real but shallow. ~100–150 lines given §2's eleven CPS frames. |
| 5. a `StateT Environment (Except Exception)` analogue of §1's delta calculus, plus three loop rules | **(iii)** | prose-only, and routine: `DeltaCore` is already `StateT`-shaped in spirit (`wf`/`mono`/`keyed` are all about two environments), so the analogue is the same three fields with the state threaded. ~120 lines. |

**Correction to `handoff-inductmap.md` §3.2's grading of item 4.** That doc lists item 4 as
machinery needed to *use* the positive clause, and closes with "nothing in it looks false". Measured,
item 4 is stronger than that: **it is the only barrier between residual B and outright falsity.**

The gate quantifies over *every* `env` with `env.constants.WF`, and (this doc's own §1 Q4, and
`InductMap.lean`'s §1 second design point) `SMap.WF` does **not** forbid a mis-keyed entry. Take an
`env` holding `.inductInfo ind` under key `types[0].name` with `ind.name = weird ∉ indDeclNamesN types k`
for every `k`. Then on the nested branch:

* `env'.find? types[0].name = some (.inductInfo ind)` (the entry is inherited, `DeltaCore.mono`);
* the rebuild's `let some (.inductInfo ind) := env'.find? indType.name | unreachable!` succeeds,
* `checkName ind.name` passes (`env` does *not* hold key `weird`),
* and `modify (·.add <| .inductInfo { ind with all := allIndNames })` writes at key **`weird`**.

That is `DeltaCore.keyed` violated, i.e. residual B false. The **only** thing that rejects such an
`env` is `checkName info.name` inside `declareInductiveTypes` (`Add.lean`:298) — and that fires at
index `j` only if the `Array.zipWith indTypes stats.nindices` (`Add.lean`:289) *reaches* `j`. So
`nindices.size = indTypes.size` is not bookkeeping; it is what makes the statement true. The
implementation agrees: `Add.lean`:254 is `assert! stats.nindices.size == indTypes.size`, and a fired
`assert!` in this monad hands the continuation `default`, whose `nindices` is `#[]` — i.e. **zero**
members checked and zero declared.

Consequence for sequencing: item 4 must be done **first**, not last. Items 2 and 5 are independent of
it; item 3's constructor half is independent of it; item 3's member half and the whole
truth of residual B are downstream of it.

### M3 (2026-09-05) — what was written, and what it costs

`Lean4Lean/Verify/Inductive/NestedRebuild.lean`, new, 555 lines, **no `sorry`**, no warnings.
Bare `lake build`: **green, 1670 jobs** (was 1668; +2 is the new module's `olean`/`ilean`).
Guards **1 ✓ / 2 ✓ / 3 ✓** (guard 1: 24 frozen axioms; guard 2: whitelist ✓, proof INCOMPLETE —
`sorryAx` present, unchanged; guard 3: 2/2 implementation gaps). `scripts/sorry-census.lean`
**TOTAL 13**, unchanged, and `Lean4Lean.Verify.Inductive.NestedRebuild` does not appear in it.
Every new declaration's axiom set is a subset of `[propext, Classical.choice, Quot.sound]`, all three
already inside `Guard.lean`'s whitelist (checked against the guard's own printed output, not assumed).

| name (as `scripts/exists.lean` prints it) | arity | cone | what it is |
|---|---|---|---|
| `Lean4Lean.auxRecName_mem_indDeclNamesN` | 3 | — | `j < k → auxRecName types j ∈ indDeclNamesN types k` |
| `Lean4Lean.indBudget_auxRecName` | 2 | — | the `∃ k` instantiated **per name** at `j+1` |
| `Lean4Lean.SWF` | 5 | — | the `StateT Environment (Except Exception)` delta triple (§3.2 item 5) |
| `Lean4Lean.SWF.bind'` | 11 | 100 | composition at a *constant* invariant `DeltaCore e₀ · B` |
| `Lean4Lean.SWF.checkName'` | 5 | 6180 | freshness from the check to the `add`; `env.constants.WF` is **not** a hypothesis (the delta supplies it) |
| `Lean4Lean.SWF.addStep` | — | — | one `add`, via `DeltaCore.add_of` |
| `Lean4Lean.SWF.forM'` | — | — | the loop rule at a body that asks nothing of the state |
| `Lean4Lean.forIn_auxRecFold` | 2 | — | the two-`mut` `for` in `mkAuxRecNameMap` **is** a fold |
| `Lean4Lean.auxRecFold_inv` | 6 | 1657 | the three-clause loop invariant (range ⊆ `auxRecName`, dom ⊇ `oldRecNames`, `1 ≤ idx`) |
| `Lean4Lean.mkAuxRecNameMap_spec` | 6 | 2573 | §3.2 item 2's missing half, discharged |
| `Lean4Lean.mkAuxRecNameMap_panic` | — | — | both conclusions at `default`, so the two panic branches need no side condition |
| `Lean4Lean.indBudget_processRec` | 5 | 979 | the budget of a `processRec` write, either call site |
| `Lean4Lean.RunFreshGate` | 0 | 1 | **the named barrier** — three fields, `member` / `ctor` / `ctors` |
| `Lean4Lean.inductInfo_name_eq` | 12 | 8750 | the mis-keying hole, closed from `RunFreshGate.member` + `WF_run` |
| `Lean4Lean.ctorInfo_name_eq` | 12 | — | the same step at a constructor |
| `Lean4Lean.rebuild_indWrite_budget` | 15 | — | **write site 1** (`Add.lean`:1172) budgeted |
| `Lean4Lean.rebuild_ctorWrite_budget` | 19 | 8777 | **write site 2** (`:1177`) budgeted |
| `Lean4Lean.rebuild_recWrite_budget_user` | — | — | **write site 3** (`:1167`, user member) budgeted, **no gate** |
| `Lean4Lean.rebuild_recWrite_budget_aux` | 10 | 2693 | **write site 4** (`:1167` via `recNames'.forM`) budgeted, **no gate** |

Cones are as of 2026-09-05 at HEAD `9438e39` + this file, and are **not** invariant across a module
move. Blank cells are names I did not put through `exists.lean` individually.

### M4 (2026-09-05) — `RunFreshGate` priced. `exists.lean` called it out and it was right to.

`scripts/exists.lean` prints, for a bare `Prop`: *"NO PROOF TERM: cone is type-constants only; it says
NOTHING about satisfiability — price the witnesses."* So §5.2 prices it: a `#eval` runs
`AddInductive.run 0 res.types 1` on the expanded `NTreeX` block and **throws** unless all three fields'
instances hold there. Measured: they do, at both members (`NTreeX` and `_nested.List_1`) — member
names fresh in the input environment, constructor names fresh, `ind.name = t.name` (i.e. the entry
`AddInductive.run` actually stores is **not** mis-keyed), and `ind.ctors = t.ctors.map (·.name)`.
That is not a proof of the gate — the gate is universally quantified — but it rules out the failure
mode §1's Q2(b) names, which had already cost two rounds this week.

### M5 (2026-09-05) — the limits of this result, stated

1. **`InductMap.lean` is unchanged.** I removed nothing from it. Residual B is still its hypothesis
   `GB`, and `inductiveMapGate_of` still carries it. What this round did is split `GB` into a
   *named* barrier (`RunFreshGate`, three fields) plus monadic plumbing, and discharge four
   name-budget obligations and one loop invariant outright. The honest statement is that residual B
   is now **strictly smaller and its false-branch is identified**, not that it is closed.
2. **The four write-site budget lemmas are about the *names*, not about the `do`-block.** Each takes
   the read-back `ConstantInfo` as a hypothesis and concludes `indBudget types (written name)`.
   Assembling them into `SWF … (StateT.run (s := env) …) …` is what remains, and it needs two things
   §3 does not yet have: a `forIn`-shaped loop rule (`SWF.forM'` is `List.forM`; the rebuild uses
   `for indType in types do`, which elaborates to `forIn`, and §4's `forIn_auxRecFold` shows the
   conversion is a three-line induction but has to be done per shape), and the `run_prefix` bridge
   from `res.types` to `types` at each of the two `htt` hypotheses.
3. **`RunFreshGate.ctor` is provable now and I did not prove it.** `r113e_ctorOuter_WF`'s freshness
   clause is unconditional, and `DeltaCore.mono`'s contrapositive lifts `e₁.find? = none` back to
   `c.env.find? = none`. What blocks it is only that it must be threaded through `WF_run`'s CPS
   skeleton with a *constant* postcondition, i.e. a second pass over the eleven §2 frames. ~60 lines.
   `RunFreshGate.member` and `.ctors` both need `stats.nindices.size = indTypes.size` first.
4. **The two `TypeChecker.M.run` re-check passes at the end of the rebuild are not analysed at all.**
   They write nothing to the constant map, so they cannot violate the budget — but that is an
   inspection, not a lemma, and `SWF` has no rule for them yet.
5. **The satisfiability witness is one block.** `NTreeX` has `nparams = 0`, one member, one
   constructor, one nested occurrence, and `numNested = 1`. It does not exercise `numNested ≥ 2`,
   mutual blocks, or parameters, so it prices residual B's premises but does not survey them.

### Revised cost estimate

`handoff-inductmap.md` said 400–500 lines. Measured after doing the cheap third: **the remaining work
is ~380 lines** — `nindices` invariant 130, `RunFreshGate.ctor`/`.ctors` from it 90, `forIn` loop rules
and the block assembly 130, `run_prefix` bridging 30 — on top of the 555 written here, of which about
200 are prose. The sequencing correction in M2 matters more than the number: item 4 first.

### Scorecard (filled 2026-09-05)

| # | Prediction | Outcome |
|---|---|---|
| P1 | residual B satisfiable | **CONFIRMED** (M1), and made a build-time guard. `addInductive` accepts a real nested block with `numNested = 1`, adding exactly the 4 budgeted names. |
| P2 | §3.2's five split 2 / 1 / 2 | **REFUTED** — measured **1 / 1 / 3** (M2). I over-credited the doc; the brief's warning was right and my prediction hedged against it by only one item. |
| P3 | residual B same-hypotheses-plus-one, i.e. not under-hypothesised | **HALF-RIGHT, and the wrong half is the interesting one.** It carries no *missing* hypothesis, so as a Lean statement it is well-formed; but it is **false without item 4**, which is failure mode (b) arriving by a different door than I predicted (a missing hypothesis in the *implementation's* reachable states, not in the statement). |
| P4 | `numNested = 1` is already the general case | **CONFIRMED so far** — nothing in the four write-site lemmas or the `mkAuxRecNameMap` invariant needs `numNested ≤ 1`; the `∃ k` is per-name (`indBudget_auxRecName` instantiates it at `j+1` independently of `numNested`), and `auxRecFold_inv` is uniform in the list length. Limit: not tested against a `numNested ≥ 2` block. |
| P5 | ≥400 lines; land satisfiability + table + main statement + 1–2 sub-obligations; do **not** discharge the residual | **CONFIRMED, at the upper end of the range.** Landed: satisfiability (guarded), the classified table, item 2 discharged (`mkAuxRecNameMap_spec`), item 5 discharged (`SWF`), all four write-site budgets, and item 3's reduction from a named gate. Not landed: items 4 and the block assembly. The residual is **not** discharged, as predicted. |
| P6 | `env'.constants.WF` free because `_hn` is unused | **CONFIRMED and used** — `SWF.checkName'` and `SWF.addStep` take no `env.constants.WF` hypothesis at all; the delta's own `wf` field supplies it at every step, which is why §3 is 100 lines and not 200. |

### §2.1 Method gaps of *this* round

1. **The cheapest instrument was cheap and I still nearly skipped it.** M1 took one `#eval` and
   ~10 minutes and it is the round's headline. But the *first* attempt reused the existing `NFn`
   witness and would have failed for an irrelevant reason (`NFn` is already declared in the
   environment that witness lives in, so `checkName` rejects it) — and a failure there reads exactly
   like "residual B is vacuous". A satisfiability check must construct a **name-fresh** block, and no
   method rule says so. Add: *when firing an implementation that checks names, the witness's names
   must be absent from the environment you fire it in — check that first, or a rejection will be
   misread as vacuity.*
2. **Method rule 2 (instantiate numerals at extremes) did not find the falsity risk; reading the
   *quantifier over environments* did.** The dangerous instantiation was not a numeral at 0 or the
   boundary — it was `env` at a **mis-keyed** value, which is an extreme of a *non-numeric*
   universally quantified argument. Rule 2 should read: instantiate every universally quantified
   argument at its extremes, and for a structure with a `WF` side condition the extremes are the
   states `WF` **fails to forbid**. `InductMap.lean` §1 had already written down that `SMap.WF` does
   not forbid mis-keying; I had it in §1's Q4 as a "structural gift" and only later saw it was also a
   loaded gun.
3. **I priced the round before starting it and the price was right**, which is the fix
   `handoff-inductmap.md` §5 gap 1 asked for. P5's "≥400 lines, land a fraction, name what is left"
   was the plan, and the deviation is that the fraction landed was *chosen by sequencing* (items 2
   and 5, which are independent of item 4) rather than by which looked hardest.
4. **What I did not instrument: the two `TypeChecker.M.run` re-check passes.** I asserted by
   inspection that they write nothing to the constant map. That is the same class of claim
   ("verify rather than trust") this brief was written to catch, and I am recording it as unverified
   rather than quietly relying on it. M5.4.

### M6 (2026-09-05) — **correction to M3's table.** Five arities there were written from reading the
statement rather than from `scripts/exists.lean`, and four of the five were wrong. This is the
"a count without a date is a defect" rule applied to arity: an arity read off a statement is a guess,
because section `variable`s and `include` add binders that are not visible at the declaration. The
measured values, all at HEAD `9438e39` + this file on 2026-09-05:

| name | arity | cone | M3 said |
|---|---|---|---|
| `Lean4Lean.auxRecName_mem_indDeclNamesN` | 4 | 834 | arity 3 ✗ |
| `Lean4Lean.indBudget_auxRecName` | 2 | 836 | arity 2 ✓ |
| `Lean4Lean.SWF` | 6 | 12 | arity 5 ✗ |
| `Lean4Lean.SWF.addStep` | 4 | 3510 | — |
| `Lean4Lean.SWF.forM'` | 6 | 135 | — |
| `Lean4Lean.forIn_auxRecFold` | 3 | 743 | arity 2 ✗ |
| `Lean4Lean.mkAuxRecNameMap_panic` | 1 | 712 | — |
| `Lean4Lean.ctorInfo_name_eq` | 14 | 8751 | arity 12 ✗ |
| `Lean4Lean.rebuild_indWrite_budget` | 14 | 8777 | arity 15 ✗ |
| `Lean4Lean.rebuild_recWrite_budget_user` | 5 | 1002 | — |

The two large cones (8751, 8777) are the `WF_run`-consuming lemmas and sit just above `WF_run`'s own
8746, which is the expected shape: the reduction adds ~5 constants over the lemma it composes with.

Also re-polled at the end of the round, as the brief requires: bare `lake build` **green, 1670 jobs**;
`Lean4Lean/Verify/Inductive/InductMap.lean` has an **empty diff** (nothing removed from it, as M5.1
says); the working tree also contains `Lean4Lean/Verify/Inductive/ScanResidual.lean` and
`docs/handoff-scanresidual.md`, which are **another stream's** and are green in the same build —
not mine to report on beyond that.
