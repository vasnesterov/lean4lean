# handoff-nindices — `stats.nindices.size = its.size`, the last thing between residual B and falsity

Stream: NIndices. Started 2026-09-05, HEAD `9165203` (bare build green 1670 jobs, guards 1/2/3 ✓, census 13).

Owned: `Lean4Lean/Verify/Inductive/NIndices.lean` (new), `Lean4Lean/Verify/Inductive/NestedRebuild.lean`
(existing), `docs/handoff-nindices.md` (this file). Everything else read-only.
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are frozen and untouched.

Target, as handed over by the NestedRebuild round: prove `stats.nindices.size = its.size`, said to be
~130 lines, and with it the `Lean4Lean.RunFreshGate` fields that follow (~90 lines). The claim that
makes it first rather than last: the gate quantifies over *every* `env` with `constants.WF`, and
`SMap.WF` does not forbid a mis-keyed entry (`Lean4Lean/Std/SMap.lean`:34-38, freshness binder `_hn`
unused), so a mis-keyed `.inductInfo` survives into `env'`, passes `checkName ind.name`, and is `add`ed
at `ind.name`, violating `DeltaCore.keyed`. The only rejector is `checkName info.name` inside
`declareInductiveTypes` (`Inductive/Add.lean`:298), which fires at index `j` only if the `zipWith` at
:289 reaches `j`. Hence the size equality.

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `NIndices.lean` (does not exist yet), `NestedRebuild.lean`,
`Inductive/Add.lean`, `docs/handoff-nestedrebuild.md` §2 onwards, or any `Theory/Inductive/*` in this
session.** Inputs so far: `CLAUDE.md`, the orchestrator's brief, and lines 1-140 of
`docs/handoff-nestedrebuild.md` read *solely* for this file's §1 format (its M1 measurement about
`NTreeX` satisfiability was visible in that slice and is therefore declared here as a read input, not
as my own measurement). Answers appended below; **filled answers are never edited, corrections go in §2.**

### The four shape questions, instantiated to `stats.nindices.size = its.size`

**Q1. Does the target exist — by *conclusion head*, not by obligation name?**
The conclusion head is an `Array.size` (or `List.length`) equality between a field of whatever record
`stats` inhabits and the input list of `InductiveType`s. So: *what is the actual type of `stats`, what
is the actual type of `nindices`, and which function produces it?* Candidates to enumerate before
writing anything: a `Nat`-indexed `Array Nat` built by an `Array.push` loop over `its`, or a `List Nat`
built by `mapM`. If it is a `mapM`/`map` over `its`, `List.length_map`/`Array.size_map` closes it in
one line and the "~130 lines" estimate is prose. If it is a `foldl` with an early `throw`, the size
equality is only true on the `.ok` branch and the statement needs that hypothesis. Also: does a lemma
with this conclusion head already exist anywhere (`nindices`, `size_nindices`, `nindices_length`)?

**Q2. Is the work in the direction I think — is the statement even true, and does it do the job?**
Two independent failure modes, to be ruled out in this order:
(a) **False as stated.** `nindices` could be shorter than `its` by construction (e.g. only nested/aux
    types get an entry, or the producing loop `filter`s). Extremes to instantiate per Method rule 2,
    generalised form: `its = []`; `its` a singleton; and — the form that found the barrier in the first
    place — a `stats` whose `WF` side condition does *not* forbid the mismatch, i.e. is `stats` ever
    supplied by a hypothesis/opaque rather than computed? If `stats` is universally quantified with
    only a `WF` that is silent on `nindices`, the equality is *unprovable*, not merely unproved, and
    the fix is a strengthened `WF` or a different statement.
(b) **True but useless.** The brief's chain is: size equality ⇒ `zipWith` at `Add.lean`:289 reaches
    every `j` ⇒ `checkName info.name` fires at every `j` ⇒ mis-keyed entry rejected. Per Method rule 3
    I must **count the uses in the consumer before building it**: does `zipWith`'s length actually
    depend on `nindices.size`, or on some third list? `zipWith` truncates to the *shorter* of two
    arguments, so the equality must be between the two things zipped — if `nindices` is not one of the
    zipped arguments, proving its size buys nothing.

**Q3. Measurement or docstring? — which of the handed-over claims are prose?**
Classify each of these, (i) named lemma that compiles today / (ii) exists but statement mismatched /
(iii) prose with no referent: the "~130 lines"; the "~90 lines of `RunFreshGate` fields that follow";
"items 2, 5 and item 3's constructor half are independent and already partly done"; the three field
names of `RunFreshGate`; and the assertion that `Add.lean`:254 is the implementation's own `assert!`
for exactly this. Every name reported must come from `scripts/exists.lean`, fully qualified as it
prints it, with **arity and cone** — never read off a statement (Method rule 5: section
`variable`/`include` binders are invisible in the source text).

**Q4. What does the proof have to route around, and what are its limits?**
Which opaque/partial comparison sits on this path — `Name` `BEq`/`DecidableEq` inside `checkName`,
`Lean.Expr.eqv` (`@[extern]`), `PersistentHashMap.findAux`/`containsAux` (`partial`)? Per `CLAUDE.md`'s
2026-09-04 corollary the preferred move is to restate around them, not replace them. And per Method
rule 8: **after proving the size equality, what does residual B still need, and can I prove that my
result does not suffice?** A name-checking obligation needs a name-fresh witness (Method rule 4): any
satisfiability check I run must use names absent from the ambient environment, or the rejection reads
as vacuity.

### Numbered predictions, made cold — written before any reading of the target files

- **P1 (what `nindices` is).** Prediction: `nindices` is an `Array Nat` (one entry per declared type,
  the number of indices of that type) built by a loop over `its`, and the size equality is a `foldl`/
  `push` invariant, not a `map`. Confidence: medium. Falsifier: it is a `map`/`mapM` over `its`
  (then ~1-5 lines, and "130" was prose), or it is not per-type at all.
- **P2 (truth).** Prediction: **true on the `.ok` branch and only there** — I expect the honest
  statement to carry an `.ok`/success hypothesis or to be phrased about the value returned by the
  producing function rather than about a universally quantified `stats`. Confidence: medium-high.
  Falsifier for the bad case: `stats` is a bare universally quantified argument whose `WF` never
  mentions `nindices`, in which case the target as literally written is **unprovable** and §2 will say so.
- **P3 (usefulness / Method rule 3 count).** Prediction: `nindices` **is** one of the two arguments of
  the `zipWith` at `Add.lean`:289 (otherwise the previous round's mechanism does not close), and the
  number of places the consumer needs the equality is **1-2**, not the many that would justify 130
  lines. Confidence: low-medium — this is exactly the shape of promise that misled three rounds.
- **P4 (cost).** Prediction: the size equality itself lands in **under 60 lines** if P1's loop shape
  holds, and I land it plus at most **one** `RunFreshGate` field this round. Confidence: medium.
- **P5 (`RunFreshGate` fields).** Prediction: of the three fields, the size equality unlocks **one**
  outright; the other two need the per-`j` `checkName` firing, which is a separate loop invariant.
  Confidence: medium-low.
- **P6 (residual B's fate).** Prediction: residual B still stands a chance of being true — i.e. the
  size equality is provable and does block the mis-keyed counterexample. Confidence: medium.
  Falsifier: P2's bad case, or a *second* independent route by which a mis-keyed entry reaches `add`
  (e.g. a write that bypasses `declareInductiveTypes` entirely).

### Scorecard (filled at the end)

| # | Prediction | Outcome |
|---|---|---|
| P1 | `nindices` an `Array Nat` from a push/fold loop, not a `map` | **confirmed** (M1) — `Array Nat`, `push` at `Add.lean`:248, invariant `size = dIdx` |
| P2 | true only on the `.ok` branch; unprovable if `stats` is a bare `∀` | **half right, and wrong about the reason** (M1, M2).  `stats` is not a bare `∀` — it is the value `checkInductiveTypes` computes, so the `.ok` framing is automatic in `M.WF`.  But the statement *is* conditional, on something I did not predict: `0 < its.size`, forced by the **fourth** `assert!`, not by the `.ok` branch |
| P3 | `nindices` is one of the zipped args; 1-2 consumer uses | **confirmed** — `Array.zipWith indTypes stats.nindices` (`Add.lean`:289) truncates to the shorter, and the consumer needs it in exactly **1** place (the `stats.nindices[j]? = some ni` guard of `AddInductive.M.WF.declareInductiveTypes`, `DeclareStages.lean`:173, reached through `r113e_indInfos_getElem?`:142).  The previous round's "with X, Y disappears" claim survives Method rule 3's count |
| P4 | equality under 60 lines; land it + ≤1 gate field | **refuted both ways**: §1 is ~150 lines, not <60 (the four `assert!`s, M1), and **all three** gate fields landed, not ≤1 |
| P5 | unlocks 1 of 3 `RunFreshGate` fields | **refuted, in the good direction: 3 of 3** (M3).  `Lean4Lean.runFreshGate` (arity 0, cone 8855, hole-free) |
| P6 | residual B still possibly true | **confirmed, and strengthened**: the mis-keyed-environment route to falsity is now *closed*, not merely unexercised — `WF_run_member` says an `env` holding anything at a member key makes `run` **reject**, so §1.1's counterexample env cannot satisfy residual B's hypotheses |

---

## §2 — Measurements and corrections (append-only)

### M1 (2026-09-05) — **P1 confirmed, and the target's cost is not where the handoff put it.**

`stats : Lean4Lean.AddInductive.InductiveStats` (`Inductive/Add.lean`:127-135), `nindices : Array Nat`
with default `#[]`.  It is produced by `checkInductiveTypes.loopInd` (`:203-257`), which pushes
**exactly one** entry per member (`:248`, `nindices := stats.nindices.push nindices`) alongside
`indConsts` (`:249`).  So P1 is right that it is a push loop, not a `map`, and the invariant is
`nindices.size = dIdx` — which on its own would be ~25 lines on top of `InductMap.lean`'s existing
frames.

**But that is not the obligation.**  Measured (first attempt's two `omega` failures, verbatim in the
goal): the continuation `k` is applied not to the threaded `stats` but to the **four-fold `assert!`
chain** at `:253-257`:

```
k <| assert! stats.levels.length == lparams.length     -- (1)
     assert! stats.nindices.size  == indTypes.size     -- (2)
     assert! stats.indConsts.size == indTypes.size     -- (3)
     assert! stats.params.size    == nparams           -- (4)
     stats
```

`assert! c; e` elaborates to `if c then e else panicWithPosWithDecl …`, and `panic` bottoms out in
`panicCore`, an `@[extern] opaque`.  So in **any** failing branch the delivered stats is a term about
which nothing whatever is provable, and the postcondition `stats.nindices.size = indTypes.size` is
**not derivable from a `nindices`-only invariant**: all four conditions must be discharged first.
That is the whole reason `WF_checkInductiveTypes_loop_inv` needs a five-field `LoopInv` rather than
one equation.  Condition (4) is a genuine invariant of the *inner* telescope loop
(`params` is pushed only while `indConsts` is empty, and read as `params[i]!` for every later member),
and condition (1) forced a new frame: `InductMap.lean` §2's frames export only `c'.env = c.env`,
while (1) compares against the **reader's** `lparams`, so `c'.lparams = c.lparams` had to be threaded
through both loops (`withLocalDecl_frame'`, `WF_read_bind`).

Per `CLAUDE.md`'s 2026-09-04 corollary this is exactly the "restate around the opaque" case, and no
restatement was needed in the end — the four conditions are all true, and provable.

### M2 (2026-09-05) — **a genuine side condition the handoff did not mention: the empty block.**

Instantiating the argument `its` at its extreme (`its = #[]`, Method rule 2) **refutes** the
unconditional reading of the target.  For `its.size = 0` the member loop exits immediately at
`dIdx = 0` with `stats.params.size = 0`, so assert (4) `params.size == nparams` **fails** whenever
`nparams ≠ 0`, and the stats handed to `k` is then the panic value, whose `nindices` is unknown.
So `stats.nindices.size = its.size` is *not* provable for `its = #[]` at `nparams ≠ 0`; `0 < its.size`
is a real hypothesis of `WF_checkInductiveTypes_ni`, not a convenience.  It costs the consumer
nothing: `RunFreshGate.member`'s conclusion is `∀ t ∈ its, …`, vacuous at `its = []`.

**§1 as landed compiles** (`Lean4Lean/Verify/Inductive/NIndices.lean`, no errors, no `sorry`):
`AddInductive.WF_read_bind`, `AddInductive.withLocalDecl_frame'`, `AddInductive.LoopInv`,
`AddInductive.LoopInv.params_eq`, `AddInductive.WF_checkInductiveTypes_loop_inv`,
`AddInductive.WF_checkInductiveTypes_loopInd_inv`, `AddInductive.WF_checkInductiveTypes_ni`.

### M3 (2026-09-05) — **all three `RunFreshGate` fields proved; the barrier is gone, not reduced.**

P5 predicted one field of three.  Measured: **three of three**, and the reason the other two came
cheap is worth recording because it corrects the previous round's grading in one place.

| field | needs §1's size equality? | what it actually needed | landed as |
|---|---|---|---|
| `member` | **yes** — `M.WF.declareInductiveTypes`' clause is guarded by `stats.nindices[j]? = some ni` | nothing else | `AddInductive.WF_run_member` |
| `ctor` | **no** — `M.WF.declareConstructors`' clause is guarded by `indTypes[j]?` alone, exactly as `NestedRebuild.lean` §5 graded it | a *descent*: `declareConstructors` reports freshness in the post-`declareInductiveTypes` `e₁`, not in `c.env`, and `AddInductive.M.WF.declareInductiveTypes` **discards** the `hother` clause of `r113e_addLoop_WF` that would supply it — re-derived here as `WF_declareInductiveTypes_mono` | `AddInductive.WF_run_ctor` |
| `ctors` | **yes** — same `zipWith` | value preservation across *everything* `run` does after `declareInductiveTypes`: `declareConstructors` (`WF_declareConstructors_pres`) and the recursor `forIn'` loop (`CtorsPinned` as the loop invariant).  The argument that makes it cheap: each stage `checkName`s before it `add`s, so an added name is **fresh** in the environment it is added to, whereas a member name is already `some` there — hence the two names differ and `r113e_find?_add_ne` applies.  No name-distinctness assumption about the block is needed anywhere | `AddInductive.WF_run_ctors` |

So `NestedRebuild.lean` §5's grading of `ctor` ("needs nothing of the kind") is **confirmed**, and its
implicit grading of `ctors` ("same zip guard as `member`") is confirmed *and* incomplete: the zip guard
is necessary but the preservation walk is the bulk of it.

### M4 (2026-09-05) — what landed, priced, on HEAD `9165203`

Bare `lake build`: **green, 1672 jobs** (1670 before; +2 for the new module).  Guards, from
`lake env lean Lean4Lean/Verify/Guard.lean` and from the build itself:

* guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
* guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
* guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

Sorry census (`scripts/sorry-census-all.lean`): **13**, unchanged; 489 built modules, 0 in population
but not built.  No warnings from either owned file.  Frozen files untouched (`git status` shows only
`NestedRebuild.lean` modified and `NIndices.lean` / this doc new).

Every axiom set below is `[propext, Classical.choice, Quot.sound]` — the three on Guard.lean:144's
whitelist ahead of the frozen 24, so nothing here touches the frozen list.  Names and arities from
`scripts/exists.lean` (which resolves and prints them fully qualified), never read off a statement:

| name | arity | cone | hole |
|---|---|---|---|
| `Lean4Lean.AddInductive.LoopInv` | 6 | 5 (type-constants only — a `Prop`, unpriced by itself) | no |
| `Lean4Lean.AddInductive.WF_checkInductiveTypes_loop_inv` | 18 | 7299 | no |
| `Lean4Lean.AddInductive.WF_checkInductiveTypes_loopInd_inv` | 21 | 7402 | no |
| `Lean4Lean.AddInductive.WF_checkInductiveTypes_ni` | 8 | 7413 | no |
| `Lean4Lean.AddInductive.WF_run_member` | 5 | 8670 | no |
| `Lean4Lean.AddInductive.WF_declareInductiveTypes_mono` | 7 | 6394 | no |
| `Lean4Lean.AddInductive.WF_run_ctor` | 5 | 8509 | no |
| `Lean4Lean.AddInductive.CtorsPinned` | 2 | 2353 | no |
| `Lean4Lean.AddInductive.WF_declareConstructors_pres` | 5 | 6331 | no |
| `Lean4Lean.AddInductive.WF_run_ctors` | 5 | 8839 | no |
| `Lean4Lean.runFreshGate` | 0 | 8855 | no |

`lean_minimal_hypotheses` on `WF_checkInductiveTypes_ni`: both explicit binders (`hpos`, `H`)
**load-bearing**.  `hpos`' necessity is also proved, not just asserted, by
`AddInductive.params_assert_fails_at_empty`: at `its = #[]` the fourth `assert!`'s condition is `false`
for every `nparams ≠ 0`, so what reaches the continuation is `panicCore` — an `opaque` with **no body**,
about whose `nindices` nothing is derivable.  At an empty block the target statement is therefore
*unprovable rather than false* (the runtime panic value is `default`, whose `nindices` is `#[]`, so it
is probably true — just not a theorem).

### M5 (2026-09-05) — limits of this result, and what residual B still needs

1. **The gate is discharged; residual B is not.**  `NestedRebuild.lean` §5's own description of
   `RunFreshGate` is "everything residual B needs from `AddInductive.run` beyond `WF_run`", so what
   remains is the part that was never in the gate: §3's `StateT Environment` delta calculus applied to
   the actual rebuild `do`-block, plus `run_prefix` to move from `res.types` to `types`.  I did not
   touch that, and I make no claim about its size.
2. **`0 < its.size` is a real side condition** (M2, M4), invisible in the handoff's phrasing of the
   target.  It costs nothing at the three gate fields (all are `∀ t ∈ its, …`), but any *other*
   consumer of `WF_checkInductiveTypes_ni` inherits it.
3. **The four `assert!`s are now load-bearing for the proof**, which couples this development to an
   implementation detail: if any `assert!` at `Inductive/Add.lean`:253-257 were deleted (they are
   redundant at runtime), `WF_checkInductiveTypes_ni` would get *easier*, but if one were **changed**,
   §1 breaks.  A comment at those lines would be worth adding by whoever owns `Inductive/Add.lean`;
   this stream does not own it and did not edit it.
4. **What I did not check.**  Whether `stats.nindices[j]` equals the *abstract* index count
   (`T.indices.length`) — that is `Decl.lean`:1134's row, a different obligation from the size
   equality, and nothing here bears on it.  Nor did I re-verify `AddInductive.WF_run` itself; my
   theorems are independent of it and share only the frames.
5. **Method gap.** The extreme-instantiation instrument found the empty-block case (`its = #[]`) but
   **not** the `assert!` obstacle — that appeared only when `omega` printed the panic chain in its
   counterexample.  Generalising Method rule 2 further: for a CPS function, instantiate the
   *continuation's argument* too, not just the caller's arguments; the delivered value need not be the
   threaded one.

### M6 (2026-09-05) — the vacuity check my own three theorems need, and where it already is

All three are `M.WF`-shaped (`∀ a, run np its nn c = .ok a → …`), so they would be **vacuously true**
if `AddInductive.run` never accepted.  Method rule 4's point applies to my results and not only to the
gate: a name-checking obligation needs a *name-fresh* witness.  That witness already exists and still
fires — `NestedRebuild.lean` §5.2's build-time `#eval` runs `AddInductive.run` on the expanded `NTreeX`
block, whose names (`NTreeX`, `_nested.List_1`) are absent from the ambient environment, and reports:

```
all three RunFreshGate fields hold at the 2 members of the expanded NTreeX block
([NTreeX, _nested.List_1]), at a run AddInductive.run accepts ✓
```

So the accepting case is exhibited at a fresh block, and the three theorems are non-vacuous there.
A source scan of `NIndices.lean` finds no `sorry`, `axiom`, `native_decide`, `partial`, or
`@[implemented_by]`; `lean_verify` on `WF_run_member` reports axioms
`[propext, Classical.choice, Quot.sound]` only.
