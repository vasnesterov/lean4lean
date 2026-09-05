# handoff-rebuildfinish — the block assembly: `InductiveMapGate`'s residual B, finished or honestly sized

Stream: RebuildFinish. Started 2026-09-05, HEAD `4a13ad3` (bare build green 1675 jobs, guards 1/2/3 ✓,
census 13).

Owned: `Lean4Lean/Verify/Inductive/RebuildFinish.lean` (new),
`Lean4Lean/Verify/Inductive/NestedRebuild.lean` and `Lean4Lean/Verify/Inductive/InductMap.lean`
(existing — may discharge `InductMap`'s residual), and `docs/handoff-rebuildfinish.md` (this file).
Everything else read-only. `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are
frozen and untouched.

Target, as handed over: residual B of `InductiveMapGate` is down to ~160 lines by the previous round's
itemisation — `forIn` loop rules + block assembly 130, `run_prefix` bridging 30 — plus
`handoff-nestedrebuild.md` M2's item 5 (a `StateT Environment (Except Exception)` analogue of
`InductMap.lean` §1's delta calculus), graded there as *"prose-only, and routine … ~120 lines"*.
The brief instructs me to **verify that grading rather than trust it**, and to apply the rule that has
caught three wrong cost sentences this week: *when a handoff says "with X, Y disappears", count Y's
uses in the consumer before building X.*

---

## §1 — Questions asked cold, before any reading of the target files

**Written before opening `RebuildFinish.lean` (does not exist), `NestedRebuild.lean`, `InductMap.lean`,
`NIndices.lean`, `Inductive/Add.lean`, or any `Theory/Inductive/*` in this session.** Read inputs so
far, declared: `CLAUDE.md`; the orchestrator's brief; and the *complete* text of
`docs/handoff-nindices.md` and `docs/handoff-nestedrebuild.md` (both read before writing this section —
so every claim of theirs quoted below is a *read input*, not a measurement of mine, and it is exactly
those claims that §2 is obliged to re-measure). Answers and measurements are appended to §2.
**Filled answers are never edited; corrections go in §2 as new numbered entries.**

Interpretation note on the brief's "predictions blank": predictions are only worth anything if made
cold, so the numbered predictions below are written **now**, in this same first write, before any
target file is opened; what is left blank until the end is the **scorecard's Outcome column**.

### The four shape questions, instantiated to "assemble the rebuild block and discharge residual B"

**Q1. Does the target exist — by *conclusion head*, not by obligation name?**
The thing to build is not "the block assembly". Its conclusion head is a delta statement about the
*whole* nested-rebuild `do`-block: something of the form
`SWF env (StateT.run (s := env) rebuild…) (indBudget types)` — i.e. after unfolding, a
`DeltaCore env env' (indBudget types)` (fields `wf` / `mono` / `keyed`) for the environment the block
returns. So, to enumerate before writing a line:
  (a) what is `SWF`'s actual signature (arity **6** per `handoff-nestedrebuild.md` M6, cone 12) and is
      its conclusion the same `DeltaCore` that `InductMap.lean` §1's calculus uses, or a *different*
      record that would need a bridge?
  (b) which combinators already exist — `SWF.bind'`, `SWF.checkName'`, `SWF.addStep`, `SWF.forM'` —
      and does one of them already cover the block's *actual* shape? `forM'` is `List.forM`; the
      rebuild is written `for indType in types do`, which elaborates to `forIn`, so the question is
      whether a `forIn`→`forM` bridge exists anywhere in the tree (`forIn_auxRecFold` is one, for a
      two-`mut` fold; `Lean4Lean/Verify` may have others for `StateT`).
  (c) is there a lemma anywhere whose conclusion head is already "delta of a `StateT.run`"? If yes,
      transporting it beats building (Method rule 3 — that move won twice this week).

**Q2. Is the work in the direction I think — is residual B true, does the assembly discharge it, and
what does `InductMap.lean` actually still ask for?**
Failure modes to rule out, in this order, *before* building:
  (a) **The consumer does not need what I would build.** The brief's own rule: count `GB`'s (residual
      B's) occurrences in `InductMap.lean` — how many times is it used, in how many lemmas, and is
      `inductiveMapGate_of`'s `GB` binder even *load-bearing* (`lean_minimal_hypotheses` answers this,
      and `Lean.SMap.WF.insert`'s `_hn` shows an unused binder is a real possibility in this repo)?
      If `GB`'s statement is not literally the delta of the block, the 160 lines land on the wrong side
      of a mismatch.
  (b) **Unprovable branches inside the block, not "loops".** The rebuild reads back constants with
      `let some (.inductInfo ind) := env'.find? indType.name | unreachable!`
      (`handoff-nestedrebuild.md` M2 quotes exactly this). `unreachable!` is `panic`, and
      `handoff-nindices.md` M1 established that `panic` bottoms out in body-less `@[extern] opaque
      panicCore`, so **on a panic branch of a `StateT` block the returned environment is a term about
      which nothing is provable** — the delta is then not merely unproved but *unprovable*, exactly as
      that round found for its four `assert!`s. Every `unreachable!` / `panic!` / `assert!` inside the
      rebuild must therefore be *excluded* by a positive lemma, not passed through. **How many are
      there?** The previous round's 160-line itemisation names loop rules and `run_prefix` and does not
      mention them; the analogous chain cost the `nindices` round its whole 150 lines.
  (c) **Vacuity of my own result.** Residual B's premises were exhibited satisfiable at `NTreeX`
      (M1 there), so the branch is live; but any *new* `M.WF`-shaped lemma of mine is vacuous if the
      block never succeeds. Method rule 4: a name-checking obligation needs a **name-fresh** witness,
      and the existing `#eval` guard at `NestedRebuild.lean` §5.2 uses `NTreeX` / `_nested.List_1`
      precisely for that reason. Does my assembly get exercised by that same witness, or do I need
      another one?
  (d) **Two unanalysed passes.** `handoff-nestedrebuild.md` M5.4 records, *as an unverified
      inspection*, that the two `TypeChecker.M.run` re-check passes at the end of the rebuild write
      nothing to the constant map. That is a claim of exactly the class this brief exists to catch. It
      must become a lemma or an explicitly-flagged limit.

**Q3. Measurement or docstring? — which handed-over claims are prose?**
Classify each as **(i)** a named lemma that compiles today / **(ii)** exists but statement mismatched /
**(iii)** prose with no referent:
  1. "`forIn` loop rules + block assembly, 130 lines";
  2. "`run_prefix` bridging, 30 lines" — does `Lean4Lean.ElimNestedInductive.run_prefix` have the
     statement the two `htt` hypotheses need, or a different one?
  3. item 5's *"routine … the same three fields with the state threaded"* — is `SWF` (already written,
     arity 6) actually **sufficient** for the block, or does it lack a rule per branch shape
     (`forIn`, `Except` short-circuit, `panic`, a nested `.run` of a different monad)? This is the
     grading the brief tells me to verify; "already discharged" (M3/P5 there) and "still owed"
     (the brief's framing) cannot both be right, and finding out which is a measurement, not a read.
  4. `Lean4Lean.runFreshGate` is *"a closed term of arity 0, cone 8855, hole-free"* — re-measure it
     myself with `scripts/exists.lean`; every `G`-parametrised result in `NestedRebuild.lean` being
     unconditional depends on it, and it is the single load-bearing read input of this round.
  5. `elimNoAuxGate` is **top-level, not under `AddInductive`** — and `mkAuxRecNameMap_spec` covers the
     `processRec`-over-auxiliary-recursor-names case.
Every name I report comes from `scripts/exists.lean` as it prints it, fully qualified, **with arity and
cone measured, never read off a statement** (Method rule 5; four of five so written were wrong two
rounds ago).

**Q4. What must the proof route around, and what are the limits of the result?**
Which opaque/partial things sit on this path: `panicCore` (`unreachable!`, Q2(b)), `Lean.Expr.eqv`
(`@[extern]`, so no `decide`), `PersistentHashMap.containsAux`/`findAux` (`partial`), `Name` `BEq`
inside `checkName`. Per `CLAUDE.md`'s 2026-09-04 corollary the preferred move for each is to **restate
the obligation around it**, not to replace it — and note that this round is *forbidden* to touch
`Inductive/Add.lean` anyway (not owned), which also means the four `assert!`s at `Add.lean`:253-257 that
`NIndices.lean` §1 now depends on must stay exactly as they are; if my assembly would be easier with
one deleted, that is a note in this doc, not an edit. Finally, Method rule 7: after whatever lands,
what does `InductiveMapGate` *still* need, and can I **prove** that my result does not suffice rather
than guess it?

### Numbered predictions, made cold — before opening any target file

- **P1 (panic branches are the hidden item).** Prediction: the rebuild block contains **at least two**
  `unreachable!`/`panic`-shaped eliminations (the `.inductInfo` read-back, and at least one more — a
  constructor read-back or a `headD`/`get!`), each of which must be excluded by a positive lemma before
  any delta is provable, and **none of them is in the previous round's 160-line itemisation**.
  Confidence: medium-high (the `nindices` round hit exactly this and the itemisation was written
  before that lesson landed). Falsifier: the block's read-backs are all `Option.getD`/`match` with a
  provable-total else-branch, or the panic value's *state* component is provably `env` (possible if
  `panic!` in `StateT` is `fun s => (default, s)`-shaped rather than `default` at the pair) — in which
  case the branches are free and P1 is refuted.
- **P2 (`GB`'s uses in the consumer).** Prediction: `GB` occurs in `InductMap.lean` in **1–2**
  lemmas, and is load-bearing in each (i.e. the "with X, Y disappears" promise is true here, unlike
  three times this week). Confidence: medium. Falsifier: ≥3 consumers, or a consumer whose `GB` binder
  `lean_minimal_hypotheses` reports unused.
- **P3 (item 5's "routine" grading).** Prediction: **half-holds**. `SWF`'s three fields are the right
  shape (so "routine" is right about the *calculus*), but the four existing combinators are
  **insufficient** for the block: I predict I must add **2–4** new rules — a `forIn`/`forIn'` rule, a
  rule for the panic branches of P1, and a rule for the `TypeChecker.M.run` passes — so the honest
  remaining cost is **above** 160 lines. Confidence: medium-high. Falsifier: `SWF.bind'` + `forM'`
  plus one `forIn` bridge closes the block.
- **P4 (what I land).** Prediction: I do **not** discharge `InductiveMapGate` outright this round;
  I land the `forIn` rule(s), the panic-branch exclusions, `run_prefix` bridging, and the assembly of
  the straight-line part, leaving **one** named residual (most likely the two `TypeChecker.M.run`
  passes of Q2(d), or a second `forIn` shape). Confidence: medium — deliberately pessimistic, since
  the previous two rounds each *over*-delivered against their own P4/P5 once the barrier was named.
  Falsifier in the good direction: `GB` is closed and `InductMap.lean`'s residual is removed.
- **P5 (`run_prefix`, the one cheap item).** Prediction: class **(i)** — exists, compiles, and the
  bridging really is ≤30 lines. Confidence: high. Falsifier: class (ii), statement about
  `res.types`/`types` in the wrong direction, needing an inversion.
- **P6 (`runFreshGate` re-measured).** Prediction: confirmed closed, arity 0, hole-free, cone within
  ±50 of 8855 (cones move with module contents). Confidence: high. Falsifier: nonzero arity — which
  would mean every "unconditional" result in `NestedRebuild.lean` is still parametrised and the round's
  premise is wrong.
- **P7 (a new side condition, by analogy).** Prediction: the assembly acquires **at least one** side
  condition invisible in the handoff's phrasing, by the same mechanism that forced `0 < its.size` on
  `WF_checkInductiveTypes_ni` — the extreme instantiation to look at first is `types = []` /
  `res.types = []` and the `headD default` in `auxRecName`. Confidence: medium.

### Scorecard (Outcome column filled at the end)

| # | Prediction | Outcome |
|---|---|---|
| P1 | ≥2 panic branches, unitemised, must be excluded | |
| P2 | `GB` used in 1–2 consumers, load-bearing | |
| P3 | item 5 "routine" half-holds; 2–4 new rules; >160 lines | |
| P4 | do not discharge outright; one named residual left | |
| P5 | `run_prefix` class (i), ≤30 lines | |
| P6 | `runFreshGate` arity 0, hole-free | |
| P7 | ≥1 new side condition, `types = []` the first extreme | |

---

## §2 — Measurements and corrections (append-only)

### M1 (2026-09-05) — the consumer counted first (**P2 confirmed**), and the block read (**P1 confirmed on count**)

Per the brief's rule, `GB`'s uses in the consumer **before** building anything. `grep -n GB
Lean4Lean/Verify/Inductive/InductMap.lean` gives **4 lines, 2 of them binders**:

* `:801` — the binder of `Lean4Lean.addInductive_mapDelta`; `:827` — its single use, on the
  `¬(∃ res, … aux2nested = [])` branch of a `by_cases`;
* `:836` — the binder of `Lean4Lean.inductiveMapGate_of`; `:849` — its single use, which is just
  `addInductive_mapDelta GB`.

So residual B has **exactly one real consumer** (`addInductive_mapDelta`), reached by the second
through a one-line relay. P2 confirmed at the low end: 1–2 lemmas, load-bearing in the only place it
matters, and *"with residual B, `InductiveMapGate` disappears"* is a **true** promise — the two lemmas
are literally `theorem … (GB : …) … := by … exact fun env' h => GB …`. This is the fourth time the rule
has been applied this week and the second time the promise survived it.

The exact obligation, copied from `:801-810` (this is the statement I must prove **without** the
binder):

```
∀ {env env' : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
  {iu ap : Bool} {fuel : FuelConfig},
  env.constants.WF → Environment.addInductive env lparams np types iu ap fuel = .ok env' →
  (∀ res, (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res → res.aux2nested ≠ []) →
  DeltaCore env env' (indBudget types)
```

Note the *shape*: it is a hypothesis about the **whole `addInductive` function**, not about the
`StateT.run` block — `InductMap.lean` §4.1 says why (the block "is a term with no name: it mentions
`res`, `recNameMap'` and `allIndNames`, all local"). So the assembly has to re-derive the whole
`addInductive` prefix (the `checkNoNestedAux` loops, `ElimNestedInductive.run`, `AddInductive.run`)
before it even reaches the block. That prefix is **not** in the 160-line itemisation either.

**The block, read (`Inductive/Add.lean`:1145-1211).** `(·.2) <$> StateT.run (s := env) do` over:
`processRec` (a local `def`-in-`do`, called from two places), `for indType in types do` (three `add`
sites: member, its ctors, `processRec (mkRecName indType.name)`), `recNames'.forM processRec`, then
**two** `TypeChecker.M.run` passes and a **third** `TypeChecker.M.run` inside a `for recName in
recNames` loop — i.e. `handoff-nestedrebuild.md` M5.4's "two re-check passes" is **three** call sites
(:1183, :1199, :1203), the last one inside a loop.

`unreachable!` count in `1145-1235`: **6** (P1's "at least two" confirmed on count), and they split
into two classes that cost differently — which is the measurement P1 got only half right about:

| site | monad | affects the delta? |
|---|---|---|
| `:1157` `env'.find? recName` in `processRec` | inside the `StateT` | **yes** |
| `:1170` `env'.find? indType.name` | inside the `StateT` | **yes** |
| `:1174` `env'.find? ctorName` | inside the `StateT` | **yes** |
| `:1201`, `:1203` (`final.find?` in the ctor re-check) | inside `TypeChecker.M.run`'s own monad | *pending* |
| `:1206` (`final.find? recName`) | inside the `StateT`, but before a `TypeChecker.M.run` that writes nothing | *pending* |

Whether the three-to-six panic branches cost anything at all turns on **one** question I had not
thought to ask cold: what `Inhabited` instance `panic!` uses at
`StateT Environment (Except Exception) α`. If `Inhabited (Except ε α)` is `.error default`, the panic
branch **rejects**, and every one of the six is free by vacuity (`Except.WF` says nothing about a
rejecting run). If it is `.ok default`, each must be excluded by a positive read-back lemma. Measured
next; this is exactly the "instantiate the continuation's argument, not the threaded state" instrument
the previous round added, applied to a `panic` instead of an `assert!`.

### M2 (2026-09-05) — **P1 refuted by its own named falsifier: all six panic branches are free**, and two files of this repo contradict each other about why

The question M1 ended on, answered by `rfl`:

```lean
example (env : Environment) :
    (unreachable! : StateT Environment (Except Exception) Unit) env = .ok (default, env) := rfl
```

**This compiles.** So on a panic branch of the rebuild the block returns `default` and **leaves the
state exactly as it found it** — the delta is preserved for free, and *not one* of the six
`unreachable!`s needs a positive read-back lemma. P1 is refuted, by the falsifier P1 itself named
("the panic value's *state* component is provably `env`"), which is the falsifier being worth writing
down.

Two independent reasons it works, both worth recording because each is a trap on its own:

1. `panicCore` is **not** a body-less `opaque`: `@[extern "lean_panic_fn"] def panicCore … := default`
   — an `@[extern]` *`def`*, so it unfolds in the logic even though the compiled behaviour aborts.
   (Guard 3 is unaffected: `panicCore` is core Lean, not `Lean4Lean.*`, so it is outside the guard's
   module filter and needs no whitelist entry.)
2. The `Inhabited` instance at a monadic type is **`instInhabitedOfMonad`**, i.e. `pure default`, not
   the function instance `fun _ => default`. The proof that it is: the `rfl` above needs **no**
   `Inhabited Kernel.Environment` — and indeed asking for one fails ("failed to synthesize instance …
   `Inhabited Kernel.Environment`"), which the function instance would have required. So the panic is
   `fun s => .ok (default, s)`: state-preserving *by construction of the instance*, not by luck.

**The contradiction, and which side is right.** `Verify/Inductive/NestedRunInvariant.lean`:303 proves
exactly this for `ElimNestedInductive.M` (`panic_eq : (panicWithPosWithDecl … : M α) env s = .ok (default, s)`)
and its §4 note says the "returns `.ok (default, default)`" folklore is "**wrong**" in the second
component. `Verify/Inductive/NIndices.lean`:61 says the opposite in prose — "`panicWithPosWithDecl` is
an opaque `panicCore`, so in a failing branch **nothing at all** can be [proved]" — and its M4 note
calls the empty-block statement "*unprovable* rather than false (the runtime panic value is `default`
…)". Measured, `NestedRunInvariant` is right and `NIndices`' prose is wrong: the panic value is
`default` **in the logic**, not merely at runtime.

Consequences, stated carefully because one of them touches a file I do not own:

* For **this** round: the three state-affecting `unreachable!`s (`Add.lean`:1157, :1170, :1174) and the
  three inside the re-check passes are all discharged by one rule (`SWF.panic'` below), not six
  lemmas. This is the single largest cost item M1 had identified, and it is worth ~0 lines.
* `NestedRebuild.lean`'s `mkAuxRecNameMap_panic` (which I own) is stated at `default` with the
  docstring "which is what the two panic branches return". That docstring was **unjustified** when
  written — `default` and `panicCore …` are different terms — and is now **justified**, by the same
  `rfl`. §3 below turns the docstring into the equation, so the lemma is actually connectable to its
  call site instead of merely looking connectable.
* `NIndices.lean` (not mine) is **not wrong as a theorem** — `WF_checkInductiveTypes_ni`'s `0 < its.size`
  is a hypothesis, and adding a hypothesis cannot make a true theorem false. What is wrong is its
  *claim of necessity*: M4 there says the empty-block case is "unprovable", and
  `params_assert_fails_at_empty` proves only that the fourth `assert!` *fails*, which by this
  measurement means the delivered stats is `default` with `nindices = #[]`, so at `its = #[]` the
  conclusion `#[].size = 0` is **true and provable**. `hpos` is therefore load-bearing *for that
  proof* (which is all `lean_minimal_hypotheses` ever claims) but **not necessary** for the statement.
  I own neither that file nor the right to restate it; recorded here, sized at ~15 lines to remove,
  and left alone.

### M3 (2026-09-05) — the assembly landed; the itemisation was ~65% of the truth and mis-composed

`Lean4Lean/Verify/Inductive/RebuildFinish.lean`, new, **381 lines: 247 code, 92 prose, 43 blank**,
no `sorry`, no warnings. The handed-over itemisation was "`forIn` loop rules + block assembly 130,
`run_prefix` bridging 30" (~160), with item 5 declared already done.

| item | priced | measured (code lines) | verdict |
|---|---|---|---|
| `forIn` loop rules | in the 130 | **25** — one rule (`SWF.forIn'`) covers all four `for`s *and*, after `rw [← Array.forIn_toList]`, the `Array` one; `SWF.mapM'` covers the `mapM` inside `processRec` | under-priced in count, right in kind |
| block assembly | in the 130 | **78** | about right |
| `run_prefix` bridging | 30 | **32** (`ElimNestedInductive.run_mem`) | **exact** — the one estimate in the whole itemisation that held |
| item 5, the `StateT` delta calculus | 120, "prose-only and routine" | **0 new** for the definition (it was already written), **+59** for combinators it lacked | see below |
| *unlisted*: the six `unreachable!`s | — | **13** (`panic_stateT_eq`, `SWF.panic'`, `SWF.panic_weak`, `panic_eq_default`) | M2 |
| *unlisted*: `mkAuxRecNameMap_spec'` | — | **22** | M4 |
| *unlisted*: gate wiring and consumers | — | **27** | M5 |

**The "routine" grading, adjudicated.** It holds for the *shape*: `SWF`'s three-field delta triple with
the state threaded is exactly right, and nothing in it needed changing. It fails for *sufficiency* —
and one of the four existing combinators is the interesting failure:

* `SWF.checkName'` is stated for `get >>= fun e => liftM (checkName e n ap)`. The `do`-elaborator emits
  `get >>= fun e => (liftM (checkName e n ap) >>= rest)`. Those differ by **associativity, which is not
  definitional in `Except`** (`Except.bind (Except.bind x f) g` needs a case split on `x`), so
  `checkName'` is class **(ii)** at every one of the block's four `checkName` sites: it exists, and it
  does not apply. `SWF.checkName_bind` (20 lines, and it must redo `checkName'`'s own proof rather than
  compose with it) is what the block needs. This is the round's second instance of the pattern the brief
  names: something that *looks* like it covers a step and does not.
* `SWF.forM'` applies at exactly **one** of the block's five loops (`recNames'.forM`); the other four are
  `forIn`.
* `SWF.addStep`/`bind'`/`lift'`/`get'`/`pure'`/`mono`/`weaken` all applied unchanged — 7 of 11.

So: 7 new rules (`panic'`, `panic_weak`, `forIn'`, `mapM'`, `liftTriv`, `checkName_bind`, `toDelta`),
against P3's predicted 2–4. **P3 confirmed in direction (>160 lines: 247) and refuted in count.**

**The two costs that were in no itemisation and are not lemmas at all** — both are the
`do`-elaborator's shape, i.e. `handoff-inductmap.md` §5 gap 3 arriving twice more:

1. `split` splits the **outermost** `match` it finds. The goal contains `mkAuxRecNameMap env2 types`,
   whose *own* body opens with `let mainType :: _ := types | unreachable!`, so the first `split` landed
   inside `mkAuxRecNameMap` and produced goals about `indBudget (recInfo :: hrf)` — nonsense that took a
   full read of the error to diagnose. Fix: `generalize hgen : mkAuxRecNameMap env2 types = M at hrange
   hdom ⊢` before any `split`, *then* `obtain ⟨rn, rm⟩ := M`.
2. `processRec` is a `have`-bound lambda, so zeta-expansion leaves `(fun recName => …) (mkRecName
   indType.name)` — a **beta-redex**, and `split` is syntactic, so it fails there. `simp only []` makes
   no progress; `beta_reduce` **does not exist** in this project (no Mathlib — it is a Mathlib tactic,
   and trying it cost a build cycle). `dsimp only` does it in one token.

### M4 (2026-09-05) — the panic-freeness paid a second dividend: a hypothesis pair deleted, not discharged

`mkAuxRecNameMap_spec` (`NestedRebuild.lean`, arity 6, cone 2573) carries `hmain : env'.find?
mainType.name = some (.inductInfo mainInfo)` and `hlen : mainInfo.all.length > types.length`. At the
call site `hmain` would demand that `AddInductive.run` **positively stored** an `.inductInfo` at the
first member's key — a *fourth* field of `RunFreshGate`, and (grep over `Verify/`) nothing in the tree
proves anything of that shape in general; the only `some (.recInfo …)` / `some (.inductInfo …)`
existence facts are witness-specific, at concrete environments.

With M2 both hypotheses are simply **not needed**: on either failure branch the function's value *is*
`default`, provably (`panic_eq_default`), and `mkAuxRecNameMap_panic` already gave both conclusions
there. `Lean4Lean.mkAuxRecNameMap_spec'` (arity **2** — `env'` and `types`, nothing else) is the
unconditional form. Note what this means for the previous round's docstring: it said `default` "is what
the two panic branches return", which was an assertion relating two *different terms*; it is now a
theorem, and `mkAuxRecNameMap_panic` is connectable to its call site for the first time.

### M5 (2026-09-05) — **`InductiveMapGate` is discharged**, and exactly where the wiring stops

`Lean4Lean.inductiveMapGate` : `InductiveMapGate`, **arity 0, cone 9444, hole-free, axioms
`[propext, Classical.choice, Quot.sound]`** — a closed term. Its proof is
`inductiveMapGate_of (fun mapWF h hne => addInductive_delta_nested mapWF hne _ h)`, i.e. `InductMap.lean`'s
own verbatim restatement of the gate, with the `GB` binder filled.

**What I removed from `InductMap.lean`: nothing, and it is not a choice.** `RebuildFinish.lean` *imports*
`InductMap.lean` (through `NIndices` → `NestedRebuild`), so `addInductive_mapDelta`'s and
`inductiveMapGate_of`'s `GB` binders cannot be deleted there — the proof of `GB` lives strictly above
them. Deleting them would require moving §4 of `InductMap.lean` into this file or below it; that is a
file-layout decision with no proof content, and I did not take it. The two `GB`-carrying theorems are
byte-identical to before; what changed is that a closed instance of `GB` now exists.

The same import fact applies at the *consumer* end, and here it is worth stating precisely, because it
is the one place where "discharged" needs a qualifier. `InductiveMapGate` is **defined and consumed** in
`Verify/Inductive/NoNestedAll.lean`, which does **not** import `InductMap.lean` (its chain is
`RestoreFaithful` → `ProjNoNested`/`NestedRestore`/`RunIdentity`/`NestedOccData`). Nothing imports
`NoNestedAll` from this side, so `RebuildFinish.lean` may import it — verified, no cycle, build green —
and the four `Gi`-taking theorems get unconditional corollaries here:

| `NoNestedAll.lean` (still takes `Gi`) | unconditional corollary in `RebuildFinish.lean` |
|---|---|
| `addInductive_noNestedEnv` | `Lean4Lean.addInductive_noNestedEnv'` (arity 10, cone 9487) |
| `addDecl_noNestedEnv` | `Lean4Lean.addDecl_noNestedEnv'` (arity 6, cone 10045) |
| `VEnv.NoNestedN.of_addDecl` | `Lean4Lean.VEnv.NoNestedN.of_addDecl'` (arity 9, cone 10433) |
| `addDecls_noNestedEnv` | `Lean4Lean.addDecls_noNestedEnv'` (arity 6, cone 10048) |

So the honest one-sentence answer to "is `VEnv.NoNestedN` unconditional on every branch": **yes — as a
theorem it is, `VEnv.NoNestedN.of_addDecl'` being closed and hole-free; but the *unprimed* names in
`NoNestedAll.lean` still carry their `Gi` binder**, and removing those binders is an edit to a file this
stream does not own. That edit is now purely mechanical (delete `Gi`, add the import) and it is not a
frozen file, so it needs no approval beyond its owner's.

### M6 (2026-09-05) — priced, on HEAD `4a13ad3` + this round's three files

Bare `lake build`: **green, 1677 jobs** (1675 before; +2 for the new module's `olean`/`ilean`).
Guards, from `lake env lean Lean4Lean/Verify/Guard.lean`:

* guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
* guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
* guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

`scripts/sorry-census-all.lean`: **HOLES 13**, unchanged; 494 built modules, **0 in population but not
built**. `RebuildFinish` appears in the census's *module list* (it is in the population) and contributes
**no hole**. No warnings from any owned file (`lean_diagnostic_messages` at severity `warning`: empty).

Names as `scripts/exists.lean` prints them, arity and cone **measured, never read off a statement**.
All are hole-free with `cone reaches sorryAx: false`:

| name | arity | cone |
|---|---|---|
| `Lean4Lean.panic_stateT_eq` | 8 | 422 |
| `Lean4Lean.panic_eq_default` | 7 | 376 |
| `Lean4Lean.SWF.panic'` | 10 | 435 |
| `Lean4Lean.SWF.panic_weak` | 12 | 439 |
| `Lean4Lean.SWF.forIn'` | 9 | 196 |
| `Lean4Lean.SWF.mapM'` | 8 | 258 |
| `Lean4Lean.SWF.liftTriv` | 5 | 116 |
| `Lean4Lean.SWF.toDelta` | 9 | 2406 |
| `Lean4Lean.SWF.checkName_bind` | 9 | 6176 |
| `Lean4Lean.ElimNestedInductive.run_mem` | 10 | 5797 |
| `Lean4Lean.mkAuxRecNameMap_spec'` | 2 | 2591 |
| `Lean4Lean.addInductive_delta_nested` | 9 | 9404 |
| `Lean4Lean.inductiveMapGate` | 0 | 9444 |
| `Lean4Lean.addInductive_noNestedEnv'` | 10 | 9487 |
| `Lean4Lean.addDecl_noNestedEnv'` | 6 | 10045 |
| `Lean4Lean.addDecls_noNestedEnv'` | 6 | 10048 |
| `Lean4Lean.VEnv.NoNestedN.of_addDecl'` | 9 | 10433 |

Re-measured, as P6 required, rather than relayed: `Lean4Lean.runFreshGate` — **arity 0, cone 8855,
hole-free**, exactly as the previous round reported. **P6 confirmed**; the round's load-bearing read
input was sound.

`lean_minimal_hypotheses` on `addInductive_delta_nested`: **both** explicit binders (`mapWF`, `hne`)
load-bearing. `hne` is load-bearing for *this* proof, not necessary for the truth of an unconditional
delta — `InductMap.lean` §4 covers the `numNested = 0` branch and `inductiveMapGate_of` joins them, which
is why the gate closes.

The four axioms beyond the standard three that the primed consumers report — `Expr.abstractRange_eq`,
`Expr.abstract_eq`, `Expr.hasLooseBVar_eq`, `Expr.lowerLooseBVars_eq` — come from `NoNestedAll`'s own
chain, are on `Guard.lean`'s frozen-24 list, and are inherited by the unprimed theorems too: this round
adds **no** axiom. `inductiveMapGate` itself reaches none of them.

### M7 (2026-09-05) — limits of this result, and the ones I can prove

1. **`kernel_sound` is not affected.** Guard 2 still prints "proof INCOMPLETE: sorryAx present" and the
   census is still 13. `InductiveMapGate` was one residual of `VEnv.NoNestedN`; the 13 holes elsewhere
   are untouched, and nothing here claims otherwise.
2. **The unprimed `NoNestedAll` names still carry `Gi`** (M5). Sized: delete four binders, add one
   import, adjust four proof bodies that pass `Gi` along — under 15 lines, in a file I do not own.
3. **`InductMap.lean` and `NestedRebuild.lean` are unchanged except for prose pointers.** The `GB`
   binders stay for the import reason in M5; `mkAuxRecNameMap_spec` keeps its two hypotheses (the
   unconditional `spec'` is a separate lemma above it, not a replacement, because `spec'`'s proof needs
   `panic_eq_default`, which lives above `NestedRebuild.lean`).
4. **What the panic result does *not* say.** `panic_eq_default` is about the *logical* value. The
   compiled `@[extern "lean_panic_fn"]` behaviour differs (it prints and, in the C kernel, aborts), so
   this is a statement about the proof obligation, not a claim that the two kernels agree at a panic.
   Nothing in `divergences.md` needs a new entry: the panic branches are unreachable in the accepting
   runs the gate quantifies over — but note that I did **not** prove them unreachable, I proved they do
   not matter, which is strictly weaker and strictly cheaper.
5. **Non-vacuity.** `addInductive_delta_nested` is `Except.WF`-shaped, so a rejecting input satisfies it
   for free. The accepting case at a *name-fresh* nested block is exhibited by
   `NestedRebuild.lean` §1's `#eval` (`NTreeX`, `_nested.List_1`; `addInductive` returns `.ok` and adds
   exactly `NTreeX`, `NTreeX.node`, `NTreeX.rec`, `NTreeX.rec_1`), which still runs in this build. That
   witness has `numNested = 1`, one member, no parameters: it prices the branch, it does not survey it.
   **`numNested ≥ 2` and mutual nested blocks are still un-exercised by any witness**, and my proof is
   uniform in both (nothing in it splits on `numNested` beyond `≠ 0`), so I claim generality from the
   proof, not from the witness.
6. **The `assert!` coupling recorded by the previous round is untouched and unweakened.** I did not edit
   `Inductive/Add.lean`, and nothing here depends on the four `assert!`s at :253-257 except through
   `NIndices.lean`'s `WF_checkInductiveTypes_ni`, which is unchanged.

### §2.1 Method gaps of *this* round

1. **The cheapest instrument was one `rfl`, and it decided the round.** M2 took a single `example … := rfl`
   and turned the largest cost item (six panic branches, feared to need a fourth gate field) into ~13
   lines. The generalisation to add: **before assuming a `panic`/`unreachable!` blocks a proof, evaluate
   it** — `panicCore` is an `@[extern] def` with body `default`, and at a monadic type the `Inhabited`
   instance is `pure default`, so a panic in a state monad is *state-preserving and value-known*. Two
   files in this repo asserted the opposite in prose (`NIndices.lean`:61) and one had already measured
   the truth (`NestedRunInvariant.lean`:303) — **the measurement was one file away from the assertion
   and neither cited the other**. That is a search failure, not a proof failure: the instrument to add is
   *grep the tree for the fact before writing prose that contradicts it*.
2. **My own §1 named P1's falsifier and I still predicted P1.** The falsifier ("the panic value's state
   component is provably `env`") was written down cold, and it was the truth. Writing falsifiers is
   working; *weighing* them is not. A falsifier that costs one `rfl` to test should be tested **before**
   the prediction is recorded as medium-high confidence.
3. **Two of the three real obstacles were tactic-level, not mathematical** (M3: `split` on the wrong
   `match`, the beta-redex). No method rule covers "the `do`-elaborator's shape defeats a syntactic
   tactic", though `handoff-inductmap.md` §5 gap 3 recorded one instance and this round hit two more.
   Proposed rule: **when reasoning about an elaborated `do`-block, `generalize` every applied helper and
   every `Id.run`-shaped call before the first `split`, and reach for `dsimp only` the moment a `split`
   reports "could not split".**
4. **I priced the round at "do not discharge" and over-delivered** — the same shape as the previous two
   rounds, which also beat their own P4/P5 once the barrier was named. Three rounds in a row is a
   pattern: *once a residual has a name and a closed sub-gate, the remaining cost is systematically
   over-estimated.* The counter-rule is not "be optimistic"; it is that **the estimate should be made
   after the cheapest instrument has been fired, not before**, which is exactly gap 2 restated.
5. **Not instrumented: the three `TypeChecker.M.run` passes' *contents*.** `SWF.liftTriv` proves they
   cannot change the constant map (they are `liftM`s of `Except`, state untouched) — which upgrades
   `handoff-nestedrebuild.md` M5.4 from an inspection to a theorem, and is the answer to §1's Q2(d).
   What I did *not* look at is whether they *reject* when they should; that is a completeness question
   about the checker, not a soundness one about the map, and it is out of this round's scope.

### Scorecard (filled 2026-09-05)

| # | Prediction | Outcome |
|---|---|---|
| P1 | ≥2 panic branches, unitemised, must be excluded | **half-confirmed, half-refuted — and the refuted half is the round's headline.** Six of them (more than predicted), unitemised (as predicted), and **not one needs excluding** (M2): `panicCore` is an `@[extern] def` with body `default` and the monadic `Inhabited` is `pure default`, so a panic preserves the state. Refuted by P1's own named falsifier |
| P2 | `GB` used in 1–2 consumers, load-bearing | **confirmed at the low end** (M1): one real consumer (`addInductive_mapDelta`), one one-line relay (`inductiveMapGate_of`). The "with X, Y disappears" promise was **true** — the fourth application of the brief's counting rule this week and the second survival |
| P3 | item 5 "routine" half-holds; 2–4 new rules; >160 lines | **confirmed in direction, refuted in count.** The calculus's *shape* was right and needed no change; its *combinator set* was insufficient — **7** new rules, not 2–4, and `SWF.checkName'` was class (ii) at all four of its call sites (associativity is not definitional in `Except`). 247 code lines against ~160 priced |
| P4 | do not discharge outright; one named residual left | **REFUTED, in the good direction.** `Lean4Lean.inductiveMapGate` is a closed term, arity 0, cone 9444, hole-free, standard axioms only. No residual remains in the gate; what remains is a four-binder edit in a file I do not own (M5) |
| P5 | `run_prefix` class (i), ≤30 lines | **confirmed** — class (i), and 32 code lines (`ElimNestedInductive.run_mem`), needing `runSkelExtends` alongside it for the length. The only estimate in the itemisation that was exactly right |
| P6 | `runFreshGate` arity 0, hole-free | **confirmed, re-measured not relayed**: arity 0, cone 8855, hole-free — identical to the previous round's figure |
| P7 | ≥1 new side condition, `types = []` the first extreme | **REFUTED.** `addInductive_delta_nested`'s hypotheses are exactly `GB`'s two, and both are load-bearing; no `0 < types.length` appears. The reason is worth keeping: every clause the assembly consumes is `∀ t ∈ types, …`, so the empty block is vacuous rather than special — and M2 removes the one place (`mkAuxRecNameMap`'s `types = []` panic) where it would have bitten |

### M8 (2026-09-05) — correction to M6's HEAD, and the final poll

M6 says "HEAD `4a13ad3`". That was the HEAD this round started on; **another stream committed during it**
and HEAD is now `5ed287d` ("the probe is open — but the context coordinate is provably content-free").
Every number in M6 was measured *after* that commit was already in the tree, so the figures stand; only
the label was stale. The working tree at the end of the round contains exactly four paths, all mine:

```
 M Lean4Lean/Verify/Inductive/InductMap.lean       (prose pointer only — the `GB` binders are unchanged)
 M Lean4Lean/Verify/Inductive/NestedRebuild.lean   (prose only: one correction, one update note)
?? Lean4Lean/Verify/Inductive/RebuildFinish.lean   (new, 381 lines)
?? docs/handoff-rebuildfinish.md                   (this file)
```

Final poll, all after the prose edits: bare `lake build` **green, 1677 jobs**; guards **1 ✓ / 2 ✓
(proof INCOMPLETE: sorryAx present) / 3 ✓ (2/2)**; census **13 holes, 494 built, 0 in population but not
built**; **no warnings from any of the three owned Lean files**. One trap worth recording for the next
stream: mid-round, `scripts/exists.lean` reported `addInductive_delta_nested` as *"own value is a hole:
true; cone reaches sorryAx: true"* — because it reads the **`olean`**, and the last `lake build` had
captured an intermediate `sorry` state of the file. `lake env lean <file>` type-checks the source but
writes no `olean`, so **`exists.lean` must be run after a `lake build`, never after a bare
`lake env lean`**, or it will report the previous state of your own file with no indication that it has.
