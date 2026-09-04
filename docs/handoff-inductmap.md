# handoff-inductmap — closing `InductiveMapGate`, the last residual in `NoNestedN`

Round scope: prove `Lean4Lean.InductiveMapGate` (`Verify/Inductive/NoNestedAll.lean`:511) — the
constant-map side of the `inductDecl` branch — and thereby make `addDecl_noNestedEnv` /
`VEnv.NoNestedN.of_addDecl` / `addDecls_noNestedEnv` unconditional on every branch.

Ownership: `Lean4Lean/Verify/Inductive/InductMap.lean` (new), the gate in
`Lean4Lean/Verify/Inductive/NoNestedAll.lean` (removal only, once proved), and this file.
Everything else read-only, `Verify/{Soundness,Axioms,Guard}.lean` frozen.

Starting state (recorded, dated): HEAD `0cfbdc8`, 2026-09-04. Brief reports bare build green at
1665 jobs, guards 1/2/3 ✓, census 13.

The target, verbatim from `NoNestedAll.lean`:511:

    def InductiveMapGate : Prop :=
      ∀ {env env' : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
        {iu ap : Bool} {fuel : FuelConfig},
        Environment.addInductive env lparams np types iu ap fuel = .ok env' → env.constants.WF →
          env'.constants.WF ∧ ∀ n ci, env'.constants.find? n = some ci →
            env.constants.find? n = some ci ∨ ∃ k, n ∈ Lean4Lean.indDeclNamesN types k

## §0 — PRIORS, written before the first instrument call

Read before writing these, as the brief directed: the gate's own docstring,
`addInductive_noNestedEnv`, `addMutual_noNestedEnv` and `addMutual_header_post_contains` (the
`WF`-carrying precedents), §4.1/§4.2/§4.3 and the §5 firings of `NoNestedAll.lean`, and
`docs/handoff-addinductmap.md` §0-§1 (which is about the *flip*, not this gate — confirming the
brief's correction that the two are different obligations). No LSP call, no build, no read of
`Lean4Lean/Inductive/Add.lean` yet.

### THREE SHAPE PRIORS FIRST (the four shape questions)

**S1 — does the target exist already, under another name?** `shape.lean` is blind here (the gate's
type is literally `Prop`), so the instrument must be a *hypothesis-diff*: look for anything whose
statement contains both `Environment.addInductive … = .ok env'` and a conclusion about
`env'.constants.find?` / `contains` / `SMap.WF`. `addInductive_WF_noNestedDeclNames` is the *name*
half and provably exists; the *map* half is what is missing.
**S1 (50%)** — a partial map-side lemma about which constants `addInductive` inserts already exists
somewhere in `Verify/Inductive/{AddInductiveStep,DeclareStages,RestoreFaithful,SurfaceMap}.lean`
(names hinting at it: `SurfaceMap`, `DeclareStages`), i.e. I will be composing rather than starting
from the raw implementation. 50 because the gate has survived many rounds, which is evidence
*against* an easy composition existing — but `addInductive_WF_noNestedDeclNames` already had to
walk the same implementation to get the name half, so its proof is likely reusable scaffolding.

**S2 — is the work in the direction I think?** I believe the proof is: unfold
`Environment.addInductive`, find every `Environment.add` (or `SMap.insert`) it performs, and show
(a) `SMap.WF` is preserved by each and (b) each inserted name lies in `indDeclNamesN types k` for
some `k`. That is a loop/`Except` postcondition extraction, for which the brief hands me the model
(`MutualNames.lean`'s `forIn_ok_fresh` / `addMutual_header_post`).
**S2 (70%)** — the map side really is a finite composition of `Environment.add` steps plus one or
two loops (constructors, recursors), with no third mechanism (no `modify` of `constants` outside
`add`, no `replay`, no `addDecl` re-entry). 30% that there is a further mechanism — most likely the
nested path writing auxiliary constants and then *removing* or *restoring* them, which would make
`env'.constants.find? n = some ci` reachable for a name that is neither old nor in the budget only
if `indDeclNamesN` misses the aux names; the docstring claims it includes `I.rec_k`, which is
evidence the budget was designed for exactly this.

**S3 — measurement or docstring?** The gate's docstring asserts "`indDeclNamesN` is exactly the
list the nested path declares, auxiliary recursors `I.rec_k` included", citing
`TrIndDeclN.mem_indDeclNamesN` (`Verify/Environment/InductR.lean`:329). That is a *docstring*
claim about a *kernel* function, sourced from an *abstract-side* lemma — the exact shape that has
misfired before (a lemma about `TrIndDeclN` says nothing about `Environment.addInductive`).
**S3 (60%)** — `indDeclNamesN` is defined over `types` on the kernel side (`List Name`-valued, from
`InductiveType.name`/`ctors`) and its relation to what `addInductive` inserts is **unproved**, i.e.
the docstring's citation does not discharge the map half and I must do the name arithmetic myself.
40% that `mem_indDeclNamesN` or a sibling is directly usable.

**S4 — what does the implementation compare with, and is it opaque?** Two candidate opaque walls.
(i) `env'.constants.WF`: if `SMap.WF` insert-preservation needs *freshness* of the inserted name,
I am pushed through `SMap.WF.find?_isSome` → `PersistentHashMap.containsAux`, a body-less `partial
def`. (ii) name equality: `indDeclNamesN` membership is `List.Mem` over `Name` with `BEq`/`DecEq`
— `Name.beq` is `@[extern]` but has a Lean model, unlike `Expr.eqv`.
**S4 (65%)** — `env'.constants.WF` is the *cheap* conjunct: `SMap.WF` is a staging invariant
(`map₂ = ∅` before init / stage discipline), preserved by `insert` with **no** freshness side
condition, so it needs no `containsAux` reasoning; the expensive conjunct is the `∀ n ci` one, and
the `env.constants.WF` hypothesis is spent there (turning `contains = false` guards inside
`addInductive` into `find? = none`) rather than on `WF` preservation. 35% the reverse.

### Then the cost priors

**C1 (40%)** — the gate is fully proved and removed from `NoNestedAll.lean` this round, leaving
`addDecl_noNestedEnv` unconditional. 40 and not higher because the gate has stood through at least
three rounds of neighbours landing around it, and because it is the *last* residual, which is
usually the one that is last for a reason.
**C2 (75%)** — if I get only part of it, the part I get is the `env'.constants.WF` conjunct plus
the map conjunct restricted to a *subset* of `addInductive`'s stages (e.g. the header/type
insertions but not the recursors), and the remainder will be **unproved rather than false**.
**C3 (20%)** — some conjunct of the gate as stated is actually **false** of the implementation,
i.e. `addInductive` inserts a name outside `indDeclNamesN types k` for every `k` (candidates: a
`_nested`-prefixed aux name whose index does not appear in the budget; a `.recOn`/`.below`-style
extra; the block's `I.rec` under a *different* mangling than the budget's). If so the deliverable
is a machine-checked refutation plus a repaired statement, and that is a real result, not a miss.
**C4 (55%)** — `Environment.addInductive` in `Lean4Lean/Inductive/Add.lean` inserts constants at
**≥ 4** distinct syntactic sites (types, ctors, recursors, plus at least one nested/aux site).
**C5 (85%)** — census stays 13 and I add no `sorry`; if I cannot close a conjunct I leave it as a
*smaller named* residual with a stated diff, not a hole.
**C6 (50%)** — build stays green at 1665 ± a handful of jobs and guards 1/2/3 stay ✓ (a new file
adds jobs, so the figure will move; I will report the number I measure, dated).

## §1 — MEASUREMENTS (appended one line per instrument call, as made)

**M1 — hypothesis-diff for the map half (S1's instrument).** `grep` for statements carrying
`Environment.addInductive … = .ok`/`.WF` in `Lean4Lean/Verify/`: 12 files mention it, and exactly
one has a *map* conclusion — `AddInductPost.find?_of_not_mem` (`AddDeclWF.lean`:403):
`∃ nn, ∀ n ∉ indDeclNamesN types nn, env'.constants.find? n = env.constants.find? n`, i.e. the
gate's map half in `∉`-form and **stronger** (equality, not just "old or budgeted"). But its
hypothesis is `AddInductPost`, which unfolds to `InductStepNested` — *the flip*. So it is the
seven-file route, unusable here. **S1 scores: half-right.** The statement exists; the version that
exists is downstream of the flip, so I am starting from the implementation after all.

**M2 — `indDeclNamesN`, read rather than believed** (`Verify/Environment/InductR.lean`:244,
`Verify/Environment/Induct.lean`:302):

    def indDeclNamesN (types) (numNested) : List Name :=
      indDeclNames types ++ (List.range numNested).map (auxRecName types)
    def auxRecName (types) (k) : Name :=
      appendIndexAfter' (mkRecName (types.headD default).name) (k + 1)

Both are **kernel-side** definitions over `List InductiveType`. **S3 scores: confirmed (60% → the
predicted branch).** `TrIndDeclN.mem_indDeclNamesN` is about `D.allNamesCR R K`, an *abstract*
declaration, and says nothing about `Environment.addInductive`; the docstring's citation does not
discharge the map half. The name arithmetic is mine to do.

**M2a — a free simplification nobody wrote down.** The gate quantifies `∃ k` **per name**, inside
the `∀ n ci`. Since `indDeclNamesN types k` is monotone in `k` and `auxRecName types j ∈
indDeclNamesN types (j+1)`, I never have to relate the *number* of auxiliary types to `numNested`:
each inserted name needs only *some* witness. That kills the hardest-looking coupling in the gate
(matching `mkAuxRecNameMap`'s `nextIdx` count against `res.aux2nested.length`) before it starts.

**M3 — `Environment.addInductive`, read (`Inductive/Add.lean`:1117-1205).** Five stages; only two
touch the map. (i) a guard `for` loop over `types` (`checkNoMVarNoFVar`, `checkNoNestedAux`,
`checkNoNestedAuxName`, `checkNoLooseBVars`, `checkUniformIndOccs`) — no map change; (ii)
`ElimNestedInductive.run` in `ReaderT Environment (StateT State Except)` — reads the env, never
writes it; (iii) `AddInductive.run np res.types numNested` → `env'`; **if `numNested = 0`, `return
env'` and that is the whole function**; (iv) otherwise `StateT.run (s := env)` — from the
**original** `env`, not `env'` — re-adding the user's members with restored types plus the renamed
auxiliary recursors; (v) three `TypeChecker.M.run` re-checks that read the state and never modify
it. **S2 scores: confirmed at 70%'s predicted branch, with a correction**: the mechanism is
`Environment.add` throughout (no `replay`, no `addDecl` re-entry), but the *nested* branch is not
"more adds on top of `env'`" — it **discards `env'`'s map** and rebuilds from `env`. That is
better for me than S2 assumed: the nested branch's delta is over `env` directly.

**M4 — the three `add` sites in `AddInductive.run` (`Inductive/Add.lean`:285,390,624).**
`declareInductiveTypes`: `infos.foldlM` with `env.add (.inductInfo info)`, `info.name = member
name`. `declareConstructors`: two nested `foldlM` with `env.add (.ctorInfo {name := ctor.name,…})`.
`run`'s recursor loop: `for h : dIdx in [:indTypes.size]`, `env.add (.recInfo {name := mkRecName
indTypes[dIdx].name,…})`. Every one preceded by `checkName`. So `AddInductive.run`'s inserted key
set is exactly `indDeclNames res.types`. **C4 scores: wrong (55% for ≥4 sites).** There are
**three** in `AddInductive.run` and **four** in the nested branch (`.inductInfo`, `.ctorInfo`,
`processRec` for user members, `processRec` for auxiliaries) — but the two branches are exclusive,
so no run of `addInductive` sees more than four, and the non-nested run sees three.

**M5 — `ElimNestedInductive.run` preserves the user members' names** (`Inductive/Add.lean`:877).
`res.types = s.newTypes.toList`, `newTypes` initialised to `types.toArray` and touched in exactly
two ways: `set! i { indType with ctors := … }` where each ctor is `{ ctor with type := … }` (names
untouched), and `newTypes.push newType` inside `replaceIfNested` (:840) — which sits in the same
`for J_name in I_val.all` loop as `nestedAux.push`. So `res.aux2nested = []` (i.e. `numNested = 0`)
forces `newTypes` never pushed, hence `res.types` has **exactly** `types`' names and constructor
names. This is what makes the non-nested branch's budget `indDeclNames types` rather than
`indDeclNames res.types`.

**M6 — the toolkit exists, and it is `Except`-flavoured, not `VContext`-flavoured.**
`Verify/Inductive/DeclareStages.lean` has `r113e_constants_wf_add` / `r113e_find?_add_self` /
`r113e_find?_add_ne` (§1, all three from `SMap.WF.insert` + `WF.find?_insert`), a loop rule
`r113e_addLoop_WF` whose **fourth** conjunct is `∀ n, (∀ b ∈ xs, (g b).name ≠ n) → env'.find? n =
env.find? n` — the "nothing else moves" clause, i.e. the gate's map half for that loop — and
`AddInductive.M.WF.declareInductiveTypes` / `.declareConstructors` built on it. `AddInductive.M.WF`
is `∀ env', f c = .ok env' → P env'` at a plain `AddInductive.Context`: **no `VContext`, no `ves.WF
env`**, so the `venvsWF_refuted_at_inductInfo` poison the brief warned about does not reach it.
**S4 scores: refuted in its cheap half.** `r113e_constants_wf_add` needs `env.find? ci.name =
none`, i.e. `SMap.WF.insert` *does* want the key absent — so `env'.constants.WF` is **not** free:
it is bought by the same `checkName` freshness the map half needs, through
`mapWF.find?'_eq_find?`. The `env.constants.WF` hypothesis is spent on *both* conjuncts, which is
why the gate is well-posed only with it — exactly the brief's reading.

**M7 — `SMap.WF` read, and S4's cheap half refuted in the other direction.** `Lean.SMap.WF`
(`Lean4Lean/Std/SMap.lean`:29) has two fields, `stage₁ = true` and `map₂ = .empty` — a *staging*
invariant. Consequences, both used: (i) `SMap.WF.insert`'s hypothesis `_hn : s.find? k = none` is
**unused in its own proof** (`obtain ⟨st,m₁,m₂⟩ := s; cases h.stage; exact ⟨rfl, h.map₂⟩`), and
`WF.find?_insert` needs no freshness either — so `SMap_wf_insert` and `find?_add` in §1.1 of
`InductMap.lean` are the freshness-free forms, and `env'.constants.WF` costs nothing. (ii) `SMap.WF`
does **not** say an entry is stored under its own name. That is what makes the `ci.name = n`
conjunct of the delta load-bearing: the nested branch re-adds an `.inductInfo` it read back out of
the intermediate environment at *its own* `name` field, so a mis-keyed entry in the incoming `env`
would let `addInductive` write an arbitrary name. **S4 scores half-right**: `env'.constants.WF` is
indeed the cheap conjunct (65% branch), but not for the reason given — no `containsAux` reasoning
is involved *anywhere*, because freshness is never needed for `WF`. Where `env.constants.WF` is
actually spent is `checkName.WF` (`Verify/Environment/Checker.lean`:13), which needs
`find?_isSome` to turn `contains = false` into `find? = none`, i.e. exactly the bridge the brief
predicted — but for the *monotonicity* clause of the delta, not for `WF`.

**M8 — the delta calculus needs no freshness clause and no per-step name bookkeeping.** With
`find?_add` unconditional, `DeltaCore env env' B` (wf ∧ mono ∧ keyed) composes by `trans` at a
**fixed** budget `B`, so every loop invariant in this file is constant. That removes the
`hnone`/`hother` bookkeeping `DeclareStages.lean`'s `r113e_addLoop_WF` carries. Two consequences
for the plan: `MapDeltaIn` is the relativised export (`env.constants.WF → DeltaCore …`), and every
internal lemma takes `mapWF` explicitly — because a relativised invariant cannot be used inside a
loop body, where `checkName.WF` needs the *current* map's `WF` to state its own postcondition.

**M9 — the CPS frames, measured and closed (2026-09-04).** `AddInductive.M = ReaderT Context
(Except Exception)` and **none** of the continuation-passing phases calls `withEnv` or `add`, so an
environment-only postcondition passes through them. Nine frame lemmas, all proved in
`InductMap.lean` §2: `withLocalDecl_frame` (`rfl` on the context — the plain-`Context` analogue of
`Verify/Inductive/Add.lean`'s `M.WF.withLocalDecl`, which is at a `VContext` and carries
`TrExprS`/`IsType` obligations a map statement does not need), `WF_checkInductiveTypes_loop`,
`WF_checkInductiveTypes_loopInd`, `WF_checkInductiveTypes`, `WF_loopArgs1`, `WF_loopInd1`,
`WF_loopCtorArgs`, `WF_loopU`, `WF_loopCtors`, `WF_loopInd2`, `WF_mkRecInfos`. Three findings worth
recording:
* `checkConstructors`, `getElimLevel`, `isKTarget`, `mkRecRules` and `loopUArgs` need **no** frame:
  they occur in *value* position (`let x ← f …`), where `M.WF.bind_triv` treats them as opaque. So
  the CPS surface is **two** functions (`checkInductiveTypes`, `mkRecInfos`), not five.
* `rw [f]` on a `let rec` whose body matches on an `Expr` silently picks the *fallback* equation
  and leaves an unprovable side goal `∀ name dom body bi, type = .forallE … → False`. `rw
  [f.eq_def]` is the correct instrument; then `split` on the fuel match renames the fuel and needs
  `obtain rfl : fuel' = fuel := (Nat.succ.inj heq).symm`.
* `split` cannot see through the `have __do_jp := …` join points the `do`-elaborator inserts for a
  `mut`-variable `if`/`else if`; `dsimp only` zeta-reduces them first. This cost three iterations
  and is the kind of thing that makes a round's cost estimate wrong.

**M10 — residual A is a theorem, and no *flat* invariant can prove it.** The coupling needed for the
non-nested branch is `res.types.length = types.length` when `res.aux2nested = []`. Measured against
the implementation: `newTypes` is pushed at `Inductive/Add.lean`:858, inside the same
`for J_name in I_val.all` body as the `nestedAux` push at :845 and **after** it. Two candidate flat
invariants are both refuted by that: `newTypes.size ≤ L + nestedAux.size` is broken by the
`newTypes.push`, and `L + nestedAux.size ≤ newTypes.size` by the `nestedAux.push`. What works is
`Bal L s := s.nestedAux = #[] → s.newTypes.size = L`, which **every** step preserves except the
`newTypes.push`, plus `NE s := s.nestedAux ≠ #[]`, which every step preserves including it, and
`NE → Bal L` vacuously. The automation then works after all, because the *switch* can be an
alternative of the `first` combinator: a `MWF.bind'` whose first component is the `nestedAux.push`
with postcondition `NE`. `MWF.replaceIfNested_bal` went through on the first attempt with that one
extra alternative. `NestedRunInvariant.lean`'s `MWF.{replaceNoCacheT, isNestedApp', forIn_inv,
mapM', panic', liftExcept', get_inv, read_inv, withParams'}` are already generic in the invariant;
only `mkUniqueName` and `replaceParams` needed re-stating (`MWF.mkUniqueName_gen`,
`MWF.replaceParams_gen`), both two-line, both from `mkUniqueName_state` / `panic_eq`, which that
file already proved.

**M11 — final build, dated.** 2026-09-04 21:20 UTC. Started at HEAD `0cfbdc8`; other streams landed
`9dbff4e`, `531d9eb`, `42925b4` during the round, and the measurements below were taken against
`42925b4` + this file (all three of theirs are `Theory`/docs commits and touch nothing in my cone). `lake build` (bare):
**green, 1667 jobs** (1665 before; the new module is +2). Guards, from `lake build
Lean4Lean.Verify.Guard`: **guard 1 ✓** (exactly the 24 frozen axioms), **guard 2 ✓** (kernel_sound
axioms within whitelist; still `proof INCOMPLETE: sorryAx present`, unchanged by this round),
**guard 3 ✓** (2/2 implementation gaps). **Sorry census 13**, unchanged — this round adds none, and
no declaration of mine has a hole or reaches `sorryAx`. Warnings from the file I own: **none**.

| name (all in `Verify/Inductive/InductMap.lean`) | arity | cone | hole | sorryAx | axioms |
|---|---|---|---|---|---|
| `Lean4Lean.inductiveMapGate_of` | 11 | 9213 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.addInductive_mapDelta` | 9 | 9212 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.AddInductive.WF_run` | 5 | 8746 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.AddInductive.WF_mkRecInfos` | 8 | 7466 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.AddInductive.WF_checkInductiveTypes` | 7 | 7316 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.runBudget_of_noAux` | 13 | 5800 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.ElimNestedInductive.MWF.run_bal` | 5 | 5737 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.elimNoAuxGate` | 0 | 5739 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.ElimNestedInductive.MWF.replaceIfNested_bal` | 6 | 5518 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.find?_add` | 4 | 3463 | false | false | propext, Classical.choice, Quot.sound |
| `Lean4Lean.InductiveMapGate` (the target, unchanged) | 0 | 7751 | false | false | — |

No frozen axiom appears in any cone: the three axioms above are the Lean core three, and
`Verify/Guard.lean`'s whitelist question does not arise (guard 1 still reports exactly 24). The
"watched declarations in cone: none of 6" line is `scripts/exists.lean`'s hole-watch, clean for
every entry.

## §3 — THE RESULT, AND ITS LIMITS

### §3.1 What is proved

`InductiveMapGate` is **not** closed. What is closed is stated exactly, in
`Lean4Lean.inductiveMapGate_of`: the gate's own statement, restated verbatim (it cannot be imported
— `NoNestedAll.lean` sits above this file), follows from **one** hypothesis, residual B below. So
the round converted `InductiveMapGate` from an unanalysed `Prop` into a *strictly smaller* named
residual, with everything else machine-checked:

* **§1 the delta calculus.** `DeltaCore env env' B` (wf ∧ mono ∧ keyed-under-own-name), composable
  at a fixed budget. `find?_add` and `SMap_wf_insert` are the freshness-free `Environment.add`
  equations (M7).
* **§2 the CPS frames**, eleven lemmas: `AddInductive.M`'s continuation-passing phases move only
  `lctx`/`ngen`, so an environment-only postcondition passes through them.
* **§3 the three `add` sites** and **`WF_run`**: *every constant `AddInductive.run` writes is a
  member name, a constructor name, or `mkRecName` of a member name of the block it was called on*.
  This is the piece the gate is really about, and it is unconditional.
* **§3.3 residual A, proved** (`elimNoAuxGate`): `ElimNestedInductive.run` reporting
  `numNested = 0` implies it added no member, so the block `AddInductive.run` sees is the input
  block.
* **§4 the split**: `Environment.addInductive`'s `numNested = 0` exit is discharged outright.
* **§5 the firing**: a build-time `#eval` that *throws* unless `Environment.addInductive` accepts
  `inductive Foo : Prop | mk` from the empty environment and the resulting map holds **exactly** the
  three `indDeclNames` names — so §4's `Except.WF` is not satisfied vacuously, and all three `add`
  sites fired.

### §3.2 What is not, and whether it is false

**Residual B — the nested rebuild.** Unproved, and **not false**. Its statement is the hypothesis
`GB` of `addInductive_mapDelta` / `inductiveMapGate_of`: on inputs where
`ElimNestedInductive.run` reports `res.aux2nested ≠ []`, `Environment.addInductive`'s delta stays
inside `indBudget types`. Why it is a separate obligation and what it needs, measured:

1. That branch **discards** `AddInductive.run`'s environment and rebuilds from the *original* `env`
   (`Inductive/Add.lean`:1156, `StateT.run (s := env)`), so §3's delta is not the answer — it is an
   *input* to the answer, because the block reads `env'` back with `env'.find?`.
2. The four `add` sites are keyed by `ind.name`, `ctor.name`, `mkRecName indType.name` and
   `(recNameMap'.lookup recName).getD recName`. The last two are budgeted by inspection
   (`auxRecName types j = appendIndexAfter' (mkRecName (types.headD default).name) (j+1)` is exactly
   what `mkAuxRecNameMap` builds, and `indDeclNamesN types (j+1)` contains it — note the gate's
   `∃ k` is **per name**, so the number of auxiliary members never has to be matched against
   `numNested`, which kills the coupling that looks hardest).
3. The first two are **not** budgeted by inspection, and this is the real content: `ind` comes from
   `env'.find? indType.name`, and `SMap.WF` does not forbid a mis-keyed entry (M7), so
   `ind.name = indType.name` and `ind.ctors = types[j].ctors.map (·.name)` have to be *derived*.
   The derivation available: `DeclareStages.lean`'s positive clauses
   (`M.WF.declareInductiveTypes`/`.declareConstructors`) carried forward by `DeltaCore.mono`, plus
   `NestedRunInvariant.lean`'s `run_prefix` (proved, unconditional) to move from `res.types[j]` to
   `types[j]`.
4. That needs one thing this round did **not** prove: `stats.nindices.size = its.size`, because
   `r113eIndInfos` is an `Array.zipWith` of `indTypes` with `stats.nindices`, so the positive clause
   at index `j` is available only when the zip reaches `j`. It is an extra invariant on
   `WF_checkInductiveTypes_loopInd` (`nindices.size = dIdx ∧ dIdx ≤ its.size`, plus
   `indConsts.size = dIdx`, `levels = c.lparams.map .param` and `dIdx = 0 ∨ params.size = nparams`
   to make the four `assert!`s at `Inductive/Add.lean`:253-256 not fire — a fired `assert!` hands the
   continuation `default`, whose `nindices` is `#[]`, and `default.nindices.size = its.size` then
   holds only when `its.size = 0`, which is the one case to split on).
5. Plus a `StateT Environment (Except Exception)` analogue of §1's calculus and three loop rules.

Estimated at 400-500 lines. Nothing in it looks false; every sub-fact named above is either already
proved elsewhere or an invariant on a loop whose body is already written out here.

### §3.3 The gate is **not** removed from `NoNestedAll.lean`

I own that file's gate and did not touch it, because the honest reading of "you may remove the gate
once you have proved it" is that residual B leaves it unproved. `NoNestedAll.lean` is unchanged;
`addDecl_noNestedEnv` still carries `InductiveMapGate`, and `VEnv.NoNestedN` is still conditional on
the `inductDecl` branch and unconditional on the other six. What a later round removes it with is
`inductiveMapGate_of` applied to a proof of residual B — the statement is already the gate's, word
for word, so no restatement or re-derivation is needed at that point.

**Quoted before not-removing** (`NoNestedAll.lean`:511-517, the target, unchanged on disk):

    def InductiveMapGate : Prop :=
      ∀ {env env' : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
        {iu ap : Bool} {fuel : FuelConfig},
        Environment.addInductive env lparams np types iu ap fuel = .ok env' → env.constants.WF →
          env'.constants.WF ∧ ∀ n ci, env'.constants.find? n = some ci →
            env.constants.find? n = some ci ∨ ∃ k, n ∈ Lean4Lean.indDeclNamesN types k

Two of its docstring's claims are now **wrong** and should be repaired by whoever owns the text
(I did not edit it): "the map side of the inductive step — the *seven-file flip*" (`:535`, `:608`,
and `Inductive/Add.lean`:1096, `RestoreFaithful.lean`:418) — it is **not** the flip; the flip is
`AddInductPost`/`InductStepNested`, and this gate is discharged from the implementation with no
reference to `AddInduct` at all, as the brief said and as `WF_run` now demonstrates. And the
docstring's citation of `TrIndDeclN.mem_indDeclNamesN` as the reason `indDeclNamesN` is "exactly the
list the nested path declares" does not bear on the gate: that lemma is about `D.allNamesCR R K`, an
abstract declaration, and says nothing about `Environment.addInductive` (M2).

## §4 — PRIOR SCORING

| prior | p | outcome |
|---|---|---|
| S1 (a partial map-side lemma exists to compose from) | 50% | **half-right** — `AddInductPost.find?_of_not_mem` is the statement, in stronger `∉`-form, but gated on the flip, so unusable. The *reusable* material was elsewhere and richer than expected: `DeclareStages.lean`'s loop rules and `NestedRunInvariant.lean`'s invariant-generic `MWF` calculus did most of §3 and all of §3.3's plumbing. |
| S2 (the map side is `Environment.add` sites plus loops, no third mechanism) | 70% | **confirmed**, with the correction that the nested branch discards `env'` and rebuilds from `env` — which makes residual B *harder* (it must read `env'` back) and §4 *easier*. |
| S3 (`indDeclNamesN`'s relation to what `addInductive` inserts is unproved; the docstring's citation does not discharge it) | 60% | **confirmed** — and the name arithmetic was mine to do, `runBudget` → `indDeclNames`. |
| S4 (`env'.constants.WF` is the cheap conjunct; `env.constants.WF` is spent on the `∀ n ci` half through `contains`→`find?`) | 65% | **half-right, right answer for the wrong reason** — `WF` is free because `SMap.WF.insert` ignores freshness (M7), not because staging avoids `containsAux`; and `env.constants.WF` is spent on `checkName.WF`, needed for the *monotonicity* clause, not the budget clause. |
| C1 (gate fully proved and removed this round) | 40% | **missed.** One residual (B) remains; the gate stays in `NoNestedAll.lean`. |
| C2 (a partial result is `WF` plus a *subset of stages*, and the remainder is unproved not false) | 75% | **half-right.** The partition was not by stage but by *branch*: all three stages of `AddInductive.run` are closed, and the split is non-nested (closed) vs nested (open). "Unproved not false" holds. |
| C3 (some conjunct is actually false of the implementation) | 20% | **not fired.** No refutation found; the closest thing is that a mis-keyed `env` entry *would* refute the nested branch were it not for `declareInductiveTypes`' `checkName`, which is why residual B needs the positive clauses rather than just the delta. |
| C4 (≥4 `add` sites) | 55% | **wrong as stated, right in substance** — three in `AddInductive.run`, four in the nested rebuild, but the branches are exclusive, so no run sees more than four and the non-nested run sees three. |
| C5 (census stays 13, no `sorry`; a shortfall is a *smaller named* residual with a stated diff) | 85% | **confirmed**, both halves: census 13, and residual B is named with its five sub-obligations listed. |
| C6 (build green, jobs move, guards ✓) | 50% | **confirmed**: 1667 jobs (1665 + 2), guards 1/2/3 ✓. |

## §5 — METHOD GAPS

1. **I did not price the round before starting it.** The §0 cost priors were about *outcomes*, not
   about line counts, so "40% the gate lands" was a guess with no model behind it. A per-stage line
   estimate written at §0 (frames 300, run 200, coupling 200, nested 400) would have told me at the
   outset that the nested branch was out of reach and that the right shape was "reduce to residual
   B", which is what I ended up doing by accident rather than by plan.
2. **Three of the four shape priors scored "half-right", and in two cases the half that was wrong
   was the *mechanism*.** S4 predicted the right conjunct is cheap and the wrong reason why; S1
   predicted the right conclusion (compose, don't start from scratch) but the wrong source. A prior
   that names an outcome without naming the instrument that would distinguish its branches is not
   falsifiable in the way rule 1 intends.
3. **Two tool-level facts cost five iterations and are not in any doc**: `rw [f]` on a `let rec`
   whose body matches an `Expr` silently selects the *fallback* equation and emits an unprovable
   side goal (use `f.eq_def`), and `split` cannot see through the `have __do_jp := …` join points
   the `do`-elaborator emits for `mut`-variable `if`/`else if` (use `dsimp only` first). They are
   recorded in M9 for the next stream.
4. **I did not check whether residual B is *satisfiable* at a real nested block.** §5's firing
   exercises only the non-nested branch. A `#eval` on `Lean.Json` or `Lean.PrefixTreeNode` (which
   `MRedex.MRWit` already uses) would show the nested rebuild running and its output map's names, and
   would catch a *false* residual B before anyone spends 400 lines on it. That is the first thing the
   next round should do, before writing any Lean.
5. **The `∃ k`-per-name simplification (M2a) was found by reading the statement, not by any
   instrument.** It removes the hardest-looking coupling in the gate, and it had been sitting in the
   gate's text for several rounds. There is no method step in this round's rules that would have
   surfaced it; "read the target's quantifier structure before pricing it" should be one.
