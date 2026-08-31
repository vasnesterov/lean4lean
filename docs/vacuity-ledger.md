# The vacuity ledger

*Written 2026-08-31, after four independent instances of the same failure mode turned up in
one round.*

## 0. Why this file exists

This project has two automated measurements of how far the proof has to go, and **both are
blind to the same failure mode**.

| instrument | counts | blind to |
| --- | --- | --- |
| `scripts/sorry-census.lean` | declarations whose value mentions `sorryAx` | a hole that is not a `sorry` |
| guard 3 (`Verify/Guard.lean`) | `partial` / `@[extern]` / `@[implemented_by]` reachable from `addDecl` | anything in the *specification* |
| `scripts/hole-cone.lean` | which `sorry`s a given theorem depends on | **a hypothesis** — a cone walks `deps`, and a hypothesis is not a dependency |

The failure mode none of them sees: **a statement that is green because it says nothing.**

A lemma whose hypotheses cannot be jointly satisfied is *provable*, records as sorry-free,
appears in no cone as a hole, and contributes exactly nothing. It is strictly worse than a
`sorry`, because a `sorry` is honest — it is red, it is counted, and it names itself. A
vacuous lemma looks like progress.

Guard 2 — the stop condition — is `#print axioms Lean4Lean.kernel_sound`. It cannot tell the
difference. **A chain of vacuous lemmas can make guard 2 print "proof COMPLETE" over a proof
of nothing.** That is not a hypothetical; §4 below is a machine-checked demonstration.

So: a third instrument, `scripts/empty-inductives.lean`, plus this ledger, which is the part
that cannot be automated — for each load-bearing statement, whether its hypotheses are
known-satisfiable, known-unsatisfiable, or **unmeasured**.

## 1. The root: one empty inductive

    ~/.elan/bin/lake env lean scripts/empty-inductives.lean
    empty-inductives: 1 in the Lean4Lean namespace
      Lean4Lean.AddInduct: reach 31, Prop  <-- VACUITY SOURCE

`Lean4Lean.AddInduct` (`Verify/Environment/Basic.lean:149`) is declared

    inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop
      -- TODO

with **no constructors**, and it is the single root cause of every entry in §3. It is the only
empty inductive in the package, and the mechanism by which it does damage is worth stating
precisely, because it is *not* the obvious one:

1. `AddInduct` is empty, so it is equivalent to `False`.
2. It appears as a **premise of the `induct` constructor of `TrEnv'`**. So that constructor can
   never fire, and `TrEnv' safety m Q venv` is unsatisfiable for any `m` holding an
   `.inductInfo` at the relevant safety level. This is not vacuity — it makes `TrEnv'` *too
   strong*, i.e. false where it should hold.
3. *Therefore* every statement that takes `TrEnv'` (or `TrEnv`, or `VEnvs.WF`) as a
   **hypothesis** at such an environment is vacuous.

Two hops, and the second hop is where the green comes from. Both `AddInduct.to_addInduct`
(`Basic.lean:153`, proved `nomatch H`) and `VEnvs.WF.no_inductInfo`
(`Verify/InductFlip.lean:366`) are the emptiness in usable form.

`scripts/empty-inductives.lean` prints `reach` = the number of declarations naming `AddInduct`
directly. Today all 31 are `AddInduct`'s own auto-generated eliminators, `TrEnv'`'s API, and
`AddInductFlip`. That is the blast radius to audit.

## 2. The flip, stated exactly

The repair has a name in the tree already. `AddInductFlip`
(`Verify/Inductive/AddDeclWF.lean:463`):

    def AddInductFlip : Prop :=
      ∀ {m m' : ConstMap} {env env' : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore},
        AddInductStagesR m env D K R m' env' → AddInduct m env D m' env'

and `InductStepNested.trEnv'` (same file, :470) proves that **the flip alone** carries the
honest arm to the `TrEnv'` step — no extra hypothesis, no side condition. So the distance from
here to a non-vacuous `TrEnv'` is exactly this one `Prop`.

Discharging it means giving `AddInduct` constructors, which turns
`AddInduct.to_addInduct`'s `nomatch H` into a real obligation. Its cost is measured in
`docs/critical-path.md` §"what the flip costs": census **14 → 17**, the three being
`reduceProjCore_none`, `reduceProjCore.WF`, `inductiveReduceRec_eq_none` — theorems asserting
the checker never handles inductives, sorry-free today *only because* `AddInduct` is empty.

**This is the human's decision and no agent should take it.** It is not a frozen-file edit
(`Basic.lean` is proof machinery); it is a decision only because it raises the census, and a
rising census is the one thing that looks like regression while being progress.

## 3. Registry of measured statements

Every row is backed by a **proved** lemma in the tree, not an argument in a docstring. Kinds:

- **vacuous** — the statement's own hypotheses are jointly unsatisfiable; it is provable and
  says nothing.
- **false** — the statement is refutable as written; it must be *re-derived from a different
  statement*, never assumed.
- **dead route** — a proposed sufficient condition is itself unattainable, so that route to
  the goal is closed (this is useful negative information, not a defect).
- **bounded** — a residual hypothesis proved *neither* trivially true *nor* false. This is the
  good outcome and the discipline §5 asks for.

| # | statement | kind | proved by | flip repairs? |
| --- | --- | --- | --- | --- |
| 1 | `addDecl.WF`, `inductDecl` branch | **false** | `addDecl_inductDecl_WF_false` (`Verify/Inductive/AddDeclWF.lean:306`) | **yes** — this is the flip's purpose. Reshape to `AddDeclPost` meanwhile. |
| 2 | `foldAddDecl_tr` (`Verify/Bridge.lean:172`) | **false** |  `foldAddDecl_tr_false` (`Verify/PreludeVacuity.lean:93`); **proved theorem, see §4a** | **yes** |
| 3 | `PreludeBridge stdPrelude` (`Verify/Bridge.lean:225`) | **vacuous** | `preludeBridge_vacuous_at_nil` (`PreludeVacuity.lean`) | **yes** — real only after the flip |
| 4 | `TrEnv .safe env venv` at any `env` holding a safe inductive | **false** | `TrEnv.not_safe_inductInfo` (`PreludeVacuity.lean:73`) | **yes** — the mechanism itself |
| 5 | `addQuot.WF`, non-initialized branch | **vacuous** | `addQuot_trivial_of_wf` (`Verify/QuotReach.lean:261`), `no_wf_envEqInd` (:241) | **yes** |
| 6 | `coherentOn_addConstList` / `coherentOn_addInduct`, `hocc` at the pre-block environment | **vacuous** | `addConstList_hocc_unsat` (`Theory/SetModel/CnstRecursion.lean:117`), `hocc_unsat_eqIndDecl` (:150) | **no** — independent mis-statement; repaired by `StagedOcc` + `coherentOn_addConstList'`, separation witnessed by `stagedOcc_separates` (:179) |
| 7 | model parameter `LevelAssign` | **circular** — the parameter *contained* the hole it was used to prove | `levelAssign_gives_sortUniq` (`Theory/SemanticRouteClosed.lean:136`) | **no** — independent; already repaired by replacing the parameter |
| 8 | `LevelSeparating` as a route to `SortUniq` | **dead route** | `hasChains_refutes_levelSeparating` (`SemanticRouteClosed.lean:235`) | n/a |
| 9 | `ForallPropDomInj` (`PiInv`'s domain conjunct) | **dead route** | `not_forallPropDomInj` (`SemanticRouteClosed.lean:403`) | n/a |
| 10 | `OracleOK` residual | **bounded** | `not_oracleOK_falseProp` (`CnstRecursion.lean:651`) — not satisfiable by an inconsistent oracle | n/a |
| 11 | `InductOracleOK` residual | **bounded** both ways | `not_inductOracleOK_falseProp` (:663) and `inductOracleOK_empty` (:676) | n/a |
| 12 | `SortInv` from the model | **bounded** — exact, an `iff` | `sortEqRaw_iff` (`SemanticRouteClosed.lean:217`) | n/a |
| 13 | `inferProj` / `tryEtaStructCore` / `isDefEqUnitLike` never fire | **true today, and their falsity is the goal** | `inferProj_always_throws`, `tryEtaStructCore_never_true`, `isDefEqUnitLike_never_true` | the flip **kills** these three (correctly) |

Rows 1–5 are one bug. Rows 6 and 7 are independent, and that is the ledger's main finding:
**the failure mode is not confined to `AddInduct`.** It recurred in the abstract theory
(row 6, a hypothesis stated at the wrong environment) and in the model interface (row 7, a
parameter that assumed its own conclusion). Neither has anything to do with the other.

## 4. The trap: how guard 2 could print a false "proof COMPLETE"

`Verify/Inductive/AddDeclWF.lean` §5.4 item 3 proposes making `foldAddDecl_tr` a *hypothesis*
of the assembly, so that the chain type-checks while the inductive case is open. That is
exactly the wrong move, and it is refuted in the tree
(`Verify/PreludeVacuity.lean`):

    theorem anything_of_foldAddDecl_tr_hypothesis (hex : PreludeHoldsSafeInduct)
        (hbad : ∀ (fuel : FuelConfig) (ds : List Declaration) (env : Kernel.Environment),
          foldAddDecl fuel ds = .ok env → ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF)
        (Q : Prop) : Q :=
      absurd hbad (foldAddDecl_tr_false hex)

Assuming row 2 proves **any proposition**, `kernel_sound` included, and `#print axioms` would
report nothing amiss because no axiom was added — the falsity entered as a hypothesis. The
`hex` side condition is discharged by an `#eval` in the same file, which confirms `stdPrelude`
leaves `Eq` an `.inductInfo` with `isUnsafe = false`.

**Standing rule.** A statement in the **false** column of §3 is never to be assumed as a
hypothesis, a parameter, an `axiom`, or a `variable`. It must be *replaced* by a statement that
is true, and the replacement's non-vacuity recorded here.

## 4a. A *proved* theorem with a false statement — and what that condemns

Row 2 deserves its own section, because `foldAddDecl_tr` is not an open goal. It is a
**proved theorem** (`Verify/Bridge.lean:172`), five lines, no `sorry` of its own:

    theorem foldAddDecl_tr (hok : foldAddDecl fuel ds = .ok env) :
        ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF := by
      obtain ⟨ves, wf⟩ := foldAddDecl_WF hok
      exact ⟨ves.venv .safe, wf.tr, wf.tr.wf⟩

and its statement is false (`foldAddDecl_tr_false`, modulo `hex`, which the `#eval` in
`PreludeVacuity.lean` confirms). A proof of a false statement means the proof rests on a
`sorry` that **cannot be filled** — filling it would prove `False`.

Its hole cone is exactly nine declarations:

    Lean4Lean.addDecl.WF                                  <-- row 1, the condemned one
    Lean4Lean.TrProj.uniq
    Lean4Lean.TrProj.weak'_inv
    Lean4Lean.TypeChecker.Inner.inferProj.WF
    Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF
    Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF
    Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified
    Lean4Lean.VEnv.IsDefEqU.weakN_iff
    Lean4Lean.VEnv.WF.rigidShapeUniqNS

**Read this correctly.** The natural inference — "these nine are all suspect" — is wrong, and
getting it wrong would stall the work that is actually sound. Falsity does not propagate
backwards along a proof: a true lemma can perfectly well be used in an unsound derivation. What
the measurement establishes is that **at least one** of the nine is unfillable as stated, and
row 1 already identifies which: `addDecl.WF`'s `inductDecl` arm, refuted by
`addDecl_inductDecl_WF_false` independently of this cone.

The other eight are ordinary open holes, upstream of a bad consumer. `IsDefEqU.weakN_iff`,
`forallE_inv_stratified`, `rigidShapeUniqNS`, the two `TrProj` lemmas — none of them is
implicated. Rows 13 and §6 note separately that the three checker `.WF` holes will only acquire
*content* after the flip, which is a different observation (they are vacuity-adjacent, not
condemned).

For contrast, the `False`-witness half of the assembly measures clean: `hasType_falseProp`'s
cone is **7244 declarations with zero holes**. The soundness statement's other wing is finished.

Reproduce with the walker in `scripts/hole-cone.lean` seeded at
`Lean4Lean.Bridge.foldAddDecl_tr`, `Lean4Lean.addDecl.WF`, `Lean4Lean.Bridge.hasType_falseProp`.

## 5. The discipline this ledger asks for

Three checks, in order of cost:

1. **Before proving a lemma, satisfy its hypotheses.** Exhibit one environment / one
   declaration / one value where they all hold — an `#eval` is enough, and `#eval` witnesses in
   `PreludeVacuity.lean` and `AddDeclWF.lean` are the pattern. If you cannot, the lemma is a
   candidate for §3.
2. **When you reduce a goal to a residual, bound the residual both ways.** Prove it is not
   trivially true (some instance fails) *and* not false (some instance holds). Rows 10–12 are
   what this looks like; `not_inductOracleOK_falseProp` + `inductOracleOK_empty` is the model.
   A reduction to an unmeasured residual is not progress, it is relocation.
3. **`lake env lean scripts/empty-inductives.lean` must print an accounted-for list.** Every
   empty inductive in the package needs an entry here saying why it is empty. Today: one, and
   §1 is its entry.

## 6. Unmeasured — the to-do

Load-bearing statements whose hypotheses have **not** been checked for joint satisfiability.
This is the honest part of the ledger; the entries above were all found by looking, and nobody
has looked at these.

- `Bridge.AddDeclWF` (`Verify/Bridge.lean:132`) — repeats row 1's refuted statement verbatim,
  and `Bridge.addDeclWF` (:138) derives it from `addDecl.WF`. Presumed **false** by row 1 but
  not separately measured.
- The `TrProj` family — `TrProj.weak'_inv` (29 users), `TrProj.uniq` (93). These have open
  `sorry`s, so they are counted; what is unmeasured is whether their *hypotheses* are
  satisfiable at a structure the checker actually reaches, given row 13.
- `inferProj.WF` (0 users), `isDefEqUnitLike.WF` (1), `tryEtaStructCore.WF` (2) — the three
  checker `.WF` holes. Row 13 says the functions never fire today, so these three are
  vacuity-adjacent by construction: they will only acquire content after the flip.
- `Theory/Typing/` step lemmas generally. Row 6 was found in `docs/soundness-ledger.md`'s list
  of "available" step lemmas, which means that list was not satisfiability-checked. It should
  be, entry by entry.

## 7. Related files

- `docs/critical-path.md` — what stands between here and `kernel_sound`, with Corrections 3
  and 4 recording rows 1–4.
- `docs/frozen-edit-requests.md` — the proposals touching frozen files, none made. Its closing
  section notes that the flip is *not* one.
- `docs/soundness-ledger.md` — the abstract-side inventory; row 6 is its correction.
- `scripts/empty-inductives.lean` — the instrument for §1.
