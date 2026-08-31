# The vacuity ledger

*Written 2026-08-31, after four instances of the same failure mode turned up in one round, and
a survey then found four more already refuted elsewhere in the tree. Nineteen statements are
now measured; six are vacuous or false, three are refuted outright, two routes are dead, and
eight are bounded or acquitted.*

## 0. Why this file exists

This project has two automated measurements of how far the proof has to go, and **both are
blind to the same failure mode**.

| instrument | counts | blind to |
| --- | --- | --- |
| `scripts/sorry-census.lean` | declarations whose value mentions `sorryAx` | a hole that is not a `sorry` |
| guard 3 (`Verify/Guard.lean`) | `partial` / `@[extern]` / `@[implemented_by]` reachable from `addDecl` | anything in the *specification* |
| `scripts/hole-cone.lean` | which `sorry`s a given theorem depends on | **a hypothesis** — a cone walks `deps`, and a hypothesis is not a dependency |

And a fourth blindness, the mirror image of the third and just as costly: **an obligation
carried as a hypothesis of a *proved* theorem counts as zero.** `VEnv.addInductR_ordered'`
(`Theory/Inductive/NestedOrdered.lean:146`) is proved, sorry-free, and in nobody's hole cone —
and it carries three undischarged obligations (`hctors`, `hrecs`, `hrules`) that are the entire
nested-soundness content of the inductive route. Factoring a hole into named hypotheses is good
practice and this repo does it well; the cost is that the census then reads 0 where the work
is. §6 lists the four such obligations that block the goal today.

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
| 14 | `LevelAssign` as originally stated (`LevelAssignUnguarded`) | **`IsEmpty`** — the strongest form there is | `no_levelAssign` (`Theory/SetModel/LevelAssignUnsat.lean:106`) | **no** — independent; repaired by guarding `lvl_sound` |
| 15 | `LevelAssign.Stable`'s `lvl_instN` as originally stated | **unsatisfiable** | `no_stable` (`LevelAssignUnsat.lean:172`) | **no** — repaired by the `env.HasType` guard, which its docstring flags as load-bearing |
| 16 | `CtxInvariant L R` **in isolation** | **trivially satisfiable, hence untestable alone** — take `R := Eq` | argued at `Theory/SetModel/CoherentWitness.lean:109`; the *pair* with `hRd` is machine-checked consistent by `ctxInvariant_prop_agrees` | n/a |
| 17 | `PropSplit` (the live parameter) | **satisfiable and non-trivial** | `exists_propSplit`, `propSplit_not_constant`, `prop_forces_false`/`prop_forces_true` (`PropSplitAudit.lean`) | n/a |
| 18 | `PropSplit.Stable` (the live parameter) | **satisfiable, and exact** | `exists_stable_propSplit`, `propSplitOf_stable_iff` (`StableAudit.lean`) | n/a |
| 19 | `Bridge.AddDeclWF` (`Verify/Bridge.lean:132`) | **false**, and `Bridge.addDeclWF` (:138) is a *proved theorem* of it — a second instance of §4a, on a shorter path than row 2's | `addDeclWF_false` (`Verify/PreludeVacuity.lean`) | **yes** |

Rows 1–5 are one bug. Rows 6, 7, 14 and 15 are independent of it, and that is the ledger's main
finding: **the failure mode is not confined to `AddInduct`.** It recurred in the abstract theory
(row 6, a hypothesis stated at the wrong environment) and three times over in the model
interface (rows 7, 14, 15). Nothing connects them.

Rows 16–18 are the *good* rows, and §5a is about where they came from.

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

The same trap exists one link earlier and shorter: `anything_of_addDeclWF_hypothesis`, from
row 19. `Bridge.AddDeclWF` is a single `def` away from `addDecl.WF` itself, so it is the more
tempting of the two to assume.

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

## 5. The diagnostic, and the discipline

### The defect signature

`Theory/SetModel/CoherentWitness.lean:109` states the general rule, and it is better than an
inventory because it predicts:

> The defect signature is a structure quantifying over a relation **parameter** that the
> relation's own constructors never constrain.

It covers all three model-side refutations and correctly *acquits* the fourth candidate:

* row 14, `LevelAssign` — `IsDefEq.bvar` places no condition on the context, so `lvl_wf` and
  `lvl_sound` could be pointed at a context holding an out-of-range universe parameter.
* row 15, `Stable.lvl_instN` — `Ctx.InstN` declares `e₀` as a parameter its `zero` constructor
  never mentions, so the field could be pointed at an arbitrary substituted term.
* row 6, `coherentOn_addConstList`'s `hocc` — stated at the *pre-block* environment, which the
  constructors of the block-building relation never tie to the post-block one.
* **acquitted:** `CtxInvariant`'s companion `hRd` — its `A` and `A'` are not free, they arrive
  with a derivation `Γ ⊢ A ≡ A' : .sort u`, and that derivation is exactly what makes the two
  demands agree (`ctxInvariant_prop_agrees`, machine-checked).

Row 4 fits the same shape one level up: `TrEnv'`'s `induct` constructor constrains its premise
with `AddInduct`, which no constructor of anything can satisfy.

**So the check to run when writing a structure with several fields over a shared parameter:**
for each field, ask what pins the parameter. If nothing does, two fields can be pointed at
inconsistent instances and the structure is empty.

### Three checks, in order of cost

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

## 5a. This is already done well in one place — copy it

`Theory/SetModel/` is the best-audited directory in the tree, and every practice §5 asks for was
invented there. It carries **three files whose entire purpose is this audit**:

| file | what it establishes |
| --- | --- |
| `LevelAssignUnsat.lean` | the two refutations (rows 14, 15), each with the *repair* stated and the guard's load-bearing role documented at the field |
| `PropSplitAudit.lean` | satisfiability (`exists_propSplit`) **and** non-triviality of the replacement (`propSplit_not_constant`, plus `prop_forces_false` / `prop_forces_true` — a forced-`False` case and a forced-`True` case, which is non-triviality in both directions) |
| `StableAudit.lean` | satisfiability of the guarded `Stable` (`exists_stable_propSplit`) and an **exact** characterisation (`propSplitOf_stable_iff`), plus the bridge `toPropSplit_stable` from the old parameter |

Note what `no_stable`'s repair did: the `env.HasType nv Γ₀ e₀ A₀` guard now sits in
`PropSplit.Stable`'s `prop_instN` field with a docstring that says *why* it is load-bearing and
names the lemma that would fail without it. That is the pattern — **the refutation lives next to
the guard it justifies**, so nobody removes the guard as redundant.

`CnstRecursion.lean`'s residual bounds (rows 10–11) and `SemanticRouteClosed.lean`'s dead routes
(rows 8–9) are the same discipline applied outward.

## 6. Unmeasured — the to-do

Load-bearing statements whose hypotheses have **not** been checked for joint satisfiability.

The gap is **not** uniform, and an earlier draft of this section implied otherwise, which was
unfair and would have misdirected effort. `Theory/SetModel/` is audited to the standard of §5a.
What is unaudited is `Verify/` and `Theory/Typing/` — and note that rows 1–5, all in `Verify/`,
were found the moment anyone looked.

- ~~`Bridge.AddDeclWF`~~ — **now measured**, see row 19.
- The `TrProj` family — `TrProj.weak'_inv` (29 users), `TrProj.uniq` (93). These have open
  `sorry`s, so they are counted; what is unmeasured is whether their *hypotheses* are
  satisfiable at a structure the checker actually reaches, given row 13.
- `inferProj.WF` (0 users), `isDefEqUnitLike.WF` (1), `tryEtaStructCore.WF` (2) — the three
  checker `.WF` holes. Row 13 says the functions never fire today, so these three are
  vacuity-adjacent by construction: they will only acquire content after the flip.
- `docs/soundness-ledger.md`'s "Full ingredient list". Row 6 was found in it, so at least one
  entry marked available was not satisfiability-checked. Its three entries marked *hypothesis*
  — `AgreeInst` entanglement, `Stable`, `CtxInvariant` — are in fact all covered (rows 16–18 and
  §5a), and its `LevelAssign` rows are stale by rows 7/14. **The file needs re-marking against
  this ledger**, and the remaining unchecked entries identified rather than assumed.
- `Theory/Typing/` step lemmas. No file in that directory does what `PropSplitAudit.lean` does.
  Worth a single audit file on the model of §5a rather than case-by-case doubt.

### The four uncounted obligations that block the inductive route

Found by reading for the fourth blindness above rather than by running anything. **None of these
is a decision; all four are ordinary open theorems that the census reads as 0.** They are what
stands between the tree and a nested-capable `AddInduct`, i.e. between here and the version of
the flip that would actually unblock `kernel_sound`:

1. `hctors` — a *declared* constructor's **restored** stored type is a type in the environment
   carrying the step's type constants.
2. `hrecs` — each **renamed** recursor's **restored** type is a type in the environment carrying
   those and the constructors.
3. `hrules` — each **restored** ι-rule is a well-formed definitional equation there.

   All three are hypotheses of `VEnv.addInductR_ordered'`, to be discharged from
   `OwnId` + `Faithful` + `D.WF env`. They are known **satisfiable**: `nfnAux_addInductR_ordered`
   (`Theory/Typing/ConstSubstNested.lean:1235`) supplies all three in a non-trivial instance, and
   `addInductR_ordered_nil` shows that at the identity restoration they collapse to what
   `addInduct'` already discharges. So this is a genuine open proof, not a vacuity.

4. ~~The `induct` arm of `VEnv.WF'.keys`.~~ **Already done — `Theory/Inductive/NestedKeys.lean`.**
   And done better than "a different argument": the *invariant* is false, not just the proof.
   `KeyMajorUnique` — a rule is determined by the head of its major premise — fails in any
   environment holding a nested block, because the companion's restored ι-rule and the real
   block's own ι-rule share a major (`[NFn.rec_1, PFn.mk]` against `[PFn.rec, PFn.mk]`;
   `nfn_keyMajorUnique_false`). The replacement `VEnv.KeyUnique` (whole key determines the rule)
   is **preserved** by a nested step (`keysR_induct`), is *not* refuted by the same witness
   (`nfn_keys_ne`), and the sole consumer is re-proved from it
   (`Pat.iota_rule_uniq_keyUnique`). `nfn_keys_summary` packages all of it with no hypotheses.

   What is left is **plumbing in two files**: swap `KeyMajorUnique` for `KeyUnique` in
   `DeltaUnique.lean`'s `WF'.keys` chain, and re-point `PatternRules.lean`'s `Pat.iota_data_uniq`
   at `Pat.iota_rule_uniq_keyUnique` (a hypothesis reshuffle — the two `types[j]? = some T`
   hypotheses it needs are already at the call site).

**A process note, from getting item 4 wrong.** I read `NestedOrdered.lean:170`'s docstring —
"it is the second of the two obligations that the `inductNested` rule waits on" — took it at face
value, and wrote a fresh refutation of `KeyMajorUnique` at the `NTree`/`List.cons` witness before
grepping. `Theory/Inductive/NestedKeys.lean` had already refuted it at `NFn`/`PFn`, stated the
replacement, proved the nested arm, and re-proved the consumer. The duplicate was deleted.
`dup-names.lean` could never have caught it: the names differed, only the *result* was the same.
**The rule that would have: grep for the invariant's name across the tree before proving anything
about it.** And note the direction of the drift — the stale docstring overstated what was open,
which is the direction that wastes work rather than the direction that hides it.

**This corrects a framing carried in `docs/critical-path.md` and in §2 above.** The `AddInduct`
flip was described as the thing standing between the tree and the main theorem, and therefore as
a decision. Half of that is wrong. The *non-nested* flip is available today and is a decision
(it costs census 14 → 17 and leaves nested blocks vacuous). The *nested* flip — the only one that
unblocks `kernel_sound`, and the one CLAUDE.md's "nested declarations are a primary target"
requires — is blocked on the four items above, and no decision makes them go away.

## 7. Related files

- `docs/critical-path.md` — what stands between here and `kernel_sound`, with Corrections 3
  and 4 recording rows 1–4.
- `docs/frozen-edit-requests.md` — the proposals touching frozen files, none made. Its closing
  section notes that the flip is *not* one.
- `docs/soundness-ledger.md` — the abstract-side inventory; row 6 is its correction.
- `scripts/empty-inductives.lean` — the instrument for §1; wired into `scripts/status-report.sh`.
- `Theory/SetModel/LevelAssignUnsat.lean`, `PropSplitAudit.lean`, `CoherentWitness.lean`,
  `StableAudit.lean` — the audit apparatus of §5a, and the source of the defect signature.
  Read these before writing a new one.
