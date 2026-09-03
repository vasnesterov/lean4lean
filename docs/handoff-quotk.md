# Handoff: the `keta` case of `ParRedK.constApp_inv` — anti-vacuity check, 2026-09-03

Marks: **[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a run whose output is reproduced here; **[read]** = read off source;
**[analysis]** = neither, and flagged as such.

The task: `Theory/Typing/DescendConstSpineK.lean`'s `ParRedK.constApp_inv` — the critical-path
`ConstSpine` lemma ported from `ParRed`'s eight constructors to `ParRedK`'s nine — discharges its
ninth (`keta`) case, and that discharge had never been exercised. `propLoop_no_etaK` records the
case as vacuous at `propLoopParams`, and its docstring generalises that to all of `Theory/`,
naming `Verify/QuotAppParams.lean`'s `quotParams` as the first instance that could test it. The
previous stream on this target crashed before running the check.

---

## 0. Headline: the check runs, it passes, and the reason it "needed `Verify/`" was false

1. **`quotParams`' pattern table does admit a `keta` step**, and the step fires: two concrete
   `EtaK` inhabitants at the canonical `Quot.lift`/`Quot.mk` rule table
   (`quot_etaK_here`, `quot_etaK_under`). **[machine-checked]**
2. **The `keta` branch of `constApp_inv` can never "fire" in the returns-a-witness sense — at
   any instance, ever.** That is not an absence claim, it is `EtaK.constApp_free` turned around
   (`keta_branch_unreachable`): `PatFreeHead c` and `EtaK Γ ((.const c ls).mkApp as) e'` are
   jointly contradictory for every `Params`. Anyone hunting for such an instance is hunting for a
   contradiction. **[machine-checked, hole-free]**
3. **The measurement that *is* available — and is the one worth having — is that the hypothesis is
   load-bearing in the `keta` case specifically.** It is: at both instances a genuine `EtaK` step
   fires at a genuine constant spine, and deleting `PatFreeHead` makes `constApp_inv` **false
   through the ninth constructor alone** (`appParams_keta_refutes_unhypothesised`,
   `quot_keta_needs_hyp`). Before this round the same control existed only for the `extra`
   constructor (`propLoop_constApp_inv_needs_hyp`). **[machine-checked]**
4. **The premise that this needed a `Verify/`-side file is wrong**, and worse: *the tree already
   contained the witness two days before it claimed not to*. §2.

So the answer is neither the brief's outcome 2 nor its outcome 3 as posed: the case **is**
exercised, hole-free, inside `Theory/`; the residual "never fires" reading is a **theorem**, not
a gap; and the honest limit is a different one — §4.

---

## 1. Answers to the four questions as asked

| # | question | answer |
| --- | --- | --- |
| 1 | find `quotParams`; does its table admit a `keta` step? | `Lean4Lean/Verify/QuotAppParams.lean:123` **[read]**. **Yes** — it registers `quotPat = SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3` (`quotParams_pat_app`), `EtaK.matches_head`'s precondition, and the step is exhibited **[machine-checked]** |
| 2 | exhibit a firing instance | Done twice, in the *load-bearing* sense (reading 3 above): `appParams_keta_refutes_unhypothesised` (hole-free, `Theory/`), `quot_keta_needs_hyp` (canonical table, `PiInv`-tainted). In the *returns-a-witness* sense it is impossible and that is a theorem (reading 2) |
| 3 | if no, prove it vacuous and name the first instance that would test it | Both delivered anyway: `keta_branch_unreachable` is the vacuity proof, valid at **every** instance and not just the ones in the tree; and the "first instance" answer in the tree is **wrong** — §2 |
| 4 | is the branch exercised anywhere in the repository today? | **Yes, as of this round**, at two instances, one of them hole-free. **Before this round: no** — measured, §3.3 |

---

## 2. Where the tree — and the brief relaying it — is wrong

**The claim.** `Theory/Typing/DescendConstSpineK.lean`'s `propLoop_no_etaK` docstring, repeated in
`docs/handoff-descend.md` §3.1 and §6 item 1, and relayed to me:

> every `Params` instance in `Theory/` has a δ-only table — `refNoPat`, `cycNoPat`, and
> `propLoopParams`' explicit table … the first instance that would test it is
> `Verify/QuotAppParams.lean`'s `quotParams`, which `Theory/` may not import

**The theorem `propLoop_no_etaK` is true.** It is a statement at `propLoopParams` alone. Its
**docstring is false**, twice over:

1. The enumeration omits a fourth `Theory/` instance: `Theory/Typing/PatAppParams.lean:221`'s
   **`appParams`**, which registers **two `.app` patterns** (`appParams_pat_app`,
   `appParams_pat_app2`) over the `VEnv.WF` environment `cycEnv`, and carries **no holes** — its
   own header's first line is "`appParams`: the first `Params` instance that registers `.app`
   patterns". **[read, definition site]**
2. `Theory/Typing/KEtaDiamond.lean:276` has carried a concrete, hole-free `EtaK` inhabitant at
   that instance — `appParams_etaK_under : EtaK [] (.const `C []) (.lam (.const `P []) cycG2)` —
   since commit `3c7ded0`, **2026-09-01**. `DescendConstSpineK.lean` landed in `2cf1898`,
   **2026-09-03**. `KEta.lean:881`'s own docstring points at it by name. **[measured,
   `git log --diff-filter=A` on both files]**

**So the check was three lines away from `Theory/` for two days.**
`appParams_keta_refutes_unhypothesised_pre` is that derivation, written out: the pre-existing
witness's subject `.const `C []` *is* the spine `(.const `C []).mkApp []`, its reduct is a `.lam`,
and `VExpr.constApp_ne_lam` — already in `PatKHead.lean`, i.e. already in
`DescendConstSpineK.lean`'s own import cone — closes it. **[machine-checked, hole-free]**

**Why this matters beyond bookkeeping.** §6 item 1 of `DescendConstSpineK.lean` and §6 item 1 of
`docs/handoff-descend.md` both make "move `PatFreeHead` down into `Theory/`" the prerequisite for
running this check, and rank it "the cheapest thing on this list". The move has since happened
(`PatKHead.lean`) — and the check *still* was not run, because the docstring said the instance
did not exist. A false negative suppressed work that would have succeeded: that is
`docs/vacuity-ledger.md` §0's **kind 4** overstatement, in the document that catalogues it.

**Also wrong, and mine:** my own first draft of `QuotKAppEta.lean` called its `EtaK` witnesses
"the first concrete `EtaK` inhabitants anywhere in this repository". That was kind-4 again, caught
only by running a compiled-environment census (§3.3) rather than trusting the grep that had
produced it. The docstrings now credit `KEtaDiamond.lean` and say what my witnesses add instead.

**Three further corrections, smaller:**

* `DescendConstSpineK.lean`'s docstring §"Layering: the copies are gone" is accurate, but
  `docs/handoff-descend.md` §2.5 still describes the six marked copies as present. They are gone;
  `PatKHead.lean` holds the originals. **[read, both]**
* `docs/handoff-descend.md` §3.1's bullet "its `keta` case's **content** is untested" is now false
  as a statement about the repository, and was already false as a statement about what was
  *reachable*.
* This round's brief inherited all of the above verbatim. Every claim in it about `Theory/` having
  no `.app` table is wrong; its instruction "do not construct an artificial `Params` table just to
  make the case fire" turned out to be the *right* warning aimed at the wrong risk — see §4.

---

## 3. What was built and measured

### 3.1 Files — both created, nothing existing edited

| file | jobs | holes | axioms |
| --- | --- | --- | --- |
| `Lean4Lean/Theory/Typing/QuotKAppEta.lean` (225 lines) | **93** **[measured]** | none, in any declaration's cone | `[propext, Classical.choice, Quot.sound]` or less |
| `Lean4Lean/Verify/Typing/QuotKEta.lean` (274 lines) | **1286** **[measured]** | the instance's two, no new ones | see §3.2 |

Both were created by me; no pre-existing file was edited, and no frozen file
(`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) was opened, edited or
`touch`ed.

**Why two files, and which is which.** The brief allowed a `Theory/Typing/QuotK*` file *or* a
`Verify/Typing/QuotK*` file. Both were needed and they say different things:

* **`Theory/Typing/QuotKAppEta.lean`** — the check at `appParams`, **hole-free**, no `Verify/`
  import. Its instance is legitimate (all ten `Params` fields proved, `cycEnv_wf`) but its **rule
  table is artificial**: `cycEnv` carries no defeq at all (`AppPat.extra` is discharged by
  `cycEnv_no_defeqs`) while `AppPat` claims two rules. `Params` permits this — `extra_pat`
  constrains the table only in the direction *env-rule ⇒ registered*. So this file proves the
  `keta` case is reached at *some* legitimate instance; it is **not** evidence that a real Lean
  environment reaches it, and it is labelled that way in its own docstring. (Per the brief's
  instruction: I did not construct the artificial table — it has been in the tree since
  2026-09-01 — but it *is* artificial and saying so is the point.)
* **`Verify/Typing/QuotKEta.lean`** — the same check at **`quotParams`**, the canonical table: the
  real `Quot.lift`/`Quot.mk` rule of an environment `Verify/QuotConsts.lean` shows refines a real
  `Environment`. It must live in `Verify/` because `quotParams` does and `Theory/` may not import
  it. The price is that instance's two holes.

The pair bounds the question from both sides: hole-free at an artificial table, canonical but
hole-tainted at the real one. Neither alone answers "does the real kernel reach the `keta` case".

### 3.2 Axioms and holes — stated separately, as asked **[measured, `#print axioms`, names read off each file's own `namespace` lines]**

`Theory/Typing/QuotKAppEta.lean` — **no `sorryAx` anywhere**:

```
cycG_mkApp, cycG2_mkApp, appStuck_mkApp, cycQ_headConst, cycQ2_headConst
                                              -- does not depend on any axioms
appParams_etaK_here, appParams_etaK_stuck, appParams_parRedK_keta,
appParams_not_patFreeHead, appParams_patFreeHead, appParams_parRedK_bvar,
appParams_constApp_inv_statement_holds, appParams_keta_refutes_unhypothesised,
appParams_keta_refutes_unhypothesised_pre, appParams_parRedK_pSpine,
appParams_constApp_inv_fires, appParams_no_etaK_at_patFree
                                              -- [propext, Classical.choice, Quot.sound]
```

`Classical.choice` enters through `cycEnv_wf.ordered`, exactly as `PatAppParams.lean`'s header
records for its own declarations. Forward hole cone over all ten non-`rfl` seeds: **empty**
**[measured, a private copy of `scripts/hole-cone.lean`'s walker; I did not edit that script]**.

`Verify/Typing/QuotKEta.lean`:

```
keta_branch_unreachable                       -- [propext, Quot.sound]         cone 728, holes []
quot_etaK_premises_sat                        -- [propext, Quot.sound]         cone 1065, holes []
qKRedex_eq, qKRedexT_eq, quotPat_headConst    -- no axioms
quot_keta_target_not_spine                    -- [propext]
quot_etaK_here / _under, quot_parRedK_keta, quot_not_patFreeHead, quot_patFreeHead,
quot_keta_needs_hyp, quot_parRedK_mkSpine, quot_constApp_inv_fires,
quot_no_etaK_at_patFree, quotParams_Pat_eq
      -- [propext, sorryAx, Classical.choice, Quot.sound]; cone ≈9300, holes exactly
      -- [IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]
```

**No new obligation.** Those two are `quotParams`' own holes, entering through
`paramsOfPiInv … (piInv_axiom …)`, exactly as `QuotAppParams.lean`'s header measures for its four
results.

**And the taint is syntactic, not semantic — with the argument's status flagged.** `EtaK` reads
exactly three `Params` fields, and all three are `rfl`-equal at `quotParams` to hole-free data:
`quotParams_env`, `quotParams_univs` (both pre-existing) and `quotParams_Pat_eq` (new). Every
premise `KStep.mk` and `EtaK.under` consume for both witnesses is stated instance-free and proved
`sorryAx`-free in `quot_etaK_premises_sat`. So the `EtaK` firing is real content of the canonical
rule table and `PiInv` is needed only to *package* `qEnv` as a `Params` instance. **This is an
argument, not a theorem** — a fully hole-free version needs a `Params`-free copy of
`KStep`/`EtaK`, which I did not build. Marked **[analysis]** in the file too.

### 3.3 The ABSENCE claim, against the compiled environment

*Claim:* before this round the repository contained **no** hypothesis-free `EtaK` inhabitant at
the canonical table, and exactly **two** at `appParams`.

*Instrument:* a probe over the joined cone of **17 modules** — every file in the tree whose text
mentions `EtaK` (`KEta`, `KMeasure`, `KEtaDiamond`, `DescendRestate`, `KSite7`, `KKetaRow`,
`ParRedCycle`, `DescendConstSpineK`, `ParRedMissing`, `ParRedKGraded`, `KSite7Rows`, `KSite7App`,
`ParRedPropRefute`, `KDiamondJoin`, `Verify/QuotAppParams`, plus my two) — enumerating every
constant whose **type** mentions `Lean4Lean.VEnv.EtaK` and whose type peels to an `EtaK`
conclusion through instance-implicit binders only. **[measured]**

```
declarations whose TYPE mentions EtaK: 85
hypothesis-free EtaK inhabitants: [appParams_etaK_under', appParams_etaK_here,
  quot_etaK_here, quot_etaK_under, appParams_etaK_under, appParams_etaK_stuck]
```

Two pre-existing (`appParams_etaK_under`, `appParams_etaK_under'`, `KEtaDiamond.lean`, 2026-09-01)
and four new. This is the measurement that caught my own "first inhabitant" error; the grep that
preceded it did not, because the pre-existing pair is used only inside `KEtaDiamond.lean` and its
names do not contain the string I had grepped for.

*Coverage:* the tree covered is every module that mentions `EtaK` at all; a hypothesis-free `EtaK`
inhabitant in a module that never names `EtaK` is impossible.

### 3.4 The refutation attempt I ran against my own conclusion

Per the brief, I tried to prove the case **vacuous** rather than only to find a firing instance.
That attempt **succeeded**, and its success is `keta_branch_unreachable` — the branch is
unreachable under its own hypothesis at every instance. Recognising that this is a *theorem* and
not a gap is what stopped this round from reporting "still untested" (which the brief's framing
invited) or from manufacturing a table where `hc` and `keta` coexist (which is impossible).

The complementary attempt also ran: `appParams_no_etaK_at_patFree` and `quot_no_etaK_at_patFree`
are the instance-level vacuity statements, sharper than `propLoop_no_etaK` because at both
instances `EtaK` *is* inhabited and still fires at no rule-free spine.

### 3.5 Anti-strawman

`appParams_keta_refutes_unhypothesised`'s hypothesis is `ParRedK.constApp_inv`'s statement with
`PatFreeHead` and nothing else removed. The check is
`appParams_constApp_inv_statement_holds`: the *hypothesised* statement, written in the same shape
and proved **by** `ParRedK.constApp_inv`. **[machine-checked]**

Honest qualifier, in the file too: the `extra` constructor also refutes the hypothesis-free
statement at `appParams`, and `propLoop_constApp_inv_needs_hyp` already refutes it that way
elsewhere. The content here is that the **ninth** constructor independently needs the hypothesis —
a repair that guarded only `extra` would not save the lemma.

### 3.6 Which reduct fails, and why two witnesses

| witness | subject | reduct | how the conclusion fails |
| --- | --- | --- | --- |
| `KEtaDiamond.appParams_etaK_under` (pre-existing) | `(.const `C []).mkApp []` | `.lam (.const `P []) cycG2` | **shape**: `VExpr.constApp_ne_lam` |
| `appParams_etaK_stuck` (new) | `(.const `C []).mkApp [.bvar 0]` | `cycG2 = (.const `C []).mkApp [.const `D2 []]` | **argument-wise**, at the same head *and arity*: the `Forall₂` needs `ParRedK appCtx (.bvar 0) (.const `D2 [])`, and a variable reduces only to itself (`appParams_parRedK_bvar`, whose `keta` case is `EtaK.not_bvar`) |
| `quot_etaK_here` (new, canonical) | six-argument `Quot.lift` spine | `g x` | **shape**: reduct's spine head is the variable `g` |

The second row is the one worth keeping: a guard that only excluded shape changes would still be
unsound, and only that witness shows it.

---

## 4. The honest limit — a different one from the one I was sent to check

What is **not** established: that a **real Lean environment** puts a `keta` step at a constant
spine. The two instances split the evidence and neither closes it:

* `appParams` is hole-free but its rule table is not any environment's (`cycEnv` has no defeqs);
* `quotParams` *is* the canonical table, but stating anything at it costs
  `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`.

**[analysis]** The gap closes exactly when `PiInv` does, and not before: `PatAppParams.lean`'s
header argues (also as analysis, and flags it) that `pat_wf` at any pattern with `.var` positions —
i.e. every ι- and quot-rule a `VEnv.WF` environment can actually carry — needs `HasArgs.of_mkApp`,
hence `PiInv`. If that route argument is right, **no** hole-free instance over a real rule table
exists today, and `appParams`' artificiality is forced rather than lazy. I did not verify it and it
should be treated as a conjecture; it is the thing to check before anyone reports the `keta` case
as "exercised at a real environment".

---

## 5. Build state at hand-off, including two things that are not mine

* `lake build Lean4Lean.Theory.Typing.QuotKAppEta` — green, **93 jobs**. **[measured]**
* `lake build Lean4Lean.Verify.Typing.QuotKEta` — green, **1286 jobs**. **[measured]**
* Full `lake build` — **red, at `Lean4Lean/Theory/Typing/SpineVar.lean:654/655/663/770`**, a
  concurrent stream's file with in-flight edits. Neither of my modules imports it. **[measured]**
* `scripts/sorry-census-all.lean`: on disk **405**, default-target population **381**, built
  **380**, **not built 1** (`Lean4Lean.Theory.Typing.SpineVar`, the same stream), holes **13**
  (pass A 13 / pass B 0) — **unchanged**. Both my modules are in the population and in the
  **ORPHAN** list (28), which is the ownership rule's intended consequence. **[measured]**
* `scripts/dup-names.lean`: "no duplicate `Lean4Lean` declarations across the joined cone" — but
  its import list does **not** include my modules, so that run says nothing about them. The
  substitute check is a structural scan of all 35 names I introduce (verified against the compiled environment: 17 + 18 user declarations, plus 3 auto-generated `.match_*`) against every `theorem`/`def`/
  `abbrev` in the tree: **no clash**. **[measured]**
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — **empty**. **[measured]**

**Two artifact incidents, recorded because the brief predicted them and both happened.**

1. Mid-session a `lake env lean` on my file failed with *"object file … `Theory/Typing/Lemmas.olean`
   of module `Lean4Lean.Theory.Typing.Lemmas` does not exist"* while `lake build` had been green
   minutes earlier. A rebuild fixed it and no conclusion was drawn from a stale artifact.
2. One full-`lake build` run failed with *"no such file or directory (error code: 4294967294)"* on
   `Verify/Typing/ProjGenLiftWitness` and `Verify/Typing/ProjGenInst`; an immediate re-run was
   clean. Treat single-run "no such file" failures in this repo as races with a concurrent stream,
   not as breakage.

---

## 6. A row for `docs/vacuity-ledger.md` §0 — the deliverable, not written into that file

I own no existing file this round, so the row is stated here for whoever merges. It should replace
any row that records the `keta` case as untested.

> **`ParRedK.constApp_inv`'s `keta` case** — *graded, and the grading is three-valued.*
> (a) *Returns-a-witness reachability:* **provably empty at every `Params` instance**
> (`keta_branch_unreachable`, `Verify/Typing/QuotKEta.lean`, `[propext, Quot.sound]`, cone 728,
> holes []). Not a gap; do not file it as one.
> (b) *Hypothesis load-bearing in this case:* **yes, hole-free**
> (`appParams_keta_refutes_unhypothesised`, `Theory/Typing/QuotKAppEta.lean`) and at the canonical
> table (`quot_keta_needs_hyp`, `PiInv`-tainted).
> (c) *Reached at a real environment's rule table:* **open**, and open exactly as far as `PiInv`
> is (§4). Anything stronger is a claim.
> Prior grade "vacuous at every `Theory/` instance; first testable at `quotParams`" was **false
> when written** — `KEtaDiamond.lean:276` (2026-09-01) predates
> `DescendConstSpineK.lean` (2026-09-03) and refutes it in three lines
> (`appParams_keta_refutes_unhypothesised_pre`).

---

## 7. What to pick up first

1. **Fix the two docstrings that caused this, before anything else.** `propLoop_no_etaK`'s
   docstring in `Theory/Typing/DescendConstSpineK.lean` and §3.1/§6.1 of
   `docs/handoff-descend.md`. Both are one-paragraph edits and both currently tell a reader that a
   check which *is* available from `Theory/` is unreachable. I did not make them: I own neither
   file this round. **This is the highest-value follow-up in this handoff and it is not a proof
   task.**
2. **Decide whether `appParams` counts as evidence, in writing.** Six files now state results "at
   the first `.app` instance", and `appParams`' rule table corresponds to no environment rule.
   Either the ledger records that qualifier once, centrally, or every consumer re-derives it —
   and one of them will forget. `QuotKAppEta.lean`'s docstring is the current best statement of
   it.
3. **Do not** spend a session looking for an instance where the `keta` branch returns a witness.
   `keta_branch_unreachable` says there is none, at any instance, and the search is a search for a
   contradiction.
4. The real obstruction on this route is unchanged and untouched by this round:
   `ParRed.triangle`'s analogue over `ParRedK` (`ParRedMissing.lean` §3), and the two ambient
   injectivity holes — which are also what stands between §4's open item and closing it.

## 8. Files

* `Lean4Lean/Theory/Typing/QuotKAppEta.lean` — **new**, 225 lines, no `sorry`, 93 jobs, 17
  declarations. Named `QuotK*` only because this round's ownership rule required that prefix;
  nothing in it concerns the quotient rule.
* `Lean4Lean/Verify/Typing/QuotKEta.lean` — **new**, 274 lines, no `sorry`, 18 declarations, 1286 jobs.
* `docs/handoff-quotk.md` — this file.
* Nothing else changed. No frozen file was read for edit, opened for edit, or touched. No
  state-changing `git` command was run, no `lake update`, and nothing left this repository.
