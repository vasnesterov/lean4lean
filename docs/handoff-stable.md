# Handoff: `PropSplit.Stable` at the prelude

Session of 2026-09-03.  Brief: "discharge `L.Stable` for the prelude, or price its removal",
with four outcomes ranked 1 (supply `L.Stable` at the consumer's `L`) to 4 (a measurement showing
which is cheapest, or that one is impossible).

Owned file: `Lean4Lean/Theory/SetModel/StablePrelude.lean` (new, 542 lines, 25 declarations,
`lake env lean` 3.0 s, 0 `sorry`).  `EqIotaRule.lean` / `IffIotaRule.lean` were **not** edited;
§3 below is the diff for the orchestrator.  No git operation, no `lake update`, nothing sent
anywhere.

---

## 0. The answer, plainly

**Outcome 1 as literally stated is equivalent to Input 2 of the main theorem, and therefore not
achievable here** — that is a theorem, not a failure report:

```
propSplitUp_stable_iff :
  (propSplitUp env nv henv hU hT).Stable ↔ env.InstDescendUp nv
```

`UpperBound.OracleInput` (`SetModel/UpperBound.lean:98-101`) fixes the consumer's split to be
exactly `propSplitUp env 0 henv hU hT`, and `UpperBound.InstDescendInput` is
`∀ env, env.LeanWF → env.InstDescendUp 0`.  So "prove `L.Stable` at the `L` the prelude consumer
uses" *is* Input 2.  No cleverer proof against that split exists; the `iff` closes the route.

**But outcome 1's practical goal — both `inductOracleOK_*` results becoming `hle`-only — is
reachable for sixteen lines of edit, and I have compiled it.**  The reason is a factoring the
brief's ~270-line estimate did not have:

| half of `Stable` | fields | sole consumer | status at `propSplitUp` |
|---|---|---|---|
| `StableLift` | `prop_liftN`, `proof_liftN` | `InterpSubst.interp_liftN` (uses them at lines 224, 239, 261 — nothing else) | **FREE from `env.Ordered`** |
| `StableInst` | `prop_instN`, `proof_instN` | `InterpSubst.interp_inst` (lines 399, 419, 446) | `= env.InstDescendUp nv`, open |

`InterpSound.interp_closed_ctx` is a corollary of `interp_liftN` alone, and it is the **only**
thing either ι-rule file takes `hS` for (`EqIotaRule.lean:505`, `IffIotaRule.lean:814`; the other
ten occurrences of `hS` in the two files are pure threading — verified by
`grep -n 'hS' <file>`).  So both ι-rule results depend on `StableLift` and not on `StableInst`,
and `StableLift` is free at the consumer's split.

Grade: **outcome 2, executed and verified, delivering outcome 1's payoff**, plus outcome 4 in the
form of `propSplitUp_stable_iff` (outcome 1's literal form is *impossible without Input 2*).

---

## 1. Proved (machine-checked; `#print axioms` output quoted from the file's §8 census)

Namespaces read off the file's own `namespace` lines: `Lean4Lean.SetModel` and
`Lean4Lean.SetModel.StablePrelude`.  Directory is not namespace in this repo.

| statement | § | axioms |
|---|---|---|
| `PropSplit.StableLift`, `PropSplit.StableInst` (structures) | 1 | — |
| `PropSplit.Stable.stableLift`, `.stableInst`, `PropSplit.stable_iff_lift_and_inst` | 1 | `[propext]` |
| **`propSplitUp_stableLift`** — `StableLift` for the consumer's split from `env.Ordered` alone | 3 | `[propext, Classical.choice, Quot.sound]` |
| `exists_stableLift_propSplit`, `exists_stableLift_propSplit_of_agree` | 3 | same |
| `propSplitUp_stableInst_iff` — `StableInst ↔ env.InstDescendUp nv` | 4 | same |
| **`propSplitUp_stable_iff`** — `Stable ↔ env.InstDescendUp nv` | 4 | same |
| `interp_liftN_lift`, `interp_closed_ctx_lift` — `InterpSubst.interp_liftN` / `InterpSound.interp_closed_ctx` under `StableLift` | 5 | same |
| `onCtx_levelWF`, `not_isType_sortParam_of_onCtx`, `not_onCtx_of_lift'_sortParam`, `not_isPropUpOn_sortParam_target` | 6 | `[propext, Quot.sound]` |
| **`not_stableLift_propSplitUpOn`, `not_stable_propSplitUpOn`** — the *guarded* split is **never** `StableLift`, at every env | 6 | `[propext, Classical.choice, Quot.sound]` |
| `not_stableLift_propSplitUpOnPreludeEnv` (corollary at `preludeEnv`) | 6 | `[propext, sorryAx, …]` — **inherited, see §5** |
| `junkSplitOf` + `junkSplitOf_not_stableLift` / `_not_stable` / `stableLift_is_a_real_restriction` / two positive controls | 7 | `[propext, Classical.choice, Quot.sound]` |

`interp_liftN_lift` is `InterpSubst.interp_liftN`'s proof **verbatim** — the only change is the
hypothesis' type.  That is deliberate: `StableLift`'s fields were given `Stable`'s field names so
the copy is byte-identical below the signature.  Its value is not new mathematics, it is the
*measurement* that the two `inst` fields are unused there.  If `InterpSubst.lean` is ever edited
to take `StableLift` directly, delete §5 rather than keeping a parallel copy.

## 2. The two side conditions: **both are open assumptions, neither is discharged at `preludeEnv`**

This was the brief's key question, and the answer is the one it warned about.

* **`VEnv.InstDescendUp`** — definition site `Lean4Lean/Theory/SetModel/PropSplitUp.lean:406`.
  Tree searched: `grep -rn 'InstDescendUp' --include=*.lean .` over the **whole repository**
  (`Lean4Lean/`, `Main.lean`, the test tree).  Every occurrence is a hypothesis, a docstring, or
  one of exactly two producers:
  `PropSplitUp.instDescendUp_of_propDescend` (from `PropDescend`, itself open) and
  `PreludeWitness.lean:418  instDescend_of_input (h : InstDescendInput) : preludeEnv.InstDescendUp 0`
  — where `InstDescendInput` is `UpperBound.lean:91`, **Input 2 of the main theorem, an
  assumption**.  Only the `.bvar k` case is closed (`InstDescendBvar` §4, `StableGuarded` §6).
* **`VEnv.PropDescend`** — definition site `Lean4Lean/Theory/SetModel/StableAudit.lean` (structure
  `VEnv.PropDescend`).  Same tree.  **No producer of any kind**: it occurs only as a hypothesis
  and in prose.  Its two `lift` fields are strengthening-shaped and `Strengthen.lean` records the
  general form as `sorryAx`-tainted through Π-injectivity.

So chaining `L.Stable` to either of these and stopping would be a measurement, not progress, and
`StableAudit.exists_stable_propSplit` / `PropSplitUp.exists_stable_propSplitUp` are both such
chains.  What §3 below does instead is remove the need for the chain at the two ι-rule blocks.

## 3. The exact edit, for the orchestrator — **compiled, not read off**

Two files, sixteen lines.  Both outside this stream's ownership; I did not touch them.

```
# in BOTH Lean4Lean/Theory/SetModel/EqIotaRule.lean and .../IffIotaRule.lean
1.  after line 1, add:   import Lean4Lean.Theory.SetModel.StablePrelude
2.  s/(hS : L\.Stable)/(hS : L.StableLift)/g        # 6 hits per file
3.  s/interp_closed_ctx M L hS/interp_closed_ctx_lift M L hS/g   # 1 hit per file
```

Hit lines: `EqIotaRule.lean` 454, 505, 735, 882, 901, 913, 1017; `IffIotaRule.lean` 734, 814,
1187, 1385, 1402, 1413, 1497.

**Verification actually run** (scratch copies at `/tmp`, never in the repo):

```
$ sed -e '1a import Lean4Lean.Theory.SetModel.StablePrelude' \
      -e 's/(hS : L\.Stable)/(hS : L.StableLift)/g' \
      -e 's/interp_closed_ctx M L hS/interp_closed_ctx_lift M L hS/g' \
      Lean4Lean/Theory/SetModel/EqIotaRule.lean > /tmp/EqIotaRule_SL.lean
$ lake env lean /tmp/EqIotaRule_SL.lean       # no error, no warning
$ …same for IffIotaRule.lean                  # no error, no warning
```

and, appended to each scratch copy, the payoff:

```lean
theorem inductOracleOK_Eq_at_propSplitUp {envF : VEnv} {nv : ℕ} (henv : envF.Ordered)
    (hU : envF.PropUniq nv) (hT : envF.PropTypeAgree nv) (κ : ℕ → V) (ls : List ℕ)
    (hle : eqEnv ≤ envF) :
    InductOracleOK (propSplitUp envF nv henv hU hT) κ ls
      (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst eqIndDecl :=
  inductOracleOK_Eq _ κ ls (propSplitUp_stableLift henv hU hT) hle
-- 'Lean4Lean.SetModel.EqIotaAudit.inductOracleOK_Eq_at_propSplitUp' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

and the `Iff` twin, same axioms.  **Both `hle`-only, `sorryAx`-free.**  `hU`/`hT` are *data*
arguments of `propSplitUp` and `UpperBound.OracleInput` already takes them, so this adds **no**
obligation at the consumer.

**Nothing downstream breaks.**  `grep -rn` over the whole repository for
`inductOracleOK_Eq|inductOracleOK_Iff|inductOracleOK_rules_Eq|inductOracleOK_rules_Iff|defEqOK_eqRule|defEqOK_iffRule|interp_iotaRhsBody_val|interp_sides_eq_of_ne`
outside those two files finds **no call sites at all** — only the two import comments in
`Theory/Equiconsistency.lean:16-17` and one prose mention at
`SetModel/InductOracleAudit.lean:321` (which says `inductOracleOK_Eq` carries `L.Stable`; after
the edit that line becomes wrong and should be amended to `L.StableLift`).

After the edit, the two payoff corollaries above should be added somewhere — the natural home is
`EqIotaRule.lean` / `IffIotaRule.lean` themselves, since `StablePrelude.lean` sits *below* them in
the import graph and cannot state them.

## 4. What this does NOT buy — read before quoting §3

1. **`InstDescendInput` (Input 2) does not leave the main theorem.**  `InterpSubst.interp_inst`
   needs the two `inst` fields, hence `ModelFits` does, hence
   `UpperBound.consistent_of_inputs` does through `modelFits_of_propSplitUp_inputs … hI …`.
   What leaves is Input 2's appearance in the *three `.induct` steps of the prelude*, which is
   exactly what `handoff-setmodel.md` §24.9 item 1 asks for and no more.
2. **Nothing here is a claim at `preludeEnv` unconditionally.**  `propSplitUp` needs the
   *unguarded* `PropTypeAgree env 0` as **data** — Input 1, open at `preludeEnv`.
3. **Outcome 3 is refuted along its cheapest route.**  `∃ L : PropSplit preludeEnv 0, L.Stable`
   with side conditions *discharged* would want the split whose data is free there,
   `InstDescendBvar.propSplitUpOnPreludeEnv`.  §6 proves `¬ (propSplitUpOn env 0 henv hU hT).StableLift`
   at **every** environment and every choice of the two guarded inputs, hence
   `¬ … .Stable`.  So that route is closed, not merely unproved.  (This does not say *no*
   `PropSplit preludeEnv 0` is `StableLift` — `propSplitUp` is one, and its existence is Input 1.)

## 5. Two corrections to the tree's own records

1. **`PropAgreeWall.preludeEnv_propUniqOnCtx` and `preludeEnv_propTypeAgreeOnCtx` print
   `sorryAx`.**  Measured:
   ```
   'Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propTypeAgreeOnCtx' depends on axioms:
     [propext, sorryAx, Classical.choice, Quot.sound]
   'Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propUniqOnCtx'      … same
   'Lean4Lean.SetModel.InstDescendBvar.propSplitUpOnPreludeEnv'      … same
   ```
   They are `VEnv.WF.propTypeAgreeOn` / `WF.propUniqOn` applied to `preludeEnv_WF`, and those two
   are the `sorryAx` carriers (`SetModel/NotProofNoModel.lean`; `Verify/QuotAppParams.lean:372`
   already names them as such).  So `InstDescendBvar` §8b's description of
   `propSplitUpOnPreludeEnv` as coming "from the two guarded imports, **both of which are theorems
   there**" is true only of `sorryAx`-tainted theorems, and `StableGuarded` §5's "the class the
   guarded fields live on is inhabited where the recursion goes" inherits that.  Route B
   (`PropAgreeWall.preludeEnv_propTypeAgreeOnCtx_of_stratifiedN`) is the `sorryAx`-free version and
   is conditional on `∀ n, PropTypeAgreeN 0 n` and `∀ n, PropUniqN 0 n`.
   The refutation in §6 of my file is itself `sorryAx`-free
   (`not_stableLift_propSplitUpOn`); only the `preludeEnv`-instance *corollary* inherits the taint,
   and it inherits it from the object it names, not from any reasoning.
2. `StableGuarded.preludeEnv_stableOn_liftN`'s own docstring is accurate, but it is **not** a step
   toward `Stable`: see §6 below.

## 6. Where the brief is wrong

Asked for plainly.  Four things; the first two are load-bearing.

1. **"`preludeEnv_stableOn_liftN` … may already be most of outcome 1."**  **Refuted.**  It is the
   two `lift` fields of `PropSplit.StableOn` — the **guarded** structure — not of `Stable`; and
   `PropSplit.Stable.stableOn` runs `Stable → StableOn`, the wrong direction for a consumer that
   needs `Stable`.  Worse, `StableGuarded` §4 already proves (`not_interpLiftNObligation`) that the
   guard **cannot** be threaded into `Stable` while `interp_liftN` keeps its hypotheses, so no
   amount of work on `StableOn` reaches the consumer.  The brief flagged this as a guess; the guess
   is wrong, and the route it points at is provably closed.
   What replaces it is not a guard at all: it is dropping the two `inst` fields, which the
   consumer genuinely does not use.  Nobody had looked at *which* fields `interp_closed_ctx` needs.
2. **"~270 lines across both blocks — six layers, two of them `mkForallProp`-shaped field
   spaces."**  **Measured at sixteen lines of edit** (§3), plus ~100 lines of verbatim restatement
   in a file I own.  The ~270 figure prices a *different* repair — recomputing `⟦iotaLam⟧` at the
   ι-context so `interp_closed_ctx` is never called — and that repair is unnecessary:
   `interp_closed_ctx` is fine, its *hypothesis* was too strong.  `handoff-setmodel.md` §24.9 item
   1 should be superseded, not just re-estimated: the driver it names (binder count × nests) does
   not apply to the actual fix at all.
3. **The outcome ranking is inverted.**  Outcome 1 as literally stated is Input 2
   (`propSplitUp_stable_iff`) and so cannot be delivered; outcome 2 delivers outcome 1's payoff for
   sixteen lines.  Ranking outcome 2 below outcome 1 sent me looking for a discharge that a theorem
   in this file shows does not exist.
4. **Right, and worth saying so:** the brief's insistence that "chaining `L.Stable` to
   `PropDescend`/`InstDescendUp` and stopping is outcome 4, not outcome 1" is exactly the trap here,
   and §2 above is the answer it asked for — *both* side conditions are open assumptions, and
   `PropDescend` has **no producer anywhere in the repository**.

## 7. Anti-vacuity

* **Negative control, at exactly the freeness result's hypotheses.**  `junkSplitOf env henv hU hT`
  (§7 of the file) is a complete `PropSplit env 0` — all six fields, `prop_sound` and `proof_sound`
  proved, not `sorry`ed — and `junkSplitOf_not_stableLift` refutes `StableLift` for it.
  `stableLift_is_a_real_restriction` states both sides together:
  `(∃ L, L.StableLift) ∧ (∃ L, ¬ L.StableLift)` from `Ordered ∧ PropUniq 0 ∧ PropTypeAgree 0`.  So
  §3's freeness is a genuine selection, and `Stable`/`StableLift` are not everywhere-true on
  `PropSplit`.  `sorryAx`-free, at an arbitrary environment.
  The doctoring (`IsPropAt … ∧ Γ ≠ [Sort (param 0)]`) lives only where `prop_sound` cannot look:
  `[Sort (param 0)]` is not `OnCtx`, which is why the sound fields survive and `Stable` — stated
  over raw contexts — does not.
* **Positive controls on the same object**, so the refutation is not an empty predicate:
  `junkSplitOf_isPropAt_falseProp` (`∀ p : Prop, p` is a proposition at `[]`) and
  `junkSplitOf_not_isPropAt_sort` (`Prop` is not).  Two truth values, one object.
* **Parameters quantified, not fixed.**  Everything in §§1–5 and §7 of the file is at arbitrary
  `env : VEnv` and arbitrary `nv` (§§6–7 fix `nv = 0`, forced: `Sort (param 0)` is only junk at
  `nv = 0`, and `PropSplit`'s guarded inputs are stated at `0`).  `V`, the `SetStructure`/ZF/AC
  instances, `M : ModelData V`, `L : PropSplit env nv`, `κ` and `ls` are all universally
  quantified; **no `κ` is chosen anywhere in the file** and `Above` does not occur.
* **The `iff`s are tight in both directions**, which is what stops a hypothesis being silently
  swapped for a weaker one: `stable_iff_lift_and_inst`, `propSplitUp_stableInst_iff`,
  `propSplitUp_stable_iff`.
* **What is hole-free but NOT discharged:** `env.PropTypeAgree 0` (Input 1) is still needed as
  *data* for `propSplitUp` to exist; `env.InstDescendUp 0` (Input 2) is still needed for
  `ModelFits`.  Neither is touched here.

## 8. What I tried that failed, and the step it failed at

* **Avoiding the copy of `interp_liftN`.**  I looked for a way to obtain
  `interp_closed_ctx`'s conclusion from `StableLift` without restating the 90-line recursion —
  building an auxiliary `PropSplit` with the same `IsPropAt`/`IsProofAt` and a provable `Stable`,
  so `interp` would be unchanged.  Fails at the `inst` fields: any split with the same predicates
  has the same `inst` fields, so its `Stable` is the same open statement.  There is no proof-term
  route; either the recursion is copied (what §5 does) or `InterpSubst.lean` is edited.
* **`interp_closed_ctx_lift_eq_interp_closed_ctx`**, written and compiled as an "agreement" lemma,
  then **deleted**: it is an equation between two *proofs*, so `rfl` closes it by proof
  irrelevance and it asserts nothing.  Exactly the shape `docs/vacuity-ledger.md` §0 warns about;
  it was in the file for about ten minutes.
* **`induction W` on `Ctx.Lift' l [Sort (param 0)] Γ'`** — "Invalid target: Index in target's type
  is not a variable".  Fixed by generalising the source context and carrying
  `Γ = [Sort (param 0)]` as an equation.  Routine, recorded because it is the shape every
  `Ctx.Lift'` induction in this corner will hit.
* **`not_isType_sortParam_of_onCtx trivial`** with `Γ` left implicit — the metavariable is not
  solved from `trivial : True`, so `(Γ := [])` is required.  §§23.5/24.5 of `handoff-setmodel.md`
  record the same trap for `OnCtx` at an empty tail; it recurs here for the same reason.
* **`VEnv.not_isPropUp_sort` / `VEnv.IsPropUp.of_hasType`**: the first is in `SetModel`, the second
  in `VEnv`, both in `PropSplitUp.lean`.  Guessing the namespace from the neighbour cost two
  round-trips.  Read the `namespace` lines.
* **Not attempted.**  I did not try to weaken `Stable` in `InterpSubst.lean` itself (not my file,
  and §3 shows it is unnecessary for the goal); I did not attack `InstDescendUp` or `PropDescend`;
  I did not run the full `lake build`, the guards, `sorry-census`, `dup-names`, or the Kernel
  Arena.

## 9. Measured versus read off

| claim | source | status |
|---|---|---|
| `interp_liftN` uses only the two `lift` fields; `interp_inst` only the two `inst` fields | `grep -n 'hS\.' InterpSubst.lean` → 224/239/261 vs 399/419/446 | **measured** |
| `interp_closed_ctx` is a corollary of `interp_liftN` alone | read (InterpSound.lean:674-684) then **compiled** as `interp_closed_ctx_lift` | measured |
| `hS` is used only at `interp_closed_ctx` in the two ι-rule files | `grep -n 'hS'`, 11 hits per file, 1 substantive | **measured** |
| the sixteen-line edit elaborates, and yields `hle`-only results | `lake env lean` on `/tmp` copies + payoff corollaries | **measured** |
| no downstream caller of the twelve affected declarations | `grep -rn` whole repository | **measured** (floor: a string search sees no `export` aliases or `simp` sets) |
| `InstDescendUp` / `PropDescend` are undischarged assumptions | `grep -rn` whole repository, both symbols, producers enumerated | **measured** |
| `preludeEnv_prop{Uniq,TypeAgree}OnCtx` print `sorryAx` | `#print axioms` | **measured** |
| the guarded split is never `StableLift` | **proved** (`not_stableLift_propSplitUpOn`) | measured |
| ~270 lines to remove `L.Stable` | `handoff-setmodel.md` §24.9 / the brief | **refuted**: prices a different repair |
| `preludeEnv_stableOn_liftN` is most of outcome 1 | the brief, flagged as a guess | **refuted** |

Tooling: Bash `grep -rn --include=*.lean` over the repository root, `lake env lean <file>`,
`lake build <module>` (`Lean4Lean.Theory.SetModel.StablePrelude`: 1212 jobs, success).  I used no
`lean-lsp` MCP tool this session, so I can neither confirm nor deny `handoff-setmodel.md` §24.7's
unverified claim about `lean_local_search` / `lean_references`.

## 10. What to pick up first

1. **Make the §3 edit** (human decision).  Sixteen lines, verified.  It removes Input 2 from all
   three prelude `.induct` steps — `PreludeOracle.inductOracleOK_NE` never needed it — and after
   it, `SetModel/InductOracleAudit.lean:321` should say `L.StableLift`.
2. **Then consider pushing `StableLift` upstream into `InterpSubst.lean`**, i.e. changing
   `interp_liftN`'s hypothesis from `L.Stable` to `L.StableLift` in place and deleting §5 of
   `StablePrelude.lean`.  That is a one-line signature change in a file this stream does not own;
   its blast radius is `interp_liftN`'s call sites (`InterpSound.lean:764, 775, 785` go through
   `interp_closed_ctx`, which would take `StableLift` too).  Not measured — I did not test it.
3. **Input 2 is now the whole of `Stable`'s cost**, and `propSplitUp_stableInst_iff` says so
   exactly.  Its `.bvar k` case is closed at every `k` (`InstDescendBvar` §4); the open cases are
   `.forallE` / `.app` / `.lam`, blocked on inversion at a sort — that is where the next real
   mathematics is, not in `Stable`.
4. **Do not re-price the ι-rule repair.**  §24.9 item 1's costing model (binder count × nests) is
   sound for recomputing an interpretation but is the wrong model for this obligation; the
   obligation was a hypothesis that was too strong, and hypothesis-weakening costs are measured by
   *which fields the proof touches*, not by the size of the proof.
5. **`StablePrelude.lean` is currently ORPHANED** — no module imports it, so no instrument (guard,
   `sorry`-census, axiom audit run over `Theory.Equiconsistency`) sees it.  This repo's convention
   is to import a new `SetModel/` file into `Theory/Equiconsistency.lean` with a load-bearing note;
   that file is outside this stream's ownership, so I did not.  The natural note names
   `propSplitUp_stableLift` (the freeness result), `propSplitUp_stable_iff` (the `Stable`↔Input 2
   equivalence) and `stableLift_is_a_real_restriction` (the control).  This is the same hazard
   `handoff-setmodel.md` records at `InstDescendBvar.lean` ("was orphaned — no file imported it, so
   no instrument saw it").
