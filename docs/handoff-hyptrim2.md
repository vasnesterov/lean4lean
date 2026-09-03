# Handoff: the `include`-group defect swept to zero in `Verify/` — and the previous round's *mechanism* is refuted

2026-09-03.  Files this round owns and edited: `Theory/Inductive/NestedHead.lean`,
`Theory/Typing/ConstSubstNested.lean`, `Verify/Environment/InductR.lean`,
`Verify/Inductive/NestedRestore.lean`, `Verify/Inductive/TrIndDeclNCtorOwn.lean`, plus the new
`Theory/Inductive/HypTrim2Witness.lean` and this document.  **`SetModel/IndStage.lean` was not
touched** — see §3.

## Summary

| item | status |
| --- | --- |
| the brief's claim that `include` hides `linter.unusedSectionVars` | **REFUTED** — §1 |
| `Verify/` swept (never swept before) | **done, and the class is there** — 2 instances, both fixed |
| `NestedHead.lean` — `ntree_const_staged`, `nlist_const_staged` (`h`) | **trimmed**, 4 consumer sites re-pointed |
| `ConstSubstNested.lean` — `nfnF₂_ordered` (`hE₂`) | **trimmed**, 2 consumer sites re-pointed |
| `Verify/Environment/InductR.lean` — `trIndDeclN_wit` (`hPFnMk`) | **trimmed**, 5 consumer sites re-pointed |
| `Verify/Inductive/NestedRestore.lean` — `recRenames_keys` (`h`) | **trimmed**, 1 consumer re-pointed |
| cascade: `memIndDeclNamesN_sat`, `notAddInductStagesR_sat` (`hPFnMk`) | **trimmed**, zero ripple |
| `SetModel/IndStage.lean`'s "two on `hE`" | **do not exist** — already `omit hE` since 2026-08-22 |
| anti-vacuity, strong form where available | **proved**, 7 + 6 + 3 witness declarations |
| can the linter be "enabled" going forward? | **it already is** — the round-close check is in §7 |

Full `lake build`: **green at 1579 jobs** after all of this round's edits.  A later full build
failed — in **two untracked files belonging to concurrent streams and in nothing else**:
`Theory/Typing/ShapeIndepStep.lean` (unsolved goals, `:141`/`:152`) and
`Verify/Inductive/ArgsTypedSupply.lean` (unknown identifiers, and
`Unknown constant Lean4Lean.NestedWit.pfnOcc_ctorTele_agree` — a `NestedWit` lemma that exists
neither in my edited files nor in `HEAD`, so it is theirs in progress, not breakage from the
`hPFnMk` trim).  `lake build` restricted to my cone plus `Lean4Lean.Verify.Guard`: **green, 1275
jobs**, all three guards printing.  Job counts observed: **1575** at session start, **1577** after
the five trims, **1579** after the witnesses (the +2 between the first two is another stream's
commits landing, not mine).  Census: **13**, hole list unchanged and identical to
the recorded one; no hole is in a file this round touched.  `#print axioms` over **all five**
touched modules, every pre-existing declaration: **byte-identical before and after** (§5).

---

## 1. Where the brief is wrong: the mechanism

The brief, and `docs/handoff-hyptrim.md` §1 which it relays, say:

> Lean *has* `linter.unusedSectionVars` for exactly this, and **an explicit `include` suppresses
> it** — it fires only for automatically included variables.  So the class is invisible in source
> and has a working detector sitting right behind it.

**This is false in both halves.**  Measured three ways:

**(a) A minimal probe.**  Three sections, same two variables `(hp : n = 0) (hq : n = n)`, proof
uses only `hq`:

| form | linter fires on `hp`? |
| --- | --- |
| `include hp hq` (bare, scope-wide) | **yes** |
| `include hp hq in theorem …` | **yes** |
| no `include` at all | n/a — `hq` is then *not in scope*: "Unknown identifier `hq`" |

The third row is the reason the claim is exactly backwards.  A `Prop`-valued section variable is
**never** automatically included in Lean 4 — it must be `include`d to be usable — so if the linter
only fired for automatic inclusion it could never fire on a hypothesis at all, and the previous
round could not have been "reported the third instance by the linter itself", which it says
happened.

**(b) The previous round's own headline instance was reported by the linter, before the fix.**
Elaborating `git show 4f6ac00^:Lean4Lean/Theory/Inductive/RestoreBridge.lean`:

```
:502  automatically included section variable(s) unused in theorem
      `Lean4Lean.VIndRestore.substC_tyApp_eq_tyAppR_map`:  hcl
:531  automatically included section variable(s) unused in theorem
      `Lean4Lean.VIndRestore.substC_tyAppR`:  hp  hnd  hown  …
```

Both were in `lake build`'s ordinary output for as long as the code stood.

**(c) `lake build` on the tree I inherited emitted 24 of these warnings**, naming every instance
the brief asked me to hunt and several it did not.

**So the defect class was never invisible.  The *warning stream* was unread.**  What misled
everyone is the message's own wording — Lean says "automatically included section variable(s)"
whatever the inclusion route was.  Reading that phrase as a scope condition rather than as
boilerplate is the entire error.

Consequences worth acting on:

* **The textual `include` scanner is unnecessary.**  Its measured precision here was 7/12 in
  `Theory` (previous round) and **2/5 in `Verify`** (this round; the three misses are the same
  `trS_tac`-reads-the-context class as `ParamRedex`'s `type_tac` five).  It is also *incomplete*:
  it sees only `include` scopes, so it missed 18 of the 24 real warnings.  Do not rebuild it.
* **`docs/handoff-hyptrim.md` §1 and `Theory/Inductive/HypTrimWitness.lean`'s module docstring are
  wrong** on this point, and the claim has already been copied into
  `Theory/Inductive/OwnRule.lean:56-57` ("invisible in the source because the section's `include`
  suppresses `linter.unusedSectionVars`") — that file is still **untracked**, i.e. a concurrent
  stream is writing the error in right now.  None of the three is mine; three one-sentence
  corrections are needed and I have not made them.

## 2. What was fixed

Every fix is `omit … in` above the docstring, or a name dropped from an `include … in` line, plus
argument deletion at call sites.  No proof body changed.

```
Theory/Inductive/NestedHead.lean:901   ntree_const_staged     omit h        4 sites re-pointed
Theory/Inductive/NestedHead.lean:908   nlist_const_staged     omit h          (2 in-file, 2 in
                                                                               ConstSubstNested)
Theory/Typing/ConstSubstNested.lean:1154  nfnF₂_ordered       drop hE₂      2 sites, both in-file
Verify/Environment/InductR.lean:858   trIndDeclN_wit         drop hPFnMk    5 sites (1 in-file,
                                                                            4 in TrIndDeclNCtorOwn)
Verify/Inductive/NestedRestore.lean:456  recRenames_keys      omit h        1 site (`h.recRenames_keys`
                                                                            → `recRenames_keys`)
Verify/Inductive/TrIndDeclNCtorOwn.lean:156  memIndDeclNamesN_sat   drop hPFnMk   cascade, 0 ripple
Verify/Inductive/TrIndDeclNCtorOwn.lean:167  notAddInductStagesR_sat drop hPFnMk  cascade, 0 ripple
```

Two of the seven are a **cascade** — they became visible only once `trIndDeclN_wit` stopped
demanding `hPFnMk`.  That is the same phenomenon the previous round hit and did not predict; it
is now twice observed and should be expected: *fix one, rebuild, read the linter again.*

`hPFnMk` is now a dead `variable` in `TrIndDeclNCtorOwn.lean:142`.  Left in place deliberately —
deleting it changes no signature and there is no linter for it.

### The one cascade I did **not** apply — this is the ripple measurement you asked for

Trimming `NestedHead`'s two staged lemmas makes `ntreeAux_WF` (`NestedHead.lean:925`) unused-`h`
too, and the linter now says so.  `h : VEnv.empty.addInduct' listDecl = some env₁` is the only
thing tying `env₁` to the `List` environment, so the trimmed form would read
`∀ {env : VEnv}, ntreeAux.WF env` — **the auxiliary nested block is well-formed in every
environment**, which is a strictly stronger and genuinely useful statement, and the same *kind* of
finding as `hp : D.params = []` last round.

I did not apply it, and the reason is **ownership, not difficulty**: `ntreeAux_WF h` has **25 call
sites in 8 files**, of which `Inductive/CtorBeta.lean` (3), `Inductive/RecTyped.lean` (2) and
`Inductive/NestedTele.lean` (2) belong to a concurrent stream, and `Inductive/TeleCongr.lean` (3),
`Inductive/NestedBuild.lean` (2) and `Inductive/RestoreOpWit.lean` (prose only) are not mine
either.  The edit is one line (`omit h in` above `NestedHead.lean:924`) plus deleting one argument
at each site.  Full list:

```
CtorBeta.lean:319,321,324,628,630,633   ConstSubstNested.lean:912,943,966,968,971,2109,2299,2300,2301
RecTyped.lean:891,917                   TeleCongr.lean:278,280,283
NestedBuild.lean:1609,2144              NestedTele.lean:4051,4260   NestedHead.lean:1020
```

**Until it is done the build carries one warning that was not there before** (24 → 20 overall, and
one of the 20 is this new one).  That is a deliberate trade: the warning is a true statement about
the code and it is how the next stream will find the route.

## 3. Where the brief is wrong: `IndStage.lean` has nothing to fix

> `Theory/SetModel/IndStage.lean` — two, on `hE`, **zero ripple**.

There is no such pair.  `IndStage.lean:144` already reads a bare `omit hE`, three lines above
`Ind_subsingleton_stage`, and `git blame` puts it in commit **a213ec1 (2026-08-22)** — before the
previous round ran.  Checked against the **compiled environment**, not the source:

```
@Ind_subsingleton_stage : … → IsInaccessible k → IsStageSignature k S → S.WF →
                          IsSubsingletonSignature S → ∀ (x i y : V), … → … → x = y
@indRec_indep_of_proof_stage : … → IsInaccessible k → IsStageSignature k S → S.WF →
                          IsSubsingletonSignature S → ∀ {i x y : V}, … → … → …
```

No `IsMinorPremise` premise in either.  `lake build` emits **zero** warnings from `IndStage.lean`.
The previous round's scanner reported them because it honoured `omit … in` but not bare `omit`;
its own §3 says the `omit … in` handling was the bug it fixed, and this is the other half of the
same bug, still present.

**Consequence for the contested-file protocol: `IndStage.lean` needed no coordination and got
none.  I did not read or write it beyond `sed -n` and `git blame`.**  Anything you find in it is
the other stream's.

## 4. `Verify/`, swept — the higher-value half

**Instrument: the linter, over the whole compiled build.**  This is a stronger population than any
scan: 1579 jobs, every module lake builds, `Foundation` included.  There is **no**
`set_option linter.unusedSectionVars false` anywhere in `Lean4Lean/` and no `leanOptions` in
`lakefile.toml`, so nothing is masked.

**Result: `Verify/` held 2 instances (now 4, with the cascade), all fixed.  After the fixes,
`lake build` emits zero `automatically included section variable` warnings from any
`Lean4Lean/Verify/**` module.**  Population for the absence claim: 3192 top-level
`theorem`/`lemma` declarations under `Lean4Lean/Verify/` (`Theory/`: 8114); definition sites
`Verify/Environment/InductR.lean` and `Verify/Inductive/NestedRestore.lean`; tree covered
`Lean4Lean/Verify/**`; compiled environment the full green build at 1579 jobs.

**Frozen files, swept read-only and not fixed** (nothing needed fixing):
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` each contain **zero** `include`
and zero `omit` lines and produce **zero** linter warnings.  Not edited, not `touch`ed.

### The 20 warnings that remain, and what they mean

Two carry a named `Prop` hypothesis; 18 are unused **instance** binders.

**(i) `Theory/Typing/StrengthenAxiom.lean:162` — `Ctx.LiftN.exists_instN_typed`, `henv : Ordered env`.
This is the highest-value one left, and it is not mine.**  The lemma is
`Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) → ∃ Γ₀ A₀, …`, declared under
`variable! (henv : Ordered env) in`, and the proof is a pure induction on the `LiftN` that never
uses orderedness.  So a purely structural strengthening lemma is gated behind an environment
well-formedness premise it does not need — the same shape as `hp : D.params = []`, which is the
class the brief says it cares about.  Ripple: **9 call sites in 5 files** —
`Verify/Typing/ProjInhab.lean:142,162,174`, `Verify/Typing/ProjWeakInvSplit.lean:188`,
`Theory/Typing/ConstVar.lean:511`, `Theory/Typing/StrengthenAxiom.lean:218,322`,
`Theory/Typing/StrengthenVerdict.lean:121,169` (the last two destructure six components, so check
whether they resolve to this lemma or a shadowing one before re-pointing).  **Pick this up first.**

**(ii) `Theory/Inductive/NestedHead.lean:925` — `ntreeAux_WF`, `h`.**  §2 above; mine, blocked on
ownership of six other files.

**(iii) The 18 instance-binder warnings**, listed because two groups are substantive rather than
cosmetic:

| where | unused instance | reading |
| --- | --- | --- |
| `Theory/SetModel/IndInterp.lean` ×9 | `[Nonempty V]`, `[⊧* 𝗭𝗙]`, `[⊧* 𝗔𝗖]` | **nine model-side lemmas do not need ZFC or AC.**  `indStep₂_eq`, `indStep_at_mono` (`:846`, `:900`) are free of **AC** specifically.  For a soundness argument whose whole point is what the model costs, that is a measurement, not lint. |
| `Theory/SetModel/Cnst.lean:255` | `[SetStructure V]`, `[Nonempty V]` | `oracleExtend_append` is a list fact, not a set-theory one |
| `Theory/Typing/KDescend.lean` ×3, `KEta.lean`, `KMeasure.lean`, `KSite7.lean` ×2 | `[Params]` | 7 K-rule lemmas independent of the `Params` class |
| `Foundation/FirstOrder/SetTheory/Z.lean:35` | `[Nonempty V]`, `[⊧* 𝗭]` | **upstream, pinned.**  `subset_of_eq` needs no set theory.  Per `CLAUDE.md` nothing goes outward; recorded here and nowhere else. |

I did not touch any of these.  Instance binders are the *weak* half of the class — they are
inferred, so an unused one rarely blocks a route — but the ZFC/AC ones are worth a deliberate
decision rather than a blanket trim, exactly as the previous round warned about staging
hypotheses.

## 5. Axioms: measured, not argued

Method: for each touched module, dump `(name, collectAxioms name)` for every non-internal
declaration in `env.constants.map₂` (this-module only), sorted, before and after.  "Before" is the
module's `git show HEAD:` text.  Two of the five needed a modified upstream `.olean`
(`ConstSubstNested` needs old `NestedHead`; `TrIndDeclNCtorOwn` needs old `InductR`); those were
built into a scratch symlink mirror of `.lake/build/lib/lean` with the two oleans replaced, and
the old text elaborated against it.  No `.lake` artefact in the repo was modified.

| module | declarations compared | diff |
| --- | --- | --- |
| `Theory/Inductive/NestedHead.lean` | 169 | **identical** |
| `Theory/Typing/ConstSubstNested.lean` | 308 | **identical** |
| `Verify/Environment/InductR.lean` | 81 | **identical** |
| `Verify/Inductive/NestedRestore.lean` | 94 | **identical**, + 6 new `HypTrim2` decls |
| `Verify/Inductive/TrIndDeclNCtorOwn.lean` | 11 | **identical**, + 3 new `HypTrim2` decls |

**663 declarations, zero axiom-set changes.**  Census 13, hole list unchanged.

New declarations' axioms: `HypTrim2Witness` (7) — `[propext, Quot.sound]` throughout except
`nfnF₂_ordered_no_ctor_stage` `[propext, Classical.choice, Quot.sound]`;
`NestedRestore.HypTrim2` (6) — `badTypes` `[]`, `auxRecName_badTypes_isNested` `[propext]`, rest
`[propext, Quot.sound]`; `TrIndDeclNCtorOwn.HypTrim2` (3) — `exists_pfnOnly`
`[propext, Quot.sound]`, the other two `[propext, Classical.choice, Quot.sound]`.
**Hole-freeness, stated separately from inhabitation: no `sorryAx` in any of the 16.**

## 6. Anti-vacuity, in the strong form where the strong form exists

Removing a `Prop` hypothesis cannot make a true statement false, so the risk is that what remains
is vacuous.  The strong check is an instance at a point where the **removed** hypothesis is
*refuted*, so the untrimmed statement had no instance there at all.  That is possible exactly when
the removed hypothesis's own variables survive into the trimmed signature.  Scored honestly:

| trim | strong form | witness |
| --- | --- | --- |
| `ntree_const_staged`, `nlist_const_staged` | **yes** | `HypTrim2Witness.listEnv_ne_empty` refutes `h` at `env₁ := VEnv.empty`; `ntreeAux_staged_over_empty` inhabits the surviving `hs` there; `staged_consts_over_empty` is the arity-0 application, and `staged_names_distinct` shows its two conclusions are two facts |
| `trIndDeclN_wit` + the two `_sat` cascades | **yes** | `TrIndDeclNCtorOwn.HypTrim2.exists_pfnOnly` builds an environment holding `PFn` and **not** `PFn.mk` by `VEnv.addConst`, with the `constants` map computed; `trIndDeclN_wit_without_pfnMk` and `memIndDeclNamesN_sat_without_pfnMk` are the applications there.  **Not instantiated: `notAddInductStagesR_sat`** — it additionally needs a `ConstMap` with `WF` and all-`none` `find?`, and I did not build one; it shares the environment witness but has no application of its own here |
| `recRenames_keys` | **yes, and uniform** | `RestoreData.auxRec` mentions none of `r`, `D`, `K`, `tyArgs`, so `restoreData_refuted_at_badTypes` refutes the removed hypothesis for **every** one of them at `types := badTypes` (a one-member list whose member is itself `_nested`-prefixed).  `recRenames_keys_at_badTypes` applies the trimmed lemma there, and `_nonempty` shows the instance is not `[] = []` |
| `nfnF₂_ordered` | **NO — and this is the honest half** | `hE₂`'s witness `E₂` leaves the signature entirely, so there is no `E₂` left to refute the hypothesis at.  Worse for the trim's importance: `nfn_ctor_stage_exists` **proves the ctor stage succeeds** at the unique `E₁` that `hE₁` pins.  So this trim removes a discharge-able obligation, not an impossible one: **incidental, not route-opening.**  What is proved instead is `nfnF₂_ordered_no_ctor_stage`: the conclusion at a concrete four-environment chain that never constructs a ctor stage anywhere |

Inhabitation, stated separately: `staged_consts_over_empty`, `nfnF₂_ordered_no_ctor_stage`,
`exists_pfnOnly`, `recRenames_keys_at_badTypes` are all arity 0 or take only the surviving
hypothesis.  `recRenames_keys_at_badTypes_nonempty` and `staged_names_distinct` are the guards
against the "true for a trivial reason" trap the previous round flagged.

**Severity count, the number that actually matters:** of the seven trims, **zero** were blocking a
route today (the two `NestedHead` ones and `recRenames_keys` are now strictly more general and
their strong witnesses prove it, but no existing caller wanted the general form).  The one
route-opening instance this round found is **`exists_instN_typed`'s `henv`, which I could not
fix** (§4(i)), and the one it *created* is `ntreeAux_WF`'s `h` (§2).  So the honest headline is:
**the sweep is now complete and mechanised, and it hands the next stream two named routes.**

## 7. The round-close check — exact text, and I do not own the file

`ORCHESTRATOR.md` is not mine.  The addition, verbatim, for its round-close checks:

> - **Read the build's own linter output.**  `lake build 2>&1 | grep -c "automatically included
>   section variable"` must be **0**, or every remaining warning must be named in the round's
>   handoff with its ripple measured.  This is the `include`-over-supply class
>   (`docs/handoff-hyptrim2.md`): a theorem carrying a hypothesis its proof never uses, where the
>   hypothesis is often the reason a route looked closed.  Lean detects it for free — under bare
>   `include`, under `include … in`, and for unused instance binders — and the class went
>   undetected for two rounds only because nobody read the warnings.  Do **not** substitute a
>   textual scan: measured precision 7/12 and 2/5, and it misses every instance outside an
>   `include` scope (18 of 24 on 2026-09-03).  After fixing one, **rebuild and read again** —
>   cascades are the norm, twice observed.
>   Current baseline: **20**, all named in `docs/handoff-hyptrim2.md` §4.

Worth more than any individual fix, as the brief said.  Note the check also catches unused
*instance* binders for free, which is where the ZFC/AC-independence findings in §4(iii) came from.

## 8. Pick up first

1. **`Ctx.LiftN.exists_instN_typed`'s `henv`** (`Theory/Typing/StrengthenAxiom.lean:162`), 9 sites
   in 5 files.  A structural lemma gated behind `Ordered env`.  §4(i).
2. **`ntreeAux_WF`'s `h`** (`NestedHead.lean:925`), 25 sites in 8 files, 3 of them a concurrent
   stream's.  Yields `∀ {env}, ntreeAux.WF env`.  §2.
3. **Correct the mechanism claim** in `docs/handoff-hyptrim.md` §1,
   `Theory/Inductive/HypTrimWitness.lean`'s docstring, and
   `Theory/Inductive/OwnRule.lean:56-57`.  Three sentences; none of those files is mine.
4. **Add the §7 check to `ORCHESTRATOR.md`.**
5. Decide the 9 `IndInterp.lean` instance trims deliberately — `indStep₂_eq` and
   `indStep_at_mono` are **AC-free**, which the soundness ledger should probably say out loud.
6. Still open from the previous round and untouched here: delete
   `VIndRestore.substC_tyAppR_free` from `Theory/Inductive/CtorBeta.lean` (proved redundant by
   `rfl` last round; `CtorBeta.lean` is a concurrent stream's file this round too).

## 9. Not done, and deliberately

`tryEtaStructCore.WF` and `isDefEqUnitLike.WF` untouched; no `AddInduct` flip;
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` swept read-only, never opened
for writing, never `touch`ed; `IndStage.lean` not edited; no `git` state changed (no stash, no
worktree, no checkout — the old-text comparisons in §5 go through `git show` into `/tmp`);
`grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` still empty, which is why the Verify-side
witnesses live in the `Verify` files themselves and not in `HypTrim2Witness.lean`; nothing sent
outside this repo.
