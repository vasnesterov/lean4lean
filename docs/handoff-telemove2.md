# handoff-telemove2: the module move, PERFORMED for (A) and HALF-performed for (B)

*Stream started 2026-09-03. Written incrementally. Grading follows `docs/vacuity-ledger.md` §0.*

## 0. Bottom line

| item | verdict |
| --- | --- |
| **(A)** four-component `ctorConstsCR_wf_of_betaD` is **the** statement | **DONE.** `CtorBeta.lean`'s theorem now asks for four data per companion-pointing recursive field, not five, and derives `hbv` itself. Its own witness `ntreeAux_ctorConstsCR_wf_of_betaD` supplies four. Axiom lines for all 21 of `CtorBeta.lean`'s declarations **byte-identical** before and after |
| **(A)** enabling move `§1–§3` → upstream | **DONE.** New module `Theory/Inductive/TeleMove2.lean` (7 theorems), imported by `CtorBeta.lean` in place of `NestedTele.lean`. All 7 axiom lines identical to what `TeleCongr.lean` printed for them |
| **(B)** `minorCtor_hAs` + the two-component supplier at their site | **DONE.** Moved into `RecTyped.lean` §4b/§4c, beside the `MinorCtorHargs` definition they lighten. Axiom lines identical; the 16 pre-existing `RecTyped.lean` declarations' axiom lines identical |
| **(B)** two-component `MinorCtorHargs` as the **stated** bundle | **NOT DONE — a fifth file, and a concurrent stream's file.** Machine-measured ripple in §4. And the reachable bundle is **three** components, not two (§3) — a correction to `handoff-telecongr.md` §6 item 2 |
| the discharges **exercised** rather than available | **DONE, both.** (A) at `CtorBeta.lean` §7b; (B) at `TeleCongr.lean` §2/§3, which now derive `hAs` and then the whole `MinorCtorHargs` at `ntreeAux`'s *moving* entry from `hfld`/`hcbody`/`hfun` alone |

Files touched: `CtorBeta.lean`, `RecTyped.lean`, `TeleCongr.lean` (all three mine), plus the new
`TeleMove2.lean`. **`NestedTele.lean` was not touched at all** — `git diff` on it is empty, so the
two concurrent streams importing it saw nothing from me.

## 1. Where my brief was wrong — the highest-value output, up front

1. **"Therefore … the two-component `MinorCtorHargs` cannot be proved in `RecTyped.lean`."**
   Half wrong, and the half that is wrong matters. The two-component **supplier**
   (`minorCtorHargs_of_hargs'`: bundle from `hcbody` + `hfun` + `hfld`) *can* be proved in
   `RecTyped.lean` and now **is** — it needs only `NestedTele.lean` machinery plus the two `def`s in
   `RecTyped.lean` §4 itself. What cannot be done is changing the **definition** of
   `MinorCtorHargs`, and the obstruction is **not module order at all**: it is that
   `Theory/Inductive/HargsShared.lean` and `Theory/Inductive/HTeleGen.lean` destructure the bundle
   (§4). So the (B) half of the brief mis-names its own blocker, in exactly the way
   `handoff-telecongr.md` §5 item 4 records for the round before.
2. **"§6's move is unverified" — verified, and it is not an *upstream* move.** §6 mentions
   `VIndRestore.MinorFldDefEq` and `.MinorCtorHargs`, both **defined in `RecTyped.lean`**
   (`:694`, `:704`). So §6 cannot move upstream of `RecTyped.lean`; it moves *into* it. That is why
   `TeleMove2.lean` holds only §1–§3 and nothing of §6.
3. **`handoff-telecongr.md` §6 item 2's "`MinorCtorHargs` should lose `hpi` and `hAs`" is not
   reachable — `hAs` yes, `hpi` no** (§3). Dropping `hpi` requires pinning `B`, and the only
   available `B` is `D.atRec (instAll (splitPis npJ (ci.type.instL …)).2 (R.tyArgs t))`, whose
   *statement* mentions a constant `ci` that only an environment supplies. A bundle that pins `B`
   therefore has to take `env`, `npJ` and `ci` as parameters. So "four components become two" is
   true of the **supplier** and false of the **bundle**; the bundle's floor is three.
4. **"a comparable move had zero ripple and identical axioms at 37 declarations" — my move's
   relocation set is 12 declarations, and it is not the whole story.** The relocation set
   (7 to `TeleMove2.lean`, 3 to `RecTyped.lean`, 2 staying) has identical axiom sets. But
   `ctorConstsCR_wf_of_betaD` is **not** a relocation — its statement changed — and I checked its
   axiom set anyway (unchanged). Reporting the distinction because "identical axioms" is not by
   itself evidence a statement was preserved: `ctorConstsCR_wf_of_betaD` proves *less* now and its
   axiom line is the same.
5. **`lake build 2>&1 | grep -c "automatically included section variable"` moved 20 → 18, and none
   of it is mine.** Measured rather than argued: the 18 surviving warnings are all in
   `Theory/SetModel/*`, `Theory/Typing/K*` and `Foundation`; the two that vanished are
   `Theory/Inductive/NestedHead.lean` (HEAD 1 → now 0) and `Theory/Typing/StrengthenAxiom.lean`
   (HEAD 1 → now 0), both **concurrent streams' files** (checked by elaborating each file's `HEAD`
   text and its current text and counting). Zero of the 20 were ever in a file I touched.

## 2. What moved, and the axiom-identity measurement

`TeleCongr.lean` printed **14** `#print axioms` lines at `HEAD`. After the move:

| declaration | `HEAD` axiom set | new home | new axiom set |
| --- | --- | --- | --- |
| `VEnv.TeleDefEq.of_isDefEqCtx_aux` | `[propext]` | `TeleMove2.lean` §1 | same |
| `VEnv.TeleDefEq.of_isDefEqCtx` | `[propext]` | `TeleMove2.lean` §1 | same |
| `VEnv.TeleDefEq.substC` | `[propext, Quot.sound]` | `TeleMove2.lean` §1 | same |
| `VEnv.TeleDefEq.weak0` | `[propext, Quot.sound]` | `TeleMove2.lean` §1 | same |
| `VIndRestore.csubstTy_freshIn` | `[propext, Quot.sound]` | `TeleMove2.lean` §2 | same |
| `VIndCtor.WF.hasArgs_params_bvars` | `[propext, Classical.choice, Quot.sound]` | `TeleMove2.lean` §3 | same |
| `VIndCtor.WF.hasArgs_params_bvars_of_wf` | `[propext, Classical.choice, Quot.sound]` | `TeleMove2.lean` §3 | same |
| `VIndRestore.minorCtor_hAs` | `[propext, Quot.sound]` | `RecTyped.lean` §4b | same |
| `VIndRestore.minorCtorHargs_of_hargs` | `[propext, Classical.choice, Quot.sound]` | `RecTyped.lean` §4c | same |
| `VIndRestore.minorCtorHargs_of_hargs'` | `[propext, Classical.choice, Quot.sound]` | `RecTyped.lean` §4c | same |
| `…ntree_nlistCons_fieldTypesR_ne` | `[propext, Quot.sound]` | stays in `TeleCongr.lean` §1 | same |
| `…ntree_minorCtorHargs_sides_at_cons` | `[propext, Quot.sound]` | stays in `TeleCongr.lean` §1 | same |
| `VEnv.ctorConstsCR_wf_of_betaD₄` | — | **deleted** | superseded: it *is* `ctorConstsCR_wf_of_betaD` now |
| `…ntreeAux_ctorConstsCR_wf_of_betaD₄` | — | **deleted** | superseded by `…ntreeAux_ctorConstsCR_wf_of_betaD` |

Whole-file checks, not per-declaration eyeballing: `git show HEAD:<file>` elaborated with
`lake env lean` into one text and `diff`ed against the same for the working copy —

* `CtorBeta.lean`: **21 declarations, `diff` empty.** (Its `hbeta` lost a conjunct and it gained
  `henv`, and the axiom set is still identical.)
* `RecTyped.lean`: **16 pre-existing declarations, `diff` empty**; the 3 moved ones appended.

New declarations (all in `TeleCongr.lean`, all `[propext, Quot.sound]` except the last):
`ntree_tyArgs_one_noCSubst`, `ntree_minorCtor_hAs_at_cons`,
`ntree_minorCtorHargs_of_two_at_cons` (`[propext, Classical.choice, Quot.sound]`). No `sorryAx`
anywhere in the four files.

### (A), stated exactly

`VEnv.ctorConstsCR_wf_of_betaD` (`CtorBeta.lean` §7) now takes `henv : env.Ordered` and an
`hbeta` whose per-field bundle is `⟨As, B, B', v, hOn, hbody, hpi, hAs, hsort⟩` — **four**
components where it was five. The deleted component is the parameter spine

    e₁.HasArgs D.uvars Γfld D.params (VExpr.bvars (r.binders.length + i) D.np)

which the proof now derives at the call site from
`VIndCtor.WF.hasArgs_params_bvars_of_wf henv he₁ hD h₃ hσ Δ`. **Nothing was added to the bundle**;
the only hypothesis added to the theorem is `henv`, and every caller already has it (`CtorBeta.lean`
derives `henv₃` from `henv₁`, so anything that can supply `henv₃` has `henv`).

`§7b`'s witness `ntreeAux_ctorConstsCR_wf_of_betaD` lost its hand-built `HasArgs` block
(`.cons (by type_tac) .nil` at a three-entry context) and nothing replaced it. That is the
"instantiate, don't admire" check for (A): the discharge is exercised at `ntreeAux`
(`NTree`/`List`, `np = 1`, a real nested block with a companion-pointing recursive field), not
merely available.

### (B), stated exactly

`RecTyped.lean` §4b/§4c now hold `minorCtor_hAs` (the `hAs` conjunct from `MinorFldDefEq` plus
§T13's two side conditions and §T16.2's parameter σ-identity) and the two suppliers. `MinorCtorHargs`
itself is **unchanged** — see §3/§4 for why.

`TeleCongr.lean` is now the *downstream* file it should have been: three sections of checks on
`RecTyped.lean`'s statements.

* §1 `ntree_minorCtorHargs_sides_at_cons` — the five non-data hypotheses, jointly, at `q = 2`
  (`nlistCons`, two recursive fields, restored telescope provably ≠ source). Unchanged from before.
* §2 `ntree_minorCtor_hAs_at_cons` — **new, and the point of the round**: the `hAs` conjunct itself,
  at that entry, from `hfld` alone. The three side conditions are discharged in the term (`rfl`,
  `rfl`, an explicit `ClosedTele`). A conjunction of side conditions proves nothing about whether
  they *compose*; this is the composition.
* §3 `ntree_minorCtorHargs_of_two_at_cons` — **new**: the whole `MinorCtorHargs` at that entry from
  `hfld` + `hcbody` + `hfun`, through `minorCtorHargs_of_hargs'`, with `hCwf` pulled from
  `(ntreeAux_WF h).ctors`, `hargsF` from `ntree_tyArgs_one_noCSubst`, `hcl` from
  `ntree_tyArgs_closedN_np` and the σ-identities *called* rather than assumed. `ci`/`hci`/`hagree`
  are hypotheses because `hcbody`'s **statement** mentions `ci`; §1's fourth conjunct is exactly
  `∃ ci, hci ∧ hagree` at this block, so they are not doing hidden work.

**Grade.** (A): a discharge — a component left the bundle and nothing entered it. (B): still a
*reduction*, now composed end-to-end at a witness. `hcbody`/`hfun` are `hargs` and `hfld` is
`MinorFldDefEq`; all three stay open. No flip; census 13 before and 13 after, same list.

## 3. The bundle's floor is THREE components, not two — and why

`MinorCtorHargs` is `∃ As B B', hcbody B ∧ hpi(B, As, B') ∧ hAs(As) ∧ hfun(B')`.

* **`As` and `B'` are functions of `D, R, t, C, q` alone** — `instAllTele (D.atRecTele (C.fieldTypesR D R)) (bvars k D.np) 0`
  and `instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args)) (bvars k D.np) (C.fieldTypesR D R).length`,
  with `k = nr + nf + (D.nm + q)`. Neither mentions `σ`, `env` or `ci`. So they can be **pinned** in
  the definition, and `hAs` then becomes a closed formula that `minorCtor_hAs` proves. That is the
  three-component form, and it is the one I probed in §4.
* **`B` is not.** `hpi`'s derivation is `instAt_ctor_hpi hlen hagree`, and `hagree` is
  `R.instAt D npJ t ci.type = C.typeR D R t` for a `ci` that comes out of
  `Faithful.ctor_agree` — i.e. out of an *environment*. Pinning `B` means the definition takes
  `env`, `npJ` and `ci`, and `hcbody`'s type then mentions `ci`. The bundle would stop being a
  predicate on `(R, D, σ, e, q, t, C)`.

So `handoff-telecongr.md` §6 item 2's edit ("`def MinorCtorHargs` should lose `hpi` and `hAs`") is
half impossible as stated. The `hpi` half survives only as the **supplier** —
`minorCtorHargs_of_hargs`, which takes `hlen`/`hagree` and hands back the bundle — and that is
where it now lives.

## 4. The ripple, measured — this is the "fifth file" report

Probe: `MinorCtorHargs` replaced by the three-component pinned form (`hAs` deleted, `As`/`B'`
pinned), the two in-file consumers adjusted, one `sorry` at the closure's `hAs` slot so the module
elaborates, then each downstream consumer built. **Reverted immediately**; `RecTyped.lean` contains
zero occurrences of `sorry`, elaborates with 0 errors, and both rippled files build clean again.

| module | result under the probe | ownership |
| --- | --- | --- |
| `Theory/Inductive/RecTyped.lean` | 2 errors (`:883` the §4c anonymous constructor, `:998` the closure's `obtain`) | **mine** — fixable, and both fixes are one line |
| `Theory/Inductive/HargsShared.lean` | **3 errors** at `:259`, `:262`, `:262` — all inside `minorCtorHargs_iff`, whose proof is `rintro ⟨As, B₀, B', hbody, hpi, hAs, hfun⟩` in both directions | **NOT mine — the fifth file** |
| `Theory/Inductive/HTeleGen.lean` | **1 error** at `:114` — `obtain ⟨As, B, B', hcbody, hpi, hAs, hfun⟩` | **NOT mine, and a CONCURRENT STREAM's** (`Theory/Inductive/HTele*`) |
| `Theory/Inductive/ConsumeTeleOffK.lean` | clean | not mine |
| `Theory/Inductive/HypTrimWitness.lean` | clean | not mine |
| `Theory/Inductive/HTeleNTree.lean` | clean | concurrent stream's |
| `Theory/Inductive/TeleCongr.lean` | clean | mine |

**Total ripple outside my ownership: 2 files, 4 error sites.** Both are pure destructurings of the
bundle, so both are mechanical: `HargsShared.lean`'s `MinorCtorShape` would lose its `As`/`B'`
existentials and its `hAs` conjunct (and `minorCtorHargs_iff` its two `rintro` patterns);
`HTeleGen.lean`'s `obtain` becomes `⟨B, hcbody, hpi, hfun⟩` and its
`minorEntry_defeq_of_hargs` call needs `hAs` from `minorCtor_hAs`.

**And there is a second cost the ripple hides**, which is why I would not recommend the change as
it stands. Deleting `hAs` from the bundle moves its proof into
`VEnv.recConstsR_wf_of_recHargsD`, which then needs `minorCtor_hAs`'s side conditions at *every*
entry. `hσp` is free there (`atRecTele_params_substC_eq henv hD hfresh`), but `hσf` and `hclF` are
not: the closure has no `env₃`/`h₃` and no `Faithful`, so the honest form of the change is

    hAs (one typed `HasArgs` per companion entry, inside the bundle)
      ⟶  hσfD : ∀ q t C, D.ctorsAll[q]? = some (t,C) →
                  (D.atRecTele (C.fieldTypesR D R)).map (substC · (R.csubst D K))
                    = D.atRecTele (C.fieldTypesR D R)
          hclFD : ∀ q t C, D.ctorsAll[q]? = some (t,C) →
                  ClosedTele (D.atRecTele (C.fieldTypesR D R)) D.np

— **two decidable side conditions on the restoration data in, one typed datum out**, at every
entry rather than only at companion ones. At `ntreeAux` both are `rfl`/explicit terms (that is
what §1's sixth and seventh conjuncts are), so the trade is real progress *in kind*; but it is a
change to the closure's hypothesis set, so `ntreeAux_obligationB_of_bundles` and
`ntreeAux_recHargs_premises_inhabited` would both need re-verifying. I did not make it. Per the
brief I stopped and measured.

## 5. What is NOT claimed

* The flip is **not** made. Census 13 → 13, same list; `tryEtaStructCore.WF` and
  `isDefEqUnitLike.WF` untouched.
* (A) is **not** discharged. `ctorConstsCR_wf_of_betaD` was and remains a *reduction* of (A) to
  `hargs`; it is now one component lighter.
* (B) is **not** discharged. `hcbody`, `hfun`, `hfld` are open; §3's instantiation takes all three
  as hypotheses and says so in its statement.
* **`MinorFldDefEq` is not inhabited at the moving entry.** `TeleCongr.lean` §2 and §3 both take it
  as a hypothesis. `RecTyped.lean`'s `ntree_minorFld_nil` inhabits it at `q = 1` and discloses that
  as degenerate; `ConsumeTeleOffK.lean` §2 brackets it from below at `q = 0`. Neither settles `q = 2`.
* `substC_tyAppR_free` was **not** touched (the brief's standing instruction), and neither was
  `HypTrimWitness.lean`.
* Nothing here changes `NestedTele.lean`, so nothing here can have disturbed the two concurrent
  streams importing it.

## 6. Verification

* **`lake build` green, 1587 jobs** (1582 at my baseline). **+1 is mine** (`TeleMove2.lean`); the
  other **+4 are concurrent streams'** untracked modules (`HTeleGen.lean`, `HTeleNTree.lean`,
  `Theory/Typing/LiftTrimWitness.lean`, `Verify/Typing/NoConfGuard.lean`). Reported as measured, not
  as the +1 I would have predicted.
* **A transient red build mid-round was not mine.** `Verify/Typing/NoConfGuard.lean:327` — a
  concurrent stream's untracked file. Checked rather than assumed: its transitive import closure was
  computed and contains **none** of `CtorBeta`, `RecTyped`, `TeleCongr`, `TeleMove2`. It went green
  on its own.
* **Census 13 before and 13 after, from the same tree, same hole list**:
  `lake env lean --run scripts/sorry-census-all.lean` → `HOLES … 13`,
  `BUILT: 404; in population but NOT BUILT: 0` (399 at baseline; +5 modules, attribution as above).
* **Section-variable warnings 20 → 18, fully attributed to concurrent streams** (§1 item 5). None of
  the 18 is in `Theory/Inductive/`.
* `TeleMove2.olean` present at `.lake/build/lib/lean/Lean4Lean/Theory/Inductive/TeleMove2.olean`,
  checked directly rather than inferred from a green build; `TeleCongr.olean` likewise.
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — empty.
* **Frozen files:** `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` not opened,
  not written, not `touch`ed; `git diff --stat` on all three empty.
* Guards `24 / INCOMPLETE / 2-2`. Recorded, but **not** evidence for anything here: Guard's closure
  is 24 modules and excludes all of `Theory/Inductive/`.
* 7 + 21 + 19 + 5 = **52 `#print axioms` lines** across the four files, none carrying `sorryAx`.
* No `git` state changed. No `lake update`. Nothing sent anywhere.

## 7. Pick up first

1. **The `MinorCtorHargs` three-component change, if the orchestrator wants it.** Fully specified in
   §4: 2 files outside my ownership, 4 error sites, plus the closure's two new side conditions and
   the two `ntreeAux` inhabitation theorems that re-verify. One of the two files belongs to a live
   concurrent stream, so this wants sequencing, not parallelism.
2. **`MinorFldDefEq` at `ntreeAux`'s moving entries.** It is now the *only* non-`hargs` input to
   the whole minor block: `TeleCongr.lean` §3 shows everything else at `q = 2` is supplied.
   `NestedTele.lean` §T16.1 claims to reduce it to the same head datum; unverified.
3. **The stale "outstanding obstruction" wording is now retired in `CtorBeta.lean` §6d** (it says
   `hbv` is a theorem and points at `TeleMove2.lean` §3). `NestedTele.lean:1550`'s `congr_tele`
   docstring still carries it, and I deliberately did not touch that file.
4. **`docs/handoff-telecongr.md` §6 items 1 and 2 are now done and half-done respectively**, and its
   item 2 is wrong about `hpi` (§3 here). Its §2 "the frozen-file / not-mine edit this implies" is
   discharged.
5. **`hargs`, still.** Both obligations bottom out in strictly less than they did and in the *same*
   less. Nothing here moved that, and `instAt_indep_of_tyArgs` still says no
   restoration-independent argument will.
