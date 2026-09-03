# `VEnv.TeleDefEq` relocated to `Theory/Typing/Lemmas.lean`, and the hole restated over it

Stream of 2026-09-03.  Files I own for this task: `Theory/Typing/ConstSubstNested.lean` (source),
`Theory/Typing/Lemmas.lean` (destination), `Theory/Inductive/Decl.lean`,
`Theory/Inductive/RecArgIndep.lean`, plus this file.  `Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean` **not opened for writing, not `touch`ed**.

*(Written incrementally; sections appear as they are measured.)*

---

## 0. Baseline, measured on this tree before any edit

| quantity | value | how |
| --- | --- | --- |
| commit | `b7bf5b6`, working tree clean apart from four concurrent streams' untracked/modified files | `git status` |
| `lake build` | exit 0, **1558 jobs** | full build |
| guards | `guard 1: 24 ✓` / `guard 2: whitelist ✓ (proof INCOMPLETE: sorryAx present)` / `guard 3: 2/2 ✓` | same build log |
| census | on disk 399 / population 375 / **BUILT 375 / NOT BUILT 0** / **13 holes** | `lake env lean --run scripts/sorry-census-all.lean` |
| `VIndRecArg.exists_indep` in the census | yes, `[Lean4Lean.Theory.Inductive.Decl]` | same |

Axiom baselines are in `/tmp/telemove/axioms-before.txt` (21 declarations around `TeleDefEq`)
and `/tmp/telemove/axioms2-before.txt` (16 declarations in `RecArgIndep.lean`), both taken with
`lake env lean` on a freshly-built tree.

## 1. Is the move pure?  **Measured, and the relayed claim is nearly right but not literally right**

The claim relayed to me was: "its only dependencies are `VEnv.IsDefEq` and `List VExpr`."

What the inductive actually mentions (`ConstSubstNested.lean:148-152`, read off the source):
`VEnv`, `Nat`, `List VExpr`, `VExpr` (in `.sort`), **`VLevel`** (the `{u : VLevel}` binder of
`cons`), and `env.IsDefEq`.  So the claim omits `VLevel` and `VExpr.sort`.  That omission is
harmless — both live in `Theory/VLevel.lean` / `Theory/VExpr.lean`, which are in
`Theory/Typing/Lemmas.lean`'s import closure — but it is the sort of thing that has been wrong
twice this session, so: **the conclusion survives, the stated reason was incomplete.**

Measured import closures (`/tmp/telemove/closure.py`, a transitive walk of `import` lines):

| module | closure size | contains `Typing/Lemmas` | contains `Inductive/Decl` |
| --- | --- | --- | --- |
| `Theory/Typing/Lemmas` | **7** | — | **no** |
| `Theory/Inductive/Decl` | 9 | yes | (itself) |
| `Theory/Typing/ConstSubstNested` | 42 | yes | yes |
| `Theory/Inductive/NestedTele` | 47 | yes | yes |
| `Theory/Inductive/ParamRedex` | 50 | yes | yes |
| `Theory/Inductive/StoredIota` | 49 | yes | yes |
| `Theory/Inductive/RecArgIndep` | 44 | yes | yes |
| `Theory/Inductive/NestedRules` (untracked, a concurrent stream's) | 46 | yes | yes |

`Lemmas.lean`'s whole closure is `Std.Basic`, `Std.VariableBang`, `Typing.Basic`, `VEnv`,
`VExpr`, `VLevel` and itself — so everything the inductive names is already there, and nothing
in it is downstream of `Decl.lean`.  This also **re-confirms** last round's two layering
refutations independently: `Decl.lean` is in `ConstSubstNested.lean`'s closure, and
`ConstSubstNested.lean` is *not* in `Decl.lean`'s.

Users of the inductive, tree-wide (`grep -rl TeleDefEq`, then read):

| file | mentions | uses the inductive? |
| --- | --- | --- |
| `Theory/Typing/ConstSubstNested.lean` | 42 | yes (definition site + 8 declarations) |
| `Theory/Inductive/NestedTele.lean` | 149 | yes (9 `TeleDefEq.*` lemmas) |
| `Theory/Inductive/ParamRedex.lean` | 24 | yes |
| `Theory/Inductive/StoredIota.lean` | 9 | yes |
| `Theory/Inductive/RecArgIndep.lean` | 20 | yes |
| `Theory/Inductive/NestedRules.lean` | 3 | **no — prose only**, all three in a docstring |
| `Experimental/ConeJoin.lean` | 1 | **no — prose only**, in an `import` line's trailing comment |

Every user has `Typing/Lemmas` in its closure, so **the move needs no `import` edit anywhere**:
relocating a declaration *upstream* can only widen availability.  That is the structural reason
the ripple should be zero, and it is a measurement, not a guess.

## 2. The move, and the ripple: **zero**

`Theory/Typing/Lemmas.lean` gained, immediately after `IsDefEqCtx.refl` (inside that file's
`namespace VEnv`, so the *full name is unchanged* — `Lean4Lean.VEnv.TeleDefEq`), a section
comment plus the inductive **verbatim**, with only `inductive VEnv.TeleDefEq` rewritten to
`inductive TeleDefEq` because the destination is already inside `namespace VEnv`.
`ConstSubstNested.lean` lost those seven lines and gained a five-line pointer in the
`/-! ## The congruence half … -/` section header that used to introduce it.  The `mkPi`/`mkLams`
congruences stayed put: they need `VEnv.Ordered` and the `mkPi` API, which is `Telescope.lean`'s.

| check | result |
| --- | --- |
| files edited for the move | **2** — the source and the destination, both mine.  No third file, no `import` line anywhere |
| targeted build | `lake build` of `Typing.Lemmas Typing.ConstSubstNested Inductive.Decl Inductive.NestedTele Inductive.ParamRedex Inductive.StoredIota Inductive.RecArgIndep Verify.Guard` — **exit 0, 1192 jobs, 0 errors** |
| guards | `24 ✓ / whitelist ✓ INCOMPLETE / 2-2 ✓` |
| `#print axioms`, 21 declarations around `TeleDefEq` | **byte-identical** before/after (`diff` clean) |
| `#print axioms`, 16 declarations in `RecArgIndep.lean` | **byte-identical** before/after |
| proof terms changed | **none** — the four files that consume the inductive and that I do not own (`NestedTele`, `ParamRedex`, `StoredIota`, and `ConstSubstNested`'s own eight consumers) re-elaborate unedited |

So the move meets the bar the brief set (proof terms accepted unchanged, `#print axioms`
identical) at **37** declarations.

### 2b. Three build failures in the full tree, and none of them is mine

The full `lake build` at 09:25 fails in exactly three modules, all of them files a **concurrent
stream is editing right now** (mtimes 09:25:07 and 09:27:41, i.e. during my build):

* `Theory/Inductive/MemberRedex.lean:1085` and `Theory/Inductive/RestoreBridge.lean:974` —
  `` `fields_noK` is not a field of structure `VInductDecl'.Built` `` / `Fields missing: kfresh`.
  That is the `FieldsRemove*`/`NestedBuild.lean` stream replacing `Built.fields_noK` with
  `kfresh` (`git diff --stat NestedBuild.lean` = 55 changed lines) and not yet having propagated
  it.  Nothing to do with `TeleDefEq`.
* `Verify/Typing/QuotKEta.lean:238` — `` the environment does not contain
  `Lean4Lean.VEnv.IsDefEq.refl` ``.  I checked: **no such declaration has ever existed in this
  tree** (`grep -rn "theorem VEnv.IsDefEq.refl\|theorem IsDefEq.refl"` is empty).  That file is
  untracked and was last written 20 seconds before my build reached it.

My eight targets plus their 1192-job closure are green, which is the strongest statement I can
make about the move while another stream's tree is red.  **Do not read "full build green" off
this round** — read "green on the closure of everything that mentions `TeleDefEq`, plus the
guards".

### 2c. An instrument note: `Verify/Guard.lean` was *not* rebuilt, and that is correct

Lake said `Replayed Lean4Lean.Verify.Guard` and `Guard.olean`'s mtime stayed at 06:33 while
`Lemmas.olean` was rewritten at 09:22:59.  I chased this as a possible stale-`.olean` (the hazard
the brief names) and it is not one: **`Verify/Soundness.lean`'s import closure is 20 modules and
`Verify/Guard.lean`'s is 24, and neither contains `Theory/Typing/Lemmas.lean`.**  The guards are
genuinely independent of the whole `Theory/Typing` layer, so a replay is a valid answer.  Anyone
using "did Guard rebuild?" as a proxy for "did my `Theory/` edit land?" will get a false negative.

## 3. The restatement — outcome 1, in a form the brief did not name

`TeleDefEq.refl` moved with the inductive (four lines, same purity argument, `#print axioms`
re-checked below).  That was not asked for and it is the load-bearing part of the round: it is
what makes the degenerate witness free **at `Decl.lean`'s layer**.

`Decl.lean`'s conclusion is now the original **six** conjuncts plus one:

```
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
      r'.BindersIndep pre i ∧
      env.TeleDefEq D.uvars Γ r.binders r'.binders
```

Hypotheses **unchanged** (all ten, `hOn` included).  The `sorry` is still a `sorry` — not closed,
not weakened, not turned into a hypothesis; the census still names it and this file's
faithfulness check still applies it.

### 3a. Why *this* shape and not `IndepUpgrade`

The brief flagged outcome 3 — "the current inlined form is a strict superset of the original six
and recovering the old form needs no `SortUniq`" — as a legitimate result, and it is right that
the obvious `TeleDefEq` restatement is worse.  Replacing the conclusion by `IndepUpgrade`
(`∃ bs, TeleDefEq … ∧ NoBlock ∧ BindersIndep`, `RecArgIndep.lean` §6) **drops** the `F.type`
conversion `IsDefEqType Γ F.type (r'.canonType D i)`, and recovering it costs exactly
`isDefEqType_trans_of_sortUniq` — that is what `indepGoal_of_indepUpgrade` has always paid.  So
`IndepUpgrade` as the conclusion would have re-imposed the `SortUniq` charge on every consumer,
which is the regression the brief warned about.

Keeping the six and replacing only the *morning's two extra conjuncts* by the `TeleDefEq` avoids
that, and it is strictly better than the morning's form in both directions:

| | morning (two conjuncts) | evening (`TeleDefEq`) |
| --- | --- | --- |
| original six conjuncts | verbatim | verbatim |
| `SortUniq` to recover the original six | none | none |
| the two context-relative facts | *are* the conjuncts | derived — `RecArgIndep.indepGoalPair_of_indepGoal`, from `hOn` (a hole hypothesis) and `pos`'s own `canonResult` typing, `[propext]`, no `SortUniq` |
| degenerate witness `r' = r` | needs `hOn` (`isDefEqCtx_refl_suffix`) and `hdefeq` (`isDefEqType_refl_r`) | needs **nothing** — `VEnv.TeleDefEq.refl` carries no typing |
| converse (two conjuncts → `TeleDefEq`) | — | **fails** without pi-injectivity: that is the whole point of the conjunct |

So the new conclusion is strictly stronger than the morning's, and `indepGoalPair_of_indepGoal`
is the machine-checked "nothing is lost".  The morning's form is kept in `RecArgIndep.lean` as
`VIndRecArg.IndepGoalPair` so that claim is a theorem and not a note.

### 3b. The three halves: **all re-proved, and they got cheaper**

| theorem | axioms before this round | axioms after | change |
| --- | --- | --- | --- |
| `VIndRecArg.exists_indep_of_pre_norec` | `[propext, Quot.sound]` | `[propext, Quot.sound]` | `hOn` is now **unused** (`_hOn`) |
| `VIndRecArg.exists_indep_of_binders_nil` | `[propext, Quot.sound]` | `[propext, Quot.sound]` | same |
| `VIndRecArg.exists_indep_of_i_zero` | `[propext, Quot.sound]` | `[propext, Quot.sound]` | same |
| `VIndRecArg.indepGoal_of_bindersIndep` | `[propext]` | `[propext]` | lost its `hOn` hypothesis |
| `VIndRecArg.indepGoal_of_exists_indep` (faithfulness) | `[propext, sorryAx, Quot.sound]` | `[propext, sorryAx, Quot.sound]` | now points at the **new** statement |
| `RecArgIndep.posSome_transport_of_indepGoal` (the consumer) | `[propext, Quot.sound]` | `[propext, Quot.sound]` | goes through §4b; still **no `SortUniq`** |
| `RecArgIndep.indepGoal_of_indepUpgrade` | `[propext, Quot.sound]` | `[propext, Quot.sound]` | now measures exactly the price of the `F.type` conjunct |

The brief expected this to be the hard part ("a `TeleDefEq`-shaped conclusion may not admit the
same trick").  It admits a *better* one: `VEnv.TeleDefEq.refl` is unconditional, so the two
reflexivity lemmas the previous round had to invent are no longer needed for the hole at all —
they are now used only by `indepGoalPair_of_bindersIndep`, the same degeneracy statement for the
morning's form, which I kept precisely so those two lemmas stay live and the comparison stays
measurable.

### 3c. Anti-vacuity, stated as three separate facts

* **Hole-freeness.**  Every declaration in `RecArgIndep.lean` except
  `VIndRecArg.indepGoal_of_exists_indep` is `sorryAx`-free (33 `#print axioms` lines in the
  file's own §8 audit, all green).  That one carries `sorryAx` *by construction*: it applies the
  hole, so it typechecks only if `IndepGoal` is the hole's conclusion — and it still does, which
  is how I know the faithfulness check follows the new statement.
* **Inhabitation of the conclusion.**  Proved on the `BindersIndep`-already-holds regime
  (`indepGoal_of_bindersIndep`, `[propext]`), and it is now *free*.
* **Satisfiability of the premise — new this round, and it was missing.**  Last round's
  `rai_hyps` exhibits the **five** pre-repair hypotheses at `raiEnv`, and last round's own
  `rai_not_staged` then proves the repaired statement's `henv₀`+`hstage` pair **excludes** that
  environment.  So between the two, the tree contained **no instance satisfying all ten current
  hypotheses at once** — and a statement whose premises are jointly unsatisfiable is vacuous
  however strong the conclusion looks (ledger §0).  `RecArgIndep.rai_hyps_all`
  (`[propext, Quot.sound]`, §7.3c) closes that: all ten hold at `env₀ = VEnv.empty`,
  `env = raiEnv0` (the environment `rai_staged` actually produces), `pre = []`, `i = 0`,
  `Γ = []`, `F = raiF0`, `r = ⟨[], 0, []⟩`.
  **Degeneracy, kept separate**: that instance has `pre = []`, so its conclusion is satisfied by
  `r' = r` and it says nothing whatever about the hard case.  §7.2 remains the record of the hard
  case, at a different instance.  The two facts do not imply each other, in either direction.

## 4. Final measurements (all after a rebuild, and after the tree stopped flapping)

| quantity | value |
| --- | --- |
| files I edited | **4** — `Theory/Typing/Lemmas.lean` (+30), `Theory/Typing/ConstSubstNested.lean` (net −8 code, +11 doc), `Theory/Inductive/Decl.lean` (statement + docstring), `Theory/Inductive/RecArgIndep.lean`.  **No fifth file.**  The other seven modified paths in `git status` belong to concurrent streams |
| targeted build (`Lemmas ConstSubstNested Decl NestedTele ParamRedex StoredIota RecArgIndep Guard`) | **exit 0, 1192 jobs, 0 errors** |
| guards | **`24 ✓` / `whitelist ✓ (proof INCOMPLETE: sorryAx present)` / `2-2 ✓`** |
| census, after | **13 holes** (identical list, `VIndRecArg.exists_indep` among them); population 375 → **381**, BUILT **380**, NOT BUILT **1** |
| the one unbuilt module | `Lean4Lean.Theory.Typing.SpineVar` — untracked, a concurrent stream's, rewritten at 09:40:18 *during* my build |
| `#print axioms`, 21 declarations around `TeleDefEq` | **byte-identical** to baseline (`diff` clean) |
| `#print axioms`, 16 declarations in `RecArgIndep.lean` | **byte-identical** to baseline (`diff` clean) — this covers the three halves, the consumer, and the faithfulness check |
| layering | `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — **empty** |
| frozen files | `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` untouched (not in `git status`, never opened for writing, never `touch`ed) |

**Full `lake build` is *not* green, and not because of me.**  Three consecutive full builds during
this round failed in three different sets of modules, each set a concurrent stream's in-flight
work; the intersection with my four files is empty.  See §2b and §5.  What I can report is the
1192-job closure of everything that mentions `TeleDefEq`, plus the three guards, plus the census.

## 5. Two instrument anomalies, both worth ledger rows

1. **`lake build` failed with `no such file or directory` for three `.olean`s that exist.**
   The 09:37 build reported `error: no such file or directory (error code: 4294967294)` for
   `Theory/Typing/UnivDiscrim.olean`, `Theory/SetModel/CnstRecursion.olean` and
   `Verify/Inductive/SpineTransfer.olean`.  All three Lean processes had **succeeded** (their
   `#print axioms` and their `measured: …✓` lines are in the log), and all three `.olean`s are on
   disk with mtimes *inside* the build window.  Disk was 21% full.  The next build had no such
   error.  Most likely cause, flagged as a **[guess]**: several streams run `lake build` in this
   one tree concurrently, and Lake's write-then-rename into `.lake/build` races.  Consequence:
   **`lake build` exit 1 is not by itself evidence that any source file is broken** — read the
   error kind first.  This is the mirror image of rows 189c/191c (green build, missing `.olean`).
2. **`Verify/Guard.lean` legitimately does not rebuild after a `Theory/Typing` edit** (§2c):
   its import closure is 24 modules and contains no `Theory/Typing/Lemmas.lean`.  "Guard replayed"
   is not evidence that a `Theory/` edit failed to land.

## 6. Where the brief and the previous round were wrong

1. **"It would be a pure move: the inductive's own dependencies are `VEnv.IsDefEq` and
   `List VExpr` only."**  Substantively right, literally incomplete — it also names `VLevel` and
   `VExpr.sort` (§1).  Harmless here; recorded because the reason given was not the reason that
   holds.
2. **"A `TeleDefEq`-shaped conclusion may not admit the same trick" (the degeneracy worry).**
   Refuted, and in the *good* direction: `VEnv.TeleDefEq.refl` is unconditional, so the degenerate
   witness needs **no** hypothesis at all, where the morning's form needed two.  The three halves
   did not merely survive — they now leave `hOn` unused.
3. **Outcome 3 was a real risk and it is real for the *obvious* restatement.**  Replacing the
   conclusion by `IndepUpgrade` (the pure `TeleDefEq` existential) *would* have been worse: it
   drops the `F.type` conversion, and recovering that is `isDefEqType_trans_of_sortUniq`, i.e. a
   `SortUniq` charge on every consumer.  What lands instead keeps the six and swaps only the
   morning's two extra conjuncts.  So the brief's warning was correct about a statement that is
   not the one I wrote (§3a).
4. **A hole in the previous round's anti-vacuity story, which I closed.**  `rai_hyps` shows the
   **five** pre-repair hypotheses at `raiEnv`; `rai_not_staged` shows the repaired statement
   *excludes* `raiEnv`.  Neither the previous round nor the brief noticed that this left **no
   witness for the current ten-hypothesis premise anywhere in the tree** — which is ledger §0's
   own failure mode applied to the premise instead of the conclusion.  `rai_hyps_all` (§7.3c)
   fixes it.
5. **A number in the previous handoff to read carefully, not a mistake**: it says "the `sorry` is
   at line 645".  The build's warning says 625.  Both are right — 625 is the `theorem` line the
   `declaration uses sorry` warning attaches to, 645 was the `sorry` token.  After this round they
   are 625 and 642.

## 7. Pick up first

1. **`VEnv.TeleDefEq` now has a two-part API split across two layers**: the inductive and `refl`
   in `Theory/Typing/Lemmas.lean`, and `append`/`of_eq`/`of_entries`/`of_entries'`/`instN`/
   `weakN`/`append4`/`length_eq`/`append4'` still in `Theory/Inductive/NestedTele.lean` plus the
   `mkPi`/`mkLams` congruences in `ConstSubstNested.lean`.  `length_eq` in particular is duplicated:
   `VEnv.TeleDefEq.length_eq` (NestedTele) and `RecArgIndep.teleDefEq_length_eq` prove the same
   thing.  `length_eq`, `of_eq` and `append` are all pure in the same sense the inductive was, so
   they can follow it; `RecArgIndep.teleDefEq_length_eq` should then be deleted in favour of the
   one in `Lemmas.lean`.  I did not do it: `NestedTele.lean` is not mine, and the measured ripple
   bar wants one owner per move.
2. **The hole is now stated in the form its consumer wants, so the next move is the proof, not the
   statement.**  Its two open inputs are unchanged: `IsDefEqU.forallE_inv` and — *only for whoever
   proves it* — `VEnv.SortUniq` (§3a's table; `RecArgIndep.posSome_transport_of_indepGoal` still
   takes neither).
3. **`RecArgIndep.rai_hyps_all` is a degenerate instance and is labelled as one.**  What is still
   missing, and is the honest next anti-vacuity job, is a **single instance satisfying all ten
   hypotheses where `r` is *not* a witness**.  §7.2's `raiRec1` is such an `r`, but at an
   environment `rai_not_staged` excludes, and building the same shape at a *staged* environment is
   the open question — it may be impossible, which would be the strongest possible result about
   this hole (the residual regime empty ⇒ the whole obligation is §2's degenerate case).
   **[analysis, not proved]** either way.
4. `Theory/Inductive/NestedBuild.lean`'s `VNestedOcc.bindersIndep` is still the unexamined lead
   from the previous round's §7.3 — I did not touch it (that file is another stream's) and did not
   measure whether it makes the `∃ r'` form unnecessary on the nested-companion regime.
