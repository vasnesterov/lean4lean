# handoff-migrate2 — two layering migrations: `MutualNamesGate` removed, `WFPos` §1 into `Decl.lean`

Stream: `migrate2`, opened 2026-09-04.  HEAD at open: `fca5b82`.

Owned (editable): `Lean4Lean/Verify/Inductive/NoNestedAll.lean`,
`Lean4Lean/Verify/Inductive/MutualNames.lean`, `Lean4Lean/Verify/Inductive/WFPos.lean`,
`Lean4Lean/Theory/Inductive/Decl.lean` (**add-only**; the census hole
`VIndRecArg.exists_indep` at :678 is off limits — not touched, not attempted, not re-documented),
and this file.  Everything else read-only.  `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` are frozen and are never opened for writing.

This is a **refactor round**: no new mathematics, and no statement may change meaning.

## §1 Priors — written BEFORE any edit, NEVER edited.  Corrections go in §2 only.

**Context available when these were written.**  `cat`/`grep`/`sed` only, plus **one** bare
`lake build` run as a baseline before the priors were written (recorded honestly as M0 below —
it is a measurement that predates §1, and I am not pretending otherwise; it answers no prior
about *my* work, only the tree's starting state).  Read in full: `CLAUDE.md`;
`docs/handoff-mutualnames.md` §3 and §4 (and its §1/§2 headings); `docs/handoff-wfpos.md` M14
and §3; `Verify/Inductive/MutualNames.lean` all 314 lines; `Verify/Inductive/NoNestedAll.lean`
lines 1-40 and 330-470 plus a full declaration outline; `Verify/Inductive/WFPos.lean` lines
1-215 and 520-572 plus a full outline; `Theory/Inductive/Decl.lean` lines 1-20, 215-360,
660-700, 1085-1138 plus a full outline; `scripts/{exists,shape,can-cite,sorry-census,
sorry-census-all}.lean|py` header comments.  No LSP call, no `scripts/*` run, no `can-cite.py`
run yet.

### §1a SHAPE priors (four, written first, per method rule 1)

| # | prediction | p |
| --- | --- | --- |
| **S1** | **Does the target already exist? — Partly, and in a form no name search finds.** Searching by *conclusion head* rather than by name: `spineArgs_drop_tyApp`'s conclusion (`(D.tyApp _ _ args).spineArgs.drop D.np = args`) is **already proved inline inside `Decl.lean`**, as the third `Prod.ext` goal of `VIndCtor.skeleton_type` (:1107-1110), specialised to `C.canonResult`. So Migration 2's first declaration is a *factorisation of an existing tactic block in the destination file*, not new content — which strengthens the case for the move and is invisible to `exists.lean` (no such name) and to `shape.lean` (the statement is an `Eq`, and the inline step is not a declaration at all). I predict `uniformOcc?_canonResult_snd` and `residualClean_canonType` have **no** counterpart, inline or named. | 0.8 |
| **S2** | **Is the work in the direction I think? — For Migration 2, NO, and M14's stated insertion point is WRONG.** M14 says insert all three "immediately after `instance decidableResidualClean` … just before `end VInductDecl'` at what is currently line 320". But `VIndRecArg.canonResult` and `VIndRecArg.canonType` are declared at **:334 and :338**, i.e. *after* that `end VInductDecl'` (:322). Two of the three declarations mention `r.canonResult`/`r.canonType` in their statements, so at line 320 they do not elaborate. The correct insertion point is **after the "Canonical types (design §3)" group**, and `namespace VInductDecl'` must be re-opened there. This is a placement defect in the spec, exactly the thing my brief says placement is my job. | 0.85 |
| **S3** | **Is what I am about to trust a measurement or a docstring? — M14 is a measurement; §3.1's "no import change" is a docstring-grade claim.** M14 says `lean_run_code` with `Theory.Inductive.Decl` as the only import elaborated all three verbatim, zero diagnostics — that is a measurement, but it was taken with the declarations in *some* order in a scratch file, which is precisely blind to S2's in-file ordering problem (a scratch file can put `canonType` first). `handoff-mutualnames.md` §3.1's list of eight prerequisites already in `NoNestedAll.lean` is a hand-audit of names, not a compile: it omits `M_bind_ok'`… no, it lists it. What it *cannot* have checked is that the eight transplanted theorems land **before** their first use and **after** their own dependencies inside a 629-line file. I predict the mutualnames transplant needs **no reordering beyond the block boundary given**, because §3.1's dependency list is entirely at lines 92-341 and the insertion is at 343. | 0.7 |
| **S4** | **What does the implementation compare with, and is that comparison opaque? — Yes, and it is the whole reason Migration 1 exists.** `MutualNamesGate` asserts `env.find? v.name = none` with no hypothesis on `env.constants`; the only check that supplies it (`checkName`) yields `env.contains v.name = false`; the bridge at `SMap` stage 2 runs through `PersistentHashMap.containsAux`/`findAux`, both upstream `partial def` and therefore body-less. So the gate is not "unproved" — it is **independent**, and removing it is not merely tidying: it deletes a `Prop` that reads to a future maintainer as an open obligation when the obligation is a question about two opaque upstream functions. I predict this makes the migration *mandatory* rather than cosmetic, and that no `divergences.md` entry is needed because nothing about the implementation changes. | 0.9 |

### §1b Cost / outcome priors (written after the shape priors, deliberately)

| # | prediction | p |
| --- | --- | --- |
| C1 | Bare `lake build` is green at the end, job count **unchanged at 1662** (no module added, none removed). | 0.8 |
| C2 | All three guards pass unchanged: guard 1 "24 frozen axioms ✓", guard 2 "within whitelist ✓ (proof INCOMPLETE: sorryAx present)", guard 3 "2/2 remaining ✓". | 0.9 |
| C3 | Census stays at **13**. Nothing I touch has a `sorry`; `exists_indep` is not touched. | 0.9 |
| C4 | **Arity falls by exactly 1** on four declarations (`addMutual_noNestedEnv`, `addDecl_noNestedEnv`, `VEnv.NoNestedN.of_addDecl`, `addDecls_noNestedEnv`) and their **cones grow**, because the gate argument (a bound variable, cost 0) is replaced by a real proof term reaching `forIn_ok_fresh`/`checkConstantVal_find?_none`. | 0.85 |
| C5 | **Cones are invariant under Migration 2.** A cone is a property of a proof term, not of a module, so `spineArgs_drop_tyApp` (cone reported 881 for `residualClean_canonType` in `vacuity-ledger.md` row 326) should measure identically after the move. If it does not, the move changed a proof, which rule 5 forbids. | 0.8 |
| C6 | No downstream module outside my four files needs an edit: nothing in the tree cites `MutualNamesGate` except `NoNestedAll.lean` and `MutualNames.lean`, and nothing cites the three moved names except `WFPos.lean`. | 0.75 |
| C7 | Two prose repairs named in `handoff-mutualnames.md` §3.4 (`Inductive/Add.lean`:1096-1098 and `Verify/Inductive/RestoreFaithful.lean`:418-420) become **stale-and-now-wrong** the moment Migration 1 lands, and **I do not own either file**, so they stay wrong and I report them. | 0.85 |
| C8 | `WFPos.lean` §6's sentence "Every declaration this file introduces, in order" becomes false for its first three `#print axioms` lines. I keep the checks (they are coverage) and repair the sentence, in a file I own. | 0.8 |

## §2 Measurements — appended the moment each lands, before the next tool call

### M0. Baseline, taken before §1 was written (disclosed, not backdated)
Bare `lake build` at `fca5b82`, clean worktree: **exit 0, "Build completed successfully (1662 jobs)"**.
Guards, verbatim from the log:
* `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`
* `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
* `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`

### M1. Before-cones (`scripts/exists.lean`, population **476 built modules**, 2026-09-04)

Migration 1 (all in `Verify.Inductive.NoNestedAll`):

| name | arity | cone |
| --- | --- | --- |
| `MutualNamesGate` | 0 | 7301 |
| `addMutual_noNestedEnv` | 7 | 8145 |
| `addDecl_noNestedEnv` | 8 | 9192 |
| `addDecls_noNestedEnv` | 8 | 9195 |
| `VEnv.NoNestedN.of_addDecl` | 11 | 9592 |

Migration 2 (all in `Verify.Inductive.WFPos`):

| name | arity | cone |
| --- | --- | --- |
| `VInductDecl'.spineArgs_drop_tyApp` | 4 | 633 |
| `VInductDecl'.uniformOcc?_canonResult_snd` | 7 | 862 |
| `VInductDecl'.residualClean_canonType` | 4 | 881 |
| `VIndField.residualClean_of_canon` (stays in `WFPos`) | 6 | 884 |
| `VInductDecl'.residualClean_of_recArgOf` (stays) | 6 | 1744 |

All ten: own value is a hole **false**, cone reaches `sorryAx` **false**.

### M2. **S3 half-RIGHT: M14's `can-cite` claim reproduces exactly; M14's *insertion point* does not.**
`scripts/can-cite.py` re-run 2026-09-04: `Theory.Inductive.NestedHead` (closure **50** modules) and
`Theory.Inductive.DeclExamples` (closure **30**) both answer **NO** on all three declarations,
"defined in `Lean4Lean.Verify.Inductive.WFPos`… or the declaration must move upstream".  So the
motivation for Migration 2 is confirmed against the compiled environment, not taken on trust.

**But S2 (0.85) is RIGHT and this is the round's one real correction to a spec.** M14 says to insert
all three "immediately after `instance decidableResidualClean` … just before `end VInductDecl'` at
what is currently line 320".  `decidableResidualClean` ends at :320 and `end VInductDecl'` is :322 —
and `VIndRecArg.canonResult` / `VIndRecArg.canonType` are declared at **:334 / :338**, *after* that
`end`.  `uniformOcc?_canonResult_snd` and `residualClean_canonType` both mention `r.canonResult` /
`r.canonType` **in their statements**, so at line 320 neither elaborates: `unknown identifier`.
M14's supporting measurement (`lean_run_code`, `Theory.Inductive.Decl` as sole import) is blind to
this by construction — a scratch snippet supplies its own order.  Actual insertion point used:
**after `VIndCtor.recFields` (:354), at the end of the "Canonical types (design §3)" group**, with
`namespace VInductDecl'` re-opened for the three.  No statement changed; only the line number in the
spec was wrong.

### M3. **S1 (0.8) RIGHT, both halves.**
(a) `spineArgs_drop_tyApp`'s conclusion is *already proved inline* in the destination file, as the
third `Prod.ext` goal of `VIndCtor.skeleton_type` (`Decl.lean`:1107-1110):
`rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.spineArgs_mkApp, VExpr.spineArgs_const,
List.nil_append, List.drop_left' (by simp)]` — the same five rewrites, specialised to
`C.canonResult`.  So the moved lemma is a factorisation of a tactic block that was already in
`Decl.lean`, which no name search and no `shape.lean` query can see (an inline `rw` chain is not a
declaration).  **I did not refactor `skeleton_type` to cite it** — that would be a proof change in a
refactor round, and the brief forbids inventing work.  It is recorded here as a free follow-up.
(b) `shape.lean` on conclusion head `VInductDecl'.ResidualClean` (476 modules, 2026-09-04): **28**
constants, of which the only producers at the canonical form are `residualClean_canonType` and
`residualClean_of_recog`, both in `WFPos`.  The two `Decl.lean` producers are the trivial
`residualClean_of_uniformOcc_{none,some}` and the `decide` instance.  No counterpart exists for the
other two moved declarations.

### M4. Census before edits: **13** (`scripts/sorry-census-all.lean --run`, 476 modules, pass A 13 /
pass B 0), `VIndRecArg.exists_indep [Theory.Inductive.Decl]` among them and untouched.

### M5. Migration 2 landed; the placement M14 gave would have failed
Inserted into `Theory/Inductive/Decl.lean` after `VIndCtor.recFields` (:353), re-opening
`namespace VInductDecl'`, with a section comment recording the provenance.  Removed from
`WFPos.lean` §1 (56 lines, including the now-empty `namespace VInductDecl'` wrapper) and replaced by
a pointer paragraph inside §1's own module comment.  `lake build Lean4Lean.Theory.Inductive.Decl
Lean4Lean.Verify.Inductive.WFPos`: **green, 212 jobs**.  Zero proof characters changed; the only text
edited inside the three docstrings was two cross-references that pointed at their old home
("§1's headline" → the statement it makes; "`Decl.lean`:241" → "the `ResidualClean` docstring above")
plus two line re-wraps to stay inside 100 columns.

### M6. Migration 1 landed, unconditionally
`Verify/Inductive/NoNestedAll.lean`: `MutualNamesGate`'s docstring and `def` deleted (13 lines,
quoted in §4 below); the eight theorems of `MutualNames.lean` §1/§2/§4 transplanted verbatim in
their source order under a new `/-! ### §3.1 addMutual's header loop, extracted -/`; four consumers
lost their `Gm` binder; four docstrings repaired; §4.2 retitled "The **one** gate".
`lake build Lean4Lean.Verify.Inductive.NoNestedAll`: **green, 196 jobs**.
`lake build Lean4Lean.Verify.Inductive.MutualNames`: **green, 197 jobs**, and its `#eval` firing
still prints the ✓ line (block accepted, duplicate/`_nested`/`safe` blocks rejected,
`check := false` accepted).

### M7. **C6 (0.75) RIGHT for code, WRONG for prose — and this is a finding I cannot fix.**
Nothing outside my four files *cites* any changed declaration, so no downstream code broke.  But two
files I do not own carry prose that HEAD `fca5b82` had already repaired to point at
`addMutual_noNestedEnv'` — the primed copy in `MutualNames.lean` — and that name no longer exists,
because edit 2 made the unprimed `addMutual_noNestedEnv` in `NoNestedAll.lean` say exactly what it
said.  Both are pure prose; neither breaks the build.  **Not edited — not my files.**

1. `Lean4Lean/Inductive/Add.lean`:1097-1099: *"The header loop's postcondition is now a **theorem**
   (`addMutual_header_post`, `Verify/Inductive/MutualNames.lean`) and the `mutualDefnDecl` branch
   stands **unconditionally** (`addMutual_noNestedEnv'`)."*  Both citations are now wrong in
   *location*: `addMutual_header_post` and `addMutual_noNestedEnv` are both in
   `Verify/Inductive/NoNestedAll.lean` §3.1, and the primed name is gone.
2. `Lean4Lean/Verify/Inductive/RestoreFaithful.lean`:424-425: *"`Verify/Inductive/MutualNames.lean`
   proves the postcondition (`addMutual_header_post`) and discharges the branch outright
   (`addMutual_noNestedEnv'`)."*  Same two errors.  Suggested replacement for both: *"the
   postcondition (`addMutual_header_post`) and the gate-free branch (`addMutual_noNestedEnv`) are
   both in `Verify/Inductive/NoNestedAll.lean` §3.1."*

## §3 What I removed, quoted before removing it (method rule 3)

### §3.1 `MutualNamesGate` — `NoNestedAll.lean`:344-356, deleted
```lean
/-- **The one residual on the `mutualDefnDecl` branch.**  `addMutual`'s header loop runs
`checkConstantVal env v.toConstantVal` on every member and rejects a repeated name, so it
establishes exactly this; what is missing is the *extraction*, an `M`-monad `forIn` induction with
the `found` accumulator threaded through three `if`s — the `Except`-level pattern of
`guardLoop_noNested` (`Verify/Inductive/RestoreFaithful.lean` §1.1) lifted to
`ReaderT Context (StateT State (Except Exception))`.

This is **unproved, not false**: every conjunct is a postcondition of a check the loop actually
performs (`Lean4Lean/Environment.lean`:86-104). -/
def MutualNamesGate : Prop :=
  ∀ {env env' : Environment} {vs : List DefinitionVal} {fuel : FuelConfig},
    addMutual env vs true fuel = .ok env' →
      (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧ (vs.map (·.name)).Nodup
```
The docstring's second paragraph is the reason this removal is not tidying.  "Every conjunct is a
postcondition of a check the loop actually performs" is *true*; "**unproved, not false**" is *not*
the right grade; and neither sentence is what stands between a reader and a proof.  The middle
conjunct `env.find? v.name = none` is unreachable at an environment carrying no `constants.WF`
hypothesis, and the surviving replacement (`addMutual_header_post`, which takes `mapWF`) is what the
statement should have been.  The proposition itself has not been lost: it survives, delta-expanded,
as the conclusion of `mutualNamesGate_of_contains` in `MutualNames.lean` §4.

### §3.2 `MutualNamesGateWF` and `mutualNamesGateWF` — `MutualNames.lean`:132-142, deleted
```lean
/-- **`MutualNamesGate` with the hypothesis its statement is missing.**  Everything else about it
is unchanged; this is the form that is a theorem, and the form the gate should have had.  See §6.1
for why the hypothesis cannot be dropped, and `docs/handoff-mutualnames.md` §3.2 for the two-line
`NoNestedAll.lean` edit that would make the existing gate suppliable. -/
def MutualNamesGateWF : Prop := …
/-- **The gate, discharged in the form that admits a proof.** -/
theorem mutualNamesGateWF : MutualNamesGateWF := fun mapWF h => addMutual_header_post mapWF h
```
Read before deleting, and the docstring is what licenses the deletion: it says in its own words that
this exists to support `docs/handoff-mutualnames.md` **§3.2**, the alternative my brief tells me not
to take.  Its content is `addMutual_header_post` eta-expanded; nothing is lost.

### §3.3 `addMutual_noNestedEnv'` — `MutualNames.lean`:113-128, deleted
16 lines, body identical to the post-edit `addMutual_noNestedEnv` in `NoNestedAll.lean` (that is
exactly what `handoff-mutualnames.md` §3.1's edit 2 *is*: `G h` → `addMutual_header_post hC.wf h`).
Keeping both would have been a literal duplicate statement in the same import closure.

### §3.4 `WFPos.lean` §1's three declarations — moved, not deleted
52 lines of declaration plus the 4-line `namespace VInductDecl'` wrapper.  Verbatim text is now in
`Theory/Inductive/Decl.lean`; the removed original is preserved in `git diff` and the whole group is
re-cited from `WFPos.lean` §1.1/§2 unchanged.

## §4 Statements: did any change meaning?

**One rendering changed; no proposition did.**  `mutualNamesGate_of_contains`'s conclusion was
written `MutualNamesGate`; that abbreviation no longer exists, so the conclusion is now the same
proposition written out in full (delta-expansion).  The proof term is character-for-character what it
was, which is the check that it *is* delta-expansion and not a restatement: a changed proposition
would not have accepted the old term.

Nothing else.  Four theorems lost a *binder* (`Gm : MutualNamesGate`), which strictly strengthens
them and is the point of the migration; a hypothesis-removal is not a meaning change in the sense
rule 5 forbids, because every old application is still derivable (`fun _ => new`) while the converse
is not.

**Arity and cone, before → after** (`scripts/exists.lean`, 476 modules, 2026-09-04):

| name | arity | cone |
| --- | --- | --- |
| `MutualNamesGate` | 0 → **gone** | 7301 → — |
| `addMutual_noNestedEnv` | 7 → 6 | 8145 → see M8 |
| `addDecl_noNestedEnv` | 8 → 7 | 9192 → see M8 |
| `addDecls_noNestedEnv` | 8 → 7 | 9195 → see M8 |
| `VEnv.NoNestedN.of_addDecl` | 11 → 10 | 9592 → see M8 |
| `VInductDecl'.spineArgs_drop_tyApp` | 4 → 4 | 633 → see M8 |
| `VInductDecl'.uniformOcc?_canonResult_snd` | 7 → 7 | 862 → see M8 |
| `VInductDecl'.residualClean_canonType` | 4 → 4 | 881 → see M8 |

## §5 My method's gaps, honestly

1. **My baseline `lake build` preceded my priors.** Rule 1 says §1 before any *edit*, and I made no
   edit before writing it — but I did make a *measurement*, and a stream that wanted its own priors to
   be honest about the tree's state would have written them from the source alone. It changes nothing
   here (M0 answers no prior about my work) and it is disclosed rather than backdated, but the clean
   order was available and I did not take it.
2. **Three of my four shape priors were about the *specs*, not about the world.** S1 asked "does the
   target exist"; S2/S3 asked "is this spec right"; S4 asked about opacity. That is a better ratio
   than the rounds this file follows, and S2 is the one that paid — but I got it by *reading line
   numbers*, which is luck disguised as method. The generalisable version is narrower and worth
   stating: **a migration spec that names an insertion point by line number is a claim about
   ordering, and ordering is the one thing a `lean_run_code` scratch check cannot validate.** Check
   the destination's declaration order for every identifier in the moved *statements*, not just for
   the tactics in the moved proofs — M14's own dependency audit listed four `Telescope` lemmas the
   proofs need and missed the two `VIndRecArg` definitions the statements need.
3. **I did not measure whether the transplant into `NoNestedAll.lean` needed reordering; I asserted
   S3 and then it happened to hold.** The right measurement was cheap — for each of the eight
   transplanted theorems, the maximum source line of its dependencies inside `NoNestedAll.lean`
   (max 341, insertion at 343). I checked this by eye against `handoff-mutualnames.md` §3.1's list
   rather than deriving it, so if that list had been incomplete I would have found out from `lake
   build` instead of from an argument. It was complete.
4. **I left one duplicated proof in place that I could have removed for free, and one I should not
   have.** `VIndCtor.skeleton_type` (`Decl.lean`:~1160 after the insert) still inlines exactly
   `spineArgs_drop_tyApp`'s five rewrites, and now it *could* cite the lemma; I did not change it,
   because a refactor round that starts rewriting proofs it was not asked to touch has stopped being
   a refactor round. That is a judgement, and it is arguable in the other direction: the whole point
   of the migration was to make that lemma citable from `Theory/`, and its first customer is 800
   lines below it in the same file.
5. **I cannot verify the two prose repairs M7 names.** They are in files I do not own, they are now
   wrong, and the only thing I can do is write down the exact replacement text. A future reader of
   `Inductive/Add.lean`:1099 will look for `addMutual_noNestedEnv'` and not find it.
6. **"No statement changed meaning" is checked structurally, not semantically.** My evidence is that
   the old proof terms still elaborate and the guards/census are unmoved — not that I re-derived each
   statement's intent. For a pure move that is the right standard; for the delta-expansion in §4 it is
   the *only* standard I have, and it is a strong one (a changed proposition rejects the old term).
7. **The `WFPos.lean` §6 axiom checks now cover three declarations the file no longer introduces.**
   I kept them deliberately (dropping them drops coverage) and said so in the file, but it means
   `#print axioms` in `WFPos.lean` is no longer a list of what `WFPos.lean` owns, and a future
   reader auditing "which module owns which axiom claim" will have to read the sentence I added.

### M8. Round-close numbers (2026-09-04, HEAD `fca5b82` + this round's edits)

| # | measurement | before | after |
| --- | --- | --- | --- |
| 1 | bare `lake build` | exit 0, **1662 jobs** | exit 0, **1662 jobs** |
| 2 | guard 1 | `exactly the 24 frozen axioms ✓` | identical |
| 2 | guard 2 | `within whitelist ✓ (proof INCOMPLETE: sorryAx present)` | identical |
| 2 | guard 3 | `implementation gaps within frozen list (2/2 remaining) ✓` | identical |
| 3 | census (`sorry-census-all.lean`, 476 modules) | **13** (pass A 13 / B 0) | **13** (pass A 13 / B 0), same 13 names |
| 4 | warnings from files I own | `Decl.lean` ×2 (`exists_indep` `sorry`; `henv` unreferenced) | the same 2, shifted by the insert (678→750, 1132→1204) |

The whole build's warning set is **identical**, 211 → 211 lines, once line/column numbers are
normalised — so nothing I did introduced or silenced a warning anywhere in the tree.

**Cones after, and C5 (0.8) is WRONG in its strict form:**

| name | module after | arity | cone before → after |
| --- | --- | --- | --- |
| `addMutual_noNestedEnv` | `Verify.Inductive.NoNestedAll` | 7 → **6** | 8145 → **8191** |
| `addDecl_noNestedEnv` | `Verify.Inductive.NoNestedAll` | 8 → **7** | 9192 → **9206** |
| `addDecls_noNestedEnv` | `Verify.Inductive.NoNestedAll` | 8 → **7** | 9195 → **9209** |
| `VEnv.NoNestedN.of_addDecl` | `Verify.Inductive.NoNestedAll` | 11 → **10** | 9592 → **9606** |
| `MutualNamesGate` | — | 0 → **NOT FOUND** | 7301 → — |
| `MutualNamesGateWF` | — | **NOT FOUND** | — |
| `addMutual_noNestedEnv'` | — | **NOT FOUND** | — |
| `forIn_ok_fresh` | `Verify.Inductive.NoNestedAll` (was `MutualNames`) | 9 | 597 → **597** |
| `addMutual_header_post` | `Verify.Inductive.NoNestedAll` (was `MutualNames`) | 6 | — → **8156** |
| `VInductDecl'.spineArgs_drop_tyApp` | `Theory.Inductive.Decl` | 4 | 633 → **633** |
| `VInductDecl'.uniformOcc?_canonResult_snd` | `Theory.Inductive.Decl` | 7 | 862 → **861** |
| `VInductDecl'.residualClean_canonType` | `Theory.Inductive.Decl` | 4 | 881 → **880** |
| `VIndField.residualClean_of_canon` (untouched, stays in `WFPos`) | `Verify.Inductive.WFPos` | 6 | 884 → **883** |
| `VInductDecl'.residualClean_of_recArgOf` (untouched, stays) | `Verify.Inductive.WFPos` | 6 | 1744 → **1746** |

C4 (0.85) is **RIGHT**: arity −1 on exactly four declarations, cones up by 14-46 as the gate binder
is replaced by a real proof term.

C5 predicted the moved cones would be *invariant*; they moved by −1, −1, 0 and (for an
**untouched** downstream consumer) +2.  **The source is byte-identical** — `diff` of the extracted
block against the original shows changes on **four docstring lines only**, no statement or tactic
line — so the deltas are not proof changes.  Measured cause: the cone counts *elaboration
auxiliaries* (`…match_1_5`, `…match_3.splitter`, `…match_3.eq_2`), which Lean generates and shares
**per module**.  `Lean4Lean.VInductDecl'.uniformOcc?_canonResult_snd.match_1_5` now lives in
`Theory.Inductive.Decl`, where before it lived in `Verify.Inductive.WFPos`, and its siblings are
shared differently on each side.  **So `scripts/exists.lean`'s cone number is not invariant under a
module move even when the source is byte-identical**, and a future round comparing cones across a
migration must not read a ±2 as a proof change.  That is an instrument caveat this repo did not have
written down, and it is the one thing worth keeping from C5 being wrong.

### Prior scoring, all twelve

| prior | outcome |
| --- | --- |
| **S1** (0.8) does the target already exist | **RIGHT, both halves** (M3). `spineArgs_drop_tyApp` was already proved *inline* in the destination file; the other two had no counterpart. |
| **S2** (0.85) is the work in the direction I think | **RIGHT, and it was the round's one correction to a spec** (M2): M14's insertion point is 20 lines above two definitions the moved *statements* need. |
| **S3** (0.7) measurement or docstring | **half RIGHT** (M2): M14's `can-cite` half reproduced exactly; its `lean_run_code` half was structurally blind to ordering. The mutualnames transplant needed no reordering, as predicted. |
| **S4** (0.9) what does it compare with, is it opaque | **RIGHT** (§3.1): the removal is mandatory rather than cosmetic, and no `divergences.md` entry is needed because no implementation behaviour changed. |
| C1 (0.8) green, 1662 jobs | **RIGHT** (M8) |
| C2 (0.9) three guards unchanged | **RIGHT** (M8) |
| C3 (0.9) census 13 | **RIGHT** (M8), same 13 names |
| C4 (0.85) arity −1 on four, cones grow | **RIGHT** (M8) |
| C5 (0.8) Migration 2 cones invariant | **WRONG in the strict form** (M8) — and the reason is worth more than the prediction |
| C6 (0.75) no edit needed outside my files | **RIGHT for code, WRONG for prose** (M7) — two files I do not own now cite a deleted name |
| C7 (0.85) the two §3.4 prose claims go stale | **RIGHT, but not in the way predicted**: they had *already* been repaired at HEAD, and my edits made the repairs wrong again (M7) |
| C8 (0.8) `WFPos` §6's sentence goes false | **RIGHT**; repaired in a file I own, checks kept |

## §6 The limits of this result

1. **This round proved nothing.**  Both migrations are moves.  The mathematics they carry
   (`addMutual_header_post`, `residualClean_canonType`) was proved by two earlier rounds; all I did
   was put it where its consumers can reach it and delete a `Prop` that misdescribed the situation.
2. **`InductiveMapGate` is untouched and is now the *only* gate on `addDecl_noNestedEnv`.**  Nothing
   here makes it cheaper; `docs/handoff-addinduct.md` still prices it at seven files.
3. **`VIndRecArg.exists_indep` is untouched, unattempted and undocumented by me.**  It is still the
   census hole in `Decl.lean`, still at 13-hole parity, and nothing I added is in its cone or routes
   through it.  My insert shifted its line number 678 → 750, which is the only effect I had on it.
4. **The migration does not make any `by decide` disappear.**  M14's stated payoff — the five
   `by decide`s in `accDecl_WF`/`mutDecl_WF`/`wDecl_WF`/`ntreeAux_WF'`/`tqAuxB_WF` becoming
   `residualClean_canonType (by …)` — is now *possible* and has **not been done**: those are files I
   do not own, and doing it would be a proof change in a refactor round.  The migration removes the
   layering obstruction; it does not collect the payoff.  Whoever collects it should re-check
   `can-cite.py` first, because the answer has changed today.
5. **`Verify/Inductive/WFPos.lean` §1 is now a pointer, not a section.**  Its §1.1, §2, §3, §4, §5
   and §6 are unchanged and still cite the three theorems from their new home.  A reader looking for
   "§1" in that file finds a paragraph explaining where it went.
6. **The gate's unprovability is still an argument from `partial def` opacity, not a Lean theorem.**
   Removing the gate does not settle its truth value; it removes a statement that could not have been
   settled either way.  `mutualNamesGate_of_contains` and `mutualNamesGate_at_wf` are what remains of
   the record, and `MutualNames.lean` §6.1 flags the argument's status.
