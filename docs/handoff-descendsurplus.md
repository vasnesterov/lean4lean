# handoff-descendsurplus — is `NormalEq.descend` surplus?

Stream: `descendsurplus`. Owns exactly `Lean4Lean/Theory/Typing/DescendSurplus.lean` and this file.
Everything else read-only. Started 2026-09-04.

## §1 PRIORS (written before any Lean interaction; never edited afterwards)

### 1.1 Claims in the brief I intend to VERIFY rather than trust

The brief has been wrong about files and namespaces before, so each of these gets a measurement.

- **P1.** `Lean4Lean.VEnv.NormalEq.descend` exists, lives in `Lean4Lean/Theory/Typing/ChurchRosser.lean`,
  and its statement begins at line 2009 (brief says 2009; my `grep` of the `theorem` keyword says
  **2011**, so the brief's line number is already suspect — verify with `lean_declaration_file` /
  `sed`). Verify: name resolves in the compiled environment, `own value is a hole: true`.
- **P2.** It has exactly **three** `sorry`s, all in the `.app`-node case. Verify by reading the
  declaration slice and counting `sorry` tokens inside its extent.
- **P3.** `Lean4Lean.VEnv.NormalEq.appDF_extra_of_descend` exists in the same file (grep says
  line 2201) and is the **only direct user** of `descend`. ChurchRosser.lean:1837 already asserts
  this ("`descend` has exactly **one** direct user"). Verify with `lean_references` at the
  declaration site of `descend`, not by grep — the brief explicitly warns docstring mentions
  dominate grep here, and indeed my grep found ~40 mentions of the string `descend` in
  ChurchRosser.lean of which the overwhelming majority are prose.
- **P4.** `Lean4Lean.VEnv.NormalEq.descendV` and `Lean4Lean.VEnv.NormalEq.appDF_extra_of_descendV`
  exist in `Lean4Lean/Theory/Typing/KDescend.lean`. Verify both names and both modules;
  the brief's namespace guess (`Lean4Lean.VEnv.NormalEq.*`) is the thing most likely misspelled.
- **P5.** `Theory/Typing/DescendAttack.lean` contains `refDescentLam_zero_const`,
  `refDescentLam_one_id`, `refDescentLam_one_F3`, `not_descendBranchLocalProofArg`,
  `not_descendBranchLocalEtaArg`, `not_descendBranchLocalEtaFun`, `descendBranch*_iff_not_ih`.
  Note: ChurchRosser.lean:1571 names the refutations `not_descendStatement`,
  `not_descendStatement_etaArg`, `not_descendStatement_etaFun` — **different names** from the
  brief's `not_descendBranchLocal*`. At least one of the two lists is wrong, or both sets exist.
  Verify both spellings with `exists.lean`; do not compose names.
- **P6.** The frontier is `Lean4Lean.VEnv.IsDefEq.church_rosser`. Verify it exists, get its exact
  statement, and verify that `descend` is in **its** cone (if it is not, the whole round changes:
  `descend` would already be surplus for `church_rosser` and the real consumer is elsewhere).
- **P7.** ChurchRosser.lean:1815 claims `descend` has **224** transitive users in 41 modules
  (`scripts/users.lean`, 2026-09-03), superseding an earlier figure of 193 — while :1837 still
  says "all 193 pass through a single [direct user]". Verify the current number myself with
  `scripts/users.lean`; treat both recorded numbers as stale.
- **P8.** `Lean4Lean.VEnv.NormalEq.appDF_extra_of_descendVK` exists too (ChurchRosser :1831,
  attributed to `KSite7App.lean` at :728). If it does, there may be **two** candidate
  replacements, and picking the wrong one is the obvious way to burn the round.

### 1.2 My own predictions (recorded so they can be scored)

- **Q1 (most likely outcome, ~55%).** `descend`'s only Lean consumer is
  `appDF_extra_of_descend`, whose only consumer in turn is one branch of the `NormalEq`
  machinery that `church_rosser` sits on. If `appDF_extra_of_descendV` (or `…VK`) has the
  *same conclusion* and only extra hypotheses that are discharge-able at that single call site,
  the re-derivation is a **copy of one case split with one call swapped**, and the honest
  deliverable is a `church_rosser_ofV` whose cone omits `descend`. I expect the mechanical
  obstacle to be that the case split sits inside a big mutual/`match` inside a large theorem I
  do not own, so re-deriving it means **duplicating that theorem into my file** — possibly
  several hundred lines — because I cannot refactor `ChurchRosser.lean` to expose a hook.
- **Q2 (the predicted failure mode, ~35%).** The consumer of `appDF_extra_of_descend` is
  *inside* the same recursive nest as `descend` itself (ChurchRosser :2282 calls
  `NormalEq.descend` and :2344 calls `NormalEq.appDF_extra_of_descend`, which smells like one
  mutual block). If `descend` and its consumer are mutually recursive, I cannot re-derive the
  consumer without re-deriving the recursion — i.e. copying the whole nest — and the round ends
  as a **sharp negative**: "descendV dominates descend pointwise, but the domination cannot be
  wired without an edit to ChurchRosser.lean", with that edit written verbatim.
- **Q3 (~10%).** `descendV`'s extra hypothesis ("the pattern has no `.app` node",
  per ChurchRosser :1790) is **not** available at the frontier — the frontier genuinely needs
  the `.app` case — and route (1) alone is insufficient exactly as :1795 warns
  ("route (1) alone is not enough"). Then `descendV` does **not** dominate `descend` and the
  answer is NO, with the missing side condition named. :1795 is the single line in the brief's
  supporting material that most threatens the task's premise, and the brief does not mention it.
- **Q4.** Whatever I produce, its cone will **not** be hole-free: I expect
  `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (named at ChurchRosser :726 as exactly the hole
  `appDF_extra_of_descendV` carries) and probably others. The claim I can hope to prove is
  "`descend` absent from the cone", not "hole-free", and I will state it that way.
- **Q5.** I predict the *consumer* question (step 6, `scripts/can-cite.py`) answers "zero users
  today": my file will be a leaf, since rewiring the real consumers means editing
  ChurchRosser.lean, which I do not own. I will say so plainly rather than dress it up.

### 1.3 Hard constraints I will not violate

- No edit to any file but my two. If a fix requires editing `ChurchRosser.lean`, `KDescend.lean`,
  or anything else, the edit goes in this handoff **verbatim** and I stop.
- No import of `Lean4Lean.Verify.*` from my `Theory/` file; checked with `scripts/layer-check.py`.
- Never edit `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.
- No `sorry` in my file. If I cannot close it, the file contains only what closes, and the
  residual is prose here.
- No state-changing git commands.

## §2 MEASUREMENTS (appended as made; §1 is never edited)

### 2.1 Names and cones (`scripts/exists.lean`, WATCH=`Lean4Lean.VEnv.NormalEq.descend`, population 462 built modules)

Quoted verbatim, names spelled as the script prints them:

```
FOUND       Lean4Lean.VEnv.NormalEq.descend
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 12, cone 3874
            own value is a hole: true; cone reaches sorryAx: true
            holes in cone: [IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS, NormalEq.descend]
            *** WATCHED IN CONE: [Lean4Lean.VEnv.NormalEq.descend] ***
FOUND       Lean4Lean.VEnv.NormalEq.appDF_extra_of_descend
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 24, cone 3979
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [... , NormalEq.descend]      *** WATCHED IN CONE ***
FOUND       Lean4Lean.VEnv.NormalEq.descendV
            module Lean4Lean.Theory.Typing.KDescend, arity 13, cone 3876
            holes in cone: [IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.NormalEq.appDF_extra_of_descendV
            module Lean4Lean.Theory.Typing.KDescend, arity 25, cone 3991
            holes in cone: [IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.NormalEq.appDF_extra_of_descendVK
            module Lean4Lean.Theory.Typing.KSite7App, arity 24, cone 4026
            holes in cone: [IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.IsDefEq.church_rosser
            module Lean4Lean.Theory.Typing.ChurchRosser, arity 7, cone 4383
            holes in cone: [IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified,
                            WF.rigidShapeUniqNS, NormalEq.descend]
            *** WATCHED IN CONE: [Lean4Lean.VEnv.NormalEq.descend] ***
```

**P1 verdict.** Confirmed except the line number: `descend`'s `theorem` line is **2011**, not
2009 (2009-2010 are the last two lines of its docstring). Q4 confirmed in advance: nothing here
is hole-free; `descendV`'s cone carries `forallE_inv_stratified` + `rigidShapeUniqNS`, exactly
as `KDescend.lean`'s own header says. **P4, P8 confirmed** — all three K-side names resolve, in
the modules the brief named.

### 2.2 The real call-site list (`lean_references`, not grep)

- **`NormalEq.descend`** (decl `ChurchRosser.lean:2011:9`) — `total: 3`, i.e. **2** uses:
  - `Lean4Lean/Theory/Typing/ChurchRosser.lean:2282` — inside `NormalEq.appDF_extra_of_descend`
  - `Lean4Lean/Theory/Typing/DescendRefute.lean:430` — `descendStatement_holds`, the
    anti-strawman check (`DescendStatement I := @VEnv.NormalEq.descend I`), not a proof consumer
- **`NormalEq.appDF_extra_of_descend`** (decl `ChurchRosser.lean:2201:9`) — `total: 2`, i.e.
  **1** use: `ChurchRosser.lean:2344`, the `appDF` × `extra` case of **`NormalEq.parRed`**
  (`ChurchRosser.lean:2297`).
- **`NormalEq.parRed`** (decl `ChurchRosser.lean:2297:9`) — `total: 7`, i.e. **6** uses:
  `KMeasure.lean:706`, `KSite7.lean:36`, `KCanonical.lean:583`, `ChurchRosser.lean:2425`
  (`NormalEq.parRedS`), `ChurchRosser.lean:2450` and `:2452` (`ParRedS.church_rosser`,
  `CRDefEq.trans`).

**P3 verdict: CONFIRMED.** One single Lean chokepoint. **P2 verdict: the brief's expectation
in step 1 ("consumers are few and all inside `ChurchRosser.lean`, reaching the outside world
through `church_rosser`") is CORRECT** for `descend` and `appDF_extra_of_descend`; it becomes
false one level up (`parRed` is cited from three K-modules directly), but that is above the
chokepoint and irrelevant to the route.

The full route is therefore, with no branching below `parRed`:

```
NormalEq.descend  (2011, 3 sorrys, REFUTED)
  → NormalEq.appDF_extra_of_descend  (2201)          ← the only consumer
    → NormalEq.parRed  (2297), case appDF × extra    ← the only consumer
      → NormalEq.parRedS (2419) / ParRedS.church_rosser (2436) / CRDefEq.trans (2467)
        → IsDefEq.church_rosser (2481)               ← the outside world's entry point
```

### 2.3 User counts (`scripts/users.lean`, 2026-09-04, population 462 modules / 27495 decls)

| seed | direct | transitive | modules |
|---|---|---|---|
| `NormalEq.descend` | 2 | **255** | 46 |
| `NormalEq.appDF_extra_of_descend` | 1 | 253 | 45 |
| `NormalEq.parRed` | 5 | 252 | 45 |
| `IsDefEq.church_rosser` | 9 | 243 | 42 |

**P7 verdict: both recorded numbers are stale.** `ChurchRosser.lean:1815` and
`DescendRestate.lean` say 224/41 (2026-09-03) and 193; today it is **255/46**. The "193" and
"224" sentences should say 255. `church_rosser`'s 9 direct users span
`HeadReduction`, `Verify/Typing/ConstSpine`, `ParamsBuild`, `KCanonical`, `ParamsWitness` — so
**`Verify/` really does consume it**, confirming P6's choice of frontier.

### 2.4 The frontier statement, exact (step 2 of the brief)

The chokepoint is one lemma, and it is the *only* thing the tree gets from `descend`. Written
out from `#check` (universe/notation expanded), `NormalEq.appDF_extra_of_descend`'s type is:

```
∀ [Params] {Γ : List VExpr} {f A B a b f₂ : VExpr},
  OnCtx Γ (IsType env univs) →
  Γ ⊢ f : A.forallE B → Γ ⊢ f₂ : A.forallE B → Γ ⊢ a : A → Γ ⊢ b : A →
  (∀ {e₂'}, Γ ⊢ f₂ ≫ e₂' → ∃ e₁', Γ ⊢ f ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
  (∀ {e₂'}, Γ ⊢ b  ≫ e₂' → ∃ e₁', Γ ⊢ a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
  ∀ {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'},
  Params.Pat p r → p.Matches (f₂.app b) m1 m2 →
  Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd →
  (∀ x, Γ ⊢ m2 x ≫ m2' x) →
  ∃ e₁', Γ ⊢ f.app a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst
```

I take **this**, not `church_rosser`, as the frontier to re-derive: everything between it and
`church_rosser` is already `descend`-free *as a proof*, and would only need re-deriving because
the intermediate lemmas physically sit in `ChurchRosser.lean` (a file I do not own). Re-deriving
the chokepoint is the whole mathematical content; the rest is transcription.

`scripts/shape.lean` with `HEADS="VEnv.ParRedS VEnv.NormalEq Pattern.RHS.apply VEnv.Params.Pat"`
reports **exactly two** constants in the tree with that shape —
`appDF_extra_of_descend` (arity 24) and `appDF_extra_of_descendV` (arity 25) — and **0 structure
fields**. So there is no third spelling of the frontier, and no `Prop`-on-`Params` wrapper for
it: `DescendRefute.lean` wraps `descend` (`DescendStatement`) and `DescendRestate.lean` wraps
`descendV` (`DescendStatementV`), but **nothing wraps the chokepoint**. That gap is what my file
fills.

### 2.5 The three candidate replacements, differenced

From `#check` (§2.1 names):

| | relation | extra hypothesis vs. `appDF_extra_of_descend` |
|---|---|---|
| `appDF_extra_of_descend` | `ParRed`/`ParRedS` | — (but proved from the refuted `descend`) |
| `appDF_extra_of_descendV` | `ParRed`/`ParRedS` | `hK : ∀ {Δ e e'}, KStep Δ e e' → ParRed Δ e e'` |
| `appDF_extra_of_descendVK` | **`ParRedK`/`ParRedKS`** | none |

So `appDF_extra_of_descendV` **is** the `descend`-free derivation of the frontier — modulo
exactly one hypothesis, `hK`, and nothing else. The domination question reduces to: is `hK`
available?

### 2.6 It is not: `hK` is refuted, and so is the frontier itself

`Lean4Lean/Theory/Typing/ParRedPropRefute.lean` already contains

- `VEnv.not_hK_of_propMajor` (`:130`) — `hK` is **false** at a registered `.app` rule whose
  major-premise slot is typed by a `Prop`;
- `VEnv.not_parRedStatement_of_propMajor` (`:75`) — and so is `ParRedStatement`
  (`KCanonical.lean:459`), `NormalEq.parRed`'s statement verbatim, *with no `hK` and no `KStep`
  at all*.

**Q3 was the right prediction, and the mechanism is worse than Q3 guessed.** It is not that
`descendV`'s `q.NoApp` side condition is unavailable at the frontier (it is genuinely
unavailable — the call site at `ChurchRosser.lean:2282` descends at the pattern `q₁.app q₂`,
where `NoApp` reduces to `False`; `Params.pat_app_noApp` frees it only for the two *children*).
It is that the bridge which replaces the whole-node descent — descend at `.var q₁` and fire the
rule with a K-step — needs `hK`, and `hK` is false.

**The new fact this round adds** (nothing in the tree stated it): the *frontier statement
itself* is refuted at the same witness, by the same three moves. I prove that in my file as
`not_appDFExtraStatement_of_propMajor`. It is strictly sharper than
`not_parRedStatement_of_propMajor`, because it refutes the **one lemma** that a "delete
`descend` and rewire" patch would have to re-prove, rather than the statement of the theorem
that consumes it. Consequence: **no `descend`-free derivation of the frontier exists — not from
`descendV`, not from anything** — while the reduction relation stays `ParRed`.


## §3 THE DELIVERABLE: `Lean4Lean/Theory/Typing/DescendSurplus.lean`

Imports `Theory/Typing/KSite7App` and `Theory/Typing/ParRedPropRefute` only.
`python3 scripts/layer-check.py`: **0 mentions of `DescendSurplus`** in either soft report; the
hard rule (`Theory/SetModel/` must not reach `Verify/`) is unaffected. Zero errors and zero
warnings (`lake env lean` silent; `lean_diagnostic_messages` returns `items: []`).

| declaration | arity | cone | `descend` in cone | holes in cone | `#print axioms` |
|---|---|---|---|---|---|
| `VEnv.AppDFExtraStatement` | 1 | 655 | no | none | `[propext, Quot.sound]` |
| `VEnv.appDFExtraStatement_holds` (anti-strawman) | 1 | 3981 | **YES, by design** | the 2 + `descend` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `VEnv.appDFExtraStatement_of_hK` | 2 | 3993 | **no** | `forallE_inv_stratified`, `rigidShapeUniqNS` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `VEnv.not_appDFExtraStatement_of_propMajor` | 22 | 3706 | **no** | the same 2 (via `ParRed.hasType` only) | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `VEnv.not_appDFExtraStatement_of_propMajor'` | 23 | **688** | **no** | **none** | **`[propext, Quot.sound]`** |
| `VEnv.not_hK_of_appDFExtra` | 22 | 3996 | **no** | the same 2 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `VEnv.AppDFExtraKStatement` | 1 | 655 | no | none | `[propext, Quot.sound]` |
| `VEnv.appDFExtraKStatement_holds` | 1 | 4028 | **no** | the same 2 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `VEnv.not_bridge_appDFExtraK_to_appDFExtra` | 22 | 4040 | **no** | the same 2 | `[propext, sorryAx, Classical.choice, Quot.sound]` |

### 3.1 The watched-cone output (step 4 of the brief), quoted verbatim

`WATCH="Lean4Lean.VEnv.NormalEq.descend" lake env lean --run scripts/exists.lean …`

```
population: 464 built modules
watching 1 declarations for cone membership

FOUND       Lean4Lean.VEnv.appDFExtraStatement_of_hK
            module Lean4Lean.Theory.Typing.DescendSurplus, arity 2, cone 3993
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.not_appDFExtraStatement_of_propMajor
            module Lean4Lean.Theory.Typing.DescendSurplus, arity 22, cone 3706
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.not_appDFExtraStatement_of_propMajor'
            module Lean4Lean.Theory.Typing.DescendSurplus, arity 23, cone 688
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.appDFExtraKStatement_holds
            module Lean4Lean.Theory.Typing.DescendSurplus, arity 1, cone 4028
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
FOUND       Lean4Lean.VEnv.not_bridge_appDFExtraK_to_appDFExtra
            module Lean4Lean.Theory.Typing.DescendSurplus, arity 22, cone 4040
            own value is a hole: false; cone reaches sorryAx: true
            holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS]
            watched declarations in cone: none of 1
```

Only `appDFExtraStatement_holds` — the anti-strawman check, whose whole job is to be
`@NormalEq.appDF_extra_of_descend` at the predicate — reports `*** WATCHED IN CONE ***`.
Everything else is `descend`-free by measurement, not by hope.

## §4 VERDICT

**`NormalEq.descend` is NOT surplus.** `descendV` dominates it at the frontier *up to exactly one
hypothesis*, `hK`, and `hK` is false; and the frontier statement it would have to deliver is
itself false at the same witness. So there is no `descend`-free derivation of what the tree gets
from `descend` — from `descendV` or from anything else — while the reduction relation stays
`ParRed`. Deleting `descend` is therefore **not** a text edit; it is a migration of the whole
confluence layer to `ParRedK`, and that migration currently costs `WeakNInvDS`
(`ParRedKGraded.lean:373`, `parRedKStatement_of_weakNInvDS`).

Scoring §1's predictions: **Q3 was right** (and it was the prediction the brief's own supporting
material contradicted, at `ChurchRosser.lean:1795`), though for a sharper reason than Q3 gave —
the obstruction is not `q.NoApp`'s unavailability but `hK`'s falsity, and beyond that the
frontier's own falsity. Q1 and Q2 were both wrong: the wiring was never the problem, because the
target is unprovable. Q4 was right (nothing is hole-free; the two ambient injectivity holes are
everywhere). Q5 was right — see §4.1.

### 4.1 Consumers (step 6), answered honestly

`python3 scripts/can-cite.py Lean4Lean.Theory.Typing.ChurchRosser
Lean4Lean.VEnv.not_appDFExtraStatement_of_propMajor'` →

```
  NO   defined in Lean4Lean.Theory.Typing.DescendSurplus
       Lean4Lean.Theory.Typing.ChurchRosser would have to gain Lean4Lean.Theory.Typing.DescendSurplus
```

**Zero users today, and here is why.** `DescendSurplus.lean` sits at the bottom of the import
order (it imports `KSite7App`, which is ~15 modules below `ChurchRosser`), so nothing that
consumes `descend` can cite it. That is correct and not fixable by me: the file's content is a
*refutation* plus a *bound*, and neither is meant to be consumed by a proof — it is meant to stop
a repair attempt. The one thing it would be cited by is the eventual `ParRedK` migration, which
would cite `appDFExtraKStatement_holds` as the statement it is migrating **to**.

### 4.2 Edits I would make elsewhere, and did not (I own only two files)

Both are prose corrections in files I do not own. Written verbatim, for the orchestrator:

1. **`Lean4Lean/Theory/Typing/ChurchRosser.lean:1815`** currently reads
   `` `descend` has **224** transitive users in 41 modules (`scripts/users.lean`, 2026-09-03; the **193** previously recorded here was taken over a smaller closure) ``.
   Replace `**224**` with `**255**` and `41 modules` with `46 modules`, and change the date to
   `2026-09-04`. (Measured today, population 462→464 modules / 27495 declarations.)
2. **`Lean4Lean/Theory/Typing/DescendRestate.lean`**, the "Consumer bound (b), the count"
   paragraph, says `` `KSite7App.lean`'s `NormalEq.appDF_extra_of_descendVK` is that chokepoint's *unconditional* replacement (`hK` discharged by `ParRedK.hK`) ``.
   Suggested replacement sentence:
   `` `KSite7App.lean`'s `NormalEq.appDF_extra_of_descendVK` is the unconditional replacement of the chokepoint's **`ParRedK` analogue**, not of the chokepoint itself: it proves `AppDFExtraKStatement`, and `DescendSurplus.lean`'s `not_bridge_appDFExtraK_to_appDFExtra` shows `AppDFExtraKStatement → AppDFExtraStatement` is false at the propMajor witness.  The chokepoint's own statement is refuted (`not_appDFExtraStatement_of_propMajor'`, `sorryAx`-free), so the rewiring is a migration, not a discharge. ``
   Its user counts (`193`, `224`) need the same 255/46 correction as (1).

**No frozen file needs any change**, and none was touched. `Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean` were not read for edit and not modified.

## §5 THE PRECISE RESIDUAL (step 5)

- **Which hypothesis of `descendV` cannot be supplied at the frontier?** Two, in a chain:
  1. `descendV`'s own `q.NoApp`. At the frontier the descent is at the pattern `q₁.app q₂`
     (`ChurchRosser.lean:2282`), where `NoApp` *is* `False`. `Params.pat_app_noApp`
     (`KDescend.lean`) frees `NoApp` for the two children only.
  2. So the V-route does not descend the node; it descends the function side at `.var q₁` and
     fires the rule with a K-step, which costs `hK : KStep Δ e e' → ParRed Δ e e'` — and
     `appDF_extra_of_descendV` carries exactly that and nothing else (`#check` diff, §2.5).
- **Is it a real gap or a missing bridge lemma?** A **real gap, and worse than a gap**: `hK` is
  refuted (`ParRedPropRefute.not_hK_of_propMajor`, and independently by this round's
  `not_hK_of_appDFExtra` via the frontier), and the frontier statement `hK` would buy is itself
  refuted (`not_appDFExtraStatement_of_propMajor'`, `sorryAx`-free). There is no bridge lemma to
  find; the reduction relation has to grow, which is the `ParRedK` migration.

## §6 GAPS IN MY OWN METHOD

1. **The refutations are conditional on an instance that does not exist.** Every hypothesis of
   `not_appDFExtraStatement_of_propMajor(')` is a property of the witness, but it needs a
   registered `.app` (ι-) pattern whose major-premise slot is typed by a `Prop`, and **no
   `Params` instance in this tree registers an `.app` pattern at all** (`PatWFIota.lean` is where
   that would come from). So "the frontier is false" means "false at instances of a shape the
   tree does not yet build", exactly as for `not_parRedStatement_of_propMajor`. `descend`'s own
   refutation is stronger in this one respect: it is at `refParams`, which exists. If someone
   later proves that *no* `Params` instance can register such a rule, my refutation goes vacuous
   and the round would have to be re-run. I did not attempt that direction and cannot rule it
   out. This is the single biggest caveat and I want it read as such.
2. **`hbrig` in the primed version is a strengthening I did not check for satisfiability.**
   `not_appDFExtraStatement_of_propMajor'` buys its clean axiom set by demanding the matched
   argument `b` be `ParRed`-normal. I argued (in the docstring) that this holds at the intended
   `b := Eq.refl` with rigid arguments, but I did **not** build a witness instance exhibiting it,
   the way `DescendRefute.lean` builds `refParams`. The unprimed version has exactly
   `not_parRedStatement_of_propMajor`'s hypotheses and no extra demand, at the cost of routing
   through `ParRed.hasType`; treat the pair as a bound, not as one theorem.
3. **I re-derived the frontier, not `church_rosser`.** §2.4 argues that everything between the
   chokepoint and `IsDefEq.church_rosser` is transcription — five lemmas in `ChurchRosser.lean`
   that are already `descend`-free as proofs. I did not transcribe them, because copying ~110
   lines of a file I do not own into mine would duplicate content two other streams are
   compiling against. If the orchestrator wants a literal `church_rosser_ofV`, that transcription
   is the remaining work — but it is *only* worth doing after `hK` or the `ParRedK` migration
   lands, since today the chain would still terminate at a refuted statement.
4. **Cone numbers move.** The population grew 462 → 464 built modules *while I was measuring*
   (two other streams compiling). Cone sizes here are consistent within a run but should not be
   compared digit-for-digit with `DescendRestate.lean`'s table, which was taken at a different
   closure — that is precisely the mistake that produced the 193/224/255 discrepancy in §2.3.
5. **`appDFExtraStatement_holds` deliberately imports the taint.** It is the only declaration of
   mine with `descend` in its cone. If someone later greps my module for `descend`-freeness at
   *module* granularity rather than declaration granularity, they will get the wrong answer.
   Cone measurement is per-declaration and must stay that way here.
6. **I built an `olean` for my module by hand** (`lake env lean … -o
   .lake/build/lib/lean/…/DescendSurplus.olean`) so that `scripts/exists.lean`'s
   filesystem-walked population would include it. I did not run `lake build`, to avoid colliding
   with the two concurrent streams. If the module is later added to a build target the olean will
   simply be rebuilt; nothing depends on the hand-built artifact.
