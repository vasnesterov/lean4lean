# handoff-addinductmap — scoping the CONSTANT-MAP side of the nested flip

Round scope: measure and characterise the constant-map side of the nested flip, i.e. everything
between "`TrIndDeclN` is constructible" and "`Lean4Lean.AddInduct` has a constructor". The
previous round (`docs/handoff-flipwiring.md` §3.3) reported four owed items and I am asked to
verify, size, order them, and give a hole verdict.

Ownership: I own EXACTLY this file and, if written, `Lean4Lean/Verify/Inductive/AddInductMapScope.lean`.
Everything else read-only. `Theory/SetModel/InterpMkPi.lean` belongs to a concurrent stream — a red
build there is that stream's work in flight, to be re-polled and reported, not investigated.

## §0 — PRIORS, written before the first instrument call

Brief's list to verify:
1. `Lean4Lean.VEnv.addInductR_ordered`
2. the `DeltaUnique` freshness repair, reportedly FALSE for nested blocks —
   `Lean4Lean.VEnv.iotaRulesR_major_not_fresh` (arity 12, cone 879, hole-free; brief says verified)
3. `VDecl.WF.induct → Lean4Lean.VEnv.AddNestedStep` generalisation
4. four case additions in files the previous round did not own

Calibration I am inheriting: the brief's *cone figures* have been exact all session (six for six
across three rounds); its *attributions* are wrong 7 of 11. So I should trust `879` and distrust
"in two files".

P1 (70%) — At least one of the four named items does **not** exist under the name given. The
    brief's own attribution record is 7-wrong-of-11, and item 1 (`VEnv.addInductR_ordered`) is
    named as if it were a single lemma while the prose says "three obligations", which is the
    signature of a name that is really a docstring wish-list entry rather than a declaration.
P2 (60%) — `Lean4Lean.VEnv.iotaRulesR_major_not_fresh` DOES exist with arity 12 / cone 879 and is
    hole-free, exactly as stated (numbers are the reliable half of this brief).
P3 (75%) — Item 2 is genuinely a **repair**, not a proof: i.e. there is a statement in the tree
    (in `Theory/Typing/DeltaUnique.lean` or its consumers) whose nested instance is refuted by
    `iotaRulesR_major_not_fresh`. This is the item worth flagging above everything else.
P4 (55%) — The corrected form of the freshness statement will be a *relativised* freshness:
    freshness against the pre-block environment plus explicit permission for the block's own
    companion/major names, rather than absolute `FreshIn`. I.e. the repair is a restatement whose
    proof then goes through, not an unprovable dead end.
P5 (65%) — The "four case additions" are `VDecl.WF`/`Ordered`-style inductive-family case arms
    that must be extended once a new constructor (`AddNestedStep` / `.induct` nested variant) is
    added — so they live in files that do case analysis over `VDecl` or over `Ordered`, and there
    will be MORE than two files (the brief says two).
P6 (50%) — `Lean4Lean.VEnv.AddNestedStep` exists as a definition/inductive, but the
    generalisation of `VDecl.WF.induct` to it does **not** exist under any name.
P7 (30%) — Something on this critical path IS one of the 13 census holes. My reasoning: the
    census holes have been characterised repeatedly as (a) known-false, (b) inert, (c) vacuous
    until the flip lands; the flip's *own* path is more likely ordinary open work — declarations
    that simply do not exist yet — than sorry-holes, because "no constructor" is the shape here,
    and a missing constructor is not a hole.
P8 (65%) — The critical path has ≥2 genuinely parallel branches: the ordering/typing obligations
    (item 1) and the freshness repair (item 2) should not depend on each other.
P9 (20%) — I will need to write Lean. The task says write it only where a claim needs it to be
    honest; the honest-claim risk here is the *refutation* in item 2, and the brief says that is
    already machine-checked, so I expect to be able to report from measurement alone.
P10 (85%) — Census will read 13 / NOT BUILT 0 if I build (i.e. I add no holes).

## §1 — MEASUREMENTS (appended one line per instrument call, as made)

**M1 — `exists.lean` on the four named items + the intended definition (population 450).**

| name | verdict |
|---|---|
| `Lean4Lean.VEnv.addInductR_ordered` | **FOUND**, `Theory/Inductive/NestedOrdered.lean`, arity 11, cone 1143, own value is a hole: false; cone reaches sorryAx: false; watched declarations in cone: none of 6 |
| `Lean4Lean.VEnv.iotaRulesR_major_not_fresh` | **FOUND**, `Theory/Inductive/NestedOrdered.lean`, arity 12, cone 879, hole false, sorryAx false, none of 6 — brief's figures **exact**, fourth round running |
| `Lean4Lean.VEnv.AddNestedStep` | **FOUND**, `Theory/Inductive/Restore.lean`, arity 5, cone 1015, hole false, sorryAx false, none of 6 |
| `Lean4Lean.AddInduct` | **FOUND**, `Verify/Environment/Basic.lean`, arity 5, cone 276, `[NO PROOF TERM: cone is type-constants only]`, none of 6 |
| `Lean4Lean.VEnv.AddInductStagesR` | **NOT FOUND** — the intended *definition* of `AddInduct` is named by something else, or does not exist |
| `Lean4Lean.VDecl.WF` | FOUND, `Theory/Typing/Env.lean`, arity 3, cone 3, `[NO PROOF TERM]`, none of 6 |

First correction to the brief already: **item 1 is not owed — it exists with a proof term and a
clean cone.** And the name the brief gave for `AddInduct`'s intended body does not resolve.

**M2 — the name correction.** `Lean4Lean.AddInductStagesR` **FOUND**, module
`Lean4Lean.Verify.Environment.InductR`, arity 7, cone 1014, hole false, sorryAx false, none of 6.
The brief's `Lean4Lean.VEnv.AddInductStagesR` is wrong — there is no `VEnv.` prefix. Also found:
`Lean4Lean.AddInductStages` (`Verify/Environment/Basic.lean`, arity 5, cone 819, hole false, none
of 6) — the **non-nested** analogue, which is the template `AddInduct` must follow.

**M3 — read `Lean4Lean/Verify/Environment/Basic.lean:106-160` (the `AddInduct` docstring).** It is
the authority the brief was paraphrasing, and it is *more* precise than the brief. Intended body,
verbatim from the docstring:

    def AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
      ∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂

The docstring's own "what remains" paragraph, after a correction it applied to itself, is: two
*theorems* — `VEnv.addInductR_ordered` and the `DeltaUnique` freshness repair — "**plus four
one-line case additions in two files this stream does not own; see
`docs/handoff-inductive-add.md` §5**". So the four case additions are *documented*, with a
pointer; item 4 is findable, not "four cases somewhere".

Also from this docstring, load-bearing for the hole verdict: `VEnvs.WF env` is **unsatisfiable**
for any `env` whose constant map holds an `.inductInfo` (`VEnvs.WF.no_inductInfo`,
`Verify/InductFlip.lean`), so `addDecl.WF`'s `inductDecl` branch is a **false** statement today,
not merely open.

**M4 — read `docs/handoff-inductive-add.md` §5 (the pointer the docstring gave), lines 835-960.**
This is the authority; it is more precise than the brief and it *contradicts the brief's count*.

§5.4 is titled "four one-line case additions in two unowned files", but its table — which the doc
says was obtained by a **measured** probe (add a clone constructor to `VDecl.WF`, build, collect
every `Alternative 'inductNested' has not been provided`, patch, rebuild until `Lean4Lean.Theory`
(96 modules) and `Verify.{Soundness,SafeFragment,Bridge}` were green, then `git checkout` revert)
— lists:

| file | sites | owned by that round? | what the nested case needs |
|---|---|---|---|
| `Theory/Typing/EnvLemmas.lean` | 1 (`VEnv.WF.ordered`) | yes | `addInductR_ordered` |
| `Theory/Typing/DeclRules.lean` | 1 (`WF'.defeq_isDeclRule`) | yes | `addInductR_defeqs_iff` + `IsDeclRule` for `iotaRulesR` |
| `Theory/Inductive/Nested.lean` | 5 (`VDecl.WF.le`, `WF'.exists_addInduct'`, `WF'.induct_eq_of_type_name` ×2, `WF'.iotaRule_provenance`) | yes | `addInductR_le` (exists); the rest restated |
| `Theory/Typing/DeltaUnique.lean` | 3 (`WF'.defEqHeads`, `WF'.keys`, `WF'.iotaTypes`) | **no** | §5.3 |
| `Theory/Typing/PatternRules.lean` | 1 (`WF'.ruleShape`) | **no** | `ruleShape_inductR` |

**Two things follow, and both correct the brief.**
(i) "**four case additions**" is the *unowned subset only* (DeltaUnique 3 + PatternRules 1 = 4).
    The total requirement is **eleven sites in five files**, seven of them in files that round
    *did* own and therefore never reported as owed.
(ii) The doc's own prose says "**nine** sites in five files" while its table sums to
    **1+1+5+3+1 = 11**. That is an arithmetic slip in the authority document, of exactly the
    kind that concealed `trCtorsLen` last round (the brief records "my field census was off by
    one … an arithmetic slip that concealed the live item"). I will treat 11 as the number and
    re-measure the site list independently.
(iii) §5.4's last line already denies the brief's sizing: "the ask on the unowned side is four
    `| inductNested … =>` arms — but they are **not one-line** until §5.2 and §5.3 are done".

Staleness warning on this doc: its §8 reports "**20** `sorry` tree-wide", and the current census
is 13, so it predates several rounds. Everything above must be re-verified against today's tree.

**M5 — read the live source, `Lean4Lean/Theory/Typing/Env.lean:18-50` and its section docstring
`:55-93`.** `VDecl.WF` today has **seven** constructors — `axiom`, `def`, `unsafeDef`, `opaque`,
`example`, `quot`, `induct` — and the `induct` arm is

    | induct : decl.WF env → env.addInduct' decl = some env' → VDecl.WF env (.induct decl) env'

No `inductNested`. The rule text sits in the docstring at `:70-75`, verbatim as §5.4 quoted it,
and `Env.lean:96-99` carries an `example` that machine-checks the name `VEnv.AddNestedStep`
*elaborates at this position in the import graph* (that was a real earlier blocker; it is gone).

The live docstring's own count at `:88-93` is "**four** proofs in two files this stream does not
own … **plus five** in `Theory/Inductive/Nested.lean` and one each in `EnvLemmas.lean` and
`DeclRules.lean`, which are owned", i.e. **4 + 5 + 1 + 1 = 11**. So the live source agrees with
the table's 11 and it is `handoff-inductive-add.md`'s *prose* ("nine") that is the slip. The
brief's "four" is the unowned subset, correctly transcribed but presented as the whole item.

**M6 — independent re-measurement of the case-addition sites (grep for `| induct` arms across the
tree, then `awk` back to the enclosing theorem to confirm each is a case-split over `VDecl.WF`).**
All thirteen confirmed as `VDecl.WF`-`induct` arms inside inductions on `VEnv.WF'`/`VDecl.WF`:

| file | line | enclosing theorem | owned by the flip streams? |
|---|---|---|---|
| `Lean4Lean/Theory/Typing/EnvLemmas.lean` | 151 | `Lean4Lean.VEnv.WF.ordered` | yes |
| `Lean4Lean/Theory/Typing/DeclRules.lean` | 185 | `Lean4Lean.VEnv.WF'.defeq_isDeclRule` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 235 | `Lean4Lean.VDecl.WF.le` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 252 | `Lean4Lean.VEnv.WF'.exists_addInduct'` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 270 | `Lean4Lean.VEnv.WF'.declared` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 307 | `Lean4Lean.VEnv.WF'.induct_eq_of_type_name` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 315 | `Lean4Lean.VEnv.WF'.induct_eq_of_type_name` | yes |
| `Lean4Lean/Theory/Inductive/Nested.lean` | 450 | `Lean4Lean.VEnv.WF'.iotaRule_provenance` | yes |
| `Lean4Lean/Theory/Typing/DeltaUnique.lean` | 480 | `Lean4Lean.VEnv.WF'.defEqHeads` | **no** |
| `Lean4Lean/Theory/Typing/DeltaUnique.lean` | 960 | `Lean4Lean.VEnv.WF'.keys` | **no** |
| `Lean4Lean/Theory/Typing/DeltaUnique.lean` | 1293 | `Lean4Lean.VEnv.WF'.iotaTypes` | **no** |
| `Lean4Lean/Theory/Typing/DeltaUnique.lean` | 1397 | `Lean4Lean.VEnv.WF'.keysNonempty` | **no** |
| `Lean4Lean/Theory/Typing/PatternRules.lean` | 576 | `Lean4Lean.VEnv.WF'.ruleShape` | **no** |

**Thirteen sites in five files, five of them in unowned files.** Two sites are newer than the
authority doc's probe and neither doc mentions them:

* `Theory/Inductive/Nested.lean:270`, `VEnv.WF'.declared` — added by the very round that ran the
  probe (its own §7 ledger says "`Theory/Inductive/Nested.lean` | received `VEnv.WF'.declared`"),
  so the probe measured the tree *before* its own edit. The count drifts as the tree grows.
* `Theory/Typing/DeltaUnique.lean:1397`, `VEnv.WF'.keysNonempty` — a **fifth** unowned site, so
  the brief's headline number is wrong in the direction that matters: **five unowned arms, not
  four**, and it will keep drifting.

Sanity check that constructing is not affected: `Verify/ClosednessPropagation.lean:325` and
`Verify/Inductive/AddDeclWF.lean:494` both *build* `.induct hwfD (hflip hadd) H`, and
`Verify/TypeChecker/EtaUnitRefute.lean:10,34,36,209` build `.induct decl_WF …`. Construction sites
are unaffected by a new constructor; only the 13 elimination sites are. And the docstring's claim
"nothing in `Verify/` case-splits on `VDecl.WF`" **re-verified true today** — every `Verify/` hit
is a construction.

**M7 — read `Lean4Lean/Theory/Inductive/NestedOrdered.lean` in full (317 lines).** This overturns
**two** of the brief's four items. The file is a running log of self-corrections and the brief was
reading an outdated entry of it.

**(1) Item 1 is not one theorem owed; it is a theorem that EXISTS plus three named hypotheses.**
`Lean4Lean.VEnv.addInductR_ordered` (`:67`) and `Lean4Lean.VEnv.addInductR_ordered'` (`:146`) are
both proved. `addInductR_ordered'` reduces `Ordered env'` to exactly three obligations, and the
first of the original four is discharged outright by `Lean4Lean.VEnv.addInductR_typeConstsC_wf`
(`:88`) — "`typeConstsC` only *removes* members". The three live ones, as literal hypotheses:

    (hctors) ∀ {e₁}, env.addConstList (D.typeConstsC K) = some e₁ →
               ∀ c ∈ D.ctorConstsCR R K, c.2.WF e₁
    (hrecs)  ∀ {e₁ e₂}, … → e₁.addConstList (D.ctorConstsCR R K) = some e₂ →
               ∀ c ∈ D.recConstsR R K, c.2.WF e₂
    (hrules) ∀ {e₁ e₂ e₃}, … → e₂.addConstList (D.recConstsR R K) = some e₃ →
               ∀ df ∈ D.iotaRulesRS R K, df.WF e₃

Conservativity is machine-checked: `Lean4Lean.VEnv.addInductR_ordered_nil` (`:163`) collapses the
three to what `addInduct'` already discharges at `K = []`, `R = D.idRestore` — *unconditionally*,
"since ruling 116d dropped the `D.Canonical` hypothesis this used to carry". So the three are about
the **restoration**, not about inductives.

**(2) ITEM 2 IS ALREADY DONE. The brief is reporting a repair that has LANDED.** `:207-211`,
verbatim:

> **LANDED.** `WF'.keys` now carries `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, and
> `keys_induct`'s key fact is discharged from the freshness of the key's *head* only — so the
> non-nested arm and `keysR_induct` finally have the same shape.

The repair's shape, for the record, because it is the interesting kind: `VEnv.KeyMajorUnique` was
not hard, it was **false** (`nfn_keyMajorUnique_false`: `[PFn.rec, PFn.mk]` vs `[NFn.rec_1,
PFn.mk]`, two distinct rules sharing a major). It was **replaced** by `VEnv.KeyUnique` (the whole
key determines the rule), which *is* preserved by a nested step (`VEnv.keysR_induct`, from
`Faithful` + `VIndRestore.KeysDistinct`) and is not refuted by the same witness (`nfn_keys_ne`);
the sole consumer was re-proved (`Pat.iota_rule_uniq_keyUnique`). `KeyMajorUnique` survives only
as a definition so the refutations have a subject. This all lives in
`Theory/Inductive/NestedKeys.lean`.

And the file states the consequence the brief missed (`:220-221`):

> So `addInductR_ordered'`'s three obligations — `hctors`, `hrecs`, `hrules` — are now the
> **only** thing the `inductNested` rule waits on.

`iotaRulesR_major_not_fresh` — the lemma the brief cites as *the repair* — is at `:305`, and it is
the **refutation that motivated** the repair, not an outstanding obligation. It is a three-line
proof (`let ⟨ci, hci, _⟩ := hf.ctor_agree …; ⟨ci, hci⟩`). Citing it as owed work inverts its role.

**M8 — `exists.lean` on the ten names the status entries cite (population 450).** All hole-free,
all `cone reaches sorryAx: false`, all `watched declarations in cone: none of 6`:

| name | module | arity | cone |
|---|---|---|---|
| `Lean4Lean.VEnv.ctorConstsCR_wf_of_np_zero'` | `Theory.Inductive.RestoreBridge` | 20 | 2534 |
| `Lean4Lean.VEnv.recConstsR_wf_of_np_zero` | `Theory.Inductive.NestedRules` | 14 | 2278 |
| `Lean4Lean.VEnv.iotaRulesRS_wf_of_np_zero` | `Theory.Inductive.NestedRules` | 15 | 2323 |
| `Lean4Lean.VEnv.ctorConstsCR_wf_of_substC'` | `Theory.Typing.ConstSubstNested` | 15 | 2453 |
| `Lean4Lean.VEnv.iotaRulesRS_wf_of_components` | `Theory.Inductive.NestedTele` | 7 | 1184 |
| `Lean4Lean.VEnv.keysR_induct` | `Theory.Inductive.NestedKeys` | 11 | 1610 |
| `Lean4Lean.VEnv.KeyUnique` | `Theory.Typing.DeltaUnique` | 1 | 434 |
| `Lean4Lean.VEnv.KeyMajorUnique` | `Theory.Typing.DeltaUnique` | 1 | 434 |
| `Lean4Lean.VIndRestore.IotaHargs` | `Theory.Inductive.NestedTele` | 6 | 914 |
| `Lean4Lean.VEnv.ctorConstsCR_wf_of_np_zero` (no prime) | — | — | **NOT FOUND** (the primed name is the real one) |

**The decisive line: all three of `addInductR_ordered'`'s obligations have a proved
parameterless case.** `hctors` → `ctorConstsCR_wf_of_np_zero'`; `hrecs` →
`recConstsR_wf_of_np_zero`; `hrules` → `iotaRulesRS_wf_of_np_zero`. The status entry that said
"`hrecs` is one bridge away" is itself stale — `NestedRules.lean` closed it (that file was
untracked at the session's start and is now in the tree). So the remaining gap on the whole
constant-map side is **`D.np > 0`**, not the obligations themselves.

**M9 — `shape.lean VEnv.AddNestedStep VEnv.Ordered` (population 450).** Exactly **2** constants in
the tree conclude something mentioning both heads, 0 of them structure fields:

* `Lean4Lean.AddInductN.ordered_of_obligations`, arity 10, `Verify/Inductive/FlipConstruct.lean`
* `Lean4Lean.InductiveDeclExamples.ntreeAux_ordered_via_residual`, arity **0**,
  `Verify/Inductive/FlipConstruct.lean` — an arity-0 witness, i.e. the `Ordered` half is already
  discharged at a real parameterised nested block

So the `AddNestedStep → Ordered` step is *not* unnamed work; it has a named reduction and a closed
instance. This is exactly the check the brief's own docstring warns about ("a name search invented
an absence once").

**M10 — read `Lean4Lean/Verify/Inductive/FlipConstruct.lean` §5-§10 (lines 186-610). THIS IS THE
BIGGEST CORRECTION OF THE ROUND: the constructor's payload is already written, proved, and
witnessed at a parameterised nested block.**

`Lean4Lean.AddInductN` (`FlipConstruct.lean:207`) is a `def` in a file the flip streams own:

    def AddInductN (m₁ : Lean.ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : Lean.ConstMap) (env₂ : VEnv) : Prop :=
      ∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂ ∧
        VEnv.AddNestedStep env₁ decl K R env₂

**The brief's stated intended body is WRONG, and so is `Basic.lean`'s docstring.** Both say
`∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂`. `FlipConstruct.lean:195-205` gives the reason
that is insufficient, and it is a soundness reason, not a stylistic one:

> `VEnv.AddNestedStep` is the abstract side, and it is **not** derivable from the fold: the fold is
> exact on the *names and types* the step declares, and says nothing about whether `R` is an honest
> restoration. **A lying `R` — one renaming a companion to a type it is not — passes the fold.**

So the correct body has **two** conjuncts. A flip that used the docstring's one-conjunct body would
admit a dishonest restoration.

All the Tier-1 arms are proved off it, each one line: `Lean4Lean.AddInductN.le` (`:228`),
`.map_wf` (`:231`), `.find?_shape` (`:234`), `.defeqs_and_anti_lie` (`:243`),
`.to_addNestedStep` (`:250`), `.to_addInductR` (`:255`).

And the payload is **constructed at a parameterised nested block**:
* `Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN` (`:392`) — `np = 1`, `uvars = 1`,
  `recUvars = 2`; assumes only `m.WF` and freshness at the four declared names; the map is *not*
  assumed empty.
* `Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN_ordered` (`:422`) — the payload **plus**
  `env'.Ordered`, i.e. what `VEnv.WF.ordered`'s nested arm needs, at this block.
* `Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN_nonvacuous` (`:474`) — inhabited with
  nothing assumed at all.
* `Lean4Lean.InductiveDeclExamples.ntreeAux_not_addInduct'` (`:444`) — the payload's
  `env₁.addInduct' ntreeAux ≠ some env'`, so `AddInduct.to_addInduct`
  (`Verify/Environment/Basic.lean:153`) is **false**, not unproved. This is a *third* frozen-adjacent
  consequence the brief's item list omits entirely.

**M11 — `FlipConstruct.lean` §10 (`:490-530`) and §10a (`:565-586`): the residual, and the hole
verdict, both already stated in the tree.**

`Lean4Lean.AddInductN.ordered_of_obligations` (`:541`, arity 10) is "the precise statement that
**nothing else** is missing": the payload supplies `D.WF env`, `R.OwnId D K` and the `addInductR`
equation from inside itself, so a caller holding the three obligations has `Ordered` with no
further input. It is honest about what it does *not* prove: a genuine converse ("`Ordered env'` →
the three obligations") "needs an inversion of the `addConstList` chain, which is **not** proved
here and is not claimed".

Anti-vacuity is designed in, not asserted: the obligations are stated at a **fixed** `K`/`R`, and
`:534-539` explains why a `∀ K R` form would be *vacuous* (it would demand `VConstant.WF` of the
constant lists a junk restoration produces, which is false, making the hypothesis set
unsatisfiable — "the defect `docs/vacuity-ledger.md` §0 is about").
`Lean4Lean.InductiveDeclExamples.ntreeAux_ordered_via_residual` (`:571`, arity 0) is the
inhabitation check at the same fixed `K`/`R`.

**The file's own §10 status paragraph, dated 2026-09-03, is the answer to (e) and I did not have to
derive it:**

> All three are theorems *in general at `D.params = []`*, and all three are theorems
> *hypothesis-free at `ntreeAux`* (arity 0: `ntreeAux_obligationA/B/C`, cones 3594/5407/5643).
> What is open is the general parameterful case, and each is an ordinary open theorem — **not** one
> of the thirteen holes.

> (B) and (C)'s general routes take `hσ : (R.csubst D K).WFD env e₃ D.recUvars`, whose `val` field
> is `VIndRestore.ValAt` — node 3 of `Verify/Inductive/RestrictStep.lean`'s cycle. …
> `valStrengthen_endpoints_clean` shows the latter is a **plain** instance of
> `VEnv.AxiomConservativityWF` ≡ `StrengtheningTarget`, one of the thirteen holes … So the general
> (B)/(C) routes have **no known entry other than that instance family** … but they are **not
> provably dependent on the hole**: `RestrictStep.lean` §3a discharges an instance of the family
> *with no hole at all*.

`VEnv.AxiomConservativityWF` and `VEnv.StrengtheningTarget` are two of `exists.lean`'s six WATCHED
declarations, so this is checkable by cone measurement and I do that next.

§10's general-route names differ from the ones the earlier `NestedOrdered.lean` entry gave —
`VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` for (B), `VEnv.iotaRulesRS_wf_of_hargsD` /
`_of_hargsD_of_barrier` for (C) — so the earlier entry's `iotaRulesRS_wf_of_components` is one
generation behind. Verifying both generations next.

**M12 — `exists.lean` on the general routes and the concrete-block obligations (population 450).**
Every one FOUND, hole-free, `cone reaches sorryAx: false`, **`watched declarations in cone: none of
6`**:

| name | module | arity | cone |
|---|---|---|---|
| `Lean4Lean.InductiveDeclExamples.ntreeAux_obligationA` | `Theory.Typing.ConstSubstNested` | 0 | 3594 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_obligationB` | `Theory.Typing.ConstSubstNested` | 0 | 5407 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_obligationC` | `Theory.Inductive.NestedTele` | 0 | 5643 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_addInductR_ordered` | `Theory.Inductive.NestedTele` | **0** | 5657 |
| `Lean4Lean.VEnv.recConstsR_wf_of_blocksD` | `Theory.Inductive.NestedTele` | 13 | 2372 |
| `Lean4Lean.VEnv.recConstsR_wf_of_entriesD` | `Theory.Inductive.NestedTele` | 13 | 2404 |
| `Lean4Lean.VEnv.iotaRulesRS_wf_of_hargsD` | `Theory.Inductive.NestedTele` | 16 | 3131 |
| `Lean4Lean.VEnv.iotaRulesRS_wf_of_hargsD_of_barrier` | `Verify.Inductive.FlipPriceCompose` | 17 | 3272 |
| `Lean4Lean.AddInductN.ordered_of_obligations` | `Verify.Inductive.FlipConstruct` | 10 | 1193 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN_ordered` | `Verify.Inductive.FlipConstruct` | 3 | 6995 |

**`ntreeAux_addInductR_ordered` is arity 0 and clean.** So `Ordered` after a nested step at a
**parameterised** (`np = 1`) real nested block is fully closed with no hypotheses, no hole, and no
watched declaration. The brief's item 1 is not merely proved-modulo-obligations; it is *closed at a
parameterised witness*.

Both generations of general-route names exist, so neither of my two sources was inventing a name.
The 2026-09-03 generation (`_of_blocksD`, `_of_entriesD`, `_of_hargsD`, `_of_hargsD_of_barrier`) is
the current one.

**Preliminary hole verdict (to be confirmed by (e) below): nothing measured so far touches one of
the six watched declarations.** Every cone above reports `none of 6`, and that includes
`VEnv.AxiomConservativityWF` and `VEnv.StrengtheningTarget`, the two the §10 paragraph names as the
family the *general parameterful* (B)/(C) routes have no other known entry to.

**M13 — grep for `to_addInduct` consumers (the sites the flip must rewire).** `AddInduct.to_addInduct`
(`Verify/Environment/Basic.lean:153`, `nomatch H`) is **false** at the payload
(`ntreeAux_not_addInduct'`), so every consumer must be rewired. Eight sites, all confirmed by grep:

| file:line | what consumes it |
|---|---|
| `Lean4Lean/Verify/Environment/Basic.lean:665` | `TrEnv'.wf`'s `induct` arm: `.induct h1 h2.to_addInduct` |
| `Lean4Lean/Verify/Environment/Basic.lean:718` | `TrEnv'.wf_noUnsafe`'s `induct` arm, same shape |
| `Lean4Lean/Verify/Environment/Basic.lean:889` | the `R10.Wit` witness assembly |
| `Lean4Lean/Verify/InductFlip.lean:31` | `VEnv.addInduct'_types H.to_addInduct hT` |
| `Lean4Lean/Verify/InductFlip.lean:80` | `VEnv.addInduct'_eq_some_iff.1 ⟨_, H.to_addInduct⟩` |
| `Lean4Lean/Verify/InductFlip.lean:353` | `addInduct'_recs` / `addInduct'_ctors` |
| `Lean4Lean/Verify/StructureBridge.lean:265` | `refine ⟨_, _, H, ?_, H.to_addInduct⟩` |
| `Lean4Lean/Verify/Inductive/StagesFiring.lean:360` | `refine ⟨_, H, H.to_addInduct, ?_⟩` |

**The two at `Basic.lean:665/718` are the ones that force the ordering.** They produce
`VDecl.WF env (.induct D) env'`, and the only nested-capable rule for that is
`VDecl.WF.inductNested`, which does not exist. So **`AddInduct`'s constructor cannot land before
`VDecl.WF` gains `inductNested`**, which cannot land before the 13 case arms of M6, one of which
(`EnvLemmas.lean:151`, `VEnv.WF.ordered`) needs `addInductR_ordered` at **fully general `np`**.

That is the true shape of the critical path, and it is a chain, not a list of four parallel items.

**M14 — read `Theory/Inductive/NestedTele.lean` §T15.3a (`:2185-2199`) and §T16.10-12
(`:3920-4000`): what the general parameterful case actually asks for, and a vacuity trap already
sprung inside it.**

§T15.3a records that the *earlier* generation of (B)'s routes is **vacuous above `np = 0`**:

> `Theory/Typing/ConstSubstNested.lean` §B proves that the `hσ` of `recConstsR_wf_of_blocks` and
> `recConstsR_wf_of_entries` — `(R.csubst D K).WF E₂ e₂ D.recUvars` … — is **false** at every
> parameterised block, because `CSubst.WF.const` *is* obligation (A)'s refuted syntactic bridge. So
> both closures above, and `recConstsR_wf_of_substC'` itself, are vacuous *in `hσ`* at `D.np ≥ 1`.

So `VEnv.ctorConstsCR_wf_of_substC'` — which `FlipConstruct.lean` §10's table still lists as (A)'s
"live general route" — is **vacuous at every parameterised block**. The live ones take
`CSubst.WFD`, not `CSubst.WF`: `recConstsR_wf_of_blocksD` / `_of_entriesD` (arity 13) and
`iotaRulesRS_wf_of_hargsD` (arity 16). `WFD` is what `ntree_csubst_WFD₂` actually proves at a
parameterised block. **This is a live inconsistency between two docstrings in the tree** and the
`_of_substC'` entry in `FlipConstruct.lean:503` should not be relied on.

The shape of the residual hypotheses, read off the signatures:
* (B) `_of_blocksD`: `hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars`, `he₂ : e₂.Ordered`, plus
  `hM`/`hQ` (`TeleDefEq` over motives and minors, both sides `substC`-ed) and `hbody`
  (per-block `IsDefEq` of the major-premise former). `_of_entriesD` is the same entrywise
  (`hmot`/`hmin`/`hbody`).
* (C) `_of_hargsD`: `hown`, `hat : R.SubstAt`, `hfr : R.SubstFree`, `hσc : Closed`,
  `hσ : WFD`, `hI : D.IotaCtx env`, `henv : e₃.Ordered`, `hpos`, and
  `hdata : ∀ q j C, D.ctorsAll[q]? = some (j, C) → R.IotaHargs D (R.csubst D K) e₃ j C`.
  `VIndRestore.IotaHargs` (`:3929`, arity 6, cone 914) is a four-conjunct bundle: one `TeleDefEq`
  over the ι-context plus `∃ A₀ v`, a `HasType` for the motive-partial application, and two
  `IsDefEq`s (the type conversion and the major-premise conversion) sharing that `A₀`.

§T16.12 also prices (C) at the witness honestly: `ntreeAux.ctorsAll` has three entries, ι-contexts
of lengths 8/6/8 (measured), and **all nine components move** (`ntree_iota_components_ne`, by
`decide`) — so no `TeleDefEq.rfl` discount applies anywhere. That is the honest size of (C) at one
small block.

`CSubst.WFD`'s `val` field is `VIndRestore.ValAt`, which is the node the §10 paragraph ties to the
hole family. Measuring that next.

**M15 — `exists.lean` on the hole-adjacency chain (population now **451** — one module more than
M1-M14; a concurrent stream landed a file mid-round, consistent with the brief's note that
`Theory/SetModel/InterpMkPi.lean` is in flight).**

| name | module | arity | cone | watched in cone |
|---|---|---|---|---|
| `Lean4Lean.VIndRestore.ValAt` | `Verify.Inductive.RestrictCompanion` | 5 | 397 | none of 6 |
| `Lean4Lean.VIndRestore.ValStrengthen` | `Verify.Inductive.RestrictStep` | 5 | 397 | none of 6 |
| `Lean4Lean.VIndRestore.restrictStep_entry` | `Verify.Inductive.RestrictStep` | 9 | 3257 | none of 6 |
| `Lean4Lean.VIndRestore.valStrengthen_endpoints_clean` | `Verify.Inductive.RestrictStep` | 14 | 1347 | **none of 6** |
| `Lean4Lean.CSubst.WFD` | `Theory.Typing.ConstSubstNested` | 4 | 7 `[NO PROOF TERM]` | none of 6 |
| `Lean4Lean.InductiveDeclExamples.ntree_csubst_WFD₂` | `Theory.Typing.ConstSubstNested` | 10 | 5301 | none of 6 |

All hole-free, all `cone reaches sorryAx: false`.

**A discrepancy to run down before I write the hole verdict.** `FlipConstruct.lean:513-517` says
`valStrengthen_endpoints_clean` "shows the latter is a **plain** instance of
`VEnv.AxiomConservativityWF` ≡ `StrengtheningTarget`, one of the thirteen holes". If its statement
were *about* those, they would be in its cone — `AxiomConservativityWF` and `StrengtheningTarget`
are two of the six WATCHED names. Its cone is 1347 and reports **none of 6**. So either the
docstring names the wrong lemma, or "clean" means the *opposite* of what the sentence reads as.
Reading the source next rather than guessing.

**M16 — read `Verify/Inductive/RestrictStep.lean:25-55` and `:185-218`, plus the body of
`valStrengthen_endpoints_clean` (`:331-345`). The discrepancy in M15 RESOLVES IN THE TREE'S FAVOUR;
the docstring is careful and I was reading it too fast.**

`valStrengthen_endpoints_clean`'s conclusion is `t.ConstsIn e₁.contains ∧ ci.type.ConstsIn
e₁.contains` — it discharges the *side condition* of the hole's statement, so its own type mentions
neither watched name and `none of 6` is exactly right. The "plain instance of
`AxiomConservativityWF`" claim is prose supported by `RestrictCompanion.lean` §4, not a claim about
this lemma's type.

The two paragraphs that matter for (e), verbatim, and they are the most carefully hedged prose I
have read in this tree:

> `restrictStep_entry` is the punchline: `D.ArgsTypedK K e₁ occ ↔ R.ValStrengthen D K e₂ e₁` — *the
> whole residual is one constant-strengthening step* … so it is a **plain** instance of
> `VEnv.AxiomConservativityWF`, which is provably equivalent to `StrengtheningTarget`, one of
> `UniqueTyping.lean`'s thirteen holes. Since `restrictStep_entry` is an `↔`, **no node of the cycle
> is a cheaper door.**

> **What this does NOT say, and the distinction matters.** Node 5 is an *instance* of
> `AxiomConservativityWF`, not that statement itself … A proof of the instance family need therefore
> not be a proof of the hole — and §3a exhibits an instance discharged with no hole at all, by
> `type_tac` on the concrete spine at the `NTree`/`List` witness.

And: "Nothing here proves the strengthening instance either: §2 *locates* the residual on the
recorded hole, it does not discharge it."

So the hole relationship is: **the general parameterful route's residual is provably equivalent (by
an `↔`) to an instance family of one of the thirteen holes, and that instance family is provably not
equivalent to the hole pointwise** (one instance is discharged hole-free). That is a sharper answer
than either "it is a hole" or "it is ordinary open work", and it is the honest one.

**M17 — `shape.lean VIndRestore.ValStrengthen VEnv.AxiomConservativityWF` (population 451).**

    0 constants in Lean4Lean conclude something mentioning all heads
    NOTHING -- and this IS meaningful, because heads were resolved to real constants.

**So the "plain instance of `AxiomConservativityWF`" link is prose, not a machine-checked
reduction.** Nothing in the tree derives `ValStrengthen` from `AxiomConservativityWF`, or states
their relationship as a theorem. The `↔` that *is* machine-checked (`restrictStep_entry`) relates
five nodes of the cycle to each other, not to the hole.

This cuts both ways and I will report both: (i) the hole-adjacency claim in `RestrictStep.lean` and
`FlipConstruct.lean` is weaker than it reads — it is a human judgement about statement shape, and
`shape.lean` finds no formal witness; (ii) *therefore nothing forces the path through the hole
either*, which strengthens the "ordinary open work" side of the verdict.

**M18 — `scripts/sorry-census-all.lean --run` (whole-tree, both passes).**

    BUILT: 453; in population but NOT BUILT: 1
    NOT BUILT: Lean4Lean.Theory.SetModel.InterpMkPi
    pass A: 450 modules; pass B (the `Replay` reverse closure): 3
    HOLES over the WHOLE built population, unioned across both passes: 13  (pass A 13, pass B 0)

**NOT BUILT is 1, and it is `Lean4Lean.Theory.SetModel.InterpMkPi` — the concurrent stream's file,
named in my brief as theirs and in flight.** Per the brief's instruction I do not investigate it; I
re-poll at round close and report. I wrote no Lean at the time of this measurement, so nothing here
is mine.

The thirteen, verbatim as the census prints them:

1. `Lean4Lean.TrProj.weak'_inv` [`Lean4Lean.Verify.Typing.Lemmas`]
2. `Lean4Lean.TypeChecker.Inner.inferProj.WF` [`Lean4Lean.Verify.TypeChecker.InferType`]
3. `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` [`Lean4Lean.Verify.TypeChecker.IsDefEq`]
4. `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` [`Lean4Lean.Verify.TypeChecker.IsDefEq`]
5. `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` [`Lean4Lean.Theory.Typing.Injectivity`]
6. `Lean4Lean.VEnv.IsDefEqU.weakN_iff` [`Lean4Lean.Theory.Typing.UniqueTyping`]
7. `Lean4Lean.VEnv.NormalEq.descend` [`Lean4Lean.Theory.Typing.ChurchRosser`]
8. `Lean4Lean.VEnv.WF.rigidShapeUniqNS` [`Lean4Lean.Theory.Typing.Injectivity`]
9. `Lean4Lean.VIndRecArg.exists_indep` [`Lean4Lean.Theory.Inductive.Decl`]
10. `Lean4Lean.addDecl.WF` [`Lean4Lean.Verify.Environment`]
11. `Lean4Lean.kernel_complete` [`Lean4Lean.Verify.Soundness`]
12. `Lean4Lean.kernel_sound` [`Lean4Lean.Verify.Soundness`]
13. `Lean4Lean.leanTT_equiconsistent_zfc_omega_inaccessibles` [`Lean4Lean.Theory.Equiconsistency`]

Cross-referencing against M1/M8/M12/M15: **every declaration I measured on the constant-map path
reports `cone reaches sorryAx: false`**, so no declaration on the path *contains* or *reaches* any of
the thirteen. Hole #6 (`IsDefEqU.weakN_iff`) is where `StrengtheningTarget` is recorded and is the
one the general parameterful route is *prose-adjacent* to (M16/M17). Hole #9
(`VIndRecArg.exists_indep`) is inductive-side and in `Theory/Inductive/Decl.lean`, but no path cone
reaches it. Hole #10 (`addDecl.WF`) is **downstream** of the flip, not upstream: its `inductDecl`
branch is a *false* statement today (`VEnvs.WF.no_inductInfo`), which the flip is what repairs.

**M19 — `exists.lean` + `shape.lean` on the nested counterpart for each of the 13 case arms.** For
each `_induct` helper I read its actual conclusion head out of the source first (so the `shape.lean`
heads are the real ones, not guesses), then queried by name *and* by conclusion shape. Names queried
and NOT FOUND: `VEnv.addInductR_defeqs_iff`, `VEnv.ruleShape_inductR`, `VEnv.iotaTypes_inductR`,
`VEnv.defEqHeads_inductR`, `VEnv.keysNonempty_inductR`. Conclusion-shape queries, all with heads
resolved to real constants (so `NOTHING` is meaningful):

| `shape.lean` heads | hits |
|---|---|
| `VEnv.addInductR` + `VEnv.IotaTypeDeclared` | **0** |
| `VEnv.addInductR` + `VEnv.IotaTypeNotKey` | **0** |
| `VEnv.addInductR` + `VEnv.KeysNonempty` | **0** |
| `VEnv.addInductR` + `VEnv.RuleShape` | **0** |
| `VEnv.addInductR` + `VEnv.DefEqHeadsDeclared` | **0** |
| `VEnv.DefEqHeads` | HEAD NOT A CONSTANT — the real conclusion is `DefEqHeadsDeclared ∧ DefEqHeadsUnique` (`DeltaUnique.lean:455-456`), which is why I re-read the source before querying |

Found, i.e. arms that are **already served**: `Lean4Lean.VEnv.keysR_induct` (M8) serves
`WF'.keys`; `Lean4Lean.VEnv.addInductR_le` (`Theory.Inductive.NestedHead`, arity 6, cone 1051,
hole-free, none of 6) serves `VDecl.WF.le`; `Lean4Lean.VEnv.addInductR_defeqs`
(`Theory.Inductive.NestedHead:522`, arity 8, cone 1047, hole-free, none of 6) is the **forward**
half of what `WF'.defeq_isDeclRule` needs — but that arm uses `addInduct'_defeqs_iff` as an **`↔`**
(`DeclRules.lean:185-188`, `rcases (addInduct'_defeqs_iff h2).1 h`), and the `↔` for `addInductR`
does not exist. So that arm needs the converse direction plus `VDefEq.IsDeclRule` for a *restored*
ι-rule.

**Result: of the 13 sites, 2 are served outright, 1 is half-served, 10 need new content.**

**M20 — grep for consumers of the four owned `Nested.lean` provenance arms.**
`Lean4Lean.VEnv.WF'.iotaRule_provenance` has **zero** consumers anywhere outside its own file (not
even a prose mention). `WF'.induct_eq_of_type_name` has one *prose* mention
(`Theory/Inductive/Companion.lean:298`) and no code consumer. `WF'.exists_addInduct'` is cited in
prose twice (`Theory/Inductive/Decl.lean:945`, `Theory/SetModel/AxiomsValidatedAudit.lean:16`).
`WF'.declared` has six prose citations and is load-bearing by design (it is what discharges
`VInductDecl'.Declared` from a history).

So three of the four `addInduct'`-provenance arms are **inert or nearly inert**, which changes their
size: an inert arm can be *narrowed* (restricted to the `induct` rule, i.e. left true by
construction) or deleted, rather than generalised. That is materially cheaper than "restate five
lemmas".

**M21 — read `Lean4Lean/Verify/Environment/AddDeclPath.lean:357-386`. The chain I derived in M13 is
already a THEOREM in the tree, and I nearly reported a derivation as my own finding.**

`Lean4Lean.not_addInduct_to_addInduct_of_flip` (`:374`) is machine-checked:

    theorem not_addInduct_to_addInduct_of_flip (hflip : AddInductFlip) :
      ¬ ∀ ⦃m₁ m₂⦄ ⦃env₁ env₂⦄ ⦃D⦄, AddInduct m₁ env₁ D m₂ env₂ → env₁.addInduct' D = some env₂

i.e. **under the flip, `AddInduct.to_addInduct` is not merely unproved but false**, proved from
`ntreeAux_addInductN_ordered`. Its docstring states the consequence in exactly the terms I reached
independently: "the flip cannot be installed while `VDecl.WF`'s only inductive rule is `induct`; it
needs the `inductNested` rule". And: "`Lean4Lean.VDecl.WF.inductNested` **does not exist** (checked
against the compiled environment, not by grep)".

Note this docstring repeats the **four**-site count (`defEqHeads`, `keys`, `iotaTypes`, `ruleShape`)
and so misses `keysNonempty` (M6) — the same stale figure propagated into a third file.

**M22 — IMPORT-GRAPH MEASUREMENT (python over every `import Lean4Lean.*` line, transitive closure).
THIS IS THE ROUND'S CRUX AND NO DOCUMENT IN THE TREE MENTIONS IT.**

For each of the 13 case-arm sites, I asked whether the module that *provides* the nested content is
upstream of the module that *needs* it:

| consumer (case-arm site) | provider of the nested content | verdict |
|---|---|---|
| `Theory/Typing/EnvLemmas.lean` (`VEnv.WF.ordered`) | `Theory/Inductive/NestedOrdered.lean` (`addInductR_ordered'`) | **CYCLE — provider is DOWNSTREAM of consumer** |
| `Theory/Typing/DeltaUnique.lean` (`WF'.keys`) | `Theory/Inductive/NestedKeys.lean` (`keysR_induct`) | **CYCLE — provider is DOWNSTREAM of consumer** |
| `Theory/Inductive/Nested.lean` (`VDecl.WF.le`) | `Theory/Inductive/NestedHead.lean` (`addInductR_le`) | **CYCLE — provider is DOWNSTREAM of consumer** |
| `Theory/Typing/DeclRules.lean` (`WF'.defeq_isDeclRule`) | `Theory/Inductive/NestedHead.lean` (`addInductR_defeqs`) | INCOMPARABLE (neither imports the other) |
| `Theory/Typing/PatternRules.lean` (`WF'.ruleShape`) | `Theory/Inductive/NestedHead.lean` | INCOMPARABLE |
| `Theory/Typing/EnvLemmas.lean` | `Theory/Inductive/Restore.lean` | **OK — provider upstream** |

**So the three case arms whose nested content already exists cannot cite it.** Every one of
`addInductR_ordered'`, `keysR_induct` and `addInductR_le` sits *below* the theorem that would need
it. This is invisible to `exists.lean` (which measures the whole compiled environment at once) and
invisible to every "does the lemma exist?" question, which is why four documents in a row have
listed these as done-or-nearly-done items.

The tree has already solved this problem **once**, and the solution is the precedent:
`Theory/Typing/Env.lean`'s docstring records that `VEnv.addInductR` and `VIndRestore.Faithful`
"lived downstream of this file" and were **moved** into `Theory/Inductive/Restore.lean`, which my
last row confirms *is* upstream of `EnvLemmas.lean`. `Env.lean:96-99`'s `example` is the
machine-checked nameability certificate for that move.

**Consequence for the critical path: there is a migration step, not present in any item list, that
must happen before any of the 13 arms can be written.** It is not one file: `addInductR_ordered'`
(and the three obligations' general routes it consumes), `keysR_induct`, `addInductR_le` and
`addInductR_defeqs` all have to become nameable at or above `Theory/Typing/EnvLemmas.lean` /
`DeltaUnique.lean` / `DeclRules.lean` / `PatternRules.lean`. `Restore.lean` is the established
landing zone and is already upstream of `EnvLemmas.lean`.

**M23 — `lean_run_code` nameability probes (scratch snippets, nothing written to the tree; this is
the same instrument `Theory/Typing/Env.lean:96-99` uses as an `example`, run at the *consumers'*
positions).** This turns M22's import-graph verdict into a machine-checked one and, more usefully,
splits the migration into "data" and "theorems".

*Probe 1 — at `import Lean4Lean.Theory.Typing.EnvLemmas`:*

    #check @Lean4Lean.VEnv.addInductR_ordered'   -- error: Unknown constant
    #check @Lean4Lean.VEnv.keysR_induct          -- error: Unknown constant
    #check @Lean4Lean.VEnv.addInductR_le         -- error: Unknown constant
    #check @Lean4Lean.VEnv.addInductR_defeqs     -- error: Unknown constant
    #check @Lean4Lean.VEnv.addInductR            -- OK
    #check @Lean4Lean.VEnv.AddNestedStep         -- OK
    #check @Lean4Lean.VEnv.addInduct_WF          -- OK  (the non-nested arm cited at :151 today)
    #check @Lean4Lean.VIndRestore.Faithful       -- OK
    #check @Lean4Lean.VInductDecl'.iotaRulesRS   -- OK
    #check @Lean4Lean.VInductDecl'.typeConstsC / .ctorConstsCR / .recConstsR  -- all OK

**So M22's cycles are confirmed against the compiled environment, not inferred from import lines —
and the good news is that ALL THE DATA IS ALREADY UPSTREAM. Only the theorems are downstream.**

*Probe 2 — `addInductR_ordered'`'s complete statement, obligations and all, written out at
`EnvLemmas.lean`'s position as a `Prop`-valued `example`: **it elaborates with no error.*** So the
statement is nameable exactly where it is needed; the migration is a *proof* move, not a data move,
and the target layer is bounded above by `Theory/Typing/InductiveLemmas.lean` (where
`VEnv.addInduct_WF`, the arm's current non-nested citation, lives).

*Probe 3 — at `import Lean4Lean.Theory.Typing.DeltaUnique`:* `keysR_induct`'s **statement**
elaborates fine, but two things are missing at that position:
`Lean4Lean.VEnv.keysR_induct` itself (Unknown constant) and `Lean4Lean.VIndRestore.KeysDistinct`
(`Theory/Inductive/NestedKeys.lean:228`) — the side condition its proof needs. Note the contrast
with `VIndRestore.KeysFree`, which *is* already at `Theory/Inductive/Restore.lean:889`, i.e. upstream.
**So `keysR_induct`'s migration needs one definition moved as well as the theorem: `KeysDistinct`
from `NestedKeys.lean` to `Restore.lean`, alongside its sibling `KeysFree`.** That is a concrete,
small, independent task and it is the single cheapest item anywhere in this scope.

`Theory/Inductive/Restore.lean` is upstream of **all five** consumer files (`EnvLemmas`,
`DeltaUnique`, `PatternRules`, `DeclRules`, `Nested`) and of `Theory/Typing/Env.lean`, measured; its
own import closure is 12 modules. `NestedOrdered.lean`'s closure exceeds it by 25 modules, four of
which are consumer files themselves — so the migration is dependency untangling, not `git mv`.

**M24 — round-close re-poll (I wrote no Lean into the tree; these are the tree's numbers, not mine).**
* whole-tree `lake build`: **Build completed successfully (1639 jobs)**, exit 0.
* `scripts/sorry-census-all.lean --run`: **BUILT: 456; in population but NOT BUILT: 0**;
  **HOLES over the whole built population, unioned across both passes: 13** (pass A 13, pass B 0).
  The `NOT BUILT: 1` of M18 (`Lean4Lean.Theory.SetModel.InterpMkPi`) has **cleared on re-poll** — it
  was the concurrent stream's work in flight, exactly as the brief said, and I did not investigate it.
* guard 1: `Axioms.lean declares exactly the 24 frozen axioms ✓`
* guard 2: `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
* guard 3: `checker cone implementation gaps within frozen list (2/2 remaining) ✓`
* `scripts/layer-check.py`: **exit 0**; hard rule ok (65 modules, none reaches `Verify/`); soft report
  unchanged at 4 pre-existing drift files (`CommutationLemmas`, `EtaGuardLand`, `NoConfRepair`,
  `StructEtaPrice`) — none of them mine.
* frozen files untouched: I edited **only** `docs/handoff-addinductmap.md`. No Lean file created or
  modified anywhere; the Lean I ran was `lean_run_code` scratch snippets (M23), which touch no file.

---

## §2 — (a) THE FOUR ITEMS, VERIFIED AND CORRECTED

**Three of the four are wrong as stated, and one is already done.**

### Item 1 — `Lean4Lean.VEnv.addInductR_ordered`: **EXISTS AND IS PROVED.** Not owed.
`Theory/Inductive/NestedOrdered.lean:67`, arity 11, cone 1143, hole-free, `none of 6` (M1).
`VEnv.addInductR_ordered'` (`:146`, arity 11) reduces `Ordered env'` to **three** hypotheses, the
fourth having been discharged outright (`addInductR_typeConstsC_wf`, `:88`).
`addInductR_ordered_nil` (`:163`) machine-checks conservativity at `K = []`, unconditionally.
And `ntreeAux_addInductR_ordered` (`Theory/Inductive/NestedTele.lean`, **arity 0**, cone 5657,
hole-free, none of 6) closes it at a real **parameterised** (`np = 1`) nested block with no
hypotheses at all (M12).
**Size: split in two, and the brief's single item conflates them.** The *theorem* is not a proof and
not a restatement — it is a **MIGRATION** (M22/M23): it exists, and the theorem that needs it cannot
see it. Its *three obligations at `D.np > 0`* are a genuine **PROOF**, done at `np = 0` in general and
done hypothesis-free at one parameterised block. §4 keeps these as separate steps (3 and 4) because
they are independent and can run in parallel.

### Item 2 — the `DeltaUnique` freshness repair: **ALREADY LANDED.** Not owed.
`NestedOrdered.lean:207-211`: "**LANDED.** `WF'.keys` now carries
`KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, and `keys_induct`'s key fact is discharged from the
freshness of the key's *head* only."
The repair was of the species the brief flags as most important, and it went the whole way:
`VEnv.KeyMajorUnique` was **false** (`nfn_keyMajorUnique_false`: `[PFn.rec, PFn.mk]` vs
`[NFn.rec_1, PFn.mk]`); it was **replaced** by `VEnv.KeyUnique`; the nested preservation was proved
(`VEnv.keysR_induct`, `Theory/Inductive/NestedKeys.lean`, arity 11, cone 1610, hole-free, none of 6);
the sole consumer was re-proved (`Pat.iota_rule_uniq_keyUnique`); `KeyMajorUnique` survives only so
the refutations have a subject.
`VEnv.iotaRulesR_major_not_fresh` — the lemma the brief names *as the repair* — is at
`NestedOrdered.lean:305`, arity 12, cone 879, hole-free (**the brief's figures exact, fifth round
running**), and it is the **refutation that motivated** the repair, a three-line proof, not
outstanding work. Citing it as owed inverts its role.
**Size: DONE.** What is left of it is a migration (`KeysDistinct` + `keysR_induct`, M23 probe 3).

### Item 3 — `VDecl.WF.induct → VEnv.AddNestedStep`: **REAL, and correctly described.**
`Lean4Lean.VDecl.WF.inductNested` **NOT FOUND** (M21, against the compiled environment).
`VEnv.AddNestedStep` exists (`Theory/Inductive/Restore.lean`, arity 5, cone 1015, hole-free).
`VDecl.WF` has seven constructors and no nested one (M5); the rule's exact text sits in
`Theory/Typing/Env.lean:70-75` and `Env.lean:96-99` machine-checks that the name elaborates there.
**Size: a RESTATEMENT (add one constructor) whose cost is entirely in its 13 fallout arms.**

### Item 4 — "four case additions in files that round did not own": **THIRTEEN sites in FIVE files,
FIVE of them unowned, and the number drifts as the tree grows.**
Measured independently (M6). The brief's "four" is the *unowned subset of a stale probe*: the probe
missed `Theory/Typing/DeltaUnique.lean:1397` (`VEnv.WF'.keysNonempty`), so the unowned count is
**five**, and it missed `Theory/Inductive/Nested.lean:270` (`VEnv.WF'.declared`) which the same round
*added after measuring*. Three documents now repeat the stale "four" (`handoff-inductive-add.md`
§5.4, `Theory/Typing/Env.lean:88-93`, `Verify/Environment/AddDeclPath.lean:368-371`), and
`handoff-inductive-add.md`'s prose says "nine" where its own table sums to eleven.
**Size: 2 arms served, 1 half-served, 5 needing genuinely new theorems, 5 restatements/narrowings
of arms that are inert or nearly inert (M20).**

### Item the brief omits entirely — and it is bigger than any of the four
`Lean4Lean.AddInductN` (`Verify/Inductive/FlipConstruct.lean:207`) **is the constructor's payload,
already written, with every Tier-1 arm proved and a witness at a parameterised nested block**
(M10). And the body the brief gives for `AddInduct` — `∃ K R, AddInductStagesR …` — is **wrong**,
as is `Verify/Environment/Basic.lean:118`'s docstring: the fold alone admits a **lying `R`**, so the
correct body carries `VEnv.AddNestedStep` as a second conjunct. A flip built to the brief's stated
body would admit a dishonest restoration.
Also omitted: `AddInduct.to_addInduct` becomes **FALSE**, machine-checked
(`Lean4Lean.not_addInduct_to_addInduct_of_flip`, `Verify/Environment/AddDeclPath.lean:374`, arity 1,
cone 7053, hole-free), with **eight** consumer sites to rewire (M13).

---

## §3 — (c) THE CASE ADDITIONS, NAMED TO FILE AND LINE

Thirteen `| induct …` arms over `VDecl.WF`, each confirmed by reading back to its enclosing theorem
(M6). Sized by what the nested arm actually needs (M19/M20):

| # | file:line | theorem | owned by flip streams | what it needs | size |
|---|---|---|---|---|---|
| 1 | `Lean4Lean/Theory/Typing/EnvLemmas.lean:151` | `Lean4Lean.VEnv.WF.ordered` | yes | `addInductR_ordered'` **migrated upstream**, then its three obligations at general `np` | **PROOF (the hard one)** + migration |
| 2 | `Lean4Lean/Theory/Typing/DeclRules.lean:185` | `Lean4Lean.VEnv.WF'.defeq_isDeclRule` | yes | the **`↔`** `addInductR_defeqs_iff` (only the forward `VEnv.addInductR_defeqs` exists, `NestedHead.lean:522`) + `VDefEq.IsDeclRule` for a restored ι-rule | proof (small) |
| 3 | `Lean4Lean/Theory/Inductive/Nested.lean:235` | `Lean4Lean.VDecl.WF.le` | yes | `VEnv.addInductR_le` (**exists**, `NestedHead.lean`, arity 6, cone 1051) — but it is DOWNSTREAM of this file (M22) | migration only |
| 4 | `Lean4Lean/Theory/Inductive/Nested.lean:252` | `Lean4Lean.VEnv.WF'.exists_addInduct'` | yes | conclusion is *about* `addInduct'`; two prose citations, no code consumer | restatement / narrowing |
| 5 | `Lean4Lean/Theory/Inductive/Nested.lean:270` | `Lean4Lean.VEnv.WF'.declared` | yes | same; load-bearing by design (discharges `VInductDecl'.Declared`) | restatement |
| 6 | `Lean4Lean/Theory/Inductive/Nested.lean:307` | `Lean4Lean.VEnv.WF'.induct_eq_of_type_name` | yes | `addInduct'`-provenance; one prose mention, no code consumer | restatement / narrowing |
| 7 | `Lean4Lean/Theory/Inductive/Nested.lean:315` | `Lean4Lean.VEnv.WF'.induct_eq_of_type_name` (second arm) | yes | as #6 | restatement / narrowing |
| 8 | `Lean4Lean/Theory/Inductive/Nested.lean:450` | `Lean4Lean.VEnv.WF'.iotaRule_provenance` | yes | **zero consumers anywhere** (M20) | narrowing or deletion |
| 9 | `Lean4Lean/Theory/Typing/DeltaUnique.lean:480` | `Lean4Lean.VEnv.WF'.defEqHeads` | **no** | nothing concludes `DefEqHeadsDeclared`/`…Unique` from `addInductR` (`shape.lean`: 0 hits) | **proof** |
| 10 | `Lean4Lean/Theory/Typing/DeltaUnique.lean:960` | `Lean4Lean.VEnv.WF'.keys` | **no** | `VEnv.keysR_induct` (**exists**) + `VIndRestore.KeysDistinct` migrated from `NestedKeys.lean:228` to `Restore.lean` | migration only |
| 11 | `Lean4Lean/Theory/Typing/DeltaUnique.lean:1293` | `Lean4Lean.VEnv.WF'.iotaTypes` | **no** | nothing concludes `IotaTypeDeclared`/`IotaTypeNotKey` from `addInductR` (0 hits) | **proof** |
| 12 | `Lean4Lean/Theory/Typing/DeltaUnique.lean:1397` | `Lean4Lean.VEnv.WF'.keysNonempty` | **no** | nothing concludes `KeysNonempty` from `addInductR` (0 hits). **This site is in no document.** | **proof** (should be the cheapest of the four) |
| 13 | `Lean4Lean/Theory/Typing/PatternRules.lean:576` | `Lean4Lean.VEnv.WF'.ruleShape` | **no** | nothing concludes `RuleShape` from `addInductR` (0 hits); needs `ruleShape_inductR` | **proof** |

Every "0 hits" above is a `shape.lean` conclusion-shape query with heads resolved to real constants,
run after reading each helper's actual conclusion out of the source — not a name search (M19).

Re-verified today and still true: **nothing in `Verify/` case-splits on `VDecl.WF`** — every `Verify/`
hit is a *construction* of `.induct …`, which a new constructor does not break (M6).

---

## §4 — (d) THE ORDERED CRITICAL PATH TO `AddInduct`'s CONSTRUCTOR

Marked **[P]** proof / **[R]** restatement / **[M]** migration (a species the brief's taxonomy has no
slot for and which turns out to gate three items) / **[D]** human decision.

**Step 0 — DONE, no work.** `AddInductN` payload, all six Tier-1 arms, the parameterised witness
(`ntreeAux_addInductN`, `…_ordered`, `…_nonvacuous`), `ordered_of_obligations`, and
`not_addInduct_to_addInduct_of_flip`. `Verify/Inductive/FlipConstruct.lean`, all hole-free.

**Step 1 [M] — move `VIndRestore.KeysDistinct` from `Theory/Inductive/NestedKeys.lean:228` to
`Theory/Inductive/Restore.lean`, beside its sibling `KeysFree` (`:889`).** The single cheapest item
in this whole scope; machine-checked as the missing piece by M23 probe 3. **Independent of everything.**

**Step 2 [M] — make `VEnv.keysR_induct` nameable at `Theory/Typing/DeltaUnique.lean`.** Needs Step 1.
Then case arm #10 is a one-liner. Its *statement* already elaborates at that position (M23 probe 3).

**Step 3 [M] — move `addInductR_stages`, `addInductR_typeConstsC_wf`, `addInductR_ordered`,
`addInductR_ordered'` to at-or-above `Theory/Typing/InductiveLemmas.lean`; likewise
`addInductR_le` and `addInductR_defeqs` out of `NestedHead.lean`.** Bounded above: M23 probe 2
machine-checks that `addInductR_ordered'`'s **complete statement, obligations included, elaborates at
`EnvLemmas.lean`'s position**, and all its data (`typeConstsC`, `ctorConstsCR`, `recConstsR`,
`iotaRulesRS`, `AddNestedStep`, `Faithful`) is already upstream. What is *not* bounded is the proof's
dependencies: `NestedOrdered.lean`'s import closure exceeds `Restore.lean`'s by **25 modules**, four
of which are consumer files. **Independent of Step 4** — the theorems are stated modulo the
obligations, so the migration does not wait on them.

**Step 4 [P] — the three obligations at `D.np > 0`.** The substantive nested-soundness content.
Done at `np = 0` in general (`ctorConstsCR_wf_of_np_zero'`, `recConstsR_wf_of_np_zero`,
`iotaRulesRS_wf_of_np_zero`) and done *hypothesis-free at `ntreeAux`* (`ntreeAux_obligationA/B/C`,
arity 0, cones 3594/5407/5643). Three parallel sub-branches over one shared prerequisite:
* 4a (A) `hctors` — beware: `ctorConstsCR_wf_of_substC'`, which `FlipConstruct.lean:503` still lists
  as the live route, is **vacuous at every parameterised block** (`NestedTele.lean:2185-2192`).
* 4b (B) `hrecs` — `recConstsR_wf_of_blocksD` / `_of_entriesD`, residual `hM`/`hQ`/`hbody` (or
  `hmot`/`hmin`/`hbody`).
* 4c (C) `hrules` — `iotaRulesRS_wf_of_hargsD`, residual `VIndRestore.IotaHargs` per ι-rule; priced
  at the witness as 3 rules × ι-contexts of length 8/6/8, **all nine components moving**.
* **4-shared: `CSubst.WFD`**, whose `val` field is `VIndRestore.ValAt` — the `RestrictStep.lean`
  cycle. Two concurrent streams are already on it (`StrengthenFamily.lean`, `ValAtParam.lean`).

**Step 5 [P/R] — the 13 case arms** (§3). Sub-parallel: #9, #11, #12, #13 are four **independent**
proofs needing only Step 3's migration, **not** Step 4. #3 and #10 fall out of Steps 3 and 2. #2 is a
small proof. #4–#8 are restatements/narrowings, and #8 has no consumers at all.

**Step 6 [R] — add `VDecl.WF.inductNested` to `Theory/Typing/Env.lean`.** One commit with Step 5.

**Step 7 [R] — `Verify/Environment/Basic.lean`: give `AddInduct` the two-conjunct body, delete
`to_addInduct` (false), rewire the eight consumers** (M13: `Basic.lean:665,718,889`,
`InductFlip.lean:31,80,353`, `StructureBridge.lean:265`, `StagesFiring.lean:360`).
**This is where `AddInduct` gets its constructor.**

**Step 8 [D] — the nine statements in rows 6–9** (`Verify/SafeFragment.lean`,
`Verify/Environment/Extension.lean`, `Verify/TypeChecker/{Reduce,WHNF,InferType,IsDefEq}.lean`) become
**false** when the flip lands, and they are the human's standing ruling. **Ask now, in parallel with
everything**: a green Step 7 is impossible without this decision, so it is a hard gate that no amount
of proving removes.

### The reordering that matters most

**Step 4 can be moved AFTER Step 7** if `VDecl.WF.inductNested` carries the three obligations as
premises rather than deriving them. Then case arm #1 is literally `addInductR_ordered'` applied to the
rule's own premises — the shape is already machine-checked as `AddInductN.ordered_of_obligations`
(arity 10, cone 1193, hole-free) — and the debt moves to whoever *builds* an `AddInduct` at a real
block, where it is still open at `np > 0` but no longer blocks the flip's structural landing.
`ordered_of_obligations`' own docstring warns why the obligations must stay at a **fixed** `K`/`R`
(a `∀ K R` form is *vacuous*), so the strengthened rule must be `∃ K R, AddNestedStep … ∧ (three
obligations at that K/R)`. **This is a design decision, not a proof, and it changes the critical path
from a chain into two mostly-independent halves.** I flag it rather than take it.

### Parallelism summary

| lane | contents | blocked by |
|---|---|---|
| L1 | Step 1 → Step 2 → arm #10 | nothing |
| L2 | Step 3 (migration) → arms #2, #3, #9, #11, #12, #13 | nothing |
| L3 | Step 4a / 4b / 4c over shared `CSubst.WFD` | nothing (two streams already on `WFD`) |
| L4 | arms #4–#8 (restate/narrow/delete) | nothing |
| L5 | Step 8 (human decision) | nothing — **ask immediately** |
| L6 | Steps 6, 7 | all of L1–L5 |

L1–L5 are five genuinely independent lanes. Only L6 serialises.

---

## §5 — (e) THE HOLE VERDICT

**Nothing on this critical path is one of the 13 census holes. It is all ordinary open work — with one
sharply-stated caveat that is neither "it is a hole" nor "it is not".**

The positive measurement: **every declaration I measured on the constant-map path reports
`cone reaches sorryAx: false` and `watched declarations in cone: none of 6`** — M1, M2, M8, M12, M15,
M19, M21, without exception. The six watched names include `VEnv.AxiomConservativityWF` and
`VEnv.StrengtheningTarget`, i.e. the two names by which hole #6 (`Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean`) is reached. So no path declaration reaches a hole and no path
declaration routes around one through a forbidden statement.

The caveat, stated as the tree states it (M16) rather than louder: `RestrictStep.lean`'s
`restrictStep_entry` is an **`↔`** showing the residual of Step 4's shared prerequisite is
*equivalent* to `VIndRestore.ValStrengthen`, and `RestrictStep.lean`/`FlipConstruct.lean` judge that to
be a **plain instance** of `AxiomConservativityWF ≡ StrengtheningTarget`, hole #6 — so "no node of the
cycle is a cheaper door". But the same paragraphs are explicit that node 5 is an *instance*, not the
statement, and `RestrictStep.lean` §3a discharges an instance of the family **with no hole at all**.
So the instance family is provably not equivalent to the hole pointwise, and whether it is strictly
weaker is open (a concurrent stream's question in `StrengthenFamily.lean`).

**And a measurement that weakens even the caveat:** `shape.lean VIndRestore.ValStrengthen
VEnv.AxiomConservativityWF` returns **0 constants** with both heads resolved to real constants (M17).
The "plain instance of the hole" link is **prose, not a machine-checked reduction** — nothing in the
tree derives one from the other or states their relationship as a theorem. That cuts both ways and I
report both: the adjacency claim is softer than it reads, and correspondingly nothing *forces* Step 4
through the hole.

Relation of the flip to the three hole categories the brief distinguishes:
* **known-false** — the flip's own path contains three refuted statements, all already refuted and all
  *repaired or scheduled*: `VEnv.KeyMajorUnique` (repaired, `KeyUnique`), `AddInduct.to_addInduct`
  (Step 7 deletes it), `CSubst.WF` at `np ≥ 1` (routes moved to `WFD`). Plus the standing
  `addDecl.WF`-`inductDecl` falsity, which is hole #10 and **downstream**: the flip is what repairs it.
* **inert** — case arm #8 (`WF'.iotaRule_provenance`) has zero consumers; arms #4/#6/#7 have prose
  citations only.
* **vacuous until the flip lands** — hole #10 (`Lean4Lean.addDecl.WF`) and, per
  `handoff-inductive-add.md` §6 rows 6–9, the `.WF` holes #2/#3/#4
  (`inferProj.WF`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`) sit behind `never_true`/`always_throws`
  theorems that the flip makes false. Those are **consequences** of the flip, in Step 8's decision, not
  prerequisites of it.

Hole #9 (`Lean4Lean.VIndRecArg.exists_indep`, `Theory/Inductive/Decl.lean`) is the only hole physically
inside the inductive machinery, and **no path cone reaches it**.

---

## §6 — PRIORS SCORECARD

| # | prediction | conf. | verdict |
|---|---|---|---|
| P1 | ≥1 of the four items does not exist under the name given | 70% | **TRUE, and stronger than predicted** — `VEnv.AddInductStagesR` does not resolve (no `VEnv.` prefix), and items 1 and 2 exist *as done work* rather than as owed work |
| P2 | `iotaRulesR_major_not_fresh` exists, arity 12, cone 879, hole-free | 60% | **TRUE**, exact. The brief's figures are now exact five rounds running |
| P3 | Item 2 is a repair, not a proof | 75% | **half-TRUE and the interesting half is the other one** — it *was* a repair of a false statement, and it **already landed**. I predicted the species correctly and the status not at all |
| P4 | the corrected statement is a relativised freshness, provable | 55% | **FALSE on the mechanism, TRUE on the outcome** — the repair was not to relativise freshness but to **replace the predicate** (`KeyMajorUnique` → `KeyUnique`) and use head-freshness only |
| P5 | the case additions live in >2 files and are `VDecl.WF`-arm extensions | 65% | **TRUE** — 13 sites in 5 files; and the brief's "four" is a stale unowned subset |
| P6 | `AddNestedStep` exists; the generalisation does not | 50% | **TRUE**, both halves |
| P7 | something on the path is one of the 13 holes | 30% | **FALSE** — and I was right to price it low; every path cone is `none of 6` and `sorryAx: false` |
| P8 | ≥2 genuinely parallel branches | 65% | **TRUE, and understated** — five independent lanes (§4) |
| P9 | I will need to write Lean | 20% | **FALSE**, and deliberately so: the round's crux is an *import-graph* fact, which no file I am permitted to own can test (I own only a downstream `Verify/Inductive/` path). I machine-checked it with `lean_run_code` scratch probes instead, which touch no file and risk no other stream's build. `AddInductMapScope.lean` was **not** created |
| P10 | census 13 / NOT BUILT 0 | 85% | **TRUE** on re-poll (M24); M18 caught `NOT BUILT 1` mid-round, the concurrent stream's file in flight |

**7 of 10 clean, plus two halves.** The instructive miss is P3/P4: I priced the *species* of item 2
correctly and its *status* not at all, because I trusted the brief's present tense. The brief's
figures were exact for the fifth round running and its attributions wrong for the eighth — which is
now less a calibration note than a rule: **read every claim in this area's briefs as "this was true
when someone wrote it", and re-poll the status separately from the shape.**

The thing I did not predict at all, and which is the round's actual finding: **a whole species of work
— import-graph migration — gates three of the items, is invisible to every existence measurement in
this repo, and appears in no document.** `exists.lean` and `shape.lean` both measure the compiled
environment *as a whole*, so a lemma that exists but cannot be seen from where it is needed reads as
"done" to both instruments. That is how four consecutive documents came to list `addInductR_ordered`,
`keysR_induct` and `addInductR_le` as available.

---

## §7 — TWO OBSERVATIONS ABOUT THE ROUND'S CONTEXT (not my results)

1. `git status` at round close shows two Lean files that were not in the tree when I started:
   `Lean4Lean/Verify/Inductive/CtorsLenGeneral.lean` and
   `Lean4Lean/Verify/Inductive/FragmentWiden.lean`, with `docs/handoff-ctorslen.md` and
   `docs/handoff-fragmentwiden.md`. By name those are the *translation*-side blockers
   `handoff-flipwiring.md` §3.3 ranked 1 and 2 (`trCtorsLen`; widening `ctorTr?` past the six-case
   fragment). They are other streams' work and I make no claim about them; the whole-tree build was
   green with both present (1639 jobs). If they land, the translation side is complete and **this
   scope becomes the entire remaining flip.**
2. `Lean4Lean/Theory/SetModel/InterpMkPi.lean` was `NOT BUILT` at M18 and built by M24. That is the
   concurrent stream named in my brief; I re-polled rather than investigated, as instructed.

## §8 — FROZEN FILES

No frozen file needs changing for anything in this scope, and I changed none.
`Verify/Soundness.lean`, `Verify/Axioms.lean` and `Verify/Guard.lean` are untouched (`git status`
shows only `docs/handoff-addinductmap.md` among my paths). One forward note for whoever executes
Step 7/8: the nine statements of §4 Step 8 live in `Verify/SafeFragment.lean`,
`Verify/Environment/Extension.lean` and `Verify/TypeChecker/{Reduce,WHNF,InferType,IsDefEq}.lean` —
**none of which is frozen** — so Step 8 is a human *ruling*, not a frozen-file edit request. Nothing
in this round produces a frozen-edit request.
