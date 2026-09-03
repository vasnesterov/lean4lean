# handoff — the remainder of the nested flip (`ArgsTypedK` at `e₂`, and the `ResultSortInhab` residue)

Round owner files: `Lean4Lean/Verify/Inductive/FlipRemainder.lean` (new), this file (new).
Everything else read-only — in particular `TrSpineProducer.lean`, `SpineClosedLand.lean`,
`StrengthenFamily.lean`, `SortWitEnv.lean`, `RestoreFaithful.lean`,
`Verify/Environment/InductR.lean`. `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` FROZEN — not edited, not to be edited. No state-changing git.
`docs/vacuity-ledger.md` not touched.

## §0 — Brief as received (2026-09-04), figures UNVERIFIED

Written before any Lean ran, per standing rule (eleven API crashes this session; the only round
that wrote no handoff first is the only one whose report was lost).

Context as given: `TrIndDeclN.trSpine` is a field, and the datum three obligations bottomed out
in is produced in general, hole-free, by
- `Lean4Lean.VIndRestore.trSpine_of_resultSortInhab` (claimed arity 21, cone 3345)
- `Lean4Lean.trIndDeclN_of_succLevel` (claimed arity 20, cone 3348)
- `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine` (claimed arity 0, cone 5834)

Reportedly remaining (per `docs/handoff-trspineproducer.md` §4), to verify not believe:

1. **`ResultSortInhab` residue** — blocks with `D.lvl = .param i`, no telescope binder at that
   level, in an environment with **no `Sort u`-valued constant**. Last conjunct claimed live:
   `Verify/Inductive/SortWitEnv.lean` refutes `Lean4Lean.VEnv.SortWitness` at the environment
   this corner runs at, via `Lean4Lean.not_sortWitness_of_restrictStepCfg₃` (claimed arity 0,
   cone 3521, hole-free). For such blocks the `↔` reportedly says the cost is exactly the
   forward direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`.
2. **The datum at `e₂`** (`ArgsTypedK K e₂ occ`), carried as a premise. General extraction
   reportedly `Lean4Lean.VInductDecl'.WF.recField_canonResult`, with the last step to
   `ArgsTypedH` existing only at two concrete witnesses.

TASK as received:
- (a) item 2 first: produce the datum at `e₂` in general, or reduce to the smallest sufficient
  premise with an `↔`. Say precisely what the "last step to `ArgsTypedH`" needs and whether it
  generalises.
- (b) item 1: is the residue **reachable at all**? A block with `D.lvl = .param i`, no binder at
  that level, arising from a real `Lean4Lean.addDecl` history, in an environment declaring no
  `Sort u`-valued constant. If no such block can arise, the residue is empty for a reason with
  nothing to do with `weakN_iff` — the most valuable finding available. If it can arise, exhibit
  one.
- (c) state exactly what remains of the flip, separating what I own from what is owned elsewhere
  (`Built`/`FreshIn`/`tyLvls`-WF in `RestoreData`, `Faithful` in `RestoreFaithful.lean`).
- (d) arity-0 existentially-closed witness at `Lean4Lean.InductiveDeclExamples.ntreeAux`
  (`Theory/Inductive/NestedHead.lean:624`, `uvars = 1`, `params = [.sort (.succ (.param 0))]`),
  through general theorems not block-specific lemmas. `nfnAux` is degenerate; must not become it.
- (e) round-close: whole-tree `lake build` green, census **13 and NOT BUILT 0**, three guards,
  zero in-repo section-variable warnings. Report census first if it moves.

Forbidden / WATCHED IN CONE statements: `Lean4Lean.VEnv.HasArgs.of_mkApp`,
`Lean4Lean.VEnv.IsDefEq.uniq`, `Lean4Lean.VEnv.IsDefEq.uniqU`,
`Lean4Lean.VEnv.AxiomConservativityWF`, `Lean4Lean.VEnv.StrengtheningTarget`,
`Lean4Lean.VEnv.SortWitness`. A clean `sorryAx` line does not clear them. Report BOTH lines for
every declaration claimed.

## §1 — Pre-flight, re-measured myself (`scripts/exists.lean`, population 437 built modules)

Every figure in §0 was re-measured before any Lean was written.  **The brief's figures are all
correct.**

| name | arity | cone | hole | WATCHED IN CONE |
|---|---|---|---|---|
| `Lean4Lean.VIndRestore.trSpine_of_resultSortInhab` | 21 | 3345 | no | none of 6 |
| `Lean4Lean.trIndDeclN_of_succLevel` | 20 | 3348 | no | none of 6 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine` | 0 | 5834 | no | none of 6 |
| `Lean4Lean.not_sortWitness_of_restrictStepCfg₃` | 0 | 3521 | no | **`[VEnv.SortWitness]`** |
| `Lean4Lean.VInductDecl'.WF.recField_canonResult` | 15 | 915 | no | none of 6 |
| `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | 11 | 3231 | **YES** | none of 6 |
| `Lean4Lean.VEnv.SortWitness` | 1 | 19 | no | **`[VEnv.SortWitness]`** |

`recField_canonResult` lives in `Verify/Inductive/ArgsTypedSupply.lean` (the brief gave no
arity/cone for it).

### The one figure the brief got structurally wrong, and it decided the round

The brief (inheriting `TrSpineProducer.lean` §4 item 2) says the datum at `e₂` "comes from `D.WF` +
`stage₂`".  Checked at the source: `RestrictStepCfg.stage₂` is literally
`env.addIndTypes D = some e₂`, i.e. **`e₂` *is* the environment `VInductDecl'.WF.ctors` is staged
at**.  So the environment mismatch `ArgsTypedSupply.lean` §9 records ("the two are incomparable, so
§5's supply and §2.1's consumer do not compose in general") is a statement about §8.7's consumer at
stage 2 of `AddInductStagesR` — it does **not** apply to this obligation.  Item 2 therefore has no
environment obstruction at all, only telescope arithmetic.

## §2 — Item 2 (a): the datum at `e₂`

**Reduced to one `HasArgs` per companion member, with an `↔`, hole-free.**

`Lean4Lean.VInductDecl'.argsTypedK_iff_hargs` (arity 9, cone 666) says: under the syntactic,
environment-free side condition `Lean4Lean.VInductDecl'.OccTeleAgree` (arity 3, cone 644 — each
foreign constructor's parameter telescope agrees with the foreign member's; `ArgsTypedSupply.lean`
§8's condition, satisfied by `decide` at both witnesses),

    D.ArgsTypedK K e₂ occ  ↔  ∀ j T, D.types[j]? = some T → T.name ∈ K →
      e₂.HasArgs D.uvars D.params.reverse
        (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 (occ j).args

Two of the three components of `ArgsTypedH` are gone: `ctor` collapses into `ty` by the side
condition, and **`lvls` is not assumed at all** — it is read off the configuration
(`RestrictStepCfg.lvls` composed with `Built.tyLvls`).  The forward direction needs no side
condition.

**And the one remaining `HasArgs` is produced from `D.WF` in general**, not per witness:
`Lean4Lean.VNestedOcc.argsTypedH_ty_of_recField` (arity 18, cone 944, hole-free).

### What "the last step to `ArgsTypedH`" needs, precisely — and it does NOT generalise

`recField_canonResult` types `r.canonResult D i` in the context

    r.binders.reverse ++ ((C.fields.take i).map (·.type)).reverse ++ D.params.reverse

while `ArgsTypedH.ty` wants the typing in `D.params.reverse` **alone**.  For `i = 0` with
`r.binders = []` those two contexts are *equal lists*, which is why the theorem above is
unconditional there; the remaining premises are then equations, not judgements
(`(splitPis np …).1 = [.sort D.lvl]` and `N.args = [r.canonResult D 0]`).

For `i > 0` the earlier field types are in the way and removing them is **strengthening — the
forward direction of `weakN_iff`**, the same statement item 1 was said to bottom out at.  The
substitute-an-inhabitant trick that discharges strengthening elsewhere in this corner is **not**
available here: the binders being removed are constructor *field* types, which may be uninhabited.
So `ArgsTypedSupply.lean` §9's coincidence 1 ("the field must sit at declaration position 0") is now
**priced**: it is exactly one `weakN_iff` instance per intervening field.

Coincidences 2–4 of that list are absorbed into the theorem's two equational premises and are
therefore side conditions rather than obstructions.

**Non-vacuity, checked**: `Lean4Lean.InductiveDeclExamples.ntree_hargs_of_recField` (arity 3, cone
1992) fires the general theorem at `ntreeAux`/`listOcc`, and
`Lean4Lean.InductiveDeclExamples.ntree_argsTypedK_of_recField` (arity 6, cone 3489) composes it with
the `↔` to get `ArgsTypedK ntreeK env₂ (fun _ => listOcc)` — the same conclusion as the
block-specific `listOcc_argsTypedH_of_wf`, reached through general theorems.

## §3 — Item 1 (b): the residue was in the WRONG PLACE

**The residue's environment conjunct — "no `Sort u`-valued constant" — was never the obstruction,
and the `SortWitness` refutation is not load-bearing for it.**

`ResultSortInhab` was being discharged at the **pre-block** environment `env`.  The bypass does not
need it there: it needs the junk value typed at **`e₁`**, and `e₁ = env.addIndTypesC D K` **declares
the block's own non-companion members**.  A member of the block is a `Sort D.lvl`-valued constant
*after saturation* — `VIndType.WF.canon` makes its type `Π params indices, Sort D.lvl`, and
`ResultSortInhab`'s context `T.indices.reverse ++ D.params.reverse` is exactly what supplies the
parameters.  **The block supplies its own sort witness.**

New, general, hole-free:

| name | arity | cone | hole | WATCHED IN CONE |
|---|---|---|---|---|
| `Lean4Lean.VInductDecl'.resultSortInhab_of_memberSat` | 12 | 2114 | no | none of 6 |
| `Lean4Lean.VInductDecl'.resultSortInhab_of_member` | 11 | 2115 | no | none of 6 |
| `Lean4Lean.VInductDecl'.constants_stage₁_of_not_mem_K` | 11 | 515 | no | none of 6 |
| `Lean4Lean.VInductDecl'.resultSortInhab_stage₁_of_memberSat` | 14 | 2188 | no | none of 6 |
| `Lean4Lean.VInductDecl'.resultSortInhab_stage₁_of_member` | 13 | 2189 | no | none of 6 |
| `Lean4Lean.VIndRestore.spineHargsN_of_memberSat` | 17 | 3371 | no | none of 6 |
| `Lean4Lean.VIndRestore.spineHargsN_of_member` | 16 | 3372 | no | none of 6 |
| `Lean4Lean.VIndRestore.spineHargsN_of_head_sat` | 16 | 3377 | no | none of 6 |
| `Lean4Lean.VIndRestore.spineHargsN_of_head_indexFree` | 15 | 3378 | no | none of 6 |
| `Lean4Lean.trIndDeclN_of_head_indexFree` | 20 | 3380 | no | none of 6 |

`resultSortInhab_of_memberSat` carries **no level condition and no environment condition** — only
that some member's index telescope is instantiated by some spine over the parameters.  `_of_member`
is the `is = []` case.

`spineHargsN_of_head_sat` sharpens "some non-companion member" to "**the head member**": `hcomp`
(`TrIndDeclN.companions`) makes member `0` non-companion whenever the user's declaration list is
non-empty, and `D.WF.types_ne` guarantees member `0` exists.

### The residue, final form

> `D.lvl` neither `≈ .succ _` nor `≈ .zero`, no telescope binder at `Sort D.lvl`, no `Sort u`-valued
> constant in the environment, **and no non-companion member of the block has an index telescope
> with a stage-1 inhabiting spine** — `∀ T₀ ∈ D.types, T₀.name ∉ K → ¬ ∃ is,
> e₁.HasArgs D.uvars D.params.reverse T₀.indices is`.

Every non-indexed nested block is outside it, for `D.lvl` **arbitrary** — that is every nesting
Lean's own elimination has been run on (`List`/`Option`/`Prod`).  So is `inductive T : Nat → Sort u`
nesting (`is = [Nat.zero]`).  What survives is a block all of whose own members are indexed over
telescopes with no stage-1 inhabitant, e.g. `inductive T : Empty → Sort u`.

**Not claimed**: that the residue is empty.  What *is* established is that its remaining conjunct is
an **inhabitation** question about the block's own index telescopes, not a strengthening one:
nothing in §3 touches `weakN_iff`, `AxiomConservativityWF` or `SortWitness`, and the `↔` that priced
the old residue at `weakN_iff` is simply not reached.  `SortWitEnv.lean` is deliberately imported but
never *named in a statement*, so none of the ten declarations above has `SortWitness` in its cone —
verified, not assumed (`WATCHED IN CONE: none of 6`, all ten).

### A false informal argument in a read-only file, refuted here

`Verify/Inductive/SortWitEnv.lean` §2a already re-bases the bypass at `e₁`
(`VInductDecl'.junkVal_hasType₁`, `VInductDecl'.companionVals_junk₁`,
`VIndRestore.argsTypedK_of_resultSortInhab₁`).  Its docstring then says:

> Note what this does *not* buy at a nested block: `e₁` is `env` plus the block's **non**-companion
> type constants, whose declared types are `Π params indices, Sort D.lvl` — a sort only when the
> block has no parameters and the member no indices.  At `ntreeAux` (params `[Type u]`) they are
> `.forallE`s, so the `e₁` form fails there exactly as the `env` form does (§1).

The premise is right; the inference is false.  `ResultSortInhab` does not ask for a constant *whose
type is a sort*, it asks for a **term** of type `Sort D.lvl` over each member's telescope — and a
constant of type `Π params indices, Sort D.lvl` supplies one once **saturated**.  §5's arity-0
witness discharges the field at `ntreeAux` through exactly that route, so the quoted verdict is
refuted.  The search for a `SortWitness` was a search for the wrong object.  **The three stage-1
lemmas are used verbatim, not re-proved** — a first draft of my file re-proved all three and
`scripts/sorry-census-all.lean` caught the duplicate names outright (see §6).

## §4 — (d) The arity-0 witness

`Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_of_member` — arity **0**, cone 5840, hole-free,
`WATCHED IN CONE: none of 6`, axioms `[propext, Classical.choice, Quot.sound]`:

    ∃ env₁, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType]

and `Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_text_of_member` (arity 0, cone 5841) states the
same conclusion as `InductR.lean` spells the `trSpine` field, with no rewriting.

Route: §3's `spineHargsN_of_head_indexFree` and nothing else.  Everything block-specific supplied to
it is *configuration data* (`ntreeAux_restrictStepCfg`, `ntreeAux_argsTypedK_of_wf`,
`ntreeAux_companions`) — the same standard `TrSpineProducer.lean` §3 set.  In particular this does
**not** go through `resultSortInhab_of_succ`, so unlike `ntreeAux_trSpine` it uses no fact about
`ntreeAux.lvl` at all.

Non-degeneracy, by computation, in the file: `uvars = 1`, `params = [.sort (.succ (.param 0))]`,
head member index-free and `∉ ntreeK`, companion `∈ ntreeK` (so `ntreeK ≠ []` and
`spineHargsC_nil` does not collapse the conclusion), and the substituted inhabitant computes to
`NTree #0` — the *declared* member, not a sort.  `nfnAux`'s degeneracy (`uvars = 0`, `params = []`)
is checked for contrast; the witness is not it.

## §5 — (c) What remains of the flip

**Mine, and now closed:** `TrIndDeclN.trSpine` — general producers with *two* independent sufficient
conditions, either of which suffices and neither of which is a hole:
`spineHargsN_of_succLevel`/`_of_zeroLevel` (level, previous round) and
`spineHargsN_of_head_sat`/`_of_head_indexFree` (head member, this round, level-free).  Construction
site form: `trIndDeclN_of_head_indexFree` (arity 20, cone 3380).

**Mine, and reduced but not closed:** `D.ArgsTypedK K e₂ occ`.  It is an `↔` away from one `HasArgs`
per companion member, and that `HasArgs` is general for foreign blocks presenting their nested
parameter as the *first* constructor field.  Residue: nested parameter at field position `i > 0`,
priced at `i` instances of `weakN_iff`.

**Owned elsewhere, untouched:**
* `Built` / `FreshIn` / `tyLvls`-WF in `RestoreData` — `Verify/Inductive/NestedRestore.lean` side.
* `Faithful` — `Verify/Inductive/RestoreFaithful.lean`.
* The remaining `TrIndDeclN` fields (`trType`, `trCtors`, `trCtorsLen`, `ctorName_own`, …).  Measured:
  the only things in the tree that *conclude* a whole `TrIndDeclN` are `InductR.lean`'s
  `trIndDeclN_wit` (a witness at `nfnAux`) and the non-nested `TrIndDecl.toN`.  So a general nested
  producer for the block as a whole is still absent — `trSpine` is no longer the reason.

## §6 — Round-close

* `lake build` whole tree: **green, 1625 jobs**, exit 0.
* Census (`scripts/sorry-census-all.lean`): **13 holes**; on disk 466, population 442,
  **BUILT 442 / NOT BUILT 0**; pass A 439 modules found 13, pass B 3 modules found 0.  Two
  consecutive identical runs.  Census figure **unmoved** (13 before, 13 after).
* `scripts/dup-names.lean`: **no duplicate `Lean4Lean` declarations across the joined cone.**
* Guards: 1 ✓ (exactly the 24 frozen axioms), 2 ✓ (`kernel_sound` axioms within whitelist, proof
  INCOMPLETE: sorryAx present), 3 ✓ (2/2 remaining).
* In-repo `unused section variable` warnings: **0**.  The separate "Variable name … is not explicitly
  referenced" class: **66 in `Lean4Lean/`**, unchanged from the previous round's baseline.  Warnings
  of any kind in the new file: **0**.
* Frozen files **not touched** — empty `git diff`, md5 `570efe63b2a7c567e25b6b89b4057690` /
  `513849e172cd4a5da9e3db2ce2eff7f3` / `006f49ce5b64d7e8d9bf80db50a17a4a`, byte-identical to the
  figures the previous round recorded.
* `docs/vacuity-ledger.md` not touched.  No state-changing git.
* Axiom bar `after ⊆ before`: no existing declaration was edited; only additions.  All 17 new
  declarations `[propext, Quot.sound]`, the four that reach `TrIndDeclN`/`ntree_stage₂_exists` also
  `Classical.choice` — the same sets `TrSpineProducer.lean`'s corresponding declarations carry.

### Two things worth reporting that were not asked for

1. **The duplicate-name catch.** My first draft re-proved `junkVal_hasType₁`,
   `companionVals_junk₁` and `argsTypedK_of_resultSortInhab₁`, which already existed in
   `SortWitEnv.lean`; two of the three name collisions were *exact*.  `lake build` was **green** on
   my module throughout — the collision is invisible to it, because nothing imported both modules
   until I added the import.  `scripts/sorry-census-all.lean` failed outright with
   `environment already contains 'Lean4Lean.VIndRestore.argsTypedK_of_resultSortInhab₁'`.  That is
   the fourth-plus occurrence of the class `Theory/Inductive/Decl.lean`'s `HasArgs.defeqDFC`
   docstring records, and the census caught it exactly as designed.  Resolved by deleting my
   duplicates and importing the existing home.
2. **Population fluctuation from a concurrent stream.**  `scripts/exists.lean` reported population
   437, then 439, then 438 over the round, and `git status` changed underneath me
   (`Theory/SetModel/CnstRecursion.lean` + `InductOracleAudit.lean` modified and
   `Theory/Inductive/NestedRules.lean` + `SetModel/InaccChainOmega.lean` untracked at start; gone and
   replaced by `Theory/Typing/ConfluenceRebuildPrice.lean` + `docs/handoff-confluencerebuild.md` at
   the end).  All cone figures in §1–§4 were taken *after* the final whole-tree build, and the census
   was run twice at the end with identical results, so the reported numbers are self-consistent — but
   a successor comparing cones against these should re-measure rather than assume.
