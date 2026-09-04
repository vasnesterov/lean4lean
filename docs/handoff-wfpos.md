# handoff-wfpos — `VIndField.WF.pos`'s `some` branch, at the real nested block

Owned files: `Lean4Lean/Verify/Inductive/WFPos.lean` (new), `docs/handoff-wfpos.md` (this).
Predecessors read in full before writing this: `docs/handoff-b6.md` ("What remains of Claim B",
items 1–3), `docs/handoff-userblockr.md` (skimmed for `chain`), `Theory/Inductive/Decl.lean`
lines 53, 241, 449, 463–535, 678–706, 717, 1025, 1065, 1088.

Everything outside my two files is read-only. `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` are frozen and I never open them for writing.

## §1 Priors — written BEFORE any Lean tool call, NEVER edited

Reading source with `cat`/`grep` is not "running Lean"; I read `Theory/Inductive/Decl.lean`,
`Theory/Inductive/DeclExamples.lean`, `Theory/Inductive/NestedHead.lean`,
`Theory/Inductive/NestedBuild.lean` (§recogniser), `Theory/Inductive/Restore.lean` (§Canonical),
`Verify/Inductive/B6.lean`, `Verify/Inductive/ClaimB.lean` §2 and `Verify/Inductive/UserBlockR.lean`
(outline) first. Every claim below that a reading already settled is marked **(read)** and still
carries a probability, because reading is not elaboration and I have been wrong about `rfl`
before. Corrections and scores go in §2 and §3 only.

- **P1. The tree builds when I start.** `git status --porcelain` at HEAD `ca04f43` shows only
  `docs/handoff-crshape.md` modified and `docs/handoff-nonestedall.md` untracked — no `.lean` in
  flight from another stream *right now*. Prior that a bare `lake build` is exit 0 before I write
  a line: **0.75**. Prior that some file I do not own goes red *during* the round (two other
  streams are live, one in `Verify/Inductive/`, one in `Theory/Typing/`): **0.45**. If that
  happens I re-poll before reporting it, per my brief.
- **P2. The `some` branch is ALREADY discharged in the tree — three times — and my brief's
  premise is therefore wrong as stated. (read)** `Theory/Inductive/DeclExamples.lean` holds
  `accDecl_WF` (line 1651), `mutDecl_WF` (1691) and `wDecl_WF` (1782), each a complete
  `VInductDecl'.WF .empty`, and each *does* reach `pos`'s `some` branch on a recursive field
  (`accIntro` field 1, `forestCons` fields 0 and 1, `wDecl`'s recursive field). The nine-conjunct
  tuple is written out literally there, residual clause included (`by decide`). Confidence those
  three are real, `sorry`-free and elaborate today: **0.9**. So "the last consumer nobody has
  discharged" is false *in general*; what is undischarged is the `some` branch **at a nested
  block, with `recArg` supplied by B6's reader rather than by hand**, and that is the honest
  target. Confidence that no `VInductDecl'.WF`/`VIndCtor.WF`/`VIndField.WF` witness at
  `ntreeAux` exists anywhere in the tree (grepped): **0.85**.
- **P3. `exists_indep` is NOT on my path.** `pos` and `binders_indep` are *different fields* of
  `VIndField.WF`; the census hole `VIndRecArg.exists_indep` is the discharge obligation for
  `binders_indep` alone (its docstring says so), and `pos`'s nine conjuncts never mention
  `BindersIndep`. Furthermore every `recArg` in `ntreeAux` has `binders := []`, so
  `BindersIndep` is reached with nothing to check (the `r.binders[k]? = some B` premise is
  `nofun`) — the same discharge `mutDecl_WF` uses for `forestCons`. Prior `exists_indep` is off
  my path for `pos`: **0.9**; off my path for a *whole* `VInductDecl'.WF ntreeAux` too: **0.8**.
  If it is on the path I stop and report, per my brief.
- **P4. What line 241 actually demands, as a statement.** `pos`'s `some` branch is a
  nine-conjunct tuple; conjuncts 1–4 and 9 are pure syntax (decidable at a concrete block) and
  5–8 are typing in the *staged* environment. Prior that the right restatement is that split —
  `PosSyn` decidable, `PosTy` the only real work: **0.8**. Prior that conjunct 8
  (`IsDefEqType Γ F.type (r.canonType D i)`) is *syntactic equality* at `ntreeAux`, hence
  discharged by conjunct 6 plus reflexivity rather than by a conversion: **0.8** (the `tyApp`
  arithmetic `bvars 1 1 = [.bvar 1]` and `ownLvls = [.param 0]` says it should be, and
  `ntreeAux_Canonical` already asserts exactly this shape for the whole block).
- **P5. The general theorem I expect to be the deliverable.** *At a canonical field
  (`F.type = r.canonType D i`), `pos`'s residual clause (conjunct 9) is implied by its own
  conjunct 4 (`∀ a ∈ r.args, D.NoBlock a`) — so the clause is **redundant** there, and
  non-redundant exactly where the stored type is not canonical.* Two cases: `r.binders = []`
  makes the trigger fire with `rest = r.args`; `r.binders ≠ []` makes `F.type` `.forallE`-headed
  so the trigger cannot fire and the clause is vacuous. Prior provable as stated: **0.8**. Prior
  it needs a side condition I have not seen (e.g. `r.args.length` versus the parameter prefix, or
  `ls = D.ownLvls`): **0.35**.
- **P6. The reader does not supply conjunct 4, and that is the missing link. (read)**
  `VIndRestore.recogAt` (`Theory/Inductive/NestedBuild.lean`:144) checks the head constant, the
  stored-instantiation prefix and a length bound, and then takes `args := sp.drop nA`
  **with no `NoBlock` scan at all**. The C++ kernel's `isValidIndAppIdx` does scan. So composing
  B6's `recArgOf`/`recog` with `WF.pos` needs one extra decidable check, which is precisely F7's
  residual scan. Prior the `NoBlock` scan is genuinely absent from `recog`: **0.85**. Prior this
  is a *gap* rather than a *refutation* (i.e. the check is true at `ntreeAux` and at every field
  `MemberRedexScan` measured): **0.8**.
- **P7. The firing.** A complete `VInductDecl'.WF VEnv.empty ntreeAux` this round: **0.6**. A
  complete `VIndField.WF` for all four fields of the block's three constructors (the part my
  brief actually asks for): **0.8**. Residual risk in both: `VIndCtor.WF.result` and
  `VIndField.WF.pos` conjunct 6 need the block constant at the *staged* environment, which is
  `acc_const_staged`'s shape and should transfer, and `VIndField.WF.hasType` for
  `_nested.List_1.{u} α : Sort (u+1)` needs `.constDF`, not `type_tac`'s `forallE` branch (which
  `accIntro_WF`'s long comment says breaks when the target sort is concrete). I expect to spend
  most of the round there, not on the interesting part.
- **P8. `isLE`.** `ntreeAux.isLE = true` and `ntreeAux.lvl = .succ (.param 0)`, so `LECond`'s
  cheap first disjunct (`IsNeverZero`) should fire and I never touch the second. **0.8**.
- **P9. `WF.pos` is NOT the last unpopulated field of `VInductDecl'.WF`.** `binders_indep` reads
  `recArg` too (that is its whole content), and `VIndCtor.WF.args_ty` / `VIndType.WF.canon` are
  "recorded, not derived" fields that the *translation* does not supply either. Prior that the
  honest answer to my brief's question 4 is "`pos` is one of at least two `recArg` consumers, and
  `WF` has other recorded fields besides": **0.9**.
- **P10. Imports.** I expect to import `Verify.Inductive.B6` (for the reader equations and
  `ntreeAux`'s `recArg` facts) and to need `Theory.Typing.Meta`'s `type_tac`, which
  `DeclExamples.lean` gets via `Theory.Meta`. Prior both are reachable without an import cycle
  and without pulling in a hand-built `VInductDecl'.WF ntreeAux` (there is none): **0.85**. Prior
  I must import `DeclExamples` itself (and therefore disclose `accDecl_WF`/`mutDecl_WF` as
  in-closure prior art rather than as excluded): **0.5**.
- **P11. Vacuity of my own firing.** `ntreeAux` has **no indices**, so every `r.args = []` and
  the residual clause fires with an **empty** residual: the trigger is exercised (which
  `.forallE`-headed `accIntro` does *not* do) but the residual scan has nothing to scan. Prior
  that my `ntreeAux` firing is therefore *trigger-non-vacuous but residual-vacuous*, and that I
  must say so rather than claim the clause is tested: **0.85**. Prior an indexed nested witness
  with a genuinely non-empty residual exists in the tree already
  (`Theory/Inductive/IndexedNested.lean`, `IndexedWit.lean`): **0.5**; prior I can reach one this
  round: **0.3**.
- **P12. Round-close.** My file adds 0 `sorry`s and 0 axioms beyond the whitelist; `#print axioms`
  on every new declaration shows either nothing or only what `ntreeAux`'s neighbourhood already
  carries. **0.75**. Prior that at least one of my new declarations comes out `sorryAx`-tainted
  through a typing lemma I did not expect: **0.3**.

## §2 Measurements (appended the moment each is made, before the next tool call)

### M1. The tree is green at the start of the round — **P1 (0.75) RIGHT**
`git rev-parse HEAD` = `ca04f43`. Bare `lake build`: **exit 0, 1657 jobs, "Build completed
successfully"** (2026-09-04). `git status --porcelain` before I wrote anything: only
`docs/handoff-crshape.md` (M) and `docs/handoff-nonestedall.md` (??) — no `.lean` from another
stream in flight at that moment. This is the measurement the method rules exist for; it is
recorded before any other tool call.

### M2. **P2 (0.9) RIGHT, and my brief's premise is wrong as written** — `pos`'s `some` branch is already discharged three times
`scripts/exists.lean`, population **470 built modules**, 2026-09-04:

| declaration | module | arity | cone | own value a hole | cone reaches `sorryAx` |
|---|---|---|---|---|---|
| `InductiveDeclExamples.fooDecl_WF` | `Theory.Inductive.DeclExamples` | 0 | 1834 | false | **false** |
| `InductiveDeclExamples.accDecl_WF` | `Theory.Inductive.DeclExamples` | 0 | 1956 | false | **false** |
| `InductiveDeclExamples.mutDecl_WF` | `Theory.Inductive.DeclExamples` | 0 | 1981 | false | **false** |
| `InductiveDeclExamples.wDecl_WF` | `Theory.Inductive.DeclExamples` | 0 | 2000 | false | **false** |
| `VIndRecArg.exists_indep` | `Theory.Inductive.Decl` | 18 | 851 | **true** | true (itself) |

`fooDecl_WF` discharges `pos` by its `none` branch only (`nofun` on the `some` side); the other
three reach the `some` branch on a real recursive field and write the nine-conjunct tuple out
literally, residual clause included (`by decide`). So the sentence in my brief — "`WF.pos`'s
`some` branch is the last consumer of the populated `recArg` that nobody has discharged" — is
**false as an unqualified claim**. The true residue is narrower and I restate it in §3.

### M3. **P3 (0.9) RIGHT and sharper than I predicted** — `exists_indep` is off the path for a concrete block
`exists_indep` is in **none** of the four `WF` witnesses' cones (the script watched it explicitly:
"watched declarations in cone: none of 6"). So a `VInductDecl'.WF` at a *concrete* block does not
route through the census hole at all: `binders_indep` is discharged directly there
(`accIntroRec_BindersIndep`, `forestCons_BindersIndep`, `nofun`), and `exists_indep` exists for
the *general* induction on the field index, not for any witness. That is the answer to my brief's
`exists_indep` trap warning, measured rather than argued: **not on my path, and not on the path of
any existing firing either.**

### M4. **THE ROUND'S HEADLINE, AND IT IS A CORRECTION TO MY BRIEF: `VInductDecl'.WF` at the real nested block ALREADY EXISTS.**
`HEADS="VInductDecl'.WF" lake env lean --run scripts/shape.lean` (2026-09-04) returns **179**
declarations whose type mentions `VInductDecl'.WF`, among them:

* **`InductiveDeclExamples.ntreeAux_WF' : ntreeAux.WF env₁`** — `Theory/Inductive/NestedHead.lean`
  line 943, arity 1 (the environment), **at an arbitrary `VEnv`**. Its docstring says the
  `addInduct'` hypothesis it once took was reported unused by `lake build` and removed, and that
  "the `ntreeAux_WF h` wrapper that used to sit below was retired once all **32 of its application
  sites (in 14 files)** were re-pointed here".
* `MRedex.TQWit.tqAuxB_WF` (`Theory/Inductive/IndexedWit.lean`) — the **indexed** nested block,
  which is where the residual clause can have non-empty content.
* `InductiveDeclExamples.nfnAux_WF` (`NestedBuild.lean`), `nfnAuxDirty_WF` (`RestoreBridge.lean`),
  `MRedex.QNWit.qnAux_WF` (`MemberRedex.lean`), `MRedex.MPWit.mpAuxB_WF` (`ParamRedex.lean`),
  `SetModel.eqIndDecl_WF`, `iffIndDecl_WF`, `nonemptyIndDecl_WF`, `SetModel.UnitAudit.unitDecl_WF`,
  `IndexedWit.t5Aux_WF`, `InductiveDeclExamples.fooComp_WF` / `fooComp'_WF`.

So my brief's task 2 ("discharge it at the real nested block") is **already discharged**, and
task 4's question ("does `VInductDecl'.WF` follow at the real block") is **already answered yes**,
in `Theory/Inductive/NestedHead.lean`, with 32 downstream consumers. This is exactly the failure
mode method rule 3 exists to catch: `ntreeAux_WF'` is invisible to a grep for `WF.pos`, invisible
to a grep for `ResidualClean`, and its name does not contain `pos`, `field` or `nested`. I found it
with `shape.lean` on the *conclusion head*, on my third tool call, before writing a line of Lean —
which is the only reason this round is not a re-derivation of committed work.

**P7 (0.6 that I would produce `VInductDecl'.WF VEnv.empty ntreeAux` this round) is now moot and
is scored 0** — not because it was too optimistic but because it was the wrong target. The round
re-aims in §3.

### M5. The *residual clause* (conjunct 9) has **no general producer** — that is the real hole in the room
`HEADS="VInductDecl'.ResidualClean" lake env lean --run scripts/shape.lean` (2026-09-04): the whole
population that concludes `ResidualClean` is

| declaration | module | what it is |
|---|---|---|
| `VIndField.WF.pos` | `Theory.Inductive.Decl` | the **structure field** itself (flagged `[FIELD]`; free wherever a `VIndField.WF` is in scope, never a premise) |
| `VInductDecl'.residualClean_of_uniformOcc_none` (arity 4) | `Decl` | vacuity when the trigger misses |
| `VInductDecl'.residualClean_of_uniformOcc_some` (arity 7) | `Decl` | the clause restated once the trigger's answer is in hand |
| `VInductDecl'.decidableResidualClean` (arity 3) | `Decl` | the `decide` instance every firing uses |
| `InductiveDeclExamples.ntreeAux_residualClean_badSpine` | `Theory.Inductive.NestedFresh` | a **negative** witness |
| `MRedex.TQWit.tq_hostile_not_residualClean` | `Theory.Inductive.IndexedNested` | the **refutation** the clause exists to exclude |
| the rest | `Decl`/`Lemmas` | `WF.rec`/`casesOn`/`mk`/`mono` auto-generated |

So **every one of the five existing `some`-branch firings discharges conjunct 9 by `by decide` at a
closed block**, and nothing in the tree says *why* it holds — there is no lemma of the form
"conjunct 9 follows from the conjuncts above it". That is the gap my brief was pointing at without
knowing it, and it is where the round's Lean goes (§3, P5).

### M6. **P6 (0.85) RIGHT** — the recogniser performs no `NoBlock` scan, and that is exactly F7's residual scan
`VIndRestore.recogAt` (`Theory/Inductive/NestedBuild.lean`:144) checks three things — head constant
`= .const (R.tyName k) (R.tyLvls k)`, stored-instantiation prefix `sp.take nA = (R.tyArgs k).map
(·.liftN (ξ.length + i))`, and `nA ≤ sp.length` — and then sets `args := sp.drop nA` **unscanned**.
The C++ kernel's `isValidIndAppIdx` (`Lean4Lean/Inductive/Add.lean`:299-345) *does* scan those with
`hasIndOcc`. So the reader's answer can carry a block-mentioning residual, and the specification's
conjunct 4 (`∀ a ∈ r.args, D.NoBlock a`) is the abstract counterpart of that scan. This is a **gap
to be bridged by one decidable check, not a refutation** — and `MRedex.TQWit.tq_hostile_args_not_noBlock`
(`Theory/Inductive/IndexedNested.lean` §8) is the machine-checked case where the check is what fails.

### M7. Machinery available for the general theorem (all pre-existing, none of it mine)
`VExpr.length_bvars` (`@[simp]`, `Telescope.lean`:144), `VExpr.mkPi_cons` (`@[simp]`, :107),
`VExpr.spineArgs_mkApp` / `spineArgs_const` (`Decl.lean`), `VExpr.mkApp_spineFn_spineArgs`
(`Restore.lean`), `VIndRecArg.canonTypeR_id` (arity 3, `NestedHead.lean`),
`VInductDecl'.tyAppR_id` (`@[simp]`, `NestedHead.lean`:96), `VExpr.betaSpine_eq_mkApp` and
`VExpr.betaHead_eq_self_of_noLam` (`B6.lean` §1), `recArgOf_sound` / `recArgOf_idx_lt`
(`ClaimB.lean` §2.3), `InductiveDeclExamples.ntreeAux_Canonical` (`NestedHead.lean`:646).
`VInductDecl'.idRestore` has `tyArgs _ := bvars 0 D.np` and `tyLvls _ := D.ownLvls`, which is why
the recogniser's prefix test and `uniformOcc?`'s parameter-prefix test are the *same* test at the
identity restoration — the fact the reader route turns on.

### M8. **P5 (0.8) RIGHT, and stronger than I predicted** — the core theorem is *unconditional*
`Lean4Lean.VInductDecl'.residualClean_canonType` elaborates clean (2026-09-04):

```
theorem residualClean_canonType {D : VInductDecl'} {i : Nat} {r : VIndRecArg}
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) (r.canonType D i)
```

No environment, no `Ordered`, no `VEnv.WF`, no block hypothesis. My 0.35 residual risk ("needs a
side condition I have not seen — a length condition, or `ls = D.ownLvls`") was **wrong, and for an
instructive reason**: `uniformOcc?` returns `e.spineArgs.drop D.np`, which is a function of `e`
alone, so the theorem needs *nothing* about `D.memberIdx` or about the reported member index `j`.
That is recorded as its own lemma (`uniformOcc?_canonResult_snd`) because it means the theorem holds
even at a block with **duplicate member names**, where `memberIdx (types.getD r.idx …).name = some
r.idx` is false. The two cases are: `r.binders = []`, trigger fires and reports exactly `r.args`;
`r.binders ≠ []`, canonical form is `.forallE`-headed so `spineFn` is not a `.const` and the trigger
**cannot** fire (one `rfl`).

### M9. §2 lands: conjunct 9 is free on the **whole range** of B6's two-stage reader
Three declarations, all clean first try (2026-09-04):

* `VExpr.betaHead_eq_self_of_spineFn_const` — the head β step is the identity on a `.const`-headed
  spine. **This is a strict weakening of B6 §1's `betaHead_eq_self_of_noLam`**, which asks `.lam`-
  freeness of every subterm; a stored field type may contain a `.lam` deep inside an argument
  (`tqAuxNodeB`'s does), so the `noLam` version does not cover the reader's range and the
  spine-head version does.
* `VInductDecl'.spineFn_const_of_uniformOcc?` — the trigger fires only on a `.const`-headed spine.
* `VInductDecl'.residualClean_of_recog` and `VInductDecl'.residualClean_of_recArgOf` — conjunct 9
  from the single- and two-stage readers, given conjunct 4.

The two-stage case is the one that matters and the argument is worth stating in one line: **where the
residual clause says anything at all the trigger has fired, and a firing trigger forces the stored
type to be `.const`-headed, so stage 2's head β step is the identity exactly there.** So the reader
contributes no failure mode of its own to F7, and the *only* way a reader-populated field can fail
conjunct 9 is a residual argument mentioning the block — which is precisely what the C++ kernel's
`isValidIndAppIdx` scans for, and precisely `tq_hostile_args_not_noBlock`.

### M10. §3 and §4 land — the split, the reader composition, and the firing
* `VIndField.PosSyn` (conjuncts 1-4 and 9, `Decidable` via `decidablePosSyn`), `VIndField.PosTy`
  (conjuncts 5-8), `posSome_of_split` (the two halves *are* the structure field — stated as a
  producer for `WF.mk`, not an `Iff`, because the field's type is a `match` on `F.recArg` and only
  becomes a proposition once `F.recArg` is known), and the two projections `WF.posSyn` / `WF.posTy`.
* `VIndField.posSyn_of_recArgOf` — **the reader plus a three-part decidable check gives all five
  syntactic conjuncts.** Conjunct 1 from `recArgOf_idx_lt`, conjunct 9 from §2; what is left is the
  index-arity equation and the two `NoBlock` scans, which are the abstract form of
  `checkPositivity`'s `hasIndOcc` calls and `isValidIndAppIdx`'s residual scan.
* Firing at `ntreeAux`, anchored on the block's own field records (`types.getD … ctors.getD …
  fields.getD`) so it cannot drift: `ntreeAux_{node_field1,cons_field0,cons_field1}_recArgOf` (the
  reader computing, three `rfl`s), `ntreeAux_recArgOf_eq_stored`, `PosSyn` at all three recursive
  fields **with no `decide` on the residual clause**, the canonicity route as an independent second
  derivation (`ntreeAux_residualClean_of_canonical` through `ntreeAux_Canonical`), and
  `ntreeNode_field1_WF` — a complete `VIndField.WF` for the block's flagship recursive field, typing
  half built here from `ntreeAux_params_WF` / `nlist_const_staged` / `type_tac` rather than taken
  from `ntreeAux_WF'`.

Two small frictions worth recording because both cost a cycle: `simp [VLevel.eval, ntreeAux,
Lean.Nat.imax]` does **not** discharge `VIndField.WF.level` when the field is written as
`fields.getD 1 default` rather than substituted to a literal — the constructor (`ntreeNode`) has to
be in the simp set too. And `PosTy`'s `canonResult`/`defeq` need the staged constant in the *local
context* under the name `type_tac`'s `assumption` will find, so `have hf := nlist_const_staged hs`
has to precede the structure instance.

### M11. Round-close measurements — **P12 (0.75) RIGHT**, and the structural exclusion is measured
Bare `lake build` after the file landed: **exit 0, 1659 jobs, "Build completed successfully"**
(2026-09-04; 1657 at M1, +1 for `WFPos.lean`, +1 for another stream's module — population went
470 → 473 built modules during the round, so another stream landed while I worked). **0 warnings from
`WFPos.lean`.** `#print axioms` on all 29 new declarations: `[propext]` or `[propext, Quot.sound]`,
**no `sorryAx` anywhere, nothing outside guard 1's whitelist.**

`scripts/exists.lean` with six declarations **watched** — `ntreeAux_WF'`, `VIndRecArg.exists_indep`,
`MRedex.TQWit.tq_hostile_not_residualClean`, `ntreeAux_residualClean_badSpine`, `accDecl_WF`,
`mutDecl_WF`:

| declaration | arity | cone | hole | `sorryAx` | watched in cone |
|---|---|---|---|---|---|
| `VInductDecl'.residualClean_canonType` | 4 | **881** | false | false | **none of 6** |
| `VInductDecl'.residualClean_of_recog` | 6 | 1722 | false | false | none of 6 |
| `VInductDecl'.residualClean_of_recArgOf` | 6 | 1744 | false | false | none of 6 |
| `VExpr.betaHead_eq_self_of_spineFn_const` | 4 | **427** | false | false | none of 6 |
| `VIndField.posSome_of_split` | 9 | 872 | false | false | none of 6 |
| `VIndField.posSyn_of_recArgOf` | 8 | 1826 | false | false | none of 6 |
| `InductiveDeclExamples.ntreeNode_field1_posSyn` | 0 | 1847 | false | false | none of 6 |
| `InductiveDeclExamples.ntreeAux_residualClean_of_canonical` | 9 | **999** | false | false | none of 6 |
| `InductiveDeclExamples.ntreeNode_field1_WF` | 3 | 2103 | false | false | none of 6 |

So the header's exclusion claim is **measured, not asserted**: no declaration in this file borrows
`ntreeAux_WF'`'s `pos` (which discharges conjunct 9 by `decide`), nor either existing hand-built
`ResidualClean` instance, nor the census hole. **P3 confirmed a third time: `exists_indep` is in none
of my cones.**

### M12. Instrument note — a shell trap that would have produced a false absence claim
`lake env lean --run scripts/exists.lean Lean4Lean.VInductDecl'.residualClean_canonType` **loses the
apostrophe** when the name is passed unquoted, and the script then reports
`NOT FOUND Lean4Lean.VInductDecl.residualClean_canonType`. I hit this on a name I had just compiled,
so I caught it; on a name I merely believed existed it would have gone into a handoff as an absence.
Use `NAMES="…"` with the whole list in double quotes for any `VInductDecl'`/`VIndRestore'`-style name.

### M13. Census unchanged — 13 holes, none of them mine
`scripts/sorry-census.lean`, 2026-09-04: **TOTAL declarations directly containing `sorryAx`: 13**,
identical list to the one at HEAD (`leanTT_equiconsistent_zfc_omega_inaccessibles`,
`VIndRecArg.exists_indep`, `VEnv.NormalEq.descend`, `VEnv.WF.rigidShapeUniqNS`,
`VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.IsDefEqU.weakN_iff`, `addDecl.WF`, `kernel_sound`,
`kernel_complete`, `inferProj.WF`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`, `TrProj.weak'_inv`).
`WFPos.lean` contributes **0**. `scripts/layer-check.py` exit 0, with the pre-existing "14 of 286
Theory modules downstream of Verify/" unchanged — my module is in `Verify/` and imports only
`Verify.Inductive.B6`, so it cannot add such an edge.

### M14. **The one edit elsewhere my work implies — stated verbatim, NOT made**
`scripts/can-cite.py` (2026-09-04): `Theory.Inductive.NestedHead` (closure 50) and
`Theory.Inductive.DeclExamples` (closure 30) **cannot cite** `VInductDecl'.residualClean_canonType`
— it lives in `Verify.Inductive.WFPos` and the arrow runs the wrong way. So the four existing
Theory-side firings (`accDecl_WF`, `mutDecl_WF`, `wDecl_WF`, `ntreeAux_WF'`, and `tqAuxB_WF`) cannot
use §1 where they are.

**And the statement does not need `Verify/` at all.** Measured, not argued: `lean_run_code` with
`import Lean4Lean.Theory.Inductive.Decl` as the *only* import elaborates
`spineArgs_drop_tyApp`, `uniformOcc?_canonResult_snd` and `residualClean_canonType` **verbatim, zero
diagnostics**. Only §2 (the reader route) genuinely needs `Verify/`, because `VInductDecl'.recArgOf`
is declared in `Verify.Inductive.ClaimB`.

So the migration is a pure move with no proof debt, and it is an edit to a file I do not own. **I am
not making it.** The exact edit, for the orchestrator:

> In `Lean4Lean/Theory/Inductive/Decl.lean`, immediately after
> `instance decidableResidualClean` (which ends the `ResidualClean` group, just before
> `end VInductDecl'` at what is currently line 320), insert the three declarations
> `VInductDecl'.spineArgs_drop_tyApp`, `VInductDecl'.uniformOcc?_canonResult_snd` and
> `VInductDecl'.residualClean_canonType` **exactly as they stand in
> `Lean4Lean/Verify/Inductive/WFPos.lean` §1** (they are inside `namespace VInductDecl'` in both
> places, so the bodies transfer character for character; `spineArgs_drop_tyApp` needs
> `VExpr.spineArgs_mkApp`, `spineArgs_const`, `mkPi_cons` and `length_bvars`, all of which
> `Decl.lean` already has through `Theory.Inductive.Telescope`). Then delete the three
> declarations from `WFPos.lean` §1 and let it cite them. The three §1.1 corollaries
> (`VIndField.residualClean_of_canon`, `VIndCtor.residualClean_of_canonical`,
> `VInductDecl'.residualClean_of_canonical`) need `VIndCtor.Canonical`, which lives in
> `Theory/Inductive/Restore.lean`, so they belong there rather than in `Decl.lean`.

Payoff of that move, which is why it is worth asking about: the four `by decide`s in
`ntreeAux_WF'`'s `pos` fields and the ones in `accDecl_WF`/`mutDecl_WF`/`wDecl_WF` become
`residualClean_canonType (by …)` — i.e. the residual clause stops being a closed computation at each
block and becomes a consequence of the conjunct above it, which is what makes it *free at a block
nobody has enumerated yet*. Nothing breaks if the move is declined; §1 simply stays unusable from
`Theory/`.

## §3 Findings, and the restatement my brief needed

**F1. The brief's premise was false, and the correct residue is one level down.** `VIndField.WF.pos`'s
`some` branch is discharged at five blocks already (`accDecl`, `mutDecl`, `wDecl`, `ntreeAux`,
`tqAuxB`), and `VInductDecl'.WF` at the real nested block is `ntreeAux_WF'`, a lemma with 32
application sites in 14 files. The undischarged thing was never the branch: it was that **conjunct 9,
F7's residual clause, had no general producer** — five `by decide`s and no theorem.

**F2. Conjunct 9 is not independent information on the canonical range** (`residualClean_canonType`,
unconditional, cone 881), **nor on the reader's range** (`residualClean_of_recArgOf`, cone 1744). On
both, it follows from conjunct 4. The reader's second stage — the head β step that makes B7's `whnf`
gap one step wide — cannot open the clause, because a firing trigger forces a `.const` head and the β
step is the identity exactly there.

**F3. It *is* independent in the specification as a whole**, and the tree already knows why:
`TQWit.tqHostile` satisfies conjuncts 1-8 and fails 9. So §1 is as strong as its shape allows, and the
clause is not deletable from `Decl.lean`.

**F4. What the reader does not supply, precisely.** `recogAt` performs **no `NoBlock` scan**. So
composing B6's reader with `WF.pos` needs exactly one extra decidable check — the two `NoBlock`
scans plus an index-arity equation (`posSyn_of_recArgOf`'s three hypotheses) — and that check is the
abstract counterpart of `checkPositivity`'s `hasIndOcc` calls and `isValidIndAppIdx`'s residual scan.
That is a clean statement of what the refinement owes, and it did not exist before this round.

**F5. `exists_indep` is off the path, three times measured.** It is `binders_indep`'s obligation, not
`pos`'s; it is in **none** of the four existing `WF` witnesses' cones, and in none of my nine measured
declarations' cones. At `ntreeAux` `binders_indep` is free because every `ξ` is empty. The brief's
trap warning was well placed and the answer is negative.

**F6. `WF.pos` is not the last `recArg` consumer**, so the brief's question 4 has a two-part answer:
`binders_indep` reads `recArg` too (and *that* one is hole-backed in general), and `VIndCtor.WF.args_ty`
/ `VIndType.WF.canon` are "recorded, not derived" fields the translation does not supply either.
`VInductDecl'.WF` at the real block does not *become* establishable — it already was.

### Scoring my own §1 priors
| prior | claim | outcome |
|---|---|---|
| P1 (0.75) | tree green at start | **RIGHT** (M1) |
| P2 (0.9) | `some` branch already discharged elsewhere | **RIGHT**, and understated — also at `ntreeAux` itself (M2, M4) |
| P3 (0.9/0.8) | `exists_indep` off my path | **RIGHT**, measured three ways (M3, M11) |
| P4 (0.8) | the 5-syntactic/4-typing split is the right restatement | **RIGHT** (M10, `PosSyn`/`PosTy`) |
| P4b (0.8) | conjunct 8 is syntactic equality at `ntreeAux` | **RIGHT** (`defeq := ⟨_, by type_tac⟩`, no conversion) |
| P5 (0.8) | canonical ⟹ conjunct 9 from conjunct 4 | **RIGHT and stronger** — unconditional; the 0.35 "needs a side condition" branch was wrong because the residual does not depend on the reported index (M8) |
| P6 (0.85) | `recog` performs no `NoBlock` scan | **RIGHT** (M6) |
| P7 (0.6) | I produce `VInductDecl'.WF VEnv.empty ntreeAux` | **scored 0 — wrong target**, it existed (M4) |
| P8 (0.8) | `isLE` via `IsNeverZero` | **not exercised** (I never needed the block-level `WF`); `ntreeAux_WF'` does it that way, so the prior was right about the block |
| P9 (0.9) | `pos` is not the last `recArg` consumer | **RIGHT** (F6) |
| P10 (0.85) | imports reachable, no cycle, no borrowed instance | **RIGHT**, and the exclusion is measured rather than asserted (M11) |
| P11 (0.85) | my firing is trigger-non-vacuous but residual-vacuous | **RIGHT**, and §5(b) says so in the file |
| P12 (0.75) | 0 sorries, 0 new axioms | **RIGHT** (M11, M13) |

### My method's gaps, honestly
1. **I nearly re-derived committed work.** M4 was found on the *third* tool call only because
   `shape.lean` was in my brief's method rules. Had I trusted the brief's "nobody has discharged" and
   started writing Lean, I would have spent the round rebuilding `ntreeAux_WF'`. The generalisable
   lesson is narrower than "run shape.lean": **query by the conclusion head of the thing you are
   about to prove, not by the name of the obligation you were handed.** `WF.pos`, `ResidualClean` and
   `pos` all miss `ntreeAux_WF'`; `VInductDecl'.WF` finds it instantly.
2. **My priors were about my proof and not about the world.** Eleven of twelve concerned what I would
   prove or what would break; only P2 asked whether the target already existed, and P2 is the one
   that decided the round. That ratio is backwards and I would write four such priors next time.
3. **§5(a) is a citation, not a proof.** I chose structural exclusion over importing `IndexedNested`,
   which means the sharpness of §1 is asserted in my file and only measured in this handoff. A round
   that wanted it machine-checked *in the file* would have to accept `IndexedNested` in the closure,
   or rebuild a hostile witness — I judged the exclusion worth more than the in-file citation, and
   that judgement is arguable.
4. **I did not test §2 at a non-canonical block.** `residualClean_of_recArgOf`'s interesting case is a
   field where stage 1 misses and stage 2 answers (`ROWit.roDecl`). I proved the theorem covers it but
   fired only at `ntreeAux`, where stage 1 answers. `ROWit.roField.type` is `.lam`-headed, so the
   trigger misses and the clause is vacuous there — the firing would be honest but empty, which is why
   I left it; a block where stage 2 answers *and* the trigger fires would be the real test, and I do
   not know whether one exists.
5. **One number I did not date and should have.** The "179 declarations mentioning `VInductDecl'.WF`"
   in M4 is `shape.lean`'s report with a truncated tail ("159 more"); I did not re-run it after the
   population moved 470 → 473, so treat it as ±3 as of 2026-09-04.

### M15. Correction to M4's one undated number
M4 says `shape.lean` on `VInductDecl'.WF` "returns **179**". What the captured output actually shows
is 19 rendered rows plus "… 159 more", i.e. **178**, and I did not re-run it after the population moved
470 → 473 built modules. Corrected here rather than edited above, so the record shows the slip. The
finding M4 rests on — that `ntreeAux_WF'` is among them — is a single named row and is unaffected.
