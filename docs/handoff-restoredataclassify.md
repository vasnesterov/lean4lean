# handoff — classifying three `RestoreData`-adjacent obligations of the nested flip

**Round type: MEASUREMENT.** Deliberately small. Fourteen API crashes this session, four of the
last five at the measure→author transition, and the last two lost every measurement because it
was held in context. So: every `scripts/exists.lean` / `scripts/shape.lean` / `scripts/users.lean`
call gets a line appended here **before the next call is made**. Nothing is batched.

Target: the three obligations that `Verify/Inductive/SpineClosedLand.lean`:236 names as "the flip's
*remaining* obligations … `RestoreData`/`OccResidue` business":

* **A. `Built`** — `D.Built R K env occ` at `R = r.mkRestore types D.uvars D.np ls as`
* **B. `FreshIn`** — `(R.csubstTy D K).FreshIn env`
* **C. `tyLvls`-WF** — `∀ j T, D.types[j]? = some T → T.name ∈ K → ∀ l ∈ R.tyLvls j, l.WF D.uvars`

Each must be classified as exactly one of: **already general** (and where) / **general modulo a
named lemma** (and which) / **open** (and what the obstruction is).

## §0 Priors, written before the first measurement

Read-only source reading done before writing this (no scripts run yet): `NestedRestore.lean`
(the `RestoreData` structure at :279 and `mkRestore` at :237), `RestoreFaithful.lean` §3's
discharge table at :251-263, `TeleMove2.lean` §2 at :90-107, `SpineClosedLand.lean` :200-245,
`TrSpineProducer.lean` :316.

**Prior on B (`FreshIn`): already general, ~90%.** The brief's claim is directly corroborated by
source text I have read, twice over. `TeleMove2.lean`:98 states
`VIndRestore.csubstTy_freshIn {env E₁ R D K} (h₁ : env.addIndTypes D = some E₁) :
(R.csubstTy D K).FreshIn env` — universally quantified over `R`, `D`, `K`, with the *only*
hypothesis a type-staging equation. And `RestoreFaithful.lean`:263's table row says the same in
prose, calling it "a *negative* result about my own condition": the `Restrict*` files' freshness
hypothesis is **not** bought by the gate or by `NoNestedN`. The residual 10% is that the proof
might be `sorry`-backed or the statement weaker than it reads (the environment is easy to get
wrong here — `FreshIn env₃` is *false*, only `FreshIn env` holds). `exists.lean` settles that.
If it holds I stop working on B, per the brief.

**Prior on C (`tyLvls`-WF): general modulo a premise on the semantic parameter `ls`, ~65%; small
chance already general, ~15%; open, ~20%.** `mkRestore` sets
`tyLvls j := if j < types.length then VLevel.params uvars else tyLvls j` — the `else` branch is
the *unconstrained function parameter* `ls`. Meanwhile `RestoreData.companions` says
`T.name ∈ K ↔ types.length ≤ j`, so the guard `T.name ∈ K` selects **exactly** the `else` branch.
That means `RestoreData` cannot possibly discharge C: the obligation lands entirely on `ls`, about
which `RestoreData` says nothing (its `args` field constrains `as`, and there is no `lvls` field).
So my prior is that C is "general modulo a premise on `ls`", and the smallest sufficient premise
is the obvious one — `∀ j, ∀ l ∈ ls j, l.WF D.uvars` — with the own-member half
(`VLevel.params uvars` all WF at `uvars`) being the part that is actually a lemma. The 15% is that
someone already stated exactly that (`shape.lean` on `VLevel.WF` + `VIndRestore.tyLvls` will say).
The 20% "open" is if the `if` guard and the `∈ K` guard fail to line up without a further fact.

**Prior on A (`Built`): general modulo a named residue, ~70%; open, ~25%; already general, ~5%.**
`NestedRestoreWit.lean` §6 (:516-591) advertises itself as "the general bridge: `Built` from
`RestoreData` plus a named residue", says four of `Built`'s nine clauses are discharged by
`RestoreData`, and names `OccResidue` at :560 as "the residue of `Built` a `Result` does not
determine". If that reads as I expect, A is "general modulo `OccResidue`" and the honest question
is whether `OccResidue` is itself general or a witness-only fact — the latter would make A open in
substance while looking closed. The 25% is that reading.

**Prior on the `head` residual: needs the wider check, ~55%; independent of both, ~30%;
discharged by the existing gate, ~15%.** `RestoreFaithful.lean`:304's `presentedHead_clean_of_declared`
carries `hdecl` — "`presentedHead` lands on a declared constant" — and the docstring is explicit
that "§1 cannot supply it" because it is "a statement about `aux2nested`'s *values*, not about
names". The gate `NoNestedDeclNames` is a predicate on input `types`' names, so on its face it
cannot see `aux2nested`'s value map: that is the 15%→low. The question is whether the wider
whole-environment `_nested`-prefix check costed in `docs/decision-nested-prefix-all-decls.md` would
supply `hdecl`, and my prior is that it would *not* directly either — that check is also about
names, and `hdecl` asks for **containment** (`venv.contains`), a different kind of fact. Hence the
30% on "independent of both". I expect this to be the round's most likely surprise.

**Prior on `auxRec` removability: true, ~85%.** `NestedRestore.lean`:307's own docstring already
says "**REMOVABLE**: derivable from the gate condition alone … `NoNestedDeclNames.auxRecName`
(cone 3588)", and gives the general lemma it rests on. That is a self-report by the file that
introduced the field, so it is strong but not a measurement.

**Prior on the whole round: I expect to return three classifications and no new Lean.** Two rounds
today found their assigned work already done and a third found half of it; the brief says a round
of three well-evidenced classifications with no new Lean is a complete success, and my priors say
B is already done and C's residue is a one-line premise rather than a theorem worth a file.

## §1 Measurements, appended one per call

### M1 — `exists.lean`, eight names (the brief's three specific claims plus the `Built` bridge)

Command: `lake env lean --run scripts/exists.lean` on the eight names below.
Population: **439 built modules**; the script watches **6** forbidden declarations for cone
membership. **Every one of the eight: `watched declarations in cone: none of 6`, `own value is a
hole: false`, `cone reaches sorryAx: false`.** Both cleanliness lines clean for all eight.

| name (exactly as printed) | module | arity | cone |
| --- | --- | --- | --- |
| `Lean4Lean.VIndRestore.csubstTy_freshIn` | `Lean4Lean.Theory.Inductive.TeleMove2` | 6 | **1093** |
| `Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_built` | `…Verify.Inductive.NestedRestoreWit` | 14 | **2061** |
| `Lean4Lean.ElimNestedInductive.Result.OccResidue` | `…Verify.Inductive.NestedRestoreWit` | 7 | 10 |
| `Lean4Lean.NoNestedDeclNames.auxRecName` | `…Verify.Inductive.RestoreFaithful` | 3 | **3588** |
| `Lean4Lean.ElimNestedInductive.Result.ownName_of_gate` | `…Verify.Inductive.RestoreFaithful` | 14 | 5796 |
| `Lean4Lean.ElimNestedInductive.Result.ownCtor_of_gate` | `…Verify.Inductive.RestoreFaithful` | 16 | 5796 |
| `Lean4Lean.ElimNestedInductive.Result.presentedHead_clean_of_declared` | `…Verify.Inductive.RestoreFaithful` | 9 | 671 |
| `Lean4Lean.NestedWit.nfnResult_occResidue` | `…Verify.Inductive.NestedRestoreWit` | 2 | 1668 |

`OccResidue` carries the script's own caveat: **`[NO PROOF TERM: cone is type-constants only; it
says NOTHING about satisfiability — price the witnesses]`**. That is why `nfnResult_occResidue` is
in the same call: it is the model, cone 1668, clean, so `OccResidue` is not vacuous.

**Reads for the classifications.** B's lemma is real, clean, and cheap (1093) — prior confirmed,
and its signature (read at `TeleMove2.lean`:96-98) universally quantifies `R`, `D`, `K` with the
single hypothesis `env.addIndTypes D = some E₁`. The `auxRec`-removability claim (cone 3588) and
both `own*_of_gate` claims (5796 each) are confirmed present and clean. The `head` claim is
confirmed **reduced only**: `presentedHead_clean_of_declared` exists at cone 671 but its statement
(read at `RestoreFaithful.lean`:304-315) carries `hdecl` as an explicit premise.

### M2 — `shape.lean`, `HEADS="VLevel.WF VIndRestore.tyLvls"` (tail only; my error)

I piped through `tail -50` and so saw the **expensive end** of a sorted-cheapest-first list, which
is the wrong half. Logging it anyway rather than pretending the call did not happen. What the tail
does show: the population of things whose type mentions both `VLevel.WF` and `VIndRestore.tyLvls`
is large and consists of the `Restrict*`/`Hargs*`/`valAt`/`tyVal_hasType`/`csubstTy_WF` family —
i.e. **`VLevel.WF … R.tyLvls` appears throughout as a carried `hlvl` premise**, at arity 13-21
(`Lean4Lean.VIndRestore.csubstTy_WF_of_hargs`, `…csubstTy_WF_of_spineHargsC`,
`Lean4Lean.TrIndDeclN.csubstTy_WF` arity 21, `Lean4Lean.TrIndDeclN.tyVal_hasType` arity 19,
`Lean4Lean.VIndRestore.tyVal_hasType_of_faithful`, `…tyVal_hasType_of_spineHargsC`,
`Lean4Lean.RestrictStepCfg.mk` arity 16 — so it is also a **field** of `RestrictStepCfg`).
No consumer in the tail *concludes* it. Re-running for the cheap head as M3.

**Correction to my own prior on C.** Reading `NestedBuild.lean`:771 while this ran: `Built.tyLvls`
is **not** a WF clause, it is the equation `R.tyLvls j = (occ j).lvls`. So obligation C is
specifically the `hlvl` premise of `SpineClosedLand.lean`:207-215 / :222-231, and via `Built.tyLvls`
it is **equivalent to `∀ l ∈ (occ j).lvls, l.WF D.uvars` — a fact about the occurrence `occ`, not
about `mkRestore`'s parameter `ls` at all** once `Built` is in hand. My §0 prior had the right
shape (the obligation lands outside `RestoreData`) but named the wrong carrier.

### M3 — `shape.lean`, `HEADS="VLevel.WF VIndRestore.tyLvls"`, full output (the decisive one for C)

Population 439 modules. **29 constants in `Lean4Lean` conclude something mentioning both heads; 1
is a structure field.**

* `FIELD arity 14 Lean4Lean.RestrictStepCfg.lvls` — of `Lean4Lean.RestrictStepCfg`
  (`…Verify.Inductive.RestrictStep`). Flagged by the script: "free wherever you have a
  `Lean4Lean.RestrictStepCfg` — do NOT carry this as a hypothesis". So inside the
  `RestrictStepCfg`-shaped configuration, C is **already free**.
* **The only two plain declarations that CONCLUDE it are both witnesses, both arity 6:**
  `Lean4Lean.NestedWit.nfnAux_tyLvls_wf` (`…Verify.Inductive.ValAtPrice`) and
  `Lean4Lean.InductiveDeclExamples.ntreeAux_tyLvls_wf` (`…Verify.Inductive.ValAtParam`).
* Everything else at arity ≥ 10 is a `RestrictStepCfg` auto-generated eliminator or a **consumer**
  that carries it as a premise (`valAt_of_*`, `tyVal_hasType_of_*`, `csubstTy_WF_of_*`,
  `TrIndDeclN.csubstTy_WF`, `TrIndDeclN.tyVal_hasType`, `spineTypedAt_of_hargs`,
  `hargs_of_spineTyped`, `restrictC_*`, `csubst_WFD` at arity 32).

**Verdict for C: no general lemma concludes `tyLvls`-WF — two block-specific witnesses only.** This
is exactly the pattern the brief warned `shape.lean` catches, run in the *negative* direction: the
instrument that has caught three already-done assignments says here that this one is genuinely not
done. Combined with the M2 correction (`Built.tyLvls : R.tyLvls j = (occ j).lvls`), the smallest
sufficient premise is now identifiable and it is a fact about `occ`, not about `RestoreData`.

### M4 — `shape.lean`, `HEADS="VLevel.WF VNestedOcc.lvls"` (C's real carrier)

Chased after M2's correction re-aimed C at `(occ j).lvls`. Population 439 modules.
**6 constants conclude something mentioning both heads; 1 is a structure field.**

* `FIELD arity 6 Lean4Lean.VNestedOcc.ArgsTypedH.lvls` — of `Lean4Lean.VNestedOcc.ArgsTypedH`
  (`Lean4Lean.Theory.Inductive.HargsShared`), script-flagged "free wherever you have a
  `Lean4Lean.VNestedOcc.ArgsTypedH` — do NOT carry this as a hypothesis".
* plain declarations, all arity 6: `Lean4Lean.VNestedOcc.argsTypedH_of_ty`
  (`Lean4Lean.Verify.Inductive.ArgsTypedSupply`) plus the four `ArgsTypedH` auto-generated
  `rec`/`recOn`/`casesOn`/`mk`.

So **the level well-formedness of an occurrence's levels is a FIELD of `VNestedOcc.ArgsTypedH`** —
this is the same failure mode as `shape.lean`'s own docstring example (`VInductDecl'.WF.params`, "a
field of a structure that was already in scope at the claim site"). C is not an independent
obligation at all: it is free from `ArgsTypedH`, and the only non-eliminator producer in the tree is
`argsTypedH_of_ty`, arity 6. Next: price `argsTypedH_of_ty` and check it is general rather than a
witness (`TrSpineProducer.lean`:305-309 warns that `ArgsTypedH` "exists in the tree only at the two
witnesses `listOcc_argsTypedH_of_wf`, `pfnOcc_argsTypedH_of_wf`", which if still true would make
this a relocation of the obligation rather than a discharge).

### note (source reading, no script) — M4's field is CIRCULAR for C, and the general route named

Read `HargsShared.lean`:590-596 and `ArgsTypedSupply.lean`:793-803:

```
structure VNestedOcc.ArgsTypedH (N : VNestedOcc) (D : VInductDecl') (e : VEnv) : Prop where
  lvls : ∀ l ∈ N.lvls, l.WF D.uvars
  ty   : …  ctor : …
```
```
theorem VNestedOcc.argsTypedH_of_ty (hlvls : ∀ l ∈ N.lvls, l.WF D.uvars) (hctor …) (hty …) :
    N.ArgsTypedH D e := { lvls := hlvls, ty := hty, ctor := … }
```

So the *only* non-eliminator producer **takes C as its first hypothesis and stores it verbatim**.
`ArgsTypedH.lvls` is therefore free only if you already have an `ArgsTypedH` from a witness. C is
bundled, not discharged. Same for `RestrictStepCfg.lvls`. And `VNestedOcc.Occurs`
(`NestedBuild.lean`:658-672) has `lvls_len : N.lvls.length = N.decl.uvars` but **no** WF clause, so
`Built.occurs` does not supply it either — and note the mismatch of arities: `Occurs` constrains the
levels' *count* against `N.decl.uvars` (the **foreign** block), while C wants their *WF* at
`D.uvars` (the **new** block). Two different blocks; no clause relates them.

**The general route, named:** `Lean4Lean.VLevel.WF.of_mapM_ofLevel` (`Theory/VLevel.lean`:185) —
`List.mapM (VLevel.ofLevel Us) us = some us' → ∀ l ∈ us', l.WF Us.length` — is exactly C's shape
once `(occ j).lvls` is known to be the translation of the occurrence's `Lean.Level`s under the
declaration's `Us` with `Us.length = D.uvars`. `NestedOccData.lean`:929 already carries a
`List.mapM (VLevel.ofLevel Us) ls = some ls'` hypothesis, so the plumbing point is identified.

### M5 — `shape.lean`, `HEADS="VEnv.contains ElimNestedInductive.Result.presentedHead"` (the `head` residual)

Population 439 modules. **1 constant in `Lean4Lean` concludes something mentioning both heads; 0
are structure fields.** The one hit is
`arity 9  Lean4Lean.ElimNestedInductive.Result.presentedHead_clean_of_declared`
(`Lean4Lean.Verify.Inductive.RestoreFaithful`) — i.e. the *consumer* that carries `hdecl` as a
premise, and **nothing at all in the tree concludes `venv.contains (r.presentedHead t.name)`**. No
field, no witness, not even a block-specific one. This is the sparsest result of the round: C at
least had two witnesses (M3); the `head` residual's `hdecl` has zero.

### M6 — `exists.lean`, eight more names (pricing everything the classifications cite)

Population **440 built modules** — up from 439 in M1-M5; a concurrent stream landed a module
mid-round. Nothing here depends on which, but the figure is recorded so a later reader does not
read 439 vs 440 as an instrument inconsistency. Watching 6 forbidden declarations.
**All eight: `watched declarations in cone: none of 6`, `own value is a hole: false`, `cone reaches
sorryAx: false`.**

| name (exactly as printed) | module | arity | cone |
| --- | --- | --- | --- |
| `Lean4Lean.VEnv.NoNestedN` | `…Verify.Inductive.ProjNoNested` | 1 | 208 |
| `Lean4Lean.VEnv.NoNestedN.addInductR_of_tr` | `…Verify.Inductive.RestoreFaithful` | 16 | 3995 |
| `Lean4Lean.NestedWit.nfnAux_tyLvls_wf` | `…Verify.Inductive.ValAtPrice` | 6 | 1280 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_tyLvls_wf` | `…Verify.Inductive.ValAtParam` | 6 | 755 |
| `Lean4Lean.VLevel.WF.of_mapM_ofLevel` | `Lean4Lean.Theory.VLevel` | 6 | **558** |
| `Lean4Lean.VNestedOcc.argsTypedH_of_ty` | `…Verify.Inductive.ArgsTypedSupply` | 6 | 655 |
| `Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_AddNested` | `…Verify.Inductive.NestedRestoreWit` | 17 | 2658 |
| `Lean4Lean.VInductDecl'.KFresh` | `Lean4Lean.Theory.Inductive.NestedBuild` | 4 | 7 |

`VInductDecl'.KFresh` carries the same `[NO PROOF TERM: … says NOTHING about satisfiability —
price the witnesses]` caveat as `OccResidue`; its model is the `⟨pfnEnv_constsClosedC h,
nfnK_not_contains h, fun _ _ _ _ => pfnOcc_args_noK⟩` triple supplied inside `nfnAux_built'`
(read at `NestedRestoreWit.lean`:722-731), which M1 priced clean at cone 1668 via
`nfnResult_occResidue` in the same theorem.

## §2 The three classifications

### A. `Built` — **general modulo named lemmas** (`OccResidue`, `KFresh`, `blockNames.Nodup`)

`Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_built` (M1: cone 2061, arity 14, both
lines clean) concludes `D.Built (r.mkRestore types D.uvars D.np ls as) K env occ` from
`r.RestoreData types D K as` plus exactly five things: `hnd : D.blockNames.Nodup`,
`hkf : D.KFresh K env occ`, the two parameter-choice equations `hl`/`ha` (`ls j = (occ j).lvls`,
`as j = (occ j).args` — the docstring is right that these are a *choice*, not a hypothesis, because
`ls`/`as` are `mkRestore` parameters the caller supplies), and
`hres : r.OccResidue types D K env … occ`. Four of `Built`'s nine clauses come from `RestoreData`
(three presentation clauses + `own` via `h.mkRestore_ownId`), four from `OccResidue`, two from
`hnd`/`hkf`. So: **not open, and not already general** — general modulo three named premises.

Why "general modulo" and not "open in substance": the residue is **satisfiable and non-vacuous, and
both bounds are proved.** `Lean4Lean.NestedWit.nfnResult_occResidue` (M1: cone 1668, clean) is a
model of all four `OccResidue` clauses; and `Lean4Lean.NestedWit.nfnResultBadHead_not_occResidue` /
`…nfnResultBadHead_not_built` are the *negative* bound — at a perturbed `Result` whose `RestoreData`
and whose four name-discipline obligations all still hold, `OccResidue.head` is **false** and `Built`
fails at its `tyName` clause. That pair is the honest proof that `OccResidue` is not derivable from
`RestoreData`, i.e. that this decomposition is tight rather than a place to hide work.
`mkRestore_AddNested` (M6: cone 2658, clean) carries it through to the whole nested step.

**What is *not* closed inside A, stated so it is not read as closed:** `KFresh`'s three clauses
(`env.ConstsClosedC`, `∀ n ∈ K, ¬ env.contains n`, companion-spine cleanliness) are about
`D`/`K`/`env`/`occ` and nothing in `RestoreData` or `OccData` mentions them — `NestedRestoreWit.lean`
§6 says so explicitly ("Ruling 116d's cost is still a hypothesis, not a theorem"). And `nodup`'s
companion half would come from `RestoreData.auxNodup` plus the `IsNestedName` separation, "and that
derivation is not done here". So A's residue is three named premises, one of which (`OccResidue`)
has a model and a matching refutation, and two of which are stated but underived.

### B. `FreshIn` — **ALREADY GENERAL**, at `Lean4Lean.VIndRestore.csubstTy_freshIn`

`Lean4Lean.Theory.Inductive.TeleMove2`, arity 6, **cone 1093**, own value is a hole: false, cone
reaches sorryAx: false, watched in cone: none of 6 (M1).

```
theorem csubstTy_freshIn {env E₁ : VEnv} {R : VIndRestore} {D : VInductDecl'}
    {K : List Lean.Name} (h₁ : env.addIndTypes D = some E₁) : (R.csubstTy D K).FreshIn env
```

`R`, `D`, `K` are all implicit and unconstrained; the sole hypothesis is the type-staging equation,
which every consumer already has. **The brief's claim is correct and this is the answer: `FreshIn` is
already general, and I stopped working on it**, per instruction. Two independent corroborations were
already in the tree before this round: `RestoreFaithful.lean`:263's discharge table states it as a
deliberate *negative* result ("the `Restrict*` files' freshness hypothesis is not one of the things
the measurement buys, and a second route to it would be a duplicate"), and `NestedTele.lean`:1123
records the `csubst` sibling the same way. One live trap for whoever consumes it, from
`TeleMove2.lean`:90: the environment is **`env`, before `addIndTypes`** —
`(R.csubstTy D K).FreshIn env₃` is *false* whenever `K` names a member of `D`. Getting the
environment wrong here does not fail to compile, it proves something else.

### C. `tyLvls`-well-formedness — **OPEN**

The obligation, from `SpineClosedLand.lean`:207-215 and :222-231:
`∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ l ∈ R.tyLvls j, l.WF D.uvars`.

Evidence, in the order it accumulated:

1. **`RestoreData` cannot reach it, structurally.** `RestoreData` has no level field at all (its
   `args` field constrains `as`, nothing constrains `ls`); and `mkRestore` sets
   `tyLvls j := if j < types.length then VLevel.params uvars else tyLvls j`, while
   `RestoreData.companions` gives `T.name ∈ K ↔ types.length ≤ j`. So the `∈ K` guard selects
   **exactly** the `else` branch — the unconstrained parameter. The own-member branch, which
   `RestoreData` *could* have helped with, is the branch the guard excludes.
2. **`Built` relocates it rather than discharging it.** `Built.tyLvls` (`NestedBuild.lean`:771) is the
   equation `R.tyLvls j = (occ j).lvls`, not a WF clause, so with `Built` in hand C becomes
   `∀ l ∈ (occ j).lvls, l.WF D.uvars` — a fact about the occurrence.
3. **`Occurs`/`OccursN` do not supply it, and the near-miss is at the wrong block.**
   `Occurs.lvls_len` is `N.lvls.length = N.decl.uvars` — the **foreign** block's universe count —
   whereas C wants WF at `D.uvars`, the **new** block's. No clause relates the two.
4. **M3: nothing general concludes it.** 29 constants mention both `VLevel.WF` and
   `VIndRestore.tyLvls`; one is the field `Lean4Lean.RestrictStepCfg.lvls`, the rest are either
   `RestrictStepCfg` eliminators or **consumers** carrying it as `hlvl`. The only two plain
   declarations that conclude it are block-specific witnesses:
   `Lean4Lean.NestedWit.nfnAux_tyLvls_wf` (cone 1280) and
   `Lean4Lean.InductiveDeclExamples.ntreeAux_tyLvls_wf` (cone 755).
5. **M4 + source: the one structure that looks like it discharges it is circular.**
   `Lean4Lean.VNestedOcc.ArgsTypedH.lvls` is literally the clause `∀ l ∈ N.lvls, l.WF D.uvars`, and
   the only non-eliminator producer `Lean4Lean.VNestedOcc.argsTypedH_of_ty` (cone 655) **takes it as
   hypothesis `hlvls` and stores it verbatim**. Same for `RestrictStepCfg.lvls`. So C is *bundled*
   into two configuration structures and *proved* nowhere in general.

**The obstruction, stated precisely.** `occ` enters the flip existentially (`VEnv.AddNestedB`,
`AddNested`, `Built`, `KFresh` all take `occ : Nat → VNestedOcc` as a parameter) and **no predicate
in the tree ties `(occ j).lvls` to any level list the checker has validated.** `Occurs` constrains
their count against the wrong block; `OccResidue`'s four clauses are about `member`, `occurs`,
`ctorName_inv` and `head`, none of them about levels. Until `occ`'s levels are connected to the
`Lean.Level`s `replaceIfNested` read off the occurrence `I.{I_lvls}`, C has no source.

**Smallest sufficient premise, and the general lemma that finishes it.** The lemma is already in the
tree: `Lean4Lean.VLevel.WF.of_mapM_ofLevel` (`Theory/VLevel.lean`:185, M6: arity 6, **cone 558**,
clean) —
`List.mapM (VLevel.ofLevel Us) us = some us' → ∀ l ∈ us', l.WF Us.length`.
So the smallest sufficient premise is a *plumbing* one, not a level-theoretic one:

> `hocclvl : ∃ (lvls : Nat → List Lean.Level), ∀ j, List.mapM (VLevel.ofLevel Us) (lvls j) = some (occ j).lvls`
> together with the arity fact `Us.length = D.uvars`

— i.e. **"each occurrence's recorded levels are the translation, under the declaration's own level
parameters, of a `Lean.Level` list"**. With that, C is `VLevel.WF.of_mapM_ofLevel` plus
`Built.tyLvls` plus the `companions` guard, and nothing else. `NestedOccData.lean`:929 already
carries a `List.mapM (VLevel.ofLevel Us) ls = some ls'` hypothesis of exactly this shape (in
`TrExprS.instL`'s side conditions), and §9(A) there records that `replaceIfNested` supplies both it
and the arity match, "`I_lvls` comes from a well-formed constant application `I.{I_lvls}` and
`J_info.levelParams.length = I_lvls.length` is the `numLevelParams` check". So the premise is not
speculative — it is the same side condition the `member` commutation already needs, which means C
and `OccResidue.member` should be paid together rather than separately.

I did **not** write the lemma. Per the brief's budget ("at most a small Lean file, and only if a
classification needs a proof to be honest"), C's classification is a *negative* one carried by M3/M4
plus a source reading of `argsTypedH_of_ty`, and stating the sufficient premise does not require a
proof to be honest. Naming it as "general modulo `VLevel.WF.of_mapM_ofLevel`" would have been the
dishonest option: that lemma is general and clean, but the premise it needs is not in the tree, so
the obligation is **open**, not "modulo a named lemma".

## §3 The `head` residual — verdict: **NEITHER, and it splits in two**

`Lean4Lean.ElimNestedInductive.Result.presentedHead_clean_of_declared` (M1: cone 671, clean) reduces
`RestoreData.head` to two premises, and they have **different** answers:

* **`hnn : venv.NoNestedN`** — needs the wider check. `VEnv.NoNestedN`
  (`ProjNoNested.lean`:379, M6 cone 208) is `∀ {n}, env.contains n → ¬ IsNestedName n`.
  `Lean4Lean.VEnv.NoNestedN.addInductR_of_tr` (M6: cone 3995, clean) preserves it across the
  *inductive* step from the gate `NoNestedDeclNames types` — but only that step.
  `docs/decision-nested-prefix-all-decls.md` records the machine-checked table (`#eval` at
  `RestoreFaithful.lean`:448, fails the build if a flag flips): `inductive _nested.Zzz` **REJECTED**,
  `axiom _nested.zzz` **ACCEPTED**, `def _nested.ddd` **ACCEPTED**. So the induction on `TrEnv'`
  has nothing to supply `NoNestedN.addConst`'s name hypothesis in the `axiom`/`defn`/`opaque`/`quot`
  cases, and `hnn` is exactly what the one-line `checkNoNestedAuxName v.name` in `checkConstantVal`
  would buy.
* **`hdecl : ∀ j t, r.types[j]? = some t → types.length ≤ j → venv.contains (r.presentedHead t.name)`**
  — **independent of both.** M5 is the measurement: **one** constant in the whole 439-module
  population mentions both `VEnv.contains` and `Result.presentedHead`, and it is
  `presentedHead_clean_of_declared` itself, the consumer. Nothing concludes `hdecl`, at any block.
  And it cannot be bought by either check on principle: the gate and the wider check are both
  *rejections of names carrying a prefix*, whereas `hdecl` asserts **containment** — that a
  particular computed name **is** declared. A check that refuses declarations never proves one
  exists. `RestoreFaithful.lean`:304's own docstring says the same thing from the other side ("a
  statement about `aux2nested`'s values, not about names, so §1 cannot supply it").

**So: the existing gate discharges neither half.** The decision doc's sentence that a global
invariant "is the route that retires it" is right about `hnn` and, read as covering the whole field,
overstates the case for `hdecl` — that half is a fact about `aux2nested`'s value map
(`replaceIfNested` found the head constant *by looking it up in the ambient environment*, which is
where the proof will come from), and it is independent of both the PR #45 gate and the wider check.
This is the round's one real surprise against my §0 priors, which put 55% on "needs the wider check"
as a single answer; the honest answer is that the field has two premises with two different verdicts.

## §4 The brief's three pre-checks, confirmed

| claim | verdict | evidence |
| --- | --- | --- |
| `Lean4Lean.VIndRestore.csubstTy_freshIn` proves `FreshIn` from type-staging success alone | **CONFIRMED** | M1 (cone 1093, clean, none of 6) + signature at `TeleMove2.lean`:96-98: only hypothesis `env.addIndTypes D = some E₁`, `R`/`D`/`K` free |
| `auxRec` removable via `Lean4Lean.NoNestedDeclNames.auxRecName` | **CONFIRMED** | M1 (cone 3588, clean); `NestedRestore.lean`:307's own docstring names it and the underlying general lemma `not_isNestedName_appendIndexAfter'_mkRecName` |
| `ownName`/`ownCtor` discharged by `…Result.ownName_of_gate` / `.ownCtor_of_gate` | **CONFIRMED** | M1 (cone 5796 each, clean); both take `hgate : NoNestedDeclNames types` + `run` success only |
| `head` reduced only, residual a fact about `aux2nested`'s *values* | **CONFIRMED, and sharper** | M5: zero declarations conclude `hdecl`; §3 splits the field into `hnn` (wider check) + `hdecl` (independent of both) |

## §5 Housekeeping

* **Nothing built, nothing edited outside this file.** No `Lean4Lean/Verify/Inductive/RestoreDataClassify.lean`
  was created: the round's three classifications are two positive citations of existing clean
  declarations and one negative result carried by `shape.lean`, none of which needs new Lean to be
  honest. So no sorry-census run is owed (the brief conditions it on having built something), and
  the 13 / NOT BUILT 0 figure is neither confirmed nor disturbed by this round.
* **No state-changing git.** `docs/vacuity-ledger.md` untouched.
* Six script calls, each logged before the next was made (M1 `exists`, M2 `shape` (tail, my error),
  M3 `shape`, M4 `shape`, M5 `shape`, M6 `exists`). No `users.lean` call was needed — no
  classification turned on a dependant count.
* **Priors scorecard.** B: correct (90% → confirmed). A: correct (70% → confirmed, and the
  anti-vacuity pair made it firmer than I expected). C: **wrong in its carrier** — I predicted
  "general modulo a premise on `ls`" at 65% and it is open, with the obligation living on `occ`, not
  `ls`; the 20% I put on "open" was the right branch for the wrong reason. `head`: wrong — I put 55%
  on a single "needs the wider check" answer and the field has two premises with different verdicts,
  the one I rated 30% ("independent of both") being right for `hdecl`. `auxRec`: correct (85%).
  "No new Lean": correct.
