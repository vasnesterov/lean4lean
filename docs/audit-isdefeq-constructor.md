# Pricing: a new `VEnv.IsDefEq` constructor for structure eta (`StructEtaG`)

*Round of 2026-09-03.  Deliverable: a costing and a soundness verdict, not an edit.  No file
outside this document was changed; `VEnv.IsDefEq` was **not** touched.*

Every row is tagged **[measured]** (I ran the named instrument this round) or **[source]** (read
off source, not re-run).  Nothing is from memory.

## 0. Instrument

**The instrument behind every enumeration below.** A Lean metaprogram run against the built `.olean`s:

```
~/.elan/bin/lake env lean --run /tmp/pricing/census.lean     # eliminator-site census
~/.elan/bin/lake env lean --run /tmp/pricing/census3.lean    # mirrors, cone, auto-gen filter
```

It imports **340 of the 346 `Lean4Lean.*` modules** (346 = every `.lean` under `Lean4Lean/` plus
`Lean4Lean.lean`; the 6 exclusions are `Lean4Lean.Replay`, `Lean4Lean.Tests(.Toolchain)`,
`Verify.Inductive.{CanonGapMeasure,MemberRedexScan,UniformOccMeasure}` — all of which either
clash with Foundation's `ImportGraph` on `Lean.Environment.importsOf` or import one that does —
**plus all of `Lean4Lean/Experimental/`**, which cannot be imported as a whole: `ShapeLogRel.olean`
does not exist and `Experimental.MoreStepIndexed`/`Experimental.LogRel` both declare
`Lean4Lean.SExpr.Classifier`).  For each declaration it takes
`type.getUsedConstantsAsSet ∪ (value? (allowOpaque := true)).getUsedConstantsAsSet` — the
`allowOpaque` that `scripts/cone-measure.lean`'s docstring warns about, without which every
theorem reports zero dependencies — and asks whether it **directly** names an eliminator of the
family.  `rg` was not used anywhere (it is only a shell function here); `grep` was used only to
cross-check, never as the basis of a count.

---

## Summary table

| # | item | measurement | verdict |
|---|---|---|---|
| 1 | "**65** induction sites over the `IsDefEq`/`IsDefEqStrong`/`HasTypeStrong`/`HasTypeStratified` family" | the same instrument (`.rec` mentions only) gives **79** today, not 65 (per relation 25 / 25 / 19 / 10 against the doc's 22 / 20 / 14 / 10).  A correct instrument (every eliminator flavour, auto-generated declarations filtered out) gives **111 hand-written / 173 total**. | **the brief's number is stale, and the instrument behind it under-counts.**  Both figures are floors — see §1.3 |
| 2 | …but is 111 the **migration set**? | **No: 67 of the 111 are `HasTypeStrong` (47) and `HasTypeStratified` (20), and neither needs a new arm.**  Both are *separate, non-mutual, typing-only* inductives (`Strong.lean:99`, `Strong.lean:947`): 9 constructors each, **no `extra`, no `eta`, no `beta`, no `proofIrrel`**.  A defeq rule whose two endpoints differ adds no constructor to either. | **the real migration set is 44** = 22 `IsDefEq` + 22 `IsDefEqStrong`, disjointly |
| 3 | "all 65 in `Theory/`, **none in `Verify/`**" | true for the four-family: **0** of the 111 are in `Verify/`.  **But it stops one relation too early.** `IsDefEq.church_rosser` is one of the 22 and it is **in the refinement cone**; mirroring the rule into `ParRed`/`CParRed` adds 30 more sites, **6 of them in `Verify/`** (`Verify/Typing/ConstSpine.lean` 3, `Verify/QuotAppParams.lean` 3). | **"none in `Verify/`" is true only if you never re-prove confluence, and confluence is in the cone** |
| 4 | cone position of the 44 | **23** in `Bridge.not_leanTTConsistent_of_kernel_proves_false`'s cone (identical for `Bridge.addDeclWF` and `Bridge.kernel_sound_of`); **21** in `leanTTConsistent_of_consistent_zfcInacc`'s (the model half); **7 already sit on top of a `sorryAx`** | the tax is real but under half the tree |
| 5 | **model obligation** | a new `IsDefEqStrong` constructor, a new case in `SetModel.soundAbove`, **and a fifth field on `CoherentOn`** — which has exactly four (`const_congr`, `const_type`, `defeq`, `defeq_type`; `OracleOK` has exactly two). | **the existing interpretation cannot discharge it**, §3 |
| 6 | can the model be extended to discharge it? | `Theory/SetModel/` contains **no** positive-field pairing lemma — every one is `…_of_zero_field` / `…_of_no_fields` — and the whole `SetModel/` tree **never mentions `projTerm`, `projTermG`, `projAll` or `etaExpansion`** (grep, 60 files). | **not refuted, but the model side is empty at the field counts `StructEtaG` quantifies over** |
| 7 | does it **narrow `kernel_sound`**? | No.  `kernel_sound` (`Verify/Soundness.lean:185–191`) mentions no `Lean4Lean.Theory` constant at all.  Enlarging `IsDefEq` **transfers** debt: the refinement half has `IsDefEq` in *positive* position (gets easier), the consistency half in *negative* position (gets harder).  Both halves are hypotheses of `Bridge.kernel_sound_of`. | **no narrowing; a debt transfer plus a 44-arm syntactic tax** |
| 8 | cheaper alternative A — eta as a `VDefEq` in `env.defeqs`, consumed by the **existing** `extra` constructor (zero new constructors, zero migration sites, and `CoherentOn.defeq` already quantifies over every `df`) | **CLOSED, and this is the most useful negative result in the round.**  `Params.extra_pat` (`ChurchRosser.lean:84`) requires *every* `df ∈ env.defeqs` to be `mkLams Δ L` with `p.Matches L m1 m2`; `Pattern`'s only base case is `.const c` (`Pattern.lean:8–11`) and `Params.pat_not_var` forbids var-headed patterns.  Structure eta's λ-peeled left side is `.bvar 0`. | **not expressible as a `VDefEq` without making `Params` uninstantiable — and `Params`, `ParRed`, `CParRed`, `church_rosser` are all in the refinement cone** |
| 9 | cheaper alternative B — the `Prop` fragment via the existing `proofIrrel` | genuinely constructor-free, but covers only blocks at `Sort 0`.  Non-equivalent: `StructureExamples.sigmaDecl` / `subtypeDecl` are `isLE := true` structures at `Type u` where the `proofIrrel` premise is unavailable. | **halves the residual, cannot close it; the checker does not test the universe** |
| 10 | a **precondition** nobody has priced: is the rule even *true*? | `IsDefEqStrong.hasType'` (in the refinement cone) forces the new case to produce `HasTypeStrong Γ (D.etaExpansionG …) ((const S us).mkApp ps)` — i.e. the η-expansion must be **well typed**.  That is `projTermG_hasType`, named "**wall 2**" at `Verify/TypeChecker/InferType.lean:467` and open. | **settle wall 2 first: if it fails, the constructor makes the specification assert a defeq with an ill-typed side — wrong, not merely expensive** |
| 11 | vacuity, reported separately as instructed | `StructEtaG` is satisfied today only vacuously, so everything derived *from* it is hole-free and discharges nothing.  Additionally: there is exactly **one** witness that `StructEtaG`'s premises are jointly satisfiable (`MutField.declEnv_structEtaG_premises`, `EtaStructG.lean:487`), at `decl.isLE = false` with a single **`Prop`** field.  **No witness anywhere exercises F17's `isLE = true` disjunct** — i.e. the data-carrying structures the kernel actually η-expands (`Prod`, `Sigma`, `Subtype`) have no satisfiability certificate. | the residual's non-vacuity is established at *one* shape, not at the shape that matters |

**Bottom line.**  The route is **not closed by the model** — so I am not retiring it — but it is **not the minimal route either**, and it has an unpriced precondition ahead of it.  Recommended order: **wall 2 (`projTermG_hasType`) → the `CoherentOn` denotation field → positive-field pairing → then the constructor.**  Adding the constructor first buys 44 arms, 23 of them in the goal's cone, on a rule that is not yet known to be *true* at the instances that motivate it.

---

## 1. The site count, measured

### 1.1 Reproducing the brief's instrument, and where it lands today  **[measured]**

`docs/handoff-isdefequ.md` §4 counted "declarations whose type-or-value mentions each
eliminator", scope "every `Theory/Typing/*.lean` plus the `Verify/Bridge.lean` closure", and got
65.  Re-running **the same predicate** (`X.rec` mentioned directly, no auto-generated filter) over
the whole tree:

| eliminator | §4 | today | delta |
|---|---|---|---|
| `VEnv.IsDefEq.rec` | 22 | **25** | +3 |
| `VEnv.IsDefEqStrong.rec` | 20 | **25** | +5 |
| `VEnv.HasTypeStrong.rec` | 14 | **19** | +5 |
| `VEnv.HasTypeStratified.rec` | 10 | **10** | 0 |
| total | **65** | **79** | **+14** |

New modules explain the drift: `SortInvIndep` (+2 on `IsDefEqStrong`), `InjOneFact`, `InjPiRogue`,
`RetypeAdmissible`, `ProofRetypeHeads` (+2 on `HasTypeStrong`), `BaseUniqChain`, `RetypeCase`,
`ConstVar`, `ConstSubstNested`, `StrengthenNarrow`.  **So the first thing the brief gets wrong is
the number: it is 79 by its own instrument, and 65 is two-plus rounds stale.**

### 1.2 The instrument under-counts, for a nameable reason  **[measured]**

`.rec` is what `induction … with` elaborates to.  `cases`, `rcases`, `obtain`, `match` and `nofun`
elaborate to `casesOn` (directly, or through a per-declaration matcher `….match_N` whose *value*
names `casesOn`).  Counting only `.rec` misses every one of those.  Widening to
`{rec, casesOn, recOn, brecOn, binductionOn, below, ibelow, ndrec, ndrecOn, recAux, casesAux}` and
subtracting auto-generated declarations (last component in the generated-name list, or any
component in `{below, brecOn, rec, casesOn, …}`, or a leading `_`):

| relation | total mentions | hand-written | auto-generated |
|---|---|---|---|
| `VEnv.IsDefEq` | 40 | **22** | 18 |
| `VEnv.IsDefEqStrong` | 40 | **22** | 18 |
| `VEnv.HasTypeStrong` | 60 | **47** | 13 |
| `VEnv.HasTypeStratified` | 33 | **20** | 13 |
| **union of the four** | **173** | **111** | 62 |

Directory split of the 111: `Theory/Typing` **109**, `Theory/SetModel` **2**
(`SetModel/Consts.lean`, `SetModel/SoundInduction.lean`), `Verify/` **0**.

### 1.3 …and 67 of the 111 are not part of the migration at all  **[measured]**

`HasTypeStrong` (`Theory/Typing/Strong.lean:99`) and `HasTypeStratified` (`Strong.lean:947`) are
**separate, non-mutual** inductives — `HasTypeStrong`'s `defeq` constructor mentions
`IsDefEqStrong env uvars Γ e1 e2 A` as an already-built *parameter*, and `HasTypeStratified`'s
mentions plain `IsDefEq`; the source even says so ("*functionally* a mutual inductive type, but
using a bool index …" — meaning the `HasTypeStrong`/`:!` pair, not a mutual block with
`IsDefEqStrong`).  Their constructor lists are `bvar, sort', const, app, lam, forallE, base,
defeq` — **9 each, with no `beta`, `eta`, `proofIrrel` or `extra`.**

That is decisive.  A structure-eta rule has **two different endpoints** (`e` on the left, the
η-expansion on the right), exactly like `beta`, `eta`, `proofIrrel` and `extra`.  Such a rule
contributes no new *typing* judgement, so neither typing relation gains a constructor, so neither
relation's 47 + 20 = **67** eliminator sites needs a new arm.  Confirmed structurally by the
census: the L4L inductives carrying an `extra` and/or `eta` constructor are exactly

```
VEnv.IsDefEq (13 ctors)   VEnv.IsDefEqStrong (13)  VEnv.IsDefEqRaw (12)  VEnv.IsDefEqE (14)
VEnv.Stratified (19)      VEnv.ParRed (8)          VEnv.CParRed (8)      VEnv.ParRedK (9)
VEnv.ParRedKn (9)         VEnv.WHRed (4)
```

— `HasTypeStrong` and `HasTypeStratified` are absent from that list.

### 1.4 The migration set, with cone position  **[measured]**

| set | sites | in refinement cone | in model cone |
|---|---|---|---|
| `IsDefEq` alone | 22 | 11 | 11 |
| `IsDefEqStrong` alone | 22 | 12 | 10 |
| **`IsDefEq` + `IsDefEqStrong` (the migration)** | **44** | **23** | **21** |
| `HasTypeStrong` alone (**not needed**) | 47 | 12 | 0 |
| `HasTypeStratified` alone (**not needed**) | 20 | 17 | 0 |
| all four (the brief's scope) | 111 | 52 | 21 |
| + `IsDefEqRaw`, `IsDefEqE` (forced by `IsDefEq.raw`, `IsDefEq.toE`) | 47 | 23 | 21 |
| + `ParRed`, `CParRed` (forced by `IsDefEq.church_rosser`) | **74** | **32** | 21 |
| every relation with an `extra`/`eta` constructor | 144 | 32 | 21 |

Refinement cone = `Bridge.not_leanTTConsistent_of_kernel_proves_false` (8871 L4L constants;
`Bridge.addDeclWF` 8826 and `Bridge.kernel_sound_of` 8873 give the same three counts).  Model cone
= `leanTTConsistent_of_consistent_zfcInacc` (2194).  `kernel_sound` itself is a bare `sorry`:
cone 787, **0** of the 111 in it — so, as `docs/handoff-eta.md` finding 5 says, nothing here can
move guard 2 today.

### 1.5 The 22 `IsDefEq` arms, named, with cone flags  **[measured]**

`REF` = in the refinement cone, `MOD` = in the model cone, `HOLED` = already transitively
depends on a `sorryAx`.

| # | declaration | module | flags |
|---|---|---|---|
| 1 | `VEnv.IsDefEq.strong'` | `Typing/Strong` | REF MOD |
| 2 | `VEnv.IsDefEq.weakN` | `Typing/Lemmas` | REF MOD |
| 3 | `VEnv.IsDefEq.instN` | `Typing/Lemmas` | REF MOD |
| 4 | `VEnv.IsDefEq.instL` | `Typing/Lemmas` | REF MOD |
| 5 | `VEnv.IsDefEq.mono` | `Typing/Lemmas` | REF MOD |
| 6 | `VEnv.IsDefEq.isType'` | `Typing/Lemmas` | REF MOD |
| 7 | `VEnv.IsDefEq.levelWF` | `Typing/Lemmas` | REF MOD |
| 8 | `VEnv.IsDefEq.closedN'` | `Typing/Lemmas` | REF MOD |
| 9 | `VEnv.IsDefEq.sort_inv'` | `Typing/Lemmas` | REF MOD |
| 10 | `VEnv.IsDefEq.forallE_inv'` | `Typing/Lemmas` | REF MOD |
| 11 | `VEnv.IsDefEq.church_rosser` | `Typing/ChurchRosser` | REF, **HOLED** |
| 12 | `VEnv.IsDefEq.constsIn` | `SetModel/Consts` | MOD |
| 13 | `VEnv.IsDefEq.mono_uvars` | `Typing/Strong` | — |
| 14 | `VEnv.IsDefEq.substC` | `Typing/ConstSubst` | — |
| 15 | `VEnv.IsDefEq.noCSubst'` | `Typing/ConstSubst` | — |
| 16 | `VEnv.IsDefEq.substCD` | `Typing/ConstSubstNested` | — |
| 17 | `VEnv.IsDefEq.raw` | `Typing/RawDefEq` | — |
| 18 | `VEnv.IsDefEq.toE` | `Typing/Enlarged` | — |
| 19 | `VEnv.Strengthening.of_typing` | `Typing/Strengthen` | **HOLED** |
| 20 | `VEnv.Strengthening.of_typing_narrow` | `Typing/StrengthenNarrow` | **HOLED** |
| 21 | `loop_conv_collapse` | `Typing/CycleConv` | — |
| 22 | `cvarMain` | `Typing/ConstVar` | — |

The 22 `IsDefEqStrong` arms include `IsDefEqStrong.{weakN, instN, instL, mono, isType', hasType',
forallE_inv', defeq, retypes, stratifyN}`, `EqUpToLevels.{defeq, instL}`, `SetModel.soundAbove`,
and five inversion lemmas — `IsDefEqU.{sort_forallE_inv, const_sort_inv, const_forallE_inv,
const_app_inv, forallE_inv_of_rigidPi}`, four of them **HOLED**.

**7 of the 44 already sit on a `sorryAx`** (`church_rosser`, `Strengthening.of_typing`,
`of_typing_narrow`, and the four `const_*`/`sort_forallE` inversions).  Cross-check on the
instrument: it finds exactly **13** direct `sorryAx` holes in the tree, matching
`scripts/sorry-census.lean`'s standing TOTAL of 13, name for name.

### 1.6 Why "mechanical" is the wrong word for most of the 44  **[source]**

`handoff-isdefequ.md` §4 argued every non-`uniq` case is mechanical, "for one structural reason:
`retype` does not move the endpoints, only the type index".  **That reason does not transfer.**
A structure-eta rule *does* move the endpoints, and moves them to a term built by
`D.etaExpansionG T C us ps j e` = `(const C.name us).mkApp (ps ++ projAllG …)`, where each
`projAllG` component is a full recursor spine `D.projTermG T C us ps [] i j e`.  So arms 2–4, 8,
9, 12, 14–16 each need a **commutation lemma for `etaExpansionG`** — that lifting, instantiation,
level-instantiation, closedness, constant-occurrence and constant-substitution each pass through a
padded recursor spine.  None of those lemmas exists.

Compare the one existing endpoint-moving rule with an *environment-supplied* right-hand side:
`extra`.  Its arms are one-liners in all 22 lemmas (`| extra h1 _ _ => … .instL`) for a single
reason — **`VDefEq.lhs`/`rhs`/`type` are closed terms**, so `liftN`, `instN`, `instL` and
`NoCSubst` are all trivially stable on them.  A constructor whose right-hand side is open in
`Γ`, `ps` and `e` gets none of that.

---
## 2. What the constructor would have to look like, and the two relations it drags with it

The shape to add is `StructEtaG`'s, not `StructEta`'s (`docs/handoff-eta.md` §7.1), i.e. verbatim
the body of `VEnv.StructEtaG` (`Verify/TypeChecker/EtaStructG.lean:172`) as a constructor of
`VEnv.IsDefEq`:

```
| structEta :
  env.IsStructureG S D j T C → T.indices = [] → C.recFields = [] →
  us.length = D.uvars → (∀ l ∈ us, l.WF uvars) → ps.length = D.np →
  env.HasArgs uvars Γ (D.params.map (VExpr.instL us)) ps →
  Γ ⊢ e : (VExpr.const S us).mkApp ps →
  (D.isLE = true ∨ ∀ k, k < C.fields.length → (C.fields.getD k default).lvl.inst us ≈ .zero) →
  Γ ⊢ e ≡ D.etaExpansionG T C us ps j e : (VExpr.const S us).mkApp ps
```

**Note the import direction this forces.**  `VEnv.StructEtaG` and `VEnv.IsStructureG` live in
`Verify/TypeChecker/EtaStructG.lean` today, and `etaExpansionG`/`projTermG` in
`Theory/Inductive/*` — but `Theory/Typing/Basic.lean` currently imports only
`Theory/Theory.VEnv`.  Putting the constructor in `Basic.lean` means `Theory/Typing/Basic.lean`
must import the whole inductive-declaration development (`VInductDecl'`, `VIndType`, `VIndCtor`,
`projTermG`, `IsStructureG`), which today sits **downstream** of `Theory/Typing/` — `Decl.lean`
imports `Theory/Typing/*`.  **[measured: `Theory/Inductive/Decl.lean`'s header imports
`Lean4Lean.Theory.Typing.…`; `Basic.lean` imports only `Lean4Lean.Theory.VEnv`.]**  So the
constructor cannot be added without either (a) hoisting the whole `VInductDecl'` datatype and
`projTermG` above `Theory/Typing/Basic.lean`, or (b) parameterising `IsDefEq` by an abstract
eta-rule table.  **This is a cost the brief's 65-site figure does not contain at all**, and it is
the largest single item in the price: it is a re-layering of the theory's import graph, not an
arm-by-arm migration.

### 2.1 `IsDefEqStrong` is forced; `HasTypeStrong`/`HasTypeStratified` are not

`SetModel.soundAbove` inducts on `IsDefEqStrong`, not `IsDefEq` (`SoundInduction.lean:226`, and
the module doc explains why: `appDF` needs the intermediate sort derivations).  The only bridge is
`IsDefEq.strong'` (arm 1), which inducts on `IsDefEq` and produces `IsDefEqStrong`.  So the model
half is reachable only if `IsDefEqStrong` gains a matching constructor — hence 22 + 22 = 44.
`HasTypeStrong` and `HasTypeStratified` gain nothing (§1.3).

### 2.2 `IsDefEqRaw`, `IsDefEqE`, `ParRed`, `CParRed` are forced *conditionally*

`IsDefEq.raw` (arm 17) and `IsDefEq.toE` (arm 18) force matching constructors in `IsDefEqRaw` and
`IsDefEqE`; neither is in any cone, so both can be left broken indefinitely at the cost of two red
files.  `IsDefEq.church_rosser` (arm 11) is different: **it is in the refinement cone**, and its
arm needs the new rule *simulated by parallel reduction* — a new `ParRed` constructor, and the
diamond re-proved with it.  That is +30 sites (`ParRed` ∪ `CParRed`, taking the migration from 44
to 74), **6 of them in `Verify/`**:

```
Lean4Lean.Verify.Typing.ConstSpine   3 sites
Lean4Lean.Verify.QuotAppParams       3 sites
```

Those six are `ParRed`/`CParRed` case-splits (`| extra _ h2 => exact absurd h2.headConst nofun`
and friends), not `IsDefEq` ones — which is why the four-family census correctly reports 0 in
`Verify/` and why the brief's "none in `Verify/`" is nevertheless misleading.

---

## 3. The soundness question: does the set model still validate it?

**Verdict: the model does not refute it, so this does not retire the route — but the existing
interpretation cannot discharge it, and the machinery that would has never been built at the
field counts `StructEtaG` quantifies over.**

### 3.1 The exact new obligation  **[measured]**

`SetModel.soundAbove` (`SoundInduction.lean:226`) is a 13-case induction on `IsDefEqStrong`.  Two
of its cases are discharged **entirely from a hypothesis** rather than from the interpretation:

```
| @constDF … => … hC.const_congr … ; hC.const_type …
| @extra df ls u Γ h1 h2 h3 … => … hC.defeq h1 h2 h3 ; hC.defeq_type h1 h2 h3
```

`hC : CoherentOn M L env₀`, and `CoherentOn` (`InterpSound.lean:720`) has **exactly four fields**:
`const_congr`, `const_type`, `defeq`, `defeq_type`.  `OracleOK` (`Cnst.lean:181`) has **exactly
two**: `congr` and `type`, the second a **membership** (`o n us ∈ (interp … ci.type …).toFun ∅`).

So:

* A new `structEta` case in `soundAbove` has **nothing to appeal to**.  `defeq`/`defeq_type` are
  quantified over `env.defeqs df`, and the eta rule is not in `env.defeqs` (that is the point of
  making it a constructor).  `const_type` pins a constant's value's *membership* in its type, never
  the *identity* of a type former's denotation.
* Therefore the obligation is a **fifth field on `CoherentOn`** (and a matching addition to
  `SetModel.OracleInput`, which is one of the three named inputs of
  `SetModel.upper_bound_of_inputs`).  Its content, in the model's own vocabulary:

  1. **a denotation equation for the type former** — `⟦(const S us).mkApp ps⟧ = Ind₃ (interpSig₃ …) …`
     fibre.  This is `docs/soundness-ledger.md`'s standing item ("define the `.induct` oracle as
     `IndFiber ∘ interpSig₃` and add the denotation equation to `OracleOK`"), unchanged.
  2. **positive-field surjective pairing** — every member of the fibre is
     `⟨tag, ⟨f₁,…,fₙ⟩⟩`.
  3. **a denotation equation for the projection spine** —
     `⟦D.projTermG T C us ps [] i j e⟧ = the i-th component of ⟦e⟧`.

### 3.2 What the model already has, and what it does not  **[measured]**

`Theory/SetModel/UnitEtaPairing.lean` (766 lines) is the pairing development.  Reading every
pairing statement in it:

```
mem_Ind₃_fibre_iff_of_zero_field       Ind₃_fibre_subsingleton_of_zero_field
interpSig₃_fibre_iff_of_no_fields      fldDoms_of_no_fields   ctorFldSet_of_no_fields
recFields_of_no_fields                 slotDoms_of_no_fields  posDoms_of_no_fields
zfSig_fibre_iff  (zfSig = one zero-field constructor per block member)
```

**Every one is gated on `C.fields = []`.**  There is no positive-field pairing lemma anywhere in
`Theory/SetModel/`.  And obligation 3 has no foothold at all: **`grep -rl 'projTerm\|projAll\|etaExpansion' Lean4Lean/Theory/SetModel/` returns nothing** — the model tree has never mentioned the
syntactic projection terms.  The only occurrence of the intent is a design note,
`SetModel/Inductive.lean:241`: "*arbitrary tagged set) so that surjective pairing, hence structure
eta, holds on*" — a comment, not a theorem.

This is exactly the trap the brief flagged: **a one-index test of an all-index hypothesis.**
`StructEtaG` quantifies over `C.fields` of every length (its F17 clause literally reads
`∀ k, k < C.fields.length → …`).  The model's pairing work is complete at length **0** and empty at
every length **> 0**.  `docs/handoff-eta.md` §2's claim B ("the model-side pairing cost was nil")
is true *of the zero-field rule* and does not extend to `StructEtaG`.

### 3.3 Why it is nonetheless not unprovable

The intended interpretation builds an inductive's denotation as the canonical tagged-pair fixed
point `Ind₃`, for which pairing is a *theorem* rather than an assumption — that is what
`mem_Ind₃_fibre_iff_of_zero_field` demonstrates at length 0, with no hypothesis bounding the
carrier `S.Q`.  Obligation 2 at positive field counts is the same argument with a non-empty
`ctorFldSet` product, and obligation 3 then follows from 2 plus the ι-rule denotation (once `e` is
known to be `mk`-headed in the model, the recursor spine reduces).  So the honest reading is:
**bounded, unbuilt, and not blocked** — roughly the size of `UnitEtaPairing.lean` again, on top of
the `.induct` oracle definition that is already the standing item.

**The one thing that would retire the route** is if the rule were *false*.  See §5.

---
## 4. Does it narrow `kernel_sound`?  No — measured, not reasoned from the shape

### 4.1 The statement cannot move  **[measured]**

`Lean4Lean.kernel_sound` (`Verify/Soundness.lean:185–191`) reads

```lean
theorem kernel_sound (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment)
    (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 := by sorry
```

Not one constant of `Lean4Lean.Theory` appears in it — the module doc says as much ("The abstract
type theory (`Lean4Lean.Theory`) is proof machinery, not part of this statement").  So enlarging
`VEnv.IsDefEq` **provably cannot narrow the main theorem**; there is no statement to narrow.  No
frozen file was opened this round.

### 4.2 Where the debt actually goes  **[measured]**

`Bridge.kernel_sound_of` (`Verify/SoundnessAssembly.lean:92`) is the assembly, and it composes two
halves with **opposite polarity in `IsDefEq`**:

| half | theorem | `IsDefEq` polarity | effect of enlarging |
|---|---|---|---|
| refinement (checker → abstract) | `Bridge.not_leanTTConsistent_of_kernel_proves_false` via `Bridge.addDeclWF` → `addDecl.WF` → the `.WF` layer | **positive** (in the conclusion: "checker says true ⇒ `IsDefEqU`") | **easier** — every `.WF` obligation has more ways to be met.  This is exactly why the eta holes reduce to `StructEtaG` at all |
| consistency (abstract → no proof of `False`) | `leanTTConsistent_of_consistent_zfcInacc` → `SetModel.upper_bound_of_inputs` → `soundAbove` | **negative** (in the hypothesis: "derivable ⇒ validated") | **harder** — §3 |

Both halves are hypotheses of the same theorem, so the net is a **transfer**: 23 of the 44 arms
land in the refinement cone as pure tax (they make nothing easier there — they only keep the
already-proved lemmas true), and the 21 in the model cone are where the enlargement is *paid for*.
Measured cone sizes: refinement 8871 L4L constants, model 2194, `soundAbove` 649.

### 4.3 The nine-hole cone

`Bridge.addDeclWF`'s cone contains 23 of the 44, the same 23 as the full-bridge cone
(the two cones differ by 47 constants and by none of the sites).  It contains **no new hole**: the
44 arms are all *existing green theorems* that must stay green.  Of the 13 `sorryAx` holes in the
tree, **7 of the 44 sites already depend on one** (§1.5), so those 7 arms would be written on top
of holed lemmas — new work whose correctness is already conditional.  The enlargement neither adds
nor removes a hole by itself.

---

## 5. The precondition nobody priced: is the rule *true*?

`IsDefEqStrong.hasType'` is one of the 22 `IsDefEqStrong` arms **and is in the refinement cone**.
Its content is that both endpoints of a derivation are typed.  For the new case that means
supplying

```
HasTypeStrong Γ (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)
```

i.e. **the η-expansion must be well typed** — every `D.projTermG T C us ps [] i j e` must be
typeable at its field's type.  That is `projTermG_hasType`, named "**wall 2**" in
`Verify/TypeChecker/InferType.lean:467` and open; the narrow ancestor `realMinor_hasType_gen`
(`Verify/Typing/ProjGenMinor.lean:97`) is proved only modulo `realMinor_hasType_gen'`'s residual
`hiota` premise.

`Verify/TypeChecker/EtaStructG.lean:172`'s own docstring already makes exactly this argument for
the *`noRec`* field and draws the right conclusion:

> `VEnv.IsDefEq` implies both sides are well typed, so if `projTermG` were **not** typeable at a
> recursive one-constructor block, the rule would be *false* there and
> `tryEtaStructCore.WF_of_structEtaG` would be vacuous …

The same reasoning applies one field over, to the rule as a **constructor**: as a hypothesis,
`StructEtaG` being false makes the derived `.WF`s vacuous (bad but inert).  As a *constructor*, it
makes `IsDefEq` assert a definitional equality with an ill-typed side — and then
`IsDefEqStrong.hasType'`, `IsDefEq.isType'` and the four `const_*_inv` inversions become **false**,
not merely unproved, and the model obligation becomes unprovable because there is nothing to
validate.  **So wall 2 is a precondition of the constructor being admissible, not a step in its
proof, and it must be settled first.**

---

## 6. Cheaper alternatives

### 6.1 Eta as a `VDefEq` in `env.defeqs` — **closed**, with a machine-readable reason

This is the obvious cheap route and it is worth stating why it fails, because on its face it
dominates the constructor on every axis measured above: **zero** new constructors, **zero**
migration sites, and `CoherentOn.defeq`/`defeq_type` already quantify over *every* `df ∈
env.defeqs`, so §3.1's obligation would collapse into an existing field.  The tree already carries
schematic rules this way: `VInductDecl'.iotaRule` (`Theory/Inductive/Decl.lean:788`) is
λ-abstracted over its context (`lhs := mkLams Γ' (D.iotaLhs j C)`) and `VEnv.addIndRules` folds
them into `defeqs`; consumers apply and β-reduce.  A `D.etaRule j C` with
`lhs := mkLams (params ++ [S ps]) (bvar 0)` and `rhs := mkLams … (etaExpansionG …)` is the exact
analogue.

**It cannot be done.**  `VEnv.Params` (`Theory/Typing/ChurchRosser.lean:12`), the interface the
whole confluence development is relative to, carries the field

```lean
extra_pat : OnCtx Γ (IsType env univs) → env.defeqs df → (∀ l ∈ ls, l.WF univs) →
  ls.length = df.uvars →
  ∃ Δ L R p r m1 m2, df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
    Pat p r ∧ p.Matches L m1 m2 ∧ … ∧ R = r.1.apply m1 m2
```

— "every `extra` rule of `env` is a `Pat`-registered pattern **under some leading lambdas**", and

* `Pattern` (`Theory/Typing/Pattern.lean:8`) is `| const (c : Name) | app (f a) | var (f)`, whose
  **only base case is `.const c`**; `Pattern.Matches` (`Pattern.lean:96`) bottoms out at
  `Matches (.const c) (.const c ls) …`;
* `Params.pat_not_var : ¬Pat (.var p) r` (`ChurchRosser.lean:94`) rules out a var-headed pattern
  outright.

Structure eta's λ-peeled left side is `.bvar 0` — no constant anywhere — so no `p` matches it.
Reversing the orientation does not help: `mk ps (proj₁ x) … (projₙ x)` is `const`-headed, but
`Matches` assigns each `Path` leaf an **independent** expression, so the pattern would fire on
`mk ps a₁ … aₙ` for arbitrary `aᵢ` and the right-hand side `x` is not recoverable from the matched
pieces (`R = r.1.apply m1 m2`).  **Structure eta is an extensionality principle, not a rewrite
rule; the `defeqs` slot is a rewrite-rule slot.**

Consequence, stated with polarity: `extra_pat` is a *hypothesis*, so adding the eta `VDefEq` does
not make anything false — it makes `Params` **uninstantiable** for exactly the environments the
rule is needed in, hence `IsDefEq.church_rosser` inapplicable there.  `Params`, `ParRed`,
`CParRed` and `church_rosser` are all in the refinement cone **[measured]**, so that is a real
break rather than a cosmetic one.  (Honest caveat: `Params` *is* instantiable today — `quotParams`,
`Verify/QuotAppParams.lean:123`, for the quotient environment — but no instance exists for any
inductive environment, so this break is currently latent rather than active.)

**Non-equivalence, as required.**  This is not a reformulation of `StructEtaG` that I am claiming
is weaker or stronger; it is a *rejected* encoding, and the rejection is the finding.  Nothing was
added to the tree, so no collapse test applies.

### 6.2 The `Prop` fragment via the existing `proofIrrel` — real, partial, already scoped

For a block at `Sort 0`, `Γ ⊢ e ≡ D.etaExpansionG … : (const S us).mkApp ps` follows from the
**existing** `proofIrrel` constructor, given `Γ ⊢ (const S us).mkApp ps : .sort .zero` and the
typing of both sides.  No new constructor, no migration, no model obligation — `proofIrrel` is
already a case of `soundAbove` (`proofIrrel_sound`).

`docs/handoff-eta.md` §5 records this route being abandoned, and gives the step: it needs
`IsStructureG S D j T C → HasArgs (D.params.map (instL us)) ps → HasType ((const S us).mkApp ps)
(.sort (D.lvl.inst us))` plus the same for `C.name`, which the previous stream did not own.  Those
two lemmas *are* derivable in principle from `IsStructureG.decl`'s `addInduct'` history
(`VEnv.addInduct'_types` / `addInduct'_ctors` give the constants, `constDF` gives the typing,
`HasArgs` applies them) — the same route `MutField.declEnv_A` and `declEnv_Amk` already walk
concretely in `EtaResidual.lean`.  **This is the one alternative I would fund**, and it belongs to
whoever owns `Theory/Typing/DeclRules.lean` + `Theory/Inductive/`.

**It does not close the holes, and the non-equivalence is exhibited rather than argued.**
`Theory/Inductive/StructureExamples.lean` carries `sigmaDecl`, `subtypeDecl` and `andDecl`, all
`isLE := true`, and computes their `etaExpansion` concretely (`… = rfl`, lines 316–342).  For
`Sigma`/`Subtype` at `Type u` the `proofIrrel` premise `HasType … (.sort .zero)` is unavailable, so
the `Prop` fragment says nothing there — while `tryEtaStructCore` and `isDefEqUnitLike` **do not
test the structure's universe** (`StructureExamples.lean:325`: "*`tryEtaStructCore` and
`isDefEqUnitLike` do not test the structure's universe, so this is a real call site*").  So the two
`.WF`s still need the non-`Prop` half, and pairing the fragment with a `WF_prop`-style split is the
step `docs/research-structeta.md` §2 marks `[inferred]` and never machine-checked.  Halving, not
closing.

### 6.3 What I checked and rejected

* **Deriving eta from the ι-rule.**  Cannot work in principle: ι fires only on a
  constructor-headed major premise, and the whole content of eta is that an *arbitrary* inhabitant
  is constructor-headed.  Eta is the no-junk property; ι is the computation rule.  Not attempted in
  Lean.
* **Parameterising `IsDefEq` by an abstract rule table** (a field `env.etaRules : … → Prop`
  alongside `defeqs`, with a constructor consuming it).  This is the constructor route with the
  import problem of §2 solved and *identical* site counts — every one of the 44 arms still needs an
  arm, because the constructor still exists.  It removes the re-layering cost, not the migration.
  Worth doing **if** the constructor is ever funded; it does not change the price of the arms.
* **Restricting `StructEtaG` to non-`Prop` blocks** — `handoff-eta.md` §5's abandoned attempt;
  re-reading it, the blocker it names (the block constant's and constructor's typings) is 6.2's
  missing lemma, i.e. the two attempts are gated on the *same* fact from opposite sides.

---

## 7. Where the brief is wrong

Stated plainly, as asked.

1. **"65 induction sites" is stale and the instrument under-counts.**  Its own predicate gives
   **79** today.  A predicate that also catches `cases`/`match`/`nofun` gives **111** hand-written
   (173 with auto-generated declarations).  Neither is the migration cost.
2. **"all 65 in `Theory/`, none in `Verify/`" — true for the four relations, but the four relations
   are the wrong set in both directions.**  Too big: 67 of the 111 are `HasTypeStrong` /
   `HasTypeStratified`, which are separate typing-only inductives with no `extra`/`eta`/
   `proofIrrel` constructor and need **no** new arm.  Too small: `IsDefEq.church_rosser` is in the
   refinement cone, and mirroring the rule into `ParRed`/`CParRed` adds 30 sites, **6 of them in
   `Verify/`**.
3. **The real migration set is 44** (22 `IsDefEq` + 22 `IsDefEqStrong`), 23 in the refinement cone,
   21 in the model cone, 7 already sitting on a `sorryAx`.
4. **The largest cost is not in any site count.**  `Theory/Typing/Basic.lean` imports only
   `Theory/VEnv`; `VInductDecl'`, `projTermG`, `IsStructureG` and `etaExpansionG` all live
   *downstream* of `Theory/Typing/`.  The constructor needs the theory's import graph re-layered
   (or `IsDefEq` parameterised by an abstract rule table).  No site count contains that.
5. **"the model-side pairing cost was nil" does not survive the widening.**  It is nil *at zero
   fields*; `StructEtaG` quantifies over all field counts, and `Theory/SetModel/` has **no**
   positive-field pairing lemma and **never mentions `projTerm`/`projTermG`/`projAll`/
   `etaExpansion`** at all.
6. **There is a precondition ahead of the whole question.**  Wall 2 (`projTermG_hasType`) decides
   whether the rule is *true*.  As a hypothesis, a false `StructEtaG` is merely vacuous; as a
   constructor it makes `IsDefEqStrong.hasType'`, `IsDefEq.isType'` and four inversions **false**.
   Pricing the migration before settling wall 2 is pricing the wrong thing.
7. **One thing the brief got right and I checked twice:** the route is *not* closed by the model.
   I looked for a refutation and did not find one; `mem_Ind₃_fibre_iff_of_zero_field` carries no
   hypothesis bounding the carrier, so the tagged-pair interpretation really does validate pairing
   where it has been developed.

---

## 8. Vacuity, reported separately as instructed

* **`StructEtaG` is satisfied today only vacuously**, so `EtaResidual.lean`'s
  `isDefEqUnitLike.WF_of_structEtaG`, `tryEtaStructCore.WF_of_structEtaG'` and
  `etaHoles_of_structEtaG` are hole-free statements that **discharge nothing**.  Nothing in this
  document changes that, and nothing in this document was proved *from* `StructEtaG`.
* **The satisfiability certificate is thinner than it looks.**  There is exactly **one** witness
  that `StructEtaG`'s premises are jointly satisfiable — `MutField.declEnv_structEtaG_premises`
  (`EtaStructG.lean:487`) — and it is at `decl.isLE = false` with a single **`Prop`** field, so F17
  is discharged in its small-elimination disjunct.  `EtaResidual.lean`'s `toUnitEta` discharges
  F17 by `.inr (by simp [hnf])`, i.e. **vacuously at zero fields**.  **No witness anywhere in
  `Lean4Lean/` supplies `StructEtaG`'s premises with `isLE = true`** — the disjunct that covers
  `Prod`, `Sigma`, `Subtype`, i.e. every structure the kernel actually η-expands in practice.
  `Theory/Inductive/StructureExamples.lean` has those blocks and computes their `etaExpansion`, but
  proves nothing about `StructEtaG` at them.  **[measured: `grep 'isLE := true'` over `Lean4Lean/`
  → `StructureExamples`, `Consistency`, `NestedBuild`, `IndexedNested`, `ProjGenInstWitness`,
  `StagesFiring`; `grep 'structEtaG_premises'` → one declaration.]**
* Block index `j` *is* tested at both values of a two-member block (`declEnv_IsStructureG` at
  `j = 1`, `declEnv_IsStructureG_0` at `j = 0`).  Field count is tested at 0 and 1.  The level side
  condition is tested only in one of its two disjuncts.

## 9. Reproducing this

Nothing was built and no Lean file was added, so there are no per-module job counts or
`#print axioms` to report: **this round elaborated no new declaration.**  No `sorry` was added,
removed or traded; the instrument independently re-derives the standing total of **13** direct
`sorryAx` holes, name for name, which is the cross-check that it is reading the same tree
`scripts/sorry-census.lean` reads.

The four instrument variants are `/tmp/pricing/census{,3,4,5,6}.lean`, each run as
`~/.elan/bin/lake env lean --run <file>` from the repo root against the built `.olean`s.  Their
shared preamble is the 340-module import list at `/tmp/pricing/imports4.txt` (§0), and their
shared predicate is `deps` — `type.getUsedConstantsAsSet ∪ value?(allowOpaque := true)
.getUsedConstantsAsSet`.  If they are wanted permanently they belong in `scripts/` next to
`cone-measure.lean`, whose `allowOpaque` warning they follow.
