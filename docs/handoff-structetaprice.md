# Handoff — pricing the fourteenth `IsDefEq` constructor (structure eta)

Round of **2026-09-03**.  Owner file: `Lean4Lean/Theory/Typing/StructEtaPrice.lean` (new, builds
clean, zero warnings).  Nothing else was modified; `IsDefEq` was **not** touched, as the brief
required.

## Verdict in one paragraph

The 14th-constructor repair is **not free, and the expensive part is not the induction cases.**
The induction cost is 136 sites (measured, below), of which ~40 are routine and ~20 need real
typing arguments.  The cost nobody had priced is that structure eta **refutes const-head
no-confusion**, `VEnv.IsDefEq.constApp_inv` (187 transitive users), and it does so
*route-independently* — no formulation escapes it, because the refutation is a fact about Lean
itself.  Against that, the **set model is not a risk at all**: it validates surjective pairing,
and the validation is *forced* by an obligation the model already carries, which corrects a claim
in `SetModel/UnitEtaPairing.lean`.  And there is a **cheaper route than a new constructor**:
state the rule between closed λ-terms and carry it as a `VDefEq`, which the existing `extra`
constructor already handles — 0 new induction cases.  **Recommendation: take the `VDefEq` route.**

## (a) Induction-site count — measured 2026-09-03, 17:01–17:25 UTC

Method: a scratch script (`/tmp/elim.lean`, adapted from `scripts/users.lean`) imported the built
population (421 modules) and, for each declaration in `Lean4Lean`, tested whether its **proof
term** mentions an eliminator of the relation (`.rec`, `.recOn`, `.casesOn`, `.brecOn`,
`.below.*`, `.ndrec`, `.induct`, `.binductionOn`).  Compiler-generated eliminators declared in the
inductive's own module are netted out.  This is exact, not a grep: `grep` for
`induction … using`/`cases` finds **zero** sites, because every one of them is written as
`induction H with | bvar h => …`.

| relation | hand-written eliminator sites | needs the constructor |
|---|---|---|
| `VEnv.IsDefEq` | **22** | yes |
| `VEnv.IsDefEqStrong` | **31** | yes (`IsDefEq.strong'`) |
| `VEnv.NormalEq` | **31** | yes (`church_rosser`'s target) |
| `VEnv.ParRed` | **26** | yes |
| `VEnv.ParRedK` | **23** | yes (`ParRed.toK`) |
| `VEnv.IsDefEqE` | **3** | yes (`IsDefEq.toE`) |
| `VEnv.IsDefEqRaw` | **0** | yes (`IsDefEq.raw`) — constructor only, nothing inducts |
| `VEnv.ParRedS` | 0 | no — it is a closure `def` |
| **total** | **136** | |

`IsDefEq`'s own 22, by module: `Typing/Lemmas` 9, `Typing/Strong` 2, `Typing/ConstSubst` 2, one
each in `Typing/{Strengthen,StrengthenNarrow,RawDefEq,CycleConv,ChurchRosser,ConstSubstNested,
ConstVar}` and `SetModel/Consts`.  `IsDefEqStrong`'s 31: `Typing/Strong` 10,
`Typing/Injectivity` 5, `ShapeVar` 3, `SpineVar` 3, `SortInvIndep` 2, `SpineVarVacuity` 2, one
each in `InjOneFact`, `Stratified`, `InjPiRogue`, `RetypeAdmissible`, `SortPiDisjPrice`, and
**`SetModel/SoundInduction`** (`soundAbove` — the model induction runs on the strong relation, not
on `IsDefEq`).  Full per-module listings for all seven relations are reproducible by re-running
the script; the table above is the summary.

**Real work vs. `nofun`.**  There is no `nofun` case, and that is structural: the new rule's
left-hand side is a **bare variable** `e`, so no head-shape split can dismiss it.

* ~40 congruence/stability sites (`weakN`, `instN`, `instL`, `mono`, `mono_uvars`, `closedN'`,
  `levelWF`, `isType'` and their `Strong`/`E`/`Raw` mirrors) need the η-expansion to commute with
  the operation.  `etaExpansion_instL`, `projAll_instL` and `projTerm_instN` exist;
  **`projTerm_weakN`, `projTermG_weakN`, `etaExpansion_weakN`, `etaExpansionG_weakN` and
  `etaExpansionG_instL` do not** (checked with `scripts/exists.lean` this round).  Five missing
  commutation lemmas over a recursor spine is the floor.
* ~20 inversion sites (`forallE_inv'`, `sort_inv'`, `Injectivity`'s five, the `Shape`/`Spine`/
  `Sort*` twelve) currently dismiss `extra` by head shape; they now need "no term is both a sort
  and an inhabitant of a structure", i.e. the `SortUniq`/`UnivDiscrim` machinery where the
  existing injectivity holes live.
* 1 site is the model (§c) — cheap.
* 1 site is the wall (`church_rosser`) — §d, and it is worse than hard.

**A cost nobody had named.** `Theory/Typing/Basic.lean` imports only `Theory/VEnv`.  The
η-expansion needs `etaExpansionG` → `projTermG` (`Verify/Typing/ProjGen.lean`) → `VInductDecl'`
(`Theory/Inductive/Decl.lean`), and `Decl.lean` imports `Theory/Typing/Lemmas` → `Basic`.
**Writing the constructor into `Basic.lean` is an import cycle.**  It is breakable — `projCore`,
`projArgs`, `projTerm`, `projTermG`, `etaExpansion(G)` are purely syntactic and `Telescope.lean`
imports only `Theory/VExpr` — but the break is a three-file split (`Decl`, `Structure`, `ProjGen`
each into a syntax half below `Basic.lean` and a `WF` half above it) plus an import re-layer,
before a single proof case is written.

## (b) The constructor, stated

`Lean4Lean/Theory/Typing/StructEtaPrice.lean` §3 declares `VEnv.IsDefEqSE`: `IsDefEq`'s thirteen
constructors verbatim plus

```lean
| structEta {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {e : VExpr} :
  env.IsStructureG S D j T C →
  T.indices = [] →
  C.recFields = [] →
  us.length = D.uvars → (∀ l ∈ us, l.WF uvars) →
  ps.length = D.np →
  HasArgsSE Γ (D.params.map (VExpr.instL us)) ps →
  IsDefEqSE Γ e e ((VExpr.const S us).mkApp ps) →
  (D.isLE = true ∨ ∀ k, k < C.fields.length →
    (C.fields.getD k default).lvl.inst us ≈ .zero) →
  IsDefEqSE Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)
```

with a mutually-defined `HasArgsSE` (the parameter spine over the new relation).

Three shape decisions, each argued in the file:

1. **The typing premises are in the new relation** (`HasArgsSE`, `IsDefEqSE … e e …`), not the old
   one, following `beta`/`eta`/`proofIrrel`.  `VEnv.StructEtaG` states them in the old relation
   because it is a predicate *about* that relation; a constructor must be closed under its own
   conclusion, and the `TrExprS` bridge supplies typing in whatever relation `venv` carries.
2. **`IsStructureG` does not move** with the relation — it is environment data.
3. **`recFields = []` kept, `types` narrowing not reinstated** — `VEnv.StructEtaG`'s choices, for
   its reasons (`EtaStructG.lean`).  The F17 level clause is **not optional**: without it the rule
   is *false*, not useless, at a small-eliminating structure with a large field.

**Strong enough** — `VEnv.structEtaGSE : ∀ env, env.StructEtaGSE` is proved, where `StructEtaGSE`
is `VEnv.StructEtaG` with only the conclusion's relation swapped.  So
`TypeChecker.Inner.etaHoles_of_structEtaG` applies verbatim after the swap: **both holes close.**
`IsDefEq.toSE` (thirteen one-line cases) is the machine-checked form of "each induction gains
exactly one case".

**Weak enough to be sound** — the rule's two sides are at the same type by construction; the
`Prop` case is independently derivable (`structEta_of_prop`); `VEnv.empty.StructEtaG` holds; and
the set model validates it (§c).  What makes it *not* obviously sound is §d.

**(e) Anti-vacuity — it fires, twice.**  `MutField.structEtaSE_foo`: at `MutField.unitEnv`'s
zero-field member `A` with the **axiom** inhabitant `foo`, giving `foo ≡ A.mk`.
`MutField.structEtaSE_B`: at the same block's **positive-field** member, giving `x ≡ B.mk x.f`.
Both are members of a two-type mutual block in `Type` at which the *narrow* rule `VEnv.StructEta`
cannot even be stated (`MutField.decl_not_isStructure`).

## (c) The set model — verdict: **it validates the rule, and the validation is forced**

`SetModel/UnitEtaPairing.lean`'s stated residual is

> `OracleOK` constrains a type former's denotation by membership only, so a model satisfying
> `InductOracleOK` may interpret a zero-field structure as a two-element set and refute eta
> outright.

**That claim is wrong**, and the missed step is nameable: `InductOracleOK.consts` quantifies over
`D.allConsts`, and `allConsts` contains the **recursor** (`SetModel/EqOracle.lean`'s
`eq_allConsts` computes `[Eq, Eq.refl, Eq.rec]`).  The recursor's own `OracleOK.type` field asks
`o (S.rec) us ∈ interp ((D.recType j).instL us)`, and `recType` quantifies `motive` over the
**full** set-theoretic function space — `interp`'s `forallE` clause is `mkForallType`,
`{f ∈ (⋃…)^(G ρ) ; …}`, not a definable-families subset (`Theory/SetModel/Interp.lean:186`).  So
`motive` may be the *characteristic family of the constructor*, and an inhabitant of the recursor
type then exists only if every element of the type former's denotation **is** the constructor's
value.  That is surjective pairing, from an obligation the model already carries.

Machine-checked evidence in §8 of the Lean file:

* `SetModel.eq_singleton_of_recProp` — if `mkv ∈ Sv` and for every `m ∈ UProp ^ Sv` with
  `pt ∈ m ‘ mkv` we have `∀ x ∈ Sv, pt ∈ m ‘ x`, then `Sv = {mkv}`.  Hole-free, `Above`-free, no
  chain of inaccessibles: Replacement and Power only.
* `SetModel.charFam` / `charFam_mem_pow` / `charFam_value` — the characteristic family, built with
  `sep` rather than `ite` because `definability` does not see through `ite`.
* `SetModel.mkForallType_const_eq_pow` — the general lemma the existing peel was missing:
  `mkForallType` with constant codomain over a **non-empty** domain is the function space.
  `UnitAudit.mkForallType_singleton_const` assumes a *singleton* domain, which is the conclusion
  being proved and so cannot be used.
* `SetModel.recProp_at_singleton` — the hypothesis is satisfied at `Sv = {mkv}`, so the
  implication is not vacuous.

Corroboration from the other side: `SetModel/UnitOracleLarge.lean`'s oracle sends
`Unit1 ↦ {•}` — a singleton — and *closes* `InductOracleOK` there, and its
`pt_not_mem_interpL_recType_of_ne` is this file's contradiction step at a domain that is already a
singleton.  And the carrier is built from Kuratowski tuples precisely so that surjective pairing
holds on the nose (`SetModel/Inductive.lean:241`, `mem_Ind_iff` "no junk",
`mem_Ind₃_fibre_iff_of_zero_field`).

**Two steps still owed, both bookkeeping.** (1) Peel `interp ((D.recType j).instL us)` to the
shape `eq_singleton_of_recProp` consumes — `UnitOracleLarge.lean` performs exactly that peel at
`unitDeclLE` (six `mkLam_mem_mkForallType_of_dom` layers); at a general block it is `recType`'s
telescope instead of two binders.  (2) The `PropSplit` side condition: `interp (.app f a)`
collapses to `pt` when `L.IsProof M Γ f`, so the argument needs the motive not to be classified as
a proof — true (its type is `S ps → Sort u`) but stated nowhere in that form.

At **positive fields** the same argument gives the full rule: take the family
`m x = ⟦x = mk ps (proj₀ x) …⟧` and the recursor's type forces it inhabited everywhere.

So the model is **not** the risk.  Estimated cost of the model case: one file, mostly the `recType`
peel.

## (d) The real risk, and the priced alternative

### The price, and it is route-independent

`eta_and_constNoConf_incompatible` (§6): for an **arbitrary** binary relation `R` on `VExpr`, the
one eta instance at `MutField.unitEnv` and const-head no-confusion are contradictory.  `R` has no
constructors, no closure, no typing — so the conclusion is *"every design that yields structure
eta pays this price"*, not "this design does".  `constNoConf_false_for_IsDefEqSE` instantiates it:
`VEnv.IsDefEq.constApp_inv` is **refuted**, not merely unproved, for the extended relation, at an
environment with a machine-checked `VEnv.WF`.

**And this is a fact about Lean, not about the design.**  Checked against the real elaborator this
round:

```lean
structure A where
axiom foo : A
example : foo = A.mk := rfl                                   -- typechecks
example (q : P Nat Bool) : q = P.mk q.fst q.snd := rfl        -- typechecks
```

So const-head no-confusion **is false in the real kernel**, and `VEnv.IsDefEq.constApp_inv` is a
true lemma about a relation *strictly weaker than real definitional equality*.  Anything that used
it to justify checker behaviour was leaning on that gap.  This is a finding independent of whether
the repair is made, and it belongs in `bugs-found.md`/`divergences.md` territory — the orchestrator
should decide.  Measured with `scripts/users.lean`, 2026-09-03: `IsDefEq.constApp_inv` 4 direct /
**187 transitive**; `constApp_inv_of_patWF` 3 / 169; `constApp_inv_of_wf` 2 / 157;
`constNoConf_of_notIsProof` 2 / 7; `IsDefEq.church_rosser` 9 / **212**;
`NormalEq.constApp_inv` 1 / 188.  `DescendConstSpineK.lean:16` names the chain:
`addAxiom.WF ← … ← constApp_inv_of_patWF ← IsDefEq.constApp_inv ← IsDefEq.church_rosser`.

The repair therefore needs a **weaker no-confusion lemma with a side condition excluding
structure constructors (or unit-like types)**, and that side condition exists nowhere in the tree.
That is the item to scope next, and it is on the critical path of `addAxiom.WF`.

### The alternative: structure eta as a closed `VDefEq` — 0 induction cases

`docs/design-inductive.md` §6.3 says structure eta "cannot be added as a `VDefEq`, because
`Pattern.Matches` only matches `const`-headed spines and the rule's left-hand side is a variable".
**The premise is right; the conclusion does not follow.**  The left-hand side is a variable only if
the rule is stated pointwise.  State it between closed functions —

```
(fun ps… x => x)  ≡  (fun ps… x => S.mk ps (proj₀ x) …)   :   ∀ ps…, S ps → S ps
```

— and both sides are closed `VExpr`s, so this is an ordinary `VDefEq` and the **existing** `extra`
constructor carries it.  Pointwise instances come back by `appDF` + `beta`.

`structEta_of_extra` (§7) is that derivation, machine-checked at the zero-parameter zero-field
case — which is `isDefEqUnitLike`'s hole exactly — using only the thirteen constructors: `extra`,
`appDF`, two `beta`s, a `symm`, two `trans`.  `MutField.structEta_of_extra_fires` runs it at
`MutField.unitEnv.addDefEq (etaDfZ …)` and derives `foo ≡ A.mk` in the **thirteen**-constructor
relation.

| | 14th constructor | closed `VDefEq` |
|---|---|---|
| induction cases added | **136**, ~20 needing typing arguments | **0** |
| missing commutation lemmas | 5 | **0** (`extra`'s `instL` case exists) |
| file split / import re-layer | 3 files | **0** |
| `church_rosser` | new `NormalEq`/`ParRed` rule, no rewrite orientation | `extra` case, written |
| `constApp_inv` (187 users) | **refuted** | **refuted** — route-independent |
| `PatWF` / `PatFreeHead` | unchanged | must admit a `lam`-headed rule, or exempt it |
| `addInduct'` | unchanged | `D.etaRules : List VDefEq` + `VDefEq.WF` per rule |
| RHS typeable | needed | needed (same `StructureClosed` chain) |

The `VDefEq` route is cheaper on every line but two, and both of those are *localised*: one
predicate (`VEnv.PatWF`) plus `patWF_of_wf`, and one fold in `addInduct'` mirroring the
`iotaRules` fold already there.  The `PatWF` change is forced in the constructor route too — §6
shows `PatFreeHead`-based no-confusion has to give either way.

**Not settled here:** the telescoped form (parameters, positive fields).  The schema is the same
three moves per binder; `Theory/Inductive/Telescope.lean`'s `instAllTele`/`instTele` and
`VEnv.HasArgsDF` (`StructureClosed.lean:500`) are what it runs on; the `beta` chain over a
telescope is the one piece of real work.  Estimated **one file**.  That is the number to compare
against 136.

## Recommendation

1. **Take the closed-`VDefEq` route, not a new constructor.**  Proved here at the
   zero-parameter zero-field case, which is one of the two holes outright; the telescoped case
   needed for `StructEtaG` in general is *not* proved and is the one piece of real work it
   carries (estimated one file).  Even so it is 0 induction cases against 136, with no import
   re-layer.  Cost estimate: one file for the telescoped derivation, one for `addInduct'`'s
   `etaRules` fold and their `VDefEq.WF`, one for the `PatWF` restatement.
2. **Scope the no-confusion repair first, before either route.**  It is the only genuinely
   unbounded item: 187 transitive users of a lemma that is *false* once eta is in, and no side
   condition anywhere in the tree that would save it.  If that repair turns out to be
   unaffordable, neither route is affordable, and the round should say so rather than start
   writing induction cases.
3. **Do not treat the set model as a risk.**  §c corrects the ledger's pessimism and gives the
   machine-checked core; the residual there is a `recType` peel plus a `PropSplit` side condition.
4. **Two prose corrections are owed** (both outside this stream's files, so they are *stated*, not
   made): `SetModel/UnitEtaPairing.lean`'s "may interpret a zero-field structure as a two-element
   set and refute eta outright" is false for the reason in §c; `docs/design-inductive.md` §6.3's
   "cannot be added as a `VDefEq`" is false for the reason in §d.  `docs/vacuity-ledger.md` is
   **not** touched, per the brief.

## Reproducing the measurements

* Eliminator sites: `/tmp/elim.lean` (kept out of the repo), `INDS="Lean4Lean.VEnv.IsDefEq …"
  lake env lean --run /tmp/elim.lean`.  It is `scripts/users.lean`'s population loader with the
  dependency test replaced by "does the proof term mention an eliminator of this inductive".
  Worth promoting to `scripts/` if another round needs it.
* User counts: `NAMES="…" lake env lean --run scripts/users.lean`.
* Absence claims: `NAMES="…" lake env lean --run scripts/exists.lean`.

## Status

`lake build Lean4Lean.Theory.Typing.StructEtaPrice` succeeds, zero warnings.  Axioms: only
`eta_and_constNoConf_incompatible` and `constNoConf_false_for_IsDefEqSE` carry `sorryAx`, inherited
from `MutField.unitEnv_not_isProof_foo` exactly as `MutField.unitEnv_not_unitEta` already does.
Everything else — the embedding, both firings, `structEtaGSE`, the whole alternative section and
the whole model section — is hole-free.  `after ⊆ before`.
