# handoff: EtaGuardLand

**Owner file:** `Lean4Lean/Theory/Typing/EtaGuardLand.lean` (new, mine)
**This doc:** `docs/handoff-etaguardland.md` (new, mine)
Everything else read-only. Frozen: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.
Hands off: `Theory/Typing/NoConfRepair.lean`, `Theory/Typing/StructEtaPrice.lean`,
`Verify/Typing/ConstSpine.lean`, `Verify/Typing/NoConfGuard.lean`, all of `Verify/Inductive/`,
`Verify/Environment/InductR.lean`, `docs/vacuity-ledger.md`.

## Section 0 — task as received (written before any Lean ran)

Goal, in order:

(a) Re-verify the claimed **absence** of `IsStructureG.ruleFreeHead` myself (`shape.lean` on
    `VEnv.IsStructureG` + `VEnv.RuleFreeHead`, heads resolved). Then supply the lemma —
    suggested shape `IsStructure.ruleFreeHead` with `iotaTypeNotKey D j 0`. Both existing
    bridges carry `hrf` as a hypothesis; the payoff is discharging it.
(b) Two smaller gaps: `StructInhab` transport along `IsDefEqU`; `¬ IsProof` persistence.
(c) State precisely what `Lean4Lean.VEnv.IsStructure.spine_inv_of_si` still needs to be a
    **drop-in** replacement for `Lean4Lean.VEnv.IsStructure.spine_inv` at its call sites;
    prove as much as possible in my own file. Do NOT edit `ConstSpine.lean` / `NoConfGuard.lean` —
    state the exact edits instead.
(d) Vacuity both ways: any relation exhibited must relate something; any guard must be
    satisfiable by a real environment. Use `Lean4Lean.MutField.unitEnv` (zero-field) and
    `Lean4Lean.MutField.bigEnv` (positive-field) — must check the guard at a *positive-field*
    structure, since the failure was shown not to be zero-field-only.
(e) Holes verified per declaration with `exists.lean`. Re-deriving an already-tainted lemma at
    the same taint is fine but must be stated as such, not as hole-free.

Context handed to me (to be re-verified, not trusted):
- surviving guard `Lean4Lean.VEnv.ConstNoConf` (IsType-guarded row)
- `Lean4Lean.VEnv.structEta_lhs_structInhabAt` (cone 84, hole-free)
- proposed replacement `Lean4Lean.VEnv.ConstAppInvSI` (NoConfRepair.lean, arity 2, cone 633)
- `Lean4Lean.VEnv.IsStructure.spine_inv_of_si` (arity 26, cone 7528, four holes)
- `Lean4Lean.guard_rejects_an_axiom` (cone 382) — no head-name guard can work.

Standing risk noted by the brief: 14 prior false-absence instances. Every cited scan re-run.

## Log

(appended incrementally below)

### Pre-flight, 2026-09-03 (all re-run by me, `lake build` clean at 1619 jobs, population 433)

`scripts/exists.lean`:

| name | status | arity | cone | holes |
|---|---|---|---|---|
| `Lean4Lean.VEnv.IsStructure.ruleFreeHead` | FOUND (`Theory/Typing/StructureRuleFree`) | 7 | 4091 | none |
| `Lean4Lean.VEnv.IsStructureG.ruleFreeHead` | **NOT FOUND** | — | — | — |
| `Lean4Lean.VEnv.ConstNoConf` | FOUND (`Verify/Typing/Rigidity`) | 2 | 405 | none |
| `Lean4Lean.VEnv.structEta_lhs_structInhabAt` | FOUND (`Theory/Typing/NoConfRepair`) | 14 | 84 | none |
| `Lean4Lean.VEnv.ConstAppInvSI` | FOUND (`NoConfRepair`) | 2 | 633 | none |
| `Lean4Lean.VEnv.IsStructure.spine_inv` | FOUND (`Verify/Typing/ProjSpineInv`) | 24 | 7538 | 4 (weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, NormalEq.descend) |
| `Lean4Lean.VEnv.IsStructure.spine_inv_of_si` | FOUND (`NoConfRepair`) | 26 | 7528 | same 4 |
| `Lean4Lean.guard_rejects_an_axiom` | FOUND (`NoConfRepair`) | 7 | 382 | none |
| `Lean4Lean.MutField.unitEnv` | FOUND (`Verify/TypeChecker/EtaUnitRefute`) | 0 | 928 | none |
| `Lean4Lean.MutField.bigEnv` | FOUND (`NoConfRepair`) | 0 | 930 | none |
| `Lean4Lean.VEnv.WF.iotaTypeNotKey` | FOUND (`Theory/Typing/DeltaUnique`) | 2 | 4023 | none |
| `Lean4Lean.VEnv.IsStructureG.iotaDefeq` | FOUND (`Verify/Typing/ProjGenTerm`) | 10 | 1119 | none |
| `Lean4Lean.VEnv.notStructInhab_of_isType` | FOUND (`NoConfRepair`) | 8 | 7479 | same 4 |
| `Lean4Lean.VEnv.notStructInhab_of_forallE` | FOUND (`NoConfRepair`) | 10 | 7481 | same 4 |
| `Lean4Lean.VEnv.StructInhab` | FOUND (`NoConfRepair`) | 4 | 84 | none |
| `Lean4Lean.VEnv.HasType.defeqU_l` | FOUND (`Theory/Typing/UniqueTyping`) | 10 | 3477 | 1 (forallE_inv_stratified) |
| `Lean4Lean.VEnv.IsProof` | FOUND (`Theory/Typing/Injectivity`) | 4 | 12 | none |

Note: the brief and `NoConfRepair.lean` §6 say `HasType.defeqU_l'` (primed). **The primed name
does not exist**; the unprimed `Lean4Lean.VEnv.HasType.defeqU_l` is the lemma.

**`shape.lean` correction — the cited "0 hits" is wrong; it is 5.**
`HEADS="Lean4Lean.VEnv.IsStructureG Lean4Lean.VEnv.RuleFreeHead"`, population 433, run by me:
**5 constants**, 0 of them structure fields:
`VEnv.ConstAppInvSI.constNoConf` (5), `VEnv.notStructInhab_of_isType` (8),
`VEnv.notStructInhab_of_forallE` (10), `VEnv.ConstAppInvSI.of_isType` (17),
`VEnv.IsStructure.spine_inv_of_si` (26) — all in `NoConfRepair.lean`.
**The absence claim survives, but for a different reason than reported**: all five mention both
heads because each *carries* `hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S`
as a hypothesis. Nothing *concludes* `RuleFreeHead` from `IsStructureG`. So:
absence of the lemma — **confirmed**; the cited scan figure — **refuted (5, not 0)**.

## Section 1 — results

Owner file: `Lean4Lean/Theory/Typing/EtaGuardLand.lean`, 544 lines, 31 declarations (2 private) + 3 examples,
**zero diagnostics** (`lean_diagnostic_messages` returns `[]` — no warnings, no infos).
Full `lake build`: 1620 jobs, completed successfully. `scripts/sorry-census-all.lean`:
**13 holes, unchanged**; 437/437 in population built.

Imports: `Theory.Inductive.IotaGen`, `Theory.Typing.StructureRuleFree`,
`Theory.Typing.NoConfRepair`, `Verify.Typing.NoConfGuard`.

### (a) The absence, and the lemma

- **Absence confirmed** by `exists.lean` (`Lean4Lean.VEnv.IsStructureG.ruleFreeHead`: NOT FOUND).
- **The cited scan figure is refuted**: `shape.lean` gives **5** hits, not 0. All five are the
  `hrf`-carrying lemmas of `NoConfRepair.lean`; none concludes `RuleFreeHead` from `IsStructureG`.
- **Lemma supplied**: `Lean4Lean.VEnv.IsStructureG.ruleFreeHead`, arity 8, **cone 4093,
  hole-free**, `[propext, Classical.choice, Quot.sound]`. The narrow lemma is 4091, so the wide
  one costs **two constants** — its two private helpers.
- Also `Lean4Lean.VEnv.WF.isStructureG_ruleFreeHead` (arity 8, cone 4094, hole-free) — `hrf`
  itself; and `Lean4Lean.VEnv.IsStructure.ruleFreeHead_of_g` (arity 7, cone 4101, hole-free), the
  collapse test showing §1 subsumes the narrow lemma.
- **Placement is verified, not asserted**: §1 elaborates standalone with only
  `Theory.Inductive.IotaGen` + `Theory.Typing.StructureRuleFree` imported — no `Verify/` module —
  so it can move into `StructureRuleFree.lean`, which is what makes it visible to
  `ProjSpineInv.lean` and `NoConfRepair.lean`. `IotaGen`'s import closure is 15 modules, contains
  no `Verify/` module and does not contain `StructureRuleFree`: cycle-free.
  This is why the two Verify-resident inputs (`VEnv.IsStructureG.iotaDefeq`,
  `VInductDecl'.mem_ctorsAll_gen`) are re-derived as private lemmas rather than imported.

### (a) What discharging `hrf` buys

Five statements lose a hypothesis (all in §2 of my file, each proved *through* the unedited
original, so the proposed edit to `NoConfRepair.lean` is type-checked before it is made):

| new name (cone, holes) | replaces |
|---|---|
| `Lean4Lean.VEnv.notStructInhab_of_isType_of_wf` (7528, 4) | `notStructInhab_of_isType` |
| `Lean4Lean.VEnv.notStructInhab_of_forallE_of_wf` (7530, 4) | `notStructInhab_of_forallE` |
| `Lean4Lean.VEnv.ConstAppInvSI.of_isType_of_wf` (7530, 4) | `ConstAppInvSI.of_isType` |
| `Lean4Lean.VEnv.ConstAppInvSI.constNoConf_of_wf` (7532, 4) | `ConstAppInvSI.constNoConf` |
| `Lean4Lean.VEnv.IsStructure.spine_inv_of_si_wf` (7538, 4) | `spine_inv_of_si` |

"4" = the four census holes `IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`,
`WF.rigidShapeUniqNS`, `NormalEq.descend` — **the same four the originals carry**. These are
re-derivations of already-tainted lemmas at the same taint, not new hole-free results.

The concrete payoff, beyond one fewer hypothesis: `ConstAppInvSI.of_isType_of_wf` is now
**hypothesis-for-hypothesis identical to `VEnv.constApp_inv_of_wf` apart from a single extra
premise**, `H : env.ConstAppInvSI U`. Before the discharge it had two extra. And
`notStructInhab_of_forallE_of_wf` now says outright that no Π-typed term of a well-formed
environment is a structure inhabitant — the sub-spine guard is *free*, with nothing to carry.

### (b) Two smaller gaps

- **`StructInhab` transport**: `Lean4Lean.VEnv.StructInhab.defeqU` (arity 9, cone 3481, **1
  hole**: `IsDefEqU.forallE_inv_stratified`) and its contrapositive
  `Lean4Lean.VEnv.notStructInhab_defeqU` (arity 9, cone 3482, same hole). Three lines, as
  advertised. **Correction:** the lemma is `VEnv.HasType.defeqU_l`, not `HasType.defeqU_l'` —
  the primed name cited by `NoConfRepair.lean` §6 (ii) and vacuity-ledger row 245f does **not
  exist** (`exists.lean`: NOT FOUND).
- **`¬ IsProof` does not go away — now a theorem, not prose.**
  `Lean4Lean.VEnv.structInhabOnlyNoConf_false` (cone 3815, **hole-free**): the row with
  `¬ IsProof` deleted and `RuleFreeHead` + `¬ StructInhab` kept is **false** at `VEnv.ncPropEnv`.
  This is sharper than `not_constNoConfUG_ncPropEnv`, which deletes both guards: here the new
  guard genuinely *holds* at the witness. Supporting results:
  `Lean4Lean.VEnv.IsStructureG.not_of_no_defeqs` (1191, hole-free) — an environment with empty
  `defeqs` satisfies `IsStructureG` for nothing, because `decl` places the block's ι-rules;
  `Lean4Lean.VEnv.not_structInhabAt_of_no_defeqs` (1193, hole-free);
  `Lean4Lean.VEnv.not_structInhab_ncPropEnv` (1202, hole-free). So the two guards are independent
  and `ConstAppInvSI` carrying both is forced.

### (c) What `spine_inv_of_si` still needs to be a drop-in

`VEnv.IsStructure.spine_inv` has exactly **two** call sites, both in its own module:
`Verify/Typing/ProjSpineInv.lean:86` (`h₁.spine_inv henv hΓ h₂ ht₁ ht₂ H`) and `:150`
(`(hS1.spine_inv henv hΓ₁ hS2 hty1 hty2 H).1`). Both are dot-notation on the first `IsStructure`,
so a replacement must keep the explicit order `henv, hΓ, h₂, ht₁, ht₂, H`. `spine_inv_of_si_wf`
does.

After (a), **exactly one** thing is missing, and it is named:

    Lean4Lean.ConstAppInvSIFromWF : Prop := ∀ (env : VEnv) (U : Nat), env.WF → env.ConstAppInvSI U

(cone 637, hole-free as a *statement*.) The drop-in claim is machine-checked rather than
eyeballed, by transcribing `spine_inv`'s statement as `Lean4Lean.SpineInvStmt` (cone 596) and
pinning it from both sides:

- `Lean4Lean.spineInvStmt_today` (cone 7540, 4 holes) — the tree's lemma inhabits it, so the
  transcription is not stronger than `spine_inv`;
- `Lean4Lean.spine_inv_of_spineInvStmt` (arity 25, cone 597, **hole-free**) — it delivers
  `spine_inv`'s conclusion at `spine_inv`'s hypotheses, so it is not weaker either;
- `Lean4Lean.spineInvStmt_of_repair` (arity 1, cone 7541, 4 holes) — **`ConstAppInvSIFromWF`
  suffices**. That is the whole remaining re-basing cost for the 156 transitive users of
  `IsDefEq.constApp_inv` that reach it only through `spine_inv`.

**Cone-neutral, and this is new**: `spine_inv_of_si_wf` measures **7538**, which is
`spine_inv`'s own figure **exactly** (7538). So on this route the repair does not merely stay
bounded, it costs nothing in cone. (`spine_inv_of_si`, with `hrf` still carried, measured 7528 —
the ten-constant difference is `hrf`'s absence from the *cone* while it sat in the *signature*.)

### (d) Vacuity, both ways

*Guard non-trivial at a POSITIVE-FIELD structure* — the specific requirement:

- `Lean4Lean.MutField.bigEnv_structInhab_bar` (cone 3871, **hole-free**): the guard is **false**
  at the eta rule's left endpoint at `MutField.B`, whose constructor has one field
  (`MutField.bCtor_has_a_field`). Zero-field is not the whole story, matching
  `zeroFieldOnlyNoConf_false_for_IsDefEqSE`.
- `Lean4Lean.MutField.bigEnv_not_structInhab_B` (cone 7594, 4 holes): the guard is **true** at
  that same one-field structure's own type, via §2 — `hrf` discharged generally, not `decide`d.
- `Lean4Lean.MutField.bigEnv_guard_separates_at_B` (cone 7607, 4 holes): both at once. A guard
  that failed to separate would be vacuous or trivial; this one separates at a positive-field
  structure.
- Zero-field companions: `bigEnv_structInhab_foo2` (3871, hole-free),
  `bigEnv_not_structInhab_A` (7594, 4 holes).

*§1's hypothesis satisfiable, at both block indices*:
`Lean4Lean.MutField.bigEnv_ruleFreeHead_A_general` (4282, hole-free, `j = 0`) and
`Lean4Lean.MutField.bigEnv_ruleFreeHead_B_general` (4283, hole-free, **`j = 1`, one field** —
the case the narrow lemma cannot reach at all, `MutField.decl` having two types). An `example`
cross-checks the general route against `bigEnv_ruleFreeHead`'s `decide` route at `B`.

*§1's conclusion refutable* (so it is not a tautology): `example` for a δ-rule environment.
*§1's hypothesis refutable* (so it is not "`RuleFreeHead` always"): `example` at `ncPropEnv`.

*`SpineInvStmt`'s own premises satisfiable* — the drop-in target quantifies over the **narrow**
`IsStructure`, which no `MutField` environment satisfies, so this had to be checked elsewhere:
`Lean4Lean.spineInvStmt_premises_satisfiable` (cone 1938, hole-free) at `Lean4Lean.barEnv`
(`Verify/Typing/ProjLevelWitness.lean`) — a singleton block whose constructor has **two** fields.
Its `VEnv.WF` was not in the tree (`Lean4Lean.EtaUnit.barEnv_wf` is a *different* `barEnv`), so
`Lean4Lean.barEnv_wf'` (cone 1930, hole-free) supplies it. `Lean4Lean.barEnv_ruleFreeHead_general`
(4231, hole-free) then runs §1 there through `IsStructure.toG`.

### (e) Axiom bar

`after ⊆ before` holds. Every declaration is either **hole-free** or carries exactly the holes its
input already carried:

- hole-free (17): `IsStructureG.ruleFreeHead`, `WF.isStructureG_ruleFreeHead`,
  `IsStructure.ruleFreeHead_of_g`, `ConstAppInvSIFromWF`, `SpineInvStmt`,
  `spine_inv_of_spineInvStmt`, `IsStructureG.not_of_no_defeqs`,
  `not_structInhabAt_of_no_defeqs`, `not_structInhab_ncPropEnv`, `structInhabOnlyNoConf_false`,
  `bigEnv_ruleFreeHead_A_general`, `bigEnv_ruleFreeHead_B_general`, `bigEnv_structInhab_bar`,
  `bigEnv_structInhab_foo2`, `barEnv_wf'`, `spineInvStmt_premises_satisfiable`,
  `barEnv_ruleFreeHead_general`;
- 1 hole (`forallE_inv_stratified`), inherited from `HasType.defeqU_l`: `StructInhab.defeqU`,
  `notStructInhab_defeqU`. **Recorded at the statement** as unavoidable on this route;
- 4 holes (the census four), inherited unchanged from the `NoConfRepair.lean` originals: the five
  §2 re-derivations, `spineInvStmt_today`, `spineInvStmt_of_repair`, `bigEnv_not_structInhab_A/_B`,
  `bigEnv_guard_separates_at_B`.

No new hole, no new axiom, census still 13.

## Section 2 — exact edits proposed elsewhere (none made)

Full prose is in §6 of `EtaGuardLand.lean`. Summary:

1. **`Theory/Typing/StructureRuleFree.lean`** — add `import Lean4Lean.Theory.Inductive.IotaGen`
   (verified cycle-free); move §1's three declarations + two private helpers in verbatim; rewrite
   `VEnv.IsStructure.ruleFreeHead`'s body to `IsStructureG.ruleFreeHead henv H.toG`.
2. **`Theory/Typing/NoConfRepair.lean`** — delete `hrf` from four signatures
   (`notStructInhab_of_isType`, `notStructInhab_of_forallE`, `ConstAppInvSI.of_isType`,
   `IsStructure.spine_inv_of_si`); `ConstAppInvSI.constNoConf` loses it by propagation. Replace
   `hrf _ _ _ _ _ hS` by `IsStructureG.ruleFreeHead henv hS`, and pass-throughs by
   `henv.isStructureG_ruleFreeHead`. Mark gap (i) closed. Fix (ii)'s `HasType.defeqU_l'` →
   `HasType.defeqU_l`, and correct the `shape.lean` figure 0 → 5.
3. **`Verify/Typing/ProjSpineInv.lean`** — **statement unchanged**, body only, and **only once
   `ConstAppInvSIFromWF` is a theorem**:

       -- today
       VEnv.constApp_inv_of_wf henv U hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
         (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)
       -- after
       (Hsi env U henv).of_isType_of_wf henv hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
         (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)

   Neither call site changes. `spineInvStmt_of_repair` is that substitution, elaborated.
4. **`docs/vacuity-ledger.md` row 245f** — the `shape.lean` evidence "0 hits, heads resolved"
   should read "5 hits, none concluding". I did not touch that file (forbidden).

No frozen file needs any change; none was edited or read for edit.

## Section 3 — what I did not do, and why

- **`ConstAppInvSIFromWF` is not proved.** It is the repair itself (the eta cases of
  `ParRed.constApp_inv` at `ConstSpine.lean:115` and `NormalEq.constApp_inv` at `:186`, then the
  Church–Rosser chain). Out of scope for (a)–(e), and `ConstSpine.lean` is read-only for me.
- **I did not check `ConstAppInvSI` at a concrete environment.** `NoConfRepair.lean` §3's
  `etaLink` already exhibits a non-degenerate relation satisfying eta + the guarded row at
  `unitEnv`; adding a second such model was not asked for and would not sharpen it.
- **The full instantiation of `SpineInvStmt` at `barEnv`** stops at the environment-side premises
  (`WF` + `IsStructure` + field count). The two `HasType`s at `Bar`'s spine would need two
  inhabitants of `Bar`, and `barDecl` has no axiom inhabitant; adding one means a new environment,
  which is `NoConfRepair.lean`'s `bigEnv` pattern at a *narrow* block and was not on the brief.
  Recorded as a bounded gap, not a claim.
