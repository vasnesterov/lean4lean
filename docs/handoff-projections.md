# Handoff: the projection cluster

**Census: 19 → 19** (`lake env lean scripts/sorry-census.lean`, run at the start *and* at the
end of this round; the same 19 names).  No hole closed, none added — this round is additive,
as the four before it were.  `TrProj.uniq` and `TrProj.weak'_inv` sat at **83** and **28**
transitive users at both ends of the round, unmoved.  **Three counts did move and it was not
this stream**: `IsDefEqU.forallE_inv` 105 → 107, `forallE_inv_stratified` 353 → 355 and
`weakN_iff` 107 → 109, because another stream edited `Theory/Typing/KEta.lean` and
`KMeasure.lean` and added an untracked `Theory/Typing/ProofRetypeHeads.lean` during the round.
Every declaration this stream added has a **measured empty hole cone**, so none of them can be
a user of anything.  `scripts/dup-names.lean` reports no duplicates over the joined cone, and
this round's three new modules are now **in** that cone — `Experimental/ConeJoin.lean` gained
`import Lean4Lean.Verify.Typing.ProjGenInstWitness`, which pulls `ProjGenInst` and
`ProjGenBeta` with it.  All three `Verify/Guard.lean` checks pass, unchanged: guard 1 ✓
(25 frozen axioms), guard 2 ✓ *"proof INCOMPLETE: sorryAx present"* (as it must), guard 3 ✓
(54/54).

Everything below is separated into **[checked]** (a named declaration in this tree, with its
axiom set or its measured cone reproduced) and **[read off source]** (an argument from reading
definitions, not run).

*Numbering.*  `§0.x` is **this** round, `§0′.x` the previous one, `§0″.x` the one before that,
then `§0‴.x` and `§0⁗.x`; all five are kept because later sections cross-reference them.
Sections 1–8 are older editions, and `§n` references *inside* them are to that edition's own
numbering.

---

## 0. This round: block A **finished** (`instN`, `instL`), and ingredient (b) of the real minor's typing lemma

### 0.1 Headline

`§0′.8`'s three named pick-ups are all done.

* **Block A is complete.**  The `instN` family — `padMinor_instN`, `realMinor_instN`,
  `padMotive_instN`, `VIndType.projMotive_instN`, `padMotives_instN`, `padMinorsAux_instN`,
  `padMinors_instN`, `projCoreG_instN`, `projArgsG_instN`, `projTermG_instN` — and the
  `instL` family — `projLvls_inst`, `padMinor_instL`, `realMinor_instL`, `padMotive_instL`,
  `VIndType.projMotive_instL`, `padMotives_instL`, `padMinorsAux_instL`, `padMinors_instL`,
  `projCoreG_instL`, `projArgsG_instL`, `projTermG_instL` — join last round's `lift'` family.
  Together with `lift'` these are the three entries `TrProj.weak'`, `TrProj.instN` and
  `TrProj.instL` run on.  **[checked]**
* **Ingredient (b) of `realMinor_hasType_gen` is landed**, in `ProjGenBeta.lean`:
  `projMotiveBodyG_instAll`, plus the three callees the generalisation also needed —
  `ProjClosedG.ftype_closedN`, `projTermG_instAll`, `projArgsG_eq_map`.
* **One correction to `§0′.6` and one to a statement of this stream's own** — §0.5.

Two new proof files and one new witness file, all owned.  Every new declaration has a
**measured empty hole cone** (`scripts/hole-cone.lean`, re-run, transitive over type *and*
value with `allowOpaque := true`) and no `sorryAx` (`scripts/proj-rerun.lean`, re-run: the
only three names in it that carry `sorryAx` are the three that carried it before —
`TrProj.wf`, `tryEtaStructCore.WF_of_structEta`, `isDefEqUnitLike.WF_of_structEta`).
**[checked]**

| file | content |
|---|---|
| `Lean4Lean/Verify/Typing/ProjGenInst.lean` | `VExpr.inst_liftN_add`/`map_inst_liftN_add`, the whole `instN` family, `projLvls_inst`, the whole `instL` family |
| `Lean4Lean/Verify/Typing/ProjGenBeta.lean` | `ProjClosedG.ftype_closedN`, `projTermG_instAll`, `projArgsG_eq_map`, **`projMotiveBodyG_instAll`** |
| `Lean4Lean/Verify/Typing/ProjGenInstWitness.lean` | the refutation re-run at the *conclusion*, the passenger check, the `Rich` firings, `padMinor_inst_moves`, the `Poly` block and the `instL` disequalities, the `DepPair` block, **three** negative controls |

Edited outside those three: `scripts/proj-rerun.lean`, `scripts/hole-cone.lean` (this round's
names and the new import in both) and **`Lean4Lean/Experimental/ConeJoin.lean`** — one import
line, the brief's standing instruction, so that both instruments see the new leaf.
`ProjGen.lean`, `ProjGenWitness.lean`, `ProjGenLift.lean`, `ProjGenLiftWitness.lean`,
`ProjClosedG.lean`, `ProjClosedGWitness.lean`, `Structure.lean`, `StructureClosed.lean`,
`StructureEta.lean`, `StructureExamples.lean`, `ProjSkip.lean`, `Lemmas.lean`,
`StructureUniq.lean`, `Rigidity.lean`, `DefEqCtx.lean` are **unedited**.  `TrProj`,
`TrProj.wf`, `projCore` and `IsStructure` are untouched for a **fifth** round, and
`IsStructureG` stays separate from `IsStructure` for `§0⁗.3` correction 4's polarity reason.

`TrProj.wf`'s measured hole cone is **`{weakN_iff, forallE_inv_stratified}` — unchanged**.  No
implementation file was touched, so the Kernel Arena is unaffected and was not re-run.

### 0.2 The `instN` family: the same shape, and the one thing that was different

Mirror of last round's `lift'` family, step for step, under the same `ProjClosedG` hypothesis
and for the same reason: `padMinor`/`realMinor` splice the constructor's field *and induction
hypothesis* telescope in with `instAll`, and an entry not closed at the spine arity keeps a
variable the substitution reaches on one side of the equation and not on the other.  The
counterparts are `VExpr.inst_instAllTele₀`, `inst_instAll`, `inst_bvars` — all already in
`TelescopeLift.lean` — and `Structure.lean:373–460` is the narrow model.  **[checked]**

The one repeated step that had no packaged form was
`(x.liftN n).inst e₀ (k + n) = (x.inst e₀ k).liftN n`: `Structure.lean` writes the same
`List.map_congr_left fun x _ => by rw [Nat.add_comm k n]; …` block out three times
(lines 412, 434, 454).  It is `VExpr.liftN_instN_lo` at `k := 0`, and it is now
`VExpr.inst_liftN_add` with a list version `map_inst_liftN_add`.  Its associativity is the
only thing that bit: in `projMotive_instN` the offset arrives as `k + |is| + 1` and the lemma
wants `k + (|is| + 1)`, so one `show … from by omega` rewrite is needed before the `simp only`
will fire.  That was the whole difficulty; `padMinorsAux_instN`'s `acc.length = q`
bookkeeping, which `§0′.6` flagged as the thing to watch, behaved exactly as the `lift'`
version did.

### 0.3 The `instL` family carries **no** hypothesis, and that is checked, not assumed

`instL` rewrites level data and moves no de Bruijn index, so none of these lemmas takes a
`ProjClosed`-style premise — `Structure.lean`'s header records the same asymmetry for the
narrow term.  What replaces it is that the level data stored inside `projCoreG` has to move
consistently, and that is `projLvls_inst`:
`(D.projLvls C us i).map (VLevel.inst ls) = D.projLvls C (us.map (VLevel.inst ls)) i`, the
generalised form of the `split <;> simp [VLevel.inst_inst]` that ends `projCore_instL`.

**The risk here is vacuity, not unsoundness**, and it is a real one: `Rich` and every
`blockOf _` in this cluster have `uvars = 0` and only closed levels, so `instL` is the
identity on them and a firing there would test nothing.  So §0.4 builds `Poly`.

### 0.4 Non-vacuity — **[checked]**

**The refutation is re-run against the fix, and this time at the *conclusion*.**  Last round
showed `ProjClosedGap.badCtor_not_projClosedG`: the block that satisfies all three
`ProjClosed` fields *fails the new predicate*.  This round is stronger.
`padMinor_instN_false_at_badCtor` shows that at that same block the **conclusion of
`padMinor_instN` is false** — `padMinor_at_badCtor_inst` and `padMinor_at_badCtor_spine`
compute the two sides, and they differ at the induction hypothesis's own binder, i.e. exactly
at the stored `ξ`.  So the hypothesis is not decoration: drop it and the lemma is not merely
unproved, it is wrong.

**The second conjunct is not a passenger.**  `argsCtor` moves only the stored `π`, with `ξ`
empty and all three `ProjClosed` fields holding.  `padMinor_instN_false_at_argsCtor` shows the
conclusion still fails there, and `padMinor_at_argsCtor_inst`/`_spine` locate the discrepancy
at the `π`-derived variable — a *different* position from `badCtor`'s.

**The consumer fires where the closedness bound is exactly saturated.**  `Rich`'s
`minorBinders` is closed at `D.np + D.nm + q = 2` and **not** at `1`
(`Rich.minorBinders_not_closed_at_1`, last round).  `padMinor_instN_fires` runs
`padMinor_instN` at a spine of length exactly `2`; `projCoreG_instN_fires` and
`projTermG_instN_fires` run the whole chain there with every premise discharged.

**The conclusion is not an identity, and it is a *different* test from the lift's.**
`padMinor_at_rich_inst` computes the padding minor at `Rich` after the substitution and
**four distinct positions move**: the field type `.bvar 0 ↦ W`, the ih's own `ξ` binder
`.bvar 2 ↦ W`, the motive it applies `.bvar 4 ↦ .bvar 3`, and the padding type
`.bvar 5 ↦ .bvar 4`.  Two of the four are *replacements* and two are *renumberings*, whereas
`padMinor_lift_moves` saw four renumberings — so this is not the same check re-run.
`padMinor_inst_moves` turns it into a machine-checked `≠`, decided from the constructors'
`injEq` rather than read off the two computations.

**The `instL` family, at a block whose levels actually move.**  `Poly` has one universe
parameter and `isLE := true`, so `projLvls` reads the projected field's own level:
`projLvls_at_poly` is `[u, u]`, and with `isLE := false` it would be `[u]` and carry no field
data at all.  `projLvls_inst_fires`, `projLvls_moves`, `projMotive_at_poly(_instL)`,
`projMotive_instL_moves` and `projTermG_instL_fires` are the firings and the two
disequalities.

**Three negative controls, none of them an arity error.**

* `realMinor_instN_false_without_hi` — at a **nullary** constructor the `ClosedTele` premise
  holds vacuously (the telescope is empty), so `i < C'.fields.length` is the only premise
  standing; drop it and `realMinor`'s body is a variable of the *ambient* context, which the
  substitution replaces on the left and leaves alone on the right.  Both sides are the same
  `realMinor` at the same block, spine length and minor index.
* `projArgsG_instN_false_at_zero` — at `k = 0` the substitution reaches the major-premise
  binder `.bvar 0`, so `1 ≤ k` is not slack.  `projArgsG_one_at_rich` records that both sides
  are one-element lists, so this is not a length mismatch; the discrepancy is read out with
  `lastArg`, the spine's final argument.
* `projMotiveBodyG_instAll_false_without_hps` — drop `ps.length = D.np` and the beta
  ingredient is false at `Rich`: the stored field type is the parameter `.bvar 0`, which the
  shortened `instAll` no longer covers, so the major premise reaches it.
  `motiveBody_lhs_without_hps` computes the left side to `W` and
  `motiveBody_rhs_without_hps` the right to `.bvar 0`.

### 0.5 Two corrections

**Correction 1 — `§0′.6` item 1(b) put `projMotiveBody_instAll` in the wrong file, and it is
four lemmas, not one.**  It is *used* in `Verify/Typing/Lemmas.lean` (lines 1296 and 1361); it
is **declared** in `Theory/Inductive/StructureClosed.lean:1298`.  And it is not
self-contained: its proof runs on `VInductDecl'.projTerm_instAll` and
`VInductDecl'.projArgs_eq_map` (`Theory/Inductive/Structure.lean:585,600`) and on
`ftype_closedN` (`StructureClosed.lean:1226`), and all three are narrow in the same way — they
take `D.ProjClosed T C`, and `projTerm`/`projArgs` rather than `projTermG`/`projArgsG`.  So
ingredient (b) is **four** generalisations.  All four are now proved, in `ProjGenBeta.lean`,
and none of the narrow four was edited.  **[checked]**

**Correction 2 — this stream's own `projTermG_instN` was over-hypothesised, and the
over-hypothesis would have been fatal one lemma later.**  It was first written with
`hk : 1 ≤ k`, by analogy with `projArgsG_instN`.  That premise is **not** in the narrow
`projTerm_instN`, and for a reason: `projTerm_instN` calls `projArgs_instN` at cut
`k + |is| + 1`, which is `≥ 1` unconditionally.  The premise was removed, and the check that
it mattered is `projTermG_instAll`: that lemma iterates the substitution over a whole spine
and instantiates at cut **`0`** on every step (`VExpr.instAll_cons` then `Nat.zero_add`), so
with `1 ≤ k` in place it could not have been proved at all.  This is `ORCHESTRATOR.md`'s
"invariant too strong to propagate", caught by writing the consumer.  **[checked]**

### 0.6 Ingredient (b), and what it does and does not settle

`projMotiveBodyG_instAll` says: the real motive's body, saturated by index terms and a major
premise, is field `i`'s type with the parameters and the earlier **generalised** projections
of that major premise substituted.  The narrow `hcl : D.ProjClosed T C` becomes `ProjClosedG`
plus the two `IsStructureG` fields `hTj`/`hctors` — the latter only because `projTermG_instN`
needs them (they are what makes `projected_fields_lt` hold).  Everything else is the narrow
proof unchanged: `instAll_instAll` at the closedness bound, `instAll_liftN` to cancel the
parameter half, `projTermG_instAll` on each of the `i` earlier projections.  **[checked]**

Its non-vacuity needed a second block.  At `Rich`, field types are a parameter and a constant,
so the `(List.range i)` block on the right-hand side is substituted into a type that does not
mention it — the equation fires (`Rich.projMotiveBodyG_instAll_fires`) but shows nothing about
the substitution.  `DepPair` is a two-field block whose **second field's type mentions the
first field**; there `DepPair.rhs_computed` shows the right-hand side is
`B (projTermG … 0 0 x)`, and `DepPair.rhs_moves` is the machine-checked statement that it is
**not** the stored type.  **[checked]**

What this does **not** settle: ingredient (c).  See §0.7.

### 0.7 What is left, exactly

1. **`realMinor_hasType_gen`** — still open, still what `VEnv.IsStructure.noRec` is waiting on.
   Of its three ingredients:
   * **(a) `VIndType.projMotive_liftN`** — landed last round.  **[checked]**
   * **(b) the block-index generalisation of `projMotiveBody_instAll`** — landed this round,
     as four lemmas (§0.5 correction 1).  **[checked]**
   * **(c) the field-variable lookup through the ih block** — **untouched, and it is now the
     whole of what is left.**  `realMinor`'s body is `.bvar (Θ.length - 1 - i)` with
     `Θ = fields ++ ihs`, which resolves to `Θ[i]` — the right field — but its looked-up type
     is `Θ[i]` weakened by `Θ.length - i`, i.e. by `nr` more than in the narrow case, and that
     lift has to be reconciled with the declared body.  `projMinor_hasType`
     (`Verify/Typing/Lemmas.lean:984`) is the `nr = 0` ancestor; it runs a strong induction
     packaged as `ProjHasType` (`StructureClosed.lean:1335`), and *that* induction is the
     bulk.  **[read off source]**, not attempted, not costed.  The reason it was left is the
     brief's own ordering — (b) first, so that the induction is the only open part when it is
     attempted — and that ordering is now satisfied.
2. **Block B (the swap)** is unchanged and was not attempted; it needs `projCoreG_hasType`,
   which needs item 1.
3. `TrProj.uniq` (83 users) and `TrProj.weak'_inv` (28) remain **structurally** blocked
   (`§0‴.6`, `§0⁗.6`): they need `VEnv.PatWF`/`VEnv.WeakNorm`, which are open hypotheses, not
   census holes, plus ledger G4, which has no statement in the tree.  Consuming them needs a
   new `sorry` or axiom.  Not this round's business and not next round's.

### 0.8 What I would pick up first

1. **Ingredient (c)**, i.e. `projMinor_hasType`'s `ProjHasType` induction re-run with the ih
   block bound.  It is the only thing between here and `realMinor_hasType_gen`, and
   `realMinor_hasType_gen` is the only thing between there and block B.  Budget a full round:
   the narrow ancestor is ~330 lines of `Verify/Typing/Lemmas.lean` and the generalisation
   changes the telescope under every one of them.
2. Before starting it, read `minorTele_gen` and `minorBodyArgs_gen` (`ProjGen.lean`) — they
   already say what `Θ` and the motive's spine *are* at a recursive constructor, and (c) is
   the lookup **into** that `Θ`, not a re-derivation of it.
3. Do **not** treat the const-application family as unconditional: `ConstSpineWF.lean`'s route
   passes through `church_rosser`, which is under `§0‴.6`'s live conditional refutation.
   Re-measured this round from the same instrument: `not_crStatement_of_kstep`'s cone is
   `{forallE_inv_stratified}` and still does **not** contain `NormalEq.descend`, so the
   refutation is not circular with the hole confluence waits on.  **[checked]**

### 0.9 Relay to the orchestrator

* **`Experimental/ConeJoin.lean` was edited by this stream** — one import line
  (`Lean4Lean.Verify.Typing.ProjGenInstWitness`), on the brief's standing instruction that a
  new leaf module must be added there or both instruments are blind to it.  This stream does
  not own that file; the edit is one line and nothing else in it was touched.
* **Another stream's uncommitted work is in the census cone and moved three counts**:
  `Theory/Typing/KEta.lean` and `KMeasure.lean` are modified and
  `Theory/Typing/ProofRetypeHeads.lean` is untracked, and over the round
  `IsDefEqU.forallE_inv` went 105 → 107, `forallE_inv_stratified` 353 → 355 and `weakN_iff`
  107 → 109.  Not touched, not a problem — recorded so a "the counts moved" reading is not
  attributed to this cluster.  `TrProj.uniq` and `TrProj.weak'_inv` did **not** move.
* **`Theory/Typing/ProofRetypeHeads.lean` is not in `Experimental/ConeJoin.lean`.**  If it is
  a leaf, `dup-names.lean` and `sorry-census.lean` cannot see it, and the "no duplicates" line
  does not cover it.  That is the other stream's call, not this one's.


## 0′. The previous round: `ProjClosedG` **derived**, and block A's `lift'` family closed

### 0.1 Headline

Two of the three items §0″.6 left open are done.

* **Item 3's prerequisite is built, not stated.**  `VInductDecl'.ProjClosedG` — the four-field
  predicate §0″.4 wrote out — is **derived** from `D.WF env₀` + the `addInduct'` staging +
  `Ordered env` (`projClosedG_of_wf`), so it is a theorem at every environment `ProjClosed`
  was, and `VEnv.IsStructureG.projClosedG` / `VEnv.IsStructure.projClosedG` are the two
  corollaries.  Its **one real consumer** is proved:
  `closedTele_minorBinders : ClosedTele ((D.minorBinders q C').map (·.instL lvls)) (D.np + D.nm + q)`
  — the audit §0″.9 asked for *before* the rest of block A.  It went through.
* **Block A's `lift'` family is complete**: `projCoreG_lift'`, `projArgsG_lift'`,
  `projTermG_lift'`, on top of `padMinor_lift'`, `realMinor_lift'`, `padMotive_lift'`,
  `projMotive_lift'`, `padMotives_lift'`, `padMinorsAux_lift'`, `padMinors_lift'`.  These are
  the entries `TrProj.weak'` and `TrProj.mono` run on.
* **One entry of item 2 fell out of it**: `VIndType.projMotive_liftN`, the real motive's
  analogue of `padMotive_liftN`, is a three-line corollary of `projMotive_lift'`.  It is one of
  the three ingredients `realMinor`'s typing lemma needs (§0′.6).

Three new files, all owned; nothing existing was edited except the two instruments.  Every new
declaration has a **measured empty hole cone** (`scripts/hole-cone.lean`, re-run) and no
`sorryAx` (`scripts/proj-rerun.lean`, re-run).  **[checked]**

| file | content |
|---|---|
| `Lean4Lean/Verify/Typing/ProjClosedG.lean` | `ProjClosedG`, `toProjClosed`, `projClosedG_of_wf`, the two `IsStructure*` corollaries, `ClosedTele.liftTele`/`.shiftTele`, `closedN_ihType`, **`closedTele_minorBinders`** |
| `Lean4Lean/Verify/Typing/ProjClosedGWitness.lean` | `badCtor_not_projClosedG`, `argsCtor`/`projClosedG_needs_recArgs_args`/`argsCtor_not_projClosedG`, the `Rich` block and `richBlock_projClosedG`, `ihType_closed`, `minorBinders_closed`, two negative controls |
| `Lean4Lean/Verify/Typing/ProjGenLift.lean` | the whole `lift'` family, plus `length_projArgsG`, `projected_fields_lt`, `projMotive_liftN` |
| `Lean4Lean/Verify/Typing/ProjGenLiftWitness.lean` | `projCoreG_lift'_fires`, `projTermG_lift'_fires`, `padMinor_at_rich(_lifted)`, `padMinor_lift_moves` |

### 0.2 The derivation, and the environment staging §0″.4 flagged

§0″.4 said the environment-staging step "should be looked at first, because it is where the
existing `projClosed` proof had to route around `env₁`".  That was the right thing to look at,
and the answer is cheaper than it looked.  **[checked]**

`VEnv.addInduct'_stages` splits `addInduct'` into `addIndTypes → addIndCtors → addIndRecs →
addIndRules`, and the three `_le` lemmas plus `addIndRules_le` give **`env₁ ≤ env`** for the
block-types-added environment `env₁`.  `Ordered.closed`'s `OnTypes … ClosedN` is antitone, so
it restricts to `env₁` exactly as `IsStructure.projClosed` restricts it to `env₀`.  After that:

* `params`, `indices` — `VExpr.ClosedTele.of_onCtx₀` at `env₀`, verbatim from
  `IsStructure.projClosed` with `H.types` replaced by the quantified `D.types[t]? = some T'`;
* `fields` — the **constructor constant** route, unchanged; the only new step is
  `(t, C') ∈ D.ctorsAll` from `D.types[t]? = some T'` and `C' ∈ T'.ctors`, which is
  `mem_ctorsAll`'s converse and is three lines;
* `recArgs` — both conjuncts come from `VIndField.WF.pos`'s `some r` branch **in `env₁`**:
  `ClosedTele r.binders (D.np + i)` from its `OnCtx (r.binders.reverse ++ Γ)` via
  `ClosedTele.of_onCtx₀`, and `∀ a ∈ r.args, a.ClosedN (D.np + i + |ξ|)` from its
  `HasType … (r.canonResult D i) (.sort D.lvl)` via `IsDefEq.closedN'` + `closedN_mkApp`.
  `Γ`'s length is `i + D.np` because `(C'.fields.take i).length = i`, which needs `i < nf` —
  supplied by `(i, r) ∈ C'.recFields`.

**No `Ordered env₁` is needed anywhere**, which is the point: `Ordered` is used only for the
final `env` (for `closedC` and for the antitone restriction).

### 0.3 The consumer, and the arithmetic that had to work out

`closedTele_minorBinders` splits `minorBinders = liftTele (nm+q) (atRecTele fields) ++ ihTypes`
by `closedTele_append`.  The first half is `ClosedTele.liftTele` (new, three lines).  The
second is `closedN_ihType`, and that is where the fourth field is consumed — the **only** place
it is needed.  The identity that has to hold, entry `s` of `ihTypes` at bound
`np + nm + q + nf + s`:

    (np + i + m) + (nm + q) + (nf - i + s)  =  (np + nm + q + nf + s) + m     for the ξ telescope
    (np + i + nxi) + (nm + q) + (nf - i + s)  =  (np + nm + q + nf + s) + nxi  for each π entry

both requiring `i ≤ nf`, and the head `.bvar (nxi + s + nf + q + (nm-1-r.idx))` requiring
`0 < D.nm` — which the consumer gets from `D.types[t]? = some T'`, not from `r.idx < D.nm`.
**[checked]**

### 0.4 Non-vacuity, and the refutation re-run against the fix — **[checked]**

**The repair kills its own witness.**  `ProjClosedGap.badCtor_not_projClosedG`:
`blockOf badCtor` — §0″.4's block, which satisfies all three `ProjClosed` fields and whose
`minorBinders` is not closed — **fails `ProjClosedG`**, at its recursive field's `ξ`.  So the
fourth field is not merely *sufficient* for the consumer; it is *false* exactly where the
three-field predicate was too weak.

**The second conjunct is not a passenger.**  §0″.4's witness moves only `ξ`.  `argsCtor` moves
only `π` — `ξ` is empty, all three `ProjClosed` fields hold, the fourth field's *first*
conjunct holds — and `projClosedG_needs_recArgs_args` shows the conclusion still fails
(`minorBinders_args` computes the offending entry: the ih reads `.bvar 2` at a bound of 2, and
the offending variable comes from `π`).  `argsCtor_not_projClosedG` is the matching
`ProjClosedG` failure.

**The consumer fires where the fourth field carries data.**  `Rich` is a block with a
parameter, an index, two fields, and a recursive field whose `ξ = [.bvar 1]` (the parameter)
and `π = [.bvar 0]` (the `ξ` binder) are **both non-empty** — `recFields_rich` records that.
`richBlock_projClosedG` is built by hand (no `WF` claim is made at this witness, so it cannot
come from `projClosedG_of_wf`), and then:

* `minorBinders_rich` computes the telescope:
  `[.bvar 1, .const Dummy, ∀ (.bvar 3), (.bvar 3) (.bvar 0) ((.bvar 1) (.bvar 0))]`;
* `ihType_closed` fires `closedN_ihType` at bound `1+1+0+2+0 = 4`, and the entry's largest
  variable is `.bvar 3` — **exactly saturated**;
* `minorBinders_closed` fires `closedTele_minorBinders` end to end at bound `np+nm+q = 2`.

**Two negative controls, neither of them a length error** (three entries either way):
`minorBinders_not_closed_at_1` — one below the proved bound the telescope is *not* closed, so
`D.np + D.nm + q` is not slack; and `ihEntry_not_closed_at_3` — the ih entry is not closed at
`3`, which is what `np + nm + q + nf` would be with the **motive block forgotten**.  The
variable that escapes there is the `ξ`-shifted `.bvar 3`, i.e. precisely the datum
`ProjClosed`'s three fields say nothing about.

### 0.5 Block A's `lift'` family, and its non-vacuity — **[checked]**

The chain, in dependency order, all under `ProjClosedG`:

| name | content |
|---|---|
| `padMinor_lift'`, `realMinor_lift'` | the two minor shapes; `VExpr.lift'_instAllTele₀` at `closedTele_minorBinders`' telescope.  `realMinor` additionally needs `i < C'.fields.length` so its body variable is inside the telescope |
| `padMotive_lift'` | the `Lift` version of `padMotive_liftN` |
| `VIndType.projMotive_lift'` | the fragment of `projCore_lift'` that concerns the motive, split out |
| `padMotives_lift'` | the block: real motive at `j`, padding elsewhere |
| `padMinorsAux_lift'`, `padMinors_lift'` | the accumulator recursion.  `acc.length = q` is what ties the accumulator to the minor index so the spine's length really is `np + nm + q` |
| `projCoreG_lift'`, `projArgsG_lift'`, `projTermG_lift'` | the capstones, mirroring `Structure.lean:296–450` |

Two hypotheses beyond `projCore_lift'`'s: `D.types[j]? = some T` and `T.ctors = [C]` — the two
`IsStructureG` fields.  They are needed for `projected_fields_lt`: `padMinorsAux` builds a
`realMinor` at **every** constructor of the projected type, so `i < C'.fields.length` has to
hold for each of them, and `T.ctors = [C]` is what makes that `hi`.  (`IsStructureG.ctors` is
the field §0⁗.3's correction 4 says is genuinely forced by the kernel, so this costs nothing.)

**Fired end to end** at `Rich` — a *recursive* block, which is the case the whole
generalisation exists for: `projCoreG_lift'_fires` and `projTermG_lift'_fires`, with every
premise discharged and the concrete lifted spine on the right.

**The conclusion is not an identity.**  `padMinor_at_rich` and `padMinor_at_rich_lifted`
compute the padding minor at `Rich` before and after `.skip .refl`, and **four distinct
variables move** — the field type `.bvar 0 → 1`, the ih's own `ξ` binder `.bvar 2 → 3`, the
motive it applies `.bvar 4 → 5`, and the padding type `.bvar 5 → 6`.  `padMinor_lift_moves`
turns that into a machine-checked `≠` (decided from the constructors' `injEq`, not read off the
two computations).

### 0.6 What is left, exactly

1. **`realMinor`'s typing lemma** — still open, and still what `VEnv.IsStructure.noRec` is
   waiting on.  This round did not close it, but it **costed** it, and one of its three
   ingredients landed.  What `realMinor_hasType_gen` needs, by comparison with
   `padMinor_hasType'` (whose steps 1–2 — `hsplit` by `instAll_mkPi`, then `IsType.mkPi_inv` —
   are shape-generic and apply unchanged):
   * **(a) `projMotive_liftN`** — the real motive commutes with the weakening past the minor's
     own binders.  **Done this round**, as a corollary of `projMotive_lift'`.  **[checked]**
   * **(b) a block-index generalisation of `projMotiveBody_instAll`** (`Verify/Typing/Lemmas.lean`)
     — the real motive applied to `minorBodyArgs` β-reduces to the projected field's type.  This
     is the analogue of `padMotive_app_beta`, and it is stated at `IsStructure`'s index `0`;
     the generalisation is the same substitution of `H.types0`/`H.memCtor`/`H.memCtorsAll`/
     `H.typesD` that `ctorArgs_hasArgs_gen` performed.  **[read off source]**, not attempted.
   * **(c) the field-variable lookup through the ih block.**  `realMinor`'s body is
     `.bvar (Θ.length - 1 - i)` with `Θ = fields ++ ihs`, which resolves to `Θ[i]` — the right
     field, checked by hand against `Θ.reverse` — but its looked-up type is `Θ[i]` weakened by
     `Θ.length - i`, i.e. **by `nr` more than in the narrow case**, and that lift has to be
     reconciled with the declared body.  `projMinor_hasType` (`Verify/Typing/Lemmas.lean`) is
     the `nr = 0` ancestor; it runs a strong induction packaged as `ProjHasType`, and *that*
     induction, not (b) or (c) individually, is the bulk.  **[read off source]**, not attempted,
     not costed.
2. **Block A's `instN` and `instL` families.**  The `lift'` family is done; `instN` mirrors it
   step for step (`VExpr.inst_instAllTele₀`, `inst_instAll`, `inst_bvars` are the counterparts
   already proved in `TelescopeLift.lean`, and `Structure.lean:376–460` is the narrow model),
   and `instL` is the easy one — no `ProjClosed`-style hypothesis at all, as
   `Structure.lean`'s header notes.  **Not attempted.**  Nothing in this round suggests they
   will behave differently; the one thing to watch is that `padMinorsAux_instN`'s accumulator
   bookkeeping is the same `acc.length = q` invariant, which is where the `lift'` version's
   only real difficulty was.
3. **Block B (the swap)** is unchanged and was not attempted; it needs `projCoreG_hasType`,
   which needs item 1.

### 0.7 Files this round

New (all owned): `Lean4Lean/Verify/Typing/ProjClosedG.lean`, `ProjClosedGWitness.lean`,
`ProjGenLift.lean`, `ProjGenLiftWitness.lean`.

Edited: `scripts/proj-rerun.lean` and `scripts/hole-cone.lean` only — this round's names added
to both instruments, and `ProjGenLiftWitness` added to both imports.

**Unedited**: `ProjGen.lean`, `ProjGenWitness.lean`, `Structure.lean`, `StructureClosed.lean`,
`StructureEta.lean`, `StructureExamples.lean`, `ProjSkip.lean`, `Lemmas.lean`,
`StructureUniq.lean`, `Rigidity.lean`, `DefEqCtx.lean`, `ConstSpineWF.lean`.  `TrProj`,
`TrProj.wf`, `projCore` and `IsStructure` are untouched for a **fourth** round.
`IsStructureG` stays separate from `IsStructure` for §0⁗.3 correction 4's polarity reason:
`IsStructure` sits in a **negative** position in `VEnv.StructEta`, and **no non-vacuity check
can detect an over-strong assumption** — the witnesses still fire.

`TrProj.wf`'s measured hole cone is **`{weakN_iff, forallE_inv_stratified}` — unchanged**.  No
implementation file was touched, so the Kernel Arena is unaffected and was not re-run.

### 0.8 What I would pick up first

1. **Block A's `instN` family** — it is the same shape as this round's `lift'` family, the
   hypothesis (`ProjClosedG`) now exists and is derived, and the audit that could have
   invalidated the whole approach (`closedTele_minorBinders`) has passed.  Half a round.
2. Then `instL`, then item 1(b) — the block-index generalisation of `projMotiveBody_instAll`,
   which is mechanical and is the ingredient of `realMinor`'s typing lemma that does *not*
   need the `ProjHasType` induction.  Do that **before** attempting 1(c), so that when the
   induction is attempted the only open part is the induction.
3. Do **not** treat the const-application family as unconditional: its route passes through
   `church_rosser`, which is under §0‴.6's live conditional refutation.  Re-measured this round
   from the same instrument: `not_crStatement_of_kstep`'s cone is `{forallE_inv_stratified}`
   and still does **not** contain `NormalEq.descend`, so the refutation is not circular with
   the hole confluence waits on.  **[checked]**
4. `TrProj.uniq` and `TrProj.weak'_inv` remain **structurally** blocked (§0‴.6, §0⁗.6): they
   need `VEnv.PatWF`/`VEnv.WeakNorm` plus ledger G4, which has no statement in the tree.

### 0.9 Relay to the orchestrator

* Another stream's **uncommitted** `Lean4Lean/Verify/Primitive.lean` is in the census cone and
  added two transitive users to each of `TrProj.uniq` and `TrProj.weak'_inv` during this round.
  Not touched, not a problem — recorded because a "the counts moved" reading of the census
  would otherwise be attributed to this cluster.
* Untracked at the end of the round and not this stream's: `Lean4Lean/Theory/Typing/ConstVar.lean`,
  `Lean4Lean/Theory/Typing/RetypeAdmissible.lean`.  Not touched.
* `scripts/dup-names.lean` does **not** import this cluster's witness modules, so its
  "no duplicates" line does not cover new files in `Verify/Typing/`.  This round checked the
  joined cone plus the three new modules explicitly; a permanent fix would be to add them to
  `Experimental/ConeJoin.lean`, which this stream does not own.

---

## 0″. Two rounds back: the padding minor at a **recursive** constructor, and one correction to §0‴.4

### 0′.1 Headline

**§0‴.10's named pick-up — item 1 of §0‴.4, the padding minor at a recursive constructor —
is closed.**  `padMinor_hasType_gen` is `padMinor_hasType_norec` with
`hrec : C'.recFields = []` **removed**: the padding minor's whole typing obligation now holds
at *any* constructor of *any* block member.  Six new declarations in
`Lean4Lean/Verify/Typing/ProjGen.lean`, three witness theorems plus a two-theorem refutation
in `ProjGenWitness.lean` (both owned), every one with a **measured empty hole cone**
(`scripts/hole-cone.lean`, re-run; transitive over type *and* value, `allowOpaque := true`).
**[checked]**

| name | content |
|---|---|
| `VExpr.instAll_liftN_below` | the missing commutation: a weakening whose cut is **below** the substitution window. `TelescopeLift.lean`'s `liftN_instAll` is the case `j = k`; the induction hypotheses sit at cut `0` while the window starts at `nr + nf`, so it does not apply |
| **`VInductDecl'.minorTele_gen`** | the minor's telescope splits as *field block* `++` *ih block*, at any constructor.  `minorTele_norec` is now its `recFields = []` corollary |
| **`VInductDecl'.minorBodyArgs_gen`** | the motive's spine is the non-recursive one **weakened by `nr`**.  `minorBodyArgs_norec` is now its `recFields = []` corollary |
| **`padMinor_hbs_gen`** | `padMinor_hasType'`'s last premise, discharged with no `hrec`.  `padMinor_hbs_norec` is now a one-line corollary |
| **`padMinor_hasType_gen`** | **the capstone**: the padding minor is well-typed at any constructor of any block member.  `padMinor_hasType_norec` is now a one-line corollary |
| `MutRec.R`, `rmk`, `decl1r`, `ihTypes_at_rmk`, `minorTele_at_rmk`, `minorBodyArgs_at_rmk` | non-vacuity at a genuinely recursive block — §0″.3 |
| `ProjClosedGap.projClosedG_needs_recArgs`, `projClosed_ok_without_recArgs` | the correction to §0‴.4 item 3 — §0″.4 |

Nothing was deleted: all four `_norec` names still exist, with their statements unchanged, as
corollaries.

### 0′.2 How it went through, and the one lemma that was missing

§0‴.4 item 1 named the three steps, and two of the three were right:

* **values** — `shift (nm+q) nr nf (atRec a)` is `((atRec a).liftN (nm+q) nf).liftN nr 0`,
  and the outer `liftN nr` has to cross the `instAll` at cut `nr + nf`.  §0‴.4 named
  `VExpr.liftN_instAll` (`TelescopeLift.lean:324`) for this.  **It does not apply**:
  `liftN_instAll` is `instAll (liftN n X k) as (k + n) = liftN n (instAll X as k) k`, i.e. the
  lift's cut and the window's lower edge coincide.  Here the lift's cut is `0` and the
  window's is `nf`.  The lemma that was actually needed is new —
  `VExpr.instAll_liftN_below`, `instAll (X.liftN n j) as (n + k) = (instAll X as k).liftN n j`
  for `j ≤ k` — three lines, by the same `liftN_instN_lo` induction.  **[checked]**
* **context** — §0‴.4 named `HasArgs.weak'`/`weakR`.  `weakR` is the **wrong direction**: it
  extends the context on the *outside* and shifts no index, whereas the ihs are new binders
  on the *inside*.  What is used is `HasArgs.weakN` at `Ctx.LiftN nr 0`.  `weak'` is not used
  either.  **[checked]**
* **`ihTypes` needs no typing** — this was right, and it is why the whole thing is cheap: the
  padding minor binds the ihs and ignores them, so all that is ever used about the ih block is
  its **length**.  `padMinor_hbs_gen`'s proof mentions `D.ihTypes` only inside `Ctx.LiftN.zero
  … (by simp)`.  **[checked]**

The structural choice worth carrying: `padMinor_hbs_gen` proves the `nf`-level statement
first (`base`, literally `ctorArgs_hasArgs_gen` and `ctorApp_hasType_gen` concatenated), then
weakens it once.  The alternative — re-deriving the two constructor lemmas over lifted data —
is what §0‴.2 already recorded as the mistake to avoid at the motive, and it would have been
the same mistake here.

### 0′.3 Non-vacuity, at a block `decl2` cannot express — and two negative controls

`decl2`, the witness every earlier round used, has **no recursive constructor**: every
constructor of `decl2` is nullary, so `nr = 0` there and the `liftN nr` this round introduces
is the identity.  A firing at `decl2` would therefore have tested nothing.  So a second
witness was built:

`MutRec.R` — `inductive R where | mk : R → R`, **declared for real**, with an `#eval` guard
that fails the build if `isRec` stops being `true`, if the arity moves, or if
`Lean.isNonRecStructure` starts accepting it.  Its abstract image is `decl1r` / `rmk`, with
one field carrying `recArg := some ⟨[], 0, []⟩`, so `nr = nf = nm = 1`.  **[checked]**

* `MutRec.ihTypes_at_rmk` — `decl1r.ihTypes 0 rmk = [.app (.bvar 1) (.bvar 0)]`, i.e. the ih
  is *motive applied to field*, and `nr = 1`.  **[checked]**
* `MutRec.minorTele_at_rmk` — `minorTele_gen` fired: the telescope is
  `[R, .app (m.liftN 1) (.bvar 0)]`, **two** binders, the second being the induction
  hypothesis with the motive weakened past the field.  **[checked]**
* `MutRec.minorBodyArgs_at_rmk` — `minorBodyArgs_gen` fired: the constructor applied to its
  own field is `R.mk (.bvar 1)`, **not** `R.mk (.bvar 0)`.  **[checked]**

**The two negative controls, run outside the tree, output reproduced in the docstrings.**
Both are the `nr = 0` reading — which is exactly what the `_norec` lemmas assert — and both
are rejected:

    -- minorTele: the `norec` collapse
    error: Application type mismatch: The argument `rfl` has type `?m = ?m`
    but is expected to have type
      instAllTele (List.map (fun F => instL [] F.type) rmk.fields) [] ++
          instAllTele (List.map (instL []) (decl1r.ihTypes 0 rmk)) ([] ++ [m] ++ [])
            rmk.fields.length
        = [const `MutRec.R []]

    -- minorBodyArgs: the field read at `.bvar 0` instead of `.bvar 1`
    error: Application type mismatch: The argument `rfl` has type `?m = ?m`
    but is expected to have type
      List.map (fun x => liftN (decl1r.ihTypes 0 rmk).length x) (…)
        = [(const `MutRec.R.mk []).mkApp [bvar 0]]

Neither is an arity error: the telescope has the same length either way in the first, and the
spine has one entry either way in the second.  This is the `minorBody_head_at_decl2` standard
of §0‴.3, met at the datum this round actually changed.  **[checked]**

**What is *not* fired end to end:** `padMinor_hbs_gen` and `padMinor_hasType_gen` themselves.
Their premises include `env.Ordered`, `D.IotaCtx env` and a `HasArgs` for the parameter spine,
so firing them needs a *well-formed environment* witness, which no witness in this cluster has
(`decl2` and `decl1r` both make no `WF` claim, by design — see `StructureBridge.lean`'s note).
Same status as `padMinor_hasType'` in §0‴.3.  **"No witness" is not evidence of truth**; what
is evidence is that both syntactic ingredients are fired at a recursive block above, and that
the third ingredient (`ctorArgs_hasArgs_gen`/`ctorApp_hasType_gen`) is unchanged from the
non-recursive case, which *was* reachable.

### 0′.4 **Correction: §0‴.4 item 3 understates block A's prerequisite** — **[checked]**

§0‴.4 item 3 says the first prerequisite of the `lift'`/`instN`/`instL` commutation lemmas is
"a `ProjClosed` generalised to every block member (`ClosedTele` for *each* `T'.indices` and
each `C'.fields`, not just the projected pair)".

**That is not sufficient, and this round is why.**  `projCoreG`'s minor block is built over
`minorBinders`, which contains `ihTypes`, which splices in a recursive field's stored `ξ`
(`VIndRecArg.binders`) and `π` (`.args`).  `VExpr.lift'_instAllTele` — the step every one of
those commutations runs on — asks for
`ClosedTele ((D.minorBinders q C').map (·.instL lvls)) (D.np + D.nm + q)`, and the three
fields of `ProjClosed` do not determine it.

`ProjClosedGap.projClosedG_needs_recArgs` is the machine-checked witness: a one-type block
with no parameters and no indices whose single field records
`recArg := some ⟨[.bvar 0], 0, []⟩`.  All three `ProjClosed` fields hold (`params`, `indices`
and `fields` are each `ClosedTele … 0`), and `minorBinders` computes to
`[Q, ∀ (.bvar 2), .bvar 2 (.bvar 1 (.bvar 0))]`, whose second entry is **not** `ClosedN … 2`.
`ProjClosedGap.projClosed_ok_without_recArgs` is the **positive control**: the same block with
`binders := []` *is* closed, so what fails is precisely the recursive-field data and not the
shape of `ihTypes`.  **[checked]**

**Register, stated carefully.**  This is a counterexample to an *implication between
predicates*, which is what a hypothesis-sufficiency claim is: `ProjClosed` is a **hypothesis**
the commutation lemmas take (`VEnv.IsStructure.projClosed` derives it, but the lemmas
themselves do not), so the question is whether its fields determine the closedness the proof
needs.  They do not.  `blockOf badCtor` is **not** a well-formed declaration —
`VIndField.WF.pos`'s `some r` branch demands `OnCtx (r.binders.reverse ++ Γ)`, which forces
`r.binders` closed at `np + i` — so **nothing here says a real block breaks.**  It says the
generalised predicate must record the recursive-field data, or the lemmas must take
`D.WF env` / `D.IotaCtx env` and derive it.

**[read off source]** the shape that would be needed, if it is recorded as a predicate:

```
structure ProjClosedG (D : VInductDecl') : Prop where
  params  : ClosedTele D.params 0
  indices : ∀ t T', D.types[t]? = some T' → ClosedTele T'.indices D.np
  fields  : ∀ t T', D.types[t]? = some T' → ∀ C' ∈ T'.ctors,
              ClosedTele (C'.fields.map (·.type)) D.np
  recArgs : ∀ t T', D.types[t]? = some T' → ∀ C' ∈ T'.ctors → ∀ i r, (i, r) ∈ C'.recFields →
              ClosedTele r.binders (D.np + i) ∧
              ∀ a ∈ r.args, a.ClosedN (D.np + i + r.binders.length)
```

and **[read off source]** the derivation route: the first three copy
`VEnv.IsStructure.projClosed` (`StructureClosed.lean:75`) with `H.types`/`H.ctors`/`hTj`
substituted, exactly as `ctorArgs_hasArgs_gen` did; the fourth comes from `VIndField.WF.pos`'s
`OnCtx (r.binders.reverse ++ Γ)` via `ClosedTele.of_onCtx₀`, and from its `HasArgs … r.args`
clause.  **Not attempted, not costed** — and the environment-staging step (`pos` is a
judgement in `env₁`, the block-types-added environment, while `projClosed`'s `hc₀` is
`OnTypes env₀`) is the part that should be looked at first, because it is where the existing
`projClosed` proof had to route around `env₁` for the field case.

### 0′.5 The standing checks, re-run — **[checked]**

`scripts/proj-rerun.lean` (updated with this round's names) prints `#print axioms` for every
standing check.  All fire, none acquired `sorryAx`:

    VEnv.empty_structEta                     [propext, Quot.sound]
    bazEnv_structEta                         [propext, Classical.choice, Quot.sound]
    bazEnv_etaExpansion_eq                   [propext]
    bazEnv_projMinors_distinct               [propext]
    bazEnv_structEta_premises                [propext, Classical.choice, Quot.sound]
    MutNonRec.kernelProjChecks               [propext, Classical.choice, Quot.sound]
    MutNonRec.projCore_arity_wrong           [propext]
    MutNonRec.projCoreG_arity_right          [propext, Quot.sound]
    MutNonRec.projCoreG_arity_right'         [propext, Quot.sound]
    VInductDecl'.projTermG_eq_projTerm       [propext, Quot.sound]
    VInductDecl'.recArity_eq_projCoreG       [propext, Quot.sound]
    VInductDecl'.projCoreG_eq_projCore       [propext, Quot.sound]
    TrProj.wf                                [propext, sorryAx, Classical.choice, Quot.sound]
    tryEtaStructCore.WF_of_structEta         [propext, sorryAx, …]
    isDefEqUnitLike.WF_of_structEta          [propext, sorryAx, …]
    VInductDecl'.minorBody_instAll_spine     [propext, Quot.sound]
    padMotive_app_beta / padMinor_beta / padMinor_hasType'          (clean)
    padMinor_hbs_norec / padMinor_hasType_norec                     (clean)
    VInductDecl'.minorTele_gen               [propext, Quot.sound]
    VInductDecl'.minorBodyArgs_gen           [propext, Quot.sound]
    padMinor_hbs_gen                         [propext, Classical.choice, Quot.sound]
    padMinor_hasType_gen                     [propext, Classical.choice, Quot.sound]
    MutRec.ihTypes_at_rmk                    [propext]
    MutRec.minorTele_at_rmk                  [propext, Quot.sound]
    MutRec.minorBodyArgs_at_rmk              [propext, Quot.sound]
    ProjClosedGap.minorBinders_bad           [propext]
    ProjClosedGap.projClosedG_needs_recArgs  [propext]
    ProjClosedGap.projClosed_ok_without_recArgs [propext]

`TrProj.wf`'s measured hole cone is **`{weakN_iff, forallE_inv_stratified}` — unchanged**, so
the round is additive at the cone level as well as the file level.  Every new declaration's
hole cone is **empty**.  `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations
across the joined cone"*.  **[checked]**

The five `rfl` validations of `etaExpansion` against Lean's elaborator remain **anonymous
`example`s** in `Theory/Inductive/StructureExamples.lean` — no names, so not `#print
axioms`-able; their only instrument is that the module elaborates, which it does.  (§0‴.5's
correction, repeated because handoffs keep citing them as if they were named theorems.)

### 0′.6 What is left of the generalisation, exactly

1. ~~The padding minor at a recursive constructor.~~  **Closed this round.**
2. **The real minor at index `j`.**  `realMinor` (bind fields *and* ihs, return field `i`)
   still has **no typing lemma at all**.  `projMinor_app` (`StructureClosed.lean:826`) is the
   `nr = 0` ancestor.  Not started, not costed.  **This — not item 1 — is what
   `VEnv.IsStructure.noRec` is now waiting on**: `padMinor_hasType_gen` lifts `noRec` for the
   *padding* minors (constructors of block members other than the projected one), and the
   projected constructor's own minor is item 2.  `padMinor_hasType_gen`'s docstring says so;
   do not read "the recursive case is closed" as "`noRec` can be dropped".
3. **Mechanical block A**, the `lift'`/`instN`/`instL` commutation for `projCoreG` —
   `projCoreG_lift'`, `projCoreG_instN`, `projCoreG_instL` and the `projArgsG`/`projTermG`
   versions, mirroring `Theory/Inductive/Structure.lean:296–450`.  `padMotive_liftN` is still
   the only entry proved.  Its prerequisite is **§0″.4's four-field `ProjClosedG`**, not the
   three-field one §0‴.4 named.  Block B (the swap) cannot start before block A.

### 0′.7 Files this round

Edited (all owned):

* `Lean4Lean/Verify/Typing/ProjGen.lean` — §0″.1, additively.  The four `_norec` lemmas'
  *proofs* changed (they are now corollaries); their **statements are untouched**.
* `Lean4Lean/Verify/Typing/ProjGenWitness.lean` — §0″.3, §0″.4.  Adds namespaces `MutRec` and
  `ProjClosedGap`; the `MutNonRec` half is untouched.
* `scripts/proj-rerun.lean`, `scripts/hole-cone.lean` — this round's names added to both
  instruments.

Unchanged: `Structure.lean`, `StructureClosed.lean`, `StructureEta.lean`,
`StructureExamples.lean`, `ProjSkip.lean`, `Lemmas.lean`, `StructureUniq.lean`,
`Rigidity.lean`, `ConstSpineWF.lean`, `DefEqCtx.lean`.  `TrProj`, `TrProj.wf`, `projCore`,
`IsStructure` are untouched for a **third** round; the generalisation is still additive by
design, and §0⁗.3 correction 4's polarity argument still stands — `IsStructureG` must stay
separate from `IsStructure`, because `IsStructure` sits in a **negative** position in
`VEnv.StructEta` and no non-vacuity check can detect an over-strong assumption.

Nothing here touches an implementation file, so the Kernel Arena is unaffected and was not
re-run.

### 0′.8 Relay to the orchestrator

Mid-round `Lean4Lean/Theory/Typing/ChurchRosser.lean` (another stream's, modified and
uncommitted) did not compile, which blocked `scripts/sorry-census.lean`,
`scripts/dup-names.lean` and the full `scripts/hole-cone.lean` — all three import it
transitively.  **Re-checked at the end of the round: green**, and all three then ran; their
numbers above are from the re-run.  Not touched.  (Recorded because the rule is *wait,
re-check, report, never fix*, and a "stream X is red" relay sent without the re-check would
have been wrong by the time it was read — the same thing happened last round with
`Verify/Primitive.lean`.)

Still modified/untracked by other streams at the end of the round: `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Theory/Typing/Enlarged.lean`,
`docs/handoff-injectivity.md`, and untracked `Theory/Typing/KMeasure.lean`,
`RetypeCase.lean`, `StrengthenAxiom.lean`.  Not touched.

Full owned closure green with all three guards printing ✓:

    lake build Lean4Lean.Verify.Typing.ProjGenWitness Lean4Lean.Verify.Typing.ConstSpineWF \
      Lean4Lean.Verify.Typing.Lemmas Lean4Lean.Verify.TypeChecker \
      Lean4Lean.Theory.Inductive.StructureExamples Lean4Lean.Verify.StructureBridge \
      Lean4Lean.Verify.Soundness Lean4Lean.Verify.Guard

**[checked]**

### 0′.9 What I would pick up first

1. **Item 3's prerequisite, built rather than stated** — the four-field `ProjClosedG` of
   §0″.4, *derived* from `IsStructureG` + `Ordered env` (the way `IsStructure.projClosed`
   derives the three-field one) rather than assumed, and immediately audited against its one
   real consumer: prove
   `ClosedTele ((D.minorBinders q C').map (·.instL lvls)) (D.np + D.nm + q)` from it.  If that
   proof does not go through, the predicate is still wrong, and finding that out costs one
   lemma rather than all of block A.  The environment-staging step (`VIndField.WF.pos` lives
   in `env₁`) is the part to look at first.
2. Then the rest of block A, then item 2 (`realMinor`), then the swap.

Do **not** pick up `TrProj.uniq` expecting `PatWF` to be the blocker (§0‴.6 discharged it),
and do not treat the const-application family as unconditional: its route passes through
`church_rosser`, which is under the live conditional refutation of §0‴.6 — measured again this
round, `not_crStatement_of_kstep`'s cone is `{forallE_inv_stratified}` and still does **not**
contain `NormalEq.descend`, so the refutation is not circular with the hole confluence waits
on.

---

## 0‴. Three rounds back: the residual is closed, and the padding minor is proved for non-recursive blocks

### 0″.1 Headline

`docs/handoff-projections.md` §0⁗.5's **one mathematical residual** — `padMinor_hasType`'s
`hbeta` premise, "identify `minorBody`'s head `.bvar` with `mots[t]` after `instAll`" — is
**closed**.  So is more than was asked: the padding minor's *whole* typing obligation is
proved outright for a **non-recursive** constructor at **any** member of the block.

Seventeen new declarations, all in `Lean4Lean/Verify/Typing/ProjGen.lean` and
`ProjGenWitness.lean` (both owned by this stream), every one with a **measured empty hole
cone** — transitive over type *and* value, `allowOpaque := true`, so the `.thmInfo` trap is
handled.  The instrument is committed as `scripts/hole-cone.lean`.  **[checked]**

| name | content |
|---|---|
| `VInductDecl'.minorBody_instAll_spine` | **the residual.**  `instAll (minorBody q t C).instL lvls) (ps ++ mots ++ acc) nΘ = (mots[t].liftN nΘ).mkApp (minorBodyArgs …)` |
| `VInductDecl'.minorBodyArgs`, `length_minorBodyArgs`, `length_minorBinders_map` | the spine `minorBody` hands the motive, named so the computations can quote it |
| `VInductDecl'.padMotive_liftN` | the padding motive commutes with a weakening of `ps` and `X` (the first entry of mechanical block A) |
| `padMotive_body_hasType` | the padding motive's *body*, typed under its own binders — split out of `padMotive_hasType`, which now uses it |
| **`padMotive_app_beta`** | the padding motive applied to a saturating spine **β-reduces to `X → X`**, as an `IsDefEq` at the elimination sort |
| **`padMinor_beta`** | `hbeta` itself, discharged: `minorBody_instAll_spine` + `padMotive_liftN` + `padMotive_app_beta` |
| **`padMinor_hasType'`** | `padMinor_hasType` with `hbeta` gone; only the constructor-spine premise `hbs` remains |
| `VInductDecl'.padMotives_getElem_eq`, `padMotives_getElem_ne` | the motive block really does hold the real motive at `j` and a `padMotive` elsewhere — this is what makes `padMinor_beta`'s `hget` satisfiable |
| `VInductDecl'.minorTele_norec`, `minorBodyArgs_norec` | at a non-recursive constructor, the minor's telescope **is** the field telescope and its motive spine **is** the pair of terms the existing chain already types |
| `ctorArgs_hasArgs_gen`, `ctorApp_hasType_gen` | `StructureClosed.lean`'s two constructor-spine lemmas at an **arbitrary block index** — the generalisation is the substitution of `H.types0`/`H.memCtor`/`H.memCtorsAll`/`H.typesD`, nothing else |
| `tyBinder_instAll` | the major-premise binder with the index spine substituted, which is what `HasArgs.concat` asks for |
| **`padMinor_hbs_norec`** | `hbs`, discharged for a non-recursive constructor |
| **`padMinor_hasType_norec`** | **the capstone**: the padding minor is well-typed, at a non-recursive constructor of any block member |
| `MutNonRec.minorBody_head_at_decl2`, `padMotives_at_decl2` | non-vacuity — §0‴.3 |

### 0″.2 How the residual was actually closed, and the one structural choice

The index arithmetic §0⁗.5 recorded was right and is now machine-checked:
`VExpr.instAll_bvar_get` fires with `t' := np + t`, because
`(nr+nf) + (np+nm+q) = (nr+nf+q+(nm-1-t)) + 1 + (np+t)` whenever `t < D.nm`.

The **structural choice** worth carrying forward: `padMotive_app_beta` is stated at an
**arbitrary ambient context**, with the padding motive's own data (`ps`, `X`) as parameters,
rather than at the minor's telescope with everything lifted.  The lifting is then paid once,
syntactically, by `padMotive_liftN`, and the semantic lemma never mentions the minor at all.
The first attempt threaded the lift through the typing and needed the whole of
`padMotive_hasType` re-derived over lifted data; this version needs none of it.

`VEnv.IsDefEq.betaMkLams` (`StructureClosed.lean`) is the tool, as §0⁗.5 predicted, and it
asks for the **body**'s typing — which is why `padMotive_body_hasType` had to be split out.
Note how few hypotheses that split-out lemma turned out to need: not the block index, not the
parameter spine, not the motive prefix.  **[checked]**

### 0″.3 Non-vacuity, and a **negative** control

`padMinor_hasType'` cannot yet be fired end to end (its `hspine` premise is the consumer's,
and `projCoreG_hasType` does not exist).  What *is* fired, at `MutNonRec.decl2` — the same
two-type non-recursive block the refutation uses:

* `MutNonRec.padMotives_at_decl2` — the block holds the **real** motive at `j = 0` and a
  **`padMotive`** at index 1.  So `padMinor_beta`'s `hget` is satisfiable, at the padding
  entry, at a block Lean's own kernel accepts `.proj` on.  **[checked]**
* `MutNonRec.minorBody_head_at_decl2` — minor 0 reads motive `m0`; minor 1, with one more
  accumulator entry below it, reads `m1`.  Two different `(q, t)` pairs, distinct motives.
  **[checked]**
* **The negative control, and it is the point of the previous item.**  The same statement
  with minor 1 reading `m0` is *rejected* — `rfl` fails on `[m0, m1][1]? = some m0`.  Run
  outside the tree, output reproduced:

      error: Application type mismatch: The argument `rfl` has type `?m = ?m`
      but is expected to have type `[m0, m1][1]? = some m0`

  An off-by-one in the head index would not have been caught by **any** arity check in this
  cluster: the spine has the right *length* either way.  **[checked]**

`decl2`'s types have no fields and no indices, so what these exercise is exactly the
`q + (nm - 1 - t)` half of the index — the half that is new.  The `nf`/`nr` half is exercised
instead by `padMinor_hasType_norec`'s own statement being about arbitrary `C'`.

### 0″.4 What is left of the generalisation, exactly

Three items, none of them the residual any more.

1. **The padding minor at a *recursive* constructor.**  `minorTele_norec`,
   `minorBodyArgs_norec` and `padMinor_hbs_norec` all carry `hrec : C'.recFields = []`.  What
   `recFields ≠ []` changes is one thing: the `nr` induction-hypothesis binders sit between
   the fields and the body, so `minorBinders = liftTele (nm+q) (atRecTele fields) ++ ihTypes`
   no longer collapses to the field telescope, and the constructor's spine has to be weakened
   past them.  The exact steps, **[read off source]**, not run:
   * the values: `shift (nm+q) nr nf (atRec a)` is `((atRec a).liftN (nm+q) nf).liftN nr 0`,
     and `VExpr.liftN_instAll` (`TelescopeLift.lean:324`) moves the outer `liftN nr` across
     the `instAll` at cut `nr + nf`, leaving `minorBodyArgs_norec`'s term lifted by `nr`;
   * the context: `HasArgs.weak'`/`weakR` (`StructureClosed.lean:109`, `:1045`) move
     `ctorArgs_hasArgs_gen`/`ctorApp_hasType_gen` from `fields.reverse ++ Γ` to
     `ihs.reverse ++ fields.reverse ++ Γ`;
   * `ihTypes` itself needs no typing here — the padding minor binds the ihs and ignores
     them.  **This is the half that lifts the `noRec` narrowing**, so it is not optional.
2. **The real minor at index `j`.**  `realMinor` (bind fields *and* ihs, return field `i`) has
   **no typing lemma at all** yet.  `projMinor_app` (`StructureClosed.lean:826`) is the
   `nr = 0` ancestor.  Not started, not costed.
3. **Mechanical block A**, the `lift'`/`instN`/`instL` commutation for `projCoreG` —
   `projCoreG_lift'`, `projCoreG_instN`, `projCoreG_instL` and the `projArgsG`/`projTermG`
   versions, mirroring `Theory/Inductive/Structure.lean:296–450`.  `padMotive_liftN` is the
   first entry and is proved; the rest is not started.  These are what `TrProj.mono`,
   `TrProj.instL` and `TrProj.weak'` run on, so **block B (the swap) cannot start before
   they land**.  A `ProjClosed` generalised to every block member (`ClosedTele` for *each*
   `T'.indices` and each `C'.fields`, not just the projected pair) is their first
   prerequisite; `padMotive_liftN` already takes that `ClosedTele` as an explicit premise, so
   the shape is known.

**Block B (the swap) is unchanged from §0⁗.5 and was not attempted.**  It needs
`projCoreG_hasType`, which needs items 1–3 above plus the generalised `recApp_hasType''`
plumbing.  Nothing this round makes it closer than one full item at a time.

### 0″.5 `TrProj.wf` and the refutation, re-run — **[checked]**

Reproduced from `scripts/proj-rerun.lean` (committed; `#print axioms` on every standing check
of the cluster, so a check that stopped existing or acquired `sorryAx` shows up there rather
than in a build log):

    VEnv.empty_structEta                     [propext, Quot.sound]
    bazEnv_structEta                         [propext, Classical.choice, Quot.sound]
    bazEnv_etaExpansion_eq                   [propext]
    bazEnv_projMinors_distinct               [propext]
    bazEnv_structEta_premises                [propext, Classical.choice, Quot.sound]
    MutNonRec.kernelProjChecks               [propext, Classical.choice, Quot.sound]
    MutNonRec.projCore_arity_wrong           [propext]
    MutNonRec.projCoreG_arity_right          [propext, Quot.sound]
    MutNonRec.projCoreG_arity_right'         [propext, Quot.sound]
    VInductDecl'.projTermG_eq_projTerm       [propext, Quot.sound]
    VInductDecl'.recArity_eq_projCoreG       [propext, Quot.sound]
    VInductDecl'.projCoreG_eq_projCore       [propext, Quot.sound]
    TrProj.wf                                [propext, sorryAx, Classical.choice, Quot.sound]
    tryEtaStructCore.WF_of_structEta         [propext, sorryAx, …]
    isDefEqUnitLike.WF_of_structEta          [propext, sorryAx, …]

`TrProj.wf`'s measured hole cone is **`{weakN_iff, forallE_inv_stratified}` — exactly what it
was**, so the round is additive at the cone level too, not merely at the file level.
**[checked]**

**A correction to the previous edition's list.**  The five `rfl` validations of
`etaExpansion` against Lean's own elaborator (`Prod`, `Sigma`, `And`, `Subtype`) and the F17
clause at `And` are **anonymous `example`s** in `Theory/Inductive/StructureExamples.lean`.
They have no names, so they cannot be `#print axioms`'d, and any handoff that lists them
beside named theorems invites someone to look for names that do not exist.  Their instrument
is that the module elaborates:

    lake build Lean4Lean.Theory.Inductive.StructureExamples

which it does.  `scripts/proj-rerun.lean` says so in a comment rather than pretending
otherwise.  **[checked]**

### 0″.6 The `PatWF` re-measurement — and the caveat the brief did not have

**Asked:** `VEnv.patWF` now holds at an arbitrary `VEnv.WF` environment from `VEnv.PiInv`;
land the resulting unconditional (A)/(B)/(D) in `Verify/Typing/`, and report the cone.

**Landed**, `Lean4Lean/Verify/Typing/ConstSpineWF.lean` (new, owned): `VEnv.patWF_of_wf`,
`constApp_inv_of_wf`, `const_app_inv_of_wf`, `const_forallE_inv_of_wf`, `const_sort_inv_of_wf`,
`constNoConf_of_wf`, plus two non-vacuity firings at `propLoopEnv2` with **no** `PatWF`
argument anywhere.  `VEnv.piInv_axiom` supplies `PiInv` from the **existing** census hole
`IsDefEqU.forallE_inv`, so nothing new is consumed.

**The cone, measured both ways — the answer to the question as asked:**

    VEnv.const_app_inv_of_patWF   weakN_iff, forallE_inv_stratified, NormalEq.descend, forallE_inv
    VEnv.const_app_inv_of_wf      weakN_iff, forallE_inv_stratified, NormalEq.descend, forallE_inv
    VEnv.constNoConf_of_wf        (the same four)
    VEnv.patWF_of_wf              forallE_inv_stratified, forallE_inv

**Discharging `PatWF` adds nothing to the cone.**  What it buys is that `PatWF` stops being a
*carried hypothesis*: `TrProj.uniq`'s obligations (2) and (3) were blocked on producing one
(§0⁗.6 said consuming it "requires a new `sorry` or axiom, both forbidden"), and that is no
longer true.  **[checked]**

**The caveat, and it is the most important thing in this document.**  Commit `967e4ba` landed
`VEnv.not_crStatement_of_kstep` (`Theory/Typing/KCanonical.lean`), which refutes
**`VEnv.IsDefEq.church_rosser`'s statement** at any `Params` instance registering the ι-rule
of a large-eliminating subsingleton.  *Every* result in the (A)/(B)/(D) family routes through
`church_rosser`, and `VEnv.paramsOfPiInv` at an arbitrary `VEnv.WF` environment is such an
instance whenever the environment declares `Eq`.  Three registers, kept apart:

* **[checked]** `not_crStatement_of_kstep`'s own hole cone is `forallE_inv_stratified`
  **alone** — it does *not* contain `NormalEq.descend`.  So the refutation is **not circular**
  with the hole `church_rosser` is waiting on.
* **[read off source]** no `Params` instance discharging that refutation's hypotheses is built
  in this tree.  `Theory/Typing/PatWFIota.lean`'s own note says a full ι witness is *not*
  constructed.  What exists is a **conditional** refutation, not a counterexample.  Note this
  cuts both ways: *"no witness" is not evidence of truth* either.
* **[analysis]** if such an instance is built, `NormalEq.descend` is false — it is the only
  hole in `church_rosser`'s cone that is not plainly Π-injectivity — and (A), (B), (D) and
  `constRigid_of_weakNorm` all have to be re-derived by another route.  The *statements* are
  not thereby refuted; the *proof* is.

So the honest reading of "landed it": the hypothesis is gone, the cone is unchanged, and the
route the cone runs through is now under a live conditional refutation.  This is recorded in
`ConstSpineWF.lean`'s module docstring so nobody reads the file as an unqualified win.

**Assessed as instructed and unchanged:** `InferTypeS.weakU_inv` still touches neither of
`TrProj.weak'_inv`'s two blockers — §0⁗.6's assessment stands, and the identification is still
(C) and the level reconciliation still (B).  Not taken.

### 0″.7 A defect found and fixed, in a file this stream owns

**`Verify/Typing/Rigidity.lean` and `Verify/Environment/Basic.lean` each declared
`VEnv.addDefEqList_defeqs_inv` and `VEnv.addIndRules_defeqs_inv`, so the two modules could
never be imported together.**  This is not a build error — nothing imported both — and no
check in this tree would ever have found it.  It surfaced only because a cone-measurement
script needed both:

    error: import Lean4Lean.Verify.Typing.Rigidity failed, environment already contains
    'Lean4Lean.VEnv.addDefEqList_defeqs_inv' from Lean4Lean.Verify.Environment.Basic

Fixed by priming the two in `Rigidity.lean` (the later, local re-derivation — the disjuncts
are in the other order, so they are not literally the same lemma) and recording why at the
docstring.  Nothing else changed; `Rigidity.lean` builds.  **[checked]**

Worth generalising: *a duplicate top-level name between two modules is invisible to
`lake build`.*  If the orchestrator wants a cheap structural check, it is one pass over the
`.olean`s comparing declared names.

### 0″.8 Relay to the orchestrator: other streams' in-flight files

Mid-round, `Lean4Lean/Verify/Primitive.lean` (modified, uncommitted, another stream's) did not
parse:

    error: Lean4Lean/Verify/Primitive.lean:676:11: unexpected token '/--'; expected …

**Re-checked at the end of the round and it is green** — that stream fixed it while this one
was running.  Recorded because the rule is *wait, re-check, report, never fix*, and the
re-check is the half that is usually skipped; a "stream X is red" relay sent without it would
have been wrong by the time it was read.

`Lean4Lean/Primitive.lean` and `Lean4Lean/Verify/Primitive.lean` remain modified and
uncommitted, and `Theory/Typing/Enlarged.lean`, `EnlargedModel.lean`, `KEta.lean` are
untracked — all other streams' in-flight work.  Not touched.

The whole of this stream's dependency closure is green, with all three guards printing ✓:

    lake build Lean4Lean.Verify.Typing.ProjGenWitness Lean4Lean.Verify.Typing.ConstSpineWF \
      Lean4Lean.Verify.Typing.Lemmas Lean4Lean.Verify.TypeChecker \
      Lean4Lean.Theory.Inductive.StructureExamples Lean4Lean.Verify.StructureBridge \
      Lean4Lean.Verify.Soundness Lean4Lean.Verify.Guard

**[checked]**  Nothing this round touches any implementation file, so the Kernel Arena is
unaffected and was not re-run.

### 0″.9 Files this round

New (both owned):

* `Lean4Lean/Verify/Typing/ConstSpineWF.lean` — §0‴.6.  Imports `Theory/Typing/PatWFIota` and
  `Verify/Typing/Rigidity`.  Nothing imports it.
* `scripts/hole-cone.lean`, `scripts/proj-rerun.lean` — the two instruments this round's
  numbers come from.  Deliberately outside any `lean_lib` glob, like `scripts/cone-measure.lean`.

Edited (all owned):

* `Lean4Lean/Verify/Typing/ProjGen.lean` — §0‴.1, additively; `padMotive_hasType` is the one
  pre-existing declaration whose *proof* changed (it now calls `padMotive_body_hasType`), and
  its statement is untouched.
* `Lean4Lean/Verify/Typing/ProjGenWitness.lean` — §0‴.3.
* `Lean4Lean/Verify/Typing/Rigidity.lean` — §0‴.7, two renames and a docstring.  No proof
  changed.

Unchanged: `Structure.lean`, `StructureClosed.lean`, `StructureEta.lean`,
`StructureExamples.lean`, `ProjSkip.lean`, `Lemmas.lean`, `StructureUniq.lean`, `Expr.lean`,
`ConstSpine.lean`.  `TrProj`, `TrProj.wf`, `projCore`, `IsStructure` are all untouched for a
second round; the generalisation is still additive by design (§0⁗.3 correction 4 — and the
polarity argument there still stands: `IsStructureG` must stay separate from `IsStructure`,
because `IsStructure` sits in a **negative** position in `VEnv.StructEta` and no non-vacuity
check can detect an over-strong assumption).

### 0″.10 What I would pick up first

1. **Item 1 of §0‴.4** — the padding minor at a recursive constructor.  Every step is named
   above with the lemma that does it, and it is the half that lifts `noRec`.
2. **Item 3** — block A, starting with `ProjClosed` generalised to every block member, since
   block B cannot start without it.
3. Only then item 2 and the swap.

Do **not** pick up `TrProj.uniq` expecting `PatWF` to still be the blocker: it is discharged
(§0‴.6).  What is left there is ledger G4 / `RecTypeResidual` (still with no statement in the
tree) and a `projTerm` congruence — plus the standing question of whether the whole
constant-application family survives the Church–Rosser refutation.

---

## 0⁗. Four rounds back: `projCore` generalised, and four corrections

### 0‴.1 What landed — `Lean4Lean/Verify/Typing/ProjGen.lean` (new, owned)

The repair `docs/handoff-eta.md` §3 specified — pad the motive and minor blocks so the
projection's spine saturates the recursor at *every* block, not only singleton ones — is now
**built and machine-checked at the definitional and motive-typing layers**, additively:
`projCore`, `IsStructure`, `TrProj` and `TrProj.wf` are untouched, so nothing went red.

Every declaration listed below has an **empty hole cone** (measured: transitive
`getUsedConstantsAsSet` with the `.thmInfo`/`allowOpaque` trap handled; `sorryAx` absent from
all twelve).  **[checked]**

| name | content |
|---|---|
| `VInductDecl'.padMotive`, `padMotives` | the motive block: the real motive at index `j`, `fun ι_k x_k => X → X` elsewhere |
| `VInductDecl'.minorBinders`, `minorBody`, `minorType_eq_mkPi` | `minorType` split into its binder telescope and its body, by `rfl` |
| `VInductDecl'.padMinor`, `realMinor`, `padMinorsAux`, `padMinors` | the minor block; `realMinor` binds the **induction hypotheses** as well as the fields, which is what lifts the `noRec` narrowing |
| `VInductDecl'.projCoreG`, `projArgsG`, `projTermG` | the generalised projection term.  `projArgsG` is still **structural in `i`** — both recursive calls at `i` — so it reduces by `rfl`, the property `projArgs`' docstring warns must be preserved |
| `length_padMotives`, `length_padMinors`, `length_projCoreG_spine`, **`recArity_eq_projCoreG`** | the arity identity — §0⁗.2 |
| `minorTele_narrow`, `padMotives_narrow`, `padMinors_narrow`, **`projCoreG_eq_projCore`**, `projArgsG_eq_projArgs`, **`projTermG_eq_projTerm`** | at a block with one type, one constructor and no recursive fields — exactly `IsStructure`'s hypotheses — the generalised term **is** the old one.  So this is a generalisation, not a substitution, and every `rfl` validation of `projTerm` against Lean's own elaborator carries over |
| `motiveType_instL_instAll_gen`, `motiveG_declType_isType`, `padMotiveCtx_wf`, **`padMotive_hasType`** | the padding motive is well-typed at the recursor's motive binder — §0⁗.4 |
| `padMotive_body_instAll` | the padding motive's β-normal form: applied to any spine of the right length it collapses to `X → X` |
| **`padMinor_hasType`** | the padding minor inhabits its declared type, **modulo one named premise** — §0⁗.5 |
| `VEnv.IsStructureG`, `.mono`, `.lt_nm`, `VEnv.IsStructure.toG` | the widened shape predicate (`types : D.types[j]? = some T`, no `noRec`) and the narrow one embedded in it at `j = 0` |
| `VIndCtor.fieldUsed_index_irrel` (+ `VExpr.skips'_mkApp`, `skips'_mkPi_congr`) | §0⁗.3, correction 3 |

`Lean4Lean/Verify/Typing/ProjGenWitness.lean` (new, owned) holds §0⁗.2.

### 0‴.2 The refutation, re-run and killed at its own witness  **[checked]**

`MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) refutes weakening
`IsStructure.types` by measuring, at `MutNonRec.decl2` (a two-type non-recursive block —
the abstract image of a block Lean's **kernel** accepts `.proj` on and performs structure eta
at, `MutNonRec.kernelProjChecks`):

* `projCore`'s spine: **3** entries; `decl2.recArity = 5`; `¬ decl2.nm + decl2.nmin = 2`.

`MutNonRec.projCoreG_arity_right` and `projCoreG_arity_right'` fire the same measurement on
`projCoreG` **at `decl2` itself**:

* motive block **2**, minor block **2**, spine **5**, `recArity` **5** — and
  `recArity_eq_projCoreG` is *unconditional*, so the `nm + nmin = 2` side condition that
  `recArity_eq_projCore_iff` makes everything turn on is not merely satisfied, it is gone.
  `projCoreG_arity_right'` states the identity and `¬ decl2.nm + decl2.nmin = 2` **together**,
  so the witness that refutes the weakening is visibly inert against the generalisation.

`TrProj.wf` is untouched and still **proved** — the generalisation is additive, so nothing
could have made it false; `projTermG_eq_projTerm` is what will let the swap be made without
re-proving it from scratch.

### 0‴.3 Four corrections to the brief and to `handoff-eta.md` §3

1. **The prescribed `Sort ℓ` witness is not the cheapest, and the cheaper one deletes an
   ingredient.**  §3 (and this round's brief) specify the padding motive's body as
   `Xᵢ → Xᵢ` with `Xᵢ := instAll (A_i.instL us) (ps ++ [proj 0 e, …, proj (i-1) e])` — the
   projected field's type at projections of the **ambient** `e`, which is a *second*
   projection list beside the one `projArgs` builds at the motive's own binder.  Not needed:
   **`X := mot.mkApp (ιs ++ [e])`**, the real motive applied to the index spine and the major
   premise, is the same type up to β, is built from data `projCore` already has, and is
   *already typed by the existing chain* — it is exactly the term `projCore_hasType`'s
   `hconv` premise is about.  `projCoreG` uses it.  **[checked]** — and see correction 2 for
   what that buys.
2. **The padding motive needs no F17 clause.**  `padMotive_hasType` takes `X` at the
   **elimination** level (`D.elimLvl.inst (D.projLvls C us i)`) and closes with
   `VLevel.imax_self`.  The two-branch `isLE` / F17 argument is paid *once*, where `X` itself
   is typed (`projMotiveBody_hasType`, already proved), and not again per padding entry.  The
   brief's "a dummy motive must land in `Sort ℓ` at the **field's** level" is right about the
   level and misleading about where the cost sits.  **[checked]**
3. **`TrProj`'s F17 clause hard-codes the type index `0` (`C.FieldUsed D 0 k`), and that is
   safe.**  This looked like the classic "statement about the wrong thing" once `T` may sit
   at index `j ≠ 0`.  It is not: `VIndCtor.fieldUsed_index_irrel` proves
   `C.FieldUsed D j k ↔ C.FieldUsed D j' k` — `FieldUsed` reads only the de Bruijn structure
   of `C.canonResult D j`, and `j` changes only the head constant's *name*, which
   `VExpr.Skips'` ignores.  So that clause transports verbatim.  **[checked]**
4. **Widening `IsStructure` *in place* would silently strengthen `VEnv.StructEta`, and that
   is why `IsStructureG` is a separate predicate.**  `IsStructure` occurs in a **negative**
   position in `VEnv.StructEta`'s definition (`Theory/Inductive/StructureEta.lean:139`,
   `env.IsStructure S D T C →`).  Dropping `noRec` there does not weaken an obligation — it
   *extends the eta rule* to recursive one-constructor inductives, which is precisely the case
   Lean's own eta gate excludes (`is_structure_like` tests `isRec`; recorded at
   `IsStructure.noRec`'s docstring, machine-checked by `MutNonRec.kernelProjChecks`).  Note
   that **the existing non-vacuity witnesses would not have caught this**: `empty_structEta`
   and `bazEnv_structEta_premises` still pass under a strengthened `StructEta`; a vacuity
   check does not detect an over-strong assumption.  So: `noRec` may be dropped for the
   **projection** path (`TrProj`) and must be kept for the **eta** path.  The brief's "widen
   `IsStructure` … `types` *and* `noRec`" is one predicate too few.  **[read off source]** —
   the negative position is a reading of the definition, not a check.

   Related, and smaller: an in-place widening also breaks exactly one *unowned* declaration,
   `fooEnv_IsStructure` (`Theory/Inductive/DeclExamples.lean:1363`), which builds an
   `IsStructure` with a `where` block including `noRec := rfl`.  Every other construction site
   (`ProjLevelWitness`, `StructureUniq`, `StructureEta`) is owned by this stream, and every
   *consumer* of `H.noRec` (`StructureUniq.lean:182,611–613`; `Lemmas.lean:1013,1087,1124`) is
   too.  `Verify/TypeChecker/IsDefEq.lean` and `Verify/StructureBridge.lean` mention
   `IsStructure` only in hypothesis position and never read `noRec`.  **[read off source]**,
   name-based scan for `.noRec` plus every anonymous/`where` construction.

   Also corrected, in this stream's favour: `Theory/Inductive/StructureEta.lean` uses
   `hS.types` (line 353) only to get `T ∈ D.types`, which the widened form still supplies.
   An earlier version of this note claimed the eta chain reads `noRec`; it does not.

### 0‴.4 The cost estimate in `handoff-eta.md` §3 was too pessimistic at the typing layer

§3 priced the repair as "`StructureClosed.lean` (1657 lines) re-derives every
`lift'`/`instN`/`instL` commutation over the new shape" plus the `ProjSkip`/`Lemmas` typing
chain gaining `nm - 1` motive and `nmin - 1` minor obligations.  Measured this round:

* **The recursor-application plumbing is already fully general.**
  `VInductDecl'.recApp_hasType''` (`Theory/Inductive/RecApp.lean`) takes `ms`/`mins` blocks of
  arbitrary length at an arbitrary type index; `VInductDecl'.motiveType_isType` and
  `minorType_isType` (`Theory/Inductive/Lemmas.lean`) are general in the motive/minor index
  *and* in the context prefix.  What is specialised to index `0` is only the thin layer in
  `StructureClosed.lean` (`motiveType_instL_instAll`, `motive_declType_isType`,
  `minorType_instL_instAll`, `minor_declType_isType`, `motiveCtx_wf`, `motives_eq`,
  `minors_eq`, `idxTele_collapse`).  Two of those are now generalised in `ProjGen.lean`
  (`motiveType_instL_instAll_gen`, `motiveG_declType_isType`) at ~60 lines each.  **[checked]**
* **`minorType_instL_instAll` need not be generalised at all for the minor telescope.**
  `padMinor` *defines* its telescope as the instantiation of `minorType`'s own binder block,
  so `instAll_mkPi` splits the declared type into exactly that telescope and a body, and
  `IsType.mkPi_inv` supplies the context — no computation of the `ihTypes` block is required.
  This is the step §3 priced highest and it is not on the critical path.  **[checked]**
* **The syntactic commutation lemmas *do* still have to be re-derived** over the padded shape
  (`projCoreG_lift'`, `projCoreG_instN`, `projCoreG_instL`, and the `projArgsG`/`projTermG`
  versions).  Not started.  These are what `TrProj.mono`/`TrProj.instL`/`TrProj.weak'` run on.

### 0‴.5 What is left of the generalisation, exactly

**One mathematical residual, and two mechanical blocks.**

* **Residual (the only one).**  `padMinor_hasType`'s `hbeta` premise: the declared body of
  minor `q` — `minorBody q t C'`, the motive of the constructor's *own* type applied to the
  result indices and to the constructor — is definitionally `X → X` once that motive is a
  padding motive.  `padMotive_body_instAll` (proved) is the collapse itself; what is missing
  is the step identifying the head `.bvar` of `minorBody` with the `t`-th entry of the motive
  block after `instAll`, and then `VEnv.IsDefEq.betaMkLams` (proved, in `StructureClosed`).
  The index arithmetic is settled and recorded here so it need not be redone: in the spine
  `ps ++ mots ++ mins<q` of length `np + nm + q`, under the `nr + nf` binders of the minor,
  `minorBody`'s head `.bvar (nr+nf+q+(nm-1-t))` resolves to spine element
  `np + nm + q - 1 - (q + nm - 1 - t) = np + t`, i.e. `mots[t]`; and `ihTypes`' heads resolve
  the same way to `mots[r.idx]`.  **Consequence, and it is what makes the accumulator in
  `padMinorsAux` avoidable in the proofs: neither `minorType`'s telescope nor its body ever
  refers to the `mins<q` block.**  **[read off source]** — an index computation over
  `minorType`/`ihType`, not checked.
* **Mechanical block A.**  The `lift'`/`instN`/`instL` commutation lemmas for `projCoreG`
  (§0⁗.4, third bullet).
* **Mechanical block B.**  The swap itself: `TrProj` re-stated over `IsStructureG` and
  `projTermG`, `TrProj.wf` re-proved via `projCoreG_hasType` (the generalisation of
  `projCore_hasType`, whose `[mot]`/`[minor]` `HasArgs` steps become `HasArgs` over the two
  blocks — `recApp_hasType''` already accepts them), and the *narrow* `TrProj` kept or derived
  from the wide one so that `Verify/TypeChecker/IsDefEq.lean` and
  `Theory/Inductive/DeclExamples.lean` do not go red.  `projTermG_eq_projTerm` is the bridge.

### 0‴.6 Task 2 (`TrProj.uniq`, `TrProj.weak'_inv`) is *structurally* blocked, not effort-blocked

This is a correction to the brief's sequencing, not a report of difficulty.  Both lemmas need
facts that are **not census holes** and therefore cannot be consumed without adding a `sorry`
(forbidden) or an axiom (forbidden):

* `VEnv.PatWF` (`Theory/Typing/ParamsBuild.lean`) — a `def … : Prop`, **open**.  Proved only on
  the δ fragment.  Needed for fact (B) (`const_app_inv_of_patWF`) and fact (D)
  (`constNoConf_of_patWF`), i.e. for two of `TrProj.uniq`'s four obligations and for
  `weak'_inv`'s level half.
* `VEnv.WeakNorm` (`Verify/Typing/ConstSpine.lean`) — stated, **no route in the tree**.  Needed
  for (C) rigidity, `weak'_inv`'s other half.
* ledger **G4** / `RecTypeResidual` — has no statement in the tree; `TrProj.uniq`'s obligation (1).
* a `projTerm` congruence — `TrProj.uniq`'s obligation (4); mechanical, still uncosted.

Consuming an *existing* census hole (say `IsDefEqU.forallE_inv`) is permissible and would leave
the census at 19 while making a new declaration `sorry`-free; consuming `PatWF` or `WeakNorm` is
not, because they are hypotheses rather than holes.  So neither lemma could close this session
regardless of effort, and the brief's "then close what it unblocks" does not follow — **the
`projCore` generalisation unblocks neither**, and it was never claimed to (`handoff-eta.md` §3,
"What it is not").

**`InferTypeS.weakU_inv`, assessed as instructed.**  `Theory/Typing/HeadReduction.lean:691`,
`(W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') : ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A`.  It does
replace steps 1 and 3 of the traced route (`HasType.skips` at `Ctx.LiftN`, which would first
need a `Ctx.Lift'` version, plus `IsDefEqU.weakN_iff`) with one already-proved lemma, and so
**removes `weakN_iff` — a census hole — from `weak'_inv`'s cone**, at the price of the `Params`
gate.  But what it hands back is an *inferred, weak-head-normal* type `A` living in `Γ` with
`A.lift' ρ` convertible to `(.const S us).mkApp (ps ++ ιs)`; concluding that `A` **is** a spine
with head `S` is still exactly (C) rigidity, and reconciling the recovered `us'` with `us` is
still (B).  **So it touches neither blocker.**  Worth taking when (C) lands; not a way in now.
**[read off source]**, not machine-checked.

### 0‴.7 Relay to the orchestrator

`Theory/Typing/PatWFIota.lean` and `Theory/Typing/KCanonical.lean` are **uncommitted, untracked,
and belong to another stream**, and `Theory/Typing/PatternRules.lean` is modified by it.
`PatWFIota.lean` was **red** during this round's full build (unknown constant
`Lean4Lean.VLevel.IsEquiv.symm`; "No goals to be solved"; a failed `rewrite` — lines 501, 502,
605).  Reported, not touched.  That stream is attacking `PatWF`'s ι case, which is **the single
highest-leverage unblock for `TrProj.uniq`** (§0⁗.6): it would make (B) and (D) unconditional.

---

## 1. Pick this up first (previous edition — **superseded by §0″.10**)

> **Superseded.**  Item 1 below — "`VEnv.PatWF` … the single hypothesis standing between this
> tree and (A), (B) and (D) unconditionally" — is **done**: §0″.6.  Read §0″.10 instead.  The
> rest of this section is kept because items 2 and 3 are unchanged.


*Note on numbering.*  Sections 2–8 are the previous edition, renumbered by one; `§n`
cross-references **inside** them are to that edition's numbering (`§2` there is `§3` here,
and so on).  `§0″.x` always means this round.

1. **`VEnv.PatWF`** (`Theory/Typing/ParamsBuild.lean`).  It is now the single hypothesis
   standing between this tree and (A), (B) and (D) *unconditionally*.  It is one field of
   `VEnv.Params`; `VEnv.paramsOfWF` derives the other nine from `VEnv.WF`.  It is proved
   outright on the δ fragment (`patWF_of_deltaFragment`); the ι and quotient cases need
   `IsDefEqU.forallE_inv`, which is an **existing census hole**, not a new one.  Discharging
   `PatWF` closes `quotReduceRec.WF`'s mathematical content and two of `TrProj.uniq`'s four
   obligations at once.  This is the highest-leverage single item in the cluster.
2. **`RecTypeResidual`** (§3.4 of the previous edition, unchanged) — ledger G4's remainder.
3. **Weak-head normalisation** (`VEnv.WeakNorm`, `Verify/Typing/ConstSpine.lean`) — (C)'s
   only residual, and `TrProj.weak'_inv`'s last mathematical one.

---

## 2. Status of the four

| | status | blocked on |
|---|---|---|
| `TrProj.wf` | **PROVED** (previous edition) | — (cone: `IsDefEqU.weakN_iff`, `forallE_inv_stratified`) |
| `TrProj.weak'_inv` | open | (C) ⇐ `WeakNorm`; (B) ⇐ ~~`PatWF`~~ (discharged, §0″.6); `IsDefEqU.weak'_iff` |
| `TrProj.uniq` | open | ~~`PatWF`~~ (discharged, §0″.6); `RecTypeResidual`; a `projTerm` congruence |
| `inferProj.WF` | open **by deliberate choice** | see the previous edition §6; unchanged |

---

## 3. What landed the *previous* round: `Verify/Typing/ConstSpine.lean` (707 lines)

### 2.1 The correction that unlocked it

`Theory/Typing/Injectivity.lean` attaches the same residual to all six of its statements: the
**`trans`** case of an induction on `IsDefEqStrong` — "a term convertible with a rule-free
constant application reduces to one".  Last round's note that `const_app_inv` had been
"reduced to `trans` as its only residual" was correct about that induction.

**But the `trans` case is an artefact of the induction, not of the statements.**
`VEnv.NormalEq` (`Theory/Typing/ChurchRosser.lean`) has **no `trans` constructor** —
transitivity there is `NormalEq.trans`, a *theorem*, and `VEnv.IsDefEq.church_rosser` has
already paid for it.  An argument routed through Church–Rosser never meets that case.

Machine-checked, all in `Verify/Typing/ConstSpine.lean`:

| name | content |
|---|---|
| `VEnv.ParRed.constApp_inv`, `.ParRedS.constApp_inv` | a parallel reduct of `(const c ls).mkApp as` is `(const c ls).mkApp as'` with `as ≫ as'` pointwise.  `beta` is impossible (the spine head is not a λ), `extra` is impossible under `PatFreeHead` |
| `VEnv.NormalEq.constApp_inv` | `NormalEq` between two constant spines is head-, level- and argument-wise.  Only `refl`, `constDF`, `appDF` are reachable; `proofIrrel` is blocked by `¬IsProof` threaded down the spine by `IsProof.app'`; `etaL`/`etaR` by shape |
| `VEnv.IsDefEq.constApp_inv` | the two joined by `church_rosser`.  **(B) and (D) in one statement** |
| `VEnv.NormalEq.constApp_forallE`, `.constApp_sort`, `IsDefEqU.constApp_forallE_false`, `.constApp_sort_false` | **(A)**, by the same route and more cheaply — with the right-hand side a Π or a sort, `proofIrrel` is `NormalEq`'s only live constructor, and the right-hand side's being a type refutes it |

### 2.2 The `VEnv`-level results, and the anti-strawman checks

`VEnv.paramsOfWF` turns each of these into a statement about an arbitrary well-formed
environment, conditional on `VEnv.PatWF`:

* `VEnv.const_forallE_inv_of_patWF`, `VEnv.const_sort_inv_of_patWF` — **(A)**
* `VEnv.const_app_inv_of_patWF` — **(B)**
* `VEnv.constApp_inv_of_patWF` — (B) and (D) together
* `VEnv.constNoConf_of_patWF` (`Verify/Typing/Rigidity.lean`) — **(D)**, as the stated
  `VEnv.ConstNoConf`, so it is its own anti-strawman check

For (A) and (B) the anti-strawman check is explicit and in the house style of
`Theory/Typing/HeadRedStuck.lean`: `ConstAppInvStmt`, `ConstForallEInvStmt`,
`ConstSortInvStmt` are the three `Injectivity.lean` theorems' types with every binder made
explicit and nothing else changed; `…_holds` proves each **by** that theorem (deliberately
`sorryAx`-tainted) and `…_of_patWF` proves the same `Prop` from `PatWF`.  The two sit side by
side, so no statement can have been narrowed unnoticed.

### 2.3 The measured cone — this is the point

Machine-measured (forward reachability from the declaration, `sorryAx`-containing
declarations only):

```
Lean4Lean.VEnv.constApp_inv_of_patWF        -- (B)+(D)
Lean4Lean.VEnv.const_forallE_inv_of_patWF   -- (A), Π half
Lean4Lean.VEnv.const_sort_inv_of_patWF      -- (A), sort half
    IsDefEqU.weakN_iff
    IsDefEqU.forallE_inv_stratified
    NormalEq.descend
    IsDefEqU.forallE_inv
```

Four existing census holes, **none of them a constant-application fact**.  In particular
`const_app_inv`, `const_forallE_inv`, `const_sort_inv` and `sort_forallE_inv` are *not* in the
cone, so this is not circular.

**Consequence for the ledger.**  The constant-application family is not an independent
obligation.  It is downstream of the sort/Π family, of `NormalEq.descend`, and of `PatWF`.

### 2.4 A second correction: (B)'s side condition is not the one that blocks the step

`RuleFreeHead` is a fact about `env.defeqs`.  The reduction step it has to block is
`WHRed.extra` / `ParRed.extra`, which fires on a `Params.Pat`-registered pattern.  The
`Params` class relates `Pat` and `defeqs` in **one direction only** (`extra_pat`: every rule
is a registered pattern under leading λs); nothing forbids an instance whose `Pat` registers a
pattern headed by a `RuleFreeHead` constant.

So `VEnv.PatFreeHead` is the honest condition, and:

* `Lean4Lean.Pat.headConst_defeqs` (machine-checked) — every pattern the **canonical** table
  `Lean4Lean.Pat env` registers has the head constant of a rule's left-hand side, in all three
  constructors (δ, ι, quot);
* `VEnv.RuleFreeHead.patFreeHead` (machine-checked) — hence `RuleFreeHead → PatFreeHead` at
  `paramsOfWF`'s instance, which is the only one any consumer meets.

This matters for `VEnv.ConstRigid` as it was stated in `Verify/Typing/Rigidity.lean`: it is
`[Params]`-gated and carries `RuleFreeHead`, so **as stated it is under-hypothesised** — the
hypothesis cannot reach the step it is meant to block.  The statement is kept verbatim (so the
correction is legible) and `VEnv.ConstRigidPat` is the repaired form.  This is the same defect
class as `RecTypeInj` (§3.3 of the previous edition): a hypothesis set carrying strictly less
information than its conclusion needs, invisible to an auto-bound-implicit audit.  (The
running count of such statements in this development is kept elsewhere and is not asserted
here; what is asserted is the defect and its repair.)  Note the difference from the earlier
finds: `ConstRigid` is not shown **false** — it is shown *unreachable from its own
hypotheses*.  No instance refuting it is exhibited, and none is claimed.

Machine-checked necessity, at the tree's one concrete `Params` instance
(`Theory/Typing/ParamsWitness.lean`'s `propLoopParams`, where a `ParRed.extra` step really
fires) — all three `sorry`-free:

* `propLoop_not_patFreeHead_A` — `PatFreeHead` fails at `A` there;
* `propLoop_patFreeHead_other` — and holds at every other name;
* `parRed_constApp_inv_needs_patFreeHead` — **dropping `PatFreeHead` from
  `ParRed.constApp_inv` makes that lemma false**, because `A ≫ B` and `B` is not an
  application of `A`.

### 2.5 Non-vacuity: (A), (B) and (D) fired end to end, with `PatWF` **discharged**

`Theory/Typing/CycleConv.lean`'s `propLoopEnv2` is `propLoopEnv` *before* its two δ-rules are
added: two constants `A B : Prop` and no definitional-equality rules at all.  It is in the δ
fragment vacuously, so `VEnv.patWF_of_deltaFragment` discharges `PatWF` outright.  Added to
`Verify/Typing/Rigidity.lean`, all machine-checked:

* `propLoopEnv2_wf`, `propLoopEnv2_patWF` — **`sorry`-free**.  Two `VDecl.axiom` steps from the
  empty environment, then `PatWF` from the δ fragment.
* `propLoopEnv2_A_ne_B` — **(D) with content**: two distinct propositions of a rule-free
  environment are not definitionally equal.
* `propLoopEnv2_A_ne_sort`, `propLoopEnv2_A_ne_forallE` — **(A) with content**.

These are the first end-to-end firings of the constant-application family in this tree:
`VEnv.WF` → `paramsOfWF` → `IsDefEq.church_rosser` → the spine analysis, with **no hypothesis
carried**.  Their only taint is the four inherited holes of §2.3.  So the results are not
vacuous, and `PatWF` is not an unsatisfiable ask — it is discharged here.

---

## 4. (C) rigidity: why Church–Rosser does not settle it, and what does

### 3.1 The obstruction, exactly

The spine recursion that proves (B) and (D) works because *both* endpoints are constant
spines, so `NormalEq.etaL` is excluded by shape at every level.  For (C) only the right
endpoint is known, and `etaL` relates a **λ** to a constant application.

* At the **top** of the spine that is excluded by (C)'s `IsType` side condition: an
  η-expansion has a Π type, and a Π is not a sort.  Machine-checked as
  `VEnv.isType_lam_false`.
* At a **proper sub-spine** it is not excluded, because a sub-spine legitimately has a Π type.
  And the induction hypothesis one would need there is **false**: `.lam A b` is a weak-head
  normal form (`WHNF.lam`) that η-relates to a constant application and is not one.
  Machine-checked as `VEnv.whnf_lam_not_constApp` (`sorry`-free).

This is why (C) is genuinely a different statement from (B), and it is a *sharper* reason than
the one `Injectivity.lean` gives ("its formulation mentions weak-head reduction").

### 3.2 The repair, machine-checked

A `WHNF` application has a `WHNF`, non-λ function (`VEnv.WHNF.app_fn`,
`VEnv.WHNF.app_not_lam`), so along a `WHNF` spine `etaL` is excluded at every level after all.

| name | content |
|---|---|
| `VEnv.StRed.constApp_whnf` | a weak-head normal form that standard-reduces to a constant spine *is* one |
| `VEnv.NormalEq.constApp_whnf` | the spine analysis under a `WHNF`, non-λ subject |
| `VEnv.WeakNorm` | `∀ Γ e A, OnCtx Γ → Γ ⊢ e : A → ∃ e', Γ ⊢ e ⤳* e' ∧ WHNF Γ e'` |
| **`VEnv.constRigid_of_weakNorm`** | **(C), from `WeakNorm` and nothing else** |
| `VEnv.constRigidPat_of_weakNorm` | the same, packaged as the stated `VEnv.ConstRigidPat` |

Cone of `constRigid_of_weakNorm`: `weakN_iff`, `forallE_inv_stratified`, `NormalEq.descend`,
`forallE_inv`, `sort_forallE_inv` — one more than (A)/(B)/(D), all existing census holes.

Read off source (not checked): `WeakNorm` is not in the tree in any form, and
`Theory/Typing/HeadRedStuck.lean` is the relevant warning — it shows that a `Params` instance
hosting a *stuck* K-redex that is definitionally a sort would refute `IsDefEq.reduce_sort`.
Any route to `WeakNorm` has to rule such instances out.

---

## 5. `TrProj.weak'_inv`: the swap does **not** transfer, and there is a cheaper entry point

**Asked and answered.**  `ProjSkip.lean`'s swap (the move that unblocked `TrProj.wf`) replaces
an unused entry of the *projection's own field telescope*, so that `projMotiveTerm` stays
saturated while being typed.  Every clause `TrProj.mk` asks for in `weak'_inv`'s conclusion —
`IsStructure`, one `HasType`, three length equations, `hus`, two `HasArgs`, F17 — is a
statement in the ambient context `Γ`, and **none of them mentions that telescope**.  So the
swap has nothing to act on here.  (Read off source: the clause list is `TrProj`'s definition,
`Verify/Typing/Expr.lean:81–145`.)

Machine-measured: the two lemmas' *shared* residual is `IsDefEqU.weakN_iff` and
`forallE_inv_stratified` — `TrProj.wf`'s whole cone — and nothing else.  The previous
edition's claim that they "share a blocker" is right about `weakN_iff` and was never about the
swap.

**Cheaper entry point, not yet tried** (read off source): `VEnv.InferTypeS.weakU_inv`
(`Theory/Typing/HeadReduction.lean:691`) inverts a lift on a whole *inferred typing* and hands
back a type living in `Γ`.  That is steps 1 and 3 of the traced route (`HasType.skips` at
`Ctx.Lift'`, then `IsDefEqU.weak'_iff`) in one already-proved lemma, at the cost of being
`Params`-gated — which (C) already is.  `VEnv.InferType.exists` supplies its input from
`VEnv.WF` alone.

What `weak'_inv` still needs after that, read off source: (C) at `Γ'`; `WHRedS.weakU_inv` to
move the reduction into `Γ` (already proved, already in `Ctx.Lift'` form); (B)'s level half to
reconcile the recovered `us'` with the use site's `us` (**now available**,
`const_app_inv_of_patWF`); a `HasArgs` congruence along argument-wise `IsDefEqU`; and a
`HasArgs` strengthening across the lift.  The last two are plumbing that does not exist yet
and has not been costed.

---

## 6. `TrProj.uniq`: two of four obligations discharged

Unchanged in statement.  Its four obligations were: (1) ledger G4, (2) fact (B), (3) fact (D)
via the independence of `s₁`, `s₂`, (4) a `projTerm` congruence lemma.

* (2) and (3) are **proved**, modulo `PatWF` — `const_app_inv_of_patWF`,
  `constNoConf_of_patWF`.
* (1) is `RecTypeResidual`, unchanged from the previous edition §3.4.
* (4) is unchanged: mechanical, real work, still uncosted.

Note (D) is now proved *without* ledger G4: no-confusion between distinct rule-free constants
does not go through structure uniqueness at all.  G4 is still needed for (1).

Non-vacuity of (D) at a rule-free environment is §2.5, with `PatWF` discharged.  At the
two-field *structure* witness it is machine-checked
(`Verify/Typing/Rigidity.lean`) as: `barEnv_ruleFreeHead'` generalises the previous
`barEnv_ruleFreeHead` to every name but `Bar.rec`, and `barEnv_bar_ne_ctorApp` derives from
(D) that `Bar` is **not** definitionally equal to any application of `Bar.mk` — a negative
statement with content, at the environment where `RuleFreeHead` is proved rather than assumed.
Two hypotheses are carried rather than discharged there, and neither is about `barDecl`:
`barEnv.WF` (because `VInductDecl'` is not yet wired into `VDecl.induct` — the same gap
`ProjWfWitness.lean` §2.5 records) and `PatWF` (the open `Params` field itself).

---

## 7. Corrections to earlier editions of this file and to docstrings

1. **"(B) is reduced to `trans` as its only residual"** — true of the `IsDefEqStrong`
   induction, and *not* a fact about the statement.  Church–Rosser proves (B) outright modulo
   `PatWF`; the `trans` case never arises because `NormalEq` has no `trans` constructor.
2. **"(C) needs (B) plus rigidity"** and **"`TrProj.weak'_inv` needs (C), (B)'s level half and
   `weak'_iff`"** — the list is right, and (C)'s own residual is now named: `WeakNorm`.
3. **`VEnv.ConstRigid`'s `RuleFreeHead` side condition** is the wrong condition under an
   abstract `Params`.  Use `VEnv.ConstRigidPat`.  §2.4.
4. **"`TrProj.wf`'s swap may help `weak'_inv`"** — it cannot.  §4.
5. `Theory/Typing/Injectivity.lean`'s module docstring says a fourth fact (no-confusion) "is
   not stated because no consumer has asked for it".  It is now stated *and proved*
   (`VEnv.ConstNoConf`, `VEnv.constNoConf_of_patWF`).  Both it and the (A)/(B) proofs belong
   in that file rather than under `Verify/`; they are here only because that file is another
   stream's.  Nothing in `ConstSpine.lean` depends on `Verify/`, so it moves verbatim.

---

## 8. Files

### This round

New (both owned; nothing imports them, so nothing can have gone red because of them):

* `Lean4Lean/Verify/Typing/ProjGen.lean` — §0″.1, §0″.3–§0″.5.  Imports
  `Theory/Inductive/StructureClosed` only.
* `Lean4Lean/Verify/Typing/ProjGenWitness.lean` — §0″.2.  Imports `Verify/StructureBridge`
  (read-only) and `ProjGen`.  Carries `set_option maxHeartbeats 2000000`: the first witness
  takes ~90 s, because `decl2`'s block data is unfolded through `padMotives`/`padMinors`.

Edited: none.  `Structure.lean`, `StructureClosed.lean`, `StructureEta.lean`,
`StructureExamples.lean`, `ProjSkip.lean`, `Lemmas.lean`, `StructureUniq.lean`,
`Expr.lean` are all **unchanged** this round — the generalisation is additive by design
(§0″.3, correction 4).

Re-run and still passing after the round **[checked]**: the five `rfl` checks of
`etaExpansion` against Lean's own elaborator at `Prod`/`Sigma`/`And`/`Subtype` plus the F17
clause at `And` (`Theory/Inductive/StructureExamples.lean`); `empty_structEta`,
`bazEnv_structEta_premises`, `bazEnv_structEta`, `bazEnv_etaExpansion_eq`,
`bazEnv_projMinors_distinct`, `barField0_lvl_ne_zero` (`StructureEta.lean`);
`MutNonRec.kernelProjChecks`, `projCore_arity_wrong` (`Verify/StructureBridge.lean`);
`tryEtaStructCore.WF_of_structEta`, `isDefEqUnitLike.WF_of_structEta`
(`Verify/TypeChecker/IsDefEq.lean`).  The honest caveat of `handoff-eta.md` §6 is **preserved
unchanged**: both eta bridges are still provable for every `c` for the `TrEnv.not_ctorInfo`
reason, so today's instantiation is still empty, and nothing this round converts that into an
apparent result — no file on that path was touched.

### Previous round

New:

* `Lean4Lean/Verify/Typing/ConstSpine.lean` — §2, §3.  Imports `Theory/Typing/HeadReduction`,
  `Theory/Typing/Injectivity`, `Theory/Typing/ParamsBuild`.  Depends on nothing in `Verify/`.

Edited (all owned by this stream):

* `Lean4Lean/Verify/Typing/Rigidity.lean` — (D) proved; (C) repaired and reduced;
  `PatFreeHead` necessity witnesses; the `propLoopEnv2` end-to-end firings (§2.5); `barEnv`
  non-vacuity; header rewritten.  Now imports `Theory/Typing/ParamsWitness` and
  `Verify/Typing/ConstSpine`.
* `Lean4Lean/Verify/Typing/Lemmas.lean` — docstrings of `TrProj.weak'_inv` and `TrProj.uniq`
  updated (§4, §5).  No proof changed; census unchanged.
* `Lean4Lean/Verify/TypeChecker/WHNF.lean` — `quotReduceRec.WF`'s docstring updated: its
  residual is now *forward* (discharge `PatWF`), not *sideways* (state a new inversion
  principle).

Unchanged: `Theory/Inductive/StructureClosed.lean`, `Verify/Typing/ProjLevelWitness.lean`,
`Verify/Typing/ProjSkip.lean`, `Verify/Typing/ProjWfWitness.lean`,
`Verify/Typing/StructureUniq.lean`, `Verify/TypeChecker/InferType.lean`.

**Auto-bound-implicit audit.**  Every new statement is a `def … : Prop` with explicit binders,
or a theorem whose binders were read back from the elaborated type.  The defect that bit this
round was again a different one — §2.4.
