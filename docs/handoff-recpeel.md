# handoff-recpeel — the general `interp (D.recType j)` peel, and `sort_not_proof`

## Priors (written before the first instrument call of the round)

Brief: two steps the set model reportedly still owes `kernel_sound`.

1. A **general** `interp (D.recType j)` peel. Brief says all three existing peels in
   `Theory/SetModel/` are per-declaration.
2. `Lean4Lean.SetModel.sort_not_proof` — brief says NOT FOUND; decide the statement,
   decide truth, prove it.

Priors, stated so they can be scored:

- P1 (0.75) The "three peels are per-declaration" claim is TRUE. `UnitOracleLarge`,
  `EqRecLarge`, `IffRecLarge` are named per-declaration by their filenames, and the
  orchestrator's *cone* figures are reliable while its *attributions* have been wrong
  five times — but "which files contain a peel" is closer to a cone/enumeration fact
  than an attribution. Risk: a fourth, general peel exists under a name not containing
  "peel".
- P2 (0.5) A fully general `interp (D.recType j) = <peeled form>` is NOT reachable this
  round as a bare equation, because `interp` of a recursor type quantifies over the
  motive space and the peel must know the *arity decomposition* of `D.recType j`, which
  is per-`D` data. Expected outcome: an `↔` reduction to a smallest-sufficient premise,
  in the brief's own escape hatch.
- P3 (0.6) `sort_not_proof`'s intended content is NOT "sorts and proofs have distinct
  interpretations" as a raw statement but something like: an element of the interpretation
  of a `Prop` (a proof) is never itself the interpretation of a `.sort` — used to rule
  out a `.sort` inhabiting a proposition. Prior that *some* true statement of that shape
  is provable in the model: 0.7. Prior that the *named* reading is the load-bearing one:
  0.45.
- P4 (0.85) Neither step touches the `Theory/Equiconsistency.lean` hole: that hole is
  about equiconsistency strength, not about interp peeling.
- P5 (0.3) The peel needs something Foundation does not provide. Set-theoretic function
  space and singleton reasoning should already be there given `eq_singleton_of_recProp`
  exists hole-free.
- P6 (0.9) Round-close census will be 13 / NOT BUILT 0 as the brief states.

## Measurements

(one line per instrument call, appended as made)

- M1 `grep -rn peel` + read `Theory/Typing/StructEtaPrice.lean` §8. **The brief's two steps are
  verbatim the two bullets of StructEtaPrice.lean's "What is still owed, precisely."**
  (1) unfolding `interp (D.recType j)` to `eq_singleton_of_recProp`'s shape; (2) the `PropSplit`
  side condition — "the argument needs the motive not to be classified as a proof, which
  `PropSplit`'s agreement with typing gives ... but which no lemma in the tree states in that
  form." So step 2 (`sort_not_proof`) is *specified* by that sentence, not a guess: P3's
  "distinct interpretations" reading is already looking wrong; the real content is
  `¬ IsProof (motive)`. Prior P3 updating down.
- M2 `exists.lean` × 10. Cone figures confirmed exactly as briefed:
  `Lean4Lean.SetModel.eq_singleton_of_recProp` FOUND, module **`Lean4Lean.Theory.Typing.StructEtaPrice`**
  (NOT `Theory/SetModel/`), arity 8, cone 5826, hole-free. `Lean4Lean.SetModel.soundAbove` FOUND,
  module `Theory.SetModel.SoundInduction`, arity 23 (brief said "arity 7163 cone" — the 7163 is the
  cone, arity is 23), cone 7163, hole-free.
  `Lean4Lean.SetModel.sort_not_proof` **NOT FOUND** — brief confirmed.
  **BUT** `Lean4Lean.VEnv.sort_not_proof` FOUND (`Theory.Typing.SortUniq`, arity 10, cone 2378,
  hole-free) and `Lean4Lean.SetModel.sortNotProof_of_propSplit` FOUND
  (`Theory.SetModel.NotProofNoModel`, arity 10, cone 1062, hole-free), and
  `Lean4Lean.SetModel.sortDenot_not_mem_propDenot` FOUND (arity 18, cone 6508, hole-free).
  So "sort_not_proof" *as a syntactic statement* is already in the tree twice over. P3 was wrong
  in the direction that matters: the missing thing is not `¬IsProof (.sort u)` at all.
  population 444 modules, watching 6, **none of 6 in any cone** (no forbidden statement reached).
  `mkForallType_const_eq_pow` FOUND arity 13 cone 5784 hole-free; `charFam` arity 6 cone 5693.
- M3 outlines of the three peels. **CLAIM VERIFIED: all three are per-declaration.**
  `SetModel/UnitOracleLarge.lean` `interpL_motTyU` is stated at `unitEnvLE`/`motTyU` (hardcoded
  `.const \`Unit1 []`); `SetModel/EqRecLarge.lean` `motSet_eq_interp_motTyE` at `eqIndDecl` with an
  `EqSpec M v` hypothesis; `SetModel/IffRecLarge.lean` `motSetI_eq_interp_motTyI` at `iffIndDecl`
  with `IffSpec M`. Each peels by N hardcoded `UnitAudit.mkLam_mem_mkForallType_of_dom` layers
  (6 / 6 / 5). No `D`-quantified peel anywhere. P1 scored CORRECT.
  Side find: `SetModel/IffRecLarge.not_isProof_mot_gen` is the per-declaration form of owed step 2.
- M4 read `Theory/SetModel/Interp.lean` (`interp`, `PropSplit`, `IsProp`/`IsProof` = `(L.lvl/srt Γ _).eval ls = 0`),
  `Theory/Inductive/Telescope.lean` (`VExpr.mkPi`), `Theory/Inductive/Decl.lean:804` (`recType j =
  mkPi (atRecTele params ++ motives ++ minors ++ liftTele _ indices) (.forallE major (motive_j …))`),
  `SoundInduction.isProp_iff`/`isProof_iff`. **Design fixed**: the general peel is telescope-general
  (`mkPi`), not `recType`-specific, and it needs exactly two side conditions, which are the two
  things owed: (a) `¬ IsProp` at each binder — reducible to the *innermost* codomain because a Π's
  sort is `imax dom cod` and `imax _ v` evals to 0 iff `v` does; (b) `¬ IsProof` of the motive in
  the body's `app` clause — which IS owed step 2. So step 2 is a *prerequisite* of step 1, not an
  independent item; the brief's "independent" applies only w.r.t. confluence.
  **`sort_not_proof`'s right statement identified**: `¬ L.IsProof M Γ A` whenever
  `env.HasType nv Γ A (.sort u)` — because `A`'s type is `.sort u`, whose own sort is `.succ u`, and
  `(.succ u).eval ls = u.eval ls + 1 ≠ 0`. Unconditional in `u`; no `u.eval ≠ 0` needed. The
  literal `¬ L.IsProof M Γ (.sort u)` is the special case at `A = .sort u`.
- M5 `lake env lean` on new `Theory/SetModel/RecTypePeel.lean` §1-§2: GREEN.
  `SetModel.not_isProof_of_isType` (owed step 2, general), `SetModel.sort_not_proof` (the cited
  name, now FOUND), `SetModel.TeleWF`, `SetModel.TeleWF.onCtx`, `SetModel.exists_sort_mkPi`.
  `exists_sort_mkPi` is the level content: `mkPi As B : .sort w` with `w.eval ls = 0 ↔ v.eval ls = 0`
  at every `ls`, by a right fold of `imax` and `SoundInduction.imax_eq_zero_iff`.
- M6 §3-§7 GREEN: `apply_mem_of_mem_mkForallType`, `PeelArgs`, `appAll`, `snocs`,
  `appAll_mem_interp_of_peel` (the general `mkPi` peel), `not_isProof_of_typeFormer`,
  `not_isProof_bvar_of_typeFormer`, `VInductDecl'.recPiTele`/`recPiBody`/`recType_eq_mkPi`/
  `recType_instL_eq_mkPi`/`recPiTele_length`, `appAll_mem_interp_recPiBody(_instL)`.
  Imports added: `Theory.Typing.StructEtaPrice` (for `eq_singleton_of_recProp`; note it itself
  imports `Verify/TypeChecker/EtaUnitRefute`, so Theory->Verify already exists in the tree, this
  adds no new architectural direction) and `Theory.Inductive.NestedHead` (ntreeAux).
- M7 **TRAP FOUND, and it invalidates my own first §7.** `interp`'s `forallE` clause branches on
  whether the **codomain** is a Prop. At `elimLvl = .zero` the *whole* `recType` is propositional,
  so EVERY binder takes the `mkForallProp` branch, not `mkForallType` -- including the motive
  binder, whose *domain* is a type. `eq_singleton_of_recProp`'s `H` is the `UProp` (small-elim)
  shape, so the peel it consumes is the **`mkForallProp`** one. A `mkForallType`-based composition
  carrying `UProp ^ Sv` as the motive space (my first §7) is at best not the instance that arises
  and at worst vacuous: its `hnpx : ¬IsProp B` contradicts the very slice `eq_singleton_of_recProp`
  is about. Rewriting §7 as the Prop-branch peel; keeping the `mkForallType` peel as the
  large-eliminator route (non-vacuous -- it is what `UnitOracleLarge`/`EqRecLarge`/`IffRecLarge`
  do at their large slices).
- M8 `lake env lean` on the finished file: **ZERO errors, ZERO warnings** (including zero
  section-variable warnings). 26 `#print axioms` lines, all `[propext]` or
  `[propext, Classical.choice, Quot.sound]` -- **no `sorryAx` anywhere**.
  Sections: §1 sort_not_proof, §2 TeleWF/exists_sort_mkPi/isProp_mkPi_iff, §3
  apply_mem_of_mem_mkForallType, §4 PeelArgs + appAll_mem_interp_of_peel, §5
  not_isProof_of_typeFormer/_bvar_, §6 VInductDecl'.recPiTele/recPiBody/recType_eq_mkPi/
  recType_instL_eq_mkPi/motiveType_eq_mkPi_sort/recPiTele_length, §7 PeelArgsP +
  mem_interp_of_peelP + mem_interp_recPiBody_of_peelP(_instL), §8
  eq_singleton_of_mem_interp_mkPi3, §9 not_isProof_motive_bvar, §10 unitDeclLE firings,
  §11 ntreeAux firings.
- M9 whole-tree `lake build`: **green, 1633 jobs**.
- M10 `lake build` grep for section-variable warnings, excluding `.lake/packages`:
  **exactly one, and it is NOT in-repo** -- `Foundation/FirstOrder/SetTheory/Z.lean:35`
  (`LO.FirstOrder.SetTheory.subset_of_eq`), i.e. in the pinned dependency. **Zero in-repo.**
- M11 `scripts/sorry-census-all.lean`: `BUILT: 450; in population but NOT BUILT: 0` and
  `HOLES over the WHOLE built population, unioned across both passes: 13`. **13 / NOT BUILT 0.**
- M12 `Lean4Lean/Verify/Guard.lean` re-elaborated: guard 1 "Axioms.lean declares exactly the 24
  frozen axioms ✓"; guard 2 "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx
  present)"; guard 3 "checker cone implementation gaps within frozen list (2/2 remaining) ✓".
  All three pass.
- M13/M14 `exists.lean` on all 22 new names (population 447, watching 6). Every one FOUND in
  `Lean4Lean.Theory.SetModel.RecTypePeel`, every one `own value is a hole: false` and
  `cone reaches sorryAx: false`, and every one **`watched declarations in cone: none of 6`** --
  no forbidden statement reached by anything in this round.
  Cones: `sort_not_proof` 777 (arity 13); `not_isProof_of_isType` 776 (15);
  `not_isProof_of_typeFormer` 1176 (17); `not_isProof_bvar_of_typeFormer` 1178 (17);
  `not_isProof_motive_bvar` 1217 (20); `exists_sort_mkPi` 1079 (9); `isProp_mkPi_iff` 1166 (17);
  `appAll_mem_interp_of_peel` 6304 (17); `mem_interp_of_peelP` 6297 (17);
  `eq_singleton_of_mem_interp_mkPi3` 6316 (27); `mem_interp_recPiBody_of_peelP` 6378 (17);
  `mem_interp_recPiBody_of_peelP_instL` 6381 (18); `appAll_mem_interp_recPiBody` 6385 (17);
  `VInductDecl'.recPiTele` 667 (2); `VInductDecl'.recPiBody` 591 (2);
  `VInductDecl'.recType_eq_mkPi` 673 (2); `VInductDecl'.recType_instL_eq_mkPi` 678 (3);
  `VInductDecl'.motiveType_eq_mkPi_sort` 705 (3);
  `UnitAudit.unitDeclLE_recType_instL_mkPi` 694 (1); `UnitAudit.isPropL_recB1_iff'` 6485 (14);
  `UnitAudit.unitL_denot_eq_singleton_of_zero` 8250 (14);
  `InductiveDeclExamples.ntreeAux_recPiTele_length` 1556 (0);
  `InductiveDeclExamples.ntreeAux_motiveType_mkPi` 720 (1);
  `InductiveDeclExamples.ntreeAux_recType_mkPi` 686 (1).

## Prior scoring

| prior | outcome |
|---|---|
| P1 (0.75) three peels are per-declaration | **CORRECT** -- M3 |
| P2 (0.5) a bare general peel is out of reach, expect an `↔` | **WRONG in my favour**: the bare general peel exists in both branches, no `↔` escape needed. What *is* left as a premise is the argument list plus one `IsProp` decision, and `isProp_mkPi_iff` collapses the decision family to one |
| P3 (0.6) `sort_not_proof` is not the "distinct interpretations" reading | **CORRECT**, and sharper than I priced: the reading is `¬IsProof` of a *term whose type is a type former*, and the `.sort` case is the degenerate one. The "distinct interpretations" reading was already in the tree three times over (M2) |
| P4 (0.85) no contact with the `Equiconsistency.lean` hole | **CORRECT** -- every cone is `sorryAx`-free (M13/M14), so nothing here reaches any hole, that one included |
| P5 (0.3) needs something Foundation lacks | **WRONG (good)**: only `mem_function_iff`, `value_eq_of_kpair_mem`, `mem_of_mem_functions`, `IsFunction.of_mem`, `mem_power_iff` -- all already used by `UnitOracleLarge.motiveL_app_mem_U`. No new Foundation demand, no pin change |
| P6 (0.9) census 13 / NOT BUILT 0 | **CORRECT** -- M11 |

## Verdict: what the model still owes `kernel_sound` after this round

1. **`TeleWF env₀ nv Γ (D.recPiTele j)` from `D.RecCtx env`.** The typings exist
   (`VInductDecl'.RecCtx.onCtxParams`, `onCtxMotives`, `onCtxMinors`, `recType_isType`,
   `Theory/Inductive/Lemmas.lean`) but they are `OnCtx`, which does not record level
   well-formedness, and `PropSplit.prop_sound`/`proof_sound` need it. Bridge:
   `IsDefEq.levelWF` / `CtxStrong.levelWF`. Level bookkeeping, not mathematics. This is the only
   thing between §7 and a `D`-quantified surjective-pairing theorem with no `interp` equations
   left as hypotheses.
2. **The four per-declaration `interp` equations** of §8 (`hmot`/`hmin`/`hmaj`/`hbody`) at a
   general block. These are what the oracle's *definition* fixes; the general versions are
   `interp`-of-`tyApp'`, `interp`-of-`minorType`, `interp`-of-`recPiBody`, and they need the
   oracle interface (`InductOracleOK`), not the peel.
3. **Positive fields.** `eq_singleton_of_recProp` is the zero-field core.
   `StructEtaPrice.lean` §8 says the positive-field case is `SetModel/Inductive.lean`'s
   `mem_Ind_iff` read through the oracle; `mem_Ind₃_fibre_iff_of_zero_field` is the zero-field
   half. Untouched here.
4. Nothing here touches `Theory/Equiconsistency.lean`'s hole or the Foundation interface.

- M15 conclusion-shape query (not grep-by-name): every statement in `Theory/SetModel/` and
  `Theory/Typing/` mentioning both `interp` and `recType` is at a **named** declaration
  (`eqIndDecl`, `unitDeclLE`, `iffIndDecl`), always at `Γ = []`, `ρ = ∅` and a concrete `instL`
  argument list -- `EqOracle.lean` (9 sites), `EqRecLarge.lean` (6), `EqRecNecessity.lean`,
  `EqZeroSlice.lean` (2), plus `UnitOracleLarge`/`IffRecLarge`. **No `D`-quantified one.** The
  per-declaration claim is confirmed twice over (M3 by outline, M15 by conclusion shape), which is
  the pairing `exists.lean`'s own docstring asks for before an absence claim is written down.
