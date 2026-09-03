/-
# `FlipPrice`: a measurement of the nested `AddInduct` flip, 2026-09-03

This file *measures*; it proves nothing new.  It exists because `docs/vacuity-ledger.md` §6
and `docs/critical-path.md` Correction 5 price the nested flip against a state of the tree
that no longer holds, and a re-pricing has to be checkable rather than read off docstrings.

Everything below is `#print axioms` on declarations that already exist.  A clean
`[propext, Classical.choice, Quot.sound]` here means *hole-free*, and nothing more; in
particular it does **not** mean non-vacuous.  Where a statement's non-vacuity matters it is
noted in `docs/handoff-flipprice.md`, never inferred from an axiom line.
-/
import Lean4Lean.Theory.Inductive.RestoreBridge
import Lean4Lean.Theory.Inductive.NestedTele
import Lean4Lean.Theory.Inductive.NestedOrdered
import Lean4Lean.Theory.Inductive.NestedKeys

/-! ## 1. `addInductR_ordered'` — the reduction the three obligations hang off -/
#print axioms Lean4Lean.VEnv.addInductR_ordered'
#print axioms Lean4Lean.VEnv.addInductR_ordered_nil

/-! ## 2. Obligation (A): general at `D.params = []`, plus the two general bridges -/
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_np_zero'
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_substC
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_substC'

/-! ## 3. Obligations (B) and (C): the general bridge statements -/
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_substC
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_substC

/-! ## 4. The two end-to-end instances: `np = 0` and `np = 1` (parameterful) -/
#print axioms Lean4Lean.InductiveDeclExamples.nfnAux_addInductR_ordered
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_addInductR_ordered
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationB
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationC

/-! ## 5. The block that used to refute (A), and now refutes nothing -/
#print axioms Lean4Lean.InductiveDeclExamples.nfnAuxDirty_obligationA
#print axioms Lean4Lean.InductiveDeclExamples.nfnAuxDirty_iotaRulesRS_bridge
#print axioms Lean4Lean.InductiveDeclExamples.nfnNodeDirty_declared_clean

/-! ## 6. Ledger item 4: the keys arm -/
#print axioms Lean4Lean.VEnv.keysR_induct

/-! ## 7. The third obstruction on (B)/(C): `csubst`'s domain escapes `blockNames` -/
#print axioms Lean4Lean.InductiveDeclExamples.nfn_csubst_dom_escapes_blockNames

/-! ## 8. Signatures — what hypotheses the general bridges still demand -/
#check @Lean4Lean.VEnv.ctorConstsCR_wf_of_np_zero'
#check @Lean4Lean.VEnv.ctorConstsCR_wf_of_substC'
#check @Lean4Lean.VEnv.recConstsR_wf_of_substC
#check @Lean4Lean.VEnv.iotaRulesRS_wf_of_substC

/-! ## 9. The np = 0 trio, in general — one per obligation

Added after the structural scan (`FlipPriceScan.lean`) turned up (B)'s and (C)'s parameterless
theorems in `Theory/Inductive/NestedRules.lean`.  `docs/vacuity-ledger.md` §6 predates all three
and names none of them.

**CORRECTED 2026-09-03**: an earlier revision of this note said `NestedRules.lean` "was untracked
at the start of this session".  It is tracked, and has been since `b4d6e21` (09-01 09:06); (B)/(C)
at `np = 0` landed in `146ce97` (09-01 09:34).  Only the claim about §6 survives. -/
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_np_zero'
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_np_zero
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_np_zero

/-! ## 10. The general (parameterful) routes, and the syntactic bridge that is REFUTED at np = 1

`ntree_iotaRules_bridge_false` is the (C) *syntactic list* bridge — the hypothesis of
`iotaRulesRS_wf_of_substC` — refuted by `decide` at `ntreeAux`, `D.np = 1`.  So the route
`docs/vacuity-ledger.md` §6 and `NestedOrdered.lean`'s STATUS entry both point at for (C) is a
dead end above `np = 0`, and the live one is the componentwise-defeq
`iotaRulesRS_wf_of_components`. -/
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iotaRules_bridge_false
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_components
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_substC'

/-! ## 11. All three obligations at the PARAMETERISED witness, hypothesis-free -/
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationA
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationB
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationC

/-! ## 12. Part 6's obstruction, and the composition — which turned out to be already made

`NoConstIn.noCSubst` is stated for an ARBITRARY predicate `P` and any `σ` whose domain
satisfies it, and `IsNestedName` is a `_nested`-PREFIX test, so it holds of the companion's
constructor and recursor names as well as its type name — exactly the three name kinds
`csubst`'s domain contains and `NoBlock`/`blockNames` does not reach.

**CORRECTED 2026-09-03.**  An earlier revision of this note said the two "have never been composed
against (B)/(C)".  That is **wrong**: the composition is `VIndRestore.NameBarrier`
(`Verify/Inductive/NestedRestore.lean` §2), whose `dom` field is `csubst_dom` plus the three
`aux*` clauses and whose `substFree` field reads `(h.resArgs j a ha).noCSubst fun _ _ => h.dom`.
(B)/(C) were restated to take `R.SubstFree D (R.csubst D K)`, which `NameBarrier.substFree`
discharges from name discipline alone.  What was genuinely missing was the end-to-end statement,
now in `Verify/Inductive/FlipPriceCompose.lean`.  The rest of the analysis above stands, including
which three name kinds matter.  See `docs/handoff-flipprice.md` §5. -/
#print axioms Lean4Lean.VExpr.NoConstIn.noCSubst
#print axioms Lean4Lean.IsNestedName.mkRecName
#check @Lean4Lean.VExpr.NoConstIn.noCSubst
#check @Lean4Lean.VEnv.iotaRulesRS_wf_of_components

/-! ## 13. The three live general **parameterful** routes — the whole of what still blocks

Added 2026-09-03 so that `docs/handoff-flipprice.md` §6's table is measured rather than read off
docstrings.  One route per obligation, each hole-free, each carrying exactly one open residual:

* (A) `ctorConstsCR_wf_of_substC'` — the telescope defeq, with `ntreeNode_beta_bridge` the
  one-block β-step done by hand;
* (B) `recConstsR_wf_of_blocksD` / `_of_entriesD` — the motive/minor telescopes and the recursor
  body, blockwise or entrywise;
* (C) `iotaRulesRS_wf_of_hargsD` — `R.IotaHargs` per constructor; `ntreeAux_iotaRulesRS_wf_of_nine`
  is it at `ntreeAux`, and `ntree_iota_components_ne` says all nine components **move**, so there
  is no `TeleDefEq.rfl` discount to be had. -/
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_beta_bridge
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_blocksD
#print axioms Lean4Lean.VEnv.recConstsR_wf_of_entriesD
#print axioms Lean4Lean.VEnv.iotaRulesRS_wf_of_hargsD
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_iotaRulesRS_wf_of_nine
#print axioms Lean4Lean.InductiveDeclExamples.ntree_iota_components_ne
