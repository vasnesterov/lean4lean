# `handoff-sortwitenv.md` — is the `Sort u`-constant condition automatic at the restriction step?

Owner file: `Lean4Lean/Verify/Inductive/SortWitEnv.lean` (new; nothing else was touched).
Written incrementally during the run.

## 0. The question

`Verify/Inductive/StrengthenFamily.lean` §5 proves the bypass of the strengthening hole

    VIndRestore.argsTypedK_of_resultSortInhab
      (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
      (hb : D.ResultSortInhab env b) : R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ

hole-free (arity 11, cone 3333).  Four clauses discharge `hb`; the strong one,
`VInductDecl'.resultSortInhab_of_const` (arity 5, cone 749, hole-free), subsumes the other three
and needs only

    hc : env.constants c = some ⟨1, .sort (.param 0)⟩

— **one universe-polymorphic `Sort u`-valued constant in the environment**, `PUnit.{u}` being the
standard example.  `StrengthenFamily.lean` §8 (corrected 2026-09-03, after
`VEnv.not_forall_sort_param_uninhabited` refuted its own normal-form argument) leaves exactly this
open: "what remains is not a level condition but an environment one: that the environment at
`RestrictStepCfg`'s `e₁`/`e₂` actually declares such a constant."

## 1. VERDICT

**Possibility (ii)/(iii): the condition is NOT automatic.  The bypass needs exactly this one
named, satisfiable hypothesis.**

It does not follow from `RestrictStepCfg`'s nine fields, at any of its three environments, and the
counterexample is not a manufactured environment — it is *the project's own parameterised nested
witness*.  `env₁ = VEnv.empty.addInduct' listDecl` (the environment `ntreeAux_restrictStepCfg` is
instantiated at) declares exactly `List`, `List.nil`, `List.cons`, `List.rec`, and **no constant of
it has a type of the form `Sort l` at all**, for any universe count and any level.  Adding the
block's own type constants does not help: `NTree` and `_nested.List_1` are both declared at
`Type u → Type u`.

The condition *is* satisfiable at a real configuration of the same nested block (§4 below,
arity 0), and it holds in any environment declaring `PUnit.{u}` — so in practice it is discharged
by inspecting the environment's constant table, which is decidable, rather than by a proof about
the block.  "Usually present" is exactly right, and that is why it has to be stated.

## 2. The condition, named

    def VEnv.SortWitness (env : VEnv) : Prop :=
      ∃ c : Name, env.constants c = some ⟨1, .sort (.param 0)⟩          -- cone 19

A fact about the environment alone: no block, no occurrence data, no judgement, no level.

| declaration | arity | cone | hole-free |
|---|---|---|---|
| `VEnv.SortWitness` | 1 | 19 | yes (no proof term) |
| `VEnv.SortWitness.sortInhab` — every well-formed level's sort is inhabited in every context | 6 | 731 | yes |
| `VInductDecl'.resultSortInhab_of_sortWitness` | 4 | 752 | yes |
| `VIndRestore.argsTypedK_of_sortWitness` — **the bypass with the condition explicit** | 11 | 3342 | yes |
| `VEnv.SortWitness.mono` | 4 | 30 | yes |

`argsTypedK_of_sortWitness`'s only other premise is `D.lvl.WF D.uvars`, which `VInductDecl'.WF`
carries wherever the kernel accepted the block and which is `decide`-able at a concrete block.

## 3. The refutation (task (a)(iii), task (b))

| declaration | arity | cone | hole-free |
|---|---|---|---|
| `VConstant.typeIsSort` / `_eq_true` — the decidable shadow | 1 / 2 | small | yes |
| `VEnv.addInduct'_constants_inv` | 7 | 1044 | yes |
| `InductiveDeclExamples.listDecl_allConsts_no_sort` (`by decide`) | 2 | 722 | yes |
| `InductiveDeclExamples.listEnv_no_sort_const` — **no sort-typed constant at all** | 5 | 1070 | yes |
| `InductiveDeclExamples.listEnv_not_sortWitness` | 2 | 1073 | yes |
| `InductiveDeclExamples.listEnv₂_not_sortWitness` (at `e₂`) | 4 | 1078 | yes |
| `InductiveDeclExamples.listEnv₃_not_sortWitness` (at `e₁`) | 4 | 1079 | yes |
| `not_sortWitness_of_restrictStepCfg` | **0** | 3518 | yes |
| `not_sortWitness_of_restrictStepCfg₃` — at `env`, `e₂` **and** `e₁` | **0** | 3521 | yes |
| `not_sortWitness_of_wf` — not implied by `VEnv.WF` either | **0** | 75 | yes |

`listEnv_no_sort_const` is the sharp form: `env₁.constants c ≠ some ⟨n, .sort l⟩` for *every* `c`,
`n` and `l`.  So the failure is not "no `PUnit`-shaped constant"; it is "no `Sort`-typed constant".

**Can such an environment arise from `addDecl`?  Yes.**  It is `VEnv.empty` with `List` declared
over it — a legitimate declaration history, `Ordered` in-tree via
`InductiveDeclExamples.listEnv_ordered`, and the very environment every `ntreeAux` witness in this
repository runs at.  Lean's real prelude declares `PUnit` long before `List`, so a *prelude*
environment satisfies the condition; the spec quantifies over environments, so that is not a proof,
which is precisely the distinction the brief asked about.

## 4. Satisfiability, and the arity-0 witness at `ntreeAux` (task (c), task (d))

The witness is `listDecl`'s environment with **one** `Sort u` axiom (`sortWit`, the `VConstVal`
`VEnv.sortWitCV` from `Theory/Typing/WeakNForward.lean` §4.3) declared on top.  The axiom's name is
disjoint from every name the `NTree` block introduces, so both staging equations still hold and
every field of `RestrictStepCfg` survives.  Two monotonicity steps were missing from the tree and
are proved here; neither is specific to this witness.

| declaration | arity | cone | hole-free |
|---|---|---|---|
| `VNestedOcc.OccursN.mono` | 5 | 942 | yes |
| `VEnv.ConstsClosedC.addConst_sort` | 7 | 403 | yes |
| `VInductDecl'.KFresh.addConst_sort` | 11 | 765 | yes |
| `InductiveDeclExamples.ntree_sortWit_fresh` | 2 | — | yes |
| `InductiveDeclExamples.ntree_sortWit_stage_exists` | **0** | 1067 | yes |
| `InductiveDeclExamples.ntreeAux_built_sortWit` | 4 | 1429 | yes |
| `InductiveDeclExamples.ntreeAux_restrictStepCfg_sortWit` | 8 | 3504 | yes |
| **`InductiveDeclExamples.ntreeAux_sortWitness_bypass`** | **0** | 4173 | yes |
| `InductiveDeclExamples.ntreeAux_argsTypedK_of_sortWitness` | **0** | 4176 | yes |
| `InductiveDeclExamples.ntreeAux_sortWit_valStrengthen_nonvacuous` | **0** | 4177 | yes |

`ntreeAux_sortWitness_bypass` closes existentially over the pre-block environment and the two
staging environments and asserts, all at once: the configuration, `env₁.SortWitness`, the datum at
`e₂`, `ResultSortInhab` at the sort-witness value, the `CompanionVals` data, node 5
(`ValStrengthen`) and node 1 (the datum at `e₁`).  Nothing hypothesised.  The block is `ntreeAux`
(`uvars = 1`, `params = [.sort (.succ (.param 0))]`, `np = 1`) — **not** the degenerate `nfnAux`.

Vacuity controls, both directions:

* not trivially true — §3 (`not_sortWitness_of_restrictStepCfg₃`, `not_sortWitness_of_wf`);
* not trivially false — the arity-0 theorems above;
* the substitution is not degenerate — `ntree_sortWitJunk_dom_val` (arity 0, cone 472) shows the
  companion name is in `junkSubst`'s domain with value
  `λ (α : Type u), sortWit.{u+1}`; `ntree_sortWitJunkVal_ne_tyVal` (cone 799) shows it is not the
  intended `ntreeVal`; `ntree_sortWitJunk_ne_ntreeJunk` (cone 784) shows it is not
  `StrengthenFamily.lean` §6's successor-clause value either, so the **fourth** clause is the one
  firing and not the first;
* node 5 is not vacuous at the extended witness — `ntreeAux_sortWit_valStrengthen_nonvacuous`
  moves the concrete typing `ntreeVal : Type u → Type u` down to `e₁`.  Incidental finding: this
  statement is **hole-free** here, whereas the analogous `RestrictStep.lean` §3a
  `ntreeAux_valStrengthen_nonvacuous` is tainted (it routes through
  `VEnv.IsDefEq.restrict_of_conservativity`).

`HasArgs.of_mkApp` is not used anywhere in the file; the corner stays `PiInv`-free.

## 5. §2a: the premise moved from `env` to `e₁`

`StrengthenFamily.lean`'s `ResultSortInhab` is stated at the **pre-block** `env` and moved up by
`.mono C.le₁`; §8's residue talks about `e₁`/`e₂`.  Those are different conditions and the `e₁` one
is strictly weaker, so it is the one worth having.  `junkVal_hasType₁` monotonises the two
ingredients that come from `D.WF env` (the canonical-type defeq, the index context) instead of the
whole judgement, and everything downstream follows.

| declaration | arity | cone | hole-free |
|---|---|---|---|
| `VInductDecl'.junkVal_hasType₁` | 9 | 700 | yes |
| `VInductDecl'.companionVals_junk₁` | 10 | 1181 | yes |
| `VIndRestore.argsTypedK_of_resultSortInhab₁` | 11 | 3333 | yes |
| `VIndRestore.argsTypedK_of_sortWitness₁` | 11 | 3342 | yes |

What this does **not** buy at a nested block: `e₁` is `env` plus the block's non-companion type
constants, whose declared types are `Π params indices, Sort D.lvl` — a sort only when the block has
no parameters and the member no indices.  At `ntreeAux` they are `.forallE`s, so the `e₁` form
fails there exactly as the `env` form does; `listEnv₃_not_sortWitness` is that, machine-checked.

## 6. Holes routed through (task (e)): **NONE**

Verified two ways.  `scripts/exists.lean`, over the 424-module built population, was run on the 31
substantive declarations and every one reports `cone reaches sorryAx: false`.  All 36 declarations
are additionally graded by an in-file `#print axioms`, and the build log carries no `sorryAx` for
any of them.  So restating the bypass's side condition has **not** smuggled the strengthening hole
back in through the condition, and the bypass remains a bypass.

Axiom bar `after ⊆ before` holds: the general declarations use `{propext, Quot.sound}`, exactly
`VIndRestore.argsTypedK_of_resultSortInhab`'s set; the concrete `ntree` witnesses use
`{propext, Classical.choice, Quot.sound}`, exactly the set the pre-existing witness
`InductiveDeclExamples.ntreeAux_argsTypedK_of_level` already has.

Zero errors, zero warnings from `lake build Lean4Lean.Verify.Inductive.SortWitEnv`.

## 7. What is not claimed

1. That `VEnv.SortWitness` is *necessary*.  It is sufficient.  §3 refutes only its derivability
   from `RestrictStepCfg`; at `ntreeAux` the bypass still holds, because `D.lvl = .succ (.param 0)`
   makes `StrengthenFamily.lean`'s **first** clause fire.  What fails at `ntreeAux` is this
   clause's premise, not the bypass.
2. That the residue of `StrengthenFamily.lean` §8 is empty.  It is not: for a block whose `D.lvl`
   is `.param i`, with no telescope binder at that level, in an environment with no `Sort u`-valued
   constant, none of the four clauses fires.  The contribution here is that the residue is now
   *exactly* one decidable environment predicate rather than an unstated assumption.
3. Anything about the flip, `tryEtaStructCore.WF`, `isDefEqUnitLike.WF`, or the other twelve holes.
4. No frozen file was read for edit and none was changed; no file outside
   `Lean4Lean/Verify/Inductive/SortWitEnv.lean` and this document was modified.

## 8. Suggested (NOT made) edit to another stream's file

`StrengthenFamily.lean` §8's closing paragraph currently ends "What remains is not a level
condition but an environment one: that the environment at `RestrictStepCfg`'s `e₁`/`e₂` actually
declares such a constant."  That sentence is now answered and could cite
`Verify/Inductive/SortWitEnv.lean`: the condition is `VEnv.SortWitness`, it is **not** implied by
`RestrictStepCfg` at any of the three environments (`not_sortWitness_of_restrictStepCfg₃`, arity 0),
and it is satisfiable at a real configuration of the same nested block
(`ntreeAux_sortWitness_bypass`, arity 0).  `StrengthenFamily.lean` is another stream's file, so no
edit was made.
