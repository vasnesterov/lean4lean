# handoff: is the `ValStrengthen` instance family weaker than the strengthening hole?

**Owner file**: `Lean4Lean/Verify/Inductive/StrengthenFamily.lean` (new).
Written incrementally; the Lean is the record, this file is the map.

## §0 The question

`Lean4Lean/Verify/Inductive/RestrictStep.lean` reduced the nested restriction step to one
judgement,

    restrictStep_entry : D.ArgsTypedK K e₁ occ  ↔  R.ValStrengthen D K e₂ e₁

and located `ValStrengthen` as a *plain instance* of `VEnv.AxiomConservativityWF`
(`Lean4Lean/Theory/Typing/ConstVar.lean:478`, arity 2, cone 362, hole-free), which
`VEnv.axiomConservativityWF_iff_target` (ConstVar.lean:586) proves **equivalent** to
`VEnv.StrengtheningTarget` — one of `UniqueTyping.lean`'s thirteen holes.

RestrictStep.lean §2 left open: *is the instance family strictly weaker than the general
statement?*  That is this file's question.

**Name resolution (done first, per the standing rule).**  The brief's guess
`Lean4Lean.AxiomConservativityWF` is indeed NOT FOUND; the real name is
`Lean4Lean.VEnv.AxiomConservativityWF`.  Confirmed with
`NAMES="…" lake env lean --run scripts/exists.lean`.

## §1 Answer, up front

**The family is strictly cheaper, and the reason is sharp: the family only ever needs the
*inhabited* case of axiom conservativity, and the inhabited case is provable outright.**

`ConstVar.lean` itself proves `axiomConservativityWF_iff_uninhabWF`: the general statement is
equivalent to its restriction to axioms *with no inhabitant*.  So all the content of the hole
sits in the uninhabited case.  The companion constants that `ValStrengthen` has to drop are the
type constants of inductive members — `Π params indices, Sort D.lvl` — and those are inhabited
whenever `Sort D.lvl` is inhabited over the member's own telescope.  Substituting *any*
inhabitant (not the intended `R.tyVal D j`) discharges the whole family through
`VEnv.IsDefEq.substC`, with **no hole and no `PiInv`**.

(Details, statements and cone sizes: filled in below as each lands.)

## §2 What is in the file (all hole-free unless marked)

`Lean4Lean/Verify/Inductive/StrengthenFamily.lean`, 618 lines, **zero build warnings**,
34 declarations, `#print axioms` for every theorem in §7.  Cone sizes from
`scripts/exists.lean` (population 418 modules).

### (a) The family, as its own definition

| decl | arity | cone | sorryAx |
| --- | --- | --- | --- |
| `VIndRestore.StrengthenFamily` | 0 | 761 | no |
| `VEnv.ClosedConservativeStep` | 3 | 37 | no |
| `VInductDecl'.CompanionVals` | 5 | 8 (structure) | no |
| `VInductDecl'.ResultSortInhab` | 3 | 48 | no |

`StrengthenFamily` is `VIndRestore.ValStrengthen` quantified over every `RestrictStepCfg`
(empty context, one `addConstList`, per companion member) — the instance shape RestrictStep.lean
described in prose, now an object.  `ClosedConservativeStep e₂ e₁ U` is its general parent for
that pair of environments: closed, typed conservativity with clean endpoints.

### (b) The family FROM the general statement — and this leg is NOT hole-free

* `VIndRestore.valStrengthen_of_closedStep` (arity 10, cone 1351, hole-free): the family from
  `ClosedConservativeStep`, a plain instantiation, using RestrictStep's
  `valStrengthen_endpoints_clean` for the side condition.
* `VEnv.closedConservativeStep_of_axiomConservativityWF` (arity 11, cone 3518,
  **reaches `sorryAx` via `VEnv.IsDefEqU.forallE_inv_stratified`**): one added constant, from
  `VEnv.AxiomConservativityWF`.

**Measurement worth keeping.**  `AxiomConservativityWF` is a statement about `IsDefEqU`, so it
loses the type; recovering the *typed* judgement the family needs goes through
`VEnv.IsDefEq.uniqU` (cone 3474, tainted by `forallE_inv_stratified`).  So *as stated*, the
general statement does not imply the family without a **second** hole.  Also unproved: presenting
`e₂` as an `addConst` chain above `e₁` needs a reordering lemma for `addConstList`
(`D.typeConsts` is an interleaving of `D.typeConstsC K` with the companion entries, not an
append); `VEnv.ClosedConservativeStep.comp` is the composition step such a chain would feed.

### (c) The family PROVED — the headline

The route: adding constants whose declared types are **inhabited at the smaller environment** is
conservative, by replacing each constant with an inhabitant.  `VEnv.IsDefEq.substC` is the only
transport; no `PiInv`, no `HasArgs.of_mkApp`, no strengthening hole.

| decl | arity | cone | sorryAx |
| --- | --- | --- | --- |
| `VInductDecl'.CompanionVals.csubst_WF` | 10 | 2537 | no |
| `VIndRestore.valStrengthen_of_companionVals` | 11 | 2749 | no |
| `VIndRestore.argsTypedK_of_companionVals` | 11 | 3310 | no |
| `VInductDecl'.junkVal_hasType` | 7 | 116 | no |
| `VInductDecl'.companionVals_junk` | 10 | 1176 | no |
| `VInductDecl'.resultSortInhab_of_succ` | 6 | 606 | no |
| `VInductDecl'.resultSortInhab_of_zero` | 4 | 627 | no |
| `VInductDecl'.resultSortInhab_of_lookup` | 4 | 53 | no |
| **`VIndRestore.argsTypedK_of_resultSortInhab`** | 11 | **3333** | **no** |
| **`VIndRestore.argsTypedK_of_succLevel`** | 13 | **3335** | **no** |

The last two give `R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ` — node 5 *and* node 1 of
RestrictStep's five-node cycle — from the configuration, the free datum at `e₂`, and one premise
about the block's **result sort**.

**Stated as asked: this is a bypass of `Theory/Typing/UniqueTyping.lean:193` (the forward
direction of `VEnv.IsDefEqU.weakN_iff`) for the nested restriction step, at every block whose
result sort is inhabited over its members' telescopes** — which includes every block whose result
level is `≈`-a-successor, i.e. every non-`Prop` block Lean emits.  Nothing in the file attacks
`weakN_iff`; the stream owning `Theory/Typing/WeakNForward.lean` is unaffected.

### (d) Why the family is cheaper, in one sentence

`VEnv.axiomConservativityWF_iff_uninhabWF` (`Theory/Typing/ConstVar.lean`) proves the general
statement is *equivalent* to its restriction to axioms with **no inhabitant**.  All of the hole's
content is in the uninhabited case; the constants `ValStrengthen` drops are inductive members'
type constants, definitionally `Π params indices, Sort D.lvl` (`VIndType.canonType`, reached from
the stored type by `VIndType.WF.canon`, never by inverting a Π), and those are inhabited.

### (e) Was RestrictStep.lean §3a's hole-free instance special?

Not in the way that mattered, and not for the reason it looked like.  §3a discharges its instance
by `type_tac` on the concrete spine `List.{u} (NTree.{u} #0)`, which reads as an accident of a
small witness.  The general reason the family is cheap is different: **the value being moved never
has to be the intended `R.tyVal D j`.**  `InductiveDeclExamples.ntree_junkVal_ne_tyVal` (cone 799,
hole-free, by `decide`) makes that machine-checked at the parameterised witness — the substituted
value is `λ (α : Type u), Sort u`, containing no member constant, where `ntreeVal` is
`λ (α : Type u), List.{u} (NTree.{u} α)`.  This is exactly why the route escapes
`RestrictCompanion.lean` §3's sandwich: that sandwich is a statement about `R.csubstTy D K`, and
`R.csubstTy D K` is not the substitution used.

### (f) Vacuity control (working rule 4) — at `ntreeAux`, not at a degenerate block

`ntreeAux` (`Theory/Inductive/NestedHead.lean:624`): `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `lvl = .succ (.param 0)`, the parameterised nested block
Lean's own kernel runs nested elimination on.  Deliberately not `nfnAux`, which is degenerate
(`uvars = 0`, `params = []`).

* `InductiveDeclExamples.ntreeAux_resultSortInhab` (cone 606, hole-free): the premise, by
  `decide` on the level plus reflexivity.
* `InductiveDeclExamples.ntreeAux_argsTypedK_of_level` (arity 0, cone **4155**, hole-free):
  existentially closes the staging and exhibits, at one witness, the configuration, the datum at
  `e₂`, the `CompanionVals`, node 5 and node 1.  Nothing hypothesised.
* `InductiveDeclExamples.ntree_junkSubst_dom_val` (hole-free, `decide`): the substitution's
  domain is **not** empty at the witness — `_nested.List_1 ↦ λ (α : Type u), Sort u`.  A
  `CompanionVals` with an everywhere-`none` `σ` would make §2's transport the identity and the
  discharge worthless; it is not that.

The antecedent of `ValStrengthen` itself is satisfiable at the same witness — that is
RestrictStep.lean's `ntreeAux_valStrengthen_nonvacuous`, unchanged and re-used, not re-proved.

## §3 What is NOT claimed

1. **No equivalence to the premise.**  `ResultSortInhab` is *sufficient*; no reverse implication
   is proved.  The task asked for an `↔` if one existed and there is none: a block could satisfy
   the family for other reasons.  So the residue below is a residue of *this route*, not a lower
   bound on the family.
2. **The residue.**  A block whose `D.lvl` is neither `≈ .succ _` nor `≈ .zero` **and** which has
   no binder of its own telescope at level `D.lvl` — e.g. a closed `inductive T : Sort u`.  §8 of
   the Lean file records the normal-form argument for why `Sort (.param i)` has no closed
   inhabitant, explicitly marked **informal and not machine-checked**.
3. **Nothing about the flip**, `tryEtaStructCore.WF`, `isDefEqUnitLike.WF`, or the other twelve
   holes.  No `Verify/Soundness.lean` / `Axioms.lean` / `Guard.lean` was read for edit, and no
   frozen-file edit is proposed.
4. `ResultSortInhab` quantifies over *every* member rather than only the companions.  Narrowing it
   to `T.name ∈ K` is free; it was not done because all three discharge clauses are uniform in `T`.

## §4 One-line summary for the orchestrator

The family is **not** as strong as the general statement: it is discharged outright, hole-free,
`PiInv`-free, from a level-only side condition, because it only ever needs the *inhabited* case of
axiom conservativity — and `ConstVar.lean` already proves the general statement's whole content
sits in the *uninhabited* case.  `VIndRestore.argsTypedK_of_succLevel` (cone 3335, hole-free) is
the bypass of `UniqueTyping.lean:193` for the nested restriction step at every non-`Prop` block.
The one leg that *is* tainted is the uninteresting one: deriving the family *from* the general
statement needs `IsDefEq.uniqU`, hence a second hole.
