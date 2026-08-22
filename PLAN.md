# Plan: proving `Lean4Lean.kernel_sound`

Working document for the campaign toward stop-condition 2 in `CLAUDE.md`.
Goal 1 (Kernel Arena) is **met** as of commit `2f2cc79`: 185 correct, 6 `either`,
0 incorrect.

## The target

```lean
theorem kernel_sound (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment)
    (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰
```

## Route

Three links, composed:

1. **Refinement** (`Lean4Lean/Verify/`). The executable checker accepting a
   declaration list yields a well-formed abstract environment:
   `foldAddDecl fuel (stdPrelude ++ ds) = .ok env` and `ds` axiom-free give a
   `VEnv` with `VEnv.LeanWF`, and `ContainsSafeProofOfFalse env` gives a term
   `e` with `HasType 0 [] e falseProp`. So `¬ leanTTConsistent`.
2. **Consistency of the abstract theory** (`Lean4Lean/Theory/`). `leanTTConsistent`
   holds whenever the metatheory has enough inaccessibles.
3. **Discharge to first-order ZFC** (Foundation). `Entailment.Inconsistent T`
   is `T ⊢ ⊥`, and Foundation's completeness gives it from "T has no model":
   ```
   SetTheory.provable_of_models (T := 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) (φ := ⊥)
     : (∀ M [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰], M↓[ℒₛₑₜ] ⊧ ⊥) → 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ⊢ ⊥
   ```
   then `Entailment.inconsistent_of_provable`. Needs an instance
   `𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, built by `Entailment.WeakerThan.trans` from
   `𝗘𝗤 _ ⪯ 𝗭𝗙𝗖` and `𝗭𝗙𝗖 ⪯ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` (Foundation has no transitivity instance).

   So link 2's real form is: **fix an arbitrary `M ⊧ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` and build the
   Carneiro model of Lean's type theory inside `M`.**

## Design decisions

- **Internal set theory lives in lean4lean, not Foundation.** Foundation is
  pinned and may not be changed without sign-off. `V_α`/rank/inaccessible-closure
  are built in `Lean4Lean/Theory/SetModel/`, importing Foundation's `Z.lean`,
  `Function.lean`, `Ordinal.lean`, `ZF.lean`, `Recursion.lean`.
- **Interpret inductive types directly, not via W-types.** Carneiro §5 reduces
  Lean inductives to eight primitives (`⊥ Σ + ulift ‖·‖ W = acc`), but leaves
  the intro rules, recursors and ι-rules of that reduction explicitly as future
  work (`Wtypes.tex:198`) — it is unwritten mathematics, not transcription.
  Interpreting a general inductive family directly as a least fixed point of a
  monotone operator on `V_κ`, with its recursor by ∈-rank recursion, is known
  mathematics and matches the shape `Theory/Inductive.lean` must specify anyway.
- **Soundness in schema form with an explicit universe bound.** State
  "if the κ-sequence is `k`-correct and every universe index in the derivation
  is `< k`, then …" rather than Carneiro's `∃k`. Each Lean proof mentions
  finitely many levels; the `atLeastInaccessibles n` schema is designed for
  exactly this, and `Entailment.inconsistent_compact` supplies the finiteness.
- Only `Prop`-level formers and `+`/quotients are free; `Π`, `Σ`, and inductive
  formation at level `n` are what consume the `n`-th inaccessible.

## Status of the pieces

### Link 1 — `Lean4Lean/Verify/` (refinement)

Solid: `TrEnv`/`TrConstant`/`TrDefVal`, `TrEnv'.wf`, all of `Environment/Checker.lean`
and `Environment/Extension.lean`, `Verify/Level.lean` (3880 lines, sorry-free),
`Verify/Expr.lean`, six of seven `addDecl` branches, and `inferType`/`isDefEq`/`whnf`
correctness outside the projection/recursor/structure-eta cases.

Open:

| Item | File | Blocked on |
|---|---|---|
| `checkPrimitiveDef.WF` | `Verify/Environment/Boundaries.lean` | nothing — independent |
| `TrProj` (a `sorry` *definition*) | `Verify/Typing/Expr.lean:67` | inductive spec |
| `TrProj.{weak',weak'_inv,defeqDFC,wf,uniq,instN,instL}` | `Verify/Typing/Lemmas.lean` | `TrProj` |
| `reduceRecursor.WF` (ι-reduction) | `Verify/TypeChecker/WHNF.lean:6` | inductive spec |
| `reduceProjCore.WF` | `Verify/TypeChecker/Reduce.lean:145` | `TrProj` |
| `inferProj.WF` | `Verify/TypeChecker/InferType.lean:388` | `TrProj` |
| `tryEtaStructCore.WF`, `isDefEqUnitLike.WF` | `Verify/TypeChecker/IsDefEq.lean` | structure metatheory |
| `AddInduct` (an inductive with **no constructors**) | `Verify/Environment/Basic.lean:105` | inductive spec |
| `addDecl.WF`, `inductDecl` branch | `Verify/Environment.lean:236` | all of the above |

Because `AddInduct` is empty, `TrEnv` provably contains no inductive
(`TrEnv'.no_inductInfo`), which makes `addQuot.WF` and `checkEqType.WF` **vacuous**
today. `stdPrelude` is mostly `.inductDecl`s, so the refinement layer currently
says nothing about it.

Not started: a `foldAddDecl` iteration lemma, and the axiom-free bookkeeping.
`Verify/Soundness.lean` does not even import `Verify/Environment.lean` yet.

### Link 2 — `Lean4Lean/Theory/` (abstract metatheory)

Solid and substantial (~4500 lines): `VExpr`/`VLevel`/`VEnv`, the single
`VEnv.IsDefEq` judgment, `Strong`, `IsDefEq.uniq`, Church–Rosser,
`HeadReduction` (`InferType.exists`/`.determ`).

Open:

| Item | File | Note |
|---|---|---|
| `VInductDecl.WF`, `VEnv.addInduct` — `sorry` **definitions** | `Theory/Inductive.lean` | **the keystone**; the spec of inductive types does not exist |
| `addInduct_WF` | `Theory/Typing/InductiveLemmas.lean` | blocked on the above |
| `IsDefEqU.sort_inv`, `.forallE_inv_stratified`, `.sort_forallE_inv` | `Theory/Typing/Injectivity.lean` | research; circular with Church–Rosser |
| `NormalEq.parRed`, two ι-rule cases | `Theory/Typing/ChurchRosser.lean` | grindy but routine |
| `IsDefEqU.weakN_iff`, forward direction | `Theory/Typing/UniqueTyping.lean:174` | routine-ish strengthening |
| nothing instantiates `VEnv.Params` | — | `addInduct` must produce `Pattern`-shaped ι-rules satisfying the orthogonality axioms |
| `leanTT_equiconsistent_zfc_omega_inaccessibles` | `Theory/Equiconsistency.lean` | the model; only the `→` direction is needed |

`VEnv.WF.ordered` routes through `addInduct_WF`, so every `henv : VEnv.WF env`
downstream is sorry-tainted until the keystone lands.

### Link 3 — the model (not started)

Missing from Foundation and to be built in `Lean4Lean/Theory/SetModel/`:
the cumulative hierarchy `V_α` and rank inside a model, cardinal arithmetic
enough for strong-limit/regular, closure of `V_κ` under `Π`/`Σ`/least fixed
points for inaccessible `κ`, the `U_n` sequence with `U_0 = {∅,{•}}`, a choice
function on `U_ω`, then the interpretation `⟦Γ ⊢ e⟧` by well-founded recursion
on Carneiro's size measure, and soundness by induction on `IsDefEq`.

Foundation does supply: `Ordinal V` with transfinite induction, transfinite
recursion (`Recursion.lean`), replacement gadgets (`ZF.lean`), `CardLE`/`CardLT`,
power set, `ω`, and the definability instances needed to apply separation and
replacement to the formulas we write.

## Order of work

- **Phase A** — close everything independent of the inductive spec:
  `checkPrimitiveDef.WF`, the two `ChurchRosser` cases, `weakN_iff`, and
  investigate whether `Experimental/` resolves the `Injectivity` circularity.
- **Phase B** — the keystone: `VInductDecl.WF` / `VEnv.addInduct`, the `Params`
  instance, `addInduct_WF`, `TrProj`, `AddInduct`, and the `addDecl.WF`
  inductive branch. Unblocks ~13 refinement sorries.
- **Phase C** — wire link 1 to link 2: the `foldAddDecl` iteration lemma and
  `¬ leanTTConsistent` from `kernel_sound`'s hypotheses.
- **Phase D** — link 3: internal set theory, the interpretation, soundness.

Phases A/B/D are largely independent and run in parallel; C is short and waits
on B.

## One flagged edit to a frozen file — needs human sign-off

`Verify/Soundness.lean` imports only `Lean4Lean.Environment` and
`Foundation.FirstOrder.SetTheory.InaccessibleCardinal`. Nothing in that closure
mentions `VEnv`, so `kernel_sound` **cannot be proved without adding an import**
to the frozen file. The endgame therefore requires exactly two changes there:

- add `import Lean4Lean.Verify.Bridge` (the module linking the refinement layer
  to the model), and
- replace the `sorry` in `kernel_sound` with the proof term.

Neither touches the statement: every definition the theorem mentions
(`stdPrelude`, `foldAddDecl`, `Declaration.IsAxiomFree`, `falseExpr`,
`ContainsSafeProofOfFalse`) and the Foundation side stay byte-identical, and the
two build-time adequacy `#eval`s keep passing. Guard checks 1–3 continue to
police the axiom cone. **Do not make this edit until there is a finished proof
to insert, and flag it to the human when you do.**

## Ground rules for contributors

`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are frozen.
No new `axiom`, `sorry` (outside a declared work item), `native_decide`, or
`@[implemented_by]`. No `lake update`, no change to the Foundation pin. Guard
checks 1–3 must keep passing on every commit.
