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
| `checkPrimitiveDef.WF` | `Verify/Environment/Boundaries.lean` | **false as stated** — see below |
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

`Verify/Bridge.lean` (new) now carries the Phase C scaffolding: the `foldAddDecl`
iteration lemma over `addDecl.WF`, the `TrExprS` inversion turning a kernel-level
`∀ p : Prop, p` into a `VExpr`-level proof of `falseProp` (this one is
unconditional), and the export `not_leanTTConsistent_of_kernel_proves_false`. It
mirrors the four definitions from the frozen `Soundness.lean` rather than
importing it, since `Soundness.lean` will eventually import Bridge; the mirrors
are checked defeq to the originals.

Three gaps there are explicit hypotheses rather than sorries:

- `AddDeclWF fuel` — `addDecl.WF` is stated only for `fuel := {}`, but
  `kernel_sound` quantifies over all fuel. Mechanical: everything below
  `Environment/Checker.lean` is already fuel-polymorphic; fuel is pinned only by
  optional-argument defaults in eight lemma statements, ~25 lines across three
  files, no proof bodies change.
- `HasEmptyModel` — **a real defect.** `Kernel.Environment.empty` builds its
  constant map as `{ stage₁ }` with `stage₁ := false`, while `TrEnv'.empty` and
  `Aligned.empty` pin the literal `({} : ConstMap)`, whose `stage₁` defaults to
  `true`. No other `TrEnv'` rule can produce `VEnv.empty` at that map, so
  `∃ ves, ves.WF (Kernel.Environment.empty ‵main)` is underivable today. Fix by
  weakening the two `empty` constructors to any map with `map₁ = ∅ ∧ map₂ = ∅`.
- `PreludeBridge` — blocked on the inductive keystone: `TrEnv'.wf` yields
  `∃ ds, VEnv.WF' ds venv` with no control over the tail, while `VEnv.LeanWF`
  demands the tail be exactly `leanPrelude.reverse`.

#### Workstream: primitive reflection (`checkPrimitiveDef.WF`)

Investigated and found **unprovable as written**, for two independent reasons.

*Beta-redex types.* `VEnv.HasPrimitives` pins a primitive's `VConstant` to a
literal syntactic type (e.g. `Char.ofNat ↦ ⟨0, .forallE .nat .char⟩`), and
`TrConstant` translates `v.type` structurally via `TrExprS`. But the recognizer
in `Primitive.lean` only checks `isDefEq v.type q(Nat → Char)`. Declaring
`Char.ofNat` with type `(fun _ : Nat => Nat → Char) Nat.zero` passes the
recognizer, translates to a structurally different `VConstant`, and refutes
`preserves` — which quantifies over *every* `ci'` with `TrDefVal`, so no proof
can dodge it. `String.ofList` fails the same way. Fix: make those branches
compare `v.type` syntactically.

*Ill-typed pseudo-types.* The 15 `Nat` arithmetic branches establish
`ReflectsNatNatNat`/`…Bool` via `defeq1 a b := isDefEq (.arrow q(Nat) a) (.arrow q(Nat) b)`,
comparing deliberately ill-typed terms to get under a binder. Every spec for
`isDefEq` requires `TrExprS` on both sides, and `TrExprS.forallE` requires the
body to be a type — which `Nat.add x 0` is not. So no `e'` exists and the
hypothesis is unsatisfiable: those checks carry no usable semantic content
through the current interface. Fix: rewrite `defeq1`/`defeq2` with
`withLocalDecl`-bound fvars, as the `Nat.div`/`Nat.mod` branches already do.

Both fixes have landed, along with three further gaps the audit turned up.
`VEnv.HasPrimitives` had no field for `Nat.pred` or `Nat.bitwise` even though the
`Nat.sub` and `land`/`lor`/`xor` branches depend on their semantics; both are now
pinned. `Nat.bitwise` is second order — `Nat.land`'s value is `Nat.bitwise`
applied to a combinator from a later declaration — so the obvious field puts
`ReflectsBoolBoolBool` in negative position and is **not monotone**, which a
`HasPrimitives` invariant must be; the field is relativized to an arbitrary
extension instead. And every arithmetic branch was building `Nat`/`Bool` literals
and depending on other primitives without requiring any of them present; those
are now explicit `env.contains` guards.

What remains is genuinely large: **16** reflection theorems relating the
GMP-accelerated `Nat` operations to their Lean definitions, including
`Nat.div`/`Nat.mod` (fuel recursion through `Nat.modCore.go`) and
`Nat.gcd`/`Nat.bitwise` (`WellFounded.Nat.fix`, `Acc.rec`). `natBitwise` is the
hard one: it quantifies over all extensions, so its proof must use only monotone
facts. Nothing in the repo supports any of this today — `ReflectsNatNat*` is only
ever consumed. Independent of every other workstream, so it can be picked up at
any time.

### Link 2 — `Lean4Lean/Theory/` (abstract metatheory)

Solid and substantial (~4500 lines): `VExpr`/`VLevel`/`VEnv`, the single
`VEnv.IsDefEq` judgment, `Strong`, `IsDefEq.uniq`, Church–Rosser,
`HeadReduction` (`InferType.exists`/`.determ`).

Open:

| Item | File | Note |
|---|---|---|
| `VInductDecl.WF`, `VEnv.addInduct` — `sorry` **definitions** | `Theory/Inductive.lean` | superseded — see `Theory/Inductive/Decl.lean`; the swap into `VDecl` is still to schedule |
| `addInduct_WF` | `Theory/Typing/InductiveLemmas.lean` | blocked on the above |
| `IsDefEqU.sort_inv`, `.forallE_inv_stratified`, `.sort_forallE_inv` | `Theory/Typing/Injectivity.lean` | route found — see below |
| `NormalEq.parRed`, the `appDF` × `extra` case | `Theory/Typing/ChurchRosser.lean` | needs two new `Params` axioms — see below |
| `IsDefEqU.weakN_iff`, forward direction | `Theory/Typing/UniqueTyping.lean:174` | routine-ish strengthening |
| nothing instantiates `VEnv.Params` | — | `addInduct` must produce `Pattern`-shaped ι-rules satisfying the orthogonality axioms |
| `leanTT_equiconsistent_zfc_omega_inaccessibles` | `Theory/Equiconsistency.lean` | the model; only the `→` direction is needed |

`VEnv.WF.ordered` routes through `addInduct_WF`, so every `henv : VEnv.WF env`
downstream is sorry-tainted until the keystone lands.

#### `Params` and `Pattern` need redesigning — this is part of the keystone

Three separate findings say the same thing: the `VEnv.Params` / `Pattern`
abstraction as it stands cannot describe real ι-rules.

*`extra_pat` is unsatisfiable.* `VDefEq.lhs` as built by the `vdefeq(...)`
elaborator is a lambda-abstracted closed term — `Theory/Quot.lean`'s `quotDefEq`
is `fun α r β f c a => Quot.lift … (Quot.mk r a)` — but `Pattern.Matches` only
matches `.const`/`.app` spines and never sees through a `.lam`. So no `Params`
instance can exist for any environment containing an iota or quot rule, which is
why none exists in the repo. Either `VDefEq` moves to applied form (rule
variables as pattern metavariables) or `Matches` learns to see through the
abstraction; `quotDefEq` has to be re-encoded either way.

*Two axioms are missing.* The remaining `NormalEq.parRed` case needs (a) the
major premise of a recursor pattern to have a type not defeq to a `forallE`,
which excludes the `etaL` case — a lam only parallel-reduces to a lam, and an
inductive type is never a Π-type; and (b) small elimination: if the major premise
is a proof then the whole redex is a proof, which is the real `Acc.rec` /
`Quot.lift`-over-a-Prop case. Both are facts about the inductive *declaration*
that the `Pat` abstraction hides. Carneiro's corresponding proof uses exactly
these two, one silently.

*The consequence for phasing.* `addInduct` must not merely produce ι-rules — it
must produce ones that provably satisfy the `Params` axioms including these two.
That is now part of the keystone's acceptance criteria, and it is why
`ChurchRosser.lean` and `HeadReduction.lean` are vacuous today.

#### Workstream: injectivity

The circularity is real: `ChurchRosser.lean` uses the three injectivity
statements 12 times directly and 23 more through `IsDefEq.uniq`, so they cannot
be corollaries of `IsDefEq.church_rosser`. Two other routes are ruled out.
Re-stratifying to Carneiro's `⊢_n` would mean re-indexing ~2300 lines of
finished proof: the repo's `HasTypeStratified` indexes typing-derivation
*height*, whereas Carneiro's index counts alternations on the conversion
judgment, which is what makes `thm:0dinv`/`thm:1dinv` go through. And porting
the logical relation to `VExpr` would reintroduce the level congruences that
`SLevel` exists to kill.

The viable route is the shape model already in `Experimental/`.
`Experimental/ShapeLogRel.lean` (6100 lines) is **fully proved** — its `sorry`
hits are inside a dead block comment — and `ShapeLogRelAdequacy.lean` proves all
three injectivity statements for `SExpr`, a copy of `VExpr` with semantically
quotiented levels and a heterogeneous `trans'` rule. Commit `84f2b04`
("Finished injectivity! 🎉") is that work; it never reached the mainline because
**there is no `SExpr ↔ VExpr` bridge**.

`sort_inv` and `sort_forallE_inv` need only the *forward* translation
`VExpr → SExpr`, since their conclusions are `u ≈ v` and `False`. Only
`forallE_inv_stratified` needs the reverse reflection; `trans'`-elimination for
it is already proved (`Experimental/UniqueTyping.lean:261`), leaving a
representative-choice induction.

Two things this changes elsewhere. `Experimental/SExpr.lean` has 25 open
declarations and 1 axiom that the bridge may need. And `LR.adequacy`'s `const`
case needs `Params.ctor_ty` — so **injectivity is not independent of the
inductive-spec keystone** after all, and Phase A cannot fully close without
Phase B.

Also worth noting: `Params` is uninstantiated on *both* sides, and the two
`Params` classes differ. Until `addInduct` supplies an instance,
`ChurchRosser.lean` and `HeadReduction.lean` are vacuous.

### Link 3 — the model

`Lean4Lean/Theory/SetModel/` is ~3200 lines, sorry-free, all internal to an
arbitrary `V` with `[SetStructure V] [Nonempty V] [V ⊧* 𝗭𝗙]` — so it applies to
whatever model Foundation's completeness theorem hands us.

- `Rank.lean` — transfinite recursion repackaged as a usable function, `Vset`,
  membership induction (which needed a transitive closure built from scratch),
  rank, and the closure lemmas that need no large cardinal.
- `Inaccessible.lean` — Foundation's inaccessible-cardinal formulas reflected
  into Lean predicates with `Defined` instances, `exists_inaccessibleChain`
  turning `M ⊧ atLeastInaccessibles n` into usable objects, and Π/Σ closure with
  strong-limitness and regularity each spent in exactly one place.
- `Universe.lean` — the `U_n` sequence, `propext`, impredicativity (free: no
  large cardinal, no limit ordinal, only `𝗭`), an internal choice function, and
  the equivalence closure and factorization that `Quot` needs.
- `Inductive.lean` — inductive families as least fixed points, with injective
  constructors, no junk, no confusion, the recursor built as an internal graph
  (external well-founded recursion is unavailable: a model of ZF need not be
  externally well-founded), and the ι-rule.
- `Cardinal.lean` — full replacement inside `V_κ`.

What remains: the carrier's closure-ordinal argument (bounded, ordinary work),
and then the interpretation `⟦Γ ⊢ e⟧` itself — which needs Carneiro's proof
splitting, hence the `lvl`/`sort` functions, hence unique typing, and so waits on
the injectivity and keystone streams.

Foundation's own gaps found along the way are written up in
`docs/foundation-gaps.md`.

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

## The critical path, as it now stands

The model side defined the interpretation without needing Carneiro's size
measure — `VExpr` has no `let`, and the constant assignment is a parameter rather
than something to unfold, so the recursion is structural. That narrowed the
endgame to a single chain:

> the keystone's `addInduct'` metatheory → a `VEnv.Params` instance →
> `IsDefEqU.sort_inv` → the level assignment → the interpretation,
> unconditionally → soundness → `leanTTConsistent` → `kernel_sound`.

`sort_inv` is the pivot. It is **the only one of the three injectivity statements
the interpretation needs** — `forallE_inv` and `sort_forallE_inv` bite later, in
soundness's congruence cases — and it is already proved on the shape-model side
relative to a `Params` instance. So the two things gating everything are the
keystone and the shape model's own frontier.

## Progress log

Landed since the plan was written:

- `Verify/Bridge.lean` — the Phase C scaffolding. `HasEmptyModel` and
  `AddDeclWF fuel` are proved; `PreludeBridge` is the only remaining hypothesis,
  blocked on the keystone.
- `Theory/SetModel/Rank.lean` — cumulative hierarchy, membership induction,
  transitive closure, rank, and the no-large-cardinal closure lemmas, inside an
  arbitrary model of ZF. 560 lines, sorry-free.
- `Theory/Typing/ChurchRosser.lean` — the `constDF` × `extra` case of
  `NormalEq.parRed`.
- `Experimental/Bridge.lean`, `Experimental/BridgeInjectivity.lean` — the forward
  `VExpr → SExpr` simulation, and `sort_inv` / `sort_forallE_inv` for `VExpr`
  relative to a `Params` instance.
- `docs/design-inductive.md` — the keystone specification.
- `Theory/Inductive/Decl.lean` + `DeclExamples.lean` — **the keystone itself**.
  The structured `VInductDecl'`, its `WF` staged as the kernel stages its checks,
  and `VEnv.addInduct'` with the recursor types and ι-rules written out.
  Validated against ground truth rather than against the design: the real
  recursor is elaborated with `type_of%`, translated, and compared for syntactic
  equality. `Eq`, `Nat`, `Acc` and a mutual `Tree`/`Forest` block all come out
  identical to Lean's own, argument order included. That validation caught a real
  bug — stored telescopes live at the block's universe numbering but get spliced
  into terms at the recursor's, so with `isLE` every `.param i` shifts by one.
  The C++ kernel is immune because its universe parameters are names, not
  indices.

The keystone is now **wired in**: `VDecl.induct` carries the structured record,
`Theory/Inductive.lean` and its two `sorry`ed definitions are deleted, and the
prelude literals in `Consistency.lean` are re-expressed and checked against
Lean's own declarations by `rfl`. `Nonempty` turned out to be the repo's first
small-eliminator — its large-elimination condition genuinely fails and its
recursor takes one universe parameter rather than two — a case no existing
validation had exercised.

Still to schedule for the keystone: `addInduct_WF`, now reduced to exactly two
obligations (`onCtxMinors` and `iotaRule_WF`); the `Params` instance; `TrProj`;
and `AddInduct`'s constructors.

- `Theory/SetModel/Inaccessible.lean` — Foundation's inaccessible-cardinal
  formulas reflected into Lean predicates with `Defined` instances,
  `exists_inaccessibleChain`, Π/Σ closure with the hypotheses split finely, and
  least fixed points. 706 lines, sorry-free.
- `Theory/Inductive/Telescope.lean` — the telescope algebra the keystone is built
  on. 894 lines, sorry-free.
- `Primitive.lean` — both refutations of `checkPrimitiveDef.WF` closed; arena
  unchanged at 185/6/0.
- `Experimental/` — `SExpr.Params.extra_pat` moved from a standalone `axiom` into
  a `ParamsExtra` class, so there are now zero axioms under the `Lean4Lean`
  namespace in that cone.

Three statements have been found **false, not merely unproved**, each with a
machine-checked refutation. `checkPrimitiveDef.WF` (twice, both now fixed);
`∃ ves, ves.WF (Kernel.Environment.empty ‵main)` (the SMap stage flag, fixed);
and `SExpr.IsDefEq.strong`, which lacks the `Ctx.WF Γ` hypothesis its `VExpr`
analogue carries — `IsDefEqStrong.bvar` demands the looked-up type be a type
while `IsDefEq.bvar` assumes nothing about the context. A fourth is open:
`VEnv.HasPrimitives` has no field for `Nat.pred` or `Nat.bitwise`, yet the
`Nat.sub` and `Nat.land`/`lor`/`xor` branches of the recognizer depend on their
semantics, so an environment defining `Nat.pred := fun _ => 0` satisfies
`HasPrimitives` and still passes the `Nat.sub` check.

A fourth statement was found **under-hypothesised rather than false**, and the distinction
is worth keeping: `VEnv.Params.pat_wf` quantified over an arbitrary `Γ` with no
`OnCtx Γ (env.IsType univs)`, while both routes to proving it — `HasType.app_inv` and
`IsDefEq.uniq` — require a well-formed context. It is very likely *true* (an ill-formed `Γ`
only lets `bvar` carry junk types), but was unprovable by any route in the tree. Its only
consumer already had `hΓ` in scope, so the hypothesis was added at zero cost.

That is the same structural defect as `SExpr.IsDefEq.strong`, which *was* false for exactly
this reason. Twice is a pattern: **a rule stated about an arbitrary `Γ` with no
well-formedness hypothesis should be treated as suspect by default on this project** — check
whether the `VExpr` analogue carries `Ctx.WF Γ` / `OnCtx Γ` before trying to prove it.

The lesson is worth stating: on this project, when a statement resists proof, the
first hypothesis should be that it is false. Four of the harder-looking sorries
turned out to be.

## Ground rules for contributors

`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` are frozen.
No new `axiom`, `sorry` (outside a declared work item), `native_decide`, or
`@[implemented_by]`. No `lake update`, no change to the Foundation pin. Guard
checks 1–3 must keep passing on every commit.
