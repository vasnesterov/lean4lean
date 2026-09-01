> **CORRECTION (2026-08-30, machine-checked — this document is stale in two ways).**
>
> **1. The syntactic import is not two statements, it is three.** Measured:
> `PropTypeAgree ∧ PropUniq ∧ InstDescendUp`. `Stable` was never audited when this
> document was written; `Theory/SetModel/StableAudit.lean` later showed
> `propSplitOf_stable_iff : Stable ↔ PropDescend`, i.e. **`Stable` is also a statement
> about the judgement**, so listing it as "standing" measured the wrong object.
>
> **2. The dependence on strengthening was never in the interface.** It sat in
> `propSplitOf`'s *choice of predicate*. `Theory/SetModel/PropSplitUp.lean` closes that
> predicate under lifts and proves **both `lift` fields of `Stable`, both directions**,
> plus both **ascent** halves of the `inst` fields — with no strengthening statement
> anywhere. `prop_sound`/`proof_sound` survive from the same two inputs, because typing
> transports forward along a lift. What remains is `InstDescendUp` (substitution
> *descent*), which is blocked on `IsDefEqU.sort_forallE_inv` — **not** on strengthening.
>
> The trade is exact, not merely favourable: collapsing the new predicate back to the
> canonical one is proved **equivalent** to the two fields the old route derived from
> the hole. And the two predicates agree on **every well-typed input** — they differ
> only on syntax with no sort at `Γ`, the region `Stable` quantifies over and
> `prop_sound` does not.
>
> Everything below predates all of that. Read it for the construction, not for the
> ledger.

> **UPDATE (2026-09-01, machine-checked, sorry-free).** Two model-side items moved, and
> **neither is the `PropSplit env 0` with `Stable` that this document tracks** — that one is
> untouched and is now the *only* thing left between the recursion and `CoherentOn` at the
> one list where everything else is discharged.
>
> **1. Input A is gone.** `Theory/SetModel/ModelExists.lean`'s `modelExistsInput` proves
> `InaccChainOmega.ModelExistsInput` from Foundation — `Theory.small_satisfiable_of_consistent`
> (which is `Satisfiable.{0}` for `ℒₛₑₜ : Language.{0}`, so the model lands in `Type 0` with
> no `ULift`), `QuotNormalize` to make `=` real, and `𝗘𝗤 ℒₛₑₜ ⊆ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` to form it. Hence
> `inaccModelInput : InaccModelInput` is a theorem and
> `upper_bound_of_modelFits (hB : ModelFitsLeanInput) : Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 →
> leanTTConsistent` — the whole model side on **one** input. Bounded both ways:
> `consistent_of_setModel` (soundness converse) makes the consistency-free form of the input
> *equivalent* to `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, and `not_forall_model_false` is the Row-24 check
> that the class of models it binds over is inhabited rather than empty.
>
> **2. The `.induct` residual has a positive witness at a `WF`, reachable block.**
> `Theory/SetModel/InductOracleWitness.lean`'s `inductOracleOK_zero` proves **both** fields
> of `InductOracleOK` at `InductOracleAudit.lean`'s `boxDecl`
> (`inductive Box (e : Ext) : Prop | mk`, `VInductDecl'.WF` over `extEnv`, on the certified
> history `boxDecl_history`), and `oracleFits_zero` extends it to the whole list. So
> `coherentOn_zero` gives `CoherentOn` there with **no oracle obligation left** — the
> remaining hypotheses are exactly `L.Stable`, `CtxInvariant` and `env ≤ envF`. Read the
> bound with its limitation: the oracle is `fun _ _ ↦ ∅`, making `axiom Ext : Prop` false in
> the model, so every declared type is a `∀` over an **empty** domain. What is still open is
> `consts` at a `WF` block whose parameter and index domains are *inhabited*.
>
> The three enabling lemmas are worth reusing and carry **no typing hypotheses**:
> `mkLam_eq_empty_of_empty`, `interp_lam_of_empty_dom` (`⟦λ x : A, b⟧ = pt` when `⟦A⟧ = ∅`)
> and `pt_mem_interp_forallE_of_empty_dom` (`pt ∈ ⟦∀ x : A, B⟧` when `⟦A⟧ = ∅`). Both
> branches of each `interp` clause are taken directly, because `L.IsProof` / `L.IsProp` are
> decidable syntactic predicates; and `pt = ∅` (`Universe.lean:53`) makes the propositional
> witness and the empty function the same element, so no case split leaks outward.

> **UPDATE (2026-09-01, machine-checked, sorry-free): the empty-domain limitation is
> lifted, and the frontier is `isLE`, not `Prop`.**
> `Theory/SetModel/UnitOracleWitness.lean` proves `inductOracleOK_unit` at
> `unitDecl = inductive Unit1 : Prop | mk`, `VInductDecl'.WF` over **`VEnv.empty`**
> (`unitDecl_WF` — no ambient constant is needed) on the one-declaration history
> `unitDecl_history`, with the oracle `Unit1 ↦ {•}` and everything else `↦ •`.
> `oracleFits_unit` extends it to `[.induct unitDecl]`.
>
> Nothing here is empty and nothing is vacuous, and that is checked:
> `unitDecl_params_nil` / `unitTy_indices_nil` (there is no telescope to empty),
> `interp_Unit1_ne_empty`, `exists_true_motive` (an `f ∈ ⟦Unit1 → Prop⟧` with `f ‘ • = {•}`,
> hypothesis-free) and `exists_nonempty_minor_domain`. `Above`-free at an arbitrary `κ`:
> `mem_interp_consts_unit`, `defEq_rules_unit`.
>
> **The forecast above was wrong on one point.** It said this case needs a real `mkLam`, i.e.
> `IndInterp.lean`. It does not. `unitDecl.isLE = false`, so the *whole* of `recType 0` is a
> proposition and `interp` takes the impredicative `mkForallProp` branch at every binder; the
> oracle can hand `Unit1.rec` the value `•`, and the ι-rule's two sides are both `•` because
> their bodies are proofs. Three `mem_interp_forallE_prop_iff` steps and
> `eq_empty_or_eq_true_of_mem_UProp` close it.
>
> **The large eliminator was the next open case, and it is now closed.** Real Lean declares it
> for `Unit1` and `VInductDecl'.WF` permits it (`unitDeclLE_LECond`, vacuous because the
> constructor has no fields). At `isLE := true` the recursor gains a universe parameter, and
> for `u.eval ls ≠ 0` the innermost binder takes `mkForallType`, where `•` is not a legal value
> (`pt_not_mem_mkForallType_of_nonempty`). `Theory/SetModel/UnitOracleLarge.lean` supplies the
> three-layer `mkLam` nest and the ι-rule's β-computation: `inductOracleOKL`, `oracleFitsL`,
> `oracleFitsL_at_consumer`.

> **UPDATE (2026-09-01, machine-checked, sorry-free): the large eliminator.**
>
> * **`u.eval ls = 0` is a separable slice and it is free** (`pt_mem_interpL_recType_of_zero`,
>   `interpL_unitRule_sides_of_zero`): large elimination *into `Prop`* collapses to the small
>   case, so the genuine residual is the `≠ 0` slice alone. Both slices are non-empty cases
>   (`exists_eq_zero_level`, `exists_ne_zero_level`).
> * **The ι-rule still closes with a functional recursor value** (`interpL_unitRule_eq_of_ne`).
>   The computational core is `recFnL_beta : ((recFnL κ n ‘ f) ‘ m) ‘ • = m`.
> * **The oracle's level branch is forced** (`pt_not_mem_interpL_recType_of_ne`): no
>   level-uniform value works for a large eliminator. The hypothesis "given any inhabitant of
>   the motive space" is load-bearing — a junk `κ` with `U κ n = ∅` collapses `recFnL κ n` to
>   `∅ = •`. **No `κ` is chosen.**
> * **It did not need `IndInterp.lean`** — the second forecast this pair of files corrected.
>   Four reusable, `interp`-free lemmas carried it: `mem_mkForallType_of_graph`,
>   `mkLam_mem_mkForallType_of_dom` (domains need only *agree at the valuation*;
>   `InterpSound.mkLam_mem_mkForallType` demands the same term, impossible when one side is the
>   oracle and the other `interp`), `mkForallType_singleton_const`
>   (`⟦Unit1 → Sort u⟧ = U_n ^ {•}`) and `mkLam_ext`.
> * `Above`-free at an arbitrary `κ`, both fields, both slices: `mem_interp_constsL`,
>   `defEq_rulesL`.
> * **What is open now** is a block with **recursive fields** (the least fixed point,
>   `SetModel/IndInterp.lean`) or with parameters/indices; `unitDecl`/`unitDeclLE` have neither.
>
> **Cost of the `hle`.** Every branch decision is read off a typing derivation in `unitEnv`
> through `isProp_iff`/`isProof_iff`, so the theorems carry `hle : unitEnv ≤ envF` — the same
> hypothesis `QuotInterp.lean` carries. It is free: `coherentOn_cnstOf` threads `env ≤ envF`
> at every step and at `[.induct unitDecl]` that `env` **is** `unitEnv` (`eq_unitEnv_of_wf'`),
> so `oracleFits_unit_at_consumer` has no `hle` in its statement.

> **UPDATE (2026-09-01, machine-checked, sorry-free).** The 2026-08-30 correction above
> listed the import as `PropTypeAgree ∧ PropUniq ∧ InstDescendUp` on the strength of
> `PropSplitUp.exists_stable_propSplitUp`. **That was one step ahead of the chain**, and the
> missing step is now supplied. `ModelFits` fixes *one* `L` for all its components, and the
> tree's only producer of the relation slot (`AboveAudit.ctxAgreeRd_propSplitOf`) was proved
> for `propSplitOf` alone — `exists_stable_propSplitUp` says nothing about its `L`'s relation
> slot, and `R := Eq` fails the pairing hypothesis. So the only route into `ModelFits` still
> took `PropDescend 0`.
>
> `Theory/SetModel/PropUpFits.lean` closes it: `Ctx.Lift'.split_mid` (a lift splits at a
> marked context entry, and everything above the entry is independent of it — pure de Bruijn
> bookkeeping) gives `ctxAgreeRd_propSplitUp`, hence
>
>     modelFits_of_propSplitUp_inputs :
>       env.Ordered → env.PropUniq 0 → env.PropTypeAgree 0 → env.InstDescendUp 0 →
>       OracleFits (propSplitUp env 0 henv hU hT) κ ls o ds → ModelFits κ env ds
>
> and `modelFits_of_agree_instDescendUp` with `PropUniq` discharged from `hfalse`.
> `OracleFits`' witnesses transfer unchanged: `InductOracleWitness.oracleFits_zero` is stated
> for an arbitrary `L`.
>
> The trade is bounded **both ways**: `propDescend_iff_instDescendUp` proves
> `PropDescend nv ↔ SortLiftDescend nv ∧ ProofLiftDescend nv ∧ InstDescendUp nv`, so the only
> difference between the old and new top-level reductions is the two strengthening-shaped
> `lift` fields. Both fields of `InstDescendUp` are exhibited separately, at one substitution
> that really substitutes. `InstDescendUp env 0` remains **open**, and it is not shown
> *strictly* weaker than `PropDescend` — no separating environment is exhibited.

# The syntax ↔ set-theory boundary

Specification of the interface between `Lean4Lean/Theory/` (the abstract syntax
and its judgements) and `Lean4Lean/Theory/SetModel/` (the ZFC model). Written
from the model side, because the constraints below are what the model can
actually consume; neither side can design this boundary alone.

The model side is complete apart from the interpretation itself. Everything
cited here is proved, sorry-free, in `SetModel/`.

> **Standing label, and it must travel with every result quoted from here.**
> The interpretation is parameterised by `PropSplit` (§5), and **nothing in the
> tree exhibits one.** Its residual syntactic import is now **one** statement,
> `PropTypeAgree` (§7 — `PropUniq` is discharged from the consistency
> hypothesis the goal itself supplies), and `PropTypeAgree` remains **open**.
> Everything below is proved *against* that parameter and stays valid, but a
> completed `.induct` is **not** an unconditional result, and should not be
> reported as one. Narrowing two parameters to one narrows the conditional; it
> does not remove it.

Throughout:

```lean
variable {V : Type*} [SetStructure V] [Nonempty V]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)
```

`hκ` comes from `exists_inaccessibleChain` (`SetModel/Inaccessible.lean`), which
turns the `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` axiom schema into `n` internal inaccessibles
`κ 0 ∈ κ 1 ∈ … ∈ κ (n-1)`. `U κ i` (`SetModel/Universe.lean`) is the universe
sequence: `U κ 0 = UProp = ℘ {•}`, `U κ (i+1) = vsetV (κ i)`.

---

## 1. Definability is designed in, not added later

**This is the binding constraint.** Every set the model builds comes from `sep`
or `repl`, and both demand an `ℒₛₑₜ`-formula. There is no escape hatch: a Lean
function `V → V` that is not first-order definable cannot be separated or
replaced along, so it cannot participate in any construction that produces a set.

Therefore the interpretation must never be presented as a bare Lean function.
Every syntactic former's interpretation is a **bundle**:

```lean
structure DefFun (V : Type*) [SetStructure V] where
  toFun : V → V
  definable : ℒₛₑₜ-function₁[V] toFun
```

and likewise `DefFun₂`, `DefFun₃`, `DefFun₄` for the higher arities. Concretely,
what the model consumes for a term `e` in a context of length `m` is

```lean
interp : VExpr → (levels : ℕ → ℕ) → DefFunₘ V
```

not `VExpr → (ℕ → ℕ) → (Fin m → V) → V`.

Three consequences worth stating explicitly, because they shape the syntax side's
code rather than just its statements:

* **Composition must stay inside the bundle.** `Language.DefinableFunctionₖ.comp`
  gives closure under composition for `k ≤ 5`; beyond that, curry through
  Kuratowski pairs. Note the tactic gap: `definability` only knows arities 1–3
  out of the box (see `docs/foundation-gaps.md` §1); `SetModel/Inductive.lean`
  registers 4 and 5.
* **Environments are valuations, and must be definable in the same sense.** A
  context of length `m` is interpreted by a `Fin m → V`; the interpretation is
  `DefFunₘ`, so `m` is a meta-level natural and the arity is fixed per term. Do
  not try to package a context as a single set-valued function unless you also
  supply its definability.
* **`Classical.choice` at the meta level is not allowed to leak in.** Anything
  built with `Classical.choose` on the Lean side is not definable and cannot be
  fed to `sep`. Where the model needs choice it uses the *model's* `𝗔𝗖`
  internally (`exists_choiceFunction`), producing a choice function that is an
  element of `U κ (i+1)`.

---

## 2. Inductive declarations: hand the model an `IndSignature`

The model never sees a telescope. The syntax side owns the whole translation and
delivers a set-theoretic signature:

```lean
structure IndSignature (V : Type*) [SetStructure V] where
  Idx : V                            -- ⟦index telescope⟧ at the fixed parameters
  Q : V                              -- the constructor tags
  Fld : V → V                        -- Fld q  : ⟦non-recursive fields of q⟧
  Pos : V → V → V                    -- Pos q a : recursive positions, Σⱼ ⟦ξⱼ⟧
  posIdx : V → V → V → V             -- posIdx q a b ∈ Idx : ⟦π⟧
  resIdx : V → V → V                 -- resIdx q a ∈ Idx : ⟦C.args⟧
  Fld_definable      : ℒₛₑₜ-function₁[V] Fld
  Pos_definable      : ℒₛₑₜ-function₂[V] Pos
  posIdx_definable   : ℒₛₑₜ-function₃[V] posIdx
  resIdx_definable   : ℒₛₑₜ-function₂[V] resIdx
```

### The function to write

```lean
def interpSig (D : VInductDecl') (levels : ℕ → ℕ) (params : V) : IndSignature V
```

with `params` the interpretation of `D.params` (a Kuratowski tuple of the
parameter values), together with two proofs:

```lean
theorem interpSig_stage (hD : D.WF env) … : IsStageSignature (κ i) (interpSig D levels params)
theorem interpSig_wf    (hD : D.WF env) … : (interpSig D levels params).WF
```

where

```lean
structure IsStageSignature (k : V) (S : IndSignature V) : Prop where
  idx_mem : S.Idx ∈ vsetV k
  q_mem   : S.Q ∈ vsetV k
  fld_mem : ∀ q ∈ S.Q, S.Fld q ∈ vsetV k
  pos_mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, S.Pos q a ∈ vsetV k

structure IndSignature.WF (S : IndSignature V) : Prop where
  resIdx_mem : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, S.resIdx q a ∈ S.Idx
```

### The translation, field by field

Against `Theory/Inductive/Decl.lean`'s record:

| Model component | Built from |
|---|---|
| `Idx` | `⟦T.indices⟧` — the dependent sum of the index telescope at `params` |
| `Q` | the tags of `D.ctorsAll`, i.e. `nmin` (a natural number of `V`) |
| `Fld q` | iterated dependent sum of `⟦F.type⟧` over the `F ∈ C.fields` with `F.recArg = none`, **in declaration position** |
| `Pos q a` | `disjUnion` over `C.recFields` of `⟦r.binders⟧(a)` |
| `posIdx q a b` | `⟦r.args⟧(a, x)` where `b` encodes the field index `j` and the binder value `x` |
| `resIdx q a` | `⟦C.args⟧(a)` |

**Mutual blocks need nothing extra.** Take `Idx := disjUnion` of the per-type
index sets and have `resIdx`/`posIdx` land in the appropriate summand. Nothing
in `SetModel/Inductive.lean` assumes `Idx` is indecomposable. `VIndRecArg.idx`
and the `j` of `D.ctorsAll` are what select the summand.

**Interleaving is fine; do not segregate the telescope.** `Fld q` is an
unconstrained set, so it is free to be the dependent sum of the non-recursive
fields *in declaration position*, with later ones depending on earlier ones. A
recursive field's `binders` and `args` may depend on earlier non-recursive
fields, which is why `Pos`, `posIdx` and `resIdx` all take `a`. (`Pos q a` sees
all of `a`, including components declared after the recursive field in question;
harmless — `⟦ξⱼ⟧` ignores them.)

### Why `Fld : V → V` is well defined — the joint, spelled out

This is the one place where the two sides of this boundary have to be glued, and
neither side's own reasoning is sufficient. Stating it here because it was
previously implicit in two documents at once.

**The problem.** `VIndCtor.WF.fields` types field `i` in the context
`((C.fields.take i).map (·.type)).reverse ++ D.params.reverse` — over *all*
earlier fields, recursive ones included. So for a non-recursive field `F`,
`⟦F.type⟧` is nominally a function of the earlier recursive components too, i.e.
of elements of the family being constructed. But `Fld : V → V` takes only `q`.
If that dependence were real, `Fld q` could not be defined before the family
exists, `indStep` would not be an operator on a fixed carrier, and the whole
construction in `SetModel/Inductive.lean` would not typecheck. This is design
item F8.

**The argument, in two steps.** Both are obligations on the syntax side.

1. **`interp_congr` (§4).** `VIndField.WF.pos`, in the `none` branch, asks only
   for `∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A` — the field type
   is *definitionally* block-free, not syntactically. Only defeq-invariance of
   the interpretation licenses replacing `F.type` by `A`:
   `⟦F.type⟧ = ⟦A⟧`. **Without `interp_congr` there is no first step at all**, so
   `interp_congr` has to be stated and proved before `interpSig_wf` can even be
   stated. That is why it is an obligation and not hygiene.

2. **`NoBlock.indep` — a second, purely syntactic obligation.**
   `interp_congr` is *necessary but not sufficient*. Block-freeness of `A` says
   `A` mentions no constant of the block; it does **not** by itself say that `A`
   is independent of a *variable* `r` whose type mentions the block. What is
   needed is:

   > If `A` is block-free and well-typed in a context containing recursive-field
   > variables, then `⟦A⟧` does not depend on the values at those positions.

   The reason this is true is that at constructor-checking time the block has no
   eliminator — the recursors are added after all the constructors — so nothing
   in scope can consume a value of type `I p π`. Any term that did consume `r`
   would have to be applied to it through a function whose type mentions the
   block, and such a function is not block-free and cannot be an earlier field
   (that field's own `pos` would fail). The canonical example is
   `| mk : (r : T) → (fun _ : T => Nat) r → T`: the second field's stored type
   mentions both `T` and `r`, but its whnf `Nat` mentions neither, and it is the
   whnf that `pos` provides.

   This is a real lemma about the syntax, not a corollary of step 1, and it
   should be proved alongside `interpSig`.

**The escape hatch — taken, and built.** `SetModel/IndInterp.lean`.

`NoBlock.indep` was measured and it bottoms out in `Injectivity.lean`'s
disjointness family (`const_forallE_inv`, stated-but-open, plus an unstated "a
constant application is not a sort"). That family already has two other
consumers, so the model side was generalised instead:

```lean
structure IndSignature₂ (V) [SetStructure V] where
  Fld : V → V → V                 -- Fld W q, at the current approximation W
  Fld_mono : ∀ {W₁ W₂}, W₁ ⊆ W₂ → ∀ q, Fld W₁ q ⊆ Fld W₂ q
  …                               -- Idx, Q, Pos, posIdx, resIdx as before
```

A non-recursive field's domain may now legitimately mention family elements, so
**no independence argument is needed at all** and the disjointness family is
never consulted. The deciding factor was decoupling, not cost: this lets the
model progress independently of the tree's most contested obligation.

*The generalisation is conservative in both directions*, which is what keeps it
additive rather than a rewrite — `IndSignature.toTwo` embeds the old notion,
`IndSignature₂.at` specialises back at a fixed approximation, and
`IndSignature.at_toTwo` is `rfl`.

> **⚠ Status: superseded — the port landed and the translation is built.**
> `IndSignature₃` adds `Args W q`, a signature-chosen set of admissible pairs
> `⟨a, f⟩ₖ`, which is exactly what ties the two independent quantifications
> together. The translation is `SetModel/CtorTrans.lean`; see
> "The translation, built" below for the layout it takes and why.

*And one price stated here was overstated — though not the one that matters.*
The paragraph this replaces said the rank argument for the recursor would need
redoing, "since the non-recursive data `a` would then itself contain family
elements". **The rank argument does not.** The inequality driving the recursion
is

```lean
rank_lt_indCtorVal : (⟨b, y⟩ₖ : V) ∈ f → rank y < rank (⟨q, ⟨a, f⟩ₖ⟩ₖ : V)
```

whose proof descends `rank y < rank f < rank ⟨a,f⟩ₖ < rank ⟨q,⟨a,f⟩ₖ⟩ₖ` — through
the *recursive-position function* `f`, **never inspecting `a`**. Together with

```lean
theorem Ind₂_eq_Ind_at (S : IndSignature₂ V) (D : V) :
    Ind₂ S D = Ind (S.at (Ind₂ S D)) D
```

— the generalised family *is* the ordinary family of the signature specialised
at itself — every existing theorem about `Ind` transfers by one rewrite;
`indRec₂_mem` is the worked instance. `IsStageSignature`'s `fld_mem` adaptation
(`IsStageSignature₂`) is likewise bounded and done.

**But "not a rank argument" was the wrong thing to check.** What the escape
hatch actually breaks is the recursor's *interface*, not its well-foundedness:
`IsMinorPremise` delivers recursive results only through `h ∈ R ^ Pos q a`, so a
design that moves the family elements into `a` and empties `Pos` starves it. The
lesson, recorded because it cost a round: **enumerate the consumers, not the
first one that comes to hand.**

**Do not weaken `pos` to a syntactic `NoBlock`.** That would make step 2 trivial,
but it rejects types the kernel accepts (`checkPositivity` applies `hasIndOcc` to
the whnf), so the spec would no longer refine the kernel.

### The translation, built — `SetModel/CtorTrans.lean`

Sorry-free, `[propext, Classical.choice, Quot.sound]`, and it consumes **no
independence clause at all**.

**The layout.** `a` is the valuation of the *whole* field telescope, recursive
slots included; `Args q` says those slots are the curried components of `f`.
Concretely, per constructor:

| component | built from |
|---|---|
| `Fld _ q` | `teleFun` of the per-field domains: `⟦A⟧` at a non-recursive field, for the block-free `A` that `WF.pos` supplies; `Dcar ^ ⟦ξ⟧` at a recursive one |
| `Pos q a` | `tagUnionF` of `⟦ξⱼ⟧` evaluated at `a ↾ (np + i)` |
| `posIdx q a b` | `⟨r.idx, argsVal ⟦π⟧⟩ₖ` at the position's payload |
| `resIdx q a` | `⟨j, argsVal ⟦C.args⟧⟩ₖ` |
| `Args _ q` | the pairs whose recursive slots agree with `f` pointwise |

Four facts worth carrying forward.

1. **The prefix is explicit.** `ξ` lives over field `i`'s context, `a` over the
   whole telescope, and `interp` is length-sensitive — it appends at `|Γ|`, so a
   longer valuation puts the `ξ`-binders at the wrong positions. Foundation's
   `restrict` *is* that prefix on the `snoc` encoding and is already definable,
   so no new primitive was needed; `teleFun_restrict` and `teleFun_slot` are the
   two lemmas tying `Fld`'s slot domains to `Pos`'s summands.
2. **`Fld` and `Args` are constant in `W` here.** A recursive slot need only be
   *some* function into the carrier — `Args` pins it to `f`, and `indStep₃`'s
   own conjunct constrains `f` — so the approximation-indexing `IndSignature₂`
   introduced is not spent by this translation, and both monotonicity
   obligations are `subset_refl`.
3. **`A` comes from choice on a chain-free existential**, as §4 requires:
   `exists_blockFreeTypes` turns `VIndField.WF.pos`'s `none` branch into a
   function `ℕ → VExpr`, so `ctorDataOf` is a function of `VIndCtor.WF` and
   nothing else.
4. **It is not vacuous.** `exists_mem_args`: above *every* element of `Fld`
   there is an admissible `f`. That is the statement a `Fld`/`Pos` mismatch
   would falsify, and it is proved with no syntactic hypothesis.

### The correction this required: blanking needs the clause at **three** sites

The ledger records the other layout — `a` blanks the recursive slots — and the
`Decl.lean` clause `VIndField.WF.binders_indep` was added for it. That layout
does not close, and the reason is new:

> `Pos q a` is not the only component evaluated at `a`. **`posIdx q a b` is
> `⟦r.args⟧` and `resIdx q a` is `⟦C.args⟧`**, and both live over a context
> containing the recursive fields. Blanking the slots therefore needs the
> independence clause at `r.binders`, at `r.args` *and* at `C.args`; only the
> first exists.

Note the asymmetry, which makes this fixable in principle but not cheaply:
`Pos q a` *types* `f`, so it structurally cannot receive it — that is what makes
`binders_indep` unavoidable for the blanking layout — while `posIdx` and
`resIdx` merely *use* `a` and could be given `f` by a further port. That port
was not taken, because the layout above needs neither.

### And the objection to the built layout is about a statement, not a theorem

The ledger rules out fillers-in-`a` because `IsSubsingletonSignature.fld_det`
("the non-recursive data is determined by the result index") becomes false, and
names `Acc` — a large-eliminating subsingleton with a recursive field — as the
family it kills. With `Args` forcing the copies to agree with `f`, the family
holds exactly the elements it held before; what changes is that `a` is
determined by the index **and `f`**, not by the index alone.

`Ind₃_subsingleton` (`SetModel/CtorTrans.lean`) is `Ind_subsingleton`'s proof
against the restated hypothesis, and it goes through with the pinning order
preserved: domains first (`pos_det`), then `f` by the rank induction, then `a`
(`fld_det`). So the independence facts are not eliminated — they reappear as
`pos_det`/`posIdx_det`/`fld_det` — but they are now owed **only by a
large-eliminating subsingleton** instead of by every declaration. That is the
whole trade, and it is why the translation is not blocked.

**Checked — the instance exists.** `accSig_isSubsingleton`
(`SetModel/CtorTransExamples.lean`) is `IsSubsingletonSignature₃` at `Acc`'s
signature, sorry-free, `[propext, Classical.choice, Quot.sound]`. So the
ledger's objection is now closed in both directions: the theorem holds against
the restated hypothesis, *and* the restated hypothesis holds at the family the
ledger named as the one the layout would kill.

Four things the instance settles, in decreasing order of how surprising they
were.

1. **`fld_det` is where `Args` earns its place, and it goes through.** `a`'s
   recursive slot is a function on `Pos q a` agreeing pointwise with `f`, so
   `f = f'` forces the slots equal by `function_ext`. That is the step the
   ledger predicted would fail, and the prediction was about `fld_det`'s old
   statement, not about `Acc`.
2. **`posIdx_det` is free at *every* declaration**, not just at `Acc`:
   `interpSig₃_posIdx_indep` (`SetModel/CtorTrans.lean`) proves it with no
   hypothesis at all, because `posIdxVals`' entries are literally
   `fun _a x ↦ …` — a recursive occurrence's `⟦π⟧` is evaluated at the
   *position*, and `posIdx`'s `a` slot is vestigial. One of the four fields is
   therefore not a per-declaration obligation at all.
3. **`pos_det` is `resIdx` determining a prefix.** `Pos` reads `a` only through
   `a ↾ (np + i)` (`interpSig₃_Pos_congr`, also general), and at `Acc` the
   result index *is* the field-0 slot, so the prefix is determined on the nose.
4. **No syntactic hypothesis is used, and the block-free replacements `A` are
   left arbitrary.** None of the four fields inspects a field *domain*, only the
   shape of the valuation. The one hypothesis is `IsSeq params 2`, which
   `isSeq_params` supplies and which is separately exhibited (`isSeq_two`).

The instance is then **used**, not merely stated: `accInd_subsingleton` and
`accIndRec_indep_of_proof` are `Ind₃_subsingleton` and `indRec₃_indep_of_proof`
at it, with the subsingleton hypothesis discharged.

### `Fld ≠ ∅` is not a theorem, and asking for it is the wrong ask

`exists_mem_args` is stated *above every element of `Fld`*, and the standing
worry is that this makes it vacuous. Both directions are now separated and
proved, and the conjunct that was asked for is not one of them:

* **`Fld ≠ ∅` is false in general and no amount of soundness will fix it.** A
  constructor whose field types are uninhabited has no applications — `Acc` over
  an empty `α`, or `Foo | mk : False → Foo` with no parameters at all.
  `not_mem_accFldSet_of_slot_empty` is that direction.
* **What *would* be a defect is `Fld` inhabited with `Args` empty above it**,
  and that is exactly what `exists_mem_args` rules out. `accArgs_nonempty` is
  `exists_mem_args` at `Acc` with its antecedent discharged from the two slot
  domains rather than assumed, so the admissibility condition is satisfiable and
  not merely stated.

### What the model gives back

With `hS : IsStageSignature (κ i) S` and `hWF : S.WF`, at `hi : i < n`:

```lean
Ind S (U κ (i+1))                              -- the family, a set
Ind_mem_U_stage hκ hi hS hWF                   -- : Ind S (U κ (i+1)) ∈ U κ (i+1)
indCtor S q a f                                -- the constructor application
ctor_mem_Ind_stage hk hS hWF …                 -- constructors land in the family
mem_Ind_iff_stage hk hS hWF                    -- no junk
indCtor_inj, indCtor_ne_of_tag_ne              -- injectivity, no confusion
Ind_induction                                  -- the induction principle
indRec S (U κ (i+1)) R e he                    -- the recursor, arbitrary codomain R
indRec_indCtor_stage hk hS hWF hE …            -- the ι-rule
Ind_subsingleton_stage, indRec_indep_of_proof_stage   -- the Prop case
IndProp S D i, IndProp_mem_UProp               -- the ℓ = 0 interpretation
```

Note `indRec`'s codomain `R` is arbitrary, with no universe hypothesis: **large
elimination is free in the model.** The restriction appears only for
`Prop`-valued families, where `IndProp` remembers whether the fibre is inhabited
but not which element inhabits it; `IsSubsingletonSignature` (one constructor,
non-recursive data determined by the result index — satisfied by `Eq` and `Acc`)
is exactly when a large motive is still well-defined.

The recursor's minor premise is the four-argument bundle

```lean
e : V → V → V → V → V     -- e q a f h,  with he : ℒₛₑₜ-function₄[V] e
IsMinorPremise S (U κ (i+1)) R e      -- e q a f h ∈ R on the relevant arguments
```

and the ι-rule reads `F (ctor q a f) = e q a f (F ∘ f)`, i.e. Carneiro's
`F(a,f) = e(a)(f)(F ∘ f)` on the nose.

---

## 3. Universe levels are `ℕ` bounded by `n`, and soundness is a schema

A `VLevel` valuation lands in a meta-level `ℕ`:

```lean
def levelVal (D : …) : ℕ → ℕ           -- universe parameter ↦ its index
```

and the model's stage for index `i` is `U κ i`. **The theorem must never say
`∃ k`.** It says: *fix* `n`, *assume* `hκ : IsInaccessibleChain n κ`, and
*hypothesise* that every universe index occurring in the derivation is `≤ n`.
`Entailment.inconsistent_compact` then supplies the finiteness that turns the
schema into a contradiction, matching the fact that one Lean proof mentions
finitely many universes and one first-order derivation uses finitely many schema
instances.

### How to read the bound off

`SetModel/Universe.lean` records the closure of each stage in three tiers. The
required `n` is the largest universe index whose stage a derivation actually
uses, and the tier tells you what that costs:

| Tier | Constructions | Requires |
|---|---|---|
| free | `sUnion_mem_U`, `sep_mem_U`, `mem_U_of_subset_of_mem`, **`lfp_mem_U`**, **`acc_mem_U`** | only that `κ i` be an ordinal — bookkeeping, not a hypothesis |
| limit | pairing, `℘`, `×ˢ`, `^`, `Pi`, `Sigma`, `disjUnion`, `setQuotient`, `eqvClosure` | `i < n` |
| regularity | `repl_mem_U`, `piFun_mem_U`, `sigmaFun_mem_U`, and inductive **formation** | `i < n` |

Two facts to lean on when computing the bound.

* **`Sort i` needs `i < n`, and nothing else does.** `U_mem_succ hκ hi : U κ i ∈ U κ (i+1)`
  is the universe rule; `U_subset_succ hκ hi : U κ i ⊆ U κ (i+1)` is what `Π`/`Σ`
  and inductive formation use. They are different facts and both are proved.
* **`Prop` is free.** `piProp_mem_UProp` — the interpretation of an impredicative
  `∀` — holds for an *arbitrary* index set `A`, with no bound on `A`'s universe
  level and no inaccessible mentioned. Likewise `propext_of_mem_UProp`. So a
  derivation's `Prop` layer contributes nothing to `n`.
* **Least fixed points are free.** `lfp_mem_U` needs nothing about the universe
  level at all, so interpreting an inductive type as a least fixed point costs
  nothing at *formation*; the budget goes entirely on the `Π`/`Σ` that build the
  operator, and on the replacement in `Ind_mem_U_stage`.

There is no `U_ω` inside the model — its rank would be `sup_i κ i`, which is
below no `κ i`. Within one schema instance `U κ n` is the ambient universe, and
`U_subset_top hκ (hi : i ≤ n) : U κ i ⊆ U κ n` is the statement to cite. State
the soundness theorem against `U κ n`, never against a limit of the sequence.

---

## 4. Defeq-invariance: already proved, and the wrapped form is enough

> **This section previously said `interp_congr` was an unproved obligation owed
> by the syntax side, and that `interpSig_wf` could not be stated until an
> *unconditional* version existed. Both halves were wrong about the tree.** It
> is proved, it has been for some time under another name, and the wrapped form
> it comes in is sufficient. What follows is the corrected analysis; the
> superseded claim is kept only as the note at the end, because *why* it was
> wrong is reusable.

### It exists: `SetModel/SoundInduction.lean:interp_congr`

```lean
theorem interp_congr {Γ : List VExpr} {e₁ e₂ B : VExpr}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (H : env₀.IsDefEq nv Γ e₁ e₂ B) :
    Above M (EqSound M L Γ e₁ e₂)
```

It is not new machinery. `Sound` has two fields, and `Sound.eq` is
`EqSound M L Γ e₁ e₂`, which unfolds to exactly
`∀ ρ ∈ interpCtx M L Γ, ⟦e₁⟧ρ = ⟦e₂⟧ρ`. So `interp_congr` is `sound` with the
`type` half projected away — three lines — and it holds for arbitrary `B`, not
only at `.sort u`. The section was right that in Carneiro this is part 4 of the
soundness theorem proved by one induction with part 3. That is precisely what
`SoundInduction.lean` does; the projection had simply never been named.

### It is `Above`-wrapped, and that is enough

`Above M P` is `∃ m, IsInaccessibleChain m M.κ → P`. Soundness is stated that
way and cannot be stated otherwise: a derivation's premises can need
arbitrarily higher inaccessibles than its conclusion, so no bound on the
conclusion is inherited by the premises, and the bound cannot be moved onto `L`
either, since `L.lvl Γ (.sort k) = k+1` for every `k`. See `SoundInduction.lean`'s
module header.

**The split that makes this work is data versus properties.**

`cnstOf`'s `.induct` line is `oracleExtend o D.allNames …`, and
`o : Name → List VLevel → V` is a plain function parameter — *data*, supplied
with no chain in sight. So constructor and recursor **values** must be sets,
defined unconditionally. That rules out the shape
`Above M (∃ S : IndSignature V, …)`: data cannot be extracted from an `Above`.

But `OracleOK`'s two fields are **already** `Above`-wrapped
(`SetModel/Cnst.lean:183–186`), as are `ModelData.Coherent`'s four and the pair
`coherentOn_addDefEqFold` consumes. So every **property** may be wrapped, and
every consumer already expects it that way.

| piece | status | why |
|---|---|---|
| `interpSig D hD levels params : IndSignature V` | **unconditional data** | its fields are `⟦A⟧` for the block-free `A` that `VIndCtor.WF`'s `pos` clause supplies; extracting `A` is `Classical.choice` on `∃ A, D.NoBlock A ∧ IsDefEqType … F.type A` — a **chain-free** existential |
| the bundled `Fld_definable` &c. | **unconditional** | definability of `⟦A⟧` is `(interp …).definable`; no congr involved |
| `interpSig_stage`, `interpSig_wf`, the `⟦ctorType⟧` connection | **`Above`-wrapped** | all `Prop`s, and every consumer takes `Above` |

### Where the old claim went wrong: defining versus relating

`Fld q` is *defined* from the block-free `A`. Knowing `⟦F.type⟧ = ⟦A⟧` is never
needed to write the definition down — it is needed only to carry a membership
proved at `A` over to `F.type`, and that is a `Prop`.

That step is machine-checked in the wrapped form:

```lean
theorem above_mem_congr (hρ : ρ ∈ interpCtx M L Γ)
    (hAA' : Above M (EqSound M L Γ A A'))
    (h : Above M ((interp M L Γ e).toFun ρ ∈ (interp M L Γ A').toFun ρ)) :
    Above M ((interp M L Γ e).toFun ρ ∈ (interp M L Γ A).toFun ρ)
```

The congr's threshold and the membership's threshold merge; nothing is
unwrapped. `SetModel/SoundInduction.lean`.

### The `Above` algebra this needs

`Above` had only `pure` and `imp` — enough to *carry* one wrapped fact, not
enough to *combine* two, which is what any construction with several
chain-dependent properties needs. Now also in `SoundInduction.lean`:

* `Above.and` — two thresholds merge by `max`, because `IsInaccessibleChain` is
  downward closed (`IsInaccessibleChain.le`);
* `Above.imp₂`;
* `Above.forall_mem` — finitely many wrapped facts under one threshold, which an
  inductive block needs immediately: one obligation per constructor.

### Price of an unconditional version, if anyone still wants one

De-`Above`-ing soundness cannot be done by bounding the chain, for the reason
above. It would need a model with a **proper class of inaccessibles**, or a
reflection argument. That is **a change to the model's foundational hypothesis,
not a lemma** — the whole development is currently stated against an
`n`-inaccessible-chain *schema*, and this would replace it. Against that, the
wrapped route cost three combinators and one transport lemma.

**Recommendation: build `interpSig` unconditionally, keep every property
wrapped, and do not weaken `WF.pos` to a syntactic `NoBlock`.**

### The other two reasons the old section gave, which still stand

* **Almost every model-side step replaces a type by a definitionally equal
  one.** `VIndType.WF.canon`, `VIndCtor.WF.params_eq`, and every `IsDefEqType`
  clause in `VIndField.WF` hand the model a `≈` where it wants an `=`.
  `above_mem_congr` is the shape each of those takes.
* **The interpretation's own case splits must be stable under `≡`.** That is
  `LevelAssign.lvl_congr` and `LevelAssign.srt_congr` in `SetModel/Interp.lean`,
  both proved there from `LevelAssign` alone.

### Note to the next reader: check the tree before pricing the work

This section priced work the tree had already made unnecessary, and it is the
second time in two rounds that a doc here was accurate about *when it was
written* and stale about *what exists now*. The check that would have caught
both took seconds. Before building what a doc says you need:

1. **Check whether an existing structure's field already unfolds to it.**
   `Sound.eq` *was* `interp_congr`.
2. **Check whether the consumer already accepts the weaker form.** `OracleOK`'s
   fields were already `Above`-wrapped, so no unconditional version was ever
   required.

A document naming something as the first blocker is evidence about its own date,
not about the current tree.

---

## 5. What proof-splitting actually requires: the model needs no level

`Theory/Typing/SortUniq.lean` establishes that `SortUniq` is **not a semantic
consequence** of Lean's rules — add cumulativity, which every nested-universe
model validates, and it is false — and that `LevelAssign.srt_sound` *is*
`SortUniq` restated. Together those say the model cannot discharge its own
parameter, in principle rather than for want of effort. This section is the
measurement of what the parameter would have to be instead.

### The interface is two predicates, and that is a counted fact

Machine-checked by scanning `Theory/SetModel/`, classifying **every**
occurrence rather than the likely ones:

* **92** occurrences of `.eval` in the directory. **15 involve `L.lvl`/`L.srt`,
  and every one of them is the `= 0` test** — `LevelAssign.IsProp` /
  `LevelAssign.IsProof` or a comment about them. The other **77** take their
  level from the *syntax*: the `u` of `.sort u`, the `u`/`v` of a rule's
  premises, a constant's level arguments `us`.
* Every universe index the model ever forms is `U κ i` for a stage parameter `i`
  or `U M.κ (u.eval M.ls)` for a **syntactic** `u`. **`L.lvl` supplies no
  universe index anywhere.** In particular `mkLam`, `mkForallType` and
  `mkForallProp` take no universe argument at all — the guess that `lvl` was
  needed for one is wrong, and wrong in the favourable direction.
* Every *fact* about `L` — `lvl_sound`, `srt_sound`, `lvl_congr`/`srt_congr`,
  `Stable`'s four fields, `CtxInvariant`'s two — is consumed **only** by
  rewriting inside a `… .eval M.ls = 0`. All **12** such sites are literally
  `simp only [LevelAssign.IsProof, VLevel.equiv_def.mp … M.ls]`.
* Two bridge lemmas, `isProp_iff` and `isProof_iff`
  (`SoundInduction.lean:118–131`), are the entire interface between `L` and the
  soundness induction. They have **15** uses, all insulated from any change to
  `L`. Outside `SetModel/`, `LevelAssign` occurs only in `SortUniq.lean`'s prose.

So what `interp` requires is **not a canonical level per term**. It is two
Prop-valued predicates satisfying

```
IsProp  Γ A ↔ u.eval ls = 0     whenever Γ ⊢ A : .sort u   (u.WF)
IsProof Γ e ↔ u.eval ls = 0     whenever Γ ⊢ e : A, Γ ⊢ A : .sort u
```

That is `PropSplit` (`SetModel/Interp.lean`). `LevelAssign.toPropSplit` embeds
the old parameter; there is no converse, and there should not be — the
weakening is the point.

### Why a purely semantic criterion is impossible — keep this argument

Before asking for a weaker parameter it is worth knowing that **no
parameterisation removes the syntactic input entirely**, and the reason is about
the setting rather than about this construction:

* the `{•}` collapse at a `Prop` is **forced by impredicativity**. A genuine
  dependent product of subsingletons *is* a subsingleton, so proof irrelevance
  would be validated without any collapse — but its rank is that of the domain,
  which impredicativity leaves unbounded, so it cannot inhabit a fixed
  `U κ 0`. Only the collapse to a subset of `{•}` is rank-bounded;
* and the collapse must be decided at `lam` and `app`, which **carry no type**.
  The `forallE` split could be taken semantically (test `⟦B⟧ ⊆ {•}` pointwise,
  a definable condition); the `lam` split cannot, because a term's *value*
  being `•` is not the same as its type being a proposition.

So proof-splitting is a syntactic decision, necessarily. The question is only
*which* syntactic statement it imports.

### The residual obligation, and it is not `SortUniq`

`SortUniq.lean`'s cumulativity rule is stated for arbitrary `e`, so it refutes
the ↔-form directly: a proposition `P` gets `P : .sort 0` and `P : .sort 1`,
forcing `IsProp Γ P` both ways. The obvious repair is the **minimum
convention** — `IsProp Γ A` means *some* sort of `A` evaluates to `0`, with
`U_mono` absorbing a `Prop` branch taken against a non-zero sort.

**It was attempted and it does not work.** Two thirds of the argument hold:
the `⇐` direction survives, the non-`Prop` branch uses only its contrapositive,
and `U_mono` does absorb the **formation** obligation (`piProp ∈ U κ 0 ⊆ U κ k`).

What it cannot absorb is **parts 1 and 2**. `propSound_of_mem_sort` turns
`⟦e⟧ρ ∈ ⟦.sort u⟧ρ` into `⟦e⟧ρ ⊆ {•}`, and its hypothesis `u.eval ls = 0` is
load-bearing (machine-checked); dropping it leaves exactly

```
h : ⟦e⟧ρ ∈ U M.κ (u.eval M.ls)
⊢ ⟦e⟧ρ ⊆ {pt}
```

— the **downward** inclusion, and `U_mono` only moves memberships up. `Sound.proof`
(part 2, consumed by `appDF`, `lamDF`, `beta`, `eta`) then takes the type's
`Sound` **at the sort its premise names**, and if the split says "proof" while
that sort is non-zero the witness sort's soundness is not in scope at all: the
induction supplies one `Sound` per premise, not one per sort the type happens to
have.

**So the `↔`-form is the weakest form the present induction can run on, and the
model's syntactic import is both statements, not one** — *as statements about
an arbitrary environment*.  §7 shows that at the **environment `kernel_sound`
actually reaches**, where the goal has already handed the proof a proof of
`False`, the first of the two is free:

> **`PropUniq`** — the sorts of a *type* agree on being zero. Reached by the
> cumulativity check, so, like `SortUniq`, it needs a syntactic proof.
>
> **`PropTypeAgree`** — the types of a *term* agree on being propositions. Not
> reached by that check: cumulativity retypes at sorts and never gives a proof a
> second type.

Both are strictly weaker than `SortUniq` — that is what step 1 bought, and it
stands. `PropTypeAgree` remains the more interesting of the two, and the
connection found from the other end is exact:

> **`sort_not_proof` *is* `PropTypeAgree` at `e = .sort u`**, its two types
> being `.sort (u+1)` and the proposition `p`.

Two streams arrived at that statement independently — one asking what survives
the cumulativity check, one asking what the interpretation branches on.

**Neither is priced syntactically**; that is the injectivity stream's call. What
is settled here is that these two, and not `sort_inv`, are what the model needs.

*What would remove `PropUniq`*, for whoever prices that: strengthen `Sound` to
quantify over **all** types of a term rather than the one its premise names —
close to assuming the uniqueness it is trying to avoid — or decide the `forallE`
branch semantically (`⟦B⟧ρ ⊆ {•}` pointwise is a definable test). The second is
a real option for `forallE` congruence and does **not** help parts 1 and 2,
which are about `lam`/`app` terms whose *type* is a proposition.

**A third route existed and is the one that worked — §7.** Neither of the two
above changes anything about `prop_sound`; §7 leaves `prop_sound` in its
`↔`-form exactly as this section concludes it must be, and changes only how
`propSplitOf`'s *first input* is discharged.

### Built, and what the audit found

**`PropSplit` is in the tree and the whole directory runs on it.** `interp` and
every downstream file take `(L : PropSplit env nv)`; `LevelAssign` is kept, no
longer used by the interpretation, and `LevelAssign.toPropSplit` is the bridge.
Full build green, sorry-free, three standard axioms. `LevelAssign`'s own
refutation file (`LevelAssignUnsat.lean`) still compiles and stays as the record
of why the guards exist.

Mechanically it was what the scan predicted: the `Stable` and `CtxInvariant`
fields became `↔`s on the predicates, the 12 `simp only [LevelAssign.IsProof,
VLevel.equiv_def.mp …]` sites became one-line `exact`s, and the 15 consumers of
`isProp_iff`/`isProof_iff` did not move at all.

**The audit — `SetModel/PropSplitAudit.lean`, run before anything was built on
the result**, in three parts:

1. *Upper bound*: `LevelAssign.toPropSplit` — the new parameter asks for nothing
   the old one did not already give.
2. *The fields do real work*: `prop_forces_false` (`Prop` is not a proposition)
   and `prop_forces_true` (a variable of type `Prop` is), both from `prop_sound`
   alone, so no constant predicate is a `PropSplit` (`propSplit_not_constant`).
   The second is a `bvar` instance — the shape that refuted the unguarded
   `LevelAssign`, here satisfied rather than contradictory.
3. *Lower bound*: `propSplitOf` builds one, so satisfiability reduces to two
   named statements about the judgement.

**And the audit sharpened the residual, which the analysis above had merged.**
The `↔`-form now in the tree needs **two** statements, not one:

| | statement | reached by the cumulativity check? |
|---|---|---|
| `PropUniq` | the sorts of a **type** agree on being zero | **yes** — a proposition then has sorts `0` and `1` |
| `PropTypeAgree` | the types of a **term** agree on being propositions | **no** — cumulativity retypes at sorts, never gives a proof a second type |

Both are `Prop`-valued defs in `PropSplitAudit.lean`, and both are load-bearing
in `propSplitOf` (machine-checked). The minimum convention was expected to delete the first row and **does not** —
see "The residual obligation" below. Both rows stand *as inputs to
`propSplitOf`*; **§7 discharges the first row from the goal's own `hfalse`**,
which is a different move — it leaves `propSplitOf` and `prop_sound` untouched
and supplies one of the two inputs rather than removing it.

### Confidence split, kept deliberately

* The interface scan is **machine-checked** (counts above, reproducible by
  grep), and so is everything in `PropSplitAudit.lean`.
* The minimum convention was **attempted and refuted**, at
  `propSound_of_mem_sort`'s load-bearing `u.eval ls = 0` (machine-checked by
  hypothesis-necessity) and at `Sound.proof`'s use of the premise's own sort.
  The `↔`-form stands. This corrects the estimate two rounds running: the first
  version said the residual was one statement, the second that the minimum
  convention would make it so; neither survived attempting the use.
* **`PropTypeAgree` is not priced syntactically.** It follows from unique
  typing; whether it has a cheaper route is the injectivity stream's call.

---

## 6. `SortForallEDisjoint` has no cheap model route either, and the reason is `proofIrrel`

Asked from the syntactic side: *a term cannot have both a sort and a Π as its
type* —

```
SortForallEDisjoint : Γ ⊢ e : .sort u → Γ ⊢ e : .forallE A B → False
```

— passes the cumulativity check that excluded `SortUniq` and `PropUniq` from
semantic argument, so is a **cut-down** model available that separates "inhabits
a sort" from "inhabits a Π" and needs neither proof-splitting nor a level
assignment?

**No.** Three things, in the order they decide it.

### The premise is weaker than it looks

Passing the cumulativity check shows that *that* extension does not refute the
statement. It is evidence of **not being excluded**, not evidence that a route
exists. Those are different, and the difference is the whole of this section.

### The direct route is blocked, at a named instance

A model refutation needs `⟦.sort u⟧ρ ∩ ⟦.forallE A B⟧ρ = ∅`. **In the model
that exists they are not disjoint**, and two one-line facts (both machine-checked
against `SetModel/`) say so:

* `∅ ∈ UProp` — the `Prop` universe contains the empty set;
* `∅ ∈ mkForallType G hG F hF ρ` whenever `G ρ = ∅` — the empty function is the
  unique function out of an empty domain, so it inhabits *every* dependent
  product over an empty domain.

Take an empty type as the witness. `⟦False⟧ρ = ∅ ∈ ⟦Sort 0⟧ρ`, and
`∅ ∈ ⟦∀ x : False, B⟧ρ`. The model is **consistent with** `False : ∀ x : False, B`
— both memberships the argument would have to contradict simply hold. This is
not "no argument was found"; it is the argument's premise failing at an instance
one can name.

The overlap is structural in ZF, not an encoding artifact: `Y ^ ∅ = {∅}` is a
theorem, and universes contain `∅`. Separating them requires **tagging**, which
is a new construction rather than a reading of the existing one.

### Tagging is the only repair, and it needs the statement it would prove

Tag type-values `⟨0, ·⟩` and function-values `⟨1, ·⟩`. Disjointness is then free
by pair injectivity, and β, η and the constant equations survive — tags are a
relabelling.

It dies at **`proofIrrel`**. That is the one rule of the theory which identifies
terms *without regard to their structure*: any two inhabitants of a proposition
are equal, so their denotations are equal, so **the tag is constant on the
inhabitants of every proposition**. A tag assignment therefore exists only if no
proposition has both a sort-tagged and a Π-tagged inhabitant — i.e. only if a
sort term inhabits no proposition, which is `sort_not_proof`
(`Theory/Typing/SortUniq.lean`).

And `sort_not_proof` *is* `PropTypeAgree` at `e = .sort u` (§5). So the cut-down
model bottoms out at the same statement the full interpretation does, and it is
the statement the syntactic route is trying to reach. **Circular.**

This is the same shape as the impredicativity impossibility in §5: a specific
rule of the theory destroys exactly the distinction the argument depends on.
There, impredicative `∀`-formation forces the `{•}` collapse, so proof-splitting
cannot be decided semantically. Here, `proofIrrel` forces the identification, so
sorts and Πs cannot be separated semantically. **Both are facts about the
setting, not about this construction.**

### Two consequences worth acting on

* **The overlap is raw material for a *refutation*.** Since the interpretation
  does not separate the two, the standard model would validate a rule extension
  that gives some term both types, if one can be written syntactically — exactly
  `SortUniq.lean`'s method. `False` and `∀ x : False, B` is where to aim it. If
  such a rule exists, `SortForallEDisjoint` is not a semantic consequence either
  and the "cumulativity check passes" reading flips. (A model failing to decide
  a statement is not evidence the statement is false; this is a test to run, not
  a claim.)
* **`sort_not_proof` is the higher-value ask.** Granted it, the tagged model
  becomes available and *would* give `SortForallEDisjoint`. `SortUniq.lean`
  independently calls `sort_not_proof` "the statement worth asking the model
  stream for"; this section reaches the same conclusion from the model side.
  Note it is not itself cheaply semantic — the obvious argument (`U κ i ≠ pt`,
  a universe is not the proof object) needs soundness, hence the apparatus —
  but it is the point where the whole family meets.

*The honest alternative*, if a separating model is wanted anyway: tags defined
by induction on derivations rather than on syntax, i.e. reducibility candidates
— a normalization proof, which is the Church–Rosser-scale metatheory already
priced, and is the syntactic route in semantic clothing.

---

## 7. `PropUniq` is free at the environment the goal reaches — built

**`SetModel/PropUniqFromFalse.lean`, `SetModel/PropReduce.lean`,
`SetModel/FalseProp.lean`.** All three sorry-free, `[propext, Classical.choice,
Quot.sound]`. This section supersedes §5's "the model's syntactic import is
both statements, not one" *at the environment `kernel_sound` reaches*; §5's
analysis of an arbitrary environment is unchanged and still correct.

### The observation, and it only appears reading backwards from `kernel_sound`

`leanTTConsistent` is `∀ env, env.LeanWF → ¬ ∃ e, env.HasType 0 [] e falseProp`.
`¬ P` **is** `P → False`, so its proof may `intro` the inhabitant of `falseProp`
**before** any model is built. From that point every proposition of `env` is
inhabited, and `PropUniq` is `PropTypeAgree`'s **diagonal** (`A' := A`) guarded
by the existence of an inhabitant — a guard that bites only at propositions,
which is exactly where the `False` proof supplies one.

```lean
theorem PropUniq.of_propTypeAgree (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0) :
    env.PropUniq 0

noncomputable def propSplitOfAgree (env : VEnv) (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0) :
    PropSplit env nv
```

**Not the refuted minimum convention.** That weakening changed `prop_sound` and
died at `propSound_of_mem_sort` and `Sound.proof` (§5). This keeps `prop_sound`
in the `↔`-form and touches neither site; what changes is how one of
`propSplitOf`'s two inputs is discharged. The two failure sites are consumers of
`prop_sound`, and `prop_sound` still holds in full.

**Not circular.** `hf` is a *hypothesis of the theorem*, not something the model
produces. `Verify/Bridge.hasType_falseProp` delivers it, proved and sorry-free,
before `leanTTConsistent` is invoked; the model is built after it and its job is
to contradict it.

**It costs a hypothesis, which is the check that it is not a triviality.** All
eight explicit binders of `propUniq_aux` are load-bearing (machine-checked by
hypothesis-necessity). Without `hf` nothing is claimed: the diagonal has no `e`
to instantiate at an uninhabited proposition.

**And the hypothesis pair is satisfiable, not merely stated.**
`ordered_and_inconsistent_satisfiable` exhibits `loopEnv2`
(`Theory/Typing/CycleConv.lean`): `VEnv.WF` by two `.axiom` steps, with a
constant of type `falseProp`. It is not `LeanWF`, so it is no counterexample to
consistency — it is the witness that `Ordered ∧ inconsistent` is a non-empty
class.

### The two `nv` questions, both answered

**`PropUniq env 0 → PropUniq env nv`, and the same for `PropTypeAgree`**
(`SetModel/PropReduce.lean`, `PropUniq.of_zero` / `PropTypeAgree.of_zero`), for
every `nv`, with **no hypothesis on `env` at all**. Both conclusions are about
`u.eval ls` at a *single* valuation, and any valuation of `ℕ`s is realised by
closed levels `succ^k zero`; `IsDefEq.instL` transports the derivations and
`VLevel.eval_inst` transports the value. So the §7 derivation — which runs at
zero universe parameters — is available at every `nv`, and the separate question
of whether the model's *outer* induction can be run at `nv = 0` never has to be
asked.

The one place care was needed: `instL` substitutes at every parameter index
while `u.WF nv` bounds only the ones `u` mentions. `VLevel.eval_eq_of_wf` is the
lemma that says `eval` cannot see the difference.

**Weakening into an arbitrary `Γ` needs no context hypothesis.**
`PropUniq`/`PropTypeAgree` carry no `OnCtx`/`CtxClosed`, and the derivation
weakens a typing at `[]` into the `Γ` they quantify over. `HasType.weak0`
(`Theory/Typing/Lemmas.lean`) does that with only `Ordered env` — its
`CtxClosed` argument is discharged at the *source* context `[]`. So **`PropSplit`
does not need to grow a context field**, and `inhabited_of_hasType_falseProp` is
stated at a universally quantified `Γ` with no side condition.

### `⟦falseProp⟧ ∅ = ∅` — the one place the goal touches the model

`SetModel/FalseProp.lean`. Nothing in the tree composed this before; until it
existed nobody knew what `sound_nil` had to be instantiated at.

```lean
theorem interp_falseProp : (interp M L [] falseProp).toFun ∅ = (∅ : V)
theorem falseProp_above_false … (H : env₀.HasType nv [] e falseProp) : Above M False
```

Three properties, all machine-checked:

* **Branch-independent.** Both clauses of `interp`'s `forallE` case give `∅`:
  the impredicative `∀` has an empty fibre over `∅ ∈ UProp`, and a dependent
  product must have a *value* over `∅ ∈ UProp`, which would land in that fibre.
  So the consistency conclusion does not depend on the split being right at the
  one place it is finally applied. (`falseProp_isProp_branch` records that the
  branch is in fact forced — `prop_forces_true` at `M.ls` — so this is
  robustness, not necessity.)
* **Unconditional, not `Above`-wrapped.** The only universe it mentions is
  `U M.κ 0 = UProp = ℘{•}`, whose definition names no inaccessible. The
  threshold in `falseProp_above_false` is entirely `sound_nil`'s.
* **Not vacuous.** `interp_forallE_falseProp_sort_nonempty` exhibits a `∀` whose
  denotation is *inhabited* (`∀ x : (∀ p : Prop, p), Prop`, which the empty
  function inhabits), so the clause `interp_falseProp` lands in is not uniformly
  empty; and `interp_falseProp_dom` gives `⟦Prop⟧ = UProp`, which *contains* `∅`,
  so `interp` is not the constant `∅` either.

`falseProp_above_false` concludes `Above M False`. Turning that into `False`
needs a `ModelData` whose `κ` carries a chain of the threshold's length — the
outer construction (`exists_inaccessibleChain` plus the constant assignment),
which is *not* built here.

### What this does not do

* **It does not move `PropTypeAgree` one inch.** That statement is open, with
  three characterised obstructions (`docs/handoff-stratified.md` §5). What is
  claimed is that it is now the *only* thing the model needs.
* **It does not claim `PropTypeAgree ⟹ PropUniq` without `hf`.**
* **It does not shorten the inductive keystone or `PreludeBridge`.**
* **It does not remove the parameter.** `PropSplit` is still a hypothesis
  nothing in the tree constructs; §7 narrows what would construct it from two
  open statements to one.

## What the model still needs from the syntax side

The interpretation `⟦Γ ⊢ e⟧` is now **defined** — see `SetModel/Interp.lean` —
relative to a `LevelAssign`, which packages exactly Carneiro's `lvl`/`sort`
lemma. What remains from the syntax side is:

1. **`PropTypeAgree`** — and, since §7, **that alone**: `PropUniq` is
   discharged from the goal's own `hfalse`, and both statements reduce to zero
   universe parameters. Not `IsDefEqU.sort_inv`. See §5: the interpretation
   branches on propositionhood, never on a level, so what it imports is that a
   term's types agree on being propositions. `sort_inv`/`SortUniq` is
   *sufficient* (it gives a `LevelAssign`, which gives a `PropSplit`) and is
   known **not** to be a semantic consequence; `PropTypeAgree` is what is
   actually needed and is not refuted by the same check. Notably *not*
   `IsDefEqU.forallE_inv` or `IsDefEqU.sort_forallE_inv`: the interpretation's
   definition uses neither.

   The paragraph below is the old scoping of this item, kept because its
   diagnosis of `srt_sound` is what led to §5.

   **Caveat on scope.** "`sort_inv` is all a `LevelAssign` needs" is a claim
   about the `lvl` field. `srt_sound` asks that `srt Γ e ≈ lvl Γ A` for *every*
   `A` typing `e`, and `srt` can only choose one — so it also needs the sorts of
   a term's two types to agree, and nothing links those without `A ≈ A'`, which
   is unique typing. `LevelAssign.srt_uniq` (`SetModel/Interp.lean`) is the
   necessary condition that makes this testable; the test is to attempt
   `levelAssign_of_sort_inv` and see which hypothesis the second field demands.
1b. **`PropDescend env 0`** — and, since `SetModel/AboveAudit.lean`, together with item 1
   that is the *whole* proof-split side of `ModelFits`. `ModelFits`'s relation parameter is
   no longer an obligation at all: `CtxAgree L` is the greatest `CtxInvariant` relation, so
   the existential over `R` is eliminable (`modelFits_iff_ctxAgreeRd`), and for
   `PropSplitAudit.propSplitOf` the pairing hypothesis `hRd` is **discharged** —
   `IsDefEq.defeqDFC'` already carries an arbitrary common prefix, and `propSplitOf`'s two
   predicates contain their own typing derivations, so nothing well-typedness-shaped has to
   be supplied. Net: `modelFits_of_propSplit_inputs` builds `ModelFits` from
   `Ordered`, `PropUniq 0`, `PropTypeAgree 0`, `PropDescend 0` and `OracleFits` alone.
2. **`NoBlock.indep`** (§2) — the remaining obligation that makes `interpSig`
   well defined. `interp_congr` is **no longer on this list**: it is proved
   (§4), and its `Above`-wrapped form is sufficient.
3. The constant assignment `ModelData.cnst` and its coherence with `env.defeqs`,
   by induction over the declaration list. The `.quot` form of this is complete
   — all four `const_type` obligations and both `quotDefEq` obligations, in
   `SetModel/QuotInterp.lean`. The `.induct` **step** is now complete too:
   `coherentOn_addInduct` (`SetModel/IndInterp.lean`). It pushes the
   per-constant `OracleOK` and the per-ι-rule obligations out to the caller,
   where the translation supplies them.
4. **The `VIndCtor → CtorData₃`/`Args` translation** — **done**,
   `SetModel/CtorTrans.lean`, sorry-free and instantiated at `Acc`, `W'` and
   `Forest'.cons` in `SetModel/CtorTransExamples.lean`. See "The translation,
   built" in §2 for the layout and for the two corrections it forced.

   **`VIndField.WF.binders_indep` is not consumed by it.** The clause was added
   for the blanking layout, where `Pos q a` has to be evaluated without the
   fillers; the layout taken carries them, so `⟦ξ⟧` is evaluated at a valuation
   that has them. The clause is not wasted — it is exactly what
   `IsSubsingletonSignature₃.pos_det` will need for a large-eliminating
   subsingleton — but it is no longer on the critical path, and neither is its
   open discharge obligation `VIndRecArg.exists_indep` (which remains `sorry`,
   blocked on `IsDefEqU.forallE_inv`). Nothing in `CtorTrans.lean` depends on
   `sorryAx`; the three standard axioms are the whole footprint.

   What `.induct` still lacks after this is *not* the translation but the
   obligations `coherentOn_addInduct` pushes to its caller: the per-constant
   `OracleOK` (a constructor's and a recursor's value inhabiting its declared
   type) and the per-ι-rule pair. Those are the `Quot.mk`-shaped work, one
   nesting level deeper.

5. **`interpSig₃_wf` / `_stage` at this data** — the *plumbing* is now done
   (`SetModel/CtorTrans.lean`, section "The two assembly obligations, reduced to
   this data"), and doing it separately from discharging them was worth it,
   because the two obligations turn out to owe completely different things.

   | obligation | what the reduction leaves |
   |---|---|
   | `interpSig₃_wf` | **one statement per constructor**: the result-index tuple `⟦C.args⟧` inhabits the block member's index telescope `⟦T.indices⟧`. Nothing else survives — in particular the *recursive* fields contribute nothing, since `resIdx` does not read them. |
   | `interpSig₃_stage` | four stage memberships: `Q` (a numeral), and `Idx`, `Fld`, `Pos` (telescope sums). |

   **The `wf` row bottoms out at `interp_congr`, which is proved.** Run at `Acc`
   (`accSig_wf`), the per-constructor statement collapses to "the block-free
   replacement for field 0's type denotes what `α` denotes" — §4's congruence
   and nothing more. `accInd_subsingleton_of_congr` composes it with the
   subsingleton instance, leaving `IsIndCarrier₃` as the only standing
   hypothesis, and that one is not specific to `Acc`.

   **The `stage` row is reduced all the way to the domains** —
   `interpSig₃_stage_of_domains`. `teleFun`'s elements are internal *sequences*,
   so it needs `snoc ρ x` in the stage; that looked like a missing model-side
   tower, and **it was not** — `SetModel/Rank.lean` already has
   `insert_mem_Vset`, `kpair_mem_Vset`, `domain_mem_Vset`, `union_mem_Vset`,
   `prod_mem_Vset`, `singleton_mem_Vset`, and `mem_vsetV_iff_mem_Vset` is
   `Iff.rfl`. `snoc_mem_vsetV`, `teleFun_mem_vsetV` and `tagUnionF_mem_vsetV`
   are four short lemmas over that, all proved. *Recorded because the check
   took under a minute and the wrong reading survived a whole paragraph of this
   document: grep at the `Vset` level, not the `U` level.*

   What is left is exactly `⟦_⟧ ∈ vsetV k` for three families of domains — the
   index telescopes, the field domains, the recursive fields' `ξ` — plus
   `params ∈ vsetV k`. That is soundness part 3 and nothing else.

   **A defect found and fixed on the way.** `mkIndSignature₃_stage`'s `hpos`
   quantified over an **arbitrary** `a : V`, while `IsStageSignature₂.pos_mem`
   only ever uses it above an element of `Fld`. The stronger form is not merely
   wasteful, it is **false at the translation**: `Pos q a` evaluates `⟦ξ⟧` at
   `a ↾ (np + i)`, so a junk `a` reads `⟦.bvar j⟧` off an unbounded valuation
   and no stage contains the result. Had the reduction been done by assuming
   the assembly-level hypothesis rather than by attempting to discharge it, the
   whole `stage` line would have rested on an unsatisfiable premise — the exact
   failure mode `docs/soundness-ledger.md` keeps warning about, caught here only
   because the premise was pushed down to something checkable. The premise is
   now the one the structure actually uses.

Nothing else on the set-theoretic side is outstanding.

## Where things live

| | |
|---|---|
| `SetModel/Rank.lean` | `Vset`, `rank`, `mem_induction`, `rank_induction`, `value_eq_of_kpair_mem` |
| `SetModel/Inaccessible.lean` | `IsInaccessible` and the chain from the axiom schema; `Pi`/`Sigma`; `lfp`; `acc` |
| `SetModel/Universe.lean` | `UProp`, `propext_of_mem_UProp`, `piProp`, `U`, the closure tiers, choice, `Quot` |
| `SetModel/Cardinal.lean` | `\|V_β\| < κ`, full replacement in `Vset κ` |
| `SetModel/Inductive.lean` | `IndSignature`, `Ind`, constructors, recursor, ι-rule |
| `SetModel/IndStage.lean` | `IsStageSignature`, the carrier discharged, the `…_stage` forms |
| `SetModel/IndCard.lean` | `Ind_mem_vsetV` / `Ind_mem_U_stage` |
| `SetModel/Interp.lean` | `LevelAssign`, `interp`, `interpCtx`, proof splitting |
| `SetModel/IndInterp.lean` | `IndSignature₂`/`₃` and the port, `mkIndSignature₃`, `interpSig_wf`/`_stage`, `coherentOn_addInduct` |
| `SetModel/CtorTrans.lean` | the `VIndCtor → CtorData₃`/`Args` translation, `interpSig₃`, `Ind₃_subsingleton`, the tag-combinator congruences, `interpSig₃_wf`/`_stage`, `interpSig₃_stage_of_domains`, stage closure for `snoc`/`teleFun`/`tagUnionF` |
| `SetModel/PropSplitAudit.lean` | `PropUniq`, `PropTypeAgree`, and the three-part satisfiability audit for `PropSplit` |
| `SetModel/PropReduce.lean` | `VLevel.ofNat`/`numerals`/`eval_eq_of_wf`; `PropUniq.of_zero`, `PropTypeAgree.of_zero` — both statements reduce to `nv = 0` |
| `SetModel/PropUniqFromFalse.lean` | `PropUniq.of_propTypeAgree` (§7), `propSplitOfAgree`, and the satisfiability witness for its hypothesis pair |
| `SetModel/FalseProp.lean` | `interp_falseProp` (`⟦∀ p : Prop, p⟧ ∅ = ∅`, branch-independent), `falseProp_above_false`, the non-vacuity instances |
| `SetModel/CtorTransExamples.lean` | the translation applied to `Acc`, `W'`, `Forest'.cons`; the `IsSubsingletonSignature₃` instance and `accSig_wf` |
| `SetModel/Cnst.lean` | `cnstOf`, `oracleExtend`, `CoherentOn` and its `addConst`/`addDefEq`/`addConstList` steps |
| `SetModel/InaccChainOmega.lean` | `inaccSeq`, `exists_inaccessibleChain_omega` (one `κ` for every finite length), `ModelExistsInput` |
| `SetModel/ModelExists.lean` | `modelExistsInput` / `inaccModelInput` — **Input A discharged**; `upper_bound_of_modelFits`; `ZFCInaccModel`; the two-way bounds |
| `SetModel/AboveAudit.lean` | the `Above` vacuity witnesses (`above_false_zeroChain`), the wrapper-stripping equivalences (`oracleOK_iff_of_chain`, `inductOracleOK_iff_of_chain`, `coherentOn_iff_of_chain`, `above_omegaChain_iff`), `CtxAgree`/`CtxAgreeRd` and `modelFits_iff_ctxAgreeRd`, `modelFits_of_propSplit_inputs` |
| `SetModel/InductOracleWitness.lean` | the empty-domain `λ`/`∀` lemmas; `zeroOracle`; `inductOracleOK_zero`, `oracleFits_zero`, `coherentOn_zero` — the `.induct` residual's positive bound at a `WF` block |
| `SetModel/UnitOracleLarge.lean` | the four `interp`-free `mkForallType`/`mkLam` lemmas (`mem_mkForallType_of_graph`, `mkLam_mem_mkForallType_of_dom`, `mkForallType_singleton_const`, `mkLam_ext`); `unitDeclLE`'s environment and `WF`; `recFn3`/`recFn2`/`recFnL` and `recFnL_beta`; `interpL_motTyU`; the `= 0` / `≠ 0` slices; `inductOracleOKL`, `oracleFitsL`, `oracleFitsL_at_consumer`; `pt_not_mem_interpL_recType_of_ne` |
| `SetModel/UnitOracleWitness.lean` | `unitDecl`/`unitEnv`/`unitOracle`; `unitDecl_WF`, `unitDecl_history`; the branch facts from typing (`isProp_recB*`, `isProof_iota*Lam`); `inductOracleOK_unit`, `oracleFits_unit`, `oracleFits_unit_at_consumer` — the same bound with **no empty domain**; `exists_true_motive`, `pt_not_mem_mkForallType_of_nonempty`, `not_defEqOK_falseType` |
| `docs/foundation-gaps.md` | what Foundation is missing, and the `isDefEq` hazard |
