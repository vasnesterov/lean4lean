# The syntax ↔ set-theory boundary

Specification of the interface between `Lean4Lean/Theory/` (the abstract syntax
and its judgements) and `Lean4Lean/Theory/SetModel/` (the ZFC model). Written
from the model side, because the constraints below are what the model can
actually consume; neither side can design this boundary alone.

The model side is complete apart from the interpretation itself. Everything
cited here is proved, sorry-free, in `SetModel/`.

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

**The escape hatch, if `NoBlock.indep` turns out to be hard or false.**
Generalise the model side rather than the syntax side: replace `Fld : V → V` by
a monotone `Fld : V → V → V` taking the current approximation of the family, and
have `Pos`/`posIdx`/`resIdx` defined on the resulting dependent sum. `indStep`
stays monotone, so formation (`Ind_mem_U_stage`) and the induction principle
survive unchanged; what needs redoing is the rank argument for the recursor,
since the "non-recursive data" `a` would then itself contain family elements.
Tell the model side if this becomes necessary — it is a bounded change, but not
a free one.

**Do not weaken `pos` to a syntactic `NoBlock`.** That would make step 2 trivial,
but it rejects types the kernel accepts (`checkPositivity` applies `hasIndOcc` to
the whnf), so the spec would no longer refine the kernel.

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

## What the model still needs from the syntax side

The interpretation `⟦Γ ⊢ e⟧` is now **defined** — see `SetModel/Interp.lean` —
relative to a `LevelAssign`, which packages exactly Carneiro's `lvl`/`sort`
lemma. What remains from the syntax side is:

1. **`IsDefEqU.sort_inv`**, which is what a `LevelAssign` needs — and nothing in
   the tree exhibits a `LevelAssign`, so this is the one unwitnessed hypothesis
   the whole set model rests on. Notably *not* `IsDefEqU.forallE_inv` or
   `IsDefEqU.sort_forallE_inv`: the interpretation's definition uses neither.

   **Caveat on scope.** "`sort_inv` is all a `LevelAssign` needs" is a claim
   about the `lvl` field. `srt_sound` asks that `srt Γ e ≈ lvl Γ A` for *every*
   `A` typing `e`, and `srt` can only choose one — so it also needs the sorts of
   a term's two types to agree, and nothing links those without `A ≈ A'`, which
   is unique typing. `LevelAssign.srt_uniq` (`SetModel/Interp.lean`) is the
   necessary condition that makes this testable; the test is to attempt
   `levelAssign_of_sort_inv` and see which hypothesis the second field demands.
2. **`NoBlock.indep`** (§2) — the remaining obligation that makes `interpSig`
   well defined. `interp_congr` is **no longer on this list**: it is proved
   (§4), and its `Above`-wrapped form is sufficient.
3. The constant assignment `ModelData.cnst` and its coherence with `env.defeqs`,
   by induction over the declaration list. The `.quot` form of this is complete
   — all four `const_type` obligations and both `quotDefEq` obligations, in
   `SetModel/QuotInterp.lean`. The `.induct` form is what `interpSig` is for.

Nothing on the set-theoretic side is outstanding.

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
| `docs/foundation-gaps.md` | what Foundation is missing, and the `isDefEq` hazard |
