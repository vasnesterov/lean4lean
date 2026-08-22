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

**F8 is vacuous, and `VIndField.WF.pos` is what makes it so.** In the `none`
branch, `pos` asks only for `∃ A, D.NoBlock A ∧ IsDefEqType … F.type A` — the
field type is *definitionally* block-free. Since the interpretation is
defeq-invariant (§4), `⟦F.type⟧` is independent of the family being constructed,
so `Fld : V → V` is correct as written. Do not weaken `pos` to a syntactic
`NoBlock`: that would reject types the kernel accepts, and it is also what keeps
this interface simple.

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

## 4. Defeq-invariance is part of the contract

State it at the boundary:

```lean
theorem interp_congr (h : env.IsDefEq uvars Γ e e' A) : ⟦e⟧ = ⟦e'⟧
```

rather than deriving it downstream. Two reasons.

* The model *needs* it, and needs it early. §2's F8 argument is exactly an
  appeal to it: `VIndField.WF.pos` gives only definitional block-freeness, so
  `⟦F.type⟧` is well-defined as an `X`-independent set only because defeq terms
  interpret equally.
* Almost every model-side step replaces a type by a definitionally equal one —
  `VIndType.WF.canon`, `VIndCtor.WF.params_eq`, and the `IsDefEqType` clauses
  throughout `VIndField.WF` all hand the model a `≈` where it wants an `=`. If
  invariance is a downstream lemma, every one of those becomes a separate
  obligation.

Practically this means the interpretation should be defined on the *judgement*,
or defined on terms with `interp_congr` proved by the same induction that proves
totality — not bolted on afterwards.

---

## What the model still needs from the syntax side

Only the interpretation itself. It is blocked on Carneiro's proof-splitting,
which needs the `lvl`/`sort` functions, which need unique typing — i.e. on
`Theory/Typing/Injectivity.lean`. Nothing on the set-theoretic side is
outstanding.

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
| `docs/foundation-gaps.md` | what Foundation is missing, and the `isDefEq` hazard |
