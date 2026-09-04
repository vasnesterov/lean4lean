import Lean4Lean.Theory.Inductive.IndepResidual
import Lean4Lean.Theory.Typing.InjCorner

/-!
# The two-substitution argument at a **field** context

`Theory/Inductive/IndepResidual.lean` §2b closes the sharpest form of the residual behind
`VIndRecArg.exists_indep` — the block-free side is an *arbitrary* type `A` and what is excluded is
`A ≡ I_j p π` outright — and states its own gap at :302:

> Unlike §2a this needs `Γ` block-free, because `σ` and `σ'` send the same context to *different*
> contexts and `isDefEqType_trans_of_sortUniq` needs one context.  Where the hole lives `Γ` is not
> block-free, so this lemma covers the `.lam`-domain route only when every earlier field is
> non-recursive.

This file answers that gap, and the answer is **negative with a witness**: the two-substitution
argument does not reach a field context, and the obstruction is exact rather than technical.

## §1 The side condition, minimised

`noBlockType_not_defeqType_blockSpine_ctxEq` is `IndepResidual.noBlockType_not_defeqType_blockSpine`
with `hΓ : ∀ C ∈ Γ, D.NoBlock C` replaced by the *weakest* thing the proof uses:
`hΓeq : Γ.map (·.substC σ) = Γ.map (·.substC σ')` — the two substituted contexts agree.  Block-free
`Γ` implies it (`ctxEq_of_noBlock`), so this is a strict generalisation, and everything below is a
statement about `hΓeq` rather than about the proof.

## §2 The obstruction, at the tree's own field context

`RecArgIndep.raiΓ` is a real field context: `raiΓ_eq` proves it is literally
`(raiPre.map (·.type)).reverse ++ raiD.params.reverse`, the hole's own `hΓ`, and it is *not*
block-free — its single entry is field 0's stored type, the block spine `raiI` on the nose
(`raiΓ_not_noBlock`, by `decide`).  At that context the entry **is** the judgement's right-hand
side, so:

* `substC_ctxEq_iff` — the side condition `hΓeq` is *equal to* "the two replacement values agree";
* `not_substC_ctxEq_of_shapes` — and the sort/Π requirement forbids that, so `hΓeq` is **false**
  for every admissible pair `σ`, `σ'`.  Not "hard to establish": false.
* `images_conv_refutes_sortPiDisjNil` — relaxing `hΓeq` from equality to a *conversion* of the two
  images does not help either: at `raiΓ` that conversion **is** `VEnv.SortPiDisjNil env₁ U`, the
  empty-context form of the very predicate the argument reduces to
  (`VEnv.rigidSortPiDisj_iff_nil`).  `rai_side_condition_iff_open_instance` states the two as
  one `↔`, and at the tree's own pair `Rai.raiσ`/`Rai.raiσ'` it is `Prop ≡ (Prop → Prop)` — the
  single open instance `VEnv.nil_endpoints_typeable` names.
* `common_inhabitant_refutes` — and so does the third reconciliation, instantiating the offending
  context variable by a closed inhabitant on each side: that needs one term inhabiting both images,
  which under `VEnv.UniqTy` is again `sort ≡ Π`.

So all three ways to run the argument at a field context are **self-blocking**: each side condition
holds only if the predicate the argument reduces to fails.  The reason is structural, and §2's
prose states it: every transport available at this layer (`substC`, `instN`, Π-abstraction of the
context, instantiating a context variable) is a homomorphism on syntax, so a transport that sends
the block to two different values sends *every* block occurrence to two different things.  The
block occurs in the field context.  The mismatch therefore moves — context → term → environment —
and is never annihilated.

## §3 What replaces it: one substitution, and no hypothesis on `Γ` at all

The composition is what needed two contexts, so the repair is to not compose.  Case on the shape of
`A`: if `A` is a sort, the Π-valued substitution alone contradicts `RigidSortPiDisj`; otherwise the
sort-valued substitution alone contradicts **`SortRigid`** — "nothing but a sort is convertible to a
sort".  `noBlockType_not_defeqType_blockSpine_oneSubst` is that theorem: no `SortUniq`, no
`Ordered env₁`, no composition, and **no hypothesis on `Γ`**, so it fires at a field context.

## §4 …and what that costs, stated as a theorem rather than a hope

`SortRigid` is strictly the wrong shape to be free: `SortRigid.rigidSortPiDisj` shows it implies the
old target, and `not_sortRigid_wf_sortAbbrevEnv` shows it is **false at a `VEnv.WF` environment** —
`def rogueC : Sort 1 := Prop` is an ordinary declaration, and its constant is a non-sort convertible
to a sort.  `RigidSortPiDisj`, by contrast, is only known false at `Ordered` environments
(`IndepResidual.not_rigidSortPiDisj_rogueSortPiEnv`), and is *conjectured* at `VEnv.WF` ones.  So §3
buys the field context at the price of a predicate that no rich environment satisfies.  What makes
it not vacuous is the same thing that makes `IndepResidual` §3 work: the target environment is `∅`,
which has no δ-rule to abbreviate a universe with — `not_sortRigid_of_sortAbbrev` says a δ-rule to a
sort is exactly what refutes `SortRigid`, and `∅` has none.

## §5 Fired at the field context

`rai_fieldCtx_noBlockType_not_defeqType_blockSpine`: at `RecArgIndep.raiEnv0`, over the **field**
context `raiΓ`, no block-free type is convertible to the block constant — from the single
hypothesis `SortRigid ∅ 0`.  The `OnCtx` side condition is *discharged*, not assumed.  For contrast,
`IndepResidual.Rai.rai_noBlockType_not_defeqType_blockSpine` cannot be *instantiated* at `raiΓ`:
`raiΓ_not_noBlock` refutes the `hΓ` it would have to be given.
-/

namespace Lean4Lean
namespace BlockCtx

open VExpr (mkApp)
open IndepResidual

/-! ## §1 The two-substitution argument, with the side condition minimised -/

/-- `IndepResidual.blockSpineType_defeq_transport` with the context **substituted** rather than
required block-free — the `IsDefEqType` form of `IndepResidual.blockSpine_defeq_transport_ctx`,
which is the §2a move the sharpest form never got. -/
theorem blockSpineType_defeq_transport_ctx {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {U : Nat} {Γ : List VExpr} {A t : VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hA : D.NoBlock A) (has : ∀ a ∈ as, D.NoBlock a)
    (H : env.IsDefEqType U Γ A (mkApp (.const c ls) as)) :
    env₁.IsDefEqType U (Γ.map (VExpr.substC · σ)) A (mkApp (t.instL ls) as) := by
  have := isDefEqType_substC hσ H
  rwa [(VExpr.NoConsts.noCSubst hdom₁ hA).substC_eq,
    VExpr.substC_mkApp, VExpr.substC_const_some ht,
    VExpr.map_substC_eq_self (fun a ha => VExpr.NoConsts.noCSubst hdom₁ (has a ha))] at this

/-- **The two-substitution argument, over the weakest context hypothesis its proof uses.**

`IndepResidual.noBlockType_not_defeqType_blockSpine` asks `Γ` to be block-free; all the proof needs
is that the *images* of `Γ` under the two substitutions coincide, which is what
`RecArgIndep.isDefEqType_trans_of_sortUniq` consumes.  Stating it this way is what makes §2 possible:
the obstruction becomes a fact about `hΓeq` rather than a fact about a proof. -/
theorem noBlockType_not_defeqType_blockSpine_ctxEq {env env₁ : VEnv} {D : VInductDecl'}
    {σ σ' : CSubst} {U : Nat} {Γ : List VExpr} {A t t' A' B' : VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {v : VLevel}
    (henv₁ : env₁.Ordered) (hsu : env₁.SortUniq U) (hsp : env₁.RigidSortPiDisj U)
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hσ' : σ'.WF env env₁ U) (hdom₁' : ∀ c, σ' c ≠ none → c ∈ D.blockNames)
    (ht' : σ' c = some t')
    (hsort : mkApp (t.instL ls) as = .sort v)
    (hpi : mkApp (t'.instL ls) as = .forallE A' B')
    (hΓeq : Γ.map (VExpr.substC · σ) = Γ.map (VExpr.substC · σ'))
    (hΓon : OnCtx Γ (env.IsType U))
    (hA : D.NoBlock A) (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqType U Γ A (mkApp (.const c ls) as) := fun H => by
  have h1 := blockSpineType_defeq_transport_ctx hσ hdom₁ ht hA has H
  have h2 := blockSpineType_defeq_transport_ctx hσ' hdom₁' ht' hA has H
  rw [hsort] at h1
  rw [hpi, ← hΓeq] at h2
  have hΓ' := onCtx_substC hσ hΓon
  exact hsp hΓ' (RecArgIndep.isDefEqType_trans_of_sortUniq henv₁ hsu hΓ' h1.symm h2).toU

/-- A block-free context satisfies the side condition, so §1 strictly generalises
`IndepResidual.noBlockType_not_defeqType_blockSpine`. -/
theorem ctxEq_of_noBlock {D : VInductDecl'} {σ σ' : CSubst} {Γ : List VExpr}
    (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (hdom₁' : ∀ c, σ' c ≠ none → c ∈ D.blockNames)
    (hΓ : ∀ C ∈ Γ, D.NoBlock C) :
    Γ.map (VExpr.substC · σ) = Γ.map (VExpr.substC · σ') := by
  rw [VExpr.map_substC_eq_self (fun C hC => VExpr.NoConsts.noCSubst hdom₁ (hΓ C hC)),
    VExpr.map_substC_eq_self (fun C hC => VExpr.NoConsts.noCSubst hdom₁' (hΓ C hC))]

/-! ## §2 The obstruction, at `RecArgIndep.raiΓ` — a real field context

`RecArgIndep.raiΓ_eq` is the receipt that this is the hole's own context shape, and the entry is
field 0's stored type: a recursive field, `ξ = []`, `π = []`, so the stored type is the block
constant on the nose. -/

open RecArgIndep (raiI raiD raiΓ raiPre)

/-- **The field context is not block-free** — so `IndepResidual`'s §2b lemma and its `Rai`
instantiation, both of which take `hΓ : ∀ C ∈ Γ, D.NoBlock C`, cannot be instantiated at this `Γ`.
They are not vacuous (a block-free `Γ` satisfies `hΓ`); they are unusable at the context the hole
hands them. -/
theorem raiΓ_not_noBlock : ¬ ∀ C ∈ raiΓ, raiD.NoBlock C := by decide

/-- The field context is exactly one block spine, so its image under `σ` is exactly `σ`'s value. -/
theorem raiΓ_substC {σ : CSubst} {t : VExpr} (h : σ raiI = some t) :
    raiΓ.map (VExpr.substC · σ) = [t.instL []] := by
  simp [raiΓ, VExpr.substC_const_some h]

/-- **The side condition, decoded.**  At a field context whose entry is the block spine, "the two
substituted contexts agree" is *the same statement as* "the two replacement values agree". -/
theorem substC_ctxEq_iff {σ σ' : CSubst} {t t' : VExpr}
    (h : σ raiI = some t) (h' : σ' raiI = some t') :
    (raiΓ.map (VExpr.substC · σ) = raiΓ.map (VExpr.substC · σ')) ↔ t.instL [] = t'.instL [] := by
  rw [raiΓ_substC h, raiΓ_substC h']
  simp

/-- **The obstruction, syntactic half.**  The two substitutions the argument needs are one
sort-valued and one Π-valued; at a field context that makes `hΓeq` **false**.  There is no pair of
admissible substitutions to look for. -/
theorem not_substC_ctxEq_of_shapes {σ σ' : CSubst} {t t' A' B' : VExpr} {v : VLevel}
    (h : σ raiI = some t) (h' : σ' raiI = some t')
    (hsort : t.instL [] = .sort v) (hpi : t'.instL [] = .forallE A' B') :
    raiΓ.map (VExpr.substC · σ) ≠ raiΓ.map (VExpr.substC · σ') := by
  intro he
  rw [substC_ctxEq_iff h h', hsort, hpi] at he
  cases he

/-- **The obstruction, conversion half.**  Weakening `hΓeq` from syntactic equality to a conversion
of the two images — the "block-spine-only context" route — does not escape either: at a field
context that conversion *is* `VEnv.SortPiDisjNil`, the empty-context form of the predicate the
whole argument reduces to. -/
theorem images_conv_refutes_sortPiDisjNil {env₁ : VEnv} {U : Nat} {σ σ' : CSubst}
    {t t' A' B' : VExpr} {v : VLevel}
    (h : σ raiI = some t) (h' : σ' raiI = some t')
    (hsort : t.instL [] = .sort v) (hpi : t'.instL [] = .forallE A' B')
    (hconv : ∀ X ∈ raiΓ, env₁.IsDefEqU U [] (X.substC σ) (X.substC σ')) :
    ¬ VEnv.SortPiDisjNil env₁ U := by
  intro hnil
  have hx := hconv (.const raiI []) (by simp [raiΓ])
  rw [VExpr.substC_const_some h, VExpr.substC_const_some h', hsort, hpi] at hx
  exact hnil hx

/-- …and therefore refutes the target itself, via `VEnv.RigidSortPiDisj.nil`. -/
theorem images_conv_refutes_target {env₁ : VEnv} {U : Nat} {σ σ' : CSubst}
    {t t' A' B' : VExpr} {v : VLevel}
    (h : σ raiI = some t) (h' : σ' raiI = some t')
    (hsort : t.instL [] = .sort v) (hpi : t'.instL [] = .forallE A' B')
    (hconv : ∀ X ∈ raiΓ, env₁.IsDefEqU U [] (X.substC σ) (X.substC σ')) :
    ¬ env₁.RigidSortPiDisj U := fun hsp =>
  images_conv_refutes_sortPiDisjNil h h' hsort hpi hconv hsp.nil

/-- **The two propositions are one.**  At the tree's own pair of substitutions
(`IndepResidual.Rai.raiσ` sort-valued, `Rai.raiσ'` Π-valued), the relaxed side condition at the
field context is *literally* `Prop ≡ (Prop → Prop)` at the empty context — the single open instance
`VEnv.nil_endpoints_typeable` names as `RigidSortPiDisj`'s residual.  So running the argument at a
field context and closing the hole are the same problem, not two. -/
theorem rai_side_condition_iff_open_instance {env₁ : VEnv} {U : Nat} :
    (∀ X ∈ raiΓ, env₁.IsDefEqU U [] (X.substC Rai.raiσ) (X.substC Rai.raiσ')) ↔
      env₁.IsDefEqU U [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) := by
  constructor
  · intro h
    have hx := h (.const raiI []) (by simp [raiΓ])
    rwa [VExpr.substC_const_some Rai.raiσ_raiI, VExpr.substC_const_some Rai.raiσ'_raiI] at hx
  · intro h X hX
    simp only [raiΓ, List.mem_singleton] at hX
    subst hX
    rwa [VExpr.substC_const_some Rai.raiσ_raiI, VExpr.substC_const_some Rai.raiσ'_raiI]

/-- **The syntactic half, fired at the tree's own pair.**  `IndepResidual.Rai.raiσ` and `Rai.raiσ'`
send the field context to `[Prop]` and `[Prop → Prop]` — so there is nothing to repair: the side
condition `hΓeq` is *false*, and what would repair it is `Prop ≡ (Prop → Prop)`. -/
theorem rai_substC_ctxEq_false :
    raiΓ.map (VExpr.substC · Rai.raiσ) = [.sort .zero] ∧
      raiΓ.map (VExpr.substC · Rai.raiσ') = [.forallE (.sort .zero) (.sort .zero)] ∧
      raiΓ.map (VExpr.substC · Rai.raiσ) ≠ raiΓ.map (VExpr.substC · Rai.raiσ') :=
  ⟨raiΓ_substC Rai.raiσ_raiI, raiΓ_substC Rai.raiσ'_raiI,
    not_substC_ctxEq_of_shapes Rai.raiσ_raiI Rai.raiσ'_raiI rfl rfl⟩

/-- **The third reconciliation is circular too.**  Instead of matching the two contexts one can try
to *remove* them, instantiating the offending context variable with a closed inhabitant on each
side; but the two judgements only recombine if the *same* `w` is used, and a `w` inhabiting both
images gives `sort ≡ Π` by unique typing.  So this route also holds only when the target fails. -/
theorem common_inhabitant_refutes {env₁ : VEnv} {U : Nat} {w A' B' : VExpr} {v : VLevel}
    (huq : env₁.UniqTy U)
    (h1 : env₁.HasType U [] w (.sort v)) (h2 : env₁.HasType U [] w (.forallE A' B')) :
    ¬ VEnv.SortPiDisjNil env₁ U := fun hnil => hnil (huq trivial h1 h2)

/-! ## §3 The replacement: one substitution, and no hypothesis on the context -/

/-- **Sort-rigidity**: nothing but a sort is convertible to a sort.

This is the price of not composing.  The two-substitution argument needed `sort ≢ Π` *plus* a
transitivity step through `A`; a single substitution needs to know `A` itself is not convertible to
the substituted value's shape, which for a sort-shaped value is exactly this.  See §4 for what it
costs — it is refutable at a `VEnv.WF` environment, which `RigidSortPiDisj` is not known to be. -/
def SortRigid (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {v : VLevel}, OnCtx Γ (env.IsType U) →
    (∀ w, A ≠ .sort w) → ¬ env.IsDefEqU U Γ A (.sort v)

/-- `SortRigid` is at least as strong as the old target: `RigidSortPiDisj` is its `A = Π`
instance. -/
theorem SortRigid.rigidSortPiDisj {env : VEnv} {U : Nat} (h : SortRigid env U) :
    env.RigidSortPiDisj U := by
  intro Γ u A B hΓ hc
  refine h hΓ ?_ hc.symm
  exact fun _ => nofun

/-- Either `A` is a sort or it is not — decided by cases on the constructor, so no `Classical`. -/
theorem sort_or_not (A : VExpr) : (∃ w, A = .sort w) ∨ ∀ w, A ≠ .sort w := by
  cases A <;> first
    | exact .inl ⟨_, rfl⟩
    | exact .inr fun _ => nofun

/-- **No block-free type is convertible to a block spine — over an arbitrary context.**

The hypothesis budget: two substitutions of the block into `env₁`, one landing on a sort and one on
a Π, and two predicates at `env₁`.  What is *not* in it, compared with
`IndepResidual.noBlockType_not_defeqType_blockSpine`: `VEnv.SortUniq env₁`, `VEnv.Ordered env₁`, and
— the point — any hypothesis on `Γ`.  Neither substitution is composed with the other; each case
uses one of them alone, which is why the two images of `Γ` never have to be compared.

`hsp` is redundant given `hsr` (`SortRigid.rigidSortPiDisj`) and is taken separately only so that a
consumer holding just `RigidSortPiDisj` can see which case needs which. -/
theorem noBlockType_not_defeqType_blockSpine_oneSubst {env env₁ : VEnv} {D : VInductDecl'}
    {σ σ' : CSubst} {U : Nat} {Γ : List VExpr} {A t t' A' B' : VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {v : VLevel}
    (hsr : SortRigid env₁ U) (hsp : env₁.RigidSortPiDisj U)
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hσ' : σ'.WF env env₁ U) (hdom₁' : ∀ c, σ' c ≠ none → c ∈ D.blockNames)
    (ht' : σ' c = some t')
    (hsort : mkApp (t.instL ls) as = .sort v)
    (hpi : mkApp (t'.instL ls) as = .forallE A' B')
    (hΓon : OnCtx Γ (env.IsType U))
    (hA : D.NoBlock A) (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqType U Γ A (mkApp (.const c ls) as) := fun H => by
  obtain ⟨w, rfl⟩ | hns := sort_or_not A
  · have h2 := blockSpineType_defeq_transport_ctx hσ' hdom₁' ht' hA has H
    rw [hpi] at h2
    exact hsp (onCtx_substC hσ' hΓon) h2.toU
  · have h1 := blockSpineType_defeq_transport_ctx hσ hdom₁ ht hA has H
    rw [hsort] at h1
    exact hsr (onCtx_substC hσ hΓon) hns h1.toU

/-! ## §4 What §3 costs: `SortRigid` is refuted by a single δ-rule to a sort -/

/-- **A δ-rule whose right-hand side is a sort refutes `SortRigid`.**  One rule, no hub: contrast
`IndepResidual.not_rigidSortPiDisj_rogueSortPiEnv`, whose witness needs *two* rules out of one
constant and is therefore not `VEnv.WF`. -/
theorem not_sortRigid_of_sortAbbrev {env : VEnv} {U : Nat} {df : VDefEq} {ls : List VLevel}
    {u : VLevel} (hdf : env.defeqs df) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    (hne : ∀ w, df.lhs.instL ls ≠ .sort w) (hrhs : df.rhs.instL ls = .sort u) :
    ¬ SortRigid env U := fun h =>
  h (Γ := []) trivial hne ⟨_, hrhs ▸ VEnv.IsDefEq.extra (Γ := []) hdf hls hlen⟩

/-- `def rogueC : Sort 1 := Prop` — `VEnv.rogueEnv1` plus `VEnv.rogueDfSort`, which
is the *first* of `rogueSortPiEnv`'s two rules taken alone. -/
def sortAbbrevVal : VDefVal where
  uvars := 0
  type := .sort (.succ .zero)
  name := VEnv.rogueC
  value := .sort .zero

theorem sortAbbrevVal_toDefEq : sortAbbrevVal.toDefEq = VEnv.rogueDfSort := by
  simp [sortAbbrevVal, VDefVal.toDefEq, VEnv.rogueDfSort, VLevel.params]

/-- The environment of that one declaration. -/
def sortAbbrevEnv : VEnv := VEnv.rogueEnv1.addDefEq VEnv.rogueDfSort

theorem sortAbbrev_decl_wf : VDecl.WF VEnv.empty (.def sortAbbrevVal) sortAbbrevEnv := by
  have h := VDecl.WF.def (env := VEnv.empty) (ci := sortAbbrevVal) (env' := VEnv.rogueEnv1)
    (show VDefVal.WF _ _ from VEnv.roguePropType) (by exact VEnv.addConst_rogueEnv1)
  rwa [sortAbbrevVal_toDefEq] at h

theorem wf_sortAbbrevEnv : VEnv.WF sortAbbrevEnv :=
  ⟨[.def sortAbbrevVal], .decl sortAbbrev_decl_wf .empty⟩

theorem sortAbbrevEnv_defeqs : sortAbbrevEnv.defeqs VEnv.rogueDfSort := .inl rfl

/-- **The limitation, stated as a theorem.**  `SortRigid` is false at a **`VEnv.WF`** environment —
the one whose only declaration is `def rogueC : Sort 1 := Prop`.  So §3's route is worth exactly
what a δ-rule-free target is worth; at `∅` there is no rule to abbreviate a universe with, which is
the same reason `IndepResidual` §3 survives its own §4. -/
theorem not_sortRigid_wf_sortAbbrevEnv : ¬ SortRigid sortAbbrevEnv 0 :=
  not_sortRigid_of_sortAbbrev (ls := []) (u := .zero) sortAbbrevEnv_defeqs (by simp) rfl
    nofun rfl

/-! ## §5 Fired at the field context -/

/-- The field context is a context at the staged environment — *discharged*, so §5's headline
carries no `OnCtx` hypothesis to be suspicious of. -/
theorem onCtx_raiΓ : OnCtx raiΓ (RecArgIndep.raiEnv0.IsType 0) :=
  ⟨trivial, _, RecArgIndep.raiI_hasType Rai.raiEnv0_I⟩

/-- **The headline, at a real field context.**  At `RecArgIndep.raiEnv0` — the staged environment of
a real block — over `raiΓ`, which `RecArgIndep.raiΓ_eq` certifies is the hole's own field context
and `raiΓ_not_noBlock` certifies is **not** block-free, no block-free type is convertible to the
block constant.  One hypothesis, at the **empty** environment.

This is the `.lam`-domain route of `RecArgIndepClose` §2's enumeration, closed at this block over a
field context — which is what `IndepResidual` §2b could not reach. -/
theorem rai_fieldCtx_noBlockType_not_defeqType_blockSpine {A : VExpr}
    (hsr : SortRigid ∅ 0) (hA : raiD.NoBlock A) :
    ¬ RecArgIndep.raiEnv0.IsDefEqType 0 raiΓ A (.const raiI []) :=
  noBlockType_not_defeqType_blockSpine_oneSubst (D := raiD) (as := []) (v := .zero)
    (A' := .sort .zero) (B' := .sort .zero)
    hsr hsr.rigidSortPiDisj Rai.raiσ_WF Rai.raiσ_dom₁ Rai.raiσ_raiI
    Rai.raiσ'_WF Rai.raiσ'_dom₁ Rai.raiσ'_raiI rfl rfl onCtx_raiΓ hA nofun

/-- …and the same statement over the *block-free* half of the context is what `IndepResidual` §2b
already gives, so the two are comparable: this file's contribution is exactly the entry
`raiΓ_not_noBlock` names. -/
theorem rai_fieldCtx_is_the_new_part :
    (∀ C ∈ ([] : List VExpr), raiD.NoBlock C) ∧ ¬ ∀ C ∈ raiΓ, raiD.NoBlock C :=
  ⟨nofun, raiΓ_not_noBlock⟩

/-! ## §6 Axiom check

    #print axioms Lean4Lean.BlockCtx.blockSpineType_defeq_transport_ctx
    #print axioms Lean4Lean.BlockCtx.noBlockType_not_defeqType_blockSpine_ctxEq
    #print axioms Lean4Lean.BlockCtx.ctxEq_of_noBlock
    #print axioms Lean4Lean.BlockCtx.raiΓ_not_noBlock
    #print axioms Lean4Lean.BlockCtx.substC_ctxEq_iff
    #print axioms Lean4Lean.BlockCtx.not_substC_ctxEq_of_shapes
    #print axioms Lean4Lean.BlockCtx.images_conv_refutes_sortPiDisjNil
    #print axioms Lean4Lean.BlockCtx.images_conv_refutes_target
    #print axioms Lean4Lean.BlockCtx.rai_side_condition_iff_open_instance
    #print axioms Lean4Lean.BlockCtx.rai_substC_ctxEq_false
    #print axioms Lean4Lean.BlockCtx.common_inhabitant_refutes
    #print axioms Lean4Lean.BlockCtx.SortRigid.rigidSortPiDisj
    #print axioms Lean4Lean.BlockCtx.noBlockType_not_defeqType_blockSpine_oneSubst
    #print axioms Lean4Lean.BlockCtx.not_sortRigid_of_sortAbbrev
    #print axioms Lean4Lean.BlockCtx.wf_sortAbbrevEnv
    #print axioms Lean4Lean.BlockCtx.not_sortRigid_wf_sortAbbrevEnv
    #print axioms Lean4Lean.BlockCtx.onCtx_raiΓ
    #print axioms Lean4Lean.BlockCtx.rai_fieldCtx_noBlockType_not_defeqType_blockSpine

`docs/handoff-blockctx.md` records the run. -/

end BlockCtx
end Lean4Lean
