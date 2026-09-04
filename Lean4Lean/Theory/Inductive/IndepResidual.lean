import Lean4Lean.Theory.Inductive.RecArgIndepClose
import Lean4Lean.Theory.Inductive.RestoreBridge
import Lean4Lean.Theory.Typing.ForallInvPrice

/-!
# `VIndRecArg.exists_indep`: the residual, with the block deleted

`VIndRecArg.exists_indep` (`Theory/Inductive/Decl.lean`, `sorry`) is the discharge obligation for
`VIndField.WF.binders_indep`.  `Theory/Inductive/RecArgIndepClose.lean` reduced it to two named
predicates — `VEnv.RigidConstPiDisj` and `VEnv.RigidConstSortDisj` at the *block's* constants,
guarded by `VEnv.RuleFreeHead`, which it discharges — and showed the tree's one refutation route (a
two-δ-rule hub aimed at a rule-free head) is unavailable at a staged environment, by freshness
alone (`defeq_noBlock_of_staged`).  It left the residual as "confluence over rules that never
mention the block", `[analysis, not proved]`.

This file does not close that.  It **relocates** it, and the relocation changes its status.

## What is here

**§1.**  `blockSubst_WF`: at a staged environment the block is *eliminable by a constant
substitution*.  `Theory/Typing/ConstSubst.lean`'s `CSubst.WF_of_hasType` has four obligations and
two of them are exactly `RecArgIndepClose`'s two theorems —
`env₀_const_noBlock_of_staged` gives `const`, `defeq_noBlock_of_staged` gives `defeq` — so
`defeq_noBlock_of_staged` turns out to be worth more than "the hub route is closed": it is half of a
licence to **delete the block from any judgement**.  `VEnv.IsDefEq.substC` is the only transport in
`Theory/` that can remove a constant, so this is the one tool available that does not need
confluence.

**§2, §2a.**  What deletion buys.  The block spine `I_c ls as` is convertible to `t ls as` for
*whatever* closed `t` the substitution assigns — so **a block spine behaves exactly like a
universally quantified variable of its arity**: anything convertible to it is convertible to every
closed inhabitant of that arity.  Pick a value whose spine is a **sort** and block-spine/Π
disjointness becomes sort/Π disjointness at the target environment; pick one whose spine is a **Π**
and block-spine/sort disjointness becomes the same predicate.  So the two residual predicates
collapse to **one**, `VEnv.RigidSortPiDisj`, and it is the member of the family with no constant in
it.  §2a is the form that applies where the hole lives: the field context is *not* block-free (a
recursive earlier field's stored type **is** a block spine), so the context travels along the
substitution and its `OnCtx` side condition is discharged, not assumed.

**§3.**  The reduction, fired at a real staged environment.  `RecArgIndep.raiEnv0` is
`VEnv.empty.addIndTypes raiD`; its one block constant is `raiI : Sort 1`; `Prop` and
`∀ (_ : Prop), Prop` both inhabit `Sort 1` in **every** environment, so both substitutions land in
the **empty** environment.  The conclusion: at that staged environment, "the block constant is
convertible to neither a Π nor a sort" *is* `VEnv.RigidSortPiDisj ∅` — an environment with no
constants and no δ-rules.

## Why the relocation is a status change and not bookkeeping

`Theory/Typing/InjSortPiModel.lean` grades the five conjuncts of `VEnv.WF.rigidShapeUniqNS` against
the set model.  `RigidConstPiDisj` and `RigidConstSortDisj` are **dead** there —
`ModelData.cnst` is a free field, so `InjSortPi.not_constNotUniv` and
`SetModel.not_coherentConstNotPi` / `SetModel.not_coherentConstNotUniv` say a constant may denote
anything and `interp` cannot separate a spine from a Π or from a universe.
`RigidSortPiDisj`'s semantic residual, by contrast, is a **theorem**
(`InjSortPi.interp_sort_ne_interp_forallE`; the separating element is `{•}`).  So this file moves
the hole's residual off both semantically-unreachable conjuncts and onto the one where the model
layer already has the fact.

`Theory/Typing/InjCorner.lean` then narrows the target further: `VEnv.rigidSortPiDisj_iff_nil` says
the family form of `RigidSortPiDisj` is exactly its empty-context restriction, and
`VEnv.nil_endpoints_typeable` names its one open instance as `.sort .zero` against
`.forallE (.sort .zero) (.sort .zero)` — `Prop ≢ (Prop → Prop)`.  Those are the two replacement
values §3 uses, reached independently as the sort-shaped and Π-shaped inhabitants of `Sort 1`.

## What is *not* here

* **The hole is not closed and no census number moves.**  `RigidSortPiDisj` is open, and at
  `Ordered` environments it is *false* — §4's `not_rigidSortPiDisj_rogueSortPiEnv`, from
  `VEnv.ordered_sortPiEnv` and `VEnv.not_sortPiDisjUC_sortPiEnv` — so the reduction is only worth
  what its target is worth.  What it does buy is that §3's target is `∅`, which has no δ-rules to
  build a hub out of.
* **The two-substitution route (§2b) still wants a block-free context.**  Comparing two
  substitutions is what closes the route where the block-free side is an *arbitrary* type `A`
  (the `.lam`-domain case of `RecArgIndepClose` §2's enumeration), and the two substitutions send
  the same context to *different* contexts, so the composition needs them to coincide.  The Π and
  sort routes do not have that defect (§2a).  This is the one gap the file leaves inside its own
  method, and it is stated rather than papered over.
* **No claim that `exists_indep` is false.**  See `docs/handoff-indepresidual.md` §(b): every
  refutation route dies on the same fact, that no rule of a staged environment can mention the
  block, and the substitution argument is a *necessary* condition on a conversion, so its failure
  at a degenerate `env₀` does not manufacture a derivation.
-/

namespace Lean4Lean
namespace IndepResidual

open VExpr (mkApp)

/-! ## §1 The block substitution -/

theorem blockSubst_WF {env₀ env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst} {U : Nat}
    (henv₀ : VEnv.Ordered env₀) (henv₁ : VEnv.Ordered env₁)
    (hstage : env₀.addIndTypes D = some env)
    (hle : env₀ ≤ env₁)
    (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames)
    (hdom₂ : ∀ c ∈ D.blockNames, σ c ≠ none)
    (hcl : σ.Closed)
    (hval : ∀ {c : Lean.Name} {t : VExpr} {ci : VConstant}, σ c = some t →
      env.constants c = some ci → env₁.HasType ci.uvars [] t (ci.type.substC σ)) :
    σ.WF env env₁ U := by
  refine CSubst.WF_of_hasType henv₁ hcl hval (fun {c ci} hn hc => ?_) (fun {df} hdf => ?_)
  · have hnb : c ∉ D.blockNames := fun hb => hdom₂ c hb hn
    have hc₀ : env₀.constants c = some ci := by
      rw [← VEnv.addConstList_constants_of_not_mem hstage
        (by rw [RecArgIndepClose.typeConsts_map_fst]; exact hnb)]
      exact hc
    have heq : ci.type.substC σ = ci.type :=
      (VExpr.NoConsts.noCSubst (σ := σ) (S := D.blockNames) hdom₁
        (RecArgIndepClose.env₀_const_noBlock_of_staged henv₀ hstage hc₀)).substC_eq
    rw [heq]
    exact hle.1 hc₀
  · obtain ⟨h1, h2, h3⟩ := RecArgIndepClose.defeq_noBlock_of_staged henv₀ hstage hdf
    have heq : df.substC σ = df :=
      VDefEq.NoCSubst.substC_eq ⟨VExpr.NoConsts.noCSubst hdom₁ h1,
        VExpr.NoConsts.noCSubst hdom₁ h2, VExpr.NoConsts.noCSubst hdom₁ h3⟩
    rw [heq]
    exact hle.2 (by rw [VEnv.addConstList_defeqs hstage] at hdf; exact hdf)

/-! ## §2 What deleting the block buys -/

/-- **`OnCtx` transports along a constant substitution.** -/
theorem onCtx_substC {env env₁ : VEnv} {σ : CSubst} {U : Nat} (hσ : σ.WF env env₁ U) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      OnCtx (Γ.map (VExpr.substC · σ)) (env₁.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨onCtx_substC hσ h1, VEnv.IsType.substC hσ h2⟩

/-- **Conservativity of the block extension, on the nose.**  A conversion between two
syntactically block-free terms, in a block-free context, at a staged environment, already holds in
any environment the block substitutes into — with the *same* context and the *same* terms. -/
theorem defeqU_noBlock_transport {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst} {U : Nat}
    {Γ : List VExpr} {e₁ e₂ : VExpr} (hσ : σ.WF env env₁ U)
    (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames)
    (hΓ : ∀ B ∈ Γ, D.NoBlock B) (h₁ : D.NoBlock e₁) (h₂ : D.NoBlock e₂)
    (H : env.IsDefEqU U Γ e₁ e₂) : env₁.IsDefEqU U Γ e₁ e₂ := by
  have := VEnv.IsDefEqU.substC hσ H
  rwa [(VExpr.NoConsts.noCSubst hdom₁ h₁).substC_eq,
    (VExpr.NoConsts.noCSubst hdom₁ h₂).substC_eq,
    VExpr.map_substC_eq_self (fun B hB => VExpr.NoConsts.noCSubst hdom₁ (hΓ B hB))] at this

/-- …and the context hypothesis transports too, so a consumer that has `OnCtx` at `env` has it at
`env₁` without extra work. -/
theorem onCtx_noBlock_transport {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst} {U : Nat}
    {Γ : List VExpr} (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames)
    (hΓ : ∀ B ∈ Γ, D.NoBlock B) (h : OnCtx Γ (env.IsType U)) : OnCtx Γ (env₁.IsType U) := by
  have := onCtx_substC hσ h
  rwa [VExpr.map_substC_eq_self (fun B hB => VExpr.NoConsts.noCSubst hdom₁ (hΓ B hB))] at this

/-- **The block spine behaves as a free variable of its arity.**  If a block-free term `e` is
convertible to the block spine `I_c ls as` (with `as` block-free) at a staged environment, then `e`
is convertible to `t ls as` in `env₁` — for the value `t` that `σ` happens to assign, *whatever*
that value is.  Since `σ`'s values are only constrained by their type, this says: anything
convertible to a block spine is convertible to **every** closed inhabitant of the block's arity,
applied to the same arguments. -/
theorem blockSpine_defeq_transport {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst} {U : Nat}
    {Γ : List VExpr} {e t : VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hΓ : ∀ B ∈ Γ, D.NoBlock B) (he : D.NoBlock e) (has : ∀ a ∈ as, D.NoBlock a)
    (H : env.IsDefEqU U Γ e (mkApp (.const c ls) as)) :
    env₁.IsDefEqU U Γ e (mkApp (t.instL ls) as) := by
  have := VEnv.IsDefEqU.substC hσ H
  rwa [(VExpr.NoConsts.noCSubst hdom₁ he).substC_eq,
    VExpr.substC_mkApp, VExpr.substC_const_some ht,
    VExpr.map_substC_eq_self (fun a ha => VExpr.NoConsts.noCSubst hdom₁ (has a ha)),
    VExpr.map_substC_eq_self (fun B hB => VExpr.NoConsts.noCSubst hdom₁ (hΓ B hB))] at this

/-- **The residual, with the block deleted.**  Contrapositive of `blockSpine_defeq_transport`:
to know that a block-free `e` is *not* convertible to a block spine, it is enough to exhibit **one**
closed inhabitant `t` of the block's arity whose spine `e` is not convertible to, in an environment
that need not know the block exists. -/
theorem not_defeq_blockSpine_of {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst} {U : Nat}
    {Γ : List VExpr} {e t : VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hΓ : ∀ B ∈ Γ, D.NoBlock B) (he : D.NoBlock e) (has : ∀ a ∈ as, D.NoBlock a)
    (hne : ¬ env₁.IsDefEqU U Γ e (mkApp (t.instL ls) as)) :
    ¬ env.IsDefEqU U Γ e (mkApp (.const c ls) as) := fun H =>
  hne (blockSpine_defeq_transport hσ hdom₁ ht hΓ he has H)

/-- **The reduction, in general: block-spine/Π disjointness ⟸ sort/Π disjointness at `env₁`.**
The only thing asked of the substituted value is that the spine it produces *is* a sort.  No
`trans` is used, and none is available: `VEnv.IsDefEqU` has no transitivity at this layer
(`RecArgIndep.isDefEqType_trans_of_sortUniq` is the priced composition, and its price,
`VEnv.SortUniq`, is one the hole already pays for its `F.type` conjunct — so a version of this
lemma with `hshape` weakened to a conversion costs the hole nothing new). -/
theorem blockSpine_not_defeq_forallE_of_sortVal {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {U : Nat} {Γ : List VExpr} {t A B : VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {v : VLevel}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hshape : mkApp (t.instL ls) as = .sort v)
    (hsp : env₁.RigidSortPiDisj U)
    (hΓ' : OnCtx Γ (env₁.IsType U)) (hΓ : ∀ C ∈ Γ, D.NoBlock C)
    (hA : D.NoBlock A) (hB : D.NoBlock B) (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqU U Γ (.forallE A B) (mkApp (.const c ls) as) := fun H => by
  have h' := blockSpine_defeq_transport (e := .forallE A B) hσ hdom₁ ht hΓ ⟨hA, hB⟩ has H
  rw [hshape] at h'
  exact hsp hΓ' h'.symm

/-- **…and block-spine/sort disjointness ⟸ the same predicate**, via a value whose spine is a Π.
So the *two* rigidity facts `RecArgIndepClose` §2 left open collapse to **one**, and it is the
smallest member of the family — the one with no constant in it. -/
theorem blockSpine_not_defeq_sort_of_piVal {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {U : Nat} {Γ : List VExpr} {t A' B' : VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {v : VLevel}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hshape : mkApp (t.instL ls) as = .forallE A' B')
    (hsp : env₁.RigidSortPiDisj U)
    (hΓ' : OnCtx Γ (env₁.IsType U)) (hΓ : ∀ C ∈ Γ, D.NoBlock C)
    (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqU U Γ (.sort v) (mkApp (.const c ls) as) := fun H => by
  have h' := blockSpine_defeq_transport (e := .sort v) hσ hdom₁ ht hΓ trivial has H
  rw [hshape] at h'
  exact hsp hΓ' h'

/-! ### §2a The same three, with **no requirement on the context**

The block-free-context hypothesis above is *not* satisfied where the hole lives: the field context
`(pre.map (·.type)).reverse ++ D.params.reverse` contains the earlier fields' stored types, and a
recursive field's stored type **is** a block spine.  So the lemmas that matter carry the context
along the substitution instead of asking it to be fixed — `Γ ↦ Γ.map (·.substC σ)` — and their
`OnCtx` side condition is then discharged by `onCtx_substC` rather than assumed at `env₁`. -/

/-- `blockSpine_defeq_transport` with the context substituted rather than required block-free. -/
theorem blockSpine_defeq_transport_ctx {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {U : Nat} {Γ : List VExpr} {e t : VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (he : D.NoBlock e) (has : ∀ a ∈ as, D.NoBlock a)
    (H : env.IsDefEqU U Γ e (mkApp (.const c ls) as)) :
    env₁.IsDefEqU U (Γ.map (VExpr.substC · σ)) e (mkApp (t.instL ls) as) := by
  have := VEnv.IsDefEqU.substC hσ H
  rwa [(VExpr.NoConsts.noCSubst hdom₁ he).substC_eq,
    VExpr.substC_mkApp, VExpr.substC_const_some ht,
    VExpr.map_substC_eq_self (fun a ha => VExpr.NoConsts.noCSubst hdom₁ (has a ha))] at this

/-- **The reduction that applies where the hole lives: block-spine/Π disjointness ⟸ sort/Π
disjointness at `env₁`, over an arbitrary context.**  The `OnCtx` hypothesis is at `env`, the
environment the caller has it at. -/
theorem blockSpine_not_defeq_forallE_of_sortVal_ctx {env env₁ : VEnv} {D : VInductDecl'}
    {σ : CSubst} {U : Nat} {Γ : List VExpr} {t A B : VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {v : VLevel}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hshape : mkApp (t.instL ls) as = .sort v)
    (hsp : env₁.RigidSortPiDisj U) (hΓ : OnCtx Γ (env.IsType U))
    (hA : D.NoBlock A) (hB : D.NoBlock B) (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqU U Γ (.forallE A B) (mkApp (.const c ls) as) := fun H => by
  have h' := blockSpine_defeq_transport_ctx (e := .forallE A B) hσ hdom₁ ht ⟨hA, hB⟩ has H
  rw [hshape] at h'
  exact hsp (onCtx_substC hσ hΓ) h'.symm

@[inherit_doc blockSpine_not_defeq_forallE_of_sortVal_ctx]
theorem blockSpine_not_defeq_sort_of_piVal_ctx {env env₁ : VEnv} {D : VInductDecl'}
    {σ : CSubst} {U : Nat} {Γ : List VExpr} {t A' B' : VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {v : VLevel}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hshape : mkApp (t.instL ls) as = .forallE A' B')
    (hsp : env₁.RigidSortPiDisj U) (hΓ : OnCtx Γ (env.IsType U))
    (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqU U Γ (.sort v) (mkApp (.const c ls) as) := fun H => by
  have h' := blockSpine_defeq_transport_ctx (e := .sort v) hσ hdom₁ ht trivial has H
  rw [hshape] at h'
  exact hsp (onCtx_substC hσ hΓ) h'

/-! ### §2b The sharpest form: *two* replacement values, and the block-free side is arbitrary

`blockSpine_not_defeq_forallE_of_sortVal` still needs to know the block-free side is a Π (or a
sort).  The `.lam`-domain route of `RecArgIndepClose` §2's enumeration does not: there the
block-free side is an **arbitrary** type `A`, and what has to be excluded is `A ≡ I_j p π` outright.
Two substitutions settle that, because the block spine is convertible to *whatever* value is
substituted for it: substitute a sort once and a Π once, and the two images must be convertible to
each other. -/

/-- `IsDefEqType` transports along a constant substitution: the recorded sort is a sort. -/
theorem isDefEqType_substC {env env₁ : VEnv} {σ : CSubst} {U : Nat} {Γ : List VExpr}
    {A B : VExpr} (hσ : σ.WF env env₁ U) (H : env.IsDefEqType U Γ A B) :
    env₁.IsDefEqType U (Γ.map (VExpr.substC · σ)) (A.substC σ) (B.substC σ) :=
  let ⟨u, h⟩ := H; ⟨u, h.substC hσ⟩

@[inherit_doc isDefEqType_substC]
theorem blockSpineType_defeq_transport {env env₁ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {U : Nat} {Γ : List VExpr} {A t : VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr}
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hΓ : ∀ C ∈ Γ, D.NoBlock C) (hA : D.NoBlock A) (has : ∀ a ∈ as, D.NoBlock a)
    (H : env.IsDefEqType U Γ A (mkApp (.const c ls) as)) :
    env₁.IsDefEqType U Γ A (mkApp (t.instL ls) as) := by
  have := isDefEqType_substC hσ H
  rwa [(VExpr.NoConsts.noCSubst hdom₁ hA).substC_eq,
    VExpr.substC_mkApp, VExpr.substC_const_some ht,
    VExpr.map_substC_eq_self (fun a ha => VExpr.NoConsts.noCSubst hdom₁ (has a ha)),
    VExpr.map_substC_eq_self (fun B hB => VExpr.NoConsts.noCSubst hdom₁ (hΓ B hB))] at this

/-- **No block-free type is convertible to a block spine.**  The whole hypothesis budget is:
two substitutions of the block into one environment `env₁`, one of them landing on a sort and one
on a Π, plus `VEnv.SortUniq env₁` and `VEnv.RigidSortPiDisj env₁`.  Nothing about inductive
declarations, nothing about the staged environment, and no constant in either predicate.

`SortUniq` is the price of composing two `IsDefEqType`s
(`RecArgIndep.isDefEqType_trans_of_sortUniq`), and it is the price
`VIndRecArg.exists_indep` already pays for its `F.type` conjunct — so this route charges the hole
nothing it was not already paying.

**The one gap in the method.**  Unlike §2a this needs `Γ` block-free, because `σ` and `σ'` send the
same context to *different* contexts and `isDefEqType_trans_of_sortUniq` needs one context.  Where
the hole lives `Γ` is not block-free, so this lemma covers the `.lam`-domain route only when every
earlier field is non-recursive — which is the regime `RecArgIndep.bindersIndep_of_pre_norec`
already closes.  Closing it in general needs either a context-conversion between the two images
(which is the very disjointness being proved) or a transport that keeps one context. -/
theorem noBlockType_not_defeqType_blockSpine {env env₁ : VEnv} {D : VInductDecl'}
    {σ σ' : CSubst} {U : Nat} {Γ : List VExpr} {A t t' A' B' : VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {v : VLevel}
    (henv₁ : env₁.Ordered) (hsu : env₁.SortUniq U) (hsp : env₁.RigidSortPiDisj U)
    (hσ : σ.WF env env₁ U) (hdom₁ : ∀ c, σ c ≠ none → c ∈ D.blockNames) (ht : σ c = some t)
    (hσ' : σ'.WF env env₁ U) (hdom₁' : ∀ c, σ' c ≠ none → c ∈ D.blockNames)
    (ht' : σ' c = some t')
    (hsort : mkApp (t.instL ls) as = .sort v)
    (hpi : mkApp (t'.instL ls) as = .forallE A' B')
    (hΓ' : OnCtx Γ (env₁.IsType U)) (hΓ : ∀ C ∈ Γ, D.NoBlock C)
    (hA : D.NoBlock A) (has : ∀ a ∈ as, D.NoBlock a) :
    ¬ env.IsDefEqType U Γ A (mkApp (.const c ls) as) := fun H => by
  have h1 := blockSpineType_defeq_transport hσ hdom₁ ht hΓ hA has H
  have h2 := blockSpineType_defeq_transport hσ' hdom₁' ht' hΓ hA has H
  rw [hsort] at h1
  rw [hpi] at h2
  exact hsp hΓ' (RecArgIndep.isDefEqType_trans_of_sortUniq henv₁ hsu hΓ' h1.symm h2).toU

/-! ## §3 A concrete staged environment: the residual is sort/Π disjointness at `∅` -/

namespace Rai
open RecArgIndep

/-- **The substitution that deletes `raiD`'s block.**  Its one type constant is
`raiI : Sort 1`, and `Prop` inhabits `Sort 1` in *every* environment — so the target of the
substitution can be the **empty** environment. -/
def raiσ : CSubst := CSubst.one raiI (.sort .zero)

theorem raiσ_eq (c : Lean.Name) :
    raiσ c = if c = raiI then some (.sort .zero) else none := rfl

theorem raiσ_raiI : raiσ raiI = some (.sort .zero) := by rw [raiσ_eq]; simp

theorem raiD_blockNames : raiD.blockNames = [raiI] := rfl

theorem raiσ_dom₁ : ∀ c, raiσ c ≠ none → c ∈ raiD.blockNames := by
  intro c h
  rw [raiσ_eq] at h
  split at h
  · subst_vars; rw [raiD_blockNames]; exact List.mem_cons_self
  · exact absurd rfl h

theorem raiσ_dom₂ : ∀ c ∈ raiD.blockNames, raiσ c ≠ none := by
  rw [raiD_blockNames]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc; rw [raiσ_raiI]; exact nofun

theorem raiσ_closed : raiσ.Closed := by
  intro c t h
  rw [raiσ_eq] at h
  split at h
  · cases h; exact trivial
  · exact absurd h nofun

theorem raiEnv0_I : raiEnv0.constants raiI = some raiCiI := by simp [raiEnv0]

/-- The one `val` obligation, discharged in the empty environment. -/
theorem raiσ_val : ∀ {c : Lean.Name} {t : VExpr} {ci : VConstant}, raiσ c = some t →
    raiEnv0.constants c = some ci →
    (∅ : VEnv).HasType ci.uvars [] t (ci.type.substC raiσ) := by
  intro c t ci h hc
  rw [raiσ_eq] at h
  split at h
  case isFalse => exact absurd h nofun
  case isTrue he =>
  subst he; cases h
  rw [raiEnv0_I] at hc; cases hc
  exact VEnv.HasType.sort (l := .zero) trivial

/-- **The block substitution is well formed, from `∅ + raiI` to `∅`.**  Anti-vacuity for §1:
the machinery fires at a real staged environment. -/
theorem raiσ_WF {U : Nat} : raiσ.WF raiEnv0 ∅ U :=
  blockSubst_WF (D := raiD) .empty .empty rai_staged VEnv.LE.rfl
    raiσ_dom₁ raiσ_dom₂ raiσ_closed raiσ_val

/-- **The headline.**  At `raiEnv0` — the staged environment of a real, if small, block over the
empty environment — "a Π is not convertible to the block constant" *is* "a Π is not convertible to
`Prop`", in the **empty** environment: an environment with no constants and no δ-rules at all.
So the residual of `VIndRecArg.exists_indep` is not a fact about inductive declarations; at this
block it is `VEnv.RigidSortPiDisj ∅`. -/
theorem rai_blockSpine_not_defeq_forallE {Γ : List VExpr} {A B : VExpr}
    (hsp : (∅ : VEnv).RigidSortPiDisj 0) (hOn : OnCtx Γ (raiEnv0.IsType 0))
    (hA : raiD.NoBlock A) (hB : raiD.NoBlock B) :
    ¬ raiEnv0.IsDefEqU 0 Γ (.forallE A B) (.const raiI []) :=
  blockSpine_not_defeq_forallE_of_sortVal_ctx (D := raiD) (t := .sort .zero) (as := [])
    (v := .zero) raiσ_WF raiσ_dom₁ raiσ_raiI rfl hsp hOn hA hB nofun

/-- The second replacement: a **Π** inhabiting `Sort 1`, for the sort side of the reduction. -/
def raiσ' : CSubst := CSubst.one raiI (.forallE (.sort .zero) (.sort .zero))

theorem raiσ'_eq (c : Lean.Name) :
    raiσ' c = if c = raiI then some (.forallE (.sort .zero) (.sort .zero)) else none := rfl

theorem raiσ'_raiI : raiσ' raiI = some (.forallE (.sort .zero) (.sort .zero)) := by
  rw [raiσ'_eq]; simp

theorem raiσ'_dom₁ : ∀ c, raiσ' c ≠ none → c ∈ raiD.blockNames := by
  intro c h
  rw [raiσ'_eq] at h
  split at h
  · subst_vars; rw [raiD_blockNames]; exact List.mem_cons_self
  · exact absurd rfl h

theorem raiσ'_dom₂ : ∀ c ∈ raiD.blockNames, raiσ' c ≠ none := by
  rw [raiD_blockNames]
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc; rw [raiσ'_raiI]; exact nofun

theorem raiσ'_closed : raiσ'.Closed := by
  intro c t h
  rw [raiσ'_eq] at h
  split at h
  · cases h; exact ⟨trivial, trivial⟩
  · exact absurd h nofun

/-- `∀ (_ : Prop), Prop` really does inhabit `Sort 1` — the level side is `imax 1 1 ≈ 1`. -/
theorem raiPi_hasType :
    (∅ : VEnv).HasType 0 [] (.forallE (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) := by
  refine VEnv.IsDefEq.defeq (u := .succ (.imax (.succ .zero) (.succ .zero)))
    (VEnv.IsDefEq.sortDF ⟨trivial, trivial⟩ trivial ?_)
    (VEnv.HasType.forallE (VEnv.HasType.sort trivial) (VEnv.HasType.sort trivial))
  funext ls
  simp [VLevel.eval, Lean.Nat.imax]

theorem raiσ'_val : ∀ {c : Lean.Name} {t : VExpr} {ci : VConstant}, raiσ' c = some t →
    raiEnv0.constants c = some ci →
    (∅ : VEnv).HasType ci.uvars [] t (ci.type.substC raiσ') := by
  intro c t ci h hc
  rw [raiσ'_eq] at h
  split at h
  case isFalse => exact absurd h nofun
  case isTrue he =>
  subst he; cases h
  rw [raiEnv0_I] at hc; cases hc
  exact raiPi_hasType

theorem raiσ'_WF {U : Nat} : raiσ'.WF raiEnv0 ∅ U :=
  blockSubst_WF (D := raiD) .empty .empty rai_staged VEnv.LE.rfl
    raiσ'_dom₁ raiσ'_dom₂ raiσ'_closed raiσ'_val

/-- **The other half of the headline.**  "The block constant is not convertible to a sort" is,
at this staged environment, again sort/Π disjointness in the empty environment — reached through a
*different* replacement value.  Both halves of `RecArgIndepClose` §2's residual therefore land on
`VEnv.RigidSortPiDisj ∅`, and nothing about inductive declarations survives in the target. -/
theorem rai_blockSpine_not_defeq_sort {Γ : List VExpr} {v : VLevel}
    (hsp : (∅ : VEnv).RigidSortPiDisj 0) (hOn : OnCtx Γ (raiEnv0.IsType 0)) :
    ¬ raiEnv0.IsDefEqU 0 Γ (.sort v) (.const raiI []) :=
  blockSpine_not_defeq_sort_of_piVal_ctx (D := raiD) (as := []) (A' := .sort .zero)
    (B' := .sort .zero) raiσ'_WF raiσ'_dom₁ raiσ'_raiI rfl hsp hOn nofun

/-- **The sharpest concrete statement.**  At `raiEnv0`, *no* block-free type is convertible to the
block constant — over exactly two hypotheses about the **empty** environment,
`VEnv.SortUniq ∅` and `VEnv.RigidSortPiDisj ∅`.

This is the `.lam`-domain route of `RecArgIndepClose` §2's enumeration, closed at this block modulo
those two.  And `InjCorner.rigidSortPiDisj_iff_nil` says the family form of the second is exactly
its empty-context restriction, whose one open instance
(`InjCorner.nil_endpoints_typeable`) is `¬ IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero)
(.sort .zero))` — literally `Prop ≢ (Prop → Prop)`.  The two replacement values used here are those
same two terms, arrived at independently. -/
theorem rai_noBlockType_not_defeqType_blockSpine {Γ : List VExpr} {A : VExpr}
    (hsu : (∅ : VEnv).SortUniq 0) (hsp : (∅ : VEnv).RigidSortPiDisj 0)
    (hΓ : ∀ C ∈ Γ, raiD.NoBlock C) (hOn : OnCtx Γ (raiEnv0.IsType 0))
    (hA : raiD.NoBlock A) :
    ¬ raiEnv0.IsDefEqType 0 Γ A (.const raiI []) := by
  have hOn' : OnCtx Γ ((∅ : VEnv).IsType 0) :=
    onCtx_noBlock_transport (D := raiD) raiσ_WF raiσ_dom₁ hΓ hOn
  exact noBlockType_not_defeqType_blockSpine (D := raiD) (as := []) (v := .zero)
    (A' := .sort .zero) (B' := .sort .zero)
    .empty hsu hsp raiσ_WF raiσ_dom₁ raiσ_raiI raiσ'_WF raiσ'_dom₁ raiσ'_raiI rfl rfl
    hOn' hΓ hA nofun

/-! ### §3b The one binder in the tree that must move needs a constant the staging cannot hold

`RecArgIndep.raiB = raiP (bvar 0)` is the tree's **only** binder that mentions an earlier recursive
field (`RecArgIndep.not_bindersIndep_raiRec1`), and it is well typed only at `raiEnv`, which
declares `raiP : raiI → Sort 1` — a constant whose *type* mentions the block
(`RecArgIndep.raiCiP_type_hasBlock`).  `RecArgIndep.rai_not_staged` shows no `Ordered` environment
stages `raiD` into `raiEnv`; the fact below is the blunter half of the same point, and it is what
makes the residual case *unreachable in this tree* rather than merely unproved: at the staged
environment the head of the offending binder does not exist. -/

theorem raiEnv0_P_none : raiEnv0.constants raiP = none := by
  simp [raiEnv0, raiI, raiP]

/-- …and `raiB`'s head is exactly that constant, so the binder is not even a term of the staged
environment's vocabulary. -/
theorem raiB_head : raiB = .app (.const raiP []) (.bvar 0) := rfl

end Rai

/-! ## §4 The honest caveat: the target inherits "false at `Ordered`"

The reduction is only worth what its target is worth, and its target is *false* at general `Ordered`
environments — for exactly the reason `RecArgIndepClose` §2c gives for the two predicates it
replaces.  `Theory/Typing/ForallInvPrice.lean` already has the witness: `VEnv.rogueSortPiEnv` is
`Ordered` (`VEnv.ordered_sortPiEnv`) with two δ-rules sharing an lhs — `rogueC ≡ ∀ (_ : Prop), Prop`
and `rogueC ≡ Prop` — and `VEnv.sortPi_link` links `Prop` to that Π through the hub.

What the reduction buys is therefore **not** an escape from the `Ordered`-vs-`VEnv.WF` gap in
general.  It is that §3's target environment is `∅`: an environment with no δ-rules at all, so there
is nothing to build a hub out of, and the whole known refutation family is unavailable *by
construction* rather than by an argument about freshness. -/

/-- **The reduction target is false at an `Ordered` environment** — one line, from
`VEnv.sortPiDisjUC_of_rigidSortPiDisj` and `VEnv.not_sortPiDisjUC_sortPiEnv`.  Stated here so that
no successor reads §2's collapse as having removed the `Ordered` problem. -/
theorem not_rigidSortPiDisj_rogueSortPiEnv : ¬ VEnv.rogueSortPiEnv.RigidSortPiDisj 0 := fun h =>
  VEnv.not_sortPiDisjUC_sortPiEnv (VEnv.sortPiDisjUC_of_rigidSortPiDisj h)

/-! ## §5 Axiom check

    #print axioms Lean4Lean.IndepResidual.blockSubst_WF
    #print axioms Lean4Lean.IndepResidual.onCtx_substC
    #print axioms Lean4Lean.IndepResidual.defeqU_noBlock_transport
    #print axioms Lean4Lean.IndepResidual.onCtx_noBlock_transport
    #print axioms Lean4Lean.IndepResidual.blockSpine_defeq_transport
    #print axioms Lean4Lean.IndepResidual.not_defeq_blockSpine_of
    #print axioms Lean4Lean.IndepResidual.blockSpine_not_defeq_forallE_of_sortVal
    #print axioms Lean4Lean.IndepResidual.blockSpine_not_defeq_sort_of_piVal
    #print axioms Lean4Lean.IndepResidual.isDefEqType_substC
    #print axioms Lean4Lean.IndepResidual.blockSpineType_defeq_transport
    #print axioms Lean4Lean.IndepResidual.noBlockType_not_defeqType_blockSpine
    #print axioms Lean4Lean.IndepResidual.Rai.raiσ_WF
    #print axioms Lean4Lean.IndepResidual.Rai.raiσ'_WF
    #print axioms Lean4Lean.IndepResidual.Rai.raiPi_hasType
    #print axioms Lean4Lean.IndepResidual.Rai.rai_blockSpine_not_defeq_forallE
    #print axioms Lean4Lean.IndepResidual.Rai.rai_blockSpine_not_defeq_sort
    #print axioms Lean4Lean.IndepResidual.Rai.rai_noBlockType_not_defeqType_blockSpine
    #print axioms Lean4Lean.IndepResidual.not_rigidSortPiDisj_rogueSortPiEnv

`docs/handoff-indepresidual.md` records the run.  Every line is `[propext, Quot.sound]` or less:
no `sorryAx`, no `Classical.choice`. -/

end IndepResidual
end Lean4Lean
