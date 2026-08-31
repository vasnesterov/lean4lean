import Lean4Lean.Theory.Typing.PiLevelPin

/-!
# What `WF.rigidShapeUniqNS` is, exactly — and why it is *not* `VEnv.SortUniq`

`Injectivity.lean`'s `VEnv.WF.rigidShapeUniq` was the second-largest hole in the tree (176
transitive users).  The question this file answers is the classification question: **does it
reduce to `VEnv.SortUniq`?**

**Answer: no.**  It reduces to a conjunction of four properties, one of which is `VEnv.PiInv`
— unstratified Π-injectivity — and universe uniqueness provably does not deliver `PiInv` by
any of the routes this tree has.  Concretely, this file proves:

1. `rigidShapeUniqNS_iff_family`: the narrowed bridge **is** the conjunction

       PiInv ∧ RigidSortPiDisj ∧ RigidConstAppInv ∧ RigidConstPiDisj ∧ RigidConstSortDisj

   with both directions `sorry`-free.  This is the sharp classification: an exact
   decomposition, not a bracketing.

2. The `sort`/`sort` entry has already been removed from the bridge upstream
   (`Injectivity.rigidShapeUniq_of_sortUniq`), and it is the **only** entry `SortUniq` pays
   for — so the list above is what is left, and `SortUniq` appears nowhere in it.

3. `Injectivity.rigidPiUniq_iff_piInv` identifies the `pi`/`pi` entry with `PiInv` on the
   nose (both directions, `sorry`-free).

4. `imax_dom_not_pinned`: the *domain* half of `PiInv` is not reachable from level data, the
   domain analogue of `PiLevelPin.imax_cod_not_pinned`.  This is the machine-checked form of
   the argument `PiLevelPin`'s docstring makes in prose ("take `B = B' = .sort .zero`, where
   the conclusion says nothing about `A`, `A'`").

## Correction to the framing this file was written to check

The hoped-for reading was: `piInvStratApp_iff_sortUniq` shows the 449-user hole
`IsDefEqU.forallE_inv_stratified` **is** `SortUniq`, so if `rigidShapeUniq` also reduced to
`SortUniq` the whole injectivity corner would collapse to one node.  That reading is
backwards about which way the "modulo" runs.

`piInvStratApp_iff_sortUniq` is `(sortUniq_iff_piInvStratApp henv (piInv_axiom henv)).symm`.
Its side hypothesis is `piInv_axiom`, i.e. `PiInv`, and that is *precisely* why it is modulo
`rigidShapeUniq`.  So the equivalence it establishes is

    forallE_inv_stratified  ≈  SortUniq   **given PiInv**

not `forallE_inv_stratified ≈ SortUniq` outright.  And the reverse road is blocked:
`PiLevelPin.piInvCod_of_piInvStratApp` shows `PiInvStratApp` recovers only `PiInvCod`, the
codomain half, and its docstring records that the domain half is not recoverable at all.  So
`SortUniq → PiInv` is not available here, and the corner has **two** nodes:

* `VEnv.SortUniq` — universe uniqueness, the target of the set-model attack;
* `VEnv.PiInv` — Π-injectivity, which is confluence content.

A model-side proof of `SortUniq` alone therefore does **not** finish the theory layer's
injectivity corner.  It closes `forallE_inv_stratified` only if `PiInv` arrives from
somewhere, and `PiInv` is `rigidShapeUniqNS`'s `pi`/`pi` entry, i.e. it *is* the second hole.
The two holes are not one hole seen twice.

## Where the remaining three conjuncts live

They are not independent obligations.  `Verify/Typing/ConstSpine.lean` proves
`const_app_inv`/`const_forallE_inv`/`const_sort_inv` and the constant no-confusion fact from
`IsDefEq.church_rosser` plus `VEnv.PatWF`, and `Theory/Typing/PatWFIota.lean`'s `patWF` gives
`PiInv → PatWF` `sorry`-free.  So `RigidConstAppInv`, `RigidConstPiDisj` and
`RigidConstSortDisj` are downstream of `PiInv` together with confluence.

**Do not, however, discharge them that way**: `ConstSpine`'s results route through
`IsDefEq.church_rosser`, whose cone runs through `IsDefEqU.forallE_inv`, whose cone is
`rigidShapeUniqNS`.  Closing the bridge from `const_*_of_patWF` is circular and vacuous.  The
non-circular route is to take `KCanonical.CRStatement` as an explicit hypothesis, which is
also why `crStatement_holds` must not be used for it.  This has been checked, not guessed:
`NormalEq.constApp_inv`'s `appDF` case calls `h.forallE_inv henv` directly.

`RigidSortPiDisj` is `IsDefEqU.sort_forallE_inv`, and `Theory/Typing/UnivDiscrim.lean` already
machine-checks that it is not a universe fact: `.sort u` and `.forallE (.sort u) (.sort u)` are
both types at `.succ u`, so no level discriminant separates them.

## Net effect on the census

The census is unchanged in count: `Injectivity.lean` still has two holes, but the second is
now `WF.rigidShapeUniqNS`, which is `WF.rigidShapeUniq` minus its `sort`/`sort` entry — eight
of nine entries instead of nine.  Nothing in this file adds a `sorry`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The domain half of `PiInv` is not level data -/

/-- **The dual of `PiLevelPin.imax_cod_not_pinned`: the shared type of two Π types does not
pin their *domain* levels either.**

Witness: `u = 1`, `u' = 2`, `v = v' = 0`.  Then `imax u v = 0 = imax u' v'` (a Π into `Prop`
is a `Prop` whatever its domain lives in) and `1 ≉ 2`.

This is why the *domain* conjunct of `VEnv.PiInv` cannot be recovered from `SortUniq`, and
hence why `PiLevelPin.piInvCod_of_piInvStratApp` stops at the codomain: at a `Prop`-valued
codomain, the type of a Π carries no information about its domain at all.  Together with
`imax_cod_not_pinned` it says the level side of Π-injectivity is exhausted in *both*
coordinates — the content has to come from normalisation, in both. -/
theorem imax_dom_not_pinned :
    ∃ u u' v v' : VLevel, v ≈ v' ∧ VLevel.imax u v ≈ VLevel.imax u' v' ∧ ¬ u ≈ u' := by
  refine ⟨.succ .zero, .succ (.succ .zero), .zero, .zero, rfl, ?_, ?_⟩
  · simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
  · intro h; exact absurd (congrFun h []) (by simp [VLevel.eval])

/-! ## §2 The four conjuncts, named -/

/-- Sort/Π disjointness at the conversion level: `IsDefEqU.sort_forallE_inv`, packaged.  This
is *not* the typing-level `SortForallEDisjoint` family (`Theory/Typing/UnivDiscrim.lean`),
which is a different statement. -/
def RigidSortPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, OnCtx Γ (env.IsType U) →
    ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B)

/-- Injectivity of a rule-free constant spine: `IsDefEqU.const_app_inv`, with `IsType`
weakened to `¬ IsProof` — the form the induction proves, and the form the bridge asks for. -/
def RigidConstAppInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as') →
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

/-- Spine/Π disjointness: `IsDefEqU.const_forallE_inv`, packaged. -/
def RigidConstPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B)

/-- Spine/sort disjointness: `IsDefEqU.const_sort_inv`, packaged. -/
def RigidConstSortDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u)

/-! ## §3 The narrowed bridge is exactly their conjunction -/

/-- **⟸.**  `rigidShapeUniq_of_family` minus its `hsort` hypothesis: with the `sort`/`sort`
entry excluded by `¬ BothSort`, universe uniqueness is not needed anywhere.  `sorry`-free. -/
theorem rigidShapeUniqNS_of_family (henv : VEnv.WF env)
    (hpi : env.PiInv U) (hsp : env.RigidSortPiDisj U) (hca : env.RigidConstAppInv U)
    (hcp : env.RigidConstPiDisj U) (hcs : env.RigidConstSortDisj U) :
    env.RigidShapeUniqNS U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ hns h₁ h₂
  have hs : env.IsDefEqU U Γ s₁.toExpr s₂.toExpr := ⟨T, h₁.symm.trans h₂⟩
  cases s₁ with
  | sort u =>
    cases s₂ with
    | sort v => exact absurd trivial hns
    | pi A B => exact hsp hΓ hs
    | app c ls as => exact hcs hΓ hr₂ hs.symm
  | pi A B =>
    cases s₂ with
    | sort v => exact hsp hΓ hs.symm
    | pi A' B' =>
      obtain ⟨⟨u, ha⟩, v, hb⟩ := hpi hΓ hs
      exact ⟨⟨u, ha⟩, v, hb, ha.defeqDF_l henv.ordered hb⟩
    | app c ls as => exact hcp hΓ hr₂ hs.symm
  | app c ls as =>
    cases s₂ with
    | sort v => exact hcs hΓ hr₁ hs
    | pi A B => exact hcp hΓ hr₁ hs
    | app c' ls' as' =>
      rintro rfl
      exact hca hΓ hr₁ (fun hp => hnp (hp.defeqU henv hΓ ⟨T, h₁.symm⟩)) hs

/-- **⟹, first conjunct.**  Chases `Injectivity.rigidPiUniq_iff_piInv`. -/
theorem RigidShapeUniqNS.piInv (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeUniqNS U) : env.PiInv U :=
  piInv_of_rigidPiUniq henv hsu (RigidShapeUniqNS.piUniq henv hsu h)

/-- Every off-diagonal entry is reached by taking the middle term to be the left shape
itself: `h.trans h.symm` types it at the shared type, and the `¬ IsProof` side condition is
free because a term convertible to a sort or a Π is not a proof. -/
theorem RigidShapeUniqNS.sortPiDisj (henv : VEnv.WF env) (h : env.RigidShapeUniqNS U) :
    env.RigidSortPiDisj U := by
  intro Γ u A B hΓ ⟨T, hd⟩
  exact h (s₁ := .sort u) (s₂ := .pi A B) hΓ
    (not_isProof_of_defeqU_sort henv hΓ ⟨_, hd.trans hd.symm⟩) trivial trivial not_false
    (hd.trans hd.symm) hd

@[inherit_doc RigidShapeUniqNS.sortPiDisj]
theorem RigidShapeUniqNS.constPiDisj (henv : VEnv.WF env) (h : env.RigidShapeUniqNS U) :
    env.RigidConstPiDisj U := by
  intro Γ c ls as A B hΓ hc ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .pi A B) hΓ
    (not_isProof_of_defeqU_forallE henv hΓ ⟨_, hd⟩) hc trivial not_false
    (hd.trans hd.symm) hd

@[inherit_doc RigidShapeUniqNS.sortPiDisj]
theorem RigidShapeUniqNS.constSortDisj (henv : VEnv.WF env) (h : env.RigidShapeUniqNS U) :
    env.RigidConstSortDisj U := by
  intro Γ c ls as u hΓ hc ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .sort u) hΓ
    (not_isProof_of_defeqU_sort henv hΓ ⟨_, hd⟩) hc trivial not_false
    (hd.trans hd.symm) hd

@[inherit_doc RigidShapeUniqNS.sortPiDisj]
theorem RigidShapeUniqNS.constAppInv (_henv : VEnv.WF env) (h : env.RigidShapeUniqNS U) :
    env.RigidConstAppInv U := by
  intro Γ c ls ls' as as' hΓ hc hnp ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .app c ls' as') hΓ hnp hc hc not_false
    (hd.trans hd.symm) hd rfl

/-- **The classification, both ways.**  `sorry`-free.

The narrowed 176-user bridge is *exactly* the conjunction of unstratified Π-injectivity and
the three constant-spine facts.  `VEnv.SortUniq` does not occur in it; it occurs only in the
`sort`/`sort` entry that `Injectivity.rigidShapeUniq_of_sortUniq` already removed, and as a
side hypothesis of the `⟹` direction here (needed only to know a Π is not a proof).

So the answer to "does `rigidShapeUniq` reduce to `SortUniq`?" is **no**, and the second node
of the injectivity corner is `VEnv.PiInv`. -/
theorem rigidShapeUniqNS_iff_family (henv : VEnv.WF env) (hsu : env.SortUniq U) :
    env.RigidShapeUniqNS U ↔
      (env.PiInv U ∧ env.RigidSortPiDisj U ∧ env.RigidConstAppInv U ∧
        env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) :=
  ⟨fun h => ⟨h.piInv henv hsu, h.sortPiDisj henv, h.constAppInv henv,
      h.constPiDisj henv, h.constSortDisj henv⟩,
   fun ⟨hpi, hsp, hca, hcp, hcs⟩ => rigidShapeUniqNS_of_family henv hpi hsp hca hcp hcs⟩

/-!
## §4 Axiom check

    #print axioms Lean4Lean.VEnv.imax_dom_not_pinned
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_family
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_iff_family

all report `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**, despite the import of
`Injectivity.lean`.  Nothing here consumes either of that file's holes; the `SortUniq`
hypothesis is taken, not supplied (`Injectivity.WF.sortUniq'` *would* supply it, but it is
`sorryAx`-tainted through `forallE_inv_stratified`, which is why this file's statements carry
`hsu` explicitly instead).

## §5 What this does *not* settle

`RigidConstAppInv`, `RigidConstPiDisj` and `RigidConstSortDisj` are argued above to be
downstream of `PiInv` plus confluence, but that argument is not machine-checked here, because
doing so non-circularly requires re-deriving `ConstSpine.lean`'s three-step Church–Rosser
argument with `PiInv` threaded through in place of its internal `forallE_inv` call, and with
`KCanonical.CRStatement` hypothesised rather than `crStatement_holds` applied.  Until that is
done, the honest statement of the corner is: **two nodes for certain (`SortUniq`, `PiInv`),
plus three constant-spine conjuncts that are very likely not independent.**

Anyone doing that work should also note `KCanonical.not_crStatement_of_kstep`: confluence *as
stated there* is refuted at any `Params` instance registering the ι-rule of a large-eliminating
subsingleton, so the hypothesis to thread is whatever survives that refutation, not
`CRStatement` verbatim.
-/

end VEnv
end Lean4Lean
