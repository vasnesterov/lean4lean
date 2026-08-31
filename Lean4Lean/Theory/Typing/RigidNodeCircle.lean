import Lean4Lean.Theory.Typing.PiLevelPin

/-!
# What `WF.rigidShapeUniqNS` is, exactly — and why it is *not* `VEnv.SortUniq`

`Injectivity.lean`'s `VEnv.WF.rigidShapeUniq` was the second-largest hole in the tree (176
transitive users).  The question this file answers is the classification question: **does it
reduce to `VEnv.SortUniq`?**

**Answer: no.**  It reduces to a conjunction of five properties, the first of which is
`VEnv.PiInv` — unstratified Π-injectivity — and `SortUniq` is not one of them.

Read the "no" precisely, because it is a claim about this tree and not a provability
separation: nothing below shows `SortUniq → PiInv` is *unprovable*.  What is machine-checked
is (a) the exact decomposition, which contains `PiInv` and does not contain `SortUniq`, and
(b) that the one route from `SortUniq` towards `PiInv` this tree has — level arithmetic
through `PiInvStratApp` — is closed in **both** coordinates (`PiLevelPin.imax_cod_not_pinned`
and `imax_dom_not_pinned` below).  A model-side proof of `SortUniq` therefore leaves `PiInv`
standing, and planning should assume two fronts, not one.

Concretely, this file proves:

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
codomain half, and `imax_dom_not_pinned` below machine-checks why the domain half cannot come
from that direction: at a `Prop`-valued codomain the type of a Π carries *no* information
about its domain.  So `SortUniq → PiInv` is not available here, and the corner has **two**
nodes:

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
entry excluded by `¬ BothSort`, universe uniqueness is not needed anywhere.

`sorryAx`-free.  `htr` is `VEnv.ProofTransport`, taken as a hypothesis rather than supplied by
`WF.proofTransport`, because that supply is tainted through `forallE_inv_stratified`; see
`ProofTransport`'s docstring.

**The `htr` tax is smaller than it looks** (`Theory/Typing/InjSpineTransport.lean`).  It is used
in **one** of the nine branches below — `app`/`app` — and there its subject is the rule-free
constant spine, never an arbitrary term.  `proofTransportSpine_of` supplies that restricted form
from `ConvPiInv` alone (`BaseUniqChain.baseUniqCAt_of` needs `ConvSortInv` only for its
`.forallE` head, which a spine never presents), and `InjChainStep.convPiInv_of_convStep2`
supplies `ConvPiInv` from `ConvStep2 ∧ PiInv` — with `PiInv` already conjunct 1 here.  So
`rigidShapeUniqNS_of_family_convStep2` replaces `htr` by `ConvStep2`, and since
`InjChainStep.sortUniq_iff_convStep2_sortInv` splits hole A into `ConvStep2 ∧ SortInv` over
`PiInv`, this bridge's dependence on hole A is exactly the `ConvStep2` half.
`docs/vacuity-ledger.md` row 30's "tainted by hole A" should read "tainted by `ConvStep2`". -/
theorem rigidShapeUniqNS_of_family (hord : Ordered env) (htr : env.ProofTransport U)
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
      exact ⟨⟨u, ha⟩, v, hb, ha.defeqDF_l hord hb⟩
    | app c ls as => exact hcp hΓ hr₂ hs.symm
  | app c ls as =>
    cases s₂ with
    | sort v => exact hcs hΓ hr₁ hs
    | pi A B => exact hcp hΓ hr₁ hs
    | app c' ls' as' =>
      rintro rfl
      exact hca hΓ hr₁ (fun hp => hnp (htr hΓ ⟨T, h₁.symm⟩ hp)) hs

/-- **⟹, first conjunct.**  Chases `Injectivity.rigidPiUniq_iff_piInv`. -/
theorem RigidShapeUniqNS.piInv (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (htr : env.ProofTransport U) (h : env.RigidShapeUniqNS U) : env.PiInv U :=
  piInv_of_rigidPiUniq henv hsu (RigidShapeUniqNS.piUniqOf hsu henv.ordered htr h)

/-- Every off-diagonal entry is reached by taking the middle term to be the left shape
itself: `h.trans h.symm` types it at the shared type.  For the sort/Π entry the `¬ IsProof`
side condition needs no transport at all — the middle term *is* `.sort u`, so
`sort_not_proof` applies directly. -/
theorem RigidShapeUniqNS.sortPiDisj (hsu : env.SortUniq U) (hord : Ordered env)
    (h : env.RigidShapeUniqNS U) : env.RigidSortPiDisj U := by
  intro Γ u A B hΓ ⟨T, hd⟩
  exact h (s₁ := .sort u) (s₂ := .pi A B) hΓ
    (fun ⟨_, hp0, he⟩ => sort_not_proof hsu hord hΓ hp0 he) trivial trivial not_false
    (hd.trans hd.symm) hd

@[inherit_doc RigidShapeUniqNS.sortPiDisj]
theorem RigidShapeUniqNS.constPiDisj (hsu : env.SortUniq U) (hord : Ordered env)
    (htr : env.ProofTransport U) (h : env.RigidShapeUniqNS U) : env.RigidConstPiDisj U := by
  intro Γ c ls as A B hΓ hc ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .pi A B) hΓ
    (not_isProof_of_forallE' hsu hord htr hΓ ⟨_, hd⟩) hc trivial not_false
    (hd.trans hd.symm) hd

@[inherit_doc RigidShapeUniqNS.sortPiDisj]
theorem RigidShapeUniqNS.constSortDisj (hsu : env.SortUniq U) (hord : Ordered env)
    (htr : env.ProofTransport U) (h : env.RigidShapeUniqNS U) : env.RigidConstSortDisj U := by
  intro Γ c ls as u hΓ hc ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .sort u) hΓ
    (not_isProof_of_sort' hsu hord htr hΓ ⟨_, hd⟩) hc trivial not_false
    (hd.trans hd.symm) hd

/-- The `app`/`app` entry needs no side input at all: the family statement already carries the
`¬ IsProof` premise the bridge asks for, at the very term the bridge asks about. -/
theorem RigidShapeUniqNS.constAppInv (h : env.RigidShapeUniqNS U) :
    env.RigidConstAppInv U := by
  intro Γ c ls ls' as as' hΓ hc hnp ⟨T, hd⟩
  exact h (s₁ := .app c ls as) (s₂ := .app c ls' as') hΓ hnp hc hc not_false
    (hd.trans hd.symm) hd rfl

/-- **The classification, both ways.**  `sorryAx`-free.

The narrowed 176-user bridge is *exactly* the conjunction of unstratified Π-injectivity and
the three constant-spine facts.  `VEnv.SortUniq` does not occur in it; it occurs only in the
`sort`/`sort` entry that `Injectivity.rigidShapeUniq_of_sortUniq` already removed, and as a
side hypothesis here, where its only job is to know that a sort and a Π are not proofs.

So the answer to "does `rigidShapeUniq` reduce to `SortUniq`?" is **no**, and the second node
of the injectivity corner is `VEnv.PiInv`. -/
theorem rigidShapeUniqNS_iff_family (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (htr : env.ProofTransport U) :
    env.RigidShapeUniqNS U ↔
      (env.PiInv U ∧ env.RigidSortPiDisj U ∧ env.RigidConstAppInv U ∧
        env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) :=
  ⟨fun h => ⟨h.piInv henv hsu htr, h.sortPiDisj hsu henv.ordered, h.constAppInv,
      h.constPiDisj hsu henv.ordered htr, h.constSortDisj hsu henv.ordered htr⟩,
   fun ⟨hpi, hsp, hca, hcp, hcs⟩ =>
     rigidShapeUniqNS_of_family henv.ordered htr hpi hsp hca hcp hcs⟩

/-!
## §4 Axiom check

    #print axioms Lean4Lean.VEnv.imax_dom_not_pinned
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_family
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_iff_family
    #print axioms Lean4Lean.VEnv.RigidShapeUniqNS.piInv

all report no `sorryAx`, and so do `Injectivity.rigidShapeUniq_of_sortUniq`,
`Injectivity.IsDefEqU.forallE_inv_of_rigidPi`, `Injectivity.rigidPiUniq_iff_piInv` and
`Injectivity.RigidShapeUniqNS.piUniqOf`.  That took care: the first draft of this file *was*
tainted, through `VEnv.IsProof.defeqU`, whose cone reaches `IsDefEqU.forallE_inv_stratified`
by way of `HasType.defeqU_l'`.  Hence `VEnv.ProofTransport`, and hence every statement here
carrying `hsu` and `htr` explicitly instead of helping itself to `WF.sortUniq'` and
`WF.proofTransport`.

The lesson generalises: in this corner of the tree, `¬ IsProof` premises are *not* free.  They
look free because `Injectivity.not_isProof_of_defeqU_forallE` and `not_isProof_of_defeqU_sort`
discharge them with no hypothesis — but both are `sorryAx`-backed.  `not_isProof_of_forallE'`
and `not_isProof_of_sort'` are the clean forms.

Instrument caution, paid for here: `#print axioms` run from a `lake env lean` scratch file
reads the **compiled `.olean`**, not the source just edited.  The first three runs of the check
above reported `sorryAx` for statements whose source had already been cleaned; the module had
not been rebuilt.  `lake build <module>` first, or the answer is the previous build's.

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
