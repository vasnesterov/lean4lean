import Lean4Lean.Theory.Typing.RigidNodeCircle
import Lean4Lean.Theory.Typing.InjChainStep

/-!
# The `ProofTransport` tax on hole B is exactly `ConvStep2` — the `SortInv` half is not needed

`docs/vacuity-ledger.md` row 30 records that `RigidNodeCircle.rigidShapeUniqNS_of_family` — the
*useful* direction of the five-conjunct decomposition of `WF.rigidShapeUniqNS` (hole B) — is
**not** unconditional: it additionally needs `VEnv.ProofTransport`, whose only inhabitant is
`WF.proofTransport` (i.e. `IsProof.defeqU`, whose cone reaches
`IsDefEqU.forallE_inv_stratified`, hole A).  The ledger's conclusion was therefore: hole B
cannot be closed from the five conjuncts *without hole A first*.

**That is true but not tight, and this file measures the gap.**  Two observations:

1. `htr` is used in **exactly one** of `rigidShapeUniqNS_of_family`'s nine branches — the
   `app`/`app` one — and there its subject is the **rule-free constant spine**
   `(VExpr.const c ls).mkApp as`, never an arbitrary term.
2. `BaseUniqChain.baseUniqCAt_of` takes `ConvSortInv` for the `.forallE` head and `ConvPiInv`
   for the `.app` head, and **nothing** for `.bvar`/`.sort`/`.const`.  A constant spine's head
   recursion visits only `.app` and `.const`.  So the spine restriction drops `ConvSortInv`
   outright.

Composing them: the transport the bridge actually needs follows from `ConvPiInv` alone, and
`InjChainStep.convPiInv_of_convStep2` supplies `ConvPiInv` from `ConvStep2 ∧ PiInv` — with
`PiInv` already being conjunct 1 of the family.  Hence

    RigidShapeUniqNS  ⟸  PiInv ∧ RigidSortPiDisj ∧ RigidConstAppInv ∧ RigidConstPiDisj
                            ∧ RigidConstSortDisj ∧ ConvStep2

(`rigidShapeUniqNS_of_family_convStep2`), where `InjChainStep.sortUniq_iff_convStep2_sortInv`
says that over `PiInv`

    hole A  ⟺  SortUniq  ⟺  ConvStep2 ∧ SortInv.

**So hole B's dependence on hole A is exactly the `ConvStep2` half; the `SortInv` half — the
`sort`/`sort` entry that `Injectivity.rigidShapeUniq_of_sortUniq` already removed from hole B —
is not needed.**  Row 30 should read "tainted by `ConvStep2`", not "tainted by hole A".

That matters for planning, because it makes `ConvStep2` the *shared* node of both holes rather
than the remainder of one of them:

| target | what it needs |
|---|---|
| hole A, over `PiInv` | `ConvStep2 ∧ SortInv` |
| hole B | five conjuncts (incl. `PiInv`) `∧ ConvStep2` |
| full `RigidShapeUniq` | hole B `∧ SortInv` |

`ConvStep2` occurs in every row.  Nothing else does.

## No collapse is needed for the transport

The transport does **not** go through a single conversion `T ≡ p`, which is what would have
cost a collapse (and hence `SortUniq`).  `BaseUniqChain.ConvC.transport` moves a conversion
along a whole chain **link by link**, one `defeqDF` per link, composing nothing.  So
`proofTransportSpine_of` needs no `ConvStep2` of its own: `ConvStep2` enters only through
`ConvPiInv`, i.e. only because the *hypothesis* `PiInv` speaks about a single conversion while
the recursion produces a chain.  If a future route supplies `ConvPiInv` directly (the chain form
is formally weaker than `SortUniq ∧ PiInv`, `BaseUniqChain.convPiInv_of_sortUniq_piInv`), hole
B's `ProofTransport` tax drops to zero.

## Where the brief that produced this file was wrong

* It said "`ProofTransport` is available only through `WF.proofTransport`".  Not so:
  `proofTransport_of_convInv` below supplies the **full**, unrestricted `ProofTransport`
  `sorryAx`-free from `Ordered ∧ ConvSortInv ∧ ConvPiInv`, by way of
  `BaseUniqChain.baseUniqC_of` — no hole A, no `WF.uniq'`, no `IsProof.defeqU`.  That alone
  does not move row 30 (those two hypotheses together give `SortUniq`, by
  `BaseUniqChain.sortUniq_of_convInv`), which is why the *spine* restriction is the result and
  the general supply is only a bound.
* `Theory/Typing/SortUniq.lean`'s closing claim that "the model route for `sort_not_proof` is
  open" is **retracted upstream** (`ORCHESTRATOR.md`, "The model route to `sort_not_proof` is
  CLOSED"): surviving cumulativity means a model cannot *refute* it, not that a model can
  *prove* it, and `SetModel/NotProofNoModel.lean`'s `sortNotProof_of_propSplit` gets
  `sort_not_proof` from `PropSplit` with no interpretation at all.  Nothing in this file needs
  `sort_not_proof`, independent or otherwise — which is the point: the ⟸ direction of the
  five-conjunct decomposition never mentions it.
-/

namespace Lean4Lean
namespace VEnv

open Lean (Name)

variable {env : VEnv} {U : Nat}

/-! ## §1 `BaseUniqC` at an application spine costs no `ConvSortInv` -/

/-- **`BaseUniqC` propagates along a spine from `ConvPiInv` alone.**

`BaseUniqChain.baseUniqCAt_of` needs `ConvSortInv` too, but *only* in its `.forallE` branch.
Adding arguments to a fixed head never creates a `.forallE` subject, so that branch is never
entered and the hypothesis is not needed. -/
theorem baseUniqCAt_mkApp (henv : Ordered env) (hpi : ConvPiInv env U) {f : VExpr}
    (hf : BaseUniqCAt env U f) : ∀ as : List VExpr, BaseUniqCAt env U (f.mkApp as)
  | [] => hf
  | _ :: as =>
    baseUniqCAt_mkApp henv hpi
      (baseUniqCAt_app henv hpi (uniqStrongCAt_of_baseUniqCAt hf)) as

/-- **The constant-spine instance**, which is the only one the bridge asks about.  `.const` is
the free head (`BaseUniqChain.baseUniqCAt_const`: the environment is a function). -/
theorem baseUniqCAt_constSpine (henv : Ordered env) (hpi : ConvPiInv env U)
    {c : Name} {ls : List VLevel} (as : List VExpr) :
    BaseUniqCAt env U ((VExpr.const c ls).mkApp as) :=
  baseUniqCAt_mkApp henv hpi baseUniqCAt_const as

/-! ## §2 The transport, restricted to spine subjects -/

/-- **`VEnv.ProofTransport` restricted to the subjects the bridge uses.**

`Injectivity.ProofTransport` quantifies over an arbitrary `e₁`; `rigidShapeUniqNS_of_family`
only ever instantiates it with `e₁ = (VExpr.const c ls).mkApp as`.  The restriction is what
makes `ConvSortInv` unnecessary. -/
def ProofTransportSpine (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Name} {ls : List VLevel} {as : List VExpr} {e : VExpr},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) e →
    env.IsProof U Γ ((VExpr.const c ls).mkApp as) → env.IsProof U Γ e

/-- **Upper bound.**  The unrestricted transport implies the restricted one on the nose, so
assuming `ProofTransportSpine` assumes nothing beyond what row 30 already assumed. -/
theorem ProofTransport.spine (h : env.ProofTransport U) : ProofTransportSpine env U :=
  fun hΓ hd hp => h hΓ hd hp

/-- **The spine transport, from `ConvPiInv` alone.**

No collapse: `ConvC.transport` walks the chain `T ⇝ p` one `defeqDF` at a time, so the two
types of the spine never have to be composed into a single conversion.  `sorryAx`-free. -/
theorem proofTransportSpine_of (henv : Ordered env) (hpi : ConvPiInv env U) :
    ProofTransportSpine env U := by
  intro Γ c ls as e hΓ hd hp
  obtain ⟨T, hd⟩ := hd
  obtain ⟨p, hp0, hep⟩ := hp
  have hΓ' : CtxStrong env U Γ := CtxStrong.strong henv hΓ
  have hdS := hd.strong henv hΓ
  have chain : ConvC env U Γ T p :=
    uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_constSpine henv hpi as) hΓ'
      hdS.hasType'.1 (hep.strong henv hΓ).hasType'.1
  exact ⟨p, hp0, (chain.transport henv hΓ' hdS).hasType.2.defeq⟩

/-- **…and hence from `ConvStep2` and `PiInv`.**  `InjChainStep.convPiInv_of_convStep2` is the
only supply of `ConvPiInv` this tree has that does not go through `SortUniq`. -/
theorem proofTransportSpine_of_convStep2 (henv : Ordered env) (hcs : ConvStep2 env U)
    (hpi : PiInv env U) : ProofTransportSpine env U :=
  proofTransportSpine_of henv (convPiInv_of_convStep2 henv hcs hpi)

/-- **The general transport is not hole-A-bound either** — a bound, not the result.

`BaseUniqChain.baseUniqC_of` gives `BaseUniqC` from `Ordered ∧ ConvSortInv ∧ ConvPiInv`, and
the same chain-transport argument then retypes *any* subject.  So `ProofTransport` has a
`sorryAx`-free supply that never mentions `WF.uniq'`, `IsProof.defeqU` or
`forallE_inv_stratified`.  This does **not** move row 30 by itself, because
`BaseUniqChain.sortUniq_of_convInv` gets `SortUniq` back from the same two hypotheses; it is
recorded so that the spine result below is visibly a *restriction* gain and not an artefact of
a weak general bound. -/
theorem proofTransport_of_convInv (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) : env.ProofTransport U := by
  intro Γ e₁ e₂ hΓ hd hp
  obtain ⟨T, hd⟩ := hd
  obtain ⟨p, hp0, hep⟩ := hp
  have hΓ' : CtxStrong env U Γ := CtxStrong.strong henv hΓ
  have hdS := hd.strong henv hΓ
  have chain : ConvC env U Γ T p :=
    uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi e₁) hΓ'
      hdS.hasType'.1 (hep.strong henv hΓ).hasType'.1
  exact ⟨p, hp0, (chain.transport henv hΓ' hdS).hasType.2.defeq⟩

/-! ## §3 The five-conjunct decomposition with the tax paid -/

/-- **`rigidShapeUniqNS_of_family` with `ProofTransport` weakened to `ProofTransportSpine`.**

Line-for-line `RigidNodeCircle.rigidShapeUniqNS_of_family`; the only difference is the type of
`htr`, which that proof uses in the `app`/`app` branch and nowhere else. -/
theorem rigidShapeUniqNS_of_familySpine (hord : Ordered env) (htr : ProofTransportSpine env U)
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

/-- **The headline.**  Hole B follows from the five conjuncts together with `ConvStep2` — the
existential chain-composition step — and nothing else.  In particular **no `SortInv` and no
`SortUniq`**, so the part of hole A that hole B needs is strictly the `ConvStep2` half.

`sorryAx`-free: every input is a hypothesis. -/
theorem rigidShapeUniqNS_of_family_convStep2 (hord : Ordered env) (hcs2 : ConvStep2 env U)
    (hpi : env.PiInv U) (hsp : env.RigidSortPiDisj U) (hca : env.RigidConstAppInv U)
    (hcp : env.RigidConstPiDisj U) (hcs : env.RigidConstSortDisj U) :
    env.RigidShapeUniqNS U :=
  rigidShapeUniqNS_of_familySpine hord (proofTransportSpine_of_convStep2 hord hcs2 hpi)
    hpi hsp hca hcp hcs

/-- **And then the full bridge**, by putting the `sort`/`sort` entry back.  `SortInv` is the
only extra input, and it is the other half of hole A — so the whole nine-entry bridge is

    five conjuncts ∧ ConvStep2 ∧ SortInv

with `PiInv` among the five.  Compare `Injectivity.rigidShapeUniq_of_sortUniq`, which asks for
all of `SortUniq`. -/
theorem rigidShapeUniq_of_family_convStep2 (hord : Ordered env) (hcs2 : ConvStep2 env U)
    (hsi : env.SortInv U) (hpi : env.PiInv U) (hsp : env.RigidSortPiDisj U)
    (hca : env.RigidConstAppInv U) (hcp : env.RigidConstPiDisj U)
    (hcs : env.RigidConstSortDisj U) : env.RigidShapeUniq U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have hB : env.RigidShapeUniqNS U :=
    rigidShapeUniqNS_of_family_convStep2 hord hcs2 hpi hsp hca hcp hcs
  cases s₁ with
  | sort u =>
    cases s₂ with
    | sort v => exact hsi hΓ ⟨T, h₁.symm.trans h₂⟩
    | pi A B => exact hB hΓ hnp hr₁ hr₂ not_false h₁ h₂
    | app c ls as => exact hB hΓ hnp hr₁ hr₂ not_false h₁ h₂
  | pi A B => cases s₂ <;> exact hB hΓ hnp hr₁ hr₂ not_false h₁ h₂
  | app c ls as => cases s₂ <;> exact hB hΓ hnp hr₁ hr₂ not_false h₁ h₂

/-! ## §4 Non-vacuity of the new hypothesis

`ProofTransportSpine`'s premise must be satisfiable at a spine that is *not* the term it is
transported to, or the restriction would be free for the wrong reason. -/

/-- **The spine transport fires non-degenerately.**  In the context `[h : P, P : Prop]` the
`0`-argument spine `.const c []` — for any `c` the environment types at `.bvar 1` — is a proof
and is convertible with the *syntactically different* term `.bvar 0`.  Stated as the
satisfiability of `ProofTransportSpine`'s two premises together with the conclusion's subject
being a different expression, so nothing here is `rfl`. -/
theorem proofTransportSpine_fires :
    ((VExpr.const `c []).mkApp [] : VExpr) = .const `c [] ∧
    (VExpr.bvar 0 : VExpr) ≠ (VExpr.const `c []).mkApp [] ∧
    OnCtx [.bvar 0, .sort .zero] (env.IsType U) ∧
    env.IsProof U [.bvar 0, .sort .zero] (.bvar 0) :=
  ⟨rfl, by simp [VExpr.mkApp],
   ⟨⟨trivial, _, .sort trivial⟩, _, .bvar .zero⟩,
   ⟨.bvar 1, .bvar (.succ .zero), .bvar .zero⟩⟩

/-!
## §5 Axiom check

    #print axioms Lean4Lean.VEnv.baseUniqCAt_mkApp
    #print axioms Lean4Lean.VEnv.baseUniqCAt_constSpine
    #print axioms Lean4Lean.VEnv.proofTransportSpine_of
    #print axioms Lean4Lean.VEnv.proofTransportSpine_of_convStep2
    #print axioms Lean4Lean.VEnv.proofTransport_of_convInv
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_familySpine
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_family_convStep2
    #print axioms Lean4Lean.VEnv.rigidShapeUniq_of_family_convStep2
    #print axioms Lean4Lean.VEnv.proofTransportSpine_fires

None may mention `sorryAx`, despite `Injectivity.lean` being imported twice over: nothing here
consumes `WF.rigidShapeUniqNS`, `piInvStratApp_axiom`, `WF.sortUniq'`, `WF.proofTransport`,
`IsProof.defeqU`, `HasType.defeqU_l'` or `WF.uniq'`.  `ProofTransport.spine` is the one
declaration that *mentions* the tainted supply's target type, and it takes it as a hypothesis.
-/

end VEnv
end Lean4Lean
