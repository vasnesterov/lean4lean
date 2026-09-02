import Lean4Lean.Theory.Typing.SortInvIndep

/-!
# `ConvPiInv` is free after `SortInvIndep.lean`, and the corner's residual is two statements

`docs/handoff-sortinv-route.md` §7 item 1 asks for `ConvPiInv` to be discharged so that
`sortUniq_of_propAgreeOn` and `sortLinkInvUC_iff_sortUniq` shed it as a hypothesis, leaving the
sort side's residual as `ConvStep2 ∧ ShapeMidShapeless` with nothing else.  **That is done here,
and it costs less than the handoff expected:** the route it proposed (through
`piInv_of_propAgreeOn`, hence through `RigidShapeUniqNS`) is *not* the cheap one and would have
made the statement weaker, because `RigidShapeUniqNS` is a strictly larger hypothesis than the
`ConvPiInv` it replaces.  The cheap route was already in `InjOneFact.lean` and unnoticed:

* `InjOneFact.shapeLinkAgree_iff` decomposes `ShapeLinkAgree` into three entries, and the
  middle one, `PiLinkInvUC`, already concludes **both** halves of `ConvPiInv`'s conclusion
  (`ConvC Γ A A' ∧ ConvC (A::Γ) B B'`) — for a single link at an arbitrary index.
* `InjChainStep.ConvC.collapseE` turns a chain into a single link from `ConvStep2` alone.

Composing the two gives `ConvPiInv` from `ConvStep2 ∧ ShapeLinkAgree` (§1), and
`SortInvIndep.shapeLinkAgree_of_propAgreeOn` supplies `ShapeLinkAgree` from
`VEnv.WF ∧ PropAgreeOn ∧ ShapeMidShapeless`.  `InjOneFact.lean` only ever exported the
*codomain* half of this (`convPiInvCod_of_shapeLinkAgree`), which is why it was missed.

## What that buys, and the honest grade

**Bought** (§2–§4), all `sorryAx`-free, all with hole-cone `[]`:

| target | before | after |
| --- | --- | --- |
| `SortUniq` | `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ConvPiInv ∧ ShapeMidShapeless` | `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ShapeMidShapeless` |
| `PiInv` | `WF ∧ PropAgreeOn ∧ RigidShapeUniqNS` | `WF ∧ ConvStep2 ∧ ShapeLinkAgree` (no `PropAgreeOn` at all) |
| `RigidSortPiDisj` | conjunct 2 of `rigidShapeUniqNS_iff_family` | free from `ShapeLinkAgree` |
| `RigidShapeUniqNS` (hole B) | five conjuncts `∧ ConvStep2` | **three** const-spine conjuncts `∧ ConvStep2 ∧ ShapeMidShapeless ∧ PropAgreeOn` |

So `docs/vacuity-ledger.md`'s corner table row "hole B: the five conjuncts (incl. `PiInv`)
`∧ ConvStep2`" should read **three** conjuncts, and all three are the constant-spine facts.

**The grade, and it is not a strength reduction.**  `ShapeMidShapeless` is equivalent to
`ShapeLinkAgree` (`InjOneFact.shapeMidShapeless_iff`, `Ordered env` only), and
`shapeLinkAgree_iff` says `ShapeLinkAgree` *is* the conjunction of all three entries of the
corner — including `PiLinkInvUC`, which `InjOneFact.lean` §6 itself records as "at least as
strong as the two Π consumers".  So every reduction in the table above lands in a hypothesis
that is **known to be at least as strong as its own target**.  They are therefore *not*
reductions in strength; they are a **single normal form** for the corner:

    the sort/Π corner, after the independent source, is exactly  `ConvStep2 ∧ ShapeMidShapeless`

which is what makes `SortInvIndep.lean` §3's negative airtight rather than what weakens it.
This is graded **collapse-shaped, consolidating** in `docs/handoff-sortinv-route.md` §8: two
hypotheses instead of four, no claim of a weaker obligation.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 `ConvPiInv` from a single-link fact and the chain collapse -/

/-- **`ConvPiInv` from `PiLinkInvUC` and `ConvStep2`.**  The companion of
`InjOneFact.convPiInvCod_of_shapeLinkAgree`, which exports only the codomain half even though
`PiLinkInvUC` concludes both.  `ConvC.collapseE`'s `refl` branch is a *syntactic* equation
between two Π's, so the domain and codomain equations come out by `injection` and need no
reflexivity witness. -/
theorem convPiInv_of_convStep2_piLinkInvUC (hcs : ConvStep2 env U) (H : PiLinkInvUC env U) :
    ConvPiInv env U := by
  intro Γ A B A' B' hΓ h
  match h.collapseE hcs hΓ with
  | .inl eq => cases eq; exact ⟨.refl, .refl⟩
  | .inr ⟨_, hw⟩ => exact H hΓ hw

/-- **…and hence from the one fact.**  `ConvStep2 ∧ ShapeLinkAgree → ConvPiInv`. -/
theorem convPiInv_of_shapeLinkAgree (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) :
    ConvPiInv env U :=
  convPiInv_of_convStep2_piLinkInvUC hcs (shapeLinkAgree_iff.1 H).2.1

/-- **Both chain-inversion hypotheses at once**, which is what `BaseUniqChain`'s recursion asks
for.  `InjOneFact.convSortInv_of_shapeLinkAgree` is the other half. -/
theorem convInv_of_shapeLinkAgree (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) :
    ConvSortInv env U ∧ ConvPiInv env U :=
  ⟨convSortInv_of_shapeLinkAgree hcs H, convPiInv_of_shapeLinkAgree hcs H⟩

/-! ## §2 The sort side, with `ConvPiInv` gone -/

/-- **The handoff's §7 item 1, done.**  `SortInvIndep.sortUniq_of_propAgreeOn` with its
`ConvPiInv` hypothesis discharged: given the independent source, the sort side's residual is
exactly `ConvStep2 ∧ ShapeMidShapeless`. -/
theorem sortUniq_of_propAgreeOn' (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hcs : ConvStep2 env U) (hm : ShapeMidShapeless env U) : env.SortUniq U :=
  have H : ShapeLinkAgree env U := shapeLinkAgree_of_propAgreeOn henv hT hm
  sortUniq_of_convInv henv.ordered (convSortInv_of_shapeLinkAgree hcs H)
    (convPiInv_of_shapeLinkAgree hcs H)

/-- The same with the one fact in place of the residual, which is the form the `↔` below
wants. -/
theorem sortUniq_of_shapeLinkAgree (henv : Ordered env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) : env.SortUniq U :=
  sortUniq_of_convInv henv (convSortInv_of_shapeLinkAgree hcs H)
    (convPiInv_of_shapeLinkAgree hcs H)

/-- **`SortLinkInvUC ↔ SortUniq` with the `ConvPiInv` hypothesis replaced by the independent
source and the `trans` residual** — `SortInvIndep.sortLinkInvUC_iff_sortUniq` with its last
non-`ConvStep2` hypothesis paid.  Note the `←` direction does not use `hm` at all. -/
theorem sortLinkInvUC_iff_sortUniq' (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hcs : ConvStep2 env U) (hm : ShapeMidShapeless env U) :
    SortLinkInvUC env U ↔ env.SortUniq U :=
  ⟨fun _ => sortUniq_of_propAgreeOn' henv hT hcs hm, sortLinkInvUC_of_sortUniq henv.ordered⟩

/-! ## §3 `PiInv` without `RigidShapeUniqNS` — and without `PropAgreeOn`

`SortInvIndep.piInv_of_propAgreeOn` derives `PiInv` from `VEnv.WF ∧ PropAgreeOn ∧
RigidShapeUniqNS`.  That was the point of that file: it takes `PiInv` off
`forallE_inv_stratified`.  It is *not* the cheapest route: `PiLinkInvUC` already states
Π-injectivity at an arbitrary index for a single link, so all that is missing is the chain
collapse, and the independent source is not needed anywhere. -/

/-- **Unstratified Π-injectivity from the one fact and the chain collapse.**

No `RigidShapeUniqNS`, no `PropAgreeOn`, no `SortUniq`, no `ProofTransport`.  The only place a
side fact is used is `ConvC.collapseE`'s `refl` branch, and there `HasType.forallE_inv`
supplies the reflexivity witness from the Π's own typing. -/
theorem piInv_of_shapeLinkAgree (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) : env.PiInv U := by
  intro Γ A B A' B' hΓ hd
  obtain ⟨T, hd⟩ := hd
  have hΓ' : CtxStrong env U Γ := CtxStrong.strong henv.ordered hΓ
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hd.hasType.1.forallE_inv henv.ordered
  have hΓA : CtxStrong env U (A::Γ) := ⟨hΓ', u, hA.strong henv.ordered hΓ⟩
  obtain ⟨hdom, hcod⟩ := (shapeLinkAgree_iff.1 H).2.1 hΓ' (hd.strong henv.ordered hΓ)
  refine ⟨?_, ?_⟩
  · match hdom.collapseE hcs hΓ' with
    | .inl eq => exact eq ▸ ⟨u, hA⟩
    | .inr ⟨w, hw⟩ => exact ⟨w, hw.defeq⟩
  · match hcod.collapseE hcs hΓA with
    | .inl eq => exact eq ▸ ⟨v, hB⟩
    | .inr ⟨w, hw⟩ => exact ⟨w, hw.defeq⟩

/-! ## §4 Hole B: two of the five conjuncts are now free -/

/-- `RigidSortPiDisj` — conjunct 2 of `RigidNodeCircle.rigidShapeUniqNS_iff_family` — is the
sort/Π entry of the one fact, so it is free from it. -/
theorem rigidSortPiDisj_of_shapeLinkAgree (henv : Ordered env) (H : ShapeLinkAgree env U) :
    env.RigidSortPiDisj U :=
  SortPiDisjUC.rigidSortPiDisj henv (shapeLinkAgree_iff.1 H).2.2

/-- **Hole B from the three constant-spine conjuncts alone**, plus `ConvStep2` and the one
fact.  `RigidNodeCircle.rigidShapeUniqNS_of_family`'s remaining two conjuncts (`PiInv` by §3,
`RigidSortPiDisj` above) and its `ProofTransport` premise (by
`InjSpineTransport.proofTransportSpine_of` on the `ConvPiInv` of §1) are all supplied. -/
theorem rigidShapeUniqNS_of_constSpine (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) (hca : env.RigidConstAppInv U) (hcp : env.RigidConstPiDisj U)
    (hcsd : env.RigidConstSortDisj U) : env.RigidShapeUniqNS U :=
  rigidShapeUniqNS_of_familySpine henv.ordered
    (proofTransportSpine_of henv.ordered (convPiInv_of_shapeLinkAgree hcs H))
    (piInv_of_shapeLinkAgree henv hcs H) (rigidSortPiDisj_of_shapeLinkAgree henv.ordered H)
    hca hcp hcsd

/-- …and with the independent source in place of the one fact, which is the form
`SortInvIndep.lean` leaves the corner in. -/
theorem rigidShapeUniqNS_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hcs : ConvStep2 env U) (hm : ShapeMidShapeless env U) (hca : env.RigidConstAppInv U)
    (hcp : env.RigidConstPiDisj U) (hcsd : env.RigidConstSortDisj U) :
    env.RigidShapeUniqNS U :=
  rigidShapeUniqNS_of_constSpine henv hcs (shapeLinkAgree_of_propAgreeOn henv hT hm)
    hca hcp hcsd

/-! ## §5 The anti-collapse measurement, run in the direction that matters

`docs/vacuity-ledger.md` §0 asks whether the thing reduced *to* is equivalent to the thing
reduced *from*.  Here the answer is **yes, by construction, and it is stated rather than
hidden**: `InjOneFact.shapeMidShapeless_iff` makes the residual equivalent to `ShapeLinkAgree`,
and `shapeLinkAgree_iff` makes *that* the conjunction of the three entries of the corner.  So
each of §2–§4 reduces a target to a hypothesis containing that target's own entry.

The consequence for planning is the useful part, and it is the *converse* implications that
make it precise: each entry of the residual is recovered from the corresponding target, so the
residual is not a strictly stronger demand either — it is the same demand, packaged once. -/

/-- The sort entry comes back from `SortUniq`, so §2 is an equivalence in that coordinate and
not a strengthening (`SortInvIndep.sortLinkInvUC_of_sortUniq` is the inhabitant). -/
theorem sortLinkInvUC_of_sortUniq' (hord : Ordered env) (hsu : env.SortUniq U) :
    SortLinkInvUC env U := sortLinkInvUC_of_sortUniq hord hsu

/-- The sort/Π entry comes back from `RigidSortPiDisj`, so §4's conjunct 2 is an equivalence
(`InjOneFact.RigidSortPiDisj.sortPiDisjUC`). -/
theorem sortPiDisjUC_of_rigidSortPiDisj (H : env.RigidSortPiDisj U) : SortPiDisjUC env U :=
  RigidSortPiDisj.sortPiDisjUC H

/-- **What is NOT established, stated as the negative it is.**  `PiLinkInvUC` is not recovered
from `PiInv`: `InjOneFact.lean` §6 records that the converse of
`PiLinkInvUC → PiLinkInvCod ∧ PiLinkInvDom` "is not available and no claim is made that it
is", because moving an arbitrary index `T` to a syntactic sort is uniqueness of typing.  So
§3's reduction of `PiInv` to `ShapeLinkAgree` is into something *possibly strictly stronger*,
and it is recorded that way.  The one-line fact below is the direction that *is* free, kept as
the control that the instrument fires at all. -/
theorem piLinkInvCod_of_shapeLinkAgree (H : ShapeLinkAgree env U) : PiLinkInvCod env U :=
  PiLinkInvUC.piLinkInvCod (shapeLinkAgree_iff.1 H).2.1

section Audit
#print axioms Lean4Lean.VEnv.convPiInv_of_convStep2_piLinkInvUC
#print axioms Lean4Lean.VEnv.convPiInv_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.convInv_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.sortUniq_of_propAgreeOn'
#print axioms Lean4Lean.VEnv.sortUniq_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.sortLinkInvUC_iff_sortUniq'
#print axioms Lean4Lean.VEnv.piInv_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.rigidSortPiDisj_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_constSpine
#print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_propAgreeOn
#print axioms Lean4Lean.VEnv.sortLinkInvUC_of_sortUniq'
#print axioms Lean4Lean.VEnv.sortPiDisjUC_of_rigidSortPiDisj
#print axioms Lean4Lean.VEnv.piLinkInvCod_of_shapeLinkAgree
end Audit

end VEnv
end Lean4Lean
