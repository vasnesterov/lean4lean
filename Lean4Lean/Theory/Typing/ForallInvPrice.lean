import Lean4Lean.Theory.Typing.PiInvResidual

/-!
# The price of `IsDefEqU.forallE_inv_stratified` (hole A), and it is now exact

`Theory/Typing/Injectivity.lean:261` is the `sorry` this file is about.  It is packaged there as
`VEnv.PiInvStrat`, and `Injectivity.lean` already parameterises its whole development on that
`Prop` (`uniqQ` and `uniqAux` take `PiInvStratApp`), so what is missing is an *inhabitant*.

## What is proved here

Everything below is `sorryAx`-free, and the audit blocks print the axiom sets.

**§1, the discharge.**  `piInvStrat_of_shapeLinkAgree`:

    VEnv.WF env  →  ConvStep2 env U  →  ShapeLinkAgree env U  →  PiInvStrat env U

i.e. hole A's *exact* statement (§6 restates it verbatim in the `sorry`'s own shape) from the two
`Prop`s the corner has been reduced to.  This is a composition of three theorems that all
existed — `Injectivity.piInvStrat_of`, and `PiInvResidual.{sortUniq,piInv}_of_shapeLinkAgree`
(landed 2026-09-02) — and it had not been composed: `PiInvResidual.lean` does not mention
`PiInvStrat`, and `docs/vacuity-ledger.md`'s corner table still prices hole A as
"`ConvStep2 ∧ SortInv`, **over `PiInv`**".  `PiInv` is no longer needed: it *is* the composition's
second input, supplied by `piInv_of_shapeLinkAgree`.

**§3, the price is exact.**  Over `VEnv.WF env`:

    ConvStep2 ∧ ShapeLinkAgree   ↔   PiInvStrat ∧ SortPiDisjUC

The `→` is §1 plus `shapeLinkAgree_iff`.  The `←` is §2: hole A gives back `ConvStep2` (through
`SortUniq`), `SortLinkInvUC` (ditto), and — this is the coordinate `PiInvResidual.lean` §5
explicitly records as *not* recovered from `PiInv` — `PiLinkInvUC`, which **is** recovered from
hole A, because hole A's own hypothesis is an `IsDefEqU` at an arbitrary index and
`HasTypeStrong.stratify` supplies the two stratified premises.  So the only strength the corner's
normal form has beyond hole A is `SortPiDisjUC`: *sort/Π disjointness for a single
`IsDefEqStrong` link*.

That closes the anti-vacuity question in the only form available for a hypothesis equivalent to
an open target (§7, `hyp_inhabited_iff`): the hypothesis of §1 is inhabited **iff** hole A is
(together with `SortPiDisjUC`).  It cannot be vacuous unless hole A is unsatisfiable over
well-formed environments.  An *absolute* witness is not offered and, by §3, cannot be offered
without closing the corner — that is a theorem here, not an excuse.

**§4–§5, the negative control.**  `sortPiEnv` — `InjPiRogue.rogueEnv1` with δ-rules
`rogueC ≡ ∀ (_ : Prop), Prop` **and** `rogueC ≡ Prop` — is `Ordered` and refutes
`ShapeLinkAgree` outright (`not_shapeLinkAgree_sortPiEnv`), through the sort/Π entry.  So §1 is
not a tautology of the definitions and `VEnv.WF` is load-bearing in it.  §5 proves
`¬ VEnv.WF sortPiEnv` (two δ-rules share an lhs, `DeltaUnique.WF.defEqHeadsUnique`), so the
control is a control and **not** a refutation of the corner — the same discipline
`InjPiRogue.not_wf_roguePiEnv` observes for its own witness.

The complementary control, for the *conclusion*, already exists and is not repeated here:
`Injectivity.piInvStratApp_fires` instantiates hole A's premises at a non-degenerate instance
(two syntactically different domains, hence two different codomain contexts) over **every**
environment.  So neither side of §1 is degenerate.

**§8, what to do next.**  `piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` discharges **both**
standing holes of the corner from one hypothesis set, and hole A consumes a *strict subset* of
it: hole B additionally needs the three constant-spine conjuncts.  So hole A is not a second
problem — closing hole B along `PiInvResidual.rigidShapeUniqNS_of_constSpine` closes hole A for
free.

## What is NOT proved, stated as the negatives they are

* `PiInvStrat → SortPiDisjUC` is **not** proved here and no claim is made either way; the route
  through `IsDefEqU.sort_forallE_inv` (`Injectivity.lean`) is unavailable because that theorem's
  `trans` case consumes hole B (`docs/vacuity-ledger.md` row 41).  Nor is the *separation*
  proved: no `VEnv.WF` environment is exhibited satisfying hole A and refuting `SortPiDisjUC`.
* **The substitution at the `sorry` site is not available.**  `Injectivity.lean` is eight imports
  *upstream* of `PiInvResidual.lean` (`Injectivity ← PiLevelPin ← RigidNodeCircle ←
  InjSpineTransport ← InjPiInhab ← InjPiRogue ← InjOneFact ← SortInvIndep ← PiInvResidual`), and
  even within `Injectivity.lean` the ingredient `piInvStrat_of` sits at line 580, after the
  `sorry` at 261.  §1 is therefore a *downstream* discharge: it can only be cashed by threading
  `PiInvStrat`/`PiInvStratApp` as a hypothesis, which is what `uniqQ` already does.  See
  `docs/handoff-forallinv.md`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 Forward: hole A from `ConvStep2 ∧ ShapeLinkAgree` -/

theorem piInvStrat_of_shapeLinkAgree (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) : PiInvStrat env U :=
  piInvStrat_of henv (sortUniq_of_shapeLinkAgree henv.ordered hcs H)
    (piInv_of_shapeLinkAgree henv hcs H)

theorem piInvStrat_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hcs : ConvStep2 env U) (hm : ShapeMidShapeless env U) : PiInvStrat env U :=
  piInvStrat_of_shapeLinkAgree henv hcs (shapeLinkAgree_of_propAgreeOn henv hT hm)

section Audit
#print axioms Lean4Lean.VEnv.piInvStrat_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.piInvStrat_of_propAgreeOn
end Audit

/-! ## §2 Backward: three of the four coordinates come back from hole A -/

theorem convStep2_of_piInvStrat (henv : VEnv.WF env) (hstrat : PiInvStrat env U) :
    ConvStep2 env U :=
  convStep2_of_sortUniq henv.ordered (sortUniq_of_piInvStrat henv hstrat)

theorem sortLinkInvUC_of_piInvStrat (henv : VEnv.WF env) (hstrat : PiInvStrat env U) :
    SortLinkInvUC env U :=
  sortLinkInvUC_of_sortUniq henv.ordered (sortUniq_of_piInvStrat henv hstrat)

theorem piLinkInvUC_of_piInvStrat (henv : VEnv.WF env) (hstrat : PiInvStrat env U) :
    PiLinkInvUC env U := by
  intro Γ A B A' B' T hΓ h
  obtain ⟨n, h2⟩ := h.hasType'.1.stratify
  obtain ⟨n', h3⟩ := h.hasType'.2.stratify
  obtain ⟨⟨u, hA, -⟩, v, hB, -, -⟩ := hstrat hΓ.defeq ⟨_, h.defeq⟩ h2 h3
  have hΓA : CtxStrong env U (A::Γ) := ⟨hΓ, u, hA.hasType.1.strong henv.ordered hΓ.defeq⟩
  exact ⟨.one (hA.strong henv.ordered hΓ.defeq), .one (hB.strong henv.ordered hΓA.defeq)⟩

section Audit
#print axioms Lean4Lean.VEnv.convStep2_of_piInvStrat
#print axioms Lean4Lean.VEnv.sortLinkInvUC_of_piInvStrat
#print axioms Lean4Lean.VEnv.piLinkInvUC_of_piInvStrat
end Audit

/-! ## §3 The exact price: an `iff` with one named extra coordinate -/

theorem sortPiDisjUC_of_shapeLinkAgree (H : ShapeLinkAgree env U) : SortPiDisjUC env U :=
  (shapeLinkAgree_iff.1 H).2.2

theorem shapeLinkAgree_of_piInvStrat (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (hd : SortPiDisjUC env U) : ShapeLinkAgree env U :=
  shapeLinkAgree_iff.2 ⟨sortLinkInvUC_of_piInvStrat henv hstrat,
    piLinkInvUC_of_piInvStrat henv hstrat, hd⟩

/-- **The price of hole A, exactly.** -/
theorem convStep2_shapeLinkAgree_iff (henv : VEnv.WF env) :
    (ConvStep2 env U ∧ ShapeLinkAgree env U) ↔ (PiInvStrat env U ∧ SortPiDisjUC env U) :=
  ⟨fun ⟨hcs, H⟩ => ⟨piInvStrat_of_shapeLinkAgree henv hcs H, sortPiDisjUC_of_shapeLinkAgree H⟩,
   fun ⟨hstrat, hd⟩ => ⟨convStep2_of_piInvStrat henv hstrat,
     shapeLinkAgree_of_piInvStrat henv hstrat hd⟩⟩

section Audit
#print axioms Lean4Lean.VEnv.shapeLinkAgree_of_piInvStrat
#print axioms Lean4Lean.VEnv.convStep2_shapeLinkAgree_iff
end Audit

/-! ## §4 Negative control: the hypothesis is refutable at an `Ordered` environment -/

/-- A second δ-rule for `InjPiRogue.rogueC`, this time to a **sort**. -/
def rogueDfSort : VDefEq := ⟨0, .const rogueC [], .sort .zero, .sort (.succ .zero)⟩

/-- `rogueC : Sort 1` with two δ-rules: `rogueC ≡ ∀ (_ : Prop), Prop` and `rogueC ≡ Prop`. -/
def sortPiEnv : VEnv := (rogueEnv1.addDefEq rogueDf1).addDefEq rogueDfSort

theorem ordered_sortPiEnv : Ordered sortPiEnv :=
  .defeq (.defeq ordered_rogueEnv1 ⟨rogueC_type rogueEnv1_constants, roguePi1_type⟩)
    ⟨rogueC_type rogueEnv1_constants, roguePropType⟩

theorem sortPiEnv_defeqs1 : sortPiEnv.defeqs rogueDf1 := by
  simp [sortPiEnv, VEnv.addDefEq, rogueEnv1]

theorem sortPiEnv_defeqsS : sortPiEnv.defeqs rogueDfSort := by
  simp [sortPiEnv, VEnv.addDefEq, rogueEnv1]

theorem sortPi_link :
    sortPiEnv.IsDefEqStrong 0 [] (.sort .zero) roguePi1 (.sort (.succ .zero)) := by
  have h1 := IsDefEq.extra (env := sortPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rogueDfSort) sortPiEnv_defeqsS (by simp) rfl
  have h2 := IsDefEq.extra (env := sortPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rogueDf1) sortPiEnv_defeqs1 (by simp) rfl
  simp [rogueDfSort, rogueDf1, roguePi1, VExpr.instL, VLevel.inst] at h1 h2
  exact (h1.symm.trans h2).strong ordered_sortPiEnv trivial

/-- **The negative control.**  `ShapeLinkAgree` is *false* at an `Ordered` environment, so §1 is
not a tautology of the definitions and `VEnv.WF` is load-bearing in it. -/
theorem not_shapeLinkAgree_sortPiEnv : ¬ ShapeLinkAgree sortPiEnv 0 := fun H =>
  H (Γ := []) (s₁ := .sort .zero) (s₂ := .pi (.sort .zero) (.sort .zero)) trivial sortPi_link

/-- The same for the sort/Π coordinate on its own. -/
theorem not_sortPiDisjUC_sortPiEnv : ¬ SortPiDisjUC sortPiEnv 0 := fun H =>
  H (Γ := []) trivial sortPi_link

section Audit
#print axioms Lean4Lean.VEnv.ordered_sortPiEnv
#print axioms Lean4Lean.VEnv.sortPi_link
#print axioms Lean4Lean.VEnv.not_shapeLinkAgree_sortPiEnv
#print axioms Lean4Lean.VEnv.not_sortPiDisjUC_sortPiEnv
end Audit

/-! ## §5 The control is a control, not a refutation: `sortPiEnv` is not `VEnv.WF` -/

theorem sortPi_rules_share_lhs : rogueDf1.lhs = rogueDfSort.lhs ∧ rogueDf1 ≠ rogueDfSort := by
  refine ⟨rfl, fun h => ?_⟩
  simp [rogueDf1, rogueDfSort, roguePi1] at h

theorem not_defEqHeadsUnique_sortPiEnv : ¬ sortPiEnv.DefEqHeadsUnique := fun H =>
  sortPi_rules_share_lhs.2
    (H _ _ rogueC sortPiEnv_defeqs1 sortPiEnv_defeqsS ⟨[], rfl⟩ ⟨[], rfl⟩)

/-- So §4 refutes the hypothesis only *off* `VEnv.WF`, exactly as `InjPiRogue.lean`'s
`not_wf_roguePiEnv` does for its own witness.  Nothing here refutes the corner. -/
theorem not_wf_sortPiEnv : ¬ VEnv.WF sortPiEnv :=
  fun h => not_defEqHeadsUnique_sortPiEnv h.defEqHeadsUnique

/-! ## §6 The substitution, in the sorry's own shape -/

/-- `IsDefEqU.forallE_inv_stratified`'s statement verbatim, with the two hypotheses of §1. -/
theorem IsDefEqU.forallE_inv_stratified_of_shapeLinkAgree {Γ : List VExpr}
    {A B A' B' V V' : VExpr} {n n' : Nat} (henv : VEnv.WF env) (hcs : ConvStep2 env U) (Hs : ShapeLinkAgree env U)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' :=
  piInvStrat_of_shapeLinkAgree henv hcs Hs hΓ h1 h2 h3

section Audit
#print axioms Lean4Lean.VEnv.not_defEqHeadsUnique_sortPiEnv
#print axioms Lean4Lean.VEnv.not_wf_sortPiEnv
#print axioms Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified_of_shapeLinkAgree
end Audit

/-! ## §7 Anti-vacuity, in the `∃` form `docs/vacuity-ledger.md` §0 asks for -/

/-- **The hypothesis of §1 is inhabited exactly when hole A is** (together with single-link
sort/Π disjointness).  This is the strongest inhabitation statement available for a hypothesis
that is an *equivalent* of an open target: it cannot be vacuous unless hole A itself is
unsatisfiable over well-formed environments.  It is a corollary of §3 and carries no new
content; the point is that it is stated in the `∃` form rather than argued. -/
theorem hyp_inhabited_iff :
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ ConvStep2 env U ∧ ShapeLinkAgree env U) ↔
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ PiInvStrat env U ∧ SortPiDisjUC env U) := by
  constructor
  · rintro ⟨env, U, henv, h⟩; exact ⟨env, U, henv, (convStep2_shapeLinkAgree_iff henv).1 h⟩
  · rintro ⟨env, U, henv, h⟩; exact ⟨env, U, henv, (convStep2_shapeLinkAgree_iff henv).2 h⟩

section Audit
#print axioms Lean4Lean.VEnv.hyp_inhabited_iff
end Audit

/-! ## §8 The two forms that are actionable -/

/-- The same price with the residual `SortInvIndep.lean` leaves, given the independent source. -/
theorem convStep2_shapeMidShapeless_iff (henv : VEnv.WF env) (hT : PropAgreeOn env U) :
    (ConvStep2 env U ∧ ShapeMidShapeless env U) ↔ (PiInvStrat env U ∧ SortPiDisjUC env U) := by
  have h := shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn henv hT
  rw [← convStep2_shapeLinkAgree_iff henv, h]

/-- **Both holes of the injectivity corner, from one hypothesis set — and hole A needs a strict
subset of it.**  `PiInvStrat` is hole A (`IsDefEqU.forallE_inv_stratified`); `RigidShapeUniqNS`
is hole B (`VEnv.WF.rigidShapeUniqNS`).  The three `RigidConst*` conjuncts are consumed by hole
B only, so *anyone who closes hole B by `PiInvResidual.rigidShapeUniqNS_of_constSpine` closes
hole A for free*. -/
theorem piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree (henv : VEnv.WF env)
    (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) (hca : env.RigidConstAppInv U)
    (hcp : env.RigidConstPiDisj U) (hcsd : env.RigidConstSortDisj U) :
    PiInvStrat env U ∧ env.RigidShapeUniqNS U :=
  ⟨piInvStrat_of_shapeLinkAgree henv hcs H,
   rigidShapeUniqNS_of_constSpine henv hcs H hca hcp hcsd⟩

section Audit
#print axioms Lean4Lean.VEnv.convStep2_shapeMidShapeless_iff
#print axioms Lean4Lean.VEnv.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree
end Audit

end VEnv
end Lean4Lean
