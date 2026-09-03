import Lean4Lean.Theory.Typing.ForallInvPrice

/-!
# The one open coordinate of `ForallInvPrice`: `PiInvStrat → SortPiDisjUC`

`Theory/Typing/ForallInvPrice.lean` prices hole A (`IsDefEqU.forallE_inv_stratified`,
`Injectivity.lean:261`) as, over `VEnv.WF`,

    ConvStep2 ∧ ShapeLinkAgree   ↔   PiInvStrat ∧ SortPiDisjUC

and names one coordinate as open: **`PiInvStrat → SortPiDisjUC`**, which would collapse the
right-hand side to hole A alone.  This file measures that coordinate.  It is neither proved nor
refuted here either; what is new is *where it sits*, and both bounds are theorems.

## §1 The coordinate **is** hole B (`WF.rigidShapeUniqNS`), exactly

Over `VEnv.WF env` and hole A:

* `sortPiDisjUC_of_rigidShapeUniqNS` — hole B gives the coordinate, with **no** further input;
* `rigidShapeUniqNS_of_sortPiDisjUC` — the coordinate gives hole B back, modulo the three
  constant-spine conjuncts that `ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree`
  already carries;
* `sortPiDisjUC_iff_rigidShapeUniqNS` — hence an `iff`.

Two consequences, both stated as theorems rather than as advice:

* **Proving the coordinate proves hole B** (given hole A and the three constant conjuncts).  So
  the coordinate is not a loose end of hole A's pricing; it is the *live* conjunct of the other
  standing hole of the corner (`RigidNodeCircle.rigidShapeUniqNS_iff_family`'s conjunct 2).
* **Refuting the coordinate refutes hole B** (`refutation_refutes_rigidShapeUniqNS`), and hole B
  is asserted at `Injectivity.lean:1046` as `WF.rigidShapeUniqNS`, a `sorry` over *every*
  well-formed environment.  So outcome "refute" is not a cheap settlement: it makes that `sorry`
  unfillable.  This is the precise form of `docs/vacuity-ledger.md` row 41's blockage — the route
  through `sort_forallE_inv` eats hole B not by accident of that proof, but because the coordinate
  *is* hole B's sort/Π conjunct.

## §2 Which constructor of `IsDefEqStrong` carries it: `trans`, and nothing else

`SortPiMid` is the sort/Π `trans` residual — a shapeless midpoint between a sort and a Π.
`sortPiDisjUC_of_sortPiMid` proves the coordinate from `VEnv.WF`, hole A and `SortPiMid` alone,
by a class-level induction (`sortClass_of_wf`) that is `InjOneFact.shapeAgree_of_wf` with
`SPShape.Agree` weakened to *shape class*.  Two things fall out of the weakening:

* the induction needs **no** `Ordered` and **no** `ConvC.defeqDFC` — `symm`/`trans` are `Iff.symm`
  and `Iff.trans`;
* the `proofIrrel` residual is **discharged by hole A**: `shapeNotProofC_of_sortUniq` proves
  `SortInvIndep.ShapeNotProofC` from `VEnv.SortUniq`, and `Injectivity.sortUniq_of_piInvStrat`
  supplies `SortUniq` from hole A.  `InjOneFact.lean` §9 calls `ShapeNotProof` "genuinely the
  stratification" residual and records it as reachable only through `WF.sortUniq'` (i.e. through
  the hole); *relative to hole A as a hypothesis* it is free, and that is a strictly weaker claim
  than "it is free", stated that way on purpose.

**Credit where it is due, and it bounds the novelty of §2.**  `IsDefEqU.sort_forallE_inv`'s own
docstring (`Injectivity.lean:1240-1245`) already records the same two residuals for the same
statement one level up (at `IsDefEqU`): `trans`, "discharged by `VEnv.WF.rigidShapeUniq`", and
`proofIrrel`, "`VEnv.sort_not_proof` given `VEnv.SortUniq`".  What is new here is (i) that the
`trans` discharge is not merely *a* route through hole B but is equivalent to it (§1), (ii) the
`ShapeNotProofC`-interface form of the `proofIrrel` discharge, which is `sorryAx`-free and
parametric in `SortUniq` where `not_isProof_of_defeqU_sort` routes through `WF.sortUniq'`, and
(iii) the class-level induction, which drops `Ordered` and `ConvC.defeqDFC` entirely.

`sortPiMid_of_sortPiDisjUC` is the converse — one `trans` — so `SortPiMid` is **equivalent** to
the coordinate, not weaker than it.  That is recorded as the negative it is (the discipline of
`PiInvResidual.lean` §5): §2 is a *localisation*, naming the single constructor that carries the
coordinate, not a reduction of it.

## §3 The confluence request the coordinate needs is weaker than the corner's

`SortPiCR` is `InjOneFact.ShapeCR` with the `normal` clause weakened from "a shape's reducts are
shapes that *agree*" to "a sort's reducts are sorts and a Π's reducts are Π's" — no domain chain,
no codomain chain, no level relation.  `sortPiDisjUC_of_sortPiCR` gets the coordinate from it, and
`ShapeCR.sortPiCR` shows it is implied by the corner's own request, so this is a genuine weakening.

## §4 Outcome "refute", measured

A refutation needs a `VEnv.WF` environment.  Such environments **are** constructible in this tree
— `wf_witness_exists` below is one line over `InjPiRogue.wf_wfPiEnv`, and
`WeakNProjGate.exists_typingStrengthening_env` is another — so the obstruction to a refutation is
*not* witness availability.  It is §1: any such witness refutes hole B.

## §5 Negative controls

* `not_sortPiMid_sortPiEnv`: `SortPiMid` is **false** at `ForallInvPrice.sortPiEnv`, and the
  refuting midpoint is a genuine shapeless one (`.const rogueC []`), so §2's hypothesis has content
  and is not an artefact of the midpoint condition.
* `not_wf_sortPiEnv` (`ForallInvPrice` §5) proves that environment is not `VEnv.WF`, so the control
  is a control and **not** a refutation of the coordinate.
* `sortPi_premises_fire`: the premise class of `SortPiDisjUC` is non-empty at the degenerate
  instance `Γ = []` (at that same non-`WF` environment), which is the check
  `docs/vacuity-ledger.md` §0's seventh blindness asks for.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The coordinate is hole B -/

/-- **Hole B gives the coordinate.**  No constant-spine conjunct, no `ProofTransport`: hole A is
used only for the `SortUniq` that `RigidShapeUniqNS.sortPiDisj` needs to know a sort is not a
proof. -/
theorem sortPiDisjUC_of_rigidShapeUniqNS (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (h : env.RigidShapeUniqNS U) : SortPiDisjUC env U :=
  RigidSortPiDisj.sortPiDisjUC
    (h.sortPiDisj (sortUniq_of_piInvStrat henv hstrat) henv.ordered)

/-- **The coordinate gives hole B back**, modulo exactly the three constant-spine conjuncts that
`ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` already carries. -/
theorem rigidShapeUniqNS_of_sortPiDisjUC (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (hd : SortPiDisjUC env U) (hca : env.RigidConstAppInv U) (hcp : env.RigidConstPiDisj U)
    (hcsd : env.RigidConstSortDisj U) : env.RigidShapeUniqNS U :=
  rigidShapeUniqNS_of_constSpine henv (convStep2_of_piInvStrat henv hstrat)
    (shapeLinkAgree_of_piInvStrat henv hstrat hd) hca hcp hcsd

/-- **The measurement.**  Over `VEnv.WF`, hole A and the three constant-spine conjuncts, the open
coordinate of `ForallInvPrice` §3 is *equivalent* to hole B. -/
theorem sortPiDisjUC_iff_rigidShapeUniqNS (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (hca : env.RigidConstAppInv U) (hcp : env.RigidConstPiDisj U)
    (hcsd : env.RigidConstSortDisj U) :
    SortPiDisjUC env U ↔ env.RigidShapeUniqNS U :=
  ⟨fun hd => rigidShapeUniqNS_of_sortPiDisjUC henv hstrat hd hca hcp hcsd,
   sortPiDisjUC_of_rigidShapeUniqNS henv hstrat⟩

/-- **What a refutation would cost.**  A `VEnv.WF` environment satisfying hole A and refuting the
coordinate refutes `Injectivity.WF.rigidShapeUniqNS` — the corner's other standing `sorry`, stated
there for every well-formed environment.  The three constant-spine conjuncts are *not* needed for
this direction. -/
theorem refutation_refutes_rigidShapeUniqNS (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (hd : ¬ SortPiDisjUC env U) : ¬ env.RigidShapeUniqNS U :=
  fun h => hd (sortPiDisjUC_of_rigidShapeUniqNS henv hstrat h)

/-- **Anti-vacuity in the only form available for an equivalent of an open target**
(`ForallInvPrice.hyp_inhabited_iff`'s discipline): the hypothesis set of §1 is inhabited exactly
when hole B's is. -/
theorem sortPiDisjUC_inhabited_iff :
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ PiInvStrat env U ∧ env.RigidConstAppInv U ∧
      env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U ∧ SortPiDisjUC env U) ↔
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ PiInvStrat env U ∧ env.RigidConstAppInv U ∧
      env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U ∧ env.RigidShapeUniqNS U) := by
  constructor
  · rintro ⟨env, U, henv, hs, hca, hcp, hcsd, hd⟩
    exact ⟨env, U, henv, hs, hca, hcp, hcsd,
      rigidShapeUniqNS_of_sortPiDisjUC henv hs hd hca hcp hcsd⟩
  · rintro ⟨env, U, henv, hs, hca, hcp, hcsd, h⟩
    exact ⟨env, U, henv, hs, hca, hcp, hcsd, sortPiDisjUC_of_rigidShapeUniqNS henv hs h⟩

section Audit
#print axioms Lean4Lean.VEnv.sortPiDisjUC_of_rigidShapeUniqNS
#print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_sortPiDisjUC
#print axioms Lean4Lean.VEnv.sortPiDisjUC_iff_rigidShapeUniqNS
#print axioms Lean4Lean.VEnv.refutation_refutes_rigidShapeUniqNS
#print axioms Lean4Lean.VEnv.sortPiDisjUC_inhabited_iff
end Audit

/-! ## §2 Which constructor carries the coordinate -/

/-- The **shape class**: `SPShape.Agree` with everything but "sort or Π" forgotten.  It is an
equivalence on classes, which is why the induction below needs no `Ordered` and no
`ConvC.defeqDFC`. -/
def SPShape.SortClass : SPShape → Prop
  | .sort _ => True
  | .pi _ _ => False

/-- **The sort/Π `trans` residual**: the sort/Π slice of `InjOneFact.ShapeMidShapeless`, with the
conclusion weakened from `SPShape.Agree` to `False` (the two classes differ, so `Agree` *is*
`False` at this slice — the weakening is in the other entries, which are dropped). -/
def SortPiMid (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a : VLevel} {A B M T : VExpr}, CtxStrong env U Γ →
    (∀ c, M ≠ .sort c) → (∀ D E, M ≠ .forallE D E) →
    env.IsDefEqStrong U Γ (.sort a) M T → env.IsDefEqStrong U Γ M (.forallE A B) T → False

/-- The slice is implied by the corner's own `trans` residual. -/
theorem ShapeMidShapeless.sortPiMid (H : ShapeMidShapeless env U) : SortPiMid env U :=
  fun hΓ h1 h2 hl hr => H (s₁ := .sort _) (s₂ := .pi _ _) hΓ h1 h2 hl hr

/-- **The `proofIrrel` residual of the sort/Π corner, from `VEnv.SortUniq`.**  `SortInvIndep.lean`
§2 proves the same `ShapeNotProofC` from the *independent* source `PropAgreeOn`; this is the same
statement from universe uniqueness, which `Injectivity.sortUniq_of_piInvStrat` supplies from hole
A.  So, **relative to hole A as a hypothesis**, the residual `InjOneFact.lean` §9 calls "genuinely
the stratification" is free.  That is weaker than "it is free": `WF.sortUniq'` reaches `SortUniq`
only through the hole. -/
theorem shapeNotProofC_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U) :
    ShapeNotProofC env U := by
  intro Γ s p hΓ h1 h2
  cases s with
  | sort a => exact sort_not_proof hsu hord hΓ.defeq h1.defeq.hasType.1 h2.defeq.hasType.1
  | pi A B => exact forallE_not_proof hsu hord hΓ.defeq h1.defeq.hasType.1 h2.defeq.hasType.1

/-- The shapeless-midpoint step, at the class level and in both orders. -/
theorem SortPiMid.class_of_links (hm : SortPiMid env U) {Γ : List VExpr} {M A : VExpr}
    (hΓ : CtxStrong env U Γ) (h1 : ∀ c, M ≠ .sort c) (h2 : ∀ D E, M ≠ .forallE D E)
    {s₁ s₂ : SPShape} (hl : env.IsDefEqStrong U Γ s₁.toExpr M A)
    (hr : env.IsDefEqStrong U Γ M s₂.toExpr A) : (s₁.SortClass ↔ s₂.SortClass) := by
  match s₁, s₂ with
  | .sort _, .sort _ => exact Iff.rfl
  | .pi _ _, .pi _ _ => exact Iff.rfl
  | .sort _, .pi _ _ => exact (hm hΓ h1 h2 hl hr).elim
  | .pi _ _, .sort _ => exact (hm hΓ h1 h2 hr.symm hl.symm).elim

/-- **`InjOneFact.shapeAgree_of_wf` at the class level.**  Same thirteen constructors, same two
residuals — but the conclusion is an `Iff` of classes, so `symm` and `trans` are `Iff.symm` and
`Iff.trans`, and `Ordered env` is not used anywhere.  `VEnv.WF` survives in exactly one case,
`extra`. -/
theorem sortClass_of_wf (henv : VEnv.WF env) (hm : SortPiMid env U) (hp : ShapeNotProofC env U)
    {Γ : List VExpr} {e1 e2 A : VExpr} (h : env.IsDefEqStrong U Γ e1 e2 A) :
    CtxStrong env U Γ → ∀ (s₁ s₂ : SPShape), e1 = s₁.toExpr → e2 = s₂.toExpr →
      (s₁.SortClass ↔ s₂.SortClass) := by
  induction h with
  | bvar _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | constDF _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | appDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | lamDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | beta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | eta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | sortDF _ _ _ =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact Iff.rfl
  | forallEDF _ _ _ _ _ =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact Iff.rfl
  | symm _ ih => exact fun hΓ s₁ s₂ e1 e2 => (ih hΓ s₂ s₁ e2 e1).symm
  | defeqDF _ _ _ _ ih2 => exact ih2
  | @trans _ _ M _ _ hl hr ihl ihr =>
    intro hΓ s₁ s₂ e1 e2
    subst e1; subst e2
    match M, hl, hr, ihl, ihr with
    | .sort c, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.sort c) rfl rfl).trans (ihr hΓ (.sort c) s₂ rfl rfl)
    | .forallE D E, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.pi D E) rfl rfl).trans (ihr hΓ (.pi D E) s₂ rfl rfl)
    | .bvar _, hl, hr, _, _ => exact hm.class_of_links hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .const _ _, hl, hr, _, _ =>
      exact hm.class_of_links hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .app _ _, hl, hr, _, _ =>
      exact hm.class_of_links hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .lam _ _, hl, hr, _, _ =>
      exact hm.class_of_links hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
  | proofIrrel h1 h2 _ _ _ _ =>
    intro hΓ s₁ _ e1 _; subst e1; exact (hp hΓ h1 h2).elim
  | extra h1 _ _ _ _ _ _ _ _ =>
    intro _ s₁ _ e1 _
    cases s₁
    · exact (henv.instL_lhs_ne_sort h1 _ _ e1).elim
    · exact (henv.instL_lhs_ne_forallE h1 _ _ _ e1).elim

/-- **The coordinate from `VEnv.WF`, hole A, and the `trans` residual alone.** -/
theorem sortPiDisjUC_of_sortPiMid (henv : VEnv.WF env) (hstrat : PiInvStrat env U)
    (hm : SortPiMid env U) : SortPiDisjUC env U := by
  intro Γ a A B T hΓ h
  exact (sortClass_of_wf henv hm
    (shapeNotProofC_of_sortUniq henv.ordered (sortUniq_of_piInvStrat henv hstrat)) h hΓ
    (.sort a) (.pi A B) rfl rfl).1 trivial

/-- **…and the converse, in one `trans`.**  So §2 is a *localisation*, not a reduction: the
residual is equivalent to the target, exactly as `InjOneFact.lean` §5 finds for the wide statement.
What it localises is which constructor of `IsDefEqStrong` carries the coordinate — `trans`, since
every other case above is discharged outright or by hole A. -/
theorem sortPiMid_of_sortPiDisjUC (H : SortPiDisjUC env U) : SortPiMid env U :=
  fun hΓ _ _ hl hr => H hΓ (hl.trans hr)

/-- The equivalence, stated so nobody quotes §2 as a reduction. -/
theorem sortPiMid_iff (henv : VEnv.WF env) (hstrat : PiInvStrat env U) :
    SortPiMid env U ↔ SortPiDisjUC env U :=
  ⟨sortPiDisjUC_of_sortPiMid henv hstrat, sortPiMid_of_sortPiDisjUC⟩

section Audit
#print axioms Lean4Lean.VEnv.shapeNotProofC_of_sortUniq
#print axioms Lean4Lean.VEnv.sortClass_of_wf
#print axioms Lean4Lean.VEnv.sortPiDisjUC_of_sortPiMid
#print axioms Lean4Lean.VEnv.sortPiMid_iff
end Audit

/-! ## §3 The confluence request this coordinate needs, weakened -/

/-- **`InjOneFact.ShapeCR` with the `normal` clause weakened to shape *class*.**  `join` is
unchanged (Church–Rosser for every conversion); what is dropped is the requirement that a shape's
reducts *agree* with it — no domain chain, no codomain chain, no level relation.  This is all the
sort/Π coordinate needs. -/
structure SortPiCR (env : VEnv) (U : Nat) (Red : List VExpr → VExpr → VExpr → Prop) : Prop where
  join : ∀ {Γ : List VExpr} {e1 e2 A : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ e1 e2 A → ∃ M, Red Γ e1 M ∧ Red Γ e2 M
  sortNormal : ∀ {Γ : List VExpr} {a : VLevel} {M : VExpr}, CtxStrong env U Γ →
    Red Γ (.sort a) M → ∃ b, M = .sort b
  piNormal : ∀ {Γ : List VExpr} {A B M : VExpr}, CtxStrong env U Γ →
    Red Γ (.forallE A B) M → ∃ D E, M = .forallE D E

/-- **The coordinate from the weakened request**, with no `VEnv.WF`, no hole A and no induction. -/
theorem sortPiDisjUC_of_sortPiCR {Red : List VExpr → VExpr → VExpr → Prop}
    (H : SortPiCR env U Red) : SortPiDisjUC env U := by
  intro Γ a A B T hΓ h
  obtain ⟨M, h1, h2⟩ := H.join hΓ h
  obtain ⟨b, rfl⟩ := H.sortNormal hΓ h1
  obtain ⟨D, E, hE⟩ := H.piNormal hΓ h2
  cases hE

/-- The corner's own request implies it, so §3 really is a weakening. -/
theorem ShapeCR.sortPiCR {Red : List VExpr → VExpr → VExpr → Prop} (H : ShapeCR env U Red) :
    SortPiCR env U Red where
  join := H.join
  sortNormal := by
    intro Γ a M hΓ hr
    obtain ⟨s, rfl, ha⟩ := H.normal (s := .sort a) hΓ hr
    cases s with
    | sort b => exact ⟨b, rfl⟩
    | pi _ _ => exact ha.elim
  piNormal := by
    intro Γ A B M hΓ hr
    obtain ⟨s, rfl, ha⟩ := H.normal (s := .pi A B) hΓ hr
    cases s with
    | sort _ => exact ha.elim
    | pi D E => exact ⟨D, E, rfl⟩

/-- **Control: `Red := Eq` fails `join`.**  `InjOneFact.shapeCR_eq_join_fails`'s witness, so the
`join` clause of §3 has content and the request is not satisfied by the identity. -/
theorem not_sortPiCR_eq : ¬ SortPiCR (∅ : VEnv) 0 (fun _ a b => a = b) := by
  intro H
  obtain ⟨M, e1, e2⟩ := H.join (Γ := []) trivial shapeCR_eq_join_fails.1
  exact shapeCR_eq_join_fails.2 (e1.trans e2.symm)

/-- **Control: conversion itself fails `sortNormal`.**  `InjOneFact.shapeCR_conv_normal_fails`'s
β-redex again: at `∅`, `Sort 0` converts to a term that is not a sort.  So the weakened `normal`
clause is still genuinely about a *reduction* relation and cannot be met at the conversion
level. -/
theorem not_sortPiCR_conv :
    ¬ SortPiCR (∅ : VEnv) 0 (fun Γ a b => ∃ T, (∅ : VEnv).IsDefEqStrong 0 Γ a b T) := by
  intro H
  obtain ⟨b, hb⟩ := H.sortNormal (Γ := []) trivial ⟨_, shapeCR_conv_normal_fails.1.symm⟩
  exact shapeCR_conv_normal_fails.2 (.sort b) hb

section Audit
#print axioms Lean4Lean.VEnv.sortPiDisjUC_of_sortPiCR
#print axioms Lean4Lean.VEnv.ShapeCR.sortPiCR
#print axioms Lean4Lean.VEnv.not_sortPiCR_eq
#print axioms Lean4Lean.VEnv.not_sortPiCR_conv
end Audit

/-! ## §4 `VEnv.WF` witnesses exist, so a refutation is not blocked on witness availability -/

/-- **A hole-free `VEnv.WF` environment**, one line over `InjPiRogue.wf_wfPiEnv` — an environment
with a constant `rogueC : Sort 1` and the single δ-rule `rogueC ≡ ∀ (_ : Prop), Prop`.
`WeakNProjGate.exists_typingStrengthening_env` is a second, independent one.  So "no `VEnv.WF`
witness can be built in this tree" is **false**, and the obstruction to refuting the coordinate is
§1 — a refutation refutes hole B — not the availability of environments. -/
theorem wf_witness_exists : ∃ env : VEnv, VEnv.WF env := ⟨wfPiEnv, wf_wfPiEnv⟩

/-! ## §5 Negative controls -/

/-- The two δ-rule links of `ForallInvPrice.sortPiEnv`, separated: `Sort 0 ≡ rogueC` and
`rogueC ≡ ∀ (_ : Prop), Prop`, both at the type `Sort 1`.  The midpoint `.const rogueC []` is
**shapeless** — neither a sort nor a Π syntactically — which is what makes the next theorem a
control on `SortPiMid` rather than on the target. -/
theorem sortPi_links :
    sortPiEnv.IsDefEqStrong 0 [] (.sort .zero) (.const rogueC []) (.sort (.succ .zero)) ∧
    sortPiEnv.IsDefEqStrong 0 [] (.const rogueC []) roguePi1 (.sort (.succ .zero)) := by
  have h1 := IsDefEq.extra (env := sortPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rogueDfSort) sortPiEnv_defeqsS (by simp) rfl
  have h2 := IsDefEq.extra (env := sortPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rogueDf1) sortPiEnv_defeqs1 (by simp) rfl
  simp [rogueDfSort, rogueDf1, roguePi1, VExpr.instL, VLevel.inst] at h1 h2
  exact ⟨(h1.symm.strong ordered_sortPiEnv trivial), (h2.strong ordered_sortPiEnv trivial)⟩

/-- **The control for §2.**  `SortPiMid` is false at an `Ordered` environment, at a genuinely
shapeless midpoint — so the hypothesis of `sortPiDisjUC_of_sortPiMid` is not an artefact of its
midpoint side conditions, and `VEnv.WF` is load-bearing there. -/
theorem not_sortPiMid_sortPiEnv : ¬ SortPiMid sortPiEnv 0 := fun H =>
  H (Γ := []) (M := .const rogueC []) trivial (by rintro c ⟨⟩) (by rintro D E ⟨⟩)
    sortPi_links.1 sortPi_links.2

/-- **The control is a control.**  `ForallInvPrice.not_wf_sortPiEnv` — two δ-rules share an lhs —
so §5 refutes the hypothesis only *off* `VEnv.WF` and nothing here refutes the coordinate. -/
theorem control_is_control : ¬ VEnv.WF sortPiEnv := not_wf_sortPiEnv

/-- **The degenerate-instance check** (`docs/vacuity-ledger.md` §0, blindness seven): the premise
class of `SortPiDisjUC` is non-empty at `Γ = []`, so the statement is not true-because-empty at the
instance everything else in this corner is tested at.  At a `VEnv.WF` environment it had better be
empty — that is what the coordinate says — which is why this control is run at `sortPiEnv`. -/
theorem sortPi_premises_fire :
    CtxStrong sortPiEnv 0 [] ∧
    sortPiEnv.IsDefEqStrong 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero))
      (.sort (.succ .zero)) :=
  ⟨trivial, sortPi_link⟩

section Audit
#print axioms Lean4Lean.VEnv.wf_witness_exists
#print axioms Lean4Lean.VEnv.sortPi_links
#print axioms Lean4Lean.VEnv.not_sortPiMid_sortPiEnv
#print axioms Lean4Lean.VEnv.sortPi_premises_fire
end Audit

end VEnv
end Lean4Lean
