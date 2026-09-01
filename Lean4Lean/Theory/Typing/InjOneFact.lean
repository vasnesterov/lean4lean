import Lean4Lean.Theory.Typing.InjPiRogue

/-!
# The one fact, stated once — and the β-redex that refutes its "residual" form

`docs/handoff-injectivity.md` §4H.6 prices the injectivity corner's three residuals
(`SortMidNonSort`, `PiMidNonPi`, `RigidSortPiDisj`) as **three instances of one fact**: a κ-normal
rigid head has no reduct of another shape.  This file does two things.

**1. It states the one fact once** (`ShapeLinkAgree`) and machine-checks that the single statement
is *exactly* the conjunction of the three consumers (`shapeLinkAgree_iff`), so "one prerequisite,
three consumers" is a theorem here and not a reading.  One induction over `IsDefEqStrong`
(`shapeAgree_of_wf`) closes eleven of the thirteen constructors at `VEnv.WF`, leaving `trans` and
`proofIrrel` — the same two the sort side left, now shared by all three consumers.

**2. It refutes the claim that the `trans` residual is a genuine localisation.**
§4H.5 says of `SortMidNonSort` that "target → residual is free and **the converse has no route**,
because a single link offers no non-sort midpoint", and row 86 of `docs/vacuity-ledger.md` and
`docs/critical-path.md`'s "The convergence" repeat it.  **That is false.**  A single link offers a
non-sort midpoint, and β manufactures it: for any `X` with `Γ ⊢ X : A`,

    betaMid X = (fun (_ : Type 0) => X) Prop

is `.app`-headed — so neither a sort nor a Π — and `Γ ⊢ betaMid X ≡ X : A` by one `beta`
(`betaMid_link`).  Hence `SortMidNonSort` implies `SortLinkInv` (`sortLinkInv_of_sortMidNonSort`),
`PiMidNonPi` implies `PiLinkInvCod` (`piLinkInvCod_of_piMidNonPi`), and the unified residual
implies the unified target (`shapeLinkAgree_of_shapeMidShapeless`) — all over `Ordered env` alone,
which `VEnv.WF` supplies.  So these are **collapse six and collapse seven**, not reductions, and
the same argument shows **no syntactic condition on the midpoint can ever localise a `trans` node**
(`midShapeless_restriction_vacuous`): β produces a midpoint satisfying every shape-based side
condition at once.

§4H.8 item 5 already contains the mechanism — "the costly midpoint heads are reached by **β
alone**" — so the two claims contradict each other inside one document.  The `[analysis]`-flagged
half won.

**Where that puts the CR boundary.**  §4H.7 advertises `PiMidNonPi` as a request with "no reduction
relation, no subject, no typing judgement and no level arithmetic".  That is precisely why it is
worthless: a purely conversion-level statement cannot tell a manufactured β-midpoint from a genuine
one, so it is equivalent to its own target.  What CR must supply therefore *has* to mention a
reduction relation (or a normal-form predicate).  `ShapeCR` below is that request, parametric in
the relation, and `shapeLinkAgree_of_shapeCR` discharges the whole target from it.  Nothing here
claims `ShapeCR` is satisfiable; that is the confluence layer's `PatMajorCanonical` question.

**Not used anywhere:** `IsDefEqU.sort_forallE_inv`, `rigidShapeUniqNS`, `forallE_inv_stratified`,
`weakN_iff`, `NormalEq.descend`, `Injectivity.not_isProof_of_defeqU_sort`.  `ShapeNotProof` is a
named residual, cited to `Injectivity.not_isProof_of_defeqU_sort` and deliberately not imported:
that route proves it from `WF.sortUniq'`, i.e. from the statement being reduced.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The manufactured midpoint

`appMid` (`InjPiRogue.lean` §13) is this construction at one fixed term over `∅`.  Here it is a
function of the term, over an arbitrary environment and context, which is what turns it from a
remark about midpoints into a refutation of the midpoint localisations. -/

/-- `(fun (_ : Type 0) => X) Prop` — a β-redex whose value is `X`, and whose head is an
application, so it is neither a sort nor a Π whatever `X` is. -/
def betaMid (X : VExpr) : VExpr :=
  .app (.lam (.sort (.succ .zero)) X.lift) (.sort .zero)

theorem betaMid_ne_sort (X : VExpr) : ∀ c, betaMid X ≠ .sort c := by rintro c ⟨⟩

theorem betaMid_ne_forallE (X : VExpr) : ∀ D E, betaMid X ≠ .forallE D E := by rintro D E ⟨⟩

theorem betaMid_isApp (X : VExpr) : ∃ f a, betaMid X = .app f a := ⟨_, _, rfl⟩

/-- **The one link every well-typed term has to a shapeless midpoint.**  No hypothesis on `X` and
none on `A` beyond `X`'s having that type: the domain `Type 0` is inhabited by `Prop` in every
context, so the redex always exists. -/
theorem betaMid_link {Γ : List VExpr} {X A : VExpr} (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U)) (hX : env.HasType U Γ X A) :
    env.IsDefEqStrong U Γ (betaMid X) X A := by
  have hp : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial rfl
  have hw : env.HasType U (.sort (.succ .zero) :: Γ) X.lift A.lift := hX.weakN henv .one
  have h := IsDefEq.beta (env := env) (uvars := U) (Γ := Γ) (A := .sort (.succ .zero))
    (B := A.lift) (e := X.lift) (e' := .sort .zero) hw hp
  rw [VExpr.inst_lift, VExpr.inst_lift] at h
  exact h.strong henv hΓ

/-! ## §2 The two published localisations, collapsed

Both are `iff`s once the free direction (already in `InjPiRogue.lean`) is put beside these. -/

/-- **Collapse six.**  §4H.5's "the converse has no route" is false: `SortMidNonSort` gives back
the very statement `sortLinkInv_of_wf` derives from it. -/
theorem sortLinkInv_of_sortMidNonSort (henv : Ordered env) (hm : SortMidNonSort env U) :
    SortLinkInv env U := by
  intro Γ u v w hΓ h
  have hb := betaMid_link henv hΓ.defeq (X := .sort u) h.hasType.1.defeq
  exact hm (betaMid_ne_sort _) hb.symm (hb.trans h)

/-- The index-free sort target: `SortLinkInvU` with the `OnCtx` hypothesis `SortLinkInvU` omits.
Every consumer supplies it (`CtxStrong.defeq` one way, `CtxStrong.strong` the other), and
`SortLinkInvU → SortLinkInvUC → SortLinkInv` are both free. -/
def SortLinkInvUC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a b : VLevel} {A : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.sort a) (.sort b) A → a ≈ b

theorem SortLinkInvU.sortLinkInvUC (H : SortLinkInvU env U) : SortLinkInvUC env U := fun _ h => H h

theorem SortLinkInvUC.sortLinkInv (H : SortLinkInvUC env U) : SortLinkInv env U := fun hΓ h => H hΓ h

/-- **Collapse six, at the index-free target** — the form §4H.5 says to measure against.  So
`SortMidNonSort` is equivalent to `SortLinkInvUC`, and `sortLinkInv_of_wf` derives its conclusion
from a hypothesis of exactly the same strength. -/
theorem sortLinkInvUC_of_sortMidNonSort (henv : Ordered env) (hm : SortMidNonSort env U) :
    SortLinkInvUC env U := by
  intro Γ a b A hΓ h
  have hb := betaMid_link henv hΓ.defeq (X := .sort a) h.hasType.1.defeq
  exact hm (betaMid_ne_sort _) hb.symm (hb.trans h)

/-- `SortMidNonSort` with the context hypothesis every consumer already has.  Stating the collapse
at this variant makes it an honest `iff`: `SortMidNonSort` itself omits `CtxStrong`, so the
backward direction cannot be stated for it, and the sandwich
`SortLinkInvU → SortMidNonSort → SortMidNonSortC ↔ SortLinkInvUC → SortLinkInv` is the whole
picture — every step free or `Ordered`-only, and the two ends differ by nothing but that
hypothesis. -/
def SortMidNonSortC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a b : VLevel} {M A : VExpr}, CtxStrong env U Γ → (∀ c, M ≠ .sort c) →
    env.IsDefEqStrong U Γ (.sort a) M A → env.IsDefEqStrong U Γ M (.sort b) A → a ≈ b

theorem SortMidNonSort.sortMidNonSortC (H : SortMidNonSort env U) : SortMidNonSortC env U :=
  fun _ hM h1 h2 => H hM h1 h2

/-- **The collapse test on `SortMidNonSort`, FAILING — both directions, `Ordered` only.** -/
theorem sortMidNonSortC_iff_sortLinkInvUC (henv : Ordered env) :
    SortMidNonSortC env U ↔ SortLinkInvUC env U := by
  refine ⟨fun H Γ a b A hΓ h => ?_, fun H Γ a b M A hΓ _ h1 h2 => H hΓ (h1.trans h2)⟩
  have hb := betaMid_link henv hΓ.defeq (X := .sort a) h.hasType.1.defeq
  exact H hΓ (betaMid_ne_sort _) hb.symm (hb.trans h)

/-- **Collapse seven.**  §4H.7's `PiMidNonPi`, the "request for the CR stream", gives back
`PiLinkInvCod` — the statement it was asked to supply.  Row 77c's "bounded above by the statement
it is asked to supply" is therefore an equivalence, not a bound. -/
theorem piLinkInvCod_of_piMidNonPi (henv : Ordered env) (hm : PiMidNonPi env U) :
    PiLinkInvCod env U := by
  intro Γ A B A' B' u hΓ h
  have hb := betaMid_link henv hΓ.defeq (X := .forallE A B) h.hasType.1.defeq
  exact hm hΓ (betaMid_ne_forallE _) hb.symm (hb.trans h)

/-- And the domain half too, from the same input — so `PiMidNonPi` is at least as strong as both
projections of the single-link statement, not just the codomain one. -/
theorem piLinkInvCod_iff_piMidNonPi (henv : Ordered env) :
    PiMidNonPi env U ↔ PiLinkInvCod env U :=
  ⟨piLinkInvCod_of_piMidNonPi henv, PiLinkInvCod.piMidNonPi⟩

/-- **The sort side's `iff`**, closing the loop with `SortLinkInvU.sortMidNonSort`. -/
theorem sortMidNonSort_of_sortLinkInvU (H : SortLinkInvU env U) : SortMidNonSort env U :=
  H.sortMidNonSort

/-! ## §3 The one fact, stated once

Two shapes, because the corner has three consumers and all three live in the sort/Π square: the
sort/sort diagonal (`ConvSortInv`'s residual), the Π/Π diagonal (`PiLinkInvCod` and
`PiLinkInvDom`), and the off-diagonal (`RigidSortPiDisj`).  The constant-spine shape of
`Injectivity.RigidShape` is deliberately absent: its entries carry a `RuleFreeHead` side condition
that an arbitrary midpoint cannot be given, and none of the three consumers needs it.

The conclusion is `ConvC`-valued rather than `IsDefEq`-valued for the reason `BaseUniqChain.lean`
gives: composing a chain into one link is exactly `ConvStep2`, so a chain conclusion keeps that
cost out of the statement. -/

/-- A sort or a Π — the two rigid shapes the corner's three consumers range over. -/
inductive SPShape where
  | sort (u : VLevel)
  | pi (A B : VExpr)

/-- The term a shape denotes. -/
def SPShape.toExpr : SPShape → VExpr
  | .sort u => .sort u
  | .pi A B => .forallE A B

@[simp] theorem SPShape.toExpr_sort {u : VLevel} : (SPShape.sort u).toExpr = .sort u := rfl
@[simp] theorem SPShape.toExpr_pi {A B : VExpr} : (SPShape.pi A B).toExpr = .forallE A B := rfl

/-- **What two shapes in one conversion class must have in common.**  The diagonal entries are the
two injectivity facts, the off-diagonal ones are disjointness.  The Π/Π entry carries the domain
chain as well as the codomain chain: it has to, because that is what makes the statement closed
under `symm` and `trans` (`SPShape.Agree.symm`, `.trans`), and it answers row 82c — the domain half
is not a separate ingredient of the induction, it is part of what the induction proves. -/
def SPShape.Agree (env : VEnv) (U : Nat) (Γ : List VExpr) : SPShape → SPShape → Prop
  | .sort u, .sort v => u ≈ v
  | .pi A B, .pi A' B' => ConvC env U Γ A A' ∧ ConvC env U (A::Γ) B B'
  | _, _ => False

theorem SPShape.Agree.symm (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ) :
    ∀ {s₁ s₂ : SPShape}, s₁.Agree env U Γ s₂ → s₂.Agree env U Γ s₁ := by
  intro s₁ s₂ h
  match s₁, s₂, h with
  | .sort _, .sort _, h => exact Eq.symm h
  | .pi _ _, .pi _ _, ⟨hd, hc⟩ => exact ⟨hd.symm, (ConvC.defeqDFC henv hΓ hd hc).symm⟩
  | .sort _, .pi _ _, h => exact False.elim h
  | .pi _ _, .sort _, h => exact False.elim h

theorem SPShape.Agree.trans (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ) :
    ∀ {s₁ s s₂ : SPShape}, s₁.Agree env U Γ s → s.Agree env U Γ s₂ → s₁.Agree env U Γ s₂ := by
  intro s₁ s s₂ h1 h2
  match s₁, s, s₂, h1, h2 with
  | .sort _, .sort _, .sort _, h1, h2 => exact Eq.trans h1 h2
  | .pi _ _, .pi _ _, .pi _ _, ⟨hd1, hc1⟩, ⟨hd2, hc2⟩ =>
    exact ⟨hd1.trans hd2, hc1.trans (ConvC.defeqDFC henv hΓ hd1.symm hc2)⟩
  | .sort _, .sort _, .pi _ _, _, h2 => exact False.elim h2
  | .sort _, .pi _ _, _, h1, _ => exact False.elim h1
  | .pi _ _, .sort _, _, h1, _ => exact False.elim h1
  | .pi _ _, .pi _ _, .sort _, _, h2 => exact False.elim h2

/-- **The one fact.**  A single `IsDefEqStrong` link between two rigid shapes, at an *arbitrary*
type index, forces the shapes to agree.  Index-free for the reason §22 of `InjPiRogue.lean` gives
for the sort side: the conclusion never mentions the index, which is what makes `defeqDF` free —
and here that carries over to the Π side, which is why no `.sort u` index is needed. -/
def ShapeLinkAgree (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {s₁ s₂ : SPShape} {A : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ s₁.toExpr s₂.toExpr A → s₁.Agree env U Γ s₂

/-- The `trans` residual: the same statement with the midpoint restricted to a term that is
syntactically neither a sort nor a Π.  **§5 shows this is equivalent to `ShapeLinkAgree`**, so it
is a name for the target and not a reduction of it. -/
def ShapeMidShapeless (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {s₁ s₂ : SPShape} {M A : VExpr}, CtxStrong env U Γ →
    (∀ c, M ≠ .sort c) → (∀ D E, M ≠ .forallE D E) →
    env.IsDefEqStrong U Γ s₁.toExpr M A → env.IsDefEqStrong U Γ M s₂.toExpr A →
    s₁.Agree env U Γ s₂

/-- The `proofIrrel` residual, for both shapes at once: **a sort is not a proof, and neither is a
Π.**  Compare `Injectivity.not_isProof_of_defeqU_sort` / `not_isProof_of_defeqU_forallE`, which
prove exactly these from `WF.sortUniq'` — i.e. from the statement being reduced.  Cited, not
imported: that bound runs through `sorryAx`.  `SortNotProof` (`InjPiRogue.lean`) is this at
`s = .sort a`; `SortNotPropStrong` is the shape-free shadow of the same case. -/
def ShapeNotProof (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {s : SPShape} {p : VExpr},
    env.IsDefEqStrong U Γ p p (.sort .zero) → env.IsDefEqStrong U Γ s.toExpr s.toExpr p → False

theorem ShapeNotProof.sortNotProof (H : ShapeNotProof env U) : SortNotProof env U :=
  fun h1 h2 => H (s := .sort _) h1 h2

/-! `ShapeNotProof` is **not** `SortNotPropStrong` (`InjPiRogue.lean` §15).  That one says a sort
is not a *proposition* (`.sort u : .sort .zero`); this one says a shape is not a *proof*
(`.sort u : p` with `p : .sort .zero`).  The `proofIrrel` constructor's premise is the latter, and
neither implies the other by any route in this file. -/

/-! ## §4 One induction, eleven constructors, two residuals

The table is `InjPiRogue.lean` §22's, now for both shapes at once and with the Π/Π and sort/Π
entries included.  `symm` and `trans`-through-a-shape close because `SPShape.Agree` is symmetric
and transitive (§3) — which is where `ConvC.defeqDFC` is spent, once, rather than in the statement.
-/

theorem shapeAgree_of_wf (henv : VEnv.WF env) (hm : ShapeMidShapeless env U)
    (hp : ShapeNotProof env U) {Γ : List VExpr} {e1 e2 A : VExpr}
    (h : env.IsDefEqStrong U Γ e1 e2 A) : CtxStrong env U Γ →
      ∀ (s₁ s₂ : SPShape), e1 = s₁.toExpr → e2 = s₂.toExpr → s₁.Agree env U Γ s₂ := by
  induction h with
  | bvar _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | constDF _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | appDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | lamDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | beta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | eta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | sortDF _ _ h3 =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact h3
  | forallEDF _ _ h3 h4 _ =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact ⟨.one h3, .one h4⟩
  | symm _ ih => exact fun hΓ s₁ s₂ e1 e2 => (ih hΓ s₂ s₁ e2 e1).symm henv.ordered hΓ
  | defeqDF _ _ _ _ ih2 => exact ih2
  | @trans _ _ M _ _ hl hr ihl ihr =>
    intro hΓ s₁ s₂ e1 e2
    subst e1; subst e2
    match M, hl, hr, ihl, ihr with
    | .sort c, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.sort c) rfl rfl).trans henv.ordered hΓ (ihr hΓ (.sort c) s₂ rfl rfl)
    | .forallE D E, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.pi D E) rfl rfl).trans henv.ordered hΓ (ihr hΓ (.pi D E) s₂ rfl rfl)
    | .bvar _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .const _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .app _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .lam _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
  | proofIrrel h1 h2 _ _ _ _ =>
    intro _ s₁ _ e1 _; subst e1; exact (hp h1 h2).elim
  | extra h1 _ _ _ _ _ _ _ _ =>
    intro _ s₁ _ e1 _
    cases s₁
    · exact (henv.instL_lhs_ne_sort h1 _ _ e1).elim
    · exact (henv.instL_lhs_ne_forallE h1 _ _ _ e1).elim

/-- **The one fact, from the two residuals and `VEnv.WF`.** -/
theorem shapeLinkAgree_of (henv : VEnv.WF env) (hm : ShapeMidShapeless env U)
    (hp : ShapeNotProof env U) : ShapeLinkAgree env U :=
  fun hΓ h => shapeAgree_of_wf henv hm hp h hΓ _ _ rfl rfl

/-! ## §5 The collapse test on the unified residual, and the general theorem behind it

`ShapeMidShapeless` is equivalent to `ShapeLinkAgree`, so §4's induction derives its conclusion
from a hypothesis of exactly the same strength.  The general statement is `midShapeless_vacuous`:
**no side condition on the midpoint that a β-redex satisfies can localise anything**, which covers
"not a sort" (`SortMidNonSort`), "not a Π" (`PiMidNonPi`), "neither" (`ShapeMidShapeless`), "is an
application", "is a β-redex", and "has no rigid head" alike. -/

theorem ShapeLinkAgree.shapeMidShapeless (H : ShapeLinkAgree env U) : ShapeMidShapeless env U :=
  fun hΓ _ _ h1 h2 => H hΓ (h1.trans h2)

/-- A midpoint statement with an arbitrary side condition `P` on the midpoint. -/
def ShapeMidP (env : VEnv) (U : Nat) (P : VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {s₁ s₂ : SPShape} {M A : VExpr}, CtxStrong env U Γ → P M →
    env.IsDefEqStrong U Γ s₁.toExpr M A → env.IsDefEqStrong U Γ M s₂.toExpr A →
    s₁.Agree env U Γ s₂

/-- **The general collapse.**  If `P` holds of every `betaMid X` — and every shape-based condition
that excludes sorts and Πs does, since `betaMid X` is `.app`-headed — then restricting the midpoint
by `P` gives back the unrestricted single-link statement. -/
theorem midShapeless_vacuous (henv : Ordered env) {P : VExpr → Prop}
    (hP : ∀ X, P (betaMid X)) (H : ShapeMidP env U P) : ShapeLinkAgree env U := by
  intro Γ s₁ s₂ A hΓ h
  have hb := betaMid_link henv hΓ.defeq (X := s₁.toExpr) h.hasType.1.defeq
  exact H hΓ (hP _) hb.symm (hb.trans h)

theorem ShapeLinkAgree.shapeMidP (H : ShapeLinkAgree env U) (P : VExpr → Prop) :
    ShapeMidP env U P := fun hΓ _ h1 h2 => H hΓ (h1.trans h2)

theorem shapeMidP_iff (henv : Ordered env) {P : VExpr → Prop} (hP : ∀ X, P (betaMid X)) :
    ShapeMidP env U P ↔ ShapeLinkAgree env U :=
  ⟨midShapeless_vacuous henv hP, fun H => H.shapeMidP P⟩

/-- The instance of `midShapeless_vacuous` that names the residual §4 leaves. -/
theorem shapeMidShapeless_iff (henv : Ordered env) :
    ShapeMidShapeless env U ↔ ShapeLinkAgree env U := by
  refine ⟨fun H => midShapeless_vacuous henv (P := fun M => (∀ c, M ≠ .sort c) ∧
    ∀ D E, M ≠ .forallE D E) (fun X => ⟨betaMid_ne_sort X, betaMid_ne_forallE X⟩)
    (fun hΓ hP h1 h2 => H hΓ hP.1 hP.2 h1 h2), fun H => H.shapeMidShapeless⟩

/-! ## §6 One statement, three consumers

`shapeLinkAgree_iff` decomposes the one fact into exactly three entries — sort/sort, Π/Π, sort/Π —
both directions, so "one prerequisite, three consumers" is a theorem here rather than a reading of
`unique.tex`.  Each entry then reaches the tree's named consumer.

**The bound, stated honestly in both directions.**

* sort/sort: `SortLinkInvU → SortLinkInvUC → SortLinkInv` are both free, so the entry is sandwiched
  between the two forms `InjPiRogue.lean` already names, differing only by a hypothesis
  (`CtxStrong`) that `CtxStrong.strong` supplies at every use site.
* Π/Π: `PiLinkInvUC → PiLinkInvCod ∧ PiLinkInvDom` is free.  **The converse is not available and no
  claim is made that it is:** `PiLinkInvCod` fixes the index at `.sort u`, and moving an arbitrary
  index `T` to a syntactic sort is uniqueness of typing, i.e. the hole.  So this entry is *at least*
  as strong as the two Π consumers, which is the right direction for a prerequisite.
* sort/Π: `SortPiDisjUC ↔ RigidSortPiDisj`, both directions (`IsDefEq.strong` one way,
  `IsDefEqStrong.defeq` the other), so here the bound is tight.

**What this settles that §17 of `InjPiRogue.lean` left open.**  That section says "explicitly not
claimed: that these plus `VEnv.WF` close `PiLinkInvCod`", and §14 says only an induction on the
derivation can make progress on the Π side.  §4 runs that induction, and the two things that
unblocked it are *not* `ConvC.defeqDFC` (which is still used, but only inside `Agree.symm` and
`Agree.trans`): they are **dropping the `.sort u` index**, which makes `defeqDF` free exactly as on
the sort side, and **carrying the domain chain in the conclusion**, which makes the statement closed
under `symm` and `trans`.  Row 82c's "`PiLinkInvDom` is needed as an ingredient" is therefore right
about the need and wrong about the shape: it is not a separate hypothesis, it is part of what the
induction proves. -/

/-- Π-injectivity for a single link at an **arbitrary** index — both halves. -/
def PiLinkInvUC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' T : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.forallE A B) (.forallE A' B') T →
    ConvC env U Γ A A' ∧ ConvC env U (A::Γ) B B'

/-- Sort/Π disjointness for a single link at an arbitrary index. -/
def SortPiDisjUC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a : VLevel} {A B T : VExpr}, CtxStrong env U Γ →
    ¬ env.IsDefEqStrong U Γ (.sort a) (.forallE A B) T

/-- **The one fact is the conjunction of the three consumers.** -/
theorem shapeLinkAgree_iff :
    ShapeLinkAgree env U ↔ SortLinkInvUC env U ∧ PiLinkInvUC env U ∧ SortPiDisjUC env U := by
  constructor
  · refine fun H => ⟨fun hΓ h => H (s₁ := .sort _) (s₂ := .sort _) hΓ h,
      fun hΓ h => H (s₁ := .pi _ _) (s₂ := .pi _ _) hΓ h,
      fun hΓ h => H (s₁ := .sort _) (s₂ := .pi _ _) hΓ h⟩
  · rintro ⟨h1, h2, h3⟩ Γ s₁ s₂ A hΓ h
    match s₁, s₂, h with
    | .sort _, .sort _, h => exact h1 hΓ h
    | .pi _ _, .pi _ _, h => exact h2 hΓ h
    | .sort _, .pi _ _, h => exact h3 hΓ h
    | .pi _ _, .sort _, h => exact h3 hΓ h.symm

theorem PiLinkInvUC.piLinkInvCod (H : PiLinkInvUC env U) : PiLinkInvCod env U :=
  fun hΓ h => (H hΓ h).2

theorem PiLinkInvUC.piLinkInvDom (H : PiLinkInvUC env U) : PiLinkInvDom env U :=
  fun hΓ h => (H hΓ h).1

/-- **Consumer 3, both directions.**  `RigidSortPiDisj` (`RigidNodeCircle.lean`) is the
`IsDefEqU` form of the off-diagonal entry; the two differ only by `IsDefEq.strong` /
`IsDefEqStrong.defeq`, so the entry is neither weaker nor stronger. -/
theorem SortPiDisjUC.rigidSortPiDisj (henv : Ordered env) (H : SortPiDisjUC env U) :
    RigidSortPiDisj env U :=
  fun hΓ ⟨_, h⟩ => H (CtxStrong.strong henv hΓ) (h.strong henv hΓ)

theorem RigidSortPiDisj.sortPiDisjUC (H : RigidSortPiDisj env U) : SortPiDisjUC env U :=
  fun hΓ h => H hΓ.defeq ⟨_, h.defeq⟩

/-- **Consumer 1**, composed with `InjPiRogue.lean` §20: the corner's single residual, given the
chain collapse `ConvStep2`. -/
theorem convSortInv_of_shapeLinkAgree (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) :
    ConvSortInv env U :=
  convSortInv_of_convStep2_sortLinkInv hcs
    (SortLinkInvUC.sortLinkInv (shapeLinkAgree_iff.1 H).1)

/-- **Consumer 2**, likewise. -/
theorem convPiInvCod_of_shapeLinkAgree (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) :
    ConvPiInvCod env U :=
  convPiInvCod_of_convStep2_piLinkInvCod hcs
    (PiLinkInvUC.piLinkInvCod (shapeLinkAgree_iff.1 H).2.1)

/-! ## §7 What confluence must actually supply

§5 says a conversion-level statement about a midpoint cannot be the request, because β manufactures
a midpoint satisfying any shape condition.  So the request has to name a **reduction relation**, and
the content is the tension between its two clauses: strong enough to join every conversion, weak
enough that a shape's reducts are shapes.  `ShapeCR` is that request, parametric in the relation —
`Red Γ e M` should be read "`e` reduces to `M` in `Γ`", and nothing here fixes it to κ-reduction,
`ParRedK`, or anything else.

Two negative controls show both clauses carry weight: `Red := Eq` fails `join`
(`shapeCR_eq_join_fails`), and `Red := ` conversion fails `normal`
(`shapeCR_conv_normal_fails`, which is `betaMid` again).  **Not claimed:** that any `Red` satisfies
both.  That is the confluence layer's question (`PatMajorCanonical`, `docs/handoff-confluence.md`),
and this file takes no dependency on it. -/

/-- **The confluence request, stated tightly.**  Both clauses are needed and they pull against each
other; `join` is Church–Rosser, `normal` is "a rigid head has no reduct of another shape". -/
structure ShapeCR (env : VEnv) (U : Nat) (Red : List VExpr → VExpr → VExpr → Prop) : Prop where
  join : ∀ {Γ : List VExpr} {e1 e2 A : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ e1 e2 A → ∃ M, Red Γ e1 M ∧ Red Γ e2 M
  normal : ∀ {Γ : List VExpr} {s : SPShape} {M : VExpr}, CtxStrong env U Γ →
    Red Γ s.toExpr M → ∃ s' : SPShape, M = s'.toExpr ∧ s.Agree env U Γ s'

theorem SPShape.toExpr_inj : ∀ {s s' : SPShape}, s.toExpr = s'.toExpr → s = s'
  | .sort _, .sort _, h => by cases h; rfl
  | .pi _ _, .pi _ _, h => by injection h with h1 h2; cases h1; cases h2; rfl
  | .sort _, .pi _ _, h => by cases h
  | .pi _ _, .sort _, h => by cases h

/-- **The whole target from the request.**  No `VEnv.WF`, no induction on the derivation: `join`
plus `normal` plus §3's `Agree` algebra. -/
theorem shapeLinkAgree_of_shapeCR (henv : Ordered env)
    {Red : List VExpr → VExpr → VExpr → Prop} (H : ShapeCR env U Red) : ShapeLinkAgree env U := by
  intro Γ s₁ s₂ A hΓ h
  obtain ⟨M, hm1, hm2⟩ := H.join hΓ h
  obtain ⟨t1, rfl, a1⟩ := H.normal hΓ hm1
  obtain ⟨t2, e2, a2⟩ := H.normal hΓ hm2
  cases SPShape.toExpr_inj e2
  exact a1.trans henv hΓ (a2.symm henv hΓ)

/-! ## §8 Non-vacuity, and the two negative controls -/

/-- `Ordered ∅`, and a link between two distinct sort expressions at `∅`: `Sort (max 0 0)` and
`Sort 0` are `≈` but not equal, so `join` is not satisfied by `Red := Eq`. -/
theorem shapeCR_eq_join_fails :
    (∅ : VEnv).IsDefEqStrong 0 [] (.sort (.max .zero .zero)) (.sort .zero)
      (.sort (.succ (.max .zero .zero))) ∧
    (VExpr.sort (.max .zero .zero) ≠ .sort .zero) := by
  refine ⟨.sortDF ⟨trivial, trivial⟩ trivial ?_, by rintro ⟨⟩⟩
  funext ls; simp [VLevel.eval]

/-- **`Red := ` conversion fails `normal`**, and the witness is `betaMid` once more: at `∅` the
β-redex `(fun (_ : Type 0) => Prop) Prop` converts to `.sort .zero` and is not a shape.  So the
`normal` clause is genuinely about reduction and cannot be discharged at the conversion level. -/
theorem shapeCR_conv_normal_fails :
    (∅ : VEnv).IsDefEqStrong 0 [] (betaMid (.sort .zero)) (.sort .zero)
      (.sort (.succ .zero)) ∧ ∀ s : SPShape, betaMid (.sort .zero) ≠ s.toExpr := by
  refine ⟨betaMid_link .empty trivial (.sortDF trivial trivial rfl), fun s => ?_⟩
  cases s <;> simp [betaMid]

/-! ## §9 Where the CR boundary falls, in one place

**Provable now, at `VEnv.WF`, with neither confluence nor the stratification** (all of §3–§4):

* the `Agree` algebra — `symm` and `trans`, over `Ordered env` alone, `ConvC.defeqDFC` spent here
  and nowhere else;
* eleven of the thirteen `IsDefEqStrong` constructors, i.e. **everything that is a statement about
  the rule set or about endpoint shapes**: `extra` by `DeclRules.WF.instL_lhs_ne_sort` /
  `instL_lhs_ne_forallE`, the six endpoint-shape clashes by no-confusion, `sortDF` and `forallEDF`
  by their own side conditions, `symm`/`defeqDF`/`trans`-through-a-shape by the induction;
* the reduction of all three consumers to one statement, in both directions (§6);
* the whole target from an abstract confluence interface (§7).

**Genuinely a confluence consequence:** the `trans` node, and *nothing weaker*.  §5 is the sharp
form of that: the residual cannot be localised by any condition on the midpoint that a β-redex
satisfies, so "descent at a non-sort midpoint" and "descent at a non-Π midpoint" are names for the
whole statement.  Any request handed to the confluence stream must therefore mention a reduction
relation or a normal-form predicate; `ShapeCR` is the minimal such request found here.

**Genuinely the stratification:** `proofIrrel`, i.e. `ShapeNotProof`.  It is the one residual §4
separates out, and the reference's route to it (unique typing at `n`, `unique.tex:40-54`) is the one
this tree refutes — `Theory/Typing/SubstCRefute.lean`, `VEnv.SubstC` false at `n = 1` over `∅`;
cited from §4H.6/row 86c, not re-derived here.

**A consequence for the two packagings.**  §7's `ShapeCR` absorbs `ShapeNotProof` into `join`: a
`proofIrrel` link is a link, so any `Red` that joins every conversion must already cope with proof
irrelevance — which is exactly the cycle `ParRedCycle.lean` and `DescendRefute.lean` are stuck on.
So of the two decompositions in this file, only §4's separates the stratification-side residual from
the CR-side one, and its CR-side residual is equivalent to the whole target.  **That is the honest
shape of the boundary: the corner has one prerequisite and it is confluence, with `ShapeNotProof`
the only piece that can be peeled off it.** -/

/-- **`Red := Eq` does not satisfy `ShapeCR`** — the `join` clause has content. -/
theorem not_shapeCR_eq : ¬ ShapeCR (∅ : VEnv) 0 (fun _ a b => a = b) := by
  intro H
  obtain ⟨M, e1, e2⟩ := H.join (Γ := []) trivial shapeCR_eq_join_fails.1
  exact shapeCR_eq_join_fails.2 (e1.trans e2.symm)

/-- **`Red := ` conversion does not satisfy `ShapeCR`** — the `normal` clause has content, and the
witness is `betaMid` a third time.  So the request genuinely needs a reduction relation: at the
conversion level `normal` is false, and any relation for which it holds is one β cannot fake. -/
theorem not_shapeCR_conv :
    ¬ ShapeCR (∅ : VEnv) 0 (fun Γ a b => (∅ : VEnv).IsDefEqStrong 0 Γ a b (.sort (.succ .zero))) := by
  intro H
  obtain ⟨s', e, _⟩ := H.normal (Γ := []) (s := .sort .zero) trivial
    shapeCR_conv_normal_fails.1.symm
  exact shapeCR_conv_normal_fails.2 s' e

/-- The `Agree` relation is not trivially true: its off-diagonal entries are `False`, so
`ShapeLinkAgree` has content at every mixed pair. -/
theorem agree_sort_pi_eq_false {Γ : List VExpr} {u : VLevel} {A B : VExpr} :
    (SPShape.sort u).Agree env U Γ (.pi A B) = False := rfl

/-- And its premise is inhabited, so §4's conclusion is not vacuous. -/
theorem shapeLinkAgree_premise_fires :
    (∅ : VEnv).IsDefEqStrong 0 [] (SPShape.sort .zero).toExpr (SPShape.sort .zero).toExpr
      (.sort (.succ .zero)) := .sortDF trivial trivial rfl

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.betaMid_ne_sort
#print axioms Lean4Lean.VEnv.betaMid_ne_forallE
#print axioms Lean4Lean.VEnv.betaMid_isApp
#print axioms Lean4Lean.VEnv.betaMid_link
#print axioms Lean4Lean.VEnv.sortLinkInv_of_sortMidNonSort
#print axioms Lean4Lean.VEnv.SortLinkInvU.sortLinkInvUC
#print axioms Lean4Lean.VEnv.SortLinkInvUC.sortLinkInv
#print axioms Lean4Lean.VEnv.sortLinkInvUC_of_sortMidNonSort
#print axioms Lean4Lean.VEnv.SortMidNonSort.sortMidNonSortC
#print axioms Lean4Lean.VEnv.sortMidNonSortC_iff_sortLinkInvUC
#print axioms Lean4Lean.VEnv.piLinkInvCod_of_piMidNonPi
#print axioms Lean4Lean.VEnv.piLinkInvCod_iff_piMidNonPi
#print axioms Lean4Lean.VEnv.sortMidNonSort_of_sortLinkInvU
#print axioms Lean4Lean.VEnv.SPShape.Agree.symm
#print axioms Lean4Lean.VEnv.SPShape.Agree.trans
#print axioms Lean4Lean.VEnv.ShapeNotProof.sortNotProof
#print axioms Lean4Lean.VEnv.shapeAgree_of_wf
#print axioms Lean4Lean.VEnv.shapeLinkAgree_of
#print axioms Lean4Lean.VEnv.ShapeLinkAgree.shapeMidShapeless
#print axioms Lean4Lean.VEnv.midShapeless_vacuous
#print axioms Lean4Lean.VEnv.ShapeLinkAgree.shapeMidP
#print axioms Lean4Lean.VEnv.shapeMidP_iff
#print axioms Lean4Lean.VEnv.shapeMidShapeless_iff
#print axioms Lean4Lean.VEnv.shapeLinkAgree_iff
#print axioms Lean4Lean.VEnv.PiLinkInvUC.piLinkInvCod
#print axioms Lean4Lean.VEnv.PiLinkInvUC.piLinkInvDom
#print axioms Lean4Lean.VEnv.SortPiDisjUC.rigidSortPiDisj
#print axioms Lean4Lean.VEnv.RigidSortPiDisj.sortPiDisjUC
#print axioms Lean4Lean.VEnv.convSortInv_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.convPiInvCod_of_shapeLinkAgree
#print axioms Lean4Lean.VEnv.SPShape.toExpr_inj
#print axioms Lean4Lean.VEnv.shapeLinkAgree_of_shapeCR
#print axioms Lean4Lean.VEnv.shapeCR_eq_join_fails
#print axioms Lean4Lean.VEnv.shapeCR_conv_normal_fails
#print axioms Lean4Lean.VEnv.not_shapeCR_eq
#print axioms Lean4Lean.VEnv.not_shapeCR_conv
#print axioms Lean4Lean.VEnv.agree_sort_pi_eq_false
#print axioms Lean4Lean.VEnv.shapeLinkAgree_premise_fires
end Audit
