import Lean4Lean.Theory.Typing.CRKProve

/-!
# `CParRedK` -- the complete development for `ParRedK`, and what the triangle still owes

2026-09-04.  Started at HEAD `e0aee76`, verified green there first (bare `lake build`,
`Build completed successfully (1659 jobs)`, exit 0).  **HEAD moved to `4b7ec7c` under me mid-round**
(another stream landed `Verify/Inductive/PosScan.lean` and friends); the closing bare `lake build`
is green at `4b7ec7c` + this file, 1663 jobs, exit 0.  Every cone figure below is dated and names
its commit, because two of them would otherwise be ambiguous between the two.  `CRKProve.lean` proved `CRStatementK` from `ParRedKStatement` and `ParRedKDiamond` and
identified the blocker as **a missing object, not a missing proof**: `CParRedK`, `CParRedK.exists`,
`ParRedK.triangle`, `ParRedK.church_rosser` were all NOT FOUND, while `CParRed.exists` for the
plain relation is cone 3461 and `sorryAx`-free.  This file builds the object.

## What is proved

* `CParRedKn` (§2) -- the complete development, **graded**, and the grade is not a convenience:
  `ParRedK.keta`'s second premise develops the *contractum*, which is not a subterm of the subject
  and for `EtaK.under` is strictly larger, so `VExpr.brecOn` alone -- `CParRed.exists`'s whole
  proof technique -- cannot carry the `keta` case.  Grade `0` is reflexivity; congruences, `beta`
  and `extra` keep the grade; `keta` drops it.  `ParRedK.toN` (`KKetaRow`) already proves
  `ParRedK = ⋃ₙ ParRedKn`, so grading costs no generality.
* `CParRedKn.exists` (§3) -- **unconditional**, cone 3603, own value not a hole, and the *single*
  hole in its cone is `IsDefEqU.forallE_inv_stratified` (entering through `EtaK.defeqU`'s `under`
  case).  This is the lemma `CRKProve` reports missing.
* `parRedKDiamond_of_triangle`, `crStatementK_of_triangle` (§4) -- the assembly: grade both steps
  with `ParRedK.toN`, develop at their maximum, run the triangle twice.  So `CRStatementK`'s second
  hypothesis is now `ParRedKnTriangle` -- the exact analogue of `ChurchRosser.ParRed.triangle`,
  which is a *theorem* one relation over -- instead of `ParRedKDiamond`.
* §5 -- the triangle's new rows, **compiled row by row** rather than tabulated in prose.  Of the
  nine rows where `keta` is the development's root step, five are vacuous
  (`EtaK.not_bvar/not_sort/not_lam/not_forallE`, and `EtaK.not_beta`, new here), one closes
  outright (`const`), one closes from `KetaDevAgree` (`keta_keta_row`), and **two resist**:
  `KetaAppRow` and `KetaExtraRow`.  `keta_root_row` assembles exactly that.
* §6 -- fired at `quotParams`, the non-degenerate instance.

## What resists, and it is *not* what was predicted

`CRKProve` scored "which case of the triangle resists" UNTESTED.  The answer is that the
`keta` x `keta` row -- the obvious candidate, and the one `EtaKDiamond` was invented for -- **does
not resist**: `keta_keta_row` closes it from `KetaDevAgree` plus the grade induction hypothesis, in
three lines.  What resists is the pair of rows where the development fires `keta` and the *step*
does something else at the same node (`KetaAppRow`, `KetaExtraRow`).  Those are the triangle twins
of the site-7 rows `KSite7App.lean`'s ledger leaves open, and the work they need is
`ParRed.triangle`'s `extra` inner induction (pattern-survival under matched-position reduction)
extended by one constructor -- so **unproved, not false**: both hold vacuously at `refParams`, and
a conclusion-shape search for a refutation of any triangle row returns nothing.

## Why `KetaDevAgree` is a better residual than `EtaKDiamond`

`EtaKDiamond` (`KEta.lean`) concludes `Joins` -- multi-step legs on both sides -- and `CRKProve`'s
`etaKDiamond_of_crStatementK` compiles the circle that makes it useless as an input.
`KetaDevAgree` compares the **developments** of the two `EtaK` contracta, with no legs.  §6's
firing is the point: at the pair that refutes the nose diamond `KDescend.KDiamond`
(`g x` versus `g ((fun y => y) x)`, `Verify/QuotAppParams.quotParams_not_kDiamond`), the two
developments are the *same term*, because a development contracts the β-redex in the matched
argument.  `Verify/QuotAppParams.not_normalEq_gx` shows the raw contracta are **not** `NormalEq`
(conditional on the injectivity corner -- it must not be quoted as unconditional).  So the entire
gap between `KDiamond` and `KetaDevAgree` at the canonical instance is one β-step, and the
development closes it.

`KetaDevAgree` is still *implied by* `CRStatementK` (two developments of one subject are defeq
reducts, and confluence upgrades that to `NormalEq`), so it is not ground either; the break must
still come from the rule table, exactly as `KDiamondJoin.lean` §3 concludes.

## The accounting, re-measured 2026-09-04 at `e0aee76` (`scripts/exists.lean`, population 477)

`IsDefEqU.constApp_forallE_false_ofHyps` is **cone 3931, holes 3** -- `CRKProve`'s figure
reproduces exactly, two commits later.  But it is a cone of a *conditional* theorem, and this file
does not discharge the condition: it moves it from `ParRedKDiamond` to `ParRedKnTriangle` and
closes six of that hypothesis's nine new rows.  **3931/3 therefore still cannot be banked**, and
`CRKProve`'s warning ("nobody should bank it before `CParRedK` exists") is answered only in its
premise: `CParRedK` now exists.

Full priors, measurements, verdicts and limits: `docs/handoff-cparredk.md`.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## §1 The neutrality test

`KEta.lean`:476's `NonNeutralK` is reused verbatim -- it is `NonNeutral` with the third disjunct
`∃ e', EtaK Γ e e'`, and its docstring already assigns it to this job ("`CParRed.exists` must
decide it, classically").  This file defines no neutrality predicate of its own. -/

/-- `NonNeutral` implies `NonNeutralK`: the first two disjuncts are shared. -/
theorem NonNeutral.toK {Γ : List VExpr} {e : VExpr} (h : NonNeutral Γ e) : NonNeutralK Γ e :=
  h.imp id .inl

/-! ## §2 The graded complete development -/

/-- **The complete development of `ParRedK`, graded by redex-nesting height.**

Grade `0` is reflexivity; at grade `n+1` every redex present at the root is contracted, and
`keta` drops the grade because its premise develops the *contractum*, which is not a subterm of
the subject (and for `EtaK.under` is strictly larger). -/
inductive CParRedKn : Nat → List VExpr → VExpr → VExpr → Prop where
  | zero {Γ e} : CParRedKn 0 Γ e e
  | bvar {n Γ i} : CParRedKn (n+1) Γ (.bvar i) (.bvar i)
  | sort {n Γ u} : CParRedKn (n+1) Γ (.sort u) (.sort u)
  | const {n Γ c ls} :
      ¬ NonNeutralK Γ (.const c ls) → CParRedKn (n+1) Γ (.const c ls) (.const c ls)
  | app {n Γ f f' a a'} : ¬ NonNeutralK Γ (.app f a) →
      CParRedKn (n+1) Γ f f' → CParRedKn (n+1) Γ a a' →
      CParRedKn (n+1) Γ (.app f a) (.app f' a')
  | lam {n Γ A A' body body'} :
      CParRedKn (n+1) Γ A A' → CParRedKn (n+1) (A::Γ) body body' →
      CParRedKn (n+1) Γ (.lam A body) (.lam A' body')
  | forallE {n Γ A A' B B'} :
      CParRedKn (n+1) Γ A A' → CParRedKn (n+1) (A::Γ) B B' →
      CParRedKn (n+1) Γ (.forallE A B) (.forallE A' B')
  | beta {n Γ A e₁ e₁' e₂ e₂'} :
      CParRedKn (n+1) (A::Γ) e₁ e₁' → CParRedKn (n+1) Γ e₂ e₂' →
      CParRedKn (n+1) Γ (.app (.lam A e₁) e₂) (e₁'.inst e₂')
  | extra {n Γ p r e m1 m2 m2'} :
      Params.Pat p r → Pattern.Matches p e m1 m2 →
      Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
      (∀ a, CParRedKn (n+1) Γ (m2 a) (m2' a)) →
      CParRedKn (n+1) Γ e (Pattern.RHS.apply m1 m2' r.1)
  | keta {n Γ e w w'} : EtaK Γ e w → CParRedKn n Γ w w' → CParRedKn (n+1) Γ e w'

/-- The development is a `ParRedK` step. -/
theorem CParRedKn.toParRedK {n : Nat} {Γ : List VExpr} {e e' : VExpr}
    (H : CParRedKn n Γ e e') : ParRedK Γ e e' := by
  induction H with
  | zero => exact .rfl
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih => exact .extra h1 h2 h3 ih
  | keta hek _ ih => exact .keta hek ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CParRedKn.hasType {n : Nat} {e e' A : VExpr}
    (H : CParRedKn n Γ e e') (he : Γ ⊢ e : A) : Γ ⊢ e' : A := H.toParRedK.hasType hΓ he

/-! ## §3 Existence: the lemma `CRKProve` says is missing -/

/-- **The complete development exists, at every grade.**  The analogue of
`ChurchRosser.CParRed.exists`, and the object `CRKProve.lean` reports as NOT FOUND. -/
theorem CParRedKn.exists : ∀ {n : Nat} {Γ : List VExpr} {e A : VExpr},
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A → ∃ o, CParRedKn n Γ e o := by
  intro n
  induction n with
  | zero => exact fun _ _ => ⟨_, .zero⟩
  | succ n IH =>
  intro Γ e A hΓ H
  induction e using VExpr.brecOn generalizing Γ A with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  have neut {Γ e A} (hΓ : OnCtx Γ (IsType env univs)) (H' : Γ ⊢ e : A)
      (e_ih : e.below (motive := motive)) :
      NonNeutralK Γ e → ∃ o, CParRedKn (n+1) Γ e o := by
    rintro (⟨A, e, a, rfl⟩ | ⟨p, r, m1, m2, h1, hp2, hp3⟩ | ⟨w, hek⟩)
    · have ⟨_, _, hf, ha⟩ := H'.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, he⟩ := hf.lam_inv henv hΓ
      have ⟨_, he⟩ := e_ih.1.2.2.1 (by exact ⟨hΓ, _, hA⟩) he
      have ⟨_, ha⟩ := e_ih.2.1 hΓ ha
      exact ⟨_, .beta he ha⟩
    · suffices ∃ m3 : p.Path → VExpr, ∀ a, CParRedKn (n+1) Γ (m2 a) (m3 a) from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H r h1 hp3
      induction p generalizing e A with
      | const => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih1 H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 hΓ H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
    · have ⟨_, hw⟩ := IH hΓ ((hek.defeqU hΓ).of_l henv hΓ H').hasType.2
      exact ⟨_, .keta hek hw⟩
  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const c ls => exact Classical.byCases (neut hΓ H e_ih) fun hn => ⟨_, .const hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hf
    have ⟨_, h2⟩ := e_ih.2.1 hΓ ha
    exact Classical.byCases (neut hΓ H e_ih) fun hn => ⟨_, .app hn h1 h2⟩
  | lam ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := H.lam_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := H.forallE_inv henv
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) hB
    exact ⟨_, .forallE h1 h2⟩

/-! ## §4 The triangle, and the assembly it feeds -/

/-- **The triangle for `ParRedKn` against the graded development.**  `ChurchRosser`'s
`ParRed.triangle` with `ParRedKn`/`CParRedKn` for `ParRed`/`CParRed`, and a grade side condition:
the development must be at least as deep as the step it dominates.

Stated as a `Prop` and **not** as a property of a relation to be assumed of `ParRedK` itself --
`ParRedMissing.lean`'s recorded trap is about the latter ("a missing reduction step must be stated
as a **constructor of an extension**, never as a property of the relation being extended"), and
this is neither: it is a metatheorem about two *fixed* inductives, of the same shape as
`ParRed.triangle` which is proved outright one relation over.  §5 checks it is not vacuous. -/
def ParRedKnTriangle : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {e e' o A : VExpr}, n ≤ m →
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    ParRedKn n Γ e e' → CParRedKn m Γ e o → ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o

/-! ### §4.1 The triangle at one grade and at one subject

Moved **down** into this file by Round 3, from `TrianglePort.lean` where Round 2 defined them.
The move is the enabling edit `docs/handoff-cparredk.md` §11.3 states verbatim: the two open rows
of §5.2 live *here*, and they cannot carry the induction hypotheses their closing neighbour
`keta_keta_row` carries unless the vocabulary for those hypotheses is available *here* too.
Nothing about the definitions changed; only the module. -/

/-- `ParRedKnTriangle` at a single grade.  Splitting the grade out is not cosmetic: the outer
induction of the port is a *strong* induction on it, because `keta` on either side drops the
grade by one while every other constructor keeps it. -/
def TriangleAt (m : Nat) : Prop :=
  ∀ {n : Nat} {Γ : List VExpr} {e e' o A : VExpr}, n ≤ m →
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    ParRedKn n Γ e e' → CParRedKn m Γ e o → ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o

/-- The same at one fixed subject.  This is exactly what `VExpr.brecOn`'s below-structure
supplies for a proper subterm, written as a `Prop` so that a residual can *carry* it instead of
silently omitting it. -/
def TriangleAtOn (m : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ {n : Nat} {e' o A : VExpr}, n ≤ m → OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    ParRedKn n Γ e e' → CParRedKn m Γ e o → ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o

theorem parRedKnTriangle_of_at (H : ∀ m, TriangleAt m) : ParRedKnTriangle :=
  fun hnm hΓ he h1 h2 => H _ hnm hΓ he h1 h2

theorem TriangleAt.on {m : Nat} (H : TriangleAt m) {Γ : List VExpr} {e : VExpr} :
    TriangleAtOn m Γ e := fun hnm hΓ he h1 h2 => H hnm hΓ he h1 h2

/-- **The diamond, from the triangle.**  This is the input `CRKProve.crStatementK_of` is missing,
and the assembly is `ChurchRosser.ParRed.church_rosser`'s three lines plus one:
grade both steps with `ParRedK.toN`, develop at their maximum, and run the triangle twice.

The grade is what makes it work: a *single* `CParRedKn m` cannot dominate every `ParRedK` step
(`keta`'s tail is unbounded), but `ParRedK.toN` bounds each of the two given steps, and
`CParRedKn.exists` supplies a development at the maximum of the two bounds. -/
theorem parRedKDiamond_of_triangle (HT : ParRedKnTriangle) : ParRedKDiamond := by
  intro Γ e e₁ e₂ A hΓ he h1 h2
  obtain ⟨n₁, k1⟩ := h1.toN
  obtain ⟨n₂, k2⟩ := h2.toN
  obtain ⟨o, ho⟩ := CParRedKn.exists (n := max n₁ n₂) hΓ he
  obtain ⟨_, p1, q1⟩ := HT (Nat.le_max_left ..) hΓ he k1 ho
  obtain ⟨_, p2, q2⟩ := HT (Nat.le_max_right ..) hΓ he k2 ho
  exact ⟨_, _, p1, p2, q1.trans hΓ (q2.symm hΓ)⟩

/-- **`CRStatementK` from the triangle and `ParRedKStatement`.**  `CRKProve.crStatementK_of`'s two
hypotheses, with the second one replaced by the triangle -- i.e. exactly the shape
`ChurchRosser.lean` has for `ParRed`, where `ParRed.triangle` is a theorem. -/
theorem crStatementK_of_triangle (HS : ParRedKStatement) (HT : ParRedKnTriangle) : CRStatementK :=
  crStatementK_of HS (parRedKDiamond_of_triangle HT)

/-! ## §5 Which rows of the triangle resist, row by row

`CRKProve` scored "which case of the triangle resists" UNTESTED.  This section tests it.  The
triangle's induction is `ParRed.triangle`'s: outer on the grade (new -- see §3), then on the
subject with `VExpr.brecOn`, then on the development `H2`, casing on the step `H1`.  Only the rows
where `keta` is one side's **root** step are new; the other sixty-four are `ParRed.triangle`'s,
verbatim modulo the grade.

Three shape facts kill most of the new rows outright, and they are already in the tree:
`EtaK.not_bvar`, `EtaK.not_sort`, `EtaK.not_lam`, `EtaK.not_forallE` (`KEta.lean`:208-217), and
`EtaK.spineHead_const`. -/

/-- A β-redex is not an `EtaK` redex: `EtaK.spineHead_const` forces a constant spine head, and
`.app (.lam A e₁) e₂`'s is the λ.  So the `keta` x `beta` row is vacuous **in both orders**. -/
theorem EtaK.not_beta {Γ : List VExpr} {A e₁ e₂ w : VExpr} :
    ¬ EtaK Γ (.app (.lam A e₁) e₂) w := by
  intro h
  obtain ⟨c, ls, hc⟩ := h.spineHead_const
  exact absurd hc (by simp [VExpr.spineHead])

/-- Grade `0` of `ParRedKn` is reflexivity: `beta`, `extra` and `keta` all require a positive
grade, so nothing but congruence is available.  This is the triangle's base case. -/
theorem ParRedKn.eq_of_grade_zero : ∀ {n : Nat} {Γ : List VExpr} {e e' : VExpr},
    ParRedKn n Γ e e' → n = 0 → e = e' := by
  intro n Γ e e' H
  induction H with
  | bvar | sort | const => intro; rfl
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    intro h; rw [ih1 h, ih2 h]
  | beta | extra | keta => intro h; exact absurd h (Nat.succ_ne_zero _)

theorem ParRedKn.zero_eq {Γ : List VExpr} {e e' : VExpr} (H : ParRedKn 0 Γ e e') : e = e' :=
  H.eq_of_grade_zero rfl

/-- The same for the development. -/
theorem CParRedKn.zero_eq {Γ : List VExpr} {e e' : VExpr} (H : CParRedKn 0 Γ e e') : e = e' := by
  cases H; rfl

/-- **A `keta` step at the root refutes the development's congruence guard.**  So every row with
`keta` on the *step* side and a guarded congruence on the *development* side is vacuous: the guard
`¬ NonNeutralK` includes `∃ w, EtaK Γ e w`, which is `NonNeutralK`'s third disjunct. -/
theorem NonNeutralK.of_etaK {Γ : List VExpr} {e w : VExpr} (h : EtaK Γ e w) : NonNeutralK Γ e :=
  .inr (.inr ⟨_, h⟩)

/-! ### §5.1 The one residual that the `keta` x `keta` row needs, and the proof that it suffices -/

/-- **`KetaDevAgree`: two `EtaK` contracta of one subject have `NormalEq` developments.**

This is the residual for the triangle's `keta` x `keta` row, and it is *not* `EtaKDiamond`.  Three
differences, and the third is the point:

1. `EtaKDiamond`'s conclusion is `Joins` -- multi-step legs on **both** sides.  This one has no
   legs at all: the two developments must be `NormalEq` on the nose.
2. But the subjects are **developments**, not the raw contracta.  `KDescend.KDiamond` -- the nose
   diamond on the raw contracta -- is **refuted** at `quotParams`
   (`Verify/QuotAppParams.quotParams_not_kDiamond`, conditional on the injectivity corner), and
   the refuting pair is `g x` versus `g ((fun y => y) x)`.  A *development* of the second contracts
   that β-redex, so it lands on `g x` and the two agree.  §6 fires exactly that.
3. So `KetaDevAgree` sits strictly between the two: weaker than `KDiamond` (developments absorb the
   β), and not comparable to `EtaKDiamond` (no legs, but developed subjects).

It is stated at a single shared grade `m`, which is all the triangle needs. -/
def KetaDevAgree : Prop :=
  ∀ {m : Nat} {Γ : List VExpr} {e w₁ w₂ o₁ o₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : A → EtaK Γ e w₁ → EtaK Γ e w₂ →
    CParRedKn m Γ w₁ o₁ → CParRedKn m Γ w₂ o₂ → Γ ⊢ o₁ ≡ₚ o₂

/-- **The `keta` x `keta` row closes from `KetaDevAgree` and the grade induction hypothesis.**

This is the row `CRKProve` predicted would resist, and it does *not* resist beyond one named
statement about the rule table's contracta.  The proof is three lines and they are the interesting
three: develop the *step's* contractum `w₁` at the same grade, close the step against that
development by the grade IH (available because `keta` drops the grade -- §3's whole point), and
transport across `KetaDevAgree`. -/
theorem keta_keta_row (HA : KetaDevAgree) {m' n' : Nat}
    (IH : ∀ {n : Nat} {Γ : List VExpr} {e e' o A : VExpr}, n ≤ m' →
      OnCtx Γ (IsType env univs) → Γ ⊢ e : A → ParRedKn n Γ e e' → CParRedKn m' Γ e o →
      ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o)
    {Γ : List VExpr} {e w₁ w₂ e' o A : VExpr} (hnm : n' ≤ m')
    (hΓ : OnCtx Γ (IsType env univs)) (he : Γ ⊢ e : A)
    (hek₁ : EtaK Γ e w₁) (hek₂ : EtaK Γ e w₂)
    (h1 : ParRedKn n' Γ w₁ e') (h2 : CParRedKn m' Γ w₂ o) :
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o := by
  have hw₁ : Γ ⊢ w₁ : A := ((hek₁.defeqU hΓ).of_l henv hΓ he).hasType.2
  obtain ⟨o₁, ho₁⟩ := CParRedKn.exists (n := m') hΓ hw₁
  obtain ⟨o', p, q⟩ := IH hnm hΓ hw₁ h1 ho₁
  exact ⟨o', p, q.trans hΓ (HA hΓ he hek₁ hek₂ ho₁ h2)⟩

/-! ### §5.2 The two rows that do resist, stated

`keta` on the development's side against a **congruence** or an **`extra`** on the step's side.
Neither reduces to `KetaDevAgree`: the step has not fired the K-redex, so there is no second
contractum to compare, and the subject's reduct `e'` need not be a K-redex at all.  These are the
`ParRedK`-triangle twins of the site-7 rows `KSite7App.lean`'s ledger leaves open
(`appDF x keta .under`), and they are stated rather than assumed away. -/

/-- The step congruences at an application while the development fires `keta`.

**Restated by Round 3 (weakened).**  Round 2's M9.3 measured that this row and `KetaExtraRow`
carried **no induction hypothesis at all**, while their closing neighbour `keta_keta_row` carries
one -- the same defect that made a gate unprovable-as-stated elsewhere in the tree.  The three
hypotheses added here are exactly what is in scope at the row's only call site inside
`TrianglePort.triangleAt_of`: the strong grade induction hypothesis below the subject's grade
`m+1`, and the triangle at grade `m+1` on each of the two children, which the `VExpr.brecOn`
below-structure supplies.  Adding them makes the `Prop` strictly **weaker**, so a proof of the old
form is a proof of this one and nothing is lost; what is gained is that the residual no longer
overstates the obligation. -/
def KetaAppRow : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {f a f' a' w o A : VExpr},
    (∀ k, k < m + 1 → TriangleAt k) →
    TriangleAtOn (m+1) Γ f → TriangleAtOn (m+1) Γ a →
    n ≤ m + 1 →
    OnCtx Γ (IsType env univs) → Γ ⊢ .app f a : A →
    EtaK Γ (.app f a) w → CParRedKn m Γ w o →
    ParRedKn n Γ f f' → ParRedKn n Γ a a' →
    ∃ o', ParRedK Γ (.app f' a') o' ∧ Γ ⊢ o' ≡ₚ o

/-- The step fires a *pattern* rule while the development fires `keta`.

**Restated by Round 3 (weakened)**, on the same measurement as `KetaAppRow`.  The second added
hypothesis is the triangle at grade `m+1` on every **matched argument** of the step's pattern;
`TrianglePort.triangleAt_of` builds it from the below-structure by an induction over the pattern,
the same induction that already feeds `ExtraDevRow`.  So the row is handed a genuine hypothesis
and not an axiom. -/
def KetaExtraRow : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {p : Pattern}
    {r : p.RHS × p.Check} {e w o A : VExpr} {m1 m2 m2'},
    (∀ k, k < m + 1 → TriangleAt k) → (∀ x, TriangleAtOn (m+1) Γ (m2 x)) →
    n ≤ m →
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    EtaK Γ e w → CParRedKn m Γ w o →
    Params.Pat p r → Pattern.Matches p e m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
    (∀ x, ParRedKn n Γ (m2 x) (m2' x)) →
    ∃ o', ParRedK Γ (Pattern.RHS.apply m1 m2' r.1) o' ∧ Γ ⊢ o' ≡ₚ o

/-- **The whole `keta`-at-the-development's-root row, from the three residuals and the grade IH.**
Eight subcases; five are vacuous by the shape lemmas above, one closes outright, and the two open
ones are the hypotheses.  This is the compiled ledger, not a table in prose. -/
theorem keta_root_row (HA : KetaDevAgree) (HApp : KetaAppRow) (HExtra : KetaExtraRow) {m' : Nat}
    {n : Nat} {Γ : List VExpr} {e e' w o A : VExpr}
    (IHlt : ∀ k, k < m' + 1 → TriangleAt k)
    (IHapp : ∀ {f a : VExpr}, e = .app f a →
      TriangleAtOn (m'+1) Γ f ∧ TriangleAtOn (m'+1) Γ a)
    (IHpat : ∀ {p : Pattern} {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr},
      Pattern.Matches p e m1 m2 → ∀ x, TriangleAtOn (m'+1) Γ (m2 x))
    (hnm : n ≤ m'+1)
    (hΓ : OnCtx Γ (IsType env univs)) (he : Γ ⊢ e : A)
    (hek : EtaK Γ e w) (h2 : CParRedKn m' Γ w o) (h1 : ParRedKn n Γ e e') :
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o := by
  have hdev : ParRedK Γ e o := .keta hek h2.toParRedK
  cases h1 with
  | bvar => exact absurd hek EtaK.not_bvar
  | sort => exact absurd hek EtaK.not_sort
  | lam => exact absurd hek EtaK.not_lam
  | forallE => exact absurd hek EtaK.not_forallE
  | beta => exact absurd hek EtaK.not_beta
  | const => exact ⟨o, hdev, .refl (hdev.hasType hΓ he)⟩
  | app a1 a2 => exact HApp IHlt (IHapp rfl).1 (IHapp rfl).2 hnm hΓ he hek h2 a1 a2
  | extra b1 b2 b3 b4 =>
    exact HExtra IHlt (IHpat b2) (Nat.le_of_succ_le_succ hnm) hΓ he hek h2 b1 b2 b3 b4
  | keta hek₁ hk =>
    exact keta_keta_row HA (IHlt m' (Nat.lt_succ_self _))
      (Nat.le_of_succ_le_succ hnm) hΓ he hek₁ hek hk h2

/-! ## §6 Fired, not admired

`quotParams` (`Verify/QuotAppParams.lean`) is the non-degenerate instance: the one of `CRKProve`
§2's eight where the rule contracts and `CRStatement` is refutable.  `refParams` is degenerate
(`KStep` empty) and is used below only as a consistency check, labelled as such. -/

/-- A `bvar`-headed application is neutral in the enlarged sense: all three disjuncts of
`NonNeutralK` need either a λ in the function position or a constant spine head, and
`Pattern.Matches.spineHead_const` / `EtaK.spineHead_const` supply the second exclusion. -/
theorem not_nonNeutralK_app_bvar {Γ : List VExpr} {i : Nat} {x : VExpr} :
    ¬ NonNeutralK Γ (.app (.bvar i) x) := by
  rintro (⟨A, e₁, e₂, h⟩ | ⟨p, r, m1, m2, _, hm, _⟩ | ⟨w, hek⟩)
  · exact absurd h (by simp)
  · obtain ⟨c, ls, hc⟩ := hm.spineHead_const
    exact absurd hc (by simp [VExpr.spineHead])
  · obtain ⟨c, ls, hc⟩ := hek.spineHead_const
    exact absurd hc (by simp [VExpr.spineHead])

/-! ### §5.2a Round 1's `KetaExtraRow`, kept verbatim so that it can be refuted

Round 3 weakened `KetaExtraRow` above by adding two induction hypotheses (§16.1 of the handoff).
This is the **pre-weakening** statement, character for character, retained for one purpose: §7.1a
refutes it, and the contrast is the round's second finding.  The weakening is therefore not
cosmetic -- it is the difference between a row this witness kills and a row it does not reach,
because the refutation would have to supply `∀ x, TriangleAtOn (m+1) Γ (m2 x)` and that is not
free at the witness. -/
def KetaExtraRow0 : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {p : Pattern}
    {r : p.RHS × p.Check} {e w o A : VExpr} {m1 m2 m2'}, n ≤ m →
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    EtaK Γ e w → CParRedKn m Γ w o →
    Params.Pat p r → Pattern.Matches p e m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
    (∀ x, ParRedKn n Γ (m2 x) (m2' x)) →
    ∃ o', ParRedK Γ (Pattern.RHS.apply m1 m2' r.1) o' ∧ Γ ⊢ o' ≡ₚ o

/-- The weakening is a genuine weakening: Round 3's `KetaExtraRow` follows from Round 1's. -/
theorem KetaExtraRow0.toWeak (H : KetaExtraRow0) : KetaExtraRow :=
  fun _ _ hnm hΓ he hek hd h1 h2 h3 h4 => H hnm hΓ he hek hd h1 h2 h3 h4

/-! ### §5.3 Round 3: two rigidity lemmas and the corrected residual, stated generically

These are used by §7's refutation, and they are stated here rather than there because §7 lives
inside `attribute [local instance] quotParams`, where the `[Params]` variable is gone. -/

/-- A `bvar` is `ParRedK`-rigid. -/
theorem parRedK_bvar_eq {Γ : List VExpr} {i : Nat} {e' : VExpr}
    (H : ParRedK Γ (.bvar i) e') : e' = .bvar i := by
  cases H with
  | bvar => rfl
  | extra _ hm _ _ =>
    obtain ⟨c, ls, hc⟩ := hm.spineHead_const
    exact absurd hc (by simp [VExpr.spineHead])
  | keta hek _ => exact absurd hek EtaK.not_bvar

/-- **`g x` is `ParRedK`-rigid.**  This is what collapses the triangle's existential to a single
candidate at the witness. -/
theorem parRedK_app_bvar_bvar_eq {Γ : List VExpr} {i j : Nat} {e' : VExpr}
    (H : ParRedK Γ (.app (.bvar i) (.bvar j)) e') : e' = .app (.bvar i) (.bvar j) := by
  cases H with
  | app h1 h2 => rw [parRedK_bvar_eq h1, parRedK_bvar_eq h2]
  | extra h1 h2 h3 _ =>
    exact absurd (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩)) not_nonNeutralK_app_bvar
  | keta hek _ => exact absurd (NonNeutralK.of_etaK hek) not_nonNeutralK_app_bvar

/-- The positive-grade restriction of `KetaDevAgree`: the residual Round 1's §6 firing actually
supports.  Stated so that the next round has the corrected object rather than the refuted one;
**not** proved here, and note that it does *not* suffice for the triangle (§7.2). -/
def KetaDevAgreePos : Prop :=
  ∀ {m : Nat} {Γ : List VExpr} {e w₁ w₂ o₁ o₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : A → EtaK Γ e w₁ → EtaK Γ e w₂ →
    CParRedKn (m+1) Γ w₁ o₁ → CParRedKn (m+1) Γ w₂ o₂ → Γ ⊢ o₁ ≡ₚ o₂

/-- `KetaDevAgree` is strictly stronger than its positive-grade restriction, and the difference is
where the refutation lives. -/
theorem KetaDevAgree.toPos (H : KetaDevAgree) : KetaDevAgreePos :=
  fun hΓ he h1 h2 d1 d2 => H hΓ he h1 h2 d1 d2


end VEnv

namespace VEnv

section
attribute [local instance] quotParams

/-- The development of `g x` is `g x`: both children are rigid and the node is neutral. -/
theorem quotParams_dev_gx {m : Nat} :
    CParRedKn (m+1) qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) (.bvar 1)) :=
  .app not_nonNeutralK_app_bvar .bvar .bvar

/-- The development of `g ((fun y => y) x)` contracts the β-redex in the argument, so it is
**`g x` on the nose**. -/
theorem quotParams_dev_beta {m : Nat} :
    CParRedKn (m+1) qc1 (.app (.bvar 3) qXbeta) (.app (.bvar 3) (.bvar 1)) :=
  .app not_nonNeutralK_app_bvar .bvar (.beta .bvar .bvar)

/-- **THE FIRING.**  At the pair that refutes `KDescend.KDiamond` -- `g x` and
`g ((fun y => y) x)`, the two `K⁺` contracta of one `quotParams` redex -- the two **developments
are syntactically the same term**, at every positive grade.

This is `KetaDevAgree`'s conclusion at the configuration where the nose diamond is false, and it
is stronger than `NormalEq`: the witnesses are equal, not merely `NormalEq`-related.  Contrast
`Verify/QuotAppParams.not_normalEq_gx`, which shows the *raw* contracta are **not** `NormalEq`
(conditional on the injectivity corner, so it must not be quoted as unconditional).  So the whole
gap between `KDiamond` and `KetaDevAgree` at the canonical instance is one β-step in a matched
argument, and the development closes it. -/
theorem quotParams_ketaDevAgree_at_kDiamond_witness {m : Nat} :
    ∃ o, CParRedKn (m+1) qc1 (.app (.bvar 3) (.bvar 1)) o ∧
      CParRedKn (m+1) qc1 (.app (.bvar 3) qXbeta) o :=
  ⟨_, quotParams_dev_gx, quotParams_dev_beta⟩

/-- The same pair, as `KetaDevAgree`'s conclusion proper: the two developments are `NormalEq`.
Needs a typing for the shared reduct, and nothing else. -/
theorem quotParams_devAgree_normalEq {m : Nat} :
    ∃ o₁ o₂, CParRedKn (m+1) qc1 (.app (.bvar 3) (.bvar 1)) o₁ ∧
      CParRedKn (m+1) qc1 (.app (.bvar 3) qXbeta) o₂ ∧ NormalEq qc1 o₁ o₂ :=
  ⟨_, _, quotParams_dev_gx, quotParams_dev_beta, .refl (qT_gx qT_x)⟩

/-- **`CParRedKn.exists` at the non-degenerate instance, on a term the K-rule actually moves.**
`qLiftT` is the term `CRKProve.quotParams_parRedK_qLiftT` reduces with a `keta` step, and
`CRKProve.quotParams_crDefEqK` is stated at it.  Developing it is not vacuous: the grade is
positive and the subject is `EtaK`-reducible, so the development's root step *is* `keta`. -/
theorem quotParams_dev_exists {m : Nat} :
    ∃ o, CParRedKn (m+1) qc0T (qLiftT .zero (.succ .zero)) o :=
  CParRedKn.exists qc0T_wf qLiftT0_hasType

end

/-- Consistency check at the degenerate instance: `KetaDevAgree` holds at `refParams`
**vacuously** -- `refParams_no_etaK` empties the hypothesis.  Recorded as a check, not as
evidence; `KCanonical.lean`'s "why there is no refutation" note applies verbatim. -/
theorem refParams_ketaDevAgree : @KetaDevAgree refParams :=
  fun _ _ h => absurd h refParams_no_etaK

/-- The same for the two open rows: vacuous at `refParams`, so **no refutation of either lives at
the only degenerate instance**, and there is none anywhere in the tree (`shape.lean` on
`{ParRedK, NormalEq}` returns 26 constants, none a negation of a triangle row).  This is a
consistency check and a *lower bound on their consistency*, not evidence that they hold. -/
theorem refParams_ketaAppRow : @KetaAppRow refParams :=
  fun _ _ _ _ _ _ h => absurd h refParams_no_etaK

theorem refParams_ketaExtraRow : @KetaExtraRow refParams :=
  fun _ _ _ _ _ h => absurd h refParams_no_etaK


/-! ## §7 Round 3: the residual list is not merely unproved -- **`KetaDevAgree` is REFUTED**

Everything above §7 is Rounds 1 and 2 (plus Round 3's §4.1 move and §5.2 weakening).  This
section is Round 3's, and it reverses the stream's verdict.

`KetaDevAgree` is quantified over **every** grade `m`, and its docstring's whole argument for why
it is weaker than `KDescend.KDiamond` is that "a *development* of the second contracts that
β-redex, so it lands on `g x` and the two agree".  That argument is sound **at positive grade
only**.  At `m = 0` the development is `CParRedKn.zero`, i.e. the identity
(`CParRedKn.zero_eq`), so the `m = 0` instance of `KetaDevAgree` says: *two `EtaK` contracta of
one subject are `NormalEq` on the nose.*  That is `KDiamond` with `EtaK.here` for `KStep` -- and
`Verify/QuotAppParams.quotParams_not_kDiamond` already refutes it, by the very pair Round 1's §6
quotes.

So the gap between `KDiamond` and `KetaDevAgree` that Round 1 measured as "one β-step in a matched
argument, and the development closes it" is closed by the development **only when the development
is allowed to move**, and grade `0` forbids it.  Round 1's §6 firing
(`quotParams_devAgree_normalEq`) is stated at `m+1` and is therefore *not* a firing of the
residual it is presented as supporting: it exhibits the positive-grade instances holding while the
grade-`0` instance is false.

The refutation is **conditional**, on exactly the corner `not_normalEq_gx` rests on (`PiInv` and
`WF.propTypeAgreeOn`, both `sorryAx`, both pre-existing).  `#print axioms` is in
`docs/handoff-cparredk.md` §16.4, and it must not be quoted as unconditional. -/

section
attribute [local instance] quotParams

/-- The subject of the two competing `K⁺` steps, typed -- the one premise of `KetaDevAgree` and of
the triangle that `quotParams_not_kDiamond` does not already carry.  The type is whatever
`HasType.app` computes; nothing below depends on its shape. -/
theorem qRedex_hasType :
    ∃ A, qEnv.HasType 0 qc1
      (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1))) A :=
  ⟨_, .app qLift1_hasType (qMk1_hasType qT_x)⟩

/-- **`KetaDevAgree` is FALSE at `quotParams`.**  Instantiate at grade `0`, where both
developments are the identity, and the conclusion is exactly `not_normalEq_gx`'s target.

Conditional on the injectivity corner -- see the section header. -/
theorem quotParams_not_ketaDevAgree : ¬ KetaDevAgree := fun H =>
  have ⟨_, hty⟩ := qRedex_hasType
  not_normalEq_gx <| H (m := 0) qc1_wf hty
    (.here quotParams_kstep_x) (.here quotParams_kstep_xbeta) .zero .zero

/-! ### §7.1 …and the triangle itself, not only the residual

The refutation does not stop at `KetaDevAgree`: it reaches `ParRedKnTriangle`, because the
configuration is a legal instance of the triangle's **own** grade side condition `n ≤ m` at
`n = m = 1`.  The development `keta _ .zero` is a `CParRedKn 1`; the step
`keta _ ParRedKn.rfl` is a `ParRedKn 1`; and the step's reduct `g x` is `ParRedK`-**rigid**, so
the triangle's existential has only one candidate and it is refuted.

Rigidity is the part that has to be proved, and it is three lines: a `bvar`-headed application is
neutral in the enlarged sense (`not_nonNeutralK_app_bvar`, Round 1), so neither `extra` nor `keta`
can fire on `g x`, and the congruence leaves it alone. -/

/-- **`ParRedKnTriangle` is FALSE at `quotParams`** -- so the hypothesis Round 1 reduced
`CRStatementK` to, and Round 2 reduced to a four-row list, is not merely unproved.

The instance is `n = m = 1`, which satisfies the triangle's own side condition `n ≤ m`; and
`n = m = 1` is not a corner, it is the **principal** case of the assembly, since
`parRedKDiamond_of_triangle` develops at exactly `max n₁ n₂`.

Conditional on the injectivity corner -- see the section header. -/
theorem quotParams_not_parRedKnTriangle : ¬ ParRedKnTriangle := by
  intro H
  obtain ⟨_, hty⟩ := qRedex_hasType
  obtain ⟨o', hred, hne⟩ := H (m := 1) (n := 1) (Nat.le_refl 1) qc1_wf hty
    (.keta (.here quotParams_kstep_x) ParRedKn.rfl)
    (.keta (.here quotParams_kstep_xbeta) .zero)
  rw [parRedK_app_bvar_bvar_eq hred] at hne
  exact not_normalEq_gx hne

/-- **The four-row list is jointly false at the live instance.**  `TrianglePort`'s
`parRedKnTriangle_of` derives the triangle from `KetaDevAgree`, `KetaAppRow`, `KetaExtraRow` and
`ExtraDevRow`; so the list cannot be discharged, and Round 2's joint-satisfiability check
(`refParams_parRedKnTriangle`, unconditional) established satisfiability **only at the degenerate
instance where every row is vacuous**.

Stated here in the negative-conjunction form, because that is the form that is honest: it does not
say which rows are false, only that they cannot all hold.  `quotParams_not_ketaDevAgree` names one
that is.  Conditional on the injectivity corner. -/
theorem quotParams_not_rows_jointly
    (HT : KetaDevAgree → KetaAppRow → KetaExtraRow → ExtraDevRow → ParRedKnTriangle) :
    ¬ (KetaDevAgree ∧ KetaAppRow ∧ KetaExtraRow ∧ ExtraDevRow) :=
  fun ⟨h1, h2, h3, h4⟩ => quotParams_not_parRedKnTriangle (HT h1 h2 h3 h4)

/-- **The refutation is tight in the grade, and this is what says so.**  The same witness at
`n = 1, m = 2` **satisfies** the triangle: the development of `E` at grade `2` is
`keta (.here quotParams_kstep_xbeta)` over the grade-`1` development of `g ((fun y => y) x)`,
which contracts the β-redex (`quotParams_dev_beta`) and lands on `g x`; the step's reduct is
`g x` too, so `NormalEq` is `refl`.

So what §7.1 refutes is not "the triangle at this witness" but "the triangle when the development
has **no grade to spare**" -- and that is exactly the configuration
`parRedKDiamond_of_triangle` manufactures, since it develops at `max n₁ n₂` and runs the triangle
at `n = m`.  One unit of slack rescues *this* row; §7.2 says why no fixed amount of slack rescues
the table. -/
theorem quotParams_triangle_holds_with_slack :
    CParRedKn 2 qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
        (.app (.bvar 3) (.bvar 1)) ∧
      ParRedKn 1 qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
        (.app (.bvar 3) (.bvar 1)) ∧
      ParRedK qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) (.bvar 1)) ∧
      NormalEq qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) (.bvar 1)) :=
  ⟨.keta (.here quotParams_kstep_xbeta) quotParams_dev_beta,
    .keta (.here quotParams_kstep_x) ParRedKn.rfl,
    ParRedK.rfl, .refl (qT_gx qT_x)⟩

/-! ### §7.1a A **second** residual falls, in the form Round 1 stated it

`KetaExtraRow0` (§5.2a) is Round 1's `KetaExtraRow` before Round 3 weakened it.  At `m = n = 0`
the development of the `EtaK` contractum is the identity and the step's matched arguments do not
move, so the row says: *the pattern rule's contractum and the `EtaK` contractum of one subject are
joined by a one-sided `ParRedK` leg meeting a nose `NormalEq`.*  At the witness the pattern
contractum is `g x`, which is rigid, and the `EtaK` contractum is `g ((fun y => y) x)` -- so the
leg cannot move and `not_normalEq_gx` applies.  The direction matters: had the two been the other
way round the β-redex would have been on the leg's side and the row would have held, which is
exactly what happens to `ExtraKetaRow` and why that row is **not** refuted here. -/

/-- **Round 1's `KetaExtraRow` is FALSE at `quotParams`.**  Conditional on the injectivity corner.

Round 3's weakened `KetaExtraRow` is *not* refuted by this proof: it would additionally require
`∀ x, TriangleAtOn 1 qc1 (m2 x)` at the witness, which is not free.  So the weakening the brief
asked for is load-bearing rather than cosmetic. -/
theorem quotParams_not_ketaExtraRow0 : ¬ KetaExtraRow0 := by
  intro H
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches (.succ .zero) (.succ .zero) (.bvar 1)
  obtain ⟨_, hty⟩ := qRedex_hasType
  obtain ⟨o', hred, hne⟩ := H (m := 0) (n := 0) (r := (quotRHS, quotCheck)) (m2' := m2)
    (Nat.le_refl 0) qc1_wf hty (.here quotParams_kstep_xbeta) .zero
    quotParams_pat_app hm hck (fun _ => ParRedKn.rfl)
  rw [hrhs] at hred
  rw [parRedK_app_bvar_bvar_eq hred] at hne
  exact not_normalEq_gx hne

/-! ### §7.2 The repair, and the exact reason a smaller one does not exist

The obvious repair is to restrict `KetaDevAgree` to positive grade.  It is not enough, and the
reason is worth stating precisely, because it is a fact about the **grading**, not about the
quotient rule.

`CParRedKn`'s grade is consumed by `keta` and by nothing else: `beta`, `extra` and every
congruence keep it.  So a `CParRedKn m` development is a *complete* development **except** that
K-chains are truncated at depth `m`, and a `keta` at the root spends one unit of the budget that
the term below then does not have.  A `ParRedKn n` step, by contrast, spends grade on `beta` and
`extra` too, and its congruences spend nothing.  Consequently, in the triangle's induction:

* `keta` on **both** sides is in lockstep -- each drops one -- which is why `keta_keta_row` closes;
* `keta` on the development's side against a **congruence** step drops the development's budget
  while the step keeps its own, so the sub-triangle at the contractum needs `n ≤ m` and is handed
  `n ≤ m+1`.  That is `KetaAppRow`, and it is the **only** row with this defect: `KetaExtraRow`
  and `ExtraKetaRow` both face a step whose own constructor also drops the grade.

No fixed amount of slack in the side condition repairs this, since a K-chain of length `k`
consumes `k` units of the development's budget and none of the step's, and `k` is bounded only by
the development's own grade.  The side condition must be `n ≤ m` at the base (grade `0`
development is the identity, and `zero_dev_row` needs `n = 0`) and `n ≤ m - k` at depth `k`;
those are incompatible.

So the repair is not in the residual list at all: **the apex of the triangle has to be a complete
development, and `CParRedKn m` is not one.**  An ungraded `CParRedK` needs the K-chain to
terminate, which nothing in `Params` supplies -- exactly the observation Round 1's own shape prior
S2 made about `CParRedKn.exists` ("nothing in `Params` says the rule table terminates") and then
worked around with the grade.  The grade makes existence provable and the triangle false. -/

/-- **The positive-grade residual is *not* refuted by this witness.**  At grade `m+1` the
development of `g ((fun y => y) x)` contracts the β-redex and lands on `g x`
(`quotParams_dev_beta`), so the two developments are literally equal and `NormalEq` is `refl`.
This is Round 1's §6 firing, restated as what it actually establishes: the grade-`0` instance is
false and the positive-grade instances at this witness are true. -/
theorem quotParams_ketaDevAgreePos_at_witness {m : Nat} :
    ∃ o₁ o₂, CParRedKn (m+1) qc1 (.app (.bvar 3) (.bvar 1)) o₁ ∧
      CParRedKn (m+1) qc1 (.app (.bvar 3) qXbeta) o₂ ∧ o₁ = o₂ :=
  ⟨_, _, quotParams_dev_gx, quotParams_dev_beta, rfl⟩

end

end VEnv

end Lean4Lean
