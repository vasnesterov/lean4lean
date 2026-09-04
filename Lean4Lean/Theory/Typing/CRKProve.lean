import Lean4Lean.Theory.Typing.CRShape
import Lean4Lean.Theory.Typing.KDiamondJoin
import Lean4Lean.Theory.Typing.ParRedKGraded
import Lean4Lean.Verify.QuotAppParams

/-!
# Proving `CRStatementK` — the assembly, and the two holes that survive it

Round 2 of 2026-09-04, `docs/handoff-crshape.md` §4–§6.  `Theory/Typing/CRShape.lean` §3 states
`CRDefEqK`/`CRStatementK` (confluence with the reduction legs over `ParRedK`) and proves
`CRStatement.toK`, so the statement is a genuine weakening.  What it does not do is *prove* it,
and §2.10 of the handoff measured why that would be worth doing: `IsDefEqU.weakN_iff` and
`NormalEq.descend` reach `Verify/Typing/ConstSpine.lean`'s three consumers **only through the
proof of confluence**, never through its statement or the reduction inversions.

This file carries out the assembly, and it changes the accounting.

## The result

```
theorem crStatementK_of (HS : ParRedKStatement) (HD : ParRedKDiamond) : CRStatementK
```
`ParRedKStatement` is `KSite7.lean:29`, already in the tree and already derived there from
`WeakNInvDS` alone (`ParRedKGraded.parRedKStatement_of_weakNInvDS`).  `ParRedKDiamond` (§1) is
`ParRed.church_rosser`'s conclusion with `ParRedK` substituted, and is new.  The proof is
`ChurchRosser.lean`'s `ParRedS.church_rosser` (`:2440`) and `IsDefEq.church_rosser` (`:2485`),
line for line, with `ParRedS` -> `ParRedKS`.

## The accounting, measured 2026-09-04 at `ca04f43` (`scripts/exists.lean`, population 471)

`crStatementK_of` has cone 3859 and holes `{IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified,
WF.rigidShapeUniqNS}` -- **three, and `NormalEq.descend` is absent**.  Discharging confluence in
`ConstSpine.lean`'s two `false` consumers (§4.1) gives 3931/3 and 3929/3 against the tree's
4431/4 and 4429/4.

> **One census hole drops out of the `ConstSpine` route, not two: `NormalEq.descend`.**

`IsDefEqU.weakN_iff` survives, and the entry point is exact: `CRDefEqK.trans` -- forced by
`IsDefEq`'s `trans` rule and present in any confluence statement over any reduction relation --
joins the two tips with `NormalEq.trans`, whose cone is 3696 with `weakN_iff` in it.
`NormalEq.trans` mentions no reduction relation, so no K repair can reach it.  By contrast
`NormalEq.parRedKS` below -- the lemma that *replaces* the `descend`-carrying
`NormalEq.parRedS` -- is cone 49 and `sorryAx`-free.  That asymmetry is the whole result.

## What blocks the hypotheses

`ParRedKDiamond` is **unproved, not false**: `quotParams_parRedKDiamond_at_kDiamond_witness`
(§4.3) shows the one witness that refutes `KDiamond` joins with *single-step* legs, so the
standing refutation does not transfer, and the tree contains no refutation of `KDiamondJ` or
`PatMajorCanonicalJ`.  What is missing is a complete development `CParRedK` (`exists.lean`:
`CParRedK`, `CParRedK.exists`, `ParRedK.triangle`, `ParRedK.church_rosser` all **NOT FOUND**;
`CParRed.exists` for `ParRed` is cone 3461 and `sorryAx`-free, so completeness is free there).
And the triangle's `keta` residual `EtaKDiamond` is **circular with the target**:
`etaKDiamond_of_crStatementK` (§4) compiles that circle.  The break is
`KDiamondJoin.kDiamondJ_of_patMajorCanonicalJ` -- M3 restated as joinability, a rule-table
property with no confluence in it.

Full priors, measurements, verdicts and limits: `docs/handoff-crshape.md` §4-§6.
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

/-! ## §1 The one missing input: a one-step diamond for `ParRedK` -/

/-- **The `ParRedK` diamond.**  This is `ChurchRosser.lean`'s `ParRed.church_rosser`'s
*conclusion*, verbatim, with `ParRed` replaced by `ParRedK` -- one parallel step on each leg and
a `NormalEq` at the tip.

It is stated, not proved.  `ParRed.church_rosser` goes through `ParRed.triangle` against the
complete development `CParRed`, and there is no `CParRedK`; `ParRed.triangle`'s new residual for
the `keta` constructor is `KEta.lean`'s `EtaKDiamond`.

**Why the legs are single steps and not `Joins`.**  `KDiamondJoin.lean` establishes that the
*`KStep`* diamond has to be joinability rather than `NormalEq` on the nose, because two `K⁺`
steps at `quotParams` give `g x` and `g ((fun y => y) x)`.  That does **not** force the
`ParRedK`-level diamond to have multi-step legs: `ParRedK` is a *parallel* reduction, so
`g ((fun y => y) x) ≫ᴷ g x` in one step and the pair closes at single-step legs.  §2's
`ParRedKDiamondJ` is the multi-step-legged weakening, and `parRedKDiamond_toJ` shows this
implies it; the converse is where the assembly below **breaks**, and §2 says exactly why. -/
def ParRedKDiamond : Prop :=
  ∀ {Γ : List VExpr} {e e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : A → ParRedK Γ e e₁ → ParRedK Γ e e₂ →
    ∃ e₁' e₂', ParRedK Γ e₁ e₁' ∧ ParRedK Γ e₂ e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂'

/-- The `Joins`-legged weakening, i.e. `KDiamondJoin.Joins` as the diamond's conclusion. -/
def ParRedKDiamondJ : Prop :=
  ∀ {Γ : List VExpr} {e e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : A → ParRedK Γ e e₁ → ParRedK Γ e e₂ → Joins Γ e₁ e₂

theorem parRedKDiamond_toJ (H : ParRedKDiamond) : ParRedKDiamondJ :=
  fun hΓ he h1 h2 =>
    have ⟨_, _, l1, l2, l3⟩ := H hΓ he h1 h2
    ⟨_, _, .tail .rfl l1, .tail .rfl l2, l3⟩

/-- Consistency, and the lower bound: where `EtaK` is empty, `ParRedK` is `ParRed` and the
diamond is `ChurchRosser.lean`'s own theorem.  Recorded as a check, not as evidence -- see
`KCanonical.lean`'s "why there is no refutation" note. -/
theorem parRedKDiamond_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : ParRedKDiamond := by
  intro Γ e e₁ e₂ A hΓ he h1 h2
  obtain ⟨_, _, l1, l2, l3⟩ :=
    ParRed.church_rosser hΓ he (ParRedK.toParRed hno h1) (ParRedK.toParRed hno h2)
  exact ⟨_, _, l1.toK, l2.toK, l3⟩

omit [Params] in
theorem refParams_parRedKDiamond : @ParRedKDiamond refParams :=
  @parRedKDiamond_of_no_etaK refParams (fun h => refParams_no_etaK h)

/-! ## §2 `CRDefEqK`'s algebra

`CRDefEqK Γ e₁ e₂` is `(∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧ Joins Γ e₁ e₂` -- the third
conjunct is `KDiamondJoin.Joins` on the nose, which `crDefEqK_eq` checks by `rfl` rather than by
eye. -/

theorem crDefEqK_eq : CRDefEqK = fun (Γ : List VExpr) (e₁ e₂ : VExpr) =>
    (∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧ Joins Γ e₁ e₂ := rfl

/-- Site 7 for `ParRedK`, closed under the reflexive-transitive closure of the right leg.  The
`ParRed` analogue is `ChurchRosser.lean`'s `NormalEq.parRedS`, whose cone carries
`NormalEq.descend`; this one carries only whatever discharges `ParRedKStatement`. -/
theorem NormalEq.parRedKS (HS : ParRedKStatement) {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : ParRedKS Γ e₂ e₂') :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  induction H2 with
  | rfl => exact ⟨_, .rfl, H1⟩
  | tail h1 h2 ih =>
    let ⟨_, a1, a2⟩ := ih
    let ⟨_, b1, b2⟩ := HS hΓ a2 h2
    exact ⟨_, a1.trans b1, b2⟩

/-- **Confluence of `ParRedKS`, from the one-step diamond and site 7.**  This is
`ChurchRosser.lean`'s `ParRedS.church_rosser` with `ParRedK`/`ParRedKS` throughout, and the proof
is that one's line for line.

**Where `ParRedKDiamondJ` would not do, measured by the failed attempt rather than guessed.**  The
inner induction's invariant is `∃ e₁' e₂', ParRedK Γ A2 e₁' ∧ ParRedKS Γ c e₂' ∧ e₁' ≡ₚ e₂'` --
first leg a **single** step -- and the diamond is applied to that leg against the next step of the
chain.  With `Joins` legs the invariant's first leg becomes `ParRedKS`, and then the diamond call
needs shape `ParRedKS × ParRedK → Joins`, i.e. a *strip* lemma, whose own induction is not
structurally smaller: it lands back on `ParRedKS × ParRedK` at the interior node.  My first draft
was exactly this and Lean rejected it at that call
(`Application type mismatch: a1 has type ParRedKS Γ b w but is expected to have type ParRedK Γ b ?m`).
So the multi-step-legged diamond is **not** a drop-in, and the single-step form is not a
convenience. -/
theorem ParRedKS.church_rosser (HS : ParRedKStatement) (HD : ParRedKDiamond)
    {Γ : List VExpr} {e e₁ e₂ A : VExpr} (hΓ : OnCtx Γ (IsType env univs)) (H : Γ ⊢ e : A)
    (H1 : ParRedKS Γ e e₁) (H2 : ParRedKS Γ e e₂) : Joins Γ e₁ e₂ := by
  induction H2 with
  | rfl => exact ⟨_, _, .rfl, H1, .refl (ParRedKS.hasType hΓ H1 H)⟩
  | @tail b c h1 H2 ih =>
    replace H := ParRedKS.hasType hΓ h1 H
    have ⟨_, A2, a1, a2, a3⟩ := ih
    have ⟨_, _, b1, b2, b3⟩ :
        ∃ e₁' e₂', ParRedK Γ A2 e₁' ∧ ParRedKS Γ c e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
      clear a3; induction a2 with
      | rfl => exact ⟨_, _, H2, .rfl, .refl (H2.hasType hΓ H)⟩
      | tail h1 h2 ih =>
        have ⟨_, _, a1, a2, a3⟩ := ih
        have ⟨_, _, b1, b2, b3⟩ := HD hΓ (ParRedKS.hasType hΓ h1 H) a1 h2
        have ⟨_, c1, c2⟩ := NormalEq.parRedKS HS hΓ (a3.symm hΓ) (.tail .rfl b1)
        exact ⟨_, _, b2, a2.trans c1, (c2.trans hΓ b3).symm hΓ⟩
    have ⟨_, c1, c2⟩ := NormalEq.parRedKS HS hΓ a3 (.tail .rfl b1)
    exact ⟨_, _, a1.trans c1, b2, c2.trans hΓ b3⟩

theorem CRDefEqK.normalEq {Γ : List VExpr} {e₁ e₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : Γ ⊢ e₁ ≡ₚ e₂) : CRDefEqK Γ e₁ e₂ :=
  let ⟨_, h⟩ := H.defeq hΓ; ⟨⟨_, h.hasType.1⟩, ⟨_, h.hasType.2⟩, _, _, .rfl, .rfl, H⟩

theorem CRDefEqK.refl {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : Γ ⊢ e : A) : CRDefEqK Γ e e :=
  .normalEq hΓ (.refl H)

theorem CRDefEqK.defeq {Γ : List VExpr} {e₁ e₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) : CRDefEqK Γ e₁ e₂ → IsDefEqU env univs Γ e₁ e₂
  | ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, h3, h4, h5⟩ =>
    ⟨_, .trans_l henv hΓ (ParRedKS.defeq hΓ h3 h1) <|
      .transU_r henv hΓ (h5.defeq hΓ) (ParRedKS.defeq hΓ h4 h2).symm⟩

theorem CRDefEqK.symm {Γ : List VExpr} {e₁ e₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) : CRDefEqK Γ e₁ e₂ → CRDefEqK Γ e₂ e₁
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h2, h1, _, _, h4, h3, h5.symm hΓ⟩

/-- **`CRDefEqK` is transitive** — the case that forces both hypotheses, and the case for whose
sake `ChurchRosser.lean` needs `ParRedS.church_rosser` at all. -/
theorem CRDefEqK.trans (HS : ParRedKStatement) (HD : ParRedKDiamond)
    {Γ : List VExpr} {e₁ e₂ e₃ : VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    CRDefEqK Γ e₁ e₂ → CRDefEqK Γ e₂ e₃ → CRDefEqK Γ e₁ e₃
  | ⟨l1, ⟨_, l2⟩, _, _, l3, l4, l5⟩, ⟨_, r2, _, _, r3, r4, r5⟩ => by
    let ⟨_, _, m1, m2, m3⟩ := ParRedKS.church_rosser HS HD hΓ l2 l4 r3
    let ⟨_, a1, a2⟩ := NormalEq.parRedKS HS hΓ l5 m1
    let ⟨_, b1, b2⟩ := NormalEq.parRedKS HS hΓ (r5.symm hΓ) m2
    exact ⟨l1, r2, _, _, l3.trans a1, r4.trans b1, a2.trans hΓ <| m3.trans hΓ (b2.symm hΓ)⟩

/-! ## §3 `CRStatementK`, proved from the two hypotheses

`ChurchRosser.lean:2485`'s induction over `IsDefEq`, verbatim, with `ParRedS` → `ParRedKS`.  The
`eta` case is the interesting one and it is *unchanged*: it closes by `NormalEq.etaL` with both
legs empty, which is why the refutation of `CRStatement`
(`KCanonical.not_crStatement_of_kstep`) is not about this case but about the `trans` case's
joining. -/

theorem crStatementK_of (HS : ParRedKStatement) (HD : ParRedKDiamond) : CRStatementK := by
  have mk {Γ e₁ e₂ A e₁' e₂'} (H : Γ ⊢ e₁ ≡ e₂ : A)
      (h1 : ParRedKS Γ e₁ e₁') (h2 : ParRedKS Γ e₂ e₂') (h3 : Γ ⊢ e₁' ≡ₚ e₂') :
      CRDefEqK Γ e₁ e₂ :=
    ⟨⟨_, H.hasType.1⟩, ⟨_, H.hasType.2⟩, _, _, h1, h2, h3⟩
  have main : ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, Γ ⊢ e₁ ≡ e₂ : A →
      OnCtx Γ (IsType env univs) → CRDefEqK Γ e₁ e₂ := by
    intro Γ e₁ e₂ A H
    induction H with
    | bvar h => exact fun hΓ => .refl hΓ (.bvar h)
    | symm _ ih => exact fun hΓ => (ih hΓ).symm hΓ
    | trans _ _ ih1 ih2 => exact fun hΓ => CRDefEqK.trans HS HD hΓ (ih1 hΓ) (ih2 hΓ)
    | sortDF h1 h2 h3 => exact fun hΓ => .normalEq hΓ (.sortDF h1 h2 h3)
    | constDF h1 h2 h3 h4 h5 => exact fun hΓ => .normalEq hΓ (.constDF h1 h2 h3 h4 h5)
    | appDF h1 h2 ih1 ih2 =>
      intro hΓ
      obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
      obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 hΓ
      exact mk (.appDF h1 h2) (.app a1 b1) (.app a2 b2) <|
        .appDF (ParRedKS.hasType hΓ a1 h1.hasType.1) (ParRedKS.hasType hΓ a2 h1.hasType.2)
          (ParRedKS.hasType hΓ b1 h2.hasType.1) (ParRedKS.hasType hΓ b2 h2.hasType.2) a3 b3
    | lamDF h1 h2 ih1 ih2 =>
      intro hΓ
      obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
      obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 ⟨hΓ, _, h1.hasType.1⟩
      have b2' := ParRedKS.defeqDFC hΓ (.succ .zero h1) h2.hasType.2 b2
      have := (ParRedKS.defeq hΓ a1 h1.hasType.1).symm
      exact mk (.lamDF h1 h2) (.lam a1 b1) (.lam a2 b2') <|
        .lamDF this.symm (this.symm.transU_l henv hΓ (a3.defeq hΓ)) b3
    | forallEDF h1 h2 ih1 ih2 =>
      intro hΓ
      obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
      refine have hΓ' := ⟨hΓ, _, h1.hasType.1⟩; have ⟨_, _, _, _, b1, b2, b3⟩ := ih2 hΓ'; ?_
      have b2' := ParRedKS.defeqDFC hΓ (.succ .zero h1) h2.hasType.2 b2
      exact mk (.forallEDF h1 h2) (.forallE a1 b1) (.forallE a2 b2') <|
        .forallEDF (ParRedKS.defeq hΓ a1 h1.hasType.1) a3
          (ParRedKS.hasType hΓ' b1 h2.hasType.1) b3
    | defeqDF _ _ _ ih2 => exact fun hΓ => ih2 hΓ
    | beta h1 h2 ih1 ih2 =>
      intro hΓ
      refine have h := IsDefEq.beta h1 h2; mk h (.tail .rfl (.beta .rfl .rfl)) .rfl ?_
      exact .refl h.hasType.2
    | eta h1 ih1 =>
      intro hΓ
      have := h1.hasType.1
      exact .normalEq hΓ <| .etaL this <| .refl <| .app (this.weak henv) (.bvar .zero)
    | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
      intro hΓ
      exact .normalEq hΓ <| .proofIrrel h1.hasType.1 h2.hasType.1 h3.hasType.1
    | @extra _ _ Γ h1 h2 h3 =>
      intro hΓ
      have h := IsDefEq.extra (Γ := Γ) h1 h2 h3
      obtain ⟨Δ, L, R, p, r, m1, m2, e1, e2, a1, a2, a3, a4⟩ := extra_pat hΓ h1 h2 h3 (Γ := Γ)
      have hstep : ParRed (Δ.reverse ++ Γ) L R := a4 ▸ ParRed.extra a1 a2 a3 fun _ => .rfl
      have hlams := ParRed.lams (Δ := Δ) hstep
      rw [← e1, ← e2] at hlams
      exact mk h (.tail .rfl hlams.toK) .rfl (.refl h.hasType.2)
  intro Γ e₁ e₂ A hΓ H
  exact main H hΓ

/-! ## §4 Fired, not admired

Three instantiations and two consequences.  §4.3 is the non-degenerate one. -/

/-- **`ParRedKDiamond` dominates `EtaKDiamond` at every typed subject.**  `KEta.lean` names
`EtaKDiamond` as `ParRed.triangle`'s new residual; an `EtaK` step is a `ParRedK` step
(`ParRedK.keta_step`), so my residual implies its conclusion wherever the shared subject has a
type.  `EtaKDiamond` itself carries no typing premise, so this is the typed fragment and not the
whole statement -- stated that way deliberately rather than overclaimed. -/
theorem joins_of_parRedKDiamond_etaK (HD : ParRedKDiamond) {Γ : List VExpr} {e e₁ e₂ A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (he : Γ ⊢ e : A)
    (h1 : EtaK Γ e e₁) (h2 : EtaK Γ e e₂) : Joins Γ e₁ e₂ :=
  parRedKDiamond_toJ HD hΓ he (.keta_step h1) (.keta_step h2)

/-- **`CRStatementK` implies `KDiamondJ`.**  `KDiamondJoin.kDiamondJ_of_crK` takes exactly
`CRStatementK`'s conclusion's third conjunct, so the restated K-diamond is *downstream* of the
corrected confluence statement, not an input to it.  Note what this does **not** say: `KDiamond`
(nose-`NormalEq`) is refuted at `quotParams` (`quotParams_not_kDiamond`), and `CRStatementK` does
not imply that one. -/
theorem kDiamondJ_of_crStatementK (H : CRStatementK) : KDiamondJ :=
  kDiamondJ_of_crK fun hΓ h => (H hΓ h).2.2

/-- **THE CIRCLE, compiled.**  `KEta.lean` names `EtaKDiamond` as `ParRed.triangle`'s new
residual, i.e. as an *input* to a proof of `ParRedKDiamond` and hence of `CRStatementK`.  But
`KDiamondJoin.etaKDiamond_of_kDiamondJ_holes` derives `EtaKDiamond` from `KDiamondJ` (discharging
`PiDomAgreeK`/`EtaKBodyTyped`/`ParRedKSDomConv` in-tree at the price of the two injectivity
holes), and `kDiamondJ_of_crStatementK` above derives `KDiamondJ` from `CRStatementK`.  So

> the residual that `CRStatementK`'s proof needs is **implied by `CRStatementK`**.

That is not a contradiction; it is a statement about where the *external* input has to come from.
`KDiamondJoin.kDiamondJ_of_patMajorCanonicalJ` (`[propext, Quot.sound]`) is the break in the
circle: `PatMajorCanonicalJ` -- lemma M3 restated as joinability -- is a property of the **rule
table**, provable without any confluence, and it is the only place the chain touches ground. -/
theorem etaKDiamond_of_crStatementK (H : CRStatementK) : EtaKDiamond :=
  etaKDiamond_of_kDiamondJ_holes (kDiamondJ_of_crStatementK H)

/-! ### §4.1 `Verify/Typing/ConstSpine.lean`'s consumers, on the two hypotheses

`CRShape.lean` §4 re-ran them with `CRStatementK` as a hypothesis.  These discharge that
hypothesis, so the cone is the honest one: what the `ConstSpine` route costs if confluence is
rebuilt over `ParRedK`. -/

theorem IsDefEqU.constApp_forallE_false_ofHyps (HS : ParRedKStatement) (HD : ParRedKDiamond)
    {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr} (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.forallE A B) :=
  IsDefEqU.constApp_forallE_false_ofK (crStatementK_of HS HD) hΓ hc

theorem IsDefEqU.constApp_sort_false_ofHyps (HS : ParRedKStatement) (HD : ParRedKDiamond)
    {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel} (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.sort u) :=
  IsDefEqU.constApp_sort_false_ofK (crStatementK_of HS HD) hΓ hc

end VEnv

namespace VEnv

/-! ### §4.2 The witness instance — degenerate, and labelled as such -/

/-- `CRStatementK` holds at `refParams`.  **Vacuously**: `KStep` is empty there
(`refParams_no_kstep`), so `EtaK` is empty, `ParRedK` is `ParRed`, and both hypotheses reduce to
`ChurchRosser.lean`'s theorems.  Recorded as a consistency check only -- `KCanonical.lean`'s "why
there is no refutation" note applies verbatim. -/
theorem refParams_crStatementK : @CRStatementK refParams :=
  @crStatementK_of refParams refParams_parRedKStatement refParams_parRedKDiamond

/-! ### §4.3 `quotParams` — the non-degenerate instance, and the four instantiations
`CRShape.lean` §2.2 could only record

The previous round could not compile these: `Verify/Environment/Checker.lean:86` did not build at
`e4e01c6`, so `Verify/QuotAppParams` was un-loadable and `CRShape.lean` §2.2 recorded the four
instantiations verbatim instead.  **The tree builds at `ca04f43`** (`lake build`, 1656 jobs), so
they are compiled here, in the file that owns them, rather than by editing `CRShape.lean` and
enlarging its `Verify/` footprint (it cites exactly one `Verify/` module, the smallest of the
thirteen). -/

section
attribute [local instance] quotParams

/-- Compiled at last: the `K⁺`-under-an-`eta` step at `quotParams` is not a `NormalEq`. -/
theorem quotParams_not_kStepNormalEq : ¬ KStepNormalEq :=
  fun h => not_normalEq_redex_rhs (h qc0_wf quotParams_kstep_eta)

/-- Compiled at last: the proof-irrelevance escape clause is refuted at the real instance.
Conditional on the same two holes as `quotParams_not_crStatement`, whose argument list this is
verbatim -- **it must not be quoted as unconditional** (commit `a561fa9`). -/
theorem quotParams_not_crUpToProof : ¬ CRUpToProof :=
  not_crUpToProof_of_kstep (u := .zero) (t := .app (.bvar 3) (.bvar 1))
    qc0T_wf qc0_wf qAT0_isProp qLiftT0_hasType quotParams_kstep_eta nofun
    qLiftT0_not_proof (fun _ => qParRed_qLiftT) (fun _ => qParRed_qAT)
    (fun _ ho => qParRed_app_bvar (fun _ => qParRed_bvar) nofun ho)
    not_normalEq_redex_rhs

/-- Compiled at last: one `keta` step reaches the λ that `ParRed` cannot. -/
theorem quotParams_parRedK_qLiftT :
    ParRedK qc0T (qLiftT .zero (.succ .zero))
      (.lam (qAT .zero) (.app (.bvar 3) (.bvar 1))) :=
  .keta (.under qLiftT0_hasType (.here quotParams_kstep_eta)) .rfl

/-- **THE FIRING.**  At exactly the configuration where `CRStatement` is false, `CRDefEqK` holds
-- at `quotParams`, the one instance of the eight where `CRStatement` is refutable and the rule
is contractive (handoff §3.1). This is the instance the previous round could only record. -/
theorem quotParams_crDefEqK :
    CRDefEqK qc0T (qLiftT .zero (.succ .zero))
      (.lam (qAT .zero) (.app (.bvar 3) (.bvar 1))) :=
  crDefEqK_of_kstep qc0_wf qAT0_isProp qLiftT0_hasType quotParams_kstep_eta

/-- **And `ParRedKDiamond`'s conclusion holds at the very pair that refutes `KDiamond`.**
`quotParams_not_kDiamond` refutes the nose-`NormalEq` diamond with the reducts
`g x` / `g ((fun y => y) x)`; `quotParams_kDiamond_joinable` joins them in one β-step and its
right leg is a **single** `ParRedK` step, so the pair also satisfies the *single-step-legged*
shape my residual asks for.  So the standing refutation of `KDiamond` does **not** transfer to
`ParRedKDiamond`, and the single-step legs of §1 are not an overreach at the one witness that
kills the nose form. -/
theorem quotParams_parRedKDiamond_at_kDiamond_witness :
    ∃ e₁' e₂', ParRedK qc1 (.app (.bvar 3) (.bvar 1)) e₁' ∧
      ParRedK qc1 (.app (.bvar 3) qXbeta) e₂' ∧ NormalEq qc1 e₁' e₂' :=
  ⟨_, _, .rfl, .app .bvar (.beta .bvar .bvar), .refl (qT_gx qT_x)⟩

end

end VEnv

end Lean4Lean
