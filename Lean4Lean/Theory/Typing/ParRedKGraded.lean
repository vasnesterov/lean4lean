import Lean4Lean.Theory.Typing.KKetaRow

/-!
# The eight non-`keta` rows, restated over `ParRedKn` -- `AppKetaRow` discharged

`KKetaRow.lean` builds the grading `ParRedKn` (redex-nesting height), proves the two
invariance facts the eta rows need (`ParRedKn.weakN`, `ParRedKn.app_bvar`), and proves the
`appDF` x `keta` row as an **induction step**: `ketaRow_of_weakNInvDS` needs site 7 only at
grade `N` while the row's own derivation has grade `N+1`.  What it left open, explicitly as a
conjecture rather than a theorem, was this:

> Doing so means restating the eight non-`keta` rows of `KSite7`/`KSite7App`/`KSite7Rows` over
> `ParRedKn`.  That is expected to be mechanical -- inspection says each of those proofs uses
> its induction hypotheses only at derivations built from the case's own premises by
> congruences and `ParRedKn.rfl`, so of grade `≤ N` -- but the expectation is **not
> machine-checked here**.

This file machine-checks it.  The conjecture is **true, row by row**, and in a sharper form
than stated: at the fixed grade bound `M`, every non-`keta` row uses its induction hypotheses
at grade `≤ M` -- the *same* bound, not a smaller one -- because

* the congruence rows (`app`, `lam`, `forallE`) have premises at the same grade as their
  conclusion, by the uniform grading;
* the redex rows (`beta`, `extra`) have premises at grade `n` with conclusion at `n+1`, so
  their premises are *below* the bound and reach it by `ParRedKn.mono`;
* `etaL`/`etaR` move the derivation by `ParRedKn.app_bvar` and `ParRedKn.weakN`, which are
  grade-preserving -- the one non-mechanical ingredient, already proved in `KKetaRow.lean`.

Only `keta` needs the *strictly smaller* bound, and that is the outer induction on `N`.

## What is new here, and what is reused

`NormalEq.appDF_extra_of_descendVK` is 145 lines and would have been the one genuinely
expensive duplication.  It is not duplicated: `KSite7App.lean`'s body was abstracted over the
development relation (`NormalEq.appDF_extra_of_descendVK'`, `develop_of_matches`), which needed
exactly three closure properties -- `hRs` (soundness into `ParRedK`, for the two `hasType`
calls and the `Check.OK.congr_defeq`), `hRc` (`const` reflexivity) and `hRa` (`app`
congruence).  `ParRedKn n Γ` has all three **at the same `n`**, so the graded row is a one-line
instantiation (`NormalEq.appDF_extra_of_parRedKn`).  That instantiation *is* the proof of the
conjecture for that row, and it is the strongest form of it: the body is literally the same
term.

The other seven rows are short and are restated with their original bodies, with `ParRedK`
replaced by `ParRedKn M` in the hypothesis positions and `.toParRedK` inserted at the places
that only need admissibility (`hasType`, `defeq`).  `ParRedKn.defeqDFC` is the one further
piece of graded infrastructure needed (`lamDF` and `forallEDF` transport their second premise
across a context conversion); it is `ParRedK.defeqDFC` with the index threaded, and it is
grade-preserving for the same reason `weakN` is.

## The result

`parRedKStatementN_succ` : `WeakNInvDS → ParRedKStatementN N → ParRedKStatementN (N+1)`,
hence `parRedKStatementN_all` : `WeakNInvDS → ∀ N, ParRedKStatementN N` (base
`KKetaRow.parRedKStatementN_zero`, which is unconditional), hence

  `parRedKStatement_of_weakNInvDS` : `WeakNInvDS → ParRedKStatement`.

So `AppKetaRow` is **discharged**: `KSite7Rows.parRedKStatement_of_rows`' second hypothesis is
gone, and site 7 for `ParRedK` costs `WeakNInvDS` alone.  `appKetaRow_of_weakNInvDS` states
that consequence in `AppKetaRow`'s own shape.

Honesty about what this does *not* do: `WeakNInvDS` is still a hypothesis, and site 7 still
reaches `IsDefEqU.weakN_iff` -- through **exactly one** row, `appDF` x `beta`, and inside it
through `ChurchRosser.ParRedExt.parRed_beta`.  See the measurement section at the foot of the
file, and `KSite7Rows.lean`'s note that discharging `WeakNInvDS` brings a second entry back.

And the vacuity note that belongs with every result in this cluster: `EtaK` has no witness at
`refParams` or at any other `Params` instance in this tree, so *at those instances* site 7 was
already known (`KSite7.refParams_parRedKStatement`) and everything here is vacuously true of
them.  What is not vacuous is the shape of the general statement: `AppKetaRow` was a genuine
second assumption -- `KSite7Rows.appKetaRow_of_parRedKStatement` shows it is exactly as strong
as site 7, so assuming it was assuming the conclusion -- and it is now gone.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## Graded infrastructure

`hasType` and `defeq` are not needed in graded form -- they are properties of the *pair*
`(e, e')`, not of the derivation, so `ParRedKn.toParRedK` suffices.  `defeqDFC` is different:
it rebuilds a derivation, so its grade behaviour is a real fact and has to be proved. -/

/-- **Invariance fact 3: context conversion keeps the grade.**  `ParRedK.defeqDFC`'s proof with
the index threaded.  Every congruence keeps its index and every redex constructor keeps its own
`+1`, exactly as in `ParRedKn.weakN`. -/
theorem ParRedKn.defeqDFC {n : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr} {e1 e2 A : VExpr}
    (hΓ₀ : OnCtx Γ₀ (IsType env univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : ParRedKn n Γ₁ e1 e2) : ParRedKn n Γ₂ e1 e2 := by
  induction H generalizing Γ₂ A with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv (W.isType' hΓ₀)
    exact .lam (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (W.succ hA) hB)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv (W.isType' hΓ₀)
    exact .beta (ih1 (W.succ hA) hb) (ih2 W ha)
  | extra h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => h.defeqDFC henv W) fun a =>
      let ⟨_, hh⟩ := h2.hasType (W.isType' hΓ₀) h a; ih a W hh
  | keta hek _ ih =>
    exact .keta (hek.defeqDFC hΓ₀ W)
      (ih W (hek.defeqU (W.isType' hΓ₀) |>.of_l henv (W.isType' hΓ₀) h |>.hasType.2))

/-- `parRedK_of_matches` at the graded relation.  The instance of `develop_of_matches`
(`KSite7App.lean`) at `R := ParRedKn n Γ`: the two closure properties it asks for are
`ParRedKn.const` and `ParRedKn.app`, both at the **same** grade `n`. -/
theorem parRedKn_of_matches {n : Nat} {Γ : List VExpr} {q : Pattern} {g : VExpr}
    {m1 : q.LPath → List VLevel} {m2 m2' : q.Path → VExpr}
    (hm : q.Matches g m1 m2) (hr : ∀ x, ParRedKn n Γ (m2 x) (m2' x)) :
    ∃ g', ParRedKn n Γ g g' ∧ q.Matches g' m1 m2' :=
  develop_of_matches (R := ParRedKn n Γ) .const .app hm hr

/-! ## The rows, graded

Each row is stated at a fixed bound `M`, with both its induction hypotheses and its `ParRedKn`
premises at `M`.  That is the shape the inner induction supplies: the induction is on
`H1 : NormalEq` at a fixed grade bound, so the hypotheses are available at every grade `≤ M`,
and `ParRedKn.mono` moves a `beta`/`extra` premise (grade `N`, conclusion `N+1 = M`) up to it.
-/

/-- Site 7's `appDF` x congruence row, graded.  `KSite7App.NormalEq.appDF_app_of_parRedK`'s
body; the two `hasType` appeals go through `ParRedKn.toParRedK`. -/
theorem NormalEq.appDF_app_of_parRedKn {M : Nat} {Γ : List VExpr} {f A B f₂ a b f' b' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, ParRedKn M Γ f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedKn M Γ b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (r1 : ParRedKn M Γ f₂ f') (r2 : ParRedKn M Γ b b') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ .app f' b' :=
  let ⟨_, a1, a2⟩ := ih1 r1
  let ⟨_, b1, b2⟩ := ih2 r2
  ⟨_, a1.app b1,
    .appDF (a1.hasType hΓ l1) (r1.toParRedK.hasType hΓ l2)
      (b1.hasType hΓ l3) (r2.toParRedK.hasType hΓ l4) a2 b2⟩

/-- Site 7's `lamDF` row, graded.  `KSite7App.NormalEq.lamDF_of_parRedK`'s body; the one
derivation-rebuilding step is `ParRedKn.defeqDFC`, which keeps the grade. -/
theorem NormalEq.lamDF_of_parRedKn {M : Nat} {Γ : List VExpr}
    {A A₁ A₂ body₁ body₂ : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ A ≡ A₁ : .sort u) (l2 : Γ ⊢ A ≡ A₂ : .sort u)
    (l3 : (A::Γ) ⊢ body₁ ≡ₚ body₂)
    (ih1 : ∀ {e₂'}, ParRedKn M (A::Γ) body₂ e₂' →
      ∃ e₁', ParRedKS (A::Γ) body₁ e₁' ∧ NormalEq (A::Γ) e₁' e₂')
    {e₂' : VExpr} (H2 : ParRedKn M Γ (.lam A₂ body₂) e₂') :
    ∃ e₁', ParRedKS Γ (.lam A₁ body₁) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  cases H2 with
  | lam r1 r2 =>
    refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩); have ⟨_, h1⟩ := l3.defeq hΓ'; ?_
    have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
    replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
    let ⟨_, b1, b2⟩ := ih1 r2
    exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
      .lamDF l1 (.trans l2 (r1.toParRedK.defeq hΓ
        (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
  | extra _ r2 => cases r2
  | keta hek _ => exact absurd hek EtaK.not_lam

/-- Site 7's `forallEDF` row, graded.  `KSite7App.NormalEq.forallEDF_of_parRedK`'s body. -/
theorem NormalEq.forallEDF_of_parRedKn {M : Nat}
    {Γ : List VExpr} {A A₁ A₂ B₁ B₂ : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ A ≡ A₁ : .sort u) (l2 : Γ ⊢ A₁ ≡ₚ A₂)
    (l3 : (A::Γ) ⊢ B₁ : .sort v) (l4 : (A::Γ) ⊢ B₁ ≡ₚ B₂)
    (ih1 : ∀ {e₂'}, ParRedKn M Γ A₂ e₂' → ∃ e₁', ParRedKS Γ A₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedKn M (A::Γ) B₂ e₂' →
      ∃ e₁', ParRedKS (A::Γ) B₁ e₁' ∧ NormalEq (A::Γ) e₁' e₂')
    {e₂' : VExpr} (H2 : ParRedKn M Γ (.forallE A₂ B₂) e₂') :
    ∃ e₁', ParRedKS Γ (.forallE A₁ B₁) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  cases H2 with
  | forallE r1 r2 =>
    let ⟨_, a1, a2⟩ := ih1 r1
    refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩)
      have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ'); ?_
    have W := l1.transU_l henv hΓ (l2.defeq hΓ)
    replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
    let ⟨_, b1, b2⟩ := ih2 r2
    have := r1.toParRedK.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
    exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
      .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2
        (b1.hasType hΓ' l3) b2⟩
  | extra _ r2 => cases r2
  | keta hek _ => exact absurd hek EtaK.not_forallE

/-- **Site 7's `etaL` row, graded** -- one of the two rows the grading exists for.
`KSite7Rows.NormalEq.etaL_of_parRedK`'s body, with `.app (H2.weakN .one) .bvar` replaced by
`ParRedKn.app_bvar H2`, which is the *same term* and is where the uniform grading pays: the
derivation gains an `app` node and a lift, and the grade does not move. -/
theorem NormalEq.etaL_of_parRedKn {M : Nat} {Γ : List VExpr} {A B e e' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ e' : .forallE A B)
    (ih1 : ∀ {x : VExpr}, ParRedKn M (A::Γ) (.app e'.lift (.bvar 0)) x →
      ∃ t, ParRedKS (A::Γ) e t ∧ NormalEq (A::Γ) t x)
    {e₂' : VExpr} (H2 : ParRedKn M Γ e' e₂') :
    ∃ e₁', ParRedKS Γ (.lam A e) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' :=
  let ⟨t, a1, a2⟩ := ih1 H2.app_bvar
  ⟨.lam A t, ParRedKS.lam .rfl a1, .etaL (H2.toParRedK.hasType hΓ l1) a2⟩

/-- Site 7's `appDF` x `beta` row, graded.  `KSite7Rows.NormalEq.appDF_beta_of_parRedK`'s body.
The induction hypothesis is used at `.lam ParRedKn.rfl r1`, grade `M`, while the row's own
derivation is `ParRedKn.beta r1 r2` at grade `M+1` -- so this row would have worked with the
*strictly smaller* bound too.  It is stated at `M` because that is what the assembly hands it
(via `ParRedKn.mono`) and because a uniform bound keeps the eight rows uniform. -/
theorem NormalEq.appDF_beta_of_parRedKn {M : Nat} {Γ : List VExpr}
    {f A B a b A₀ eb : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ .lam A₀ eb : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {x : VExpr}, ParRedKn M Γ (.lam A₀ eb) x →
      ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    (ih2 : ∀ {x : VExpr}, ParRedKn M Γ b x → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    {eb' b' : VExpr} (r1 : ParRedKn M (A₀::Γ) eb eb') (r2 : ParRedKn M Γ b b') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ eb'.inst b' := by
  let ⟨f', a1, a2⟩ := ih1 (.lam .rfl r1)
  let ⟨a', b1, b2⟩ := ih2 r2
  let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
  let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
  refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.toParRedK.hasType hΓ' (u2.defeq d2); ?_
  replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
  let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta hΓ a2
    (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
  exact ⟨_, (ParRedKS.app a1 b1).trans h1.toK,
    h2.trans hΓ (.instN_r hΓ' l3 b2 .zero d2)⟩

/-- **Site 7's `appDF` x `extra` row, graded, with no duplicated body.**  This is
`KSite7App.NormalEq.appDF_extra_of_descendVK'` -- the 145-line proof, abstracted over its
development relation -- instantiated at `ParRedKn M Γ`.  Its three requirements are met at the
*same* grade `M`:

* `hRs` = `ParRedKn.toParRedK` (admissibility only, no grade content),
* `hRc` = `ParRedKn.const`, `hRa` = `ParRedKn.app`, both grade-preserving by the uniform
  grading of the congruences.

So for this row the grade-`≤ M` conjecture is not merely checked, it is *the same proof term*
as the ungraded row. -/
theorem NormalEq.appDF_extra_of_parRedKn {M : Nat} {Γ : List VExpr} {f A B a b f₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, ParRedKn M Γ f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedKn M Γ b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'}
    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
    (r3 : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd)
    (r4 : ∀ x, ParRedKn M Γ (m2 x) (m2' x)) :
    ∃ e₁', ParRedKS Γ (f.app a) e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst :=
  NormalEq.appDF_extra_of_descendVK' (R := ParRedKn M Γ)
    ParRedKn.toParRedK .const .app hΓ l1 l2 l3 l4 ih1 ih2 r1 r2 r3 r4

/-- **Site 7's `etaR` row, graded** -- the other row the grading exists for.
`KKetaRow.etaR_case_clean`'s body verbatim (so it inherits being clean of
`IsDefEqU.weakN_iff`), with `ParRedK` replaced by `ParRedKn M` in the two premise positions and
`.toParRedK` inserted at the three admissibility appeals.  The induction hypothesis is used at
`r2`, a premise, so at grade `M`. -/
theorem etaR_case_cleanN (HD : WeakNInvDS) {M : Nat} {Γ : List VExpr}
    {A B e eb A' b' : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ e : .forallE A B) (l2 : NormalEq (A::Γ) (.app e.lift (.bvar 0)) eb)
    (ih1 : ∀ {x : VExpr}, ParRedKn M (A::Γ) eb x →
      ∃ t, ParRedKS (A::Γ) (.app e.lift (.bvar 0)) t ∧ NormalEq (A::Γ) t x)
    (r1 : ParRedKn M Γ A A') (r2 : ParRedKn M (A::Γ) eb b') :
    ∃ e₁', ParRedKS Γ e e₁' ∧ NormalEq Γ e₁' (.lam A' b') := by
  obtain ⟨⟨uA, hA⟩, vB, hB⟩ := (have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hb0 : (A::Γ) ⊢ VExpr.app e.lift (.bvar 0) : B := by
    simpa [instN_bvar0] using HasType.app (l1.weak (B := A) henv) (.bvar .zero)
  have hebty : (A::Γ) ⊢ eb : B := HasType.defeqU_l henv hΓA (l2.defeq hΓA) hb0
  have hlamty : Γ ⊢ VExpr.lam A eb : .forallE A B := hA.lam hebty
  obtain ⟨t, a1, a2⟩ := ih1 r2
  rcases etaR_inner HD hΓ hA hB l1 a1 with
    ⟨A₂, c, hred, hA₂, dc⟩ | ⟨e', f₀, hred, rfl, df⟩ | hpe
  · exact ⟨.lam A₂ c, hred, .lamDF (hA₂.of_r henv hΓ hA).symm (r1.toParRedK.defeq hΓ hA)
      ((dc.symm hΓA).trans_normalEq hΓA a2)⟩
  · have he'ty : Γ ⊢ e' : .forallE A B := ParRedKS.hasType hΓ hred l1
    have he'l2 := he'ty.weak (B := A) henv
    simp only [VExpr.liftN] at he'l2
    have hf₀ty := DomEq.hasType hΓA (df.symm hΓA) he'l2
    have Dsub : DomEq (A::Γ) (.app e'.lift (.bvar 0)) (.app f₀ (.bvar 0)) :=
      .appDF he'l2 hf₀ty (.bvar .zero) (.bvar .zero) (df.symm hΓA) (.refl (.bvar .zero))
    refine ⟨e', hred, ?_⟩
    exact (NormalEq.etaR he'ty (Dsub.trans_normalEq hΓA a2)).trans_domEq hΓ
      (.lamDF hA (r1.toParRedK.defeq hΓ hA) (.refl (r2.toParRedK.hasType hΓA hebty)))
  · obtain ⟨P, hP, he1, -⟩ := hpe
    refine ⟨e, .rfl, .proofIrrel hP he1 ?_⟩
    have hlam' : Γ ⊢ VExpr.lam A' b' : .forallE A B :=
      (ParRedK.lam r1.toParRedK r2.toParRedK).hasType hΓ hlamty
    exact HasType.defeqU_r henv hΓ (l1.uniqU henv hΓ he1) hlam'

/-! ## The assembly: site 7 by induction on the grade

The outer induction is on the grade bound `N`; the inner one is `KSite7Rows`' own induction on
`H1 : NormalEq`, run at the fixed bound `N+1`.  Every row above is used at that bound, with
`ParRedKn.mono` supplying it for the `beta` and `extra` premises (which arrive at `N`).  The
`keta` row is the only one that uses the *outer* hypothesis, and it uses it at `N`, which is
exactly the grade `ParRedKn.keta`'s tail premise has. -/

/-- **The induction step.**  Site 7 at grade `N+1` from site 7 at grade `N`, against
`WeakNInvDS` alone.  No `AppKetaRow`. -/
theorem parRedKStatementN_succ (HD : WeakNInvDS) {N : Nat} (S : ParRedKStatementN N) :
    ParRedKStatementN (N+1) := by
  suffices H : ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      OnCtx Γ (IsType env univs) → ∀ {e₂' : VExpr}, ParRedKn (N+1) Γ e₂ e₂' →
      ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' from
    fun _ _ _ _ _ hn hΓ H1 H2 => H H1 hΓ (H2.mono hn)
  intro Γ e₁ e₂ H1
  induction H1 with
  | refl l1 => exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.refl l1) H2.toParRedK
  | sortDF l1 l2 l3 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.sortDF l1 l2 l3) H2.toParRedK
  | constDF l1 l2 l3 l4 l5 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.constDF l1 l2 l3 l4 l5) H2.toParRedK
  | proofIrrel l1 l2 l3 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.proofIrrel l1 l2 l3) H2.toParRedK
  | appDF l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    intro hΓ e₂' H2
    cases H2 with
    | app r1 r2 => exact NormalEq.appDF_app_of_parRedKn hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2
    | beta r1 r2 =>
      exact NormalEq.appDF_beta_of_parRedKn hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ)
        (r1.mono (Nat.le_succ _)) (r2.mono (Nat.le_succ _))
    | extra r1 r2 r3 r4 =>
      exact NormalEq.appDF_extra_of_parRedKn hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2 r3
        (fun x => (r4 x).mono (Nat.le_succ _))
    | keta hek htail =>
      exact ketaRow_of_weakNInvDS HD S hΓ (.appDF l1 l2 l3 l4 l5 l6) hek htail
  | lamDF l1 l2 l3 ih1 =>
    exact fun hΓ _ H2 =>
      NormalEq.lamDF_of_parRedKn hΓ l1 l2 l3 (ih1 ⟨hΓ, _, l1.hasType.1⟩) H2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    exact fun hΓ _ H2 =>
      NormalEq.forallEDF_of_parRedKn hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 ⟨hΓ, _, l1.hasType.1⟩) H2
  | etaL l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    exact NormalEq.etaL_of_parRedKn hΓ l1 (ih1 ⟨hΓ, _, hA⟩) H2
  | etaR l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    cases H2 with
    | lam r1 r2 => exact etaR_case_cleanN HD hΓ l1 l2 (ih1 ⟨hΓ, _, hA⟩) r1 r2
    | extra _ r2 => cases r2
    | keta hek _ => exact absurd hek EtaK.not_lam

/-- Site 7 at every grade, from `WeakNInvDS` alone.  Base: `parRedKStatementN_zero`, which is
unconditional. -/
theorem parRedKStatementN_all (HD : WeakNInvDS) : ∀ N, ParRedKStatementN N
  | 0 => parRedKStatementN_zero
  | N+1 => parRedKStatementN_succ HD (parRedKStatementN_all HD N)

/-- **Site 7 for `ParRedK`, from `WeakNInvDS` alone.**  `AppKetaRow` is discharged. -/
theorem parRedKStatement_of_weakNInvDS (HD : WeakNInvDS) : ParRedKStatement :=
  parRedKStatement_of_graded (parRedKStatementN_all HD)

/-- `AppKetaRow` itself, discharged.  Compare `KSite7Rows.appKetaRow_of_parRedKStatement`,
which is the trivial direction; this is the one that was open. -/
theorem appKetaRow_of_weakNInvDS (HD : WeakNInvDS) : AppKetaRow :=
  appKetaRow_of_parRedKStatement (parRedKStatement_of_weakNInvDS HD)

/-- And `KSite7Rows.parRedKStatement_of_rows` with its second hypothesis removed. -/
theorem parRedKStatement_of_rows_one_hyp (HD : WeakNInvDS) : ParRedKStatement :=
  parRedKStatement_of_rows HD (appKetaRow_of_weakNInvDS HD)

/-! ## Measurement

Cones measured with `scripts/hole-cone.lean`'s `deps` walk (`allowOpaque := true`), on the
commit that introduced this file.  Holes listed are the declarations in the cone that themselves
mention `sorryAx`; `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS` are the tree's
two ambient ones and appear everywhere `NormalEq` does.

| declaration | cone | holes beyond the two ambient |
| --- | --- | --- |
| `develop_of_matches` | 151 | -- |
| `parRedKn_of_matches` | 156 | -- |
| `ParRedKn.defeqDFC` | 3546 | -- (not even `rigidShapeUniqNS`) |
| `NormalEq.appDF_app_of_parRedKn` | 3696 | -- |
| `NormalEq.lamDF_of_parRedKn` | 3771 | -- |
| `NormalEq.forallEDF_of_parRedKn` | 3772 | -- |
| `NormalEq.etaL_of_parRedKn` | 3740 | -- |
| `NormalEq.appDF_extra_of_parRedKn` | 4001 | -- |
| `etaR_case_cleanN` | 3926 | -- |
| **`NormalEq.appDF_beta_of_parRedKn`** | 3934 | **`IsDefEqU.weakN_iff`** |
| `parRedKStatementN_zero` (`KKetaRow`) | 683 | -- |
| `ketaRow_of_weakNInvDS` (`KKetaRow`) | 4100 | -- |
| `parRedKStatementN_succ` | 4303 | `IsDefEqU.weakN_iff` |
| `parRedKStatement_of_weakNInvDS` | 4316 | `IsDefEqU.weakN_iff` |

**Seven of the eight non-`keta` rows are clean of `weakN_iff`, and so is the `keta` row.**  The
single entry is `appDF` x `beta`, and it is `ParRedExt.parRed_beta`'s (cone 3875, carries
`weakN_iff`).

Two claims that circulated with this cluster and that the table refutes:

* *`NormalEq.descendV` reaches `weakN_iff` through `DescentLam.beta → DescentLam.instN →
  NormalEq.trans`.*  It does **not**, now: `NormalEq.descendV` measures cone 3839 with only the
  two ambient holes, which is why `NormalEq.appDF_extra_of_parRedKn` is clean.  (This is
  `KSite7Rows.lean`'s own correction, one round later than the ledger paragraph that states it.)
* *`etaR` is one of the two rows carrying `weakN_iff`.*  It was; `KSite7.etaR_case` now measures
  cone 3914, clean, because the `DomEq.trans_normalEq` / `NormalEq.trans_domEq` substitution is
  landed in `KSite7.lean` itself.  `etaR_case_at_kstep` (cone 3916) is clean with it.

### Where the last entry actually sits

`ParRedExt.parRed_beta` touches `weakN_iff` in four places (`ChurchRosser.lean` lines 1407,
1438, 1467, 1469).  Three of them (1407, 1467, 1469) are *typing-half* strengthenings -- `∃ B,
(A::Γ) ⊢ e.lift : B → ∃ B', Γ ⊢ e : B'` and its `IsType` variant -- i.e. they would be
discharged by `TypingStrengthening` alone (`StrengthenNarrow.lean`'s
`TypingStrengthening.hasType_weakN_iff`), the half `scripts/weakn-gate-split.lean` measures as
sufficient for **43** of `IsDefEqU.weakN_iff`'s 296 users -- **46** once the tenth gate
(`hasType_app_bvar0`) is cut; see `docs/handoff-weakn.md` §5.3 for the split and for why the
"18" this paragraph used to quote was a pre-fix undercount (that figure predates the
internal-names fix to the measurement scripts, and it was never about `descend` at all).
The fourth, line 1438, is a `NormalEq.trans` with a
general `NormalEq` on **both** sides, so the `DomEq`-narrowing that cleaned `etaR` does not
apply to it.  **That reading was flagged "inspection, not machine-checked", and it has since
been refuted** -- `Theory/Typing/CRBetaGen.lean`'s `ParRedExt.parRed_beta_gen` does the same
proof carrying the argument mismatch in the *statement* (via `NormalEq.instN₂`), and
`NormalEq.trans` / `NormalEq.weakN_iff` / `NormalEq.weakN_inv_DFC` all leave the cone
(3875 -> 3847).  `docs/vacuity-ledger.md` row 59 has the measurement; the paragraph above is
retained only as the record of what the inspection claimed.
-/

end VEnv
end Lean4Lean
