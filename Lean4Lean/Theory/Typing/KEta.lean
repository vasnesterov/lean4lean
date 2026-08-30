import Lean4Lean.Theory.Typing.KCanonical

/-!
# `EtaK`: the η-guarded K step, and why the confluence *statement* did not have to change

`Theory/Typing/KCanonical.lean` machine-checks two refutations:

* `VEnv.not_crStatement_of_kstep` -- `IsDefEq.church_rosser`'s statement, verbatim, is
  **false** at any `Params` instance registering the ι-rule of a large-eliminating
  subsingleton (`Eq`);
* `VEnv.not_parRedStatement_of_hK` -- `hK` (the K-rule as a `ParRed` step) refutes
  `NormalEq.parRed`, axiom-clean.

Both witnesses are the *same* configuration: a recursor **one argument short** of its
ι-pattern, so `ParRed`-normal, whose η-expansion `.app e.lift (.bvar 0)` *is* a K-redex.
`IsDefEq` reaches the λ (η, then `KStep.defeq` under the binder); the reduction relation
cannot follow, because `e` itself is not a redex; and `NormalEq`'s only route to a λ is
`etaR`, which asks for the K-redex to be `NormalEq` to its own contractum.

`docs/design-inductive.md` §7.6's second warning offered two repair directions: grow
`NormalEq`, or grow `ParRedS` by an eta-expansion.  **This file takes the second, in a
guarded form**, and the reason is a measurement, not a preference -- see
`docs/handoff-krule.md` §T2 (the consumer audit).  Growing `NormalEq` breaks the descent:
`NormalEq.descendV` recurses against a pattern that the *right* endpoint matches, and a
K-closure on the right endpoint destroys that match with no sub-derivation to recurse on.
Growing the reduction relation costs nothing there, because `descendV` and
`NormalEq.appDF_extra_of_descendV` **case only on `NormalEq`** and **build** `ParRedS`,
which is a positive occurrence.

## The step

`EtaK Γ e e'` says: `e` η-expands under some number of binders until the expansion is a
K-redex, which then fires.  It is *not* general η-expansion -- the recursion has to bottom
out in `EtaK.here`, an actual `KStep` -- so there are no infinite η-towers and the relation
is empty wherever `KStep` is (`refParams_no_etaK`).

```
| here  : KStep Γ e t → ParRed Γ t t' → EtaK Γ e t'
| under : Γ ⊢ e : ∀A.B → EtaK (A::Γ) (e.lift (.bvar 0)) t → EtaK Γ e (.lam A t)
```

`here` subsumes `hK` (`HasEtaK.hK`), so the one hypothesis `HasEtaK` replaces the two the
design would otherwise need.  More than one binder is genuinely reachable: `Acc.rec C F`,
short of both its index and its major premise, has
`Acc.intro x (fun y hy => Acc.inv h hy)` well-typed with `x` a *bound* variable.

## What is checked here

* **Admissibility** (`EtaK.defeqU`): every `EtaK` step is already an `IsDefEqU`, so adding it
  to `ParRed` leaves `IsDefEq` -- and therefore `kernel_sound`'s statement -- untouched.  Its
  `under` case is literally the derivation `not_crStatement_of_kstep` builds to *refute* the
  old relation; the repair is that same derivation, moved into the relation.
* **The kill** (`not_crStatement_of_kstep_inapplicable`,
  `not_parRedStatement_of_hK_inapplicable`): each refutation's own hypothesis list becomes
  *contradictory* under `HasEtaK`.  Neither statement had to be restated -- `CRStatement` and
  `ParRedStatement` are unchanged `Prop`s; what changed is the relation they quantify over.
* **The consumer kit** (`EtaK.matches_head`, `EtaK.spineHead_const`, `EtaK.not_lam`,
  `EtaK.not_forallE`, `EtaK.not_sort`): the three lemmas in `Verify/Typing/ConstSpine.lean`
  that *case on* `ParRed` need one new case each, and these are what discharges them.
* **`hK` discharged** (`HasEtaK.hK`): `NormalEq.appDF_extra_of_descendV`'s only hypothesis.
* **Non-vacuity** (`EtaK.eta_stuck_fires`) and **consistency** (`refParams_hasEtaK`), with
  the standing warning that a vacuous witness is not evidence.

## What is *not* done

`ParRed` gains no constructor here.  Landing it edits `ChurchRosser.lean` (this stream's
file) *and* `Verify/Typing/ConstSpine.lean` (which is not), so the constructor is stated and
its consumer obligations are proved, and the edit is handed over.  See
`docs/handoff-krule.md` §T5.
-/

namespace Lean4Lean

open VExpr

/-- Lifting does not move the head constant. -/
theorem VExpr.headConst?_liftN : ∀ {n : Nat} (e : VExpr) (k : Nat),
    (e.liftN n k).headConst? = e.headConst?
  | _, .bvar _, _ | _, .sort _, _ | _, .const _ _, _ | _, .forallE _ _, _ => rfl
  | _, .app f _, k => VExpr.headConst?_liftN f k
  | _, .lam _ b, k => VExpr.headConst?_liftN b (k+1)

/-- Lifting commutes with taking the head of an application spine. -/
theorem VExpr.spineHead_liftN : ∀ {n : Nat} (e : VExpr) (k : Nat),
    (e.liftN n k).spineHead = (e.spineHead).liftN n k
  | _, .bvar _, _ | _, .sort _, _ | _, .const _ _, _
  | _, .forallE _ _, _ | _, .lam _ _, _ => rfl
  | _, .app f _, k => VExpr.spineHead_liftN f k

/-- A matched term is a constant-headed spine: `Pattern.Matches` has no `.lam` case. -/
theorem Pattern.Matches.spineHead_const {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : ∃ c ls, e.spineHead = .const c ls := by
  induction H with
  | const => exact ⟨_, _, rfl⟩
  | var _ ih => exact ih
  | app _ _ ih1 _ => exact ih1

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-- **The η-guarded K step.**  `e` is η-expanded under `k ≥ 0` binders until the expansion is
a registered K-redex; the redex then fires, and its contractum reduces in parallel.

`here` with `t' = t` is the plain K-rule (`HasEtaK.hK`); `under` is what the old relation was
missing, and is exactly the configuration `not_crStatement_of_kstep` exploits. -/
inductive EtaK : List VExpr → VExpr → VExpr → Prop where
  | here {Γ : List VExpr} {e t t' : VExpr} :
      KStep Γ e t → ParRed Γ t t' → EtaK Γ e t'
  | under {Γ : List VExpr} {e A B t : VExpr} :
      HasType env univs Γ e (.forallE A B) →
      EtaK (A::Γ) (.app e.lift (.bvar 0)) t → EtaK Γ e (.lam A t)

/-- **The closure condition on `ParRed`.**  This is the single hypothesis that replaces
`KDescend.lean`'s `hK`; landing it is adding one constructor to `ParRed`. -/
def HasEtaK : Prop := ∀ {Γ : List VExpr} {e e' : VExpr}, EtaK Γ e e' → ParRed Γ e e'

/-- `HasEtaK` implies `hK`, `NormalEq.appDF_extra_of_descendV`'s only hypothesis. -/
theorem HasEtaK.hK (h : HasEtaK) {Γ : List VExpr} {a b : VExpr} (hst : KStep Γ a b) :
    ParRed Γ a b := h (.here hst .rfl)

/-! ## Shape: what an `EtaK` step can fire on -/

/-- **The redex of an `EtaK` step has a registered pattern's head.**  This is the fact
`Verify/Typing/ConstSpine.lean`'s `ParRed.constApp_inv` needs: it is stated in
`VExpr.headConst?` form rather than with `Pattern.headConst`, which is defined downstream. -/
theorem EtaK.matches_head {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    ∃ (p₁ p₂ : Pattern) (r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check)
      (f : VExpr) (m1 : p₁.LPath → List VLevel) (m2 : p₁.Path → VExpr),
      Params.Pat (Pattern.app p₁ p₂) r ∧ p₁.Matches f m1 m2 ∧
        e.headConst? = f.headConst? := by
  induction H with
  | @here _ e t t' hst _ =>
    cases hst with
    | mk hpat hm _ _ _ =>
      cases hm with
      | app hf _ => exact ⟨_, _, _, _, _, _, hpat, hf, rfl⟩
  | under _ _ ih =>
    obtain ⟨p₁, p₂, r, f, m1, m2, h1, h2, h3⟩ := ih
    exact ⟨p₁, p₂, r, f, m1, m2, h1, h2, by
      simpa [VExpr.headConst?, VExpr.headConst?_liftN] using h3⟩

/-- **An `EtaK` redex is a constant-headed spine.**  Unlike `matches_head` this survives
λ-peeling, so it is what excludes `EtaK` at a `.lam`, a `.forallE` and a `.sort`. -/
theorem EtaK.spineHead_const {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    ∃ c ls, e.spineHead = .const c ls := by
  induction H with
  | @here _ e t t' hst _ =>
    cases hst with
    | mk _ hm _ _ _ =>
      cases hm with
      | app hf _ => exact hf.spineHead_const
  | @under _ e A B t _ _ ih =>
    obtain ⟨c, ls, h⟩ := ih
    refine ⟨c, ls, ?_⟩
    have : (e.lift).spineHead = .const c ls := h
    rw [VExpr.spineHead_liftN] at this
    cases he : e.spineHead <;> rw [he] at this <;> simp [VExpr.liftN] at this
    · simp [this]

/-- `EtaK` never fires on a λ.  This is what makes `NormalEq.parRed`'s `etaR` case -- the one
`not_parRedStatement_of_hK` refutes -- **vacuous** for the new step. -/
theorem EtaK.not_lam {Γ : List VExpr} {A b e' : VExpr} : ¬ EtaK Γ (.lam A b) e' := by
  intro h; obtain ⟨_, _, hc⟩ := h.spineHead_const; exact nomatch hc

theorem EtaK.not_forallE {Γ : List VExpr} {A B e' : VExpr} : ¬ EtaK Γ (.forallE A B) e' := by
  intro h; obtain ⟨_, _, hc⟩ := h.spineHead_const; exact nomatch hc

theorem EtaK.not_sort {Γ : List VExpr} {u : VLevel} {e' : VExpr} : ¬ EtaK Γ (.sort u) e' := by
  intro h; obtain ⟨_, _, hc⟩ := h.spineHead_const; exact nomatch hc

theorem EtaK.not_bvar {Γ : List VExpr} {i : Nat} {e' : VExpr} : ¬ EtaK Γ (.bvar i) e' := by
  intro h; obtain ⟨_, _, hc⟩ := h.spineHead_const; exact nomatch hc

/-! ## Admissibility: the new step is already a definitional equality -/

/-- **Regularity of `EtaK`.**  Every η-guarded K step is an `IsDefEqU`, so adding it to
`ParRed` leaves `IsDefEq` -- and hence `Lean4Lean.kernel_sound`'s statement -- exactly where
it was.  This is `ParRed.defeq`'s new case.

The `under` branch is, line for line, the derivation `not_crStatement_of_kstep` builds in
order to *refute* the old relation (`(IsDefEq.eta he).symm.trans (.lamDF hA hbody)`).  That is
the whole repair: the equation the refutation exhibits is admitted as a reduction. -/
theorem EtaK.defeqU {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    OnCtx Γ (IsType env univs) → IsDefEqU env univs Γ e e' := by
  induction H with
  | @here Γ e t t' hst hpr =>
    intro hΓ
    obtain ⟨A, hd⟩ := KStep.defeq hΓ hst
    exact IsDefEqU.trans henv hΓ ⟨A, hd⟩ ⟨A, ParRed.defeq hΓ hpr hd.hasType.2⟩
  | @under Γ e A B t hty _ ih =>
    intro hΓ
    have ⟨⟨_, hA⟩, _, _⟩ := have ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv
    have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have hb0 := HasType.app (hty.weak henv) (.bvar .zero)
    simp [instN_bvar0] at hb0
    have hbody : IsDefEq env univs (A::Γ) (.app e.lift (.bvar 0)) t B :=
      (ih hΓA).of_l henv hΓA hb0
    exact ⟨_, ((IsDefEq.eta hty).symm).trans (.lamDF hA hbody)⟩

/-! ## Re-running the two refutations against the restatement

Neither `CRStatement` nor `ParRedStatement` is restated: they are the same `Prop`s, quantified
over a `ParRed` that now has one more constructor.  What the restatement does is make each
refutation's **own hypothesis list contradictory** -- the witness is visibly killed, rather
than merely no longer derivable.

Both proofs use exactly three of the refutation's hypotheses, and the one they contradict is
the *rigidity* of the witness: `e := Eq.rec α a C m a` is one argument short of the ι-pattern
and so is `ParRed`-normal in the old relation.  Under `HasEtaK` it is not normal at all --
it reduces to the very λ the refutation says nothing can reach. -/

/-- **`not_crStatement_of_kstep` is inapplicable.**  Its hypotheses `he`, `hstep`, `hlam`,
`hrig` are jointly contradictory once `ParRed` is closed under `EtaK`; the remaining seven
(`hΓ`, `hΓA`, `hA`, `hnp`, `hrigA`, `hrigT`, `hne`) are not even needed. -/
theorem not_crStatement_of_kstep_inapplicable (hE : HasEtaK)
    {Γ : List VExpr} {e A B t : VExpr}
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRed Γ e o → o = e) : False :=
  hlam A t (hrig _ (hE (.under he (.here hstep .rfl)))).symm

/-- **`not_parRedStatement_of_hK` is inapplicable**, and note it is `hrig`, not `hK`, that
dies: `HasEtaK` *supplies* `hK` (`HasEtaK.hK`).  §R3's diagnosis -- that the break was at
`ParRed.weakN_inv` -- and §S3's -- that it was at `NormalEq.parRed`'s `etaR` case -- are both
about a relation in which the witness is normal.  It is not. -/
theorem not_parRedStatement_of_hK_inapplicable (hE : HasEtaK)
    {Γ : List VExpr} {e A B t : VExpr}
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRedS Γ e o → o = e) : False :=
  hlam A t (hrig _ (ReflTransGen.tail .rfl (hE (.under he (.here hstep .rfl))))).symm

/-- And the `etaR` case of `NormalEq.parRed` that §S3 refutes is **vacuous** for the new step:
a λ is never an `EtaK` redex, so the configuration the refutation needs -- `e₂` a λ that
reduces -- cannot arise from `EtaK`.  (`ParRed.lam` still reduces λs; what cannot happen is
the *top-level* K-firing that the refutation turns into a `NormalEq` obligation.) -/
theorem EtaK.etaR_case_vacuous {Γ : List VExpr} {A b e' : VExpr}
    (H : EtaK Γ (.lam A b) e') : False := EtaK.not_lam H

/-! ## Non-vacuity, and consistency -/

/-- **Non-vacuity, against the measured hole.**  `HeadRedStuck.lean`'s `whnf_app_bvar` says
`.app f (.bvar i)` is weak-head normal at every `Params` instance.  `KStep.stuck_fires` shows
the *fully applied* such term is a K-redex.  This says the **under-applied** one is an `EtaK`
redex: `f` itself is weak-head normal, its η-expansion is weak-head normal, and `EtaK` still
fires -- which is the exact configuration the two refutations exploit. -/
theorem EtaK.eta_stuck_fires {Γ : List VExpr} {f A₀ B₀ t : VExpr}
    (hty : HasType env univs Γ f (.forallE A₀ B₀))
    (hstep : KStep (A₀::Γ) (.app f.lift (.bvar 0)) t)
    (hw : WHNF (A₀::Γ) f.lift) (hlam : ∀ A e, f.lift ≠ .lam A e) :
    WHNF (A₀::Γ) (.app f.lift (.bvar 0)) ∧ EtaK Γ f (.lam A₀ t) :=
  ⟨whnf_app_bvar hw hlam, .under hty (.here hstep .rfl)⟩

/-- `EtaK` is empty at the witness instance, because `KStep` is (`refParams_no_kstep`) and
every `EtaK` derivation bottoms out in a `KStep`.  Hence `HasEtaK` is a **consistent**
hypothesis, and -- the point that matters for §S1 -- `ParRed` at `refParams` is unchanged, so
`DescendRefute.lean`'s three refutations are untouched by the restatement.

**This is a consistency check, not evidence.**  No `Params` instance in this tree registers an
`.app` pattern, so nothing about the non-vacuous case is tested here. -/
theorem refParams_no_etaK {Γ e e'} : ¬ @EtaK refParams Γ e e' := by
  intro h
  induction h with
  | here hst _ => exact refParams_no_kstep hst
  | under _ _ ih => exact ih

theorem refParams_hasEtaK : @HasEtaK refParams := fun h => absurd h refParams_no_etaK

/-! ## The model: the closure is satisfiable, and not only vacuously

`HasEtaK` is a hypothesis about the *existing* `ParRed`, and `refParams_hasEtaK` only shows it
holds where `KStep` is empty.  That is the "premise the intended case makes unsatisfiable"
trap, which has bitten this development four times, so the closure is also **constructed**:
`ParRedK` is `ParRed` with the constructor added, as a mutual inductive with `EtaKK`.  It
exists at every `Params` instance, `ParRed ⊆ ParRedK` (`ParRed.toK`), and it satisfies the
closure by definition (`ParRedK.keta`) -- so the two kills below carry **no hypothesis at
all**, not even `HasEtaK`.

This is the relation `ChurchRosser.lean` would have after the edit; it is duplicated here
rather than landed there because landing it reds `Verify/Typing/ConstSpine.lean`, which this
stream does not own (`docs/handoff-krule.md` §T2, §T5). -/

/-- **`ParRed` with the η-guarded K step added.**  Constructors 1-8 are `ParRed`'s, verbatim;
`keta` is the new one, and it is the *general* `EtaK` step, so this relation extends `ParRed`
and contains every `EtaK` step.  It is a plain inductive: `EtaK` is already defined, over
`ParRed`, so nothing here is mutual. -/
inductive ParRedK : List VExpr → VExpr → VExpr → Prop where
  | bvar {Γ i} : ParRedK Γ (.bvar i) (.bvar i)
  | sort {Γ u} : ParRedK Γ (.sort u) (.sort u)
  | const {Γ c ls} : ParRedK Γ (.const c ls) (.const c ls)
  | app {Γ f f' a a'} : ParRedK Γ f f' → ParRedK Γ a a' → ParRedK Γ (.app f a) (.app f' a')
  | lam {Γ A A' body body'} :
      ParRedK Γ A A' → ParRedK (A::Γ) body body' → ParRedK Γ (.lam A body) (.lam A' body')
  | forallE {Γ A A' B B'} :
      ParRedK Γ A A' → ParRedK (A::Γ) B B' → ParRedK Γ (.forallE A B) (.forallE A' B')
  | beta {Γ A e₁ e₁' e₂ e₂'} :
      ParRedK (A::Γ) e₁ e₁' → ParRedK Γ e₂ e₂' →
      ParRedK Γ (.app (.lam A e₁) e₂) (e₁'.inst e₂')
  | extra {Γ p r e m1 m2 m2'} :
      Params.Pat p r → Pattern.Matches p e m1 m2 →
      Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
      (∀ a, ParRedK Γ (m2 a) (m2' a)) → ParRedK Γ e (Pattern.RHS.apply m1 m2' r.1)
  | keta {Γ e e'} : EtaK Γ e e' → ParRedK Γ e e'

/-- The enlarged relation contains the old one. -/
theorem ParRed.toK {Γ : List VExpr} {e e' : VExpr} (H : Γ ⊢ e ≫ e') : ParRedK Γ e e' := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih => exact .extra h1 h2 h3 ih

/-- `hK`, in the model: `KStep` is a step of `ParRedK`.  This is
`NormalEq.appDF_extra_of_descendV`'s only hypothesis, discharged. -/
theorem ParRedK.hK {Γ : List VExpr} {a b : VExpr} (h : KStep Γ a b) : ParRedK Γ a b :=
  .keta (.here h .rfl)

/-- The reflexive-transitive closure of the enlarged relation. -/
def ParRedKS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedK Γ)

/-! ### The two refutations, re-run: their hypotheses are contradictory

Neither theorem below assumes anything about the rule table, and neither assumes a closure:
`ParRedK` *is* the closed relation.  What each contradicts is the refutation's rigidity
hypothesis on the witness -- `e := Eq.rec α a C m a`, one argument short of the ι-pattern.  In
the old relation that term is normal, which is the whole content of both refutations; in this
one it reduces to the very λ they say nothing reaches. -/

/-- **`VEnv.not_crStatement_of_kstep` is inapplicable.**  Four of its eleven hypotheses are
already contradictory: `he`, `hstep`, `hlam`, `hrig`.  The other seven -- including `hne`, the
`NormalEq` gap that §S3 and §S4 identify -- are not needed, which is the precise sense in
which the repair belongs to the reduction relation and not to `NormalEq`. -/
theorem not_crStatement_of_kstep_dead
    {Γ : List VExpr} {e A B t : VExpr}
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRedK Γ e o → o = e) : False :=
  hlam A t (hrig _ (.keta (.under he (.here hstep .rfl)))).symm

/-- **`VEnv.not_parRedStatement_of_hK` is inapplicable**, and note *which* hypothesis dies:
not `hK` -- the model supplies that (`ParRedK.hK`) -- but `hrig`. -/
theorem not_parRedStatement_of_hK_dead
    {Γ : List VExpr} {e A B t : VExpr}
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRedKS Γ e o → o = e) : False :=
  hlam A t (hrig _ (ReflTransGen.tail .rfl (.keta (.under he (.here hstep .rfl))))).symm

/-- At the witness instance the enlarged relation is the old one, because `KStep` is empty
there.  So `DescendRefute.lean`'s three refutations -- which are all at `refParams` -- are
**unaffected** by the restatement, and remain the evidence that `NormalEq.descend` had to be
replaced. -/
theorem ParRedK.toParRed (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) {Γ : List VExpr} {e e' : VExpr}
    (H : ParRedK Γ e e') : Γ ⊢ e ≫ e' := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih => exact .extra h1 h2 h3 ih
  | keta h => exact absurd h hno

theorem refParams_parRedK_eq {Γ e e'} : @ParRedK refParams Γ e e' ↔ @ParRed refParams Γ e e' :=
  ⟨@ParRedK.toParRed refParams (fun h => refParams_no_etaK h) _ _ _,
   @ParRed.toK refParams _ _ _⟩

/-! ### The consumer repairs, machine-checked where they can be

`Verify/Typing/ConstSpine.lean` holds the only three declarations outside this stream's files
that **case on `ParRed`** (measured -- `docs/handoff-krule.md` §T2).  Two of them are proved
here for `ParRedK`, verbatim statements, so the edit there is one new case each, dispatched
exactly like the existing `extra` case.  The third, `ParRed.constApp_inv`, needs
`VEnv.PatFreeHead`, which is defined downstream of `Theory/`; `EtaK.matches_head` above is
what its new case consumes, and §T5 gives the edit. -/

/-- `ParRed.forallE_inv`'s statement, for the enlarged relation.  The `keta` case goes by
shape: a Π is not a constant-headed spine, so no `EtaK` step fires on it. -/
theorem ParRedK.forallE_inv {Γ : List VExpr} {A B e' : VExpr} (H : ParRedK Γ (.forallE A B) e') :
    ∃ A' B', e' = .forallE A' B' := by
  cases H with
  | forallE => exact ⟨_, _, rfl⟩
  | extra _ h2 => obtain ⟨_, _, hc⟩ := h2.spineHead_const; exact nomatch hc
  | keta h => exact absurd h EtaK.not_forallE

/-- `ParRed.sort_inv`'s statement, for the enlarged relation. -/
theorem ParRedK.sort_inv {Γ : List VExpr} {u : VLevel} {e' : VExpr}
    (H : ParRedK Γ (.sort u) e') : e' = .sort u := by
  cases H with
  | sort => rfl
  | extra _ h2 => obtain ⟨_, _, hc⟩ := h2.spineHead_const; exact nomatch hc
  | keta h => exact absurd h EtaK.not_sort

/-! ## What is still open

The restatement kills both refutations; it does not prove confluence.  What it leaves is the
diamond, and the diamond's price is unchanged from `KCanonical.lean` plus one new residual. -/

/-- `CParRed`'s neutrality test gains a third disjunct: a term whose η-expansion is a K-redex
is not neutral either.  `CParRed.exists` must decide it, classically. -/
def NonNeutralK (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  (∃ p r m1 m2, Params.Pat p r ∧ Pattern.Matches p e m1 m2 ∧
     Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2) ∨
  (∃ e', EtaK Γ e e')

/-- **The new residual for `ParRed.triangle`.**  `KDiamond` (`KDescend.lean`) prices two
K-steps at the *same* redex; this prices the η-layer: a term that both reduces at the top and
η-K-reduces must have `NormalEq`-close reducts.  It is stated, not proved, and it is *not*
implied by `KDiamond`: the two contracta live at different arities.

Do not spend `Params` fields on this or on `KDiamond` until confluence is re-derived for
`ParRedK`; §S7's eight construction sites are still eight. -/
def EtaKDiamond : Prop :=
  ∀ {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
    EtaK Γ e e₁ → EtaK Γ e e₂ → ∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ NormalEq Γ e₃ e₄

/-- Vacuously satisfied at the witness instance, for the same reason everything else in this
corner is: `KStep` is empty there.  Recorded as a consistency check, and **not** as
evidence -- see `KCanonical.lean`'s "why there is no refutation" note. -/
theorem refParams_etaKDiamond : @EtaKDiamond refParams :=
  fun _ h _ => absurd h refParams_no_etaK

/-! ### The routine cases of `ParRed`'s metatheory

`KCanonical.lean` already supplies `KStep.weakN` and `KStep.instN` with empty cones; these lift
them through the η-tower, and are `ParRed.weakN`'s and `ParRed.instN`'s new cases. -/

theorem EtaK.weakN {Γ Γ' : List VExpr} {e e' : VExpr} {n k : Nat}
    (W : Ctx.LiftN n k Γ Γ') (H : EtaK Γ e e') :
    EtaK Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | here hst hpr => exact .here (KStep.weakN W hst) (ParRed.weakN W hpr)
  | @under Γ e A B t hty _ ih =>
    refine .under (A := A.liftN n k) (B := B.liftN n (k+1))
      (by simpa [VExpr.liftN] using hty.weakN henv W) ?_
    have h := ih (Γ' := A.liftN n k :: Γ') (k := k+1) W.succ
    have he : (VExpr.app e.lift (.bvar 0)).liftN n (k+1)
        = VExpr.app ((e.liftN n k).lift) (.bvar 0) := by
      simp [VExpr.liftN, liftVar, ← VExpr.lift_liftN']
    rwa [he] at h

theorem EtaK.instN {Γ₀ Γ₁ Γ : List VExpr} {a₀ A₀' e e' : VExpr} {k : Nat}
    (H₀ : HasType env univs Γ₀ a₀ A₀') (W : Ctx.InstN Γ₀ a₀ A₀' k Γ₁ Γ)
    (H : EtaK Γ₁ e e') : EtaK Γ (e.inst a₀ k) (e'.inst a₀ k) := by
  induction H generalizing k Γ with
  | here hst hpr => exact .here (KStep.instN H₀ W hst) (ParRed.instN .rfl H₀ W hpr)
  | @under Γ₁ e A B t hty _ ih =>
    refine .under (A := A.inst a₀ k) (B := B.inst a₀ (k+1))
      (by simpa [VExpr.inst] using hty.instN henv W H₀) ?_
    have h := ih (Γ := A.inst a₀ k :: Γ) (k := k+1) W.succ
    have he : (VExpr.app e.lift (.bvar 0)).inst a₀ (k+1)
        = VExpr.app ((e.inst a₀ k).lift) (.bvar 0) := by
      simp [VExpr.inst, ← VExpr.lift_instN_lo]
    rwa [he] at h

/-! ### The two reduct-shape lemmas the refutations use, re-proved for the enlarged relation

`KCanonical.lean`'s `parRedS_rigid` and `parRedS_lam_inv` are what turn "the witness is
normal" into "the only candidate is the witness itself".  Both survive, and `parRedS_lam_inv`
gains exactly one case, closed by `EtaK.not_lam`.  So the refutations' *machinery* is intact:
what fails is their rigidity hypothesis, and nothing else. -/

theorem parRedKS_rigid {Γ : List VExpr} {e o : VExpr}
    (h : ∀ o', ParRedK Γ e o' → o' = e) (H : ParRedKS Γ e o) : o = e := by
  induction H with
  | rfl => rfl
  | tail _ hs ih => cases ih; exact h _ hs

theorem parRedKS_lam_inv {Γ : List VExpr} {A t y : VExpr}
    (hA : ∀ A', ParRedK Γ A A' → A' = A) (H : ParRedKS Γ (.lam A t) y) :
    ∃ t', y = .lam A t' ∧ ParRedKS (A::Γ) t t' := by
  induction H with
  | rfl => exact ⟨t, rfl, .rfl⟩
  | @tail b c _ hstep ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    cases hstep with
    | lam h1 h2 => cases hA _ h1; exact ⟨_, rfl, ReflTransGen.tail ht h2⟩
    | extra _ h2 => obtain ⟨_, _, hc⟩ := h2.spineHead_const; exact nomatch hc
    | keta h => exact absurd h EtaK.not_lam

end VEnv

end Lean4Lean
