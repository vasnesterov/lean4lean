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
| here  : KStep Γ e t → EtaK Γ e t
| under : Γ ⊢ e : ∀A.B → EtaK (A::Γ) (e.lift (.bvar 0)) t → EtaK Γ e (.lam A t)
```

`here` subsumes `hK` (`HasEtaK.hK`), so the one hypothesis `HasEtaK` replaces the two the
design would otherwise need.  More than one binder is genuinely reachable: `Acc.rec C F`,
short of both its index and its major premise, has
`Acc.intro x (fun y hy => Acc.inv h hy)` well-typed with `x` a *bound* variable.

**Shape C (Round 6).**  `here` used to carry a `ParRed` tail, which made `EtaK` and `ParRed`
mutually inductive once the constructor was landed -- and **Lean's `induction` tactic refuses
mutual inductives**, breaking six green proofs before any mathematics.  Dropping the tail
outright removes the mutuality but breaks `ParRed.instN`, whose statement substitutes `a1` on
the left and `a2` on the right: a bare `EtaK` step has no argument reductions to absorb the
gap.  The tail therefore moves to the *`ParRed` constructor*:

```
| keta : EtaK Γ e w → Γ ⊢ w ≫ w' → Γ ⊢ e ≫ w'
```

`EtaK` no longer mentions `ParRed`, so nothing is mutual; and `instN`'s induction hypothesis
on the second premise is exactly what carries `a1` to `a2`.  Both halves are measured, not
argued: `ParRedK.instN` and `ParRedK.defeqDFC` below are `ParRed`'s own proofs with the one
extra case, and they compile.  `docs/handoff-krule.md` §V.

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

`ParRed` gains no constructor here.  The landing was run for real in `ChurchRosser.lean`
(Round 6) and reverted: it leaves **seven** open sites, one of which is *false* without M3 and
four of which are open research.  What *is* checked here is the whole routine half --
`ParRedK.weakN`, `.instN`, `.defeq`, `.defeqDFC` -- on a relation that is now byte-for-byte the
landed one.  See `docs/handoff-krule.md` §V.
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

`here` is the plain K-rule (`HasEtaK.hK`); `under` is what the old relation was missing, and
is exactly the configuration `not_crStatement_of_kstep` exploits.

`EtaK` does **not** mention `ParRed`: the contractum's own development is a premise of
`ParRed`'s `keta` constructor instead (Shape C).  That is what keeps the landed `ParRed` a
plain, non-mutual inductive. -/
inductive EtaK : List VExpr → VExpr → VExpr → Prop where
  | here {Γ : List VExpr} {e t : VExpr} :
      KStep Γ e t → EtaK Γ e t
  | under {Γ : List VExpr} {e A B t : VExpr} :
      HasType env univs Γ e (.forallE A B) →
      EtaK (A::Γ) (.app e.lift (.bvar 0)) t → EtaK Γ e (.lam A t)

/-- **The closure condition on `ParRed`** (Shape C, `docs/handoff-krule.md` §V1).  The
contractum's own development is a *second premise*, not a tail inside `EtaK`: that is what
makes `EtaK` independent of `ParRed` (so nothing becomes mutually inductive) while still
absorbing `ParRed.instN`'s `a1`/`a2` gap through the induction hypothesis. -/
def HasEtaK : Prop :=
  ∀ {Γ : List VExpr} {e w w' : VExpr}, EtaK Γ e w → ParRed Γ w w' → ParRed Γ e w'

/-- The one-premise form: an `EtaK` step is itself a reduction.  (Shape B's constructor,
recovered from Shape C's by `ParRed.rfl`.) -/
theorem HasEtaK.step (h : HasEtaK) {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    ParRed Γ e e' := h H .rfl

/-- `HasEtaK` implies `hK`, `NormalEq.appDF_extra_of_descendV`'s only hypothesis. -/
theorem HasEtaK.hK (h : HasEtaK) {Γ : List VExpr} {a b : VExpr} (hst : KStep Γ a b) :
    ParRed Γ a b := h (.here hst) .rfl

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
  | @here _ e t hst =>
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
  | @here _ e t hst =>
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
  | @here Γ e t hst =>
    intro hΓ
    exact KStep.defeq hΓ hst
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
  hlam A t (hrig _ (hE.step (.under he (.here hstep)))).symm

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
  hlam A t (hrig _ (ReflTransGen.tail .rfl (hE.step (.under he (.here hstep))))).symm

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
  ⟨whnf_app_bvar hw hlam, .under hty (.here hstep)⟩

/-- `EtaK` is empty at the witness instance, because `KStep` is (`refParams_no_kstep`) and
every `EtaK` derivation bottoms out in a `KStep`.  Hence `HasEtaK` is a **consistent**
hypothesis, and -- the point that matters for §S1 -- `ParRed` at `refParams` is unchanged, so
`DescendRefute.lean`'s three refutations are untouched by the restatement.

**This is a consistency check, not evidence.**  No `Params` instance in this tree registers an
`.app` pattern, so nothing about the non-vacuous case is tested here. -/
theorem refParams_no_etaK {Γ e e'} : ¬ @EtaK refParams Γ e e' := by
  intro h
  induction h with
  | here hst => exact refParams_no_kstep hst
  | under _ _ ih => exact ih

theorem refParams_hasEtaK : @HasEtaK refParams := fun h => absurd h refParams_no_etaK

/-! ## The model: the closure is satisfiable, and not only vacuously

`HasEtaK` is a hypothesis about the *existing* `ParRed`, and `refParams_hasEtaK` only shows it
holds where `KStep` is empty.  That is the "premise the intended case makes unsatisfiable"
trap, which has bitten this development four times, so the closure is also **constructed**:
`ParRedK` is `ParRed` with the Shape-C constructor added.  It exists at every `Params`
instance, `ParRed ⊆ ParRedK` (`ParRed.toK`), and it satisfies the closure by definition
(`ParRedK.keta`) -- so the two kills below carry **no hypothesis at all**, not even
`HasEtaK`.

**This is now the relation `ChurchRosser.lean` gets after the edit, on the nose.**  Round 5's
fidelity caveat -- that `ParRedK` under-approximated the landed relation, because `EtaK.here`
carried a `ParRed` tail and the landed relation was the mutual fixpoint -- is **gone**: under
Shape C `EtaK` does not mention `ParRed` at all, so `ParRedK` is a plain inductive and it *is*
the fixpoint.  Negative-position transfer from `ParRedK` to the landed relation is therefore
valid again.  It is duplicated here rather than landed in `ChurchRosser.lean` because seven
sites there are still open (`docs/handoff-krule.md` §V3). -/

/-- **`ParRed` with the η-guarded K step added.**  Constructors 1-8 are `ParRed`'s, verbatim;
`keta` is the new one, in Shape C: the `EtaK` step and the contractum's own development are
two premises.  It is a plain inductive -- `EtaK` is defined without reference to `ParRed`, so
nothing here is mutual, and `ParRedK` is the fixpoint rather than an approximation of one.
`ParRedK.keta_step` recovers the one-premise form. -/
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
  | keta {Γ e w w'} : EtaK Γ e w → ParRedK Γ w w' → ParRedK Γ e w'

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

protected theorem ParRedK.rfl : ∀ {Γ : List VExpr} {e : VExpr}, ParRedK Γ e e
  | _, .bvar .. => .bvar
  | _, .sort .. => .sort
  | _, .const .. => .const
  | _, .app .. => .app ParRedK.rfl ParRedK.rfl
  | _, .lam .. => .lam ParRedK.rfl ParRedK.rfl
  | _, .forallE .. => .forallE ParRedK.rfl ParRedK.rfl

/-- The one-premise form of `keta`, recovered by reflexivity. -/
theorem ParRedK.keta_step {Γ : List VExpr} {e e' : VExpr} (h : EtaK Γ e e') : ParRedK Γ e e' :=
  .keta h .rfl

/-- `hK`, in the model: `KStep` is a step of `ParRedK`.  This is
`NormalEq.appDF_extra_of_descendV`'s only hypothesis, discharged. -/
theorem ParRedK.hK {Γ : List VExpr} {a b : VExpr} (h : KStep Γ a b) : ParRedK Γ a b :=
  .keta (.here h) .rfl

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
  hlam A t (hrig _ (.keta (.under he (.here hstep)) .rfl)).symm

/-- **`VEnv.not_parRedStatement_of_hK` is inapplicable**, and note *which* hypothesis dies:
not `hK` -- the model supplies that (`ParRedK.hK`) -- but `hrig`. -/
theorem not_parRedStatement_of_hK_dead
    {Γ : List VExpr} {e A B t : VExpr}
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRedKS Γ e o → o = e) : False :=
  hlam A t (hrig _ (ReflTransGen.tail .rfl (.keta (.under he (.here hstep)) .rfl))).symm

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
  | keta h _ _ => exact absurd h hno

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
  | keta h _ => exact absurd h EtaK.not_forallE

/-- `ParRed.sort_inv`'s statement, for the enlarged relation. -/
theorem ParRedK.sort_inv {Γ : List VExpr} {u : VLevel} {e' : VExpr}
    (H : ParRedK Γ (.sort u) e') : e' = .sort u := by
  cases H with
  | sort => rfl
  | extra _ h2 => obtain ⟨_, _, hc⟩ := h2.spineHead_const; exact nomatch hc
  | keta h _ => exact absurd h EtaK.not_sort

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
η-K-reduces must have `NormalEq`-close reducts.  It is stated, not proved.

**Correction (Round 5).**  This docstring used to add "and it is *not* implied by `KDiamond`:
the two contracta live at different arities".  **They do not.**
`Theory/Typing/KMeasure.lean`'s `EtaKn.height_uniq` proves that every `EtaK` derivation at a
given `Γ, e` has the *same* η-tower height -- `p₁.depth + 1 - e.appDepth`, with `p₁.depth`
pinned from `e`'s head constant by `Params.pat_app_depth_uniq`.  So the residual is the
*equal-height* diamond `KMeasure.EtaKDiamondAt`, and `KMeasure.etaKDiamond_of_at` discharges
the rest.  What remains is a λ-congruence induction whose base is `KDiamond`-shaped.

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
  | here hst => exact .here (KStep.weakN W hst)
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
  | here hst => exact .here (KStep.instN H₀ W hst)
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
    | keta h _ => exact absurd h EtaK.not_lam

/-! ## The Shape-C metatheory, machine-checked on the faithful model

`docs/handoff-krule.md` §U3 lists eight open sites for the landing.  Two of them are the
*routine* metatheory -- `ParRed.instN`'s `keta` case (site 1) and `ParRed.defeqDFC`'s (site
2).  Site 1 is what killed Shape B, and Shape C's whole reason for existing is that it closes
it; site 2 was called "routine **[analysis]**".  Since `ParRedK` is now byte-for-byte the
relation `ChurchRosser.lean` gets after the edit (`EtaK` no longer mentions `ParRed`, so the
inductive is not mutual and there is no under-approximation), the four lemmas below are a
*measurement* of the landing and not an analogy: each is `ParRed`'s proof verbatim with one
extra case.

**`instN` is the load-bearing one.**  Its statement substitutes `a1` on the left and `a2` on
the right; a bare `EtaK` step has no argument reductions to absorb the gap, which is exactly
the type error Shape B reports.  Shape C's `keta` carries the contractum's development as its
*second premise*, so the induction hypothesis supplies `w.inst a1 k ≫ w'.inst a2 k` and the
`EtaK` half only has to hold at the single substituend `a1` -- which `EtaK.instN` gives. -/

/-- `KStep` is stable under a definitionally-equal context.  Nothing has to be inverted:
`KStep` carries its own typing premises, so each is transported by its own `defeqDFC`. -/
theorem KStep.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {e e' : VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : KStep Γ₁ e e') : KStep Γ₂ e e' := by
  cases H with
  | mk hpat hm hck hf hdq =>
    exact .mk hpat hm (hck.map fun _ _ h => h.defeqDFC henv W)
      (hf.defeqDFC henv W) (hdq.defeqDFC henv W)

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
/-- **Site 2, discharged.**  `EtaK` is stable under a definitionally-equal context.  The
`under` case needs the domain's sort typing to extend `W`, and reads it off the carried
Π-typing; that is the only content. -/
theorem EtaK.defeqDFC {Γ₁ Γ₂ : List VExpr} {e e' : VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : EtaK Γ₁ e e') : EtaK Γ₂ e e' := by
  induction H generalizing Γ₂ with
  | here hst => exact .here (KStep.defeqDFC W hst)
  | @under Γ₁ e A B t hty _ ih =>
    have ⟨⟨_, hA⟩, _⟩ := (hty.isType henv (W.isType' hΓ₀)).forallE_inv henv
    exact .under (hty.defeqDFC henv W) (ih (W.succ hA))

theorem ParRedK.weakN {Γ Γ' : List VExpr} {e1 e2 : VExpr} {n k : Nat}
    (W : Ctx.LiftN n k Γ Γ') (H : ParRedK Γ e1 e2) :
    ParRedK Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [VExpr.liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    exact .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)
  | keta hek _ ih => exact .keta (hek.weakN W) (ih W)

variable! (H₀ : ParRedK Γ₀ a1 a2) (H₀' : Γ₀ ⊢ a1 : A₀) in
/-- **Site 1, discharged -- the reason Shape C exists.**

Shape B's `keta` (`EtaK Γ e e' → ParRed Γ e e'`) fails here with
`EtaK Γ (e.inst a1 k) (e'.inst a1 k)` against a goal of `e'.inst a2 k`.  Shape C's second
premise is where the `a1`/`a2` gap goes: `EtaK.instN` runs at the single substituend `a1`,
and the induction hypothesis on the tail moves `a1` to `a2`. -/
theorem ParRedK.instN {Γ₁ Γ : List VExpr} {e1 e2 : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : ParRedK Γ₁ e1 e2) : ParRedK Γ (e1.inst a1 k) (e2.inst a2 k) := by
  induction H generalizing Γ k with
  | @bvar _ i =>
    dsimp [VExpr.inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact ih.weakN .one
  | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [VExpr.inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀') (fun a => ih _ W)
  | keta hek _ ih => exact .keta (hek.instN H₀' W) (ih W)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- Admissibility of the whole enlarged relation: every `ParRedK` step is an `IsDefEq`, so
`kernel_sound`'s statement is untouched by the landing.  The `keta` case is `EtaK.defeqU`
followed by the induction hypothesis on the contractum's development. -/
theorem ParRedK.defeq {e e' A : VExpr} (H : ParRedK Γ e e') (he : Γ ⊢ e : A) :
    Γ ⊢ e ≡ e' : A := by
  induction H generalizing A with
  | bvar | sort | const => exact he
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he <| .appDF (ih1 hΓ h1) (ih2 hΓ h2)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact .trans_l henv hΓ he <| .lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he <| .forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have hf' := hA.lam hb
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hf')
    replace ha := ha.defeqU_r henv hΓ ⟨_, u1⟩
    exact .trans_l henv hΓ he <| .trans
      (.symm <| .appDF (.symm <| .lamDF hA (ih1 ⟨hΓ, _, hA⟩ hb)) (.symm <| ih2 hΓ ha))
      (.beta (ih1 ⟨hΓ, _, hA⟩ hb).hasType.2 (ih2 hΓ ha).hasType.2)
  | @extra p r e m1 m2 _ m2' h1 h2 h3 _ ih =>
    exact .trans_l henv hΓ he <| .transU_r henv hΓ (Params.pat_wf h1 h2 hΓ he h3) <|
     .apply_pat hΓ (fun _ _ h => ⟨_, ih _ hΓ h⟩) (.defeqU_l henv hΓ (Params.pat_wf h1 h2 hΓ he h3) he)
  | keta hek _ ih =>
    have hd := (hek.defeqU hΓ).of_l henv hΓ he
    exact hd.trans (ih hΓ hd.hasType.2)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedK.hasType {e e' A : VExpr} (H : ParRedK Γ e e') (he : Γ ⊢ e : A) : Γ ⊢ e' : A :=
  (H.defeq hΓ he).hasType.2

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRedK.defeqDFC {Γ₁ Γ₂ : List VExpr} {e1 e2 A : VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : ParRedK Γ₁ e1 e2) : ParRedK Γ₂ e1 e2 := by
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
  | @extra p r e m1 m2 _ m2' h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => h.defeqDFC henv W) fun a =>
      let ⟨_, hh⟩ := h2.hasType (W.isType' hΓ₀) h a; ih a W hh
  | keta hek _ ih =>
    exact .keta (hek.defeqDFC hΓ₀ W)
      (ih W (hek.defeqU (W.isType' hΓ₀) |>.of_l henv (W.isType' hΓ₀) h |>.hasType.2))

/-! ## The domain obstruction: `ParRed.weakN_inv` is false at `=`, and M3 does not touch it

`docs/handoff-krule.md` §V3 site 1, and the brief that produced this round, say the `keta`
case of `ParRed.weakN_inv` is false because `KStep`'s major premise `c` is existentially
quantified and may mention `.bvar k`, and that **M3** (`KCanonical.KTable`) repairs it by
making the canonical premise a syntactic function of the redex.

**That diagnosis is incomplete, and the repair does not work**, for a reason one level up
from the rule table: `EtaK.under` carries the η-expansion's **domain** `A`, constrained only
by `Γ ⊢ e : .forallE A B` -- i.e. only *up to definitional equality*.  So even a fully
canonical K-step produces a contractum `.lam A t` whose `A` may mention `.bvar k`, and that
is not a lift.  `kmajor` says nothing about `A`; no field of the rule table can, because `A`
is not read off the rule at all.
-/

/-- **The λ-domain of an `EtaK` step is only determined up to conversion.**  Given one
derivation ending in `under`, every definitionally equal domain gives another one, with the
*same* body.  `EtaK.defeqDFC` moves the sub-derivation; the Π-typing is transported by
`forallEDF`. -/
theorem EtaK.under_dom {Γ : List VExpr} {e A A' B t : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (hty : Γ ⊢ e : .forallE A B) (hB : A::Γ ⊢ B : .sort v)
    (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (H : EtaK (A::Γ) (.app e.lift (.bvar 0)) t) : EtaK Γ e (.lam A' t) :=
  .under (.defeqDF (.forallEDF hAA' hB) hty) (H.defeqDFC hΓ (.succ .zero hAA'))

/-- `ParRed.weakN_inv`'s statement (`ChurchRosser.lean:775`), verbatim, for the enlarged
relation.  Its `keta` case is `docs/handoff-krule.md` §V3's site 1. -/
def WeakNInvStatement : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    Γ' ⊢ e1.liftN n k : A → ParRedK Γ' (e1.liftN n k) e2' →
    ∃ e2, ParRedK Γ e1 e2 ∧ e2' = e2.liftN n k

/-- A domain that is definitionally equal to `A₀.lift` in `C::Γ` and **mentions `.bvar 0`**:
the type ascription redex `(fun _ : C => A₀) x` at the freshly bound `x`.  It is a lift of
nothing, and `EtaK.under_dom` puts it in the conclusion of an `EtaK` step at a lifted
redex. -/
def kdom (C A₀ : VExpr) : VExpr := .app (.lam C.lift (A₀.lift.lift)) (.bvar 0)

theorem kdom_defeq {Γ : List VExpr} {C A₀ : VExpr} {uC u : VLevel}
    (hC : Γ ⊢ C : .sort uC) (hA₀ : Γ ⊢ A₀ : .sort u) :
    (C::Γ) ⊢ kdom C A₀ ≡ A₀.lift : .sort u :=
  by simpa [kdom, VExpr.inst_lift, VExpr.liftN, VExpr.inst] using
    IsDefEq.beta (A := C.lift) ((hA₀.weak henv).weak henv) (.bvar .zero)

theorem kdom_ne_liftN {C A₀ X : VExpr} : kdom C A₀ ≠ X.liftN 1 0 := by
  intro h
  cases X <;> simp [kdom, VExpr.liftN] at h
  rename_i X1 X2
  obtain ⟨-, h⟩ := h
  cases X2 <;> simp [VExpr.liftN, Lean4Lean.liftVar] at h
  omega

/-- **Site 1 is false at `=`, and M3 cannot repair it.**  The single hypothesis `hin` is the
same configuration both standing kills use -- a K-redex at the η-expansion of a term one
argument short of its ι-pattern -- and nothing about the rule table enters the argument.

What breaks `weakN_inv` here is `EtaK.under`'s **domain**, not `KStep`'s major premise: the
step at the lifted redex `e.lift` may legitimately conclude `.lam (kdom C A₀) t`, whose
domain mentions `.bvar 0` and is therefore the lift of nothing.  `KTable.kmajor` is a
function of `(p₂, f, h)` and says nothing about the domain; no field of the rule table can,
because the domain is not read off the rule.  So the conclusion `e2' = e2.liftN n k` must
weaken however canonical the K-step is made. -/
theorem not_weakNInvStatement_of_etaK
    {Γ : List VExpr} {C e A₀ B₀ t : VExpr} {uC : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (hC : Γ ⊢ C : .sort uC)
    (he : Γ ⊢ e : .forallE A₀ B₀)
    (hin : EtaK (A₀.lift :: C :: Γ) (.app (VExpr.lift (VExpr.lift e)) (.bvar 0)) t) :
    ¬ WeakNInvStatement := by
  intro WI
  have hΓC : OnCtx (C::Γ) (IsType env univs) := ⟨hΓ, _, hC⟩
  have ⟨⟨u, hA₀⟩, v, hB₀⟩ := (have ⟨_, h⟩ := he.isType henv hΓ; h.forallE_inv henv)
  have hty : (C::Γ) ⊢ e.lift : .forallE A₀.lift (B₀.liftN 1 1) := he.weak henv
  have hB : (A₀.lift :: C :: Γ) ⊢ B₀.liftN 1 1 : .sort v := hB₀.weakN henv (.succ .one)
  have hek : EtaK (C::Γ) e.lift (.lam (kdom C A₀) t) :=
    EtaK.under_dom hΓC hty hB (kdom_defeq hC hA₀).symm hin
  obtain ⟨e2, -, heq⟩ := WI (n := 1) (k := 0) hΓC .one hty (.keta hek .rfl)
  cases e2 <;> simp [VExpr.liftN] at heq
  exact kdom_ne_liftN heq.1

/-! ### The repair: `≡ₚ`, and why the domain obstruction does not survive it

`NormalEq.lamDF` asks only that the two λ-domains be **definitionally equal** to a common
one -- `Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u → A::Γ ⊢ b₁ ≡ₚ b₂`.  That is exactly the
slack `EtaK.under`'s free domain needs, so the `≡ₚ`-weakened conclusion is **immune** to the
refutation above: the witness is visibly killed rather than merely no longer derivable
(`ORCHESTRATOR.md` working rule 2). -/

/-- **The fix, re-run against its own witness.**  At the configuration that refutes the
equality form, the `≡ₚ` form's obligation is discharged by `NormalEq.lamDF` alone. -/
theorem kdom_normalEq_lam {Γ : List VExpr} {C A₀ t t' : VExpr} {uC u : VLevel}
    (hC : Γ ⊢ C : .sort uC) (hA₀ : Γ ⊢ A₀ : .sort u)
    (ht : (A₀.lift :: C :: Γ) ⊢ t ≡ₚ t') :
    (C::Γ) ⊢ .lam (kdom C A₀) t ≡ₚ .lam A₀.lift t' :=
  .lamDF (kdom_defeq hC hA₀).symm (hA₀.weak henv) ht

/-- The `≡ₚ`-weakened conclusion of the lifting inversion, together with the information the
η-tower's own induction needs: the descended step is either a genuine `EtaK` step or the
identity.  The identity alternative is not slack -- `KTable.canon`'s proof escape produces it
(the redex is a proof, so `NormalEq.proofIrrel` closes without any downstairs step), and the
`under` layer turns it into `NormalEq.etaL`. -/
def EtaKLiftInvC (Γ Γ' : List VExpr) (n k : Nat) (e1 w : VExpr) : Prop :=
  ∃ w₀, (EtaK Γ e1 w₀ ∨ w₀ = e1) ∧ NormalEq Γ' w (w₀.liftN n k)

/-- **The residual of the lifting inversion: the `here` layer.**  This is where M3 lives --
`KCanonical.KTable.kstep_liftN_inv` is its `NormalEq` half, and what it does not yet supply
is the *downstairs step*, which needs `Pat`/`Matches`/`Check.OK` and the two typing premises
descended (`IsDefEqU.weakN_iff`, already a hole of the tree). -/
def KStepLiftInv : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 w A : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' → Γ' ⊢ e1.liftN n k : A →
    KStep Γ' (e1.liftN n k) w → EtaKLiftInvC Γ Γ' n k e1 w

/-- **The typing descent the η-tower needs.**  `Theory/Typing/Strengthen.lean`'s `PiDescend`
is the same statement with the two `VExpr.WF` premises supplied; both follow from
`IsDefEqU.weakN_iff`, which is `UniqueTyping.lean:172`'s existing hole. -/
def PiTypeDescend : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e A B : VExpr},
    OnCtx Γ (IsType env univs) → OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    Γ' ⊢ e.liftN n k : .forallE A B → ∃ A₀ B₀, Γ ⊢ e : .forallE A₀ B₀

/-- **`KStepLiftInv` from M3 and the Π-typing descent.**  Together with `etaKn_liftN_inv`
(`KMeasure.lean`) this settles `ParRed.weakN_inv`'s `keta` case *in its `≡ₚ` form*: the
`here` layer is `KTable.kstep_liftN_inv_step` and the η-tower is free.

The equality form is **not** recovered, and cannot be -- `not_weakNInvStatement_of_etaK`
above refutes it from a single K-step, axiom-clean, and the obstruction is the λ-domain,
which no field of the rule table mentions. -/
theorem kStepLiftInv_of (KT : KTable) (HP : PiTypeDescend) : KStepLiftInv := by
  intro n k Γ Γ' e1 w A hΓ' W hty H
  have hΓ : OnCtx Γ (IsType env univs) := hΓ'.weakN_inv henv W
  cases e1 with
  | bvar => exact nomatch H
  | sort => exact nomatch H
  | const => exact nomatch H
  | lam => exact nomatch H
  | forallE => exact nomatch H
  | app f h =>
    obtain ⟨_, _, hfty, -⟩ := hty.app_inv henv hΓ'
    obtain ⟨A₁, B₁, hf₀⟩ := HP hΓ hΓ' W hfty
    rcases KT.kstep_liftN_inv_step hΓ hΓ' W hf₀ H with ⟨w₀, hks, hne⟩ | hne
    · exact ⟨w₀, .inl (.here hks), hne⟩
    · exact ⟨_, .inr rfl, hne⟩

/-- **The refutation's hypotheses are load-bearing.**  Where `EtaK` is empty, `ParRedK` is
`ParRed` and `WeakNInvStatement` *holds* -- `ChurchRosser.lean`'s `ParRed.weakN_inv` is
exactly it.  So the statement is not refutable outright: what refutes it is a live K-step,
and the standing caveat applies (no `Params` instance in this tree registers an `.app`
pattern, and "no witness" is not evidence). -/
theorem weakNInvStatement_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : WeakNInvStatement := by
  intro n k Γ Γ' e1 e2' A hΓ' W hty H
  obtain ⟨e2, h1, h2⟩ := ParRed.weakN_inv hΓ' W hty (ParRedK.toParRed hno H)
  exact ⟨e2, h1.toK, h2⟩

theorem refParams_weakNInvStatement : @WeakNInvStatement refParams :=
  @weakNInvStatement_of_no_etaK refParams (fun h => refParams_no_etaK h)

/-- Vacuously satisfied where `KStep` is empty; recorded as a consistency check only. -/
theorem kStepLiftInv_of_no_kstep (hno : ∀ {Δ a b}, ¬ KStep Δ a b) : KStepLiftInv := by
  intro n k Γ Γ' e1 w A hΓ' W hty H
  exact (hno H).elim

theorem refParams_kStepLiftInv : @KStepLiftInv refParams :=
  @kStepLiftInv_of_no_kstep refParams (fun h => refParams_no_kstep h)

end VEnv

end Lean4Lean
