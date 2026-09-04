import Lean4Lean.Theory.Typing.KSite7App
import Lean4Lean.Theory.Typing.ParRedPropRefute

/-!
# Is `NormalEq.descend` surplus?  The chokepoint, wrapped and refuted

`ChurchRosser.lean:1568-1574` records that `VEnv.NormalEq.descend` is refuted three times
(`DescendRefute.lean`) and that the repair is a K-form which `KDescend.lean` already supplies
(`NormalEq.descendV` + `NormalEq.appDF_extra_of_descendV`).  What was never checked is whether
the repair is **enough** -- i.e. whether the restatement *dominates* the refuted lemma, so that
deleting `descend` becomes a text edit rather than a proof obligation.

This file answers that, and the answer is **no**, for a reason sharper than "the restatement is
too weak".

## The route, measured rather than grepped

`lean_references` at the two declaration sites (2026-09-04) gives a single chain with no
branching below `NormalEq.parRed`:

```
NormalEq.descend            (ChurchRosser.lean:2011, 3 sorrys, refuted at refParams)
  -> NormalEq.appDF_extra_of_descend   (:2201)   -- its ONLY proof consumer (:2282)
    -> NormalEq.parRed                 (:2297)   -- its ONLY consumer (:2344), appDF x extra
      -> NormalEq.parRedS / ParRedS.church_rosser / CRDefEq.trans
        -> IsDefEq.church_rosser       (:2481)   -- what `Verify/` consumes
```

(`descend`'s only other reference is `DescendRefute.lean:430`, the anti-strawman check.)
So there is exactly **one** frontier lemma, `NormalEq.appDF_extra_of_descend`, and everything
between it and `church_rosser` is already `descend`-free *as a proof*.  Retiring `descend`
therefore reduces to re-proving that one statement.  `scripts/shape.lean`
(`HEADS="VEnv.ParRedS VEnv.NormalEq Pattern.RHS.apply VEnv.Params.Pat"`) finds exactly two
constants of that shape in the tree and **no** `Prop`-on-`Params` wrapper for it:
`DescendRefute.lean` wraps `descend`, `DescendRestate.lean` wraps `descendV`, and nothing
wrapped the chokepoint.  §1 does.

## §2: the restatement does deliver the frontier -- modulo exactly one hypothesis

`appDFExtraStatement_of_hK` derives the frontier statement from `KDescend.lean`'s
`NormalEq.appDF_extra_of_descendV`, whose single hypothesis is
`hK : KStep Delta e e' -> ParRed Delta e e'`.  **`NormalEq.descend` is not in its cone.**  So the
domination question is entirely the availability of `hK`, and nothing else: no second residual,
no side condition on the pattern.  (`descendV`'s own `q.NoApp` is *not* the obstacle, though it
is unavailable at the frontier: the call site at `ChurchRosser.lean:2282` descends the whole
node at the pattern `q1.app q2`, where `NoApp` is `False`, and `Params.pat_app_noApp` frees it
only for the two children.  The V-route sidesteps that by descending at `.var q1` and firing the
rule with a K-step -- which is where `hK` comes from.)

## §3: and `hK` is false, and so is the frontier statement itself

`ParRedPropRefute.lean` already refutes `hK` (`not_hK_of_propMajor`) and `NormalEq.parRed`'s
statement (`not_parRedStatement_of_propMajor`) at a registered `.app` rule whose major-premise
slot is typed by a `Prop`.  This file adds the fact that closes the question:

> `not_appDFExtraStatement_of_propMajor` -- **the frontier statement itself is refuted at the
> same witness**, by the same three moves (`NormalEq.proofIrrel` supplies the argument side,
> `ParRed.extra` fires the rule, and the left-hand redex is `ParRed`-normal).

That is strictly sharper than refuting `ParRedStatement`, because the frontier is the *one lemma*
a "delete `descend` and rewire" patch would have to re-prove.  Consequence: **no `descend`-free
derivation of the frontier exists -- not from `descendV`, not from anything -- while the
reduction relation stays `ParRed`.**  `descend` is not surplus; it is one of two false statements
stacked on top of each other, and the outer one is false for a reason that has nothing to do with
the descent.

## §4: what the K-route actually replaces

`KSite7App.lean`'s `NormalEq.appDF_extra_of_descendVK` is unconditional and `descend`-free, and
`DescendRestate.lean` calls it "that chokepoint's *unconditional* replacement".  §4 makes the
qualification precise: it proves a **different** statement, `AppDFExtraKStatement`, over
`ParRedK`/`ParRedKS`.  `appDFExtraKStatement_holds` records that the K-side domination is real,
and `not_bridge_appDFExtraK_to_appDFExtra` records that it cannot be bridged back: at the
propMajor witness `AppDFExtraKStatement -> AppDFExtraStatement` is **false**.  So the K-route is
a change of frontier, not a discharge of this one -- which is exactly why the rewiring still
costs `WeakNInvDS` (`ParRedKGraded.lean`'s `parRedKStatement_of_weakNInvDS`).

## Hole status, stated honestly

Nothing here is hole-free, and the claim is not that it is.  Measured with `scripts/exists.lean`
(WATCH=`Lean4Lean.VEnv.NormalEq.descend`):

* `appDFExtraStatement_of_hK` and `appDFExtraKStatement_holds` carry the tree's two ambient
  injectivity holes, `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`, and **not**
  `NormalEq.descend`.
* `not_appDFExtraStatement_of_propMajor` carries the same two ambient holes and nothing else,
  and the taint enters through **one** lemma, `ParRed.hasType` (subject reduction), used twice to
  type the reducts.  `not_appDFExtraStatement_of_propMajor'` replaces those two uses by one extra
  witness hypothesis and is `sorryAx`-**free**: `[propext, Quot.sound]`, the same axiom set as
  `ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor`.
* `not_hK_of_appDFExtra` and `not_bridge_appDFExtraK_to_appDFExtra` factor through §2/§4 and so
  inherit the two ambient holes.  They are *not* `sorryAx`-free, and the clean route to the same
  `hK` refutation is `ParRedPropRefute.lean`'s `not_hK_of_propMajor`; what these two add is that
  the refutation also lands *through the frontier*, which is what makes §2 and §3 jointly sharp.
* `appDFExtraStatement_holds` (the anti-strawman check) is `descend`-tainted *by design*: it is
  `@NormalEq.appDF_extra_of_descend` at the predicate, and its only job is to certify that
  `AppDFExtraStatement` is the real statement and not a strawman.  Nothing else here depends
  on it.

## Satisfiability of the refutation's hypotheses

Inherited verbatim from `ParRedPropRefute.lean`, and it is the one caveat that matters: every
hypothesis is a property of the *witness*.  (**CORRECTED 2026-09-04**: this said "no `Params`
instance in this tree registers an `.app` pattern".  **Two do.**  `scripts/shape.lean` on
`HEADS="Lean4Lean.VEnv.Params"` finds **eight** instances, and `Theory/Typing/ParamsCR.lean`'s
`VEnv.quotParams_not_appDFExtraStatement` (arity 0, cone 9368) fires the refutation below at
`VEnv.quotParams`, where the major premise is a proof of the `Prop` `Quot.{0} α r` -- so the
frontier statement is **false at a real instance** and this refutation is **not** vacuous.  The
converse also holds: `VEnv.appParams_no_appDFExtra_refutation` shows the hypothesis list is
*contradictory* at `appParams`, where `hne` is the false member.)  So this refutation, like
`not_parRedStatement_of_propMajor` and `not_hK_of_propMajor`, is conditional on an instance of a
shape that does not exist yet -- whereas `descend`'s own refutation is at `refParams`, an
instance that *does*.  The asymmetry is the whole practical content:

* `descend` can never be closed (refuted at a real instance), so deleting it is right;
* but the deletion cannot be performed by re-derivation, because its consumer's statement is
  itself unprovable (refutable at a hypothetical instance);
* so the deletion has to be a **migration to `ParRedK`**, at the price `DescendRestate.lean`'s
  table already records.
-/

namespace Lean4Lean
namespace VEnv

open VExpr
variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
set_option hygiene false in
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-! ## §1 The frontier, as a predicate on the `Params` instance -/

/-- **`NormalEq.appDF_extra_of_descend`'s statement**, verbatim, as a predicate on the `Params`
instance -- the same treatment `DescendRefute.lean` gives `descend` (`DescendStatement`) and
`DescendRestate.lean` gives `descendV` (`DescendStatementV`), and in the same style as
`KCanonical.lean`'s `ParRedStatement`.

This is the **whole** of what the tree gets from `NormalEq.descend`: it is `descend`'s only
proof consumer, and it has exactly one consumer of its own, the `appDF` × `extra` case of
`NormalEq.parRed` (`ChurchRosser.lean:2344`).  That it is literally the type and not a
paraphrase is checked by `appDFExtraStatement_holds`. -/
def AppDFExtraStatement : Prop :=
  ∀ {Γ : List VExpr} {f A B a b f₂ : VExpr},
    OnCtx Γ (IsType env univs) →
    Γ ⊢ f : .forallE A B → Γ ⊢ f₂ : .forallE A B → Γ ⊢ a : A → Γ ⊢ b : A →
    (∀ {e₂'}, Γ ⊢ f₂ ≫ e₂' → ∃ e₁', Γ ⊢ f ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
    (∀ {e₂'}, Γ ⊢ b ≫ e₂' → ∃ e₁', Γ ⊢ a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
    ∀ {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'},
    Params.Pat p r → p.Matches (f₂.app b) m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd →
    (∀ x, Γ ⊢ m2 x ≫ m2' x) →
    ∃ e₁', Γ ⊢ f.app a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst

/-- **Anti-strawman check**: `AppDFExtraStatement` is literally
`NormalEq.appDF_extra_of_descend`'s type.  `NormalEq.descend` is in this declaration's cone --
that is the point of the check, and it is the only declaration in this file of which that is
true.  Nothing below depends on it. -/
theorem appDFExtraStatement_holds : AppDFExtraStatement := by
  intro Γ f A B a b f₂ hΓ l1 l2 l3 l4 ih1 ih2 p r m1 m2 m2' r1 r2 r3 r4
  exact NormalEq.appDF_extra_of_descend hΓ l1 l2 l3 l4 ih1 ih2 r1 r2 r3 r4

/-! ## §2 The restatement delivers the frontier, modulo exactly `hK` -/

/-- **The `descend`-free derivation of the frontier, and its one residual.**
`KDescend.lean`'s `NormalEq.appDF_extra_of_descendV` -- built from `NormalEq.descendV`, whose
`q.NoApp` hypothesis is free at every registered pattern (`Params.pat_app_noApp`) -- gives the
frontier statement outright once `hK` is supplied, and `NormalEq.descend` is **not** in this
declaration's cone.

So `descendV` dominates `descend` at the frontier *up to* `hK`, with no second residual and no
side condition on the pattern.  §3 shows `hK` is false, which is why the domination fails. -/
theorem appDFExtraStatement_of_hK
    (hK : ∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → ParRed Δ e e') :
    AppDFExtraStatement := by
  intro Γ f A B a b f₂ hΓ l1 l2 l3 l4 ih1 ih2 p r m1 m2 m2' r1 r2 r3 r4
  exact NormalEq.appDF_extra_of_descendV hK hΓ l1 l2 l3 l4 ih1 ih2 r1 r2 r3 r4

/-! ## §3 The frontier statement is itself refuted -/

/-- **A registered rule with a `Prop`-typed major premise refutes the frontier.**

`ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor` refutes `NormalEq.parRed`'s
statement at this witness; this refutes the *one lemma* that a "retire `descend` and rewire"
patch would have to re-prove, which is strictly sharper and is what makes the retirement
impossible over `ParRed` rather than merely unachieved.

The witness's two `ih` slots -- the reason one might hope the frontier is weaker than
`ParRedStatement` -- are both satisfiable here, and that is the crux:

* `ih1` is at `f₂ = f`, so it is discharged by one `ParRedS.tail` and `NormalEq.refl`;
* `ih2` is exactly proof irrelevance: `a` and `b` inhabit the same `Prop`, so any `ParRed`
  reduct of `b` is `NormalEq` to `a` without moving `a` at all.

`hrig` (the K-redex `f a` is `ParRed`-normal) and `hne` (it is not `NormalEq` to the rule's
right-hand side) are the two witness properties; see `ParRedPropRefute.lean`'s header for their
reading at `Eq.rec`.

Axioms: `[propext, sorryAx, Classical.choice, Quot.sound]`, where the `sorryAx` is the tree's two
ambient injectivity holes reached through `ParRed.hasType` alone.  See
`not_appDFExtraStatement_of_propMajor'` for the `sorryAx`-free variant. -/
theorem not_appDFExtraStatement_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (IsType env univs))
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : Γ ⊢ f : .forallE A B)
    (hA : Γ ⊢ A : .sort .zero)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A)
    (hrig : ∀ o, Γ ⊢ .app f a ≫ o → o = .app f a)
    (hne : ¬ Γ ⊢ .app f a ≡ₚ Pattern.RHS.apply m1 m2 r.1) :
    ¬ AppDFExtraStatement := by
  intro H
  obtain ⟨o, ho, hno⟩ := H (f₂ := f) (m2' := m2) hΓ hf hf ha hb
    (fun h => ⟨_, .tail .rfl h, .refl (h.hasType hΓ hf)⟩)
    (fun h => ⟨_, .rfl, .proofIrrel hA ha (h.hasType hΓ hb)⟩)
    r1 r2 r3 (fun _ => .rfl)
  cases parRedS_rigid hrig ho
  exact hne hno

/-- **The same refutation with a clean axiom set.**  `sorryAx` enters
`not_appDFExtraStatement_of_propMajor` through exactly one lemma -- `ParRed.hasType`, subject
reduction, used twice to type the reducts of `f` and of `b` -- and through nothing else.  Trading
those two uses for one extra witness hypothesis `hbrig` (the matched argument `b` is
`ParRed`-normal, which holds at the intended witness `b := Eq.refl` with rigid arguments) makes
this `[propext, Quot.sound]`: **`sorryAx`-free**, the same axiom set as
`ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor`.

Note that the *function* side needs no new hypothesis: `hrig` already forces `f` to be
`ParRed`-normal, because `ParRed.app` would otherwise move `.app f a`.  So the only genuinely new
demand is on `b`. -/
theorem not_appDFExtraStatement_of_propMajor'
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (IsType env univs))
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : Γ ⊢ f : .forallE A B)
    (hA : Γ ⊢ A : .sort .zero)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A)
    (hrig : ∀ o, Γ ⊢ .app f a ≫ o → o = .app f a)
    (hbrig : ∀ o, Γ ⊢ b ≫ o → o = b)
    (hne : ¬ Γ ⊢ .app f a ≡ₚ Pattern.RHS.apply m1 m2 r.1) :
    ¬ AppDFExtraStatement := by
  have hfrig : ∀ o, Γ ⊢ f ≫ o → o = f := by
    intro o h
    have h2 := hrig _ (h.app .rfl)
    injection h2
  intro H
  obtain ⟨o, ho, hno⟩ := H (f₂ := f) (m2' := m2) hΓ hf hf ha hb
    (fun h => ⟨_, .tail .rfl h, hfrig _ h ▸ .refl hf⟩)
    (fun h => ⟨_, .rfl, hbrig _ h ▸ .proofIrrel hA ha hb⟩)
    r1 r2 r3 (fun _ => .rfl)
  cases parRedS_rigid hrig ho
  exact hne hno

/-- **`hK` is false, refuted at the frontier rather than at `KStep`.**  A second, independent
route to `ParRedPropRefute.lean`'s `not_hK_of_propMajor`: it factors through §2's derivation, so
it certifies that §2 and §3 are jointly sharp -- the residual §2 names is exactly the thing §3
kills, and neither statement has slack the other could absorb.

Not `sorryAx`-free: it factors through §2, hence through `descendV`, hence through the tree's two
ambient injectivity holes.  `ParRedPropRefute.lean`'s `not_hK_of_propMajor` is the clean route to
the same conclusion; this one is the route *through the frontier*. -/
theorem not_hK_of_appDFExtra
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (IsType env univs))
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : Γ ⊢ f : .forallE A B)
    (hA : Γ ⊢ A : .sort .zero)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A)
    (hrig : ∀ o, Γ ⊢ .app f a ≫ o → o = .app f a)
    (hne : ¬ Γ ⊢ .app f a ≡ₚ Pattern.RHS.apply m1 m2 r.1) :
    ¬ (∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → ParRed Δ e e') := fun hK =>
  not_appDFExtraStatement_of_propMajor hΓ r1 r2 r3 hf hA ha hb hrig hne
    (appDFExtraStatement_of_hK hK)

/-! ## §4 What the K-route replaces, and why it cannot be bridged back -/

/-- **The frontier over `ParRedK`**: `AppDFExtraStatement` with `ParRed`/`ParRedS` replaced by
`ParRedK`/`ParRedKS`, i.e. `KSite7App.lean`'s `NormalEq.appDF_extra_of_descendVK`'s type as a
predicate on the instance.  Comparing the two side by side is the point: `DescendRestate.lean`
calls the `VK` lemma "that chokepoint's unconditional replacement", and it is -- of *this*
statement, not of `AppDFExtraStatement`. -/
def AppDFExtraKStatement : Prop :=
  ∀ {Γ : List VExpr} {f A B a b f₂ : VExpr},
    OnCtx Γ (IsType env univs) →
    Γ ⊢ f : .forallE A B → Γ ⊢ f₂ : .forallE A B → Γ ⊢ a : A → Γ ⊢ b : A →
    (∀ {e₂'}, ParRedK Γ f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
    (∀ {e₂'}, ParRedK Γ b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂') →
    ∀ {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'},
    Params.Pat p r → p.Matches (f₂.app b) m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd →
    (∀ x, ParRedK Γ (m2 x) (m2' x)) →
    ∃ e₁', ParRedKS Γ (f.app a) e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst

/-- **The K-side domination is real and unconditional**: `KSite7App.lean`'s
`NormalEq.appDF_extra_of_descendVK` proves the K-frontier with no hypothesis at all, and
`NormalEq.descend` is not in its cone.  So "restate over `ParRedK` and the descent is repaired"
is correct -- as a statement about `AppDFExtraKStatement`. -/
theorem appDFExtraKStatement_holds : AppDFExtraKStatement := by
  intro Γ f A B a b f₂ hΓ l1 l2 l3 l4 ih1 ih2 p r m1 m2 m2' r1 r2 r3 r4
  exact NormalEq.appDF_extra_of_descendVK hΓ l1 l2 l3 l4 ih1 ih2 r1 r2 r3 r4

/-- **The K-frontier cannot be bridged back to the `ParRed` frontier.**  At the propMajor
witness `AppDFExtraKStatement` is a theorem (§4) and `AppDFExtraStatement` is false (§3), so the
implication between them is false.  This is the machine-checked form of the qualification
`DescendRestate.lean`'s "serves all of them" needs: the `VK` route does not discharge the
chokepoint, it *moves* it, and the move is what costs `WeakNInvDS`.

Not `sorryAx`-free: it uses §4, hence `appDF_extra_of_descendVK`, hence the two ambient
injectivity holes.  `NormalEq.descend` is *not* in its cone, which is the property that matters
here. -/
theorem not_bridge_appDFExtraK_to_appDFExtra
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (IsType env univs))
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : Γ ⊢ f : .forallE A B)
    (hA : Γ ⊢ A : .sort .zero)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A)
    (hrig : ∀ o, Γ ⊢ .app f a ≫ o → o = .app f a)
    (hne : ¬ Γ ⊢ .app f a ≡ₚ Pattern.RHS.apply m1 m2 r.1) :
    ¬ (AppDFExtraKStatement → AppDFExtraStatement) := fun h =>
  not_appDFExtraStatement_of_propMajor hΓ r1 r2 r3 hf hA ha hb hrig hne
    (h appDFExtraKStatement_holds)

end VEnv
end Lean4Lean
