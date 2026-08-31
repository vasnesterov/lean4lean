import Lean4Lean.Theory.Typing.KEta

/-!
# `NormalEq.parRed`'s statement is false at a registered rule with a `Prop` major premise

`Theory/Typing/KCanonical.lean` refutes `VEnv.ParRedStatement` -- `NormalEq.parRed`'s
statement, verbatim -- **from `hK`**, the hypothesis that a `K⁺` step is a `ParRed` step
(`not_parRedStatement_of_hK`).  That leaves open the reading under which `descend` is the only
defect and the statement survives once the descent is restated: retire
`ChurchRosser.lean`'s `NormalEq.descend`, rewire `NormalEq.parRed` onto
`KDescend.lean`'s `NormalEq.descendV` + `NormalEq.appDF_extra_of_descendV`, and the hole
closes.

**It does not, and this file says why in one theorem.**  `not_parRedStatement_of_propMajor`
below refutes `ParRedStatement` **with no `hK`, no `KStep`, and no eta step** -- from nothing
but a registered `.app` rule whose major-premise slot is typed by a `Prop`.  So the obstruction
is not in the descent at all: it is in `ParRed` itself, which has no step that replaces the
major premise of a redex by a definitionally equal one, while `NormalEq` has `proofIrrel`,
which does.

## The witness, in one line

At an ι-rule `Pat (p₁.app p₂) r` matching `f b` -- read `f := Eq.rec α x C m y` and
`b := Eq.refl` -- with the major premise's type `A` a `Prop`:

* `Γ ⊢ f a ≡ₚ f b` for **any** other proof `a : A`, by `NormalEq.appDF` over
  `NormalEq.proofIrrel`;
* `Γ ⊢ f b ≫ r.1.apply m1 m2` by `ParRed.extra`, the rule firing on the nose;
* but `f a` is `ParRed`-normal (`Pattern.Matches` is syntactic: `a` is not a constructor
  spine, so no rule fires, and `f` is not a `.lam`, so no β), and `f a` is not `NormalEq` to
  the rule's right-hand side (take the minor premise `m` to be a variable and the motive `C`
  to land in `Type`, so that neither `appDF` nor `proofIrrel` applies).

## Consequences, stated exactly

1. **Retiring `NormalEq.descend` cannot make `NormalEq.parRed` provable.**  Whatever the
   descent's statement becomes, the `appDF` × `extra` case above has no witness.  Both routes
   in `ChurchRosser.lean`'s handoff note -- descend the whole node, or descend the function
   side at `.var p₁` and fire with a K-step -- fail here for the *same* reason, and the second
   one's hypothesis `hK` is therefore not merely undischarged but false at this instance:
   `KDescend.lean`'s `NormalEq.appDF_extra_of_descendV` is sound, but nothing can supply its
   premise against `ChurchRosser.lean`'s `ParRed`.

2. **The repair is on the reduction side**, as `ChurchRosser.lean`'s handoff note's option (2)
   and `KEta.lean`'s `ParRedK` already say: `ParRed` needs the proof-replacement step (or the
   K-step, which subsumes it -- a `K⁺` step fires whichever proof sits in the major-premise
   slot).  This theorem is the reason that is *forced* rather than merely convenient.
   `not_hasEtaK_of_propMajor` below states it in the form `KEta.lean` can use directly: its
   closure condition `HasEtaK` -- Shape C *on `ParRed`* -- is false, so a **new** relation
   (`ParRedK`) is not a convenience but the only option.

3. **`descend` is still worth deleting**, but for hygiene, not for the hole: its statement is
   refuted at an instance that *exists* (`DescendRefute.lean`, over `refEnv`), whereas every
   statement in this corner that carries `Pat p r` is refuted only at instances that do not
   exist yet.  Deleting it moves the hole; it does not remove one.

## Satisfiability of the hypotheses

Exactly as for `KCanonical.lean`'s `not_crStatement_of_kstep`: every hypothesis is a property
of the witness rather than of the rule table, and no `Params` instance in this tree registers
an `.app` pattern (`PatWFIota.lean` is where that would come from), so the refutation is
conditional on such an instance in precisely the same way that one is.  `hrig` is consistent
with `r1`/`r2`: `Pattern.Matches` bottoms out at `.const` leaves, so a pattern matching
`.app f a` would have to match `a` at a `.var` position of `p₂`'s spine, and `p₂` is
`(.const ctor).varN n` by `Params.pat_simple`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable [Params]
open Params

/-- **A registered rule with a `Prop`-typed major premise refutes `NormalEq.parRed`.**  No
`hK`, no `KStep`, no eta: the only facts used are that `NormalEq` has `proofIrrel` and
`ParRed` does not.

`hrig` (the K-redex `f a` is `ParRed`-normal) and `hne` (it is not `NormalEq` to the rule's
right-hand side) are the two witness properties; see the module docstring for their reading at
`Eq.rec`. -/
theorem not_parRedStatement_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (IsType env univs))
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : HasType env univs Γ f (.forallE A B))
    (hA : HasType env univs Γ A (.sort .zero))
    (ha : HasType env univs Γ a A) (hb : HasType env univs Γ b A)
    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
    (hne : ¬ NormalEq Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) :
    ¬ ParRedStatement := by
  intro H
  have h1 : NormalEq Γ (.app f a) (.app f b) :=
    .appDF hf hf ha hb (.refl hf) (.proofIrrel hA ha hb)
  have h2 : ParRed Γ (.app f b) (Pattern.RHS.apply m1 m2 r.1) :=
    .extra r1 r2 r3 fun _ => .rfl
  obtain ⟨o, ho, hno⟩ := H hΓ h1 h2
  cases parRedS_rigid hrig ho
  exact hne hno

/-- **The same witness refutes `hK` outright.**  `KDescend.lean`'s
`NormalEq.appDF_extra_of_descendV` -- the sorry-free replacement for
`ChurchRosser.lean`'s `NormalEq.appDF_extra_of_descend` -- carries the hypothesis
`hK : ∀ {Δ e e'}, KStep Δ e e' → Δ ⊢ e ≫ e'`.  That hypothesis is not merely undischargeable
against `ChurchRosser.lean`'s `ParRed`: it is **false** as soon as one registered `.app` rule
has a `Prop`-typed major-premise slot.

Read with `hrig`: `K⁺` fires at `.app f a` for *any* proof `a` of the domain, because proof
irrelevance supplies `KStep`'s `hdq`; `ParRed` does not move `.app f a` at all, because
`Pattern.Matches` is syntactic.  So no rewiring of the descent can close
`NormalEq.parRed`'s `appDF` × `extra` case -- the reduction relation itself has to grow
(`KEta.lean`'s `ParRedK`). -/
theorem not_hK_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : HasType env univs Γ f (.forallE A B))
    (hA : HasType env univs Γ A (.sort .zero))
    (ha : HasType env univs Γ a A) (hb : HasType env univs Γ b A)
    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
    (hne : Pattern.RHS.apply m1 m2 r.1 ≠ .app f a) :
    ¬ (∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → ParRed Δ e e') := by
  intro hK
  have hk : KStep Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1) :=
    .mk r1 r2 r3 hf (.proofIrrel hA ha hb)
  exact hne (hrig _ (hK hk))

/-- **`KEta.lean`'s closure condition `HasEtaK` is false**, at the same witness.  `HasEtaK` is
Shape C's condition *on `ParRed`* (`docs/handoff-krule.md` §V1), and `HasEtaK.hK` derives
exactly the `hK` refuted above; so this is the machine-checked reason `KEta.lean` has to
introduce a **new** relation `ParRedK` instead of proving the closure condition for the old
one.  Nothing in the tree assumes `HasEtaK`, and after this nothing should. -/
theorem not_hasEtaK_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : HasType env univs Γ f (.forallE A B))
    (hA : HasType env univs Γ A (.sort .zero))
    (ha : HasType env univs Γ a A) (hb : HasType env univs Γ b A)
    (hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
    (hne : Pattern.RHS.apply m1 m2 r.1 ≠ .app f a) :
    ¬ HasEtaK :=
  fun h => not_hK_of_propMajor r1 r2 r3 hf hA ha hb hrig hne
    fun hst => h (.here hst) .rfl


/-! ## Task 0: `ParRedK` defeats this witness -- and the reason is `KStep`, not eta

The question one must ask of any proposed repair is whether it survives *this* witness, and
for `KEta.lean`'s `ParRedK` the answer is yes.  The mechanism is worth stating precisely,
because it is easy to get backwards:

* **`EtaK` is not "only about eta".**  Its base constructor `EtaK.here` takes a `KStep`
  outright, so `KStep ⊆ EtaK ⊆ ParRedK` (`ParRedK.hK`).  The `under` constructor is the eta
  tower; `here` is the K-step itself.
* **`KStep` *is* the proof-replacement step.**  `KStep.mk`'s premise
  `hdq : IsDefEq env univs Γ h c A₀` says the major premise need only be *definitionally
  equal* to a matching one; `NormalEq.proofIrrel`'s content is exactly an instance of that.
  So `KStep` subsumes proof replacement at a redex position, and is in fact more general
  (any defeq argument, not just a proof).

What `ParRedK` does **not** give is a general congruence step `ParRedK Γ (.app f a)
(.app f b)` for arbitrary same-proposition proofs `a b`; there is no proof-irrelevance
constructor in `ParRedK`.  **That is not what `NormalEq.parRed` needs.**  `parRed` asks for
*some* `o` with `e₁ ≫* o` and `o ≡ₚ e₂'`, and at this witness `o := e₂'` works: the K-step
jumps `f a` straight to the rule's right-hand side, skipping `f b` entirely.  So the repair
is not "add proof irrelevance to the reduction relation" but "let the rule fire up to defeq
of the major premise", which is what `K⁺` was for all along.

Both theorems below are unconditional and share the refutations' hypotheses verbatim. -/

/-- **The witness's `hrig` is false for `ParRedK`.**  Under exactly the hypotheses of
`not_parRedStatement_of_propMajor`, the term the refutation needs to be reduction-normal is
a `ParRedK` redex: `K⁺` fires at `.app f a` with proof irrelevance discharging `KStep`'s
`hdq`.

This is the task-0 check: the counterexample dies at its rigidity hypothesis, so
`not_parRedStatement_of_propMajor` has no `ParRedK` analogue. -/
theorem ParRedK.propMajor_fires
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : HasType env univs Γ f (.forallE A B))
    (hA : HasType env univs Γ A (.sort .zero))
    (ha : HasType env univs Γ a A) (hb : HasType env univs Γ b A) :
    ParRedK Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1) :=
  ParRedK.hK (.mk r1 r2 r3 hf (.proofIrrel hA ha hb))

/-- **`ParRedK` supplies what `ParRedStatement` wanted at the `propMajor` witness.**  Where
`not_parRedStatement_of_propMajor` shows no `o` exists for `ParRed`, here `o` is the rule's
own right-hand side, reached in one step, and `NormalEq.refl` closes the second conjunct.
No `hK`, no `HasEtaK`, no eta layer: this is `ParRedK.keta` at zero eta depth. -/
theorem ParRedK.propMajor_joins
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hf : HasType env univs Γ f (.forallE A B))
    (hA : HasType env univs Γ A (.sort .zero))
    (ha : HasType env univs Γ a A) (hb : HasType env univs Γ b A)
    (hT : HasType env univs Γ (Pattern.RHS.apply m1 m2 r.1) B) :
    ∃ o, ParRedKS Γ (.app f a) o ∧ NormalEq Γ o (Pattern.RHS.apply m1 m2 r.1) :=
  ⟨_, .tail .rfl (ParRedK.propMajor_fires r1 r2 r3 hf hA ha hb), .refl hT⟩

end VEnv
end Lean4Lean
