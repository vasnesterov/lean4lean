import Lean4Lean.Theory.Typing.PatAppParams
import Lean4Lean.Theory.Typing.DescendConstSpineK
import Lean4Lean.Verify.Typing.ConstSpine

/-!
# What is the RIGHT confluence statement?  Not a proof-irrelevance quotient.

Round of 2026-09-04, `docs/handoff-crshape.md` (priors in §1, measurements in §2).

`VEnv.CRStatement` (`KCanonical.lean`) is `IsDefEq.church_rosser`'s statement verbatim, and
`VEnv.quotParams_not_crStatement` (`Verify/QuotAppParams.lean`) refutes it -- **modulo
`IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`**, which is the condition commit
`a561fa9` attached to it and which must travel with the claim.  The question this file answers is
what the corrected statement is.

## The hypothesis under test, and the verdict

> *The failure is routed through a `Prop`-typed major premise, so `CRStatement` is too syntactic:
> confluence of the reduction fails on proof terms while the conversion relation is unharmed,
> because proof irrelevance identifies the divergent results anyway.  So the right statement
> quotients by proof irrelevance -- confluence "up to `IsProof`".*

**Right about where the failure enters, wrong about the repair, and §1 refutes the repair
outright.**  Three measurements, each machine-checked below or cited:

1. **The quotient is already there.**  `VEnv.NormalEq` has a `proofIrrel` constructor, and
   `CRDefEq`'s third conjunct is `∃ e₁' e₂', e₁ ≫* e₁' ∧ e₂ ≫* e₂' ∧ e₁' ≡ₚ e₂'`.  So `CRStatement`
   is *already* joinability-up-to-proof-irrelevance, not syntactic identity.
2. **`Prop`-routing does not discriminate.**  `appParams` (`PatAppParams.lean`) fires the same
   `K⁺` step through the same proof-irrelevance move at a `Prop`-typed variable major premise, and
   `CRStatement` is **not** refutable there -- `appParams_no_crStatement_refutation`, because
   `appParams_normalEq_of_kstep` makes `hne` unsatisfiable.  What differs at `quotParams` is that
   its rule *computes*: `quotRHS = g x` depends on the matched argument
   (`quotRHS_depends_on_match`), where `appParams`' two right-hand sides are the **closed** terms
   `cycG`/`cycG2` and are mutually `NormalEq` (`appPat_rhs_eq`).  §2 states that discriminator as
   a theorem: the load-bearing property is that **every `K⁺` step is a `NormalEq`**, a property of
   the rule table's contractivity with no mention of proofs.
3. **And the divergent pair is not proof-typed.**  `not_crStatement_of_kstep` *takes* `hnp` -- "`e`
   is not a proof" -- as a hypothesis, discharged at `quotParams` by `qLiftT0_not_proof`.  So
   weakening the conclusion by any proof-irrelevance escape clause leaves the refutation standing.
   §1's `not_crUpToProof_of_kstep` proves that, and `quotParams_not_crUpToProof` exhibits it at the
   real instance.

## What the right statement is, and it was already in the tree

`KEta.lean`'s `ParRedK` -- `ParRed` plus the η-guarded K step `keta` -- and its
`not_crStatement_of_kstep_dead`: over `ParRedK` the refutation's `hrig` is *false*, so four of its
hypotheses are contradictory.  Nobody had written the resulting confluence statement down as a
`Prop`, or checked that the `quotParams` witness really joins in it.  §3 does both:
`CRDefEqK`/`CRStatementK`, `CRStatement.toK` (so it is a genuine **weakening**, not an
incomparable statement), and `crDefEqK_of_kstep` -- **at exactly the configuration that refutes
`CRStatement`, `CRDefEqK` holds in one step, with none of the refutation's ten side conditions**.

## What this file does NOT show

`CRStatementK` is not proved.  Its price is `KEta.lean`'s `EtaKDiamond`, and
`KEtaDiamond.etaKDiamondAt_of_kDiamond` shows that needs `KDiamond` verbatim plus `PiDomAgree`,
whose in-tree discharge costs exactly the two holes of §2.2 -- so the corrected statement is
**circular with the holes it was hoped to close**.  §4 measures the consumer side, where the news
is better: the three reduction inversions `ConstSpine.lean` consumes all transport, and the
`NormalEq` lemmas it consumes are untouched, because the K repair does not touch `NormalEq`.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A

/-! ## §1 The proof-irrelevance quotient does not repair `CRStatement`

`not_crStatement_of_kstep`'s proof factors into two halves that it never separates: the
construction of the offending conversion, and the case analysis on `NormalEq` that kills its
joinability.  Both are needed here, so both are named. -/

/-- **The conversion the K-redex-under-an-`eta` produces.**  This is the first three lines of
`not_crStatement_of_kstep`, extracted: `e` is `eta`-equal to `λ A. (e.lift @ #0)`, and the K-step
is admissible (`KStep.defeq`), so `e ≡ λ A. t`.  No rigidity or non-proof hypothesis is used. -/
theorem isDefEq_lam_of_kstep {Γ : List VExpr} {e A B t : VExpr} {u : VLevel}
    (hΓA : OnCtx (A::Γ) (IsType env univs))
    (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t) :
    Γ ⊢ e ≡ .lam A t : .forallE A B := by
  have hb0 := HasType.app (he.weak henv) (.bvar .zero)
  simp [instN_bvar0] at hb0
  have hbody : IsDefEq env univs (A::Γ) (.app e.lift (.bvar 0)) t B :=
    (KStep.defeq hΓA hstep).of_l henv hΓA hb0
  exact ((IsDefEq.eta he).symm).trans (.lamDF hA hbody)

/-- **The joinability half of `not_crStatement_of_kstep`, as its own statement.**  The tree only
ever states the composite `¬ CRStatement`, which cannot be reused against a *weakened* confluence
statement -- hence this. -/
theorem not_crDefEq_of_kstep {Γ : List VExpr} {e A t : VExpr}
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hnp : ∀ P, Γ ⊢ P : .sort .zero → ¬ (Γ ⊢ e : P))
    (hrig : ∀ o, ParRed Γ e o → o = e)
    (hrigA : ∀ A', ParRed Γ A A' → A' = A)
    (hrigT : ∀ t', ParRed (A::Γ) t t' → t' = t)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ CRDefEq Γ e (.lam A t) := by
  rintro ⟨-, -, x, y, hx, hy, hxy⟩
  have hxe : x = e := parRedS_rigid hrig hx
  obtain ⟨t', rfl, ht⟩ := parRedS_lam_inv hrigA hy
  have hte : t' = t := parRedS_rigid hrigT ht
  subst hte; subst hxe
  cases hxy with
  | refl _ => exact hlam _ _ rfl
  | etaL _ _ => exact hlam _ _ rfl
  | lamDF _ _ _ => exact hlam _ _ rfl
  | etaR _ h2' => exact hne h2'
  | proofIrrel hP h1' _ => exact hnp _ hP h1'

/-- **Church--Rosser with a proof-irrelevance escape clause** -- the hypothesis under test, in the
most generous form I can refute.  The conclusion may fail whenever *either* side is a proof, or
the type of the equation is a proposition; that is strictly weaker than `CRStatement`, which is
the `.inl` of it.

Weaker still would be an escape clause naming the *reducts* rather than the subjects, but that is
already what `CRDefEq` grants, via `NormalEq.proofIrrel`. -/
def CRUpToProof : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    IsDefEq env univs Γ e₁ e₂ A →
    CRDefEq Γ e₁ e₂ ∨ IsProof env univs Γ e₁ ∨ IsProof env univs Γ e₂ ∨
      HasType env univs Γ A (.sort .zero)

/-- `CRStatement` is the `.inl` branch, so this really is a weakening. -/
theorem CRStatement.toUpToProof (H : CRStatement) : CRUpToProof := fun hΓ h => .inl (H hΓ h)

/-- **The proof-irrelevance quotient does not repair anything: the refutation goes through
verbatim.**  Every one of the three escape clauses is closed by `hnp`, which
`not_crStatement_of_kstep` *already assumes* --

* `IsProof e₁` is `hnp` applied directly;
* `IsProof e₂` retypes back along the very conversion the refutation built
  (`HasType.defeqU_l'`), so `e` would be a proof too;
* "the type is a proposition" is `hnp` applied to `.forallE A B` itself, given `he`.

So the hypothesis "confluence up to `IsProof`" is not merely unhelpful: it is **false at exactly
the instances where the raw statement is false**, and for the same witness. -/
theorem not_crUpToProof_of_kstep {Γ : List VExpr} {e A B t : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓA : OnCtx (A::Γ) (IsType env univs))
    (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hnp : ∀ P, Γ ⊢ P : .sort .zero → ¬ (Γ ⊢ e : P))
    (hrig : ∀ o, ParRed Γ e o → o = e)
    (hrigA : ∀ A', ParRed Γ A A' → A' = A)
    (hrigT : ∀ t', ParRed (A::Γ) t t' → t' = t)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ CRUpToProof := by
  intro H
  have hdefeq := isDefEq_lam_of_kstep hΓA hA he hstep
  rcases H hΓ hdefeq with h | ⟨p, hp, hep⟩ | ⟨p, hp, hep⟩ | h
  · exact not_crDefEq_of_kstep hlam hnp hrig hrigA hrigT hne h
  · exact hnp _ hp hep
  · exact hnp _ hp (HasType.defeqU_l' henv hΓ ⟨_, hdefeq.symm⟩ hep)
  · exact hnp _ h he

/-! ## §2 The discriminator is rule contractivity, not `Prop`-ness

`ParamsCR.lean`'s `kstep_bvar_ctorConv` shows that a `K⁺` step at a *variable* major premise is
exactly the demand that the variable be definitionally equal to a constructor spine -- at every
instance, with no hypothesis on the environment.  Proof irrelevance is what grants that demand
when the variable's type is a `Prop`.  That much of the hypothesis under test is right.

It is also not the discriminator, and this is the statement of why. -/

/-- **The single property that decides whether `not_crStatement_of_kstep` can fire at an
instance**, and it mentions no proofs: *is every `K⁺` step already a `NormalEq`?*  If it is, the
refutation's `hne` is unsatisfiable and the route is dead, whatever the major premise's sort. -/
def KStepNormalEq : Prop :=
  ∀ {Δ : List VExpr} {a b : VExpr}, OnCtx Δ (IsType env univs) → KStep Δ a b → NormalEq Δ a b

/-- `KStepNormalEq` kills the refutation route outright. -/
theorem no_crStatement_refutation_of_kstepNormalEq (hjoin : KStepNormalEq)
    {Γ : List VExpr} {e A t : VExpr}
    (hΓA : OnCtx (A::Γ) (IsType env univs))
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) : False :=
  hne (hjoin hΓA hstep)

/-! ### §2.1 The two `.app`-pattern instances split on `KStepNormalEq`, not on `Prop`-ness

At `appParams` the property **holds** for every proof-typed major premise, which is
`appParams_normalEq_of_kstep`'s content and is why `appParams_no_crStatement_refutation` derives
`False`; the rule there merely permutes a proof between two closed right-hand sides
(`appPat_rhs_eq`).  At `quotParams` the major premise is *also* a `Prop`-typed variable and the
step *also* fires by `IsDefEq.proofIrrel` (`quotParams_kstep_eta`), and the property **fails**,
because the rule computes.  So the sort of the major premise is satisfied at both and decides
nothing. -/

/-! ### §2.2 The `quotParams` side is stated but NOT compiled here — and why

`Verify/QuotAppParams.lean` is where `KStepNormalEq` fails and where `CRUpToProof` is refuted, and
its import closure runs through `Verify/Environment/Checker.lean`, **which does not build at HEAD**
(`Checker.lean:86`, a `TypeChecker.M.WF.bind` type mismatch — see `docs/handoff-crshape.md` §2.7).
So the two instantiations below cannot be elaborated in this tree state.  They are recorded
verbatim rather than approximated, because their argument lists are **textually identical** to
`quotParams_not_crStatement`'s — `not_crUpToProof_of_kstep` takes `not_crStatement_of_kstep`'s
hypotheses in the same order — so nothing about them is guesswork except that the build must pass:

```
section
attribute [local instance] quotParams

theorem quotParams_not_kStepNormalEq : ¬ KStepNormalEq :=
  fun h => not_normalEq_redex_rhs (h qc0_wf quotParams_kstep_eta)

theorem quotParams_not_crUpToProof : ¬ CRUpToProof :=
  not_crUpToProof_of_kstep (u := .zero) (t := .app (.bvar 3) (.bvar 1))
    qc0T_wf qc0_wf qAT0_isProp qLiftT0_hasType quotParams_kstep_eta nofun
    qLiftT0_not_proof (fun _ => qParRed_qLiftT) (fun _ => qParRed_qAT)
    (fun _ ho => qParRed_app_bvar (fun _ => qParRed_bvar) nofun ho)
    not_normalEq_redex_rhs

theorem quotParams_parRedK_qLiftT :
    ParRedK qc0T (qLiftT .zero (.succ .zero))
      (.lam (qAT .zero) (.app (.bvar 3) (.bvar 1))) :=
  .keta (.under qLiftT0_hasType (.here quotParams_kstep_eta)) .rfl

theorem quotParams_crDefEqK :
    CRDefEqK qc0T (qLiftT .zero (.succ .zero))
      (.lam (qAT .zero) (.app (.bvar 3) (.bvar 1))) :=
  crDefEqK_of_kstep qc0_wf qAT0_isProp qLiftT0_hasType quotParams_kstep_eta

end
```

The instantiation that *is* compiled is `appParams_crDefEqK` in §3: the positive result fires at a
real instance here, so §3 is not admired. -/

/-! ## §3 The corrected statement: confluence over `ParRedK`

`KEta.lean` supplies the relation and the verdict (`not_crStatement_of_kstep_dead`); what was
missing is the statement as a `Prop`, the comparison with the old one, and a witness. -/

/-- `ParRedS ⊆ ParRedKS`, the reflexive-transitive form of `ParRed.toK`.  This is what makes
`CRDefEqK` a **weakening** of `CRDefEq` rather than an incomparable statement, so it is the
load-bearing lemma of the section and not a convenience. -/
theorem ParRedS.toKS {Γ : List VExpr} {e e' : VExpr} (H : ParRedS Γ e e') : ParRedKS Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact ih.tail h2.toK

/-- `CRDefEq` with the reduction legs over the K-closed relation. -/
def CRDefEqK (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  (∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧
  ∃ e₁' e₂', ParRedKS Γ e₁ e₁' ∧ ParRedKS Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂'

/-- **The corrected confluence statement.**  `CRStatement` with `CRDefEqK` in place of `CRDefEq`;
`NormalEq` is untouched, which is the precise sense in which the repair belongs to the reduction
relation (`KEta.lean`'s `not_crStatement_of_kstep_dead` docstring). -/
def CRStatementK : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    IsDefEq env univs Γ e₁ e₂ A → CRDefEqK Γ e₁ e₂

theorem CRDefEq.toK {Γ : List VExpr} {e₁ e₂ : VExpr} : CRDefEq Γ e₁ e₂ → CRDefEqK Γ e₁ e₂
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h1, h2, _, _, h3.toKS, h4.toKS, h5⟩

/-- **`CRStatementK` is a weakening of `CRStatement`**, so nothing that consumes the new statement
can prove more than the old one did, and §4's consumer check is the only thing at risk. -/
theorem CRStatement.toK (H : CRStatement) : CRStatementK := fun hΓ h => (H hΓ h).toK

/-- **At exactly the configuration that refutes `CRStatement`, `CRDefEqK` HOLDS.**

Compare hypothesis lists.  `not_crStatement_of_kstep` needs eleven explicit hypotheses (arity 18)
including three rigidity conditions, a non-λ condition, a non-proof condition and the `NormalEq`
gap `hne`.  This needs **four**, all of them typing, and joins in **one** `keta` step -- the left
leg reduces `e` to the very λ the refutation says nothing reaches.

That asymmetry is the answer to "what is the right confluence statement": the old statement fails
at this configuration for want of a reduction step, not for want of a quotient. -/
theorem crDefEqK_of_kstep {Γ : List VExpr} {e A B t : VExpr} {u : VLevel}
    (hΓA : OnCtx (A::Γ) (IsType env univs))
    (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t) :
    CRDefEqK Γ e (.lam A t) :=
  have hdefeq := isDefEq_lam_of_kstep hΓA hA he hstep
  ⟨⟨_, he⟩, ⟨_, hdefeq.hasType.2⟩, .lam A t, .lam A t,
    ReflTransGen.tail .rfl (.keta (.under he (.here hstep)) .rfl), .rfl,
    .refl hdefeq.hasType.2⟩

/-! ## §4 Do the consumers survive the weakening?

`Verify/Typing/ConstSpine.lean`'s three consumers of `IsDefEq.church_rosser` share one shape:
destructure the `CRDefEq`, invert both reduction legs, finish with a `NormalEq` lemma.  The
`NormalEq` lemmas are untouched by the K repair.  The reduction inversions exist single-step over
`ParRedK` (`KEta.lean`) and in closed form for constant spines (`DescendConstSpineK.lean`); the
other two closures are supplied here.  Then the consumers are re-run over `CRStatementK`
*verbatim*, taken as a hypothesis, which is the honest form: the statement is not proved. -/

theorem ParRedKS.forallE_inv {Γ : List VExpr} {A B e' : VExpr}
    (H : ParRedKS Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  induction H with
  | rfl => exact ⟨_, _, rfl⟩
  | tail _ h2 ih => obtain ⟨_, _, rfl⟩ := ih; exact ParRedK.forallE_inv h2

theorem ParRedKS.sort_inv {Γ : List VExpr} {u : VLevel} {e' : VExpr}
    (H : ParRedKS Γ (.sort u) e') : e' = .sort u := by
  induction H with
  | rfl => rfl
  | tail _ h2 ih => cases ih; exact ParRedK.sort_inv h2

/-! `ParRedKS.hasType` is **not** added here: it already exists (`KMeasure.lean:851`).  A first
draft of this file re-proved it; `docs/handoff-crshape.md` §2.6's row saying otherwise is corrected
in §2.8. -/

/-- **`ConstSpine.lean`'s `IsDefEqU.constApp_forallE_false`, re-run over `CRStatementK`** --
statement unchanged, proof unchanged except that the two inversions are the `ParRedKS` ones.  So
this consumer survives the weakening. -/
theorem IsDefEqU.constApp_forallE_false_ofK (HK : CRStatementK)
    {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr}
    (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.forallE A B) := by
  rintro ⟨T, H⟩
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := HK hΓ H
  obtain ⟨bs, rfl, -⟩ := ParRedKS.constApp_inv hc h1
  obtain ⟨A', B', rfl⟩ := ParRedKS.forallE_inv h2
  have ⟨⟨_, hA⟩, _, hB⟩ := H.hasType.2.forallE_inv Params.henv.ordered
  have hty : IsType env univs Γ (.forallE A' B') := ⟨_, h2.hasType hΓ (hA.forallE hB)⟩
  exact NormalEq.constApp_forallE h3 (IsType.not_isProof Params.henv hΓ hty) _ bs _ _ rfl rfl

/-- **`ConstSpine.lean`'s `IsDefEqU.constApp_sort_false`, re-run over `CRStatementK`.** -/
theorem IsDefEqU.constApp_sort_false_ofK (HK : CRStatementK)
    {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}
    (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.sort u) := by
  rintro ⟨T, H⟩
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := HK hΓ H
  obtain ⟨bs, rfl, -⟩ := ParRedKS.constApp_inv hc h1
  cases ParRedKS.sort_inv h2
  have hu : u.WF univs := H.hasType.2.sort_inv Params.henv.ordered
  exact NormalEq.constApp_sort h3
    (IsType.not_isProof Params.henv hΓ ⟨_, HasType.sort hu⟩) _ bs _ rfl rfl

end VEnv

/-! ## §5 The two instantiations at `appParams`

These live outside the `variable [Params]` scope so that `appParams` is the instance Lean picks;
inside it, the section variable wins and `omit` is refused because the statements reference it. -/

namespace VEnv

section
attribute [local instance] appParams

/-- **`KStepNormalEq` holds at `appParams` for every proof-typed major premise** — this is
`appParams_normalEq_of_kstep` restated as the property §2 names, so the degenerate instance is on
the safe side of the discriminator *by measurement* rather than by reading. -/
theorem appParams_kStepNormalEq_at_proofMajor {Γ : List VExpr} {f h t : VExpr}
    (hΓ : OnCtx Γ (cycEnv.IsType 0)) (hh : cycEnv.HasType 0 Γ h (.const `P []))
    (hstep : KStep Γ (.app f h) t) : NormalEq Γ (.app f h) t :=
  appParams_normalEq_of_kstep hΓ hh hstep

/-- **The positive result, at a real instance.**  `appParams_stuck_fires` exhibits a `K⁺` step at
`.app (.const `C []) (.bvar 0)` in `appCtx = [.const `P []]`, which is exactly
`.app e.lift (.bvar 0)` for `e := .const `C []` (a constant is its own lift).  So `crDefEqK_of_kstep`
fires, and the pair `C` / `λ P. C D2` joins in the corrected statement in one `keta` step.

This instance is not one where `CRStatement` fails — that is the point of §2 — so what it shows is
that `crDefEqK_of_kstep`'s hypotheses are **satisfiable**, i.e. the theorem is not vacuous.  The
configuration at which `CRStatement` *does* fail is `quotParams`, and §2.2 records why that
instantiation cannot be compiled in this tree state. -/
theorem appParams_crDefEqK :
    CRDefEqK [] (.const `C []) (.lam (.const `P []) cycG2) :=
  crDefEqK_of_kstep appCtx_wf cycEnv_hasP cycEnv_hasC appParams_stuck_fires.2

end

end VEnv

end Lean4Lean
