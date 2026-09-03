import Lean4Lean.Verify.QuotAppParams
import Lean4Lean.Theory.Typing.DescendConstSpineK

/-!
# Anti-vacuity: is `ParRedK.constApp_inv`'s `keta` case ever exercised?

`Theory/Typing/DescendConstSpineK.lean` ports `Verify/Typing/ConstSpine.lean`'s
`ParRed.constApp_inv` — the load-bearing reduction lemma on `descend`'s critical-path chain to
`Bridge.kernel_sound_of` — from `ParRed`'s eight constructors to `ParRedK`'s nine, and
discharges the ninth (`keta`) with `EtaK.constApp_free`.  Its own §3 then records the honest
limit: that case is **vacuous at every `Params` instance in `Theory/`**
(`propLoop_no_etaK`), because `EtaK` fires only where an `.app` pattern is registered
(`EtaK.matches_head`) and every Theory-side table — `refNoPat`, `cycNoPat`,
`propLoopParams` — is δ-only.  It names `Verify/QuotAppParams.lean`'s `quotParams` as the first
instance that could test it, and `Theory/` may not import `Verify/`.

**This file runs that check at `quotParams`.**  It lives in `Verify/Typing/` because
`quotParams` is in `Verify/` and a `Theory/` file may not import it.

**But the premise that the check *needs* `Verify/` is false, and that correction is the more
important half of this round.**  The enumeration above omits a fourth `Theory/` instance:
`Theory/Typing/PatAppParams.lean`'s `appParams` (`:221`), which registers **two `.app`
patterns** and carries **no holes at all**.  So the same check runs inside `Theory/`,
`sorryAx`-free, and it is in `Theory/Typing/QuotKAppEta.lean` (this round) — which also shows
the tree already held everything the check needed on **2026-09-01**, two days before
`DescendConstSpineK.lean` claimed otherwise (`appParams_keta_refutes_unhypothesised_pre`).  Read
the two together:

* `QuotKAppEta.lean` — hole-free, but at an **artificial rule table**: `cycEnv` registers no
  defeq whatsoever, while `AppPat` claims two rules, which `Params` permits (`extra_pat`
  constrains the table only in the other direction).
* this file — the **canonical** table, the real `Quot.lift`/`Quot.mk` rule of an environment
  `Verify/QuotConsts.lean` shows refines a real `Environment`; the price is `quotParams`' two
  holes.

Neither alone answers "does the real kernel reach the `keta` case"; the pair bounds it from both
sides, and that distinction is the point.

## What the check finds — three different questions, three different answers

The phrase "the `keta` case fires" hides a distinction that this file separates, because two of
the three readings are settled by *theorems* and only the third is an instance measurement.

1. **Is `EtaK` inhabited at all?**  At `propLoopParams`: no (`propLoop_no_etaK`) — but that is a
   fact about *that* instance and not about `Theory/`, and the tree has had a hole-free `Theory/`
   inhabitant at `appParams` since 2026-09-01 (`KEtaDiamond.appParams_etaK_under`).  At
   `quotParams`: **yes** — `quot_etaK_here` and `quot_etaK_under`, the first concrete `EtaK`
   inhabitants at the *canonical* table.  So `ParRedK`'s ninth constructor is a step
   that really moves, and `quot_parRedK_keta` is a `ParRedK` derivation whose *only* step is
   `keta`.
2. **Can the `keta` branch of `constApp_inv` be entered with its hypothesis satisfied?**
   **No — at no instance, ever.**  That is not an absence claim about this tree, it is the
   content of `EtaK.constApp_free`, repackaged here as `keta_branch_unreachable`:
   `PatFreeHead c` and `EtaK Γ ((.const c ls).mkApp as) e'` are jointly contradictory for every
   `Params`, every `c` and every table.  So the branch can never return a witness; it is
   discharged by contradiction, in the same class as `constApp_inv`'s `extra`, `bvar`, `sort`,
   `lam` and `forallE` cases.  A search for an instance where it "fires" in the
   returns-a-witness sense is a search for a contradiction, and must not be reported as a gap.
3. **Is the hypothesis load-bearing *in the `keta` case specifically*?**  This is the real
   measurement, it is the one `Theory/` could not make, and at `quotParams` the answer is
   **yes**: `quot_keta_needs_hyp`, and hole-free at `appParams`
   (`appParams_keta_refutes_unhypothesised`, which derives `False` from `constApp_inv`'s
   statement with `PatFreeHead` deleted).  A genuine `EtaK` step fires at a real constant spine —
   the six-argument `Quot.lift` redex — whose head is `Quot.lift`; the reduct `g x` is no
   `Quot.lift`-headed spine at all; and the single thing standing between that derivation and a
   refutation of `constApp_inv` is `PatFreeHead ``Quot.lift``, which is **false** here
   (`quot_not_patFreeHead`).  Before this round the same control existed only for the `extra`
   constructor (`propLoop_constApp_inv_needs_hyp`).

Read together: reading 1 upgrades `propLoop_no_etaK`'s "untested content" to "tested", reading 3
supplies the control, and reading 2 says the residue is not a gap but a theorem.  The `keta`
branch is exercised, and it is exercised in the only way it can be.

## The control is a control, per `ForallInvPrice.lean`'s discipline

`quot_keta_needs_hyp` is **not** a refutation of `ParRedK.constApp_inv`.  The environment is
legitimate (`quotVEnv_wf : qEnv.WF`, and `Verify/QuotConsts.lean` shows it refines a real
`Environment`), the table is non-empty and registers exactly one pattern (`pat_qEnv_eq`), and
what fails at `Quot.lift` is the *hypothesis*, not the conclusion.  The positive half is
`quot_patFreeHead` — `PatFreeHead c` holds for every other head — and `quot_constApp_inv_fires`
applies `ParRedK.constApp_inv` at one of them (`Quot.mk`) to a reduction that really moves a
β-redex inside the spine.  So the theorem is inhabited *and* bounded at the same instance.

## Axioms: what this inherits, stated separately from hole-freeness

Every declaration here is `sorry`-free in its own text.  Everything in the `quotParams` section
inherits that instance's two holes and adds none: `quotParams := paramsOfPiInv …
(piInv_axiom …)`, so `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS` are in the
cone of anything stated at it (`QuotAppParams.lean`'s header measures this).  The two
instance-independent facts (`qKRedex_eq`, `quotPat_headConst`) and
`keta_branch_unreachable` — which quantifies over `Params` rather than fixing one — do not.
`#print axioms` readings are in `docs/handoff-quotk.md`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

/-! ## 1. Instance-independent: the branch is unreachable under its own hypothesis -/

/-- **Reading 2, stated as the theorem it is.**  At *every* `Params` instance, `constApp_inv`'s
`keta` branch cannot be entered with its hypothesis satisfied: a rule-free head and an `EtaK`
step at a spine on that head are jointly contradictory.  This is `EtaK.constApp_free` turned
around, and it is why no instance — real, artificial, or yet to be written — can make the branch
return a witness rather than a contradiction. -/
theorem keta_branch_unreachable [Params] {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {e' : VExpr} :
    ¬ (PatFreeHead c ∧ EtaK Γ ((VExpr.const c ls).mkApp as) e') :=
  fun ⟨hc, h⟩ => EtaK.constApp_free hc h

/-! ## 2. The two redexes, as explicit constant spines

`constApp_inv`'s `keta` case is entered only when the redex is syntactically
`(VExpr.const c ls).mkApp as`.  Both `QuotAppParams.lean` witnesses are of that shape, and
these two `rfl`s are what says so. -/

/-- The `u = 1` `K⁺` redex (`quotParams_kstep_x`) as a six-argument `Quot.lift` spine. -/
def qKRedex : VExpr :=
  (VExpr.const ``Quot.lift [.succ .zero, .succ .zero]).mkApp
    [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 2, qMk (.succ .zero) (.bvar 1)]

theorem qKRedex_eq :
    qKRedex = .app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)) := rfl

/-- The `u = 0` η-layer's subject (`quotParams_kstep_eta` seen from the shorter context) as a
five-argument `Quot.lift` spine. -/
def qKRedexT : VExpr :=
  (VExpr.const ``Quot.lift [.zero, .succ .zero]).mkApp
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]

theorem qKRedexT_eq : qKRedexT = qLiftT .zero (.succ .zero) := rfl

/-- The registered pattern's head constant. -/
theorem quotPat_headConst : quotPat.headConst = ``Quot.lift := rfl

/-- **Why the `sorryAx` on §§3–5 is syntactic and not semantic.**  `EtaK` reads exactly three
`Params` fields — `env`, `univs` and `Pat` — and all three are `rfl`-equal at `quotParams` to
hole-free data: `quotParams_env`, `quotParams_univs` (both in `QuotAppParams.lean`) and this.
Together with `quot_etaK_premises_sat` below, that is the argument that the `EtaK` step is real
content of the canonical rule table and not an artefact of `piInv_axiom`.  It is an *argument*,
not a theorem: a fully hole-free version would need a `Params`-free copy of `KStep`/`EtaK`, which
this file does not build. -/
theorem quotParams_Pat_eq : @Params.Pat quotParams = Pat qEnv := rfl

section
attribute [local instance] quotParams

/-! ## 3. Reading 1: `EtaK` is inhabited — the ninth constructor really moves -/

/-- **`EtaK` is inhabited, via `here`.**  The first concrete `EtaK` inhabitant in the tree:
`Theory/` has none, because `propLoop_no_etaK` says it cannot. -/
theorem quot_etaK_here : EtaK qc1 qKRedex (.app (.bvar 3) (.bvar 1)) :=
  .here (qKRedex_eq ▸ quotParams_kstep_x)

/-- **…and via `under`**, which is the layer `matches_head`'s inductive case exists for: the
η-expansion `.app (qLiftT).lift (.bvar 0)` is the `K⁺` redex, fired by proof irrelevance at
`u = 0`, and the subject one context shorter is still a `Quot.lift` spine.  This is the witness
that exercises `constApp_free`'s `headConst?_liftN` route rather than only its base case. -/
theorem quot_etaK_under :
    EtaK qc0T qKRedexT (.lam (qAT .zero) (.app (.bvar 3) (.bvar 1))) :=
  .under qLiftT0_hasType (.here quotParams_kstep_eta)

/-- A `ParRedK` derivation whose only step is `keta`.  So the ninth constructor is not
decoration at this instance. -/
theorem quot_parRedK_keta : ParRedK qc1 qKRedex (.app (.bvar 3) (.bvar 1)) :=
  .keta_step quot_etaK_here

/-! ## 4. Reading 3: the hypothesis is load-bearing in the `keta` case -/

/-- The rule head is **not** rule-free here — the negative half of the control. -/
theorem quot_not_patFreeHead : ¬ PatFreeHead ``Quot.lift :=
  fun h => h _ _ quotParams_pat_app quotPat_headConst

/-- The positive half: at the *same* instance, every other head is rule-free.  `pat_qEnv_eq`
is what makes this sharp — `quotPat` is the only registered pattern. -/
theorem quot_patFreeHead {c : Lean.Name} (hc : c ≠ ``Quot.lift) : PatFreeHead c := by
  intro p r h
  obtain rfl := pat_qEnv_eq h
  rw [quotPat_headConst]
  exact fun h' => hc h'.symm

/-- The reduct is no `Quot.lift`-headed spine: its spine head is the variable `g`. -/
theorem quot_keta_target_not_spine (ls : List VLevel) (as' : List VExpr) :
    (VExpr.app (.bvar 3) (.bvar 1) : VExpr) ≠ (VExpr.const ``Quot.lift ls).mkApp as' := by
  intro h
  have h1 := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at h1
  simp [VExpr.spineHead] at h1

/-- **The measurement `Theory/` could not make.**  `ParRedK.constApp_inv`'s `keta` case is
entered by a real derivation at a real constant spine, whose reduct violates the conclusion, and
the only thing that stops it is the hypothesis — which fails at this head.  Dropping
`PatFreeHead` therefore breaks the lemma *through the ninth constructor alone*, not merely
through `extra` as `propLoop_constApp_inv_needs_hyp` already showed.

Per `ForallInvPrice.lean`'s discipline this is a control and not a refutation: see
`quot_patFreeHead` for the positive half and the module docstring for why the environment is
legitimate. -/
theorem quot_keta_needs_hyp :
    EtaK qc1 qKRedex (.app (.bvar 3) (.bvar 1)) ∧
      ParRedK qc1 ((VExpr.const ``Quot.lift [.succ .zero, .succ .zero]).mkApp
          [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 2, qMk (.succ .zero) (.bvar 1)])
        (.app (.bvar 3) (.bvar 1)) ∧
      ¬ PatFreeHead ``Quot.lift ∧
      (∀ ls as', (VExpr.app (.bvar 3) (.bvar 1) : VExpr) ≠
        (VExpr.const ``Quot.lift ls).mkApp as') :=
  ⟨quot_etaK_here, quot_parRedK_keta, quot_not_patFreeHead, quot_keta_target_not_spine⟩

/-! ## 5. The theorem is inhabited at this instance too, non-trivially -/

/-- A `Quot.mk` spine whose third argument is a β-redex really reduces. -/
theorem quot_parRedK_mkSpine :
    ParRedK qc1 ((VExpr.const ``Quot.mk [.succ .zero]).mkApp [.bvar 6, .bvar 5, qXbeta])
      ((VExpr.const ``Quot.mk [.succ .zero]).mkApp [.bvar 6, .bvar 5, .bvar 1]) :=
  .app (.app (.app .const .bvar) .bvar) (.beta .bvar .bvar)

/-- **Positive control: `ParRedK.constApp_inv` fires at `quotParams`.**  At the rule-free head
`Quot.mk` the lemma applies to a reduction that really moves, and hands back the argument-wise
developments.  So the instance is not one where the theorem is vacuous for want of a reduction;
only its `keta` branch is, and reading 2 says that is a theorem. -/
theorem quot_constApp_inv_fires :
    ∃ as', ((VExpr.const ``Quot.mk [.succ .zero]).mkApp [.bvar 6, .bvar 5, .bvar 1]) =
        (VExpr.const ``Quot.mk [.succ .zero]).mkApp as' ∧
      List.Forall₂ (ParRedK qc1) [.bvar 6, .bvar 5, qXbeta] as' :=
  ParRedK.constApp_inv (quot_patFreeHead (by decide)) quot_parRedK_mkSpine

/-- **Instance-level vacuity, sharper than `propLoop_no_etaK`.**  At `quotParams` `EtaK` *is*
inhabited, and yet no `EtaK` step fires at a spine on any rule-free head.  The two facts
together are the precise statement of what the `keta` branch's discharge buys. -/
theorem quot_no_etaK_at_patFree {Γ : List VExpr} {c : Lean.Name} (hc : c ≠ ``Quot.lift)
    {ls : List VLevel} {as : List VExpr} {e' : VExpr} :
    ¬ EtaK Γ ((VExpr.const c ls).mkApp as) e' :=
  fun h => EtaK.constApp_free (quot_patFreeHead hc) h

end

/-! ## 6. Instrument 7: the `EtaK` witnesses' premises, hole-free

Everything in §§3–5 mentions `quotParams` and therefore inherits its two holes.  That could be
read as "the `EtaK` step needs Π-injectivity", which is **false** and worth saying so as a
theorem: what needs `PiInv` is *packaging `qEnv` as a `Params` instance*, not any premise of the
`K⁺` step.  Below is every premise `KStep.mk` and `EtaK.under` consume for both witnesses,
stated without mentioning any instance — `sorryAx`-free, measured.  So the `EtaK` firing is real
content of the canonical rule table, and the holes sit only in the instance wrapper. -/

theorem quot_etaK_premises_sat :
    ∃ m1 m2 m1' m2',
      Pat qEnv quotPat (quotRHS, quotCheck) ∧
      -- the `u = 1` `EtaK.here` witness
      quotPat.Matches
          (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1))) m1 m2 ∧
      quotCheck.OK (qEnv.IsDefEqU 0 qc1) m1 m2 ∧
      qEnv.HasType 0 qc1 (qLift (.succ .zero) (.succ .zero))
        (.forallE (qA (.succ .zero)) (.bvar 5)) ∧
      qEnv.IsDefEq 0 qc1 (qMk (.succ .zero) (.bvar 1)) (qMk (.succ .zero) (.bvar 1))
        (qA (.succ .zero)) ∧
      Pattern.RHS.apply m1 m2 quotRHS = .app (.bvar 3) (.bvar 1) ∧
      -- the `u = 0` `EtaK.under` witness: the same, one context shorter, with the major
      -- premise supplied by proof irrelevance and the η-layer's typing premise
      quotPat.Matches (.app (qLift .zero (.succ .zero)) (qMk .zero (.bvar 1))) m1' m2' ∧
      quotCheck.OK (qEnv.IsDefEqU 0 qc0) m1' m2' ∧
      qEnv.HasType 0 qc0 (qLift .zero (.succ .zero)) (.forallE (qA .zero) (.bvar 5)) ∧
      qEnv.IsDefEq 0 qc0 (.bvar 0) (qMk .zero (.bvar 1)) (qA .zero) ∧
      qEnv.HasType 0 qc0T (qLiftT .zero (.succ .zero)) (.forallE (qAT .zero) (.bvar 4)) ∧
      Pattern.RHS.apply m1' m2' quotRHS = .app (.bvar 3) (.bvar 1) := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches (.succ .zero) (.succ .zero) (.bvar 1)
  obtain ⟨m1', m2', hm', hrhs', hck'⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  exact ⟨m1, m2, m1', m2', quotVEnv_pat_app, hm, hck, qLift1_hasType,
    (qMk1_hasType qT_x), hrhs, hm', hck', qLift0_hasType,
    .proofIrrel qA0_isProp qT_prf (qMk0_hasType qT_x), qLiftT0_hasType, hrhs'⟩

end VEnv
end Lean4Lean
