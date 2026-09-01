import Lean4Lean.Verify.QuotConsts
import Lean4Lean.Theory.Typing.PatAppParams
import Lean4Lean.Theory.Typing.PatWFIota
import Lean4Lean.Theory.SetModel.NotProofNoModel

/-!
# The canonical `.app`-pattern `Params` instance — and it refutes `KDiamond`, M3,
`NormalEq.parRed` and `IsDefEq.church_rosser`

`Theory/Typing/PatAppParams.lean` built `appParams`, the first `Params` instance registering
`.app` patterns, and flagged two things about it: `PatMajorCanonical` (M3) holds there **without
using any of its typing premises**, because both right-hand sides are closed and mutually
`NormalEq`; and the canonical instance -- the quotient rule over a real `VEnv.WF` environment --
was "one `PiInv` away", with its environment half already built in `Verify/QuotConsts.lean`.

This file builds that instance and measures it.  It lives in `Verify/` because
`Verify/QuotConsts.lean` is where the environment is, and `Theory/` cannot import `Verify/`.

## The four results

Write `α r β g cc` for the five arguments of the matched `Quot.lift` spine and `x` for the
`Quot.mk` argument, so the rule's right-hand side is `g x`.

1. **M3 is FALSE here** (`quotParams_not_patMajorCanonical`).  The two matched major premises
   `Quot.mk α r x` and `Quot.mk α r ((fun y => y) x)` are definitionally equal **by β**, both
   typed by `Quot.{1} α r`; M3 then demands `NormalEq (g x) (g ((fun y => y) x))`, and
   `NormalEq` has no β step.  So M3's typing premises are not merely *used* here -- they are
   *all* that is left, and they do not suffice, because the statement is wrong.
2. **`KDiamond` is FALSE here** (`quotParams_not_kDiamond`), by the same witness: `KStep`'s
   `hdq` is an arbitrary `IsDefEq`, so one redex has two `K⁺` steps with those two major
   premises.  This is the object `kDiamond_of_patMajorCanonical` reduces confluence *to*, and
   `KEtaDiamond.etaKDiamondAt_of_kDiamond` consumes.
3. **…and the rule table is not at fault** (`quotParams_kDiamond_joinable`): the two reducts are
   **joinable** in one β-step.  So the defect is `KDiamond`'s demand that the two reducts be
   `NormalEq` *on the nose*; the joinability shape `KEta.lean`'s `EtaKDiamond` already uses
   survives this witness.  The repair is a restatement, not a new rule-table field.
4. **`NormalEq.parRed`'s and `IsDefEq.church_rosser`'s statements are refuted here**
   (`quotParams_not_parRedStatement`, `quotParams_not_crStatement`), i.e.
   `ParRedPropRefute.lean`'s and `KCanonical.lean`'s refutations become **reachable**.  This
   corrects `PatAppParams.lean`'s closing note and ledger row 96c, which say those need "a
   `Prop` major premise with a `Type`-valued right-hand side, i.e. an `addInduct'` witness
   *and* `PiInv`", on the grounds that "`Quot.mk r a` is **not** a proof of a `Prop`".  It can
   be: `quotConst`'s type is `(α : Sort u) → (α → α → Prop) → Sort u`, so **at `u = 0`
   `Quot.{0} α r` is a proposition**, while `β` is free to be `Type 0`.  The quotient rule
   supplies the `Eq.rec` shape by itself; no inductive block is needed.

## What is clean and what is not

**Clean (`sorryAx`-free, measured):** the environment (`quotVEnv_wf`), the rule
(`quotVEnv_pat_app`), the classification `pat_qEnv_eq` (only `quotPat` is registered), the
witness contexts and every typing fact in them (`qc1_wf`, `qc0_wf`, `qc0T_wf`, `qLift1_hasType`,
`qLift0_hasType`, `qLiftT0_hasType`, `qA0_isProp`, `qAT0_isProp`, `qMk*_hasType`,
`qLiftType0_hasType`, `qT_*`), the matches with their computed right-hand sides and discharged
`Check` (`quot_matches`), the β-conversion of the two major premises (`qMk1_defeq`,
`qXbeta_hasType`), `quotPat_matches_mk` and `qLiftT_lift` (axiom-free), the instrument-7 check
`quotParams_m3_hyps_sat`, and `quotRHS_depends_on_match` -- the sharp reason `appParams`'
shortcut is unavailable: two matches at the **same** function side already have syntactically
different right-hand sides.

**Tainted only by mentioning the instance** (`ParRed`, `NormalEq`, `KStep` are all stated
`[Params]`-relative, so any statement about them at `quotParams` inherits `PiInv`): the
`ParRed`-rigidity family `qParRed_*` -- whose content is the instance-independent
`pat_qEnv_eq` -- and `quotParams_kDiamond_joinable`.

**Modulo two open holes, and exactly two.**  Measured with a forward hole-cone over this
module: the cone of every one of the four results contains exactly the sorry sites
`IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`, and nothing else.  They enter by
two routes:

* the **instance** needs `PiInv` (`paramsOfPiInv … (piInv_axiom …)`);
* the **`proofIrrel` blocks** need "this term is not a proof", which `qEnv_not_proof` gets from
  `WF.propTypeAgreeOn` (`SetModel/NotProofNoModel.lean`) -- a theorem *from `VEnv.WF`*, whose
  cone is `forallE_inv_stratified` alone.

So nothing here adds an obligation, and the refutations are as real as Π-injectivity and unique
typing -- both of which the project is trying to *prove*, not doubt.  Ledger row 33's grade for
these refutations therefore moves from "refuted only at an instance that does not exist" to
"refuted at an instance conditional on the injectivity corner".  It is **not** an unconditional
refutation, and must not be quoted as one.

## `KStep`'s major-premise conversion: both sources, and the second is the new one

`appParams` was cheap because its only conversion was proof irrelevance and its right-hand
sides were closed.  Here:

* at `u = 0` (`quotParams_kstep_eta`) `hdq` is discharged by **proof irrelevance** exactly as at
  `appParams` -- that is what makes items 2/3 fire;
* at `u = 1` (`quotParams_kstep_xbeta`) proof irrelevance is unavailable (`α : Type 0`) and
  `hdq` is discharged by **β**.  That conversion is invisible at `appParams`, whose right-hand
  sides do not mention the matched arguments, and it is what refutes M3 and `KDiamond`.

## Warning for consumers

`KEtaDiamond.etaKDiamondAt_of_kDiamond` and anything else deriving from `KDiamond` is now
deriving from a hypothesis that is **false at a concrete instance modulo the injectivity
corner**.  Those derivations are still true implications, but they cannot be discharged; the
premise has to be reshaped into the joinability form (result 3) first.  Likewise the four call
sites of `IsDefEq.church_rosser` in `Verify/Typing/ConstSpine.lean` and `Rigidity.lean` rest on
a statement that is false in the same sense: `ParRed` is missing the K-step, so the K-redex
`.app f (.bvar 0)` is `ParRed`-normal while being definitionally equal to `g x`, and
joinability collapses to `NormalEq` between two normal terms.  That is exactly the
`ParRed`-vs-`ParRedK` repair `KEta.lean` and ledger row 78b already name -- now with a
reachable witness.
-/
namespace Lean4Lean
namespace VEnv
open Lean4Lean.VExpr

/-! ## 1. The instance -/

/-- The concrete `VEnv.WF` environment that carries the quotient rule: `Eq` as an axiom, then
`addQuot`.  `Verify/QuotConsts.lean` builds it and proves it refines a real `Environment`. -/
abbrev qEnv : VEnv := quotVEnv QuotWit.venvEq

theorem quotVEnv_wf : qEnv.WF := (QuotWit.trEnv_addQuot_wit (safety := .safe)).wf

theorem quotVEnv_pat_app : Pat qEnv quotPat (quotRHS, quotCheck) :=
  .quot QuotWit.quotVEnv_venvEq_contents.2.2.2.2.2
    QuotWit.quotVEnv_venvEq_contents.2.2.1 QuotWit.quotVEnv_venvEq_contents.2.1

/-- **The canonical `.app`-pattern instance.**  `sorryAx`-tainted through `PiInv` and nothing
else. -/
@[instance_reducible] def quotParams : Params :=
  paramsOfPiInv quotVEnv_wf 0 (piInv_axiom quotVEnv_wf)

theorem quotParams_env : @Params.env quotParams = qEnv := rfl
theorem quotParams_univs : @Params.univs quotParams = 0 := rfl

/-- The instance registers the quotient rule's `.app` pattern. -/
theorem quotParams_pat_app : @Params.Pat quotParams quotPat (quotRHS, quotCheck) :=
  quotVEnv_pat_app

theorem qEnv_Quot : qEnv.constants ``Quot = some quotConst := rfl
theorem qEnv_QuotMk : qEnv.constants ``Quot.mk = some quotMkConst := rfl
theorem qEnv_QuotLift : qEnv.constants ``Quot.lift = some quotLiftConst := rfl
theorem qEnv_Eq : qEnv.constants ``Eq = some eqConst := rfl

theorem qEnv_defeqs {df} (h : qEnv.defeqs df) : df = quotDefEq := by
  rcases h with h | h
  · exact h
  · exact absurd h (by simp [QuotWit.venvEq, VEnv.insertConst, VEnv.empty])

theorem qEnv_constants {n ci} (h : qEnv.constants n = some ci) :
    n = ``Quot ∨ n = ``Quot.mk ∨ n = ``Quot.lift ∨ n = ``Quot.ind ∨ n = ``Eq := by
  by_cases h1 : ``Quot = n
  · exact .inl h1.symm
  by_cases h2 : ``Quot.mk = n
  · exact .inr (.inl h2.symm)
  by_cases h3 : ``Quot.lift = n
  · exact .inr (.inr (.inl h3.symm))
  by_cases h4 : ``Quot.ind = n
  · exact .inr (.inr (.inr (.inl h4.symm)))
  by_cases h5 : ``Eq = n
  · exact .inr (.inr (.inr (.inr h5.symm)))
  exact absurd h (by
    simp [quotVEnv, VEnv.addDefEq, VEnv.insertConst, QuotWit.venvEq, VEnv.empty,
      h1, h2, h3, h4, h5])

/-- **`quotPat` is the *only* pattern the instance registers.**  The δ case cannot fire (the
environment's only rule has a `.lam` left-hand side, not a `.const` one) and the ι case cannot
(no name in the environment is a `rec` name).  Used for the `ParRed`-rigidity facts below. -/
theorem pat_qEnv_eq {p r} (h : Pat qEnv p r) : p = quotPat := by
  cases h with
  | delta _ hdf => exact absurd (qEnv_defeqs hdf) (by simp [quotDefEq])
  | iota _ _ _ _ _ hrec => rcases qEnv_constants hrec with h|h|h|h|h <;> simp [Lean.mkRecName] at h
  | quot => rfl

/-! ## 2. "Not a proof", modulo the injectivity holes -/

/-- **A term whose type lives in a non-`Prop` sort is not a proof.**  `WF.propTypeAgreeOn`
(`SetModel/NotProofNoModel.lean`) is a theorem *from `VEnv.WF`*, `sorryAx`-tainted through
`forallE_inv_stratified` / `rigidShapeUniq` — i.e. through exactly the corner `PiInv` already
taints, and adding no new obligation. -/
theorem qEnv_not_proof {Γ : List VExpr} {e A p : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (qEnv.IsType 0)) (hu : u.WF 0) (hne : u.eval [] ≠ 0)
    (he : qEnv.HasType 0 Γ e A) (hA : qEnv.HasType 0 Γ A (.sort u))
    (hp : qEnv.HasType 0 Γ e p) (hpp : qEnv.HasType 0 Γ p (.sort .zero)) : False :=
  hne ((quotVEnv_wf.propTypeAgreeOn (nv := 0) (u := u) (u' := .zero) (ls := [])
    hΓ hu trivial he hp hA hpp).2 rfl)

/-! ## 3. The witness context -/

/-- The context of the witnesses: `α : Sort u`, `r : α → α → Prop`, `β : Sort v`, `g : α → β`,
`cc : ∀ y z, r y z → g y = g z`, `x : α`, and one extra inhabitant of `Quot.{u} α r`. -/
def qCtx (u v : VLevel) : List VExpr :=
  [ .app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4),
    .bvar 4,
    .forallE (.bvar 3) (.forallE (.bvar 4)
      (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
        (.app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
          (.app (.bvar 3) (.bvar 1))))),
    .forallE (.bvar 2) (.bvar 1),
    .sort v,
    .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort u]

/-- The pattern's function side: the five-argument `Quot.lift` spine. -/
def qLift (u v : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.lift [u, v]) (.bvar 6)) (.bvar 5)) (.bvar 4))
    (.bvar 3)) (.bvar 2)

/-- `Quot.{u} α r`: the domain of the redex, and the type of every major premise. -/
def qA (u : VLevel) : VExpr := .app (.app (.const ``Quot [u]) (.bvar 6)) (.bvar 5)

/-- The pattern's major-premise side: a `Quot.mk` spine at an arbitrary third argument. -/
def qMk (u : VLevel) (t : VExpr) : VExpr :=
  .app (.app (.app (.const ``Quot.mk [u]) (.bvar 6)) (.bvar 5)) t

/-- `(fun y : α => y) x` — a β-redex of type `α`, definitionally equal to `x` and *not*
`NormalEq` to it. -/
def qXbeta : VExpr := .app (.lam (.bvar 6) (.bvar 0)) (.bvar 1)

section
variable {u v : VLevel}

theorem qT_alpha : qEnv.HasType 0 (qCtx u v) (.bvar 6) (.sort u) := .bvar (by lookup_tac)
theorem qT_r : qEnv.HasType 0 (qCtx u v) (.bvar 5)
    (.forallE (.bvar 6) (.forallE (.bvar 7) (.sort .zero))) := .bvar (by lookup_tac)
theorem qT_beta : qEnv.HasType 0 (qCtx u v) (.bvar 4) (.sort v) := .bvar (by lookup_tac)
theorem qT_g : qEnv.HasType 0 (qCtx u v) (.bvar 3) (.forallE (.bvar 6) (.bvar 5)) :=
  .bvar (by lookup_tac)
theorem qT_x : qEnv.HasType 0 (qCtx u v) (.bvar 1) (.bvar 6) := .bvar (by lookup_tac)
theorem qT_prf : qEnv.HasType 0 (qCtx u v) (.bvar 0) (qA u) := .bvar (by lookup_tac)

/-- `g x : β`, the shape of the rule's right-hand side. -/
theorem qT_gx {t} (ht : qEnv.HasType 0 (qCtx u v) t (.bvar 6)) :
    qEnv.HasType 0 (qCtx u v) (.app (.bvar 3) t) (.bvar 4) := .app' qT_g ht rfl

/-- **The pattern matches, the right-hand side is `g t`, and the rule's `Check` holds.**
Note the right-hand side depends on the *matched* argument `t`: unlike `appParams`, this
table's right-hand sides are not closed. -/
theorem quot_matches (u v : VLevel) (t : VExpr) :
    ∃ m1 m2, quotPat.Matches (.app (qLift u v) (qMk u t)) m1 m2 ∧
      Pattern.RHS.apply m1 m2 quotRHS = .app (.bvar 3) t ∧
      quotCheck.OK (qEnv.IsDefEqU 0 (qCtx u v)) m1 m2 := by
  refine ⟨_, _, .app (.var (.var (.var (.var (.var .const))))) (.var (.var (.var .const))),
    rfl, ?_⟩
  refine iotaCheck_OK.2 ⟨?_, by simp, ?_⟩
  · rw [show ((Pattern.argPaths (Pattern.const ``Quot.lift) 5).take 2).zip
        ((Pattern.argPaths (Pattern.const ``Quot.mk) 3).take 2)
        = [(some (some (some (some none))), some (some none)),
           (some (some (some none)), some none)] from rfl]
    intro xy hxy
    cases hxy with
    | head => exact ⟨_, qT_alpha⟩
    | tail _ h2 => cases h2 with
      | head => exact ⟨_, qT_r⟩
      | tail _ h3 => nomatch h3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact rfl

end

/-! ### Inverting `quotPat.Matches`

The only fact needed downstream: a match forces the *major-premise* side to be a three-deep
`Quot.mk` spine.  Every `.app` node inside the witness redex has a `bvar` on its right, so this
one lemma refutes `ParRed.extra` at every subterm. -/

theorem quotPat_matches_mk {e m1 m2} (h : quotPat.Matches e m1 m2) :
    ∃ f ls b1 b2 b3,
      e = .app f (.app (.app (.app (.const ``Quot.mk ls) b1) b2) b3) := by
  replace h : (Pattern.app (.varN (.const ``Quot.lift) 5) (.varN (.const ``Quot.mk) 3)).Matches
      e m1 m2 := h
  cases h with
  | app _ h2 =>
    cases h2 with
    | var h2 => cases h2 with
      | var h2 => cases h2 with
        | var h2 => cases h2 with
          | const => exact ⟨_, _, _, _, _, rfl⟩

/-! ### The right-hand side is NOT closed — why `appParams`' shortcut is unavailable

`PatAppParams.lean`'s `appPat_rhs_eq` says every right-hand side of *that* table is one of two
closed terms, which is exactly why its `PatMajorCanonical` proof never touches M3's typing
premises.  Here the right-hand side is `g t` for the *matched* argument `t`, so two matches at
the **same function side** already give syntactically different right-hand sides.  This is
`sorryAx`-free and mentions no `Params` instance: it is a fact about the canonical rule table,
not about the witness. -/

theorem quotRHS_depends_on_match :
    ∃ m1 m2 m1' m2',
      quotPat.Matches (.app (qLift .zero (.succ .zero)) (qMk .zero (.bvar 1))) m1 m2 ∧
      quotPat.Matches (.app (qLift .zero (.succ .zero)) (qMk .zero (.bvar 0))) m1' m2' ∧
      Pattern.RHS.apply m1 m2 quotRHS ≠ Pattern.RHS.apply m1' m2' quotRHS := by
  obtain ⟨m1, m2, hm, hrhs, -⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  obtain ⟨m1', m2', hm', hrhs', -⟩ := quot_matches .zero (.succ .zero) (.bvar 0)
  refine ⟨m1, m2, m1', m2', hm, hm', ?_⟩
  rw [hrhs, hrhs']
  nofun

/-! ## 4. The M3 witness: `u = 1`, so the matched argument is not a proof -/

/-- The witness context at `α : Type 0`, `β : Type 0`. -/
abbrev qc1 : List VExpr := qCtx (.succ .zero) (.succ .zero)

theorem qc1_wf : OnCtx qc1 (qEnv.IsType 0) := by
  have := qEnv_Quot; have := qEnv_Eq
  refine ⟨⟨⟨⟨⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> exact ⟨_, by type_tac⟩

/-- **The five-argument `Quot.lift` spine is well typed**, at a `Π`-type whose domain is
`Quot.{1} α r`.  This is the premise `hf` of M3, and the reason the witness needs `Eq` in the
environment: `Quot.lift`'s fifth argument is a `sound` premise stated with `Eq`. -/
theorem qLift1_hasType :
    qEnv.HasType 0 qc1 (qLift (.succ .zero) (.succ .zero))
      (.forallE (qA (.succ .zero)) (.bvar 5)) := by
  have := qEnv_Quot; have := qEnv_Eq; have := qEnv_QuotLift
  type_tac

theorem qMk1_2_hasType :
    qEnv.HasType 0 qc1 (.app (.app (.const ``Quot.mk [.succ .zero]) (.bvar 6)) (.bvar 5))
      (.forallE (.bvar 6) (.app (.app (.const ``Quot [.succ .zero]) (.bvar 7)) (.bvar 6))) := by
  have := qEnv_Quot; have := qEnv_QuotMk; type_tac

theorem qMk1_hasType {t} (ht : qEnv.HasType 0 qc1 t (.bvar 6)) :
    qEnv.HasType 0 qc1 (qMk (.succ .zero) t) (qA (.succ .zero)) := .app' qMk1_2_hasType ht rfl

/-- `x ≡ (fun y : α => y) x : α`, by β. -/
theorem qXbeta_defeq : qEnv.IsDefEq 0 qc1 (.bvar 1) qXbeta (.bvar 6) :=
  (IsDefEq.beta (.bvar .zero) qT_x).symm

theorem qXbeta_hasType : qEnv.HasType 0 qc1 qXbeta (.bvar 6) := qXbeta_defeq.hasType.2

/-- The two major premises are definitionally equal: `Quot.mk α r x ≡ Quot.mk α r ((fun y => y) x)`. -/
theorem qMk1_defeq :
    qEnv.IsDefEq 0 qc1 (qMk (.succ .zero) (.bvar 1)) (qMk (.succ .zero) qXbeta)
      (qA (.succ .zero)) := .appDF qMk1_2_hasType qXbeta_defeq

section
attribute [local instance] quotParams

/-- **M3, instantiated at the quotient rule table, forces `NormalEq` across a β-redex.**
Both premises `hf` are the *same* well-typed `Quot.lift` spine; the two major premises are the
`Quot.mk` spines at `x` and at `(fun y => y) x`, which are definitionally equal by β and both
typed by `Quot.{1} α r`.  The conclusion is `NormalEq` of the two right-hand sides `g x` and
`g ((fun y => y) x)`. -/
theorem quotParams_m3_forces_beta (H : PatMajorCanonical) :
    NormalEq qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) qXbeta) := by
  obtain ⟨m1, m2, hm, hrhs, -⟩ := quot_matches (.succ .zero) (.succ .zero) (.bvar 1)
  obtain ⟨m1', m2', hm', hrhs', -⟩ := quot_matches (.succ .zero) (.succ .zero) qXbeta
  have := H (r := (quotRHS, quotCheck)) (r' := (quotRHS, quotCheck))
    quotParams_pat_app quotParams_pat_app hm hm' qLift1_hasType qLift1_hasType
    (qMk1_hasType qT_x) qMk1_defeq
  have h2 : NormalEq qc1 (Pattern.RHS.apply m1 m2 quotRHS)
    (Pattern.RHS.apply m1' m2' quotRHS) := this
  rwa [hrhs, hrhs'] at h2

/-! ### …and that `NormalEq` is refutable

`NormalEq` has no β step, so the only constructors that could relate `g x` to
`g ((fun y => y) x)` are `appDF` (descending to the argument, where the same problem recurs at
`x` versus a β-redex) and `proofIrrel`.  The latter is blocked by `qEnv_not_proof`: `α` and `β`
both live in `Sort 1`. -/

theorem not_normalEq_qXbeta : ¬ NormalEq qc1 (.bvar 1) qXbeta := by
  intro h
  cases h with
  | proofIrrel hp h1 _ =>
    exact qEnv_not_proof qc1_wf (u := .succ .zero) trivial (by decide) qT_x qT_alpha h1 hp

theorem not_normalEq_gx : ¬ NormalEq qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) qXbeta) := by
  intro h
  cases h with
  | appDF _ _ _ _ _ ha => exact not_normalEq_qXbeta ha
  | proofIrrel hp h1 _ =>
    exact qEnv_not_proof qc1_wf (u := .succ .zero) trivial (by decide)
      (qT_gx qT_x) qT_beta h1 hp

/-- **M3 is FALSE at the canonical `.app` rule table.**  Not "unproved": refuted, at the first
rule table whose right-hand sides depend on the matched arguments.  Modulo `PiInv` (the
instance) and `WF.propTypeAgreeOn` (the two `proofIrrel` blocks) -- both `sorryAx`, both the
same corner, neither new. -/
theorem quotParams_not_patMajorCanonical : ¬ PatMajorCanonical :=
  fun H => not_normalEq_gx (quotParams_m3_forces_beta H)

/-! ### The same witness refutes `KDiamond` itself

`KStep`'s `hdq` is an arbitrary `IsDefEq`, so one redex has two K-steps: the rule fires at the
matched argument `x` and at the β-redex `(fun y => y) x`, both definitionally equal major
premises.  `KDiamond` asks the two reducts to be `NormalEq`; they differ by a β-step *inside* a
matched argument, and `NormalEq` has no β. -/

theorem quotParams_kstep_x :
    KStep qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
      (.app (.bvar 3) (.bvar 1)) := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches (.succ .zero) (.succ .zero) (.bvar 1)
  have h2 : KStep qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
      (Pattern.RHS.apply m1 m2 quotRHS) :=
    KStep.mk (Γ := qc1) (r := (quotRHS, quotCheck)) quotParams_pat_app hm hck
      qLift1_hasType (qMk1_hasType qT_x)
  rwa [hrhs] at h2

theorem quotParams_kstep_xbeta :
    KStep qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
      (.app (.bvar 3) qXbeta) := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches (.succ .zero) (.succ .zero) qXbeta
  have h2 : KStep qc1 (.app (qLift (.succ .zero) (.succ .zero)) (qMk (.succ .zero) (.bvar 1)))
      (Pattern.RHS.apply m1 m2 quotRHS) :=
    KStep.mk (Γ := qc1) (r := (quotRHS, quotCheck)) quotParams_pat_app hm hck
      qLift1_hasType qMk1_defeq
  rwa [hrhs] at h2

/-- **`KDiamond` is FALSE at the canonical `.app` rule table.**  One redex, two `K⁺` steps,
two reducts that are definitionally equal but not `NormalEq`. -/
theorem quotParams_not_kDiamond : ¬ KDiamond :=
  fun H => not_normalEq_gx (H qc1_wf quotParams_kstep_x quotParams_kstep_xbeta)

/-- **…and the rule table is not at fault: the two reducts are JOINABLE.**  One β-step on the
right and the two are literally equal.  So what fails at the quotient rule table is
`KDiamond`'s *demand that the reducts be `NormalEq` on the nose*, not confluence: the shape
`KEta.lean`'s `EtaKDiamond` already uses -- reduce both sides, then `NormalEq` -- survives this
witness.  That is where the repair goes. -/
theorem quotParams_kDiamond_joinable :
    ∃ e₃ e₄, ParRedKS qc1 (.app (.bvar 3) (.bvar 1)) e₃ ∧
      ParRedKS qc1 (.app (.bvar 3) qXbeta) e₄ ∧ NormalEq qc1 e₃ e₄ :=
  ⟨_, _, .rfl, .tail .rfl (.app .bvar (.beta .bvar .bvar)), .refl (qT_gx qT_x)⟩

end

/-! ## 5. `ParRed`-rigidity of the witness terms -/

section
attribute [local instance] quotParams

theorem qParRed_const {Γ : List VExpr} {c ls o} (h : ParRed Γ (.const c ls) o) :
    o = .const c ls := by
  cases h with
  | const => rfl
  | extra hp hm _ _ =>
    obtain rfl := pat_qEnv_eq hp
    obtain ⟨_, _, _, _, _, he⟩ := quotPat_matches_mk hm; nomatch he

theorem qParRed_bvar {Γ : List VExpr} {i o} (h : ParRed Γ (.bvar i) o) : o = .bvar i := by
  cases h with
  | bvar => rfl
  | extra hp hm _ _ =>
    obtain rfl := pat_qEnv_eq hp
    obtain ⟨_, _, _, _, _, he⟩ := quotPat_matches_mk hm; nomatch he

/-- An application whose argument is a `bvar` and whose function is rigid and not a λ is rigid:
β cannot fire, and no rule can, because `quotPat`'s major-premise side is a `Quot.mk` spine. -/
theorem qParRed_app_bvar {Γ : List VExpr} {f : VExpr} {i : Nat} {o}
    (hf : ∀ o', ParRed Γ f o' → o' = f) (hlam : ∀ A b, f ≠ .lam A b)
    (h : ParRed Γ (.app f (.bvar i)) o) : o = .app f (.bvar i) := by
  cases h with
  | app h1 h2 => rw [hf _ h1, qParRed_bvar h2]
  | beta => exact absurd rfl (hlam _ _)
  | extra hp hm _ _ =>
    obtain rfl := pat_qEnv_eq hp
    obtain ⟨_, _, _, _, _, he⟩ := quotPat_matches_mk hm
    injection he with _ h2; nomatch h2

/-- The five-argument `Quot.lift` spine is `ParRed`-normal at every context. -/
theorem qParRed_qLift {Γ : List VExpr} {u v : VLevel} {o} (h : ParRed Γ (qLift u v) o) :
    o = qLift u v :=
  qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_app_bvar
    (fun _ => qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_const) nofun)
      nofun) nofun) nofun) nofun h

/-- `Quot.{u} α r` is `ParRed`-normal. -/
theorem qParRed_qA {Γ : List VExpr} {u : VLevel} {o} (h : ParRed Γ (qA u) o) : o = qA u :=
  qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_const) nofun) nofun h

end

/-! ## 6. The `Prop`-major-premise witness: `Quot.{0} α r` *is* a `Prop`

`quotConst`'s type is `(α : Sort u) → (α → α → Prop) → Sort u`, so at `u = 0` the type of every
`Quot.mk` spine is a **proposition** while the rule's right-hand side `g x : β` lives in
`Sort 1`.  That is exactly the "`Prop` major premise, `Type`-valued right-hand side" shape that
`PatAppParams.lean` and ledger row 96c say requires an `addInduct'` witness (`Eq.rec`).  It does
not: the quotient rule supplies it. -/

abbrev qc0 : List VExpr := qCtx .zero (.succ .zero)

theorem qc0_wf : OnCtx qc0 (qEnv.IsType 0) := by
  have := qEnv_Quot; have := qEnv_Eq
  refine ⟨⟨⟨⟨⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> exact ⟨_, by type_tac⟩

theorem qLift0_hasType :
    qEnv.HasType 0 qc0 (qLift .zero (.succ .zero)) (.forallE (qA .zero) (.bvar 5)) := by
  have := qEnv_Quot; have := qEnv_Eq; have := qEnv_QuotLift
  type_tac

/-- **The major premise's type is a `Prop`.** -/
theorem qA0_isProp : qEnv.HasType 0 qc0 (qA .zero) (.sort .zero) := by
  have := qEnv_Quot; type_tac

theorem qMk0_2_hasType :
    qEnv.HasType 0 qc0 (.app (.app (.const ``Quot.mk [VLevel.zero]) (.bvar 6)) (.bvar 5))
      (.forallE (.bvar 6) (.app (.app (.const ``Quot [VLevel.zero]) (.bvar 7)) (.bvar 6))) := by
  have := qEnv_Quot; have := qEnv_QuotMk; type_tac

theorem qMk0_hasType {t} (ht : qEnv.HasType 0 qc0 t (.bvar 6)) :
    qEnv.HasType 0 qc0 (qMk .zero t) (qA .zero) := .app' qMk0_2_hasType ht rfl

/-- …and the redex's *result* type is not: `.forallE (Quot.{0} α r) β` lives in
`Sort (imax 0 1)`, which evaluates to `1`. -/
theorem qLiftType0_hasType :
    qEnv.HasType 0 qc0 (.forallE (qA .zero) (.bvar 5))
      (.sort (.imax .zero (.succ .zero))) :=
  .forallE qA0_isProp (.bvar (by lookup_tac))

theorem qLift0_not_proof {p} (h1 : qEnv.HasType 0 qc0 (qLift .zero (.succ .zero)) p)
    (h2 : qEnv.HasType 0 qc0 p (.sort .zero)) : False :=
  qEnv_not_proof qc0_wf (u := .imax .zero (.succ .zero)) (by decide) (by decide)
    qLift0_hasType qLiftType0_hasType h1 h2

section
attribute [local instance] quotParams

theorem not_normalEq_lift_g :
    ¬ NormalEq qc0 (qLift .zero (.succ .zero)) (.bvar 3) := by
  intro h
  cases h with
  | proofIrrel hp h1 _ => exact qLift0_not_proof h1 hp

theorem not_normalEq_redex_rhs :
    ¬ NormalEq qc0 (.app (qLift .zero (.succ .zero)) (.bvar 0)) (.app (.bvar 3) (.bvar 1)) := by
  intro h
  cases h with
  | appDF _ _ _ _ hf _ => exact not_normalEq_lift_g hf
  | proofIrrel hp h1 _ =>
    exact qEnv_not_proof qc0_wf (u := .succ .zero) trivial (by decide)
      (.app' qLift0_hasType qT_prf rfl) qT_beta h1 hp

/-- **`NormalEq.parRed`'s statement is refuted at the canonical instance.**
`not_parRedStatement_of_propMajor` fires here: the major-premise slot is typed by the `Prop`
`Quot.{0} α r`, `.bvar 0` is another inhabitant of it, the redex-with-that-inhabitant is
`ParRed`-normal, and it is not `NormalEq` to the rule's right-hand side. -/
theorem quotParams_not_parRedStatement : ¬ ParRedStatement := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  refine not_parRedStatement_of_propMajor (a := .bvar 0) (A := qA .zero)
    qc0_wf quotParams_pat_app hm hck qLift0_hasType qA0_isProp qT_prf (qMk0_hasType qT_x)
    (fun o ho => qParRed_app_bvar (fun _ => qParRed_qLift) nofun ho) ?_
  intro hne
  have h3 : NormalEq qc0 (.app (qLift .zero (.succ .zero)) (.bvar 0))
      (Pattern.RHS.apply m1 m2 quotRHS) := hne
  rw [hrhs] at h3
  exact not_normalEq_redex_rhs h3

/-- **…and `hK` is false there**, by the same witness: `K⁺` fires at
`.app f (.bvar 0)` by proof irrelevance while `ParRed` does not move it. -/
theorem quotParams_not_hK :
    ¬ (∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → ParRed Δ e e') := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  refine not_hK_of_propMajor (a := .bvar 0) (A := qA .zero)
    quotParams_pat_app hm hck qLift0_hasType qA0_isProp qT_prf (qMk0_hasType qT_x)
    (fun o ho => qParRed_app_bvar (fun _ => qParRed_qLift) nofun ho) ?_
  intro he
  have h3 : Pattern.RHS.apply m1 m2 quotRHS
      = .app (qLift .zero (.succ .zero)) (.bvar 0) := he
  rw [hrhs] at h3
  injection h3 with h4 _
  exact absurd h4 (by nofun)

end

/-! ## 7. …and `IsDefEq.church_rosser`'s statement goes too

`not_crStatement_of_kstep` (`KCanonical.lean`) needs the K-redex to sit *under an `eta`*: the
function must be typed in the shorter context `Γ` and the major premise must be `.bvar 0`, a
variable of the `Prop` `A`.  The witness context is built so that this is free: its head entry
is exactly `Quot.{0} α r`, so `qc0 = A :: Γ` on the nose, and `qLift`'s bvars are all `≥ 1`, so
it is literally a `.lift`. -/

/-- The context one entry shorter: `qc0` without its `Quot.{0} α r` variable. -/
abbrev qc0T : List VExpr := (qCtx .zero (.succ .zero)).tail

/-- `Quot.{u} α r` in the shorter context — the head entry of `qCtx u v`. -/
def qAT (u : VLevel) : VExpr := .app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)

/-- The five-argument `Quot.lift` spine in the shorter context. -/
def qLiftT (u v : VLevel) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.lift [u, v]) (.bvar 5)) (.bvar 4)) (.bvar 3))
    (.bvar 2)) (.bvar 1)

theorem qLiftT_lift : (qLiftT u v).lift = qLift u v := rfl
theorem qAT_cons : qAT .zero :: qc0T = qc0 := rfl

theorem qc0T_wf : OnCtx qc0T (qEnv.IsType 0) := qc0_wf.1

theorem qAT0_isProp : qEnv.HasType 0 qc0T (qAT .zero) (.sort .zero) := by
  have := qEnv_Quot; type_tac

theorem qLiftT0_hasType :
    qEnv.HasType 0 qc0T (qLiftT .zero (.succ .zero)) (.forallE (qAT .zero) (.bvar 4)) := by
  have := qEnv_Quot; have := qEnv_Eq; have := qEnv_QuotLift
  type_tac

theorem qLiftTType0_hasType :
    qEnv.HasType 0 qc0T (.forallE (qAT .zero) (.bvar 4))
      (.sort (.imax .zero (.succ .zero))) :=
  .forallE qAT0_isProp (.bvar (by lookup_tac))

section
attribute [local instance] quotParams

theorem qLiftT0_not_proof (P : VExpr) (h2 : qEnv.HasType 0 qc0T P (.sort .zero)) :
    ¬ qEnv.HasType 0 qc0T (qLiftT .zero (.succ .zero)) P := fun h1 =>
  qEnv_not_proof qc0T_wf (u := .imax .zero (.succ .zero)) (by decide) (by decide)
    qLiftT0_hasType qLiftTType0_hasType h1 h2

theorem qParRed_qLiftT {Γ : List VExpr} {u v : VLevel} {o} (h : ParRed Γ (qLiftT u v) o) :
    o = qLiftT u v :=
  qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_app_bvar
    (fun _ => qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_const) nofun)
      nofun) nofun) nofun) nofun h

theorem qParRed_qAT {Γ : List VExpr} {u : VLevel} {o} (h : ParRed Γ (qAT u) o) : o = qAT u :=
  qParRed_app_bvar (fun _ => qParRed_app_bvar (fun _ => qParRed_const) nofun) nofun h

/-- **The `K⁺` step under the `eta`**, fired by *proof irrelevance*: the major premise is the
variable `.bvar 0` of the `Prop` `Quot.{0} α r`, and it is definitionally equal to the `Quot.mk`
spine that matches. -/
theorem quotParams_kstep_eta :
    KStep qc0 (.app (qLiftT .zero (.succ .zero)).lift (.bvar 0)) (.app (.bvar 3) (.bvar 1)) := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  have h2 : KStep qc0 (.app (qLift .zero (.succ .zero)) (.bvar 0))
      (Pattern.RHS.apply m1 m2 quotRHS) :=
    KStep.mk (Γ := qc0) (r := (quotRHS, quotCheck)) quotParams_pat_app hm hck qLift0_hasType
      (.proofIrrel qA0_isProp qT_prf (qMk0_hasType qT_x))
  rw [hrhs] at h2
  exact h2

/-- **`IsDefEq.church_rosser`'s statement is refuted at the canonical instance.**  No `hK`: only
`KStep.defeq`, i.e. only that the rule is admissible. -/
theorem quotParams_not_crStatement : ¬ CRStatement :=
  not_crStatement_of_kstep (u := .zero) (t := .app (.bvar 3) (.bvar 1))
    qc0T_wf qc0_wf qAT0_isProp qLiftT0_hasType quotParams_kstep_eta nofun
    qLiftT0_not_proof (fun _ => qParRed_qLiftT) (fun _ => qParRed_qAT)
    (fun _ ho => qParRed_app_bvar (fun _ => qParRed_bvar) nofun ho)
    not_normalEq_redex_rhs

end

/-! ## 8. Instrument 7: M3's hypotheses are jointly satisfiable here

The refutations above conclude `False`/`¬ …`, so what makes them non-empty is that every
hypothesis they feed is *satisfied*.  This is that check for M3, spelled out at the two matches
the refutation uses.  It is `sorryAx`-free: `Params.Pat quotParams` is `Pat qEnv` by `rfl`, so
stating it needs no instance. -/

theorem quotParams_m3_hyps_sat :
    ∃ m1 m2 m1' m2',
      Pat qEnv quotPat (quotRHS, quotCheck) ∧
      quotPat.Matches (.app (qLift (.succ .zero) (.succ .zero))
        (qMk (.succ .zero) (.bvar 1))) m1 m2 ∧
      quotPat.Matches (.app (qLift (.succ .zero) (.succ .zero))
        (qMk (.succ .zero) qXbeta)) m1' m2' ∧
      qEnv.HasType 0 qc1 (qLift (.succ .zero) (.succ .zero))
        (.forallE (qA (.succ .zero)) (.bvar 5)) ∧
      qEnv.IsDefEq 0 qc1 (qMk (.succ .zero) (.bvar 1)) (qMk (.succ .zero) (.bvar 1))
        (qA (.succ .zero)) ∧
      qEnv.IsDefEq 0 qc1 (qMk (.succ .zero) (.bvar 1)) (qMk (.succ .zero) qXbeta)
        (qA (.succ .zero)) ∧
      Pattern.RHS.apply m1 m2 quotRHS ≠ Pattern.RHS.apply m1' m2' quotRHS := by
  obtain ⟨m1, m2, hm, hrhs, -⟩ := quot_matches (.succ .zero) (.succ .zero) (.bvar 1)
  obtain ⟨m1', m2', hm', hrhs', -⟩ := quot_matches (.succ .zero) (.succ .zero) qXbeta
  refine ⟨m1, m2, m1', m2', quotVEnv_pat_app, hm, hm', qLift1_hasType,
    qMk1_hasType qT_x, qMk1_defeq, ?_⟩
  rw [hrhs, hrhs']
  nofun

end VEnv
end Lean4Lean
