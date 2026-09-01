import Lean4Lean.Theory.Typing.ParRedMissing

/-!
# The cycle is essential, grading is powerless, and the confluence layer reduces to M3

`ParRedMissing.lean` showed that repairing `NormalEq.descend`'s three witnesses requires two new
reduction steps, and that the extension `ParRedP` is **cyclic** (`refParRedP_cycle`).  That cycle
is the blocker for `ParRed.triangle` (`ChurchRosser.lean:1073`) and hence for
`ParRedS.church_rosser` (`:2435`) and `IsDefEq.church_rosser` (`:2480`).  This file settles the
three questions that were open about it.

## The witness `refEnv` could not carry, and why a new environment was needed

`refEnv` has exactly **one** constant proof of `P` (`D`), so its cycle
(`refParRedP_cycle`) runs between `.bvar 0` and `.const D []` -- one of which is a context
variable.  That leaves open the reading "orient toward closed terms".  `cycEnv` adds a **second**
constant proof `D2 : P`, so the cycle here runs between two *closed* terms `C D` and `C D2` with
no context at all (`cycCtx = []`).  There is nothing left to orient by.

## §1-§2 The cycle is essential, not an artefact of how the constructors are stated

The question was whether a proof-replacement step *oriented* by a well-founded criterion could
work.  It cannot, and the reason is upstream of any constructor:

> `descend` is called at `C D` against the pattern naming `D2`, **and** at `C D2` against the
> pattern naming `D`.  Both are legitimate `Params.pat_simple` shapes and `descend` quantifies
> over both.  So the obligation itself demands both directions.

`cyc_of_answers` proves this for an **arbitrary** relation `R`, from a requirement (`AnswersAt`)
that is strictly *weaker* than `descend`'s answer -- `answersAt_of_descentLam` checks that it is
literally the first three conjuncts of `DescentLam 0`, so this is a weakening and not a strawman.
The level clause is kept, and it is what pins the reduct to `C D2` exactly rather than up to junk
level lists (`Forall₂` forces equal length).

Hence:

* `no_decreasing_measure` -- no `Nat`-valued measure decreasing along `R`;
* `no_wf_orientation` -- no well-founded strict order orienting `R` at all;
* `parRedP_no_decreasing_measure` -- and this applies to the real extension, unconditionally.

**So the answer to "try orienting it" is a theorem, not a remark: proof irrelevance has no
preferred direction, and any relation strong enough for `descend` inherits that.**

## §4 Grading is powerless, for a different reason than last time

`no_grading_removes_cycle`: a grading is a monotone family whose union is the relation; a
two-cycle is **two steps**; a grading bounds structure *within* a step, never the length of a
chain.  So the cycle already lives at a finite grade.  This closes the `ParRedKn` route for
**every** grading, not just that one (`parRedP_cycle_survives_grading`).

Contrast ledger row 71a, where grading failed to rescue `descend` because the term does not
*move*.  Here the terms move -- they move in a circle.  Same verdict, different mechanism, which
is why the route had to be checked separately rather than inherited.

## §5 Verdict: the confluence layer sits behind rule-table canonicity (M3)

Putting the two negatives together: the route that adds steps to `ParRed` is **dead**, because
any such relation is unorientable (§2) and no grading repairs that (§4).  What survives is the
route in which **no proof ever has to move** -- `descendV` plus
`NormalEq.appDF_extra_of_descendVK`, where the K-step fires the rule *up to definitional equality
of the major premise*.  Its residual is `KDescend.lean`'s `KDiamond`.

`PatMajorCanonical` states that residual as a property of the **rule table alone** -- no `ParRed`,
no `ParRedK`, no grading, no reduction relation of any kind; only `Params.Pat`,
`Pattern.Matches`, `HasType`/`IsDefEq` and `NormalEq`.  It is `docs/design-inductive.md` §7.6's
lemma M3.  And `kDiamond_of_patMajorCanonical` **discharges `KDiamond` from it**, machine-checked
and **`sorryAx`-free** -- see its docstring for why the two major-premise conversions are passed
un-composed (composing them needs unique typing, which would pull the injectivity holes into the
request).

So the honest answer to step 3 is the one the brief allowed for: **this needs rule-table
canonicity (M3)**, and that now locates the whole confluence layer behind one named prerequisite
about the rule table rather than behind a partial measure.

**What is not claimed.**  That `KDiamond` *suffices* for `ParRedK` confluence is not proved here
-- `EtaKDiamond` reduces by `KMeasure.etaKDiamond_of_at` to an equal-height diamond plus a
λ-congruence induction whose base is `KDiamond`-shaped, and that induction is open.  What is
proved is the direction that matters for locating work: `PatMajorCanonical → KDiamond`.  Nor is
`PatMajorCanonical` shown satisfiable; at `cycParams` it is vacuous (`cycNoPat`), so its
non-vacuity needs an instance registering an `.app` pattern -- the same instance that
`ParRedPropRefute.lean` and `KCanonical.lean` need and that `PatWFIota.lean` would supply.
-/

namespace Lean4Lean
open VExpr

/-- `P : Prop`. -/
def cycP : VConstant := ⟨0, .sort .zero⟩
/-- `D : P`. -/
def cycD : VConstant := ⟨0, .const `P []⟩
/-- `D2 : P`, a *second* constant proof of the same proposition.  `refEnv` has only one, which
is why the cycle cannot be exhibited there between two closed terms. -/
def cycD2 : VConstant := ⟨0, .const `P []⟩
/-- `T : Type`. -/
def cycT : VConstant := ⟨0, .sort (.succ .zero)⟩
/-- `C : P → T`. -/
def cycC : VConstant := ⟨0, .forallE (.const `P []) (.const `T [])⟩

def cycEnv1 : VEnv :=
  { VEnv.empty with constants := fun n => if `P = n then some cycP else VEnv.empty.constants n }
def cycEnv2 : VEnv :=
  { cycEnv1 with constants := fun n => if `D = n then some cycD else cycEnv1.constants n }
def cycEnv3 : VEnv :=
  { cycEnv2 with constants := fun n => if `D2 = n then some cycD2 else cycEnv2.constants n }
def cycEnv4 : VEnv :=
  { cycEnv3 with constants := fun n => if `T = n then some cycT else cycEnv3.constants n }
def cycEnv : VEnv :=
  { cycEnv4 with constants := fun n => if `C = n then some cycC else cycEnv4.constants n }

theorem cycEnv_P : cycEnv.constants `P = some cycP := rfl
theorem cycEnv_D : cycEnv.constants `D = some cycD := rfl
theorem cycEnv_D2 : cycEnv.constants `D2 = some cycD2 := rfl
theorem cycEnv_T : cycEnv.constants `T = some cycT := rfl
theorem cycEnv_C : cycEnv.constants `C = some cycC := rfl

theorem cycEnv_no_defeqs {df} : ¬ cycEnv.defeqs df := nofun

theorem cycEnv1_eq : VEnv.empty.addConst `P cycP = some cycEnv1 := rfl
theorem cycEnv2_eq : cycEnv1.addConst `D cycD = some cycEnv2 := rfl
theorem cycEnv3_eq : cycEnv2.addConst `D2 cycD2 = some cycEnv3 := rfl
theorem cycEnv4_eq : cycEnv3.addConst `T cycT = some cycEnv4 := rfl
theorem cycEnv5_eq : cycEnv4.addConst `C cycC = some cycEnv := rfl

theorem cycEnv_wf : cycEnv.WF := by
  refine ⟨_, .decl (d := .axiom ⟨cycC, `C⟩) (.axiom ?_ cycEnv5_eq)
    (.decl (d := .axiom ⟨cycT, `T⟩) (.axiom ⟨_, .sort trivial⟩ cycEnv4_eq)
      (.decl (d := .axiom ⟨cycD2, `D2⟩) (.axiom ?_ cycEnv3_eq)
        (.decl (d := .axiom ⟨cycD, `D⟩) (.axiom ?_ cycEnv2_eq)
          (.decl (d := .axiom ⟨cycP, `P⟩) (.axiom ⟨_, .sort trivial⟩ cycEnv1_eq) .empty))))⟩
  · exact ⟨_, .forallEDF (u := .zero) (v := .succ .zero)
      (VEnv.IsDefEq.constDF (ci := cycP) rfl nofun nofun rfl .nil)
      (VEnv.IsDefEq.constDF (ci := cycT) rfl nofun nofun rfl .nil)⟩
  · exact ⟨_, VEnv.IsDefEq.constDF (ci := cycP) rfl nofun nofun rfl .nil⟩
  · exact ⟨_, VEnv.IsDefEq.constDF (ci := cycP) rfl nofun nofun rfl .nil⟩

theorem cycEnv_deltaFragment : VEnv.DeltaFragment cycEnv := by
  intro p r h; cases h <;> exact absurd ‹_› cycEnv_no_defeqs

@[instance_reducible] def cycParams : VEnv.Params :=
  VEnv.paramsOfDelta cycEnv_wf 0 cycEnv_deltaFragment

theorem cycParams_env : (@VEnv.Params.env cycParams) = cycEnv := rfl

theorem cycNoPat {p r} : ¬ @VEnv.Params.Pat cycParams p r := by
  intro h; cases h <;> exact absurd ‹_› cycEnv_no_defeqs


/-! ## Typing facts -/

theorem cycEnv_hasP {Γ} : cycEnv.HasType 0 Γ (.const `P []) (.sort .zero) :=
  VEnv.IsDefEq.constDF (ci := cycP) cycEnv_P nofun nofun rfl .nil
theorem cycEnv_hasT {Γ} : cycEnv.HasType 0 Γ (.const `T []) (.sort (.succ .zero)) :=
  VEnv.IsDefEq.constDF (ci := cycT) cycEnv_T nofun nofun rfl .nil
theorem cycEnv_hasD {Γ} : cycEnv.HasType 0 Γ (.const `D []) (.const `P []) :=
  VEnv.IsDefEq.constDF (ci := cycD) cycEnv_D nofun nofun rfl .nil
theorem cycEnv_hasD2 {Γ} : cycEnv.HasType 0 Γ (.const `D2 []) (.const `P []) :=
  VEnv.IsDefEq.constDF (ci := cycD2) cycEnv_D2 nofun nofun rfl .nil
theorem cycEnv_hasC {Γ} :
    cycEnv.HasType 0 Γ (.const `C []) (.forallE (.const `P []) (.const `T [])) :=
  VEnv.IsDefEq.constDF (ci := cycC) cycEnv_C nofun nofun rfl .nil

/-- The empty context suffices -- both proofs are closed, so the cycle below involves no
context variable at all.  (`refEnv`'s witness A used `.bvar 0`; here the cycle is between two
*closed* terms, which is what makes it a cycle rather than a one-way step.) -/
abbrev cycCtx : List VExpr := []

theorem cycEnv_hCtx : OnCtx cycCtx (cycEnv.IsType 0) := trivial

abbrev cycG : VExpr := .app (.const `C []) (.const `D [])
abbrev cycG2 : VExpr := .app (.const `C []) (.const `D2 [])
/-- The pattern naming `D` in its argument position. -/
abbrev cycQ : Pattern := .app (.const `C) (.const `D)
/-- The pattern naming `D2`.  Both are legitimate registered-rule shapes
(`Params.pat_simple` allows `.app` of two `.var`-chains over `.const` leaves), and `descend`
quantifies over both. -/
abbrev cycQ2 : Pattern := .app (.const `C) (.const `D2)

theorem cycEnv_hasG : cycEnv.HasType 0 cycCtx cycG (.const `T []) :=
  VEnv.IsDefEq.appDF cycEnv_hasC cycEnv_hasD
theorem cycEnv_hasG2 : cycEnv.HasType 0 cycCtx cycG2 (.const `T []) :=
  VEnv.IsDefEq.appDF cycEnv_hasC cycEnv_hasD2

/-- The two terms are `NormalEq`, by proof irrelevance on the argument -- so `descend` is
called at each of them, against the pattern the *other* one matches. -/
theorem cycNormalEq : @VEnv.NormalEq cycParams cycCtx cycG cycG2 := by
  letI := cycParams
  exact .appDF cycEnv_hasC cycEnv_hasC cycEnv_hasD cycEnv_hasD2 (.refl cycEnv_hasC)
    (.proofIrrel cycEnv_hasP cycEnv_hasD cycEnv_hasD2)

theorem cycNormalEq' : @VEnv.NormalEq cycParams cycCtx cycG2 cycG := by
  letI := cycParams
  exact .appDF cycEnv_hasC cycEnv_hasC cycEnv_hasD2 cycEnv_hasD (.refl cycEnv_hasC)
    (.proofIrrel cycEnv_hasP cycEnv_hasD2 cycEnv_hasD)

theorem cycMatches : ∃ m1 m2, cycQ.Matches cycG m1 m2 := ⟨_, _, .app .const .const⟩
theorem cycMatches2 : ∃ m1 m2, cycQ2.Matches cycG2 m1 m2 := ⟨_, _, .app .const .const⟩


/-! ## §1 The requirement, abstracted over the reduction relation -/

/-- **`descend`'s answer disjunct at eta-depth `0`, abstracted over the relation.**  Keeps
`descend`'s own level clause -- which is what pins the cycle *exactly* rather than up to junk
level lists -- and drops everything else (`NormalEq` on the matched arguments, both WF side
conditions, the eta tower).  So it is strictly **weaker** than `DescentLam 0`, and a relation
that fails it fails `descend`. -/
def AnswersAt (R : List VExpr → VExpr → VExpr → Prop) (Γ : List VExpr) (q : Pattern)
    (g : VExpr) (n1 : q.LPath → List VLevel) : Prop :=
  ∃ t m1 m2, ReflTransGen (R Γ) g t ∧ q.Matches t m1 m2 ∧
    ∀ lp, List.Forall₂ (· ≈ ·) (m1 lp) (n1 lp)

/-- **Anti-strawman check: `AnswersAt` is implied by `DescentLam 0`, verbatim.**  `descend`'s
answer at eta-depth `0` is `∃ t n1' n, ParRedS Γ g t ∧ q.Matches t n1' n ∧ (level clause) ∧
(WF clause) ∧ (WF clause) ∧ (NormalEq clause)`; `AnswersAt` is the first three conjuncts.  So it
is a weakening of the obligation and not a different statement, and refuting it refutes
`descend`.  (`sorryAx`-free -- it is a projection.) -/
theorem answersAt_of_descentLam {Γ : List VExpr} {q : Pattern} {g g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr}
    (H : @VEnv.DescentLam cycParams 0 Γ q g g' n1 n2) :
    AnswersAt (@VEnv.ParRed cycParams) Γ q g n1 :=
  let ⟨t, n1', n, hred, hmt, hlv, _⟩ := H; ⟨t, n1', n, hred, hmt, hlv⟩

/-- **The level clause pins the reduct.**  A term matching `cycQ2` whose read-off level lists
are `≈ []` is `cycG2` on the nose: `Forall₂` forces equal length, so both lists are empty. -/
theorem cycQ2_answer {R} (H : AnswersAt R cycCtx cycQ2 cycG (fun _ => [])) :
    ReflTransGen (R cycCtx) cycG cycG2 := by
  obtain ⟨t, m1, m2, hred, hm, hlv⟩ := H
  cases hm with
  | app hf ha =>
    cases hf; cases ha
    cases hlv (.inl ()); cases hlv (.inr ())
    exact hred

theorem cycQ_answer {R} (H : AnswersAt R cycCtx cycQ cycG2 (fun _ => [])) :
    ReflTransGen (R cycCtx) cycG2 cycG := by
  obtain ⟨t, m1, m2, hred, hm, hlv⟩ := H
  cases hm with
  | app hf ha =>
    cases hf; cases ha
    cases hlv (.inl ()); cases hlv (.inr ())
    exact hred

theorem cycG_ne_cycG2 : cycG ≠ cycG2 := by simp

/-- **The cycle is forced, not an artefact of how the constructor is stated.**  `descend` is
called at `cycG` against the pattern `cycQ2` (which `cycG2` matches) *and* at `cycG2` against
`cycQ` (which `cycG` matches) -- both are legitimate `Params.pat_simple` shapes, and `descend`
quantifies over both.  So any relation meeting the requirement carries `cycG` to `cycG2` and
back.  Orientation is impossible **before** any constructor is written down: the obligation is
symmetric because proof irrelevance is, and there are two constant proofs of one `Prop`. -/
theorem cyc_of_answers {R}
    (H1 : AnswersAt R cycCtx cycQ2 cycG (fun _ => []))
    (H2 : AnswersAt R cycCtx cycQ cycG2 (fun _ => [])) :
    ReflTransGen (R cycCtx) cycG cycG2 ∧ ReflTransGen (R cycCtx) cycG2 cycG :=
  ⟨cycQ2_answer H1, cycQ_answer H2⟩


/-! ## §2 …hence no well-founded orientation exists -/

theorem measure_le {R : List VExpr → VExpr → VExpr → Prop} {μ : VExpr → Nat}
    (hdec : ∀ Γ e e', R Γ e e' → μ e' < μ e) (Γ : List VExpr) {a b : VExpr}
    (H : ReflTransGen (R Γ) a b) : μ b ≤ μ a := by
  induction H with
  | rfl => exact Nat.le_refl _
  | tail _ h ih => exact Nat.le_trans (Nat.le_of_lt (hdec _ _ _ h)) ih

theorem measure_lt {R : List VExpr → VExpr → VExpr → Prop} {μ : VExpr → Nat}
    (hdec : ∀ Γ e e', R Γ e e' → μ e' < μ e) (Γ : List VExpr) {a b : VExpr}
    (H : ReflTransGen (R Γ) a b) (hne : a ≠ b) : μ b < μ a := by
  cases H with
  | rfl => exact absurd rfl hne
  | tail h1 h2 => exact Nat.lt_of_lt_of_le (hdec _ _ _ h2) (measure_le hdec Γ h1)

/-- **The essential-cycle theorem.**  No relation meeting `descend`'s requirement at the two
witnesses admits a measure that strictly decreases along it.  This answers "is the cycle an
artefact of how the two constructors are stated" with **no**: it is forced by the requirement,
so *every* formulation of proof replacement strong enough for `descend` is unorientable.
`sorryAx`-free. -/
theorem no_decreasing_measure {R : List VExpr → VExpr → VExpr → Prop} (μ : VExpr → Nat)
    (hdec : ∀ Γ e e', R Γ e e' → μ e' < μ e)
    (H1 : AnswersAt R cycCtx cycQ2 cycG (fun _ => []))
    (H2 : AnswersAt R cycCtx cycQ cycG2 (fun _ => [])) : False := by
  obtain ⟨h1, h2⟩ := cyc_of_answers H1 H2
  have l1 := measure_lt hdec cycCtx h1 cycG_ne_cycG2
  have l2 := measure_lt hdec cycCtx h2 (Ne.symm cycG_ne_cycG2)
  omega


/-- **No orientation by *any* well-founded strict order.**  The `Nat`-measure version above is
the common case; this is the general one, and it is what "try orienting it" reduces to.  A
well-founded relation is asymmetric, and the requirement forces `cycG` and `cycG2` each strictly
below the other.  (Transitivity is assumed because a *chain* of steps must compose into one
`lt`; that is exactly what an orientation by a strict order provides.) -/
theorem no_wf_orientation {R : List VExpr → VExpr → VExpr → Prop} {lt : VExpr → VExpr → Prop}
    (hwf : WellFounded lt)
    (htrans : ∀ x y z, lt x y → lt y z → lt x z)
    (hdec : ∀ Γ e e', R Γ e e' → lt e' e)
    (H1 : AnswersAt R cycCtx cycQ2 cycG (fun _ => []))
    (H2 : AnswersAt R cycCtx cycQ cycG2 (fun _ => [])) : False := by
  have asym : ∀ {a b : VExpr}, lt a b → lt b a → False := by
    intro a
    induction a using hwf.induction with
    | _ x ih => intro b h1 h2; exact ih b h2 h2 h1
  have chain : ∀ {a b : VExpr}, ReflTransGen (R cycCtx) a b → a ≠ b → lt b a := by
    intro a b H
    induction H with
    | rfl => intro hne; exact absurd rfl hne
    | @tail c b h1 h2 ih =>
      intro _
      refine Classical.byCases (p := a = c) (fun hac => ?_) (fun hac => ?_)
      · exact hac ▸ hdec _ _ _ h2
      · exact htrans _ _ _ (hdec _ _ _ h2) (ih hac)
  obtain ⟨c1, c2⟩ := cyc_of_answers H1 H2
  exact asym (chain c1 cycG_ne_cycG2) (chain c2 (Ne.symm cycG_ne_cycG2))

/-! ## §3 `ParRedP` meets the requirement -- so the theorem is about the real extension -/

theorem cycParRedP_G : @VEnv.ParRedP cycParams cycCtx cycG cycG2 := by
  letI := cycParams
  exact .app (.of .const) (.proofRepl cycEnv_hasP cycEnv_hasD cycEnv_hasD2)

theorem cycParRedP_G2 : @VEnv.ParRedP cycParams cycCtx cycG2 cycG := by
  letI := cycParams
  exact .app (.of .const) (.proofRepl cycEnv_hasP cycEnv_hasD2 cycEnv_hasD)

theorem cycParRedP_answers1 :
    AnswersAt (@VEnv.ParRedP cycParams) cycCtx cycQ2 cycG (fun _ => []) :=
  ⟨cycG2, _, _, .tail .rfl cycParRedP_G, .app .const .const, fun lp => by cases lp <;> exact .nil⟩

theorem cycParRedP_answers2 :
    AnswersAt (@VEnv.ParRedP cycParams) cycCtx cycQ cycG2 (fun _ => []) :=
  ⟨cycG, _, _, .tail .rfl cycParRedP_G2, .app .const .const, fun lp => by cases lp <;> exact .nil⟩

/-- **`ParRedP` admits no decreasing measure.**  Unconditional, and it is the extension
`ParRedMissing.lean` actually defines rather than a hypothesis about it. -/
theorem parRedP_no_decreasing_measure (μ : VExpr → Nat)
    (hdec : ∀ Γ e e', @VEnv.ParRedP cycParams Γ e e' → μ e' < μ e) : False :=
  no_decreasing_measure μ hdec cycParRedP_answers1 cycParRedP_answers2


/-! ## §4 No grading removes the cycle, for any grading whatsoever -/

/-- **Grading is powerless here, and the reason is structural.**  A *grading* of a one-step
relation is a monotone family whose union is the relation.  A two-cycle is **two steps**, and a
grading bounds structure *within* a step, never the length of a chain -- so the cycle already
lives at some finite grade.

This closes the `ParRedKn` route for the cycle, and closes it for **every** grading rather than
that one.  Note the contrast with `descend` (ledger row 71a): there grading failed because the
term does not *move*, and no grading fixes that; here the terms move, they move in a circle, and
no grading fixes that either -- but for a different reason, which is why the route had to be
checked separately rather than inherited. -/
theorem no_grading_removes_cycle
    {R : List VExpr → VExpr → VExpr → Prop} {Rn : Nat → List VExpr → VExpr → VExpr → Prop}
    (hmono : ∀ n Γ a b, Rn n Γ a b → Rn (n+1) Γ a b)
    (hcover : ∀ Γ a b, R Γ a b → ∃ n, Rn n Γ a b)
    (Γ : List VExpr) (a b : VExpr) (h1 : R Γ a b) (h2 : R Γ b a) :
    ∃ N, Rn N Γ a b ∧ Rn N Γ b a := by
  have up : ∀ n m, n ≤ m → ∀ x y, Rn n Γ x y → Rn m Γ x y := by
    intro n m hle x y h
    induction hle with
    | refl => exact h
    | step _ ih => exact hmono _ _ _ _ ih
  obtain ⟨n1, hn1⟩ := hcover _ _ _ h1
  obtain ⟨n2, hn2⟩ := hcover _ _ _ h2
  exact ⟨max n1 n2, up _ _ (Nat.le_max_left _ _) _ _ hn1,
    up _ _ (Nat.le_max_right _ _) _ _ hn2⟩

/-! ## §5 The precise request: rule-table canonicity, with no reduction relation in it -/

namespace VEnv
section
variable [Params]
open Params

/-- **The request.**  Two registered `.app` rules matching one application at *definitionally
equal* major premises produce `NormalEq`-related right-hand sides.

Bounded above by what it is asked to supply, and it mentions **no reduction relation**: only
`Params.Pat` (the rule table), `Pattern.Matches` (syntactic), `IsDefEqU` (the judgment) and
`NormalEq` (the equivalence the confluence layer is stated in).  This is `docs/design-inductive.md`
§7.6's lemma M3 / `pat_major_canonical`, stated so that nothing about `ParRed`, `ParRedK` or any
grading is smuggled in.

`kDiamond_of_patMajorCanonical` below discharges `KDescend.lean`'s `KDiamond` from it. -/
def PatMajorCanonical : Prop :=
  ∀ {Γ : List VExpr} {p₁ p₂ q₁ q₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {r' : (Pattern.app q₁ q₂).RHS × (Pattern.app q₁ q₂).Check}
    {f h c c' A₀ B₀ A₀' B₀' : VExpr} {m1 m2 m1' m2'},
    Params.Pat (Pattern.app p₁ p₂) r → Params.Pat (Pattern.app q₁ q₂) r' →
    (Pattern.app p₁ p₂).Matches (VExpr.app f c) m1 m2 →
    (Pattern.app q₁ q₂).Matches (VExpr.app f c') m1' m2' →
    HasType env univs Γ f (.forallE A₀ B₀) → HasType env univs Γ f (.forallE A₀' B₀') →
    IsDefEq env univs Γ h c A₀ → IsDefEq env univs Γ h c' A₀' →
    NormalEq Γ (Pattern.RHS.apply m1 m2 r.1) (Pattern.RHS.apply m1' m2' r'.1)

/-- **`KDiamond` follows from the request, and the reduction is `sorryAx`-free.**  So the whole
`ParRedK` confluence route sits behind one named prerequisite about the rule table -- which is the
localisation this round was after.

**Why the two major-premise conversions are passed un-composed.**  The natural-looking
hypothesis is a single `IsDefEqU Γ c c'`, composing `h ≡ c : A₀` with `h ≡ c' : A₀'` through the
shared redex.  Composing them needs `IsDefEqU.trans`, which reconciles `A₀` with `A₀'` and
therefore **carries `sorryAx`** (unique typing -- verified: `IsDefEqU.trans` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`).  Stating the request with the two
conversions separate is *weaker as a hypothesis*, hence a **tighter** request, and keeps this
reduction free of the injectivity holes -- ledger row 64a's split, applied deliberately: the
direction that guides work stays clean. -/
theorem kDiamond_of_patMajorCanonical (H : PatMajorCanonical) : KDiamond := by
  intro Γ e e₁ e₂ hΓ H1 H2
  cases H1 with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
    cases H2 with
    | @mk q₁ q₂ r' _ _ c' A₀' B₀' m1' m2' hpat' hm' hck' hf' hdq' =>
      exact H hpat hpat' hm hm' hf hf' hdq hdq'

end
end VEnv

/-- The instance: `ParRedP`'s cycle survives every grading of `ParRedP`. -/
theorem parRedP_cycle_survives_grading
    {Rn : Nat → List VExpr → VExpr → VExpr → Prop}
    (hmono : ∀ n Γ a b, Rn n Γ a b → Rn (n+1) Γ a b)
    (hcover : ∀ Γ a b, @VEnv.ParRedP cycParams Γ a b → ∃ n, Rn n Γ a b) :
    ∃ N, Rn N cycCtx cycG cycG2 ∧ Rn N cycCtx cycG2 cycG :=
  no_grading_removes_cycle hmono hcover cycCtx cycG cycG2 cycParRedP_G cycParRedP_G2

end Lean4Lean
