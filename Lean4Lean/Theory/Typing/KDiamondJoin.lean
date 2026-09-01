import Lean4Lean.Theory.Typing.KEtaDiamond

/-!
# `KDiamond` and M3, restated as joinability -- and priced

`Verify/QuotAppParams.lean` refutes **both** `KDescend.KDiamond` and `ParRedCycle.PatMajorCanonical`
(M3) at the canonical `.app`-pattern instance `quotParams`, and refutes them for one reason:
`quotRHS` is `g x` for the *matched* argument, so two `K⁺` steps at one redex give `g x` and
`g ((fun y => y) x)` -- definitionally equal by β, and `NormalEq` has no β step.  The same file
shows the rule table is **not** the defect (`quotParams_kDiamond_joinable`): the two reducts are
joinable in one β-step.

This file carries out the restatement that observation calls for, and then prices it.

## 1. The statements

`Joins` is `KEta.EtaKDiamond`'s conclusion, **reused rather than re-invented**: `Joins` is
defined once, and `etaKDiamond_eq_joins` / `etaKDiamondAt_eq_joins` prove that `EtaKDiamond` and
`KMeasure.EtaKDiamondAt` are literally `… → Joins Γ e₁ e₂`, by `rfl`.  It is also the `ParRedK`
analogue of `ChurchRosser.CRDefEq`'s third conjunct -- which is the whole story of §3 below.

| declaration | content |
|---|---|
| `Joins Γ e₁ e₂` | `∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ NormalEq Γ e₃ e₄` |
| `KDiamondJ` | `KDiamond` with `Joins` for `NormalEq` |
| `PatMajorCanonicalJ` | M3 with `Joins` for `NormalEq`; hypotheses **verbatim** |
| `kDiamondJ_of_patMajorCanonicalJ` | **the reduction survives**: `PatMajorCanonicalJ → KDiamondJ` |
| `patMajorCanonicalJ_of_patMajorCanonical`, `kDiamondJ_of_kDiamond` | the restatements are *weaker* |

**[measured] the reduction keeps its axiom set exactly.**  `kDiamondJ_of_patMajorCanonicalJ` is
`[propext, Quot.sound]` -- `sorryAx`-free **and** `Classical.choice`-free, the same as
`kDiamond_of_patMajorCanonical`, and by the same three lines (row 88's un-composed major-premise
conversions are what keeps it clean, and nothing here recomposes them).

## 2. Instrument 7, and its dual

A joinability conclusion is *weaker*, so the risk is that it is free.  It is not, and the
boundary is exact:

* `joins_normal_iff` (**hole-free**): if both sides are `ParRedK`-normal then
  `Joins Γ e₁ e₂ ↔ NormalEq Γ e₁ e₂`.  So the restatement cannot be discharged "by both reducts
  joining at anything"; the only way to discharge it beyond `NormalEq` is a **real reduction
  step**, and on normal forms it *is* the original.  `not_joins_of_normal` is the contrapositive
  half, which is how a future refutation of `KDiamondJ` would have to be built.
* The slack is therefore non-empty **and** located: it is exactly the pairs where one side steps.
  That is the quotient witness -- `g x` is normal, `g ((fun y => y) x)` steps.
* Strictness is already witnessed **in the tree**: `quotParams_kDiamond_joinable` (`Joins` holds)
  together with `not_normalEq_gx` (`NormalEq` fails) at the same pair.  Both are
  `Verify/QuotAppParams.lean`'s, both modulo the injectivity corner -- the second needs
  `WF.propTypeAgreeOn` to block `NormalEq.proofIrrel`, and **no unconditional `¬ NormalEq`
  witness exists anywhere in `Theory/`** -- **[read]**, by inspecting each of the five
  `¬ NormalEq` occurrences in `Theory/` (`ParRedPropRefute`, `PatAppParams` ×2,
  `KCanonical` ×2): every one is a *hypothesis*, none a conclusion.  A negative established by
  enumeration of a five-element list, not by a substring count.  So an unconditional `¬ Joins` cannot be exhibited here, and
  this file does not pretend to one.
* `joins_normal_iff`'s own hypotheses are satisfiable **at every instance**: `parRedK_bvar_rigid`
  (a `bvar` is `ParRedK`-normal -- `extra` and `keta` both need a constant-headed spine), so
  `joins_bvar_iff` instantiates the collapse at two *distinct* terms, where neither side is an
  instance of `refl`.
* Non-vacuity of the hypotheses: `appParams_kDiamondJ_nondegenerate` -- one redex, two `K⁺`
  steps, two syntactically distinct reducts.  `refParams_kDiamondJ` and
  `refParams_patMajorCanonicalJ` are **vacuous** (`KStep` empty there) and are recorded as
  consistency checks only.

## 3. Is the restatement TRUE at `quotParams`?  Yes at the refuting witness -- and it is
Church--Rosser in general.  **This is the finding.**

**At the witness that refuted the originals: yes, and the proof is instance-independent.**
`joins_beta_arg` / `joins_beta_arg_id` show that `.app f x` and `.app f ((fun _ : A => x') b)`
with `x = x'.inst b` are joinable in **one** `ParRedK` step at *every* `Params` instance, with the
only hypothesis a typing for the common reduct.  So the β-in-a-matched-argument configuration --
the entire content of `quotParams_not_kDiamond` and `quotParams_not_patMajorCanonical` -- is
discharged by the joinability form.  **The restatement is not false at `quotParams`.**

**But it is not a localisation, and the bound is two-sided.**

* *Above:* `kDiamondJ_of_crK` -- `KDiamondJ` follows from Church--Rosser over `ParRedK`.  (Two
  `K⁺` reducts of one redex are definitionally equal outright, `KStep.uniq_defeq`; so
  `KDiamondJ` is an *instance* of CR, where `KDiamond` was strictly stronger than one.  Tainted,
  through `IsDefEqU.trans` inside `uniq_defeq`, as `KStep.defeq` already is.)
* *Below, and this is the new content:* `quotPat_argJoin_of_kDiamondJ` (**hole-free**,
  `[propext, Quot.sound]`) -- at any instance registering `quotPat`, `KDiamondJ` implies that for
  **arbitrary definitionally equal `x`, `x'`** of the quotient's carrier and the `Quot.lift`
  spine's function argument `g`, the applications `g x` and `g x'` are joinable.  Take the
  redex's major premise to be `Quot.mk α r x` and let the second `K⁺` step match at `x'`
  (`quotPat_two_ksteps`): `KStep`'s `hdq` is an arbitrary `IsDefEq`, so nothing constrains `x'`
  beyond conversion.  That is **Church--Rosser at an application**, not a property of the rule
  table.

So: the repair is real (the refutation dies), the reduction is intact and clean, and the
localisation `PatMajorCanonical → KDiamond` was supposed to deliver is *gone* -- `KDiamondJ` is
sandwiched between two Church--Rosser statements.  `KDescend.KDiamond`'s own docstring already
warned that "the whole content of `KDiamond` is the upgrade from `≡` to `≡ₚ`, which is exactly
what confluence is being built to deliver"; the joinability form does not escape that, it lands
*on* it.

`joins_app_of_joins_arg` is the positive half of the same shape: if the matched arguments join,
the reducts join.  It is **not** a converse -- turning it into one needs the two `hdq`
conversions to yield `x ≡ x'`, i.e. injectivity of `Quot.mk`, which is not available.  It is the
one tainted statement in this file that is *not* an assembly: `NormalEq.appDF` wants the two
reducts typed, and `ParRedKS.hasType` (subject reduction for `ParRedK`) is where the
unique-typing hole enters -- pre-existing, and nothing else in §1--§3 depends on it.

## 4. Companion results for `Verify/QuotAppParams.lean` -- stated, not applied

`quotParams` lives in `Verify/`, which `Theory/` cannot import, and this stream does not own that
file.  The three companions below were **checked to compile** in a scratch file importing
`Verify.QuotAppParams` (then deleted); they are stated here for whoever owns that file:

```lean
section
attribute [local instance] quotParams

/-- `KDiamondJ` at the canonical instance forces Church-Rosser at the carrier. -/
theorem quotParams_kDiamondJ_forces_argJoin (H : KDiamondJ) {x x' : VExpr}
    (hx : qEnv.IsDefEq 0 qc1 x x' (.bvar 6)) :
    Joins qc1 (.app (.bvar 3) x) (.app (.bvar 3) x') :=
  quotPat_argJoin_of_kDiamondJ (ls := [.succ .zero, .succ .zero]) (ls' := [.succ .zero])
    H quotParams_pat_app qc1_wf ⟨_, qT_alpha⟩ ⟨_, qT_r⟩ rfl
    qLift1_hasType qMk1_2_hasType hx rfl

/-- The joinability form is TRUE at the pair that refuted `KDiamond`, from the general lemma. -/
theorem quotParams_joins_beta_witness :
    Joins qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) qXbeta) :=
  joins_beta_arg_id (A := .bvar 6) (qT_gx qT_x)

theorem quotParams_kDiamondJ_at_refuting_witness (H : KDiamondJ) :
    Joins qc1 (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) qXbeta) :=
  H qc1_wf quotParams_kstep_x quotParams_kstep_xbeta
end
```

All three measure `[propext, sorryAx, Classical.choice, Quot.sound]` -- tainted **only by
mentioning the instance** (`quotParams` is `paramsOfPiInv … (piInv_axiom …)`), exactly as
`quotParams_kDiamond_joinable` already is, and adding no obligation.  The general lemmas they
instantiate are `sorryAx`-free.

The middle one re-proves `quotParams_kDiamond_joinable`'s content from
`joins_beta_arg_id`; it is worth having only because it shows that file's witness is an instance
of a general fact, not a coincidence of the witness.

## 5. What happens to `KEtaDiamond.etaKDiamondAt_of_kDiamond`, and is `EtaKD` still needed?

`etaKDiamondAt_of_kDiamondJ` is the reshaping, and it is *shorter* than the original: the
induction's **base** case is where `KDiamond` was used, and `EtaKDiamondAt`'s conclusion is
already `Joins`, so the base case hands `KDiamondJ`'s output straight through instead of wrapping
a `NormalEq` in two empty legs.  The `succ` case is byte-for-byte the old one.  Axioms unchanged:
`[propext, Classical.choice, Quot.sound]`, matching `etaKDiamondAt_of_kDiamond`.
`etaKDiamond_of_kDiamondJ`, `etaKDiamondAt_of_kDiamondJ_tree` and
`etaKDiamond_of_kDiamondJ_holes` follow as before.

**`EtaKD` is still needed, and the two repairs are independent.**  Measured, not asserted:

* joinability repairs the **base** case (`KDiamond` false) and touches nothing else;
* `PiDomAgreeK` is created by the **`under`** case, out of `EtaK.under`'s λ-domain slack, and
  survives the restatement untouched -- `NormalEq.lamDF` still demands a *conversion* of the two
  domains no matter what the bodies join to.  (`ParRedKS.lam` could in principle reduce the
  domains to a common form, so joinability does open a second route; but "two convertible domains
  join" is again a Church--Rosser request, so nothing is gained.  **[analysis, not a theorem]**.)
* conversely pinning the domain (`EtaKD`) removes `PiDomAgreeK` but leaves the base case needing
  `KDiamond`, which is false.  `etaKDDiamondAt_of_kDiamondJ` is therefore **both** repairs at
  once, and with them the η-layer needs `KDiamondJ` and nothing else:
  `[propext, Quot.sound]`, matching `etaKDDiamondAt_of_kDiamond`.

`EtaKD`'s own undischarged obligation (row 100b: the kills need `dom e` defined and
Π-typing-derivable) is untouched by any of this.

## 6. Per-consumer satisfiability

`KDiamond`'s consumers are `KEtaDiamond`'s η-layer theorems and (not yet written)
`ParRed.triangle`.  Nothing became vacuous, and each surviving consumer is instantiated:

| consumer | witness |
|---|---|
| `etaKDDiamondAt_of_kDiamondJ` | `appParams_etaKD_diamondJ`, at the two `EtaKD` derivations of `KEtaDiamond.appParams_etaKD_under{,'}` |
| `etaKDiamondAt_of_kDiamondJ` | `appParams_etaKDiamondAt_zero`, at height 0 -- the layer the repair is about.  Its three other hypotheses are carried as parameters, since `PiDomAgreeK` is *not* available at `appParams` and discharging it from the tree would taint the witness for no gain |
| `kDiamondJ_of_patMajorCanonicalJ` | `appParams_kDiamondJ`, from `appParams_patMajorCanonicalJ`; non-degenerate by `appParams_kDiamondJ_nondegenerate` |
| `ParRed.triangle` | **none** -- it does not exist yet, at either strength.  Not claimed as satisfied |

## 7. Measured, this file, `#print axioms`

**No declaration in this file carries a local `sorry`, and only two carry `sorryAx` at all.**

| axiom set | declarations |
|---|---|
| none | `quotLiftSpine`, `quotMkSpine` |
| `[propext, Quot.sound]` | `Joins`, `KDiamondJ`, `PatMajorCanonicalJ`, `etaKDiamond_eq_joins`, `etaKDiamondAt_eq_joins`, `Joins.of_normalEq`, **`kDiamondJ_of_patMajorCanonicalJ`**, `patMajorCanonicalJ_of_patMajorCanonical`, `kDiamondJ_of_kDiamond`, `joins_normal_iff`, `not_joins_of_normal`, `parRedK_bvar_rigid`, `joins_bvar_iff`, `joins_beta_arg`, `joins_beta_arg'`, `joins_beta_arg_id`, **`etaKDDiamondAt_of_kDiamondJ`**, `quotPat_matches_spine`, `quotPat_two_ksteps`, **`quotPat_argJoin_of_kDiamondJ`** |
| `[propext, Classical.choice, Quot.sound]` | `etaKDiamondAt_of_kDiamondJ`, `etaKDiamond_of_kDiamondJ`, the four `appParams_*`, the two `refParams_*` |
| `[propext, sorryAx, Classical.choice, Quot.sound]` | `etaKDiamondAt_of_kDiamondJ_tree`, `etaKDiamond_of_kDiamondJ_holes` (the two in-tree discharges, same holes as `KEtaDiamond`'s), `kDiamondJ_of_crK` (`IsDefEqU.trans`), `joins_app_of_joins_arg` (`ParRedKS.hasType`) |

So the two headline results -- the reduction and the pricing -- are both `sorryAx`-free, and the
reduction is `Classical.choice`-free as well.

## 8. What is NOT claimed

* Not that `KDiamondJ` is **true** at `quotParams`.  What is proved is that the witness which
  refutes `KDiamond` there does *not* refute it, and that proving it there would prove
  Church--Rosser at the carrier.  A *refutation* of it at `quotParams` would likewise refute
  Church--Rosser for a real `VEnv.WF` environment -- which would be a much larger finding than
  this one, and nothing here suggests it.
* Not that `IsDefEq.church_rosser` or `NormalEq.parRed` are repaired.  They are refuted **as
  stated** (`quotParams_not_crStatement`, `quotParams_not_parRedStatement`) and joinability is a
  repair of `KDiamond`, not licence to soften them.  The `ParRed → ParRedK` repair (row 78b) is
  still the fix there.
* Not that the localisation of confluence to the rule table survives.  §3 says it does not.
* No measure, no grading, and no syntactic side condition is introduced anywhere in this file.
  The `ParRed` cycle question (rows 87/87a) is untouched, and `midShapeless_vacuous`'s ruling is
  not tested against: `KDiamondJ` names two reduction relations, which is what row 94b demands
  of any request handed to the confluence layer.
-/
namespace Lean4Lean
namespace VEnv

open VExpr

section
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-- **The joinability shape, named once.**  This is `KEta.EtaKDiamond`'s conclusion verbatim
(and `KMeasure.EtaKDiamondAt`'s), and it is the `ParRedK` analogue of `CRDefEq`'s third
conjunct. -/
def Joins (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ Γ ⊢ e₃ ≡ₚ e₄

/-- The reuse is literal, not analogical. -/
theorem etaKDiamond_eq_joins :
    EtaKDiamond = ∀ {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
      EtaK Γ e e₁ → EtaK Γ e e₂ → Joins Γ e₁ e₂ := rfl

theorem etaKDiamondAt_eq_joins :
    EtaKDiamondAt = ∀ {k : Nat} {Γ : List VExpr} {e e₁ e₂ : VExpr},
      OnCtx Γ (IsType env univs) → EtaKn k Γ e e₁ → EtaKn k Γ e e₂ → Joins Γ e₁ e₂ := rfl

/-- `NormalEq` on the nose is joinability with both legs empty. -/
theorem Joins.of_normalEq {Γ : List VExpr} {e₁ e₂ : VExpr} (h : Γ ⊢ e₁ ≡ₚ e₂) :
    Joins Γ e₁ e₂ := ⟨_, _, .rfl, .rfl, h⟩

/-- **`KDiamond`, restated as joinability.**  Two `K⁺` steps at one redex have *joinable*
reducts, rather than `NormalEq` reducts. -/
def KDiamondJ : Prop :=
  ∀ {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
    KStep Γ e e₁ → KStep Γ e e₂ → Joins Γ e₁ e₂

/-- **`PatMajorCanonical` (M3), restated as joinability.**  Hypotheses verbatim from
`ParRedCycle.PatMajorCanonical`; only the conclusion moves. -/
def PatMajorCanonicalJ : Prop :=
  ∀ {Γ : List VExpr} {p₁ p₂ q₁ q₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {r' : (Pattern.app q₁ q₂).RHS × (Pattern.app q₁ q₂).Check}
    {f h c c' A₀ B₀ A₀' B₀' : VExpr} {m1 m2 m1' m2'},
    Params.Pat (Pattern.app p₁ p₂) r → Params.Pat (Pattern.app q₁ q₂) r' →
    (Pattern.app p₁ p₂).Matches (VExpr.app f c) m1 m2 →
    (Pattern.app q₁ q₂).Matches (VExpr.app f c') m1' m2' →
    HasType env univs Γ f (.forallE A₀ B₀) → HasType env univs Γ f (.forallE A₀' B₀') →
    IsDefEq env univs Γ h c A₀ → IsDefEq env univs Γ h c' A₀' →
    Joins Γ (Pattern.RHS.apply m1 m2 r.1) (Pattern.RHS.apply m1' m2' r'.1)

/-- **The reduction survives the restatement**, and by the same three lines:
`kDiamond_of_patMajorCanonical` with `Joins` in place of `NormalEq`. -/
theorem kDiamondJ_of_patMajorCanonicalJ (H : PatMajorCanonicalJ) : KDiamondJ := by
  intro Γ e e₁ e₂ hΓ H1 H2
  cases H1 with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
    cases H2 with
    | @mk q₁ q₂ r' _ _ c' A₀' B₀' m1' m2' hpat' hm' hck' hf' hdq' =>
      exact H hpat hpat' hm hm' hf hf' hdq hdq'

/-- The restatement is *weaker*: the original implies it. -/
theorem patMajorCanonicalJ_of_patMajorCanonical (H : PatMajorCanonical) : PatMajorCanonicalJ :=
  fun hp hp' hm hm' hf hf' hd hd' => .of_normalEq (H hp hp' hm hm' hf hf' hd hd')

theorem kDiamondJ_of_kDiamond (H : KDiamond) : KDiamondJ :=
  fun hΓ h1 h2 => .of_normalEq (H hΓ h1 h2)


/-! ## Instrument 7, dual: where the restatement says *less*, and where it says the same

A joinability conclusion is weaker than a `NormalEq` conclusion, so the first thing to check is
that it is not weaker to the point of being free.  It is not, and the boundary is exact: on
`ParRedK`-normal terms `Joins` **is** `NormalEq`, so every pair the original could not relate
and that does not reduce is still unrelated.  The slack is entirely at pairs where at least one
side takes a step -- which is exactly the quotient-rule witness (`quotRHS`'s matched argument is
a β-redex, so the second reduct reduces and the first does not). -/

/-- **`Joins` collapses to `NormalEq` on normal forms.**  So the restatement cannot be
discharged "by both reducts joining at anything": it can only be discharged by real reduction. -/
theorem joins_normal_iff {Γ : List VExpr} {e₁ e₂ : VExpr}
    (h1 : ∀ o, ParRedK Γ e₁ o → o = e₁) (h2 : ∀ o, ParRedK Γ e₂ o → o = e₂) :
    Joins Γ e₁ e₂ ↔ Γ ⊢ e₁ ≡ₚ e₂ := by
  refine ⟨fun ⟨e₃, e₄, r1, r2, hne⟩ => ?_, Joins.of_normalEq⟩
  cases parRedKS_rigid h1 r1; cases parRedKS_rigid h2 r2; exact hne

/-- One half of the same fact, stated where it is used: if the left side is normal and the two
are not `NormalEq`, joinability still demands a real step on the right. -/
theorem not_joins_of_normal {Γ : List VExpr} {e₁ e₂ : VExpr}
    (h1 : ∀ o, ParRedK Γ e₁ o → o = e₁) (h2 : ∀ o, ParRedK Γ e₂ o → o = e₂)
    (hne : ¬ Γ ⊢ e₁ ≡ₚ e₂) : ¬ Joins Γ e₁ e₂ := fun h => hne ((joins_normal_iff h1 h2).1 h)

/-! ### …and `joins_normal_iff`'s hypotheses are satisfiable at *every* instance

Instrument 7 for the collapse lemma itself: a `bvar` is `ParRedK`-normal at every `Params`
instance -- `extra` needs a constant-headed spine (`Pattern.Matches.spineHead_const`) and `keta`
needs one too (`EtaK.not_bvar`) -- so the equivalence is instantiated at two *distinct* terms,
where it is not an instance of reflexivity. -/

theorem parRedK_bvar_rigid {Γ : List VExpr} {i : Nat} {o : VExpr}
    (h : ParRedK Γ (.bvar i) o) : o = .bvar i := by
  cases h with
  | bvar => rfl
  | extra _ h2 => obtain ⟨_, _, hc⟩ := h2.spineHead_const; exact nomatch hc
  | keta h _ => exact absurd h EtaK.not_bvar

/-- The collapse, instantiated at two distinct `bvar`s: no reduction is available on either
side, so joinability there *is* `NormalEq`, and neither is an instance of `refl`. -/
theorem joins_bvar_iff {Γ : List VExpr} {i j : Nat} :
    Joins Γ (.bvar i) (.bvar j) ↔ Γ ⊢ .bvar i ≡ₚ .bvar j :=
  joins_normal_iff (fun _ => parRedK_bvar_rigid) (fun _ => parRedK_bvar_rigid)

/-! ## The witness that refuted the originals, and what the restatement does with it

`Verify/QuotAppParams.lean`'s refutation turns on one thing: `quotRHS` is `g x` for the
*matched* argument `x`, so two `K⁺` steps at one redex give `g x` and `g x'` where `x'` is a
β-redex with `x` as its contractum, and `NormalEq` has no β step.  `joins_beta_arg` is that
configuration in the abstract: **the joinability form discharges it outright, in one `ParRedK`
step, at every `Params` instance.**  Nothing about the rule table is used. -/

/-- **The β-in-a-matched-argument witness joins.**  `.app f (e.inst b)` and
`.app f ((fun _ : A => e) b)` -- the two shapes `quotParams_kstep_x` and
`quotParams_kstep_xbeta` produce -- are joinable in one `ParRedK` step.  The only hypothesis is
a typing for the common reduct, which `NormalEq.refl` needs. -/
theorem joins_beta_arg {Γ : List VExpr} {f A e b T : VExpr}
    (h : Γ ⊢ .app f (e.inst b) : T) :
    Joins Γ (.app f (e.inst b)) (.app f (.app (.lam A e) b)) :=
  ⟨_, _, .rfl, .tail .rfl (.app .rfl (.beta .rfl .rfl)), .refl h⟩

/-- The same, with the β-redex on the left. -/
theorem joins_beta_arg' {Γ : List VExpr} {f A e b T : VExpr}
    (h : Γ ⊢ .app f (e.inst b) : T) :
    Joins Γ (.app f (.app (.lam A e) b)) (.app f (e.inst b)) :=
  ⟨_, _, .tail .rfl (.app .rfl (.beta .rfl .rfl)), .rfl, .refl h⟩

/-- **And the identity-function instance, which is the witness on the nose.**  With
`e := .bvar 0` the β-redex is `(fun _ : A => y) x` for `x = y`, i.e. `qXbeta`. -/
theorem joins_beta_arg_id {Γ : List VExpr} {f A x T : VExpr}
    (h : Γ ⊢ .app f x : T) :
    Joins Γ (.app f x) (.app f (.app (.lam A (.bvar 0)) x)) := by
  have := joins_beta_arg (f := f) (A := A) (e := .bvar 0) (b := x) (by simpa [VExpr.inst] using h)
  simpa [VExpr.inst] using this

/-! ## The η-layer, reshaped

`KEtaDiamond.etaKDiamondAt_of_kDiamond` is a true implication whose premise is now known false
(`quotParams_not_kDiamond`), so it is undischargeable as stated.  The repair is one line: the
induction's **base** case is where `KDiamond` was used, and `EtaKDiamondAt`'s conclusion is
*already* the joinability shape (`etaKDiamondAt_eq_joins`), so the base case gets *shorter* --
the two `.rfl` legs the old proof had to supply are now whatever `KDiamondJ` hands over.  The
`succ` case is byte-for-byte the old one.

**The two repairs are independent.**  Joinability fixes the base case; `PiDomAgreeK` is created
by the `under` case, out of `EtaK.under`'s λ-domain slack, and joinability does not touch it --
`NormalEq.lamDF` still demands a *conversion* of the two domains, whatever the bodies join to.
Conversely pinning the domain (`EtaKD`) removes `PiDomAgreeK` but leaves the base case needing
`KDiamond`, which is false.  So `EtaKD` is still needed, and
`etaKDDiamondAt_of_kDiamondJ` below is the combination: **both** repairs, and then the η-layer
needs `KDiamondJ` and nothing else. -/

/-- **The equal-height diamond, from `KDiamondJ`.**  Compare
`KEtaDiamond.etaKDiamondAt_of_kDiamond`: same hypotheses with `KDiamond` replaced, same `succ`
case, and a base case that no longer has to manufacture the two empty reduction legs. -/
theorem etaKDiamondAt_of_kDiamondJ (HK : KDiamondJ) (HD : PiDomAgreeK)
    (HB : EtaKBodyTyped) (HC : ParRedKSDomConv) : EtaKDiamondAt := by
  intro k
  induction k with
  | zero =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | here hs1 =>
    cases H2 with | here hs2 =>
    exact HK hΓ hs1 hs2
  | succ k ih =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | @under _ _ A₁ B₁ t₁ _ hty1 h1 =>
    cases H2 with | @under _ _ A₂ B₂ t₂ _ hty2 h2 =>
    obtain ⟨u, hAA⟩ := HD hΓ (EtaKn.toEtaK (.under hty1 h1)) hty1 hty2
    have hΓ₁ : OnCtx (A₁::Γ) (IsType env univs) := ⟨hΓ, _, hAA.hasType.1⟩
    have h2' : EtaKn k (A₁::Γ) (.app e.lift (.bvar 0)) t₂ :=
      h2.defeqDFC hΓ (.succ .zero hAA.symm)
    obtain ⟨t₃, t₄, r1, r2, hne⟩ := ih hΓ₁ h1 h2'
    have ht₂ : (A₁::Γ) ⊢ t₂ : B₁ := HB hΓ hty1 h2'.toEtaK
    exact ⟨.lam A₁ t₃, .lam A₂ t₄, ParRedKS.lam .rfl r1,
      ParRedKS.lam .rfl (HC hΓ hAA ht₂ r2), .lamDF hAA.hasType.1 hAA hne⟩

/-- **The η-layer, from `KDiamondJ` and the three named facts.** -/
theorem etaKDiamond_of_kDiamondJ (HK : KDiamondJ) (HD : PiDomAgreeK)
    (HB : EtaKBodyTyped) (HC : ParRedKSDomConv) : EtaKDiamond :=
  etaKDiamond_of_at (etaKDiamondAt_of_kDiamondJ HK HD HB HC)

/-- The two routine facts discharged from the tree, as in `KEtaDiamond.lean`; tainted by the
same pre-existing holes and no others. -/
theorem etaKDiamondAt_of_kDiamondJ_tree (HK : KDiamondJ) (HD : PiDomAgreeK) : EtaKDiamondAt :=
  etaKDiamondAt_of_kDiamondJ HK HD etaKBodyTyped_tree parRedKSDomConv_tree

theorem etaKDiamond_of_kDiamondJ_holes (HK : KDiamondJ) : EtaKDiamond :=
  etaKDiamond_of_at
    (etaKDiamondAt_of_kDiamondJ_tree HK (piDomAgreeK_of_piDomAgree piDomAgree_tree))

/-- **Both repairs at once: the pinned η-tower needs `KDiamondJ` and nothing else.**  The
analogue of `KEtaDiamond.etaKDDiamondAt_of_kDiamond`, whose `KDiamond` premise is false. -/
theorem etaKDDiamondAt_of_kDiamondJ (HK : KDiamondJ) {dom : VExpr → Option VExpr} :
    ∀ {k : Nat} {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
      EtaKD dom k Γ e e₁ → EtaKD dom k Γ e e₂ → Joins Γ e₁ e₂ := by
  intro k
  induction k with
  | zero =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | here hs1 =>
    cases H2 with | here hs2 =>
    exact HK hΓ hs1 hs2
  | succ k ih =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | @under _ _ A₁ B₁ t₁ _ _ hd1 hA hty1 h1 =>
    cases H2 with | @under _ _ A₂ B₂ t₂ _ _ hd2 _ hty2 h2 =>
    cases Option.some.inj (hd1.symm.trans hd2)
    have hΓ₁ : OnCtx (A₁::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    obtain ⟨t₃, t₄, r1, r2, hne⟩ := ih hΓ₁ h1 h2
    exact ⟨.lam A₁ t₃, .lam A₁ t₄, ParRedKS.lam .rfl r1, ParRedKS.lam .rfl r2,
      .lamDF hA hA hne⟩

/-! ## What the restatement costs: at the canonical rule table it is Church--Rosser

The rest of this file prices the repair, and the price is the finding.  `KStep.uniq_defeq`
already says two `K⁺` reducts of one redex are **definitionally equal**; `KDiamondJ` asks them
to be **joinable**.  So `KDiamondJ` is an *instance of Church--Rosser* (over `ParRedK`), where
`KDiamond` was strictly stronger than one.  `kDiamondJ_of_crK` is that upper bound.

The lower bound is the interesting half, and it is specific to the quotient rule: because
`quotRHS` is `g x` for the matched argument, the pairs `KDiamondJ` must join at `quotPat`
include `(g x, g x')` for **arbitrary definitionally equal `x`, `x'`** -- one takes the redex's
major premise to be `Quot.mk α r x` and lets the second step match at `x'`.  That is
Church--Rosser at an application, not a property of the rule table. -/

/-- **`KDiamondJ` is implied by Church--Rosser over `ParRedK`.**  Tainted: `KStep.uniq_defeq`
composes two `IsDefEqU`s, so it carries the unique-typing hole, exactly as
`KStep.defeq`/`IsDefEqU.trans` do. -/
theorem kDiamondJ_of_crK
    (H : ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
      IsDefEq env univs Γ e₁ e₂ A → Joins Γ e₁ e₂) : KDiamondJ :=
  fun hΓ h1 h2 => have ⟨_, h⟩ := KStep.uniq_defeq hΓ h1 h2; H hΓ h

/-- The five-argument `Quot.lift` spine, at arbitrary arguments. -/
def quotLiftSpine (ls : List VLevel) (a0 a1 a2 a3 a4 : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.lift ls) a0) a1) a2) a3) a4

/-- The three-argument `Quot.mk` spine, at arbitrary arguments. -/
def quotMkSpine (ls' : List VLevel) (b0 b1 t : VExpr) : VExpr :=
  .app (.app (.app (.const ``Quot.mk ls') b0) b1) t

/-- **The quotient pattern matches any such pair of spines, its right-hand side is `a3 t`, and
its `Check` reduces to two parameter conversions and one level equivalence.**  The
instance-independent form of `Verify/QuotAppParams.lean`'s `quot_matches`: no environment and no
typing are used, only `argPaths` arithmetic. -/
theorem quotPat_matches_spine {Γ : List VExpr} {ls ls' : List VLevel}
    (a0 a1 a2 a3 a4 b0 b1 t : VExpr)
    (h0 : IsDefEqU env univs Γ a0 b0) (h1 : IsDefEqU env univs Γ a1 b1)
    (hl : ls.getD 0 .zero ≈ ls'.getD 0 .zero) :
    ∃ m1 m2, quotPat.Matches
        (.app (quotLiftSpine ls a0 a1 a2 a3 a4) (quotMkSpine ls' b0 b1 t)) m1 m2 ∧
      Pattern.RHS.apply m1 m2 quotRHS = .app a3 t ∧
      quotCheck.OK (IsDefEqU env univs Γ) m1 m2 := by
  refine ⟨_, _, .app (.var (.var (.var (.var (.var .const))))) (.var (.var (.var .const))),
    rfl, ?_⟩
  refine iotaCheck_OK.2 ⟨?_, by simp, ?_⟩
  · rw [show ((Pattern.argPaths (Pattern.const ``Quot.lift) 5).take 2).zip
        ((Pattern.argPaths (Pattern.const ``Quot.mk) 3).take 2)
        = [(some (some (some (some none))), some (some none)),
           (some (some (some none)), some none)] from rfl]
    intro xy hxy
    cases hxy with
    | head => exact h0
    | tail _ h2 => cases h2 with
      | head => exact h1
      | tail _ h3 => nomatch h3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hl

/-- **The two `K⁺` steps at one quotient redex, at two matched arguments.**  Both fire on the
*same* term `.app f (Quot.mk α r x)`: the first matches on the nose, the second matches at `x'`
with the major-premise conversion supplied by `x ≡ x'`.  This is
`quotParams_kstep_x`/`quotParams_kstep_xbeta` with the β-conversion generalised to an arbitrary
one. -/
theorem quotPat_two_ksteps
    (hpat : Params.Pat quotPat (quotRHS, quotCheck))
    {Γ : List VExpr} {ls ls' : List VLevel} {a0 a1 a2 a3 a4 b0 b1 A₀ A₁ B₀ C x x' : VExpr}
    (h0 : IsDefEqU env univs Γ a0 b0) (h1 : IsDefEqU env univs Γ a1 b1)
    (hl : ls.getD 0 .zero ≈ ls'.getD 0 .zero)
    (hf : Γ ⊢ quotLiftSpine ls a0 a1 a2 a3 a4 : .forallE A₀ B₀)
    (hmk : Γ ⊢ .app (.app (.const ``Quot.mk ls') b0) b1 : .forallE C A₁)
    (hx : Γ ⊢ x ≡ x' : C) (hA : A₁.inst x = A₀) :
    KStep Γ (.app (quotLiftSpine ls a0 a1 a2 a3 a4) (quotMkSpine ls' b0 b1 x)) (.app a3 x) ∧
    KStep Γ (.app (quotLiftSpine ls a0 a1 a2 a3 a4) (quotMkSpine ls' b0 b1 x)) (.app a3 x') := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quotPat_matches_spine (Γ := Γ) a0 a1 a2 a3 a4 b0 b1 x h0 h1 hl
  obtain ⟨m1', m2', hm', hrhs', hck'⟩ :=
    quotPat_matches_spine (Γ := Γ) a0 a1 a2 a3 a4 b0 b1 x' h0 h1 hl
  have hdq : IsDefEq env univs Γ (quotMkSpine ls' b0 b1 x) (quotMkSpine ls' b0 b1 x) A₀ :=
    hA ▸ IsDefEq.appDF hmk hx.hasType.1
  have hdq' : IsDefEq env univs Γ (quotMkSpine ls' b0 b1 x) (quotMkSpine ls' b0 b1 x') A₀ :=
    hA ▸ IsDefEq.appDF hmk hx
  constructor
  · have h2 : KStep Γ (.app (quotLiftSpine ls a0 a1 a2 a3 a4) (quotMkSpine ls' b0 b1 x))
        (Pattern.RHS.apply m1 m2 quotRHS) :=
      KStep.mk (Γ := Γ) (r := (quotRHS, quotCheck)) hpat hm hck hf hdq
    rwa [hrhs] at h2
  · have h2 : KStep Γ (.app (quotLiftSpine ls a0 a1 a2 a3 a4) (quotMkSpine ls' b0 b1 x))
        (Pattern.RHS.apply m1' m2' quotRHS) :=
      KStep.mk (Γ := Γ) (r := (quotRHS, quotCheck)) hpat hm' hck' hf hdq'
    rwa [hrhs'] at h2

/-- **`KDiamondJ` at the quotient rule table implies Church--Rosser at an application.**  For
**arbitrary** definitionally equal `x`, `x'` of the quotient's carrier and the `Quot.lift`
spine's function argument `a3`, the two applications `a3 x` and `a3 x'` must be joinable.

So the joinability restatement is **not** a localisation to the rule table: it is bounded above
by Church--Rosser (`kDiamondJ_of_crK`) and below by this, and both bounds are Church--Rosser
statements.  Every hypothesis here is discharged at `quotParams` -- see the companion note in the
module docstring. -/
theorem quotPat_argJoin_of_kDiamondJ (HK : KDiamondJ)
    (hpat : Params.Pat quotPat (quotRHS, quotCheck))
    {Γ : List VExpr} {ls ls' : List VLevel} {a0 a1 a2 a3 a4 b0 b1 A₀ A₁ B₀ C x x' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (h0 : IsDefEqU env univs Γ a0 b0) (h1 : IsDefEqU env univs Γ a1 b1)
    (hl : ls.getD 0 .zero ≈ ls'.getD 0 .zero)
    (hf : Γ ⊢ quotLiftSpine ls a0 a1 a2 a3 a4 : .forallE A₀ B₀)
    (hmk : Γ ⊢ .app (.app (.const ``Quot.mk ls') b0) b1 : .forallE C A₁)
    (hx : Γ ⊢ x ≡ x' : C) (hA : A₁.inst x = A₀) :
    Joins Γ (.app a3 x) (.app a3 x') :=
  have ⟨s1, s2⟩ := quotPat_two_ksteps hpat h0 h1 hl hf hmk hx hA
  HK hΓ s1 s2


/-- **The residual, in its positive form: if the matched arguments join, the reducts join.**
Congruence, so the converse of `quotPat_argJoin_of_kDiamondJ` at the level of arguments -- but
only at the level of arguments: recovering `KDiamondJ` at `quotPat` from this would need the two
matched arguments to be *known* definitionally equal, i.e. injectivity of `Quot.mk` for the two
`hdq` conversions, which is not available.  So this is an upper bound on the residual's shape,
not an equivalence. -/
theorem joins_app_of_joins_arg {Γ : List VExpr} {f A B x x' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (hf : Γ ⊢ f : .forallE A B) (hx : Γ ⊢ x : A) (hx' : Γ ⊢ x' : A)
    (h : Joins Γ x x') : Joins Γ (.app f x) (.app f x') :=
  have ⟨_, _, r1, r2, hne⟩ := h
  ⟨_, _, ParRedKS.app .rfl r1, ParRedKS.app .rfl r2,
    .appDF hf hf (ParRedKS.hasType hΓ r1 hx) (ParRedKS.hasType hΓ r2 hx') (.refl hf) hne⟩

end


/-! ## Instrument 7 at a real `.app` rule table, and at the degenerate instance

`appParams` (`PatAppParams.lean`) is the tree's `.app`-pattern instance inside `Theory/`.  There
`KDiamond` is *true*, so the restatement holds a fortiori -- which is the check that the
restatement is not *inconsistent* with the instance where the original survived, and that its
`KStep` hypotheses are satisfiable at all.  At `refParams` every statement in this file is
vacuous, `KStep` being empty; recorded, not offered as evidence. -/

section
attribute [local instance] appParams

/-- M3's joinability form, at the rule table where M3 itself holds. -/
theorem appParams_patMajorCanonicalJ : PatMajorCanonicalJ :=
  patMajorCanonicalJ_of_patMajorCanonical appParams_patMajorCanonical

theorem appParams_kDiamondJ : KDiamondJ :=
  kDiamondJ_of_patMajorCanonicalJ appParams_patMajorCanonicalJ

/-- **The instance is not degenerate**: one redex, two `K⁺` steps, two syntactically distinct
reducts, and `KDiamondJ`'s conclusion at them.  Same witness as
`appParams_kDiamond_nondegenerate`, whose `NormalEq` is what the join uses. -/
theorem appParams_kDiamondJ_nondegenerate :
    KStep [] cycG cycG2 ∧ KStep [] cycG cycG ∧ cycG2 ≠ cycG ∧ Joins [] cycG2 cycG :=
  ⟨appParams_kstep_toD2, appParams_kstep_toD, Ne.symm cycG_ne_cycG2,
    appParams_kDiamondJ trivial appParams_kstep_toD2 appParams_kstep_toD⟩

/-- **Consumer 1, instantiated**: the pinned η-tower diamond, from `KDiamondJ` alone.  The
`KDiamondJ`-analogue of `KEtaDiamond.appParams_etaKD_diamond`, at the same two derivations. -/
theorem appParams_etaKD_diamondJ :
    Joins [] (.lam (.const `P []) cycG2) (.lam (.const `P []) cycG) :=
  etaKDDiamondAt_of_kDiamondJ appParams_kDiamondJ trivial
    appParams_etaKD_under appParams_etaKD_under'

/-- **Consumer 2, instantiated**: the unpinned equal-height diamond needs `PiDomAgreeK`, which
is *not* available at `appParams` (`KEtaDiamond`'s closing note), so what is exhibited here is
the height-0 layer -- i.e. exactly the base case the restatement repairs. -/
theorem appParams_etaKDiamondAt_zero (HD : PiDomAgreeK) (HB : EtaKBodyTyped)
    (HC : ParRedKSDomConv) : Joins [] cycG2 cycG :=
  etaKDiamondAt_of_kDiamondJ appParams_kDiamondJ HD HB HC trivial
    (.here appParams_kstep_toD2) (.here appParams_kstep_toD)

end

section
attribute [local instance] refParams

/-- Vacuous at the witness instance, `KStep` being empty there.  A consistency check and
nothing more. -/
theorem refParams_kDiamondJ : KDiamondJ :=
  fun _ h _ => absurd h refParams_no_kstep

theorem refParams_patMajorCanonicalJ : PatMajorCanonicalJ :=
  fun hp _ _ _ _ _ _ _ => absurd hp refNoPat

end

end VEnv
end Lean4Lean
