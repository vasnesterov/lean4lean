import Lean4Lean.Theory.Typing.KEta

/-!
# The `keta` termination measure

`docs/handoff-krule.md` §T6 flags one genuinely new obligation created by the `EtaK` design,
and calls it the step at which the design could still be wrong:

> `CParRed.exists`'s structural recursion cannot handle `keta`: it recurses from `e` into
> `.app e.lift (.bvar 0)`, which is *larger*.  A measure does exist -- the registered
> pattern's arity minus the term's application depth, which `EtaK.matches_head` bounds --
> but it has to be built.

This file builds it, and the construction turns out to give more than termination.

## The measure

`e.appDepth` counts the applications at the head of `e`; `p.depth` counts the `app`/`var`
nodes of a pattern.  `Pattern.Matches.appDepth` says a match forces the two to agree, so an
`EtaK` derivation's η-tower has an *exactly determined* height:

```
EtaK.tower :  EtaK Γ e e' → e.appDepth + (tower height) = p₁.depth + 1
```

for the registered pattern `.app p₁ p₂` at `e`'s head constant.  Since η-expansion adds
exactly one to `appDepth` (`VExpr.appDepth_etaExpand`), the measure `p₁.depth + 1 - appDepth`
drops by one per `under` layer and hits `0` at `here`.

## Why `p₁.depth` is a function of `e` and not of the derivation

The measure would be useless if a term could be an `EtaK` redex at two registered patterns of
different depths: the "fuel" would then depend on the derivation being built rather than on
the term, and no well-founded recursion could use it.  It cannot:

`Params.pat_app_arity_uniq` **[machine-checked]** -- *two registered patterns with the same
head constant have the same function-side depth.*  The proof is `Params.pat_app_l_uniq`
applied in both directions: for each `j ≤ m` it forbids the other pattern's arity from being
`j-1`, so each arity is `≥` the other.  Nothing else in `Params` is used, and in particular
no new field is added.

## What this discharges, and what it does not

* **Discharged**: the `under` recursion terminates, with a measure that is a function of the
  term alone (`EtaK.fuel`), and every `EtaK` derivation at a given `Γ, e` has the *same*
  height (`EtaK.height_uniq`).
* **Not discharged, and unchanged by this file**: the `here` branch's canonical major premise
  `c` is not a subterm of the redex, so a complete development still has to choose one.  That
  is `docs/design-inductive.md` §7.6's lemma M3 (`pat_major_canonical`), priced in
  `docs/handoff-krule.md` §S7 and untouched here.

The height fact has a second consumer that §T6 did not anticipate; see
`EtaK.height_uniq`'s docstring and `docs/handoff-krule.md`.
-/

namespace Lean4Lean

open VExpr

/-- The number of applications at the head of a term.  `Pattern.Matches` pins this exactly
(`Pattern.Matches.appDepth`), which is what makes the η-tower's height determined. -/
def VExpr.appDepth : VExpr → Nat
  | .app f _ => f.appDepth + 1
  | _ => 0

@[simp] theorem VExpr.appDepth_app (f a : VExpr) : (VExpr.app f a).appDepth = f.appDepth + 1 :=
  rfl

@[simp] theorem VExpr.appDepth_liftN : ∀ {n : Nat} (e : VExpr) (k : Nat),
    (e.liftN n k).appDepth = e.appDepth
  | _, .bvar _, _ | _, .sort _, _ | _, .const _ _, _
  | _, .forallE _ _, _ | _, .lam _ _, _ => rfl
  | _, .app f _, k => congrArg (· + 1) (VExpr.appDepth_liftN f k)

/-- η-expansion adds exactly one application. -/
theorem VExpr.appDepth_etaExpand (e : VExpr) :
    (VExpr.app e.lift (.bvar 0)).appDepth = e.appDepth + 1 := by
  simp [VExpr.lift]

/-- The number of `app`/`var` nodes above a pattern's head. -/
def Pattern.depth : Pattern → Nat
  | .const _ => 0
  | .app f _ => f.depth + 1
  | .var f => f.depth + 1

@[simp] theorem Pattern.depth_varN (p : Pattern) : ∀ n, (p.varN n).depth = p.depth + n
  | 0 => rfl
  | n+1 => by simp [Pattern.varN, Pattern.depth, Pattern.depth_varN p n]; omega

/-- **A match pins the application depth.**  This is the whole arithmetic content of the
measure: a pattern of depth `d` matches only terms whose head carries exactly `d`
applications. -/
theorem Pattern.Matches.appDepth {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.appDepth = p.depth := by
  induction H with
  | const => rfl
  | var _ ih => simp [Pattern.depth, ih]
  | app _ _ ih1 _ => simp [Pattern.depth, ih1]

/-- The head constant of a pattern.  (`Verify/Typing/ConstSpine.lean` declares the same
function; this one is `Theory/`-local and is the one the measure uses.  They are kept
distinct on purpose -- `scripts/dup-names.lean` would flag a collision.) -/
def Pattern.headName : Pattern → Lean.Name
  | .const c => c
  | .app f _ => f.headName
  | .var f => f.headName

@[simp] theorem Pattern.headName_varN (p : Pattern) : ∀ n, (p.varN n).headName = p.headName
  | 0 => rfl
  | n+1 => Pattern.headName_varN p n

theorem Pattern.Matches.headName {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.headConst? = some p.headName := by
  induction H with
  | const => rfl
  | var _ ih => simpa [VExpr.headConst?, Pattern.headName] using ih
  | app _ _ ih1 _ => simpa [VExpr.headConst?, Pattern.headName] using ih1

/-! ## The arity of a registered `.app` pattern is a function of its head constant

This is the fact that makes the measure a function of the *term*: without it a term could be
an `EtaK` redex at two registered patterns of different depths, and the η-tower's height
would depend on the derivation being built rather than on `e`. -/

/-- A shorter `varN` chain is a subpattern of a longer one. -/
theorem Subpattern.varN_le {p : Pattern} : ∀ {k n : Nat}, k ≤ n → Subpattern (p.varN k) (p.varN n)
  | _, 0, h => by cases Nat.le_zero.1 h; exact .refl
  | k, n+1, h => by
    rcases Nat.lt_or_ge k (n+1) with h' | h'
    · exact .varL (Subpattern.varN_le (Nat.le_of_lt_succ h'))
    · cases Nat.le_antisymm h h'; exact .refl

namespace VEnv

variable [Params]
open Params

/-- **The function-side arity of a registered `.app` pattern is determined by its head
constant.**

Two registered ι-patterns over the same recursor have the same number of leading `.var`s.
The proof is `Params.pat_app_l_uniq` in both directions and nothing else: if `m' < m` then
`(.const rec).varN m'` is `.var`-reachable inside `p₁`, so the field forces
`p₁'.inter ((.const rec).varN m') = none` -- but `p₁'` *is* `(.const rec).varN m'`, and
`Pattern.inter_self` says that intersection is `some`.

No new `Params` field is introduced, and `docs/handoff-krule.md` §S7's eight construction
sites are untouched. -/
theorem Params.pat_app_arity_uniq {rec ctor ctor' : Lean.Name} {m n m' n' : Nat}
    {r : (SimplePattern.iota rec m ctor n).toPattern.RHS ×
         (SimplePattern.iota rec m ctor n).toPattern.Check}
    {r' : (SimplePattern.iota rec m' ctor' n').toPattern.RHS ×
          (SimplePattern.iota rec m' ctor' n').toPattern.Check}
    (h : Pat (SimplePattern.iota rec m ctor n).toPattern r)
    (h' : Pat (SimplePattern.iota rec m' ctor' n').toPattern r') : m = m' := by
  have key : ∀ {c₁ c₂ : Lean.Name} {a b x y : Nat}
      {ra : (SimplePattern.iota rec a c₁ x).toPattern.RHS ×
            (SimplePattern.iota rec a c₁ x).toPattern.Check}
      {rb : (SimplePattern.iota rec b c₂ y).toPattern.RHS ×
            (SimplePattern.iota rec b c₂ y).toPattern.Check},
      Pat (SimplePattern.iota rec a c₁ x).toPattern ra →
      Pat (SimplePattern.iota rec b c₂ y).toPattern rb → b < a → False := by
    intro c₁ c₂ a b x y ra rb ha hb hlt
    have hsub : Subpattern (.var ((Pattern.const rec).varN b)) ((Pattern.const rec).varN a) := by
      have : (Pattern.const rec).varN (b+1) = .var ((Pattern.const rec).varN b) := rfl
      exact this ▸ Subpattern.varN_le hlt
    have := Params.pat_app_l_uniq ha hb (p₁ := (Pattern.const rec).varN a)
      (p₂ := (Pattern.const c₁).varN x) (p₁' := (Pattern.const rec).varN b)
      (p₂' := (Pattern.const c₂).varN y) Subpattern.refl Subpattern.refl hsub
    rw [Pattern.inter_self] at this; exact nomatch this
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd (key h' h hlt) (fun x => x)
  · exact heq
  · exact absurd (key h h' hgt) (fun x => x)

/-- The same fact stated for an arbitrary registered `.app` pattern, via `Params.pat_simple`:
the head constant determines the function side's depth. -/
theorem Params.pat_app_depth_uniq {p₁ p₂ p₁' p₂' : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {r' : (Pattern.app p₁' p₂').RHS × (Pattern.app p₁' p₂').Check}
    (h : Pat (.app p₁ p₂) r) (h' : Pat (.app p₁' p₂') r')
    (hhd : p₁.headName = p₁'.headName) : p₁.depth = p₁'.depth := by
  obtain ⟨sp, hsp⟩ := Params.pat_simple h
  obtain ⟨sp', hsp'⟩ := Params.pat_simple h'
  cases sp with
  | defn => exact nomatch hsp
  | iota rec m ctor n =>
  cases sp' with
  | defn => exact nomatch hsp'
  | iota rec' m' ctor' n' =>
  simp [SimplePattern.toPattern] at hsp hsp'
  obtain ⟨rfl, rfl⟩ := hsp
  obtain ⟨rfl, rfl⟩ := hsp'
  simp [Pattern.headName_varN, Pattern.headName] at hhd
  subst hhd
  simp only [Pattern.depth_varN, Pattern.depth]
  exact congrArg _ (Params.pat_app_arity_uniq h h')

/-! ## The counted `EtaK`, and the height equation

`EtaK`'s η-tower height is not visible in its type, so the measure is stated over a counted
copy.  `EtaK.count` and `EtaKn.toEtaK` show the two relations have the same graph. -/

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- `EtaK` with the number of `under` layers exposed.  Same rules, same graph
(`EtaK.count`, `EtaKn.toEtaK`); the index is what the measure is stated about. -/
inductive EtaKn : Nat → List VExpr → VExpr → VExpr → Prop where
  | here {Γ : List VExpr} {e t : VExpr} :
      KStep Γ e t → EtaKn 0 Γ e t
  | under {Γ : List VExpr} {e A B t : VExpr} {k : Nat} :
      Γ ⊢ e : .forallE A B →
      EtaKn k (A::Γ) (.app e.lift (.bvar 0)) t → EtaKn (k+1) Γ e (.lam A t)

theorem EtaKn.toEtaK {k : Nat} {Γ : List VExpr} {e e' : VExpr} (H : EtaKn k Γ e e') :
    EtaK Γ e e' := by
  induction H with
  | here h1 => exact .here h1
  | under h _ ih => exact .under h ih

theorem EtaK.count {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    ∃ k, EtaKn k Γ e e' := by
  induction H with
  | here h1 => exact ⟨0, .here h1⟩
  | under h _ ih => obtain ⟨k, ih⟩ := ih; exact ⟨k+1, .under h ih⟩

/-- **The height equation.**  Every `EtaK` derivation at `e` fires at a registered pattern
whose head constant is `e`'s, and its η-tower has exactly
`p₁.depth + 1 - e.appDepth` layers.

This is the measure `docs/handoff-krule.md` §T6 asks for.  The `here` case supplies the
equation (`Pattern.Matches.appDepth` on the function side of the redex) and the `under` case
propagates it, because η-expansion adds exactly one application and does not move the head
constant. -/
theorem EtaKn.height_eq {k : Nat} {Γ : List VExpr} {e e' : VExpr} (H : EtaKn k Γ e e') :
    ∃ (p₁ p₂ : Pattern) (r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check),
      Params.Pat (Pattern.app p₁ p₂) r ∧ e.headConst? = some p₁.headName ∧
      e.appDepth + k = p₁.depth + 1 := by
  induction H with
  | @here _ e t hst =>
    cases hst with
    | mk hpat hm _ _ _ =>
      cases hm with
      | app hf _ =>
        refine ⟨_, _, _, hpat, ?_, ?_⟩
        · exact hf.headName
        · simp [VExpr.appDepth, hf.appDepth]
  | @under Γ e A B t k _ _ ih =>
    obtain ⟨p₁, p₂, r, h1, h2, h3⟩ := ih
    refine ⟨p₁, p₂, r, h1, ?_, ?_⟩
    · simpa [VExpr.headConst?, VExpr.headConst?_liftN] using h2
    · simp [VExpr.appDepth, VExpr.appDepth_liftN] at h3; omega

/-- **The height is a function of the term, not of the derivation.**  Two `EtaK` derivations
at the same `Γ` and `e` have the same number of η-layers.

This **corrects `docs/handoff-krule.md` §T6**, which prices `EtaKDiamond` as *not* implied by
`KDiamond` on the grounds that "the two contracta live at different arities".  They do not:
the arity is `p₁.depth + 1 - e.appDepth`, and `Params.pat_app_depth_uniq` pins `p₁.depth` from
`e`'s head constant alone. -/
theorem EtaKn.height_uniq {k₁ k₂ : Nat} {Γ : List VExpr} {e e₁ e₂ : VExpr}
    (H1 : EtaKn k₁ Γ e e₁) (H2 : EtaKn k₂ Γ e e₂) : k₁ = k₂ := by
  obtain ⟨p₁, p₂, r, hp, hh, hd⟩ := H1.height_eq
  obtain ⟨q₁, q₂, r', hq, hh', hd'⟩ := H2.height_eq
  have : p₁.headName = q₁.headName := by
    rw [hh] at hh'; exact Option.some.inj hh'
  have := Params.pat_app_depth_uniq hp hq this
  omega

/-- The same statement for `EtaK` itself: any two steps at one term are towers of equal
height. -/
theorem EtaK.same_height {Γ : List VExpr} {e e₁ e₂ : VExpr}
    (H1 : EtaK Γ e e₁) (H2 : EtaK Γ e e₂) : ∃ k, EtaKn k Γ e e₁ ∧ EtaKn k Γ e e₂ := by
  obtain ⟨k₁, h1⟩ := H1.count
  obtain ⟨k₂, h2⟩ := H2.count
  cases EtaKn.height_uniq h1 h2
  exact ⟨_, h1, h2⟩

/-! ## The measure, in the form a recursion consumes

`CParRed.exists` recurses from `e` into `.app e.lift (.bvar 0)`, which is structurally
*larger*.  The two lemmas below are what a well-founded recursion needs in its place: the
η-expansion's `appDepth` is one greater, and the remaining tower is one shorter, so the pair
`(fuel, sizeOf)` decreases lexicographically with `fuel := p₁.depth + 1 - appDepth`. -/

/-- The measure of a term at which an `EtaK` step fires, read off the registered pattern. -/
theorem EtaKn.fuel_eq {k : Nat} {Γ : List VExpr} {e e' : VExpr}
    {p₁ p₂ : Pattern} {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    (H : EtaKn k Γ e e') (hp : Params.Pat (Pattern.app p₁ p₂) r)
    (hh : e.headConst? = some p₁.headName) : k = p₁.depth + 1 - e.appDepth := by
  obtain ⟨q₁, q₂, r', hq, hh', hd⟩ := H.height_eq
  have : q₁.headName = p₁.headName := by rw [hh'] at hh; exact Option.some.inj hh
  have := Params.pat_app_depth_uniq hq hp this
  omega

/-- **The recursion's step, and why it terminates.**  An `under` layer moves the recursion to
`.app e.lift (.bvar 0)`, whose `appDepth` is one greater and whose fuel is therefore one
smaller; `here` is the base, at fuel `0`. -/
theorem EtaKn.under_fuel {k : Nat} {Γ : List VExpr} {e A B t : VExpr}
    (hty : Γ ⊢ e : .forallE A B) (H : EtaKn k (A::Γ) (.app e.lift (.bvar 0)) t) :
    (VExpr.app e.lift (.bvar 0)).appDepth = e.appDepth + 1 ∧
      EtaKn (k+1) Γ e (.lam A t) ∧ k < k + 1 :=
  ⟨VExpr.appDepth_etaExpand e, .under hty H, Nat.lt_succ_self _⟩

/-! ## Non-vacuity

Split deliberately in two, because the two halves have different evidence.

**The arithmetic core fires at a real witness.**  `measure_witness` below exhibits a
depth-3 ι-shaped pattern and a term it matches, and reads the measure off both: `appDepth`,
`depth` and `headName` all agree, at a pattern with two `.var` layers on the function side and
one on the constructor side.  Nothing about it is degenerate, and it needs no `Params`.

**The `Params`-gated half has no witness in this tree, and that is not evidence of truth.**
`EtaKn.height_eq`, `height_uniq` and `fuel_eq` all consume `Params.Pat` at an `.app` pattern,
and **no `Params` instance in this tree registers one** -- `refParams` registers none, and
`paramsOfWF`'s `PatWF` is open in its ι and quotient cases (`docs/handoff-params.md` §1.1).
So the measure is checked against the rule *table*'s laws (`pat_simple`, `pat_app_l_uniq`) and
not against any instance.  Same standing caveat as `KStep.stuck_fires` and both kills. -/

/-- The measure at a concrete, non-degenerate ι-shaped pattern: `rec a b (ctor c)`. -/
theorem measure_witness (rec ctor : Lean.Name) (ls ls' : List VLevel) (a b c : VExpr) :
    let p := (SimplePattern.iota rec 2 ctor 1).toPattern
    let e := VExpr.app (.app (.app (.const rec ls) a) b) (.app (.const ctor ls') c)
    (∃ m1 m2, p.Matches e m1 m2) ∧ p.depth = 3 ∧ e.appDepth = 3 ∧
      p.headName = rec ∧ e.headConst? = some rec := by
  refine ⟨⟨_, _, .app (.var (.var .const)) (.var .const)⟩, rfl, rfl, rfl, rfl⟩

/-! ## What the height fact does to `EtaKDiamond`

`Theory/Typing/KEta.lean` states `EtaKDiamond` and prices it as **not** implied by `KDiamond`,
"because the two contracta live at different arities".  The height fact says they do not, so
the residual is strictly smaller than that: it is the *equal-height* diamond below, which is
a λ-congruence induction whose base (`k = 0`) is `KDiamond`-shaped.

This is a reduction, not a proof.  It passes the collapse test -- `EtaKDiamondAt` is
*strictly weaker* than `EtaKDiamond` as a `Prop` (it quantifies over one height, not two), so
`etaKDiamond_of_at` is not a tautology; what supplies the missing generality is
`EtaK.same_height`, and nothing else. -/

/-- `EtaKDiamond` restricted to two derivations of the **same** η-tower height. -/
def EtaKDiamondAt : Prop :=
  ∀ {k : Nat} {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
    EtaKn k Γ e e₁ → EtaKn k Γ e e₂ →
    ∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ NormalEq Γ e₃ e₄

/-- **The equal-height diamond suffices.**  `docs/handoff-krule.md` §T6's stated obstruction
to `EtaKDiamond` -- differing arities -- does not arise. -/
theorem etaKDiamond_of_at (h : EtaKDiamondAt) : EtaKDiamond := by
  intro Γ e e₁ e₂ hΓ H1 H2
  obtain ⟨k, h1, h2⟩ := EtaK.same_height H1 H2
  exact h hΓ h1 h2

/-! ## The lifting inversion: the η-tower is free, the `here` layer is the whole price

`KEta.lean`'s `not_weakNInvStatement_of_etaK` shows `ParRed.weakN_inv`'s **equality**
conclusion is false in the `keta` case, and that the obstruction is `EtaK.under`'s λ-domain
-- which is constrained only up to conversion -- rather than `KStep`'s major premise.  M3
therefore does not repair it, and the conclusion has to weaken to `NormalEq`
(`KEta.EtaKLiftInvC`), where `NormalEq.lamDF`'s defeq-domain slack absorbs it
(`kdom_normalEq_lam`).

What is proved here is that the weakened statement costs **nothing** beyond the base layer:
the whole η-tower is discharged from `KStepLiftInv` and `PiTypeDescend`.  The induction is
on the *height* rather than on the derivation, because the `under` step has to relocate its
sub-derivation onto a definitionally equal domain before the induction hypothesis applies,
and an induction on the derivation itself is pinned to the original context. -/

/-- `EtaK.defeqDFC` with the height preserved. -/
theorem EtaKn.defeqDFC {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (IsType env univs))
    {m : Nat} {Γ₁ Γ₂ : List VExpr} {e e' : VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : EtaKn m Γ₁ e e') : EtaKn m Γ₂ e e' := by
  induction H generalizing Γ₂ with
  | here hst => exact .here (KStep.defeqDFC W hst)
  | @under Γ₁ e A B t _ hty _ ih =>
    have ⟨⟨_, hA⟩, _⟩ := (hty.isType henv (W.isType' hΓ₀)).forallE_inv henv
    exact .under (hty.defeqDFC henv W) (ih (W.succ hA))

/-- **The η-tower of the lifting inversion, discharged.**  Every `under` layer is paid for by
`PiTypeDescend` (the downstairs Π-typing), `IsDefEqU.forallE_inv` on unique typing (the
upstairs domain is definitionally equal to the lift of the downstairs one), `EtaKn.defeqDFC`
(relocating the sub-derivation onto that lift) and then, on the way back,
`NormalEq.lamDF` for a genuine step and `NormalEq.etaL` for `KTable.canon`'s proof escape.

So `KStepLiftInv` is the *entire* open content of `ParRed.weakN_inv`'s `keta` case, and the
domain obstruction is not part of it. -/
theorem etaKn_liftN_inv (HK : KStepLiftInv) (HP : PiTypeDescend) {n : Nat} :
    ∀ {m k : Nat} {Γ Γ' : List VExpr} {e1 w A : VExpr},
      EtaKn m Γ' (e1.liftN n k) w → Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (IsType env univs) → OnCtx Γ' (IsType env univs) →
      Γ' ⊢ e1.liftN n k : A → EtaKLiftInvC Γ Γ' n k e1 w := by
  intro m
  induction m with
  | zero =>
    intro k Γ Γ' e1 w A H W hΓ hΓ' hX
    cases H with | here hst => exact HK hΓ' W hX hst
  | succ m ih =>
    intro k Γ Γ' e1 w A H W hΓ hΓ' hX
    cases H with
    | @under _ _ A₁ B₁ t _ hty hin =>
    obtain ⟨A₀, B₀, hf₀⟩ := HP hΓ hΓ' W hty
    have ⟨⟨u₀, hA₀⟩, v₀, hB₀⟩ := (have ⟨_, h⟩ := hf₀.isType henv hΓ; h.forallE_inv henv)
    have hf₀' : Γ' ⊢ e1.liftN n k : .forallE (A₀.liftN n k) (B₀.liftN n (k+1)) :=
      hf₀.weakN henv W
    obtain ⟨⟨u, hAA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ' (hty.uniqU henv hΓ' hf₀')
    have hΓA : OnCtx (A₀::Γ) (IsType env univs) := ⟨hΓ, _, hA₀⟩
    have hΓA' : OnCtx (A₀.liftN n k :: Γ') (IsType env univs) :=
      ⟨hΓ', _, hAA.hasType.2⟩
    have heq : (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        = VExpr.app ((e1.liftN n k).lift) (.bvar 0) := by
      simp [VExpr.liftN, Lean4Lean.liftVar, ← VExpr.lift_liftN']
    have hin' : EtaKn m (A₀.liftN n k :: Γ')
        ((VExpr.app e1.lift (.bvar 0)).liftN n (k+1)) t := by
      rw [heq]; exact hin.defeqDFC hΓ' (.succ .zero hAA)
    have hbty : (A₀.liftN n k :: Γ') ⊢ (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        : B₀.liftN n (k+1) := by
      rw [heq]
      have := HasType.app (hf₀'.weak (B := A₀.liftN n k) henv) (.bvar .zero)
      simpa [VExpr.liftN, instN_bvar0] using this
    obtain ⟨t₀, hd, hne⟩ := ih hin' W.succ hΓA hΓA' hbty
    cases hd with
    | inl hek =>
      refine ⟨.lam A₀ t₀, .inl (.under hf₀ hek), ?_⟩
      exact .lamDF hAA.symm hAA.hasType.2 hne
    | inr eq =>
      subst eq
      exact ⟨e1, .inr rfl, .etaL hty (heq ▸ NormalEq.defeq_l hΓ' hAA.symm hne)⟩

/-- The `EtaK` form, by `EtaK.count`. -/
theorem etaK_liftN_inv (HK : KStepLiftInv) (HP : PiTypeDescend)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 w A : VExpr}
    (H : EtaK Γ' (e1.liftN n k) w) (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (hX : Γ' ⊢ e1.liftN n k : A) : EtaKLiftInvC Γ Γ' n k e1 w :=
  let ⟨_, H⟩ := H.count; etaKn_liftN_inv HK HP H W hΓ hΓ' hX


/-! ### What is left of site 1, exactly

The `keta` case composes an `EtaK` step with a *development of its contractum*
(`ParRedK.keta`).  The lifting inversion handles the step; the tail is the residual, and it
is not routine: the contractum upstairs is only `NormalEq` to a lift, never equal to one, so
the tail's own inversion has to work modulo `NormalEq`.  That statement is
`NormalEq.parRed`-shaped -- **sites 1 and 7 of `docs/handoff-krule.md` §V3 are entangled**,
and no strengthening of the rule table separates them. -/

/-- The residual left by the `keta` case's tail: a development of a term that is `NormalEq`
to a lift is `NormalEq` to the lift of a development.  Instantiating `NormalEq` at `Eq` makes
this `ParRed.weakN_inv`'s own conclusion, so it is a genuine weakening and not a restatement;
what it adds over `weakN_inv` is exactly `NormalEq.parRed`'s commutation.

**It is not a K-hypothesis**: it is non-vacuous already where `KStep` is empty, so the
`refParams` consistency check that every other statement in this corner carries is *not*
available for it, and none is claimed.

**Correction (round 8, audit).**  Two things above are wrong.

1. It is not a *residual*: `weakNInvStatementP_of_tail` derives the whole of site 1 from it
   at `NormalEq.refl`, so `docs/handoff-krule.md` §W4's "site 1 reduces to three named facts"
   fails `ORCHESTRATOR.md`'s collapse test.  Use `KEta.KStepTail` (or `KStepTailS`) and
   `parRedK_weakN_invP` / `parRedK_weakN_invPS` instead.
2. The check *is* available and it was simply not run: `refParams_weakNInvTailS` proves the
   `≫*` form wherever `EtaK` is empty.  The single-step form written here is **not** what
   that route delivers, and no proof of it is known -- see the section on `WeakNInvTailS`. -/
def WeakNInvTail : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {u u' v : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    ParRedK Γ' u u' → NormalEq Γ' u (v.liftN n k) →
    ∃ v', ParRedK Γ v v' ∧ NormalEq Γ' u' (v'.liftN n k)

/-- **Site 1's `keta` case, in the `≡ₚ` form, from three named facts and nothing else.**
`KStepLiftInv` is M3's share (`KTable.kstep_liftN_inv_step`), `PiTypeDescend` is the typing
descent, and `WeakNInvTail` is the tail.  The λ-domain obstruction that refutes the equality
form (`not_weakNInvStatement_of_etaK`) has disappeared: it is absorbed by `NormalEq.lamDF`
inside `etaKn_liftN_inv`.

**Superseded (round 8).**  `HT` alone implies the conclusion (`weakNInvStatementP_of_tail`),
so this is not a reduction.  `keta_weakN_invK` / `keta_weakN_invKS` prove the same thing from
`KStepTail` / `KStepTailS`, which are guarded by two `KStep`s. -/
theorem keta_weakN_inv (HK : KStepLiftInv) (HP : PiTypeDescend) (HT : WeakNInvTail)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (hty : Γ' ⊢ e1.liftN n k : A)
    (hek : EtaK Γ' (e1.liftN n k) w) (htail : ParRedK Γ' w w') :
    ∃ e2, ParRedK Γ e1 e2 ∧ NormalEq Γ' w' (e2.liftN n k) := by
  obtain ⟨w₀, hd, hne⟩ := etaK_liftN_inv HK HP hek W hΓ hΓ' hty
  obtain ⟨v', hpr, hne'⟩ := HT hΓ' W htail hne
  refine ⟨v', ?_, hne'⟩
  cases hd with
  | inl hek₀ => exact .keta hek₀ hpr
  | inr eq => exact eq ▸ hpr


/-! ## Audit of `WeakNInvTail`, and the descent that replaces it

`docs/handoff-krule.md` §W4 presents `keta_weakN_inv` as reducing site 1's `keta` case to
three named facts -- `KStepLiftInv`, `PiTypeDescend`, `WeakNInvTail` -- and concludes from the
third that §V3's sites 1 and 7 are one problem.  The audit the brief asked for finds two
things, both machine-checked here.

**1. The reduction fails the collapse test** (`ORCHESTRATOR.md` working rule 5).
`WeakNInvTail` instantiated at `NormalEq.refl` *is* site 1's whole statement, so
`weakNInvStatementP_of_tail` below derives the target from the residual alone, with neither
`KStepLiftInv` nor `PiTypeDescend` in the cone.  A reduction whose residual implies the target
carries no information about the target's price.

**2. The entanglement is an artefact of the order of the two moves.**  §W4 inverts the whole
η-tower first (`etaK_liftN_inv`) and applies the development afterwards, at which point the
development meets a bare `NormalEq` and needs `NormalEq.parRed`'s commutation in full.
Carrying the development *down* the tower instead leaves a residual guarded by **two**
K-steps.  Two facts make the descent go through, neither of them about `NormalEq`:

* `EtaK.not_lam` forces the development at every `under` layer to be a λ-congruence
  (`ParRedK.lam_inv`), so there is nothing to commute there;
* `KTable.canon`'s escape is a **proof** escape, and "both sides inhabit one `Prop`"
  (`ProofEq`) is stable under a development of either side -- which a bare `NormalEq` is not.
  Keeping the escape open (`KTable.kstep_liftN_inv_stepP`) is the whole of the difference.

The residual is `KEta.KStepTail`, and it is vacuous wherever `KStep` is empty
(`refParams_kStepTail`), so it carries the `refParams` consistency check `WeakNInvTail` could
not, and it is a rule-table obligation rather than a Church-Rosser one.  **This corrects §W0.5
and §W4: no joint induction with site 7 is needed for site 1.** -/

/-- `ParRed.weakN_inv`'s statement for `ParRedK`, at the `≡ₚ` conclusion the λ-domain
obstruction forces (`KEta.not_weakNInvStatement_of_etaK`).  This is `docs/handoff-krule.md`
§V3's site 1. -/
def WeakNInvStatementP : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    Γ' ⊢ e1.liftN n k : A → ParRedK Γ' (e1.liftN n k) e2' →
    ∃ e2, ParRedK Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k)

/-- **The collapse test on §W4's reduction, failed.**  `WeakNInvTail` alone implies site 1 --
take `u := e1.liftN n k`, `v := e1` and the `NormalEq` at `refl`.  So §W4's "site 1 reduces to
three named facts" is not a reduction: `KStepLiftInv` and `PiTypeDescend` do no work in it,
and "`WeakNInvTail` is `NormalEq.parRed`-shaped, so sites 1 and 7 are one problem" is an
observation about a statement that was never weaker than the goal. -/
theorem weakNInvStatementP_of_tail (HT : WeakNInvTail) : WeakNInvStatementP :=
  fun hΓ' W hty H => HT hΓ' W H (.refl hty)

/-- The invariant the descent carries down the η-tower: either a genuine `EtaK` step
downstairs *together with* a development of its contractum -- the two premises `ParRedK.keta`
wants -- or the proof escape.  The split is what makes the `under` layer reconstructible:
`ParRedK Γ e1 e2` alone cannot be re-wrapped in a λ, because `EtaK.under` needs an `EtaK`
sub-derivation and not a `ParRedK` one. -/
def KetaLiftInvS (Γ Γ' : List VExpr) (n k : Nat) (e1 w' : VExpr) : Prop :=
  (∃ w₀ e2, EtaK Γ e1 w₀ ∧ ParRedK Γ w₀ e2 ∧ NormalEq Γ' w' (e2.liftN n k)) ∨
  ProofEq Γ' w' (e1.liftN n k)

/-- **Site 1's `keta` case, with the development carried down the η-tower.**

Compare `etaKn_liftN_inv`, which inverts the tower and hands the development a bare
`NormalEq`.  Here the development descends with the inversion, and the two `under`-layer
obligations are discharged outright: `ParRedK.lam_inv` (the development of a λ is a λ
congruence, since `EtaK.not_lam` kills the `keta` case) and `ProofEq.forallE` (the escape's
`Prop` survives a binder, by impredicativity).  What is left is the `here` layer, and there
the residual is `KStepTail` -- guarded by the upstairs K-step *and* the downstairs one. -/
theorem etaKn_keta_liftN_inv (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail)
    {n : Nat} :
    ∀ {m k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr},
      EtaKn m Γ' (e1.liftN n k) w → ParRedK Γ' w w' → Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (IsType env univs) → OnCtx Γ' (IsType env univs) →
      Γ' ⊢ e1.liftN n k : A → KetaLiftInvS Γ Γ' n k e1 w' := by
  intro m
  induction m with
  | zero =>
    intro k Γ Γ' e1 w w' A H hpr W hΓ hΓ' hX
    cases H with | here hst => ?_
    rcases HK hΓ hΓ' W hX hst with ⟨w₀, hks, hne⟩ | hpe
    · obtain ⟨v', hv, hne'⟩ := HT hΓ hΓ' W hst hks hne hpr
      exact .inl ⟨w₀, v', .here hks, hv, hne'⟩
    · exact .inr (hpe.parRedK_l hΓ' hpr)
  | succ m ih =>
    intro k Γ Γ' e1 w w' A H hpr W hΓ hΓ' hX
    cases H with
    | @under _ _ A₁ B₁ t _ hty hin => ?_
    obtain ⟨A₁', t', rfl, hAr, htr⟩ := hpr.lam_inv
    obtain ⟨A₀, B₀, hf₀⟩ := HP hΓ hΓ' W hty
    have ⟨⟨u₀, hA₀⟩, v₀, hB₀⟩ := (have ⟨_, h⟩ := hf₀.isType henv hΓ; h.forallE_inv henv)
    have hf₀' : Γ' ⊢ e1.liftN n k : .forallE (A₀.liftN n k) (B₀.liftN n (k+1)) :=
      hf₀.weakN henv W
    obtain ⟨⟨u, hAA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ' (hty.uniqU henv hΓ' hf₀')
    have ⟨⟨_, hA₁⟩, _, hB₁⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ'; h.forallE_inv henv)
    have hΓA : OnCtx (A₀::Γ) (IsType env univs) := ⟨hΓ, _, hA₀⟩
    have hΓA₁ : OnCtx (A₁::Γ') (IsType env univs) := ⟨hΓ', _, hA₁⟩
    have hΓA' : OnCtx (A₀.liftN n k :: Γ') (IsType env univs) := ⟨hΓ', _, hAA.hasType.2⟩
    have heq : (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        = VExpr.app ((e1.liftN n k).lift) (.bvar 0) := by
      simp [VExpr.liftN, Lean4Lean.liftVar, ← VExpr.lift_liftN']
    have hb1 : (A₁::Γ') ⊢ VExpr.app ((e1.liftN n k).lift) (.bvar 0) : B₁ := by
      simpa [instN_bvar0] using HasType.app (hty.weak (B := A₁) henv) (.bvar .zero)
    have htty : (A₁::Γ') ⊢ t : B₁ :=
      ((hin.toEtaK.defeqU hΓA₁).of_l henv hΓA₁ hb1).hasType.2
    have hbty : (A₀.liftN n k :: Γ') ⊢ (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        : B₀.liftN n (k+1) := by
      rw [heq]
      have := HasType.app (hf₀'.weak (B := A₀.liftN n k) henv) (.bvar .zero)
      simpa [VExpr.liftN, instN_bvar0] using this
    have hin' : EtaKn m (A₀.liftN n k :: Γ')
        ((VExpr.app e1.lift (.bvar 0)).liftN n (k+1)) t := by
      rw [heq]; exact hin.defeqDFC hΓ' (.succ .zero hAA)
    have htr' : ParRedK (A₀.liftN n k :: Γ') t t' :=
      htr.defeqDFC hΓ' (.succ .zero hAA) htty
    have hAA1 := hAA.symm.trans (hAr.defeq hΓ' hAA.hasType.1)
    rcases ih hin' htr' W.succ hΓA hΓA' hbty with ⟨z₀, z, hek₀, hz, hne⟩ | hpe
    · refine .inl ⟨.lam A₀ z₀, .lam A₀ z, .under hf₀ hek₀, .lam ParRedK.rfl hz, ?_⟩
      simpa [VExpr.liftN] using
        NormalEq.lamDF (A := A₀.liftN n k) hAA1 hAA.hasType.2 hne
    · rw [heq] at hpe
      exact .inr (ProofEq.forallE hΓ' hAA.hasType.2 hAA1 hf₀' hpe)

/-- The `EtaK` form. -/
theorem etaK_keta_liftN_inv (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr}
    (H : EtaK Γ' (e1.liftN n k) w) (hpr : ParRedK Γ' w w') (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (hX : Γ' ⊢ e1.liftN n k : A) : KetaLiftInvS Γ Γ' n k e1 w' :=
  let ⟨_, H⟩ := H.count; etaKn_keta_liftN_inv HK HP HT H hpr W hΓ hΓ' hX

/-- **Site 1's `keta` case, from `KStepLiftInvP`, `PiTypeDescend` and `KStepTail`.**

The improvement over `keta_weakN_inv` is not the count -- three hypotheses either way -- but
that all three are now *smaller than the target*: `KStepTail` is guarded by two `KStep`s,
where `WeakNInvTail` implied the target outright (`weakNInvStatementP_of_tail`). -/
theorem keta_weakN_invK (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (hty : Γ' ⊢ e1.liftN n k : A)
    (hek : EtaK Γ' (e1.liftN n k) w) (htail : ParRedK Γ' w w') :
    ∃ e2, ParRedK Γ e1 e2 ∧ NormalEq Γ' w' (e2.liftN n k) := by
  rcases etaK_keta_liftN_inv HK HP HT hek htail W hΓ hΓ' hty with ⟨w₀, e2, h1, h2, h3⟩ | hpe
  · exact ⟨e2, .keta h1 h2, h3⟩
  · exact ⟨e1, .rfl, hpe.normalEq⟩



/-! ### The other half of the audit: the single-step conclusion, and the missing check

§W4 records that `WeakNInvTail` "is non-vacuous already where `KStep` is empty, so the
`refParams` consistency check every other statement in this corner carries is unavailable for
it, and none is claimed".  The check *is* available -- it is just not vacuous -- and it
passes, **for the multi-step conclusion only**:

* `refParams_weakNInvTailS` **[machine-checked]** proves the `≫*` form wherever `EtaK` is
  empty, out of `NormalEq.parRed` (site 7, already proved for `ParRed`), `ParRedS.weakN_inv`
  and `NormalEq.symm`.
* The **single-step** form as written in `WeakNInvTail` does not follow by that route and no
  other was found: `NormalEq.parRed`'s own conclusion is `≫*`, and `ParRed.weakN_inv` turns a
  reduction *sequence* into a reduction sequence.  So the one place where `WeakNInvTail` could
  be tested against a real instance tests a statement one step weaker than it.

Both consumers of the conclusion tolerate `≫*` (`ChurchRosser.lean:2098`, `:2107`, both
`ReflTransGen.tail`, which becomes `.trans`), so nothing is lost by weakening -- but the
weakening was not stated, and the check was reported as unavailable rather than as untried. -/

theorem ParRedS.toK {Γ : List VExpr} {e e' : VExpr} (H : ParRedS Γ e e') : ParRedKS Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail h.toK

/-- `ParRed.weakN_inv` iterated along a reduction sequence.  Not in `ChurchRosser.lean`; the
multi-step form is what `NormalEq.parRed`'s conclusion actually hands you. -/
theorem ParRedS.weakN_inv {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr}
    (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (h : Γ' ⊢ e1.liftN n k : A)
    (H : ParRedS Γ' (e1.liftN n k) e2') : ∃ e2, ParRedS Γ e1 e2 ∧ e2' = e2.liftN n k := by
  induction H with
  | rfl => exact ⟨e1, .rfl, rfl⟩
  | @tail b c _ hstep ih =>
    obtain ⟨e2, h1, rfl⟩ := ih
    obtain ⟨e3, h2, rfl⟩ :=
      ParRed.weakN_inv hΓ' W (ParRedS.hasType hΓ' (h1.weakN W) h) hstep
    exact ⟨e3, h1.tail h2, rfl⟩

/-- `WeakNInvTail` with the conclusion at `≫*`.  This is the form the only available route
produces, and the form both consumers of `ParRed.weakN_inv` tolerate. -/
def WeakNInvTailS : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {u u' v : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    ParRedK Γ' u u' → NormalEq Γ' u (v.liftN n k) →
    ∃ v', ParRedKS Γ v v' ∧ NormalEq Γ' u' (v'.liftN n k)

/-- **The consistency check §W4 reported as unavailable, run.**  Where `EtaK` is empty the
multi-step tail is a theorem: `NormalEq.parRed` moves the development across the `≡ₚ`, and
`ParRedS.weakN_inv` descends the resulting sequence.  Note the shape of the proof -- it is
exactly the circle §W4 describes (site 7 then site 1), which is why it says nothing about the
K case; what it *does* say is that the statement is not false, and that the single-step form
it was written with is not what this route delivers. -/
theorem weakNInvTailS_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : WeakNInvTailS := by
  intro n k Γ Γ' u u' v hΓ' W hpr hne
  have ⟨_, hd⟩ := hne.defeq hΓ'
  obtain ⟨x, hx, hxu⟩ := (hne.symm hΓ').parRed hΓ' (ParRedK.toParRed hno hpr)
  obtain ⟨v', hv', rfl⟩ := ParRedS.weakN_inv hΓ' W hd.hasType.2 hx
  exact ⟨v', hv'.toK, hxu.symm hΓ'⟩

theorem refParams_weakNInvTailS : @WeakNInvTailS refParams :=
  @weakNInvTailS_of_no_etaK refParams (fun h => refParams_no_etaK h)

/-- The multi-step tail collapses in exactly the same way as the single-step one: at
`NormalEq.refl` it is site 1 with a `≫*` conclusion.  Recorded so the collapse is not
mistaken for an artefact of the single-step conclusion. -/
theorem weakNInvStatementS_of_tailS (HT : WeakNInvTailS)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr}
    (hΓ' : OnCtx Γ' (IsType env univs)) (W : Ctx.LiftN n k Γ Γ')
    (hty : Γ' ⊢ e1.liftN n k : A) (H : ParRedK Γ' (e1.liftN n k) e2') :
    ∃ e2, ParRedKS Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k) :=
  HT hΓ' W H (.refl hty)



/-! ### Site 1, assembled

With the `keta` case discharged by `keta_weakN_invK`, the other eight cases of `ParRedK` are
`ParRed.weakN_inv`'s own, re-proved at the `≡ₚ` conclusion.  Only three of them cost anything
beyond bookkeeping, and none of them is `NormalEq.parRed`-shaped:

* `lam`/`forallE`: the two domains are no longer equal, only `≡ₚ`, so the reconstruction goes
  through `NormalEq.lamDF`/`forallEDF` at the *middle* domain `A.liftN n k` -- exactly the
  slack `kdom_normalEq_lam` identified.
* `beta`: the substitution has to be congruent on both arguments, which is
  `NormalEq.instN` composed with `NormalEq.instN_r`.
* `extra`: the match still descends on the nose (`Pattern.matches_liftN`), so the rule's
  `Check` obligations descend by `IsDefEqU.weakN_iff` as before; only the *contractum* is
  `≡ₚ` rather than equal, and `NormalEq.apply_pat` closes it. -/

/-- **Site 1, closed, from `KStepLiftInvP`, `PiTypeDescend` and `KStepTail`.**

This is `ParRed.weakN_inv` for the enlarged relation, at the `≡ₚ` conclusion that
`not_weakNInvStatement_of_etaK` forces.  Of the three hypotheses, `KStepTail` is guarded by two
`KStep`s and `KStepLiftInvP` by one, so both are vacuous wherever `KStep` is empty
(`refParams_kStepTail`, `refParams_kStepLiftInvP`); `PiTypeDescend` is a typing descent, not a
K statement, and is `Strengthen.lean`'s neighbourhood.

**No hypothesis of this theorem is `NormalEq.parRed`-shaped**, which corrects
`docs/handoff-krule.md` §W0.5: sites 1 and 7 are *not* one problem. -/
theorem parRedK_weakN_invP (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail)
    {n : Nat} :
    ∀ {Γ' : List VExpr} {e1' e2' : VExpr}, ParRedK Γ' e1' e2' →
      ∀ {k : Nat} {Γ : List VExpr} {e1 A : VExpr},
        OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
        Γ' ⊢ e1.liftN n k : A → e1.liftN n k = e1' →
        ∃ e2, ParRedK Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k) := by
  intro Γ'₀ e1' e2' H
  induction H with
  | bvar => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .bvar, .refl h⟩
  | sort => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .sort, .refl h⟩
  | const => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .const, .refl h⟩
  | @app Γ' f f' a a' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ'
    obtain ⟨g', hg, hgn⟩ := ih1 hΓ' W hf rfl
    obtain ⟨b', hb, hbn⟩ := ih2 hΓ' W ha rfl
    refine ⟨.app g' b', .app hg hb, ?_⟩
    simpa [VExpr.liftN] using NormalEq.appDF (hp1.hasType hΓ' hf)
      ((hg.weakN W).hasType hΓ' hf) (hp2.hasType hΓ' ha)
      ((hb.weakN W).hasType hΓ' ha) hgn hbn
  | @lam Γ' A₁ A₁' body body' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨⟨_, hD⟩, _, hb⟩ := h.lam_inv henv hΓ'
    obtain ⟨D', hD1, hDn⟩ := ih1 hΓ' W hD rfl
    obtain ⟨t', ht1, htn⟩ := ih2 ⟨hΓ', _, hD⟩ W.succ hb rfl
    refine ⟨.lam D' t', .lam hD1 ht1, ?_⟩
    simpa [VExpr.liftN] using
      NormalEq.lamDF (hp1.defeq hΓ' hD) ((hD1.weakN W).defeq hΓ' hD) htn
  | @forallE Γ' A₁ A₁' B₁ B₁' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨⟨_, hD⟩, _, hB⟩ := h.forallE_inv henv
    obtain ⟨D', hD1, hDn⟩ := ih1 hΓ' W hD rfl
    obtain ⟨t', ht1, htn⟩ := ih2 ⟨hΓ', _, hD⟩ W.succ hB rfl
    refine ⟨.forallE D' t', .forallE hD1 ht1, ?_⟩
    simpa [VExpr.liftN] using
      NormalEq.forallEDF (hp1.defeq hΓ' hD) hDn
        (hp2.hasType (by exact ⟨hΓ', _, hD⟩) hB) htn
  | @beta Γ' A₁ e₁ e₁' e₂ e₂' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> injection eq
    rename_i f a eq eq2; cases eq2
    cases f <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ'
    have ⟨⟨_, hD⟩, _, hb⟩ := hf.lam_inv henv hΓ'
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ' (hf.uniqU henv hΓ' (hD.lam hb))
    replace ha := ha.defeqU_r henv hΓ' ⟨_, u1⟩
    obtain ⟨t', ht1, htn⟩ := ih1 (by exact ⟨hΓ', _, hD⟩) W.succ hb rfl
    obtain ⟨b', hb1, hbn⟩ := ih2 hΓ' W ha rfl
    refine ⟨t'.inst b', .beta ht1 hb1, ?_⟩
    rw [liftN_inst_hi]
    -- `NormalEq.instN₂` in place of `instN` + `instN_r` + `trans`: one substitution step that
    -- moves *both* sides at once, so the `NormalEq.trans` (hence `IsDefEqU.weakN_iff`) entry
    -- this composition used to carry is gone from here.  Measured: it does not clear
    -- `weakN_iff` from `parRedK_weakN_invP`, whose `extra` case calls it directly.
    exact NormalEq.instN₂ (hp2.hasType hΓ' ha) hbn htn (by exact ⟨hΓ', _, hD⟩) .zero
  | @extra Γ' p r e0 m1 m2 m2' hpat hm hck hstep ih =>
    intro k Γ e1 A hΓ' W h eq
    subst eq
    obtain ⟨m3, hm3, hn⟩ := Pattern.matches_liftN.1 hm
    have hmeq : m2 = fun x => (m3 x).liftN n k := funext hn
    have key : ∀ a, ∃ z, ParRedK Γ (m3 a) z ∧ NormalEq Γ' (m2' a) (z.liftN n k) := by
      intro a
      have ⟨_, hT⟩ := hm.hasType hΓ' h a
      exact ih a hΓ' W (by rw [← hn a]; exact hT) (hn a).symm
    have hck₀ : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m3 r.2 := by
      refine hck.map fun _ _ hab => ?_
      rw [hmeq, ← Pattern.RHS.liftN_apply, ← Pattern.RHS.liftN_apply] at hab
      exact (IsDefEqU.weakN_iff henv hΓ' W).1 hab
    have hne : ∀ a, NormalEq Γ' (m2' a) (((key a).choose).liftN n k) :=
      fun a => (key a).choose_spec.2
    refine ⟨_, .extra hpat hm3 hck₀ (fun a => (key a).choose_spec.1), ?_⟩
    rw [Pattern.RHS.liftN_apply]
    exact NormalEq.apply_pat hΓ' (fun x _ _ => hne x)
      ((ParRedK.extra hpat hm hck hstep).hasType hΓ' h)
  | @keta Γ' e w w' hek htail _ =>
    intro k Γ e1 A hΓ' W h eq
    subst eq
    exact keta_weakN_invK HK HP HT (hΓ'.weakN_inv henv W) hΓ' W h hek htail



/-! ### The same, with the honest conclusion: `≫*`

The audit above found `WeakNInvTail`'s **single-step** conclusion unsupported: the only route
to it (`NormalEq.parRed` then `ParRed.weakN_inv`) delivers `≫*`, and `ParRedExt.parRed_beta`
shows the extra steps are real (`ChurchRosser.lean:1197`, `.tail (ParRedS.app ..) (.beta ..)`).
That criticism applies verbatim to `KStepTail`: its `u` is only `≡ₚ` to a lift, so a
development of `u` may need two downstairs steps to catch up.

`ParRedK.weakN_inv` itself has no such problem -- its hypothesis is a lift *on the nose* -- so
the single-step assembly above is a genuine theorem and is the sharper one.  What is repeated
here is the assembly at the weaker hypothesis `KStepTailS`, which is the obligation a future
round should actually try to discharge.  Both consumers of `weakN_inv` tolerate `≫*`
(`ChurchRosser.lean:2098`, `:2107`: `ReflTransGen.tail` becomes `.trans`). -/

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedKS.hasType {e e' A : VExpr} (H : ParRedKS Γ e e') : Γ ⊢ e : A → Γ ⊢ e' : A := by
  induction H with
  | rfl => exact id
  | tail _ h2 ih => exact h2.hasType hΓ ∘ ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedKS.defeq {e e' A : VExpr} (H : ParRedKS Γ e e') (h : Γ ⊢ e : A) :
    IsDefEq env univs Γ e e' A := by
  induction H with
  | rfl => exact h
  | tail h1 h2 ih => exact ih.trans (h2.defeq hΓ (ParRedKS.hasType hΓ h1 h))

theorem ParRedKS.weakN {Γ Γ' : List VExpr} {e e' : VExpr} {n k : Nat}
    (W : Ctx.LiftN n k Γ Γ') (H : ParRedKS Γ e e') :
    ParRedKS Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail (h.weakN W)

theorem ParRedKS.app {Γ : List VExpr} {f f' a a' : VExpr}
    (hf : ParRedKS Γ f f') (ha : ParRedKS Γ a a') : ParRedKS Γ (.app f a) (.app f' a') := by
  refine ReflTransGen.trans (?_ : ParRedKS Γ (.app f a) (.app f a')) ?_
  · induction ha with
    | rfl => exact .rfl
    | tail _ a2 iha => exact iha.tail (.app ParRedK.rfl a2)
  · induction hf with
    | rfl => exact .rfl
    | tail _ f2 ihf => exact ihf.tail (.app f2 ParRedK.rfl)

theorem ParRedKS.lam {Γ : List VExpr} {A A' body body' : VExpr}
    (hf : ParRedKS Γ A A') (ha : ParRedKS (A::Γ) body body') :
    ParRedKS Γ (.lam A body) (.lam A' body') := by
  refine ReflTransGen.trans (?_ : ParRedKS Γ (.lam A body) (.lam A body')) ?_
  · induction ha with
    | rfl => exact .rfl
    | tail _ a2 iha => exact iha.tail (.lam ParRedK.rfl a2)
  · induction hf with
    | rfl => exact .rfl
    | tail _ f2 ihf => exact ihf.tail (.lam f2 ParRedK.rfl)

theorem ParRedKS.forallE {Γ : List VExpr} {A A' B B' : VExpr}
    (hf : ParRedKS Γ A A') (ha : ParRedKS (A::Γ) B B') :
    ParRedKS Γ (.forallE A B) (.forallE A' B') := by
  refine ReflTransGen.trans (?_ : ParRedKS Γ (.forallE A B) (.forallE A B')) ?_
  · induction ha with
    | rfl => exact .rfl
    | tail _ a2 iha => exact iha.tail (.forallE ParRedK.rfl a2)
  · induction hf with
    | rfl => exact .rfl
    | tail _ f2 ihf => exact ihf.tail (.forallE f2 ParRedK.rfl)

/-- A rule's right-hand side is a congruence for `≫*`: the spine is `fixed`/`app`/`var`, and
only the `var` leaves move. -/
theorem Pattern.RHS.apply_parRedKS {Γ : List VExpr} {p : Pattern}
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (h : ∀ a, ParRedKS Γ (m2 a) (m2' a)) : ∀ r : p.RHS,
      ParRedKS Γ (Pattern.RHS.apply m1 m2 r) (Pattern.RHS.apply m1 m2' r)
  | .fixed _ _ _ => .rfl
  | .app f a => ParRedKS.app (apply_parRedKS h f) (apply_parRedKS h a)
  | .var path => h path

/-- `KStepTail` with the conclusion at `≫*`. -/
def KStepTailS : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 u u' v : VExpr},
    OnCtx Γ (IsType env univs) → OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    KStep Γ' (e1.liftN n k) u → KStep Γ e1 v →
    NormalEq Γ' u (v.liftN n k) → ParRedK Γ' u u' →
    ∃ v', ParRedKS Γ v v' ∧ NormalEq Γ' u' (v'.liftN n k)

theorem KStepTail.toS (H : KStepTail) : KStepTailS :=
  fun hΓ hΓ' W h1 h2 h3 h4 => let ⟨v', hv, hn⟩ := H hΓ hΓ' W h1 h2 h3 h4
    ⟨v', .tail .rfl hv, hn⟩

theorem kStepTailS_of_no_kstep (hno : ∀ {Δ a b}, ¬ KStep Δ a b) : KStepTailS :=
  fun _ _ _ h => absurd h hno

theorem refParams_kStepTailS : @KStepTailS refParams :=
  @kStepTailS_of_no_kstep refParams (fun h => refParams_no_kstep h)

/-- `KetaLiftInvS` with the development at `≫*`. -/
def KetaLiftInvSS (Γ Γ' : List VExpr) (n k : Nat) (e1 w' : VExpr) : Prop :=
  (∃ w₀ e2, EtaK Γ e1 w₀ ∧ ParRedKS Γ w₀ e2 ∧ NormalEq Γ' w' (e2.liftN n k)) ∨
  ProofEq Γ' w' (e1.liftN n k)

theorem etaKn_keta_liftN_invS (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTailS)
    {n : Nat} :
    ∀ {m k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr},
      EtaKn m Γ' (e1.liftN n k) w → ParRedK Γ' w w' → Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (IsType env univs) → OnCtx Γ' (IsType env univs) →
      Γ' ⊢ e1.liftN n k : A → KetaLiftInvSS Γ Γ' n k e1 w' := by
  intro m
  induction m with
  | zero =>
    intro k Γ Γ' e1 w w' A H hpr W hΓ hΓ' hX
    cases H with | here hst => ?_
    rcases HK hΓ hΓ' W hX hst with ⟨w₀, hks, hne⟩ | hpe
    · obtain ⟨v', hv, hne'⟩ := HT hΓ hΓ' W hst hks hne hpr
      exact .inl ⟨w₀, v', .here hks, hv, hne'⟩
    · exact .inr (hpe.parRedK_l hΓ' hpr)
  | succ m ih =>
    intro k Γ Γ' e1 w w' A H hpr W hΓ hΓ' hX
    cases H with
    | @under _ _ A₁ B₁ t _ hty hin => ?_
    obtain ⟨A₁', t', rfl, hAr, htr⟩ := hpr.lam_inv
    obtain ⟨A₀, B₀, hf₀⟩ := HP hΓ hΓ' W hty
    have ⟨⟨u₀, hA₀⟩, v₀, hB₀⟩ := (have ⟨_, h⟩ := hf₀.isType henv hΓ; h.forallE_inv henv)
    have hf₀' : Γ' ⊢ e1.liftN n k : .forallE (A₀.liftN n k) (B₀.liftN n (k+1)) :=
      hf₀.weakN henv W
    obtain ⟨⟨u, hAA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ' (hty.uniqU henv hΓ' hf₀')
    have ⟨⟨_, hA₁⟩, _, hB₁⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ'; h.forallE_inv henv)
    have hΓA : OnCtx (A₀::Γ) (IsType env univs) := ⟨hΓ, _, hA₀⟩
    have hΓA₁ : OnCtx (A₁::Γ') (IsType env univs) := ⟨hΓ', _, hA₁⟩
    have hΓA' : OnCtx (A₀.liftN n k :: Γ') (IsType env univs) := ⟨hΓ', _, hAA.hasType.2⟩
    have heq : (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        = VExpr.app ((e1.liftN n k).lift) (.bvar 0) := by
      simp [VExpr.liftN, Lean4Lean.liftVar, ← VExpr.lift_liftN']
    have hb1 : (A₁::Γ') ⊢ VExpr.app ((e1.liftN n k).lift) (.bvar 0) : B₁ := by
      simpa [instN_bvar0] using HasType.app (hty.weak (B := A₁) henv) (.bvar .zero)
    have htty : (A₁::Γ') ⊢ t : B₁ :=
      ((hin.toEtaK.defeqU hΓA₁).of_l henv hΓA₁ hb1).hasType.2
    have hbty : (A₀.liftN n k :: Γ') ⊢ (VExpr.app e1.lift (.bvar 0)).liftN n (k+1)
        : B₀.liftN n (k+1) := by
      rw [heq]
      have := HasType.app (hf₀'.weak (B := A₀.liftN n k) henv) (.bvar .zero)
      simpa [VExpr.liftN, instN_bvar0] using this
    have hin' : EtaKn m (A₀.liftN n k :: Γ')
        ((VExpr.app e1.lift (.bvar 0)).liftN n (k+1)) t := by
      rw [heq]; exact hin.defeqDFC hΓ' (.succ .zero hAA)
    have htr' : ParRedK (A₀.liftN n k :: Γ') t t' :=
      htr.defeqDFC hΓ' (.succ .zero hAA) htty
    have hAA1 := hAA.symm.trans (hAr.defeq hΓ' hAA.hasType.1)
    rcases ih hin' htr' W.succ hΓA hΓA' hbty with ⟨z₀, z, hek₀, hz, hne⟩ | hpe
    · refine .inl ⟨.lam A₀ z₀, .lam A₀ z, .under hf₀ hek₀, ParRedKS.lam .rfl hz, ?_⟩
      simpa [VExpr.liftN] using
        NormalEq.lamDF (A := A₀.liftN n k) hAA1 hAA.hasType.2 hne
    · rw [heq] at hpe
      exact .inr (ProofEq.forallE hΓ' hAA.hasType.2 hAA1 hf₀' hpe)

theorem keta_weakN_invKS (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTailS)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 w w' A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (hty : Γ' ⊢ e1.liftN n k : A)
    (hek : EtaK Γ' (e1.liftN n k) w) (htail : ParRedK Γ' w w') :
    ∃ e2, ParRedKS Γ e1 e2 ∧ NormalEq Γ' w' (e2.liftN n k) := by
  have ⟨_, H⟩ := hek.count
  rcases etaKn_keta_liftN_invS HK HP HT H htail W hΓ hΓ' hty with
    ⟨w₀, e2, h1, h2, h3⟩ | hpe
  · exact ⟨e2, ReflTransGen.trans (.tail .rfl (.keta h1 ParRedK.rfl)) h2, h3⟩
  · exact ⟨e1, .rfl, hpe.normalEq⟩

/-- **Site 1, closed at the `≫*` conclusion**, from `KStepLiftInvP`, `PiTypeDescend` and
`KStepTailS`.  This is the version whose residual is not stronger than what any known route
supplies; see the section header. -/
theorem parRedK_weakN_invPS (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTailS)
    {n : Nat} :
    ∀ {Γ' : List VExpr} {e1' e2' : VExpr}, ParRedK Γ' e1' e2' →
      ∀ {k : Nat} {Γ : List VExpr} {e1 A : VExpr},
        OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
        Γ' ⊢ e1.liftN n k : A → e1.liftN n k = e1' →
        ∃ e2, ParRedKS Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k) := by
  intro Γ'₀ e1' e2' H
  induction H with
  | bvar => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .rfl, .refl h⟩
  | sort => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .rfl, .refl h⟩
  | const => intro k Γ e1 A hΓ' W h eq; cases e1 <;> cases eq; exact ⟨_, .rfl, .refl h⟩
  | @app Γ' f f' a a' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ'
    obtain ⟨g', hg, hgn⟩ := ih1 hΓ' W hf rfl
    obtain ⟨b', hb, hbn⟩ := ih2 hΓ' W ha rfl
    refine ⟨.app g' b', .app hg hb, ?_⟩
    simpa [VExpr.liftN] using NormalEq.appDF (hp1.hasType hΓ' hf)
      ((hg.weakN W).hasType hΓ' hf) (hp2.hasType hΓ' ha)
      ((hb.weakN W).hasType hΓ' ha) hgn hbn
  | @lam Γ' A₁ A₁' body body' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨⟨_, hD⟩, _, hb⟩ := h.lam_inv henv hΓ'
    obtain ⟨D', hD1, hDn⟩ := ih1 hΓ' W hD rfl
    obtain ⟨t', ht1, htn⟩ := ih2 ⟨hΓ', _, hD⟩ W.succ hb rfl
    refine ⟨.lam D' t', .lam hD1 ht1, ?_⟩
    simpa [VExpr.liftN] using
      NormalEq.lamDF (hp1.defeq hΓ' hD) ((hD1.weakN W).defeq hΓ' hD) htn
  | @forallE Γ' A₁ A₁' B₁ B₁' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> cases eq
    have ⟨⟨_, hD⟩, _, hB⟩ := h.forallE_inv henv
    obtain ⟨D', hD1, hDn⟩ := ih1 hΓ' W hD rfl
    obtain ⟨t', ht1, htn⟩ := ih2 ⟨hΓ', _, hD⟩ W.succ hB rfl
    refine ⟨.forallE D' t', .forallE hD1 ht1, ?_⟩
    simpa [VExpr.liftN] using
      NormalEq.forallEDF (hp1.defeq hΓ' hD) hDn
        (hp2.hasType (by exact ⟨hΓ', _, hD⟩) hB) htn
  | @beta Γ' A₁ e₁ e₁' e₂ e₂' hp1 hp2 ih1 ih2 =>
    intro k Γ e1 A hΓ' W h eq
    cases e1 <;> injection eq
    rename_i f a eq eq2; cases eq2
    cases f <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ'
    have ⟨⟨_, hD⟩, _, hb⟩ := hf.lam_inv henv hΓ'
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ' (hf.uniqU henv hΓ' (hD.lam hb))
    replace ha := ha.defeqU_r henv hΓ' ⟨_, u1⟩
    obtain ⟨t', ht1, htn⟩ := ih1 (by exact ⟨hΓ', _, hD⟩) W.succ hb rfl
    obtain ⟨b', hb1, hbn⟩ := ih2 hΓ' W ha rfl
    refine ⟨t'.inst b', .tail (ParRedKS.app (ParRedKS.lam .rfl ht1) hb1)
      (.beta ParRedK.rfl ParRedK.rfl), ?_⟩
    rw [liftN_inst_hi]
    -- `NormalEq.instN₂` in place of `instN` + `instN_r` + `trans`: one substitution step that
    -- moves *both* sides at once, so the `NormalEq.trans` (hence `IsDefEqU.weakN_iff`) entry
    -- this composition used to carry is gone from here.  Measured: it does not clear
    -- `weakN_iff` from `parRedK_weakN_invP`, whose `extra` case calls it directly.
    exact NormalEq.instN₂ (hp2.hasType hΓ' ha) hbn htn (by exact ⟨hΓ', _, hD⟩) .zero
  | @extra Γ' p r e0 m1 m2 m2' hpat hm hck hstep ih =>
    intro k Γ e1 A hΓ' W h eq
    subst eq
    obtain ⟨m3, hm3, hn⟩ := Pattern.matches_liftN.1 hm
    have hmeq : m2 = fun x => (m3 x).liftN n k := funext hn
    have key : ∀ a, ∃ z, ParRedKS Γ (m3 a) z ∧ NormalEq Γ' (m2' a) (z.liftN n k) := by
      intro a
      have ⟨_, hT⟩ := hm.hasType hΓ' h a
      exact ih a hΓ' W (by rw [← hn a]; exact hT) (hn a).symm
    have hck₀ : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m3 r.2 := by
      refine hck.map fun _ _ hab => ?_
      rw [hmeq, ← Pattern.RHS.liftN_apply, ← Pattern.RHS.liftN_apply] at hab
      exact (IsDefEqU.weakN_iff henv hΓ' W).1 hab
    have hne : ∀ a, NormalEq Γ' (m2' a) (((key a).choose).liftN n k) :=
      fun a => (key a).choose_spec.2
    refine ⟨_, ReflTransGen.trans (.tail .rfl (.extra hpat hm3 hck₀ fun _ => ParRedK.rfl))
      (Pattern.RHS.apply_parRedKS (fun a => (key a).choose_spec.1) r.1), ?_⟩
    rw [Pattern.RHS.liftN_apply]
    exact NormalEq.apply_pat hΓ' (fun x _ _ => hne x)
      ((ParRedK.extra hpat hm hck hstep).hasType hΓ' h)
  | @keta Γ' e w w' hek htail _ =>
    intro k Γ e1 A hΓ' W h eq
    subst eq
    exact keta_weakN_invKS HK HP HT (hΓ'.weakN_inv henv W) hΓ' W h hek htail

/-- Site 1's statement, `≫*` form, packaged. -/
theorem weakNInvStatementPS_of (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTailS)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr}
    (hΓ' : OnCtx Γ' (IsType env univs)) (W : Ctx.LiftN n k Γ Γ')
    (hty : Γ' ⊢ e1.liftN n k : A) (H : ParRedK Γ' (e1.liftN n k) e2') :
    ∃ e2, ParRedKS Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k) :=
  parRedK_weakN_invPS HK HP HT H hΓ' W hty rfl

/-- **Site 1 from the rule table, `≫*` form** -- the headline of round 8.  `KTable` is M3,
`PiTypeDescend` is the typing descent, `KStepTailS` is the new K-only residual. -/
theorem weakNInvStatementPS_of_kTable (KT : KTable) (HP : PiTypeDescend) (HT : KStepTailS)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2' A : VExpr}
    (hΓ' : OnCtx Γ' (IsType env univs)) (W : Ctx.LiftN n k Γ Γ')
    (hty : Γ' ⊢ e1.liftN n k : A) (H : ParRedK Γ' (e1.liftN n k) e2') :
    ∃ e2, ParRedKS Γ e1 e2 ∧ NormalEq Γ' e2' (e2.liftN n k) :=
  weakNInvStatementPS_of (kStepLiftInvP_of KT HP) HP HT hΓ' W hty H

/-- Site 1's statement, single-step form, packaged. -/
theorem weakNInvStatementP_of (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail) :
    WeakNInvStatementP :=
  fun hΓ' W hty H => parRedK_weakN_invP HK HP HT H hΓ' W hty rfl

/-- Site 1 from the rule table directly: `KTable` supplies `KStepLiftInvP`. -/
theorem weakNInvStatementP_of_kTable (KT : KTable) (HP : PiTypeDescend) (HT : KStepTail) :
    WeakNInvStatementP := weakNInvStatementP_of (kStepLiftInvP_of KT HP) HP HT

/-- The `≡ₚ` form of site 1 holds where `EtaK` is empty -- the refutation
(`not_weakNInvStatement_of_etaK`) kills the *equality* form only, and this is the check that
the weakening is consistent rather than merely unrefuted. -/
theorem weakNInvStatementP_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : WeakNInvStatementP := by
  intro n k Γ Γ' e1 e2' A hΓ' W hty H
  obtain ⟨e2, h1, rfl⟩ := weakNInvStatement_of_no_etaK hno hΓ' W hty H
  exact ⟨e2, h1, .refl (H.hasType hΓ' hty)⟩

theorem refParams_weakNInvStatementP : @WeakNInvStatementP refParams :=
  @weakNInvStatementP_of_no_etaK refParams (fun h => refParams_no_etaK h)



/-! ### Working rule 2: the repair, re-run at the refutation's own witness

`KEta.not_weakNInvStatement_of_etaK` refutes site 1's **equality** conclusion from a single
K-step, at the configuration `EtaK (C::Γ) e.lift (.lam (kdom C A₀) t)` -- a step whose λ-domain
`kdom C A₀` mentions `.bvar 0` and is therefore the lift of nothing.  The theorem below runs
the repaired statement at *that* configuration and produces a conclusion, so the witness is
visibly killed rather than merely no longer derivable.

Note where the descent lands on it: the `under` layer absorbs `kdom C A₀` by
`NormalEq.lamDF` at the middle domain `A₀.lift` (which is `kdom_normalEq_lam`), and the
recursion then asks `KStepLiftInvP` about `(VExpr.app e.lift (.bvar 0)).liftN 1 1`, which *is*
a lift -- the K-step is inspected one binder in, where the free domain no longer appears. -/
theorem weakNInvStatementP_at_kdom (HK : KStepLiftInvP) (HP : PiTypeDescend) (HT : KStepTail)
    {Γ : List VExpr} {C e A₀ B₀ t : VExpr} {uC : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (hC : Γ ⊢ C : .sort uC) (he : Γ ⊢ e : .forallE A₀ B₀)
    (hin : EtaK (A₀.lift :: C :: Γ) (.app (VExpr.lift (VExpr.lift e)) (.bvar 0)) t) :
    ∃ e2, ParRedK Γ e e2 ∧
      NormalEq (C::Γ) (.lam (kdom C A₀) t) (e2.liftN 1 0) := by
  have hΓC : OnCtx (C::Γ) (IsType env univs) := ⟨hΓ, _, hC⟩
  have ⟨⟨u, hA₀⟩, v, hB₀⟩ := (have ⟨_, h⟩ := he.isType henv hΓ; h.forallE_inv henv)
  have hty : (C::Γ) ⊢ e.lift : .forallE A₀.lift (B₀.liftN 1 1) := he.weak henv
  have hB : (A₀.lift :: C :: Γ) ⊢ B₀.liftN 1 1 : .sort v := hB₀.weakN henv (.succ .one)
  have hek : EtaK (C::Γ) e.lift (.lam (kdom C A₀) t) :=
    EtaK.under_dom hΓC hty hB (kdom_defeq hC hA₀).symm hin
  exact keta_weakN_invK HK HP HT hΓ hΓC .one hty hek ParRedK.rfl


end VEnv

end Lean4Lean
