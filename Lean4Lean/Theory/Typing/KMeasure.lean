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
  | here {Γ : List VExpr} {e t t' : VExpr} :
      KStep Γ e t → ParRed Γ t t' → EtaKn 0 Γ e t'
  | under {Γ : List VExpr} {e A B t : VExpr} {k : Nat} :
      Γ ⊢ e : .forallE A B →
      EtaKn k (A::Γ) (.app e.lift (.bvar 0)) t → EtaKn (k+1) Γ e (.lam A t)

theorem EtaKn.toEtaK {k : Nat} {Γ : List VExpr} {e e' : VExpr} (H : EtaKn k Γ e e') :
    EtaK Γ e e' := by
  induction H with
  | here h1 h2 => exact .here h1 h2
  | under h _ ih => exact .under h ih

theorem EtaK.count {Γ : List VExpr} {e e' : VExpr} (H : EtaK Γ e e') :
    ∃ k, EtaKn k Γ e e' := by
  induction H with
  | here h1 h2 => exact ⟨0, .here h1 h2⟩
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
  | @here _ e t t' hst _ =>
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

end VEnv

end Lean4Lean
