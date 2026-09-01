import Lean4Lean.Theory.Typing.HeadRedStuck

/-!
# `K⁺`: the K-like reduction rule `Theory/` is missing

`Theory/Typing/HeadRedStuck.lean` measures the hole: `whnf_app_bvar` shows that at **every**
`Params` instance, `f (.bvar i)` is weak-head normal whenever `f` is and `f` is not a `.lam`.
That is the K-redex `rec C ms is h` at a variable major premise `h`, which proof irrelevance
makes definitionally equal to its ι-contractum while no registered rule fires on it.

This file supplies the rule, in the shape the rest of the tree can consume, and proves the
one thing that has to be true before it may be added to `ParRed`: **it is admissible** --
every `K⁺` step is already a definitional equality of `IsDefEq`, so adding it to the
reduction relation does not enlarge the theory.

## The rule

`KStep` (below) fires at a registered pattern `.app p₁ p₂` on a term `.app f h` whose
*argument* need not match `p₂`: it is enough that `h` is definitionally equal to some `c`
for which `.app f c` does match.  The contractum is the rule's own right-hand side, computed
from that match.

Three things about this shape are deliberate.

1. **It is stated at `Pat`, not at inductive declarations.**  Carneiro's `K⁺`
   (`~/lean-type-theory/unique.tex:103`) is stated for *SS inductives*, so it does not cover
   the quotient rule; `Theory/`'s quotient rule is a `Pat` like any other, so the generic
   form covers it for free.  §"`Quot` over a `Prop` carrier" in `docs/handoff-krule.md` shows
   that this is not an idle generalisation: the quotient case is a real gap in the reference.

2. **The side condition is "the major premise has a canonical form", carried as the
   `IsDefEq` premise.**  Carneiro's rule carries `Γ ⊢ intro inv[p,h] : α` for the same
   reason, and says so: the rule "applies only when `intro inv[p,h]` is well-typed (and is
   the reason why `↝_κ` needs a context)" (`unique.tex:107`).  Discharging it per rule shape
   is `docs/design-inductive.md` §7.6's lemma M3 (`pat_major_canonical`), which is the work
   this file does *not* do.

2a. **The two typing premises are carried, not inverted.**  `KStep` records `f`'s Π-type and
   types the major-premise conversion at that domain, rather than recovering both by
   `HasType.app_inv` from a typing of the redex.  That is faithful to `K⁺`, whose side
   condition is a typing judgment for the same reason, and it is what keeps `KStep.defeq`
   out of `HasType.app_inv`'s and `IsDefEqU.of_l`'s cones.  It is also the shape
   `docs/handoff-headreduction.md` §8 item 4 asks about: a reduction rule that carries its
   typing premises, as `IsDefEqStrong.beta` does.

3. **It is a rule, not a pattern.**  `Params.no_kpattern` below shows the alternative is
   closed off: the pattern that would express K-like matching -- the recursor applied to one
   more `.var` than the ι-pattern's spine -- *intersects* that ι-pattern, so `Params.pat_uniq`
   makes registering both impossible.  (Carneiro takes the other branch of the same fork: his
   ι rule is restricted to **non-SS** inductives, `unique.tex:101`, so that only one of the
   two rules is ever available for a given recursor.)

   Taking that branch *here* -- registering the K-pattern **instead of** the ι-pattern -- does
   not work either, and for a sharper reason than uniqueness.  The K-pattern matches every
   ι-redex, so `extra_pat` would still be satisfiable; but `Params.pat_wf` would then have to
   prove `Γ ⊢ rec C ms is h ≡ RHS` for an *arbitrary* `h`, which is false unless `h`'s type is
   a `Prop`.  The guard would have to live in the rule's `Check`, and `Pattern.Check` cannot
   express it: its clauses are `defeq` between `RHS`-computable terms and `≈` between matched
   level lists, and neither can mention the *type* of a matched argument.  So the side
   condition has to sit outside the pattern language -- which is what `KStep` does.

## What is proved here

* `KStep.defeq` -- **regularity/admissibility**: a `K⁺` step is an `IsDefEqU`.  This is the
  premise `ParRed.defeq` would need for a `K⁺` constructor of `ParRed`, and it is proved
  from `Params.pat_wf` alone -- no Π-injectivity, no `NormalEq`, no confluence.
* `KStep.stuck_fires` -- **non-vacuity against the measured hole**: the very term
  `whnf_app_bvar` proves weak-head normal is a `KStep` redex.
* `Params.no_kpattern` -- K-like matching cannot be a `Pattern`.

What is **not** proved here, and is the work that remains: a `Params` instance that supplies
the canonical form (M3), and the extension of `ParRed`/`CParRed`/`NormalEq.parRed` by this
step.  See `docs/handoff-krule.md`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable [Params]
open Params

/-- **The `K⁺` step.**  At a registered pattern `.app p₁ p₂`, the term `.app f h` reduces to
the rule's right-hand side whenever the major premise `h` is definitionally equal to some `c`
making `.app f c` a redex.

`hdq` is the whole content of the rule: with `h = c` it is an ordinary ι-step, and with `h` an
arbitrary proof of the same `Prop` it is Carneiro's `K⁺`.  It is an `IsDefEqU` rather than a
syntactic side condition precisely because proof irrelevance is what supplies it. -/
inductive KStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | mk {p₁ p₂ : Pattern} {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
      {f h c A₀ B₀ : VExpr} {m1 m2} :
      Pat (.app p₁ p₂) r →
      (Pattern.app p₁ p₂).Matches (.app f c) m1 m2 →
      r.2.OK (IsDefEqU env univs Γ) m1 m2 →
      HasType env univs Γ f (.forallE A₀ B₀) →
      IsDefEq env univs Γ h c A₀ →
      KStep Γ (.app f h) (r.1.apply m1 m2)

/-- **Regularity of `K⁺`.**  Every `K⁺` step is a definitional equality, so adding the rule to
the reduction relation leaves `IsDefEq` -- and therefore `kernel_sound`'s statement -- exactly
where it was.

The proof is two steps and uses nothing from the injectivity corner: congruence moves the
major premise to its canonical form (`IsDefEq.appDF` on `hdq`), and `Params.pat_wf` fires the
rule there. -/
theorem KStep.defeq {Γ : List VExpr} {e e' : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (H : KStep Γ e e') : env.IsDefEqU univs Γ e e' := by
  cases H with
  | mk hpat hm hck hf hdq =>
    have hstep := IsDefEq.appDF hf hdq
    exact IsDefEqU.trans henv hΓ ⟨_, hstep⟩ (pat_wf hpat hm hΓ hstep.hasType.2 hck)

/-- **Non-vacuity, against the measured hole.**  `whnf_app_bvar` says `.app f (.bvar i)` is
weak-head normal for every `Params` instance; `KStep` reduces it.  The two conclusions hold
simultaneously, which is the precise sense in which the rule set -- not the reduction
relation -- was what was wrong.

The hypotheses are the honest cost: somebody must exhibit a `c` making `.app f c` a redex and
`.bvar i` definitionally equal to it.  For an inductive predicate that is proof irrelevance
plus `docs/design-inductive.md` §7.6's M3.  **Stale as of 2026-09-01: an instance now supplies it.**
`Theory/Typing/PatAppParams.lean`'s `appParams` is the first `Params` instance registering `.app`
patterns, and `appParams_stuck_fires` instantiates this statement fully — at `Γ = [P]`,
`C (.bvar 0)` is weak-head normal *and* a `K⁺` redex, proof irrelevance supplying the major-premise
conversion. -/
theorem KStep.stuck_fires {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {f c A₀ B₀ : VExpr} {i : Nat}
    {m1 m2}
    (hpat : Pat (.app p₁ p₂) r)
    (hm : (Pattern.app p₁ p₂).Matches (.app f c) m1 m2)
    (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hty : HasType env univs Γ f (.forallE A₀ B₀))
    (hdq : IsDefEq env univs Γ (.bvar i) c A₀)
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e) :
    WHNF Γ (.app f (.bvar i)) ∧ KStep Γ (.app f (.bvar i)) (r.1.apply m1 m2) :=
  ⟨whnf_app_bvar hf hlam, .mk hpat hm hck hty hdq⟩

/-- The pattern that would express K-like *matching*: the recursor's spine with one more
`.var`, so that the major premise position accepts anything.  `Pattern.varN` counts
applications, so this is the ι-pattern's function side extended by one. -/
def kPattern (rec : Lean.Name) (m : Nat) : Pattern := (Pattern.const rec).varN (m+1)

/-- **K-like reduction cannot be a `Pattern`.**  A recursor's K-pattern and its ι-pattern
intersect -- the ι-pattern refines the K-pattern's last `.var` to a constructor spine -- so
`Params.pat_uniq`, applied with `p₃ := p₁`, concludes they are the *same* pattern, which they
are not (`.app` versus `.var`).

This is why `KStep` is a rule with a semantic side condition rather than a new
`SimplePattern` constructor, and it is the same fork Carneiro takes when he restricts the ι
rule to non-SS inductives (`unique.tex:101`): at most one of the two rules may be live for a
given recursor. -/
theorem Params.no_kpattern {rec ctor : Lean.Name} {m n : Nat} {rι rk}
    (h1 : Pat (SimplePattern.iota rec m ctor n).toPattern rι)
    (h2 : Pat (kPattern rec m) rk) : False := by
  have hinter : (kPattern rec m).inter (SimplePattern.iota rec m ctor n).toPattern
      = some (SimplePattern.iota rec m ctor n).toPattern := by
    simp [kPattern, SimplePattern.toPattern, Pattern.varN, Pattern.inter,
      Pattern.inter_self]
  have := Params.pat_uniq h1 h2 Subpattern.refl hinter
  simp [kPattern, SimplePattern.toPattern, Pattern.varN] at this
