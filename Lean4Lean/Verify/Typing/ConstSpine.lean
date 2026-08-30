import Lean4Lean.Theory.Typing.HeadReduction
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.ParamsBuild

/-!
# Constant-headed spines under reduction — facts (A), (B), (C), (D)

`Theory/Typing/Injectivity.lean` records four facts about applications of a **rule-free**
constant, and leaves all of them open, with the same diagnosis attached to each: the residual
is the `trans` case of an induction on `IsDefEqStrong`, "a term convertible with a rule-free
constant application reduces to one".

**That diagnosis is right about the induction and wrong about the statements.**  The `trans`
case is an artefact of choosing to induct on the conversion derivation.  `VEnv.NormalEq`
(`Theory/Typing/ChurchRosser.lean`) has **no `trans` constructor** — transitivity there is a
theorem, and `VEnv.IsDefEq.church_rosser` has already paid for it — so an argument routed
through Church--Rosser never meets that case.  What it meets instead is a three-step
decomposition:

1. **Reduction preserves a rule-free constant head.**  `ParRed.constApp_inv` /
   `ParRedS.constApp_inv`: a parallel reduct of `(const c ls).mkApp as` is
   `(const c ls).mkApp as'` with `as ≫ as'` pointwise.  The `beta` case is impossible (the
   spine head is not a λ) and the `extra` case is impossible because no registered pattern is
   headed by `c`.
2. **`NormalEq` between two constant spines is componentwise.**  `NormalEq.constApp_inv`:
   `refl`, `constDF` and `appDF` are the only reachable constructors; `proofIrrel` is blocked
   by `¬IsProof`, threaded down the spine by `IsProof.app'` exactly as in
   `Injectivity.lean`'s own `const_app_inv` skeleton; `etaL`/`etaR` are blocked by shape,
   because a constant spine is never a λ.
3. **Church--Rosser** joins them.

Facts (A) (`const_forallE_inv`, `const_sort_inv`), (B) (`const_app_inv`) and (D)
(no-confusion, `VEnv.ConstNoConf`) all come out this way.  Their residual is **not** anything
in the `Injectivity.lean` family: measured, it is exactly

    IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, NormalEq.descend, IsDefEqU.forallE_inv

— four existing census holes, none of them a constant-application fact — plus one hypothesis,
`VEnv.PatWF`, the single field of `VEnv.Params` that `VEnv.paramsOfWF` does not derive from
`VEnv.WF`.  So the constant-application family is not an independent obligation at all: it is
downstream of the sort/Π family and of `PatWF`.

## (C) is different, and this file says exactly how

(C) rigidity — "a term definitionally equal to a rule-free constant application weak-head
reduces to one with that head" — does **not** follow, and the obstruction is step 2's `etaL`
clause.  With only *one* endpoint known to be a constant spine, `etaL` can relate a λ to it.
At the top of the spine (C)'s `IsType` side condition kills that (a λ is not a type,
`isType_lam_false`); at a proper sub-spine it does not, because a sub-spine has a Π type.  And
the induction hypothesis one would need there is *false*: `.lam A b` is a weak-head normal
form that η-relates to a constant application and is not one (`whnf_lam_not_constApp`).

Knowing the subject's weak-head normal form exists repairs it, because a `WHNF` application
has a `WHNF`, non-λ function.  `constRigid_of_weakNorm` is the result: **(C) follows from
weak-head normalisation and nothing else.**

## Two side conditions, and a correction to one of them

`RuleFreeHead` is a fact about `env.defeqs`.  The step it has to block is `WHRed.extra` /
`ParRed.extra`, which fires on a `Params.Pat`-registered pattern, and the `Params` class
relates `Pat` to `defeqs` in one direction only (`extra_pat`: every rule is a registered
pattern).  So under an *abstract* `Params`, `RuleFreeHead` cannot reach the step it is meant to
block.  `VEnv.PatFreeHead` is the condition that can, and `VEnv.RuleFreeHead.patFreeHead`
shows the two agree at the canonical table `Lean4Lean.Pat env` — the one `paramsOfWF` installs
— because every registered pattern's head constant is a rule's left-hand side's head constant
(`Lean4Lean.Pat.headConst_defeqs`).  See `Verify/Typing/Rigidity.lean` for the consequence:
`VEnv.ConstRigid` as previously stated is under-hypothesised.

The `IsType` condition is unchanged and still load-bearing; `Theory/Typing/ConstInvWitness.lean`
machine-checks that dropping either condition proves `False`.
-/

namespace Lean4Lean

open VExpr

/-- The head constant of a *pattern* — its leftmost `const` leaf. -/
def Pattern.headConst : Pattern → Lean.Name
  | .const c => c
  | .app f _ => f.headConst
  | .var f => f.headConst

/-- A matched term's head constant is the pattern's. -/
theorem Pattern.Matches.headConst {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.headConst? = some p.headConst := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih1 _ => exact ih1

/-- A constant-headed spine determines its head, levels and arguments. -/
theorem VExpr.constApp_inj {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (h : (VExpr.const c ls).mkApp as = (VExpr.const c' ls').mkApp as') :
    c = c' ∧ ls = ls' ∧ as = as' := by
  have h1 := congrArg VExpr.spineHead h
  have h2 := congrArg VExpr.spineArgs h
  rw [VExpr.spineHead_mkApp, VExpr.spineHead_mkApp] at h1
  rw [VExpr.spineArgs_mkApp, VExpr.spineArgs_mkApp] at h2
  simp [VExpr.spineHead, VExpr.spineArgs] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

theorem VExpr.constApp_ne_lam {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A b : VExpr} :
    (VExpr.const c ls).mkApp as ≠ .lam A b := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_bvar {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {i : Nat} :
    (VExpr.const c ls).mkApp as ≠ .bvar i := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_sort {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel} :
    (VExpr.const c ls).mkApp as ≠ .sort u := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_forallE {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    {A B : VExpr} : (VExpr.const c ls).mkApp as ≠ .forallE A B := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

end Lean4Lean

namespace Lean4Lean

open VExpr

/-- `List.Forall₂` at a reflexive relation. -/
theorem _root_.List.forall₂_refl' {α} {R : α → α → Prop} (hR : ∀ a, R a a) :
    ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | _ :: l => .cons (hR _) (List.forall₂_refl' hR l)

/-- Composing two `List.Forall₂`s. -/
theorem _root_.List.Forall₂.trans' {α} {R S T : α → α → Prop}
    (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ → List.Forall₂ T l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (List.Forall₂.trans' h t1 t2)

namespace VEnv

variable [Params]
open Params

/-- **`c` heads no registered rewrite pattern.**

This is the `Params`-level form of `RuleFreeHead`: `WHRed.extra` / `ParRed.extra` fire on a
`Pat`-registered pattern, and what stops them from firing at a `c`-headed spine is that no
registered pattern has `c` as its head constant.  `ruleFreeHead_patFree` below derives it
from `VEnv.RuleFreeHead` for the canonical pattern table. -/
def PatFreeHead (c : Lean.Name) : Prop := ∀ p r, Params.Pat p r → p.headConst ≠ c

/-- **Parallel reduction preserves a rule-free constant head**, its levels, and its arity. -/
theorem ParRed.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHead c) :
    ∀ {ls : List VLevel} {as : List VExpr} {e' : VExpr},
      ParRed Γ ((VExpr.const c ls).mkApp as) e' →
      ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRed Γ) as as' := by
  intro ls as e' H
  generalize he : (VExpr.const c ls).mkApp as = e₀ at H
  induction H generalizing as with
  | @const _ c₀ ls₀ =>
    obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ he nofun
    injection heq with h1 h2; subst h1; subst h2
    exact ⟨[], rfl, .nil⟩
  | @app _ f f' a a' hf ha ihf iha =>
    rcases VExpr.mkApp_app_inv as _ he with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    obtain ⟨bs', rfl, hbs⟩ := ihf hb
    exact ⟨bs' ++ [a'], by rw [VExpr.mkApp_append]; rfl, hbs.append' (.cons ha .nil)⟩
  | @beta _ A e₁ e₁' e₂ e₂' _ _ _ _ =>
    rcases VExpr.mkApp_app_inv as _ he with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    exact absurd hb VExpr.constApp_ne_lam
  | @extra p r e₀ m1 m2 _ m2' h1 h2 _ _ _ =>
    subst he
    have := h2.headConst
    rw [VExpr.headConst?_mkApp] at this
    exact absurd (Option.some.inj this).symm (hc _ _ h1)
  | bvar => exact absurd he VExpr.constApp_ne_bvar
  | sort => exact absurd he VExpr.constApp_ne_sort
  | lam => exact absurd he VExpr.constApp_ne_lam
  | forallE => exact absurd he VExpr.constApp_ne_forallE

/-- The reflexive-transitive form: a rule-free constant spine reduces only to spines with
the same head, the same levels and the same arity. -/
theorem ParRedS.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHead c)
    {ls : List VLevel} {as : List VExpr} {e' : VExpr}
    (H : ParRedS Γ ((VExpr.const c ls).mkApp as) e') :
    ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedS Γ) as as' := by
  induction H with
  | rfl => exact ⟨as, rfl, List.forall₂_refl' (fun _ => .rfl) as⟩
  | @tail b c₂ h1 h2 ih =>
    obtain ⟨bs, rfl, hbs⟩ := ih
    obtain ⟨cs, rfl, hcs⟩ := ParRed.constApp_inv hc h2
    exact ⟨cs, rfl, hbs.trans' (fun _ _ _ h h' => h.tail h') hcs⟩

/-- Every argument of a well-typed spine is well-typed, hence definitionally equal to
itself. -/
theorem hasType_spine_head {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ (as : List VExpr) {f A : VExpr}, HasType env univs Γ (f.mkApp as) A →
      ∃ B, HasType env univs Γ f B
  | [], _, A, h => ⟨A, h⟩
  | a :: as, f, A, h => by
    rw [VExpr.mkApp_cons] at h
    obtain ⟨B, hB⟩ := hasType_spine_head hΓ as h
    obtain ⟨A', B', hf, -⟩ := hB.app_inv henv hΓ
    exact ⟨_, hf⟩

theorem hasType_spine_args_defeq {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ (as : List VExpr) {f A : VExpr}, HasType env univs Γ (f.mkApp as) A →
      List.Forall₂ (IsDefEqU env univs Γ) as as
  | [], _, _, _ => .nil
  | a :: as, f, A, h => by
    rw [VExpr.mkApp_cons] at h
    obtain ⟨B, hB⟩ := hasType_spine_head hΓ as h
    obtain ⟨A', B', -, ha⟩ := hB.app_inv henv hΓ
    exact .cons ⟨_, ha⟩ (hasType_spine_args_defeq hΓ as h)

/-- **The `NormalEq` core.**  Two constant-headed spines in normal-form equality have the
same head, `≈`-equal level lists and pairwise definitionally equal arguments.

The `¬IsProof` side condition is exactly `const_app_inv`'s, for the same reason: it is what
blocks the `proofIrrel` constructor, and it propagates down the spine by `IsProof.app'`
where `IsType` would not. -/
theorem NormalEq.constApp_inv {c c' : Lean.Name} :
    ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      OnCtx Γ (IsType env univs) → ¬ IsProof env univs Γ e₁ →
      ∀ (ls ls' : List VLevel) (as as' : List VExpr),
        e₁ = (VExpr.const c ls).mkApp as → e₂ = (VExpr.const c' ls').mkApp as' →
        c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧
          List.Forall₂ (IsDefEqU env univs Γ) as as' := by
  intro Γ e₁ e₂ H
  induction H with
  | @refl _ e A h =>
    rintro hΓ - ls ls' as as' rfl he₂
    obtain ⟨rfl, rfl, rfl⟩ := VExpr.constApp_inj he₂
    exact ⟨rfl, VLevel.forall₂_equiv_refl _, hasType_spine_args_defeq hΓ _ h⟩
  | sortDF => rintro - - ls ls' as as' he₁ -; exact absurd he₁.symm VExpr.constApp_ne_sort
  | @constDF _ c₀ ci ls₀ ls₀' h1 h2 h3 h4 h5 =>
    rintro - - ls ls' as as' he₁ he₂
    obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ he₁.symm nofun
    obtain ⟨rfl, heq'⟩ := VExpr.mkApp_eq_of_not_app as' _ _ he₂.symm nofun
    injection heq with hc hl; injection heq' with hc' hl'
    subst hc; subst hl; subst hc'; subst hl'
    exact ⟨rfl, h5, .nil⟩
  | @appDF _ f₁ A B f₂ a₁ a₂ hf₁ hf₂ ha₁ ha₂ hfn han ihf iha =>
    rintro hΓ hnp ls ls' as as' he₁ he₂
    rcases VExpr.mkApp_app_inv as _ he₁.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    rcases VExpr.mkApp_app_inv as' _ he₂.symm with ⟨-, hbad⟩ | ⟨bs', rfl, hb'⟩
    · exact absurd hbad nofun
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := hf₁.isType henv hΓ; h.forallE_inv henv
    have hnpf : ¬ IsProof env univs _ f₁ := fun hp =>
      hnp (IsProof.app' Params.henv hΓ hA hB hf₁ ha₁ hp)
    obtain ⟨hcc, hl, hbs⟩ := ihf hΓ hnpf ls ls' bs bs' hb.symm hb'.symm
    exact ⟨hcc, hl, hbs.append' (.cons (han.defeq hΓ) .nil)⟩
  | lamDF => rintro - - ls ls' as as' he₁ -; exact absurd he₁.symm VExpr.constApp_ne_lam
  | forallEDF => rintro - - ls ls' as as' he₁ -; exact absurd he₁.symm VExpr.constApp_ne_forallE
  | etaL => rintro - - ls ls' as as' he₁ -; exact absurd he₁.symm VExpr.constApp_ne_lam
  | etaR => rintro - - ls ls' as as' - he₂; exact absurd he₂.symm VExpr.constApp_ne_lam
  | proofIrrel h1 h2 h3 =>
    rintro - hnp ls ls' as as' rfl -
    exact absurd ⟨_, h1, h2⟩ hnp

/-- Argument-wise parallel reduction of a well-typed spine is argument-wise conversion. -/
theorem spine_args_parRedS_defeq {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ (as bs : List VExpr) {f A : VExpr}, HasType env univs Γ (f.mkApp as) A →
      List.Forall₂ (ParRedS Γ) as bs → List.Forall₂ (IsDefEqU env univs Γ) as bs
  | [], _, _, _, _, .nil => .nil
  | a :: as, _, f, A, h, .cons hab hrest => by
    rw [VExpr.mkApp_cons] at h
    obtain ⟨B, hB⟩ := hasType_spine_head hΓ as h
    obtain ⟨A', B', -, ha⟩ := hB.app_inv henv hΓ
    exact .cons ⟨_, hab.defeq hΓ ha⟩ (spine_args_parRedS_defeq hΓ as _ h hrest)

/-! ## (B) injectivity and (D) no-confusion, relative to `Params`

Both are the same Church--Rosser argument: both endpoints parallel-reduce to constant spines
with the same heads (`ParRedS.constApp_inv`), and `NormalEq` between two constant spines is
head-, level- and argument-wise (`NormalEq.constApp_inv`).  The `trans` case that made these
statements open in `Theory/Typing/Injectivity.lean` does not arise, because `NormalEq` has no
`trans` constructor: transitivity there is a *theorem*, and `IsDefEq.church_rosser` has
already paid for it. -/

/-- **(B) + (D) together.**  Two definitionally equal constant-headed spines with rule-free
heads have the *same* head, `≈`-equal levels and pairwise convertible arguments. -/
theorem IsDefEq.constApp_inv {Γ : List VExpr} {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr} {A : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hc : PatFreeHead c) (hc' : PatFreeHead c')
    (hnp : ¬ IsProof env univs Γ ((VExpr.const c ls).mkApp as))
    (H : IsDefEq env univs Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') A) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (IsDefEqU env univs Γ) as as' := by
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
  obtain ⟨bs, rfl, hbs⟩ := ParRedS.constApp_inv hc h1
  obtain ⟨bs', rfl, hbs'⟩ := ParRedS.constApp_inv hc' h2
  have hd1 : IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls).mkApp bs) :=
    ⟨_, h1.defeq hΓ H.hasType.1⟩
  have hnp' : ¬ IsProof env univs Γ ((VExpr.const c ls).mkApp bs) := fun hp =>
    hnp (hp.defeqU henv hΓ hd1.symm)
  obtain ⟨hcc, hl, hmid⟩ := NormalEq.constApp_inv h3 hΓ hnp' ls ls' bs bs' rfl rfl
  refine ⟨hcc, hl, ?_⟩
  have hleft := spine_args_parRedS_defeq hΓ as bs H.hasType.1 hbs
  have hright := spine_args_parRedS_defeq hΓ as' bs' H.hasType.2 hbs'
  exact (hleft.trans' (fun _ _ _ h h' => h.trans henv hΓ h') hmid).trans'
    (fun _ _ _ h h' => h.trans henv hΓ h') (hright.symm' IsDefEqU.symm)

/-! ## (A) disjointness, by the same route

`const_forallE_inv` and `const_sort_inv` (`Theory/Typing/Injectivity.lean`, both `sorry`) fall
out of the same Church--Rosser argument, and even more cheaply: with the right-hand side a Π or
a sort, `NormalEq`'s only live constructor is `proofIrrel`, which the right-hand side's being a
type already refutes.  No spine recursion is needed. -/

theorem ParRed.forallE_inv {Γ : List VExpr} {A B e' : VExpr} (H : ParRed Γ (.forallE A B) e') :
    ∃ A' B', e' = .forallE A' B' := by
  cases H with
  | forallE => exact ⟨_, _, rfl⟩
  | extra _ h2 => exact absurd h2.headConst nofun

theorem ParRed.sort_inv {Γ : List VExpr} {u : VLevel} {e' : VExpr}
    (H : ParRed Γ (.sort u) e') : e' = .sort u := by
  cases H with
  | sort => rfl
  | extra _ h2 => exact absurd h2.headConst nofun

theorem ParRedS.forallE_inv {Γ : List VExpr} {A B e' : VExpr}
    (H : ParRedS Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  induction H with
  | rfl => exact ⟨_, _, rfl⟩
  | tail _ h2 ih => obtain ⟨_, _, rfl⟩ := ih; exact h2.forallE_inv

theorem ParRedS.sort_inv {Γ : List VExpr} {u : VLevel} {e' : VExpr}
    (H : ParRedS Γ (.sort u) e') : e' = .sort u := by
  induction H with
  | rfl => rfl
  | tail _ h2 ih => cases ih; exact h2.sort_inv

/-- `NormalEq` cannot relate a constant spine to a Π once the Π is known not to be a proof. -/
theorem NormalEq.constApp_forallE {c : Lean.Name} :
    ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      ¬ IsProof env univs Γ e₂ →
      ∀ (ls : List VLevel) (as : List VExpr) (A B : VExpr),
        e₁ = (VExpr.const c ls).mkApp as → e₂ = .forallE A B → False := by
  intro Γ e₁ e₂ H
  induction H with
  | refl => rintro - ls as A B rfl he₂; exact VExpr.constApp_ne_forallE he₂
  | sortDF => rintro - ls as A B - he₂; exact absurd he₂ nofun
  | constDF => rintro - ls as A B - he₂; exact absurd he₂ nofun
  | appDF => rintro - ls as A B - he₂; exact absurd he₂ nofun
  | lamDF => rintro - ls as A B he₁ -; exact VExpr.constApp_ne_lam he₁.symm
  | forallEDF => rintro - ls as A B he₁ -; exact VExpr.constApp_ne_forallE he₁.symm
  | etaL => rintro - ls as A B he₁ -; exact VExpr.constApp_ne_lam he₁.symm
  | etaR => rintro - ls as A B - he₂; exact absurd he₂ nofun
  | @proofIrrel _ p h h' h1 h2 h3 => rintro hnp ls as A B - -; exact hnp ⟨_, h1, h3⟩

/-- `NormalEq` cannot relate a constant spine to a sort once the sort is known not to be a
proof. -/
theorem NormalEq.constApp_sort {c : Lean.Name} :
    ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      ¬ IsProof env univs Γ e₂ →
      ∀ (ls : List VLevel) (as : List VExpr) (u : VLevel),
        e₁ = (VExpr.const c ls).mkApp as → e₂ = .sort u → False := by
  intro Γ e₁ e₂ H
  induction H with
  | refl => rintro - ls as u rfl he₂; exact VExpr.constApp_ne_sort he₂
  | sortDF => rintro - ls as u he₁ -; exact VExpr.constApp_ne_sort he₁.symm
  | constDF => rintro - ls as u - he₂; exact absurd he₂ nofun
  | appDF => rintro - ls as u - he₂; exact absurd he₂ nofun
  | lamDF => rintro - ls as u he₁ -; exact VExpr.constApp_ne_lam he₁.symm
  | forallEDF => rintro - ls as u he₁ -; exact VExpr.constApp_ne_forallE he₁.symm
  | etaL => rintro - ls as u he₁ -; exact VExpr.constApp_ne_lam he₁.symm
  | etaR => rintro - ls as u - he₂; exact absurd he₂ nofun
  | @proofIrrel _ p h h' h1 h2 h3 => rintro hnp ls as u - -; exact hnp ⟨_, h1, h3⟩

/-- **(A) disjointness, Π half** — a rule-free constant application is not a Π. -/
theorem IsDefEqU.constApp_forallE_false {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {A B : VExpr} (hΓ : OnCtx Γ (IsType env univs)) (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.forallE A B) := by
  rintro ⟨T, H⟩
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
  obtain ⟨bs, rfl, -⟩ := ParRedS.constApp_inv hc h1
  obtain ⟨A', B', rfl⟩ := ParRedS.forallE_inv h2
  have ⟨⟨_, hA⟩, _, hB⟩ := H.hasType.2.forallE_inv Params.henv.ordered
  have hty : IsType env univs Γ (.forallE A' B') :=
    ⟨_, h2.hasType hΓ (hA.forallE hB)⟩
  exact NormalEq.constApp_forallE h3 (IsType.not_isProof Params.henv hΓ hty) _ bs _ _ rfl rfl

/-- **(A) disjointness, sort half** — a rule-free constant application is not a sort. -/
theorem IsDefEqU.constApp_sort_false {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {u : VLevel} (hΓ : OnCtx Γ (IsType env univs)) (hc : PatFreeHead c) :
    ¬ IsDefEqU env univs Γ ((VExpr.const c ls).mkApp as) (.sort u) := by
  rintro ⟨T, H⟩
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := H.church_rosser hΓ
  obtain ⟨bs, rfl, -⟩ := ParRedS.constApp_inv hc h1
  cases ParRedS.sort_inv h2
  have hu : u.WF univs := H.hasType.2.sort_inv Params.henv.ordered
  exact NormalEq.constApp_sort h3
    (IsType.not_isProof Params.henv hΓ ⟨_, HasType.sort hu⟩) _ bs _ rfl rfl

/-! ## (C) rigidity, and the residual it really has

(C) — "a term definitionally equal to a rule-free constant application weak-head reduces to
one with the same head" — does **not** fall out of the Church--Rosser argument above, and the
reason is worth recording precisely, because it is not the reason the earlier analysis gave.

The spine recursion that proves (B) and (D) works because *both* endpoints are constant
spines, so `NormalEq`'s `etaL` constructor is excluded by shape at every level.  For (C) only
the right endpoint is known, and `etaL` says a **λ** can be `NormalEq` to a constant
application.  At the top of the spine that is excluded by (C)'s `IsType` side condition (an
η-expansion has a Π type, and a Π is not a sort); at a *proper sub-spine* it is not, because a
sub-spine legitimately has a Π type.  And the strengthened induction hypothesis one would need
there is **false**: `.lam A b` is a weak-head normal form (`WHNF.lam`) which is not a constant
application, yet η-relates to one.  `whnf_lam_not_constApp` below is that obstruction,
machine-checked.

What repairs it is knowing the subject's weak-head normal form *exists*: a `WHNF` application
has a `WHNF`, non-λ function (`WHNF.app_fn`, `WHNF.app_not_lam`), so along a `WHNF` spine
`etaL` is excluded at every level after all.  `constRigid_of_weakNorm` below is the resulting
implication.  So (C)'s residual is **weak-head normalisation**, not any further inversion
principle — and in particular not anything in the `Injectivity.lean` family. -/

theorem WHNF.app_fn {Γ : List VExpr} {f a : VExpr} (h : WHNF Γ (.app f a)) : WHNF Γ f :=
  fun _ hf => h _ (.app hf)

theorem WHNF.app_not_lam {Γ : List VExpr} {f a : VExpr} (h : WHNF Γ (.app f a)) :
    ∀ A b, f ≠ .lam A b := by rintro A b rfl; exact h _ .beta

/-- **The obstruction to the naive spine induction**, machine-checked: a λ is a weak-head
normal form, so it reduces only to itself, and it is never a constant application. -/
theorem whnf_lam_not_constApp {Γ : List VExpr} {A b e' : VExpr}
    (H : WHRedS Γ (.lam A b) e') (c : Lean.Name) (ls : List VLevel) (as : List VExpr) :
    e' ≠ (VExpr.const c ls).mkApp as := by
  cases WHNF.lam.whRedS H; exact fun h => VExpr.constApp_ne_lam h.symm

/-- A weak-head normal form that standard-reduces to a constant spine **is** one. -/
theorem StRed.constApp_whnf {c : Lean.Name} {ls : List VLevel} :
    ∀ {Γ : List VExpr} {e₀ e' : VExpr}, StRed Γ e₀ e' → WHNF Γ e₀ →
      ∀ as : List VExpr, e' = (VExpr.const c ls).mkApp as →
      ∃ as', e₀ = (VExpr.const c ls).mkApp as' := by
  intro Γ e₀ e' H
  induction H with
  | @const _ e c₀ ls₀ h1 =>
    intro hw as he
    obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ he.symm nofun
    injection heq with hc hl; subst hc; subst hl
    cases hw.whRedS h1
    exact ⟨[], rfl⟩
  | @app _ e f a f' a' h1 h2 h3 ihf iha =>
    intro hw as he
    rcases VExpr.mkApp_app_inv as _ he.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    cases hw.whRedS h1
    obtain ⟨bs', rfl⟩ := ihf hw.app_fn bs hb.symm
    exact ⟨bs' ++ [a], by rw [VExpr.mkApp_append]; rfl⟩
  | bvar => intro _ as he; exact absurd he.symm VExpr.constApp_ne_bvar
  | sort => intro _ as he; exact absurd he.symm VExpr.constApp_ne_sort
  | lam => intro _ as he; exact absurd he.symm VExpr.constApp_ne_lam
  | forallE => intro _ as he; exact absurd he.symm VExpr.constApp_ne_forallE

/-- **The spine analysis under a `WHNF` subject.**  A weak-head normal form whose standard
reduct is `NormalEq` to a rule-free constant spine is itself such a spine. -/
theorem NormalEq.constApp_whnf {c : Lean.Name} :
    ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      OnCtx Γ (IsType env univs) → ¬ IsProof env univs Γ e₂ →
      ∀ (ls : List VLevel) (as : List VExpr) (e₀ : VExpr),
        WHNF Γ e₀ → (∀ A b, e₀ ≠ .lam A b) → StRed Γ e₀ e₁ →
        e₂ = (VExpr.const c ls).mkApp as →
        ∃ ls' as', e₀ = (VExpr.const c ls').mkApp as' := by
  intro Γ e₁ e₂ H
  induction H with
  | @refl _ e A h =>
    rintro - - ls as e₀ hw - HS rfl
    exact ⟨_, StRed.constApp_whnf HS hw as rfl⟩
  | sortDF => rintro - - ls as e₀ - - - he₂; exact absurd he₂.symm VExpr.constApp_ne_sort
  | @constDF _ c₀ ci ls₀ ls₀' h1 h2 h3 h4 h5 =>
    rintro - - ls as e₀ hw - HS he₂
    obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ he₂.symm nofun
    injection heq with hc hl; subst hc
    exact ⟨_, StRed.constApp_whnf HS hw [] rfl⟩
  | @appDF _ f₁ A B f₂ a₁ a₂ hf₁ hf₂ ha₁ ha₂ hfn han ihf iha =>
    rintro hΓ hnp ls as e₀ hw hnl HS he₂
    rcases VExpr.mkApp_app_inv as _ he₂.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := hf₂.isType Params.henv.ordered hΓ;
      h.forallE_inv Params.henv.ordered
    have hnpf : ¬ IsProof env univs _ f₂ := fun hp =>
      hnp (IsProof.app' Params.henv hΓ hA hB hf₂ ha₂ hp)
    cases HS with
    | app h1 h2 h3 =>
      cases hw.whRedS h1
      obtain ⟨ls', bs', rfl⟩ :=
        ihf hΓ hnpf ls bs _ hw.app_fn (fun A b hA => hw.app_not_lam A b hA) h2 hb.symm
      exact ⟨ls', bs' ++ [_], by rw [VExpr.mkApp_append]; rfl⟩
  | lamDF => rintro - - ls as e₀ - - - he₂; exact absurd he₂.symm VExpr.constApp_ne_lam
  | forallEDF => rintro - - ls as e₀ - - - he₂; exact absurd he₂.symm VExpr.constApp_ne_forallE
  | @etaL _ e' A B e h1 h2 ih =>
    rintro - - ls as e₀ hw hnl HS -
    cases HS with
    | lam h1 _ _ => cases hw.whRedS h1; exact absurd rfl (hnl _ _)
  | etaR => rintro - - ls as e₀ - - - he₂; exact absurd he₂.symm VExpr.constApp_ne_lam
  | @proofIrrel _ p h h' h1 h2 h3 =>
    rintro - hnp ls as e₀ - - - rfl
    exact absurd ⟨_, h1, h3⟩ hnp

/-- **A λ is not a type.**  Needed to exclude `NormalEq.etaL` at the *top* of the spine,
where the subject is known to be a type but nothing else about it is known. -/
theorem isType_lam_false {Γ : List VExpr} {A b : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (h : IsType env univs Γ (.lam A b)) : False := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨⟨v, hA⟩, B, hb⟩ := hu.lam_inv Params.henv.ordered hΓ
  obtain ⟨w, hw⟩ := WF.uniq' Params.henv hΓ hu (hA.lam hb)
  exact IsDefEqU.sort_forallE_inv Params.henv hΓ ⟨_, hw⟩

/-- **Weak-head normalisation**: every well-typed term has a weak-head normal form.  This is
(C)'s residual, and the only one. -/
def WeakNorm : Prop :=
  ∀ (Γ : List VExpr) (e A : VExpr), OnCtx Γ (IsType env univs) →
    HasType env univs Γ e A → ∃ e', WHRedS Γ e e' ∧ WHNF Γ e'

/-- **(C) rigidity, from weak-head normalisation.**  A term definitionally equal to a
rule-free constant application, at a type, weak-head reduces to a constant application with
that same head. -/
theorem constRigid_of_weakNorm (hwn : WeakNorm) {Γ : List VExpr} {e : VExpr}
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hc : PatFreeHead c)
    (hty : IsType env univs Γ ((VExpr.const c ls).mkApp as))
    (hdf : IsDefEqU env univs Γ e ((VExpr.const c ls).mkApp as)) :
    ∃ (ls' : List VLevel) (as' : List VExpr),
      WHRedS Γ e ((VExpr.const c ls').mkApp as') := by
  obtain ⟨T, hdf⟩ := hdf
  obtain ⟨e₀, hred, hw⟩ := hwn Γ e T hΓ hdf.hasType.1
  have hte₀ : HasType env univs Γ e₀ T := hred.hasType hΓ hdf.hasType.1
  have hdf₀ : IsDefEq env univs Γ e₀ ((VExpr.const c ls).mkApp as) T :=
    ((hred.defeq hΓ hdf.hasType.1).symm).trans hdf
  -- `e₀` is not a λ: it is convertible with a type, and a λ is not a type.
  have hnl : ∀ A b, e₀ ≠ .lam A b := by
    rintro A b rfl
    exact isType_lam_false hΓ <| by
      obtain ⟨u, hu⟩ := hty
      exact ⟨u, HasType.defeqU_l' Params.henv hΓ ⟨_, hdf₀.symm⟩ hu⟩
  obtain ⟨-, -, e₁', e₂', h1, h2, h3⟩ := hdf₀.church_rosser hΓ
  obtain ⟨bs, rfl, -⟩ := ParRedS.constApp_inv hc h2
  have hty₂ : IsType env univs Γ ((VExpr.const c ls).mkApp bs) :=
    have ⟨u, hu⟩ := hty; ⟨u, h2.hasType hΓ hu⟩
  obtain ⟨ls', as', rfl⟩ :=
    NormalEq.constApp_whnf h3 hΓ (IsType.not_isProof Params.henv hΓ hty₂)
      ls bs e₀ hw hnl (h1.standard hΓ hte₀) rfl
  exact ⟨ls', as', hred⟩

end VEnv

/-! ## From `VEnv.RuleFreeHead` to `PatFreeHead`, at the canonical pattern table

`Params.Pat` is an abstract field, so `PatFreeHead` is not literally `RuleFreeHead`.  For the
canonical table `Lean4Lean.Pat env` (`Theory/Typing/PatternRules.lean`) — the one
`VEnv.paramsOfWF` installs — every registered pattern's head constant is the head constant of
a rule's left-hand side, so the two coincide. -/

theorem VExpr.headConst?_mkLams : ∀ (As : List VExpr) (b : VExpr),
    (VExpr.mkLams As b).headConst? = b.headConst?
  | [], _ => rfl
  | _ :: As, b => VExpr.headConst?_mkLams As b

@[simp] theorem Pattern.headConst_varN (p : Pattern) :
    ∀ n, (p.varN n).headConst = p.headConst
  | 0 => rfl
  | n+1 => Pattern.headConst_varN p n

/-- Every pattern the canonical table registers has the head constant of a rule of `env`. -/
theorem Pat.headConst_defeqs {env : VEnv} {p : Pattern} {r : p.RHS × p.Check}
    (h : Pat env p r) :
    ∃ df, env.defeqs df ∧ VExpr.headConst? df.lhs = some p.headConst := by
  cases h with
  | delta hv hrule => exact ⟨_, hrule, rfl⟩
  | @iota D j q T C _ _ hTj _ hrule _ _ _ =>
    refine ⟨_, hrule, ?_⟩
    rw [VInductDecl'.iotaRule, VExpr.headConst?_mkLams, VInductDecl'.iotaLhs,
      VExpr.headConst?_mkApp, VInductDecl'.getD_types hTj,
      VInductDecl'.iotaPat, SimplePattern.toPattern]
    simp [Pattern.headConst, VExpr.headConst?]
  | quot hrule _ _ => exact ⟨_, hrule, rfl⟩

/-- **`RuleFreeHead` implies `PatFreeHead`** at the canonical table. -/
theorem VEnv.RuleFreeHead.patFreeHead {env : VEnv} {U : Nat} {c : Lean.Name}
    (henv : env.WF) (hwf : VEnv.PatWF env U) (h : env.RuleFreeHead c) :
    @VEnv.PatFreeHead (VEnv.paramsOfWF henv U hwf) c := by
  intro p r hp hpc
  obtain ⟨df, hdf, hhd⟩ := Pat.headConst_defeqs hp
  exact h df hdf (hpc ▸ hhd)

/-! ## The `VEnv`-level statements

Everything above is stated relative to a `Params` instance.  `VEnv.paramsOfWF`
(`Theory/Typing/ParamsBuild.lean`) builds one from `env.WF` and `VEnv.PatWF env U` alone, so
each result below is a statement about an arbitrary well-formed environment, conditional on
`PatWF` — the single open field of `Params`. -/

namespace VEnv

/-- **(B) injectivity and (D) no-confusion at a `VEnv`**, conditional on `PatWF`. -/
theorem constApp_inv_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr}
    (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (H : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  let _inst := VEnv.paramsOfWF henv U hwf
  @VEnv.IsDefEq.constApp_inv _inst Γ c c' ls ls' as as' H.choose hΓ
    (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf)
    (IsType.not_isProof henv hΓ hty) H.choose_spec

/-- **(A) `IsDefEqU.const_forallE_inv`, proved** — modulo `PatWF`.  Same statement as
`Theory/Typing/Injectivity.lean`'s `sorry`-backed theorem. -/
theorem const_forallE_inv_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr}
    (hrigid : env.RuleFreeHead c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B) :=
  let _inst := VEnv.paramsOfWF henv U hwf
  @VEnv.IsDefEqU.constApp_forallE_false _inst Γ c ls as A B hΓ (hrigid.patFreeHead henv hwf)

/-- **(A) `IsDefEqU.const_sort_inv`, proved** — modulo `PatWF`. -/
theorem const_sort_inv_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}
    (hrigid : env.RuleFreeHead c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u) :=
  let _inst := VEnv.paramsOfWF henv U hwf
  @VEnv.IsDefEqU.constApp_sort_false _inst Γ c ls as u hΓ (hrigid.patFreeHead henv hwf)

/-- **(B) `IsDefEqU.const_app_inv`, proved** — modulo `PatWF`.  Same statement as
`Theory/Typing/Injectivity.lean`'s `sorry`-backed theorem, with `PatWF` added. -/
theorem const_app_inv_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (hrigid : env.RuleFreeHead c)
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as')) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  let r := constApp_inv_of_patWF henv U hwf hΓ hrigid hrigid hty h
  ⟨r.2.1, r.2.2⟩

/-! ### Anti-strawman: these are `Injectivity.lean`'s statements, not paraphrases

Each `Prop` below is the corresponding `Theory/Typing/Injectivity.lean` theorem's type with
every binder made explicit and **nothing else changed**; `…_holds` proves it *by* that theorem
(so it is deliberately `sorryAx`-tainted), and `…_of_patWF` proves the same `Prop` from
`PatWF`.  That the two live side by side is the check that no statement was narrowed. -/

/-- `IsDefEqU.const_app_inv`'s type. -/
def ConstAppInvStmt (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    env.IsType U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as') →
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

/-- `IsDefEqU.const_forallE_inv`'s type. -/
def ConstForallEInvStmt (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c : Lean.Name) (ls : List VLevel) (as : List VExpr) (A B : VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B)

/-- `IsDefEqU.const_sort_inv`'s type. -/
def ConstSortInvStmt (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c : Lean.Name) (ls : List VLevel) (as : List VExpr) (u : VLevel),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u)

/-- **`sorryAx`-tainted by inheritance, deliberately.** -/
theorem constAppInvStmt_holds {env : VEnv} (henv : env.WF) (U : Nat) : ConstAppInvStmt env U :=
  fun _ _ _ _ _ _ hΓ hr ht h => IsDefEqU.const_app_inv henv hΓ hr ht h

/-- **`sorryAx`-tainted by inheritance, deliberately.** -/
theorem constForallEInvStmt_holds {env : VEnv} (henv : env.WF) (U : Nat) :
    ConstForallEInvStmt env U := fun _ _ _ _ _ _ hΓ hr => IsDefEqU.const_forallE_inv henv hΓ hr

/-- **`sorryAx`-tainted by inheritance, deliberately.** -/
theorem constSortInvStmt_holds {env : VEnv} (henv : env.WF) (U : Nat) :
    ConstSortInvStmt env U := fun _ _ _ _ _ hΓ hr => IsDefEqU.const_sort_inv henv hΓ hr

theorem constAppInvStmt_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U) :
    ConstAppInvStmt env U :=
  fun _ _ _ _ _ _ hΓ hr ht h => const_app_inv_of_patWF henv U hwf hΓ hr ht h

theorem constForallEInvStmt_of_patWF {env : VEnv} (henv : env.WF) (U : Nat)
    (hwf : env.PatWF U) : ConstForallEInvStmt env U :=
  fun _ _ _ _ _ _ hΓ hr => const_forallE_inv_of_patWF henv U hwf hΓ hr

theorem constSortInvStmt_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U) :
    ConstSortInvStmt env U :=
  fun _ _ _ _ _ hΓ hr => const_sort_inv_of_patWF henv U hwf hΓ hr

end VEnv

end Lean4Lean
