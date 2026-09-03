import Lean4Lean.Theory.Typing.ShapeIndepFresh
import Lean4Lean.Theory.Typing.InjSpineTransport

/-!
# The injectivity corner: hole B's negative conjuncts are **context-free**

`Injectivity.lean` carries two of the tree's thirteen holes:

* **hole A**, `IsDefEqU.forallE_inv_stratified` (`Injectivity.lean:261`, the `sorry` on line
  268) — stratified Π-injectivity;
* **hole B**, `WF.rigidShapeUniqNS` (`Injectivity.lean:1046`) — the eight-entry rigid-shape
  bridge.

`RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes hole B into exactly five conjuncts,
and `InjSortPiModel.lean` classifies them by *polarity*:

| conjunct | polarity |
|---|---|
| `PiInv` | positive |
| `RigidConstAppInv` | positive |
| `RigidSortPiDisj` | negative |
| `RigidConstPiDisj` | negative |
| `RigidConstSortDisj` | negative |

**This file adds a second axis to that table, and the two agree.**  The three *negative*
conjuncts are equivalent — over the family of `VEnv.WF` environments — to their restrictions to
the **empty context**; the two *positive* ones are not, and the obstruction is a named open
node rather than a gap in effort.

## The move

`ShapeIndepStep.axiomize_step` replaces the outermost context entry by a fresh axiom, shortening
the context by one and enlarging the environment by one constant.  A judgement transports
*forward* along it (`IsDefEqU.mono` then `IsDefEqU.instN`).  A negative conjunct is a
**hypothesis** `env.IsDefEqU U Γ e₁ e₂` and a conclusion `False`, so forward transport is the
right direction: push the hypothesis down to the empty context and appeal there.  Both shapes
that occur — `.sort u` and `.forallE A B` — are stable under `VExpr.inst` (`.sort` literally, by
`VExpr.inst`'s second clause; `.forallE` up to instantiating its two components), and so is a
constant-headed spine (`VExpr.mkApp_inst`, plus `.const`'s clause), with rule-freeness carried
by `axiomize_step`'s own `∀ c', env.RuleFreeHead c' → env'.RuleFreeHead c'`.  So nothing here
needs to know anything about the shapes beyond that they are closed-headed.

This is `ShapeIndep.spineVarPiDisj_of_constPiDisj`'s induction with the `spineHead` analysis
deleted: that proof needed a case split on whether the axiomized variable *was* the spine head,
and none of the three statements here has a variable head to begin with.

## Why the positive conjuncts do not follow

`PiInv` and `RigidConstAppInv` conclude with a *conversion in `Γ`*.  Forward transport gives it
in `Γ'` over `env'`, and pulling it back needs two things this tree does not have:

1. **anti-substitution** — from `env.IsDefEqU U Γ' (A.inst a k) (A'.inst a k)` to
   `env.IsDefEqU U Γ A A'`; the tree's inversion of a context operation is
   `UniqueTyping.IsDefEqU.weakN_iff`, which is itself one of the thirteen holes;
2. **axiom conservativity** — from a judgement over `env'` (one constant richer) to one over
   `env`.  `ShapeIndep.lean`'s module docstring names this node for the sibling reason that
   `¬ IsProof` transports backwards; in the tree it is `VEnv.AxiomConservativityWF`
   (`Theory/Typing/ConstVar.lean`) and `VEnv.AxiomConservativity`
   (`Theory/Typing/StrengthenAxiom.lean`), both `Prop`s with no unconditional inhabitant.

`RigidConstAppInv` is blocked twice over: its `¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as)`
*hypothesis* is itself negative-in-the-wrong-place and transports backwards, not forwards.

So the polarity split is not an artefact of how the five conjuncts happen to be phrased; it is
the direction the only context-elimination tool in the tree runs in. **[analysis]**

## What this is worth, stated exactly

It is a narrowing of the **statement** of three of hole B's five conjuncts, not of the work in
any route that is currently live.  Two concrete consequences:

* `InjSortPiModel.lean` item 4 (`interpCtx_vFalse`, `not_sortPiEqSupply`) shows every semantic
  route into this corner owes a valuation `ρ ∈ interpCtx M L Γ`, and that the obligation is
  **unsatisfiable** at `Γ = [∀ p : Prop, p]` in every model the tree has.  At the empty context
  it is satisfiable — that file's own `empty_ctx_has_valuation` supplies it.  So the
  context-free form of `RigidSortPiDisj` is not subject to item 4's blindness, and the model's
  residual for it drops to `SetModel.sound`'s deferred inputs alone. **[analysis: the
  composition is not built here, because doing so would re-import the `PropSplit` layer into
  `Theory/Typing`; the two halves — `sortPiDisjNil` here, `empty_ctx_has_valuation` there — are
  both hole-free.]**
* It does **not** move any census number, and it is **not** a reduction at a *fixed*
  environment.  `axiomize_step` enlarges the environment, so the hypothesis of every theorem in
  §2 quantifies over `VEnv.WF` environments, exactly as `ShapeIndep.lean`'s rows do.  §3's
  `sortPiDisjNil_of_rigidSortPiDisj` and friends make each pair an `↔` in that quantified form,
  which is the receipt that no direction of it is left open.
-/

namespace Lean4Lean
namespace VEnv

open Lean (Name)

variable {U : Nat}

/-! ## §1 The three closed-context forms

Each is its `RigidNodeCircle` conjunct with `Γ` set to `[]`; the `OnCtx` guard disappears with
it, since `OnCtx [] P` is `True`. -/

/-- `RigidSortPiDisj` at the empty context. -/
def SortPiDisjNil (env : VEnv) (U : Nat) : Prop :=
  ∀ {u : VLevel} {A B : VExpr}, ¬ env.IsDefEqU U [] (.sort u) (.forallE A B)

/-- `RigidConstPiDisj` at the empty context. -/
def ConstPiDisjNil (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr}, env.RuleFreeHead c →
    ¬ env.IsDefEqU U [] ((VExpr.const c ls).mkApp as) (.forallE A B)

/-- `RigidConstSortDisj` at the empty context. -/
def ConstSortDisjNil (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}, env.RuleFreeHead c →
    ¬ env.IsDefEqU U [] ((VExpr.const c ls).mkApp as) (.sort u)

/-! ## §2 Context elimination

One induction per conjunct, on the length of the context.  All three are the same proof; the
differences are which `VExpr.inst` clauses fire on the two endpoints. -/

/-- **`RigidSortPiDisj` is context-free.**  Given the empty-context form at every `VEnv.WF`
environment, the full conjunct holds at every `VEnv.WF` environment.

The hypothesis must range over environments because `axiomize_step` adds a constant at every
step; that is the same shape `ShapeIndep.spineVarPiDisj_of_constPiDisj` takes, and for the same
reason. -/
theorem rigidSortPiDisj_of_nil (hfresh : FreshNames)
    (H : ∀ env : VEnv, env.WF → SortPiDisjNil env U) :
    ∀ env : VEnv, env.WF → env.RigidSortPiDisj U := by
  suffices h : ∀ (n : Nat) (env : VEnv), env.WF → ∀ Γ : List VExpr, Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (u : VLevel) (A B : VExpr),
        ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B) by
    intro env henv Γ u A B hΓ hc
    exact h Γ.length env henv Γ rfl hΓ u A B hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ u A B hc
    cases List.length_eq_zero_iff.1 hn
    exact H env henv hc
  | succ n ih =>
    intro env henv Γ hn hΓ u A B hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨c, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', -, -, hct, W⟩ := axiomize_step henv hΓ hcfr
    have hc' := IsDefEqU.instN henv'.ordered W (hc.mono hle) hct
    exact ih env' henv' Γ' (hlen.trans hn') hΓ' u _ _ hc'

/-- **`RigidConstPiDisj` is context-free.**  Same induction; `VExpr.mkApp_inst` and `.const`'s
`VExpr.inst` clause keep the head, and `axiomize_step` carries rule-freeness forward. -/
theorem rigidConstPiDisj_of_nil (hfresh : FreshNames)
    (H : ∀ env : VEnv, env.WF → ConstPiDisjNil env U) :
    ∀ env : VEnv, env.WF → env.RigidConstPiDisj U := by
  suffices h : ∀ (n : Nat) (env : VEnv), env.WF → ∀ Γ : List VExpr, Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (c : Name) (ls : List VLevel) (as : List VExpr) (A B : VExpr),
        env.RuleFreeHead c → ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B) by
    intro env henv Γ c ls as A B hΓ hrf hc
    exact h Γ.length env henv Γ rfl hΓ c ls as A B hrf hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ c ls as A B hrf hc
    cases List.length_eq_zero_iff.1 hn
    exact H env henv hrf hc
  | succ n ih =>
    intro env henv Γ hn hΓ c ls as A B hrf hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨c₀, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', -, hrf', hct, W⟩ := axiomize_step henv hΓ hcfr
    have hc' := IsDefEqU.instN henv'.ordered W (hc.mono hle) hct
    rw [VExpr.mkApp_inst] at hc'
    exact ih env' henv' Γ' (hlen.trans hn') hΓ' c ls _ _ _ (hrf' _ hrf) hc'

/-- **`RigidConstSortDisj` is context-free.**  Same induction again. -/
theorem rigidConstSortDisj_of_nil (hfresh : FreshNames)
    (H : ∀ env : VEnv, env.WF → ConstSortDisjNil env U) :
    ∀ env : VEnv, env.WF → env.RigidConstSortDisj U := by
  suffices h : ∀ (n : Nat) (env : VEnv), env.WF → ∀ Γ : List VExpr, Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (c : Name) (ls : List VLevel) (as : List VExpr) (u : VLevel),
        env.RuleFreeHead c → ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u) by
    intro env henv Γ c ls as u hΓ hrf hc
    exact h Γ.length env henv Γ rfl hΓ c ls as u hrf hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ c ls as u hrf hc
    cases List.length_eq_zero_iff.1 hn
    exact H env henv hrf hc
  | succ n ih =>
    intro env henv Γ hn hΓ c ls as u hrf hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨c₀, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', -, hrf', hct, W⟩ := axiomize_step henv hΓ hcfr
    have hc' := IsDefEqU.instN henv'.ordered W (hc.mono hle) hct
    rw [VExpr.mkApp_inst] at hc'
    exact ih env' henv' Γ' (hlen.trans hn') hΓ' c ls _ u (hrf' _ hrf) hc'


/-! ## §3 The converses, and the three equivalences with no side condition

`VEnv.freshNames` (`ShapeIndepFresh.lean`, hole-free) discharges `FreshNames`, so each pair is
an `↔` outright.  This is the receipt asked for by `docs/vacuity-ledger.md` §0's "state the
equivalence so no successor re-attacks the open direction": neither direction of any of the
three is left open. -/

/-- The empty context is a context. -/
theorem RigidSortPiDisj.nil {env : VEnv} (h : env.RigidSortPiDisj U) : SortPiDisjNil env U :=
  fun hc => h (Γ := []) trivial hc

@[inherit_doc RigidSortPiDisj.nil]
theorem RigidConstPiDisj.nil {env : VEnv} (h : env.RigidConstPiDisj U) : ConstPiDisjNil env U :=
  fun hrf hc => h (Γ := []) trivial hrf hc

@[inherit_doc RigidSortPiDisj.nil]
theorem RigidConstSortDisj.nil {env : VEnv} (h : env.RigidConstSortDisj U) :
    ConstSortDisjNil env U := fun hrf hc => h (Γ := []) trivial hrf hc

/-- **`RigidSortPiDisj` is exactly its empty-context restriction**, over the family of
`VEnv.WF` environments.  `sorryAx`-free. -/
theorem rigidSortPiDisj_iff_nil :
    (∀ env : VEnv, env.WF → env.RigidSortPiDisj U) ↔
      (∀ env : VEnv, env.WF → SortPiDisjNil env U) :=
  ⟨fun H env henv => RigidSortPiDisj.nil (H env henv), rigidSortPiDisj_of_nil freshNames⟩

@[inherit_doc rigidSortPiDisj_iff_nil]
theorem rigidConstPiDisj_iff_nil :
    (∀ env : VEnv, env.WF → env.RigidConstPiDisj U) ↔
      (∀ env : VEnv, env.WF → ConstPiDisjNil env U) :=
  ⟨fun H env henv => RigidConstPiDisj.nil (H env henv), rigidConstPiDisj_of_nil freshNames⟩

@[inherit_doc rigidSortPiDisj_iff_nil]
theorem rigidConstSortDisj_iff_nil :
    (∀ env : VEnv, env.WF → env.RigidConstSortDisj U) ↔
      (∀ env : VEnv, env.WF → ConstSortDisjNil env U) :=
  ⟨fun H env henv => RigidConstSortDisj.nil (H env henv), rigidConstSortDisj_of_nil freshNames⟩

/-! ## §4 Hole B, restated with its negative conjuncts in the empty context

Composing §2 with `InjSpineTransport.rigidShapeUniqNS_of_family_convStep2`.  The result is
`Injectivity.WF.rigidShapeUniqNS` — hole B — from six inputs, three of which mention no context
at all. -/

/-- **Hole B from six inputs, three of them context-free.**  `sorryAx`-free: every input is a
hypothesis.

Read against `InjSpineTransport.rigidShapeUniqNS_of_family_convStep2`, which this composes with:
the change is that `RigidSortPiDisj`, `RigidConstPiDisj` and `RigidConstSortDisj` are replaced by
their empty-context restrictions, and `hpi`/`hca`/`hcs2` are not, because §3 of the module
docstring says they cannot be. -/
theorem rigidShapeUniqNS_of_nilFamily
    (hpi : ∀ env : VEnv, env.WF → env.PiInv U)
    (hca : ∀ env : VEnv, env.WF → env.RigidConstAppInv U)
    (hcs2 : ∀ env : VEnv, env.WF → ConvStep2 env U)
    (hsp : ∀ env : VEnv, env.WF → SortPiDisjNil env U)
    (hcp : ∀ env : VEnv, env.WF → ConstPiDisjNil env U)
    (hcsd : ∀ env : VEnv, env.WF → ConstSortDisjNil env U) :
    ∀ env : VEnv, env.WF → env.RigidShapeUniqNS U := fun env henv =>
  rigidShapeUniqNS_of_family_convStep2 henv.ordered (hcs2 env henv) (hpi env henv)
    (rigidSortPiDisj_of_nil freshNames hsp env henv) (hca env henv)
    (rigidConstPiDisj_of_nil freshNames hcp env henv)
    (rigidConstSortDisj_of_nil freshNames hcsd env henv)

/-! ## §5 Controls

The failure mode this corner has produced repeatedly is a restriction that compiles, prints a
clean axiom line, and is free at the restricted instances.  The one that would apply here is
specific and worth naming: `ShapeIndep.lean`'s induction has a **free base case** — its two
`SpineVar.spineVarPiDisj_nil` / `spineVarSortDisj_nil` appeals close the empty-context instance
outright, because a closed term cannot have a `.bvar` spine head.  If the same were true of the
three statements here, §2 would be a proof and not a reduction, and the fact that it is not a
proof would be evidence of nothing.

**It is not true of them, and here is the witness.**  Both endpoints of the sort/Π statement are
*closed* and both are typeable in the empty context, over **every** environment — no `VEnv.WF`,
no constant.  So the empty-context instance of `SortPiDisjNil` has content, and §2 is a genuine
restriction rather than a disguised discharge. -/

section Controls
variable {env : VEnv}

/-- **The base case is not free.**  Contrast `SpineVar.spineVarPiDisj_nil`, which closes the
empty-context instance of the variable-spine row outright.  Nothing analogous is available here:
`.sort .zero` and `.forallE (.sort .zero) (.sort .zero)` are both closed, both typeable at `[]`,
and their disjointness at `[]` is exactly what §2 leaves open.  Holds over every environment;
`sorryAx`-free. -/
theorem nil_endpoints_typeable :
    env.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) ∧
    env.HasType 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  have hz : (VLevel.zero).WF 0 := trivial
  ⟨.sortDF hz hz rfl, .forallEDF (.sortDF hz hz rfl) (.sortDF hz hz rfl)⟩

/-- **…and the restriction is genuinely a restriction**: `SortPiDisjNil` mentions no context, so
at a *fixed* environment it is a single instance of `RigidSortPiDisj` and strictly weaker as a
statement.  What §2 buys back is the quantification over environments — `axiomize_step` adds one
constant per context entry — which is why `rigidSortPiDisj_iff_nil` is stated in the
`∀ env, env.WF → …` form and not at a fixed `env`.  This direction is the free one. -/
theorem nil_is_an_instance (h : env.RigidSortPiDisj U) {u : VLevel} {A B : VExpr} :
    ¬ env.IsDefEqU U [] (.sort u) (.forallE A B) := RigidSortPiDisj.nil h

end Controls

/-! ## §6 Axiom check

    #print axioms Lean4Lean.VEnv.rigidSortPiDisj_of_nil
    #print axioms Lean4Lean.VEnv.rigidConstPiDisj_of_nil
    #print axioms Lean4Lean.VEnv.rigidConstSortDisj_of_nil
    #print axioms Lean4Lean.VEnv.rigidSortPiDisj_iff_nil
    #print axioms Lean4Lean.VEnv.rigidConstPiDisj_iff_nil
    #print axioms Lean4Lean.VEnv.rigidConstSortDisj_iff_nil
    #print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_nilFamily
    #print axioms Lean4Lean.VEnv.nil_endpoints_typeable
-/

section Audit
#print axioms Lean4Lean.VEnv.rigidSortPiDisj_of_nil
#print axioms Lean4Lean.VEnv.rigidConstPiDisj_of_nil
#print axioms Lean4Lean.VEnv.rigidConstSortDisj_of_nil
#print axioms Lean4Lean.VEnv.rigidSortPiDisj_iff_nil
#print axioms Lean4Lean.VEnv.rigidConstPiDisj_iff_nil
#print axioms Lean4Lean.VEnv.rigidConstSortDisj_iff_nil
#print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_nilFamily
#print axioms Lean4Lean.VEnv.nil_endpoints_typeable
end Audit

end VEnv
end Lean4Lean
