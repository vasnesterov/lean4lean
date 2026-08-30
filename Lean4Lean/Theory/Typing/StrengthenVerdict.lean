import Lean4Lean.Theory.Typing.ConstVar
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Two measurements on the strengthening hole

`Theory/Typing/UniqueTyping.lean:174`'s `sorry` — equivalently `VEnv.StrengtheningTarget`
(`Theory/Typing/Strengthen.lean`), equivalently `VEnv.AxiomConservativityUninhabWF`
(`Theory/Typing/ConstVar.lean`) — is **neither proved nor refuted** here.  What this file
adds is two things the round needed and the tree did not have, both machine-checked.

## 1. A well-formed environment at which the target is a *theorem* (§2–§4)

`Strengthen.lean` §12 records `strengtheningTarget_of_allInhabited`: if every stripped entry
has an inhabitant, the substitution argument closes the target outright.  Until now no
environment was exhibited at which that hypothesis holds, so the target had **no positive
instance at all** — working rule 4's acceptance criterion was unmet on the affirmative side.

`VDecl.WF.unsafeDef` supplies one.  It typechecks a block's values in the environment that
already carries the block's own constants, so

    univInhab : ∀ (α : Sort u), α  :=  univInhab

is a well-formed step (this is `Theory/MutualDefUnsound.lean`'s mechanism, at one universe
parameter instead of zero).  In the resulting environment **every** entry of **every**
well-formed context is inhabited — `.app (.const univInhab [u]) A : A` — so the target holds
there, for every `U`, and so does every statement equivalent to it.

**This corrects a claim that has been travelling in the briefs.**  The claim is that
*"inconsistent environments make the problem easier — a closed `f : ∀ p, p` inhabits every
`Prop` entry"*.  The parenthesis does not reach the conclusion.  `∀ p : Prop, p` applies
only to entries `A` with `Γ ⊢ A : .sort .zero`, and `Strengthening1Uninhab` quantifies over
entries at **every** sort; the abstract theory has no `False.rec`, so nothing in `Theory/`
lifts such an inhabitant to an entry at a higher sort [analysis].  So
`MutualDefUnsound.selfRefDV` (`uvars = 0`, type `∀ p : Prop, p`) — and
`LogRelRowZero.loopEnv`, built from it — do **not** discharge the target.  The constant that
does is `∀ (α : Sort u), α`, which needs a universe parameter.  §4 is that version.

## 2. Why the cheapest counterexample shape collapses (§5)

`proofIrrel` is the one rule whose side condition asks for a judgement at a **fixed** sort:
it needs `Γ ⊢ p : .sort .zero`.  So it is the rule at which "what is a proposition" can
differ between `Γ` and a context extending it — `Γ' = A :: Γ` with `A = .sort .zero` makes
the *variable* `.bvar 0` a proposition, which it is not in `Γ`.  Every other rule's context
sensitivity is a typing premise at an existential type, which is where the obstruction is
already known to reduce to itself.
To exploit that one needs two `Γ`-free terms of type `.bvar 0` upstairs, and the cheapest
supply is a constant whose declared type is `.bvar 0` — which no `Ordered` environment has,
so the witness would refute `StrengtheningTarget` only as an *unqualified* predicate.

It refutes nothing: §5 shows such a constant inhabits **every inhabited type in every
context**, by one `beta` step, and therefore lands at a common proposition downstairs too,
where `proofIrrel` equates the two candidates just as well.  The attack is dead at its own
witness, and the reason is exactly `Ordered`'s "declared types are closed".

## 3. What is *not* here

The verdict.  The hole is not decided by this file and was not decided this round; see
`docs/handoff-weakn.md`.  The one thing that round found outside Lean is worth carrying:
`~/lean-type-theory/typesys.tex:88-89` (`thm:weak` (3) and (4)) **is** this statement — *if
`Γ,Δ ⊢ e ≡ e'` and `FV(e) ∪ FV(e') ⊆ Γ` then `Γ ⊢ e ≡ e'`* — and the reference proves it "by
mutual induction on the first hypothesis" (`typesys.tex:95`).  That induction does not go
through: the reference's conversion judgment has an explicit transitivity rule with an
arbitrary middle term (`axioms.tex:34`), whose free variables the hypothesis does not
constrain.  `VEnv.Strengthening.iff_trans` (`Theory/Typing/Strengthen.lean`, `sorry`-free)
is the sharp form of that observation: the `trans` case *is* the statement.

Nothing in this file mentions `IsDefEqU.weakN_iff`, and nothing in it is `sorry`-tainted.
-/

namespace Lean4Lean

open VExpr

/-! ## 2. `univInhab : ∀ (α : Sort u), α` -/

/-- The type `∀ (α : Sort u), α`, at one universe parameter. -/
def univType : VExpr := .forallE (.sort (.param 0)) (.bvar 0)

/-- `univInhab : ∀ (α : Sort u), α`. -/
def univCV : VConstVal := ⟨⟨1, univType⟩, `univInhab⟩

/-- The same, as a definition whose value is the constant it defines — the `unsafeDef`
shape of `Theory/MutualDefUnsound.lean`, at one universe parameter. -/
def univDV : VDefVal := ⟨univCV, .const `univInhab [.param 0]⟩

theorem univType_isType (env : VEnv) : env.IsType 1 [] univType :=
  ⟨_, VEnv.IsDefEq.forallEDF (u := .succ (.param 0)) (v := .param 0)
    (.sortDF (by exact Nat.zero_lt_one) (by exact Nat.zero_lt_one) rfl)
    (.bvar .zero)⟩

/-- **The universal inhabitant.**  In any environment declaring `univInhab`, every type that is
typed at a sort is inhabited, in every context. -/
theorem hasType_univInhab_app {env : VEnv} {U : Nat} {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hc : env.constants `univInhab = some ⟨1, univType⟩) (hu : u.WF U)
    (hA : env.HasType U Γ A (.sort u)) :
    env.HasType U Γ (.app (.const `univInhab [u]) A) A := by
  have hconst : env.HasType U Γ (.const `univInhab [u]) (.forallE (.sort u) (.bvar 0)) := by
    have h := VEnv.IsDefEq.constDF (Γ := Γ) (uvars := U) (ci := ⟨1, univType⟩)
      (ls := [u]) (ls' := [u]) hc (by simpa using hu) (by simpa using hu) rfl
      (List.Forall₂.rfl fun _ _ => rfl)
    simpa [VEnv.HasType, univType, VExpr.instL, VLevel.inst] using h
  have h := VEnv.IsDefEq.appDF hconst hA
  simpa [VEnv.HasType, VExpr.inst] using h

/-! ## 3. Level well-formedness of a well-formed context -/

theorem onCtx_levelWF {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → OnCtx Γ (fun _ A => A.LevelWF U)
  | [], _ => trivial
  | _::_, ⟨h1, _, h2⟩ =>
    ⟨onCtx_levelWF h1, (VEnv.IsDefEq.levelWF h2 (onCtx_levelWF h1)).1⟩

/-! ## 4. The target holds at every environment declaring `univInhab` -/

/-- **A positive instance of the hole.**  Every well-formed environment that declares
`univInhab : ∀ (α : Sort u), α` satisfies the strengthening target, at every `U`. -/
theorem strengtheningTarget_of_univInhab {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (hc : env.constants `univInhab = some ⟨1, univType⟩) : VEnv.StrengtheningTarget env U := by
  refine VEnv.Strengthening1.target henv fun {k Γ Γ' e1 e2} W _ hΓ' h => ?_
  obtain ⟨Γ₀, A₀, hI, hΓ₀, u, hA₀⟩ := W.exists_instN_typed henv.ordered hΓ'
  have hu : u.WF U := (VEnv.IsDefEq.levelWF hA₀ (onCtx_levelWF hΓ₀)).2.2
  exact VEnv.IsDefEqU.strengthen_of_instN henv.ordered (hI _) (hasType_univInhab_app hc hu hA₀) h

/-- The `unsafeDef` step declaring `univInhab` is well formed over any environment in which the
name is free. -/
theorem univInhabDecl_wf {env env' : VEnv} (h : env.addConst `univInhab ⟨1, univType⟩ = some env') :
    VDecl.WF env (.unsafeDef [univDV]) (env'.addDefEqs [univDV]) := by
  have hcs : env'.constants `univInhab = some ⟨1, univType⟩ := by
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp
  refine .unsafeDef (fun ci hci ↦ ?_) ?_ (fun ci hci ↦ ?_)
  · simp only [List.mem_singleton] at hci; subst hci; exact univType_isType _
  · show (VEnv.addConst env `univInhab ⟨1, univType⟩).bind _ = _
    rw [h]; rfl
  · simp only [List.mem_singleton] at hci; subst hci
    show env'.HasType 1 [] (.const `univInhab [.param 0]) univType
    have h := VEnv.IsDefEq.constDF (Γ := []) (uvars := 1) (ci := ⟨1, univType⟩)
      (ls := [.param 0]) (ls' := [.param 0]) hcs (by simp [VLevel.WF]) (by simp [VLevel.WF]) rfl
      (List.Forall₂.rfl fun _ _ => rfl)
    simpa [VEnv.HasType, univType, VExpr.instL, VLevel.inst] using h

/-- **The witness environment exists and is well formed.** -/
theorem exists_univInhabEnv : ∃ env : VEnv, VEnv.WF env ∧ ∀ U, VEnv.StrengtheningTarget env U := by
  obtain ⟨env', h⟩ : ∃ env', VEnv.empty.addConst `univInhab ⟨1, univType⟩ = some env' :=
    ⟨_, rfl⟩
  have hcs : env'.constants `univInhab = some ⟨1, univType⟩ := by
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp
  refine ⟨env'.addDefEqs [univDV], ⟨_, .decl (univInhabDecl_wf h) .empty⟩, fun U => ?_⟩
  refine strengtheningTarget_of_univInhab ⟨_, .decl (univInhabDecl_wf h) .empty⟩ ?_
  simpa [VEnv.addDefEqs, VEnv.addDefEq] using hcs

/-- **The scope of the witness, stated exactly.**  At any environment declaring `univInhab`, the
uninhabitedness hypothesis of `Strengthening1Uninhab` is satisfiable at *no* well-formed
context: every entry has an inhabitant.  So §4's positive instance lives entirely inside the
case `Strengthen.lean` §1 already closes, and it tests **nothing** about the hard case.  It
is a satisfiability witness for the target, not evidence about the obstruction.  (Working
rule 5's collapse test, applied to this file's own witness.) -/
theorem univInhab_no_uninhabited_entry {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr}
    (henv : VEnv.WF env) (hc : env.constants `univInhab = some ⟨1, univType⟩)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    ¬ (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) := by
  intro hemp
  obtain ⟨Γ₀, A₀, hI, hΓ₀, u, hA₀⟩ := W.exists_instN_typed henv.ordered hΓ'
  have hu : u.WF U := (VEnv.IsDefEq.levelWF hA₀ (onCtx_levelWF hΓ₀)).2.2
  exact hemp Γ₀ A₀ _ (hI _) (hasType_univInhab_app hc hu hA₀)

/-- The same, transported through `ConstVar.lean`'s equivalence: at that environment,
*adding an axiom with no inhabitant is conservative* is a theorem. -/
theorem exists_univInhabEnv_axiomConservativity :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U, VEnv.AxiomConservativityUninhabWF env U := by
  obtain ⟨env, henv, h⟩ := exists_univInhabEnv
  exact ⟨env, henv, fun U => (VEnv.axiomConservativityUninhabWF_iff_target henv).2 (h U)⟩

/-! ## 5. The cheapest counterexample shape, and its collapse -/

/-- **A constant whose declared type is an open variable inhabits every inhabited type.**
One `beta` step: `(fun (_ : A) => c) e` has type `e` when `e : A`, and reduces to `c`.
This is what `Ordered`'s "declared types are closed" excludes, and it is why the
`proofIrrel`-at-a-variable-`Prop` counterexample cannot be built from such a constant. -/
theorem constOpenType_hasType_any {env : VEnv} {U : Nat} {Γ : List VExpr} {c : Lean.Name}
    {A e : VExpr} (hc : env.constants c = some ⟨0, .bvar 0⟩)
    (he : env.HasType U Γ e A) : env.HasType U Γ (.const c []) e := by
  have hbody : env.HasType U (A::Γ) (.const c []) (.bvar 0) := by
    have h := VEnv.IsDefEq.constDF (Γ := A::Γ) (uvars := U) (ci := ⟨0, .bvar 0⟩)
      (ls := []) (ls' := []) hc nofun nofun rfl .nil
    simpa [VEnv.HasType, VExpr.instL] using h
  have h := VEnv.IsDefEq.beta hbody he
  simpa [VExpr.inst] using h.hasType.2

/-- `∀ (p : Prop), p` is a proposition, in every environment and context. -/
theorem allProp_isProp {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) := by
  refine VEnv.IsDefEq.defeqDF (u := .succ (.imax (.succ .zero) .zero))
    (.sortDF ⟨trivial, trivial⟩ trivial ?_) (VEnv.IsDefEq.forallEDF
      (u := .succ .zero) (v := .zero) (.sortDF trivial trivial rfl) (.bvar .zero))
  funext ls; simp [VLevel.eval, Lean.Nat.imax]

/-- **The collapse.**  Two constants of the open type `.bvar 0` are *already* convertible in
the empty context, so the `proofIrrel`-at-a-variable-`Prop` witness separates nothing: it
fires downstairs as well as upstairs.  (Working rule 2: the attack is killed at its own
witness.) -/
theorem constOpenType_collapse {env : VEnv} {U : Nat} {c₁ c₂ : Lean.Name}
    (h₁ : env.constants c₁ = some ⟨0, .bvar 0⟩)
    (h₂ : env.constants c₂ = some ⟨0, .bvar 0⟩) :
    env.IsDefEqU U [] (.const c₁ []) (.const c₂ []) :=
  ⟨_, .proofIrrel allProp_isProp
    (constOpenType_hasType_any h₁ allProp_isProp)
    (constOpenType_hasType_any h₂ allProp_isProp)⟩

end Lean4Lean
