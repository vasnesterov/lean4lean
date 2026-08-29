import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Inverting a saturated application — the `HasArgs` half of ledger row B7

`VEnv.HasType.mkApp'` (`Theory/Inductive/Lemmas.lean`) is the *forward* direction: a
function of `mkPi As B` type applied to a spine `as` that instantiates `As` has type
`instAll B as`.  Every consumer that has to *read a spine back* wants the converse, and
until this file it existed nowhere in the tree — not as a proof, not as a statement.

**Who wants it.**  `VEnv.PatWF`'s ι and quotient cases (`Theory/Typing/ParamsBuild.lean`),
the one open field of `VEnv.Params`.  The route there is: `IsDefEq.extra` fires the ι-rule
as `mkLams Δ L ≡ mkLams Δ R`; instantiating that at the matched spine is
`IsDefEq.extra_applied` (`Theory/Inductive/StructureClosed.lean`), whose *only* hypothesis
`PatWF` cannot discharge is `HasArgs U Γ Δ as` — because all `PatWF` holds about the
matched term is `HasType U Γ e A`, with `A` and the spine's own domains existentially
quantified by `HasType.app_inv`.  `HasArgs.of_mkApp` is exactly the bridge.  The same gap is
reported independently at `Verify/Typing/Expr.lean:85–99` for a different consumer.

**Cost, stated honestly.**  This is *not* `sorry`-free: it uses `IsDefEqU.forallE_inv`
(`Theory/Typing/Injectivity.lean`, open) and `IsDefEq.uniqU`.  It is worth landing anyway,
because it converts "the ι case of `pat_wf` needs Π-injectivity somewhere in a 400-line
argument" into "the ι case of `pat_wf` needs `HasArgs.of_mkApp`, which needs Π-injectivity
and nothing else".  The reduction is the deliverable; the taint is inherited, not new.

**Where the Π-injectivity is used, exactly**: one call, in the `cons` case, to reconcile the
domain `A₀'` that `HasType.app_inv` invents for the head with the domain `A₀` the telescope
declares.  Nothing else in the induction needs it.
-/

namespace Lean4Lean
namespace VEnv

open VExpr (mkPi mkApp instTele instAll)

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- **The head of a typed application spine is typed.**  Pure `app_inv` iteration; no
injectivity, no uniqueness. -/
theorem HasType.mkApp_head (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (as : List VExpr) (f A : VExpr),
      env.HasType U Γ (f.mkApp as) A → ∃ T, env.HasType U Γ f T := by
  intro as
  induction as with
  | nil => exact fun f A h => ⟨A, h⟩
  | cons a as ih =>
    intro f A h
    rw [VExpr.mkApp_cons] at h
    obtain ⟨T, hT⟩ := ih _ _ h
    obtain ⟨A₀, B₀, hf, -⟩ := HasType.app_inv henv hΓ hT
    exact ⟨_, hf⟩

/-- The first argument of a typed application spine is typed, at *some* domain — the
existential that `HasArgs.of_mkApp` then has to pin to the declared one. -/
theorem HasType.mkApp_arg (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (as : List VExpr) {f a A} (h : env.HasType U Γ ((f.app a).mkApp as) A) :
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀ :=
  let ⟨_, hT⟩ := HasType.mkApp_head henv hΓ as _ _ h
  HasType.app_inv henv hΓ hT

/-- **Ledger row B7, inverse direction.**  A spine that saturates a `mkPi` telescope and is
well typed *is* a `HasArgs` instantiation of that telescope.

The length hypothesis is not derivable: `f.mkApp as` can be typed with `as` shorter than
`As` (a partial application) or longer (if `B` is itself a Π).

The induction is on the **spine**, not on the telescope: the recursive call is about
`instTele a As`, which is a different list of the same length, so an induction on `As` has
no usable hypothesis there. -/
theorem HasArgs.of_mkApp (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (as : List VExpr) {As f B A}, as.length = As.length →
      env.HasType U Γ f (mkPi As B) → env.HasType U Γ (f.mkApp as) A →
      env.HasArgs U Γ As as := by
  intro as
  induction as with
  | nil =>
    intro As f B A hlen _ _
    cases List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | cons a as ih =>
    intro As f B A hlen hf h
    match As, hlen with
    | A₀ :: As, hlen =>
      rw [VExpr.mkPi_cons] at hf
      rw [VExpr.mkApp_cons] at h
      obtain ⟨A₀', B₀', hf', ha'⟩ := HasType.mkApp_arg henv.ordered hΓ as h
      obtain ⟨⟨_, hAA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ (hf'.uniqU henv hΓ hf)
      have ha : env.HasType U Γ a A₀ := HasType.defeqU_r henv hΓ ⟨_, hAA⟩ ha'
      have h1 := hf.app ha
      rw [VExpr.inst_mkPi_zero] at h1
      refine .cons ha (ih ?_ h1 h)
      simpa using Nat.succ.inj hlen

/-- **Ledger row B7's inverse, as the ledger states it.**  `Γ ⊢ f.mkApp as : T` forces
`T ≡ B[as]`, and hands back the `HasArgs` witness on the way. -/
theorem HasType.mkApp_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {As as f B A : _} (hlen : as.length = As.length)
    (hf : env.HasType U Γ f (mkPi As B)) (h : env.HasType U Γ (f.mkApp as) A) :
    env.HasArgs U Γ As as ∧ env.IsDefEqU U Γ A (instAll B as) :=
  have has := HasArgs.of_mkApp henv hΓ as hlen hf h
  ⟨has, h.uniqU henv hΓ (HasType.mkApp' has hf)⟩

/-! ## Non-vacuity

`of_mkApp`'s five hypotheses are jointly satisfiable at a spine that really applies
something, in **every** `VEnv.WF` environment and at every universe count: the witness lives
entirely in the context, so it needs no constant.  Without this the lemma could be true for
the uninteresting reason that nothing satisfies its premises — the failure mode that made
`Experimental/Reflect/Capstone.lean` worthless. -/

variable! (henv : env.WF) in
theorem HasArgs.of_mkApp_fires :
    env.HasArgs U [.sort .zero] [.sort .zero] [.bvar 0] := by
  have hΓ : OnCtx [(VExpr.sort .zero)] (env.IsType U) := ⟨trivial, _, HasType.sort trivial⟩
  have hb : env.HasType U [(VExpr.sort .zero)] (.bvar 0) (.sort .zero) := HasType.bvar .zero
  have hf : env.HasType U [(VExpr.sort .zero)]
      (.lam (.sort .zero) (.bvar 0)) (VExpr.mkPi [.sort .zero] (.sort .zero)) :=
    HasType.lam (HasType.sort trivial) (HasType.bvar .zero)
  exact HasArgs.of_mkApp henv hΓ [.bvar 0] rfl hf (hf.app hb)

end VEnv
end Lean4Lean
