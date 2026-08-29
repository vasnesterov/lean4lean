import Lean4Lean.Theory.Typing.HeadReduction
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Verify.Typing.ProjLevelWitness

/-!
# Fact (C), rigidity — stated

`Theory/Typing/Injectivity.lean`'s taxonomy names three different facts about constant
applications and says of the third:

> **(C) Rigidity** — a term definitionally equal to a constant application reduces to one with
> the same head, so its components can be read back in the smaller context.  Consumer:
> `TrProj.weak'_inv`.  **Deliberately not stated here.**  Its only faithful formulation
> mentions weak-head reduction, which lives in `Theory/Typing/HeadReduction.lean` — downstream
> of this file and gated on `Params`.  Writing a reduction-free approximation is how one gets a
> fourth wrong statement; it should be stated where the reduction relation is in scope.

This file is that place.  It sits in `Verify/` rather than in `Theory/Typing/` only because
`Theory/Typing/{Injectivity,ChurchRosser}.lean` belong to another stream; nothing here depends
on `Verify/`, so it can be moved verbatim once that stream is idle.

## The statement, and the two things it is *not*

`ConstRigid` below says: a term definitionally equal to a **rule-free-headed** constant
application, whose common type is a genuine type, weak-head reduces to a constant application
**with that same head**.  Nothing about the levels, nothing about the arguments.

* It is not **(A) disjointness** (`const_forallE_inv`, `const_sort_inv`): those say a const
  application is not a Π and not a sort.  (C)'s conclusion is about the *left* side.
* It is not **(B) injectivity** (`const_app_inv`): (B) relates two const applications with the
  same head; here only one side is a const application, which is exactly why
  `TrProj.weak'_inv`'s docstring's earlier diagnosis ("`const_app_inv`") was wrong.

## Why the two side conditions

Both are transcribed from (B)'s, whose necessity is machine-checked in
`Theory/Typing/ConstInvWitness.lean`, and both survive the transcription:

* `RuleFreeHead c`.  Without it `c` may head a δ- or ι-rule and the *right* side reduces,
  so no claim about the left side's normal form can hold.
* `IsType` on the const application.  Without it `IsDefEq.proofIrrel` identifies any two
  inhabitants of a proposition **with no rule in the environment at all** — `w2` there.  With
  it, `proofIrrel` cannot fire at the top: it would need the common type `.sort u` to itself be
  a proposition, i.e. `.succ u ≈ .zero`.
* `OnCtx Γ` is not decoration: `Params.pat_wf`'s docstring records that a rule stated about an
  arbitrary `Γ` with no well-formedness hypothesis "should be treated as suspect by default" on
  this development.

## What the consumer actually needs — corrected

`TrProj.weak'_inv`'s docstring traces its route to "concluding that `B₀` has the form
`(.const S us).mkApp (ps' ++ ιs')`", and names (C) as the residual.  Tracing it one step
further, the residual is **three** things, not one:

1. **(C)**, this statement, at `Γ'`, followed by `WHRed.weakU_inv`
   (`HeadReduction.lean:89`) to move the reduction into `Γ` — that lemma is *already proved*
   and is in exactly the `Ctx.Lift'` form `weak'_inv` is stated over.
2. **(B)'s level half**: `TrProj`'s F17 clause is stated at the *use site's* `us`, so a
   recovered head `(.const S us').mkApp as'` is useless unless `us' ≈ us`.  (C) is head-only by
   design, so this is a second, separate ask, and the docstring did not record it.
3. **Strengthening**, `IsDefEqU.weak'_iff` (`Theory/Typing/UniqueTyping.lean:231`), to carry
   `e`'s typing from `Γ'` back to `Γ`.  The docstring already flags this as "sub-gap 2";
   what it does not say is that this is the *same* residual `TrProj.wf`'s live route needs
   (`Verify/Typing/ProjSkip.lean`), so the two lemmas share a blocker rather than having two.

The docstring's "sub-gap 1" — a `Ctx.Lift'` version of `HasType.skips` — is real and small.

## Non-vacuity

A `Params` instance does not exist in this tree (`ChurchRosser.lean`'s class bundles
`env`, `henv : env.WF` and the pattern axioms; `Experimental/Reflect/Capstone.lean`'s
side condition is *provably unsatisfiable*), so `ConstRigid` cannot be fired at `barEnv`
today.  What can be checked, and is checked below, is that its **premise set is satisfiable at
a real structure environment**: `barEnv` — the `addInduct'` output of `ProjLevelWitness.lean`'s
two-field `Prop`-structure — has `RuleFreeHead `Bar``, because its only defeq rules are the
ι-rules, which are headed by `Bar.rec`.  That is the premise `TrProj.weak'_inv` would have to
discharge at its own call site, and it holds.
-/

namespace Lean4Lean

open VExpr

/-! ## The statement -/

/-- **(C) Rigidity.**  A term definitionally equal to a rule-free-headed constant application,
at a type, weak-head reduces to a constant application with the same head.

Head only: the levels and the arguments are **(B)**'s business (`IsDefEqU.const_app_inv`), and
mixing them in here is what turns three facts into one wrong one. -/
def VEnv.ConstRigid [VEnv.Params] : Prop :=
  ∀ (Γ : List VExpr) (e : VExpr) (c : Lean.Name) (us : List VLevel) (as : List VExpr),
    OnCtx Γ (VEnv.Params.env.IsType VEnv.Params.univs) →
    VEnv.Params.env.RuleFreeHead c →
    VEnv.Params.env.IsType VEnv.Params.univs Γ ((VExpr.const c us).mkApp as) →
    VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ e ((VExpr.const c us).mkApp as) →
    ∃ (us' : List VLevel) (as' : List VExpr),
      VEnv.WHRedS Γ e ((VExpr.const c us').mkApp as')

/-- The instance of (C) `TrProj.weak'_inv` uses, with the lift already in place: this is the
form in which `WHRed.weakU_inv` applies to the conclusion.  Stated separately so that the
consumer's shape is on the record and cannot drift from `ConstRigid`. -/
theorem VEnv.ConstRigid.at_lift [VEnv.Params] (H : VEnv.ConstRigid)
    {Γ Γ' : List VExpr} {l : Lift} {A : VExpr} {c : Lean.Name}
    {us : List VLevel} {as : List VExpr}
    (hΓ' : OnCtx Γ' (VEnv.Params.env.IsType VEnv.Params.univs))
    (_W : Ctx.Lift' l Γ Γ')
    (hrf : VEnv.Params.env.RuleFreeHead c)
    (hty : VEnv.Params.env.IsType VEnv.Params.univs Γ' ((VExpr.const c us).mkApp as))
    (hdf : VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ' (A.lift' l)
      ((VExpr.const c us).mkApp as)) :
    ∃ (us' : List VLevel) (as' : List VExpr),
      VEnv.WHRedS Γ' (A.lift' l) ((VExpr.const c us').mkApp as') :=
  H Γ' (A.lift' l) c us as hΓ' hrf hty hdf

/-! ## Fact (D): no-confusion between *distinct* rule-free constants

`Theory/Typing/Injectivity.lean`'s taxonomy ends with

> A fourth fact — no-confusion between *distinct* rule-free constants — is not stated because
> no consumer has asked for it; (B) is same-head only.

**A consumer has now asked.**  `TrProj.uniq` (`Verify/Typing/Lemmas.lean`) is stated with the
two structure names `s₁`, `s₂` independent, and that is *not* an auto-bound-implicit accident:
its second consumer, `IsDefEqE.trExpr`'s `proj` case (`Verify/EquivManager.lean:117`),
instantiates them differently, because `RelevantEq.proj` drops the structure name — faithfully,
since the checker's `EquivManager.isEquiv` drops it too
(`Lean4Lean/EquivManager.lean`: `| .proj _ i1 e1, .proj _ i2 e2 => pure (i1 == i2) <&&> …`).
Narrowing `TrProj.uniq` to a shared name was attempted and **breaks that file**; it was
reverted.  So `TrProj.uniq` must derive `s₁ = s₂`, and this is the statement that does it.

Side conditions are (B)'s, verbatim, and for (B)'s reasons — see
`Theory/Typing/ConstInvWitness.lean`, where dropping either makes that file prove `False`. -/

/-- **(D) No-confusion.**  Two *distinct* rule-free constants do not head definitionally equal
applications.  Belongs beside (A) and (B) in `Theory/Typing/Injectivity.lean`; it is here only
because that file is another stream's. -/
def VEnv.ConstNoConf (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (us us' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) →
    env.RuleFreeHead c → env.RuleFreeHead c' →
    env.IsType U Γ ((VExpr.const c us).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c us).mkApp as) ((VExpr.const c' us').mkApp as') →
    c = c'

/-! ## Premise satisfiability: `RuleFreeHead` at a real structure environment

Both (C) and (D) are gated on `RuleFreeHead`, so a reader should know it is reachable.  Two
independent handles:

* **At a concrete witness**, below: `barEnv.RuleFreeHead `Bar``, sorry-free.
* **At a `TrEnv'`-built environment**, by the *temporal* argument that
  `TrEnv'.ruleFreeHead_quot` (`Verify/TypeChecker/Reduce.lean`, sorry-free) runs for `Quot`:
  `VEnv.addConst` refuses a name already present and a `TrEnv'` chain only grows `constants`,
  so a δ-rule headed by `S` and the declaration step that introduces `S` cannot both occur.
  For an inductive `S` the ι-rules are headed by `mkRecName T.name ≠ S` and the quot rules by
  `Quot.lift`, so the same shape of argument should apply with the `quotInit` bit replaced by
  "`S` was introduced by an `AddInduct` step".  **Not done here** — it belongs on the
  `Verify/Environment` side, which this stream does not own, and it waits on `AddInduct`
  acquiring constructors.  Recorded so that nobody charges this to `VEnv.Sig`. -/

theorem VEnv.addDefEqList_defeqs_inv :
    ∀ (l : List VDefEq) (env : VEnv) (df : VDefEq),
      (l.foldl VEnv.addDefEq env).defeqs df → df ∈ l ∨ env.defeqs df
  | [], _, _, h => .inr h
  | d :: l, env, df, h => by
    rcases addDefEqList_defeqs_inv l (env.addDefEq d) df h with h | h
    · exact .inl (.tail _ h)
    · rcases h with rfl | h
      · exact .inl (.head _)
      · exact .inr h

theorem VEnv.addIndRules_defeqs_inv {env : VEnv} {D : VInductDecl'} {df : VDefEq}
    (h : (env.addIndRules D).defeqs df) : df ∈ D.iotaRules ∨ env.defeqs df :=
  addDefEqList_defeqs_inv _ _ _ h

theorem VEnv.addInduct'_defeqs_inv {env env' : VEnv} {D : VInductDecl'} {df : VDefEq}
    (h : env.addInduct' D = some env') (hdf : env'.defeqs df) :
    df ∈ D.iotaRules ∨ env.defeqs df := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rcases addIndRules_defeqs_inv hdf with h | h
  · exact .inl h
  · exact .inr (by rwa [VEnv.addConstList_defeqs h1] at h)

/-- `barEnv`'s only defeq rules are `barDecl`'s ι-rules. -/
theorem barEnv_defeqs {df : VDefEq} (h : barEnv.defeqs df) : df ∈ barDecl.iotaRules := by
  rcases VEnv.addInduct'_defeqs_inv barEnv_eq.choose_spec h with h | h
  · exact h
  · exact h.elim

/-- The ι-rules of a structure block are headed by its **recursor**, computed. -/
theorem barDecl_iotaRules_heads :
    barDecl.iotaRules.map (fun df => VExpr.headConst? df.lhs) = [some `Bar.rec] := rfl

/-- **The premise `(C)` needs at a structure, discharged.**  `Bar` heads no definitional-equality
rule of `barEnv`. -/
theorem barEnv_ruleFreeHead : barEnv.RuleFreeHead `Bar := by
  intro df hdf
  have hmem := barEnv_defeqs hdf
  have : VExpr.headConst? df.lhs ∈ barDecl.iotaRules.map (fun df => VExpr.headConst? df.lhs) :=
    List.mem_map_of_mem hmem
  rw [barDecl_iotaRules_heads] at this
  simp at this
  rw [this]
  exact nofun

end Lean4Lean
