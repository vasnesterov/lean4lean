import Lean4Lean.Theory.Typing.HeadReduction
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Verify.Typing.ConstSpine
import Lean4Lean.Theory.Typing.ParamsWitness

/-!
# Facts (C) and (D) — (D) proved, (C) reduced to weak-head normalisation

`Theory/Typing/Injectivity.lean`'s taxonomy names three facts about constant applications and
declines to state the third (rigidity) and a fourth (no-confusion).  This file states both,
and — since `Verify/Typing/ConstSpine.lean` landed — settles them:

| | status |
|---|---|
| **(D)** `VEnv.ConstNoConf` | **PROVED**, modulo `VEnv.PatWF` — `VEnv.constNoConf_of_patWF` |
| **(C)** rigidity | **PROVED from weak-head normalisation** — `VEnv.constRigidPat_of_weakNorm` |

Both go through `VEnv.IsDefEq.church_rosser`; see `Verify/Typing/ConstSpine.lean`'s module
docstring for the argument and for why the `trans` residual that `Injectivity.lean` attaches to
this whole family never arises on that route.

## Correction: `VEnv.ConstRigid` below is under-hypothesised

The statement kept below is the one this file originally recorded, verbatim, so that the
correction is legible.  Its side condition is `Params.env.RuleFreeHead c`, a fact about
`env.defeqs`; the reduction step it must block is `WHRed.extra`, which fires on a
`Params.Pat`-registered pattern.  `Params` constrains `Pat` and `defeqs` in one direction only
(`extra_pat`), so under an abstract instance the hypothesis cannot reach the step.  The repaired
form is `VEnv.ConstRigidPat` (below), with `VEnv.PatFreeHead`; the two coincide at the canonical
pattern table, by `VEnv.RuleFreeHead.patFreeHead`.  This is the same defect class as
`RecTypeInj` (`Verify/Typing/StructureUniq.lean` §3.3) — a hypothesis set carrying less
information than its conclusion needs — and it is invisible to an auto-bound-implicit audit.
Note what is *not* claimed: `ConstRigid` is not shown false.  No `Params` instance refuting it
is exhibited; what is shown is that its hypothesis cannot reach the step it must block, so no
proof from those hypotheses can exist by this route.

## The statement, and the two things it is *not*

`ConstRigid` says: a term definitionally equal to a **rule-free-headed** constant application,
whose common type is a genuine type, weak-head reduces to a constant application **with that
same head**.  Nothing about the levels, nothing about the arguments.

* It is not **(A) disjointness** (`const_forallE_inv`, `const_sort_inv`): those say a const
  application is not a Π and not a sort.  (C)'s conclusion is about the *left* side.  (A) is
  also now proved modulo `PatWF`, in `ConstSpine.lean`.
* It is not **(B) injectivity** (`const_app_inv`): (B) relates two const applications with the
  same head; here only one side is a const application, which is exactly why
  `TrProj.weak'_inv`'s docstring's earlier diagnosis ("`const_app_inv`") was wrong.

## Why the `IsType` side condition

`IsType` on the const application is load-bearing twice.  Without it `IsDefEq.proofIrrel`
identifies any two inhabitants of a proposition **with no rule in the environment at all**
(`Theory/Typing/ConstInvWitness.lean`'s `w2`).  And in the Church--Rosser proof it is what
excludes `NormalEq.etaL` at the top of the spine: an η-expansion has a Π type, and a Π is not a
sort (`VEnv.isType_lam_false`).

`OnCtx Γ` is not decoration: `Params.pat_wf`'s docstring records that a rule stated about an
arbitrary `Γ` with no well-formedness hypothesis "should be treated as suspect by default" on
this development.

## What the consumer actually needs — corrected

`TrProj.weak'_inv`'s docstring traces its route to "concluding that `B₀` has the form
`(.const S us).mkApp (ps' ++ ιs')`", and names (C) as the residual.  Tracing it one step
further, the residual is **three** things, not one:

1. **(C)**, at `Γ'`, followed by `WHRed.weakU_inv` (`HeadReduction.lean:89`) to move the
   reduction into `Γ` — already proved, and in exactly the `Ctx.Lift'` form `weak'_inv` is
   stated over.  (`InferTypeS.weakU_inv`, `HeadReduction.lean:691`, is the same move for the
   *typing*, and looks like the cheaper entry point: it hands back a type living in `Γ`.)
2. **(B)'s level half**: `TrProj`'s F17 clause is stated at the *use site's* `us`, so a
   recovered head `(.const S us').mkApp as'` is useless unless `us' ≈ us`.  (C) is head-only by
   design, so this is a second, separate ask.  It is now available: `const_app_inv_of_patWF`.
3. **Strengthening**, `IsDefEqU.weak'_iff` (`Theory/Typing/UniqueTyping.lean:231`), to carry
   `e`'s typing from `Γ'` back to `Γ` — the same residual `TrProj.wf`'s live route needs
   (`Verify/Typing/ProjSkip.lean`), so the two lemmas share a blocker rather than having two.

The docstring's "sub-gap 1" — a `Ctx.Lift'` version of `HasType.skips` — is real and small.

## Non-vacuity

A `Params` instance for a *structure* environment does not exist in this tree, so
`ConstRigid`/`ConstRigidPat` still cannot be fired at `barEnv`.  What is checked below is that
the premise sets are satisfiable at a real structure environment — `barEnv`, the `addInduct'`
output of `ProjLevelWitness.lean`'s two-field `Prop`-structure, has `RuleFreeHead` at every
name but `Bar.rec` — and, for (D), that its conclusion has content there:
`barEnv_bar_ne_ctorApp` derives that `Bar` is not definitionally equal to any application of
`Bar.mk`.
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

/-- Local re-derivation of `VEnv.addDefEqList_defeqs_inv` (`Verify/Environment/Basic.lean`),
with the disjuncts in the other order.  **Primed deliberately**: the unprimed name is taken by
that file, and two modules declaring one name can never be imported together — which is not a
build error (nothing imported both) but silently blocks any future file, or measurement
script, that needs both.  Found by a cone-measurement import. -/
theorem VEnv.addDefEqList_defeqs_inv' :
    ∀ (l : List VDefEq) (env : VEnv) (df : VDefEq),
      (l.foldl VEnv.addDefEq env).defeqs df → df ∈ l ∨ env.defeqs df
  | [], _, _, h => .inr h
  | d :: l, env, df, h => by
    rcases addDefEqList_defeqs_inv' l (env.addDefEq d) df h with h | h
    · exact .inl (.tail _ h)
    · rcases h with rfl | h
      · exact .inl (.head _)
      · exact .inr h

theorem VEnv.addIndRules_defeqs_inv' {env : VEnv} {D : VInductDecl'} {df : VDefEq}
    (h : (env.addIndRules D).defeqs df) : df ∈ D.iotaRules ∨ env.defeqs df :=
  addDefEqList_defeqs_inv' _ _ _ h

theorem VEnv.addInduct'_defeqs_inv {env env' : VEnv} {D : VInductDecl'} {df : VDefEq}
    (h : env.addInduct' D = some env') (hdf : env'.defeqs df) :
    df ∈ D.iotaRules ∨ env.defeqs df := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rcases addIndRules_defeqs_inv' hdf with h | h
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

/-- **The premise `(C)` and `(D)` need at a structure, discharged.**  Every name other than
the recursor heads no definitional-equality rule of `barEnv`. -/
theorem barEnv_ruleFreeHead' {c : Lean.Name} (hc : c ≠ `Bar.rec) : barEnv.RuleFreeHead c := by
  intro df hdf
  have hmem := barEnv_defeqs hdf
  have : VExpr.headConst? df.lhs ∈ barDecl.iotaRules.map (fun df => VExpr.headConst? df.lhs) :=
    List.mem_map_of_mem hmem
  rw [barDecl_iotaRules_heads] at this
  simp at this
  rw [this]
  exact fun h => hc (Option.some.inj h).symm

/-- `Bar` heads no definitional-equality rule of `barEnv`. -/
theorem barEnv_ruleFreeHead : barEnv.RuleFreeHead `Bar := barEnv_ruleFreeHead' (by decide)

/-- `Bar.mk` heads no definitional-equality rule of `barEnv` either. -/
theorem barEnv_ruleFreeHead_mk : barEnv.RuleFreeHead `Bar.mk := barEnv_ruleFreeHead' (by decide)

/-! ## (D) is proved, modulo `VEnv.PatWF`

`Verify/Typing/ConstSpine.lean` proves both (B) and (D) by the Church--Rosser route: two
constant-headed spines that are definitionally equal parallel-reduce to constant-headed
spines with the *same* heads, and `NormalEq` — which has no `trans` constructor — compares
them componentwise.  The `trans` case that `Theory/Typing/Injectivity.lean` records as the
residual of the whole family never arises, because `IsDefEq.church_rosser` has already paid
for transitivity.

What is left is `VEnv.PatWF`, the single open field of `VEnv.Params`
(`Theory/Typing/ParamsBuild.lean` discharges the other nine from `VEnv.WF`). -/

/-- **(D) `VEnv.ConstNoConf`, proved** — modulo `VEnv.PatWF`. -/
theorem VEnv.constNoConf_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U) :
    env.ConstNoConf U := fun _Γ _c _c' _us _us' _as _as' hΓ hrf hrf' hty h =>
  (VEnv.constApp_inv_of_patWF henv U hwf hΓ hrf hrf' hty h).1

/-! ### Non-vacuity of (D), at the two-field structure witness

(D) at `barEnv` with `c := Bar` and `c' := Bar.mk` is a **negative** statement with content:
the structure's type former is not definitionally equal to any application of its own
constructor.  Both `RuleFreeHead` premises are discharged above, and the `IsType` premise is
discharged from `barEnv`'s recorded type for `Bar`.

Two hypotheses are carried rather than discharged, for reasons that are not about `barDecl`:
`barEnv.WF` is unavailable because `VInductDecl'` is not yet wired into `VDecl.induct`
(`Verify/Typing/ProjWfWitness.lean` §2.5 records the same gap), and `PatWF` is the open
`Params` field itself. -/
theorem barEnv_bar_ne_ctorApp (henv : barEnv.WF) (U : Nat) (hwf : barEnv.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (barEnv.IsType U))
    (hBar : barEnv.constants `Bar = some ⟨0, VExpr.sort .zero⟩)
    {us : List VLevel} {as : List VExpr} :
    ¬ barEnv.IsDefEqU U Γ ((VExpr.const `Bar []).mkApp []) ((VExpr.const `Bar.mk us).mkApp as) := by
  have hty : barEnv.IsType U Γ ((VExpr.const `Bar []).mkApp []) := by
    refine ⟨.zero, ?_⟩
    have := VEnv.IsDefEq.constDF (env := barEnv) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
      hBar (by simp) (by simp) rfl .nil
    exact this
  exact fun h => absurd
    (VEnv.constNoConf_of_patWF henv U hwf Γ _ _ _ _ _ _ hΓ barEnv_ruleFreeHead
      barEnv_ruleFreeHead_mk hty h)
    (by decide)

/-! ### `PatFreeHead` is not decoration, at the tree's one concrete `Params` instance

`Theory/Typing/ParamsWitness.lean` builds a `Params` instance over `CycleConv.propLoopEnv`
(two constants `A B : Prop`, two δ-rules `A ⟶ B`, `B ⟶ A`) and machine-checks that a
`ParRed.extra` step really fires there.  So the side condition of `ParRed.constApp_inv` — and
hence of (A), (B), (D) and (C) — can be measured rather than argued: at that instance
`PatFreeHead` **fails** at `A`, and dropping it from `ParRed.constApp_inv` makes that lemma
outright false. -/

theorem propLoop_not_patFreeHead_A : ¬ @VEnv.PatFreeHead VEnv.propLoopParams `A := by
  intro h
  exact h (.const `A) ⟨.fixed (.const `B []) () trivial, .true⟩
    (show VEnv.PropLoopParams.Pat (.const `A) _ from Or.inl ⟨rfl, rfl⟩) rfl

theorem propLoop_patFreeHead_other {c : Lean.Name} (h1 : c ≠ `A) (h2 : c ≠ `B) :
    @VEnv.PatFreeHead VEnv.propLoopParams c := by
  intro p r hp
  replace hp : VEnv.PropLoopParams.Pat p r := hp
  obtain ⟨c₀, rfl⟩ := VEnv.PropLoopParams.Pat.const hp
  rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact fun h => h1 h.symm
  · exact fun h => h2 h.symm

/-- **Dropping `PatFreeHead` from `ParRed.constApp_inv` is false**, at the witness where the
rule fires: `A` reduces to `B`, and `B` is not an application of `A`. -/
theorem parRed_constApp_inv_needs_patFreeHead :
    ¬ ∀ (Γ : List VExpr) (c : Lean.Name) (ls : List VLevel) (as : List VExpr) (e' : VExpr),
        @VEnv.ParRed VEnv.propLoopParams Γ ((VExpr.const c ls).mkApp as) e' →
        ∃ as', e' = (VExpr.const c ls).mkApp as' := by
  intro h
  obtain ⟨as', has⟩ := h [] `A [] [] (.const `B []) VEnv.propLoopEnv_parRed_fires
  obtain ⟨hc, -, -⟩ := VExpr.constApp_inj (as := []) (as' := as') has
  exact absurd hc (by decide)

/-! ### (A), (B) and (D) fired end to end, at a genuinely rule-free environment

`propLoopEnv2` (`Theory/Typing/CycleConv.lean`) is `propLoopEnv` **before** its two δ-rules are
added: two constants `A B : Prop` and *no* definitional-equality rules at all.  It is therefore
in the δ fragment vacuously, so `VEnv.patWF_of_deltaFragment` discharges `PatWF` outright and
every hypothesis of (A)/(B)/(D) is met with nothing carried.

The consequences below are the first end-to-end firings of the constant-application family in
this tree: `VEnv.WF` → `paramsOfWF` → `IsDefEq.church_rosser` → the spine analysis.  They are
`sorryAx`-tainted only through the four inherited holes (`weakN_iff`, `forallE_inv_stratified`,
`NormalEq.descend`, `forallE_inv`); the environment and its well-formedness are `sorry`-free. -/

theorem propLoopEnv1_add : VEnv.empty.addConst `A ⟨0, .sort .zero⟩ = some propLoopEnv1 := rfl

theorem propLoopEnv2_add : propLoopEnv1.addConst `B ⟨0, .sort .zero⟩ = some propLoopEnv2 := rfl

/-- `propLoopEnv2` is well-formed: two `axiom` steps from the empty environment. -/
theorem propLoopEnv2_wf : propLoopEnv2.WF :=
  ⟨_, .decl (.axiom (ci := ⟨⟨0, .sort .zero⟩, `B⟩)
      ⟨.succ .zero, .sortDF trivial trivial rfl⟩ propLoopEnv2_add)
    (.decl (.axiom (ci := ⟨⟨0, .sort .zero⟩, `A⟩)
      ⟨.succ .zero, .sortDF trivial trivial rfl⟩ propLoopEnv1_add) .empty)⟩

theorem propLoopEnv2_defeqs {df : VDefEq} : ¬ propLoopEnv2.defeqs df := nofun

theorem propLoopEnv2_ruleFree {c : Lean.Name} : propLoopEnv2.RuleFreeHead c :=
  fun _ h => absurd h propLoopEnv2_defeqs

/-- Vacuously: with no rules there is nothing to register. -/
theorem propLoopEnv2_delta : VEnv.DeltaFragment propLoopEnv2 := by
  intro p r h
  cases h with
  | delta _ h => exact absurd h propLoopEnv2_defeqs
  | iota _ _ _ _ h => exact absurd h propLoopEnv2_defeqs
  | quot h => exact absurd h propLoopEnv2_defeqs

theorem propLoopEnv2_patWF : propLoopEnv2.PatWF 0 :=
  VEnv.patWF_of_deltaFragment propLoopEnv2_wf 0 propLoopEnv2_delta

/-- **(D), with content, unconditionally.**  Two distinct propositions of a rule-free
environment are not definitionally equal. -/
theorem propLoopEnv2_A_ne_B :
    ¬ propLoopEnv2.IsDefEqU 0 [] (.const `A []) (.const `B []) := by
  intro h
  exact absurd
    (VEnv.constNoConf_of_patWF propLoopEnv2_wf 0 propLoopEnv2_patWF
      [] `A `B [] [] [] [] trivial propLoopEnv2_ruleFree propLoopEnv2_ruleFree
      ⟨_, hasType_constProp propLoopEnv2_A⟩ h)
    (by decide)

/-- **(A), sort half, with content.**  A rule-free constant is not a sort. -/
theorem propLoopEnv2_A_ne_sort {u : VLevel} :
    ¬ propLoopEnv2.IsDefEqU 0 [] (.const `A []) (.sort u) :=
  VEnv.const_sort_inv_of_patWF propLoopEnv2_wf 0 propLoopEnv2_patWF (Γ := []) (as := [])
    trivial propLoopEnv2_ruleFree

/-- **(A), Π half, with content.**  A rule-free constant is not a Π. -/
theorem propLoopEnv2_A_ne_forallE {A B : VExpr} :
    ¬ propLoopEnv2.IsDefEqU 0 [] (.const `A []) (.forallE A B) :=
  VEnv.const_forallE_inv_of_patWF propLoopEnv2_wf 0 propLoopEnv2_patWF (Γ := []) (as := [])
    trivial propLoopEnv2_ruleFree

/-! ## (C): an information-flow defect in the statement above, and the residual

**`VEnv.ConstRigid` as stated is not provable, and the reason is a missing hypothesis.**  Its
side condition is `Params.env.RuleFreeHead c` — a fact about `env.defeqs` — while the rule
that could reduce a `c`-headed spine is `WHRed.extra`, which fires on a `Params.Pat`-
registered pattern.  `Params` constrains `Pat` and `defeqs` in *one* direction only
(`extra_pat` : every rule is a registered pattern under leading λs); nothing forbids an
instance whose `Pat` registers a pattern headed by a `RuleFreeHead` constant.  So the
hypothesis cannot reach the step it is meant to block.

This is the same defect class as `RecTypeInj` (`Verify/Typing/StructureUniq.lean` §3.3): a
hypothesis set carrying strictly less information than the conclusion needs.  It is invisible
to an auto-bound-implicit audit.

The repair is `VEnv.PatFreeHead` (`Verify/Typing/ConstSpine.lean`), which says exactly what
the `extra` step needs, together with `VEnv.RuleFreeHead.patFreeHead`: at the **canonical**
pattern table `Lean4Lean.Pat env` — the one `VEnv.paramsOfWF` installs, and the only one any
consumer will meet — `RuleFreeHead` *does* imply `PatFreeHead`, because every registered
pattern's head constant is the head constant of a rule's left-hand side
(`Lean4Lean.Pat.headConst_defeqs`).

With that repair, (C) is **proved from weak-head normalisation and nothing else**:
`VEnv.constRigid_of_weakNorm`.  See `Verify/Typing/ConstSpine.lean` for why the
Church--Rosser route that settles (B) and (D) does not settle (C) on its own — `NormalEq.etaL`
relates a λ to a constant application, and a λ is a weak-head normal form. -/

/-- **(C) with the repaired side condition, proved from weak-head normalisation.**  This is
`VEnv.ConstRigid` with `RuleFreeHead` replaced by `VEnv.PatFreeHead`; see the section
docstring for why the replacement is a correction and not a weakening. -/
def VEnv.ConstRigidPat [VEnv.Params] : Prop :=
  ∀ (Γ : List VExpr) (e : VExpr) (c : Lean.Name) (us : List VLevel) (as : List VExpr),
    OnCtx Γ (VEnv.Params.env.IsType VEnv.Params.univs) →
    VEnv.PatFreeHead c →
    VEnv.Params.env.IsType VEnv.Params.univs Γ ((VExpr.const c us).mkApp as) →
    VEnv.Params.env.IsDefEqU VEnv.Params.univs Γ e ((VExpr.const c us).mkApp as) →
    ∃ (us' : List VLevel) (as' : List VExpr),
      VEnv.WHRedS Γ e ((VExpr.const c us').mkApp as')

theorem VEnv.constRigidPat_of_weakNorm [VEnv.Params] (hwn : VEnv.WeakNorm) :
    VEnv.ConstRigidPat :=
  fun _Γ _e _c _us _as hΓ hc hty hdf => VEnv.constRigid_of_weakNorm hwn hΓ hc hty hdf

end Lean4Lean
