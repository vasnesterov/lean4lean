import Lean4Lean.Verify.Typing.ProjWeakInv
import Lean4Lean.Theory.Typing.StrengthenVerdict
import Lean4Lean.Theory.MutualDefUnsound

/-!
# The uninhabited-binder question, answered: it **is** consistency, and it is not a dichotomy

`Verify/Typing/ProjWeakInv.lean` reduces `TrProj.weak'_inv` (a `Verify/`-side census hole with
30+ transitive users) to `VEnv.ConstAppTypeStrengthen`, and localises that to one binder that
may be assumed uninhabited in its own prefix (`constAppTypeStrengthen_of_skipUninhab`), with the
complementary bound `constAppTypeStrengthen_inhab` holding over inhabited lifts.  Its round-2
docstring, and `Theory/Typing/Strengthen.lean` §12 before it, close with the same sentence:
the residual carries content exactly to the extent that **uninhabited** types over a `VEnv.WF`
environment exist, and *"exhibiting one is itself open in this tree"*.

This file answers that question.  Three findings, all machine-checked here, none previously on
the record for the projection residual:

## 1. The question is *exactly* consistency — as an iff, not a heuristic

`consistent_iff_exists_uninhabited_prop`: for every `Ordered` environment,

    env.Consistent  ↔  ∃ Γ A, OnCtx Γ ∧ Γ ⊢ A : Prop ∧ A has no inhabitant in Γ

`→` is `falseProp` itself (`falseProp_isType`, `allProp_isProp`); `←` is the observation that a
closed proof of `∀ p : Prop, p` weakens into every context and *applies* to every proposition
there, so one uninhabited proposition anywhere refutes it.  So an uninhabited **proposition**
over a `VEnv.WF` environment is not merely "as hard as" consistency: it is the same statement,
and `VEnv.Consistent` is `Theory/Consistency.lean`'s definition, which nothing in this tree
proves for any environment.  **The honest answer to "is there one?" is therefore "yes, iff some
environment is consistent" — an assumption strictly weaker than `leanTTConsistent` (`∅ ≤ env`
and `HasType.mono` push any inhabitant down to `VEnv.empty`), and one the project's own link 2
must supply anyway.**  In particular the "no" branch is *not* a neutral open alternative: it
says every environment the checker can build proves `∀ p : Prop, p`.

Note what this does **not** say, because the tree already corrects that error once
(`Theory/Typing/StrengthenVerdict.lean` §1): inconsistency does not make everything inhabited.
`∀ p : Prop, p` applies only to *propositions*, and the residual quantifies over binders at
every sort.  So `¬ env.Consistent` does not close the residual, and the iff above is stated at
`.sort .zero` on purpose.

## 2. The hypothesis that *does* close the residual, and a positive instance of it

`VEnv.AllTypesInhabited` — every type of every well-formed context is inhabited — closes the
projection residual outright, at every depth and with `us' = us` on the nose
(`VEnv.AllTypesInhabited.constAppTypeStrengthen`).  This is what the "no uninhabited type"
branch actually needs; it is strictly stronger than `¬ env.Consistent` by §1's remark.  It also
closes the `weakN_iff` target (`VEnv.AllTypesInhabited.strengtheningTarget`, one line through
`Strengthen.lean` §12's `strengtheningTarget_of_allInhabited`) — so the brief's "an answer pays
twice" is now checked rather than asserted.

And it is satisfied somewhere: `StrengthenVerdict.lean`'s `univInhab : ∀ (α : Sort u), α`
environment satisfies it, so

* `exists_univInhabEnv_constAppTypeStrengthen` — a **`VEnv.WF` environment at which
  `VEnv.ConstAppTypeStrengthen` is a theorem**, at every `U`; cone 3251, `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`, i.e. **hole-free**; and
* `exists_univInhabEnv_trProj_weak'_inv` — the exact statement of the `TrProj.weak'_inv` `sorry`,
  at that environment, obtained through `TrProj.weak'_inv_of_strengthen`.  **This one is *not*
  hole-free** (cone 3694, `sorryAx` present): the reduction it goes through carries
  `IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS` of its own,
  and inhabitation repairs none of them — the latter two are Π-injectivity, arriving with
  `HasArgs.of_mkApp`.  Recorded with that qualifier because the difference between the two rows
  is the point: **discharging the strengthening residual does not by itself discharge
  `TrProj.weak'_inv`**, even at an environment where the residual is a theorem.

The first row is the first positive instance of this residual at any environment, which working
rule 4's affirmative side had never been met for.  Its scope is
stated exactly, and it is narrow: `univInhabEnv_not_consistent` shows that environment is
**inconsistent**, and `AllTypesInhabited.no_uninhabited_binder` shows the uninhabitedness
premise of `ConstAppSkipUninhab` is satisfiable at **no** well-formed context there.  So the
instance lives entirely inside the case `constAppTypeStrengthen_inhab` already covers and tests
nothing about the hard case — the projection-side analogue of
`StrengthenVerdict.univInhab_no_uninhabited_entry`, and it is recorded here so the witness is
not mistaken for progress on the obstruction.

## 3. A defect in the localisation: `ConstAppSkipUninhab` is stronger than the residual needs

`VEnv.ConstAppSkipUninhab` carries **no** `OnCtx Γ'` premise — `constAppTypeStrengthen_of_skipUninhab`
never passes one, because the uninhabited branch of its induction has no way to strengthen
`OnCtx Γ'` to `OnCtx Γ₂` (that step is `OnCtx.weak'_inv`, i.e. the `IsDefEqU.weakN_iff` gate the
reduction is advertised to avoid).  The consequence, `constAppSkipUninhab_uninhab_premise_illFormed`:
its uninhabitedness premise is satisfiable **unconditionally, over every environment**, by an
inserted binder that is not a type at all (`.bvar 0` at `Γ = []`, uninhabited because
`IsDefEq.closedN'` forces types closed).  Such instances are *not* reachable from
`ConstAppTypeStrengthen`, whose `OnCtx Γ'` premise excludes them.

Two things follow.  (i) "`ConstAppSkipUninhab`'s premises are satisfiable" is **not** evidence
that the residual has content: the witnesses may be junk contexts, so §1's conditional
`falseProp` witness is the one that counts.  (ii) At the `univInhab` environment
`ConstAppTypeStrengthen` is a theorem (§2) while the same argument does *not* discharge
`ConstAppSkipUninhab`, because `univInhab_no_uninhabited_entry` needs `OnCtx Γ'`.  So the
one-binder form is strictly stronger than the residual, and it cannot be repaired by adding
`OnCtx Γ'` without re-importing the gate.

## Verdict for the census

**The census does not move.**  Closing the residual by the inhabited route requires
`AllTypesInhabited` at every environment the checker builds, which by §1 fails at every
consistent one; and `TrProj.weak'_inv` is needed for *arbitrary* `VEnv.WF env`, not for the one
environment of §2.  Nothing here discharges a `sorry`; what is new is that the remaining case is
pinned to `VEnv.Consistent` by an iff, so no future round need re-open the question of whether
an uninhabited type "exists".
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean VExpr

/-! ## 1. The hypothesis that closes the residual -/

/-- **Every type of every well-formed context is inhabited.**  The precise form of the "no
uninhabited type over this environment" branch.  Strictly stronger than `¬ env.Consistent`:
a proof of `∀ p : Prop, p` inhabits *propositions* only (`StrengthenVerdict.lean` §1). -/
def VEnv.AllTypesInhabited (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr}, OnCtx Γ (env.IsType U) → env.IsType U Γ A →
    ∃ e, env.HasType U Γ e A

/-- The induction behind `VEnv.AllTypesInhabited.constAppTypeStrengthen`: peel the outermost
inserted binder (`Lift.depth_succ`, `Ctx.Lift'.of_cons_skip`), instantiate it with an inhabitant
supplied by the hypothesis (`Ctx.LiftN.exists_instN_typed`, `HasType.instN`), and recurse with
the smaller context's well-formedness recovered by *instantiation* rather than by strengthening
(`Ctx.InstN.wf`) — which is what keeps `OnCtx.weak'_inv` and `IsDefEqU.weakN_iff` out of the
cone.  The level list is untouched and `as'` is an explicit substitution instance of `as`. -/
theorem constAppTypeStrengthen_of_allTypesInhabited_aux {env : VEnv} {U : Nat}
    (henv : env.Ordered) (hinh : env.AllTypesInhabited U) {c : Lean.Name} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e : VExpr} {us : List VLevel} {as : List VExpr},
      l.depth = n → Ctx.Lift' l Γ Γ' → OnCtx Γ' (env.IsType U) → (∀ u ∈ us, u.WF U) →
      env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as) →
      ∃ as', as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us).mkApp as') := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e us as hd W hΓ' hlv hty
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at hty
    exact ⟨as, rfl, hty⟩
  | succ n ih =>
    intro l Γ Γ' e us as hd W hΓ' hlv hty
    obtain ⟨l, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at hty
    obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W2.exists_instN_typed hΓ'
    obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
    have h2 := hty.instN henv (hI e₀) h₀
    rw [VExpr.inst_liftN, VExpr.inst_mkApp,
      show (VExpr.const c us).inst _ _ = VExpr.const c us from rfl] at h2
    have hΓ₂ : OnCtx Γ₂ (env.IsType U) := (Ctx.InstN.wf henv (hI e₀) h₀ hΓ').2
    obtain ⟨as', hlen, h3⟩ := ih (by simpa using hdl) W1 hΓ₂ hlv h2
    exact ⟨as', by simpa using hlen, h3⟩

/-- **`AllTypesInhabited` closes the projection residual**, at every depth, with `us' = us`. -/
theorem VEnv.AllTypesInhabited.constAppTypeStrengthen {env : VEnv} {U : Nat} (henv : env.Ordered)
    (hinh : env.AllTypesInhabited U) : env.ConstAppTypeStrengthen U := fun hΓ' W hlv hty =>
  let ⟨as', hlen, h⟩ := constAppTypeStrengthen_of_allTypesInhabited_aux henv hinh _ rfl W hΓ' hlv hty
  ⟨_, as', hlv, .rfl fun _ _ => rfl, hlen, h⟩

/-- **…and it closes the `weakN_iff` target too**, through `Strengthen.lean` §12.  So one answer
does pay for both residuals. -/
theorem VEnv.AllTypesInhabited.strengtheningTarget {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (hinh : env.AllTypesInhabited U) : VEnv.StrengtheningTarget env U := by
  refine strengtheningTarget_of_allInhabited henv fun {k Γ Γ'} W hΓ' => ?_
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
  exact ⟨Γ₀, A₀, e₀, hI _, h₀⟩

/-- The scope of any such argument, stated exactly: where `AllTypesInhabited` holds, the
uninhabitedness premise of `VEnv.ConstAppSkipUninhab` is satisfiable at **no** well-formed
context.  (`StrengthenVerdict.univInhab_no_uninhabited_entry`, for the projection residual.)

`Ordered env` used to be a hypothesis here.  It was only ever feeding
`Ctx.LiftN.exists_instN_typed`, and that lemma no longer asks for it (2026-09-03, see
`Theory/Typing/LiftTrimWitness.lean`), so this holds at unordered environments too. -/
theorem VEnv.AllTypesInhabited.no_uninhabited_binder {env : VEnv} {U k : Nat}
    {Γ Γ' : List VExpr} (hinh : env.AllTypesInhabited U)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    ¬ (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) := by
  intro hemp
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
  exact hemp Γ₀ A₀ e₀ (hI _) h₀

/-! ## 2. The question **is** consistency -/

/-- **The answer.**  An uninhabited *proposition* over `env` exists iff `env` is consistent.
`→` exhibits `falseProp`; `←` weakens a closed proof of `∀ p : Prop, p` into `Γ` and applies it
to `A`.  So "does an uninhabited type over a `VEnv.WF` environment exist?" is `VEnv.Consistent`,
a definition this tree proves for no environment — and whose failure everywhere is what the
"no" branch would require. -/
theorem consistent_iff_exists_uninhabited_prop {env : VEnv} (henv : env.Ordered) :
    env.Consistent ↔ ∃ (Γ : List VExpr) (A : VExpr), OnCtx Γ (env.IsType 0) ∧
      env.HasType 0 Γ A (.sort .zero) ∧ ∀ e, ¬ env.HasType 0 Γ e A := by
  constructor
  · exact fun hcon => ⟨[], falseProp, trivial, allProp_isProp, fun e he => hcon ⟨e, he⟩⟩
  · rintro ⟨Γ, A, hΓ, hA, hemp⟩ ⟨e, he⟩
    have he' : env.HasType 0 Γ e (.forallE (.sort .zero) (.bvar 0)) := he.weak0 henv
    exact hemp _ (by simpa [VEnv.HasType, VExpr.inst] using VEnv.IsDefEq.appDF he' hA)

/-- The conditional witness, in the residual's own vocabulary: over any consistent environment,
`falseProp` is a well-formed closed type with no inhabitant, so it is a legal *uninhabited
binder* — the shape `constAppTypeStrengthen_of_skipUninhab` reduces the residual to.  Nothing
here proves `env.Consistent` for any `env`; that is `Theory/Consistency.lean`'s open statement
(and, through `Theory/SetModel/FalseProp.lean`, the model layer's `PropSplit` parameter, which
nothing constructs). -/
theorem uninhabited_binder_of_consistent {env : VEnv} (hcon : env.Consistent) :
    env.IsType 0 [] falseProp ∧ Ctx.LiftN 1 0 ([] : List VExpr) [falseProp] ∧
      OnCtx [falseProp] (env.IsType 0) ∧
      ∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 [falseProp] [] → ¬ env.HasType 0 Γ₀ e₀ A₀ :=
  ⟨falseProp_isType _, .one, ⟨trivial, falseProp_isType _⟩,
    fun _ _ e₀ hI => by cases hI; exact fun h => hcon ⟨e₀, h⟩⟩

/-- `VEnv.empty` is below every environment. -/
theorem VEnv.empty_le (env : VEnv) : VEnv.empty ≤ env := by
  constructor
  · intro n a h; exact absurd h (by simp [VEnv.empty])
  · intro df h; exact h.elim

/-- **The weakest assumption that answers the question is `(∅ : VEnv).Consistent`.**
Consistency of *any* environment pushes down to the empty one (`HasType.mono`), and `VEnv.empty`
is `VEnv.WF` by `⟨[], .empty⟩` with `falseProp_isType` needing no environment hypothesis at all.
So "an uninhabited well-formed type over a `VEnv.WF` environment exists" follows from the
consistency of the constant-free, rule-free core — strictly weaker than `leanTTConsistent`, and
implied by it wherever `VEnv.LeanWF` is inhabited (which `Verify/PreludeVacuity.lean` shows is
itself not established here). -/
theorem empty_consistent_of_consistent {env : VEnv} (h : env.Consistent) :
    VEnv.empty.Consistent :=
  fun ⟨e, he⟩ => h ⟨e, he.mono (VEnv.empty_le env)⟩

theorem uninhabited_type_of_empty_consistent (h : VEnv.empty.Consistent) :
    ∃ (env : VEnv) (A : VExpr), VEnv.WF env ∧ env.IsType 0 [] A ∧
      ∀ e, ¬ env.HasType 0 [] e A :=
  ⟨_, falseProp, ⟨[], .empty⟩, falseProp_isType _, fun e he => h ⟨e, he⟩⟩

/-- The other half of §1's remark, machine-checked: `AllTypesInhabited` is *strictly* stronger
than inconsistency — it implies it. -/
theorem VEnv.AllTypesInhabited.not_consistent {env : VEnv} (hinh : env.AllTypesInhabited 0) :
    ¬ env.Consistent :=
  fun hcon => hcon (hinh (Γ := []) trivial (falseProp_isType env))

/-! ## 3. A positive instance of the residual, and of the `TrProj.weak'_inv` `sorry`

`StrengthenVerdict.lean` §2–§4 builds a `VEnv.WF` environment declaring
`univInhab : ∀ (α : Sort u), α` (an `unsafeDef` step, so *not* `VEnv.LeanWF`).  There every type
typed at a sort is inhabited, hence `AllTypesInhabited`, hence the residual. -/

/-- The witness environment, with the constant lookup exposed (`exists_univInhabEnv` hides it). -/
theorem exists_univInhabEnv_constants : ∃ env : VEnv, VEnv.WF env ∧
    env.constants `univInhab = some ⟨1, univType⟩ := by
  obtain ⟨env', h⟩ : ∃ env', VEnv.empty.addConst `univInhab ⟨1, univType⟩ = some env' := ⟨_, rfl⟩
  have hcs : env'.constants `univInhab = some ⟨1, univType⟩ := by
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp
  exact ⟨env'.addDefEqs [univDV], ⟨_, .decl (univInhabDecl_wf h) .empty⟩, by
    simpa [VEnv.addDefEqs, VEnv.addDefEq] using hcs⟩

theorem allTypesInhabited_of_univInhab {env : VEnv} {U : Nat}
    (hc : env.constants `univInhab = some ⟨1, univType⟩) : env.AllTypesInhabited U := by
  rintro Γ A hΓ ⟨u, hA⟩
  have hu : u.WF U := (VEnv.IsDefEq.levelWF hA (onCtx_levelWF hΓ)).2.2
  exact ⟨_, hasType_univInhab_app hc hu hA⟩

/-- **A `VEnv.WF` environment at which `VEnv.ConstAppTypeStrengthen` is a theorem**, at every
`U`.  The first positive instance of the projection residual anywhere. -/
theorem exists_univInhabEnv_constAppTypeStrengthen :
    ∃ env : VEnv, VEnv.WF env ∧ ¬ env.Consistent ∧ ∀ U, env.ConstAppTypeStrengthen U := by
  obtain ⟨env, henv, hc⟩ := exists_univInhabEnv_constants
  exact ⟨env, henv,
    VEnv.AllTypesInhabited.not_consistent (allTypesInhabited_of_univInhab hc),
    fun U => VEnv.AllTypesInhabited.constAppTypeStrengthen henv.ordered
      (allTypesInhabited_of_univInhab hc)⟩

/-- **`TrProj.weak'_inv`'s exact statement at that environment** — via
`TrProj.weak'_inv_of_strengthen`, and therefore **`sorryAx`-tainted**: measured cone 3694 with
holes `{IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}`, all three
inherited from the reduction rather than from the residual, and none of them repaired by
inhabitation.  Kept for exactly that contrast with the hole-free row above.  Read with §2 as
well: that environment is inconsistent and has no uninhabited binder at any well-formed
context, so it is a satisfiability witness, not evidence about the obstruction. -/
theorem exists_univInhabEnv_trProj_weak'_inv :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ {U : Nat} {Γ Γ' : List VExpr} {l : Lift}
      {s : Lean.Name} {i : Nat} {e e' : VExpr}, OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e'' := by
  obtain ⟨env, henv, hc⟩ := exists_univInhabEnv_constants
  exact ⟨env, henv, fun hΓ' W H => TrProj.weak'_inv_of_strengthen henv
    (VEnv.AllTypesInhabited.constAppTypeStrengthen henv.ordered
      (allTypesInhabited_of_univInhab hc)) hΓ' W H⟩

/-! ## 4. `ConstAppSkipUninhab` is stronger than the residual needs -/

/-- **The one-binder form's uninhabitedness premise is satisfiable unconditionally**, over every
environment, at a binder that is not a type: `.bvar 0` over `Γ = []`.  `IsDefEq.closedN'` forces
the *type* of any judgement closed, so nothing inhabits it — and by the same token
`[.bvar 0]` is not a well-formed context, so `VEnv.ConstAppTypeStrengthen`'s `OnCtx Γ'` premise
excludes this instance.  Hence satisfiability of `ConstAppSkipUninhab`'s premises is no evidence
that the residual has content, and the reduction cannot be tightened by adding `OnCtx Γ'`
without re-importing `OnCtx.weak'_inv` (i.e. `IsDefEqU.weakN_iff`) in the uninhabited branch. -/
theorem constAppSkipUninhab_uninhab_premise_illFormed {env : VEnv} {U : Nat} (henv : env.Ordered) :
    Ctx.LiftN 1 0 ([] : List VExpr) [VExpr.bvar 0] ∧
      (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 [VExpr.bvar 0] [] → ¬ env.HasType U Γ₀ e₀ A₀) ∧
      ¬ OnCtx [VExpr.bvar 0] (env.IsType U) := by
  refine ⟨.one, ?_, ?_⟩
  · intro Γ₀ A₀ e₀ hI h
    cases hI
    have := (h.closedN' henv.closed trivial).2.2
    simp [VExpr.ClosedN] at this
  · rintro ⟨-, u, h⟩
    have := (h.closedN' henv.closed trivial).1
    simp [VExpr.ClosedN] at this

end Lean4Lean
