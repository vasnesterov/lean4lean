import Lean4Lean.Theory.Typing.AppUniqWF
import Lean4Lean.Theory.Typing.ShapeSpine

/-!
# `AppCodType0On` is FALSE — the `OnCtx` guard does not repair it

`Theory/Typing/AppUniqWF.lean` refutes the unguarded side condition `AppCodType0` at every
environment (`appCodType0_false_everywhere`), diagnoses the cause as *`Stratified` has no
regularity*, and proposes the `OnCtx`-guarded `AppCodType0On` as the repair, feeding
`appUniqLvlOn_of_sortRedInv_codType0On`.  It grades that hypothesis **open** and describes it
as ordinary `⊢₀` regularity.

**The diagnosis is wrong and the repair fails.**  The guard `OnCtx Γ (env.IsType U)` is not
what the refutation needs to be blocked, because the obstruction is not the *context*: it is
that `AppCodType0On` demands a typing at **index `0`**, where conversion is syntactic equality
(`IsDefEqN.zero_iff`), while the `AppData` it is fed lives at index `n+1`.  Instantiating a
Π-codomain can *create* a β-redex whose argument is typed at the λ's annotation only at index
`≥ 1`, and such a term is `⊢₀`-typeable at **nothing at all** — regularity of the context is
irrelevant.

The witness is `SubstCRefute`'s, which is exactly this phenomenon, and `ShapeAgreeRefute`
already checked (`P_type`) that its context entry is a genuine Π-type — i.e. that "the
refutation does not turn on the absence of an `OnCtx` hypothesis", in that file's own words.
This file supplies the missing pieces: the context guard as `OnCtx` literally requires it (in
the *unstratified* judgment, which is what `env.IsType U` means — `Stratified` has no
soundness direction, so `P_type` does not give it), and a **parameter-free** rebuild of the
witness, since `SubstCRefute` uses `.param 0` and so lives only at `U ≥ 1`, while the target
is `U = 0` and the family is *antitone* in `U`.

## What is refuted, exactly

`¬ AppCodType0On env U (n+1)` for **every** `env`, **every** `U`, **every** `n` (§3).  So
`appUniqLvlOn_of_sortRedInv_codType0On` is vacuous everywhere, exactly like its unguarded
predecessor, and the `AppUniqWF.lean` verdict's "not proved, and not refuted:
`AppCodType0On`" is now settled in the negative.

Note the two axes this fixes relative to the older refutation: `appCodType0_false_everywhere`
is stated only at `U = 0, n = 1` and its witness *needs* the guard to be absent (its context
entry is a λ-term).  The witness here satisfies the guard, and lives at every `U` and every
index.

## What is **not** refuted, and is the thing to pick up

The *conditioned* side condition `AppCodType0OnC` (§4), which asks for the `⊢₀` typings only
of codomain instances that are already `⊢ₙ₊₁`-convertible to sorts — i.e. only in the case
`AppUniqLvlOn` actually reaches.  It is a *weaker* hypothesis, it still proves
`AppUniqLvlOn` (`appUniqLvlOn_of_sortRedInv_codType0OnC`), and this file's witness provably
does **not** refute it (§5: the stuck codomain is `⊢₁`-convertible to no sort at all, so it
never enters the conditioned statement's premises).  Its status is open.

But §4 also prices it, and the price is bad: with `SortRedInv` in hand the conditioned
hypothesis yields **full level agreement** `u ≈ v` (`appLvlAgreeOn_of_sortRedInv_codType0OnC`),
which is strictly stronger than `AppUniqLvlOn`'s `u ≈ 0 ↔ v ≈ 0`.  So the route does not
reduce its target to anything weaker: whoever proves the side condition has proved the target
and more.  Graded as such, not as a reduction.
-/
namespace Lean4Lean
namespace VEnv

namespace CodType0Refute

open VExpr

/-! ## 1. The parameter-free witness

`SubstCRefute` needs one universe parameter only to have a level that is `≈`-equal to another
without being syntactically equal.  `.max .zero .zero` does that with no parameter, so every
declaration below is at an arbitrary `U` — including `U = 0`, which is where the target lives
and where `SubstCRefute`'s own witness is unavailable. -/

/-- `max 0 0` — `≈`-equal to `.zero`, and not equal to it. -/
def q : VLevel := .max .zero .zero

/-- The argument.  Its unique `⊢₀` type is `.sort (.succ q)`, so it is typed at `A` only from
index `1` up. -/
def a : VExpr := .sort q

/-- The λ's annotation, and `a`'s type from index `1`. -/
def A : VExpr := .sort (.succ .zero)

/-- The Π-body: a β-redex in the bound variable. -/
def D : VExpr := .app (.lam A (.bvar 0)) (.bvar 0)

/-- The context entry.  Closed, so `P.lift = P`, and a genuine Π-type (§2). -/
def P : VExpr := .forallE A D

/-- `D.inst a` — the codomain instance, and the term with no `⊢₀` type whatever. -/
def lhs : VExpr := .app (.lam A (.bvar 0)) a

theorem P_lift : P.lift = P := rfl

theorem D_inst : D.inst a = lhs := rfl

theorem q_wf : q.WF U := ⟨trivial, trivial⟩

theorem succ_q_equiv : VLevel.succ q ≈ VLevel.succ .zero := by
  simp [VLevel.equiv_def, VLevel.eval, q]

variable {env : VEnv} {U : Nat}

/-! ## 2. `a` at `A` from index 1, and never at index 0 -/

theorem a_hasType1 {Γ : List VExpr} : env.HasTypeN U 1 Γ a A :=
  .conv (.sortDF (l := .succ q) (l' := .succ .zero) q_wf trivial succ_q_equiv)
    (.sort q_wf)

theorem a_hasTypeN {Γ : List VExpr} {n : Nat} : env.HasTypeN U (n+1) Γ a A :=
  a_hasType1.mono (Nat.succ_le_succ (Nat.zero_le _))

theorem a_not_hasType0 {Γ : List VExpr} : ¬ env.HasTypeN U 0 Γ a A := by
  intro H
  have h := IsDefEqN.zero_iff.1 (HasTypeN.sort_inv H).2
  simp [A, q] at h

/-- **The codomain instance is `⊢₀`-typeable at no type at all** — in any context, at any
`U`, over any environment.  Typing it would need `a` at the λ's *annotation* `A`, and at index
`0` conversion is syntactic equality. -/
theorem lhs_not_hasType0 {Γ : List VExpr} {T : VExpr} : ¬ env.HasTypeN U 0 Γ lhs T := by
  intro H
  have ⟨C, _, hlam, hA, _⟩ := HasTypeN.app_inv H
  have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hlam
  injection IsDefEqN.zero_iff.1 heq with hAC
  exact a_not_hasType0 (hAC ▸ hA)


/-! ## 3. The context entry is a genuine type, in the sense `OnCtx` means it

`ShapeAgreeRefute.P_type` types `P` in the **stratified** judgment.  That is not what the
guard asks for: `env.IsType U` is the *unstratified* `IsDefEq`, and `Stratified.lean` has only
the `HasType → HasTypeN` direction (`HasType.stratifyN`), not its converse.  So the guard has
to be built directly, which is three constructors. -/

theorem A_hasType {Γ : List VExpr} :
    env.HasType U Γ A (.sort (.succ (.succ .zero))) := .sortDF trivial trivial rfl

theorem lam_hasType : env.HasType U [A] (.lam A (.bvar 0)) (.forallE A A) :=
  .lamDF A_hasType (.bvar Lookup.zero)

theorem D_hasType : env.HasType U [A] D (.sort (.succ .zero)) :=
  .appDF lam_hasType (.bvar Lookup.zero)

theorem P_hasType :
    env.HasType U [] P (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  .forallEDF A_hasType D_hasType

theorem P_isType : env.IsType U [] P := ⟨_, P_hasType⟩

/-- **The guard is satisfied.**  This is the hypothesis `AppUniqWF.lean` §"the repaired side
condition" expected to exclude the counterexample. -/
theorem onCtx : OnCtx [P] (env.IsType U) := ⟨trivial, P_isType⟩

/-! ## 4. The `AppData`, at every index `n+1` -/

theorem hx {n : Nat} : env.HasTypeN U (n+1) [P] (.bvar 0) P :=
  P_lift ▸ Stratified.bvar Lookup.zero

theorem hbeta {n : Nat} : env.IsDefEqN U (n+1) [A, P] D (.bvar 0) :=
  .beta (.bvar .zero) (.bvar .zero)

/-- `forallEDF` carries no typing premises, so the β step on the body lifts to the Π for
free — the step that also refutes the instantiated form of `DefInv`'s clause (2). -/
theorem hpi {n : Nat} : env.IsDefEqN U (n+1) [P] P (.forallE A (.bvar 0)) :=
  .forallEDF .rfl hbeta

theorem hx2 {n : Nat} : env.HasTypeN U (n+1) [P] (.bvar 0) (.forallE A (.bvar 0)) :=
  .conv hpi hx

/-- One function, one argument, two Π-types — and the *same* domain in both, so no domain
mismatch is involved. -/
theorem witness {n : Nat} : AppData env U (n+1) [P] (.bvar 0) a A D A (.bvar 0) :=
  ⟨hx, a_hasTypeN, hx2, a_hasTypeN⟩

end CodType0Refute

/-! ## 5. The refutation -/

/-- **`AppCodType0On` is false at every environment, every `U`, and every index.**

So `appUniqLvlOn_of_sortRedInv_codType0On` is vacuous everywhere and the `OnCtx` guard is not
the repair: the counterexample's context entry `∀ (_ : Type 0), (fun _ : Type 0 => x) x` is a
genuine type (`CodType0Refute.onCtx`), and the codomain instance
`(fun _ : Type 0 => x) (Sort (max 0 0))` is `⊢₀`-typeable at *nothing*
(`CodType0Refute.lhs_not_hasType0`), let alone at a sort. -/
theorem appCodType0On_false (env : VEnv) (U n : Nat) : ¬ AppCodType0On env U (n+1) := by
  intro h
  obtain ⟨v, v', h₀, -, -⟩ := h CodType0Refute.onCtx CodType0Refute.witness
  exact CodType0Refute.lhs_not_hasType0 (CodType0Refute.D_inst ▸ h₀)

/-- Stated the way the consumer sees it: the guarded conditional is vacuous. -/
theorem appUniqLvlOn_of_sortRedInv_codType0On_vacuous (env : VEnv) (U n : Nat) :
    ¬ AppCodType0On env U (n+1) := appCodType0On_false env U n

/-! ### The `∅` argument does **not** apply here, and does not need to

`AppUniqWF.lean` §4's obstruction (`no_wf_hypothesis_avoids_empty`) applies to hypotheses
`H : VEnv → Prop` that `VEnv.WF` implies, and works because the *conclusion* is antitone in the
environment.  `AppCodType0On` is neither monotone nor antitone: its premise `AppData` is
monotone in the environment (`AppData.mono_env`) and so is its conclusion (`Stratified.mono_env`),
so the environment occurs in both a negative and a positive position and no bound in either
direction follows formally.

That is why the refutation above is stated over an arbitrary environment directly rather than
transported from `∅`: every derivation in it is structural, and the one *negative* fact
(`lhs_not_hasType0`) is proved from `⊢₀` inversion and `IsDefEqN.zero_iff`, which are
unconditional in the environment.  A δ-rule cannot rescue it, because a `⊢₀` typing may not use
one (`extra` concludes at `n+1`).

For the record, the two directions that *are* available: -/

theorem AppCodType0On.premise_mono {env env' : VEnv} (le : env ≤ env')
    {U n : Nat} {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U n Γ f a A₀ B₀ A₁ B₁) :
    OnCtx Γ (env'.IsType U) ∧ AppData env' U n Γ f a A₀ B₀ A₁ B₁ :=
  ⟨hΓ.mono fun ht => ht.mono le, d.mono_env le⟩

/-! ## 6. The conditioned repair, and the collapse it hides

The side condition is over-strong for a boring reason: it demands the `⊢₀` typings of *every*
codomain instance, including instances that are `⊢ₙ₊₁`-convertible to no sort at all and so are
never reached by `AppUniqLvlOn`.  Conditioning on the two conversions the consumer already has
removes the counterexample above (§7) and still proves the target.

That is the repair.  It is also a **collapse**, and this section proves it rather than
asserting it: on the sub-family where both codomain instances are literally sorts — where the
conditioned hypothesis is *not* vacuous — it is **equivalent** to full level agreement for the
`app` case, which is the target's own clause, strengthened.  So the route's side condition
cannot be discharged by anything weaker than the thing it was introduced to prove. -/

/-- The conditioned side condition: the `⊢₀` typings, asked for only where `AppUniqLvlOn`
needs them. -/
def AppCodType0OnC (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) →
    ∃ w w' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort w) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort w') ∧ w ≈ w'

/-- **Full level agreement for the `app` case**, guarded.  Strictly stronger, as a conclusion,
than `AppUniqLvlOn`'s `u ≈ 0 ↔ v ≈ 0` (`lvlAgree_strictly_stronger`). -/
def AppLvlAgreeOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) → u ≈ v

variable {env : VEnv} {U n : Nat}

/-- `AppCodType0On` is the unconditioned form, so it implies the conditioned one — which is
another way of seeing that the conditioned one is the weaker hypothesis (and, unlike the
unconditioned one, not yet refuted). -/
theorem AppCodType0On.conditioned (h : AppCodType0On env U n) : AppCodType0OnC env U n :=
  fun hΓ d _ _ => h hΓ d

/-- The conclusion gap is real: agreement is strictly stronger than the `Prop`-iff. -/
theorem lvlAgree_strictly_stronger :
    ∃ u v : VLevel, (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel)) ∧ ¬ u ≈ v :=
  ⟨.succ .zero, .succ (.succ .zero),
    ⟨fun h => absurd (congrFun h []) (by simp [VLevel.eval]),
     fun h => absurd (congrFun h []) (by simp [VLevel.eval])⟩,
    fun h => by simpa [VLevel.eval] using congrFun h []⟩

theorem appUniqLvlOn_of_appLvlAgreeOn (h : AppLvlAgreeOn env U n) : AppUniqLvlOn env U n := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  have := h hΓ d c₀ c₁
  exact ⟨fun h' => this.symm.trans h', fun h' => this.trans h'⟩

/-- **The conditioned repair does prove the target** — through full agreement, which is the
first half of the collapse. -/
theorem appLvlAgreeOn_of_sortRedInv_codType0OnC (henv : Ordered env)
    (hinv : SortRedInv env U (n+1)) (hct : AppCodType0OnC env U (n+1)) :
    AppLvlAgreeOn env U (n+1) := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  obtain ⟨w, w', h₀, h₁, hww'⟩ := hct hΓ d c₀ c₁
  exact SortRed.type0_agree' henv h₀ h₁ hww' ((hinv c₀).2 (.sort rfl)) ((hinv c₁).2 (.sort rfl))

theorem appUniqLvlOn_of_sortRedInv_codType0OnC (henv : Ordered env)
    (hinv : SortRedInv env U (n+1)) (hct : AppCodType0OnC env U (n+1)) :
    AppUniqLvlOn env U (n+1) :=
  appUniqLvlOn_of_appLvlAgreeOn (appLvlAgreeOn_of_sortRedInv_codType0OnC henv hinv hct)

/-- **The other half: the converse on the sort sub-family.**  When both codomain instances are
literally sorts with well-formed levels — the case where the conditioned hypothesis has any
content, since a `⊢₀` typing of a sort is forced (`Stratified.sort`) and its level is forced by
`HasTypeN.uniq_zero` — the conditioned hypothesis *is* full level agreement, modulo `SortInvN`,
which `SortRedInv` already supplies (`sortInvN_of_sortRedInv`).

So `AppCodType0OnC` is not a weaker obligation than the target: on the only instances where it
says anything, it says exactly `AppLvlAgreeOn`. -/
theorem codType0OnC_sortCase_iff_agree (hsi : SortInvN env U (n+1))
    {Γ : List VExpr} {a B₀ B₁ : VExpr} {u₀ u₁ u v : VLevel}
    (hu₀ : u₀.WF U) (hu₁ : u₁.WF U)
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (c₀ : env.IsDefEqN U (n+1) Γ (B₀.inst a) (.sort u))
    (c₁ : env.IsDefEqN U (n+1) Γ (B₁.inst a) (.sort v)) :
    (∃ w w' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort w) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort w') ∧ w ≈ w') ↔ u ≈ v := by
  have h₀ : u₀ ≈ u := hsi (e₀ ▸ c₀)
  have h₁ : u₁ ≈ v := hsi (e₁ ▸ c₁)
  constructor
  · rintro ⟨w, w', hw, hw', hww'⟩
    have t₀ : env.HasTypeN U 0 Γ (B₀.inst a) (.sort (.succ u₀)) := e₀ ▸ .sort hu₀
    have t₁ : env.HasTypeN U 0 Γ (B₁.inst a) (.sort (.succ u₁)) := e₁ ▸ .sort hu₁
    injection HasTypeN.uniq_zero t₀ hw with hw₀
    injection HasTypeN.uniq_zero t₁ hw' with hw₁
    exact h₀.symm.trans
      ((VLevel.succ_congr_iff.1 (hw₀ ▸ hw₁ ▸ hww')).trans h₁)
  · intro huv
    exact ⟨.succ u₀, .succ u₁, e₀ ▸ .sort hu₀, e₁ ▸ .sort hu₁,
      VLevel.succ_congr_iff.2 (h₀.trans (huv.trans h₁.symm))⟩

/-- `SortInvN` is free in the route's own hypotheses, so the converse direction above costs the
route nothing it does not already assume. -/
theorem sortInvN_of_route (hinv : SortRedInv env U (n+1)) : SortInvN env U (n+1) :=
  sortInvN_of_sortRedInv hinv

/-- The collapse, stated as one theorem: **on the sort sub-family the conditioned side
condition and the strengthened target are the same statement.**  Read with
`appLvlAgreeOn_of_sortRedInv_codType0OnC`: the hypothesis implies the strengthened target
outright, and the strengthened target implies the hypothesis wherever the hypothesis is not
vacuous.  Nothing in between is being reduced. -/
theorem codType0OnC_sortCase_of_agree (hsi : SortInvN env U (n+1)) (h : AppLvlAgreeOn env U (n+1))
    {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u₀ u₁ u v : VLevel}
    (hu₀ : u₀.WF U) (hu₁ : u₁.WF U)
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (hΓ : OnCtx Γ (env.IsType U)) (d : AppData env U (n+1) Γ f a A₀ B₀ A₁ B₁)
    (c₀ : env.IsDefEqN U (n+1) Γ (B₀.inst a) (.sort u))
    (c₁ : env.IsDefEqN U (n+1) Γ (B₁.inst a) (.sort v)) :
    ∃ w w' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort w) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort w') ∧ w ≈ w' :=
  (codType0OnC_sortCase_iff_agree hsi hu₀ hu₁ e₀ e₁ c₀ c₁).2 (h hΓ d c₀ c₁)

/-! ## 7. Testing the repair against this file's own witness

`AppUniqWF.lean`'s §"what would have been the sixth shape" is the reason this section exists: a
side condition must be tested before it is shipped.  The conditioned form is only worth stating
if the counterexample above does **not** also refute it, and that is a real obligation, not a
formality — it says the stuck codomain instance is `⊢₁`-convertible to *no sort*, so it never
enters `AppCodType0OnC`'s premises.

`SubstCRefute.stuck` proves exactly this for the parameterised witness; it is re-proved here for
the parameter-free one, over `∅` — the `extra` case is where an arbitrary environment would leave
a hole, so this half is `∅`-only, unlike §5. -/

namespace CodType0Refute

/-- `lhs` is `⊢₁`-related to nothing but itself, over `∅`, at every `U`.  Verbatim
`SubstCRefute.stuck`, with the parameter-free `a` and `lhs`. -/
theorem stuck {U : Nat} {Γ X Y m b} (H : Stratified (∅ : VEnv) U m Γ X Y b)
    (hm : 1 = m) (hb : false = b) :
    (X = lhs → Y = lhs) ∧ (Y = lhs → X = lhs) := by
  induction H with cases hb
  | rfl => exact ⟨id, id⟩
  | symm _ ih => exact ((ih hm rfl).symm : _ ∧ _)
  | trans _ _ ih1 ih2 =>
    exact ⟨fun h => (ih2 hm rfl).1 ((ih1 hm rfl).1 h),
      fun h => (ih1 hm rfl).2 ((ih2 hm rfl).2 h)⟩
  | sortDF | constDF | lamDF | forallEDF =>
    constructor <;> (intro h; simp [lhs] at h)
  | appDF _ hf hf' _ ha ha' =>
    cases hm
    constructor
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha) a_not_hasType0
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf'
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha') a_not_hasType0
  | beta he he' =>
    cases hm
    refine ⟨?_, ?_⟩
    · rintro ⟨⟩; exact absurd he' a_not_hasType0
    · rintro h
      exact absurd (h ▸ Stratified.instN .empty he' .zero he) lhs_not_hasType0
  | eta he =>
    cases hm
    constructor
    · intro h; simp [lhs] at h
    · intro h; exact absurd (h ▸ he) lhs_not_hasType0
  | proofIrrel _ hh hh' =>
    cases hm
    exact ⟨fun h => absurd (h ▸ hh) lhs_not_hasType0,
      fun h => absurd (h ▸ hh') lhs_not_hasType0⟩
  | extra h => exact nomatch h

/-- **The stuck codomain instance is `⊢₁`-convertible to no sort.** -/
theorem lhs_not_defeq_sort {U : Nat} {Γ : List VExpr} {u : VLevel} :
    ¬ (∅ : VEnv).IsDefEqN U 1 Γ lhs (.sort u) := fun h =>
  absurd ((stuck h rfl rfl).1 rfl) (by simp [lhs])

/-- **So the witness of §5 does not refute the conditioned side condition**: the premise
`AppUniqLvlOn` and `AppCodType0OnC` share — that the first codomain instance is convertible to a
sort — is unsatisfiable at it.  The refutation of §5 is therefore *exactly* a refutation of the
unconditioned quantifier, and nothing more. -/
theorem witness_outside_conditioned {U : Nat} {u : VLevel} :
    ¬ (∅ : VEnv).IsDefEqN U 1 [P] (D.inst a) (.sort u) :=
  fun h => lhs_not_defeq_sort (D_inst ▸ h)

/-- The failure is one-sided: the *second* codomain instance is a sort on the nose. -/
theorem witness_snd_is_sort : ((VExpr.bvar 0).inst a) = .sort q := rfl

end CodType0Refute

/-! ## 9. The collapse is intrinsic to the `⊢₀`-pin, not an artefact of this side condition

One might hope the side condition is merely clumsily stated — that asking for the codomain
instances to be `⊢₀`-typed *at sorts*, with `≈`-equal levels, is more than the pin needs.  It
is: **sort-ness is free**, and so is the level relation.  `SortRed.type0_pin` generalises to an
arbitrary `⊢₀` type, because `HeadBeta` preserves `⊢₀` typing and the base case's type is forced
by `HasTypeN.sort_inv`.

So the weakest side condition of this shape is "**the two codomain instances share a `⊢₀`
type**" — no regularity, no levels.  And *that* one still collapses: on the sort sub-family it
forces the two levels to be **syntactically equal**, which is strictly more than the `≈`
agreement of §6, which is in turn strictly more than the target.  The collapse is therefore a
property of the pin, not of the way the hypothesis was phrased. -/

/-- **`SortRed.type0_pin` with the sort dropped from the hypothesis.**  If `X` weak-head reduces
to a sort of level `≈ u` and `X` has *any* `⊢₀` type, that type is `.sort (.succ w)` with
`w ≈ u`.  Strictly more general than `AppUniqWF.lean`'s `SortRed.type0_pin`, same proof. -/
theorem SortRed.type0_pin_any (henv : Ordered env) {Γ : List VExpr} {X T : VExpr} {u : VLevel}
    (hr : SortRed u X) : env.HasTypeN U 0 Γ X T → ∃ w, w ≈ u ∧ T = .sort (.succ w) := by
  induction hr with
  | @sort w h =>
    intro hX
    exact ⟨w, h, (IsDefEqN.zero_iff.1 (HasTypeN.sort_inv hX).2).symm⟩
  | step hb _ ih => exact fun hX => ih (hb.hasTypeN_zero henv hX)

/-- The weakest side condition that feeds the pin: the two codomain instances share a `⊢₀`
type.  Conditioned, like §6's, so this file's witness does not refute it either. -/
def AppCodShareOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) →
    ∃ T : VExpr, env.HasTypeN U 0 Γ (B₀.inst a) T ∧ env.HasTypeN U 0 Γ (B₁.inst a) T

/-- It is weaker than §6's: the sorts and the level relation come for free from the pin. -/
theorem AppCodType0OnC.share (henv : Ordered env) (hinv : SortRedInv env U (n+1))
    (h : AppCodShareOn env U (n+1)) : AppCodType0OnC env U (n+1) := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  obtain ⟨T, h₀, h₁⟩ := h hΓ d c₀ c₁
  obtain ⟨w, hw, rfl⟩ := (SortRed.type0_pin_any henv ((hinv c₀).2 (.sort rfl))) h₀
  exact ⟨.succ w, .succ w, h₀, h₁, rfl⟩

theorem appLvlAgreeOn_of_sortRedInv_codShareOn (henv : Ordered env)
    (hinv : SortRedInv env U (n+1)) (h : AppCodShareOn env U (n+1)) :
    AppLvlAgreeOn env U (n+1) :=
  appLvlAgreeOn_of_sortRedInv_codType0OnC henv hinv (AppCodType0OnC.share henv hinv h)

/-- **And the weakest form collapses hardest.**  On the sort sub-family it is *syntactic*
equality of the two levels — strictly stronger than `≈`-agreement, which is strictly stronger
than the target's `Prop`-iff.  So no restatement of the side condition escapes: every
sufficient hypothesis of this shape decides the app case's two levels outright. -/
theorem codShareOn_sortCase_forces_syntactic_eq
    {Γ : List VExpr} {a B₀ B₁ : VExpr} {u₀ u₁ : VLevel}
    (hu₀ : u₀.WF U) (hu₁ : u₁.WF U)
    (e₀ : B₀.inst a = .sort u₀) (e₁ : B₁.inst a = .sort u₁)
    (h : ∃ T : VExpr, env.HasTypeN U 0 Γ (B₀.inst a) T ∧ env.HasTypeN U 0 Γ (B₁.inst a) T) :
    u₀ = u₁ := by
  obtain ⟨T, h₀, h₁⟩ := h
  have t₀ : env.HasTypeN U 0 Γ (B₀.inst a) (.sort (.succ u₀)) := e₀ ▸ .sort hu₀
  have t₁ : env.HasTypeN U 0 Γ (B₁.inst a) (.sort (.succ u₁)) := e₁ ▸ .sort hu₁
  simpa using (HasTypeN.uniq_zero t₀ h₀).trans (HasTypeN.uniq_zero t₁ h₁).symm

/-! ## 10. Verdict

**Refuted** (machine-checked, `sorryAx`-free):

* `AppCodType0On env U (n+1)` at **every** environment, **every** `U`, **every** index
  (`appCodType0On_false`).  The `OnCtx` guard is satisfied by the witness
  (`CodType0Refute.onCtx`), so the guard is *not* the repair, and `AppUniqWF.lean`'s reading of
  the earlier refutation — "for lack of *regularity*" — is the wrong diagnosis.  The cause is the
  **index-0 demand**: `⊢₀` has syntactic conversion, and instantiating a Π-codomain can create a
  β-redex whose argument is typed at the λ's annotation only from index 1 up, which is
  `⊢₀`-typeable at nothing at all.
* Consequently `appUniqLvlOn_of_sortRedInv_codType0On` is **vacuous everywhere**, joining
  `appUniqLvl_of_sortRedInv_codType0`.  Nothing about `AppUniqLvlOn` is discharged by either.

**Open, and priced**: `AppCodType0OnC`, the conditioned side condition (§6).  It is genuinely
weaker (`AppCodType0On.conditioned`), it still proves the target
(`appUniqLvlOn_of_sortRedInv_codType0OnC`), and this file's witness provably does **not** refute
it (`CodType0Refute.witness_outside_conditioned`) — tested, not assumed.

**But the route is closed, not merely expensive.**  Graded in this corner's vocabulary:

1. **The conditioned repair is a collapse.**  With `SortRedInv` it yields *full* level agreement
   `u ≈ v` (`appLvlAgreeOn_of_sortRedInv_codType0OnC`), strictly stronger as a conclusion than the
   target's `u ≈ 0 ↔ v ≈ 0` (`lvlAgree_strictly_stronger`); and on the sub-family where it is not
   vacuous — both codomain instances literally sorts — it is **equivalent** to that stronger
   statement (`codType0OnC_sortCase_iff_agree`, both directions, modulo `SortInvN`, which
   `SortRedInv` supplies free via `sortInvN_of_sortRedInv`).  So the "reduction" reduces the app
   case to the app case, strengthened.  Anyone who proves the side condition has proved the target
   and more; the route buys nothing.
2. **Hole-free ≠ discharged**, separately as always.  Every declaration here is hole-free and
   none of the four big holes is in any cone (§9).  **Discharged: nothing.**  What is *settled* is
   one hypothesis' truth value — negatively — and one route's grade.
3. **The refutation is one-way in the useful direction.**  It is stated over an arbitrary
   environment, so it applies at `preludeEnv` and at every `VEnv.WF` environment, without going
   through the `∅` bound (which does not apply here at all — §5's note).
-/

section Audit

/-! `#print axioms`, by namespace.  `CodType0Refute` first: the witness. -/
#print axioms Lean4Lean.VEnv.CodType0Refute.q
#print axioms Lean4Lean.VEnv.CodType0Refute.a
#print axioms Lean4Lean.VEnv.CodType0Refute.A
#print axioms Lean4Lean.VEnv.CodType0Refute.D
#print axioms Lean4Lean.VEnv.CodType0Refute.P
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs
#print axioms Lean4Lean.VEnv.CodType0Refute.P_lift
#print axioms Lean4Lean.VEnv.CodType0Refute.D_inst
#print axioms Lean4Lean.VEnv.CodType0Refute.q_wf
#print axioms Lean4Lean.VEnv.CodType0Refute.succ_q_equiv
#print axioms Lean4Lean.VEnv.CodType0Refute.a_hasType1
#print axioms Lean4Lean.VEnv.CodType0Refute.a_hasTypeN
#print axioms Lean4Lean.VEnv.CodType0Refute.a_not_hasType0
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs_not_hasType0
#print axioms Lean4Lean.VEnv.CodType0Refute.A_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.lam_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.D_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.P_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.P_isType
#print axioms Lean4Lean.VEnv.CodType0Refute.onCtx
#print axioms Lean4Lean.VEnv.CodType0Refute.hx
#print axioms Lean4Lean.VEnv.CodType0Refute.hbeta
#print axioms Lean4Lean.VEnv.CodType0Refute.hpi
#print axioms Lean4Lean.VEnv.CodType0Refute.hx2
#print axioms Lean4Lean.VEnv.CodType0Refute.witness
#print axioms Lean4Lean.VEnv.CodType0Refute.stuck
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs_not_defeq_sort
#print axioms Lean4Lean.VEnv.CodType0Refute.witness_outside_conditioned
#print axioms Lean4Lean.VEnv.CodType0Refute.witness_snd_is_sort

/-! `Lean4Lean.VEnv`: the refutation, the conditioned repair, and the collapse. -/
#print axioms Lean4Lean.VEnv.appCodType0On_false
#print axioms Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0On_vacuous
#print axioms Lean4Lean.VEnv.AppCodType0On.premise_mono
#print axioms Lean4Lean.VEnv.AppCodType0OnC
#print axioms Lean4Lean.VEnv.AppLvlAgreeOn
#print axioms Lean4Lean.VEnv.AppCodType0On.conditioned
#print axioms Lean4Lean.VEnv.lvlAgree_strictly_stronger
#print axioms Lean4Lean.VEnv.appUniqLvlOn_of_appLvlAgreeOn
#print axioms Lean4Lean.VEnv.appLvlAgreeOn_of_sortRedInv_codType0OnC
#print axioms Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0OnC
#print axioms Lean4Lean.VEnv.sortInvN_of_route
#print axioms Lean4Lean.VEnv.codType0OnC_sortCase_iff_agree
#print axioms Lean4Lean.VEnv.codType0OnC_sortCase_of_agree
#print axioms Lean4Lean.VEnv.SortRed.type0_pin_any
#print axioms Lean4Lean.VEnv.AppCodShareOn
#print axioms Lean4Lean.VEnv.AppCodType0OnC.share
#print axioms Lean4Lean.VEnv.appLvlAgreeOn_of_sortRedInv_codShareOn
#print axioms Lean4Lean.VEnv.codShareOn_sortCase_forces_syntactic_eq

end Audit

end VEnv
end Lean4Lean
