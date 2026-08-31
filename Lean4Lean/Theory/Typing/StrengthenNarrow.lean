import Lean4Lean.Theory.Typing.Strengthen

/-!
# The `trans` residual of strengthening, narrowed to a middle term that is not a lift

This file is round 5 of the attack on `VEnv.IsDefEqU.weakN_iff`
(`Theory/Typing/UniqueTyping.lean:172`, the `sorry` at `:174`).  Rounds 1-4 are recorded in
`docs/handoff-weakn.md` and in `Theory/Typing/Strengthen{,Axiom,Canon,Verdict,Witness}.lean`.
Read those first: the direct, untyped, model-theoretic and Church-Rosser routes are all
foreclosed there, and this file does not reopen any of them.

## What round 4 left standing, and why it was not yet a reduction

`Strengthen.lean` §5 maps the induction: of the twelve conversion rules, **eleven close from
`TypingStrengthening` alone**, and only `trans` is left.  §9 then observes that the residual
`TransStrengthening` is *not* a reduction at all — instantiate its middle term `b` at
`e2.liftN n k` and its second premise at the reflexivity the first one already supplies, and
you get `Strengthening` back (`TransStrengthening.strengthening`).  So §8's capstone
`Strengthening ↔ SortDescend ∧ PiDescend ∧ TransStrengthening` is a tautology in the `←`
direction: the third conjunct does all the work and the first two are decoration.

That is the defect this file repairs.

## The narrowing

The self-instantiation of §9 works only because the middle term it picks, `e2.liftN n k`, is
*itself in the image of the lift*.  But when the middle term is in the image of the lift, the
two induction hypotheses of the `trans` case are **not** vacuous: they apply verbatim, and
`IsDefEqU.trans` composes them.  So the residual may be restricted to middle terms that
genuinely mention one of the stripped variables — exactly `¬ b.Skips n k`, by
`VExpr.skips_iff_exists` — and the restriction kills the self-instantiation
(`TransStrengtheningNarrow.not_hyp_of_lifted`).

`TransStrengtheningNarrow` (§1) is that residual.  Beyond the non-lift hypothesis it also
carries everything the `trans` case has in hand at that point and previously threw away: a
*type downstairs* for the left endpoint, well-formedness downstairs of the right endpoint, and
both premises retyped at a **lifted** type.  Those three are free at the call site (§2) because
`TypingStrengthening` supplies them, so including them costs nothing and makes the residual
strictly weaker — i.e. a strictly better target for a future round.

* §1 the statement, and `Strengthening.transNarrow` (the converse, one line).
* §2 `Strengthening.of_typing_narrow` — `of_typing` with only its `trans` case changed.  The
  positive branch is where the two hypotheses that `of_typing` discards get used.
* §3 the capstones: `Strengthening.iff_typing_narrow`,
  `StrengtheningTarget.iff_typing_narrow` and `Strengthening.iff_descend_narrow`.  Unlike
  §8/§9 of `Strengthen.lean` these are **not** tautologies: the `←` direction genuinely needs
  both conjuncts, because the narrow residual cannot be self-instantiated.
* §4 negative controls: the excluded instantiation, and vacuity of the residual at `n = 0`.
* §5 **nine of the hole's wrappers need only the typing half.**
  `Theory/Typing/UniqueTyping.lean` proves `OnCtx.weakN_inv`, `HasType.weakN_iff`,
  `IsType.weakN_iff`, `VExpr.WF.weakN_iff`, `HasType.skips` and the four `weak'` analogues
  from the full *conversion* form; none of them needs it.  §5 reproves all nine from
  `TypingStrengthening` — equivalently, by `Strengthen.lean` §7/§9(b), from `PiDescend` — and
  that splits the hole's 131 transitive users in two.  **Measured**
  (`scripts/weakn-gate-split.lean`, reverse reachability with those nine cut): 18 of the 131
  are freed by the typing half alone, and **113 still need the narrow `trans` residual**,
  reaching the hole through `IsDefEq.weakN_iff{,'}`, `IsDefEqU.weak'_iff`,
  `IsDefEq.weak'_iff` or `IsDefEq.skips`.  So shape descent is *not* the bottleneck: the
  residual of §1 is where the 113 sit.  That is an argument for spending the next round on
  §1 and not on `PiDescend`.

## Circularity, measured (`scripts/hole-cone.lean`'s `deps`, `allowOpaque := true`)

The question "does weakN_iff's own would-be proof route pass back through
`WF.rigidShapeUniq` or `IsDefEqU.forallE_inv_stratified`?" has a split answer, and the split
matters:

| route | named holes in its cone |
| --- | --- |
| `strengthen_of_instN`, `Strengthening.iff_trans`, `Strengthening.iff_target`, `Strengthening1.iff_target`, `Strengthening1Uninhab.iff_target`, `StrengtheningCanon.iff_target`, `StrengtheningCanonUninhab.iff_strengthening1`, `strengtheningTarget_of_allInhabited`, `TypingStrengthening.iff_descend` | none |
| `Strengthening.of_typing`, `TypingStrengthening.iff_piDescend`, `PiDescend.sortDescend`, `TypingStrengthening.typed` | `WF.rigidShapeUniqNS`, `IsDefEqU.forallE_inv_stratified` |
| `Strengthening.iff_typed` | `IsDefEqU.forallE_inv_stratified` |
| `IsDefEq.church_rosser`, `NormalEq.descend` | all four, `IsDefEqU.weakN_iff` included |
| this file's §1 `Strengthening.transNarrow` and all four controls of §4 | none (sorry-free) |
| this file's §2, §3, §5 | `WF.rigidShapeUniqNS`, `IsDefEqU.forallE_inv_stratified` |

(`WF.rigidShapeUniq` was renamed `WF.rigidShapeUniqNS` on 2026-08-31; the table above is the
post-rename measurement.)

So: the **equivalence chain** (this hole = one entry = one canonical entry = axiom
conservativity) is clean of the other two holes, and any refutation or model-theoretic
verdict reached along it would be independent.  Every route that passes through the *typing*
form, this file included, consumes both other holes — through `IsDefEqU.forallE_inv` in
`Strengthen.lean` §3's `TypingStrengthening.typed`, which is the ascription-redex trick, and
nowhere else.  There is no cycle: nothing in `Strengthen.lean` or this file depends on
`IsDefEqU.weakN_iff`.  The Church-Rosser route *is* cyclic, which is why it is closed.

## Verdict of round 5

The statement is believed true and is not closable by induction on the derivation.  What is
open is one statement and only one: given a `Γ'`-conversion `e1↑ ≡ b ≡ e2↑` whose middle term
`b` genuinely mentions a variable of the stripped block, produce a `Γ`-conversion.  The
reference (`~/lean-type-theory/typesys.tex:88-89`, thm:weak (3)(4)) claims this "by mutual
induction on the first hypothesis"; that proof is gapped at exactly this point, and
`TransStrengtheningNarrow` is the sharp form of the gap.  Closing it needs either a
normalisation result that pushes `b` into the image of the lift (which is what
`NormalEq`/Church-Rosser would give, and which is cyclic here for import reasons) or a model
interpreting open terms.
-/
namespace Lean4Lean
namespace VEnv

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. The narrowed residual -/

/-- **The `trans` residual, narrowed.**  `TransStrengthening` (`Strengthen.lean` §2) with four
changes, all of them free at the one call site (§2) and all of them weakening the statement:

* the middle term `b` is required **not** to be in the image of the lift (`¬ b.Skips n k`, i.e.
  `b` genuinely mentions one of the `n` stripped variables).  This is the change that matters:
  it is what stops the residual from being re-instantiated at itself the way
  `TransStrengthening.strengthening` re-instantiates `TransStrengthening`;
* the left endpoint comes with a type `T` **downstairs**;
* the right endpoint comes with well-formedness downstairs;
* the shared type of the two premises is a **lift**, namely `T.liftN n k`.

The last three are bookkeeping: the `trans` case of `Strengthening`'s induction has all three
in hand from `TypingStrengthening` and `Strengthen.lean` §5 discards them. -/
def TransStrengtheningNarrow (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n k → env.HasType U Γ e1 T → VExpr.WF env U Γ e2 →
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    env.IsDefEqU U Γ e1 e2

/-- The narrow residual is a consequence of the target, as it must be for §3 to be an
equivalence.  Every hypothesis but the two premises is discarded. -/
theorem Strengthening.transNarrow (H : Strengthening env U) :
    TransStrengtheningNarrow env U := fun W hΓ hΓ' _ _ _ h1 h2 => H W hΓ hΓ' ⟨_, h1.trans h2⟩

/-! ## 2. The reduction

`Strengthen.lean` §5's `Strengthening.of_typing`, verbatim, with **one case changed**: `trans`.

There the middle term is split on.  If it is a lift, `of_typing`'s two discarded induction
hypotheses apply directly, and `IsDefEqU.trans` (which is available because both context
hypotheses are present) composes them.  If it is not, the narrow residual applies, after
retyping both premises at a lifted type — `TypingStrengthening` gives the left endpoint a type
`T` downstairs, `T.liftN n k` and the node's own type `A` agree by `IsDefEq.uniqU`, and
`IsDefEqU.defeqDF` moves both premises across. -/

variable! (henv : VEnv.WF env) in
theorem Strengthening.of_typing_narrow (HT : TypingStrengthening env U)
    (Hn : TransStrengtheningNarrow env U) : Strengthening env U := by
  suffices H : ∀ {Γ' a b A}, env.IsDefEq U Γ' a b A → ∀ {n k Γ e1 e2}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
      e1.liftN n k = a → e2.liftN n k = b → env.IsDefEqU U Γ e1 e2 by
    intro n k Γ Γ' e1 e2 W hΓ hΓ' h
    exact have ⟨_, h⟩ := h; H h W hΓ hΓ' rfl rfl
  intro Γ' a b A H
  induction H with
  | bvar h =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases liftN_inj.1 (eq1.trans eq2.symm)
    obtain ⟨j, rfl, rfl⟩ := VExpr.liftN_eq_bvar eq1
    exact HT W hΓ hΓ' (IsDefEq.bvar h)
  | symm _ ih => exact fun W hΓ hΓ' eq1 eq2 => (ih W hΓ hΓ' eq2 eq1).symm
  | @trans _ _ mid _ _ h1 h2 ih1 ih2 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    by_cases hmid : mid.Skips n k
    · -- the middle term *is* a lift: the two induction hypotheses `of_typing` throws away
      obtain ⟨b₀, rfl⟩ := VExpr.skips_iff_exists.1 hmid
      exact (ih1 W hΓ hΓ' eq1 rfl).trans henv hΓ (ih2 W hΓ hΓ' rfl eq2)
    · -- the middle term is not a lift: the residual, at a lifted type
      subst eq1; subst eq2
      have ⟨T, hT⟩ := HT W hΓ hΓ' h1.hasType.1
      have uu := (hT.weakN henv W).uniqU henv hΓ' h1
      exact Hn W hΓ hΓ' hmid hT (HT W hΓ hΓ' h2.hasType.2)
        (IsDefEqU.defeqDF henv hΓ' uu.symm h1) (IsDefEqU.defeqDF henv hΓ' uu.symm h2)
  | sortDF h1 h2 h3 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases VExpr.liftN_eq_sort eq1; cases VExpr.liftN_eq_sort eq2
    exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases VExpr.liftN_eq_const eq1; cases VExpr.liftN_eq_const eq2
    exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 ih1 ih2 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨g, b, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq1
    obtain ⟨g', b', rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq2
    have wf : VExpr.WF env U Γ (.app g b) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.app g b).liftN n k) _ from .appDF h1.hasType.1 h2.hasType.1)
    have ⟨A₀, B₀, hg, hb⟩ := wf.app_inv henv hΓ
    exact ⟨_, .appDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hg)
      ((ih2 W hΓ hΓ' rfl rfl).of_l henv hΓ hb)⟩
  | lamDF h1 h2 ih1 ih2 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨C, d, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq1
    obtain ⟨C', d', rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq2
    have wf : VExpr.WF env U Γ (.lam C d) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.lam C d).liftN n k) _ from .lamDF h1.hasType.1 h2.hasType.1)
    have ⟨⟨u₀, hC⟩, B₀, hd⟩ := wf.lam_inv henv hΓ
    have hΓC : OnCtx (C::Γ) (env.IsType U) := ⟨hΓ, _, hC⟩
    have hbody := (ih2 W.succ hΓC ⟨hΓ', _, h1.hasType.1⟩ rfl rfl).of_l henv hΓC hd
    exact ⟨_, .lamDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hC) hbody⟩
  | forallEDF h1 h2 ih1 ih2 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨C, d, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq1
    obtain ⟨C', d', rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq2
    have ⟨_, wf⟩ : VExpr.WF env U Γ (.forallE C d) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.forallE C d).liftN n k) _ from
        .forallEDF h1.hasType.1 h2.hasType.1)
    have ⟨⟨u₀, hC⟩, v₀, hd⟩ := HasType.forallE_inv henv wf
    have hΓC : OnCtx (C::Γ) (env.IsType U) := ⟨hΓ, _, hC⟩
    have hbody := (ih2 W.succ hΓC ⟨hΓ', _, h1.hasType.1⟩ rfl rfl).of_l henv hΓC hd
    exact ⟨_, .forallEDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hC) hbody⟩
  | defeqDF _ _ _ ih2 => exact fun W hΓ hΓ' eq1 eq2 => ih2 W hΓ hΓ' eq1 eq2
  | beta h1 h2 _ _ =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨x, a₀, rfl, eqx, rfl⟩ := VExpr.liftN_eq_app eq1
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eqx.symm
    rw [← liftN_inst_hi] at eq2
    cases liftN_inj.1 eq2
    have wf : VExpr.WF env U Γ (.app (.lam A₀ b₀) a₀) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.app (.lam A₀ b₀) a₀).liftN n k) _ from
        (IsDefEq.beta h1 h2).hasType.1)
    have ⟨A', B', hlam, ha⟩ := wf.app_inv henv hΓ
    have ⟨⟨u, hA₀⟩, B₀, hb₀⟩ := hlam.lam_inv henv hΓ
    have uu := (IsDefEq.lamDF hA₀ hb₀).uniqU henv hΓ hlam
    have ⟨⟨u', hAA'⟩, _⟩ := uu.forallE_inv henv hΓ
    exact ⟨_, .beta hb₀ (ha.defeqU_r henv hΓ ⟨_, hAA'.symm⟩)⟩
  | eta h1 _ =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    subst eq2
    obtain ⟨C, d, rfl, rfl, eqd⟩ := VExpr.liftN_eq_lam eq1
    obtain ⟨x, y, rfl, eqx, eqy⟩ := VExpr.liftN_eq_app eqd.symm
    obtain ⟨j, rfl, hj⟩ := VExpr.liftN_eq_bvar eqy.symm
    cases VExpr.liftVar_eq_zero hj.symm
    rw [lift_liftN'] at eqx
    cases liftN_inj.1 eqx
    have heta := IsDefEq.eta h1
    rw [lift_liftN'] at heta
    have wf : VExpr.WF env U Γ (.lam C (.app e2.lift (.bvar 0))) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.lam C (.app e2.lift (.bvar 0))).liftN n k) _ from
        heta.hasType.1)
    have ⟨⟨u₀, hC⟩, B₀, hbody⟩ := wf.lam_inv henv hΓ
    have hlam : env.HasType U Γ (.lam C (.app e2.lift (.bvar 0))) (.forallE C B₀) :=
      .lamDF hC hbody
    have uu := (hlam.weakN henv W).uniqU henv hΓ' heta
    have h2 := (IsDefEqU.defeqDF henv hΓ' uu.symm heta).hasType.2
    exact ⟨_, .eta (HT.typed henv W hΓ hΓ' h2)⟩
  | proofIrrel h1 h2 h3 _ _ _ =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    subst eq1; subst eq2
    have ⟨C, hC1⟩ := HT W hΓ hΓ' h2
    have uu := (hC1.weakN henv W).uniqU henv hΓ' h2
    have hp : env.HasType U _ (C.liftN n k) ((VExpr.sort .zero).liftN n k) :=
      HasType.defeqU_l henv hΓ' uu.symm h1
    have hC2 := HT.typed henv W hΓ hΓ' (HasType.defeqU_r henv hΓ' uu.symm h3)
    exact ⟨_, .proofIrrel (HT.typed henv W hΓ hΓ' hp) hC1 hC2⟩
  | extra h1 h2 h3 =>
    intro n k Γ e1 e2 W hΓ hΓ' eq1 eq2
    have ⟨⟨hl, _⟩, hr, _⟩ := henv.ordered.closed.2 h1
    rw [← hl.instL.liftN_eq (n := n) (j := k) (Nat.zero_le _)] at eq1
    rw [← hr.instL.liftN_eq (n := n) (j := k) (Nat.zero_le _)] at eq2
    cases liftN_inj.1 eq1
    cases liftN_inj.1 eq2
    exact ⟨_, .extra h1 h2 h3⟩

/-! ## 3. The capstones

These supersede `Strengthen.lean` §8/§9.  There the `←` direction of the capstone was provable
from its last conjunct alone (`Strengthening.of_trans_only`); here it is not, and §4 says why
in one line. -/

variable! (henv : VEnv.WF env) in
/-- **The target is the typing half plus the narrow `trans` residual.** -/
theorem Strengthening.iff_typing_narrow :
    Strengthening env U ↔ TypingStrengthening env U ∧ TransStrengtheningNarrow env U :=
  ⟨fun H => ⟨H.typing, H.transNarrow⟩, fun ⟨h1, h2⟩ => Strengthening.of_typing_narrow henv h1 h2⟩

variable! (henv : VEnv.WF env) in
/-- The same against the hole's own statement (`Strengthen.lean` §10). -/
theorem StrengtheningTarget.iff_typing_narrow :
    StrengtheningTarget env U ↔ TypingStrengthening env U ∧ TransStrengtheningNarrow env U :=
  (Strengthening.iff_target henv).symm.trans (Strengthening.iff_typing_narrow henv)

variable! (henv : VEnv.WF env) in
/-- **`Strengthen.lean` §8's capstone, de-tautologised.**  Compare `Strengthening.iff_descend`,
whose third conjunct implies the other two and the conclusion outright. -/
theorem Strengthening.iff_descend_narrow :
    Strengthening env U ↔
      SortDescend env U ∧ PiDescend env U ∧ TransStrengtheningNarrow env U :=
  ⟨fun H => ⟨TypingStrengthening.sortDescend henv H.typing,
      TypingStrengthening.piDescend henv H.typing, H.transNarrow⟩,
   fun ⟨h1, h2, h3⟩ =>
     Strengthening.of_typing_narrow henv (TypingStrengthening.of henv h1 h2) h3⟩

variable! (henv : VEnv.WF env) in
/-- With `Strengthen.lean` §9(b) collapsing the two descent statements: **the hole is exactly
`PiDescend` plus the narrow residual**, two statements. -/
theorem StrengtheningTarget.iff_piDescend_narrow :
    StrengtheningTarget env U ↔ PiDescend env U ∧ TransStrengtheningNarrow env U :=
  (StrengtheningTarget.iff_typing_narrow henv).trans
    (and_congr_left' (TypingStrengthening.iff_piDescend henv))

/-! ## 4. Negative controls: the narrowing is real

The point of §1's non-lift hypothesis is that it deletes the instantiation by which
`TransStrengthening.strengthening` recovers the whole statement.  Both facts below are trivial;
they are here because the tautology in `Strengthen.lean` §8 went unnoticed for three rounds. -/

/-- **The self-instantiation is excluded.**  `TransStrengthening.strengthening` takes the middle
term to be `e2.liftN n k`; that choice fails the narrow residual's hypothesis, so the argument
does not transfer and §3's capstones are not tautologies. -/
theorem TransStrengtheningNarrow.not_hyp_of_lifted {e : VExpr} {n k : Nat} :
    ¬ ¬ (e.liftN n k).Skips n k := fun h => h .liftN

/-- Every choice of middle term that makes the residual an instance of the conclusion is
excluded, not just the one §9 happened to pick: the hypothesis is *equivalent* to the middle
term not being a lift. -/
theorem TransStrengtheningNarrow.hyp_iff {b : VExpr} {n k : Nat} :
    ¬ b.Skips n k ↔ ∀ b₀ : VExpr, b ≠ b₀.liftN n k :=
  ⟨fun h _b₀ eq => h (eq ▸ .liftN), fun h hs => have ⟨_, eq⟩ := skips_iff_exists.1 hs; h _ eq⟩

/-- **The residual is vacuous where strengthening is trivial.**  At `n = 0` nothing is
stripped, every term is its own lift, and the hypothesis is unsatisfiable — so the narrowing
has not accidentally hidden content in the degenerate case. -/
theorem TransStrengtheningNarrow.vacuous_at_zero {b : VExpr} {k : Nat} :
    ¬ ¬ b.Skips 0 k := fun h => h .zero

/-- The residual is also vacuous below the lift point, for the same reason: a term whose
free variables all sit under `k` is a lift of itself. -/
theorem TransStrengtheningNarrow.vacuous_of_closedN {b : VExpr} {n k : Nat}
    (h : b.ClosedN k) : ¬ ¬ b.Skips n k :=
  fun hn => hn (skips_iff_exists.2 ⟨b, (h.liftN_eq (Nat.le_refl _)).symm⟩)

/-! ## 5. The typing half suffices for `OnCtx.weakN_inv`

`Theory/Typing/UniqueTyping.lean:198` derives `OnCtx.weakN_inv` from `IsDefEq.weakN_iff'`, the
full *conversion* form.  It does not need it.  The induction applies strengthening only at
strictly smaller lifting witnesses and only to *typing* judgments, so `TypingStrengthening`
(equivalently, by `Strengthen.lean` §9(b), `PiDescend`) is enough — no `trans` residual.

`Strengthen.lean` §10's `Strengthening.onCtx_inv` is the same induction run off the full
`Strengthening`; this is the sharper version.  The same holds for the other eight wrappers
below, and the split it induces on the hole's 131 transitive users is measured by
`scripts/weakn-gate-split.lean`: **18 freed by the typing half, 113 still needing the narrow
`trans` residual of §1.**  `IsDefEq.skips` is deliberately *not* in the gate set — its two
endpoints differ, so it is a genuine conversion; its reflexive instance `HasType.skips` is. -/

/-- `OnCtx` of a suffix.  (`Strengthen.lean` has this too, but privately.) -/
private theorem onCtx_of_append' {P} :
    ∀ {As Γ : List VExpr}, OnCtx (As ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _::_, _, h => onCtx_of_append' h.1

variable! (henv : VEnv.WF env) in
/-- **`OnCtx.weakN_inv` from the typing half alone.** -/
theorem TypingStrengthening.onCtx_inv (HT : TypingStrengthening env U) :
    ∀ {n k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) := by
  intro n k Γ Γ' W
  induction W with
  | zero => exact onCtx_of_append'
  | @succ k Γ Γ' A W ih =>
    intro h
    have hΓ := ih h.1
    have ⟨u, hA⟩ := h.2
    exact ⟨hΓ, u, HT.typed henv W hΓ h.1 hA⟩

variable! (henv : VEnv.WF env) in
/-- `IsType.weakN_iff`'s forward direction, from the typing half alone: no `trans` residual and
no `OnCtx Γ` hypothesis. -/
theorem TypingStrengthening.isType_inv (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.IsType U Γ' (A.liftN n k)) : env.IsType U Γ A :=
  H.imp fun _ h => HT.typed henv W (HT.onCtx_inv henv W hΓ') hΓ' h

variable! (henv : VEnv.WF env) in
/-- `HasType.weakN_iff`'s forward direction, likewise. -/
theorem TypingStrengthening.hasType_inv (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) : env.HasType U Γ e A :=
  HT.typed henv W (HT.onCtx_inv henv W hΓ') hΓ' H

variable! (henv : VEnv.WF env) in
/-- `VExpr.WF.weakN_iff`'s forward direction, likewise: the well-formedness half of the hole
carries no `trans` obligation at all. -/
theorem TypingStrengthening.wf_inv (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : VExpr.WF env U Γ' (e.liftN n k)) : VExpr.WF env U Γ e :=
  have ⟨_, H⟩ := H; HT W (HT.onCtx_inv henv W hΓ') hΓ' H.hasType.1

/-- The typing half as an `iff`, in the shape `HasType.weakN_iff` is stated in. -/
theorem TypingStrengthening.hasType_weakN_iff (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) ↔ env.HasType U Γ e A :=
  ⟨HT.hasType_inv henv W hΓ', fun h => h.weakN henv W⟩

/-- `HasType.weak'_iff` from the typing half: the same induction on `Lift.depth` as
`Theory/Typing/UniqueTyping.lean:257`, with the conversion-form appeal replaced by the typing
one.  This is what makes the `weak'` family part of the *typing* gate set for §6's split. -/
theorem TypingStrengthening.hasType_weak'_iff (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ') :
    env.HasType U Γ' (e.lift' l) (A.lift' l) ↔ env.HasType U Γ e A := by
  generalize eq : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero eq, W.depth_zero eq]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ eq
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      HT.hasType_weakN_iff henv hΓ' W2, ih (HT.onCtx_inv henv W2 hΓ') W1 Lift.depth_consN]

/-- `IsType.weak'_iff` from the typing half. -/
theorem TypingStrengthening.isType_weak'_iff (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e :=
  exists_congr fun _ => HT.hasType_weak'_iff henv hΓ' W (A := .sort _)

/-- `OnCtx.weak'_inv` from the typing half. -/
theorem TypingStrengthening.onCtx_weak'_inv (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) :
    ∀ {ρ : Lift} {Γ Γ' : List VExpr}, Ctx.Lift' ρ Γ Γ' →
      OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) := by
  intro ρ Γ Γ' W H
  generalize eq : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simp [W.depth_zero eq, H]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ eq
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    exact ih W1 (HT.onCtx_inv henv W2 H) (by simp)

/-- `VExpr.WF.weak'_iff`'s forward direction from the typing half: `TypingStrengthening` is
already stated with an existential type, so it iterates along `Lift.depth` directly. -/
theorem TypingStrengthening.wf_weak'_inv (henv : VEnv.WF env) (HT : TypingStrengthening env U) :
    ∀ {n : Nat} {l : Lift} {Γ Γ' : List VExpr} {e : VExpr}, l.depth = n → Ctx.Lift' l Γ Γ' →
      OnCtx Γ' (env.IsType U) → VExpr.WF env U Γ' (e.lift' l) → VExpr.WF env U Γ e := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e eq W hΓ' H
    rw [VExpr.lift'_depth_zero eq] at H
    cases W.depth_zero eq; exact H
  | succ n ih =>
    intro l Γ Γ' e eq W hΓ' H
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ eq
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have ⟨_, H⟩ := H
    have hΓ₁ := HT.onCtx_inv henv W2 hΓ'
    exact ih Lift.depth_consN W1 hΓ₁ (HT W2 hΓ₁ hΓ' H.hasType.1)

/-- `HasType.skips` from the typing half.  (`IsDefEq.skips`, its two-endpoint parent, is *not*
in the typing gate set: there the two endpoints differ, so it is a genuine conversion.) -/
theorem TypingStrengthening.hasType_skips (henv : VEnv.WF env) (HT : TypingStrengthening env U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) :
    ∃ B, env.HasType U Γ' e B ∧ B.Skips n k := by
  obtain ⟨e₀, rfl⟩ := skips_iff_exists.1 h2
  have ⟨B₀, hB₀⟩ := HT.wf_inv henv W hΓ' ⟨_, h1⟩
  exact ⟨_, hB₀.weakN henv W, .liftN⟩
