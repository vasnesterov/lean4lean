import Lean4Lean.Theory.Typing.KRule
import Lean4Lean.Theory.Typing.DescendRefute

/-!
# Wiring `KStep` in: the descent, restated so that the K-rule can fire

`Theory/Typing/DescendRefute.lean` refutes `NormalEq.descend` three times, and
`docs/handoff-krule.md` §3.2 adds a fourth defect that survives every repair proposed so far:
`descend`'s conclusion asks the left term to reduce to something that *syntactically matches*
the pattern, and a K-step never produces a match -- it produces the rule's right-hand side.

This file carries out the restatement `docs/handoff-krule.md` §3.3 identifies, and makes it
machine-checked.  The move is smaller than that section predicted, and the reason is a
structural fact about the rule table that was already in `Params`:

> **`Params.pat_simple` forces every registered pattern to be
> `.app ((.const rec).varN m) ((.const ctor).varN n)` or `.const c`.  So an `.app` node occurs
> only at the very top of a pattern, and both of its children are `.var`-chains.**
> (`Params.pat_app_noApp` below.)

`descend`'s three refuted E5 branches are all in its `.app`-node case.  At a registered
pattern that case arises **once**, at the top -- and at the top there is a rule to fire.  So
the descent proper never needs it: `NormalEq.descendV` below is `descend` restricted to
`.app`-free patterns, and it carries no `sorry` of its own.

**Do not read that as "hole-free".**  `#print axioms NormalEq.descendV` gives
`[propext, sorryAx, Classical.choice, Quot.sound]`: the `sorryAx` arrives through
`Params.sortUniq` and `IsDefEq.uniq` in the E3 branch, i.e. through
`IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`, the tree's two ambient holes
(measured cone 3839, exactly the two -- `descend` itself is *not* in it).  What `descendV`
*is*, precisely: a genuine restatement, whose one added hypothesis is free at every registered
pattern (`Params.pat_app_noApp`, which is itself `sorryAx`-free), and which is not refuted at
the instance that refutes `descend` (`DescendRestate.lean`'s `descendV_dodges_witnessA`).  It
is not a discharge of `descend`'s obligation, and the earlier wording here said otherwise.

The top node is then handled by descending the whole node at the pattern `.var q₁` -- the
function side's pattern with the argument position left **free** -- and firing the rule there
with the K-step, whose canonical major premise is the one the `NormalEq` hypothesis itself
supplies.  That is `NormalEq.appDF_extra_of_descendV`.  All three E5 cases collapse into this
one move, exactly as predicted, and the collapse is now checked rather than argued.

## What is hypothesised, and why

**Exactly one** hypothesis is carried: `hK`, saying `KStep Γ e e' → ParRed Γ e e'` -- *the
K-rule is in the reduction relation*.  Nothing else.  In particular the universe-uniqueness
side condition that `DescendRefute.lean`'s `NormalEq.appDF_proof_escape_of_sortUniq` takes
(`hsu`) is **discharged**, not propagated: `ChurchRosser.lean`'s `VEnv.Params.sortUniq`
derives it from `Params.henv` via `Injectivity.lean`'s `VEnv.WF.sortUniq'`, which is relative to
`IsDefEqU.forallE_inv_stratified` alone -- a hole the confluence development already has in
its cone through `IsDefEq.uniq`.  So E3 costs nothing at all any more, and E5 costs `hK`.

`hK` is deliberately a hypothesis.  Discharging it means adding a constructor to `ParRed`,
which forces `ParRed.triangle` to be re-proved with the new step, and *that* is where the
canonicity of the major premise comes back: `KDiamond` at the end of this file is the exact
residual, and `KStep.uniq_defeq` shows how much of it is free (the `IsDefEqU` half) and how
much is not (the `≡ₚ` half, which is what confluence itself exists to deliver).
`docs/handoff-krule.md` §3.3 claimed lemma M3 / `pat_major_canonical` is not needed for
confluence.  **That claim is right about `descend` -- this file proves it -- and wrong about
the triangle.**  See `docs/handoff-krule.md` §§3.4-3.5 for the measurement.
-/

namespace Lean4Lean

open VExpr

/-- A pattern with no `.app` node: a `.var`-chain over a single `.const` leaf.  Every
registered pattern is either such a chain (`.defn`) or an `.app` of two of them (`.iota`),
so this is the shape the descent proper ever sees. -/
def Pattern.NoApp : Pattern → Prop
  | .const _ => True
  | .app _ _ => False
  | .var f => f.NoApp

theorem Pattern.NoApp.varN {p : Pattern} (h : p.NoApp) : ∀ n, (p.varN n).NoApp
  | 0 => h
  | n+1 => h.varN n

namespace VEnv

variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
set_option hygiene false in
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-- **An `.app` node occurs only at the top of a registered pattern.**  `Params.pat_simple`
says every registered pattern is a `SimplePattern`, and `SimplePattern.toPattern` builds at
most one `.app`, whose two children are `Pattern.varN` chains over a `.const`.

This is what makes `NormalEq.descendV` below possible: the descent recurses into `q₁` and into
`q₂`, and neither contains an `.app`, so the three refuted E5 branches are *unreachable* from a
registered pattern rather than merely unproved. -/
theorem Params.pat_app_noApp {p₁ p₂ : Pattern} {r} (h : Pat (.app p₁ p₂) r) :
    p₁.NoApp ∧ p₂.NoApp := by
  obtain ⟨sp, hsp⟩ := pat_simple h
  cases sp with
  | defn c => simp [SimplePattern.toPattern] at hsp
  | iota rc m c n =>
    simp [SimplePattern.toPattern] at hsp
    obtain ⟨rfl, rfl⟩ := hsp
    exact ⟨Pattern.NoApp.varN (p := .const rc) trivial m,
      Pattern.NoApp.varN (p := .const c) trivial n⟩

/-! ### Universe uniqueness: discharged upstream

The `hsu` hypothesis that `NormalEq.appDF_proof_escape` used to take is gone.  It is
`VEnv.Params.sortUniq` (`ChurchRosser.lean`), derived from `Params.henv` via
`Injectivity.lean`'s `VEnv.WF.sortUniq'` -- relative to `IsDefEqU.forallE_inv_stratified`
alone, which is *already* in the confluence development's cone through `IsDefEq.uniq`.  So
E3 costs this development nothing.  (This file previously carried its own copy of that
derivation; it now lives in `ChurchRosser.lean`, above `descend`'s own E3 branches, which are
closed there by the same lemma.) -/

/-! ## The descent proper, at an `.app`-free pattern

`NormalEq.descendV` is `ChurchRosser.lean`'s `NormalEq.descend` with one hypothesis added --
the pattern has no `.app` node -- and it carries no `sorry` of its own (but see the header: its
axiom set is `[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming from the
E3 branch's `Params.sortUniq` / `IsDefEq.uniq`, not from `descend`).  Adding that hypothesis deletes the
whole `.app`-node case, which is where all three of `DescendRefute.lean`'s counterexamples
live; the remaining escape (`E3`, the function child is a proof) is closed by
`NormalEq.appDF_proof_escape`, which needs only universe uniqueness.

`Params.pat_app_noApp` says this hypothesis costs nothing at a registered pattern: the
descent is entered at `q₁` and at `q₂`, and both are `.app`-free.  The single `.app` node --
the top one -- is handled by `NormalEq.appDF_extra_of_descendV` below, where a rule is
available to fire. -/
theorem NormalEq.descendV :
    ∀ (N : Nat) {g : VExpr}, sizeOf g ≤ N →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      q.NoApp → OnCtx Γ (IsType env univs) → Γ ⊢ g ≡ₚ g' → q.Matches g' n1 n2 →
      DescentOut Γ q g g' n1 n2 := by
  intro N
  induction N using Nat.strongRecOn with | _ N IH => ?_
  intro g hsz Γ q g' n1 n2 hq hΓ hne hm
  cases hne with
  | refl h =>
    obtain ⟨u1, u2, hmt, hlv, hwa, hwb, hn⟩ := NormalEq.descent_refl hΓ hm h
    exact .inl ⟨0, _, u1, u2, .rfl, hmt, hlv, hwa, hwb, hn⟩
  | sortDF _ _ _ => cases hm
  | lamDF _ _ _ => cases hm
  | forallEDF _ _ _ _ => cases hm
  | etaR _ _ => cases hm
  | proofIrrel h1 h2 h3 => exact .inr ⟨_, h1, h2, h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    cases hm
    exact .inl ⟨0, _, _, _, .rfl, .const, fun _ => h5, fun _ => h2, fun _ => h3, nofun⟩
  | etaL h1 h2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := h1.isType henv hΓ; h.forallE_inv henv
    have hΓA : OnCtx (_::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have hmlift : q.Matches g'.lift n1 (fun x => (n2 x).lift) :=
      Pattern.matches_liftN.2 ⟨n2, hm, fun _ => rfl⟩
    match IH _ (by simp at hsz; omega) (Nat.le_refl _) (show (Pattern.var q).NoApp from hq) hΓA h2 (.var hmlift) with
    | .inl ⟨k, D⟩ => exact .inl ⟨k+1, _, _, _, .rfl, h1, D⟩
    | .inr ⟨P, hP, hp1, hp2⟩ =>
      have hwf := have ⟨_, h⟩ := hA.isType henv hΓ; h.sort_inv henv
      have hb0 := HasType.app (h1.weak henv) (.bvar .zero)
      simp [instN_bvar0] at hb0
      have hBP := hb0.uniqU henv hΓA hp2
      exact .inr ⟨_,
        IsDefEq.defeq (.sortDF (by exact ⟨hwf, ⟨⟩⟩) (by trivial) VLevel.imax_zero)
          (hA.forallE hP),
        hA.lam hp1,
        HasType.defeqU_r henv hΓ ⟨_, .forallEDF hA (hBP.of_l henv hΓA hB)⟩ h1⟩
  | @appDF _ f₁ A₀ B₀ f₂ a₁ a₂ l1 l2 l3 l4 l5 l6 =>
    have hszf : sizeOf f₁ < N := by simp at hsz; omega
    cases hm with
    | @var q₁ _ m1 g1 hf =>
      rename_i hf
      match IH _ hszf (Nat.le_refl _) (show q₁.NoApp from hq) hΓ l5 hf with
      | .inl ⟨0, t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩ =>
        refine .inl ⟨0, .app t a₁, u1, (·.elim a₁ u2), ParRedS.app hred .rfl, .var hmt,
          hlv, hwa, hwb, ?_⟩
        rintro (_|x)
        · exact l6
        · exact hn x
      | .inl ⟨k+1, A, e, B, hred, hty, D⟩ =>
        have ⟨⟨_, u1⟩, _, _⟩ := (hty.uniqU henv hΓ l2).forallE_inv henv hΓ
        exact .inl ⟨k, DescentLam.head
          (.trans (ParRedS.app hred .rfl) (.tail .rfl (.beta .rfl .rfl)))
          (DescentLam.beta hΓ (u1.symm.defeq l3) (fun x => hf.hasType hΓ l2 x) l6 D)⟩
      | .inr ⟨P, hP, hp1, hp2⟩ =>
        -- **E3**, closed: the function child is a proof, so the node is one.
        exact .inr (NormalEq.appDF_proof_escape_of_sortUniq Params.sortUniq hΓ l1 l2 l3 l4 l6 hP hp1)
    | @app q₁ _ m1 g1 q₂ _ m2 g2 hf ha =>
      -- **E5** is unreachable: `q` has no `.app` node.
      exact (hq : False).elim

/-! ## The top node: descend the function side, and let the K-rule supply the argument

This is `docs/handoff-krule.md` §3.3's "one uniform move", machine-checked.

`ChurchRosser.lean`'s `NormalEq.appDF_extra_of_descend` descends the **whole node** against
the whole pattern `q₁.app q₂`, which forces the argument side to reduce to something matching
`q₂` -- and `DescendRefute.lean` exhibits three terms for which it does not.  Here the node is
descended against `.var q₁` instead: the function side's pattern with the argument position
left **free**, which `Pattern.Matches.var` accepts unconditionally.  Nothing about the
argument is asked, so none of the three counterexamples applies.

The rule is then fired by `KStep`, whose canonical major premise is `b'` -- handed over by the
`NormalEq` hypothesis of the node itself, not computed by any `pat_major_canonical`.  That is
the saving §3.3 predicted, and it is real: this proof mentions no canonicity lemma. -/
theorem NormalEq.appDF_extra_of_descendV
    (hK : ∀ {Δ : List VExpr} {e e' : VExpr}, KStep Δ e e' → Δ ⊢ e ≫ e')
    {Γ : List VExpr} {f A B a b f₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, Γ ⊢ f₂ ≫ e₂' → ∃ e₁', Γ ⊢ f ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, Γ ⊢ b ≫ e₂' → ∃ e₁', Γ ⊢ a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'}
    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
    (r3 : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd)
    (r4 : ∀ x, Γ ⊢ m2 x ≫ m2' x) :
    ∃ e₁', Γ ⊢ f.app a ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst := by
  cases r2 with
  | var h => exact absurd r1 Params.pat_not_var
  | @app q₁ _ f1 g1 q₂ _ f2 g2 h1 h2 =>
    obtain ⟨hq1, hq2⟩ := Params.pat_app_noApp r1
    obtain ⟨f₂', hpf, hmf⟩ :=
      parRed_of_matches h1 (m2' := fun x => m2' (.inl x)) (fun x => r4 (.inl x))
    obtain ⟨b', hpb, hmb⟩ :=
      parRed_of_matches h2 (m2' := fun x => m2' (.inr x)) (fun x => r4 (.inr x))
    obtain ⟨tf, hf1, hf2⟩ := ih1 hpf
    obtain ⟨ta, ha1, ha2⟩ := ih2 hpb
    have heq : Sum.elim (fun x => m2' (Sum.inl x)) (fun x => m2' (Sum.inr x)) = m2' :=
      funext fun x => by cases x <;> rfl
    have hmnode : (q₁.app q₂).Matches (f₂'.app b') (Sum.elim f1 f2) m2' := heq ▸ .app hmf hmb
    have hb'ty : Γ ⊢ b' : A := hpb.hasType hΓ l4
    have hf₂'ty : Γ ⊢ f₂' : .forallE A B := hpf.hasType hΓ l2
    have htf : Γ ⊢ tf : .forallE A B := hf1.hasType hΓ l1
    have hta : Γ ⊢ ta : A := ha1.hasType hΓ l3
    have hnode : Γ ⊢ tf.app ta ≡ₚ f₂'.app b' := .appDF htf hf₂'ty hta hb'ty hf2 ha2
    have hck' : Pattern.Check.OK (IsDefEqU env univs Γ) (p := q₁.app q₂)
        (Sum.elim f1 f2) m2' r.snd :=
      r3.congr_defeq hΓ _ fun x _ hty => ⟨_, (r4 x).defeq hΓ hty⟩
    have hwB : ∀ lp, ∀ l ∈ Sum.elim f1 f2 lp, VLevel.WF univs l :=
      hmnode.levelWF hΓ (hf₂'ty.app hb'ty)
    -- The node, matched at `.var q₁`: the function side's pattern, argument position free.
    have hmvar : (Pattern.var q₁).Matches (f₂'.app b') f1
        (fun x => x.elim b' (fun y => m2' (.inl y))) := .var hmf
    -- **The firing step**, quantified over context extensions because `DescentLam.fire`
    -- descends under one binder per pending eta layer.  The rule fires by `KStep`: the term
    -- reached is `tf'.app ta'` where only `tf'` matches, and `ta'` is merely `≡ₚ` -- hence
    -- definitionally equal to -- the canonical major premise `b'`.
    have hbot : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
        {u1 : (Pattern.var q₁).LPath → List VLevel} {u2 : (Pattern.var q₁).Path → VExpr},
        Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
        (Pattern.var q₁).Matches t u1 u2 →
        (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (f1 lp)) →
        (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
        (∀ x, Γ' ⊢ u2 x ≡ₚ ((x.elim b' (fun y => m2' (.inl y)) : VExpr)).liftN n) →
        ∃ s, Γ' ⊢ t ≫* s ∧
          Γ' ⊢ s ≡ₚ (Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2) m2' r.fst).liftN n := by
      intro Γ' n t u1 u2 W hΓ' ht' hmt hlv hwA hne
      cases hmt with
      | @var _ tf' _ g1' ta' hmtf =>
        rename_i hmtf
        have ⟨_, htT⟩ := ht'
        have ⟨A₀, B₀, htf', hta'⟩ := htT.app_inv henv hΓ'
        -- the canonical major premise, weakened into `Γ'`
        have hmb' : q₂.Matches (b'.liftN n) f2 (fun x => (m2' (.inr x)).liftN n) :=
          Pattern.matches_liftN.2 ⟨_, hmb, fun _ => rfl⟩
        have hb'W : Γ' ⊢ b'.liftN n : A.liftN n := hb'ty.weakN henv W
        have hbv : Γ' ⊢ ta' ≡ₚ b'.liftN n := by simpa using hne none
        have hleaf : ∀ x, Γ' ⊢ g1' x ≡ₚ (m2' (.inl x)).liftN n := fun x => by
          simpa using hne (some x)
        -- the K-redex's data, assembled
        have hmK : (q₁.app q₂).Matches (.app tf' (b'.liftN n)) (Sum.elim u1 f2)
            (Sum.elim g1' (fun x => (m2' (.inr x)).liftN n)) := .app hmtf hmb'
        have hlvS : ∀ lp, List.Forall₂ (· ≈ ·)
            (Sum.elim u1 f2 lp) (Sum.elim f1 f2 lp) := by
          rintro (lp|lp)
          · exact hlv lp
          · exact VLevel.forall₂_equiv_refl _
        have flipeq : ∀ {l1 l2 : List VLevel},
            List.Forall₂ (· ≈ ·) l1 l2 → List.Forall₂ (· ≈ ·) l2 l1 := by
          intro l1 l2 h
          induction h with
          | nil => exact .nil
          | cons h _ ih => exact .cons h.symm ih
        have hlvS' : ∀ lp, List.Forall₂ (· ≈ ·)
            (Sum.elim f1 f2 lp) (Sum.elim u1 f2 lp) := fun lp => flipeq (hlvS lp)
        have hwAS : ∀ lp, ∀ l ∈ Sum.elim u1 f2 lp, VLevel.WF univs l := by
          rintro (lp|lp)
          · exact hwA lp
          · exact hwB (.inr lp)
        have hneS : ∀ x : (q₁.app q₂).Path,
            Γ' ⊢ (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n) : _ → VExpr) x
              ≡ₚ (m2' x).liftN n := by
          rintro (x|x)
          · exact hleaf x
          · exact have ⟨_, ht⟩ := hmb'.hasType hΓ' hb'W x; .refl ht
        have hckW := hck'.weakN W r.snd
        have hckK : Pattern.Check.OK (IsDefEqU env univs Γ') (p := q₁.app q₂)
            (Sum.elim u1 f2) (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) r.snd := by
          refine hckW.map_levels (fun x i y j hl => ?_) (fun u v h => ?_)
          · exact ((VLevel.forall₂_getD (hlvS x) i).trans hl).trans
              (VLevel.forall₂_getD (hlvS y) j).symm
          · obtain ⟨T, hT⟩ := h
            have step : ∀ (w : (q₁.app q₂).RHS) {C},
                Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                      (fun x => (m2' x).liftN n) w : C →
                Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                      (fun x => (m2' x).liftN n) w ≡
                    Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim u1 f2)
                      (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) w := by
              intro w C hw
              have hins := NormalEq.apply_instL (p := q₁.app q₂) (r := w) hΓ' hwB hwAS hlvS' hw
              have ⟨_, hh⟩ := hins.defeq hΓ'
              refine (hins.defeq hΓ').trans henv hΓ'
                (IsDefEqU.apply_pat hΓ'
                  (fun x _ _ => ((hneS x).defeq hΓ').symm) hh.hasType.2)
            exact ((step u hT.hasType.1).symm.trans henv hΓ' ⟨_, hT⟩).trans henv hΓ'
              (step v hT.hasType.2)
        -- **`KStep` fires.**  Only the function side matches; the argument `ta'` is bridged
        -- to `b'` by the node's own `NormalEq`.
        have hdq : Γ' ⊢ ta' ≡ b'.liftN n : A₀ :=
          ((hbv.defeq hΓ').of_l henv hΓ' hta')
        have hfire : Γ' ⊢ .app tf' ta' ≫
            Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim u1 f2)
              (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) r.fst :=
          hK (.mk r1 hmK hckK htf' hdq)
        refine ⟨_, .tail .rfl hfire, ?_⟩
        rw [Pattern.RHS.liftN_apply (p := q₁.app q₂) (m1 := Sum.elim f1 f2) (m2 := m2') r.fst]
        exact NormalEq.apply_congr (p := q₁.app q₂) (r := r.fst) hΓ' hwAS hwB hlvS
          (fun x _ _ => hneS x) (hfire.hasType hΓ' htT)
    match NormalEq.descendV _ (Nat.le_refl _)
        (show (Pattern.var q₁).NoApp from hq1) hΓ hnode hmvar with
    | .inl ⟨k, D⟩ =>
      have ⟨t, ht1, ht2⟩ := DescentLam.fire hΓ ⟨_, htf.app hta⟩
        (Params.pat_wf r1 hmnode hΓ (hf₂'ty.app hb'ty) hck').symm hbot D
      exact ⟨t, (ParRedS.app hf1 ha1).trans ht1, ht2⟩
    | .inr ⟨P, hP, hp1, hp2⟩ =>
      exact ⟨_, ParRedS.app hf1 ha1,
        .proofIrrel hP hp1
          ((Params.pat_wf r1 hmnode hΓ hp2 hck').of_l henv hΓ hp2).hasType.2⟩

/-! ## What is left over: the triangle, and the canonical major premise

`NormalEq.appDF_extra_of_descendV`'s single hypothesis `hK` says the K-rule is a `ParRed`
step.  Landing it means adding a constructor to `ParRed`, and the six proofs that then gain a
case are listed in `docs/handoff-krule.md` §3.4.  Five are routine.  The sixth,
`ParRed.triangle`, is not, and this section says exactly why in the tree's own language. -/

/-- **The residual `ParRed.triangle` would need from a K-step**: two K-steps at the *same*
redex land `NormalEq`-close.

This is forced by the triangle's shape.  `CParRed` must fire K whenever `ParRed` can, so the
complete development picks *some* canonical major premise `c₀` while the arbitrary step picks
`c₁`; the two contracta then differ at exactly the pattern positions that read off `c`'s
sub-arguments, and `triangle`'s conclusion is `≡ₚ`, not `≡`.

Nothing in `Params` supplies this.  Note it is **not** implied by uniqueness of the rule:
`Params.pat_uniq` cannot even be applied, because two K-steps at the same `f`-spine may use
patterns whose *argument* sides do not intersect -- two different constructors of the same
`Prop`-valued inductive, both definitionally equal to the major premise by proof irrelevance.
That is precisely the configuration Carneiro's `K⁺` excludes by restricting to
subsingleton-eliminating inductives (`~/lean-type-theory/unique.tex:103`), and it is what
`docs/design-inductive.md` §7.6's `pat_major_canonical` (lemma M3) would supply. -/
def KDiamond : Prop :=
  ∀ {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
    KStep Γ e e₁ → KStep Γ e e₂ → Γ ⊢ e₁ ≡ₚ e₂

/-- **The free half of `KDiamond`.**  Two K-steps at the same redex are definitionally equal
outright -- that is `KStep.defeq` composed with itself, and it needs nothing new.

So the whole content of `KDiamond` is the upgrade from `≡` to `≡ₚ`, which is exactly what
confluence is being built to deliver.  Assuming it inside the confluence proof is therefore
circular unless it is supplied from outside, i.e. by a canonicity fact about the rule table.
This is the precise sense in which lemma M3 is *not* eliminated by the K-rule, only moved:
`NormalEq.appDF_extra_of_descendV` above does not use it, and `ParRed.triangle` will. -/
theorem KStep.uniq_defeq {Γ : List VExpr} {e e₁ e₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H1 : KStep Γ e e₁) (H2 : KStep Γ e e₂) :
    Γ ⊢ e₁ ≡ e₂ :=
  (H1.defeq hΓ).symm.trans henv hΓ (H2.defeq hΓ)

/-! ## The boundary: why `DescendRefute.lean`'s three witnesses do not reach this file

They are not repaired, and they are not contradicted -- they are *excluded*, twice over, and
both exclusions are checkable in one line each. -/

omit [Params] in
/-- The pattern of witnesses A and C (`not_descendStatement`, `not_descendStatement_etaFun`)
has an `.app` node, so `NormalEq.descendV` never sees it. -/
theorem refQ_not_noApp : ¬ refQ.NoApp := id

omit [Params] in
/-- The pattern of witness B (`not_descendStatement_etaArg`), likewise. -/
theorem refQ2_not_noApp : ¬ refQ2.NoApp := id

omit [Params] in
/-- And the top-node lemma is out of their reach for the *other* reason the refutations
exploit: it carries `Pat p r`, and `refParams` registers nothing.  So neither of the two new
statements is refutable by the three witnesses, and neither weakens what they refute. -/
theorem refParams_no_kstep {Γ e e'} : ¬ @KStep refParams Γ e e' := by
  rintro ⟨hpat, _, _, _, _⟩; exact refNoPat hpat

omit [Params] in
/-- `hK` is a *consistent* hypothesis, which a vacuously-false one would not be: at the
witness instance it holds, because `KStep` there is empty.  This is not evidence that it is
*useful* at that instance -- `KRule.lean`'s `KStep.stuck_fires` is what shows the rule fires
on a term the tree can otherwise not reduce, and that needs a registered rule. -/
theorem refParams_hK {Γ e e'} : @KStep refParams Γ e e' → @ParRed refParams Γ e e' :=
  fun h => absurd h refParams_no_kstep

end VEnv

end Lean4Lean
