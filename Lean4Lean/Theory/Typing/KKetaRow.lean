import Lean4Lean.Theory.Typing.KSite7Rows

/-!
# `AppKetaRow` refactored: the residual is an `EtaK` transport, and its `here` half is free

`KSite7Rows.lean` leaves site 7 for `ParRedK` resting on two hypotheses, `WeakNInvDS` and
`AppKetaRow`, and records the reason `AppKetaRow` cannot be discharged as a *design* question
rather than a missing lemma:

> Site 7 is proved by induction on `H1 : NormalEq`, and `ParRedK.keta`'s second premise
> `htail : ParRedK Γ w e₂'` has to be pushed across a `NormalEq` which is **not** a
> sub-derivation of `H1`.  Reorganising the induction onto `H2 : ParRedK` closes `keta` and
> breaks the two eta rows, which consume `H2` *weakened and applied*.  Neither lexicographic
> order works and `|H1| + |H2|` is constant across `etaL`.

This file does five things.

1. **Names the right residual.**  `EtaKNormalEqInv` -- *an `EtaK` step transports backwards
   across a `NormalEq`* -- replaces `AppKetaRow`.  It mentions no `ParRedK` development at
   all, so it is not a fragment of site 7 in disguise; it is `EtaK.domEq_inv`
   (`KSite7.lean`, proved) with `DomEq` widened to `NormalEq`.

2. **Proves its `here` half outright** (`NormalEq.ketaHere_inv`), with no hypothesis.  The
   proof is `KSite7App.NormalEq.appDF_extra_of_descendVK`'s move -- descend the node at
   `.var p₁`, the pattern's function side with the argument slot left free, then fire the rule
   by `KStep`, whose `hdq` premise accepts a merely *definitionally equal* major premise.  Two
   things get *simpler* than in the `extra` row: nothing develops the pattern's holes (so
   `parRedK_of_matches` and `Check.OK.congr_defeq` are not needed), and the `NormalEq` fed to
   the descent is the caller's own, not one reassembled from two induction hypotheses -- so
   `NormalEq.appDF`'s six premises are not needed either.  In particular this covers the
   `etaL` configuration on the function side, which is what `appKetaRow_here_of_same_fun`
   (`KSite7Rows.lean`) explicitly did *not*: that lemma assumes the two function sides are
   syntactically equal.

3. **Builds the grading that breaks the circle.**  `AppKetaRow`'s `keta` premise has to be
   pushed across a `NormalEq` that is not a sub-derivation of `H1`; reorganising onto `H2`
   closes `keta` and breaks the eta rows, which consume `H2` *weakened and applied*.
   `ParRedKn` grades `ParRedK` by the **height of redex nesting** -- congruences graded
   *uniformly* rather than additively -- so that `keta` strictly decreases the grade
   (`ParRedKn` constructor) while `ParRedKn.weakN` and `ParRedKn.app_bvar` leave it alone.
   That is exactly the pair of properties `KSite7Rows.lean`'s table shows derivation size and
   `|H1| + |H2|` failing to have.

4. **Proves the `under` half from `WeakNInvDS`**, by reusing `KSite7.etaR_inner` verbatim at
   `e₁` instead of at `etaR`'s subject -- so `EtaKNormalEqInv` is *not* a second hypothesis
   (`etaKNormalEqInv_of_weakNInvDS`).  Put together: `ketaRow_of_weakNInvDS` proves the
   `appDF` x `keta` row from `WeakNInvDS` plus site 7 **at grade `N`**, applied only to
   `htail`, whose grade is `N` while the row's own derivation has grade `N+1`.  That is an
   induction step, not a hypothesis, and `parRedKStatementN_zero` supplies its base, so
   `ketaRow_of_weakNInvDS_at_one` holds from `WeakNInvDS` alone.

5. **Removes one of site 7's two `IsDefEqU.weakN_iff` entries.**  Both compositions the
   `under` half performs have a `DomEq` on one side, and `NormalEq.trans`'s single appeal to
   strengthening is its `etaR`-after-`etaL` case -- unreachable when either side is `DomEq`.
   `DomEq.trans_normalEq` and `NormalEq.trans_domEq` are those two narrow compositions, proved
   here and clean of `weakN_iff` (indeed clean of `WF.rigidShapeUniqNS` too).
   `etaR_case_clean` is `KSite7.etaR_case` rebuilt on them: same statement, and clean, which
   leaves `appDF` x `beta` (through `ChurchRosser.ParRedExt.parRed_beta`) as the **only**
   remaining entry of `weakN_iff` into site 7.

## What is *not* claimed

The reorganised site 7 is **not** assembled.  Doing so means restating the eight non-`keta`
rows of `KSite7`/`KSite7App`/`KSite7Rows` over `ParRedKn`.  That is expected to be mechanical --
inspection says each of those proofs uses its induction hypotheses only at derivations built
from the case's own premises by congruences and `ParRedKn.rfl`, so of grade `≤ N` -- but the
expectation is **not machine-checked here**, and it is large, because the row lemmas' signatures
quantify over ungraded `ParRedK` and so cannot be reused as they stand.  So `AppKetaRow` is **not discharged
here**; what is established is that every ingredient the discharge needs exists and is measured,
and that nothing in it costs a hypothesis beyond `WeakNInvDS`.

`etaR_case_clean` is a drop-in for `KSite7.etaR_case` and the substitution is **not** performed
in `KSite7.lean`.

Lower bounds are stated with `KSite7Rows.appKetaRow_of_no_etaK`'s honesty:
`etaKNormalEqInv_of_no_etaK` holds because its `EtaK` premise has no witness, which rules out
refutation and is no evidence of truth.
-/

namespace Lean4Lean

open VExpr

/-- A uniform bound over a pattern's argument paths.  `Pattern.Path` is built from `Empty`,
`Sum` and `Option`, so a pointwise bound can be maximised -- which is what `ParRedK.toN`'s
`extra` case needs, since that constructor's premise is a *family* of developments. -/
theorem Pattern.exists_bound : ∀ {p : Pattern} {P : Nat → p.Path → Prop},
    (∀ {n m : Nat} {a : p.Path}, n ≤ m → P n a → P m a) →
    (∀ a, ∃ n, P n a) → ∃ n, ∀ a, P n a
  | .const _, _, _, _ => ⟨0, nofun⟩
  | .var f, P, hmono, h => by
    obtain ⟨n₀, h₀⟩ := h none
    obtain ⟨n₁, h₁⟩ := Pattern.exists_bound (p := f) (P := fun n x => P n (some x))
      (fun hle hp => hmono hle hp) (fun x => h (some x))
    refine ⟨max n₀ n₁, ?_⟩
    rintro (_|x)
    · exact hmono (Nat.le_max_left _ _) h₀
    · exact hmono (Nat.le_max_right _ _) (h₁ x)
  | .app f a, P, hmono, h => by
    obtain ⟨n₀, h₀⟩ := Pattern.exists_bound (p := f) (P := fun n x => P n (.inl x))
      (fun hle hp => hmono hle hp) (fun x => h (.inl x))
    obtain ⟨n₁, h₁⟩ := Pattern.exists_bound (p := a) (P := fun n x => P n (.inr x))
      (fun hle hp => hmono hle hp) (fun x => h (.inr x))
    refine ⟨max n₀ n₁, ?_⟩
    rintro (x|x)
    · exact hmono (Nat.le_max_left _ _) (h₀ x)
    · exact hmono (Nat.le_max_right _ _) (h₁ x)

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## The residual, restated -/

/-- **An `EtaK` step transports backwards across a `NormalEq`.**

Compare `KSite7.EtaK.domEq_inv`, which is the same statement for `DomEq` and is *proved*
there (it is the three-line `keta` case of `DomEq.parRedK`).  The only difference is the
relation on the left, and that difference is exactly `NormalEq`'s two eta constructors.

Read as a residual this is strictly better shaped than `AppKetaRow`: `AppKetaRow` quantifies
over a `ParRedK Γ w e₂'` and so cannot be separated from site 7 itself, while this statement
never mentions a development of the contractum.  `appKetaRow_of_etaKNormalEqInv` below is the
bridge, and it makes the residual site 7 leaves behind a *sub-derivation* call. -/
def EtaKNormalEqInv : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ w : VExpr}, OnCtx Γ (IsType env univs) →
    NormalEq Γ e₁ e₂ → EtaK Γ e₂ w → ∃ t, ParRedKS Γ e₁ t ∧ Γ ⊢ t ≡ₚ w

/-- Lower bound, stated with the same honesty as `KSite7Rows.appKetaRow_of_no_etaK`: where
`EtaK` is empty the statement holds because its `EtaK` premise has no witness.  That rules out
an outright refutation and is **no evidence of truth**; it is vacuous at `refParams` and at
every other `Params` instance in this tree, none of which registers an `.app` pattern. -/
theorem etaKNormalEqInv_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : EtaKNormalEqInv :=
  fun _ _ hek => absurd hek hno

theorem refParams_etaKNormalEqInv : @EtaKNormalEqInv refParams :=
  @etaKNormalEqInv_of_no_etaK refParams (fun h => refParams_no_etaK h)

/-- **Upper bound: the collapse test.**  `EtaKNormalEqInv` is a substitution instance of
site 7 (`H2 := .keta hek .rfl`, i.e. `ParRedK.keta_step`), so it is no stronger than what it
would be used to prove.  Together with `appKetaRow_of_etaKNormalEqInv` this places it
*between* `AppKetaRow` and site 7. -/
theorem etaKNormalEqInv_of_parRedKStatement (S : ParRedKStatement) : EtaKNormalEqInv :=
  fun hΓ H1 hek => S hΓ H1 (.keta_step hek)

/-! ## The `here` half, unconditionally

`EtaK.here` is a bare `KStep` at the node.  The whole of it is: transport the *function
side's* match backwards across the `NormalEq`, and fire the rule again with the argument the
`NormalEq` supplies.  The transport is `NormalEq.descendV` at the pattern `.var p₁` -- the
function side with the argument position free -- and the firing is `KStep.mk`, whose `hdq`
premise asks only for definitional equality of the major premise.

Nothing in the argument position is inspected, which is why none of
`DescendRefute.lean`'s three counterexamples applies (they are all in `descend`'s `.app`-node
case, and `Params.pat_app_noApp` puts `.var p₁` out of its reach).  -/
theorem NormalEq.ketaHere_inv {Γ : List VExpr} {e₁ e₂ w : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H1 : Γ ⊢ e₁ ≡ₚ e₂) (hst : KStep Γ e₂ w) :
    ∃ t, ParRedKS Γ e₁ t ∧ Γ ⊢ t ≡ₚ w := by
  obtain ⟨T, hd⟩ := H1.defeq hΓ
  have he₁ : Γ ⊢ e₁ : T := hd.hasType.1
  have hwq : Γ ⊢ w ≡ e₂ := (KStep.defeq hΓ hst).symm
  cases hst with
  | @mk p₁ p₂ r f₂ b c A₀ B₀ m1 m2 r1 hm hck hf hdq =>
    obtain ⟨hq1, hq2⟩ := Params.pat_app_noApp r1
    cases hm with
    | @app _ _ f1 g1 _ _ f2 g2 hmf hmc =>
      have hcty : Γ ⊢ c : A₀ := hdq.hasType.2
      have hbty : Γ ⊢ b : A₀ := hdq.hasType.1
      have hnodety : Γ ⊢ .app f₂ b : B₀.inst b := hf.app hbty
      have hwB : ∀ lp, ∀ l ∈ Sum.elim f1 f2 lp, VLevel.WF univs l :=
        (Pattern.Matches.app hmf hmc).levelWF hΓ (hf.app hcty)
      -- The node, matched at `.var p₁`: the function side's pattern, argument slot free.  The
      -- slot is filled with the node's *own* argument `b`, not with the rule's canonical
      -- major premise `c`; bridging the two is `hdq`'s job, below.
      have hmvar : (Pattern.var p₁).Matches (.app f₂ b) f1 (fun x => x.elim b g1) := .var hmf
      have hbot : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
          {u1 : (Pattern.var p₁).LPath → List VLevel} {u2 : (Pattern.var p₁).Path → VExpr},
          Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
          (Pattern.var p₁).Matches t u1 u2 →
          (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (f1 lp)) →
          (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
          (∀ x, Γ' ⊢ u2 x ≡ₚ ((x.elim b g1 : VExpr)).liftN n) →
          ∃ s, ParRedKS Γ' t s ∧
            Γ' ⊢ s ≡ₚ (Pattern.RHS.apply (p := p₁.app p₂)
              (Sum.elim f1 f2) (Sum.elim g1 g2) r.fst).liftN n := by
        intro Γ' n t u1 u2 W hΓ' ht' hmt hlv hwA hne
        cases hmt with
        | @var _ tf' _ g1' ta' hmtf =>
          rename_i hmtf
          have ⟨_, htT⟩ := ht'
          have ⟨A₀', B₀', htf', hta'⟩ := htT.app_inv henv hΓ'
          -- the rule's canonical major premise, weakened into `Γ'`
          have hmc' : p₂.Matches (c.liftN n) f2 (fun x => (g2 x).liftN n) :=
            Pattern.matches_liftN.2 ⟨_, hmc, fun _ => rfl⟩
          have hcW : Γ' ⊢ c.liftN n : A₀.liftN n := hcty.weakN henv W
          have hbW : Γ' ⊢ b.liftN n : A₀.liftN n := hbty.weakN henv W
          have hbv : Γ' ⊢ ta' ≡ₚ b.liftN n := by simpa using hne none
          have hleaf : ∀ x, Γ' ⊢ g1' x ≡ₚ (g1 x).liftN n := fun x => by simpa using hne (some x)
          have hmK : (p₁.app p₂).Matches (.app tf' (c.liftN n)) (Sum.elim u1 f2)
              (Sum.elim g1' (fun x => (g2 x).liftN n)) := .app hmtf hmc'
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
          have hneS : ∀ x : (p₁.app p₂).Path,
              Γ' ⊢ (Sum.elim g1' (fun y => (g2 y).liftN n) : _ → VExpr) x
                ≡ₚ (Sum.elim g1 g2 x).liftN n := by
            rintro (x|x)
            · exact hleaf x
            · exact have ⟨_, ht⟩ := hmc'.hasType hΓ' hcW x; .refl ht
          have hckW := hck.weakN W r.snd
          have hckK : Pattern.Check.OK (IsDefEqU env univs Γ') (p := p₁.app p₂)
              (Sum.elim u1 f2) (Sum.elim g1' (fun y => (g2 y).liftN n)) r.snd := by
            refine hckW.map_levels (fun x i y j hl => ?_) (fun u v h => ?_)
            · exact ((VLevel.forall₂_getD (hlvS x) i).trans hl).trans
                (VLevel.forall₂_getD (hlvS y) j).symm
            · obtain ⟨V, hV⟩ := h
              have step : ∀ (v : (p₁.app p₂).RHS) {C},
                  Γ' ⊢ Pattern.RHS.apply (p := p₁.app p₂) (Sum.elim f1 f2)
                        (fun x => (Sum.elim g1 g2 x).liftN n) v : C →
                  Γ' ⊢ Pattern.RHS.apply (p := p₁.app p₂) (Sum.elim f1 f2)
                        (fun x => (Sum.elim g1 g2 x).liftN n) v ≡
                      Pattern.RHS.apply (p := p₁.app p₂) (Sum.elim u1 f2)
                        (Sum.elim g1' (fun y => (g2 y).liftN n)) v := by
                intro v C hv
                have hins := NormalEq.apply_instL (p := p₁.app p₂) (r := v) hΓ' hwB hwAS hlvS' hv
                have ⟨_, hh⟩ := hins.defeq hΓ'
                refine (hins.defeq hΓ').trans henv hΓ'
                  (IsDefEqU.apply_pat hΓ' (fun x _ _ => ((hneS x).defeq hΓ').symm) hh.hasType.2)
              exact ((step u hV.hasType.1).symm.trans henv hΓ' ⟨_, hV⟩).trans henv hΓ'
                (step v hV.hasType.2)
          -- **`KStep` fires.**  Only the function side matches; the argument reached, `ta'`,
          -- is bridged to the canonical major premise `c` through the node's own argument `b`
          -- -- `NormalEq` to `ta'`, definitionally equal to `c` by `hdq`.
          have hdq' : Γ' ⊢ ta' ≡ c.liftN n : A₀' := by
            refine ((hbv.defeq hΓ').trans henv hΓ' ?_).of_l henv hΓ' hta'
            exact ⟨_, hdq.weakN henv W⟩
          have hfire : ParRedK Γ' (.app tf' ta')
              (Pattern.RHS.apply (p := p₁.app p₂) (Sum.elim u1 f2)
                (Sum.elim g1' (fun y => (g2 y).liftN n)) r.fst) :=
            ParRedK.hK (.mk r1 hmK hckK htf' hdq')
          refine ⟨_, .tail .rfl hfire, ?_⟩
          rw [Pattern.RHS.liftN_apply (p := p₁.app p₂) (m1 := Sum.elim f1 f2)
            (m2 := Sum.elim g1 g2) r.fst]
          exact NormalEq.apply_congr (p := p₁.app p₂) (r := r.fst) hΓ' hwAS hwB hlvS
            (fun x _ _ => hneS x) (hfire.hasType hΓ' htT)
      match NormalEq.descendV _ (Nat.le_refl _)
          (show (Pattern.var p₁).NoApp from hq1) hΓ H1 hmvar with
      | .inl ⟨k, D⟩ => exact DescentLamK.fire hΓ ⟨_, he₁⟩ hwq hbot D.toK
      | .inr ⟨P, hP, hp1, hp2⟩ =>
        exact ⟨_, .rfl, .proofIrrel hP hp1 ((hwq.symm.of_l henv hΓ hp2).hasType.2)⟩


/-! ## The grading: redex-nesting height

The reorganisation the residual asks for needs a measure on `ParRedK` derivations that is

* **strictly decreased by `keta`** -- so the `appDF` x `keta` row becomes an induction step
  rather than a hypothesis, and
* **left alone by the two operations the eta rows perform on `H2`**, namely `ParRedK.weakN`
  and `· ↦ .app · .bvar` (`KSite7Rows.NormalEq.etaL_of_parRedK` builds exactly
  `.app (H2.weakN .one) .bvar`, and `KSite7.etaR_case` runs `etaR_inner` over a sequence built
  the same way).

Derivation *size* fails the second condition and the sum `|H1| + |H2|` is constant across
`etaL`, which is what `KSite7Rows.lean`'s table records.  The measure below passes both: index
the congruence constructors *uniformly* (both children at the same grade) rather than
additively, so the grade is the **height of redex nesting**, and `.bvar` -- which holds at
every grade -- costs nothing when it is grafted on.

`ParRedKn` is therefore not a mere copy of `ParRedK` with a counter: the choice of `n` on both
children of `app`/`lam`/`forallE` is what makes `app_bvar` below true. -/

/-- `ParRedK` graded by the height of redex nesting.  Constructors are `ParRedK`'s; the three
redex constructors (`beta`, `extra`, `keta`) raise the grade by one and the congruences keep
it, so `ParRedKn n` says *no chain of nested redex contractions in this derivation is longer
than `n`*.  `ParRedKn.mono` and `ParRedK.toN` show the union over `n` is `ParRedK`. -/
inductive ParRedKn : Nat → List VExpr → VExpr → VExpr → Prop where
  | bvar {n Γ i} : ParRedKn n Γ (.bvar i) (.bvar i)
  | sort {n Γ u} : ParRedKn n Γ (.sort u) (.sort u)
  | const {n Γ c ls} : ParRedKn n Γ (.const c ls) (.const c ls)
  | app {n Γ f f' a a'} :
      ParRedKn n Γ f f' → ParRedKn n Γ a a' → ParRedKn n Γ (.app f a) (.app f' a')
  | lam {n Γ A A' body body'} :
      ParRedKn n Γ A A' → ParRedKn n (A::Γ) body body' → ParRedKn n Γ (.lam A body) (.lam A' body')
  | forallE {n Γ A A' B B'} :
      ParRedKn n Γ A A' → ParRedKn n (A::Γ) B B' → ParRedKn n Γ (.forallE A B) (.forallE A' B')
  | beta {n Γ A e₁ e₁' e₂ e₂'} :
      ParRedKn n (A::Γ) e₁ e₁' → ParRedKn n Γ e₂ e₂' →
      ParRedKn (n+1) Γ (.app (.lam A e₁) e₂) (e₁'.inst e₂')
  | extra {n Γ p r e m1 m2 m2'} :
      Params.Pat p r → Pattern.Matches p e m1 m2 →
      Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
      (∀ a, ParRedKn n Γ (m2 a) (m2' a)) →
      ParRedKn (n+1) Γ e (Pattern.RHS.apply m1 m2' r.1)
  | keta {n Γ e w w'} : EtaK Γ e w → ParRedKn n Γ w w' → ParRedKn (n+1) Γ e w'

theorem ParRedKn.toParRedK {n : Nat} {Γ : List VExpr} {e e' : VExpr}
    (H : ParRedKn n Γ e e') : ParRedK Γ e e' := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih => exact .extra h1 h2 h3 ih
  | keta hek _ ih => exact .keta hek ih

protected theorem ParRedKn.rfl {n : Nat} : ∀ {Γ : List VExpr} {e : VExpr}, ParRedKn n Γ e e
  | _, .bvar .. => .bvar
  | _, .sort .. => .sort
  | _, .const .. => .const
  | _, .app .. => .app ParRedKn.rfl ParRedKn.rfl
  | _, .lam .. => .lam ParRedKn.rfl ParRedKn.rfl
  | _, .forallE .. => .forallE ParRedKn.rfl ParRedKn.rfl

theorem ParRedKn.mono : ∀ {n m : Nat} {Γ : List VExpr} {e e' : VExpr},
    n ≤ m → ParRedKn n Γ e e' → ParRedKn m Γ e e' := by
  intro n m Γ e e' hnm H
  induction H generalizing m with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app (ih1 hnm) (ih2 hnm)
  | lam _ _ ih1 ih2 => exact .lam (ih1 hnm) (ih2 hnm)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 hnm) (ih2 hnm)
  | beta _ _ ih1 ih2 =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
    exact .beta (ih1 (by omega)) (ih2 (by omega))
  | extra h1 h2 h3 _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
    exact .extra h1 h2 h3 (fun a => ih a (by omega))
  | keta hek _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
    exact .keta hek (ih (by omega))

/-- Every `ParRedK` derivation has a grade: the two relations have the same graph. -/
theorem ParRedK.toN {Γ : List VExpr} {e e' : VExpr} (H : ParRedK Γ e e') :
    ∃ n, ParRedKn n Γ e e' := by
  induction H with
  | bvar => exact ⟨0, .bvar⟩
  | sort => exact ⟨0, .sort⟩
  | const => exact ⟨0, .const⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨max n₁ n₂, .app (h₁.mono (Nat.le_max_left ..)) (h₂.mono (Nat.le_max_right ..))⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨max n₁ n₂, .lam (h₁.mono (Nat.le_max_left ..)) (h₂.mono (Nat.le_max_right ..))⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨max n₁ n₂, .forallE (h₁.mono (Nat.le_max_left ..)) (h₂.mono (Nat.le_max_right ..))⟩
  | beta _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨max n₁ n₂ + 1,
      .beta (h₁.mono (Nat.le_max_left ..)) (h₂.mono (Nat.le_max_right ..))⟩
  | @extra Γ p r e0 m1 m2 m2' h1 h2 h3 _ ih =>
    obtain ⟨n, hn⟩ := Pattern.exists_bound
      (P := fun n a => ParRedKn n Γ (m2 a) (m2' a)) (fun hle hp => hp.mono hle) ih
    exact ⟨n+1, .extra h1 h2 h3 hn⟩
  | keta hek _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .keta hek hn⟩

/-- **Invariance fact 1: weakening keeps the grade.**  `ParRedK.weakN`'s proof, with the index
threaded; every congruence keeps it and every redex constructor keeps its own `+1`. -/
theorem ParRedKn.weakN {n : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr} {j k : Nat}
    (W : Ctx.LiftN j k Γ Γ') (H : ParRedKn n Γ e1 e2) :
    ParRedKn n Γ' (e1.liftN j k) (e2.liftN j k) := by
  induction H generalizing k Γ' with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [VExpr.liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    exact .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)
  | keta hek _ ih => exact .keta (hek.weakN W) (ih W)

/-- **Invariance fact 2: η-expanding the subject keeps the grade.**  This is the step the two
eta rows take on `H2`, and it is exactly where derivation size fails: the derivation gains a
node (`app`) and a binder's worth of lifting, and the grade does not move, because `.bvar`
inhabits every grade and `app` is graded uniformly rather than additively. -/
theorem ParRedKn.app_bvar {n : Nat} {Γ : List VExpr} {A e e' : VExpr}
    (H : ParRedKn n Γ e e') :
    ParRedKn n (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) :=
  .app (H.weakN .one) .bvar

/-! ## The skeleton: site 7 graded, and the `keta` row as an induction step -/

/-- Site 7 restricted to derivations of grade at most `N`.  `parRedKStatement_of_graded` says
the family is equivalent to site 7. -/
def ParRedKStatementN (N : Nat) : Prop :=
  ∀ {n : Nat} {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}, n ≤ N → OnCtx Γ (IsType env univs) →
    NormalEq Γ e₁ e₂ → ParRedKn n Γ e₂ e₂' → ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂'

theorem ParRedKStatementN.mono {N M : Nat} (h : N ≤ M) (S : ParRedKStatementN M) :
    ParRedKStatementN N := fun hn => S (Nat.le_trans hn h)

theorem parRedKStatement_of_graded (S : ∀ N, ParRedKStatementN N) : ParRedKStatement := by
  intro Γ e₁ e₂ e₂' hΓ H1 H2
  obtain ⟨n, hn⟩ := H2.toN
  exact S n (Nat.le_refl _) hΓ H1 hn

theorem parRedKStatementN_of_parRedKStatement (S : ParRedKStatement) (N : Nat) :
    ParRedKStatementN N := fun _ hΓ H1 H2 => S hΓ H1 H2.toParRedK

/-- **The point of the file, stated exactly.**  The `keta` row -- `AppKetaRow`'s whole
content, and now at an arbitrary `NormalEq` rather than only under an `appDF` -- follows from

* `EtaKNormalEqInv`, which mentions no development at all, and
* site 7 **at grade `N`**, applied only to `htail`, which has grade `N` while the row's own
  derivation has grade `N+1`.

So the appeal is to a strictly smaller instance: this is the induction step, not a hypothesis.
Compare `KSite7Rows.appKetaRow_of_parRedKStatement`, which needs site 7 at the *same* instance
and is therefore only a collapse test.

What remains before `AppKetaRow` is discharged is the other eight rows at grade `N+1`, whose
`ParRedK`-shaped statements in `KSite7`/`KSite7App` have to be restated over `ParRedKn`.  Two
of the eight -- `etaL` and `etaR` -- are the ones the grading exists for; `ParRedKn.app_bvar`
is what they need and it is proved above. -/
theorem ketaRow_of_etaKNormalEqInv {N : Nat} (HE : EtaKNormalEqInv) (S : ParRedKStatementN N)
    {Γ : List VExpr} {e₁ e₂ w e₂' : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H1 : Γ ⊢ e₁ ≡ₚ e₂) (hek : EtaK Γ e₂ w) (htail : ParRedKn N Γ w e₂') :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  obtain ⟨t, ht1, ht2⟩ := HE hΓ H1 hek
  obtain ⟨u, hu1, hu2⟩ := S (Nat.le_refl _) hΓ ht2 htail
  exact ⟨u, ht1.trans hu1, hu2⟩

/-- The same, in `AppKetaRow`'s own shape: the six `appDF` premises are not used, which is a
measurement -- the row never inspects the node's congruence, only the `EtaK` step. -/
theorem appKetaRow_step {N : Nat} (HE : EtaKNormalEqInv) (S : ParRedKStatementN N)
    {Γ : List VExpr} {f A B f₂ a b w e₂' : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A) (l5 : Γ ⊢ f ≡ₚ f₂) (l6 : Γ ⊢ a ≡ₚ b)
    (hek : EtaK Γ (.app f₂ b) w) (htail : ParRedKn N Γ w e₂') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' :=
  ketaRow_of_etaKNormalEqInv HE S hΓ (.appDF l1 l2 l3 l4 l5 l6) hek htail


/-! ## A cleaner composition: `DomEq` on the left needs no strengthening

The `under` half above closes with `NormalEq.trans`, and that is the *only* thing in it that
carries `IsDefEqU.weakN_iff` -- `NormalEq.trans`'s single appeal to strengthening
(`ChurchRosser.lean:630`) is its `etaR`-after-`etaL` case.  Both compositions the `under` half
performs have a **`DomEq` on the left**, and `DomEq` has no `etaL`, so that case is
*unreachable* for them.

`DomEq.trans_normalEq` is the composition with that case deleted.  It is `NormalEq.trans`'s
proof with the left relation narrowed: same term measure, same case split, one case gone.
`ketaHere_inv_clean` and `etaKNormalEqInv_of_weakNInvDS'` below are the `under` half rebuilt on
it, and they are clean of `weakN_iff` -- so the `keta` row does not add a third entry to the
two `KSite7Rows.lean` measures.  The same substitution would clean `KSite7.etaR_case`, which
composes the same way (`((dc.toNormalEq).symm hΓA).trans hΓA a2`); that edit is not made here.
-/

private def meas' : VExpr → Nat
  | .app f a
  | .forallE f a => meas' f + meas' a + 1
  | .bvar _ | .const .. | .sort _ => 0
  | .lam A e => meas' A + meas' e + 3

omit [Params] in private theorem meas'_liftN {e : VExpr} {n k : Nat} :
    meas' (e.liftN n k) = meas' e := by
  induction e generalizing k <;> simp [*, meas', VExpr.liftN]
omit [Params] in private theorem meas'_lift {e : VExpr} : meas' e.lift = meas' e := meas'_liftN

attribute [local simp] meas' meas'_lift in
/-- **`DomEq ∘ NormalEq = NormalEq`, with no appeal to strengthening.**  Compare
`NormalEq.trans`, whose one use of `NormalEq.weakN_iff` -- hence of `IsDefEqU.weakN_iff` -- is
in the case where the left derivation ends in `etaR` and the right in `etaL`.  `DomEq` has no
`etaR`, so that case does not arise and the composition is unconditional. -/
theorem DomEq.trans_normalEq {Γ : List VExpr} {e1 e2 e3 : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) :
    DomEq Γ e1 e2 → Γ ⊢ e2 ≡ₚ e3 → Γ ⊢ e1 ≡ₚ e3
  | .sortDF l1 _ l3, .sortDF _ r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (List.Forall₂.trans (fun _ _ _ h1 => h1.trans) l5 r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4)
      (l5.trans_normalEq hΓ r5) (l6.trans_normalEq hΓ r6)
  | .lamDF l1 l2 l3, .lamDF r1 r2 r3 =>
    have aa := r1.trans_r henv hΓ l2.symm
    .lamDF l1 (aa.symm.trans_l henv hΓ r2)
      (l3.trans_normalEq ⟨hΓ, _, l1.hasType.1⟩ (r3.defeq_l hΓ aa))
  | .forallEDF l1 l2 l3 l4, .forallEDF r1 r2 r3 r4 =>
    have r4' := r4.defeq_l hΓ
      (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
    .forallEDF l1 (l2.trans_normalEq hΓ r2) l3
      (l4.trans_normalEq ⟨hΓ, _, l1.hasType.1⟩ r4')
  | .lamDF l1 l2 l3, .etaL r1 ih =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have eq := l2.symm.trans l1
    .etaL (IsDefEq.defeq (.forallEDF eq hB) r1) <|
      (l3.defeq_l hΓ l1).trans_normalEq ⟨hΓ, _, l1.hasType.2⟩ (ih.defeq_l hΓ eq)
  | .refl h, H2 => H2
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)
  | H1, .refl _ => H1.toNormalEq
  | H1, .etaR r1 ih => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    refine .etaR (.defeqU_l henv hΓ (H1.defeq hΓ).symm r1)
      (DomEq.trans_normalEq (e2 := .app _ (.bvar 0)) ⟨hΓ, _, hA⟩ ?_ ih)
    exact .appDF ((r1.defeqU_l henv hΓ (H1.defeq hΓ).symm).weakN henv .one)
      (r1.weakN henv .one) (.bvar .zero) (.bvar .zero)
      (H1.weakN .one) (.refl (.bvar .zero))
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3
termination_by meas' e1 + meas' e2 + meas' e3


attribute [local simp] meas' meas'_lift in
/-- **The mirror: `NormalEq ∘ DomEq = NormalEq`, also with no appeal to strengthening.**  The
bad case of `NormalEq.trans` needs `etaR` on the left *and* `etaL` on the right; killing either
one suffices, and `DomEq` on the right kills the second. -/
theorem NormalEq.trans_domEq {Γ : List VExpr} {e1 e2 e3 : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) :
    Γ ⊢ e1 ≡ₚ e2 → DomEq Γ e2 e3 → Γ ⊢ e1 ≡ₚ e3
  | .sortDF l1 _ l3, .sortDF _ r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (List.Forall₂.trans (fun _ _ _ h1 => h1.trans) l5 r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4)
      (l5.trans_domEq hΓ r5) (l6.trans_domEq hΓ r6)
  | .lamDF l1 l2 l3, .lamDF r1 r2 r3 =>
    have aa := r1.trans_r henv hΓ l2.symm
    .lamDF l1 (aa.symm.trans_l henv hΓ r2)
      (l3.trans_domEq ⟨hΓ, _, l1.hasType.1⟩ (r3.defeq_l hΓ aa))
  | .forallEDF l1 l2 l3 l4, .forallEDF r1 r2 r3 r4 =>
    have r4' := r4.defeq_l hΓ
      (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
    .forallEDF l1 (l2.trans_domEq hΓ r2) l3 (l4.trans_domEq ⟨hΓ, _, l1.hasType.1⟩ r4')
  | .etaR l1 ih, .lamDF r1 r2 r3 =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have eq := r1.symm.trans r2
    .etaR (IsDefEq.defeq (.forallEDF eq hB) l1) <|
      (ih.defeq_l hΓ eq).trans_domEq ⟨hΓ, _, r2.hasType.2⟩ (r3.defeq_l hΓ r2)
  | .refl h, H2 => H2.toNormalEq
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)
  | .etaL l1 ih, H2 => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    refine .etaL (.defeqU_l henv hΓ (H2.defeq hΓ) l1)
      (NormalEq.trans_domEq (e3 := .app _ (.bvar 0)) ⟨hΓ, _, hA⟩ ih ?_)
    exact .appDF (l1.weakN henv .one)
      ((l1.defeqU_l henv hΓ (H2.defeq hΓ)).weakN henv .one) (.bvar .zero) (.bvar .zero)
      (H2.weakN .one) (.refl (.bvar .zero))
  | H1, .refl _ => H1
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3
termination_by meas' e1 + meas' e2 + meas' e3

/-- **`KSite7.etaR_case`, rebuilt on the two narrow compositions and clean of
`IsDefEqU.weakN_iff`.**  Statement and proof are `KSite7.etaR_case`'s; the only changes are the
three `NormalEq.trans` calls, replaced by `DomEq.trans_normalEq` / `NormalEq.trans_domEq` at
the exact places where one side is already a `DomEq`.

`KSite7Rows.lean`'s row-by-row measurement lists `etaR` as one of the two rows carrying
`weakN_iff`.  With this body it does not, which leaves `appDF` x `beta` (through
`ChurchRosser.ParRedExt.parRed_beta`) as the **only** entry of `weakN_iff` into site 7.  The
substitution is not made in `KSite7.lean` here; this is the drop-in, measured. -/
theorem etaR_case_clean (HD : WeakNInvDS) {Γ : List VExpr} {A B e eb A' b' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ e : .forallE A B) (l2 : NormalEq (A::Γ) (.app e.lift (.bvar 0)) eb)
    (ih1 : ∀ {x : VExpr}, ParRedK (A::Γ) eb x →
      ∃ t, ParRedKS (A::Γ) (.app e.lift (.bvar 0)) t ∧ NormalEq (A::Γ) t x)
    (r1 : ParRedK Γ A A') (r2 : ParRedK (A::Γ) eb b') :
    ∃ e₁', ParRedKS Γ e e₁' ∧ NormalEq Γ e₁' (.lam A' b') := by
  obtain ⟨⟨uA, hA⟩, vB, hB⟩ := (have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hb0 : (A::Γ) ⊢ VExpr.app e.lift (.bvar 0) : B := by
    simpa [instN_bvar0] using HasType.app (l1.weak (B := A) henv) (.bvar .zero)
  have hebty : (A::Γ) ⊢ eb : B := HasType.defeqU_l henv hΓA (l2.defeq hΓA) hb0
  have hlamty : Γ ⊢ VExpr.lam A eb : .forallE A B := hA.lam hebty
  obtain ⟨t, a1, a2⟩ := ih1 r2
  rcases etaR_inner HD hΓ hA hB l1 a1 with
    ⟨A₂, c, hred, hA₂, dc⟩ | ⟨e', f₀, hred, rfl, df⟩ | hpe
  · exact ⟨.lam A₂ c, hred, .lamDF (hA₂.of_r henv hΓ hA).symm (r1.defeq hΓ hA)
      ((dc.symm hΓA).trans_normalEq hΓA a2)⟩
  · have he'ty : Γ ⊢ e' : .forallE A B := ParRedKS.hasType hΓ hred l1
    have he'l2 := he'ty.weak (B := A) henv
    simp only [VExpr.liftN] at he'l2
    have hf₀ty := DomEq.hasType hΓA (df.symm hΓA) he'l2
    have Dsub : DomEq (A::Γ) (.app e'.lift (.bvar 0)) (.app f₀ (.bvar 0)) :=
      .appDF he'l2 hf₀ty (.bvar .zero) (.bvar .zero) (df.symm hΓA) (.refl (.bvar .zero))
    refine ⟨e', hred, ?_⟩
    exact (NormalEq.etaR he'ty (Dsub.trans_normalEq hΓA a2)).trans_domEq hΓ
      (.lamDF hA (r1.defeq hΓ hA) (.refl (r2.hasType hΓA hebty)))
  · obtain ⟨P, hP, he1, -⟩ := hpe
    refine ⟨e, .rfl, .proofIrrel hP he1 ?_⟩
    have hlam' : Γ ⊢ VExpr.lam A' b' : .forallE A B := (ParRedK.lam r1 r2).hasType hΓ hlamty
    exact HasType.defeqU_r henv hΓ (l1.uniqU henv hΓ he1) hlam'

/-! ## The `under` half, from `WeakNInvDS` -- so the whole transport costs nothing new

`EtaK.under` is an η-tower over the redex.  Peeling a layer weakens the `NormalEq` under a
binder and applies it to `.bvar 0`; the recursion is on the tower's height (`EtaKn`,
`KMeasure.lean`, whose height is a function of the *term* by `EtaKn.height_eq`) and bottoms out
at `ketaHere_inv`.  Coming back out costs site 1 -- the answer arrives as a development of
`.app e₁.lift (.bvar 0)` upstairs and must come back down as a development of `e₁` -- and that
is exactly what `KSite7.etaR_inner` already extracts from `WeakNInvDS`.  It is reused here
verbatim, at `e₁` instead of at `etaR`'s subject; its three-way conclusion maps onto
`NormalEq.lamDF`, `NormalEq.etaR` and `NormalEq.proofIrrel` the same way
`KSite7.etaR_case`'s does.

**So `EtaKNormalEqInv` is not a second hypothesis.**  Site 7's cost after this file is
`WeakNInvDS` plus the mechanical restatement of the eight non-`keta` rows over `ParRedKn`;
`AppKetaRow` is no longer part of the price. -/
theorem etaKNormalEqInv_of_weakNInvDS (HD : WeakNInvDS) : EtaKNormalEqInv := by
  suffices H : ∀ {k : Nat} {Γ : List VExpr} {e₂ w : VExpr}, EtaKn k Γ e₂ w →
      ∀ {e₁ : VExpr}, OnCtx Γ (IsType env univs) → NormalEq Γ e₁ e₂ →
        ∃ t, ParRedKS Γ e₁ t ∧ Γ ⊢ t ≡ₚ w by
    intro Γ e₁ e₂ w hΓ H1 hek
    obtain ⟨_, hk⟩ := hek.count
    exact H hk hΓ H1
  intro k Γ e₂ w hk
  induction hk with
  | here hst => exact fun hΓ H1 => NormalEq.ketaHere_inv hΓ H1 hst
  | @under Γ e A B t k hty hek' ih =>
    intro e₁ hΓ H1
    obtain ⟨⟨uA, hA⟩, vB, hB⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv)
    have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have he₁ty : Γ ⊢ e₁ : .forallE A B := ((H1.defeq hΓ).symm.of_l henv hΓ hty).hasType.2
    -- one layer down: the `NormalEq`, weakened and applied to `.bvar 0`
    have h1l : (A::Γ) ⊢ e₁.lift : (VExpr.forallE A B).lift := he₁ty.weak henv
    have h2l : (A::Γ) ⊢ e.lift : (VExpr.forallE A B).lift := hty.weak henv
    simp only [VExpr.liftN] at h1l h2l
    have hlift : (A::Γ) ⊢ .app e₁.lift (.bvar 0) ≡ₚ .app e.lift (.bvar 0) :=
      .appDF h1l h2l (.bvar .zero) (.bvar .zero) (H1.weakN .one) (.refl (.bvar .zero))
    obtain ⟨s, hs1, hs2⟩ := ih hΓA hlift
    rcases etaR_inner HD hΓ hA hB he₁ty hs1 with
      ⟨A₂, c, hred, hA₂, dc⟩ | ⟨e', f₀, hred, rfl, df⟩ | hpe
    · exact ⟨.lam A₂ c, hred,
        .lamDF (hA₂.of_r henv hΓ hA).symm hA ((dc.symm hΓA).trans_normalEq hΓA hs2)⟩
    · have he'ty : Γ ⊢ e' : .forallE A B := ParRedKS.hasType hΓ hred he₁ty
      have he'l2 := he'ty.weak (B := A) henv
      simp only [VExpr.liftN] at he'l2
      have hf₀ty := DomEq.hasType hΓA (df.symm hΓA) he'l2
      have Dsub : DomEq (A::Γ) (.app e'.lift (.bvar 0)) (.app f₀ (.bvar 0)) :=
        .appDF he'l2 hf₀ty (.bvar .zero) (.bvar .zero) (df.symm hΓA) (.refl (.bvar .zero))
      exact ⟨e', hred, .etaR he'ty (Dsub.trans_normalEq hΓA hs2)⟩
    · obtain ⟨P, hP, hp1, -⟩ := hpe
      refine ⟨e₁, .rfl, .proofIrrel hP hp1 ?_⟩
      have hwe : Γ ⊢ e₁ ≡ VExpr.lam A t :=
        (H1.defeq hΓ).trans henv hΓ ((EtaKn.under hty hek').toEtaK.defeqU hΓ)
      exact (hwe.of_l henv hΓ hp1).hasType.2

/-- **The `keta` row from `WeakNInvDS` alone.**  `ketaRow_of_etaKNormalEqInv` with its transport
premise discharged: the row's only outside appeal is now site 7 at grade `N`, i.e. at a strict
sub-derivation of the row's own `ParRedKn (N+1)`.

This is the file's conclusion.  `AppKetaRow` is not on site 7's bill any more; what replaces it
is the mechanical restatement of the eight non-`keta` rows over `ParRedKn`, for which
`ParRedKn.app_bvar` supplies the one non-mechanical ingredient. -/
theorem ketaRow_of_weakNInvDS {N : Nat} (HD : WeakNInvDS) (S : ParRedKStatementN N)
    {Γ : List VExpr} {e₁ e₂ w e₂' : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H1 : Γ ⊢ e₁ ≡ₚ e₂) (hek : EtaK Γ e₂ w) (htail : ParRedKn N Γ w e₂') :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' :=
  ketaRow_of_etaKNormalEqInv (etaKNormalEqInv_of_weakNInvDS HD) S hΓ H1 hek htail



/-! ## The base of the induction is real

Grade `0` admits no `beta`, `extra` or `keta` -- all three constructors conclude at `n+1` -- so
a grade-0 development is a *pure* congruence, and a pure congruence is the identity.  Site 7 at
grade 0 is therefore trivial, and `ketaRow_of_weakNInvDS` at `N = 0` gives the `appDF` x `keta`
row at grade 1 from `WeakNInvDS` **alone**: an unconditional instance of what `AppKetaRow` used
to assume outright.

Note which of site 7's two `IsDefEqU.weakN_iff` entries this base case avoids: `appDF` x `beta`
cannot occur at grade 0 either, so `parRedKStatementN_zero` is clean by construction, and
`ketaRow_of_weakNInvDS_at_one` inherits that. -/

/-- A grade-0 development moves nothing. -/
theorem ParRedKn.eq_of_zero : ∀ {n : Nat} {Γ : List VExpr} {e e' : VExpr},
    ParRedKn n Γ e e' → n = 0 → e = e' := by
  intro n Γ e e' H
  induction H with
  | bvar | sort | const => exact fun _ => rfl
  | app _ _ ih1 ih2 => exact fun h => by rw [ih1 h, ih2 h]
  | lam _ _ ih1 ih2 => exact fun h => by rw [ih1 h, ih2 h]
  | forallE _ _ ih1 ih2 => exact fun h => by rw [ih1 h, ih2 h]
  | beta | extra | keta => exact fun h => absurd h (Nat.succ_ne_zero _)

/-- Site 7 at grade 0, unconditionally. -/
theorem parRedKStatementN_zero : ParRedKStatementN 0 := by
  intro n Γ e₁ e₂ e₂' hn _ H1 H2
  obtain rfl : n = 0 := Nat.le_zero.1 hn
  obtain rfl := H2.eq_of_zero rfl
  exact ⟨e₁, .rfl, H1⟩

/-- **The `appDF` x `keta` row at grade 1, from `WeakNInvDS` alone.**  No site-7 hypothesis, no
`AppKetaRow`, and clean of `IsDefEqU.weakN_iff`. -/
theorem ketaRow_of_weakNInvDS_at_one (HD : WeakNInvDS)
    {Γ : List VExpr} {e₁ e₂ w e₂' : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H1 : Γ ⊢ e₁ ≡ₚ e₂) (hek : EtaK Γ e₂ w) (htail : ParRedKn 0 Γ w e₂') :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' :=
  ketaRow_of_weakNInvDS HD parRedKStatementN_zero hΓ H1 hek htail


/-! ## The substitution, run inside the real assembly

`parRedKStatement_of_rows_clean` is `KSite7Rows.parRedKStatement_of_rows` with one change:
`KSite7.etaR_case` replaced by `etaR_case_clean`.  It is here so that the drop-in claim is
*checked in situ* rather than only in isolation -- the rest of the assembly is untouched, and
the hypotheses are the same two.

The remaining `weakN_iff` in its cone is `appDF` x `beta`'s, through
`ChurchRosser.ParRedExt.parRed_beta`; every other row is measured clean
(`KSite7Rows.lean`'s own table, plus `etaR_case_clean` and `ketaRow_of_weakNInvDS` here). -/
theorem parRedKStatement_of_rows_clean (HD : WeakNInvDS) (HA : AppKetaRow) :
    ParRedKStatement := by
  suffices H : ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      OnCtx Γ (IsType env univs) → ∀ {e₂' : VExpr}, ParRedK Γ e₂ e₂' →
      ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' from
    fun _ _ _ _ hΓ H1 H2 => H H1 hΓ H2
  intro Γ e₁ e₂ H1
  induction H1 with
  | refl l1 => exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.refl l1) H2
  | sortDF l1 l2 l3 => exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.sortDF l1 l2 l3) H2
  | constDF l1 l2 l3 l4 l5 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.constDF l1 l2 l3 l4 l5) H2
  | proofIrrel l1 l2 l3 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.proofIrrel l1 l2 l3) H2
  | appDF l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    intro hΓ e₂' H2
    cases H2 with
    | app r1 r2 => exact NormalEq.appDF_app_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2
    | beta r1 r2 => exact NormalEq.appDF_beta_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2
    | extra r1 r2 r3 r4 =>
      exact NormalEq.appDF_extra_of_descendVK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2 r3 r4
    | keta hek htail => exact HA hΓ l1 l2 l3 l4 l5 l6 hek htail
  | lamDF l1 l2 l3 ih1 =>
    exact fun hΓ _ H2 =>
      NormalEq.lamDF_of_parRedK hΓ l1 l2 l3 (ih1 ⟨hΓ, _, l1.hasType.1⟩) H2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    exact fun hΓ _ H2 =>
      NormalEq.forallEDF_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 ⟨hΓ, _, l1.hasType.1⟩) H2
  | etaL l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    exact NormalEq.etaL_of_parRedK hΓ l1 (ih1 ⟨hΓ, _, hA⟩) H2
  | etaR l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    cases H2 with
    | lam r1 r2 => exact etaR_case_clean HD hΓ l1 l2 (ih1 ⟨hΓ, _, hA⟩) r1 r2
    | extra _ r2 => cases r2
    | keta hek _ => exact absurd hek EtaK.not_lam

end VEnv
end Lean4Lean
