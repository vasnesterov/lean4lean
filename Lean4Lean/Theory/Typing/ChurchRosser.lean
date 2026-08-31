import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean
open Lean4Lean

namespace VEnv

open VExpr

class Params where
  env : VEnv
  henv : env.WF
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  /--
  `hΓ` is not optional.  Proving this field means applying the λ-abstracted rule
  (`VDefEq.lhs = mkLams Δ L`) to the matched arguments, and `IsDefEq.appDF` needs each
  argument well-typed at the *declared* domain -- so the typing of `e` has to be inverted.
  Both available routes require a well-formed context: `HasType.app_inv`
  (`Typing/Strong.lean`) goes through `H.strong henv hΓ`, and `IsDefEq.uniq`
  (`Typing/UniqueTyping.lean`) takes `hΓ` directly.  Without it the field is very likely
  still *true* -- an ill-formed `Γ` only lets `bvar` carry junk types, while the application
  rules still pin the recursor's arguments -- but it is not provable by any route in the
  tree.  The sole consumer (`NormalEq.parRed`'s `extra` case, below) already has `hΓ` in
  scope and passes it to `.trans_l henv hΓ` in the same expression, so this costs nothing.

  Compare `SExpr.IsDefEq.strong`, which was *false* for the same structural reason.  On this
  development, a rule stated about an arbitrary `Γ` with no well-formedness hypothesis
  should be treated as suspect by default.
  -/
  pat_wf : Pat p r → p.Matches e m1 m2 → OnCtx Γ (IsType env univs) →
    HasType env univs Γ e A →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  /--
  Every `extra` rule of `env` is a `Pat`-registered pattern **under some leading lambdas**.

  The λ-peeling is forced: `VDefEq.lhs` is a closed term, so a rule with parameters is
  λ-wrapped (`quotDefEq`'s lhs is `fun α r β f c a => Quot.lift α r β f c (Quot.mk r a)`),
  while `Pattern.Matches` only walks `const`/`app` spines. Without peeling this field is
  satisfiable only by environments whose every defeq is a bare δ-rule, which is why nothing
  instantiates `Params`. Peeling leaves `IsDefEq`, `VDefEq`, `Matches`, the `vdefeq`
  elaborator and `Theory/Quot.lean` untouched; the rejected alternative — storing `VDefEq`
  in applied form — would force `quotDefEq`, the elaborator and `QuotLemmas.lean` to be
  re-encoded.

  Note the `Check` obligations are discharged in the *extended* context `Δ.reverse ++ Γ`,
  which is exactly where the `ParRed.extra` step fires once `ParRed.lams` has wrapped it in
  `Δ.length` congruences.

  `hΓ` is not optional, for the same reason as `pat_wf`'s.  An ι-rule's index clauses are
  discharged by β-reducing `mkLams tel a` applied to the matched constructor arguments;
  `IsDefEq.beta` needs the function typed, typing a `mkLams` needs its telescope to be a
  well-formed context, and `OnCtx (tel.reverse ++ Δ.reverse ++ Γ)` unfolds to include
  `OnCtx Γ`.  Tail-weakening is free for `Lookup` — which is why the δ and quot cases need
  nothing — but `OnCtx` quantifies over every entry.  The sole consumer already holds the
  fact: `NormalEq.parRed`'s `extra` case (below) sits inside `IsDefEq.church_rosser`, whose
  `Γ` is an *index* of `IsDefEq`, so `induction H` reverts `hΓ` and reintroduces it in every
  case — which is why the sibling cases use it freely.  So this costs one argument at one
  call site.

  Compare `SExpr.IsDefEq.strong`, which was *false* for exactly this reason, and `pat_wf`,
  which was under-hypothesised for it.  Three for three: on this development a rule stated
  about an arbitrary `Γ` with no well-formedness hypothesis is suspect by default.

  **Level hypothesis at `univs`, not at a stray `uvars`.**  This field previously read
  `∀ l ∈ ls, l.WF uvars`, where `uvars` was an *auto-bound implicit* of the field -- a fresh
  universally quantified `Nat`, unrelated to `Params.univs`.  (`uvars` is the section
  variable of `Theory/Typing/Basic.lean`, where `IsDefEq.extra` states the same hypothesis
  correctly; inside this class it auto-bound instead of resolving.)  That made the field ask
  for the conclusion at level lists that are *not* well-formed for the judgment, which
  `Theory/Typing/PatternRules.lean`'s `Pat.extra` cannot supply -- its ι case needs
  `IsDefEqU.instL`, which needs `l.WF univs`.  The sole consumer
  (`NormalEq.parRed`'s `extra` case) holds `l.WF univs`, so narrowing costs it nothing.
  -/
  extra_pat : OnCtx Γ (IsType env univs) →
    env.defeqs df → (∀ l ∈ ls, l.WF univs) → ls.length = df.uvars →
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
      Pat p r ∧ p.Matches L m1 m2 ∧
      r.2.OK (IsDefEqU env univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2

variable [Params]
open Params

theorem Params.pat_not_var : ¬Pat (.var p) r := (nomatch pat_simple ·)

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- **Universe uniqueness at `Params`' environment — derived, not assumed.**

`appDF_proofIrrel` and `descend`'s two E3 branches used to take this as an explicit
hypothesis `hsu`, on the stated grounds that getting it from `IsDefEqU.sort_inv` "would be
circular, since it is one of the facts confluence exists to deliver".  **That is false as of
today.**  Three checks, all mechanical:

* `Params.henv` is `env.WF`, and `VEnv.WF.sortUniq'` (`Theory/Typing/Injectivity.lean`)
  proves `env.SortUniq U` from it.
* `Injectivity.lean` is *already* in this file's import closure -- `ChurchRosser` imports
  `UniqueTyping`, which imports `Injectivity` -- so no import moves and no cycle is created.
  The dependency runs `ChurchRosser → Injectivity`, i.e. confluence **consumes** the
  Π/sort-inversion family; it does not supply it.
* Using it widens no cone: `WF.sortUniq'` is already a transitive dependency of
  `IsDefEq.uniq` and `IsDefEqU.of_l`, which `appDF_proofIrrel` and `descend` call directly.

`SortUniq` carries the two side conditions `u.WF univs`, `v.WF univs` that `hsu` did not;
they are recovered from the typings themselves by `HasType.sort_inv`. -/
theorem Params.sortUniq {Γ : List VExpr} {e : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (h1 : Γ ⊢ e : .sort u) (h2 : Γ ⊢ e : .sort v) : u ≈ v :=
  WF.sortUniq' (U := univs) henv hΓ
    (have ⟨_, h⟩ := h1.isType henv hΓ; h.sort_inv henv)
    (have ⟨_, h⟩ := h2.isType henv hΓ; h.sort_inv henv) h1 h2

theorem _root_.Lean4Lean.Pattern.Check.OK.weakN (W : Ctx.LiftN n k Γ Γ') {p : Pattern}
    (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ') m1 fun x => (m2 x).liftN n k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.liftN_apply]
  exact h.weakN henv W

theorem _root_.Lean4Lean.Pattern.Check.OK.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H₀ : Γ₀ ⊢ e₀ : A₀)
    {p : Pattern} (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ₁) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 fun x => (m2 x).inst e₀ k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.instN_apply]
  exact h.instN henv W H₀

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem IsDefEq.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) : Γ ⊢ apply m1 m2 r ≡ apply m1 m2' r : A := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact he.trans_l henv hΓ <| .appDF (ih1 h1) (ih2 h2)
  | var path => exact (ih path _ he).of_l henv hΓ he

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem _root_.Lean4Lean.Pattern.Matches.hasType {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (H2 : Γ ⊢ e : V) (a) : ∃ A, Γ ⊢ m2 a : A := by
  induction H generalizing V with
  | const => cases a
  | var _ ih =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec ⟨_, ha⟩ (ih hf)
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec (ih1 hf) (ih2 ha)

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ .sort l₂
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ .const c ls'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    A::Γ ⊢ body₁ ≡ₚ body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e →
    Γ ⊢ e' ≡ₚ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ h'

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e1 ≡ e2 := by
  induction H with
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 =>
    exact ⟨_, .appDF ((ih1 hΓ).of_l henv hΓ hf₁) ((ih2 hΓ).of_l henv hΓ ha₁)⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | lamDF hA₁ hA₂ _ ihB =>
    have ⟨_, hB⟩ := ihB ⟨hΓ, _, hA₁.hasType.1⟩
    exact ⟨_, .trans (.symm <| .lamDF hA₁ hB.symm) (.lamDF hA₂ hB.hasType.2)⟩
  | forallEDF hA₁ hA hB₁ _ ihA ihB =>
    exact have hΓ' := ⟨hΓ, _, hA₁.hasType.1⟩
      ⟨_, .trans (.symm <| .forallEDF hA₁ hB₁)
        (.forallEDF (hA₁.transU_l henv hΓ (ihA hΓ)) ((ihB hΓ').of_l henv hΓ' hB₁))⟩
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_r henv hΓ ⟨_, .lamDF hA he⟩ (.eta h1)⟩
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_l henv hΓ (.symm (.eta h1)) ⟨_, .lamDF hA he⟩⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, .proofIrrel h1 h2 h3⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2) : Γ ⊢ e2 ≡ₚ e1 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | lamDF h1 h2 h3 ih1 => exact .lamDF h2 h1 (ih1 ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := ⟨hΓ, _, h1.hasType.1⟩
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaR h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaL h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

theorem NormalEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2) :
    Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W)
      (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 ih1 =>
     exact .lamDF (h1.weakN henv W) (h2.weakN henv W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN henv W) (ih1 W) (h3.weakN henv W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)

variable! (h₀ : Γ₀ ⊢ e₀ : A₀) in
theorem NormalEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e1 ≡ₚ e2) :
    Γ ⊢ e1.inst e₀ k ≡ₚ e2.inst e₀ k := by
  induction H generalizing Γ k with
  | refl h => exact .refl (h.instN henv W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀) (h4.instN henv W h₀) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (h1.instN henv h₀ W) (h2.instN henv h₀ W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.instN henv h₀ W) (ih1 W) (h3.instN henv W.succ h₀) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaR h1 _ ih =>
    refine .etaR (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀)

variable! (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : Γ₀ ⊢ e₀ ≡ₚ e₀') in
theorem NormalEq.instN_r (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e : A) :
    Γ ⊢ e.inst e₀ k ≡ₚ e.inst e₀' k := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := H.bvar_inv henv hΓ₁; clear H hΓ₁
    induction W generalizing i ty with
    | zero =>
      cases h with simp
      | zero => exact H'
      | succ h => exact .refl (.bvar h)
    | succ _ ih =>
      cases h with simp
      | zero => exact .refl (.bvar .zero)
      | succ h => exact (ih _ _ h).weakN .one
  | sort => exact .refl (.sort (H.sort_inv henv))
  | const =>
    let ⟨_, h1, h2, h3⟩ := H.const_inv henv hΓ₁
    exact .refl (.const h1 h2 h3)
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := H.app_inv henv hΓ₁
    specialize ih1 hΓ₁ W h1; have hf := h1.instN henv W h₀
    specialize ih2 hΓ₁ W h2; have ha := h2.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .appDF hf (.defeqU_l henv hΓ (ih1.defeq hΓ) hf) ha
      (.defeqU_l henv hΓ (ih2.defeq hΓ) ha) ih1 ih2
  | lam A body ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ₁
    have hA := h1.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .lamDF hA (((ih1 hΓ₁ W h1).defeq hΓ).of_l henv hΓ hA)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    have hA := h1.instN henv W h₀
    exact .forallEDF hA (ih1 hΓ₁ W h1) (h2.instN henv W.succ h₀)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)

variable! (H₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEq.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2) : Γ₂ ⊢ e1 ≡ₚ e2 := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (.defeqDFC henv W h1) (.defeqDFC henv W h2)
      (.defeqDFC henv W h3) (.defeqDFC henv W h4) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (.defeqDFC henv W h1) (.defeqDFC henv W h2) (ih1 (W.succ h1.hasType.1))
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (.defeqDFC henv W h1) (ih1 W)
      (.defeqDFC henv (W.succ h1.hasType.1) h3) (ih2 (W.succ h1.hasType.1))
  | etaL h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaL (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaR h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaR (.defeqDFC henv W h1) (ih (W.succ h2))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (.defeqDFC henv W h1)
      (.defeqDFC henv W h2) (.defeqDFC henv W h3)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.defeq_l (W : Γ ⊢ A ≡ A' : sort u) (H : A::Γ ⊢ e1 ≡ₚ e2) :
    A'::Γ ⊢ e1 ≡ₚ e2 := defeqDFC hΓ (.succ .zero W) H

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEq.weakN_inv_DFC (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1.liftN n k ≡ₚ e2.liftN n k) : Γ ⊢ e1 ≡ₚ e2 := by
  generalize eq1 : e1.liftN n k = e1' at H
  generalize eq2 : e2.liftN n k = e2' at H
  induction H generalizing Γ Γ₂ e1 e2 k with
  | refl h =>
    cases eq2; cases liftN_inj.1 eq1
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h'⟩ := (IsDefEqU.weakN_iff henv hΓ₂ W).1 ⟨_, h.defeqDFC henv W₂⟩
    exact .refl h'
  | sortDF h1 h2 h3 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h1 := h1.defeqDFC henv W₂
    replace h2 := h2.defeqDFC henv W₂
    replace h3 := h3.defeqDFC henv W₂
    replace h4 := h4.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have hΓ := hΓ₂.weakN_inv henv W
    have ⟨_, _, l1, l2⟩ :=
      let ⟨_, h⟩ := (VExpr.WF.weakN_iff henv hΓ₂ W (e := .app ..)).1 ⟨_, h1.app h3⟩
      HasType.app_inv henv hΓ h
    have ⟨_, _, r1, r2⟩ :=
      let ⟨_, h⟩ := (VExpr.WF.weakN_iff henv hΓ₂ W (e := .app ..)).1 ⟨_, h2.app h4⟩
      HasType.app_inv henv hΓ h
    have := (IsDefEqU.weakN_iff henv hΓ₂ W).1
      (.trans henv hΓ₂ ((l1.weakN henv W).uniqU henv hΓ₂ h1) (h2.uniqU henv hΓ₂ (r1.weakN henv W)))
    have ⟨⟨_, h5⟩, _⟩ := this.forallE_inv henv hΓ
    exact .appDF (l1.defeqU_r henv hΓ this) r1
      (l2.defeqU_r henv hΓ ⟨_, h5⟩) r2 (ih1 W W₂ rfl rfl) (ih2 W W₂ rfl rfl)
  | lamDF h1 h2 _ ih1 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    -- have hΓ := hΓ₂.weakN_inv henv W
    have := (IsDefEq.weakN_iff (A := .sort ..) henv hΓ₂ W).1 <|
      .defeqDFC henv W₂ (h2.symm.trans h1)
    exact .lamDF this this.hasType.1 (ih1 W.succ (W₂.succ h2) rfl rfl)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have hΓ₂' := ((W₂.succ h1).symm henv).isType' hΓ₀
    have h3' := h3.defeqDFC henv (W₂.succ h1)
    replace h4 := (IsDefEq.weakN_iff (A := .sort ..) henv hΓ₂' W.succ).1 h3'
    have := (HasType.weakN_iff (A := .sort ..) henv hΓ₂'.1 W).1 <|
      .defeqDFC henv W₂ h1.hasType.2
    exact .forallEDF this (ih1 W W₂ rfl rfl) h4 (ih2 W.succ (W₂.succ h1) rfl rfl)
  | etaL h1 _ ih =>
    cases e1 <;> cases eq1
    subst eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have hB' := hB.defeqDFC henv (W₂.succ hA)
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := (IsDefEqU.weakN_iff henv hΓ₂' W.succ).1 ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := (IsDefEq.weakN_iff (A := .forallE ..) henv hΓ₂'.1 W).1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaL this (ih W.succ (W₂.succ hA) rfl (by simp [liftN, lift_liftN']))
  | etaR h1 _ ih =>
    subst eq1
    cases e2 <;> cases eq2
    have hΓ₁ := W₂.isType' hΓ₀
    have ⟨⟨_, hA⟩, _, hB⟩ := let ⟨_, h⟩ := h1.isType henv hΓ₁; h.forallE_inv henv
    have h1' := h1.defeqDFC henv W₂
    have hA' := hA.defeqDFC henv W₂
    have hB' := hB.defeqDFC henv (W₂.succ hA)
    have := (h1'.weakN henv .one).app (.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have hΓ₂' := ((W₂.succ hA).symm henv).isType' hΓ₀
    have ⟨C, hC⟩ := (IsDefEqU.weakN_iff henv hΓ₂' W.succ).1 ⟨_, this⟩
    have ⟨_, hu⟩ := this.uniq henv hΓ₂' (hC.weakN henv W.succ)
    have := (IsDefEq.weakN_iff (A := .forallE ..) henv hΓ₂'.1 W).1 <|
      IsDefEq.defeq (.forallEDF hA' hu) h1'
    refine .etaR this (ih W.succ (W₂.succ hA) (by simp [liftN, lift_liftN']) rfl)
  | proofIrrel h1 h2 h3 =>
    subst eq1; subst eq2
    have h1' := h1.defeqDFC henv W₂
    have h2' := h2.defeqDFC henv W₂
    have h3' := h3.defeqDFC henv W₂
    have hΓ₂ := (W₂.symm henv).isType' hΓ₀
    have ⟨_, h⟩ := (IsDefEqU.weakN_iff henv hΓ₂ W).1 ⟨_, h2'⟩
    have ⟨_, hw⟩ := h2'.uniq henv hΓ₂ (h.weakN henv W)
    exact .proofIrrel
      ((HasType.weakN_iff henv hΓ₂ (A := .sort ..) W).1 (h1'.defeqU_l henv hΓ₂ ⟨_, hw⟩))
      ((HasType.weakN_iff henv hΓ₂ W).1 (hw.defeq h2'))
      ((HasType.weakN_iff henv hΓ₂ W).1 (hw.defeq h3'))

variable! (hΓ' : OnCtx Γ' (IsType env univs)) in
theorem NormalEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k ↔ Γ ⊢ e1 ≡ₚ e2 :=
  ⟨fun H => H.weakN_inv_DFC hΓ' W .zero, fun H => H.weakN W⟩

private def meas : VExpr → Nat
  | .app f a
  | .forallE f a => meas f + meas a + 1
  | .bvar _ | .const .. | .sort _ => 0
  | .lam A e => meas A + meas e + 3

omit [Params] in private theorem meas_liftN : meas (e.liftN n k) = meas e := by
  induction e generalizing k <;> simp [*, meas, liftN]
omit [Params] in private theorem meas_lift : meas e.lift = meas e := meas_liftN

attribute [local simp] meas meas_lift in
theorem NormalEq.trans (hΓ : OnCtx Γ (IsType env univs)) :
    Γ ⊢ e1 ≡ₚ e2 → Γ ⊢ e2 ≡ₚ e3 → Γ ⊢ e1 ≡ₚ e3
  | .sortDF l1 _ l3, .sortDF r1 r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4) (l5.trans hΓ r5) (l6.trans hΓ r6)
  | .lamDF l1 l2 l3, .lamDF r1 r2 r3 =>
    have aa := r1.trans_r henv hΓ l2.symm
    .lamDF l1 (aa.symm.trans_l henv hΓ r2) (l3.trans ⟨hΓ, _, l1.hasType.1⟩ (r3.defeq_l hΓ aa))
  | .forallEDF l1 l2 l3 l4, .forallEDF r1 r2 r3 r4 =>
    have r4' := r4.defeq_l hΓ (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
    .forallEDF l1 (l2.trans hΓ r2) l3 (l4.trans ⟨hΓ, _, l1.hasType.1⟩ r4')
  | .etaR l1 ih, .lamDF r1 r2 r3 =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have eq := r1.symm.trans r2
    .etaR (IsDefEq.defeq (.forallEDF eq hB) l1) <|
      (ih.defeq_l hΓ eq).trans ⟨hΓ, _, r2.hasType.2⟩ (r3.defeq_l hΓ r2)
  | .lamDF l1 l2 l3, .etaL r1 ih =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have eq := l2.symm.trans l1
    .etaL (IsDefEq.defeq (.forallEDF eq hB) r1) <|
      (l3.defeq_l hΓ l1).trans ⟨hΓ, _, l1.hasType.2⟩ (ih.defeq_l hΓ eq)
  | H1@(.etaR l1 ihl), .etaL r1 ihr => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have := ihl.trans (by exact ⟨hΓ, _, hA⟩) ihr
    generalize eq : e1.lift = e1' at this
    cases this with first | cases eq | cases liftN_inj.1 eq
    | refl h => exact .refl r1
    | proofIrrel h1 h2 h3 =>
      refine .proofIrrel (IsDefEqU.defeqDF henv hΓ ?_ (HasType.forallE hA h1))
        (.defeqU_l henv hΓ ⟨_, .eta l1⟩ (.lam hA h2))
        (.defeqU_l henv hΓ ⟨_, .eta r1⟩ (.lam hA h3))
      have hw := let ⟨_, h⟩ := hA.isType henv hΓ; h.sort_inv henv
      exact ⟨_, .sortDF ⟨hw, ⟨⟩⟩ ⟨⟩ rfl⟩
    | appDF _ _ _ _ ih => exact (NormalEq.weakN_iff (by exact ⟨hΓ, _, hA⟩) .one).1 ih
  | .refl h, H2 => H2
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)
  | .etaL l1 ih, H2 => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    refine .etaL (.defeqU_l henv hΓ (H2.defeq hΓ) l1) (ih.trans ⟨hΓ, _, hA⟩ ?_)
    exact .appDF (l1.weakN henv .one)
      ((l1.defeqU_l henv hΓ (H2.defeq hΓ)).weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H2) (.refl (.bvar .zero))
  | H1, .refl _ => H1
  | H1, .etaR r1 ih => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    refine .etaR (.defeqU_l henv hΓ (H1.defeq hΓ).symm r1) (.trans ⟨hΓ, _, hA⟩ ?_ ih)
    refine .appDF ((r1.defeqU_l henv hΓ (H1.defeq hΓ).symm).weakN henv .one)
      (r1.weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H1) (.refl (.bvar .zero))
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3
termination_by meas e1 + meas e2 + meas e3

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ₚ m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) :
    Γ ⊢ apply m1 m2 r ≡ₚ apply m1 m2' r := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact .refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact ih path _ he

omit [Params] in
theorem _root_.Lean4Lean.VLevel.forall₂_inst_congr {ls ls' : List VLevel}
    (hll : List.Forall₂ (· ≈ ·) ls ls') (us : List VLevel) :
    List.Forall₂ (· ≈ ·) (us.map (VLevel.inst ls)) (us.map (VLevel.inst ls')) := by
  induction us with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (VLevel.inst_congr rfl hll) ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.instL_congr {e : VExpr} {ls ls' : List VLevel} (hls : ∀ l ∈ ls, l.WF univs)
    (hls' : ∀ l ∈ ls', l.WF univs) (hll : List.Forall₂ (· ≈ ·) ls ls')
    (H : Γ ⊢ e.instL ls : A) : Γ ⊢ e.instL ls ≡ₚ e.instL ls' := by
  induction e generalizing Γ A with dsimp [VExpr.instL] at H ⊢
  | bvar i => exact .refl H
  | sort u => exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls') (VLevel.inst_congr rfl hll)
  | const c us =>
    have ⟨ci, h1, h2, h3⟩ := H.const_inv henv hΓ
    refine .constDF h1 h2 (fun l hl => ?_) h3 (VLevel.forall₂_inst_congr hll us)
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls'
  | app f a ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    exact .appDF hf (.defeqU_l henv hΓ ((ih1 hΓ hf).defeq hΓ) hf)
      ha (.defeqU_l henv hΓ ((ih2 hΓ ha).defeq hΓ) ha) (ih1 hΓ hf) (ih2 hΓ ha)
  | lam A body ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ
    exact .lamDF h1 (((ih1 hΓ h1).defeq hΓ).of_l henv hΓ h1)
      (ih2 (by exact ⟨hΓ, _, h1⟩) h2)
  | forallE A B ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    exact .forallEDF h1 (ih1 hΓ h1) h2 (ih2 (by exact ⟨hΓ, _, h1⟩) h2)

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.apply_instL {p : Pattern} {r : p.RHS}
    {m1 m1' : p.LPath → List VLevel} {m2 : p.Path → VExpr}
    (hls : ∀ lp, ∀ l ∈ m1 lp, l.WF univs) (hls' : ∀ lp, ∀ l ∈ m1' lp, l.WF univs)
    (hll : ∀ lp, List.Forall₂ (· ≈ ·) (m1 lp) (m1' lp)) (he : Γ ⊢ apply m1 m2 r : A) :
    Γ ⊢ apply m1 m2 r ≡ₚ apply m1' m2 r := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c lp => exact .instL_congr hΓ (hls lp) (hls' lp) (hll lp) he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact .refl he

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⋙ " e2:36 => CParRed Γ e1 e2

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- **E6**: a rule's `Check` obligations survive replacing the matched arguments by
`NormalEq`-related ones.

Needed by every route through `parRed`'s `appDF` × `extra` case: the rule fires on the
left-hand term with *its* matched arguments, so `r3`'s obligations — stated at the right-hand
term's arguments — have to be transported.  The leafwise hypothesis is the same one
`NormalEq.apply_pat` takes, and this is proved by composing two of those with the clause's
own `IsDefEqU`. -/
theorem _root_.Lean4Lean.Pattern.Check.OK.congr_normalEq {p : Pattern} (ck : p.Check)
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (hne : ∀ x A, Γ ⊢ m2 x : A → Γ ⊢ m2 x ≡ₚ m2' x)
    (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 m2' := by
  refine H.map fun a b h => ?_
  obtain ⟨T, hT⟩ := h
  have ha := NormalEq.apply_pat hΓ hne hT.hasType.1
  have hb := NormalEq.apply_pat hΓ hne hT.hasType.2
  exact ((ha.defeq hΓ).symm.trans henv hΓ ⟨_, hT⟩).trans henv hΓ (hb.defeq hΓ)

def NonNeutral (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  (∃ p r m1 m2, Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : ¬NonNeutral Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | app : ¬NonNeutral Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ⋙ m2' a) → Γ ⊢ e ⋙ r.1.apply m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl

/-- `Δ.length` nested `lam` congruences. This is what turns a λ-peeled `extra_pat` back
into a reduction of the rule's stored (λ-wrapped) left-hand side. -/
theorem ParRed.lams {Δ : List VExpr} {L R : VExpr} :
    ∀ {Γ}, ParRed (Δ.reverse ++ Γ) L R → ParRed Γ (VExpr.mkLams Δ L) (VExpr.mkLams Δ R) := by
  induction Δ with
  | nil => exact fun H => H
  | cons A Δ ih => intro Γ H; exact .lam ParRed.rfl (ih (by simpa using H))

theorem ParRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≫ e2) :
    Γ' ⊢ e1.liftN n k ≫ e2.liftN n k := by
  induction H generalizing k Γ' with
  | bvar | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    refine .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)

variable! (H₀ : Γ₀ ⊢ a1 ≫ a2) (H₀' : Γ₀ ⊢ a1 : A₀) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≫ e2) : Γ ⊢ e1.inst a1 k ≫ e2.inst a2 k := by
  induction H generalizing Γ k with
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact ih.weakN .one
  | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀') (fun a => ih _ W)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.defeq (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H generalizing A with
  | bvar | sort | const => exact he
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he <| .appDF (ih1 hΓ h1) (ih2 hΓ h2)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact .trans_l henv hΓ he <| .lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he <| .forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have hf' := hA.lam hb
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hf')
    replace ha := ha.defeqU_r henv hΓ ⟨_, u1⟩
    exact .trans_l henv hΓ he <| .trans
      (.symm <| .appDF (.symm <| .lamDF hA (ih1 ⟨hΓ, _, hA⟩ hb)) (.symm <| ih2 hΓ ha))
      (.beta (ih1 ⟨hΓ, _, hA⟩ hb).hasType.2 (ih2 hΓ ha).hasType.2)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .trans_l henv hΓ he <| .transU_r henv hΓ (pat_wf h1 h2 hΓ he h3) <|
     .apply_pat hΓ (fun _ _ h => ⟨_, ih _ hΓ h⟩) (.defeqU_l henv hΓ (pat_wf h1 h2 hΓ he h3) he)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.hasType (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e' : A :=
  (H.defeq hΓ he).hasType.2

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫ e2) : Γ₂ ⊢ e1 ≫ e2 := by
  induction H generalizing Γ₂ A with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv (W.isType' hΓ₀)
    exact .lam (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (W.succ hA) hB)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv (W.isType' hΓ₀)
    exact .beta (ih1 (W.succ hA) hb) (ih2 W ha)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => h.defeqDFC henv W) fun a =>
      let ⟨_, h⟩ := h2.hasType (W.isType' hΓ₀) h a; ih a W h

theorem ParRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, Γ ⊢ m2 a ≫ m3 a) : Γ ⊢ r.apply m1 m2 ≫ r.apply m1 m3 := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_lift' {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).lift' ρ = r.apply m1 (fun a => (m2 a).lift' ρ) := by
  induction r with simp! [*]
  | fixed _ _ h => exact instL_lift'.symm.trans ((h.lift'_eq trivial).symm ▸ rfl)

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_liftN {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).liftN k n = r.apply m1 (fun a => (m2 a).liftN k n) := by
  simp [← lift'_consN_skipN, Pattern.RHS.apply_lift']

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem HasType.matches_inv {p : Pattern} {m1 m2} (H : Γ ⊢ e : A)
    (H2 : p.Matches e m1 m2) : ∀ a, ∃ A, Γ ⊢ m2 a : A := by
  induction H2 generalizing A with
  | const => nofun
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (h|h) <;> [exact ih1 hf h; exact ih2 ha h]
  | var _ ih1 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (_|h) <;> [exact ⟨_, ha⟩; exact ih1 hf h]

-- theorem IsDefEqU.applyL {p : Pattern} (r : p.RHS) {m1 m1' m2}
--     (H : ∀ a, List.Forall₂ (· ≈ ·) (m1 a) (m1' a))
--     (H2 : TY.HasType Γ (r.apply m1 m2) A) :
--     TY.IsDefEqU Γ (r.apply m1 m2) (r.apply m1' m2) := by
--   match r with
--   | .fixed .. =>
--     dsimp [Pattern.RHS.apply]
--     exact TY.hasType_instL _ _
--   | .app f a => exact .app (apply_pat f H) (apply_pat a H)
--   | .var f => exact H _

variable! (hΓ : OnCtx Γ' (IsType env univs)) in
theorem ParRed.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (h : Γ' ⊢ e1.liftN n k : A) (H : Γ' ⊢ e1.liftN n k ≫ e2') :
    ∃ e2, Γ ⊢ e1 ≫ e2 ∧ e2' = e2.liftN n k := by
  generalize eq : e1.liftN n k = e1' at H
  induction H generalizing e1 Γ k A with
  | bvar => cases e1 <;> cases eq; exact ⟨_, .bvar, rfl⟩
  | sort => cases e1 <;> cases eq; exact ⟨_, .sort, rfl⟩
  | const => cases e1 <;> cases eq; exact ⟨_, .const, rfl⟩
  | app h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hf rfl
    obtain ⟨_, b1, rfl⟩ := ih2 hΓ W ha rfl
    exact ⟨_, .app a1 b1, rfl⟩
  | lam h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hA rfl
    obtain ⟨_, b1, rfl⟩ := ih2 (by exact ⟨hΓ, _, hA⟩) W.succ he rfl
    exact ⟨_, .lam a1 b1, rfl⟩
  | forallE h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    obtain ⟨_, a1, rfl⟩ := ih1 hΓ W hA rfl
    obtain ⟨_, b1, rfl⟩ := ih2 (by exact ⟨hΓ, _, hA⟩) W.succ hB rfl
    exact ⟨_, .forallE a1 b1, rfl⟩
  | beta h1 h2 ih1 ih2 =>
    cases e1 <;> injection eq
    rename_i f a eq eq2; cases eq2
    cases f <;> cases eq
    have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨_, a1, rfl⟩ := ih1 (by exact ⟨hΓ, _, hA⟩) W.succ hb rfl
    obtain ⟨_, b1, rfl⟩ := ih2 hΓ W ha rfl
    exact ⟨_, .beta a1 b1, (liftN_inst_hi ..).symm⟩
  | @extra p r e m1 m2 Γ' m2' h1 h2 h3 h4 ih =>
    suffices ∃ m3 m3' : _ → _, p.Matches e1 m1 m3 ∧
        (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧
        (∀ a, m2 a = (m3 a).liftN n k) ∧
        (∀ a, m2' a = (m3' a).liftN n k) by
      let ⟨m3, m3', a1, a2, a3, a4⟩ := this
      refine ⟨_, .extra h1 a1 (h3.map fun _ _ h => ?_) a2,
        .trans (by congr; funext; apply a4) r.1.apply_liftN.symm⟩
      rw [(funext a3 : m2 = _), ← Pattern.RHS.apply_liftN, ← Pattern.RHS.apply_liftN] at h
      exact (IsDefEqU.weakN_iff henv hΓ W).1 h
    clear h1 h3 r
    induction h2 generalizing e1 A with
    | const => cases e1 <;> cases eq; exact ⟨_, nofun, .const, nofun, nofun, nofun⟩
    | var h1 ih1 =>
      cases e1 <;> cases eq
      have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| some ·) (ih <| some ·) hf rfl
      have ⟨_, b2, b4⟩ := ih none hΓ W ha rfl
      exact ⟨_, Option.rec _ _, .var a1, Option.rec b2 a2, Option.rec rfl a3, Option.rec b4 a4⟩
    | app h1 h2 ih1 ih2 =>
      cases e1 <;> cases eq
      have ⟨_, _, hf, ha⟩ := h.app_inv henv hΓ
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| .inl ·) (ih <| .inl ·) hf rfl
      have ⟨_, _, b1, b2, b3, b4⟩ := ih2 (h4 <| .inr ·) (ih <| .inr ·) ha rfl
      exact ⟨_, Sum.rec _ _, .app a1 b1, Sum.rec a2 b2, Sum.rec a3 b3, Sum.rec a4 b4⟩

theorem CParRed.toParRed (H : Γ ⊢ e ⋙ e') : Γ ⊢ e ≫ e' := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih3 => exact .extra h1 h2 h3 ih3

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CParRed.exists (H : Γ ⊢ e : A) : ∃ e', Γ ⊢ e ⋙ e' := by
  induction e using VExpr.brecOn generalizing Γ A with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  have neut {e} (H' : Γ ⊢ e : A) (e_ih : e.below (motive := motive)) :
      NonNeutral Γ e → ∃ e', Γ ⊢ e ⋙ e' := by
    rintro (⟨A, e, a, rfl⟩ | ⟨p, r, m1, m2, h1, hp2, hp3⟩)
    · have ⟨_, _, hf, ha⟩ := H'.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, he⟩ := hf.lam_inv henv hΓ
      have ⟨_, he⟩ := e_ih.1.2.2.1 (by exact ⟨hΓ, _, hA⟩) he
      have ⟨_, ha⟩ := e_ih.2.1 hΓ ha
      exact ⟨_, .beta he ha⟩
    · suffices ∃ m3 : p.Path → VExpr, ∀ a, Γ ⊢ m2 a ⋙ m3 a from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H r h1 hp3
      induction p generalizing e A with
      | const => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih1 H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 hΓ H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const n ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .const hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hf
    have ⟨_, h2⟩ := e_ih.2.1 hΓ ha
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .app hn h1 h2⟩
  | lam ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := H.lam_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := H.forallE_inv henv
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) hB
    exact ⟨_, .forallE h1 h2⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.triangle (H1 : Γ ⊢ e : A) (H : Γ ⊢ e ≫ e') (H2 : Γ ⊢ e ⋙ o) :
    ∃ o', Γ ⊢ e' ≫ o' ∧ Γ ⊢ o' ≡ₚ o := by
  induction e using VExpr.brecOn generalizing Γ A e' o with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  induction H2 generalizing A e' with
  | bvar =>
    cases H with
    | bvar => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | sort =>
    cases H with
    | sort => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | const hn =>
    cases H with
    | const => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := H1.app_inv henv hΓ
    cases H with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 hΓ l2 r2 e_ih.2.2
      have o1 := p1.hasType hΓ (r1.hasType hΓ l1); have o2 := p2.hasType hΓ (r2.hasType hΓ l2)
      exact ⟨_, .app p1 p2, .appDF o1 (.defeqU_l henv hΓ (n1.defeq hΓ) o1)
        o2 (.defeqU_l henv hΓ (n2.defeq hΓ) o2) n1 n2⟩
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
    | beta => cases hn (.inl ⟨_, _, _, rfl⟩)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.lam_inv henv hΓ
    cases H with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      have := (r1.defeq hΓ l1).trans (p1.defeq hΓ (r1.hasType hΓ l1)) |>.symm
      refine ⟨_, .lam p1 ?_, .lamDF this.symm (this.symm.transU_l henv hΓ (n1.defeq hΓ)) n2⟩
      exact p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType (by exact ⟨hΓ, _, l1⟩) l2)
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.forallE_inv henv
    cases H with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      exact ⟨_, .forallE p1 (p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType hΓ' l2)),
        .forallEDF (.trans (r1.defeq hΓ l1) (p1.defeq hΓ (r1.hasType hΓ l1)))
          n1 (p2.hasType hΓ' (r2.hasType hΓ' l2)) n2⟩
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := H1.app_inv henv hΓ
    have ⟨⟨_, lA⟩, _, le⟩ := lf.lam_inv henv hΓ
    have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lA le)).forallE_inv henv hΓ
    have la' := hw.defeq la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
      ⟨ha, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    cases H with
    | app rf ra =>
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      cases rf with
      | lam rA re =>
        refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
        refine ⟨_, .beta (p2.defeqDFC hΓ (.succ .zero (rA.defeq hΓ lA)) (re.hasType hΓ' le)) p3, ?_⟩
        refine .trans hΓ
          (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
            (p2.hasType hΓ' (re.hasType hΓ' le)))
          (.instN (l2.toParRed.hasType hΓ la') .zero n2)
      | extra h1 h2 => cases h2
    | beta re ra =>
      refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      refine ⟨_, .instN p3 (ra.hasType hΓ la') .zero p2, ?_⟩
      refine .trans hΓ
        (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
          (p2.hasType hΓ' (re.hasType hΓ' le)))
        (.instN (l2.toParRed.hasType hΓ la') .zero n2)
    | extra h1 h2 => cases h2 with | app h | var h => cases h
  | @extra p r e m1 m2 Γ m2' l1 l2 l3 l4 ih =>
    have :
      (∃ m3 m3' : p.Path → VExpr, p.Matches e' m1 m3 ∧
        (∀ a, Γ ⊢ m2 a ≫ m3 a) ∧ (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ m2' a)) ∨
      (∃ p₁ e₁' e₁ m1₁ m2₁, Subpattern p₁ p ∧ (p₁ = p → e₁ = e ∧ e₁' = e' ∧ m1₁ ≍ m1 ∧ m2₁ ≍ m2) ∧
        p₁.Matches e₁ m1₁ m2₁ ∧ ∃ p' r m1 m2 m2',
        Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ (∀ a, Γ ⊢ m2 a ≫ m2' a) ∧ e₁' = r.1.apply m1 m2') := by
      clear l1 l3 l4 r
      induction H generalizing p m1 A with
      | const =>
        cases id l2; exact .inl ⟨_, _, l2, nofun, fun _ => .rfl, nofun⟩
      | @app Γ f f' a a' hf ha ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        cases l2 with
        | var lf =>
          match ih1 lf (ih <| some ·) hΓ Hf e_ih.1.2 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.varL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.varL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            have ⟨_, a3, a4⟩ := ih none hΓ Ha ha e_ih.2.2
            exact .inl ⟨_, (·.elim _ _), .var f1,
              (·.casesOn ha f2), (·.casesOn a3 f3), (·.casesOn a4 f4)⟩
        | app lf la =>
          match ih1 lf (ih <| .inl ·) hΓ Hf e_ih.1.2 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.appL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.appL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            match ih2 la (ih <| .inr ·) hΓ Ha e_ih.2.2 with
            | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
              refine .inr ⟨_, _, _, _, _, h1.appR, ?_, h3⟩
              rintro rfl; cases h1.antisymm (.appR .refl)
            | .inl ⟨_, _, a1, a2, a3, a4⟩ =>
              exact .inl ⟨_, Sum.elim _ _, .app f1 a1,
                (·.casesOn f2 a2), (·.casesOn f3 a3), (·.casesOn f4 a4)⟩
      | beta _ _ => cases l2 with | var h | app h => cases h
      | @extra _ _ _ _ _ _ _ r1 r2 _ r4 =>
        exact .inr ⟨_, _, _, _, _, .refl, fun _ => ⟨rfl, rfl, .rfl, .rfl⟩,
          l2, _, _, _, _, _, r1, r2, r4, rfl⟩
      | _ => cases l2
    match this with
    | .inl ⟨m3, m3', h1, h2, h3, h4⟩ =>
      refine
        have h := .extra l1 h1 (l3.map fun _ _ ⟨_, h1⟩ => ?_) h3
        ⟨_, h, .apply_pat hΓ (fun a _ _ => h4 a) (h.hasType hΓ (H.hasType hΓ H1))⟩
      refine ⟨_, .trans
        (.symm <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.1)
        (.trans h1 <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.2)⟩
    | .inr ⟨_, _, _, _, _, h1, h2, l2', _, _, _, _, m3, r1, r2, r4, e⟩ =>
      obtain ⟨_, -, -, hr, -⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2'⟩⟩
      obtain ⟨rfl, rfl, ⟨⟩⟩ := pat_uniq l1 r1 h1 hr
      obtain ⟨rfl, rfl, ⟨⟩, ⟨⟩⟩ := h2 rfl; subst e
      obtain ⟨rfl, rfl⟩ := l2'.uniq r2
      suffices ∃ m3' : p.Path → VExpr, (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ m2' a) by
        let ⟨m3', h3, h4⟩ := this
        refine ⟨_, ?h3, .apply_pat hΓ (fun a _ _ => h4 a) ((?h3).hasType hΓ (H.hasType hΓ H1))⟩
        exact .apply_pat _ h3
      clear H r l1 l2 l3 l4 this h1 h2 r1 r2 hr
      induction l2' generalizing A with
      | const => exact ⟨nofun, nofun, nofun⟩
      | app _ _ ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| .inl ·) _ Hf e_ih1 (r4 <| .inl ·)
        have ⟨g2, r1, r2⟩ := ih2 (ih <| .inr ·) _ Ha e_ih2 (r4 <| .inr ·)
        exact ⟨Sum.elim g1 g2, (·.casesOn l1 r1), (·.casesOn l2 r2)⟩
      | var _ ih1 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| some ·) _ Hf e_ih1 (r4 <| some ·)
        have ⟨g2, r1, r2⟩ := ih none hΓ Ha (r4 none) e_ih2
        exact ⟨(·.elim g2 g1), (·.casesOn r1 l1), (·.casesOn r2 l2)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.church_rosser (H : Γ ⊢ e : A)
    (H1 : Γ ⊢ e ≫ e₁) (H2 : Γ ⊢ e ≫ e₂) :
      ∃ e₁' e₂', Γ ⊢ e₁ ≫ e₁' ∧ Γ ⊢ e₂ ≫ e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  let ⟨e', h'⟩ := CParRed.exists hΓ H
  let ⟨_, l1, l2⟩ := H1.triangle hΓ H h'
  let ⟨_, r1, r2⟩ := H2.triangle hΓ H h'
  exact ⟨_, _, l1, r1, l2.trans hΓ (r2.symm hΓ)⟩

def ParRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed Γ)
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.hasType (H : Γ ⊢ e ≫* e') : Γ ⊢ e : A → Γ ⊢ e' : A := by
  induction H with
  | rfl => exact id
  | tail h1 h2 ih => exact h2.hasType hΓ ∘ ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.defeq (H : Γ ⊢ e ≫* e') (h : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H with
  | rfl => exact h
  | tail h1 h2 ih => exact ih.trans (h2.defeq hΓ (hasType hΓ h1 h))

variable! (hΓ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRedS.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫* e2) : Γ₂ ⊢ e1 ≫* e2 := by
  induction H with
  | rfl => exact .rfl
  | tail h1 h2 ih => refine .tail ih (h2.defeqDFC hΓ W (hasType (W.isType' hΓ) h1 h))

theorem ParRedS.app (hf : Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') :
    Γ ⊢ f.app a ≫* f'.app a' := by
  have : Γ ⊢ f.app a ≫* f.app a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.app .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.app f2 .rfl)

theorem ParRedS.lam (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.lam body ≫* A'.lam body' := by
  have : Γ ⊢ A.lam body ≫* A.lam body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.lam .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.lam f2 .rfl)

theorem ParRedS.forallE (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.forallE body ≫* A'.forallE body' := by
  have : Γ ⊢ A.forallE body ≫* A.forallE body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.forallE .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.forallE f2 .rfl)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.inst (Ha : Γ ⊢ a : A)
    (hf : A :: Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') : Γ ⊢ f.inst a ≫* f'.inst a' := by
  have : Γ ⊢ f.inst a ≫* f.inst a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.instN a2 (ParRedS.hasType hΓ a1 Ha) .zero .rfl)
  replace Ha := ha.hasType hΓ Ha
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail _ h ihf => exact .tail ihf (.instN .rfl Ha .zero h)

theorem ParRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e ≫* e') :
    Γ' ⊢ e.liftN n k ≫* e'.liftN n k := by
  induction H with
  | rfl =>  exact .rfl
  | tail _ h ih => exact .tail ih (.weakN W h)

inductive ParRedExt : Type where
  | base : ParRedExt
  | lift : ParRedExt → ParRedExt
  | app : ParRedExt → ParRedExt

def ParRedExt.depth : ParRedExt → Nat
  | .base => 0
  | .lift l
  | .app l => l.depth + 1

def ParRedExt.apply : ParRedExt → VExpr → VExpr
  | .base, e => e
  | .lift l, e => (l.apply e).lift
  | .app l, e => (l.apply e).lift.app (.bvar 0)

def ParRedExt.meas : ParRedExt → Nat
  | .base => 0
  | .lift l => l.meas + 1
  | .app l => l.meas + 2

def IsApp := fun | VExpr.app .. => True | _ => False

omit [Params] in
theorem ParRedExt.isApp {l : ParRedExt} (H : l.apply (.app f a) = e') : IsApp e' := by
  induction l generalizing e' with simp [apply] at H
  | lift l ih =>
    specialize ih rfl; unfold IsApp at ih; split at ih <;> cases ih <;>
    · rename_i h1; cases h1 ▸ H; trivial
  | _ => subst H; trivial

variable! (hΓ : OnCtx (A::Γ) (IsType env univs)) in
theorem hasType_app_bvar0
    (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B' := by
  have ⟨_, _, c1, c2⟩ := H.app_inv henv hΓ
  replace c1 :=
    have ⟨_, d1⟩ := c1.isType henv hΓ
    have ⟨_, _, d3⟩ := d1.forallE_inv henv
    have ⟨_, d4⟩ := c2.uniq henv hΓ (.bvar .zero)
    HasType.defeqU_r henv hΓ ⟨_, d4.forallEDF d3⟩ c1
  have := c1.eta
  rw [show A.lift.lam (e.lift.lift.app (bvar 0)) = (A.lam (e.lift.app (bvar 0))).lift by
    simp [VExpr.liftN, liftN'_liftN_lo, liftN_liftN]] at this
  have ⟨_, f1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, this⟩
  have ⟨⟨_, f2⟩, _, f3⟩ := f1.hasType.1.lam_inv henv hΓ.1
  exact ⟨_, (HasType.lam f2 f3).defeqU_l henv hΓ.1 ⟨_, f1⟩⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedExt.parRed_beta :
    Γ ⊢ f ≡ₚ lam A e' → ∀ {a B}, Γ ⊢ f.app a : B → ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a := by
  refine (?_ : _ ∧ ∀ (l : ParRedExt), l.depth ≤ Γ.length →
    Γ ⊢ f ≡ₚ l.apply ((lam A e').lift.app (bvar 0)) → ∃ e, Γ ⊢ f ≫* e ∧ Γ ⊢ e ≡ₚ l.apply e').1
  induction f using VExpr.brecOn generalizing Γ A e' with | _ f f_ih => ?_
  revert f_ih; change let motive := ?_; ∀ _: f.below (motive := motive), _; intro motive f_ih
  refine ⟨fun h1 a B h2 => ?_, fun l W h1 => ?_⟩
  · cases h1 with
    | @refl _ _ B H =>
      clear f_ih motive
      exact have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, .refl (h.hasType hΓ h2)⟩
    | lamDF a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, H3⟩, _, H4⟩ := H1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((H3.lam H4).uniqU henv hΓ H1).forallE_inv henv hΓ
      exact ⟨_, .tail .rfl <| .beta .rfl .rfl,
        .instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) H2) .zero a3⟩
    | @etaL _ _ A' _ _ a1 a2 =>
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
      have ⟨⟨_, c1⟩, _, c2⟩ := a1.lam_inv henv hΓ
      have ⟨_, d1, d2⟩ := (f_ih.2.1 <| by exact ⟨hΓ, _, hA⟩).2 .base (Nat.zero_le _) a2
      have ⟨_, _, c3, c4⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, c1⟩, _, c2⟩ := c3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((c1.lam c2).uniqU henv hΓ c3).forallE_inv henv hΓ
      exact ⟨_, .tail (ParRedS.app (.lam .rfl d1) .rfl) <| .beta .rfl .rfl,
        .instN (.defeq u1.symm c4) .zero d2⟩
    | etaR a1 a2 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := (H1.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a2.instN (.defeq u1 H2) .zero
      simp [inst, inst_lift] at this
      exact ⟨_, .rfl, this⟩
    | proofIrrel a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have hf := a2.uniqU henv hΓ H1; have := a1.defeqU_l henv hΓ hf
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf |>.forallE_inv henv hΓ
      exact ⟨_, .rfl, .proofIrrel (b2.instN henv .zero H2) (H1.app H2)
        ((u2.defeq c2).instN henv .zero (u1.symm.defeq H2))⟩
  generalize eq : l.apply .. = s at h1
  cases h1 with
  | @refl _ _ B H =>
    subst eq; clear f_ih motive
    generalize ls : l.meas = n
    induction n using Nat.strongRecOn generalizing l Γ B with | _ _ ih; subst ls
    cases l with
    | base =>
      refine have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, ?_⟩
      simp [instN_bvar0] at h ⊢; exact .refl (h.hasType hΓ H)
    | lift l =>
      let A::Γ := Γ
      have ⟨_, a1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, H⟩
      have ⟨_, a2, a3⟩ := ih _ (by simp [meas]) hΓ.1 l (by simpa [depth] using W) a1 rfl
      exact ⟨_, .weakN .one a2, .weakN .one a3⟩
    | app l =>
      let A::Γ := Γ
      have ⟨_, _, H1, H2⟩ := H.app_inv henv hΓ
      have ⟨_, a1, a2⟩ := ih _ (by simp [meas]) hΓ (lift l) W H1 rfl
      have := a1.hasType hΓ H1
      exact ⟨_, .app a1 .rfl, .appDF this (this.defeqU_l henv hΓ (a2.defeq hΓ)) H2 H2 a2 (.refl H2)⟩
  | @appDF _ _ A' B' f' _ a' a1 a2 a3 a4 a5 a6 =>
    obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ : ∃ n, a' = bvar n ∧
        (f' = (A.lam e').liftN (n+1) ∧ l.apply e' = liftN n e' ∨
        ∃ l', l'.depth ≤ l.depth ∧
          f' = apply l' ((A.lam e').lift.app (bvar 0)) ∧
          l.apply e' = (l'.apply e').app (bvar n)) := by
      clear W a2 a4 a5 a6
      induction l generalizing f' a' with
      | base => cases eq; exact ⟨_, rfl, .inl ⟨rfl, by simp [apply]⟩⟩
      | lift l ih =>
        simp [apply] at eq
        generalize eq' : apply .. = s at eq; cases s <;> cases eq
        obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ := ih eq'
        · refine ⟨_, rfl, .inl ⟨by simp [liftN_liftN], ?_⟩⟩
          have := congrArg VExpr.lift h
          simpa [lift_inst_hi, liftN'_liftN']
        · exact ⟨_, rfl, .inr ⟨lift _, Nat.succ_le_succ W', rfl, congrArg VExpr.lift h⟩⟩
      | app l ih => cases eq; exact ⟨_, rfl, .inr ⟨lift _, Nat.le_refl _, rfl, rfl⟩⟩
    · have ⟨⟨_, c1⟩, _, c2⟩ := (a1.defeqU_l henv hΓ (a5.defeq hΓ)).lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := a1.defeqU_l henv hΓ (a5.defeq hΓ)
        |>.uniqU henv hΓ (c1.lam c2) |>.forallE_inv henv hΓ
      have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).1 a5 (.app a1 a3)
      replace b2 := b2.trans hΓ <|
        .instN_r (by exact ⟨hΓ, _, c1⟩) (.defeqU_r henv hΓ ⟨_, u1⟩ a3) a6 .zero c2
      have := congrArg (liftN n) (instN_bvar0 e' 0)
      simp [liftN_inst_hi, liftN'_liftN', liftN] at this
      rw [Nat.add_comm, this, ← h] at b2
      exact ⟨_, b1, b2⟩
    · have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).2 l' (Nat.le_trans W' W) a5
      rw [h]; have := b1.hasType hΓ a1
      exact ⟨_, .app b1 .rfl, .appDF this (.defeqU_l henv hΓ (b2.defeq hΓ) this) a3 a4 b2 a6⟩
  | @etaL _ _ A' _ _ a1 a2 =>
    subst eq
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA⟩
      have ⟨_, b1, b2⟩ := (f_ih.2.1 hΓ').2 (app l) (by exact Nat.succ_le_succ W) a2; ?_
    have ⟨_, c1⟩ := b2.defeq hΓ'
    let ⟨_, b3⟩ := hasType_app_bvar0 hΓ' c1.hasType.2
    exact ⟨_, .lam .rfl b1, .etaL b3 b2⟩
  | @proofIrrel _ p _ _ a1 a2 a3 =>
    subst eq; refine ⟨_, .rfl, .proofIrrel a1 a2 ?_⟩
    clear a2; induction l generalizing Γ p with
    | base =>
      have ⟨_, _, b1, b2⟩ := a3.app_inv henv hΓ
      have ⟨⟨_, b3⟩, _, b4⟩ := b1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((b3.lam b4).uniqU henv hΓ b1).forallE_inv henv hΓ
      have := b4.beta (u1.symm.defeq b2)
      simp [instN_bvar0] at this
      exact .defeqU_l henv hΓ ⟨_, this⟩ a3
    | lift l ih =>
      let A::Γ := Γ
      have ⟨_, b1⟩ := (IsDefEqU.weakN_iff henv hΓ .one).1 ⟨_, a3⟩
      have u1 := a3.uniqU henv hΓ (b1.weak henv)
      have := (HasType.weakN_iff henv hΓ (A := sort _) .one).1 (a1.defeqU_l henv hΓ u1)
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      exact .defeqU_r henv hΓ u1.symm (this.weak henv)
    | app l ih =>
      let A::Γ := Γ
      let ⟨_, b1⟩ := hasType_app_bvar0 hΓ a3
      have H := a3.uniqU henv hΓ (HasType.app (b1.weak henv) (.bvar .zero))
      simp [instN_bvar0] at H
      have ⟨⟨_, b2⟩, _, b3⟩ := have ⟨_, b2⟩ := b1.isType henv hΓ.1; b2.forallE_inv henv
      have wf := let ⟨_, h⟩ := b2.isType henv hΓ.1; h.sort_inv henv
      have := b2.forallE (.defeqU_l henv hΓ H a1)
      have := IsDefEq.defeq (.sortDF (by exact ⟨wf, ⟨⟩⟩) (by trivial) VLevel.imax_zero) this
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      have := HasType.app (this.weak henv) (.bvar .zero)
      simp [instN_bvar0] at this
      exact .defeqU_r henv hΓ H.symm this
  | _ => cases l.isApp eq

/-! ### The `proofIrrel` escape of `parRed`'s `appDF` × `extra` case (scoping item E3)

In that case the pattern's spine must be descended through `l5 : Γ ⊢ f ≡ₚ f₂`, and `Pat`
forbids a top-level `.var` while `Matches.var` consumes an application node rather than
matching anything -- so **no spine position is free** and every `NormalEq` constructor has to
be handled.  Two escape the descent: `etaL` (then `f` is a `.lam`, so `f.app a` is a β-redex)
and `proofIrrel`, which is what the three lemmas below resolve.  Here `f` need have no
structure at all: it is related to `f₂` only by both being proofs.  The resolution is not to
reduce -- it is that `f.app a` is then *itself* a proof of the same proposition as the rule's
output, so `≫*` is reflexive and `NormalEq.proofIrrel` closes it.

The content is `∀ A, B` being a `Prop` forcing `B` to be one, which needs universe
uniqueness for a term with two sort typings.

**Retraction.**  This section used to take that as an explicit hypothesis `hsu`, saying that
getting it from the tree "**would be circular**, since it is one of the facts confluence
exists to deliver", and that the independent route was
`Experimental/Reflect/Capstone.lean`'s `sort_uniq_of_hasType`.  Both halves were wrong.  The
`Capstone` route is closed (`Injectivity.lean:239`), and no independent route is needed:
`Params.sortUniq` above derives the fact from `Params.henv` through
`VEnv.WF.sortUniq'`, which is **already in this file's import closure and already in this
file's dependency cone** -- `ChurchRosser` imports `UniqueTyping` imports `Injectivity`, and
`IsDefEq.uniq`/`IsDefEqU.of_l`, used throughout this section, depend on `WF.sortUniq'`
transitively.  The dependency direction is `ChurchRosser → Injectivity`: confluence
*consumes* the Π/sort-inversion family and does not supply it, so nothing here can be
circular that was not already.  Removing `hsu` therefore costs nothing and widens no cone.
-/


/-- **The codomain of a Π-type that a *proof* inhabits is a `Prop`.**  The shared core of
`appDF_proof_escape` and `appDF_proofIrrel`: `P` and `∀ A, B` are both types of `f`, so the
Π-type is a `Prop` (universe uniqueness), and `imax u v ≈ 0` forces `v ≈ 0`. -/
theorem HasType.codomain_prop_of_isProof {Γ : List VExpr} {f A B P : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (hP : Γ ⊢ P : .sort .zero) (hf : Γ ⊢ f : P) :
    ∃ uA, (Γ ⊢ A : .sort uA) ∧ ((A::Γ) ⊢ B : .sort .zero) := by
  obtain ⟨u, hPBu⟩ := hf.uniq henv hΓ l1
  have hu0 : u ≈ .zero := Params.sortUniq hΓ hPBu.hasType.1 hP
  obtain ⟨⟨uA, hA⟩, v, hB⟩ := IsType.forallE_inv henv.ordered ⟨u, hPBu.hasType.2⟩
  have himax : VLevel.imax uA v ≈ u := Params.sortUniq hΓ (hA.forallE hB) hPBu.hasType.2
  have hv0 : v ≈ .zero := VLevel.imax_eq_zero.1 (himax.trans hu0)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := by exact ⟨hΓ, _, hA⟩
  exact ⟨uA, hA, (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA)
    (show VLevel.WF univs VLevel.zero from trivial) hv0).defeq hB⟩

/-- **The proof escape climbs an application node.**  If the function side of an `appDF` node
is a proof then the node is one too, so `descend`'s `.inr` disjunct is available at the node
above.  This is `appDF_proofIrrel` without the final `NormalEq` step, which is the form
`descend`'s two E3 branches need.

Landed from `Theory/Typing/DescendRefute.lean`, where it was stated because it could not be
used there: `DescendRefute` imports this file. -/
theorem NormalEq.appDF_proof_escape {Γ : List VExpr} {f₁ f₂ a₁ a₂ A B P : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f₁ : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a₁ : A) (l4 : Γ ⊢ a₂ : A) (l6 : Γ ⊢ a₁ ≡ₚ a₂)
    (hP : Γ ⊢ P : .sort .zero) (hf : Γ ⊢ f₁ : P) :
    ∃ P', (Γ ⊢ P' : .sort .zero) ∧ (Γ ⊢ .app f₁ a₁ : P') ∧ (Γ ⊢ .app f₂ a₂ : P') := by
  obtain ⟨_, hA, hB0⟩ := HasType.codomain_prop_of_isProof hΓ l1 hP hf
  obtain ⟨_, v, hB⟩ := IsType.forallE_inv henv.ordered (l1.isType henv hΓ)
  refine ⟨B.inst a₁, hB0.instN henv.ordered .zero l3, l1.app l3, ?_⟩
  have hab := IsDefEqU.of_l henv hΓ (l6.defeq hΓ) l3
  exact (IsDefEq.instDF henv.ordered hΓ hB hab).defeq' (l2.app l4)

theorem NormalEq.appDF_proofIrrel {Γ : List VExpr} {f a b A B P e₂' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l3 : Γ ⊢ a : A) (l6 : Γ ⊢ a ≡ₚ b)
    (hp : Γ ⊢ P : .sort .zero) (hf : Γ ⊢ f : P)
    (he₂' : Γ ⊢ e₂' : B.inst b) :
    Γ ⊢ .app f a ≡ₚ e₂' := by
  obtain ⟨_, hA, hB0⟩ := HasType.codomain_prop_of_isProof hΓ l1 hp hf
  obtain ⟨_, v, hB⟩ := IsType.forallE_inv henv.ordered (l1.isType henv hΓ)
  have hBa : Γ ⊢ B.inst a : .sort .zero := hB0.instN henv.ordered .zero l3
  -- both sides inhabit it, so proof irrelevance closes the case with no reduction at all
  have hab := IsDefEqU.of_l henv hΓ (l6.defeq hΓ) l3
  have hBab := IsDefEq.instDF henv.ordered hΓ hB hab
  exact .proofIrrel hBa (l1.app l3) (hBab.defeq' he₂')

/-! ## Handoff: what is left of `parRed`'s `extra` case

**State (corrected 2026-08-31; the previous version of this paragraph was wrong three ways
and is retracted below).**  `NormalEq.parRed` and `NormalEq.appDF_extra_of_descend` are
closed.  `NormalEq.descend` has **three** `sorry`s, all in its `.app`-node case, and all
three goals are **false** -- machine-checked in `Theory/Typing/DescendRefute.lean`
(`not_descendStatement`, `not_descendStatement_etaArg`, `not_descendStatement_etaFun`).  They
are not waiting on a hypothesis; they are waiting on a **restatement**, which
`Theory/Typing/KDescend.lean` now supplies (`NormalEq.descendV` +
`NormalEq.appDF_extra_of_descendV`).  Nobody should try to close them here.

**Retraction, in the exact words that were wrong.**  This paragraph used to say the descent
had "five `sorry`s ... **every one of them waits on a hypothesis someone else must supply**:
`hsu` for proof propagation, and the two missing `Params` conditions for argument positions".
Each clause is false:

* *"five"* -- there are three.  The two "the function side is a proof" branches (E3) are now
  closed in place, at the two `.inr` arms of the `.app` case below.
* *"`hsu` ... someone else must supply"* -- `hsu` is `VEnv.SortUniq env univs`, and it is
  **derivable, not assumable**: `Params.sortUniq` (top of this file) gets it from
  `Params.henv` through `Injectivity.lean`'s `WF.sortUniq'`.  `Injectivity` was already in
  this file's import closure *and* already in `descend`'s dependency cone (through
  `IsDefEq.uniq`), so using it adds no import, no cycle and no new taint.  The old claim that
  this "would be circular", and its suggested remedy in `Experimental/Reflect/Capstone.lean`,
  are both retracted (that Capstone route is itself declared closed there).
* *"the two missing `Params` conditions for argument positions"* -- those two conditions are
  "no term matching an argument sub-pattern is a Π" and "no such term is a proof" (the shape
  of `Experimental/NormalEq.lean`'s unused `pat_onArgs` field).  Carrying them as hypotheses
  would have been **vacuity**, not progress: the second is false for every environment with a
  large-eliminating `Prop` inductive (`Eq`, `HEq`, `Acc`, `Quot`), so the three branches would
  have "closed" against an unsatisfiable hypothesis.  They are also not derivable from
  `Params` at all, since `Pat` is abstract there.

**Direction of supply, also corrected.**  This development *consumes* the Π/sort inversion
family; it supplies nothing to it.  `Injectivity.lean` is upstream of this file.

Proved here: the whole non-escape spine (E2), and **all of E4** --- the eta tower, at any
depth, including firing the rule under any number of pending layers (`DescentLam.fire`).
`DescentLam` carries the *answer* under the pending binders, so consuming a layer is
instantiation of an answer (`DescentLam.instN`, `.beta`), producing one is re-wrapping
(`descend`'s `etaL` case), and firing climbs back with `NormalEq.etaL`.  None of the three
recurses on a `NormalEq`, so the measure question that blocked the iterated case does not
arise; see that section for why height-indexing `NormalEq` would *not* have closed it.

**Why the descent has the shape it has — do not "simplify" it.**  Two constraints are not
negotiable.

*Fresh level lists.*  "`g` matches the same pattern at the same `m1`" is **unsatisfiable**:
`NormalEq.constDF` relates `.const c ls` to `.const c ls'` with only `ls ≈ ls'`, while
`Matches` pins the level list exactly:

    example (h : Pattern.Matches (.const c) (.const c ls') (fun _ => ls) nofun) : ls = ls' :=
      by cases h; rfl        -- machine-checked

So as soon as the spine's head is related by `constDF` at genuinely different (but `≈`)
levels, no descent can return the original `m1`.  Hence the fresh `n1'` with
`Forall₂ (· ≈ ·) (n1' lp) (n1 lp)`.  The resulting drift is absorbed *inside*
`appDF_extra_of_descend` — `Pattern.Check.OK.map_levels` on the way in,
`NormalEq.apply_instL` on the way out — so a prover of the descent need not think about it.
The two `VLevel.WF` outputs are in the interface because `apply_instL` needs both lists
well-formed and `constDF` carries both facts already; supplying them there is free (and
`Pattern.Matches.levelWF` below is what pays for it in the `refl` case).

*Reduction and escapes.*  A version of the descent without them was landed and withdrawn: it
is refuted by `etaL` and by `proofIrrel`, which say nothing about the left term.  See the
`DescentOut` section.

**A namespace trap, recorded because it is silent.**  `parRed_of_matches` was first declared
as `Pattern.Matches.parRed_leaves` inside `namespace VEnv`.  That creates `VEnv.Pattern`,
which then shadows `_root_.Lean4Lean.Pattern` at *every later use site in the section* — the
linter reports it as an ambiguous-`open` warning, not an error, and the failures surface far
away as "expected `Pattern.LPath ?m` but got `q₁.LPath ⊕ q₂.LPath`".  Do not put helpers
about `Pattern` under a `Pattern.*` name while inside `namespace VEnv`. -/

/-! ## `parRed`'s `appDF` × `extra` case, modulo the descent

The case reduces to one lemma about `NormalEq` and `Matches` alone — no `parRed`, hence no
recursion.  That was not obvious: the direct routes (fire on the left with `ParRed.rfl` at
the leaves, or reduce the leaves and then fire) both need `parRed` **at the leaves**, which
are strict subterms of `f₂`/`b` and so out of reach of `induction H1`'s two hypotheses.

What makes it work is that `ih1`/`ih2` accept an *arbitrary* `ParRed Γ f₂ e₂'`, not just the
one at hand.  So: reduce `f₂`'s and `b`'s matched arguments **first** (`parRed_leaves`), feed
that to the induction hypotheses, and descend the resulting `NormalEq` against the pattern.
The rule then fires on the left with `ParRed.rfl` at every leaf, and the leaf obligations are
discharged by the descent's own `NormalEq` facts.  One round, no recursion. -/

/-- Reduce a matched term's arguments in place.  The spine is untouched, so the result still
matches the same pattern, with the reduced arguments. -/
theorem parRed_of_matches {Γ : List VExpr} :
    ∀ {q : Pattern} {g : VExpr} {m1 : q.LPath → List VLevel} {m2 m2' : q.Path → VExpr},
      q.Matches g m1 m2 → (∀ x, Γ ⊢ m2 x ≫ m2' x) →
      ∃ g', Γ ⊢ g ≫ g' ∧ q.Matches g' m1 m2'
  | .const c, _, _, _, m2', .const, _ => ⟨_, .const, by
      have : m2' = nofun := funext nofun
      subst this; exact .const⟩
  | .var q, _, _, _, m2', .var h, hr => by
    obtain ⟨g', h1, h2⟩ := parRed_of_matches h (m2' := fun x => m2' (some x)) (fun x => hr (some x))
    refine ⟨.app g' (m2' none), .app h1 (hr none), ?_⟩
    have : m2' = (·.elim (m2' none) fun x => m2' (some x)) := funext fun x => by cases x <;> rfl
    rw [this]; exact .var h2
  | .app q₁ q₂, _, _, _, m2', .app h1 h2, hr => by
    obtain ⟨g1, a1, b1⟩ := parRed_of_matches h1 (m2' := fun x => m2' (.inl x)) (fun x => hr (.inl x))
    obtain ⟨g2, a2, b2⟩ := parRed_of_matches h2 (m2' := fun x => m2' (.inr x)) (fun x => hr (.inr x))
    refine ⟨.app g1 g2, .app a1 a2, ?_⟩
    have : m2' = Sum.elim (fun x => m2' (.inl x)) (fun x => m2' (.inr x)) :=
      funext fun x => by cases x <;> rfl
    rw [this]; exact .app b1 b2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- The `IsDefEqU` counterpart of `NormalEq.apply_pat`. -/
theorem IsDefEqU.apply_pat {p : Pattern} {r : p.RHS}
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (ih : ∀ x A, Γ ⊢ m2 x : A → Γ ⊢ m2 x ≡ m2' x)
    (he : Γ ⊢ Pattern.RHS.apply m1 m2 r : A) :
    Γ ⊢ Pattern.RHS.apply m1 m2 r ≡ Pattern.RHS.apply m1 m2' r := by
  induction r generalizing A with simp [Pattern.RHS.apply] at he ⊢
  | fixed c => exact ⟨_, he⟩
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact ⟨_, ((ih1 h1).of_l henv hΓ h1).appDF ((ih2 h2).of_l henv hΓ h2)⟩
  | var path => exact ih path _ he

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- **E6′**: the `IsDefEqU`-hypothesis variant of `Check.OK.congr_normalEq`.  Needed because
the arguments the rule fired on are related to the ones it will fire on by a *parallel
reduction*, which gives only `IsDefEqU`. -/
theorem _root_.Lean4Lean.Pattern.Check.OK.congr_defeq {p : Pattern} (ck : p.Check)
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (hd : ∀ x A, Γ ⊢ m2 x : A → Γ ⊢ m2 x ≡ m2' x)
    (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 m2' := by
  refine H.map fun a b h => ?_
  obtain ⟨T, hT⟩ := h
  have ha := IsDefEqU.apply_pat hΓ hd hT.hasType.1
  have hb := IsDefEqU.apply_pat hΓ hd hT.hasType.2
  exact (ha.symm.trans henv hΓ ⟨_, hT⟩).trans henv hΓ hb

/-! ## The descent (scoping items E2, E4)

`NormalEq.descend` walks a `NormalEq` down a pattern spine: given `Γ ⊢ g ≡ₚ g'` and a match
of `g'`, it reduces `g` to a term matching the same pattern, with `≈`-related level lists and
`NormalEq`-related arguments.  That is what lets `parRed`'s `appDF` × `extra` case fire the
rule on the *left*.

**The interface this replaced was false.**  A first version asked for `q.Matches g n1' n`
with no reduction and no escapes.  That statement is refuted by `NormalEq.etaL`, which
relates a `.lam` to anything of Π type -- and no `.lam` matches any pattern; the same goes
for `NormalEq.proofIrrel`, whose left term is an arbitrary proof.  Concretely, with
`c` a constant of Π type, `Γ ⊢ .lam A e ≡ₚ .const c ls` and `(.const c).Matches (.const c ls)`
are both derivable and no witness exists.  Those two cases are therefore not "open goals" but
counterexamples, and they are what `DescentOut`'s extra disjuncts exist to carry. -/

omit [Params] in
theorem _root_.Lean4Lean.VLevel.forall₂_equiv_refl :
    ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls
  | [] => .nil
  | _ :: ls => .cons (VLevel.equiv_def'.2 rfl) (VLevel.forall₂_equiv_refl ls)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- The level lists a pattern reads off a **well-typed** term are well-formed.  This is the
"matched levels of a typed term are WF" lemma `descent`'s interface would otherwise force on
its caller; the levels come out of `HasType.const_inv` at the `const` leaves. -/
theorem _root_.Lean4Lean.Pattern.Matches.levelWF {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (H2 : Γ ⊢ e : V) : ∀ lp, ∀ l ∈ m1 lp, VLevel.WF univs l := by
  induction H generalizing V with
  | const =>
    have ⟨_, _, hls, _⟩ := H2.const_inv henv hΓ
    exact fun _ => hls
  | var _ ih =>
    have ⟨_, _, hf, _⟩ := H2.app_inv henv hΓ
    exact ih hf
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    rintro (x|x)
    · exact ih1 hf x
    · exact ih2 ha x

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- The `refl` case of `descent`, at every node of the spine at once: nothing moves, the
level lists are unchanged and each matched argument is `NormalEq` to itself. -/
theorem NormalEq.descent_refl {q : Pattern} {e A : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr}
    (hm : q.Matches e n1 n2) (he : Γ ⊢ e : A) :
    ∃ n1' n, q.Matches e n1' n ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (n1' lp) (n1 lp)) ∧
      (∀ lp, ∀ l ∈ n1' lp, VLevel.WF univs l) ∧
      (∀ lp, ∀ l ∈ n1 lp, VLevel.WF univs l) ∧
      (∀ x, Γ ⊢ n x ≡ₚ n2 x) :=
  ⟨n1, n2, hm, fun _ => VLevel.forall₂_equiv_refl _, hm.levelWF hΓ he, hm.levelWF hΓ he,
    fun x => have ⟨_, h⟩ := hm.hasType hΓ he x; .refl h⟩

/-! ### The escapes, and what is open

`NormalEq.etaL` and `.proofIrrel` constrain nothing about the left term, so nothing can be
concluded about it *at that node*.  `etaL` is handled by `DescentLam` (below): the answer is
computed under the pending binders and instantiated by whichever node supplies the argument.
`proofIrrel` is returned to the node above, where the term sits in an application and
`NormalEq.appDF_proofIrrel` applies.

**Open cases: three, and all three goals are FALSE.**  *(This inventory previously said
"Five `sorry`s remain ... None of their goals is known false".  Both halves were wrong; the
corrected text follows.)*  The two E3 branches are closed in place (see below).  The three
that remain are all in the `.app`-node case, and each is refuted by an explicit witness in
`Theory/Typing/DescendRefute.lean` at a six-axiom, defeq-free environment `refEnv`:

| branch | witness | why no reduct matches |
|---|---|---|
| argument is a proof | `q = C D`, `g = C (bvar 0)`, `g' = C D`, related by `appDF (refl) (proofIrrel)` | `ParRed` has no proof-replacement rule, so `C (bvar 0)` is normal |
| argument eta-expanded | `q = F E`, `g = F (fun _ => E (bvar 0))`, `g' = F E`, related by `etaL` | `ParRed` has no eta-contraction rule, so the argument is normal |
| function eta-expanded | `g = (fun _ : P => C (bvar 1)) D`, `g' = C D`, `etaL` then `proofIrrel` | the only reducts are itself and `C (bvar 0)`, i.e. the first row again |

**Root cause, stated once.**  `NormalEq`'s two non-congruence constructors, `proofIrrel` and
`etaL`/`etaR`, have **no counterpart in `ParRed`**: `ParRed` is `bvar, sort, const, app, lam,
forallE, beta, extra` and nothing else.  `descend`'s conclusion asks a `NormalEq` to be
*pushed through to a reduct*, so at exactly those two constructors it asks for a reduction
step that the relation does not contain.  No hypothesis can fix that, and no restriction of
`q` to registered patterns can either: the same shape arises at a genuinely registered
ι-rule (a `Quot`/`Eq`/`Acc` recursor applied to a major premise that is a proof, or an
eta-expanded function argument).

**What the statement has to become.**  Two repairs, and only two:

1. *Weaken the conclusion at the `.app` node* -- do not ask the argument position to match.
   This is what `Theory/Typing/KDescend.lean` does, and it is machine-checked:
   `NormalEq.descendV` is this file's `descend` plus "the pattern has no `.app` node", and it
   is `sorry`-free; `Params.pat_app_noApp` shows that hypothesis is free at a registered
   pattern, because `pat_simple` puts the only `.app` node at the very top; and the top node
   is then handled by `NormalEq.appDF_extra_of_descendV`, which descends the *function* side
   at `.var q₁` and fires the rule with a K-step, costing one hypothesis `hK : KStep → ParRed`.
   **This is the recommended route**; `descend` here is superseded by it.
2. *Strengthen the reduction* -- give `ParRed` the two steps `NormalEq` has and it lacks
   (proof replacement `h ≫ h'` for two proofs of one `Prop`, and eta-contraction).  Both are
   definitional equalities, so `church_rosser`'s consumers survive, and all three witnesses
   above then reduce to a match.  The cost is that every `ParRed` lemma here (`triangle` above
   all) is re-proved with the new constructors.  `Theory/Typing/KEta.lean` takes this route in
   a *guarded* form -- an eta-expansion step on `ParRedS` -- for a different refutation
   (`KCanonical.lean`'s `not_crStatement_of_kstep`, which refutes `IsDefEq.church_rosser`'s
   statement verbatim); note that route (1) already absorbs the proof-replacement half, since a
   K-step fires whichever proof sits in the major-premise slot.

**Consequence for this file's own results.**  `descend` has 44 transitive users
(`scripts/sorry-census.lean`), `IsDefEq.church_rosser` among them.  Their *statements* are not
refuted, but their current *proofs* route through a false lemma, so they are not merely
"waiting on a hole": the wiring has to be redone against `KDescend.lean`'s `descendV` and
`appDF_extra_of_descendV`.  Until that is done, read every `church_rosser` consumer as
conditional on a repair, not on a hypothesis.

**The refutation's force: the two side hypotheses are satisfiable.**  `not_descendStatement`
is stated under `(hsu : refEnv.SortUniq 0)` and `(huq : refEnv.UniqTyping 0)`, so it is worth
knowing those are not vacuous.  Verdict, checked rather than assumed:

* Both are **provable** -- `DescendRefute.refEnv_sortUniq := refEnv_wf.sortUniq` and
  `refEnv_uniqTyping := fun hΓ h1 h2 => h1.uniq refEnv_wf hΓ h2` -- with a measured hole cone
  of `IsDefEqU.forallE_inv_stratified` alone, and *nothing* from this file: `descend`, `parRed`
  and `church_rosser` are not in either cone, so the refutation is not circular.
  (`not_descendStatement` and `descend_uniq_sortUniq_not_all` are themselves `sorryAx`-free;
  `DescendRefute.not_descendStatement_of_wf` is the unconditional corollary.)
* **But that provability is not evidence of satisfiability**, and saying otherwise would be an
  overclaim: `PiLevelPin.lean`'s `piInvStratApp_iff_sortUniq` shows `forallE_inv_stratified` is
  -- modulo `WF.rigidShapeUniq` -- *equivalent* to `SortUniq` at the same environment and
  index, so that derivation assumes what it checks.  Only the next bullet is independent.
* They are **not refutable by the only known failure route**: `SortUniq` fails
  (`SortUniqDown.lean`'s `sortUniq_badEnv`) only through a `.sort`-headed defeq rule, and
  `refEnv` has no defeq rules at all (`refEnv_no_defeqs`).
* So the only escape from the refutation is that `forallE_inv_stratified` is false -- which
  would sink the whole Π/sort inversion family (443 transitive users) and far more besides.
  The escape is therefore not one anybody should be waiting for: treat `descend` as refuted.

*Closed:* E4 at the top node was the third group.  `DescentLam.fire` now climbs the tower at
any depth -- the firing step is stated once, for every context extension, and `NormalEq.etaL`
does the climb -- so `appDF_extra_of_descend` is sorry-free and its two branches collapsed
into one, uniform in the number of pending layers. -/

/-! ### `DescentLam`: the answer, carried under `k` pending eta layers

**Why the answer and not the data.**  An escape that says only "`g` reduces to a `.lam` whose
body is `NormalEq` to the eta-expanded right-hand side" forces its consumer to *descend that
body*, and after the consumer's β-step the body is `e.inst a₁` -- an instantiated term, which
`sizeOf` does not bound.  Height-indexing `NormalEq` does not rescue it either, although
`NormalEq.instN` does preserve derivation height (it maps every constructor to itself): the
consumer must also repair the argument mismatch, `a₁` on the left against `a₂` on the right,
and that goes through `NormalEq.trans`, which is **not** height-bounded --
`trans (.etaL _ ih) H₂` recurses on `H₂` wrapped in a fresh `appDF`, so the composite grows
by a constant per eta layer while the consumer's budget grows by one.  (`instN_r`, the other
route to the repair, is an induction on the *term*, so it is not height-bounded either.)

`DescentLam k` carries the answer already computed under the `k` binders.  Consuming it is
then instantiation of an *answer* (`DescentLam.beta`), and producing it is re-wrapping
(`descend`'s `etaL` case).  Neither recurses, so no new measure is needed: the recursion that
remains is `descend`'s own, on the lam's body, which is a strict subterm. -/

theorem ParRedS.instN (H₀' : Γ₀ ⊢ a₁ : A₀) (W : Ctx.InstN Γ₀ a₁ A₀ j Γ₁ Γ)
    (H : Γ₁ ⊢ e ≫* e') : Γ ⊢ e.inst a₁ j ≫* e'.inst a₁ j := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail (ParRed.instN .rfl H₀' W h)

/-- The descent's answer at a node, under `k` pending eta layers.

`DescentLam 0` is the descent proper: the left term reduces to one that matches, at levels
`≈` the right term's, with `NormalEq` arguments.  `DescentLam (k+1)` says the left term
reduces to a `.lam` whose body already carries the answer at `k` layers -- against the
eta-expanded right-hand side `g'.lift.app (.bvar 0)`, which the enlarged pattern `.var q`
matches. -/
def DescentLam : Nat → (Γ : List VExpr) → (q : Pattern) → VExpr → VExpr →
    (q.LPath → List VLevel) → (q.Path → VExpr) → Prop
  | 0, Γ, q, g, _, n1, n2 =>
    ∃ t n1' n, ParRedS Γ g t ∧ q.Matches t n1' n ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (n1' lp) (n1 lp)) ∧
      (∀ lp, ∀ l ∈ n1' lp, VLevel.WF univs l) ∧
      (∀ lp, ∀ l ∈ n1 lp, VLevel.WF univs l) ∧
      (∀ x, NormalEq Γ (n x) (n2 x))
  | k+1, Γ, q, g, g', n1, n2 =>
    ∃ A e B, ParRedS Γ g (.lam A e) ∧ HasType env univs Γ g' (.forallE A B) ∧
      DescentLam k (A::Γ) (.var q) e (.app g'.lift (.bvar 0)) n1
        (fun x => x.elim (.bvar 0) fun y => (n2 y).lift)

/-- The two outcomes of descending a `NormalEq` into a matched term at one spine node: the
answer (possibly under pending eta layers), or the proof escape.  The latter constrains
nothing about the left term, so it is resolved by the node above -- see
`NormalEq.appDF_proofIrrel`. -/
def DescentOut (Γ : List VExpr) (q : Pattern) (g g' : VExpr)
    (n1 : q.LPath → List VLevel) (n2 : q.Path → VExpr) : Prop :=
  (∃ k, DescentLam k Γ q g g' n1 n2) ∨
  (∃ P, HasType env univs Γ P (.sort .zero) ∧
      HasType env univs Γ g P ∧ HasType env univs Γ g' P)

/-- Replace the right-hand arguments by pointwise-equal ones. -/
theorem DescentLam.congr_args {k : Nat} {Γ : List VExpr} {q : Pattern} {g g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 n2' : q.Path → VExpr}
    (h : ∀ x, n2 x = n2' x) (H : DescentLam k Γ q g g' n1 n2) :
    DescentLam k Γ q g g' n1 n2' := funext h ▸ H

/-- Prepend a reduction to an answer. -/
theorem DescentLam.head {k : Nat} {Γ : List VExpr} {q : Pattern} {g g₀ g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr}
    (hred : Γ ⊢ g ≫* g₀) (H : DescentLam k Γ q g₀ g' n1 n2) : DescentLam k Γ q g g' n1 n2 := by
  cases k with
  | zero => let ⟨t, u1, u2, h, rest⟩ := H; exact ⟨t, u1, u2, hred.trans h, rest⟩
  | succ k => let ⟨A, e, B, h, rest⟩ := H; exact ⟨A, e, B, hred.trans h, rest⟩

/-- An answer survives instantiation: the left side at `a₁`, the right side at any `a₂` it is
`NormalEq` to.  Nothing here recurses on a `NormalEq`, so the repair at the leaves
(`instN` then `instN_r`, composed by `trans`) costs nothing. -/
theorem DescentLam.instN : ∀ {k : Nat} {Γ₀ Γ₁ Γ : List VExpr} {a₁ a₂ A₀ : VExpr} {j : Nat}
    {q : Pattern} {g g' : VExpr} {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
    OnCtx Γ₁ (IsType env univs) → Γ₀ ⊢ a₁ : A₀ → Γ₀ ⊢ a₁ ≡ₚ a₂ →
    (∀ x, ∃ T, Γ₁ ⊢ n2 x : T) → Ctx.InstN Γ₀ a₁ A₀ j Γ₁ Γ →
    DescentLam k Γ₁ q g g' n1 n2 →
    DescentLam k Γ q (g.inst a₁ j) (g'.inst a₂ j) n1 (fun x => (n2 x).inst a₂ j) := by
  intro k
  induction k with
  | zero =>
    rintro Γ₀ Γ₁ Γ a₁ a₂ A₀ j q g g' n1 n2 hΓ₁ h₀ H' hn2 W ⟨t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩
    have ⟨_, hΓ⟩ := W.wf henv h₀ hΓ₁
    refine ⟨t.inst a₁ j, u1, fun x => (u2 x).inst a₁ j,
      ParRedS.instN h₀ W hred, Pattern.matches_instN hmt, hlv, hwa, hwb, fun x => ?_⟩
    have ⟨_, hT⟩ := hn2 x
    exact (NormalEq.instN h₀ W (hn x)).trans hΓ (NormalEq.instN_r hΓ₁ h₀ H' W hT)
  | succ k ih =>
    rintro Γ₀ Γ₁ Γ a₁ a₂ A₀ j q g g' n1 n2 hΓ₁ h₀ H' hn2 W ⟨A, e, B, hred, hty, D⟩
    have ⟨_, hΓ⟩ := W.wf henv h₀ hΓ₁
    have ⟨⟨_, hA⟩, _, _⟩ := have ⟨_, h⟩ := hty.isType henv hΓ₁; h.forallE_inv henv
    have hΓ₁A : OnCtx (A::Γ₁) (IsType env univs) := ⟨hΓ₁, _, hA⟩
    have hn2' : ∀ (x : Option q.Path), ∃ T,
        (A::Γ₁) ⊢ (x.elim (.bvar 0) fun y => (n2 y).lift) : T := by
      rintro (_|x)
      · exact ⟨_, .bvar .zero⟩
      · exact have ⟨_, h⟩ := hn2 x; ⟨_, h.weakN henv .one⟩
    have hty' : Γ ⊢ g'.inst a₂ j : (VExpr.forallE A B).inst a₁ j :=
      (((NormalEq.instN_r hΓ₁ h₀ H' W hty).defeq hΓ).of_l henv hΓ
        (hty.instN henv W h₀)).hasType.2
    have hinner := ih (q := .var q) hΓ₁A h₀ H' hn2' W.succ D
    refine ⟨A.inst a₁ j, e.inst a₁ (j+1), B.inst a₁ (j+1), ?_, hty', ?_⟩
    · simpa [VExpr.inst] using ParRedS.instN h₀ W hred
    · simp [VExpr.inst, ← VExpr.lift_instN_lo] at hinner
      refine DescentLam.congr_args (fun x => ?_) hinner
      cases x <;> simp [VExpr.inst, VExpr.lift_instN_lo]

/-- **Consuming an answer**: the function side of an application has eta-expanded (its answer
sits under a pending layer), so the node is a β-redex; β-reduce and instantiate the answer.
One layer is peeled, the argument is put back untouched. -/
theorem DescentLam.beta {k : Nat} {Γ : List VExpr} {q₁ : Pattern} {A e f₂ a₁ a₂ : VExpr}
    {m1 : q₁.LPath → List VLevel} {g1 : q₁.Path → VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (haA : Γ ⊢ a₁ : A)
    (hg1 : ∀ x, ∃ T, Γ ⊢ g1 x : T) (l6 : Γ ⊢ a₁ ≡ₚ a₂)
    (D : DescentLam k (A::Γ) (.var q₁) e (.app f₂.lift (.bvar 0)) m1
      (fun x => x.elim (.bvar 0) fun y => (g1 y).lift)) :
    DescentLam k Γ (.var q₁) (e.inst a₁) (.app f₂ a₂) m1 (fun x => x.elim a₂ g1) := by
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, haA.isType henv hΓ⟩
  have hn2 : ∀ (x : Option q₁.Path), ∃ T,
      (A::Γ) ⊢ (x.elim (.bvar 0) fun y => (g1 y).lift) : T := by
    rintro (_|x)
    · exact ⟨_, .bvar .zero⟩
    · exact have ⟨_, h⟩ := hg1 x; ⟨_, h.weakN henv .one⟩
  have H := DescentLam.instN (q := .var q₁) hΓA haA l6 hn2 .zero D
  have heq : (fun (x : (Pattern.var q₁).Path) =>
        ((x.elim (.bvar 0) fun y => (g1 y).lift : VExpr)).inst a₂) =
      (fun (x : (Pattern.var q₁).Path) => x.elim a₂ g1) :=
    funext fun x => by cases x <;> simp [VExpr.inst, VExpr.inst_lift]
  rw [heq] at H
  simpa [VExpr.inst, VExpr.inst_lift] using H


/-- **The descent**, with its escapes in the conclusion.  Induction is on the *left* term
(`ParRedExt.parRed_beta` is the precedent): the `appDF` case recurses on the two children,
and the E4 dance -- where the function child has eta-expanded, so the node is a β-redex --
recurses on the lam's *body*, which is still a strict subterm of the node. -/
theorem NormalEq.descend : ∀ (N : Nat) {g : VExpr}, sizeOf g ≤ N →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      OnCtx Γ (IsType env univs) → Γ ⊢ g ≡ₚ g' → q.Matches g' n1 n2 →
      DescentOut Γ q g g' n1 n2 := by
  intro N
  induction N using Nat.strongRecOn with | _ N IH => ?_
  intro g hsz Γ q g' n1 n2 hΓ hne hm
  cases hne with
  | refl h =>
    obtain ⟨u1, u2, hmt, hlv, hwa, hwb, hn⟩ := descent_refl hΓ hm h
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
    -- The left term *is* a `.lam`: descend its body against the eta-expanded right-hand
    -- side, which the enlarged pattern `.var q` matches, and re-wrap.  The body is a strict
    -- subterm, so this is the same `sizeOf` recursion as everywhere else.
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := h1.isType henv hΓ; h.forallE_inv henv
    have hΓA : OnCtx (_::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have hmlift : q.Matches g'.lift n1 (fun x => (n2 x).lift) :=
      Pattern.matches_liftN.2 ⟨n2, hm, fun _ => rfl⟩
    match IH _ (by simp at hsz; omega) (Nat.le_refl _) hΓA h2 (.var hmlift) with
    | .inl ⟨k, D⟩ => exact .inl ⟨k+1, _, _, _, .rfl, h1, D⟩
    | .inr ⟨P, hP, hp1, hp2⟩ =>
      -- The body is a proof, so the `.lam` is a proof: `∀ A, P` is a `Prop` by `imax_zero`.
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
    have hsza : sizeOf a₁ < N := by simp at hsz; omega
    cases hm with
    | @var q₁ _ m1 g1 hf =>
      rename_i hf
      match IH _ hszf (Nat.le_refl _) hΓ l5 hf with
      | .inl ⟨0, t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩ =>
        refine .inl ⟨0, .app t a₁, u1, (·.elim a₁ u2), ParRedS.app hred .rfl, .var hmt,
          hlv, hwa, hwb, ?_⟩
        rintro (_|x)
        · exact l6
        · exact hn x
      | .inl ⟨k+1, A, e, B, hred, hty, D⟩ =>
        -- the function side eta-expanded: β-reduce and instantiate its answer
        have ⟨⟨_, u1⟩, _, _⟩ := (hty.uniqU henv hΓ l2).forallE_inv henv hΓ
        exact .inl ⟨k, DescentLam.head
          (.trans (ParRedS.app hred .rfl) (.tail .rfl (.beta .rfl .rfl)))
          (DescentLam.beta hΓ (u1.symm.defeq l3) (fun x => hf.hasType hΓ l2 x) l6 D)⟩
      | .inr ⟨P, hP, hp1, hp2⟩ =>
        -- **E3, closed**: the function side is a proof, so the node is one too.  No hypothesis
        -- is supplied from outside: `Params.sortUniq` derives the universe uniqueness this
        -- needs from `Params.henv`.
        exact .inr (NormalEq.appDF_proof_escape hΓ l1 l2 l3 l4 l6 hP hp1)
    | @app q₁ _ m1 g1 q₂ _ m2 g2 hf ha =>
      rename_i ha
      rcases IH _ hszf (Nat.le_refl _) hΓ l5 hf with ⟨kf, Df⟩ | escf
      · rcases IH _ hsza (Nat.le_refl _) hΓ l6 ha with ⟨ka, Da⟩ | esca
        · cases kf with
          | succ kf =>
            -- **E5**: the function side eta-expanded at an `.app` node.  Peeling the layer
            -- gives an answer at `.var q₁`, whose argument position is unconstrained, while
            -- this node needs it to match `q₂`.  See the inventory, item 3.
            sorry
          | zero =>
            cases ka with
            | succ ka =>
              -- **E5**: an argument position that eta-expanded never matches `q₂`.
              sorry
            | zero =>
              obtain ⟨t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩ := Df
              obtain ⟨s, v1, v2, hred2, hms, hlv2, hwa2, hwb2, hn2⟩ := Da
              refine .inl ⟨0, .app t s, Sum.elim u1 v1, Sum.elim u2 v2,
                ParRedS.app hred hred2, .app hmt hms, ?_, ?_, ?_, ?_⟩ <;> rintro (x|x)
              · exact hlv x
              · exact hlv2 x
              · exact hwa x
              · exact hwa2 x
              · exact hwb x
              · exact hwb2 x
              · exact hn x
              · exact hn2 x
        · -- **E5**: an argument position that is a proof never matches `q₂`.
          sorry
      · -- **E3, closed**: the function side is a proof, so the node is one too (as in the
        -- `.var` case above).
        obtain ⟨P, hP, hp1, hp2⟩ := escf
        exact .inr (NormalEq.appDF_proof_escape hΓ l1 l2 l3 l4 l6 hP hp1)


/-- **Firing the rule under `k` pending eta layers** (inventory item 3).

`bot` is the firing step at the bottom of the tower.  It is quantified over context
extensions because each layer descends under one more binder -- that is the only reason it
is not simply "fire here".  The climb back up is `NormalEq.etaL` at each layer, and it works
because `(RHS.apply n1 n2 r).lift = RHS.apply n1 (lift ∘ n2) r`: the rule's output eta-expands
into exactly the shape the layer below produced.

Note what is *not* needed: nothing is re-descended, so no measure appears.  The pattern `P`
stays abstract, which is what lets the layer step derive `bot` at `.var P` from `bot` at `P`
without any `Pattern.varN` bookkeeping. -/
theorem DescentLam.fire : ∀ {k : Nat} {Γ : List VExpr} {P : Pattern} {S g g' : VExpr}
    {n1 : P.LPath → List VLevel} {n2 : P.Path → VExpr},
    OnCtx Γ (IsType env univs) → (∃ T, Γ ⊢ g : T) → Γ ⊢ S ≡ g' →
    (∀ {Γ' : List VExpr} {n : Nat} {t : VExpr} {u1 u2},
      Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
      P.Matches t u1 u2 →
      (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (n1 lp)) →
      (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
      (∀ x, Γ' ⊢ u2 x ≡ₚ (n2 x).liftN n) →
      ∃ s, Γ' ⊢ t ≫* s ∧ Γ' ⊢ s ≡ₚ S.liftN n) →
    DescentLam k Γ P g g' n1 n2 →
    ∃ t, Γ ⊢ g ≫* t ∧ Γ ⊢ t ≡ₚ S := by
  intro k
  induction k with
  | zero =>
    rintro Γ P S g g' n1 n2 hΓ hg _ bot ⟨t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩
    have ⟨_, hT⟩ := hg
    have ⟨s, hs1, hs2⟩ := bot (Γ' := Γ) (n := 0) (.zero []) hΓ ⟨_, hred.hasType hΓ hT⟩
      hmt hlv hwa (by simpa using hn)
    exact ⟨s, hred.trans hs1, by simpa using hs2⟩
  | succ k ih =>
    rintro Γ P S g g' n1 n2 hΓ hg hSg' bot ⟨A, e, B, hred, hty, D⟩
    have ⟨_, hgT⟩ := hg
    have ⟨⟨_, hA⟩, heT⟩ := (hred.hasType hΓ hgT).lam_inv henv hΓ
    have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have hSty : Γ ⊢ S : .forallE A B := (hSg'.symm.of_l henv hΓ hty).hasType.2
    have hSl : Γ ⊢ S ≡ g' : .forallE A B := hSg'.of_l henv hΓ hSty
    have hbot' : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
        {u1 : (Pattern.var P).LPath → List VLevel} {u2 : (Pattern.var P).Path → VExpr},
        Ctx.LiftN n 0 (A::Γ) Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
        (Pattern.var P).Matches t u1 u2 →
        (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (n1 lp)) →
        (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
        (∀ x, Γ' ⊢ u2 x ≡ₚ ((x.elim (.bvar 0) fun y => (n2 y).lift : VExpr)).liftN n) →
        ∃ s, Γ' ⊢ t ≫* s ∧ Γ' ⊢ s ≡ₚ ((VExpr.app S.lift (.bvar 0))).liftN n := by
      intro Γ' n t u1 u2 W hΓ' ht' hmt' hlv' hwa' hn'
      cases hmt' with
      | @var _ tf _ tg ta hmtf =>
        rename_i hmtf
        have ⟨_, htT⟩ := ht'
        have ⟨_, _, htf, hta⟩ := htT.app_inv henv hΓ'
        have ⟨s, hs1, hs2⟩ :=
          bot (Ctx.LiftN.comp (Nat.le_refl 0) (Nat.zero_le _) .one W) hΓ' ⟨_, htf⟩ hmtf hlv'
            hwa' (fun y => by simpa [VExpr.liftN_liftN] using hn' (some y))
        have hbv : Γ' ⊢ ta ≡ₚ .bvar n := by simpa [VExpr.liftN] using hn' none
        have hs' := hs1.hasType hΓ' htf
        refine ⟨.app s ta, ParRedS.app hs1 .rfl, ?_⟩
        have hS' := ((hs2.defeq hΓ').of_l henv hΓ' hs').hasType.2
        have hbvT := ((hbv.defeq hΓ').of_l henv hΓ' hta).hasType.2
        simpa [VExpr.liftN, VExpr.liftN_liftN] using
          NormalEq.appDF hs' hS' hta hbvT hs2 hbv
    have ⟨t, ht1, ht2⟩ := ih hΓA heT
      ⟨_, .appDF (hSl.weakN henv .one) (.bvar .zero)⟩ hbot' D
    exact ⟨_, hred.trans (ParRedS.lam .rfl ht1), .etaL hSty ht2⟩



/-- **`parRed`'s `appDF` × `extra` case.**  One `sorry`: E4 at the top node (item 4 of the
`DescentOut` inventory).

The descent is taken **once, on the whole node** `tf.app ta` against the whole pattern, not
once per child.  That matters: a child-by-child descent hands the `.lam` escape back here,
where it would have to be resolved a second time; taking the node whole leaves `descend` to
run its own β-dance internally, and what escapes here is only what escapes at the top.  The
`.lam` escape is still possible (`f.app a` may itself reduce to a `.lam`) — that is the one
`sorry`; the proof escape is discharged, since there both sides inhabit the same `P` and
`Params.pat_wf` types the rule's output at it.

Note what the descent may *not* assume: that the left term matches at the **same** level
lists.  `NormalEq.constDF` relates `.const c ls` to `.const c ls'` with only `ls ≈ ls'`, while
`Matches` pins the list exactly (`cases` on `Matches (.const c) (.const c ls') (fun _ => ls) _`
forces `ls = ls'`).  So a descent returning the original `m1` is unsatisfiable as soon as the
spine's head is related by `constDF` — the first version of this lemma asked for exactly that
and was vacuous.  The interface therefore returns a fresh `n1'` with
`Forall₂ (· ≈ ·) (n1' lp) (n1 lp)`, and the level drift is absorbed here by
`Check.OK.map_levels` on the way in and `NormalEq.apply_instL` on the way out.  The two
`WF` outputs are there because `apply_instL` needs both lists well-formed and `constDF`
carries both facts already. -/
theorem NormalEq.appDF_extra_of_descend {Γ : List VExpr} {f A B a b f₂ : VExpr}
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
    obtain ⟨f₂', hpf, hmf⟩ :=
      parRed_of_matches h1 (m2' := fun x => m2' (.inl x)) (fun x => r4 (.inl x))
    obtain ⟨b', hpb, hmb⟩ :=
      parRed_of_matches h2 (m2' := fun x => m2' (.inr x)) (fun x => r4 (.inr x))
    obtain ⟨tf, hf1, hf2⟩ := ih1 hpf
    obtain ⟨ta, ha1, ha2⟩ := ih2 hpb
    have heq : Sum.elim (fun x => m2' (Sum.inl x)) (fun x => m2' (Sum.inr x)) = m2' :=
      funext fun x => by cases x <;> rfl
    have hmnode : (q₁.app q₂).Matches (f₂'.app b') (Sum.elim f1 f2) m2' := heq ▸ .app hmf hmb
    have htf : Γ ⊢ tf : .forallE A B := hf1.hasType hΓ l1
    have hta : Γ ⊢ ta : A := ha1.hasType hΓ l3
    have hnode : Γ ⊢ tf.app ta ≡ₚ f₂'.app b' :=
      .appDF htf (hpf.hasType hΓ l2) hta (hpb.hasType hΓ l4) hf2 ha2
    have hck' : Pattern.Check.OK (IsDefEqU env univs Γ) (p := q₁.app q₂)
        (Sum.elim f1 f2) m2' r.snd :=
      r3.congr_defeq hΓ _ fun x _ hty => ⟨_, (r4 x).defeq hΓ hty⟩
    have hwB : ∀ lp, ∀ l ∈ Sum.elim f1 f2 lp, VLevel.WF univs l :=
      hmnode.levelWF hΓ ((hpf.hasType hΓ l2).app (hpb.hasType hΓ l4))
    -- **The firing step**, stated for every context extension because `DescentLam.fire`
    -- descends under one binder per pending eta layer.  At zero layers this *is* the case.
    have hbot : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
        {u1 : (q₁.app q₂).LPath → List VLevel} {u2 : (q₁.app q₂).Path → VExpr},
        Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
        (q₁.app q₂).Matches t u1 u2 →
        (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (Sum.elim f1 f2 lp)) →
        (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
        (∀ x, Γ' ⊢ u2 x ≡ₚ (m2' x).liftN n) →
        ∃ s, Γ' ⊢ t ≫* s ∧
          Γ' ⊢ s ≡ₚ (Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2) m2' r.fst).liftN n := by
      intro Γ' n t u1 u2 W hΓ' ht' hmt hlv hwA hne
      have flipeq : ∀ {l1 l2 : List VLevel},
          List.Forall₂ (· ≈ ·) l1 l2 → List.Forall₂ (· ≈ ·) l2 l1 := by
        intro l1 l2 h
        induction h with
        | nil => exact .nil
        | cons h _ ih => exact .cons h.symm ih
      have hlvs : ∀ lp, List.Forall₂ (· ≈ ·) (Sum.elim f1 f2 lp) (u1 lp) :=
        fun lp => flipeq (hlv lp)
      have hckW := hck'.weakN W r.snd
      have hck : Pattern.Check.OK (IsDefEqU env univs Γ') (p := q₁.app q₂) u1 u2 r.snd := by
        refine hckW.map_levels (fun x i y j hl => ?_) (fun u v h => ?_)
        · exact ((VLevel.forall₂_getD (hlv x) i).trans hl).trans
            (VLevel.forall₂_getD (hlv y) j).symm
        · obtain ⟨T, hT⟩ := h
          have step : ∀ (w : (q₁.app q₂).RHS) {C},
              Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                    (fun x => (m2' x).liftN n) w : C →
              Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                    (fun x => (m2' x).liftN n) w ≡
                  Pattern.RHS.apply (p := q₁.app q₂) u1 u2 w := by
            intro w C hw
            have hins := NormalEq.apply_instL (p := q₁.app q₂) (r := w) hΓ' hwB hwA hlvs hw
            have ⟨_, hh⟩ := hins.defeq hΓ'
            refine (hins.defeq hΓ').trans henv hΓ'
              (IsDefEqU.apply_pat hΓ' (fun x _ _ => ((hne x).defeq hΓ').symm) hh.hasType.2)
          exact ((step u hT.hasType.1).symm.trans henv hΓ' ⟨_, hT⟩).trans henv hΓ'
            (step v hT.hasType.2)
      have hfire : Γ' ⊢ t ≫ Pattern.RHS.apply (p := q₁.app q₂) u1 u2 r.fst :=
        .extra r1 hmt hck (fun _ => .rfl)
      have ⟨_, htT⟩ := ht'
      refine ⟨_, .tail .rfl hfire, ?_⟩
      rw [Pattern.RHS.liftN_apply (p := q₁.app q₂) (m1 := Sum.elim f1 f2) (m2 := m2') r.fst]
      have hstep1 := NormalEq.apply_instL (p := q₁.app q₂) (r := r.fst) hΓ' hwA hwB hlv
        (hfire.hasType hΓ' htT)
      refine hstep1.trans hΓ' ?_
      have ⟨_, hh⟩ := hstep1.defeq hΓ'
      exact NormalEq.apply_pat hΓ' (fun (x : (q₁.app q₂).Path) _ _ => hne x) hh.hasType.2
    match NormalEq.descend _ (Nat.le_refl _) hΓ hnode hmnode with
    | .inl ⟨k, D⟩ =>
      -- Uniform in the number of pending eta layers: `DescentLam.fire` climbs the tower.
      have ⟨t, ht1, ht2⟩ := DescentLam.fire hΓ ⟨_, htf.app hta⟩
        (Params.pat_wf r1 hmnode hΓ ((hpf.hasType hΓ l2).app (hpb.hasType hΓ l4)) hck').symm
        hbot D
      exact ⟨t, (ParRedS.app hf1 ha1).trans ht1, ht2⟩
    | .inr ⟨P, hP, hp1, hp2⟩ =>
      -- **E3 at the top node**: both sides are proofs, so no reduction is needed.  The rule's
      -- output inhabits the same `Prop` by `Params.pat_wf`.
      exact ⟨_, ParRedS.app hf1 ha1,

        .proofIrrel hP hp1 ((Params.pat_wf r1 hmnode hΓ hp2 hck').of_l henv hΓ hp2).hasType.2⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.parRed (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : Γ ⊢ e₂ ≫ e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  induction H1 generalizing e₂' with
  | refl l1 => exact ⟨_, .tail .rfl H2, .refl (H2.hasType hΓ l1)⟩
  | sortDF l1 l2 l3 =>
    cases H2 with
    | sort => exact ⟨_, .tail .rfl .sort, .sortDF l1 l2 l3⟩
    | extra r1 r2 => cases r2
  | @constDF c ci ls ls' Γ l1 l2 l3 l4 l5 =>
    cases H2 with
    | const => exact ⟨_, .tail .rfl .const, .constDF l1 l2 l3 l4 l5⟩
    | @extra p r _ m1 m2 _ m3 r1 r2 r3 r4 =>
      cases r2
      have l5' : List.Forall₂ (· ≈ ·) _ _ := l5.flip.imp fun _ _ h => h.symm
      have hred : Γ ⊢ .const c ls ≫ r.1.apply (fun _ => ls) m3 := by
        refine .extra (m2' := m3) r1 .const ?_ nofun
        refine r3.map_levels (fun x i y j hxy => ?_) fun a b h => ?_
        · exact ((VLevel.forall₂_getD l5' i).symm.trans hxy).trans (VLevel.forall₂_getD l5' j)
        have ⟨_, hT⟩ := h
        have pa := NormalEq.apply_instL (r := a) hΓ (fun _ => l3) (fun _ => l2)
          (fun _ => l5') hT.hasType.1
        have pb := NormalEq.apply_instL (r := b) hΓ (fun _ => l3) (fun _ => l2)
          (fun _ => l5') hT.hasType.2
        exact ((pa.defeq hΓ).symm.trans henv hΓ h).trans henv hΓ (pb.defeq hΓ)
      exact ⟨_, .tail .rfl hred,
        NormalEq.apply_instL hΓ (fun _ => l2) (fun _ => l3) (fun _ => l5)
          (hred.hasType hΓ (.const l1 l2 l4))⟩
  | @appDF Γ f A B f₂ a b l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    cases H2 with
    | app r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 hΓ r1
      let ⟨_, b1, b2⟩ := ih2 hΓ r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2) (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩
    | @beta A _ e e' _ b' r1 r2 =>
      let ⟨f', a1, a2⟩ := ih1 hΓ (.lam .rfl r1)
      let ⟨a', b1, b2⟩ := ih2 hΓ r2
      let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
      let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
      refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.hasType hΓ' (u2.defeq d2); ?_
      replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
      let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta hΓ a2
        (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
      exact ⟨_, .trans (a1.app b1) h1, h2.trans hΓ (.instN_r hΓ' l3 b2 .zero d2)⟩
    | extra r1 r2 r3 r4 =>
      -- The case is `NormalEq.appDF_extra_of_descend` above, which descends the whole node
      -- with `NormalEq.descend`.
      exact NormalEq.appDF_extra_of_descend hΓ l1 l2 l3 l4
        (fun h => ih1 hΓ h) (fun h => ih2 hΓ h) r1 r2 r3 r4
  | lamDF l1 l2 l3 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩); have ⟨_, h1⟩ := l3.defeq hΓ'; ?_
      have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
      replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
      let ⟨_, b1, b2⟩ := ih1 hΓ' r2
      exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
        .lamDF l1 (.trans l2 (r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
    | extra _ r2 => cases r2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with
    | forallE r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 hΓ r1
      refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩)
        have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ'); ?_
      have W := l1.transU_l henv hΓ (l2.defeq hΓ)
      replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
      let ⟨_, b1, b2⟩ := ih2 hΓ' r2
      have := r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
      exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
        .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2 (b1.hasType hΓ' l3) b2⟩
    | extra _ r2 => cases r2
  | etaL l1 l2 ih1 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    refine have hΓ' := by exact ⟨hΓ, _, hA⟩
      let ⟨_, a1, a2⟩ := ih1 hΓ' (.app (.weakN .one H2) .bvar); ?_
    exact ⟨_, .lam .rfl a1, .etaL (H2.hasType hΓ l1) a2⟩
  | @etaR Γ e A _ _ l1 l2 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      refine have hΓ' := (by exact ⟨hΓ, _, hA⟩); let ⟨t, a1, a2⟩ := ih1 hΓ' r2; ?_
      suffices
          (∃ A', Γ ⊢ e ≫* A'.lam t ∧ Γ ⊢ A' ≡ A) ∨
          (∃ e', Γ ⊢ e ≫* e' ∧ t = .app (.lift e') (.bvar 0)) by
        obtain ⟨_, h1, h2⟩ | ⟨_, h, rfl⟩ := this
        · exact ⟨_, h1, .lamDF (h2.of_r henv hΓ hA).symm (r1.defeq hΓ hA) a2⟩
        · have := a2.etaR (h.hasType hΓ l1)
          have ⟨_, a3⟩ := a2.defeq hΓ'
          exact ⟨_, h, this.trans hΓ (.lamDF hA (r1.defeq hΓ hA) (.refl a3.hasType.2))⟩
      generalize eq : e.lift.app (.bvar 0) = e' at a1
      clear l2 ih1 a2
      induction a1 generalizing e with subst eq
      | rfl => exact .inr ⟨_, .rfl, rfl⟩ | tail _ a1 ih
      obtain ⟨_, h1, h2⟩ | ⟨e', h, rfl⟩ := ih l1 rfl
      · have h2' := h2.of_r henv hΓ hA
        have ⟨⟨_, d1⟩, _, d2⟩ := (h1.hasType hΓ l1).lam_inv henv hΓ
        exact .inl ⟨_, h1.tail <| .lam .rfl (a1.defeqDFC hΓ (.succ .zero h2'.symm)
          (.defeqDFC henv (.succ .zero h2') d2)), h2⟩
      generalize eq : e'.lift = e1 at a1
      cases a1 with
      | app b1 b2 =>
        cases b2 with | bvar => ?_ | extra _ h => cases h
        cases eq; obtain ⟨_, b1', rfl⟩ := b1.weakN_inv hΓ' .one ((h.hasType hΓ l1).weak henv)
        exact .inr ⟨_, .tail h b1', rfl⟩
      | beta b1 b2 =>
        cases b2 with | bvar => ?_ | extra _ h => cases h
        cases e' <;> cases eq
        have ⟨⟨_, c1⟩, _, c2⟩ := (h.hasType hΓ l1).lam_inv henv hΓ
        obtain ⟨_, b1', rfl⟩ := b1.weakN_inv
          (by exact ⟨hΓ', _, c1.weak henv⟩) (.succ .one) (c2.weakN henv (.succ .one))
        rw [instN_bvar0]
        have l1' := h.hasType hΓ l1
        have ⟨⟨_, d1⟩, _, d2⟩ := l1'.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l1').forallE_inv henv hΓ
        exact .inl ⟨_, .tail h <| .lam .rfl b1', _, u1⟩
      | extra b1 b2 b3 b4 =>
        cases b2 with | app _ h => cases h | var => cases pat_not_var b1
    | extra _ r2 => cases r2
  | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (H2.hasType hΓ l3)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.parRedS (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : Γ ⊢ e₂ ≫* e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  induction H2 with
  | rfl => exact ⟨_, .rfl, H1⟩
  | tail h1 h2 ih =>
    let ⟨_, a1, a2⟩ := ih
    let ⟨_, b1, b2⟩ := a2.parRed hΓ h2
    exact ⟨_, .trans a1 b1, b2⟩

local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => CRDefEq Γ e1 e2

def CRDefEq (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  (∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂'

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.church_rosser  (H : Γ ⊢ e : A)
    (H1 : Γ ⊢ e ≫* e₁) (H2 : Γ ⊢ e ≫* e₂) : Γ ⊢ e₁ ≫≪ e₂ := by
  refine ⟨⟨_, H1.hasType hΓ H⟩, ⟨_, H2.hasType hΓ H⟩, ?_⟩
  induction H2 with
  | rfl => exact ⟨_, _, .rfl, H1, .refl (H1.hasType hΓ H)⟩
  | @tail b c h1 H2 ih =>
    replace H := ParRedS.hasType hΓ h1 H
    have ⟨_, A2, a1, a2, a3⟩ := ih
    have ⟨_, _, b1, b2, b3⟩ :
        ∃ e₁' e₂', Γ ⊢ A2 ≫ e₁' ∧ Γ ⊢ c ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
      clear a3; induction a2 with
      | rfl => exact ⟨_, _, H2, .rfl, .refl (H2.hasType hΓ H)⟩
      | tail h1 h2 ih =>
        have ⟨_, _, a1, a2, a3⟩ := ih
        have ⟨_, _, b1, b2, b3⟩ := a1.church_rosser hΓ (ParRedS.hasType hΓ h1 H) h2
        have ⟨_, c1, c2⟩ := (a3.symm hΓ).parRed hΓ b1
        exact ⟨_, _, b2, .trans a2 c1, (c2.trans hΓ b3).symm hΓ⟩
    have ⟨_, c1, c2⟩ := a3.parRed hΓ b1
    exact ⟨_, _, .trans a1 c1, b2, c2.trans hΓ b3⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂) : Γ ⊢ e₁ ≫≪ e₂ :=
  let ⟨_, h⟩ := H.defeq hΓ; ⟨⟨_, h.hasType.1⟩, ⟨_, h.hasType.2⟩, _, _, .rfl, .rfl, H⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e := .normalEq hΓ (.refl H)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₁ ≡ e₂
  | ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, h3, h4, h5⟩ =>
    ⟨_, .trans_l henv hΓ (h3.defeq hΓ h1) <| .transU_r henv hΓ (h5.defeq hΓ) (h4.defeq hΓ h2).symm⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₁
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h2, h1, _, _, h4, h3, h5.symm hΓ⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₃ → Γ ⊢ e₁ ≫≪ e₃
  | ⟨l1, ⟨_, l2⟩, _, _, l3, l4, l5⟩, ⟨_, r2, _, _, r3, r4, r5⟩ => by
    let ⟨_, _, _, _, m1, m2, m3⟩ := l4.church_rosser hΓ l2 r3
    let ⟨_, a1, a2⟩ := l5.parRedS hΓ m1
    let ⟨_, b1, b2⟩ := (r5.symm hΓ).parRedS hΓ m2
    exact ⟨l1, r2, _, _, .trans l3 a1, .trans r4 b1, a2.trans hΓ <| m3.trans hΓ (b2.symm hΓ)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.church_rosser
    (H : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ := by
  have mk {Γ e₁ e₂ A e₁' e₂'} (H : Γ ⊢ e₁ ≡ e₂ : A)
      (h1 : Γ ⊢ e₁ ≫* e₁') (h2 : Γ ⊢ e₂ ≫* e₂') (h3 : Γ ⊢ e₁' ≡ₚ e₂') : Γ ⊢ e₁≫≪ e₂ :=
    ⟨⟨_, H.hasType.1⟩, ⟨_, H.hasType.2⟩, _, _, h1, h2, h3⟩
  induction H with
  | bvar h => exact .refl hΓ (.bvar h)
  | symm _ ih => exact (ih hΓ).symm hΓ
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans hΓ (ih2 hΓ)
  | sortDF h1 h2 h3 => exact .normalEq hΓ (.sortDF h1 h2 h3)
  | constDF h1 h2 h3 h4 h5 => exact .normalEq hΓ (.constDF h1 h2 h3 h4 h5)
  | appDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 hΓ
    exact mk (.appDF h1 h2) (.app a1 b1) (.app a2 b2) <|
      .appDF (a1.hasType hΓ h1.hasType.1) (a2.hasType hΓ h1.hasType.2)
        (b1.hasType hΓ h2.hasType.1) (b2.hasType hΓ h2.hasType.2) a3 b3
  | lamDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 ⟨hΓ, _, h1.hasType.1⟩
    have b2' := b2.defeqDFC hΓ (.succ .zero h1) h2.hasType.2
    have := (a1.defeq hΓ h1.hasType.1).symm
    exact mk (.lamDF h1 h2) (.lam a1 b1) (.lam a2 b2') <|
      .lamDF this.symm (this.symm.transU_l henv hΓ (a3.defeq hΓ)) b3
  | forallEDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    refine have hΓ' := ⟨hΓ, _, h1.hasType.1⟩; have ⟨_, _, _, _, b1, b2, b3⟩ := ih2 hΓ'; ?_
    have b2' := b2.defeqDFC hΓ (.succ .zero h1) h2.hasType.2
    exact mk (.forallEDF h1 h2) (.forallE a1 b1) (.forallE a2 b2') <|
      .forallEDF (a1.defeq hΓ h1.hasType.1) a3 (b1.hasType hΓ' h2.hasType.1) b3
  | defeqDF _ _ _ ih2 => exact ih2 hΓ
  | beta h1 h2 ih1 ih2 =>
    refine have h := .beta h1 h2; mk h (.tail .rfl (.beta .rfl .rfl)) .rfl ?_
    exact .refl h.hasType.2
  | eta h1 ih1 =>
    have := h1.hasType.1
    exact .normalEq hΓ <| .etaL this <| .refl <| .app (this.weak henv) (.bvar .zero)
  | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
    exact .normalEq hΓ <| .proofIrrel h1.hasType.1 h2.hasType.1 h3.hasType.1
  | @extra _ _ Γ h1 h2 h3 =>
    have h := IsDefEq.extra (Γ := Γ) h1 h2 h3
    obtain ⟨Δ, L, R, p, r, m1, m2, e1, e2, a1, a2, a3, a4⟩ := extra_pat hΓ h1 h2 h3 (Γ := Γ)
    have hstep : ParRed (Δ.reverse ++ Γ) L R := a4 ▸ ParRed.extra a1 a2 a3 fun _ => .rfl
    have hlams := ParRed.lams (Δ := Δ) hstep
    rw [← e1, ← e2] at hlams
    exact mk h (.tail .rfl hlams) .rfl (.refl h.hasType.2)
