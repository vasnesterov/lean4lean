import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Strengthening (the inverse of weakening): what is provable, and where it is blocked

`VEnv.IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:174`) asserts that a conversion
between two *lifted* terms in the larger context descends to the smaller one.  Its forward
direction is the only `sorry` in that file, and 119 declarations of this package are tainted
through it.  Nothing here assumes it; the file records what *is* provable.

The headline, **as corrected in §9**: `TransStrengthening` is not a residual — it *is* the
target (`Strengthening.iff_trans`, sorry-free), so §8's

    Strengthening ↔ SortDescend ∧ PiDescend ∧ TransStrengthening

is a tautology read as a reduction.  What survives is a statement about the target's
*reflexive instance*, and §9 collapses that from two statements to one:

    TypingStrengthening ↔ PiDescend

Contents:

* §1 `IsDefEqU.strengthen_of_instN` — **strengthening holds whenever the stripped hypothesis
  is inhabited**, by substitution.  Sorry-free.  So the obstruction lives entirely in
  *uninhabited* context entries, which is also why no model argument can reach it.
* §2 the statement `Strengthening`, its reflexive instance `TypingStrengthening`, and the
  `trans` case `TransStrengthening` (**§9: not a residual — it is the target**).
* §3 `TypingStrengthening.typed` — the existential form implies the *typed* form, by applying
  itself to a type-ascription redex.
* §4 inversion of `liftN` against a head constructor.
* §5 `Strengthening.of_typing` — **eleven of the twelve conversion rules close from
  `TypingStrengthening` alone**; `trans` is the only case left, and there both induction
  hypotheses are vacuous.  **§9: this is a map of the induction, not a reduction** — the
  theorem is provable from its `TransStrengthening` hypothesis alone.
* §6 `Strengthening.iff_typed` — the typed statement (`IsDefEq.weakN_iff'`) and the untyped
  one are inter-derivable, so they are not two problems.
* §7 `TypingStrengthening.iff_descend` — **`TypingStrengthening` is exactly `SortDescend` ∧
  `PiDescend`**, sorry-free.  Its own induction is on the syntax-directed `HasTypeStrong`, so
  it never inspects a conversion derivation and `trans` never arises.
* §8 the capstone — **superseded by §9**, which shows its `←` direction never uses its first
  two hypotheses.
* §9 the correction: `Strengthening ↔ TransStrengthening`, and `PiDescend → SortDescend`, so
  `TypingStrengthening ↔ PiDescend`.
* §10 the bridge: `Strengthening` assumes `OnCtx Γ` and the hole does not, so §1-§9 did not
  formally reach the hole.  `Strengthening.iff_target` closes that gap, sorry-free.
* §11 `Strengthening1.iff_target` — **stripping one entry at a time is enough**, which is what
  makes §1's `n = 1` tools (`exists_instN`, `strengthen_of_instN`) apply to the target.
* §12 `Strengthening1Uninhab.iff_target` — **the obstruction is exactly the uninhabited
  entries**, §1's informal remark turned into a theorem, with its vacuity dual.

**Axiom cones, machine-checked.**  §1, §4, §7, `Strengthening.{typing,trans}` and §9's
`TransStrengthening.strengthening` / `Strengthening.iff_trans` are sorry-free.  §9's
`PiDescend.sortDescend` is not: it buys the collapse of the two shape-descent statements to
one at the price of Π-injectivity.  §3, §5, §6, §8 and the rest of §9 are `sorryAx`-tainted
through `IsDefEqU.forallE_inv` /
`IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`, pre-existing open obligations) and
through **nothing else** — in particular there is *no* dependency on `IsDefEqU.weakN_iff`
itself, so none of it is circular.  See `docs/handoff-weakn.md`.
-/
namespace Lean4Lean
namespace VEnv

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. The inhabited case: strengthening by substitution -/

/-- A `LiftN 1 k` witness is also an `InstN` witness for *any* substituted term: the entry
being stripped is not mentioned by anything in `Γ`, so instantiating it is the inverse of
lifting.  (`e₀` is unconstrained here; typing it is the caller's job.) -/
theorem _root_.Lean4Lean.Ctx.LiftN.exists_instN (e₀ : VExpr) :
    ∀ {k Γ Γ'}, Ctx.LiftN 1 k Γ Γ' → ∃ Γ₀ A₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As h =>
    match As, h with
    | [A], _ => exact ⟨Γ, A, .zero⟩
  | @succ k Γ Γ' A W ih =>
    obtain ⟨Γ₀, A₀, h⟩ := ih
    refine ⟨Γ₀, A₀, ?_⟩
    have := h.succ (A := A.liftN 1 k) (e₀ := e₀)
    rwa [inst_liftN] at this

/-- **Strengthening holds whenever the stripped hypothesis is inhabited.**  This is the
substitution argument: `(e.liftN 1 k).inst e₀ k = e`, so instantiating the variable away
turns a `Γ'`-conversion between lifted terms into a `Γ`-conversion between the terms. -/
theorem IsDefEqU.strengthen_of_instN (henv : Ordered env)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (H : env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k)) : env.IsDefEqU U Γ e1 e2 := by
  have := H.instN henv W h₀
  rwa [inst_liftN, inst_liftN] at this

/-- The same for the typed judgment. -/
theorem IsDefEq.strengthen_of_instN (henv : Ordered env)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (H : env.IsDefEq U Γ' (e1.liftN 1 k) (e2.liftN 1 k) (A.liftN 1 k)) :
    env.IsDefEq U Γ e1 e2 A := by
  have := H.instN henv h₀ W
  rwa [inst_liftN, inst_liftN, inst_liftN] at this


/-! ## 2. The statement, and its reflexive instance -/

/-- **Strengthening.**  The forward direction of `VEnv.IsDefEqU.weakN_iff`: a conversion
between two lifted terms in the larger context descends to the smaller one. -/
def Strengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- **Typing strengthening**: the reflexive instance of `Strengthening`, with the type left
existential.  This is `VExpr.WF.weakN_iff`'s forward direction, weakened so that the type is
not required to be lifted. -/
def TypingStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN n k) A → VExpr.WF env U Γ e

/-- **The `trans` residual.**  The one case of `Strengthening`'s induction whose induction
hypotheses are vacuous: the middle term `b` of a `trans` node is arbitrary, and in particular
need not be lifted, so neither premise is an instance of the statement being proved. -/
def TransStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEq U Γ' (e1.liftN n k) b A → env.IsDefEq U Γ' b (e2.liftN n k) A →
    env.IsDefEqU U Γ e1 e2

theorem Strengthening.typing (H : Strengthening env U) : TypingStrengthening env U :=
  fun W hΓ hΓ' h => H W hΓ hΓ' ⟨_, h⟩

theorem Strengthening.trans (H : Strengthening env U) : TransStrengthening env U :=
  fun W hΓ hΓ' h1 h2 => H W hΓ hΓ' ⟨_, h1.trans h2⟩

/-! ## 3. The coercion lemma: existential typing strengthening upgrades itself

`TypingStrengthening` says only that the term has *some* type downstairs.  It in fact implies
the *typed* form (`HasType.weakN_iff`'s forward direction), by applying itself to the type
ascription redex `(fun _ : A => #0) e`, whose well-typedness downstairs forces `e`'s type to
meet `A`.  This is why `TypingStrengthening` and not the typed form is the right unknown. -/

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.typed (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) : env.HasType U Γ e A := by
  have ⟨u, hA⟩ := H.isType henv hΓ'
  -- the ascription redex `(fun _ : A => #0) e`, upstairs
  have hlam : env.HasType U Γ' (.lam (A.liftN n k) (.bvar 0))
      (.forallE (A.liftN n k) ((A.liftN n k).lift)) := .lamDF hA (.bvar .zero)
  have happ := hlam.app H
  rw [inst_lift] at happ
  have hlift : VExpr.liftN n (.app (.lam A (.bvar 0)) e) k
      = .app (.lam (A.liftN n k) (.bvar 0)) (e.liftN n k) := rfl
  have wf : VExpr.WF env U Γ (.app (.lam A (.bvar 0)) e) := HT W hΓ hΓ' (hlift ▸ happ)
  have ⟨A'', B'', hf, ha⟩ := wf.app_inv henv hΓ
  have ⟨⟨u₀, hA₀⟩, _, hb⟩ := hf.lam_inv henv hΓ
  have hf' : env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lamDF hA₀ (.bvar .zero)
  have := (hf'.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact ha.defeqU_r henv hΓ (let ⟨_, h⟩ := this.1; ⟨_, h.symm⟩)

/-! ## 4. Inversion of `liftN` against a head constructor -/

section
variable {n k : Nat}

theorem _root_.Lean4Lean.VExpr.liftVar_eq_zero {j : Nat} (h : liftVar n j k = 0) : j = 0 := by
  unfold liftVar at h; split at h <;> omega

theorem _root_.Lean4Lean.VExpr.liftN_eq_bvar {e : VExpr} (h : e.liftN n k = .bvar i) :
    ∃ j, e = .bvar j ∧ i = liftVar n j k := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, rfl, h.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_sort {e : VExpr} (h : e.liftN n k = .sort l) :
    e = .sort l := by cases e <;> simp [VExpr.liftN] at h; exact h ▸ rfl

theorem _root_.Lean4Lean.VExpr.liftN_eq_const {e : VExpr} (h : e.liftN n k = .const c ls) :
    e = .const c ls := by cases e <;> simp [VExpr.liftN] at h; exact h.1 ▸ h.2 ▸ rfl

theorem _root_.Lean4Lean.VExpr.liftN_eq_app {e : VExpr} (h : e.liftN n k = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f = f'.liftN n k ∧ a = a'.liftN n k := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_lam {e : VExpr} (h : e.liftN n k = .lam A b) :
    ∃ A' b', e = .lam A' b' ∧ A = A'.liftN n k ∧ b = b'.liftN n (k+1) := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_forallE {e : VExpr} (h : e.liftN n k = .forallE A b) :
    ∃ A' b', e = .forallE A' b' ∧ A = A'.liftN n k ∧ b = b'.liftN n (k+1) := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

end

/-! ## 5. Row zero: eleven of twelve conversion rules close from `TypingStrengthening`

The induction for `Strengthening` must be on the conversion derivation — `HasType` is
*defined* as `IsDefEq e e A`, so even the reflexive instance has nothing else to induct on —
and its hypothesis and conclusion are both **asserted of** the endpoints.  By the criterion of
`docs/handoff-stratified.md` §5 that predicts failure at `trans`, whose middle term is
arbitrary; and indeed at `trans` both induction hypotheses are vacuous.

Every other rule closes, and `TypingStrengthening` is the only extra input they need. -/

variable! (henv : VEnv.WF env) in
theorem Strengthening.of_typing (HT : TypingStrengthening env U)
    (Htr : TransStrengthening env U) : Strengthening env U := by
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
  | trans h1 h2 _ _ =>
    exact fun W hΓ hΓ' eq1 eq2 => Htr W hΓ hΓ' (eq1 ▸ h1) (eq2 ▸ h2)
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

/-! ## 6. The typed form is the same statement

`IsDefEq.weakN_iff'` (the *typed* strengthening, which is what the 56 downstream consumers
actually use) is **not** a different problem from `IsDefEqU.weakN_iff`: the two are
inter-derivable given `TypingStrengthening`, which the untyped form contains outright.  In
particular, proving the typed statement "directly by induction" meets the very same `trans`
node — `IsDefEq.trans` shares its type between the two premises, so a *lifted* type is
inherited by both, but the middle *term* stays arbitrary. -/

/-- The typed form: `IsDefEq.weakN_iff'`'s forward direction. -/
def TypedStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) → env.IsDefEq U Γ e1 e2 A

variable! (henv : VEnv.WF env) in
theorem Strengthening.typed' (H : Strengthening env U) : TypedStrengthening env U := by
  intro n k Γ Γ' e1 e2 A W hΓ hΓ' h
  have ⟨_, H1⟩ := H W hΓ hΓ' ⟨_, h⟩
  refine IsDefEqU.defeqDF henv hΓ ?_ H1
  exact H W hΓ hΓ' ((H1.weakN henv W).uniqU henv hΓ' h.symm)

variable! (henv : VEnv.WF env) in
theorem Strengthening.of_typed (Ht : TypedStrengthening env U)
    (HT : TypingStrengthening env U) : Strengthening env U := by
  intro n k Γ Γ' e1 e2 W hΓ hΓ' h
  have ⟨_, h⟩ := h
  have ⟨_, hB⟩ := HT W hΓ hΓ' h.hasType.1
  have hu := (hB.weakN henv W).uniqU henv hΓ' h
  exact ⟨_, Ht W hΓ hΓ' (IsDefEqU.defeqDF henv hΓ' hu.symm h)⟩

variable! (henv : VEnv.WF env) in
/-- **The untyped and typed strengthening statements are equivalent.** -/
theorem Strengthening.iff_typed :
    Strengthening env U ↔ TypedStrengthening env U ∧ TypingStrengthening env U :=
  ⟨fun H => ⟨H.typed' henv, H.typing⟩, fun ⟨h1, h2⟩ => Strengthening.of_typed henv h1 h2⟩

/-! ## 7. `TypingStrengthening`'s own row zero — and it never meets `trans`

`TypingStrengthening` is the reflexive instance of `Strengthening`, but unlike the general
statement it has a *syntax-directed* judgment to induct on: `HasTypeStrong`
(`Theory/Typing/Strong.lean`), whose only non-syntax-directed rule, `defeq`, **keeps the same
term**, so its case closes by the induction hypothesis and no conversion derivation is ever
inspected.  It therefore *passes* the criterion of `docs/handoff-stratified.md` §5 outright.

What it costs instead is two **shape-descent** statements: a lifted term whose type upstairs
is a sort (resp. a Π) has a sort (resp. Π) type downstairs.  Those are the only residuals, and
they are together *equivalent* to `TypingStrengthening`. -/

/-- A lifted term typed at a sort upstairs is typed at a sort downstairs. -/
def SortDescend (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e : VExpr} {u : VLevel}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN n k) (.sort u) → VExpr.WF env U Γ e →
    ∃ u₀, env.HasType U Γ e (.sort u₀)

/-- A lifted function applied to a lifted argument upstairs is a function applied to an
argument of its domain downstairs. -/
def PiDescend (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a A B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
    VExpr.WF env U Γ f → VExpr.WF env U Γ a →
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀

theorem _root_.Lean4Lean.Lookup.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : Lookup Γ' (liftVar n i k) A') : ∃ A, A' = A.liftN n k ∧ Lookup Γ i A := by
  rw [← Lift.liftVar_consN_skipN] at H
  obtain ⟨A, rfl, h⟩ := H.weakU_inv (Ctx.liftN_iff_lift'.1 W)
  exact ⟨A, by rw [VExpr.lift'_consN_skipN], h⟩

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.of (HS : SortDescend env U) (HP : PiDescend env U) :
    TypingStrengthening env U := by
  suffices H : ∀ {Γ' e' A b}, env.HasTypeStrong U Γ' e' A b → ∀ {n k Γ e}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → e.liftN n k = e' →
      VExpr.WF env U Γ e by
    intro n k Γ Γ' e A W hΓ hΓ' h
    exact H (h.strong henv hΓ').hasType'.1 W hΓ hΓ' rfl
  intro Γ' e' A b H
  induction H with
  | bvar h _ _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨j, rfl, rfl⟩ := VExpr.liftN_eq_bvar eq
    obtain ⟨A₀, rfl, h'⟩ := Lookup.weakN_inv W h
    exact ⟨_, .bvar h'⟩
  | sort' h1 _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    cases VExpr.liftN_eq_sort eq
    exact ⟨_, .sortDF h1 h1 rfl⟩
  | const h1 h2 h3 _ _ _ _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    cases VExpr.liftN_eq_const eq
    exact ⟨_, .constDF h1 h2 h2 h3 (List.Forall₂.rfl fun _ _ => rfl)⟩
  | app _ _ _ _ _ hf ha _ _ _ _ ihf iha _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq
    have ⟨A₀, B₀, hf', ha'⟩ := HP W hΓ hΓ' hf.hasType ha.hasType
      (ihf W hΓ hΓ' rfl) (iha W hΓ hΓ' rfl)
    exact ⟨_, .appDF hf' ha'⟩
  | lam _ _ hA _ hbody _ ihA _ ihbody _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq
    have ⟨u₀, hA₀⟩ := HS W hΓ hΓ' hA.hasType (ihA W hΓ hΓ' rfl)
    have hΓ₁ : OnCtx (A₀::Γ) (env.IsType U) := ⟨hΓ, _, hA₀⟩
    have ⟨B₀, hb₀⟩ := ihbody W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ rfl
    exact ⟨_, .lamDF hA₀ hb₀⟩
  | forallE _ _ hA hbody ihA ihbody =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq
    have ⟨u₀, hA₀⟩ := HS W hΓ hΓ' hA.hasType (ihA W hΓ hΓ' rfl)
    have hΓ₁ : OnCtx (A₀::Γ) (env.IsType U) := ⟨hΓ, _, hA₀⟩
    have ⟨v₀, hb₀⟩ := HS W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ hbody.hasType
      (ihbody W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ rfl)
    exact ⟨_, .forallEDF hA₀ hb₀⟩
  | base _ ih => exact ih
  | defeq _ _ _ _ _ _ _ ih => exact ih

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.sortDescend (HT : TypingStrengthening env U) : SortDescend env U := by
  intro n k Γ Γ' e u W hΓ hΓ' h _
  have wf : VExpr.WF env U Γ (.forallE e (.sort .zero)) := HT W hΓ hΓ'
    (show env.HasType U _ ((VExpr.forallE e (.sort .zero)).liftN n k) _ from
      .forallEDF h (.sortDF trivial trivial rfl))
  have ⟨_, wf⟩ := wf
  exact (HasType.forallE_inv henv wf).1

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.piDescend (HT : TypingStrengthening env U) : PiDescend env U := by
  intro n k Γ Γ' f a A B W hΓ hΓ' hf ha _ _
  have wf : VExpr.WF env U Γ (.app f a) :=
    HT W hΓ hΓ' (show env.HasType U _ ((VExpr.app f a).liftN n k) _ from .appDF hf ha)
  exact wf.app_inv henv hΓ

variable! (henv : VEnv.WF env) in
/-- **`TypingStrengthening` is exactly the two shape-descent statements.** -/
theorem TypingStrengthening.iff_descend :
    TypingStrengthening env U ↔ SortDescend env U ∧ PiDescend env U :=
  ⟨fun H => ⟨H.sortDescend henv, H.piDescend henv⟩, fun ⟨h1, h2⟩ => TypingStrengthening.of henv h1 h2⟩

/-! ## 8. Capstone

Collecting §5 and §7: the target is **exactly** two shape-descent statements plus the `trans`
case.  Nothing else in the twelve conversion rules or the eight typing rules is open. -/

variable! (henv : VEnv.WF env) in
theorem Strengthening.iff_descend :
    Strengthening env U ↔
      SortDescend env U ∧ PiDescend env U ∧ TransStrengthening env U :=
  ⟨fun H => ⟨TypingStrengthening.sortDescend henv H.typing,
      TypingStrengthening.piDescend henv H.typing, H.trans⟩,
   fun ⟨h1, h2, h3⟩ => Strengthening.of_typing henv (TypingStrengthening.of henv h1 h2) h3⟩

/-! ## 9. Correction to §8: `TransStrengthening` **is** the target, and the residual is one
statement, not two

Two one-line facts.  Both change what §5 and §8 say.

**(a) `TransStrengthening` is not a residual — it is `Strengthening` itself.**  Instantiate
its middle term `b` at `e2.liftN n k` and its second premise at reflexivity, which the first
premise already supplies (`IsDefEq.hasType.2`).  So `Strengthening ↔ TransStrengthening`
(`Strengthening.iff_trans`), the `←` direction of §8's capstone never uses `SortDescend` or
`PiDescend` (`Strengthening.of_trans_only`), and §5's `Strengthening.of_typing` is provable
from its *second* hypothesis alone.  What §5 really establishes is a **case analysis** — that
eleven of the twelve rules need nothing but `TypingStrengthening` — not a reduction of the
target to a smaller statement.  Read as a reduction, §8's capstone is a tautology.

**(b) The reflexive instance is exactly `PiDescend`.**  `SortDescend` is a consequence of
`PiDescend`: apply the latter to the closed identity function `fun (_ : Sort u) => _`, whose
domain is a sort by construction, at the argument `e`.  Together with §7 this gives
`TypingStrengthening ↔ PiDescend` — one statement, not two.
-/

/-- **`TransStrengthening` implies `Strengthening`.**  Take the middle term to be
`e2.liftN n k` and the second premise to be the reflexivity the first one already provides. -/
theorem TransStrengthening.strengthening (H : TransStrengthening env U) :
    Strengthening env U := fun W hΓ hΓ' h =>
  have ⟨_, h⟩ := h; H W hΓ hΓ' h h.hasType.2

/-- **The `trans` residual of §5 is the target.**  So it is not a reduction. -/
theorem Strengthening.iff_trans : Strengthening env U ↔ TransStrengthening env U :=
  ⟨Strengthening.trans, TransStrengthening.strengthening⟩

/-- §8's capstone, `←` direction, with its first two hypotheses deleted. -/
theorem Strengthening.of_trans_only (h3 : TransStrengthening env U) : Strengthening env U :=
  h3.strengthening

/-- **`PiDescend` implies `SortDescend`.**

The witness is the closed identity function `idU := fun (_ : Sort u) => _`, whose type
`Sort u → Sort u` is fixed by construction and, being closed, is its own lift.  `PiDescend` at
`idU` and the argument `e` returns *some* Π type `A₀ → B₀` for `idU` downstairs together with
`Γ ⊢ e : A₀`; Π-injectivity identifies `A₀` with `Sort u`.

This is the only place in the file where a *sort* is obtained from a *Π*, and it is why §7's
two shape-descent statements are really one.  The cost is `IsDefEqU.forallE_inv`, which §3, §5
and §6 already consume. -/
theorem PiDescend.sortDescend (henv : VEnv.WF env) (HP : PiDescend env U) :
    SortDescend env U := by
  intro n k Γ Γ' e u W hΓ hΓ' h he
  have ⟨_, hsu⟩ := h.isType henv hΓ'
  have hu : u.WF U := hsu.sort_inv henv.ordered
  have hidf : ∀ {Δ : List VExpr}, env.HasType U Δ (.lam (.sort u) (.bvar 0))
      (.forallE (.sort u) ((VExpr.sort u).lift)) := .lamDF (.sortDF hu hu rfl) (.bvar .zero)
  have hlift : (VExpr.lam (.sort u) (.bvar 0)).liftN n k = .lam (.sort u) (.bvar 0) := by
    simp [VExpr.liftN, liftVar]
  have ⟨A₀, B₀, hf, ha⟩ := HP W hΓ hΓ' (hlift ▸ hidf) h ⟨_, hidf⟩ he
  have ⟨⟨_, hA₀⟩, _⟩ := (hidf.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact ⟨u, ha.defeqU_r henv hΓ ⟨_, hA₀.symm⟩⟩

variable! (henv : VEnv.WF env) in
/-- **The reflexive instance of the target is exactly one statement.** -/
theorem TypingStrengthening.iff_piDescend : TypingStrengthening env U ↔ PiDescend env U :=
  ⟨fun H => H.piDescend henv, fun H => TypingStrengthening.of henv (H.sortDescend henv) H⟩

/-! ## 10. The bridge to `IsDefEqU.weakN_iff` — the development's statement is the hole's

`Strengthening` carries **two** context hypotheses, `OnCtx Γ` and `OnCtx Γ'`.  The `sorry` at
`Theory/Typing/UniqueTyping.lean:174` carries only `OnCtx Γ'`.  An extra hypothesis makes
`Strengthening` a *weaker* statement, so §1–§9 do not by themselves discharge the hole: the
missing step is `OnCtx Γ' → OnCtx Γ`, which is `OnCtx.weakN_inv` — and that theorem is
downstream of the very `sorry` we are trying to close.

It is recoverable, and the recovery is not circular.  `OnCtx.weakN_inv`'s induction applies
strengthening only at **strictly smaller** `Ctx.LiftN` witnesses, so an induction on the
witness may assume `OnCtx Γ` for the tail while proving it for the head.  The head step needs
a *sort* downstairs, not merely well-formedness, and that is `SortDescend` — which
`Strengthening` supplies through `TypingStrengthening.sortDescend`, sorry-free.

The upshot, `Strengthening.iff_target`: the 500 lines above are about exactly the hole, with
no hypothesis to spare. -/

/-- `OnCtx` of a suffix.  (`OnCtx.append_right` is the same statement, but it lives in
`Theory/Inductive/Lemmas.lean`, which is not in this file's import closure.) -/
private theorem onCtx_of_append {P} :
    ∀ {As Γ : List VExpr}, OnCtx (As ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _::_, _, h => onCtx_of_append h.1

/-- **The target, exactly as stated at `Theory/Typing/UniqueTyping.lean:174`**: the forward
direction of `IsDefEqU.weakN_iff`, whose only context hypothesis is `OnCtx Γ'`. -/
def StrengtheningTarget (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- The easy direction: dropping a hypothesis. -/
theorem StrengtheningTarget.strengthening (H : StrengtheningTarget env U) :
    Strengthening env U := fun W _ hΓ' h => H W hΓ' h

variable! (henv : VEnv.WF env) in
/-- **`OnCtx.weakN_inv` from `Strengthening`.**  The one step `Strengthening` is missing
relative to the hole.  Induction on the lifting witness: the `succ` step already has
`OnCtx Γ` for the tail from the induction hypothesis, so both of `Strengthening`'s context
hypotheses are available where it is used. -/
theorem Strengthening.onCtx_inv (H : Strengthening env U) :
    ∀ {n k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) := by
  intro n k Γ Γ' W
  induction W with
  | @zero Γ As _ => exact onCtx_of_append
  | @succ k Γ Γ' A W ih =>
    intro h
    have hΓ := ih h.1
    have ⟨u, hA⟩ := h.2
    exact ⟨hΓ, TypingStrengthening.sortDescend henv H.typing W hΓ h.1 hA (H W hΓ h.1 ⟨_, hA⟩)⟩

variable! (henv : VEnv.WF env) in
/-- **`Strengthening` closes the hole.** -/
theorem Strengthening.target (H : Strengthening env U) : StrengtheningTarget env U :=
  fun W hΓ' h => H W (H.onCtx_inv henv W hΓ') hΓ' h

variable! (henv : VEnv.WF env) in
/-- **The development's statement and the hole's are the same statement.** -/
theorem Strengthening.iff_target : Strengthening env U ↔ StrengtheningTarget env U :=
  ⟨fun H => H.target henv, StrengtheningTarget.strengthening⟩

variable! (henv : VEnv.WF env) in
/-- Chaining §9: the hole is `TransStrengthening`, with no context hypothesis to spare. -/
theorem StrengtheningTarget.iff_trans : StrengtheningTarget env U ↔ TransStrengthening env U :=
  (Strengthening.iff_target henv).symm.trans Strengthening.iff_trans

/-! ## 11. One entry at a time

`Strengthening` strips `n` entries at once, but every tool in §1 is stated for `n = 1`:
`Ctx.LiftN.exists_instN` and `IsDefEqU.strengthen_of_instN` both take a `Ctx.LiftN 1 k`.  The
gap is closed here: a `Ctx.LiftN (n+1) k` factors as a `Ctx.LiftN n k` followed by a
`Ctx.LiftN 1 k` (`Ctx.LiftN.split_one`), and the factorisation is compatible with `liftN`
(`VExpr.liftN'_liftN_hi`), so **the one-entry statement implies the target**.

The one point of care is `OnCtx` of the *intermediate* context: it is not available from
either end for free, which is why the reduction is stated against `StrengtheningTarget`
(§10) rather than `Strengthening` — the target form manufactures its own `OnCtx` through
`Strengthening1.onCtx_inv`. -/

/-- A zero-entry lifting is the identity on contexts. -/
theorem _root_.Lean4Lean.Ctx.LiftN.eq_of_zero :
    ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 0 k Γ Γ' → Γ = Γ' := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As h => cases List.eq_nil_of_length_eq_zero h; rfl
  | succ _ ih => simp [← ih]

/-- **A lifting by `n+1` factors through a lifting by `n`.**  The extra entry is stripped
last, at the same position `k`. -/
theorem _root_.Lean4Lean.Ctx.LiftN.split_one :
    ∀ {n k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN (n+1) k Γ Γ' →
      ∃ Γ₁, Ctx.LiftN n k Γ Γ₁ ∧ Ctx.LiftN 1 k Γ₁ Γ' := by
  intro n k Γ Γ' W
  induction W with
  | @zero Γ As h =>
    match As, h with
    | A :: As, h =>
      refine ⟨As ++ Γ, .zero As (by simpa using h), .zero [A] rfl⟩
  | @succ k Γ Γ' A W ih =>
    obtain ⟨Γ₁, W1, W2⟩ := ih
    refine ⟨A.liftN n k :: Γ₁, W1.succ, ?_⟩
    have := W2.succ (A := A.liftN n k)
    rwa [VExpr.liftN'_liftN_hi] at this

/-- **The target, restricted to stripping a single entry.** -/
def Strengthening1 (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2

theorem Strengthening.one (H : Strengthening env U) : Strengthening1 env U :=
  fun W hΓ hΓ' h => H W hΓ hΓ' h

variable! (henv : VEnv.WF env) in
/-- §10's `onCtx_inv`, at `n = 1`.  Every use of the hypothesis in that proof — the
strengthening itself and the sort descent it feeds — is at the *same* lifting witness, so the
one-entry statement is enough. -/
theorem Strengthening1.onCtx_inv (H : Strengthening1 env U) :
    ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' →
      OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As _ => exact onCtx_of_append
  | @succ k Γ Γ' A W ih =>
    intro h
    have hΓ := ih h.1
    have ⟨u, hA⟩ := h.2
    have ⟨_, wf⟩ : VExpr.WF env U Γ (.forallE A (.sort .zero)) := H W hΓ h.1
      (show env.IsDefEqU U Γ' ((VExpr.forallE A (.sort .zero)).liftN 1 k)
          ((VExpr.forallE A (.sort .zero)).liftN 1 k) from
        ⟨_, .forallEDF hA (.sortDF trivial trivial rfl)⟩)
    exact ⟨hΓ, (HasType.forallE_inv henv wf).1⟩

variable! (henv : VEnv.WF env) in
/-- **Stripping one entry at a time is enough.** -/
theorem Strengthening1.target (H : Strengthening1 env U) : StrengtheningTarget env U := by
  intro n
  induction n with
  | zero =>
    intro k Γ Γ' e1 e2 W _ h
    cases W.eq_of_zero; simpa using h
  | succ n ih =>
    intro k Γ Γ' e1 e2 W hΓ' h
    obtain ⟨Γ₁, W1, W2⟩ := W.split_one
    refine ih W1 (H.onCtx_inv henv W2 hΓ') (H W2 (H.onCtx_inv henv W2 hΓ') hΓ' ?_)
    rwa [VExpr.liftN'_liftN_hi, VExpr.liftN'_liftN_hi]

variable! (henv : VEnv.WF env) in
/-- **The one-entry statement is the target.** -/
theorem Strengthening1.iff_target : Strengthening1 env U ↔ StrengtheningTarget env U :=
  ⟨fun H => H.target henv, fun H => Strengthening.one (StrengtheningTarget.strengthening H)⟩

/-! ## 12. The obstruction is exactly the uninhabited entries

§1 proves strengthening outright whenever the stripped entry has an inhabitant.  §11 makes
that applicable to the target.  Together they give a genuine *reduction* — one that adds a
hypothesis rather than reshuffling the existing ones:

    Strengthening1Uninhab  ⟹  StrengtheningTarget

`Strengthening1Uninhab` is the target restricted to strippings whose entry is **uninhabited
in its own prefix context**.  The case split is classical and one line; what it buys is that
any future argument may assume the entry has no inhabitant.

**Vacuity, stated exactly.**  The premises of `Strengthening1Uninhab` are satisfiable at
precisely the well-formed contexts with an uninhabited entry
(`onCtx_uninhab_premises`), and the dual is machine-checked here:
`strengtheningTarget_of_allInhabited` says that if *every* stripped entry were inhabited then
§1 alone would close the target.  So `Strengthening1Uninhab` is vacuous **iff** the target is
already proved — which is the strongest honest non-vacuity statement available, because
exhibiting an uninhabited type over a `VEnv.WF` environment is itself an open problem in this
tree: `VEnv.Consistent` (`Theory/Consistency.lean`) is a *definition*, and `leanTTConsistent`
is not proved anywhere here.  "No witness exhibited" is therefore not evidence either way. -/

/-- **The target, restricted to an uninhabited stripped entry.** -/
def Strengthening1Uninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
    env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2

theorem Strengthening1.uninhab (H : Strengthening1 env U) : Strengthening1Uninhab env U :=
  fun W hΓ hΓ' _ h => H W hΓ hΓ' h

/-- **The uninhabited case is the whole of the one-entry statement.**  Classical case split:
if the entry has an inhabitant, `IsDefEqU.strengthen_of_instN` closes it outright. -/
theorem Strengthening1Uninhab.strengthening1 (henv : Ordered env)
    (H : Strengthening1Uninhab env U) : Strengthening1 env U := by
  intro k Γ Γ' e1 e2 W hΓ hΓ' h
  by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ env.HasType U Γ₀ e₀ A₀
  · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
    exact IsDefEqU.strengthen_of_instN henv hI h₀ h
  · exact H W hΓ hΓ' (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) h

variable! (henv : VEnv.WF env) in
/-- **The uninhabited case is the whole target.** -/
theorem Strengthening1Uninhab.target (H : Strengthening1Uninhab env U) :
    StrengtheningTarget env U :=
  Strengthening1.target henv (H.strengthening1 henv.ordered)

variable! (henv : VEnv.WF env) in
theorem Strengthening1Uninhab.iff_target :
    Strengthening1Uninhab env U ↔ StrengtheningTarget env U :=
  ⟨fun H => H.target henv, fun H => (Strengthening1.uninhab
    (Strengthening.one (StrengtheningTarget.strengthening H)))⟩

variable! (henv : VEnv.WF env) in
/-- **The vacuity dual.**  If every stripped entry were inhabited, §1 alone would close the
target.  So §12's residual carries content exactly to the extent that uninhabited entries
exist. -/
theorem strengtheningTarget_of_allInhabited
    (hinh : ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) →
      ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ env.HasType U Γ₀ e₀ A₀) :
    StrengtheningTarget env U := by
  refine Strengthening1.target henv fun {k Γ Γ' e1 e2} W _ hΓ' h => ?_
  obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hinh W hΓ'
  exact IsDefEqU.strengthen_of_instN henv.ordered hI h₀ h

/-- **Premise satisfiability for §12's residual**, at the innermost position, where the
uninhabitedness hypothesis is literally "`A` has no inhabitant in `Γ`". -/
theorem onCtx_uninhab_premises {A : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.IsType U Γ A) (hemp : ∀ e₀, ¬ env.HasType U Γ e₀ A) :
    Ctx.LiftN 1 0 Γ (A :: Γ) ∧ OnCtx Γ (env.IsType U) ∧ OnCtx (A :: Γ) (env.IsType U) ∧
      ∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 (A :: Γ) Γ → ¬ env.HasType U Γ₀ e₀ A₀ :=
  ⟨.one, hΓ, ⟨hΓ, hA⟩, fun _ _ e₀ hI => by cases hI; exact hemp e₀⟩

end VEnv
end Lean4Lean
