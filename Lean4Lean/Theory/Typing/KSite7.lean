import Lean4Lean.Theory.Typing.KMeasure

/-!
# Site 7: `NormalEq.parRed` for `ParRedK`

`docs/handoff-krule.md` §V3 row 7 / §X5.  Work in progress; see the handoff for the
current status.
-/

namespace Lean4Lean
open Lean4Lean

namespace VEnv

open VExpr

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-- **Site 7**: `NormalEq.parRed`'s statement, for `ParRedK`. -/
def ParRedKStatement : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}, OnCtx Γ (IsType env univs) →
    NormalEq Γ e₁ e₂ → ParRedK Γ e₂ e₂' → ∃ e₁', ParRedKS Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂'

/-- Consistency check: where `EtaK` is empty, site 7 is `ChurchRosser.lean`'s own theorem. -/
theorem parRedKStatement_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : ParRedKStatement := by
  intro Γ e₁ e₂ e₂' hΓ H1 H2
  obtain ⟨e₁', h1, h2⟩ := H1.parRed hΓ (ParRedK.toParRed hno H2)
  exact ⟨e₁', h1.toK, h2⟩

theorem refParams_parRedKStatement : @ParRedKStatement refParams :=
  @parRedKStatement_of_no_etaK refParams (fun h => refParams_no_etaK h)


/-! ## The `etaR` inner induction

`ChurchRosser.lean:2085-2110`.  The inner lemma walks a sequence
`A::Γ ⊢ .app e.lift (.bvar 0) ≫* t` keeping

```
(∃ A', Γ ⊢ e ≫* A'.lam t ∧ Γ ⊢ A' ≡ A) ∨ (∃ e', Γ ⊢ e ≫* e' ∧ t = .app e'.lift (.bvar 0))
```

and `cases`es the next step.  `ParRedK` adds one case to that `cases`, and it is
`docs/handoff-krule.md` §V3 row 7 -- "the refutation's own witness configuration". -/

/-- **§V3 row 7, closed.**  The new `keta` case of the inner `cases a1` is one application of
`EtaK.under`: the invariant's second disjunct says the redex *is* the η-expansion of the
lift of a downstairs term, which is exactly the premise `EtaK.under` consumes, so the whole
`keta` step relocates downstairs and lands in the **first** disjunct with `A' := A`.

Nothing is inverted: `hek` is passed to `EtaK.under` unchanged, and the contractum's own
development `hd` is re-wrapped by `ParRedK.lam`.  This is `ORCHESTRATOR.md` working rule 5
in its cheapest form. -/
theorem etaR_inner_keta {Γ : List VExpr} {e A B e' w t' : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (hA : Γ ⊢ A : .sort u)
    (l1 : Γ ⊢ e : .forallE A B) (h : ParRedKS Γ e e')
    (hek : EtaK (A::Γ) (.app e'.lift (.bvar 0)) w) (hd : ParRedK (A::Γ) w t') :
    (∃ A', ParRedKS Γ e (A'.lam t') ∧ Γ ⊢ A' ≡ A) ∨
      (∃ e'', ParRedKS Γ e e'' ∧ t' = .app e''.lift (.bvar 0)) :=
  .inl ⟨A, h.tail (.keta (.under (ParRedKS.hasType hΓ h l1) hek) (.lam ParRedK.rfl hd)),
    _, hA⟩


/-! ## The obstruction: the invariant's second disjunct cannot be kept on the nose

`etaR_inner_keta` needs `t = .app e'.lift (.bvar 0)` **syntactically**, because `EtaK.under`'s
premise is an `EtaK` step at the η-expansion of a *lift*.  So the invariant cannot be weakened
at that position -- and the two `ParRed.weakN_inv` calls that keep it there
(`ChurchRosser.lean:2092`, `:2098`) are exactly what `docs/handoff-krule.md` §W1 refutes.

The statement below is `weakN_inv` cut down to the single instance the `app` branch of the
inner `cases a1` uses: `n = 1`, `k = 0`, the subject a term of the binder's own Π-type.  It is
still false, at the same witness. -/

/-- `ParRed.weakN_inv` at exactly the instance `NormalEq.parRed`'s `etaR` inner induction
consumes: one binder, at the outside, on a term whose Π-domain is that binder. -/
def EtaRLiftInv : Prop :=
  ∀ {Γ : List VExpr} {A B e f₀ : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : .forallE A B → ParRedK (A::Γ) e.lift f₀ → ∃ g, ParRedK Γ e g ∧ f₀ = g.lift

/-- **The `etaR` inner induction's own instance of site 1 is false.**  Specialising §W1's
witness to `C := A₀` -- the binder is the term's own Π-domain, which is what the `etaR` case
supplies -- the step at `e.lift` concludes `.lam (kdom A₀ A₀) t`, a λ whose domain mentions
`.bvar 0` and is the lift of nothing.

So the on-the-nose second disjunct is not recoverable by any strengthening of the rule table,
and `etaR_inner_keta`'s premise is not available from `weakN_inv`.  That, and not §V3 row 7,
is what blocks the `etaR` case. -/
theorem not_etaRLiftInv_of_etaK
    {Γ : List VExpr} {e A₀ B₀ t : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (he : Γ ⊢ e : .forallE A₀ B₀)
    (hin : EtaK (A₀.lift :: A₀ :: Γ) (.app (VExpr.lift (VExpr.lift e)) (.bvar 0)) t) :
    ¬ EtaRLiftInv := by
  intro WI
  have ⟨⟨u, hA₀⟩, v, hB₀⟩ := (have ⟨_, h⟩ := he.isType henv hΓ; h.forallE_inv henv)
  have hΓC : OnCtx (A₀::Γ) (IsType env univs) := ⟨hΓ, _, hA₀⟩
  have hty : (A₀::Γ) ⊢ e.lift : .forallE A₀.lift (B₀.liftN 1 1) := he.weak henv
  have hB : (A₀.lift :: A₀ :: Γ) ⊢ B₀.liftN 1 1 : .sort v := hB₀.weakN henv (.succ .one)
  have hek : EtaK (A₀::Γ) e.lift (.lam (kdom A₀ A₀) t) :=
    EtaK.under_dom hΓC hty hB (kdom_defeq hA₀ hA₀).symm hin
  obtain ⟨g, -, heq⟩ := WI hΓ he (.keta hek .rfl)
  cases g <;> simp [VExpr.liftN] at heq
  exact kdom_ne_liftN heq.1

/-- Non-vacuity, split honestly: where `EtaK` is empty the specialised statement *holds* -- it
is `ChurchRosser.lean`'s own `ParRed.weakN_inv` -- so it is not refutable outright and `hin`
is load-bearing.  As always: no `Params` instance in this tree registers an `.app` pattern, so
`hin` has no witness here, and that is **not** evidence of truth. -/
theorem etaRLiftInv_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : EtaRLiftInv := by
  intro Γ A B e f₀ hΓ hty H
  have ⟨⟨u, hA⟩, v, hB⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  obtain ⟨g, hg, rfl⟩ := ParRed.weakN_inv (n := 1) (k := 0) hΓA
    .one (hty.weak henv) (ParRedK.toParRed hno H)
  exact ⟨g, hg.toK, rfl⟩

theorem refParams_etaRLiftInv : @EtaRLiftInv refParams :=
  @etaRLiftInv_of_no_etaK refParams (fun h => refParams_no_etaK h)


/-! ## `DomEq`: the reason, kept

`docs/handoff-krule.md` §X5 names the candidate: *"a relation `equal up to definitionally
equal λ-domains, plus `ProofEq` at the leaves`, for which the commutation with `ParRedK`
should be provable outright"*.  Measured against the source, that relation is exactly
**`NormalEq` with `etaL` and `etaR` deleted** -- the level congruences (`sortDF`, `constDF`)
are needed too, because `NormalEq.apply_instL` is where `KTable.kstep_liftN_inv_stepP`'s
`NormalEq` comes from, and they are congruences, not eta.

Why this is the right cut, and not merely a smaller relation:

* **It preserves head shape** (except at `proofIrrel`), so a redex stays a redex.  That is
  what `NormalEq` fails to do -- `etaR` relates a K-redex to a λ -- and it is why
  `NormalEq.parRed`'s `appDF × extra` case needs the whole `NormalEq.descend` machinery
  (`ChurchRosser.lean:1706`, the file's only hole).  `DomEq`'s `appDF × extra` case fires the
  same rule on the other side.
* **It is what the λ-domain obstruction actually produces.**  `kdom_normalEq_lam` closes §W1's
  witness with `NormalEq.lamDF`, which is a `DomEq` constructor.
* **`etaR` is exactly the constructor `not_parRedStatement_of_hK` exploits**
  (`KCanonical.lean:485`): the refutation's `h1` is `NormalEq.etaR`.
-/

/-- **`NormalEq` minus `etaL`/`etaR`.**  Constructors are `NormalEq`'s, verbatim. -/
inductive DomEq : List VExpr → VExpr → VExpr → Prop where
  | refl {Γ : List VExpr} {e A : VExpr} : Γ ⊢ e : A → DomEq Γ e e
  | sortDF {Γ : List VExpr} {l₁ l₂ : VLevel} :
    l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → DomEq Γ (.sort l₁) (.sort l₂)
  | constDF {Γ : List VExpr} {c : Lean.Name} {ci ls ls'} :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    DomEq Γ (.const c ls) (.const c ls')
  | appDF {Γ : List VExpr} {f₁ f₂ a₁ a₂ A B : VExpr} :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    DomEq Γ f₁ f₂ → DomEq Γ a₁ a₂ →
    DomEq Γ (.app f₁ a₁) (.app f₂ a₂)
  | lamDF {Γ : List VExpr} {A A₁ A₂ body₁ body₂ : VExpr} {u : VLevel} :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    DomEq (A::Γ) body₁ body₂ →
    DomEq Γ (.lam A₁ body₁) (.lam A₂ body₂)
  | forallEDF {Γ : List VExpr} {A A₁ A₂ B₁ B₂ : VExpr} {u v : VLevel} :
    Γ ⊢ A ≡ A₁ : .sort u → DomEq Γ A₁ A₂ →
    A::Γ ⊢ B₁ : .sort v → DomEq (A::Γ) B₁ B₂ →
    DomEq Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | proofIrrel {Γ : List VExpr} {p h h' : VExpr} :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    DomEq Γ h h'

/-- The embedding.  `DomEq` is a sub-relation of `NormalEq`, constructor for constructor. -/
theorem DomEq.toNormalEq {Γ : List VExpr} {e₁ e₂ : VExpr} (H : DomEq Γ e₁ e₂) :
    Γ ⊢ e₁ ≡ₚ e₂ := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 ih1 ih2
  | lamDF h1 h2 _ ih => exact .lamDF h1 h2 ih
  | forallEDF h1 _ h3 _ ih1 ih2 => exact .forallEDF h1 ih1 h3 ih2
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3

theorem DomEq.defeq {Γ : List VExpr} {e₁ e₂ : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H : DomEq Γ e₁ e₂) : Γ ⊢ e₁ ≡ e₂ := H.toNormalEq.defeq hΓ

theorem DomEq.symm : ∀ {Γ : List VExpr} {e₁ e₂ : VExpr},
    DomEq Γ e₁ e₂ → OnCtx Γ (IsType env univs) → DomEq Γ e₂ e₁ := by
  intro Γ e₁ e₂ H
  induction H with intro hΓ
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | lamDF h1 h2 _ ih => exact .lamDF h2 h1 (ih ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := (⟨hΓ, _, h1.hasType.1⟩ : OnCtx (_::_) (IsType env univs))
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

theorem DomEq.hasType {Γ : List VExpr} {e₁ e₂ A : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H : DomEq Γ e₁ e₂) (h : Γ ⊢ e₁ : A) : Γ ⊢ e₂ : A :=
  (H.defeq hΓ).of_l henv hΓ h |>.hasType.2


/-! ### Shape preservation, with the proof escape

`DomEq` preserves the head shape of the right-hand side **except** at `proofIrrel`, and there
the escape is `KEta.ProofEq` -- the same escape `KetaLiftInvS` carries, and it is stable under
a development of either side (`ProofEq.parRedK_l`).  This is the property `NormalEq` lacks:
`NormalEq.etaR` relates an application to a λ. -/

theorem DomEq.app_inv_r {Γ : List VExpr} {e₁ f₂ a₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : DomEq Γ e₁ (.app f₂ a₂)) :
    (∃ f₁ a₁ A B, e₁ = .app f₁ a₁ ∧ Γ ⊢ f₁ : .forallE A B ∧ Γ ⊢ f₂ : .forallE A B ∧
        Γ ⊢ a₁ : A ∧ Γ ⊢ a₂ : A ∧ DomEq Γ f₁ f₂ ∧ DomEq Γ a₁ a₂) ∨
      ProofEq Γ e₁ (.app f₂ a₂) := by
  cases H with
  | refl h =>
    obtain ⟨A, B, hf, ha⟩ := h.app_inv henv hΓ
    exact .inl ⟨_, _, A, B, rfl, hf, hf, ha, ha, .refl hf, .refl ha⟩
  | appDF h1 h2 h3 h4 d1 d2 => exact .inl ⟨_, _, _, _, rfl, h1, h2, h3, h4, d1, d2⟩
  | proofIrrel hP h1 h2 => exact .inr ⟨_, hP, h1, h2⟩

theorem DomEq.lam_inv_r {Γ : List VExpr} {e₁ A₂ body₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : DomEq Γ e₁ (.lam A₂ body₂)) :
    (∃ A A₁ body₁, ∃ u : VLevel, e₁ = .lam A₁ body₁ ∧ Γ ⊢ A ≡ A₁ : .sort u ∧
        Γ ⊢ A ≡ A₂ : .sort u ∧ DomEq (A::Γ) body₁ body₂) ∨
      ProofEq Γ e₁ (.lam A₂ body₂) := by
  cases H with
  | refl h =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := h.lam_inv henv hΓ
    exact .inl ⟨A₂, A₂, body₂, u, rfl, hA, hA, .refl hb⟩
  | lamDF h1 h2 d => exact .inl ⟨_, _, _, _, rfl, h1, h2, d⟩
  | proofIrrel hP h1 h2 => exact .inr ⟨_, hP, h1, h2⟩

theorem DomEq.const_inv_r {Γ : List VExpr} {e₁ : VExpr} {c : Lean.Name} {ls' : List VLevel}
    (H : DomEq Γ e₁ (.const c ls')) :
    (∃ ls, e₁ = .const c ls ∧ List.Forall₂ (· ≈ ·) ls ls') ∨ ProofEq Γ e₁ (.const c ls') := by
  cases H with
  | refl h => exact .inl ⟨ls', rfl, VLevel.forall₂_equiv_refl _⟩
  | constDF h1 h2 h3 h4 h5 => exact .inl ⟨_, rfl, h5⟩
  | proofIrrel hP h1 h2 => exact .inr ⟨_, hP, h1, h2⟩

theorem DomEq.sort_inv_r {Γ : List VExpr} {e₁ : VExpr} {l₂ : VLevel}
    (H : DomEq Γ e₁ (.sort l₂)) :
    (∃ l₁, e₁ = .sort l₁ ∧ l₁ ≈ l₂) ∨ ProofEq Γ e₁ (.sort l₂) := by
  cases H with
  | refl h => exact .inl ⟨l₂, rfl, VLevel.equiv_def'.2 rfl⟩
  | sortDF h1 h2 h3 => exact .inl ⟨_, rfl, h3⟩
  | proofIrrel hP h1 h2 => exact .inr ⟨_, hP, h1, h2⟩



/-- **The escape survives an application.**  If the two function sides are proofs, so are the
two applications: a `Prop`-valued Π has a `Prop` codomain (impredicativity), which is the same
step `ProofEq.forallE` takes for a binder.  Adapted from `NormalEq.appDF_proofIrrel`, with
`Params.sortUniq` discharging its `hsu` hypothesis. -/
theorem ProofEq.app {Γ : List VExpr} {f₁ f₂ a₁ a₂ A B : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f₁ : .forallE A B) (l3 : Γ ⊢ a₁ : A) (l4 : Γ ⊢ a₂ : A)
    (hd : Γ ⊢ a₁ ≡ a₂) (hp : ProofEq Γ f₁ f₂) :
    ProofEq Γ (.app f₁ a₁) (.app f₂ a₂) := by
  obtain ⟨P, hP, hf1, hf2⟩ := hp
  obtain ⟨u, hPBu⟩ := hf1.uniq henv hΓ l1
  have hu0 : u ≈ .zero := Params.sortUniq hΓ hPBu.hasType.1 hP
  obtain ⟨⟨uA, hA⟩, v, hB⟩ := IsType.forallE_inv henv.ordered ⟨u, hPBu.hasType.2⟩
  have himax : VLevel.imax uA v ≈ u := Params.sortUniq hΓ (hA.forallE hB) hPBu.hasType.2
  have hv0 : v ≈ .zero := VLevel.imax_eq_zero.1 (himax.trans hu0)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hB0 : (A::Γ) ⊢ B : .sort .zero :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA)
      (show VLevel.WF univs VLevel.zero from trivial) hv0).defeq hB
  have hBa : Γ ⊢ B.inst a₁ : .sort .zero := hB0.instN henv.ordered .zero l3
  have hf2' : Γ ⊢ f₂ : .forallE A B := hf2.defeqU_r henv hΓ ⟨_, hPBu⟩
  have hBab := IsDefEq.instDF henv.ordered hΓ hB (IsDefEqU.of_l henv hΓ hd l3)
  exact ⟨_, hBa, l1.app l3, hBab.defeq' (hf2'.app l4)⟩

theorem DomEq.weakN {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN n k Γ Γ') (H : DomEq Γ e1 e2) :
    DomEq Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W)
      (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ ih1 => exact .lamDF (h1.weakN henv W) (h2.weakN henv W) (ih1 W.succ)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN henv W) (ih1 W) (h3.weakN henv W.succ) (ih2 W.succ)
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)

theorem DomEq.instN {Γ₀ : List VExpr} {e₀ A₀ : VExpr} (h₀ : Γ₀ ⊢ e₀ : A₀) :
    ∀ {k : Nat} {Γ₁ Γ : List VExpr} {e1 e2 : VExpr}, Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
      DomEq Γ₁ e1 e2 → DomEq Γ (e1.inst e₀ k) (e2.inst e₀ k) := by
  intro k Γ₁ Γ e1 e2 W H
  induction H generalizing Γ k with
  | refl h => exact .refl (h.instN henv W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀)
      (h4.instN henv W h₀) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ ih1 => exact .lamDF (h1.instN henv h₀ W) (h2.instN henv h₀ W) (ih1 W.succ)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    exact .forallEDF (h1.instN henv h₀ W) (ih1 W) (h3.instN henv W.succ h₀) (ih2 W.succ)
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀)

theorem DomEq.instN_r {Γ₀ : List VExpr} {e₀ e₀' A₀ : VExpr}
    (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : DomEq Γ₀ e₀ e₀') :
    ∀ {e : VExpr} {k : Nat} {Γ₁ Γ : List VExpr} {A : VExpr},
      OnCtx Γ₁ (IsType env univs) → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ₁ ⊢ e : A →
      DomEq Γ (e.inst e₀ k) (e.inst e₀' k) := by
  intro e
  induction e with intro k Γ₁ Γ A hΓ₁ W H <;> dsimp [VExpr.inst]
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
    have e1 := ih1 hΓ₁ W h1; have hf := h1.instN henv W h₀
    have e2 := ih2 hΓ₁ W h2; have ha := h2.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .appDF hf (.defeqU_l henv hΓ (e1.defeq hΓ) hf) ha
      (.defeqU_l henv hΓ (e2.defeq hΓ) ha) e1 e2
  | lam A body ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ₁
    have hA := h1.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .lamDF hA (((ih1 hΓ₁ W h1).defeq hΓ).of_l henv hΓ hA)
      (ih2 (show OnCtx (_::_) (IsType env univs) from ⟨hΓ₁, _, h1⟩) W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    have hA := h1.instN henv W h₀
    exact .forallEDF hA (ih1 hΓ₁ W h1) (h2.instN henv W.succ h₀)
      (ih2 (show OnCtx (_::_) (IsType env univs) from ⟨hΓ₁, _, h1⟩) W.succ h2)

theorem DomEq.defeqDFC {Γ₀ : List VExpr} (H₀ : OnCtx Γ₀ (IsType env univs)) :
    ∀ {Γ₁ Γ₂ : List VExpr} {e1 e2 : VExpr}, IsDefEqCtx env univs Γ₀ Γ₁ Γ₂ →
      DomEq Γ₁ e1 e2 → DomEq Γ₂ e1 e2 := by
  intro Γ₁ Γ₂ e1 e2 W H
  induction H generalizing Γ₂ with
  | refl h => exact .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (.defeqDFC henv W h1) (.defeqDFC henv W h2)
      (.defeqDFC henv W h3) (.defeqDFC henv W h4) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ ih1 =>
    exact .lamDF (.defeqDFC henv W h1) (.defeqDFC henv W h2) (ih1 (W.succ h1.hasType.1))
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    exact .forallEDF (.defeqDFC henv W h1) (ih1 W)
      (.defeqDFC henv (W.succ h1.hasType.1) h3) (ih2 (W.succ h1.hasType.1))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (.defeqDFC henv W h1) (.defeqDFC henv W h2) (.defeqDFC henv W h3)

theorem DomEq.defeq_l {Γ : List VExpr} {A A' e1 e2 : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (W : Γ ⊢ A ≡ A' : .sort u)
    (H : DomEq (A::Γ) e1 e2) : DomEq (A'::Γ) e1 e2 := DomEq.defeqDFC hΓ (.succ .zero W) H

theorem DomEq.trans {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ {e₁ e₂ e₃ : VExpr}, DomEq Γ e₁ e₂ → DomEq Γ e₂ e₃ → DomEq Γ e₁ e₃ := by
  intro e₁ e₂ e₃ H1
  induction H1 generalizing e₃ with
  | refl h => exact id
  | sortDF l1 l2 l3 =>
    intro H2; cases H2 with
    | refl h => exact .sortDF l1 l2 l3
    | sortDF r1 r2 r3 => exact .sortDF l1 r2 (l3.trans r3)
    | proofIrrel hP h1 h2 =>
      exact .proofIrrel hP
        (HasType.defeqU_l henv hΓ ((DomEq.sortDF l1 l2 l3).defeq hΓ).symm h1) h2
  | constDF l1 l2 l3 l4 l5 =>
    intro H2; cases H2 with
    | refl h => exact .constDF l1 l2 l3 l4 l5
    | constDF _ _ r3 r4 r5 =>
      exact .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
    | proofIrrel hP h1 h2 =>
      exact .proofIrrel hP
        (HasType.defeqU_l henv hΓ ((DomEq.constDF l1 l2 l3 l4 l5).defeq hΓ).symm h1) h2
  | appDF l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    intro H2; cases H2 with
    | refl h => exact .appDF l1 l2 l3 l4 l5 l6
    | appDF r1 r2 r3 r4 r5 r6 =>
      exact .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
        ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4) (ih1 hΓ r5) (ih2 hΓ r6)
    | proofIrrel hP h1 h2 =>
      exact .proofIrrel hP
        (HasType.defeqU_l henv hΓ ((DomEq.appDF l1 l2 l3 l4 l5 l6).defeq hΓ).symm h1) h2
  | lamDF l1 l2 l3 ih =>
    intro H2; cases H2 with
    | refl h => exact .lamDF l1 l2 l3
    | lamDF r1 r2 r3 =>
      have aa := r1.trans_r henv hΓ l2.symm
      exact .lamDF l1 (aa.symm.trans_l henv hΓ r2)
        (ih ⟨hΓ, _, l1.hasType.1⟩ (DomEq.defeq_l hΓ aa r3))
    | proofIrrel hP h1 h2 =>
      exact .proofIrrel hP
        (HasType.defeqU_l henv hΓ ((DomEq.lamDF l1 l2 l3).defeq hΓ).symm h1) h2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    intro H2; cases H2 with
    | refl h => exact .forallEDF l1 l2 l3 l4
    | forallEDF r1 r2 r3 r4 =>
      have r4' := r4.defeq_l hΓ
        (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
      exact .forallEDF l1 (ih1 hΓ r2) l3 (ih2 ⟨hΓ, _, l1.hasType.1⟩ r4')
    | proofIrrel hP h1 h2 =>
      exact .proofIrrel hP
        (HasType.defeqU_l henv hΓ ((DomEq.forallEDF l1 l2 l3 l4).defeq hΓ).symm h1) h2
  | proofIrrel l1 l2 l3 =>
    intro H2; exact .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)


/-! ### A redex stays a redex

This is the property that replaces `NormalEq.descend`.  `ChurchRosser.lean:1477`'s own note
says the descent exists because the naive interface *"is refuted by `NormalEq.etaL`, which
relates a `.lam` to anything of Π type -- and no `.lam` matches any pattern; the same goes for
`NormalEq.proofIrrel`"*.  Deleting `etaL`/`etaR` removes the first counterexample; the second
survives, and it is exactly `ProofEq`, which `ProofEq.app` carries up an application spine.

The statement is at an `.app`-free pattern, which by `Params.pat_app_noApp` is all the
recursion ever sees: at such a pattern the recursion descends only the *function* spine (a
`.var` node's argument is a hole, unconstrained), so every escape is a function-side escape
and `ProofEq.app` closes it. -/

/-- **`DomEq` transports a pattern match, at an `.app`-free pattern.**  Either the other side
matches the *same* pattern -- with `≈`-related level lists and `DomEq`-related arguments -- or
both sides are proofs. -/
theorem Pattern.Matches.domEq_inv {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ {p : Pattern}, p.NoApp → ∀ {e e' : VExpr} {m1 m2}, p.Matches e m1 m2 → DomEq Γ e' e →
      (∃ m1' m2', p.Matches e' m1' m2' ∧ (∀ x, List.Forall₂ (· ≈ ·) (m1' x) (m1 x)) ∧
        (∀ a, DomEq Γ (m2' a) (m2 a))) ∨ ProofEq Γ e' e := by
  intro p hp e e' m1 m2 H
  induction H generalizing e' with
  | @const c ls =>
    intro D
    rcases D.const_inv_r with ⟨ls₀, rfl, hls⟩ | hpe
    · exact .inl ⟨_, nofun, .const, fun _ => hls, nofun⟩
    · exact .inr hpe
  | @var f f' f1 g1 a' _ ih =>
    intro D
    rcases D.app_inv_r hΓ with ⟨f'', a'', A, B, rfl, hf1, hf2, ha1, ha2, df, da⟩ | hpe
    · rcases ih hp df with ⟨m1', m2', hm, hl, hd⟩ | hpe
      · exact .inl ⟨m1', (·.elim a'' m2'), .var hm, hl, fun x => x.rec da hd⟩
      · exact .inr (ProofEq.app hΓ hf1 ha1 ha2 (da.defeq hΓ) hpe)
    · exact .inr hpe
  | app => exact absurd hp id


/-! ### The congruences a rule's right-hand side needs

`NormalEq.instL_congr`, `NormalEq.apply_instL` and `NormalEq.apply_pat` are the three places
site 1's `extra` and `keta` cases build a `NormalEq`.  All three are pure congruences -- their
proofs use `refl`, `sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF` and nothing else -- so
each has a `DomEq` form, obtained by the same induction. -/

theorem DomEq.instL_congr {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ {e A : VExpr} {ls ls' : List VLevel}, (∀ l ∈ ls, l.WF univs) →
      (∀ l ∈ ls', l.WF univs) → List.Forall₂ (· ≈ ·) ls ls' →
      Γ ⊢ e.instL ls : A → DomEq Γ (e.instL ls) (e.instL ls') := by
  intro e
  induction e generalizing Γ with
    intro A ls ls' hls hls' hll H <;> dsimp [VExpr.instL] at H ⊢
  | bvar i => exact .refl H
  | sort u => exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls') (VLevel.inst_congr rfl hll)
  | const c us =>
    have ⟨ci, h1, h2, h3⟩ := H.const_inv henv hΓ
    refine .constDF h1 h2 (fun l hl => ?_) h3 (VLevel.forall₂_inst_congr hll us)
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls'
  | app f a ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    exact .appDF hf (.defeqU_l henv hΓ ((ih1 hΓ hls hls' hll hf).defeq hΓ) hf)
      ha (.defeqU_l henv hΓ ((ih2 hΓ hls hls' hll ha).defeq hΓ) ha)
      (ih1 hΓ hls hls' hll hf) (ih2 hΓ hls hls' hll ha)
  | lam A body ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ
    exact .lamDF h1 (((ih1 hΓ hls hls' hll h1).defeq hΓ).of_l henv hΓ h1)
      (ih2 (show OnCtx (_::_) (IsType env univs) from ⟨hΓ, _, h1⟩) hls hls' hll h2)
  | forallE A B ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    exact .forallEDF h1 (ih1 hΓ hls hls' hll h1) h2
      (ih2 (show OnCtx (_::_) (IsType env univs) from ⟨hΓ, _, h1⟩) hls hls' hll h2)

open Pattern.RHS in
theorem DomEq.apply_instL {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) {p : Pattern}
    {m1 m1' : p.LPath → List VLevel} {m2 : p.Path → VExpr}
    (hls : ∀ lp, ∀ l ∈ m1 lp, l.WF univs) (hls' : ∀ lp, ∀ l ∈ m1' lp, l.WF univs)
    (hll : ∀ lp, List.Forall₂ (· ≈ ·) (m1 lp) (m1' lp)) :
    ∀ {r : p.RHS} {A : VExpr}, Γ ⊢ apply m1 m2 r : A →
      DomEq Γ (apply m1 m2 r) (apply m1' m2 r) := by
  intro r
  induction r with intro A he <;> simp [apply] at he ⊢
  | fixed c lp => exact .instL_congr hΓ (hls lp) (hls' lp) (hll lp) he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact .refl he

open Pattern.RHS in
theorem DomEq.apply_pat {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) {p : Pattern}
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (ih : ∀ a A, Γ ⊢ m2 a : A → DomEq Γ (m2 a) (m2' a)) :
    ∀ {r : p.RHS} {A : VExpr}, Γ ⊢ apply m1 m2 r : A →
      DomEq Γ (apply m1 m2 r) (apply m1 m2' r) := by
  intro r
  induction r with intro A he <;> simp [apply] at he ⊢
  | fixed c => exact .refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact ih path _ he


/-! ### `KStep` and `EtaK` transport along `DomEq`

This is what `EtaK.under` needs and `NormalEq` cannot give.  `EtaK.under` fires on the
η-expansion of a *lift*; under a `NormalEq` the function side stops being a lift (§W1), and
under a `DomEq` it stops being a lift too -- but it stays a **redex**, which is all `KStep`
and `EtaK.under` actually read. -/

/-- **A `K`-redex stays a `K`-redex under `DomEq`.**  The canonical major premise `c` is
reused verbatim -- `KStep`'s side condition is an `IsDefEq`, and `DomEq` supplies the extra
conversion -- so only the *function* spine has to be re-matched, and it is `.app`-free. -/
theorem KStep.domEq_inv {Γ : List VExpr} {u v w : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (D : DomEq Γ u v) (H : KStep Γ v w) :
    (∃ w', KStep Γ u w' ∧ DomEq Γ w' w) ∨ ProofEq Γ u v := by
  cases H with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
  obtain ⟨hnf, -⟩ := Params.pat_app_noApp hpat
  cases hm with
  | @app _ _ n1 n2 _ _ k1 k2 hmf hmc => ?_
  rcases D.app_inv_r hΓ with ⟨f', h', A, B, rfl, hf1, hf2, ha1, ha2, df, da⟩ | hpe
  case inr => exact .inr hpe
  rcases Pattern.Matches.domEq_inv hΓ hnf hmf df with ⟨g1, g2, hmf', hl, hd⟩ | hpe
  case inr => exact .inr (ProofEq.app hΓ hf1 ha1 ha2 (da.defeq hΓ) hpe)
  -- the two matches, old and new
  have hmold : (Pattern.app p₁ p₂).Matches (.app f c) (Sum.elim n1 k1) (Sum.elim n2 k2) :=
    .app hmf hmc
  have hmnew : (Pattern.app p₁ p₂).Matches (.app f' c) (Sum.elim g1 k1) (Sum.elim g2 k2) :=
    .app hmf' hmc
  have hfty : Γ ⊢ f' : .forallE A₀ B₀ := DomEq.hasType hΓ (df.symm hΓ) hf
  have hcty : Γ ⊢ c : A₀ := hdq.hasType.2
  have holdty : Γ ⊢ .app f c : B₀.inst c := hf.app hcty
  have hnewty : Γ ⊢ .app f' c : B₀.inst c := hfty.app hcty
  have hlsold := hmold.levelWF hΓ holdty
  have hlsnew := hmnew.levelWF hΓ hnewty
  have hlold : ∀ x, List.Forall₂ (· ≈ ·) (Sum.elim n1 k1 x) (Sum.elim g1 k1 x) := by
    rintro (x|x)
    · exact (hl x).flip.imp fun _ _ h => h.symm
    · exact VLevel.forall₂_equiv_refl _
  -- old -> new, at every right-hand side
  have stepD : ∀ (t : (Pattern.app p₁ p₂).RHS) {C},
      Γ ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim n1 k1) (Sum.elim n2 k2) t : C →
      DomEq Γ (Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim n1 k1) (Sum.elim n2 k2) t)
        (Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim g1 k1) (Sum.elim g2 k2) t) := by
    intro t C ht
    have d1 := DomEq.apply_instL hΓ hlsold hlsnew hlold (r := t) ht
    have d2 := DomEq.apply_pat hΓ (p := Pattern.app p₁ p₂)
      (m2 := Sum.elim n2 k2) (m2' := Sum.elim g2 k2)
      (fun a _ _ => by
        rcases a with a | a
        · exact (hd a).symm hΓ
        · obtain ⟨_, hh⟩ := hmc.hasType hΓ hcty a
          exact .refl hh)
      (r := t) (DomEq.hasType hΓ d1 ht)
    exact d1.trans hΓ d2
  have step : ∀ (t : (Pattern.app p₁ p₂).RHS) {C},
      Γ ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim n1 k1) (Sum.elim n2 k2) t : C →
      Γ ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim n1 k1) (Sum.elim n2 k2) t ≡
          Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim g1 k1) (Sum.elim g2 k2) t :=
    fun t _ ht => (stepD t ht).defeq hΓ
  have hcknew : Pattern.Check.OK (IsDefEqU env univs Γ) (p := Pattern.app p₁ p₂)
      (Sum.elim g1 k1) (Sum.elim g2 k2) r.2 := by
    refine hck.map_levels (fun x i y j hij => ?_) (fun a b hab => ?_)
    · exact ((VLevel.forall₂_getD (hlold x) i).symm.trans hij).trans
        (VLevel.forall₂_getD (hlold y) j)
    · obtain ⟨T, hT⟩ := hab
      exact ((step a hT.hasType.1).symm.trans henv hΓ ⟨_, hT⟩).trans henv hΓ (step b hT.hasType.2)
  have hdqnew : IsDefEq env univs Γ h' c A₀ :=
    ((da.defeq hΓ).of_l henv hΓ (DomEq.hasType hΓ (da.symm hΓ) hdq.hasType.1)).trans hdq
  have ⟨_, hwty⟩ := Params.pat_wf hpat hmold hΓ holdty hck
  exact .inl ⟨_, .mk hpat hmnew hcknew hfty hdqnew,
    (stepD r.1 hwty.hasType.2).symm hΓ⟩


/-- **An `EtaK` redex stays an `EtaK` redex under `DomEq`.**  The `under` layer costs nothing:
`DomEq` is a congruence for the η-expansion (`weakN` + `appDF`), and the domain `A` is carried
unchanged, so `EtaK.under` re-fires with the same domain.  The escape climbs the tower by
`ProofEq.forallE`, exactly as `etaKn_keta_liftN_inv`'s does.

Contrast `NormalEq`: `EtaK.not_lam` makes this **false** for `NormalEq`, because `NormalEq.etaR`
relates a K-redex of Π type to a λ, and no λ is an `EtaK` redex. -/
theorem EtaK.domEq_inv {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ {v w : VExpr}, EtaK Γ v w → ∀ {u : VExpr}, DomEq Γ u v →
      (∃ w', EtaK Γ u w' ∧ DomEq Γ w' w) ∨ ProofEq Γ u v := by
  intro v w H
  induction H with
  | @here Γ' e t hst =>
    intro u D
    rcases KStep.domEq_inv hΓ D hst with ⟨w', hk, hd⟩ | hpe
    · exact .inl ⟨w', .here hk, hd⟩
    · exact .inr hpe
  | @under Γ' e A B t hty hin ih =>
    intro u D
    have ⟨⟨uA, hA⟩, vB, hB⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv)
    have hΓA : OnCtx (A::Γ') (IsType env univs) := ⟨hΓ, _, hA⟩
    have huty : Γ' ⊢ u : .forallE A B := DomEq.hasType hΓ (D.symm hΓ) hty
    have hb0v : (A::Γ') ⊢ VExpr.app e.lift (.bvar 0) : B := by
      simpa [instN_bvar0] using HasType.app (hty.weak (B := A) henv) (.bvar .zero)
    have hb0u : (A::Γ') ⊢ VExpr.app u.lift (.bvar 0) : B := by
      simpa [instN_bvar0] using HasType.app (huty.weak (B := A) henv) (.bvar .zero)
    have Dsub : DomEq (A::Γ') (VExpr.app u.lift (.bvar 0)) (VExpr.app e.lift (.bvar 0)) :=
      .appDF (huty.weak henv) (hty.weak henv) (.bvar .zero) (.bvar .zero)
        (D.weakN .one) (.refl (.bvar .zero))
    rcases ih hΓA Dsub with ⟨t', hek', hd⟩ | hpe
    · exact .inl ⟨.lam A t', .under huty hek', .lamDF hA hA hd⟩
    · obtain ⟨P, hP, h1, h2⟩ := ProofEq.forallE hΓ hA hA hty hpe
      refine .inr ⟨P, hP, ?_, h2⟩
      exact HasType.defeqU_l henv hΓ ⟨_, IsDefEq.eta huty⟩ h1


theorem DomEq.wf_r {Γ : List VExpr} {e₁ e₂ : VExpr} (H : DomEq Γ e₁ e₂) :
    OnCtx Γ (IsType env univs) → ∃ A, Γ ⊢ e₂ : A := by
  induction H with intro hΓ
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sort h2⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .const h1 h3 (h5.length_eq.symm.trans h4)⟩
  | appDF h1 h2 h3 h4 _ _ => exact ⟨_, h2.app h4⟩
  | lamDF h1 h2 d ih =>
    have hΓA : OnCtx (_::_) (IsType env univs) := ⟨hΓ, _, h1.hasType.1⟩
    have ⟨_, hb⟩ := ih hΓA
    exact ⟨_, HasType.lam h2.hasType.2 (hb.defeqDFC henv (.succ .zero h2))⟩
  | @forallEDF _ A A₁ A₂ B₁ B₂ u v h1 h2 h3 h4 ih1 ih2 =>
    have hΓA : OnCtx (A::_) (IsType env univs) := ⟨hΓ, _, h1.hasType.1⟩
    have hA2 : _ ⊢ A₂ : .sort u :=
      HasType.defeqU_l henv hΓ (h2.defeq hΓ) h1.hasType.2
    have hB2 := DomEq.hasType hΓA h4 h3
    have hAA2 := h1.transU_l henv hΓ (h2.defeq hΓ)
    exact ⟨_, HasType.forallE hA2 (hB2.defeqDFC henv (.succ .zero hAA2))⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, h3⟩

/-- **Developing the holes of a right-hand side, under a `DomEq`.**  This is what replaces the
descent in the `extra` case: once the rule has fired on the left, the two contracta differ only
at the `.var` leaves, and `hcomm` -- the induction hypothesis of `DomEq.parRedK` at the matched
arguments -- closes each leaf.  The escape is again `ProofEq`. -/
theorem DomEq.rhs_develop {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) {p : Pattern}
    {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr}
    (hcomm : ∀ (a : p.Path) (x : VExpr), DomEq Γ x (m2 a) →
      ∃ z, ParRedKS Γ x z ∧ DomEq Γ z (m2' a))
    (hdq : ∀ (a : p.Path) A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ m2' a) :
    ∀ (t : p.RHS) {x : VExpr}, DomEq Γ x (Pattern.RHS.apply m1 m2 t) →
      ∃ z, ParRedKS Γ x z ∧ DomEq Γ z (Pattern.RHS.apply m1 m2' t) := by
  intro t
  induction t with intro x D <;> simp [Pattern.RHS.apply] at D ⊢
  | fixed c lp => exact ⟨x, .rfl, D⟩
  | var path => exact hcomm path x D
  | app t1 t2 ih1 ih2 =>
    rcases D.app_inv_r hΓ with ⟨x1, x2, A, B, rfl, hx1, hf2, hx2, ha2, d1, d2⟩ | hpe
    · obtain ⟨z1, hz1, dz1⟩ := ih1 d1
      obtain ⟨z2, hz2, dz2⟩ := ih2 d2
      refine ⟨.app z1 z2, ParRedKS.app hz1 hz2, ?_⟩
      exact .appDF (ParRedKS.hasType hΓ hz1 hx1) (DomEq.hasType hΓ dz1 (ParRedKS.hasType hΓ hz1 hx1))
        (ParRedKS.hasType hΓ hz2 hx2) (DomEq.hasType hΓ dz2 (ParRedKS.hasType hΓ hz2 hx2)) dz1 dz2
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      have h2' : Γ ⊢ Pattern.RHS.apply m1 m2 (Pattern.RHS.app t1 t2) : P := by
        simpa [Pattern.RHS.apply] using h2
      have hd := IsDefEqU.apply_pat hΓ hdq h2'
      simp [Pattern.RHS.apply] at hd
      exact ⟨x, .rfl, .proofIrrel hP h1 (HasType.defeqU_l henv hΓ hd h2)⟩


theorem DomEq.wf_l {Γ : List VExpr} {e₁ e₂ : VExpr} (hΓ : OnCtx Γ (IsType env univs))
    (H : DomEq Γ e₁ e₂) : ∃ A, Γ ⊢ e₁ : A := (H.symm hΓ).wf_r hΓ

theorem _root_.Lean4Lean.Pattern.Matches.const_shape {c : Lean.Name} {e m1 m2}
    (H : (Pattern.const c).Matches e m1 m2) : ∃ ls, e = .const c ls ∧ m1 = fun _ => ls := by
  cases H; exact ⟨_, rfl, rfl⟩

/-- A `.const` pattern has no holes, so the argument map is irrelevant: any one will do. -/
theorem _root_.Lean4Lean.Pattern.Matches.const' {c : Lean.Name} {ls} (m2 : (Pattern.const c).Path → VExpr) :
    (Pattern.const c).Matches (.const c ls) (fun _ => ls) m2 := by
  have h : m2 = nofun := funext fun a => nomatch a
  subst h; exact .const

/-- **The rule fires on the other side.**  At an `.app`-free registered pattern this is
`Matches.domEq_inv` plus a `Check.OK` transport; at an `.app` pattern it is `KStep.domEq_inv`
plus `ParRedK.hK` -- the `K` rule is what covers the case where the *major premise* is a proof
that no longer matches, which is exactly the configuration `KStep` was introduced for.  A
`.var` pattern is impossible (`Params.pat_not_var`). -/
theorem DomEq.extra_fire {Γ : List VExpr} (hΓ : OnCtx Γ (IsType env univs)) :
    ∀ {p : Pattern} {r : p.RHS × p.Check} {e0 e₁ A : VExpr} {m1 m2},
      Params.Pat p r → p.Matches e0 m1 m2 →
      Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 → Γ ⊢ e0 : A → DomEq Γ e₁ e0 →
      (∃ w', ParRedK Γ e₁ w' ∧ DomEq Γ w' (Pattern.RHS.apply m1 m2 r.1)) ∨ ProofEq Γ e₁ e0 := by
  intro p
  cases p with
  | var f => intro r e0 e₁ A m1 m2 hpat; exact absurd hpat Params.pat_not_var
  | app p₁ p₂ =>
    intro r e0 e₁ A m1 m2 hpat hm hck hty D
    cases hm with | @app _ f n1 n2 _ c k1 k2 hmf hmc => ?_
    have ⟨A₀, B₀, hf, hc⟩ := hty.app_inv henv hΓ
    have hks : KStep Γ (.app f c)
        (Pattern.RHS.apply (p := Pattern.app p₁ p₂) (Sum.elim n1 k1) (Sum.elim n2 k2) r.1) :=
      .mk hpat (.app hmf hmc) hck hf hc
    rcases KStep.domEq_inv hΓ D hks with ⟨w', hk, hd⟩ | hpe
    · exact .inl ⟨w', .hK hk, hd⟩
    · exact .inr hpe
  | const c =>
    intro r e0 e₁ A m1 m2 hpat hm hck hty D
    obtain ⟨ls, rfl, rfl⟩ := hm.const_shape
    obtain ⟨B, hty1⟩ := D.wf_l hΓ
    rcases D.const_inv_r with ⟨ls₀, rfl, hls⟩ | hpe
    case inr => exact .inr hpe
    have hmnew : (Pattern.const c).Matches (.const c ls₀) (fun _ => ls₀) m2 :=
      Pattern.Matches.const' m2
    have hlsold := hm.levelWF hΓ hty
    have hlsnew := hmnew.levelWF hΓ hty1
    have hlold : ∀ x : (Pattern.const c).LPath,
        List.Forall₂ (· ≈ ·) ((fun _ => ls) x) ((fun _ => ls₀) x) :=
      fun _ => hls.flip.imp fun _ _ h => h.symm
    have stepD : ∀ (t : (Pattern.const c).RHS) {C : VExpr},
        Γ ⊢ Pattern.RHS.apply (p := Pattern.const c) (fun _ => ls) m2 t : C →
        DomEq Γ (Pattern.RHS.apply (p := Pattern.const c) (fun _ => ls) m2 t)
          (Pattern.RHS.apply (p := Pattern.const c) (fun _ => ls₀) m2 t) :=
      fun t _ ht => DomEq.apply_instL hΓ hlsold hlsnew hlold (r := t) ht
    have hcknew : Pattern.Check.OK (IsDefEqU env univs Γ) (p := Pattern.const c)
        (fun _ => ls₀) m2 r.2 := by
      refine hck.map_levels (fun x i y j hij => ?_) (fun a b hab => ?_)
      · exact ((VLevel.forall₂_getD (hlold x) i).symm.trans hij).trans
          (VLevel.forall₂_getD (hlold y) j)
      · obtain ⟨T, hT⟩ := hab
        exact (((stepD a hT.hasType.1).defeq hΓ).symm.trans henv hΓ ⟨_, hT⟩).trans henv hΓ
          ((stepD b hT.hasType.2).defeq hΓ)
    have ⟨_, hwty⟩ := Params.pat_wf hpat hm hΓ hty hck
    exact .inl ⟨_, ParRedK.extra hpat hmnew hcknew (m2' := m2) (fun _ => ParRedK.rfl),
      (stepD r.1 hwty.hasType.2).symm hΓ⟩


theorem DomEq.forallE_inv_r {Γ : List VExpr} {e₁ A₂ B₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : DomEq Γ e₁ (.forallE A₂ B₂)) :
    (∃ A A₁ B₁, ∃ u v : VLevel, e₁ = .forallE A₁ B₁ ∧ Γ ⊢ A ≡ A₁ : .sort u ∧
        DomEq Γ A₁ A₂ ∧ (A::Γ) ⊢ B₁ : .sort v ∧ DomEq (A::Γ) B₁ B₂) ∨
      ProofEq Γ e₁ (.forallE A₂ B₂) := by
  cases H with
  | refl h =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := h.forallE_inv henv
    exact .inl ⟨A₂, A₂, B₂, u, v, rfl, hA, .refl hA, hB, .refl hB⟩
  | forallEDF h1 h2 h3 h4 => exact .inl ⟨_, _, _, _, _, rfl, h1, h2, h3, h4⟩
  | proofIrrel hP h1 h2 => exact .inr ⟨_, hP, h1, h2⟩

theorem ParRedKS.defeqDFC {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (IsType env univs))
    {Γ₁ Γ₂ : List VExpr} {e1 e2 A : VExpr} (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : ParRedKS Γ₁ e1 e2) : ParRedKS Γ₂ e1 e2 := by
  induction H with
  | rfl => exact .rfl
  | @tail b c h1 h2 ih =>
    exact ih.tail (h2.defeqDFC hΓ₀ W (ParRedKS.hasType (W.isType' hΓ₀) h1 h))


/-! ## The commutation, outright

`docs/handoff-krule.md` §X5's claim, discharged: `DomEq` commutes with `ParRedK` **with no
hypothesis at all** -- no `KTable`, no `PiTypeDescend`, no `KStepTail`, and no
`NormalEq.descend`.  Compare `NormalEq.parRed` (`ChurchRosser.lean:1989`), which needs the
whole descent machinery for its `appDF × extra` case and is *refuted* for `ParRed` by
`not_parRedStatement_of_hK` at its `etaR` case.

The three places `NormalEq` needs machinery and `DomEq` does not:

* `appDF × extra`: `DomEq` transports the match (`DomEq.extra_fire`), so the rule fires on
  the other side.  `NormalEq.etaL` relates a λ to a redex, and no λ matches a pattern -- that
  is `NormalEq.descend`'s reason for existing.
* `× keta`: `DomEq` transports the `EtaK` step (`EtaK.domEq_inv`).  `NormalEq.etaR` relates a
  K-redex to a λ, and `EtaK.not_lam` kills it.
* the top `.app` node of a rule: when the major premise is a proof that no longer matches, the
  `K` rule fires instead (`KStep.domEq_inv` inside `DomEq.extra_fire`).
-/

theorem DomEq.parRedK :
    ∀ {Γ : List VExpr} {e₂ e₂' : VExpr}, ParRedK Γ e₂ e₂' →
      ∀ {e₁ : VExpr}, OnCtx Γ (IsType env univs) → DomEq Γ e₁ e₂ →
        ∃ e₁', ParRedKS Γ e₁ e₁' ∧ DomEq Γ e₁' e₂' := by
  intro Γ e₂ e₂' H
  induction H with
  | bvar | sort | const => intro e₁ hΓ D; exact ⟨e₁, .rfl, D⟩
  | @app Γ f f' a a' hf ha ih1 ih2 =>
    intro e₁ hΓ D
    rcases D.app_inv_r hΓ with ⟨g, b, A, B, rfl, hg1, hf1, hb1, ha1, dg, db⟩ | hpe
    · obtain ⟨g', hg', dg'⟩ := ih1 hΓ dg
      obtain ⟨b', hb', db'⟩ := ih2 hΓ db
      have hg'ty := ParRedKS.hasType hΓ hg' hg1
      have hb'ty := ParRedKS.hasType hΓ hb' hb1
      exact ⟨.app g' b', ParRedKS.app hg' hb',
        .appDF hg'ty (DomEq.hasType hΓ dg' hg'ty) hb'ty (DomEq.hasType hΓ db' hb'ty) dg' db'⟩
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.app hf ha).hasType hΓ h2)⟩
  | @lam Γ A A' body body' hA hb ih1 ih2 =>
    intro e₁ hΓ D
    rcases D.lam_inv_r hΓ with ⟨A₀, A₁, body₁, u, rfl, d1, d2, db⟩ | hpe
    · have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, d2.hasType.2⟩
      have db' : DomEq (A::Γ) body₁ body := DomEq.defeq_l hΓ d2 db
      obtain ⟨z, hz, dz⟩ := ih2 hΓA db'
      obtain ⟨Bt, hb₁ty⟩ := db'.wf_l hΓA
      have hAA1 : Γ ⊢ A ≡ A₁ : .sort u := d2.symm.trans d1
      have hz' : ParRedKS (A₁::Γ) body₁ z :=
        ParRedKS.defeqDFC hΓ (.succ .zero hAA1) hb₁ty hz
      refine ⟨.lam A₁ z, ParRedKS.lam .rfl hz', ?_⟩
      exact .lamDF d1 (d2.trans_l henv hΓ (hA.defeq hΓ d2.hasType.2))
        (DomEq.defeq_l hΓ d2.symm dz)
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.lam hA hb).hasType hΓ h2)⟩
  | @forallE Γ A₂ A₂' B₂ B₂' hA hB ih1 ih2 =>
    intro e₁ hΓ D
    rcases D.forallE_inv_r hΓ with ⟨A, A₁, B₁, u, v, rfl, d1, dA, hB₁, dB⟩ | hpe
    · have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, d1.hasType.1⟩
      have hAA2 : Γ ⊢ A ≡ A₂ : .sort u := d1.transU_l henv hΓ (dA.defeq hΓ)
      have hΓA2 : OnCtx (A₂::Γ) (IsType env univs) := ⟨hΓ, _, hAA2.hasType.2⟩
      obtain ⟨zA, hzA, dzA⟩ := ih1 hΓ dA
      have dB2 : DomEq (A₂::Γ) B₁ B₂ := DomEq.defeq_l hΓ hAA2 dB
      obtain ⟨zB, hzB, dzB⟩ := ih2 hΓA2 dB2
      have hB₁' : (A₂::Γ) ⊢ B₁ : .sort v := hB₁.defeqDFC henv (.succ .zero hAA2)
      have hA2A1 : Γ ⊢ A₂ ≡ A₁ : .sort u := hAA2.symm.trans d1
      have hzB' : ParRedKS (A₁::Γ) B₁ zB :=
        ParRedKS.defeqDFC hΓ (.succ .zero hA2A1) hB₁' hzB
      have hB₁'' : (A₁::Γ) ⊢ B₁ : .sort v := hB₁.defeqDFC henv (.succ .zero d1)
      have hΓA1 : OnCtx (A₁::Γ) (IsType env univs) := ⟨hΓ, _, d1.hasType.2⟩
      refine ⟨.forallE zA zB, ParRedKS.forallE hzA hzB', ?_⟩
      exact .forallEDF (ParRedKS.defeq hΓ hzA d1.hasType.2) dzA
        (ParRedKS.hasType hΓA1 hzB' hB₁'') (DomEq.defeq_l hΓ hA2A1 dzB)
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.forallE hA hB).hasType hΓ h2)⟩
  | @beta Γ A b b' a a' hb ha ih1 ih2 =>
    intro e₁ hΓ D
    rcases D.app_inv_r hΓ with ⟨F, X, A₃, B₃, rfl, hF, hlam2, hX, ha2, dF, dX⟩ | hpe
    · rcases dF.lam_inv_r hΓ with ⟨A₀, A₁, b₁, u, rfl, d1, d2, db⟩ | hpe2
      · have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, d2.hasType.2⟩
        have db' : DomEq (A::Γ) b₁ b := DomEq.defeq_l hΓ d2 db
        obtain ⟨z, hz, dz⟩ := ih1 hΓA db'
        obtain ⟨y, hy, dy⟩ := ih2 hΓ dX
        obtain ⟨Bt, hb₁ty⟩ := db'.wf_l hΓA
        have hAA1 : Γ ⊢ A ≡ A₁ : .sort u := d2.symm.trans d1
        have hz' : ParRedKS (A₁::Γ) b₁ z := ParRedKS.defeqDFC hΓ (.succ .zero hAA1) hb₁ty hz
        -- the argument's type: `A` and `A₃` agree because both type the same λ
        obtain ⟨⟨_, dA⟩, _, dB⟩ := hlam2.lam_inv henv hΓ
        obtain ⟨⟨_, u1⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ (hlam2.uniqU henv hΓ (dA.lam dB))
        have hyA : Γ ⊢ y : A := (ParRedKS.hasType hΓ hy hX).defeqU_r henv hΓ ⟨_, u1⟩
        obtain ⟨_, hbty⟩ := db'.wf_r hΓA
        refine ⟨z.inst y, ReflTransGen.tail
          (ParRedKS.app (ParRedKS.lam .rfl hz') hy) (.beta ParRedK.rfl ParRedK.rfl), ?_⟩
        refine (DomEq.instN hyA .zero dz).trans hΓ ?_
        exact DomEq.instN_r hyA dy hΓA .zero (hb.hasType hΓA hbty)
      · obtain ⟨P, hP, h1, h2⟩ := ProofEq.app hΓ hF hX ha2 (dX.defeq hΓ) hpe2
        exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.beta hb ha).hasType hΓ h2)⟩
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.beta hb ha).hasType hΓ h2)⟩
  | @extra Γ p r e0 m1 m2 m2' hpat hm hck hstep ih =>
    intro e₁ hΓ D
    obtain ⟨A, hty⟩ := D.wf_r hΓ
    rcases DomEq.extra_fire hΓ hpat hm hck hty D with ⟨w', hw, dw⟩ | hpe
    · have hdq : ∀ (a : p.Path) A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ m2' a :=
        fun a _ h => ⟨_, (hstep a).defeq hΓ h⟩
      obtain ⟨z, hz, dz⟩ := DomEq.rhs_develop hΓ (fun a x d => ih a hΓ d) hdq r.1 dw
      exact ⟨z, ReflTransGen.trans (.tail .rfl hw) hz, dz⟩
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.extra hpat hm hck hstep).hasType hΓ h2)⟩
  | @keta Γ e w w' hek htail ih =>
    intro e₁ hΓ D
    rcases EtaK.domEq_inv hΓ hek D with ⟨w₂, hek₂, dw⟩ | hpe
    · obtain ⟨z, hz, dz⟩ := ih hΓ dw
      exact ⟨z, ReflTransGen.trans (.tail .rfl (.keta hek₂ ParRedK.rfl)) hz, dz⟩
    · obtain ⟨P, hP, h1, h2⟩ := hpe
      exact ⟨_, .rfl, .proofIrrel hP h1 ((ParRedK.keta hek htail).hasType hΓ h2)⟩


/-- **A Π-typed term whose lift is a proof is a proof.**  Impredicativity again: the lifted
Π-type is a `Prop`, so its codomain is, so the unlifted Π-type is.  Needed by the `etaR`
inner induction's two proof escapes. -/
theorem ProofEq.strengthen_lift {Γ : List VExpr} {e A B P : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (hA : Γ ⊢ A : .sort u) (hB : (A::Γ) ⊢ B : .sort v)
    (he : Γ ⊢ e : .forallE A B)
    (hP : (A::Γ) ⊢ P : .sort .zero) (hX : (A::Γ) ⊢ e.lift : P) :
    ProofEq Γ e e := by
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hel : (A::Γ) ⊢ e.lift : (VExpr.forallE A B).lift := he.weak henv
  have huq := hX.uniqU henv hΓA hel
  have hpi0 : (A::Γ) ⊢ (VExpr.forallE A B).lift : .sort .zero :=
    HasType.defeqU_l henv hΓA huq hP
  simp only [VExpr.liftN] at hpi0
  obtain ⟨⟨u', hA'⟩, v', hB'⟩ := IsType.forallE_inv henv.ordered ⟨_, hpi0⟩
  have himax : VLevel.imax u' v' ≈ VLevel.zero := Params.sortUniq hΓA (hA'.forallE hB') hpi0
  have hv'0 : v' ≈ VLevel.zero := VLevel.imax_eq_zero.1 himax
  have hBw : (A.lift :: A :: Γ) ⊢ B.liftN 1 1 : .sort v := hB.weakN henv (.succ .one)
  have hΓA' : OnCtx (A.lift :: A :: Γ) (IsType env univs) := ⟨hΓA, _, hA'⟩
  have hv0 : v ≈ VLevel.zero := (Params.sortUniq hΓA' hBw hB').trans hv'0
  have hB0 : (A::Γ) ⊢ B : .sort .zero :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA)
      (show VLevel.WF univs VLevel.zero from trivial) hv0).defeq hB
  have hpi : Γ ⊢ VExpr.forallE A B : .sort (VLevel.imax u .zero) := hA.forallE hB0
  have hwu : VLevel.WF univs u := hA.sort_r henv.ordered hΓ
  refine ⟨_, ?_, he, he⟩
  have hwimax : VLevel.WF univs (VLevel.imax u .zero) := ⟨hwu, trivial⟩
  exact (IsDefEq.sortDF hwimax (show VLevel.WF univs VLevel.zero from trivial)
    (VLevel.imax_eq_zero.2 (VLevel.equiv_def'.2 rfl))).defeq hpi


/-! ## The `etaR` case of site 7, closed against a `DomEq` form of site 1

The invariant is the same three-way split the source carries, with the on-the-nose equation
`t = .app e'.lift (.bvar 0)` **split in two**: the argument stays `.bvar 0` on the nose (which
is what kills the `extra` case and what `EtaK.under` needs), and only the *function* is allowed
to move, by `DomEq` (which is what §W1's refutation forces).  The third disjunct is the proof
escape, discharged at the exit by `NormalEq.proofIrrel`.

Compare §X5, which says the circle is unbroken.  It is broken here: `etaR` needs only site 1,
and site 1 (§X3) does not need site 7. -/

/-- Site 1's statement at the `DomEq` conclusion, in the form the `etaR` induction consumes:
the subject is `DomEq` to a lift rather than a lift, and the development is a sequence.

**Collapse test, run:** instantiating `u := e1.liftN n k` and the `DomEq` at `refl` gives
`ParRedK`-site-1 at the `DomEq` conclusion outright, so this is *not* weaker than site 1 -- it
is site 1 plus a tail, exactly like `WeakNInvTail` (§X1).  What it is **not** is
`NormalEq.parRed`-shaped: it never mentions `NormalEq`, and `DomEq.parRedK` -- the commutation
it would otherwise need -- is proved above with no hypotheses. -/
def WeakNInvDS : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {u e1 e2' A : VExpr},
    OnCtx Γ' (IsType env univs) → Ctx.LiftN n k Γ Γ' →
    Γ' ⊢ e1.liftN n k : A → DomEq Γ' u (e1.liftN n k) → ParRedKS Γ' u e2' →
    ∃ e2, ParRedKS Γ e1 e2 ∧ DomEq Γ' e2' (e2.liftN n k)

theorem weakNInvDS_collapse (HD : WeakNInvDS) {n k : Nat} {Γ Γ' : List VExpr}
    {e1 e2' A : VExpr} (hΓ' : OnCtx Γ' (IsType env univs)) (W : Ctx.LiftN n k Γ Γ')
    (hty : Γ' ⊢ e1.liftN n k : A) (H : ParRedK Γ' (e1.liftN n k) e2') :
    ∃ e2, ParRedKS Γ e1 e2 ∧ DomEq Γ' e2' (e2.liftN n k) :=
  HD hΓ' W hty (.refl hty) (.tail .rfl H)

theorem etaR_inner (HD : WeakNInvDS) {Γ : List VExpr} {A B e : VExpr} {uA vB : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (hA : Γ ⊢ A : .sort uA) (hB : (A::Γ) ⊢ B : .sort vB)
    (l1 : Γ ⊢ e : .forallE A B) :
    ∀ {t : VExpr}, ParRedKS (A::Γ) (.app e.lift (.bvar 0)) t →
      (∃ A' c, ParRedKS Γ e (A'.lam c) ∧ Γ ⊢ A' ≡ A ∧ DomEq (A::Γ) t c) ∨
      (∃ e' f₀, ParRedKS Γ e e' ∧ t = .app f₀ (.bvar 0) ∧ DomEq (A::Γ) f₀ e'.lift) ∨
      ProofEq Γ e e := by
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  intro t H
  induction H with
  | rfl => exact .inr (.inl ⟨e, e.lift, .rfl, rfl, .refl (l1.weak henv)⟩)
  | @tail b t hseq hstep ih =>
    rcases ih with ⟨A', c, hred, hA', dc⟩ | ⟨e', f₀, hred, rfl, df⟩ | hpe
    · obtain ⟨z, hz, dz⟩ := DomEq.parRedK hstep hΓA (dc.symm hΓA)
      obtain ⟨_, hcty⟩ := dc.wf_r hΓA
      have hA'A : Γ ⊢ A' ≡ A : .sort uA := (hA'.of_r henv hΓ hA)
      have hz' : ParRedKS (A'::Γ) c z :=
        ParRedKS.defeqDFC hΓ (.succ .zero hA'A.symm) hcty hz
      exact .inl ⟨A', z, hred.trans (ParRedKS.lam .rfl hz'), hA', dz.symm hΓA⟩
    · have he'ty : Γ ⊢ e' : .forallE A B := ParRedKS.hasType hΓ hred l1
      have he'l : (A::Γ) ⊢ e'.lift : (VExpr.forallE A B).lift := he'ty.weak henv
      cases hstep with
      | @app _ _ f₁ _ a₁ c1 c2 =>
        cases c2 with
        | bvar => ?_
        | extra _ hm => cases hm
        | keta hek _ => exact absurd hek EtaK.not_bvar
        obtain ⟨e'', h1, d2⟩ := HD hΓA .one he'l df (.tail .rfl c1)
        exact .inr (.inl ⟨e'', f₁, hred.trans h1, rfl, d2⟩)
      | @beta _ A₀ body body' _ a₁' c1 c2 =>
        cases c2 with
        | bvar => ?_
        | extra _ hm => cases hm
        | keta hek _ => exact absurd hek EtaK.not_bvar
        obtain ⟨e'', h1, d2⟩ := HD hΓA .one he'l df
          (.tail .rfl (ParRedK.lam ParRedK.rfl c1))
        rcases (d2.symm hΓA).lam_inv_r hΓA with ⟨A₃, A₄, b₄, u₄, heq, q1, q2, db⟩ | hpe2
        · cases e'' <;> cases heq
          rename_i A₅ b₅
          have he''ty : Γ ⊢ VExpr.lam A₅ b₅ : .forallE A B := ParRedKS.hasType hΓ h1 he'ty
          obtain ⟨⟨_, dA5⟩, _, dB5⟩ := he''ty.lam_inv henv hΓ
          obtain ⟨⟨_, u1⟩, -⟩ :=
            IsDefEqU.forallE_inv henv hΓ (he''ty.uniqU henv hΓ (dA5.lam dB5))
          have hA5A : Γ ⊢ A₅ ≡ A := ⟨_, u1.symm⟩
          have hA3 : (A::Γ) ⊢ VExpr.bvar 0 : A₃ :=
            HasType.defeqU_r henv hΓA ⟨_, (q1.trans_l henv hΓA
              ((u1.weakN henv (Ctx.LiftN.one (A := A))).symm)).symm⟩ (.bvar .zero)
          refine .inl ⟨A₅, b₅, hred.trans h1, hA5A, ?_⟩
          have := DomEq.instN hA3 (k := 0) .zero (db.symm ⟨hΓA, _, q1.hasType.1⟩)
          simpa [instN_bvar0] using this
        · obtain ⟨P, hP, hX, -⟩ := hpe2
          have he''ty : Γ ⊢ e'' : .forallE A B := ParRedKS.hasType hΓ h1 he'ty
          have hpr := ProofEq.strengthen_lift hΓ hA hB he''ty hP hX
          obtain ⟨Q, hQ, hq, -⟩ := hpr
          refine .inr (.inr ⟨Q, hQ, ?_, ?_⟩) <;>
            exact HasType.defeqU_l henv hΓ
              ⟨_, (ParRedKS.defeq hΓ (hred.trans h1) l1).symm⟩ hq
      | extra b1 b2 b3 b4 =>
        cases b2 with
        | app _ h => cases h
        | var => cases Params.pat_not_var b1
      | keta hek hd =>
        have he'l2 := he'ty.weak (B := A) henv
        simp only [VExpr.liftN] at he'l2
        have hf₀ty := DomEq.hasType hΓA (df.symm hΓA) he'l2
        have Dsub : DomEq (A::Γ) (.app e'.lift (.bvar 0)) (.app f₀ (.bvar 0)) :=
          .appDF he'l2 hf₀ty (.bvar .zero) (.bvar .zero) (df.symm hΓA) (.refl (.bvar .zero))
        rcases EtaK.domEq_inv hΓA hek Dsub with ⟨w₂, hek₂, dw⟩ | hpe2
        · obtain ⟨z, hz, dz⟩ := DomEq.parRedK hd hΓA dw
          refine .inl ⟨A, z, ?_, ⟨_, hA⟩, dz.symm hΓA⟩
          exact (hred.tail (.keta (.under he'ty hek₂) ParRedK.rfl)).trans (ParRedKS.lam .rfl hz)
        · obtain ⟨P, hP, hq1, hq2⟩ := hpe2
          obtain ⟨Q, hQ, -, hq⟩ :=
            ProofEq.forallE hΓ hA hA he'ty (⟨P, hP, hq2, hq1⟩ : ProofEq _ _ _)
          refine .inr (.inr ⟨Q, hQ, ?_, ?_⟩) <;>
            exact HasType.defeqU_l henv hΓ ⟨_, (ParRedKS.defeq hΓ hred l1).symm⟩ hq
    · exact .inr (.inr hpe)


/-- **Site 7's `etaR` case, closed.**  `ChurchRosser.lean:2077-2110` for `ParRedK`, from
`WeakNInvDS` alone: the `keta` sub-case of the inner `cases` is `EtaK.under` (`etaR_inner`),
the `extra` sub-case is dead because the argument is `.bvar 0` on the nose, and the proof
escape is closed by `NormalEq.proofIrrel`.

The hypotheses are the induction hypothesis of `NormalEq.parRed` at `l2` (`ih1`) and the two
premises of `ParRedK.lam`, i.e. exactly what the case has in hand.  Nothing here is
`NormalEq.parRed` at a term other than `l2`'s, so the circle §X5 reports is broken. -/
theorem etaR_case (HD : WeakNInvDS) {Γ : List VExpr} {A B e eb A' b' : VExpr}
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
  · refine ⟨.lam A₂ c, hred, ?_⟩
    exact .lamDF (hA₂.of_r henv hΓ hA).symm (r1.defeq hΓ hA)
      (((dc.toNormalEq).symm hΓA).trans hΓA a2)
  · have he'ty : Γ ⊢ e' : .forallE A B := ParRedKS.hasType hΓ hred l1
    have he'l2 := he'ty.weak (B := A) henv
    simp only [VExpr.liftN] at he'l2
    have hf₀ty := DomEq.hasType hΓA (df.symm hΓA) he'l2
    have Dsub : DomEq (A::Γ) (.app e'.lift (.bvar 0)) (.app f₀ (.bvar 0)) :=
      .appDF he'l2 hf₀ty (.bvar .zero) (.bvar .zero) (df.symm hΓA) (.refl (.bvar .zero))
    have hne : NormalEq (A::Γ) (.app e'.lift (.bvar 0)) b' :=
      (Dsub.toNormalEq).trans hΓA a2
    refine ⟨e', hred, ?_⟩
    exact (NormalEq.etaR he'ty hne).trans hΓ
      (.lamDF hA (r1.defeq hΓ hA) (.refl (r2.hasType hΓA hebty)))
  · obtain ⟨P, hP, he1, -⟩ := hpe
    refine ⟨e, .rfl, .proofIrrel hP he1 ?_⟩
    have hlam' : Γ ⊢ VExpr.lam A' b' : .forallE A B := (ParRedK.lam r1 r2).hasType hΓ hlamty
    exact HasType.defeqU_r henv hΓ (l1.uniqU henv hΓ he1) hlam'


/-- The multi-step form of the commutation. -/
theorem DomEq.parRedKS {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H : ParRedKS Γ e₂ e₂') (D : DomEq Γ e₁ e₂) :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ DomEq Γ e₁' e₂' := by
  induction H with
  | rfl => exact ⟨e₁, .rfl, D⟩
  | @tail b c _ h2 ih =>
    obtain ⟨z, hz, dz⟩ := ih
    obtain ⟨z', hz', dz'⟩ := DomEq.parRedK h2 hΓ dz
    exact ⟨z', hz.trans hz', dz'⟩

theorem ParRedKS.toParRedS (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) {Γ : List VExpr} {e e' : VExpr}
    (H : ParRedKS Γ e e') : ParRedS Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail (h.toParRed hno)

/-- **The `refParams` consistency check.**  Where `EtaK` is empty, `WeakNInvDS` is
`ChurchRosser.lean`'s own `ParRed.weakN_inv` composed with the commutation proved above.  Note
what this does *not* use: `NormalEq.parRed`.  Contrast `refParams_weakNInvTailS` (§X2), whose
only route was site 7 followed by site 1 -- the circle. -/
theorem weakNInvDS_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : WeakNInvDS := by
  intro n k Γ Γ' u e1 e2' A hΓ' W hty D H
  obtain ⟨z, hz, dz⟩ := DomEq.parRedKS hΓ' H (D.symm hΓ')
  obtain ⟨e2, h1, rfl⟩ := ParRedS.weakN_inv hΓ' W hty (hz.toParRedS hno)
  exact ⟨e2, h1.toK, dz.symm hΓ'⟩

theorem refParams_weakNInvDS : @WeakNInvDS refParams :=
  @weakNInvDS_of_no_etaK refParams (fun h => refParams_no_etaK h)


/-- **Four of site 7's nine cases, closed outright.**  Whenever the `NormalEq` premise is in
fact a `DomEq` -- which is exactly `NormalEq`'s `refl`, `sortDF`, `constDF` and `proofIrrel`
constructors, none of which has a `NormalEq` sub-derivation -- site 7's conclusion follows from
`DomEq.parRedK` with no hypothesis.  In particular §V3 rows 5 (`constDF × extra`) and
§X5's `constDF × keta` are closed. -/
theorem parRedKStatement_of_domEq {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (H1 : DomEq Γ e₁ e₂) (H2 : ParRedK Γ e₂ e₂') :
    ∃ e₁', ParRedKS Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂' :=
  let ⟨z, hz, dz⟩ := DomEq.parRedK H2 hΓ H1; ⟨z, hz, dz.toNormalEq⟩


/-- **Working rule 2: the repair, run at the refutation's own witness.**
`KCanonical.not_parRedStatement_of_hK` refutes site 7 for `ParRed` at exactly this
configuration -- `H1 := NormalEq.etaR he (.refl hb0)`, `H2 := ParRed.lam .rfl (hK hstep)` --
and its five `cases hno` branches are what "nothing reaches the λ" means.  Here the same
configuration *produces a conclusion*, so the witness is visibly killed rather than merely no
longer derivable.  (`not_parRedStatement_of_hK_dead` kills its `hrig` hypothesis; this shows
the case it guards is discharged, not merely unreachable.) -/
theorem etaR_case_at_kstep (HD : WeakNInvDS) {Γ : List VExpr} {e A B t : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t) :
    ∃ e₁', ParRedKS Γ e e₁' ∧ NormalEq Γ e₁' (.lam A t) := by
  obtain ⟨⟨uA, hA⟩, vB, hB⟩ := (have ⟨_, h⟩ := he.isType henv hΓ; h.forallE_inv henv)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hb0 : (A::Γ) ⊢ VExpr.app e.lift (.bvar 0) : B := by
    simpa [instN_bvar0] using HasType.app (he.weak (B := A) henv) (.bvar .zero)
  exact etaR_case HD hΓ he (.refl hb0)
    (fun h => ⟨_, .tail .rfl h, .refl (h.hasType hΓA hb0)⟩) ParRedK.rfl (ParRedK.hK hstep)

end VEnv
end Lean4Lean
