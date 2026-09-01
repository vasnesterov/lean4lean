import Lean4Lean.Theory.Typing.KDescend

/-!
# `KDiamond`, and the two rule-table facts it needs

`Theory/Typing/KDescend.lean` reduces the K-rule's cost on the *descent* to a single
hypothesis, `hK : KStep ⊆ ParRed`, and names the residual that landing `hK` leaves behind:
`KDiamond`, "two K-steps at the same redex land `NormalEq`-close".  `KStep.uniq_defeq`
proves its free half (the two contracta are definitionally equal); the `≡ₚ` half is what this
file is about.

## Verdict

`KDiamond` is **not** provable from `Params` as it stands, and it is **not** refutable by any
witness this tree can build either.  What is proved here is the exact price:

> `KDiamond` follows from **two** facts about the rule table -- `KTable`
> (`docs/design-inductive.md` §7.6's lemma M3 / `pat_major_canonical`) and `KSmall`
> (§7.6's `pat_small`).  The proof below uses each exactly once, in disjoint branches of a
> dichotomy `KSmall` itself supplies.

The two branches are the two shapes the reference separates and this tree's `Pat`-indexed
generalisation had merged:

* **one constructor, large elimination** (`Eq`, `Acc`, `Quot` over a `Prop` carrier).  The two
  K-steps use the *same* rule and differ only in which canonical major premise they picked.
  `KTable` says that choice is canonical up to `≡ₚ`, which is Carneiro's `inv[p,h]` being a
  *term* built from the redex (`~/lean-type-theory/unique.tex:107`) rather than an
  existential.
* **several constructors** (`Or`, `And`, `Exists`).  The two K-steps use *different* rules,
  whose right-hand sides are unrelated -- `Or.rec`'s two minor premises share nothing.  What
  makes the contracta `≡ₚ` is not the rule table at all: it is that the redex is a **proof**,
  because a `Prop` with more than one constructor eliminates only into `Prop`.  That is
  `KSmall`, and `NormalEq.proofIrrel` closes the branch.

`Params.pat_uniq` supplies neither.  At two rules of one recursor the *argument* sides do not
intersect (different constructors), so its `p₂.inter p₃ = some p₄` premise is unsatisfiable
and the field never fires.  `Params.no_kpattern` (`KRule.lean`) is the same observation from
the other side.

## Two design points that were forced, both by satisfiability

1. **`kmajor` is indexed by the argument pattern**, not by the redex alone.  An earlier
   version took `kmajor : VExpr → VExpr → VExpr`; that version is **unsatisfiable** at a
   multi-constructor `Prop`.  At `Or.rec C ml mr h` with `h` a variable, both ι-rules fire,
   and a single canonical premise cannot match `(.const Or.inl).varN n` and
   `(.const Or.inr).varN n` at once.  Indexing by the pattern is also what
   `unique.tex:107`'s notation `inv[p,h]` says.

2. **`canon` carries a proof escape.**  Even per pattern, a canonical `Or.inl x₀` definable
   from `(f, h)` need not exist: `x₀ : A` cannot be built when only `B` holds.  In exactly
   that situation the redex is a proof and the K-rule is not needed, so the field concludes a
   disjunction.  Without the escape the field is again unsatisfiable -- the "staged over a
   premise the intended case makes unsatisfiable" shape.

   In the cases where the rule *is* needed the canonical form is definable, which is the
   content of §7.6's lemma M3: `Eq.refl α a` reads `α`, `a` off the recursor's own spine
   `f`; `Acc.intro x (fun y hy => Acc.inv h hy)` likewise, using `h`; and `Quot.mk r (invQ q)`
   likewise (`docs/handoff-krule.md` §4).

## Why there is no refutation, and why that is not evidence of truth

A counterexample would be a `Params` instance with two registered `.app` patterns sharing a
function side whose contracta are not `NormalEq`.  Both contracta are definitionally equal
(`KStep.uniq_defeq`) and both are `ParRed`-normal, so such an instance is a counterexample to
`IsDefEq.church_rosser` itself, not merely to `KDiamond`.  Building one needs an environment
with an `.app`-headed defeq rule, and `VEnv.WF` admits those only through `VDecl.induct` and
`VDecl.quot`; the two instances this tree has (`refParams`, `PropLoopParams`) register
`.const` patterns only, at which `KStep` is empty and every statement in this file holds
vacuously (`refParams_kSmall`, `refParams_kTable` below).  **That is a fact about the tree's
witnesses, not evidence that `KDiamond` holds.**
-/

namespace Lean4Lean

open VExpr

/-- **Two `.app`-free patterns matching one term are equal.**  A `NoApp` pattern is a
`.var`-chain over a `.const` leaf, and a term determines both the chain's length (its own
application depth) and the leaf (its head constant).

This is what lets the diamond conclude that two K-steps at one redex agree on the *function*
side before anything is known about the argument side: `Params.pat_app_noApp` makes both
function-side patterns `NoApp`, and they match the same `f`. -/
theorem Pattern.NoApp.matches_det {p p' : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (hp : p.NoApp) (hp' : p'.NoApp)
    (h : p.Matches e m1 m2) (h' : p'.Matches e m1' m2') : p = p' := by
  induction h generalizing p' with
  | const => cases h' with | const => rfl
  | @var f _ _ _ _ _ ih =>
    cases h' with
    | var h2 => exact congrArg Pattern.var (ih hp hp' h2)
    | app h1 h2 => exact hp'.elim
  | app _ _ _ _ => exact hp.elim

namespace VEnv

variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
set_option hygiene false in
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## M3: the canonical major premise -/

/-- **Lemma M3 (`docs/design-inductive.md` §7.6's `pat_major_canonical`), stated as a
definition rather than a check.**

`kmajor p₂ f h` is Carneiro's `inv[p,h]`: the constructor application that a stuck major
premise `h` is definitionally equal to, *computed from the redex*.  Two fields say what it is
for.

* `kmajor_liftN` -- it is a **syntactic function**, so it commutes with weakening.  This is
  the field that repairs `ParRed.weakN_inv` (`KTable.kstep_liftN_inv` below): at a lifted
  redex the canonical premise is a lifted term, hence so is the contractum computed from it.
  Without it `weakN_inv` is *false* -- `KStep`'s `c` is existentially quantified and may
  legitimately mention `.bvar k`, since proof irrelevance is exactly why the rule fires, and
  an ι-rule's right-hand side reads its arguments off `c`.

* `canon` -- every major premise the rule *can* fire at agrees with the canonical one, up to
  `NormalEq` on the matched data.  The relation is `≡ₚ`, not `=`: two canonical forms of one
  proof may differ syntactically (`Eq.refl α a` versus `Eq.refl α' a'` with `α`, `α'` δ-equal),
  so the equality form of this field is false and is not used.  Keeping it at `≡ₚ` is also
  what keeps `KStep` itself *liberal*, which `NormalEq.appDF_extra_of_descendV` needs: that
  proof fires the rule at the premise its `NormalEq` hypothesis hands it, which is not
  syntactically `kmajor`. -/
structure KTable where
  /-- The canonical major premise for the rule whose argument side is `p₂`, at redex
  `.app f h`.  Indexed by `p₂` because one function spine may carry several rules. -/
  kmajor : Pattern → VExpr → VExpr → VExpr
  /-- It is a syntactic function of the redex, so it commutes with weakening. -/
  kmajor_liftN : ∀ (p : Pattern) (f h : VExpr) (n k : Nat),
    kmajor p (f.liftN n k) (h.liftN n k) = (kmajor p f h).liftN n k
  /-- Either the redex is a proof -- in which case the K-rule is not needed, and this is the
  escape that makes the field satisfiable at multi-constructor `Prop`s -- or every firing
  major premise agrees with the canonical one up to `NormalEq`. -/
  canon : ∀ {Γ : List VExpr} {p₁ p₂ : Pattern}
      {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {f h c A₀ A : VExpr} {m1 m2},
    OnCtx Γ (IsType env univs) → Params.Pat (Pattern.app p₁ p₂) r →
    (Pattern.app p₁ p₂).Matches (.app f c) m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
    Γ ⊢ h ≡ c : A₀ → Γ ⊢ .app f c : A →
    (Γ ⊢ A : .sort .zero) ∨
    ∃ m1' m2', (Pattern.app p₁ p₂).Matches (.app f (kmajor p₂ f h)) m1' m2' ∧
      Γ ⊢ h ≡ kmajor p₂ f h : A₀ ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (m1 lp) (m1' lp)) ∧
      (∀ x, Γ ⊢ m2 x ≡ₚ m2' x)

/-- **`docs/design-inductive.md` §7.6's `pat_small`, in the form the diamond needs.**

Two registered rules with a common function side either *are* the same rule on the argument
side, or the redex is a proof.  In Lean this is the small-elimination restriction: a
`Prop`-valued inductive with more than one constructor eliminates only into `Prop`, so a
recursor with two ι-rules has a `Prop` motive.

It is not derivable from `Params`: `pat_uniq` cannot be applied, because two rules of one
recursor have argument sides that do not intersect.

**The `Γ ⊢ c ≡ c' : A₀` premise is not decoration.**  Without it the statement is *false* --
`Nat.rec`'s two ι-rules share a function side and `Nat.rec C z s Nat.zero` is not a proof.
What makes the field true is that two *definitionally equal* major premises cannot match two
different constructor patterns unless the type is a subsingleton: for `Nat` the premise is
unsatisfiable (constructor disjointness), and for a `Prop` with several constructors the
motive is `Prop`.  This is the "quantifier ranging wider than intended" shape, caught by
asking what the field must support rather than only what it must describe. -/
def KSmall : Prop :=
  ∀ {Γ : List VExpr} {p₁ p₂ p₂' : Pattern} {r r'} {f c c' A A₀ : VExpr} {m1 m2 m1' m2'},
    Params.Pat (Pattern.app p₁ p₂) r → Params.Pat (Pattern.app p₁ p₂') r' →
    (Pattern.app p₁ p₂).Matches (.app f c) m1 m2 →
    (Pattern.app p₁ p₂').Matches (.app f c') m1' m2' →
    Γ ⊢ c ≡ c' : A₀ →
    Γ ⊢ .app f c : A → p₂ = p₂' ∨ Γ ⊢ A : .sort .zero

/-! ## The diamond -/

/-- **`KDiamond` from M3 and small elimination.**

The proof is a dichotomy `KSmall` supplies, and it uses each hypothesis exactly once.

* The two K-steps agree on the *function* side unconditionally: `Params.pat_app_noApp` makes
  both function-side patterns `.app`-free and they match the same `f`, so
  `Pattern.NoApp.matches_det` identifies the patterns and `Pattern.Matches.uniq` identifies
  the data read off them.
* **Same argument pattern.**  `Params.pat_uniq` -- instantiated at `p₃ := p₁`, where `inter`
  is `inter_self` and the field's premise is for once satisfiable -- makes the two rules the
  same rule, and `KTable.canon` routes both matches through the canonical major premise.
* **Different argument patterns.**  `pat_uniq` is unusable and the rules are genuinely
  different, so nothing about the rule table can help.  `KSmall` says the redex is a proof
  and `NormalEq.proofIrrel` closes it -- as does either of `canon`'s own escapes. -/
theorem kDiamond_of (KT : KTable) (KS : KSmall) : KDiamond := by
  intro Γ e e₁ e₂ hΓ H1 H2
  cases H1 with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat1 hm1 hck1 hf1 hdq1 => ?_
  cases H2 with
  | @mk p₁' p₂' r' f' h' c' A₀' B₀' m1' m2' hpat2 hm2 hck2 hf2 hdq2 => ?_
  obtain ⟨hq1a, hq1b⟩ := Params.pat_app_noApp hpat1
  obtain ⟨hq2a, hq2b⟩ := Params.pat_app_noApp hpat2
  cases hm1 with | @app _ _ a1 b1 _ _ a2 b2 hmf1 hmc1 => ?_
  cases hm2 with | @app _ _ a1' b1' _ _ a2' b2' hmf2 hmc2 => ?_
  cases Pattern.NoApp.matches_det hq1a hq2a hmf1 hmf2
  obtain ⟨rfl, rfl⟩ := Pattern.Matches.uniq hmf1 hmf2
  have hfc : Γ ⊢ .app f c : B₀.inst c := hf1.app hdq1.hasType.2
  have hcc' : Γ ⊢ c ≡ c' : A₀ :=
    (IsDefEqU.trans henv hΓ ⟨_, hdq1.symm⟩ ⟨_, hdq2⟩).of_l henv hΓ hdq1.hasType.2
  have hfc' : Γ ⊢ .app f c' : B₀.inst c := (IsDefEq.appDF hf1 hcc').hasType.2
  have hx : Γ ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂)
      (Sum.elim a1 a2) (Sum.elim b1 b2) r.1 : B₀.inst c :=
    ((Params.pat_wf hpat1 (.app hmf1 hmc1) hΓ hfc hck1).of_l henv hΓ hfc).hasType.2
  have hy : Γ ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂')
      (Sum.elim a1 a2') (Sum.elim b1 b2') r'.1 : B₀.inst c :=
    ((Params.pat_wf hpat2 (.app hmf2 hmc2) hΓ hfc' hck2).of_l henv hΓ hfc').hasType.2
  refine (KS hpat1 hpat2 (.app hmf1 hmc1) (.app hmf2 hmc2) hcc' hfc).elim (fun hh => ?_)
    (fun hprop => .proofIrrel hprop hx hy)
  subst hh
  -- **Same rule.**  Route both matches through the canonical major premise.
  obtain ⟨_, _, hr⟩ := Params.pat_uniq hpat1 hpat2 Subpattern.refl (Pattern.inter_self _)
  cases eq_of_heq hr
  rcases KT.canon hΓ hpat1 (.app hmf1 hmc1) hck1 hdq1 hfc with hprop | ⟨n1, n2, hmk, hdqk, hlv1, hne1⟩
  case _ => exact .proofIrrel hprop hx hy
  rcases KT.canon hΓ hpat2 (.app hmf2 hmc2) hck2 hdq2 hfc' with hprop | ⟨n1', n2', hmk', _, hlv2, hne2⟩
  case _ => exact .proofIrrel hprop hx hy
  obtain ⟨rfl, rfl⟩ := Pattern.Matches.uniq hmk hmk'
  have hfk : Γ ⊢ VExpr.app f (KT.kmajor p₂ f h) : B₀.inst (KT.kmajor p₂ f h) :=
    hf1.app hdqk.hasType.2
  have hwk : ∀ lp, ∀ l ∈ n1 lp, VLevel.WF univs l := hmk.levelWF hΓ hfk
  have side : ∀ {u1 u2 : _ → _} {ru : (Pattern.app p₁ p₂).RHS} {t : VExpr},
      (Pattern.app p₁ p₂).Matches t u1 u2 →
      (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (n1 lp)) →
      (∀ x, Γ ⊢ u2 x ≡ₚ n2 x) →
      Γ ⊢ t : B₀.inst c →
      Γ ⊢ Pattern.RHS.apply u1 u2 ru : B₀.inst c →
      Γ ⊢ Pattern.RHS.apply u1 u2 ru ≡ₚ Pattern.RHS.apply n1 n2 ru := by
    intro u1 u2 ru t hmu hlv hne hte hty
    have s1 := NormalEq.apply_instL hΓ (hmu.levelWF hΓ hte) hwk hlv hty
    exact s1.trans hΓ (NormalEq.apply_pat hΓ (fun x _ _ => hne x)
      (HasType.defeqU_l henv hΓ (s1.defeq hΓ) hty))
  exact (side (.app hmf1 hmc1) hlv1 hne1 hfc hx).trans hΓ
    ((side (.app hmf2 hmc2) hlv2 hne2 hfc' hy).symm hΓ)

/-! ## The routine half of the wiring

`docs/handoff-krule.md` §R3 lists ten sites that a `kstep` constructor of `ParRed` breaks and
calls five of them routine.  Two of the five are the weakening and substitution lemmas, and
they are routine for a reason worth having as a lemma rather than as a claim: `KStep`'s
premises are each individually stable under `liftN`/`inst`, and `Pattern.RHS.liftN_apply` /
`Pattern.RHS.instN_apply` push the operation through the contractum.  Both are proved here,
so `ParRed.weakN` and `ParRed.instN` gain a one-line case. -/

/-- `KStep` is stable under weakening.  This is `ParRed.weakN`'s new case. -/
theorem KStep.weakN {Γ Γ' : List VExpr} {e e' : VExpr} {n k : Nat}
    (W : Ctx.LiftN n k Γ Γ') (H : KStep Γ e e') :
    KStep Γ' (e.liftN n k) (e'.liftN n k) := by
  cases H with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat hm hck hf hdq => ?_
  rw [Pattern.RHS.liftN_apply]
  show KStep Γ' (.app (f.liftN n k) (h.liftN n k)) _
  exact .mk hpat
    (by simpa [VExpr.liftN] using (Pattern.matches_liftN (n := n) (k := k)).2 ⟨m2, hm, fun _ => rfl⟩)
    (hck.weakN W r.2) (by simpa [VExpr.liftN] using hf.weakN henv W) (hdq.weakN henv W)

/-- `KStep` is stable under substitution.  This is `ParRed.instN`'s new case. -/
theorem KStep.instN {Γ₀ Γ₁ Γ : List VExpr} {a₀ A₀' e e' : VExpr} {k : Nat}
    (H₀ : HasType env univs Γ₀ a₀ A₀') (W : Ctx.InstN Γ₀ a₀ A₀' k Γ₁ Γ)
    (H : KStep Γ₁ e e') : KStep Γ (e.inst a₀ k) (e'.inst a₀ k) := by
  cases H with
  | @mk p₁ p₂ r f h c A₀ B₀ m1 m2 hpat hm hck hf hdq => ?_
  rw [Pattern.RHS.instN_apply]
  show KStep Γ (.app (f.inst a₀ k) (h.inst a₀ k)) _
  exact .mk hpat (by simpa [VExpr.inst] using Pattern.matches_instN (e₀ := a₀) (k := k) hm)
    (hck.instN W H₀ r.2) (by simpa [VExpr.inst] using hf.instN henv W H₀)
    (hdq.instN henv H₀ W)

/-! ## What M3 does for `ParRed.weakN_inv`, and what it cannot do -/

/-- **The repair of `ParRed.weakN_inv`'s K case -- in its `≡ₚ` form, which is the strongest
form available.**

`ParRed.weakN_inv` says a reduction of a *lifted* term is the lift of a reduction.  A K-step
breaks it: `KStep`'s canonical major premise `c` is existentially quantified and may mention
`.bvar k` legitimately, and an ι-rule's right-hand side reads its arguments off `c`.

`KTable.kmajor_liftN` repairs it, because the canonical premise is a *syntactic function* of
the redex: at a lifted redex it is a lifted term, so the contractum computed from it is a
lifted term, and `KTable.canon` says the actual contractum is `NormalEq` to that one.  (In
`canon`'s escape branch the redex is a proof and the witness is the redex itself, which is
trivially a lift.)

**The equality form is not recoverable, and that is not a limitation of this proof.**  A
K-step on a lifted redex may genuinely fire at a `c` mentioning `.bvar k`; nothing forbids it,
and the contractum is then not a lift of anything.  So `ParRed.weakN_inv`'s conclusion
`e2' = e2.liftN n k` must become `e2' ≡ₚ e2.liftN n k` once `KStep ⊆ ParRed`, and its one live
consumer -- `ChurchRosser.lean:2096`, `NormalEq.parRed`'s `etaR` case, which uses the equation
by `rfl` -- has to be re-proved.  The alternative, restricting `ParRed`'s K constructor to the
canonical premise, keeps the equality but breaks `NormalEq.appDF_extra_of_descendV`, which
fires the rule at the premise its `NormalEq` hypothesis hands it and cannot show that one is
canonical on the nose.  This is a correction to `docs/handoff-krule.md` §R3.1, which said M3
lets `weakN_inv` survive. -/
theorem KTable.kstep_liftN_inv (KT : KTable) {Γ' : List VExpr} {f h e' : VExpr} {n k : Nat}
    (hΓ' : OnCtx Γ' (IsType env univs))
    (H : KStep Γ' (.app (f.liftN n k) (h.liftN n k)) e') :
    ∃ e₀ : VExpr, Γ' ⊢ e' ≡ₚ e₀.liftN n k := by
  cases H with
  | @mk p₁ p₂ r _ _ c A₀ B₀ m1 m2 hpat hm hck hf hdq => ?_
  have hfc : Γ' ⊢ .app (f.liftN n k) c : B₀.inst c := hf.app hdq.hasType.2
  have hx : Γ' ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂) m1 m2 r.1 : B₀.inst c :=
    ((Params.pat_wf hpat hm hΓ' hfc hck).of_l henv hΓ' hfc).hasType.2
  rcases KT.canon hΓ' hpat hm hck hdq hfc with hprop | ⟨n1, n2, hmk, hdqk, hlv, hne⟩
  · -- the redex is a proof: the witness is the redex itself, which is a lift
    refine ⟨.app f h, ?_⟩
    have : Γ' ⊢ VExpr.app (f.liftN n k) (h.liftN n k) : B₀.inst c :=
      HasType.defeqU_l henv hΓ' ⟨_, (IsDefEq.appDF hf hdq).symm⟩ hfc
    exact .proofIrrel hprop hx (by simpa [VExpr.liftN] using this)
  rw [KT.kmajor_liftN] at hmk hdqk
  have hfk : Γ' ⊢ VExpr.app (f.liftN n k) ((KT.kmajor p₂ f h).liftN n k)
      : B₀.inst ((KT.kmajor p₂ f h).liftN n k) := hf.app hdqk.hasType.2
  have hmk' : (Pattern.app p₁ p₂).Matches
      ((VExpr.app f (KT.kmajor p₂ f h)).liftN n k) n1 n2 := by
    simpa [VExpr.liftN] using hmk
  obtain ⟨n2₀, hm₀, hn2⟩ := Pattern.matches_liftN.1 hmk'
  refine ⟨Pattern.RHS.apply (p := Pattern.app p₁ p₂) n1 n2₀ r.1, ?_⟩
  rw [Pattern.RHS.liftN_apply,
    (funext fun x => (hn2 x).symm : (fun x => (n2₀ x).liftN n k) = n2)]
  have s1 := NormalEq.apply_instL hΓ' (hm.levelWF hΓ' hfc) (hmk.levelWF hΓ' hfk) hlv hx
  exact s1.trans hΓ' (NormalEq.apply_pat hΓ' (fun x _ _ => hne x)
    (HasType.defeqU_l henv hΓ' (s1.defeq hΓ') hx))

/-- **The lifting inversion, with `canon`'s proof escape kept open.**

`kstep_liftN_inv_step` below collapses the escape branch to `NormalEq.proofIrrel` at once.
That discards the one fact the η-tower's *tail* needs: "both sides inhabit one `Prop`" is
stable under reduction of either side (subject reduction, then `proofIrrel` again), whereas a
bare `≡ₚ` is not.  Keeping the escape open is what lets `KMeasure.etaKn_keta_liftN_inv` carry
a `ParRedK` development down the tower without a `NormalEq.parRed`-shaped hypothesis, and it
is why site 1's residual is a K-only statement rather than site 7 itself
(`docs/handoff-krule.md` §X). -/
theorem KTable.kstep_liftN_inv_stepP (KT : KTable) {Γ Γ' : List VExpr}
    {f h e' A₁ B₁ : VExpr} {n k : Nat}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (hf₀ : Γ ⊢ f : .forallE A₁ B₁)
    (H : KStep Γ' (.app (f.liftN n k) (h.liftN n k)) e') :
    (∃ w₀, KStep Γ (.app f h) w₀ ∧ Γ' ⊢ e' ≡ₚ w₀.liftN n k) ∨
      (∃ P, Γ' ⊢ P : .sort .zero ∧ Γ' ⊢ e' : P ∧
        Γ' ⊢ (VExpr.app f h).liftN n k : P) := by
  cases H with
  | @mk p₁ p₂ r _ _ c A₀ B₀ m1 m2 hpat hm hck hf hdq => ?_
  have hfc : Γ' ⊢ .app (f.liftN n k) c : B₀.inst c := hf.app hdq.hasType.2
  have hx : Γ' ⊢ Pattern.RHS.apply (p := Pattern.app p₁ p₂) m1 m2 r.1 : B₀.inst c :=
    ((Params.pat_wf hpat hm hΓ' hfc hck).of_l henv hΓ' hfc).hasType.2
  rcases KT.canon hΓ' hpat hm hck hdq hfc with hprop | ⟨n1, n2, hmk, hdqk, hlv, hne⟩
  · exact .inr ⟨_, hprop, hx, by
      simpa [VExpr.liftN] using
        HasType.defeqU_l henv hΓ' ⟨_, (IsDefEq.appDF hf hdq).symm⟩ hfc⟩
  refine .inl ?_
  rw [KT.kmajor_liftN] at hmk hdqk
  have hfk : Γ' ⊢ VExpr.app (f.liftN n k) ((KT.kmajor p₂ f h).liftN n k)
      : B₀.inst ((KT.kmajor p₂ f h).liftN n k) := hf.app hdqk.hasType.2
  have hmk' : (Pattern.app p₁ p₂).Matches
      ((VExpr.app f (KT.kmajor p₂ f h)).liftN n k) n1 n2 := by
    simpa [VExpr.liftN] using hmk
  obtain ⟨n2₀, hm₀, hn2⟩ := Pattern.matches_liftN.1 hmk'
  have hn2eq : (fun x => (n2₀ x).liftN n k) = n2 := funext fun x => (hn2 x).symm
  -- the major premise, downstairs
  have hf₀' : Γ' ⊢ f.liftN n k : .forallE (A₁.liftN n k) (B₁.liftN n (k+1)) :=
    hf₀.weakN henv W
  obtain ⟨⟨_, hAA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ' (hf.uniqU henv hΓ' hf₀')
  have hh₀ : Γ ⊢ h : A₁ := (HasType.weakN_iff henv hΓ' W).1
    (hdq.hasType.1.defeqU_r henv hΓ' ⟨_, hAA⟩)
  have hdqD : Γ ⊢ h ≡ KT.kmajor p₂ f h : A₁ :=
    ((IsDefEqU.weakN_iff henv hΓ' W).1 ⟨_, hdqk⟩).of_l henv hΓ hh₀
  -- the rule's check obligations, transported and then strengthened
  have hstep : ∀ a : (Pattern.app p₁ p₂).RHS, ∀ {T},
      Γ' ⊢ Pattern.RHS.apply m1 m2 a : T →
      Γ' ⊢ Pattern.RHS.apply m1 m2 a ≡ₚ Pattern.RHS.apply n1 n2 a := by
    intro a T ha
    have s1 := NormalEq.apply_instL hΓ' (hm.levelWF hΓ' hfc) (hmk.levelWF hΓ' hfk) hlv ha
    exact s1.trans hΓ' (NormalEq.apply_pat hΓ' (fun x _ _ => hne x)
      (HasType.defeqU_l henv hΓ' (s1.defeq hΓ') ha))
  have hckN : r.2.OK (IsDefEqU env univs Γ') n1 n2 := by
    refine hck.map_levels (fun x i y j hij => ?_) (fun a b hab => ?_)
    · exact ((VLevel.forall₂_getD (hlv x) i).symm.trans hij).trans (VLevel.forall₂_getD (hlv y) j)
    · obtain ⟨T, hT⟩ := hab
      have ha := hstep a hT.hasType.1
      have hb := hstep b hT.hasType.2
      exact ((ha.defeq hΓ').symm.trans henv hΓ' ⟨_, hT⟩).trans henv hΓ' (hb.defeq hΓ')
  have hck₀ : r.2.OK (IsDefEqU env univs Γ) n1 n2₀ := by
    refine hckN.map (fun a b hab => (IsDefEqU.weakN_iff henv hΓ' W).1 ?_)
    rw [Pattern.RHS.liftN_apply, Pattern.RHS.liftN_apply, hn2eq]
    exact hab
  refine ⟨_, .mk hpat hm₀ hck₀ hf₀ hdqD, ?_⟩
  rw [Pattern.RHS.liftN_apply, hn2eq]
  exact hstep r.1 hx

/-- **The lifting inversion, with the downstairs step.**  `kstep_liftN_inv` above produces the
`NormalEq` half only; this produces the *reduction* too, which is what
`ParRed.weakN_inv`'s conclusion actually asks for.

The extra content over `kstep_liftN_inv` is three descents, all of them along
`IsDefEqU.weakN_iff` (`UniqueTyping.lean:172`, an existing hole of the tree):

* the rule's `Check` obligations, transported from the firing match to the canonical one by
  `NormalEq.apply_instL` + `NormalEq.apply_pat` (`Pattern.Check.OK.map_levels`) and then
  strengthened (`Pattern.Check.OK.map`);
* the major premise's conversion `h ≡ kmajor p₂ f h`;
* the spine function's Π-typing, which is **not** derivable here and is therefore a
  hypothesis (`hf₀`) -- `KEta.PiTypeDescend` is what supplies it, and
  `Theory/Typing/Strengthen.lean`'s `PiDescend` is its nearest relative.

The second disjunct is `canon`'s proof escape: there the redex is a proof, no downstairs step
exists or is needed, and the contractum is `NormalEq` to the redex itself. -/
theorem KTable.kstep_liftN_inv_step (KT : KTable) {Γ Γ' : List VExpr}
    {f h e' A₁ B₁ : VExpr} {n k : Nat}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓ' : OnCtx Γ' (IsType env univs))
    (W : Ctx.LiftN n k Γ Γ') (hf₀ : Γ ⊢ f : .forallE A₁ B₁)
    (H : KStep Γ' (.app (f.liftN n k) (h.liftN n k)) e') :
    (∃ w₀, KStep Γ (.app f h) w₀ ∧ Γ' ⊢ e' ≡ₚ w₀.liftN n k) ∨
      Γ' ⊢ e' ≡ₚ (VExpr.app f h).liftN n k := by
  rcases KT.kstep_liftN_inv_stepP hΓ hΓ' W hf₀ H with hl | ⟨_, hP, h1, h2⟩
  · exact .inl hl
  · exact .inr (.proofIrrel hP h1 h2)

/-! ## A third obstruction, and it is a refutation

`docs/handoff-krule.md` §R3's table lists `ChurchRosser.lean:2096` -- `NormalEq.parRed`'s
`etaR` case -- as "downstream of `ParRed.weakN_inv`".  **It is not downstream of anything: with
a K-step in `ParRed`, `NormalEq.parRed`'s own conclusion is false there**, and no weakening of
`weakN_inv` and no `Params` field repairs it.

The shape is `KStep.stuck_fires` (`KRule.lean`) meeting `NormalEq.etaR`:

> `.app e.lift (.bvar 0)` is exactly the term `whnf_app_bvar` proves weak-head normal and
> `KStep` reduces.  Put `e := Eq.rec α a C m b` -- five arguments, one short of the ι-pattern,
> so `e` is `ParRed`-normal -- and `A := Eq α a b`, a `Prop`.  Then
>
> * `Γ ⊢ e ≡ₚ .lam A (.app e.lift (.bvar 0))` by `NormalEq.etaR` and `NormalEq.refl`;
> * `Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≫ .lam A t` by `ParRed.lam` and the K-step, where
>   `t = m.lift` is the ι-rule's right-hand side;
> * so `NormalEq.parRed` must produce `o` with `Γ ⊢ e ≫* o` and `Γ ⊢ o ≡ₚ .lam A t`.
>
> `e` is `ParRed`-normal, so `o = e`, and `Γ ⊢ e ≡ₚ .lam A t` can only be `NormalEq.etaR`,
> which asks for `A::Γ ⊢ .app e.lift (.bvar 0) ≡ₚ m.lift` -- a K-redex `NormalEq` to its own
> contractum.  `NormalEq` has no reduction, and `C` may land in `Type` (measured: §2.2's first
> probe), so `proofIrrel` is unavailable.  **There is no such `o`.**

The theorem below is that argument, machine-checked, with the instance-specific facts left as
hypotheses -- each of which the `Eq.rec` reading above supplies.  It is the reason `hK` is not
merely expensive but **not landable as posed**: `NormalEq` itself (or `ParRedS`, by an
eta-expansion step) has to grow, and that changes `IsDefEq.church_rosser`'s conclusion, i.e.
the confluence interface, not just `Params`.

`docs/design-inductive.md` §7.6's second warning -- "it may be the statement rather than the
axiom that needs adjusting -- e.g. by allowing `NormalEq` a proof-irrelevance closure at the
major-premise position" -- is the same observation, reached from the design side, and this is
its machine-checked form. -/

/-- `NormalEq.parRed`'s statement, as a `Prop`, so that it can be refuted. -/
def ParRedStatement : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ e₂' : VExpr}, OnCtx Γ (IsType env univs) →
    NormalEq Γ e₁ e₂ → ParRed Γ e₂ e₂' → ∃ e₁', ParRedS Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂'

/-- **`hK` refutes `NormalEq.parRed`.**  See the section comment for the reading of each
hypothesis at `Eq.rec`; all six are properties of the *witness*, none of them of the rule
table, so no `Params` field can avoid them. -/
theorem not_parRedStatement_of_hK
    (hK : ∀ {Δ : List VExpr} {a b : VExpr}, KStep Δ a b → ParRed Δ a b)
    {Γ : List VExpr} {e A B t : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓA : OnCtx (A::Γ) (IsType env univs))
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hnp : ∀ P, Γ ⊢ P : .sort .zero → ¬ (Γ ⊢ e : P))
    (hrig : ∀ o, ParRedS Γ e o → o = e)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ ParRedStatement := by
  intro H
  have hb0 := HasType.app (he.weak henv) (.bvar .zero)
  simp [instN_bvar0] at hb0
  have h1 : NormalEq Γ e (.lam A (.app e.lift (.bvar 0))) := .etaR he (.refl hb0)
  have h2 : ParRed Γ (.lam A (.app e.lift (.bvar 0))) (.lam A t) := .lam .rfl (hK hstep)
  obtain ⟨o, ho, hno⟩ := H hΓ h1 h2
  cases hrig o ho
  cases hno with
  | refl _ => exact hlam _ _ rfl
  | etaL _ _ => exact hlam _ _ rfl
  | lamDF _ _ _ => exact hlam _ _ rfl
  | etaR _ h2' => exact hne h2'
  | proofIrrel hP h1' _ => exact hnp _ hP h1'

/-! ## The same obstruction, one level up: `IsDefEq.church_rosser` itself

The refutation above needs `hK`.  **The next one does not.**  A K-step is *admissible*
(`KStep.defeq`), so wherever one fires, `IsDefEq` already relates the redex to the contractum
-- and under an `eta`, `IsDefEq` relates the *function* to a λ whose body is the contractum.
`ParRed` cannot follow, K-rule or no K-rule, because `e` itself is not a redex; and `NormalEq`
cannot bridge, because its only route is `etaR`, which asks for the K-redex to be `NormalEq` to
its own contractum.

> **`IsDefEq.church_rosser` is false at any `Params` instance registering an ι-rule of a
> large-eliminating subsingleton** -- `Eq` is the standard one, and the kernel really does
> reduce `@Eq.rec α a C m a h` for a *variable* `h` with `C` landing in `Type` (§2.2, first
> probe, measured).  Adding K to `ParRed` does not repair this; it relocates it.

So the confluence interface, not only `Params`, is what has to change: either `NormalEq` gains
a closure at the K-redex position, or `ParRedS` gains an eta-expansion.  This is
`typesys.tex:19-48`'s incompleteness arriving in the tree's own statement, and it is the same
thing `docs/design-inductive.md` §7.6's second warning predicted. -/

/-- A `ParRed`-normal term is `ParRedS`-normal. -/
theorem parRedS_rigid {Γ : List VExpr} {e o : VExpr}
    (h : ∀ o', ParRed Γ e o' → o' = e) (H : ParRedS Γ e o) : o = e := by
  induction H with
  | rfl => rfl
  | tail _ hs ih => cases ih; exact h _ hs

/-- Reducts of a λ whose domain is `ParRed`-normal are λs with the same domain.  (`extra`
cannot fire on a λ: a `Pattern` matches only `const`/`app` spines.) -/
theorem parRedS_lam_inv {Γ : List VExpr} {A t y : VExpr}
    (hA : ∀ A', ParRed Γ A A' → A' = A) (H : ParRedS Γ (.lam A t) y) :
    ∃ t', y = .lam A t' ∧ ParRedS (A::Γ) t t' := by
  induction H with
  | rfl => exact ⟨t, rfl, .rfl⟩
  | @tail b c _ hstep ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    cases hstep with
    | lam h1 h2 => cases hA _ h1; exact ⟨_, rfl, ht.tail h2⟩
    | extra _ h2 _ _ => cases h2

/-- `IsDefEq.church_rosser`'s statement, as a `Prop`, so that it can be refuted. -/
def CRStatement : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, OnCtx Γ (IsType env univs) →
    IsDefEq env univs Γ e₁ e₂ A → CRDefEq Γ e₁ e₂

/-- **A registered K-redex under an `eta` refutes Church--Rosser.**  No `hK`: the only thing
used about the rule is `KStep.defeq`, i.e. that it is admissible.

Every hypothesis is a property of the witness, and the `Eq.rec` reading discharges each:
`e := Eq.rec α a C m b` is one argument short of the ι-pattern, so it is `ParRed`-normal
(`hrig`), is not a λ (`hlam`) and is not a proof when `C` lands in `Type` (`hnp`); `A := Eq α a b`
is a `Prop` and `ParRed`-normal (`hrigA`); the contractum `t = m` is normal for a normal `m`
(`hrigT`); and `.app e.lift (.bvar 0)` is not `NormalEq` to `m.lift`, there being no
`NormalEq` rule relating an application to an unrelated head (`hne`). -/
theorem not_crStatement_of_kstep
    {Γ : List VExpr} {e A B t : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs)) (hΓA : OnCtx (A::Γ) (IsType env univs))
    (hA : Γ ⊢ A : .sort u)
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hnp : ∀ P, Γ ⊢ P : .sort .zero → ¬ (Γ ⊢ e : P))
    (hrig : ∀ o, ParRed Γ e o → o = e)
    (hrigA : ∀ A', ParRed Γ A A' → A' = A)
    (hrigT : ∀ t', ParRed (A::Γ) t t' → t' = t)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ CRStatement := by
  intro H
  have hb0 := HasType.app (he.weak henv) (.bvar .zero)
  simp [instN_bvar0] at hb0
  have hbody : IsDefEq env univs (A::Γ) (.app e.lift (.bvar 0)) t B :=
    (KStep.defeq hΓA hstep).of_l henv hΓA hb0
  have hdefeq : IsDefEq env univs Γ e (.lam A t) (.forallE A B) :=
    ((IsDefEq.eta he).symm).trans (.lamDF hA hbody)
  obtain ⟨-, -, x, y, hx, hy, hxy⟩ := H hΓ hdefeq
  have hxe : x = e := parRedS_rigid hrig hx
  obtain ⟨t', rfl, ht⟩ := parRedS_lam_inv hrigA hy
  have hte : t' = t := parRedS_rigid hrigT ht
  subst hte; subst hxe
  cases hxy with
  | refl _ => exact hlam _ _ rfl
  | etaL _ _ => exact hlam _ _ rfl
  | lamDF _ _ _ => exact hlam _ _ rfl
  | etaR _ h2' => exact hne h2'
  | proofIrrel hP h1' _ => exact hnp _ hP h1'

/-- `ParRedStatement` is `NormalEq.parRed`'s statement **verbatim** -- this is the check, not a
claim.  Note what the pair of it and `not_parRedStatement_of_hK` says: the tree *proves* this
statement today and this file *refutes* it under `hK`.  There is no contradiction, because
`NormalEq.parRed` is `sorryAx`-tainted through `NormalEq.descend`, which is itself refuted
(`DescendRefute.lean`).  A proof consuming a false obligation simply succeeds; what the
refutation adds is *which* obligation, and that adding `hK` does not remove the problem but
moves it to a case that carries no hole at all. -/
theorem parRedStatement_holds : ParRedStatement := fun hΓ h1 h2 => NormalEq.parRed hΓ h1 h2

/-- `CRStatement` is `IsDefEq.church_rosser`'s statement **verbatim**. -/
theorem crStatement_holds : CRStatement := fun hΓ h => IsDefEq.church_rosser hΓ h

end VEnv

/-! ## Consistency of the two hypotheses -- and what that check is *not* -/

namespace VEnv

/-- `KSmall` holds at the witness instance, because `refParams` registers no rule at all.
`refParams_kTable` says the same for `KTable`.

**This is a consistency check, not evidence.**  `KStep` is empty at `refParams`
(`refParams_no_kstep`), so `KDiamond` is vacuously true there too, and nothing about the
non-vacuous case is tested.  The instance that would test it does not exist: no `Params`
instance in this tree registers an `.app` pattern.  **The reason given here was wrong, corrected
2026-09-01: it said "because" `paramsOfWF`'s `PatWF` is open, which treats `paramsOfWF` as the only
route to a `Params` — but `ParamsWitness.lean`, in this same tree, builds one by hand.  An
`.app`-pattern instance was available all along without touching `PatWF`, and
`Theory/Typing/PatAppParams.lean` now exhibits one (`appParams`).  The observation about `PatWF` is
still true of `paramsOfWF`; it was never the reason.**  For the record, `paramsOfWF`'s `PatWF` is open in
exactly its ι and quotient cases (`docs/handoff-params.md` §1.1). -/
theorem refParams_kSmall : @KSmall refParams := fun h _ _ _ _ _ => absurd h refNoPat

/-- A `KTable` at the witness instance.  `kmajor` is the identity on the major premise, which
commutes with lifting on the nose; `canon` is vacuous. -/
def refParams_kTable : @KTable refParams :=
  @KTable.mk refParams (fun _ _ h => h) (fun _ _ _ _ _ => rfl)
    (fun _ h => absurd h refNoPat)

end VEnv

end Lean4Lean
