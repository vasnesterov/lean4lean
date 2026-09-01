import Lean4Lean.Theory.Typing.ParRedCycle
import Lean4Lean.Theory.Typing.ParRedPropRefute

/-!
# `appParams`: the first `Params` instance that registers `.app` patterns

Every `Params` instance in this tree registered only `.const` patterns, and four separate open
items were waiting on that same missing object:

1. `ParRedCycle.lean`'s `PatMajorCanonical` (lemma M3, `design-inductive.md` §7.6) is **vacuous**
   at `cycParams`, because `cycNoPat` says that table is empty;
2. `ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor`;
3. `KCanonical.lean`'s `not_crStatement_of_kstep`;
4. `KRule.lean`'s `KStep.stuck_fires`.

`appParams` below is such an instance.  It is built over `ParRedCycle.lean`'s `cycEnv`
(`P : Prop`, `D D2 : P`, `T : Type`, `C : P → T`) and registers **two** `.app` patterns,
`cycQ = C D` and `cycQ2 = C D2`, each rewriting to the other side of the proof-irrelevance pair.
Both are `SimplePattern.iota _ 0 _ 0` shapes, so `pat_simple` is satisfied on the nose.

## What it settles, item by item

* **Item 4 closes.**  `appParams_stuck_fires` is `KStep.stuck_fires` **fully instantiated**: at
  `Γ = [P]`, `C (.bvar 0)` is weak-head normal *and* a `K⁺` redex, the variable being made
  definitionally equal to `D` by proof irrelevance.  `KRule.lean` states that theorem with the
  honest cost "no `Params` instance in the tree supplies it yet"; it does now.
* **Item 1 becomes non-vacuous, and `PatMajorCanonical` SURVIVES.**
  `appParams_patMajorCanonical` proves it, `appParams_patMajor_hyps_sat` shows the hypotheses are
  jointly satisfiable at two *different* registered patterns with *syntactically different*
  right-hand sides, and `appParams_kDiamond` therefore gives `KDiamond` here non-vacuously
  (`appParams_kDiamond_nondegenerate`: one redex, two K-steps, two distinct reducts).
* **Items 2 and 3 stay out of reach — and now for a proved reason, not for want of an
  instance.**  Both carry a hypothesis `hne` saying the redex-with-another-proof is *not*
  `NormalEq` to the rule's right-hand side.  Here `hne` is **false**
  (`appParams_normalEq_rhs`, `appParams_normalEq_of_kstep`), so
  `appParams_no_propMajor_refutation` and `appParams_no_crStatement_refutation` derive `False`
  from their hypothesis lists.  Every *other* hypothesis of item 2 is satisfiable here,
  `hrig` included (`appParams_propMajor_hyps_sat`), so `hne` is the sole blocker.

## Two caveats, both load-bearing

**This is a weak test of M3, and the proof says so.**  `appPat_rhs_eq` shows both right-hand
sides are the *closed* terms `cycG`/`cycG2`, and those two are `NormalEq` to each other; so
`appParams_patMajorCanonical` goes through **without using any of M3's typing premises**.  What
is established is that M3 is not *false* at the first real `.app` table; what is *not* tested is
its canonical-form content.  A table whose right-hand sides are not pairwise `NormalEq` is what
would test that, and per the next paragraph no such table is reachable in `Theory/` today.

**Why the environment carries no defeq rule, and why that is forced rather than convenient.**
`Params.pat_uniq`, applied with `p₃` the head leaf, makes registering both `.const c` and
`.app (.const c) _` **impossible** (`AppPat.uniq`'s off-diagonal cases are exactly this), and the
same for the argument leaf.  So an `.app` pattern's two leaves may carry no `.const` rule.  But a
`VEnv.WF` environment's only `.const`-left-hand-side rules are its δ-rules, and its only
`.app`-left-hand-side rules come from `addQuot` or `addInduct'` -- whose patterns have `.var`
positions, whose matched arguments are therefore arbitrary terms, and whose `pat_wf` consequently
needs `HasArgs.of_mkApp`, i.e. `PiInv` (`PatWF.lean`, `SpineInv.lean`).  `appParams` escapes that
because **both** its pattern leaves are `.const`: the matched term is determined up to its two
level lists, so `HasType.app_inv` and `HasType.const_inv` (both `sorryAx`-free) suffice to pin it,
after which the equality is *rebuilt* from the constants' declared types rather than transported
along an invented domain.  The price is that the only equality available to rebuild is proof
irrelevance -- which is precisely why `hne` fails and items 2/3 do not fire.

**[analysis, not a theorem]** that this is the *only* `PiInv`-free route to `pat_wf` at an `.app`
pattern.  Treat it as a conjecture; the negative is not proved.

## Measured, this file, `#print axioms`

**No declaration in this file carries `sorryAx`.**  The instance and everything downstream of it
measures `[propext, Classical.choice, Quot.sound]`; `Classical.choice` enters through
`VEnv.WF.ordered`, which `HasType.const_inv` needs, and is therefore not removable here.
`appPat_rhs_eq` is `[propext]`; `AppPat.simple`, `sub_app_const`, `matches_app_const_inv`,
`cycG_closed`, `cycG2_closed`, `appRuleD`, `appRuleD2` are axiom-free.

## What the canonical route still needs — measured, 2026-09-01

`PatWFIota.lean` already has the *parametrised* instance `paramsOfPiInv`, so the missing object
was never a construction there; it was a concrete environment plus `PiInv`.  **The environment
half already exists in the tree**, which `PatWF.lean`'s own non-vacuity note does not yet record:

```lean
-- needs `import Lean4Lean.Verify.QuotConsts`, so it cannot live in `Theory/`
theorem quotVEnv_wf : (quotVEnv QuotWit.venvEq).WF :=
  (QuotWit.trEnv_addQuot_wit (safety := .safe)).wf              -- [propext, Classical.choice, Quot.sound]

theorem quotVEnv_pat_app : Pat (quotVEnv QuotWit.venvEq) quotPat (quotRHS, quotCheck) :=
  .quot QuotWit.quotVEnv_venvEq_contents.2.2.2.2.2
    QuotWit.quotVEnv_venvEq_contents.2.2.1 QuotWit.quotVEnv_venvEq_contents.2.1
                                                                 -- [propext, Quot.sound]
```

so the **canonical** `Pat` table at a concrete, `sorryAx`-free `VEnv.WF` environment *already*
registers the `.app` pattern `quotPat`, and `paramsOfPiInv quotVEnv_wf 0 (piInv_axiom …)` is a
`Params` instance registering it -- `sorryAx`-tainted, through `PiInv` and nothing else
(measured `[propext, sorryAx, Classical.choice, Quot.sound]`).  So the canonical `.app` instance
is **one `PiInv` away**, and it would have to live downstream of `Verify/QuotConsts.lean`, i.e.
outside `Theory/`.

Note also that the quotient rule's major premise `Quot.mk r a` is **not** a proof of a `Prop`, so
even that instance does not reach items 2/3: those need a `Prop`-valued inductive whose motive
lands in `Type` -- the `Eq.rec` shape -- i.e. an `addInduct'` witness *and* `PiInv`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

/-! ## The rule table -/

theorem cycG_closed : cycG.Closed := ⟨trivial, trivial⟩
theorem cycG2_closed : cycG2.Closed := ⟨trivial, trivial⟩

/-- The right-hand side of the rule `C D ⟶ C D2`: the closed term `C D2`. -/
def appRuleD : cycQ.RHS × cycQ.Check := (.fixed cycG2 (.inl ()) cycG2_closed, .true)
/-- The right-hand side of the rule `C D2 ⟶ C D`. -/
def appRuleD2 : cycQ2.RHS × cycQ2.Check := (.fixed cycG (.inl ()) cycG_closed, .true)

/-- **The pattern table.**  Two `.app` patterns, `C D` and `C D2`, each rewriting to the other
side of `cycEnv`'s proof-irrelevance pair. -/
inductive AppPat : (p : Pattern) → p.RHS × p.Check → Prop
  | d : AppPat cycQ appRuleD
  | d2 : AppPat cycQ2 appRuleD2

/-! ## The ten fields -/

theorem AppPat.simple {p r} (h : AppPat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  cases h
  · exact ⟨.iota `C 0 `D 0, rfl⟩
  · exact ⟨.iota `C 0 `D2 0, rfl⟩

/-- The subpatterns of `.app (.const c) (.const a)`, enumerated. -/
theorem sub_app_const {q c a} (h : Subpattern q (.app (.const c) (.const a))) :
    q = .app (.const c) (.const a) ∨ q = .const c ∨ q = .const a := by
  cases h with
  | refl => exact .inl rfl
  | appL h => cases h; exact .inr (.inl rfl)
  | appR h => cases h; exact .inr (.inr rfl)

theorem AppPat.uniq {p₁ p₂ p₃ p₄ r r'} (h1 : AppPat p₁ r) (h2 : AppPat p₂ r')
    (h3 : Subpattern p₃ p₁) (h4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases h1 <;> cases h2 <;>
    rcases sub_app_const h3 with rfl | rfl | rfl <;>
    simp [Pattern.inter] at h4 ⊢

theorem AppPat.app_l_uniq {p p' p₁ p₂ p₁' p₂' p₃ r r'} (h1 : AppPat p r) (_h2 : AppPat p' r')
    (h3 : Subpattern (.app p₁ p₂) p) (_h4 : Subpattern (.app p₁' p₂') p')
    (h5 : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases h1 <;> rcases sub_app_const h3 with h | h | h <;> cases h <;> cases h5

theorem AppPat.app_uniq {p p' p₁ p₂ p₁' p₂' p₃ p₃' r r'} (h1 : AppPat p r) (h2 : AppPat p' r')
    (h3 : Subpattern (.app p₁ p₂) p) (h4 : Subpattern (.app p₁' p₂') p')
    (h5 : Subpattern p₃ p₁) (h6 : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  cases h1 <;> cases h2 <;>
    rcases sub_app_const h3 with h | h | h <;> cases h <;>
    rcases sub_app_const h4 with h' | h' | h' <;> cases h' <;>
    cases h5 <;> cases h6 <;> simp [Pattern.inter]

/-! ## `pat_wf`: the two rules are definitional equalities of `cycEnv`

This is the field that `ParamsBuild.lean`/`PatWFIota.lean` cannot supply at an `.app` pattern
without `PiInv`, and the reason this instance can is that **both leaves of the pattern are
`.const`**: the matched term is determined up to its two level lists, so its typing only has to
be *inverted far enough to pin those* (`HasType.app_inv` and `HasType.const_inv`, both
`sorryAx`-free), after which the equality is *rebuilt* from the constants' declared types rather
than transported along an invented domain.  A genuine ι- or quot-pattern has `.var` positions,
its matched arguments are arbitrary terms, and there the invented domains must be reconciled with
the declared ones -- which is `PiInv`. -/

theorem matches_app_const_inv {c a : Lean.Name} {e m1 m2}
    (h2 : (Pattern.app (.const c) (.const a)).Matches e m1 m2) :
    ∃ ls ls', e = .app (.const c ls) (.const a ls') ∧
      m1 = Sum.elim (fun _ => ls) (fun _ => ls') := by
  cases h2 with
  | app hf ha => cases hf; cases ha; exact ⟨_, _, rfl, rfl⟩

theorem cyc_levels_nil {c : Lean.Name} {ls ls' : List VLevel} {Γ A}
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hc : cycEnv.constants c = some ⟨0, .const `P []⟩)
    (hT : cycEnv.HasType 0 Γ (.app (.const `C ls) (.const c ls')) A) :
    ls = [] ∧ ls' = [] := by
  obtain ⟨A', B', hf, ha⟩ := HasType.app_inv cycEnv_wf.ordered hΓ hT
  obtain ⟨ci, hci, -, hlen⟩ := HasType.const_inv cycEnv_wf.ordered hΓ hf
  obtain ⟨ci', hci', -, hlen'⟩ := HasType.const_inv cycEnv_wf.ordered hΓ ha
  rw [cycEnv_C] at hci; cases hci
  rw [hc] at hci'; cases hci'
  exact ⟨List.eq_nil_of_length_eq_zero hlen, List.eq_nil_of_length_eq_zero hlen'⟩

/-- `C D ≡ C D2`, by congruence over proof irrelevance at the `Prop` `P`. -/
theorem cycG_defeq_cycG2 {Γ} : cycEnv.IsDefEq 0 Γ cycG cycG2 (.const `T []) :=
  .appDF cycEnv_hasC (.proofIrrel cycEnv_hasP cycEnv_hasD cycEnv_hasD2)

theorem AppPat.wf {p r e A m1 m2 Γ} (h1 : AppPat p r) (h2 : p.Matches e m1 m2)
    (hΓ : OnCtx Γ (cycEnv.IsType 0)) (hT : cycEnv.HasType 0 Γ e A)
    (_hck : r.2.OK (cycEnv.IsDefEqU 0 Γ) m1 m2) :
    cycEnv.IsDefEqU 0 Γ e (r.1.apply m1 m2) := by
  cases h1 with
  | d =>
    obtain ⟨ls, ls', rfl, rfl⟩ := matches_app_const_inv h2
    obtain ⟨rfl, rfl⟩ := cyc_levels_nil hΓ cycEnv_D hT
    exact ⟨_, cycG_defeq_cycG2⟩
  | d2 =>
    obtain ⟨ls, ls', rfl, rfl⟩ := matches_app_const_inv h2
    obtain ⟨rfl, rfl⟩ := cyc_levels_nil hΓ cycEnv_D2 hT
    exact ⟨_, cycG_defeq_cycG2.symm⟩

/-- `extra_pat` is vacuous: `cycEnv` registers no defeq rule at all.  That is *not* a defect of
the instance -- it is what makes the two `.app` patterns admissible at all, since `pat_uniq`
forbids registering a `.const` pattern for either leaf, and every rule a `VEnv.WF` environment
can carry with a `.const` left-hand side would need exactly that. -/
theorem AppPat.extra {Γ df ls uvars} (_hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hdf : cycEnv.defeqs df) (_hls : ∀ l ∈ ls, l.WF uvars) (_hlen : ls.length = df.uvars) :
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
      AppPat p r ∧ p.Matches L m1 m2 ∧
      r.2.OK (cycEnv.IsDefEqU 0 (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2 :=
  absurd hdf cycEnv_no_defeqs

/-- **The instance.**  Not registered as a global `instance`, for the same reason
`propLoopParams` is not: the development is stated for an arbitrary `[Params]`. -/
@[instance_reducible] def appParams : Params where
  env := cycEnv
  henv := cycEnv_wf
  univs := 0
  Pat := AppPat
  pat_simple := AppPat.simple
  pat_uniq := AppPat.uniq
  pat_wf := AppPat.wf
  pat_app_l_uniq := AppPat.app_l_uniq
  pat_app_uniq := AppPat.app_uniq
  extra_pat := AppPat.extra

theorem appParams_env : @Params.env appParams = cycEnv := rfl
theorem appParams_univs : @Params.univs appParams = 0 := rfl

/-- **The instance registers an `.app` pattern.**  This is the fact no other instance in the
tree has. -/
theorem appParams_pat_app : @Params.Pat appParams cycQ appRuleD := AppPat.d
theorem appParams_pat_app2 : @Params.Pat appParams cycQ2 appRuleD2 := AppPat.d2

/-! ## Typing facts at an arbitrary context -/

theorem cycEnv_hasG_at {Γ} : cycEnv.HasType 0 Γ cycG (.const `T []) :=
  .appDF cycEnv_hasC cycEnv_hasD
theorem cycEnv_hasG2_at {Γ} : cycEnv.HasType 0 Γ cycG2 (.const `T []) :=
  .appDF cycEnv_hasC cycEnv_hasD2

/-- Either rule's right-hand side is a **closed** term -- `cycG` or `cycG2` -- at *every*
match, because both are `.fixed` at level lists that are already empty.  This is what makes
`PatMajorCanonical` decidable at this instance without touching its typing premises, and it is
also the precise reason the instance is a weak test of M3: see the caveat below. -/
theorem appPat_rhs_eq {p r} (h : AppPat p r) {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr} :
    Pattern.RHS.apply m1 m2 r.1 = cycG ∨ Pattern.RHS.apply m1 m2 r.1 = cycG2 := by
  cases h
  · exact .inr rfl
  · exact .inl rfl

section
attribute [local instance] appParams

/-! ## Item 1: `PatMajorCanonical` at the first instance that tests it -/

/-- **`PatMajorCanonical` is TRUE at `appParams`.**  Lemma M3 survives the first rule table that
registers `.app` patterns.  Both right-hand sides are `C` applied to a proof of the `Prop` `P`,
so `NormalEq.appDF` over `NormalEq.proofIrrel` closes every one of the four cases. -/
theorem appParams_patMajorCanonical : PatMajorCanonical := by
  intro Γ p₁ p₂ q₁ q₂ r r' f h c c' A₀ B₀ A₀' B₀' m1 m2 m1' m2' hp hp' hm hm' hf hf' hd hd'
  rcases appPat_rhs_eq hp with e1 | e1 <;> rcases appPat_rhs_eq hp' with e2 | e2 <;>
    rw [e1, e2] <;>
    first
      | exact .refl cycEnv_hasG_at
      | exact .refl cycEnv_hasG2_at
      | exact .appDF cycEnv_hasC cycEnv_hasC cycEnv_hasD cycEnv_hasD2
          (.refl cycEnv_hasC) (.proofIrrel cycEnv_hasP cycEnv_hasD cycEnv_hasD2)
      | exact .appDF cycEnv_hasC cycEnv_hasC cycEnv_hasD2 cycEnv_hasD
          (.refl cycEnv_hasC) (.proofIrrel cycEnv_hasP cycEnv_hasD2 cycEnv_hasD)

/-- **`KDiamond` at `appParams`**, through `kDiamond_of_patMajorCanonical`. -/
theorem appParams_kDiamond : KDiamond :=
  kDiamond_of_patMajorCanonical appParams_patMajorCanonical

/-! ### The hypotheses are satisfiable, and the conclusion is not an instance of reflexivity

Instrument 7.  `KStep` is non-empty at `appParams` and the two rules give the *same* redex two
*different* reducts, so `appParams_patMajorCanonical` is instantiated at a pair of syntactically
distinct terms (`cycG_ne_cycG2`, `ParRedCycle.lean`). -/

/-- The rule `C D ⟶ C D2` firing on the nose: `h = c = D`. -/
theorem appParams_kstep_toD2 : KStep [] cycG cycG2 :=
  .mk (p₁ := .const `C) (p₂ := .const `D) (r := appRuleD)
    AppPat.d (.app .const .const) trivial cycEnv_hasC cycEnv_hasD

/-- The rule `C D2 ⟶ C D` firing at `C D`, i.e. **`K⁺` proper**: the major premise `D` does not
match the pattern, it is only *definitionally equal* to the one that does. -/
theorem appParams_kstep_toD : KStep [] cycG cycG :=
  .mk (p₁ := .const `C) (p₂ := .const `D2) (r := appRuleD2)
    AppPat.d2 (.app .const .const) trivial cycEnv_hasC
    (.proofIrrel cycEnv_hasP cycEnv_hasD cycEnv_hasD2)

/-- **The diamond instance is real**: one redex, two K-steps, two syntactically different
reducts, and `KDiamond`'s conclusion at them is `NormalEq [] cycG2 cycG`, which is *not* an
instance of `NormalEq.refl`. -/
theorem appParams_kDiamond_nondegenerate :
    KStep [] cycG cycG2 ∧ KStep [] cycG cycG ∧ cycG2 ≠ cycG ∧ NormalEq [] cycG2 cycG :=
  ⟨appParams_kstep_toD2, appParams_kstep_toD, Ne.symm cycG_ne_cycG2,
    appParams_kDiamond trivial appParams_kstep_toD2 appParams_kstep_toD⟩

/-! ## Item 4: `KStep.stuck_fires` at a real instance

The measured hole `whnf_app_bvar` closes: `C (.bvar 0)` is weak-head normal at this instance and
is a `K⁺` redex, because proof irrelevance makes the variable definitionally equal to `D`. -/

/-- `[P]`, a context whose only entry is the `Prop`. -/
abbrev appCtx : List VExpr := [.const `P []]

theorem appCtx_wf : OnCtx appCtx (cycEnv.IsType 0) := ⟨trivial, _, cycEnv_hasP⟩

theorem appCtx_bvar0 : cycEnv.HasType 0 appCtx (.bvar 0) (.const `P []) := .bvar .zero

/-- `C` is weak-head normal: its `.const` pattern is a *proper* subpattern of a registered one,
so `pat_uniq` forbids a rule at it (`WHNF.subpattern`). -/
theorem appParams_whnf_C : WHNF appCtx (.const `C []) :=
  WHNF.subpattern AppPat.d (.appL .refl) (by intro h; exact absurd h (by simp)) .const

/-- **`KStep.stuck_fires`, fully instantiated.**  `KRule.lean` states it with the honest cost
"somebody must exhibit a `c` making `.app f c` a redex and `.bvar i` definitionally equal to
it"; here that somebody is this instance. -/
theorem appParams_stuck_fires :
    WHNF appCtx (.app (.const `C []) (.bvar 0)) ∧
      KStep appCtx (.app (.const `C []) (.bvar 0)) cycG2 :=
  KStep.stuck_fires (p₁ := .const `C) (p₂ := .const `D) (r := appRuleD)
    AppPat.d (.app .const .const) trivial cycEnv_hasC
    (.proofIrrel cycEnv_hasP appCtx_bvar0 cycEnv_hasD) appParams_whnf_C nofun

/-! ## Items 2 and 3: still out of reach, and now for a *proved* reason

`ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor` and `KCanonical.lean`'s
`not_crStatement_of_kstep` both carry a hypothesis `hne` saying the redex-with-another-proof is
**not** `NormalEq` to the rule's right-hand side.  At this instance that hypothesis is **false**,
and the theorems below prove it rather than observing it.

The mechanism is exactly what let `pat_wf` be discharged without `PiInv`: the rule's right-hand
side is reached from the redex by congruence over proof irrelevance, and `NormalEq` has
`proofIrrel` too.  So the two are inseparable here.  **Stated as analysis, not as a theorem:**
`pat_wf` at an `.app` pattern whose right-hand side is *not* so reachable needs the rule to be a
real rule of the environment, and `VEnv.WF` admits an `.app`-left-hand-side rule only through
`addQuot` or `addInduct'`, both of which have `.var` positions in their pattern and therefore need
`HasArgs.of_mkApp`, i.e. `PiInv`.  That is a route argument, not a proof, and it should be treated
as a conjecture. -/

theorem matches_fun_const {c : Lean.Name} {Γ : List VExpr} {f b A B : VExpr} {m1 m2}
    (hm : (Pattern.app (.const `C) (.const c)).Matches (.app f b) m1 m2)
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hf : cycEnv.HasType 0 Γ f (.forallE A B)) : f = .const `C [] := by
  obtain ⟨ls, ls', he, -⟩ := matches_app_const_inv hm
  injection he with hfe hbe
  subst hfe
  obtain ⟨ci, hci, -, hlen⟩ := HasType.const_inv cycEnv_wf.ordered hΓ hf
  rw [cycEnv_C] at hci; cases hci
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  rfl

theorem appPat_fun_const {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {Γ : List VExpr}
    {f b A B : VExpr} {m1 m2}
    (h : AppPat (.app p₁ p₂) r)
    (hm : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hf : cycEnv.HasType 0 Γ f (.forallE A B)) : f = .const `C [] := by
  cases h <;> exact matches_fun_const hm hΓ hf

/-- **`hne` is false at `appParams`, for every proof `a` of `P` and either rule.**  Note the
domain `A` of `f`'s Π-type is left arbitrary: no unique typing is used. -/
theorem appParams_normalEq_rhs {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {f a b A B : VExpr} {m1 m2}
    (r1 : AppPat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hf : cycEnv.HasType 0 Γ f (.forallE A B))
    (ha : cycEnv.HasType 0 Γ a (.const `P [])) :
    NormalEq Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1) := by
  obtain rfl := appPat_fun_const r1 r2 hΓ hf
  rcases appPat_rhs_eq r1 (m1 := m1) (m2 := m2) with e | e <;> rw [e]
  · exact .appDF cycEnv_hasC cycEnv_hasC ha cycEnv_hasD (.refl cycEnv_hasC)
      (.proofIrrel cycEnv_hasP ha cycEnv_hasD)
  · exact .appDF cycEnv_hasC cycEnv_hasC ha cycEnv_hasD2 (.refl cycEnv_hasC)
      (.proofIrrel cycEnv_hasP ha cycEnv_hasD2)

/-- **`not_parRedStatement_of_propMajor` cannot be instantiated at `appParams`.**  Its `hne` is
refuted by `appParams_normalEq_rhs`; the rest of its hypotheses are reproduced verbatim (with
`A := .const `P []`, so that `ha`/`hb` are the file's own `Prop`-major-premise reading). -/
theorem appParams_no_propMajor_refutation {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {f a b B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (r1 : AppPat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (_r3 : r.2.OK (cycEnv.IsDefEqU 0 Γ) m1 m2)
    (hf : cycEnv.HasType 0 Γ f (.forallE (.const `P []) B))
    (_hA : cycEnv.HasType 0 Γ (.const `P []) (.sort .zero))
    (ha : cycEnv.HasType 0 Γ a (.const `P []))
    (_hb : cycEnv.HasType 0 Γ b (.const `P []))
    (_hrig : ∀ o, ParRed Γ (.app f a) o → o = .app f a)
    (hne : ¬ NormalEq Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) : False :=
  hne (appParams_normalEq_rhs r1 r2 hΓ hf ha)

/-- **`not_crStatement_of_kstep` cannot be instantiated at `appParams` either**, and the reason
is the same one, in its sharpest form: **every `K⁺` step whose major premise is a proof of `P` is
already a `NormalEq`**, so the `hne` that refutation needs is unsatisfiable here. -/
theorem appParams_normalEq_of_kstep {Γ : List VExpr} {f h t : VExpr}
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (hh : cycEnv.HasType 0 Γ h (.const `P []))
    (hstep : KStep Γ (.app f h) t) : NormalEq Γ (.app f h) t := by
  cases hstep with
  | mk r1 r2 _ hf _ => exact appParams_normalEq_rhs r1 r2 hΓ hf hh

/-- Item 3's exact shape: the K-redex is `.app e.lift (.bvar 0)` in a context whose head is the
`Prop`, and the variable is a proof of it. -/
theorem appParams_no_crStatement_refutation {Γ : List VExpr} {e t : VExpr}
    (hΓ : OnCtx (VExpr.const `P [] :: Γ) (cycEnv.IsType 0))
    (hstep : KStep (VExpr.const `P [] :: Γ) (.app e.lift (.bvar 0)) t)
    (hne : ¬ NormalEq (VExpr.const `P [] :: Γ) (.app e.lift (.bvar 0)) t) : False :=
  hne (appParams_normalEq_of_kstep hΓ (.bvar .zero) hstep)

/-! ### Instrument 7: which hypotheses are satisfiable, and which single one is not

`appParams_no_propMajor_refutation` concludes `False`, so its hypotheses are *jointly*
unsatisfiable -- that is its content.  The check that makes the content non-empty is that
**every hypothesis except `hne` is satisfiable**, which is what `appParams_propMajor_hyps_sat`
exhibits.  So the blocker is `hne` and nothing else. -/

theorem appParams_parRed_const_C {Γ o} (h : ParRed Γ (.const `C []) o) : o = .const `C [] := by
  cases h with
  | const => rfl
  | extra hp hm _ _ => cases hp <;> cases hm

theorem appParams_parRed_bvar {Γ i o} (h : ParRed Γ (.bvar i) o) : o = .bvar i := by
  cases h with
  | bvar => rfl
  | extra hp hm _ _ => cases hp <;> cases hm

/-- `C (.bvar 0)` is `ParRed`-normal: `Pattern.Matches` is syntactic and `.bvar 0` is not a
`.const` leaf, so neither rule fires. -/
theorem appParams_rig_C_bvar {Γ o} (h : ParRed Γ (.app (.const `C []) (.bvar 0)) o) :
    o = .app (.const `C []) (.bvar 0) := by
  cases h with
  | app h1 h2 => rw [appParams_parRed_const_C h1, appParams_parRed_bvar h2]
  | extra hp hm _ _ => cases hp <;> (cases hm with | app _ ha => cases ha)

/-- Everything `not_parRedStatement_of_propMajor` asks for **except `hne`**, at `appParams`.
Note `hrig` is among them: the redex-with-a-variable really is `ParRed`-normal. -/
theorem appParams_propMajor_hyps_sat :
    ∃ (m1 : cycQ.LPath → List VLevel) (m2 : cycQ.Path → VExpr),
      Params.Pat cycQ appRuleD ∧
      cycQ.Matches (.app (.const `C []) (.const `D [])) m1 m2 ∧
      appRuleD.2.OK (cycEnv.IsDefEqU 0 appCtx) m1 m2 ∧
      cycEnv.HasType 0 appCtx (.const `C []) (.forallE (.const `P []) (.const `T [])) ∧
      cycEnv.HasType 0 appCtx (.const `P []) (.sort .zero) ∧
      cycEnv.HasType 0 appCtx (.bvar 0) (.const `P []) ∧
      cycEnv.HasType 0 appCtx (.const `D []) (.const `P []) ∧
      (∀ o, ParRed appCtx (.app (.const `C []) (.bvar 0)) o →
        o = .app (.const `C []) (.bvar 0)) :=
  ⟨_, _, AppPat.d, .app .const .const, trivial, cycEnv_hasC, cycEnv_hasP, appCtx_bvar0,
    cycEnv_hasD, fun _ => appParams_rig_C_bvar⟩

/-- `PatMajorCanonical`'s hypotheses, jointly satisfiable at `appParams`, at **two different
registered patterns** and with **syntactically different right-hand sides**.  This is the check
that `appParams_patMajorCanonical` is neither vacuous nor an instance of reflexivity. -/
theorem appParams_patMajor_hyps_sat :
    ∃ (m1 : cycQ.LPath → List VLevel) (m2 : cycQ.Path → VExpr)
      (m1' : cycQ2.LPath → List VLevel) (m2' : cycQ2.Path → VExpr),
      Params.Pat cycQ appRuleD ∧ Params.Pat cycQ2 appRuleD2 ∧
      cycQ.Matches (.app (.const `C []) (.const `D [])) m1 m2 ∧
      cycQ2.Matches (.app (.const `C []) (.const `D2 [])) m1' m2' ∧
      cycEnv.HasType 0 [] (.const `C []) (.forallE (.const `P []) (.const `T [])) ∧
      cycEnv.IsDefEq 0 [] (.const `D []) (.const `D []) (.const `P []) ∧
      cycEnv.IsDefEq 0 [] (.const `D []) (.const `D2 []) (.const `P []) ∧
      Pattern.RHS.apply m1 m2 appRuleD.1 ≠ Pattern.RHS.apply m1' m2' appRuleD2.1 :=
  ⟨_, _, _, _, AppPat.d, AppPat.d2, .app .const .const, .app .const .const,
    cycEnv_hasC, cycEnv_hasD, .proofIrrel cycEnv_hasP cycEnv_hasD cycEnv_hasD2,
    Ne.symm cycG_ne_cycG2⟩

end
end VEnv
end Lean4Lean
