import Lean4Lean.Theory.Typing.KMeasure
import Lean4Lean.Theory.Typing.ParamsWitness
import Lean4Lean.Theory.Typing.PatKHead

/-!
# `descend`'s critical-path consumer, re-run over `ParRedK`

`NormalEq.descend` (`ChurchRosser.lean`) is refuted (`DescendRefute.lean`) and restated
(`KDescend.lean`'s `descendV`, `KSite7App.lean`'s `appDF_extra_of_descendVK`).  The restatement
lives over **`ParRedK`** -- `ParRed` plus the η-guarded K step `keta` -- so the whole
`ChurchRosser.lean` chain that consumes `descend` has to move to `ParRedK` with it.

`docs/critical-path.md` records why that matters: `descend` is on `Bridge.kernel_sound_of`'s
cone, and it enters through exactly one chain,

    addAxiom.WF ← … ← constApp_inv_of_patWF ← IsDefEq.constApp_inv ← IsDefEq.church_rosser
                ← CRDefEq.trans ← NormalEq.parRedS ← NormalEq.parRed
                ← appDF_extra_of_descend ← descend

whose load-bearing step is `Verify/Typing/ConstSpine.lean`'s `ParRedS.constApp_inv`: *a
rule-free constant spine parallel-reduces only to constant spines with the same head, levels
and arity.*  That lemma is proved by induction over `ParRed`'s **eight** constructors, and its
`extra` case is discharged by the head condition.  `ParRedK` has a **ninth**, `keta`, and
nothing in the tree had checked whether the head condition still discharges it.

**It does.**  `ParRedK.constApp_free` and `ParRedK.constApp_inv` below are the ported lemmas,
unconditional and `sorry`-free relative to their imports.  The pieces were both already
present and had never been composed: `KEta.lean`'s `EtaK.matches_head` (whose own docstring
says it is "the fact `Verify/Typing/ConstSpine.lean`'s `ParRed.constApp_inv` needs" -- written
for this use and never used for it) and `ConstSpine.lean`'s `ParRed.constApp_inv` proof, which
is reproduced here constructor-for-constructor with the ninth case added.

## What this does and does not buy

* **Does:** the K-route -- the only live repair of the confluence layer -- is *compatible* with
  the consumer that puts `descend` on the soundness cone.  Had the `keta` case failed, the
  whole `KDescend`/`KSite7`/`ParRedKGraded` programme would have been unable to reach
  `IsDefEq.constApp_inv`, i.e. unable to serve the one chain that makes `descend` matter.  That
  risk is now retired rather than assumed away.
* **Does not:** deliver `church_rosser` over `ParRedK`.  That still needs `ParRed.triangle`'s
  analogue (`ParRedCycle.lean`, `ParRedMissing.lean` §3) and `parRedKStatement_of_rows`, which
  costs `IsDefEqU.weakN_iff`.  This file is one *necessary* link, measured, not the route.

## Layering: the copies are gone

An earlier revision of this file carried six marked copies of `Verify/Typing/ConstSpine.lean`
declarations -- `patHeadConst`, `matches_patHeadConst`, `PatFreeHeadK`, `constAppK_ne_*`,
`List.Forall₂.transK`, `List.forall₂_reflK` -- because `Theory/` may not import `Verify/`.
The originals have since been **moved down** into `Theory/Typing/PatKHead.lean`; none of them
ever had a `Verify` dependency of any kind.  So the copies are deleted, and everything below is
stated against the *same* `Pattern.headConst`, `VEnv.PatFreeHead` and `VExpr.constApp_ne_*`
that `ConstSpine.lean`'s `ParRed.constApp_inv` and `ParRedS.constApp_inv` use.  There is now
one `PatFreeHead` in the tree, and the K-side and the non-K-side lemma take literally the same
hypothesis -- which is the only way the K-route can be a *drop-in* for the consumer chain.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

section Abstract
variable [Params]
open Params

/-- **The ninth case.**  An `EtaK` step cannot fire at a rule-free constant spine.

This is the whole new obligation `ParRedK` adds over `ParRed` at `ConstSpine.lean`'s
induction, and it is discharged by the *same* hypothesis: `EtaK.matches_head` says an `EtaK`
redex has the head constant of a registered `.app`-pattern's function side, and
`(p₁.app p₂).headConst = p₁.headConst` by definition. -/
theorem EtaK.constApp_free {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {e' : VExpr} (hc : PatFreeHead c)
    (H : EtaK Γ ((VExpr.const c ls).mkApp as) e') : False := by
  obtain ⟨p₁, p₂, r, f, m1, m2, h1, h2, h3⟩ := H.matches_head
  rw [VExpr.headConst?_mkApp, h2.headConst] at h3
  exact hc _ _ h1 (Option.some.inj h3).symm

/-- **`ParRedK` preserves a rule-free constant head**, its levels and its arity.

`Verify/Typing/ConstSpine.lean`'s `ParRed.constApp_inv`, ported constructor-for-constructor,
with the `keta` case added. -/
theorem ParRedK.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHead c) :
    ∀ {ls : List VLevel} {as : List VExpr} {e' : VExpr},
      ParRedK Γ ((VExpr.const c ls).mkApp as) e' →
      ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedK Γ) as as' := by
  intro ls as e' H
  generalize he : (VExpr.const c ls).mkApp as = e₀ at H
  induction H generalizing as with
  | @const _ c₀ ls₀ =>
    obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ he nofun
    injection heq with h1 h2; subst h1; subst h2
    exact ⟨[], rfl, .nil⟩
  | @app _ f f' a a' hf ha ihf iha =>
    rcases VExpr.mkApp_app_inv as _ he with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    obtain ⟨bs', rfl, hbs⟩ := ihf hb
    refine ⟨bs' ++ [a'], ?_, hbs.append' (.cons ha .nil)⟩
    rw [VExpr.mkApp_append]; rfl
  | @beta _ A e₁ e₁' e₂ e₂' _ _ _ _ =>
    rcases VExpr.mkApp_app_inv as _ he with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
    · exact absurd hbad nofun
    exact absurd hb VExpr.constApp_ne_lam
  | @extra p r e₀ m1 m2 _ m2' h1 h2 _ _ _ =>
    subst he
    have := h2.headConst
    rw [VExpr.headConst?_mkApp] at this
    exact absurd (Option.some.inj this).symm (hc _ _ h1)
  | @keta _ e w w' hη _ _ =>
    subst he
    exact absurd hη (fun h => EtaK.constApp_free hc h)
  | bvar => exact absurd he VExpr.constApp_ne_bvar
  | sort => exact absurd he VExpr.constApp_ne_sort
  | lam => exact absurd he VExpr.constApp_ne_lam
  | forallE => exact absurd he VExpr.constApp_ne_forallE

/-- The reflexive-transitive form, i.e. `ConstSpine.lean`'s `ParRedS.constApp_inv` over
`ParRedKS`.  This is the statement `IsDefEq.constApp_inv` consumes. -/
theorem ParRedKS.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHead c)
    {ls : List VLevel} {as : List VExpr} {e' : VExpr}
    (H : ParRedKS Γ ((VExpr.const c ls).mkApp as) e') :
    ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedKS Γ) as as' := by
  induction H with
  | rfl => exact ⟨as, rfl, List.forall₂_refl' (fun _ => ReflTransGen.rfl) as⟩
  | @tail b c₂ h1 h2 ih =>
    obtain ⟨bs, rfl, hbs⟩ := ih
    obtain ⟨cs, rfl, hcs⟩ := ParRedK.constApp_inv hc h2
    exact ⟨cs, rfl, hbs.trans' (fun _ _ _ h h' => h.tail h') hcs⟩

end Abstract

/-! ## Anti-vacuity: is `PatFreeHead` satisfied for a real reason?

`docs/vacuity-ledger.md` §0: a hypothesis that holds because nothing satisfies its
quantifier proves nothing.  `PatFreeHead c` quantifies over the registered pattern table, so
the degenerate way to satisfy it is an **empty** table -- which is exactly what `refParams`
(`DescendRefute.lean`, `refNoPat`) and `cycParams` (`ParRedCycle.lean`, `cycNoPat`) have.  A
theorem checked only there would be a theorem about a relation that never moves.

`ParamsWitness.lean`'s `propLoopParams` is the non-degenerate instance: `VEnv.WF`
(`propLoopEnv_wf`), two registered δ-patterns, and a `ParRed.extra` step that really fires
(`propLoopEnv_parRed_fires`).  The three theorems below are at that instance. -/

section PropLoop

attribute [local instance] propLoopParams
open PropLoopParams

/-- **Non-degenerate inhabitation.**  At `propLoopParams` -- whose pattern table is *not*
empty -- `PatFreeHead c` holds for every constant other than the two rule heads. -/
theorem propLoop_patFreeHeadK {c : Lean.Name} (hA : c ≠ `A) (hB : c ≠ `B) :
    PatFreeHead c := by
  intro p r h
  obtain ⟨c', rfl⟩ := PropLoopParams.Pat.const h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact fun h => hA h.symm
  · exact fun h => hB h.symm

/-- The table it is satisfied *against* is non-empty: `A` is a registered pattern head.  Read
with `propLoop_patFreeHeadK`, this is what says the hypothesis is not holding vacuously. -/
theorem propLoop_pat_nonempty :
    @Params.Pat propLoopParams (.const `A)
      ⟨.fixed (.const `B []) () trivial, .true⟩ := .inl ⟨rfl, rfl⟩

/-- **Negative control: `PatFreeHead` is load-bearing.**  At the *same* instance, the
head that *does* front a rule violates `ParRedK.constApp_inv`'s conclusion -- `A` reduces to
`B`, which is no `A`-headed spine.  So dropping the hypothesis makes the statement false.

Second half of the control, per `ForallInvPrice.lean`'s discipline: this is **not** a
refutation of `ParRedK.constApp_inv`, because the environment is a legitimate one
(`propLoopEnv_wf : propLoopEnv.WF`) and `PatFreeHead `A`` simply fails there
(`propLoop_not_patFreeHeadK`).  The control constrains the hypothesis, not the theorem. -/
theorem propLoop_not_patFreeHeadK : ¬ PatFreeHead `A := by
  intro h; exact h _ _ propLoop_pat_nonempty rfl

theorem propLoop_constApp_inv_needs_hyp :
    ParRedK [] (.const `A []) (.const `B []) ∧
      ∀ as' : List VExpr, (VExpr.const `B [] : VExpr) ≠ (VExpr.const `A []).mkApp as' := by
  refine ⟨ParRed.toK propLoopEnv_parRed_fires, fun as' h => ?_⟩
  have h1 := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at h1
  simp [VExpr.spineHead] at h1

/-- **The honest limit of this measurement.**  The `keta` case -- the one new obligation -- is
**vacuous at every `Params` instance `Theory/` contains**, because `EtaK` fires only where an
`.app` pattern is registered (`EtaK.matches_head`) and every Theory-side table is δ-only:
`refNoPat`, `cycNoPat`, and here.  So `EtaK.constApp_free`'s proof is instance-independent but
its *content* is untested; the first instance that would test it is
`Verify/QuotAppParams.lean`'s `quotParams`, which `Theory/` may not import. -/
theorem propLoop_no_etaK {Γ : List VExpr} {e e' : VExpr} : ¬ EtaK Γ e e' := by
  intro h
  obtain ⟨p₁, p₂, r, f, m1, m2, h1, -, -⟩ := h.matches_head
  exact h1.elim

end PropLoop

end VEnv

end Lean4Lean
