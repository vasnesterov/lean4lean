import Lean4Lean.Theory.Typing.KMeasure
import Lean4Lean.Theory.Typing.ParamsWitness

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

## Layering and duplication, stated so it is not mistaken for new content

`Pattern.headConst`, `Pattern.Matches.headConst`, `PatFreeHead` and the four `constApp_ne_*`
lemmas live in `Verify/Typing/ConstSpine.lean`, and `Theory/` may not import `Verify/`.  None
of them has any `Verify` dependency -- they are statements about `Pattern` and `VExpr` alone --
so the right repair is to **move them down into `Theory/`**.  Until then this file carries
copies under distinct names (`patHeadConst`, `PatFreeHeadK`, `constAppK_ne_*`) so that nothing
clashes if a later module imports both.  Every copy is marked; none is a new result.
-/

namespace Lean4Lean

open VExpr

/-! ## Copies of `Verify/Typing/ConstSpine.lean`'s pattern-head machinery

Kept outside `namespace VEnv` on purpose: `ChurchRosser.lean` records that declaring a helper
about `Pattern` under a `Pattern.*` name *inside* `namespace VEnv` creates `VEnv.Pattern`,
which silently shadows `_root_.Lean4Lean.Pattern` at every later use site in the section. -/

/-- Copy of `Verify/Typing/ConstSpine.lean`'s `Pattern.headConst`: a pattern's leftmost
`const` leaf. -/
def patHeadConst : Pattern → Lean.Name
  | .const c => c
  | .app f _ => patHeadConst f
  | .var f => patHeadConst f

/-- Copy of `Verify/Typing/ConstSpine.lean`'s `Pattern.Matches.headConst`. -/
theorem matches_patHeadConst {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.headConst? = some (patHeadConst p) := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih1 _ => exact ih1

/-- Copy of `Verify/Typing/ConstSpine.lean`'s `List.Forall₂.trans'`. -/
theorem _root_.List.Forall₂.transK {α} {R S T : α → α → Prop}
    (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ → List.Forall₂ T l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (List.Forall₂.transK h t1 t2)

/-- Copy of `Verify/Typing/ConstSpine.lean`'s `List.forall₂_refl'`. -/
theorem _root_.List.forall₂_reflK {α} {R : α → α → Prop} (hR : ∀ a, R a a) :
    ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | _ :: l => .cons (hR _) (List.forall₂_reflK hR l)

theorem constAppK_ne_lam {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A b : VExpr} :
    (VExpr.const c ls).mkApp as ≠ .lam A b := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem constAppK_ne_bvar {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {i : Nat} :
    (VExpr.const c ls).mkApp as ≠ .bvar i := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem constAppK_ne_sort {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel} :
    (VExpr.const c ls).mkApp as ≠ .sort u := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem constAppK_ne_forallE {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    {A B : VExpr} : (VExpr.const c ls).mkApp as ≠ .forallE A B := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

namespace VEnv

section Abstract
variable [Params]
open Params

/-- Copy of `Verify/Typing/ConstSpine.lean`'s `PatFreeHead`: `c` heads no registered rewrite
pattern, so neither `ParRed.extra` nor -- this file's content -- an `EtaK` step can fire at a
`c`-headed spine. -/
def PatFreeHeadK (c : Lean.Name) : Prop := ∀ p r, Params.Pat p r → patHeadConst p ≠ c

/-- **The ninth case.**  An `EtaK` step cannot fire at a rule-free constant spine.

This is the whole new obligation `ParRedK` adds over `ParRed` at `ConstSpine.lean`'s
induction, and it is discharged by the *same* hypothesis: `EtaK.matches_head` says an `EtaK`
redex has the head constant of a registered `.app`-pattern's function side, and
`patHeadConst (p₁.app p₂) = patHeadConst p₁` by definition. -/
theorem EtaK.constApp_free {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {as : List VExpr} {e' : VExpr} (hc : PatFreeHeadK c)
    (H : EtaK Γ ((VExpr.const c ls).mkApp as) e') : False := by
  obtain ⟨p₁, p₂, r, f, m1, m2, h1, h2, h3⟩ := H.matches_head
  rw [VExpr.headConst?_mkApp, matches_patHeadConst h2] at h3
  exact hc _ _ h1 (Option.some.inj h3).symm

/-- **`ParRedK` preserves a rule-free constant head**, its levels and its arity.

`Verify/Typing/ConstSpine.lean`'s `ParRed.constApp_inv`, ported constructor-for-constructor,
with the `keta` case added. -/
theorem ParRedK.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHeadK c) :
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
    exact absurd hb constAppK_ne_lam
  | @extra p r e₀ m1 m2 _ m2' h1 h2 _ _ _ =>
    subst he
    have := matches_patHeadConst h2
    rw [VExpr.headConst?_mkApp] at this
    exact absurd (Option.some.inj this).symm (hc _ _ h1)
  | @keta _ e w w' hη _ _ =>
    subst he
    exact absurd hη (fun h => EtaK.constApp_free hc h)
  | bvar => exact absurd he constAppK_ne_bvar
  | sort => exact absurd he constAppK_ne_sort
  | lam => exact absurd he constAppK_ne_lam
  | forallE => exact absurd he constAppK_ne_forallE

/-- The reflexive-transitive form, i.e. `ConstSpine.lean`'s `ParRedS.constApp_inv` over
`ParRedKS`.  This is the statement `IsDefEq.constApp_inv` consumes. -/
theorem ParRedKS.constApp_inv {Γ : List VExpr} {c : Lean.Name} (hc : PatFreeHeadK c)
    {ls : List VLevel} {as : List VExpr} {e' : VExpr}
    (H : ParRedKS Γ ((VExpr.const c ls).mkApp as) e') :
    ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedKS Γ) as as' := by
  induction H with
  | rfl => exact ⟨as, rfl, List.forall₂_reflK (fun _ => ReflTransGen.rfl) as⟩
  | @tail b c₂ h1 h2 ih =>
    obtain ⟨bs, rfl, hbs⟩ := ih
    obtain ⟨cs, rfl, hcs⟩ := ParRedK.constApp_inv hc h2
    exact ⟨cs, rfl, hbs.transK (fun _ _ _ h h' => h.tail h') hcs⟩

end Abstract

/-! ## Anti-vacuity: is `PatFreeHeadK` satisfied for a real reason?

`docs/vacuity-ledger.md` §0: a hypothesis that holds because nothing satisfies its
quantifier proves nothing.  `PatFreeHeadK c` quantifies over the registered pattern table, so
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
empty -- `PatFreeHeadK c` holds for every constant other than the two rule heads. -/
theorem propLoop_patFreeHeadK {c : Lean.Name} (hA : c ≠ `A) (hB : c ≠ `B) :
    PatFreeHeadK c := by
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

/-- **Negative control: `PatFreeHeadK` is load-bearing.**  At the *same* instance, the
head that *does* front a rule violates `ParRedK.constApp_inv`'s conclusion -- `A` reduces to
`B`, which is no `A`-headed spine.  So dropping the hypothesis makes the statement false.

Second half of the control, per `ForallInvPrice.lean`'s discipline: this is **not** a
refutation of `ParRedK.constApp_inv`, because the environment is a legitimate one
(`propLoopEnv_wf : propLoopEnv.WF`) and `PatFreeHeadK `A`` simply fails there
(`propLoop_not_patFreeHeadK`).  The control constrains the hypothesis, not the theorem. -/
theorem propLoop_not_patFreeHeadK : ¬ PatFreeHeadK `A := by
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
