import Lean4Lean.Theory.Typing.LogRelRowZero
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.SortUniq

/-!
# The δ-cycle and the conversion relation are independent

Follow-up to `Theory/Typing/LogRelRowZero.lean` and `docs/logrel-scope.md` §1, which
exhibit a `VEnv.WF` environment `loopEnv` — one `.unsafeDef` step from empty — whose
weak-head reduction has a two-cycle, and conclude that *no normalisation argument can
establish `Theory/Typing/Injectivity.lean`'s statements as stated*.

That conclusion is about **reduction**.  This file checks what the same witness does to
**conversion**, which is what those statements are actually about, and the answer is
*nothing*:

* `loop_conv_iff` — `loopEnv.IsDefEq` and `loopEnv2.IsDefEq` are the **same relation**.
  `loopEnv2` is `loopEnv` minus both defining equations.
* `loopEnv2_no_defeqs` — `loopEnv2` has no definitional-equality rule at all, so no
  `HeadStep.delta` and no cycle.
* `loopEnv2_wf_noUnsafe` — and it is well formed by two `.axiom` steps, with no
  `unsafeDef` anywhere in its declaration list.
* `sort_inv_transfer` — so `sort_inv` at `loopEnv` **is** `sort_inv` at a cycle-free,
  `noUnsafe` environment.  Same for the other five statements: they are all statements
  about `IsDefEqU`, and `loopEnv_conv_iff` transfers each in one line.

The reason is one line long: `loopEnv`'s two members are *proofs of one proposition*
(`falseProp`), and `IsDefEq.proofIrrel` identifies any two proofs of a proposition, with no
rule in the environment at all.  The block's rules were redundant before they were added.

**What this does and does not settle.**  It does *not* revive the logical-relation route
(`docs/logrel-scope.md`'s verdict rests on two further reasons, §§3–4 there), and it does
*not* show that every `.unsafeDef` environment is conversion-equivalent to a cycle-free one.
It settles that **the published witness does not support the claim made from it**: at
`loopEnv` the injectivity targets are not harder than at an axiom-only environment, so
that witness is no evidence that they need re-cutting.

## The second witness, for whoever re-runs the check

`propLoopEnv` is the same one-step-from-empty `unsafeDef` with the members declared at
`.sort .zero` instead of at `falseProp`: `A : Prop := B`, `B : Prop := A`.  Now `A` and `B`
are *propositions*, not proofs, so the collapse recipe would need `Γ ⊢ .sort .zero :
.sort .zero` — a sort that is a proof (`propLoop_no_direct_collapse`).  The reduction cycle
survives (`propLoop_headStep_not_wf`).  If the row-zero check of `docs/logrel-scope.md` §1
is to be restated, this is the witness to restate it at.

*Confidence: everything above is machine-checked, sorry-free, `[propext, Quot.sound]`,
except `propLoop_no_direct_collapse`'s hypothesis `SortUniq` (open) and the claim that
`propLoopEnv`'s cycle is a genuinely new conversion, which is **not** proved — only that
this file's collapse argument does not reach it.*
-/

namespace Lean4Lean

/-- `falseProp` is a *proposition*, at the literal level `.zero` that `proofIrrel` demands
(`falseProp_isType` only gives `∃ u`, and the `u` it gives is `imax 1 0`, not `zero`), in
any context. -/
theorem falseProp_isProp (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ falseProp (.sort .zero) := by
  have h : env.HasType U Γ falseProp (.sort (.imax (.succ .zero) .zero)) :=
    VEnv.IsDefEq.forallEDF (u := .succ .zero) (v := .zero)
      (.sortDF trivial trivial rfl) (.bvar .zero)
  exact .defeqDF (.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial (funext fun _ => rfl)) h

/-- `hasType_constFalse` in an arbitrary context. -/
theorem hasType_constFalse' {env : VEnv} {c : Name} {U : Nat} {Γ : List VExpr}
    (h : env.constants c = some ⟨0, falseProp⟩) : env.HasType U Γ (.const c []) falseProp :=
  VEnv.IsDefEq.constDF (ci := ⟨0, falseProp⟩) h nofun nofun rfl .nil

/-- **The cycle's two rules are redundant.** In `loopEnv2` — the same environment *without*
the two circular defining equations — `f` and `g` are already definitionally equal, by
`proofIrrel` alone: they are two proofs of the same proposition. -/
theorem loop_defeq_without_rules (U : Nat) (Γ : List VExpr) :
    loopEnv2.IsDefEq U Γ (.const `f []) (.const `g []) falseProp :=
  .proofIrrel (falseProp_isProp ..) (hasType_constFalse' loopEnv2_f)
    (hasType_constFalse' loopEnv2_g)

theorem loopEnv2_le : loopEnv2 ≤ loopEnv := ⟨id, fun h => .inr (.inr h)⟩

/-- **The δ-cycle adds no conversions.**  Every conversion of `loopEnv` — the environment
`LogRelRowZero.lean` builds, whose weak-head reduction has a two-cycle — already holds in
`loopEnv2`, which carries the same two constants but *neither* defining equation.  So the
two relations coincide (`loop_conv_iff`).

The reason is that both rules live at `falseProp`, a proposition, where `proofIrrel`
identifies the two sides anyway.  The cycle therefore breaks *reduction* without enlarging
*conversion*. -/
theorem loop_conv_collapse {U Γ e₁ e₂ A} (H : loopEnv.IsDefEq U Γ e₁ e₂ A) :
    loopEnv2.IsDefEq U Γ e₁ e₂ A := by
  induction H with
  | bvar h => exact .bvar h
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | @extra df ls _ h1 _ h3 =>
    obtain rfl | rfl | h1 := h1
    · cases List.eq_nil_of_length_eq_zero h3
      exact (loop_defeq_without_rules ..).symm
    · cases List.eq_nil_of_length_eq_zero h3
      exact loop_defeq_without_rules ..
    · exact absurd h1 nofun

theorem loop_conv_iff {U Γ e₁ e₂ A} :
    loopEnv.IsDefEq U Γ e₁ e₂ A ↔ loopEnv2.IsDefEq U Γ e₁ e₂ A :=
  ⟨loop_conv_collapse, VEnv.IsDefEq.mono loopEnv2_le⟩

theorem loopEnv_conv_iff {U Γ e₁ e₂} :
    loopEnv.IsDefEqU U Γ e₁ e₂ ↔ loopEnv2.IsDefEqU U Γ e₁ e₂ :=
  ⟨fun ⟨_, h⟩ => ⟨_, loop_conv_collapse h⟩, VEnv.IsDefEqU.mono loopEnv2_le⟩

/-- `loopEnv2` carries **no definitional-equality rule at all**, so its `HeadStep` has no
`delta` step and the two-cycle is gone. -/
theorem loopEnv2_no_defeqs {df} : ¬ loopEnv2.defeqs df := nofun

/-- **…and `loopEnv2` is well formed without `unsafeDef`** — two `.axiom` steps from the
empty environment.  So the cycling environment of `LogRelRowZero.lean` is
conversion-equivalent to a rule-free, `noUnsafe` one. -/
theorem loopEnv2_wf_noUnsafe :
    ∃ ds, VEnv.WF' ds loopEnv2 ∧ ∀ d ∈ ds, d.noUnsafe := by
  refine ⟨[.axiom ⟨⟨0, falseProp⟩, `g⟩, .axiom ⟨⟨0, falseProp⟩, `f⟩], ?_, ?_⟩
  · exact .decl (.axiom (ci := ⟨⟨0, falseProp⟩, `g⟩) (falseProp_isType _) loopEnv2_eq)
      (.decl (.axiom (ci := ⟨⟨0, falseProp⟩, `f⟩) (falseProp_isType _) loopEnv1_eq) .empty)
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain rfl | rfl := hd <;> trivial

theorem loopEnv2_wf : loopEnv2.WF := let ⟨_, h, _⟩ := loopEnv2_wf_noUnsafe; ⟨_, h⟩

/-! ## What the environment class is *not* responsible for

`sort_inv`'s only open cases are `trans` and `proofIrrel`.  `proofIrrel` is dangerous
exactly when propositions are inhabited — and that is available **over the empty
environment**, from the context alone, which `sort_inv` quantifies over with only
`OnCtx Γ (env.IsType U)`.  So no restriction on the environment removes it. -/

theorem empty_ctx_inconsistent :
    OnCtx [falseProp] (VEnv.empty.IsType 0) ∧
    VEnv.empty.HasType 0 [falseProp] (.bvar 0) falseProp :=
  ⟨⟨trivial, falseProp_isType _⟩, .bvar .zero⟩

/-! ## A cycle the collapse argument does *not* reach

`loop_conv_collapse` works because both members of `LogRelRowZero.lean`'s block are *proofs*
of one proposition.  Declare the members at type `.sort .zero` instead and they are
*propositions*, not proofs, so `proofIrrel` — which needs `Γ ⊢ p : .sort .zero` for the
common type — cannot apply to them.  The block below is the same one-step-from-empty
`unsafeDef`, re-aimed so that the row-zero check of `docs/logrel-scope.md` §1 stands at a
witness where the collapse does not. -/

/-- `A : Prop`, defined to be `B`. -/
def propLoopA : VDefVal := ⟨⟨⟨0, .sort .zero⟩, `A⟩, .const `B []⟩

/-- `B : Prop`, defined to be `A`. -/
def propLoopB : VDefVal := ⟨⟨⟨0, .sort .zero⟩, `B⟩, .const `A []⟩

def propLoopEnv1 : VEnv :=
  { VEnv.empty with
    constants := fun n => if `A = n then some ⟨0, .sort .zero⟩ else VEnv.empty.constants n }

def propLoopEnv2 : VEnv :=
  { propLoopEnv1 with
    constants := fun n => if `B = n then some ⟨0, .sort .zero⟩ else propLoopEnv1.constants n }

def propLoopEnv : VEnv := propLoopEnv2.addDefEqs [propLoopA, propLoopB]

theorem propLoopEnv_addConsts : VEnv.empty.addConsts [propLoopA, propLoopB] = some propLoopEnv2 :=
  rfl

theorem propLoopEnv2_A : propLoopEnv2.constants `A = some ⟨0, .sort .zero⟩ := rfl
theorem propLoopEnv2_B : propLoopEnv2.constants `B = some ⟨0, .sort .zero⟩ := rfl

theorem propLoopEnv_A : propLoopEnv.constants `A = some ⟨0, .sort .zero⟩ := propLoopEnv2_A
theorem propLoopEnv_B : propLoopEnv.constants `B = some ⟨0, .sort .zero⟩ := propLoopEnv2_B

theorem hasType_constProp {env : VEnv} {c : Name} {U Γ}
    (h : env.constants c = some ⟨0, .sort .zero⟩) :
    env.HasType U Γ (.const c []) (.sort .zero) :=
  VEnv.IsDefEq.constDF (ci := ⟨0, .sort .zero⟩) h nofun nofun rfl .nil

theorem propLoop_wf : VDecl.WF VEnv.empty (.unsafeDef [propLoopA, propLoopB]) propLoopEnv := by
  refine .unsafeDef (fun ci hci ↦ ?_) propLoopEnv_addConsts (fun ci hci ↦ ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    obtain rfl | rfl := hci <;> exact ⟨.succ .zero, .sortDF trivial trivial rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    obtain rfl | rfl := hci
    · exact hasType_constProp (env := propLoopEnv2) (c := `B) propLoopEnv2_B
    · exact hasType_constProp (env := propLoopEnv2) (c := `A) propLoopEnv2_A

theorem propLoopEnv_wf : propLoopEnv.WF := ⟨_, .decl propLoop_wf .empty⟩

theorem propLoopEnv_defeqs_A : propLoopEnv.defeqs propLoopA.toDefEq := .inr (.inl rfl)
theorem propLoopEnv_defeqs_B : propLoopEnv.defeqs propLoopB.toDefEq := .inl rfl

theorem propLoop_step_AB : propLoopEnv.HeadStep (.const `A []) (.const `B []) :=
  .delta (ls := []) propLoopEnv_defeqs_A rfl

theorem propLoop_step_BA : propLoopEnv.HeadStep (.const `B []) (.const `A []) :=
  .delta (ls := []) propLoopEnv_defeqs_B rfl

/-- Both cycling terms are **propositions**, not proofs: they are typed at `.sort .zero`,
so `IsDefEq.proofIrrel` — whose common type must itself be a proposition — cannot identify
them the way it identifies `LogRelRowZero.lean`'s `f` and `g`. -/
theorem propLoop_isProp :
    propLoopEnv.HasType 0 [] (.const `A []) (.sort .zero) ∧
    propLoopEnv.HasType 0 [] (.const `B []) (.sort .zero) :=
  ⟨hasType_constProp propLoopEnv_A, hasType_constProp propLoopEnv_B⟩

/-- **…and the collapse recipe does not apply to it.**  `loop_conv_collapse` derives a
rule `lhs ≡ rhs : T` from `proofIrrel` at `T`, which needs `Γ ⊢ T : .sort .zero`.  Here
`T = .sort .zero`, so the recipe would need a *sort* to be a proof — which
`VEnv.sort_not_proof` refutes, given universe uniqueness.

*Confidence: this rules out the specific recipe `loop_conv_collapse` uses, not every
derivation of `A ≡ B` in the rule-free environment.  Trap #8: "not collapsible by this
argument", not "provably a new conversion".* -/
theorem propLoop_no_direct_collapse {U Γ} (huniq : propLoopEnv.SortUniq U)
    (hΓ : OnCtx Γ (propLoopEnv.IsType U)) :
    ¬ propLoopEnv.HasType U Γ (.sort .zero) (.sort .zero) :=
  fun h => VEnv.sort_not_proof huniq propLoopEnv_wf.ordered hΓ h h

/-- **The row-zero check, re-run at a cycle between propositions.** -/
theorem propLoop_headStep_not_wf : ¬ WellFounded (fun a b => propLoopEnv.HeadStep b a) := by
  intro h
  suffices H : ∀ x : VExpr, Acc (fun a b => propLoopEnv.HeadStep b a) x →
      x ≠ .const `A [] ∧ x ≠ .const `B [] from (H _ (h.apply _)).1 rfl
  intro x hx
  induction hx with
  | intro y _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro rfl
    · exact (ih _ propLoop_step_AB).2 rfl
    · exact (ih _ propLoop_step_BA).1 rfl

/-- **Consequence, and the point of the file.**  Every open statement of
`Theory/Typing/Injectivity.lean` is a statement about `IsDefEqU`.  At the `LogRelRowZero`
witness those statements are *literally the same statements* at `loopEnv2`, which has no
δ-rule and no `unsafeDef` step.  Spelled out for `sort_inv`; the same one-line transfer
works for each of the six. -/
theorem sort_inv_transfer {U Γ u v} :
    (loopEnv2.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v) ↔
    (loopEnv.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v) :=
  ⟨fun h h' => h (loopEnv_conv_iff.1 h'), fun h h' => h (loopEnv_conv_iff.2 h')⟩

end Lean4Lean
