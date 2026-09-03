import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Pattern head constants, and `PatFreeHead` — moved down out of `Verify/`

Everything in this file used to live in `Verify/Typing/ConstSpine.lean` and is **unchanged
text**: the declarations were relocated, not restated.  Their qualified names, statements and
proof terms are identical, and `docs/handoff-patk.md` records the `#print axioms` reading
before and after the move.

**Why the move.**  `Theory/` may not import `Verify/`, and three separate `Theory/` files had
each grown their own copy of `Pattern.headConst` for that reason:

* `Theory/Typing/KMeasure.lean`'s `Pattern.headName` — same four-line recursion, with a
  docstring saying the collision with `ConstSpine.lean` is deliberate;
* `Theory/Typing/DescendConstSpineK.lean`'s `patHeadConst`, `matches_patHeadConst`,
  `PatFreeHeadK`, `constAppK_ne_*`, `List.Forall₂.transK`, `List.forall₂_reflK` — six copies,
  now deleted, that file having been the one that needed `PatFreeHead` on
  `kernel_sound`'s critical-path chain;
* `Theory/Typing/StructureRuleFree.lean`'s `VExpr.headConst?_mkLams_eq`, whose own docstring
  gives the same reason for the same duplication one level down.

None of the moved declarations mentions anything from `Verify/`: they are statements about
`Pattern`, `VExpr` and the `Params` class, all of which are `Theory/`.  `ChurchRosser.lean` is
the single import needed (it is where `Params` is declared, and its cone already contains
`Theory/Typing/Injectivity.lean`, which supplies `VExpr.headConst?` and `VExpr.spineHead`).
-/

namespace Lean4Lean

open VExpr

/-- The head constant of a *pattern* — its leftmost `const` leaf. -/
def Pattern.headConst : Pattern → Lean.Name
  | .const c => c
  | .app f _ => f.headConst
  | .var f => f.headConst

/-- A matched term's head constant is the pattern's. -/
theorem Pattern.Matches.headConst {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.headConst? = some p.headConst := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih1 _ => exact ih1

theorem VExpr.constApp_ne_lam {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A b : VExpr} :
    (VExpr.const c ls).mkApp as ≠ .lam A b := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_bvar {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {i : Nat} :
    (VExpr.const c ls).mkApp as ≠ .bvar i := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_sort {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel} :
    (VExpr.const c ls).mkApp as ≠ .sort u := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

theorem VExpr.constApp_ne_forallE {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    {A B : VExpr} : (VExpr.const c ls).mkApp as ≠ .forallE A B := by
  intro h
  have := congrArg VExpr.spineHead h
  rw [VExpr.spineHead_mkApp] at this
  exact absurd this nofun

/-- `List.Forall₂` at a reflexive relation. -/
theorem _root_.List.forall₂_refl' {α} {R : α → α → Prop} (hR : ∀ a, R a a) :
    ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | _ :: l => .cons (hR _) (List.forall₂_refl' hR l)

/-- Composing two `List.Forall₂`s. -/
theorem _root_.List.Forall₂.trans' {α} {R S T : α → α → Prop}
    (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ → List.Forall₂ T l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (List.Forall₂.trans' h t1 t2)

namespace VEnv

variable [Params]
open Params

/-- **`c` heads no registered rewrite pattern.**

This is the `Params`-level form of `RuleFreeHead`: `WHRed.extra` / `ParRed.extra` fire on a
`Pat`-registered pattern, and what stops them from firing at a `c`-headed spine is that no
registered pattern has `c` as its head constant.  `Verify/Typing/ConstSpine.lean`'s
`VEnv.RuleFreeHead.patFreeHead` derives it from `VEnv.RuleFreeHead` for the canonical pattern
table.  (That cross-reference is the only text changed by the move; the statement and proof
term are verbatim.) -/
def PatFreeHead (c : Lean.Name) : Prop := ∀ p r, Params.Pat p r → p.headConst ≠ c

end VEnv

end Lean4Lean
