import Lean4Lean.Theory.Typing.Injectivity

/-!
# The `retype` enlargement, priced at the place it is actually paid

`Theory/Typing/Enlarged.lean` prototypes the `retype` rule of `docs/backward-analysis.md` §5
and reports one blocker for making it an **in-place** rule of `Basic.lean`'s `IsDefEq`:

> Adding `retype` to `IsDefEq` forces a matching constructor in `IsDefEqStrong` … **That
> forces one in `HasTypeStrong` too**, because `IsDefEqStrong.hasType'` (`Strong.lean:829`)
> must produce `HasTypeStrong Γ e₂ B` from `HasTypeStrong Γ e₂ A` and `HasTypeStrong Γ e₁ B`
> … And that forces one in `HasTypeStratified`, whose induction is what proves
> `IsDefEq.uniq`.

**The word "forces" is wrong, and this file machine-checks that it is wrong.**  There are two
routes out of `hasType'`'s `retype` case, and this file prices both.

## Route A — discharge the case as a theorem (`HasTypeStrong.retype`)

`HasTypeStrong.retype` below is *exactly* that case, stated over the judgments the tree has
today (no enlargement is needed to state it), and it is **proved, `sorry`-free**, from
`PiInvStratApp` — the narrowed form of `IsDefEqU.forallE_inv_stratified` that
`Theory/Typing/Injectivity.lean` already isolates — together with `VEnv.WF` and `OnCtx`.
It does not use the conversion `IsDefEqStrong Γ e₁ e₂ A` at all.  So no constructor is forced
anywhere: `HasTypeStrong` and `HasTypeStratified` stay exactly as they are, `uniqQ`'s
induction gains no case, and the enlargement introduces **no new open statement**.

**But Route A moves the corner upstream, and that is measured.**  Reverse cones over
declaration *values* (theorem bodies included, `allowOpaque := true`), internal names skipped
— the same convention `scripts/sorry-census.lean` uses — over the import closure of
`Verify/Bridge.lean`:

| declaration | transitive users |
|---|---|
| `IsDefEqU.forallE_inv_stratified` | 201 |
| `IsDefEqStrong.hasType'` | **232** |
| union of the two | 234 |

(The census reports 238 for `forallE_inv_stratified` rather than 201 because it imports
`Experimental.ConeJoin`, a wider scope; the *difference* between the two rows is what matters
and it is stable across both scopes.)  **33 declarations reach `hasType'` without reaching
`forallE_inv_stratified` today.**  Route A adds the edge `hasType' → forallE_inv_stratified`,
so the corner's cone goes **201 → 234**.  Keeping `PiInvStratApp` as an explicit hypothesis
rather than discharging it with `piInvStratApp_axiom` does not help: the same 232 declarations
then carry the hypothesis instead of the edge.  Route A also gives `hasType'` a `VEnv.WF env`
and an `OnCtx Γ (env.IsType U)` premise, which it does not have today — a smaller but real
cost, since `hasType'` is currently the hypothesis-free half of the `Strong.lean` pipeline.

Worse, it destroys the disconnecting set.  Cutting the (E) family of twelve retyping lemmas
(`IsDefEqU.trans/defeqDF/of_l/of_r`, `HasType.defeqU_l/_r`, `IsType.defeqU_l`,
`IsDefEq.trans_l/trans_r/transU_l/transU_r`, `isDefEq_iff`) plus `HasType.piUniq` plus
`IsDefEq.weakN_iff'` takes `forallE_inv_stratified` from 201 to **21**.  The same three cuts
*with* Route A's single new edge leave **104**.  The enlargement exists to disconnect the
corner from `kernel_sound`; Route A re-imports it through a larger door than the one it closes.

## Route B — add the constructor after all

Then `hasType'` is one line and the cost lands in `uniqQ`'s induction, as `Enlarged.lean`
says.  `RetypeCaseCore` below is that case's obligation **in its weakest useful form**: only
the conversion conjunct of `UniqAux`'s conclusion is demanded, the three premises are taken at
a single index, and the index bounds `uniqQ` actually offers are kept (`m < n` for the node's
premises, `n₂ ≤ n` for the competing derivation).  `uniqU_of_retypeCase` then recovers
`IsDefEq.uniq` from it.

This is `Enlarged.uniqU_of_uniqAcross` **with the index bounds kept**, and that is the point:
`docs/handoff-injectivity.md` §4 lists "bound the conversion by height" and "make the
invariant asymmetric" as repairs that were walked to a failing step by *analysis*.  The
collapse here closes them by machine: even the index-bounded, single-conjunct form of the
obligation implies the theorem whose induction it is a case of, so no re-indexing of `uniqQ`
can absorb it.

`retypeCase_of_piInvStratApp` is the other half — the obligation is satisfiable from exactly
the input the tree already pays, so it is the corner restated rather than an absurd demand.

## The structural reason, in one line

`uniqQ` decrements the second derivation's index only by inverting it **against the first
derivation's subject shape** (`intro (.app …)`, `(.bvar …)`, …).  `retype` carries no subject
shape — its premise is a derivation of a *different* term — so `n₂` cannot be decremented, and
the case's obligation is the invariant at the undecremented index.  Every other constructor of
`HasTypeStratified` is subject-directed; `retype` is the only one that is not.

## What would change the verdict  **[open]**

Is `HasTypeStrong.retype` provable **without** `PiInvStratApp`?  If it is, Route A is free and
the 254 → 287 regression above evaporates, and with it the last obstacle to the in-place
enlargement.  No such proof was found here.  The statement does **not** collapse — instantiating
`e₂ := e₁` makes it trivial, so it does not imply `uniq` back the way `RetypeCaseCore` does —
so it is not refuted either.  That is the one open question in this file, and it is the thing
to attack first.

## Axioms

`HasTypeStrong.isType`, `HasTypeStrong.sortConv` → `[propext]`; `uniqStrat_of_retypeCase` →
`[propext, Quot.sound]`; `HasTypeStrong.retype`, `uniqU_of_retypeCase`,
`retypeCase_of_piInvStratApp` → `[propext, Classical.choice, Quot.sound]`.  **No `sorryAx` in
any of them** — re-checked by the `#print axioms` block at the end of the file.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Every `HasTypeStrong` derivation carries a typing of its own type. -/
theorem HasTypeStrong.isType {Γ : List VExpr} {e A : VExpr} {b : Bool}
    (H : env.HasTypeStrong U Γ e A b) :
    ∃ u, env.HasTypeStrong U Γ A (.sort u) true := by
  induction H with
  | bvar _ _ h3 _ => exact ⟨_, h3⟩
  | sort' _ h2 _ => exact ⟨_, .base (.sort' (l := .succ _) (l' := .succ _) h2 h2 rfl)⟩
  | const _ _ _ _ _ h6 _ _ => exact ⟨_, h6⟩
  | app _ _ _ _ _ _ _ h8 _ _ _ _ _ _ => exact ⟨_, h8⟩
  | lam _ _ _ _ _ h6 _ _ _ _ => exact ⟨_, h6⟩
  | forallE h1 h2 _ _ _ _ =>
    exact ⟨_, .base (.sort' (l := .imax _ _) (l' := .imax _ _) ⟨h1, h2⟩ ⟨h1, h2⟩ rfl)⟩
  | base _ ih => exact ih
  | defeq _ _ _ h4 _ _ _ _ => exact ⟨_, h4⟩

/-- Realign the level of a type's own typing. -/
theorem HasTypeStrong.sortConv {Γ : List VExpr} {A : VExpr} {u v : VLevel}
    (hu : u.WF U) (hv : v.WF U) (huv : u ≈ v)
    (H : env.HasTypeStrong U Γ A (.sort u) true) :
    env.HasTypeStrong U Γ A (.sort v) true :=
  .defeq (u := .succ u) hu (.sortDF hu hv huv)
    (.base (.sort' hu hu rfl)) (.base (.sort' hv hu huv.symm)) H

/-- **The `retype` case of `IsDefEqStrong.hasType'`, discharged as a theorem.**

Under an in-place `retype` rule this is the one case of `IsDefEqStrong.hasType'` that is not
mechanical: the node `Γ ⊢ e₁ ≡ e₂ : B` built from `Γ ⊢ e₁ ≡ e₂ : A` and `Γ ⊢ e₁ : B` has
`hasType'.1` free (it *is* the second induction hypothesis), and owes `hasType'.2`, i.e.
`HasTypeStrong Γ e₂ B`.  Note the conversion premise `IsDefEqStrong Γ e₁ e₂ A` is not needed
and is not taken: what the case needs is unique typing at `e₁`, and nothing else. -/
theorem HasTypeStrong.retype {Γ : List VExpr} {e₁ e₂ A B : VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) (hpi : PiInvStratApp env U)
    (h1A : env.HasTypeStrong U Γ e₁ A true)
    (h1B : env.HasTypeStrong U Γ e₁ B true)
    (h2A : env.HasTypeStrong U Γ e₂ A true) :
    env.HasTypeStrong U Γ e₂ B true := by
  obtain ⟨n₁, s1A⟩ := h1A.stratify
  obtain ⟨n₂, s1B⟩ := h1B.stratify
  obtain ⟨u, hAB, v, huv, tA, tB, -⟩ :=
    uniqAux henv hpi _ hΓ (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) s1A s1B
  obtain ⟨uA, sA⟩ := h1A.isType
  obtain ⟨uB, sB⟩ := h1B.isType
  obtain ⟨k₁, tA'⟩ := sA.stratify
  obtain ⟨k₂, tB'⟩ := sB.stratify
  obtain ⟨-, -, -, -, -, -, hcA⟩ :=
    uniqAux henv hpi _ hΓ (Nat.le_max_left k₁ _) (Nat.le_max_right k₁ _) tA' tA
  obtain ⟨-, -, -, -, -, -, hcB⟩ :=
    uniqAux henv hpi _ hΓ (Nat.le_max_left k₂ _) (Nat.le_max_right k₂ _) tB' tB
  have huAu : uA ≈ u := hcA _ _ rfl rfl
  have huBv : uB ≈ v := hcB _ _ rfl rfl
  have hu : u.WF U := hAB.sort_r henv.ordered hΓ
  have huA : uA.WF U := sA.hasType.sort_r henv.ordered hΓ
  have huB : uB.WF U := sB.hasType.sort_r henv.ordered hΓ
  exact .defeq hu (hAB.strong henv.ordered hΓ)
    (sA.sortConv huA hu huAu) (sB.sortConv huB hu (huBv.trans huv.symm)) h2A


/-! ## Route B: the obligation a `retype` *constructor* would create -/

/-- The **weakest useful form** of the obligation that a `retype` constructor on
`HasTypeStratified` creates in `uniqQ`'s induction, with the index bounds the induction
actually offers: the node concludes at `n₁ ≤ n`, so its premises sit at `n₁ - 1 < n`, and the
competing derivation `H2` sits at `n₂ ≤ n`.  Only the conversion conjunct is demanded — the
`HasTypeStratified` components and the sort conjunct of `UniqAux` are dropped, so anything
proved *from* this is proved from less than the real obligation. -/
def RetypeCaseCore (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ A B B' : VExpr} {m n₂ : Nat},
    OnCtx Γ (env.IsType U) → m < n → n₂ ≤ n →
    env.IsDefEq U Γ e₁ e₂ A →
    env.HasTypeStratified U Γ e₁ A true m →
    env.HasTypeStratified U Γ e₂ A true m →
    env.HasTypeStratified U Γ e₁ B true m →
    env.HasTypeStratified U Γ e₂ B' true n₂ →
    ∃ u, env.IsDefEq U Γ B B' (.sort u)

/-- **The collapse, step one.**  The obligation, at *every* index, gives unique typing for
two `HasTypeStratified` derivations of one term at unrelated indices. -/
theorem uniqStrat_of_retypeCase (H : ∀ n, RetypeCaseCore env U n)
    {Γ : List VExpr} {e A B : VExpr} {n₁ n₂ : Nat} (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.HasTypeStratified U Γ e A true n₁)
    (h2 : env.HasTypeStratified U Γ e B true n₂) :
    ∃ u, env.IsDefEq U Γ A B (.sort u) :=
  H (max n₁ n₂ + 1) (m := n₁) (n₂ := n₂) hΓ
    (Nat.lt_succ_of_le (Nat.le_max_left ..)) (Nat.le_succ_of_le (Nat.le_max_right ..))
    h1.hasType h1 h1 h1 h2

/-- **The collapse.**  `IsDefEq.uniq` — the theorem whose induction the `retype` case belongs
to — follows from the case's own obligation.  This is the collapse test of `ORCHESTRATOR.md`
rule 5, run with the index bounds kept, which is what distinguishes it from
`Enlarged.uniqU_of_uniqAcross`. -/
theorem uniqU_of_retypeCase (henv : VEnv.WF env) (H : ∀ n, RetypeCaseCore env U n)
    {Γ : List VExpr} {e₁ e₂ e₃ A B : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := by
  obtain ⟨_, s1⟩ := (h1.strong henv.ordered hΓ).hasType'.2.stratify
  obtain ⟨_, s2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  have ⟨_, h⟩ := uniqStrat_of_retypeCase H hΓ s1 s2
  exact ⟨_, h⟩

/-- …and conversely the obligation is satisfiable from exactly the input the tree already
pays, so it is not an absurd demand: it is the corner restated. -/
theorem retypeCase_of_piInvStratApp (henv : VEnv.WF env) (hpi : PiInvStratApp env U) :
    ∀ n, RetypeCaseCore env U n := by
  intro n Γ e₁ e₂ A B B' m n₂ hΓ _ _ _ a1 a2 a3 a4
  obtain ⟨u₁, hAB, -, -, tA₁, -, -⟩ :=
    uniqAux henv hpi m hΓ (Nat.le_refl _) (Nat.le_refl _) a1 a3
  obtain ⟨u₂, hAB', -, -, tA₂, -, -⟩ :=
    uniqAux henv hpi _ hΓ (Nat.le_max_left m n₂) (Nat.le_max_right m n₂) a2 a4
  obtain ⟨-, -, -, -, -, -, hc⟩ :=
    uniqAux henv hpi _ hΓ (Nat.le_max_left _ _) (Nat.le_max_right _ _) tA₁ tA₂
  exact ⟨u₁, hAB.symm.trans (.defeqDF (.sortDF (hAB'.sort_r henv.ordered hΓ)
    (hAB.sort_r henv.ordered hΓ) (hc _ _ rfl rfl).symm) hAB')⟩

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.HasTypeStrong.isType
#print axioms Lean4Lean.VEnv.HasTypeStrong.sortConv
#print axioms Lean4Lean.VEnv.HasTypeStrong.retype
#print axioms Lean4Lean.VEnv.uniqStrat_of_retypeCase
#print axioms Lean4Lean.VEnv.uniqU_of_retypeCase
#print axioms Lean4Lean.VEnv.retypeCase_of_piInvStratApp
end Audit
