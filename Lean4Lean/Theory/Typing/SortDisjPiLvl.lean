import Lean4Lean.Theory.Typing.AppUniqRefute
import Lean4Lean.Theory.Typing.SortRedApp

/-!
# `SortDisjInvN` at `piLvlEnv`: the route is **closed, not expensive**

`docs/handoff-sortinv-route.md` §13.7 leaves open whether `piLvlEnv` — the `Ordered`
environment at which `∀ n, AppUniqLvl` is false (`Theory/Typing/AppUniqRefute.lean`) —
satisfies `SortDisjInvN` at index 1, and §15 item 1 calls it "the cheapest thing that changes
the meaning of §13".  **It is the most expensive thing on that list.**

What this file establishes, all machine-checked:

1. **The environment contributes nothing.**  `piLvlEnv`'s rule is *invisible* to the
   `SortRed` predicate that `Theory/Typing/SortClauses.lean` §4 uses for exactly this job:
   `extraSortRed_piLvlEnv` is free (both sides of the rule are Π-types, and `instL` keeps a Π a
   Π), and the rule cannot fire at any of the four positions of the one open residual
   (`piLvl_rule_not_pi_typed0`, `piLvl_rule_sides_not_one_type0`).
2. **So `SortDisjInvN piLvlEnv 0 1` reduces to `SortRedAppDF piLvlEnv 0 0`** — which is the
   *same* open statement that `docs/handoff-sortred.md` leaves open over `∅`, equivalent
   (`piLvlEnv_sortRedAppDF_iff`, `piLvlEnv_chain`) to the whole of `SortRedInv piLvlEnv 0 1`.
   Graded: every link is an `↔`, so this is a **reformulation, not a reduction**.
3. **And it is at least as hard**: conversions transfer up an environment extension
   (`Stratified.mono_env`), so `SortInvN piLvlEnv 0 1 → SortInvN ∅ 0 1`
   (`sortDisjInvN_le`) — proving item (c) *proves* the long-open empty-environment clause at
   index 1.
4. **The `beta` case is free**, contrary to §13.6 item 3: `SortRed.beta_iff` closes it and
   `trans` composes two `Iff`s.  The obstruction is the **`appDF`** case, i.e. weak-head
   λ-exposure invariance (`SortRedLamExpose`), not `beta`.
5. **A new refutation that tightens the corner**: the spine predicate with each argument
   `⊢₀`-typed at *some* type — the natural first repair after `spineInv_one_false` —
   is **also false** (`spineInvTyped_one_false`).  So the argument typing must be tied to the
   function's *domain*, which a `trans` midpoint cannot supply.

6. **A second necessary sub-obligation of the residual, apparently unrecorded**: it also demands
   *argument replacement* (`SortRedArgSwap`, §9), which is non-trivial already at `f = f'` and is
   `SubstC`-shaped — and `SubstC` is false.  So the residual is not purely about λ-exposure.

Nothing here proves or refutes `SortDisjInvN piLvlEnv 0 1`; §"Verdict" says exactly why.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. Conversions transfer up an environment extension

Not in `Theory/Typing/Stratified.lean`: `Stratified.mono` is monotonicity in the *index*.  Only
`const` and `extra` mention the environment, and `VEnv.LE` covers both. -/

theorem Stratified.mono_env {env env' : VEnv} (le : env ≤ env') {U m : Nat}
    {Γ : List VExpr} {e₁ e₂ : VExpr} {b : Bool} (H : Stratified env U m Γ e₁ e₂ b) :
    Stratified env' U m Γ e₁ e₂ b := by
  induction H with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const (le.constants h1) h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE h1 h2 ih1 ih2
  | conv _ _ ih1 ih2 => exact .conv ih1 ih2
  | rfl => exact .rfl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF (le.constants h1) h2 h3 h4 h5
  | appDF _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .appDF ih1 ih2 ih3 ih4 ih5 ih6
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra (le.defeqs h1) h2 h3

/-- Clause (1) is **antitone** in the environment: the larger environment's statement is the
stronger one. -/
theorem SortInvN.mono_env {env env' : VEnv} (le : env ≤ env') (h : SortInvN env' U n) :
    SortInvN env U n := fun hc => h (hc.mono_env le)

theorem SortForallEDisjN.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : SortForallEDisjN env' U n) : SortForallEDisjN env U n :=
  fun hc => h (hc.mono_env le)

theorem SortDisjInvN.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : SortDisjInvN env' U n) : SortDisjInvN env U n :=
  ⟨SortInvN.mono_env le h.sort, SortForallEDisjN.mono_env le h.sort_forallE⟩


/-! ## 2. `piLvlEnv`'s rule is invisible to `SortRed`

Both sides of `piLvlRule` are Π-types, and `instL` keeps a Π a Π, so neither side weak-head
reduces to anything at all.  The `extra` residual of `SortClauses.sortRedInv_of` is therefore
free at this environment — the *first* of the four residuals that is environment-dependent,
and the only one that could have made `piLvlEnv` different from `∅`. -/

theorem extraSortRed_piLvlEnv : ExtraSortRed piLvlEnv := by
  intro df ls u h
  have hshape : (∃ A B, df.lhs = .forallE A B) ∧ ∃ A B, df.rhs = .forallE A B := by
    rcases h with rfl | h
    · exact ⟨⟨_, _, rfl⟩, _, _, rfl⟩
    · exact h.elim
  obtain ⟨⟨A, B, h1⟩, C, D, h2⟩ := hshape
  rw [h1, h2]
  simp only [VExpr.instL]
  exact ⟨(absurd · SortRed.not_forallE), (absurd · SortRed.not_forallE)⟩

/-! ### …and it cannot fire at any position of the one open residual

`SortRedAppDF`'s four typing premises are `⊢₀` derivations: `f`, `f'` at one Π-type and `a`,
`a'` at one type.  A Π-type is never `⊢₀`-typed at a Π-type, so the rule's sides cannot be the
`f`/`f'` of an `appDF`; and their `⊢₀` types differ *syntactically*, so they cannot be its
`a`/`a'` either.  (`⊢₀` types are unique — `HasTypeN.uniq_zero`.) -/

/-- Companion to `forallE_not_prop0`: a Π-type is never `⊢₀`-typed at a Π-type. -/
theorem forallE_not_pi0 {Γ : List VExpr} {A B C D : VExpr} :
    ¬ env.HasTypeN U 0 Γ (.forallE A B) (.forallE C D) := by
  intro h
  obtain ⟨u, v, _, _, _, _, hc⟩ := h.forallE_inv
  exact nomatch IsDefEqN.zero_iff.1 hc

theorem piLvlL_type0 {Γ : List VExpr} : piLvlEnv.HasTypeN 0 0 Γ piLvlL
    (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  Stratified.forallE trivial trivial (Stratified.sort trivial) (Stratified.sort trivial)

theorem piLvlR_type0 {Γ : List VExpr} : piLvlEnv.HasTypeN 0 0 Γ piLvlR
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  Stratified.forallE trivial trivial (Stratified.sort trivial) (Stratified.sort trivial)

/-- The rule's sides are not `⊢₀`-typed at a Π-type — so `extra` cannot be the `f ≡ f'`
premise of an `appDF`. -/
theorem piLvl_rule_not_pi_typed0 {Γ : List VExpr} {C D : VExpr} :
    ¬ piLvlEnv.HasTypeN 0 0 Γ piLvlL (.forallE C D) ∧
    ¬ piLvlEnv.HasTypeN 0 0 Γ piLvlR (.forallE C D) :=
  ⟨forallE_not_pi0, forallE_not_pi0⟩

/-- The rule's sides have **different** `⊢₀` types — `.sort (.imax 2 1)` and
`.sort (.imax 2 2)`, which are `≈` but not equal — so `extra` cannot be the `a ≡ a'` premise of
an `appDF` either, whose two arguments share one `⊢₀` type. -/
theorem piLvl_rule_sides_not_one_type0 {Γ : List VExpr} :
    ¬ ∃ T, piLvlEnv.HasTypeN 0 0 Γ piLvlL T ∧ piLvlEnv.HasTypeN 0 0 Γ piLvlR T := by
  intro ⟨T, h1, h2⟩
  have e1 := HasTypeN.uniq_zero h1 piLvlL_type0
  have e2 := HasTypeN.uniq_zero h2 piLvlR_type0
  rw [e1] at e2
  injection e2 with e2
  exact absurd e2 (by simp)


/-! ## 3. The reduction, and the fact that every link in it is an equivalence

`SortClauses.sortRedInv_of` needs four residuals at index `0`.  Three are free at any
`Ordered` environment, and §2 makes the fourth — the environment-dependent one — free here.
What is left is `SortRedAppDF piLvlEnv 0 0`, and by `SortRedApp.lean` §§8–9 that is *equal*
to its closed-sort-codomain branch and to `SortRedLamExpose piLvlEnv 0 0`. -/

theorem piLvlEnv_sortRedInv_one_of_appDF (h1 : SortRedAppDF piLvlEnv 0 0) :
    SortRedInv piLvlEnv 0 1 :=
  fun hc => sortRedInv_of hc 0 rfl h1 (PiTypedNotSortRed.zero piLvlEnv_ordered)
    (ProofNotSortRed.zero piLvlEnv_ordered) extraSortRed_piLvlEnv rfl _

/-- **The residual is equivalent to the whole reduction at `piLvlEnv`**, exactly as
`SortRedApp.empty_sortRedAppDF_iff` is over `∅`.  So nothing below is a strength reduction. -/
theorem piLvlEnv_sortRedAppDF_iff : SortRedAppDF piLvlEnv 0 0 ↔ SortRedInv piLvlEnv 0 1 :=
  ⟨piLvlEnv_sortRedInv_one_of_appDF, sortRedAppDF_of_sortRedInv⟩

/-- The full chain at `piLvlEnv`, all `↔` — the analogue of `SortRedApp.empty_chain`. -/
theorem piLvlEnv_chain :
    (SortRedLamExpose piLvlEnv 0 0 ↔ SortRedAppDFSort piLvlEnv 0 0) ∧
    (SortRedAppDFSort piLvlEnv 0 0 ↔ SortRedAppDF piLvlEnv 0 0) ∧
    (SortRedAppDF piLvlEnv 0 0 ↔ SortRedInv piLvlEnv 0 1) :=
  ⟨(sortRedAppDFSort_iff_lamExpose piLvlEnv_ordered).symm,
    (sortRedAppDF_iff_sortBranch piLvlEnv_ordered).symm, piLvlEnv_sortRedAppDF_iff⟩

theorem piLvlEnv_sortInvN_one_of_appDF (h1 : SortRedAppDF piLvlEnv 0 0) :
    SortInvN piLvlEnv 0 1 :=
  sortInvN_of_sortRedInv (piLvlEnv_sortRedInv_one_of_appDF h1)

theorem piLvlEnv_sortForallEDisjN_one_of_appDF (h1 : SortRedAppDF piLvlEnv 0 0) :
    SortForallEDisjN piLvlEnv 0 1 :=
  sortForallEDisjN_of_sortRedInv (piLvlEnv_sortRedInv_one_of_appDF h1)

/-- **§13.7's question, answered conditionally**: `SortDisjInvN piLvlEnv 0 1` holds iff the
residual does — and the residual is the statement `docs/handoff-sortred.md` leaves open over
`∅`. -/
theorem piLvlEnv_sortDisjInvN_one_of_appDF (h1 : SortRedAppDF piLvlEnv 0 0) :
    SortDisjInvN piLvlEnv 0 1 :=
  ⟨piLvlEnv_sortInvN_one_of_appDF h1, piLvlEnv_sortForallEDisjN_one_of_appDF h1⟩

theorem piLvlEnv_sortDisjInvN_one_of_lamExpose (h : SortRedLamExpose piLvlEnv 0 0) :
    SortDisjInvN piLvlEnv 0 1 :=
  piLvlEnv_sortDisjInvN_one_of_appDF
    (sortRedAppDF_of_sortBranch piLvlEnv_ordered
      (sortRedAppDFSort_of_lamExpose piLvlEnv_ordered h))

/-! ## 4. …and it is at least as hard as the empty-environment clause

`∅ ≤ piLvlEnv`, so every `⊢₁` conversion over `∅` is one over `piLvlEnv`: clause (1) and clause
(3) at `piLvlEnv` are the **stronger** statements.  Proving item (c) therefore *proves*
`SortInvN ∅ 0 1` and `SortForallEDisjN ∅ 0 1` — the goals open since
`Theory/Typing/DefInvRefute.lean`.  This is what makes the item expensive rather than cheap. -/

theorem empty_le_piLvlEnv : (∅ : VEnv) ≤ piLvlEnv := VEnv.addDefEq_le

theorem sortInvN_le (h : SortInvN piLvlEnv 0 1) : SortInvN ∅ 0 1 :=
  SortInvN.mono_env empty_le_piLvlEnv h

theorem sortForallEDisjN_le (h : SortForallEDisjN piLvlEnv 0 1) : SortForallEDisjN ∅ 0 1 :=
  SortForallEDisjN.mono_env empty_le_piLvlEnv h

theorem sortDisjInvN_le (h : SortDisjInvN piLvlEnv 0 1) : SortDisjInvN ∅ 0 1 :=
  SortDisjInvN.mono_env empty_le_piLvlEnv h

/-! ## 5. The separation §13.7 wanted, as a conditional theorem

Both forms are stated, because they cost different things.  The **index-local** form needs one
open residual; the **`∀ n`** form needs three open families, since `PiTypedNotSortRed` and
`ProofNotSortRed` are discharged only at index `0`. -/

/-- The index-1 separation: at `piLvlEnv`, clause (1)+(3) at index 1 hold (conditionally) while
`AppUniqLvl` at index 1 is **refuted** (`AppUniqRefute.piLvlEnv_appUniqLvl_false`). -/
theorem piLvlEnv_separates_at_one (h1 : SortRedAppDF piLvlEnv 0 0) :
    Ordered piLvlEnv ∧ SortDisjInvN piLvlEnv 0 1 ∧ ¬ piLvlEnv.AppUniqLvl 0 1 :=
  ⟨piLvlEnv_ordered, piLvlEnv_sortDisjInvN_one_of_appDF h1, piLvlEnv_appUniqLvl_false⟩

theorem ordered_and_sortDisjInvN_not_enough_at_one (h1 : SortRedAppDF piLvlEnv 0 0) :
    ¬ ∀ (env : VEnv), Ordered env → env.SortDisjInvN 0 1 → env.AppUniqLvl 0 1 :=
  fun h => piLvlEnv_appUniqLvl_false
    (h _ piLvlEnv_ordered (piLvlEnv_sortDisjInvN_one_of_appDF h1))

/-- The `∀ n` form of the reduction, at any environment: **three** open families, not one. -/
theorem sortDisjInvN_all_of (h1 : ∀ n, SortRedAppDF env U n)
    (h2 : ∀ n, PiTypedNotSortRed env U n) (h3 : ∀ n, ProofNotSortRed env U n)
    (h4 : ExtraSortRed env) : ∀ n, SortDisjInvN env U n
  | 0 => SortDisjInvN.zero
  | n+1 => ⟨sortInvN_succ_of_residuals (h1 n) (h2 n) (h3 n) h4,
      sortForallEDisjN_succ_of_residuals (h1 n) (h2 n) (h3 n) h4⟩

theorem piLvlEnv_sortDisjInvN_all_of (h1 : ∀ n, SortRedAppDF piLvlEnv 0 n)
    (h2 : ∀ n, PiTypedNotSortRed piLvlEnv 0 n) (h3 : ∀ n, ProofNotSortRed piLvlEnv 0 n) :
    ∀ n, SortDisjInvN piLvlEnv 0 n :=
  sortDisjInvN_all_of h1 h2 h3 extraSortRed_piLvlEnv

/-- **§13.7's positive branch, as a conditional theorem.**  Its three hypotheses are open; the
index-1 instance of the first alone implies `SortInvN ∅ 0 1` (§4). -/
theorem ordered_and_sortDisjInvN_all_not_enough_of (h1 : ∀ n, SortRedAppDF piLvlEnv 0 n)
    (h2 : ∀ n, PiTypedNotSortRed piLvlEnv 0 n) (h3 : ∀ n, ProofNotSortRed piLvlEnv 0 n) :
    ¬ ∀ (env : VEnv), Ordered env → (∀ n, env.SortDisjInvN 0 n) → ∀ n, env.AppUniqLvl 0 n :=
  fun h => piLvlEnv_appUniqLvl_false
    (h _ piLvlEnv_ordered (piLvlEnv_sortDisjInvN_all_of h1 h2 h3) 1)


/-! ## 6. The `beta` case is **free** — the correction to §13.6 item 3

`docs/handoff-sortinv-route.md` §13.6 item 3 reports the attempt at this item failing "at the
`beta` case of a `SubstCRefute.stuck`-style induction: a sort *is* `⊢₁`-convertible to a β-redex
… so no shape-class invariant is preserved and the case is the general weak-head confluence
problem".  The premise is true and the conclusion does not follow.  The redex is exhibited
below, over `piLvlEnv` itself, and `SortRed` — the tree's predicate for this job since
`SortClauses.lean` §4 — **is** invariant across it, by one line.  `trans` is free too, by
composition of `Iff`s.  The obstruction is the `appDF` case. -/

/-- `fun (_ : Type 0) => Prop` applied to `Prop`: a β-redex `⊢₁`-convertible to a sort. -/
def piLvlRedex : VExpr := .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)

theorem piLvlRedex_conv_sort :
    piLvlEnv.IsDefEqN 0 1 [] piLvlRedex (.sort .zero) :=
  Stratified.beta (Stratified.sort trivial) (Stratified.sort trivial)

/-- **…and `SortRed` does not care.**  So the fact §13.6 item 3 cites is not an obstruction to
the predicate the tree already uses; it is only an obstruction to a *syntactic shape class*,
which is what a `stuck`-style induction carries. -/
theorem piLvlRedex_sortRed_iff {u : VLevel} :
    SortRed u piLvlRedex ↔ SortRed u (.sort .zero) := SortRed.beta_iff

theorem beta_and_trans_are_free :
    (∀ {A e a : VExpr} {u : VLevel}, SortRed u (.app (.lam A e) a) ↔ SortRed u (e.inst a)) ∧
    (∀ {X Y Z : VExpr} {u : VLevel}, (SortRed u X ↔ SortRed u Y) →
      (SortRed u Y ↔ SortRed u Z) → (SortRed u X ↔ SortRed u Z)) :=
  ⟨SortRed.beta_iff, fun h1 h2 => h1.trans h2⟩

/-! ## 7. A new refutation: the argument typing must be tied to the **domain**

`SortRedApp.spineInv_one_false` refutes the *typing-free* spine predicate — the natural
strengthening under which `appDF` would become free.  The obvious next design point is to
require each spine argument to be `⊢₀`-typed, without tying it to the function's domain.
**That is false too**, at the same witness: `ArgWitness`'s separating argument `Prop` *is*
`⊢₀`-typed (at `.sort 1`), just not at the domain `P`.

Consequence, and it is the sharp form of why this corner is closed rather than expensive: the
strengthened predicate must carry `Γ ⊢₀ a : A` with `A` the function's own domain — and the
`trans` case of any induction on the conversion has a middle term with **no type at all**, so it
cannot supply a domain.  `SortRedApp.sortRedAppDF_needs_arg_typing` is one horn of that dilemma;
this is the other.  (What is *not* refuted, here or anywhere: the heterogeneously typed spine of
`docs/handoff-sortred.md` §8 item 2, whose two sides carry their own Π-types.) -/

/-- The spine predicate with each argument `⊢₀`-typed at *some* type. -/
def SpineInvTyped (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X Y : VExpr} {as as' : List VExpr} {u : VLevel},
    env.IsDefEqN U n Γ X Y → List.Forall₂ (env.IsDefEqN U n Γ) as as' →
    (∀ a ∈ as, ∃ T, env.HasTypeN U 0 Γ a T) → (∀ a ∈ as', ∃ T, env.HasTypeN U 0 Γ a T) →
    (SortRed u (X.apps as) ↔ SortRed u (Y.apps as'))

theorem spineInvTyped_of_spineInv (h : SpineInv env U n) : SpineInvTyped env U n :=
  fun hc has _ _ => h hc has

/-- **`SpineInvTyped ∅ 1 1` is false.**  Same witness as `spineInv_one_false`; the spine element
is `⊢₀`-typed, so requiring that changes nothing. -/
theorem spineInvTyped_one_false : ¬ SpineInvTyped ∅ 1 1 := fun h =>
  ArgWitness.app_constP_not_sortRed
    ((h ArgWitness.idP_conv_constP (as := [.sort .zero]) (as' := [.sort .zero])
        (List.Forall₂.cons .rfl .nil)
        (by intro a ha; rw [List.mem_singleton] at ha; subst ha; exact ⟨_, ArgWitness.arg_type⟩)
        (by intro a ha; rw [List.mem_singleton] at ha; subst ha; exact ⟨_, ArgWitness.arg_type⟩)).1
      ArgWitness.app_idP_sortRed)


/-! ## 8. Exactly how the lower bound of §4 relates to the tree's open goal

`DefInvRefute` and `docs/handoff-sortred.md` track clause (1) and clause (3) at index 1 over
`∅` at **`U = 1`** (one universe parameter).  `piLvlEnv` lives at `U = 0`, so §4's transfer lands
on the `U = 0` instance.  That instance is **weaker** — machine-checked here, not read off:
levels well-formed at `U` are well-formed at any `U' ≥ U`, so a `U = 0` derivation is a `U = 1`
derivation.  So item (c) implies an open statement that is itself implied by the tree's open
statement; it is not literally the same goal, and nothing in the tree proves either. -/

theorem _root_.Lean4Lean.VLevel.WF.mono_univs {U U' : Nat} (le : U ≤ U') {l : VLevel} :
    l.WF U → l.WF U' := by
  induction l with
  | zero => exact id
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | imax _ _ ih1 ih2 => exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | param i => exact fun h => Nat.lt_of_lt_of_le h le

theorem Stratified.mono_univs {U U' : Nat} (le : U ≤ U') {m : Nat}
    {Γ : List VExpr} {e₁ e₂ : VExpr} {b : Bool} (H : Stratified env U m Γ e₁ e₂ b) :
    Stratified env U' m Γ e₁ e₂ b := by
  induction H with
  | bvar h => exact .bvar h
  | sort h => exact .sort (h.mono_univs le)
  | const h1 h2 h3 => exact .const h1 (fun l hl => (h2 l hl).mono_univs le) h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.mono_univs le) (h2.mono_univs le) ih1 ih2
  | conv _ _ ih1 ih2 => exact .conv ih1 ih2
  | rfl => exact .rfl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF (h1.mono_univs le) (h2.mono_univs le) h3
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 (fun l hl => (h2 l hl).mono_univs le)
      (fun l hl => (h3 l hl).mono_univs le) h4 h5
  | appDF _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .appDF ih1 ih2 ih3 ih4 ih5 ih6
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 (fun l hl => (h2 l hl).mono_univs le) h3

/-- The `U = 0` instance of clause (1) is implied by the `U = 1` instance the tree tracks. -/
theorem SortInvN.mono_univs {U U' : Nat} (le : U ≤ U') (h : SortInvN env U' n) :
    SortInvN env U n := fun hc => h (hc.mono_univs le)

theorem SortForallEDisjN.mono_univs {U U' : Nat} (le : U ≤ U')
    (h : SortForallEDisjN env U' n) : SortForallEDisjN env U n :=
  fun hc => h (hc.mono_univs le)

/-- **The sandwich, in one statement.**  Item (c) sits *above* the `U = 0` empty-environment
clause at index 1, which sits *below* the `U = 1` clause the tree has open.  Both bounds are
open; neither is discharged anywhere in the tree. -/
theorem sortDisjInvN_sandwich :
    (SortDisjInvN piLvlEnv 0 1 → SortDisjInvN ∅ 0 1) ∧
    (SortInvN ∅ 1 1 → SortInvN ∅ 0 1) ∧
    (SortForallEDisjN ∅ 1 1 → SortForallEDisjN ∅ 0 1) :=
  ⟨sortDisjInvN_le, SortInvN.mono_univs (Nat.zero_le 1),
    SortForallEDisjN.mono_univs (Nat.zero_le 1)⟩

/-- …and the negative direction transfers the other way: a refutation over `∅` at `U = 0`
refutes item (c) outright. -/
theorem sortInvN_empty_false_imp (h : ¬ SortInvN ∅ 0 1) : ¬ SortInvN piLvlEnv 0 1 :=
  fun h' => h (sortInvN_le h')



/-! ## 9. A second necessary sub-obligation, apparently unrecorded: **argument replacement**

`docs/handoff-sortred.md` §6 reads the surviving residual as being about weak-head λ-*exposure*.
It contains a second, independent demand, and the cheapest way to see it is that the residual is
non-trivial **even when `f = f'`**: with the same function on both sides, `SortRedLamExpose`
still asserts that replacing the argument by a `⊢₁`-convertible one of the same `⊢₀` type
preserves `SortRed` of the instantiated body.  That is a `SubstC`-shaped statement — and
`SubstC` itself is **false** (`SubstCRefute.substC_false`), which is why this half deserves its
own name rather than being read as part of λ-exposure.

Not refuted here, and not proved: `SortRedArgSwap` is a *necessary condition* for the residual
(`sortRedArgSwap_of_lamExpose`), so refuting it would refute the residual — though not the
clauses, since `SortRedInv → SortDisjInvN` is one-way. -/

theorem headBetaS_lam_inv {A e Y : VExpr} (h : HeadBetaS (.lam A e) Y) : Y = .lam A e := by
  cases h with
  | refl => rfl
  | head hb _ => exact absurd hb HeadBeta.not_lam

/-- **Argument replacement**: a `⊢₁`-convertible argument of the same `⊢₀` type cannot change
whether the instantiated body weak-head reduces to a sort. -/
def SortRedArgSwap (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A e a a' : VExpr} {t w u : VLevel},
    env.HasTypeN U n Γ A (.sort t) → env.HasTypeN U n (A::Γ) e (.sort w) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    SortRed u (e.inst a) → SortRed u (e.inst a')

/-- **The residual implies it** — at `f = f'`, by `rfl` and one `HeadBetaS` inversion.  So the
open residual is at least as strong as this, and `SortRedLamExpose` is not purely a statement
about λ-exposure. -/
theorem sortRedArgSwap_of_lamExpose (h : SortRedLamExpose env U 0) : SortRedArgSwap env U 0 := by
  intro Γ A e a a' t w u hA he haa' ha ha' hs
  have hf : env.HasTypeN U 0 Γ (.lam A e) (.forallE A (.sort w)) := Stratified.lam hA he
  obtain ⟨e', hr', hbody'⟩ := h (f' := .lam A e) .rfl hf hf haa' ha ha' .refl hs
  injection headBetaS_lam_inv hr' with _ he'
  exact he' ▸ hbody'

/-! ## Verdict, graded

**Not proved and not refuted.**  `SortDisjInvN piLvlEnv 0 1` is *sandwiched* between two open
statements, and both bounds are machine-checked here:

* **sufficient** (§3): `SortRedAppDF piLvlEnv 0 0`, equivalently `SortRedLamExpose piLvlEnv 0 0`
  — open over `∅` since `docs/handoff-sortred.md`, with two of its cheaper repairs refuted there
  and a third refuted in §7 here.  This bound is **possibly strictly stronger** than the target:
  `SortRedInv → SortDisjInvN` is one-way and no converse is known, so §3 is *not* a proof that
  item (c) is as hard as the residual.  Graded accordingly — it is a sufficient condition, not a
  reduction.
* **necessary** (§4, §8): `SortDisjInvN ∅ 0 1`.  This is a real lower bound — item (c) *implies*
  it — and it is open.  It is the `U = 0` instance of the goal `DefInvRefute` left at `U = 1`,
  hence weaker than that goal (§8, machine-checked), so "item (c) proves the tree's open goal" is
  **not** the right claim; "item (c) proves an open goal that the tree's open goal would give
  you" is.

So the answer to §13.7's question is: **the positive branch is not cheap and not reachable
today** — it entails an open clause — and the negative branch cannot come from `piLvlEnv`'s
rule, which §2 shows is invisible to `SortRed` (and could only come from a refutation over `∅`,
which by `sortInvN_empty_false_imp` would settle item (c) as a side effect).  §13.6's own
description of the obstruction is corrected in §6: **`beta` is free; `appDF` is the residual** —
and §9 adds that the residual has an argument-replacement half as well as a λ-exposure half.

Everything in this file is `sorry`-free; the axioms are `propext`, `Quot.sound` and
`Classical.choice`, all on `Verify/Guard.lean`'s whitelist. -/

section Audit
#print axioms Lean4Lean.VEnv.Stratified.mono_env
#print axioms Lean4Lean.VEnv.Stratified.mono_univs
#print axioms Lean4Lean.VLevel.WF.mono_univs
#print axioms Lean4Lean.VEnv.SortInvN.mono_env
#print axioms Lean4Lean.VEnv.SortForallEDisjN.mono_env
#print axioms Lean4Lean.VEnv.SortDisjInvN.mono_env
#print axioms Lean4Lean.VEnv.extraSortRed_piLvlEnv
#print axioms Lean4Lean.VEnv.forallE_not_pi0
#print axioms Lean4Lean.VEnv.piLvlL_type0
#print axioms Lean4Lean.VEnv.piLvlR_type0
#print axioms Lean4Lean.VEnv.piLvl_rule_not_pi_typed0
#print axioms Lean4Lean.VEnv.piLvl_rule_sides_not_one_type0
#print axioms Lean4Lean.VEnv.piLvlEnv_sortRedInv_one_of_appDF
#print axioms Lean4Lean.VEnv.piLvlEnv_sortRedAppDF_iff
#print axioms Lean4Lean.VEnv.piLvlEnv_chain
#print axioms Lean4Lean.VEnv.piLvlEnv_sortInvN_one_of_appDF
#print axioms Lean4Lean.VEnv.piLvlEnv_sortForallEDisjN_one_of_appDF
#print axioms Lean4Lean.VEnv.piLvlEnv_sortDisjInvN_one_of_appDF
#print axioms Lean4Lean.VEnv.piLvlEnv_sortDisjInvN_one_of_lamExpose
#print axioms Lean4Lean.VEnv.empty_le_piLvlEnv
#print axioms Lean4Lean.VEnv.sortInvN_le
#print axioms Lean4Lean.VEnv.sortForallEDisjN_le
#print axioms Lean4Lean.VEnv.sortDisjInvN_le
#print axioms Lean4Lean.VEnv.piLvlEnv_separates_at_one
#print axioms Lean4Lean.VEnv.ordered_and_sortDisjInvN_not_enough_at_one
#print axioms Lean4Lean.VEnv.sortDisjInvN_all_of
#print axioms Lean4Lean.VEnv.piLvlEnv_sortDisjInvN_all_of
#print axioms Lean4Lean.VEnv.ordered_and_sortDisjInvN_all_not_enough_of
#print axioms Lean4Lean.VEnv.piLvlRedex_conv_sort
#print axioms Lean4Lean.VEnv.piLvlRedex_sortRed_iff
#print axioms Lean4Lean.VEnv.beta_and_trans_are_free
#print axioms Lean4Lean.VEnv.spineInvTyped_of_spineInv
#print axioms Lean4Lean.VEnv.spineInvTyped_one_false
#print axioms Lean4Lean.VEnv.SortInvN.mono_univs
#print axioms Lean4Lean.VEnv.SortForallEDisjN.mono_univs
#print axioms Lean4Lean.VEnv.sortDisjInvN_sandwich
#print axioms Lean4Lean.VEnv.sortInvN_empty_false_imp
#print axioms Lean4Lean.VEnv.headBetaS_lam_inv
#print axioms Lean4Lean.VEnv.sortRedArgSwap_of_lamExpose
end Audit

end VEnv
end Lean4Lean
