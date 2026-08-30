import Lean4Lean.Theory.Typing.DefInvRefute
import Lean4Lean.Theory.Typing.RegPiSat

/-!
# Clauses (1) and (3) of definitional inversion, after clause (2) was refuted

`Theory/Typing/DefInvRefute.lean` refutes `DefInv ∅ 1 1` through **clause (2) only**.
`Theory/Typing/UniqueTypingN.lean` now names the three clauses separately — `SortInvN`,
`ForallEInvN`, `SortForallEDisjN` — and every consumer that used less than all three has been
narrowed.  This file is the follow-up work on the two clauses that survive:

1. **the bridge** to `DefInvRefute`'s namespace-local copies of the same two predicates (they
   are definitionally the `VEnv` ones, `rfl`);
2. **non-vacuity** of the narrowed hypotheses: every weakened consumer replayed at index `0`
   over `CycleConv.propLoopEnv` — an environment with two constants and two δ-rules — at
   instances that are inhabited there and *not* inhabited over `∅`;
3. **`Ordered` is not enough.**  `sortPiEnv` is an `Ordered` environment carrying the rule
   `Prop ≡ ∀ (_ : Prop), Prop`; at it, clause (3) is **false** at index 1
   (`sortPiEnv_sortForallEDisjN_false`), and so is the ambient target
   `IsDefEqU.sort_forallE_inv` (`sortPiEnv_ambient_conv`).  The environment is not `VEnv.WF`
   (`sortPiEnv_not_wf`).  So `IsDefEqU.sort_forallE_inv_of_sortForallEDisjN`'s `Ordered env`
   premise cannot ever discharge its own `dinv` hypothesis: the right premise is `VEnv.WF`;
4. **a reduction of both clauses that makes `trans` free.**  `SortRed u X` says `X`
   weak-head β-reduces, in zero or more steps, to a sort of level `≈ u`.  `SortRedInv` —
   invariance of `SortRed` along a `⊢ₙ` conversion — implies both clauses
   (`sortInvN_of_sortRedInv`, `sortForallEDisjN_of_sortRedInv`), and `sortRedInv_of` proves
   `SortRedInv` at `n+1` from **four** residuals at `n`: `appDF`, `eta`, `proofIrrel`,
   `extra`.  `rfl`, `symm`, `trans`, `sortDF`, `constDF`, `lamDF`, `forallEDF` and `beta` all
   close outright;
5. **three of the four residuals discharged at the base index.**  `PiTypedNotSortRed.zero` and
   `ProofNotSortRed.zero` follow from weak-head subject reduction at `⊢₀`
   (`HeadBeta.hasTypeN_zero`) plus `DefInvRefute.sort_not_proof0`; `ExtraSortRed` is vacuous
   over `∅` and *proved* over `propLoopEnv`.  So

       SortRedAppDF ∅ 1 0  →  SortInvN ∅ 1 1 ∧ SortForallEDisjN ∅ 1 1

   (`empty_sortInvN_one_of_appDF`, `empty_sortForallEDisjN_one_of_appDF`), and the same over
   `propLoopEnv`.  **One residual is what is left of the two open goals at index 1;**
6. **the cheaper predicate is refuted.**  `HeadOnly.SortRedHead` — contract the outermost head
   redex but never reduce inside the function — is *not* invariant along `⊢₁`
   (`HeadOnly.sortRedHeadInv_one_false`), by an `appDF` whose four typing premises are `⊢₀`
   derivations over `∅`.  `HeadOnly.app_cf'_sortRed` checks that the real `SortRed` survives
   that same witness, so the `app` step in `HeadBeta` is doing work.

## What this does **not** claim

`trans` is free *at the top level of `sortRedInv_of`*.  It reappears inside the remaining
residual: `SortRedAppDF`'s premise `Γ ⊢ₙ₊₁ f ≡ f'` is an arbitrary conversion, and proving it
will need its own induction where a `trans` middle term occurs again.  What has changed is
that the obligation is now **one statement about applications whose two function endpoints are
`⊢ₙ`-typed at the same Π-type**, instead of an obligation spread over every rule.  The `⊢₀`
rigidity that premise supplies is real — it is what kills the `lamDF` and `proofIrrel` routes
to a counterexample (see §6's discussion) — but it is not a proof.

No attempt in this file refutes `SortRedAppDF ∅ 1 0`.  Two were made and both fail on the
same premise: `lamDF` would relate `.lam A (.sort v)` to `.lam A' (.sort v')`, and the shared
`⊢₀` type forces `A = A'` and `v = v'`; `proofIrrel` would need `⊢₀ (∀A.B) : .sort .zero`,
which `HasTypeN.forallE_inv` refutes syntactically.

Everything below is sorry-free; axioms are `propext`, `Quot.sound` and `Classical.choice`,
all on `Guard.lean`'s whitelist.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. The bridge to `DefInvRefute`'s copies -/

theorem sortInvN_eq_defInvRefute : DefInvRefute.SortInvN env U n = SortInvN env U n := rfl

theorem sortForallEDisjN_eq_defInvRefute :
    DefInvRefute.SortForallEDisjN env U n = SortForallEDisjN env U n := rfl

/-! ## 2. Non-vacuity: the weakened consumers fired at index zero over `propLoopEnv` -/

section NonVacuity

/-- Clause (1) at the base index, over an environment with constants and δ-rules. -/
theorem propLoopEnv_sortInvN_zero : SortInvN propLoopEnv U 0 := SortInvN.zero

/-- Clause (3) at the base index, same environment. -/
theorem propLoopEnv_sortForallEDisjN_zero : SortForallEDisjN propLoopEnv U 0 :=
  SortForallEDisjN.zero

/-- **`sortNotProof_of` fires.**  `propLoopEnv` has an actual proposition — the constant `A` —
so the conclusion "no sort inhabits it" is a statement about a real type, not an empty one. -/
theorem propLoopEnv_sort_not_proof {Γ : List VExpr} {u : VLevel} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.sort u) (.const `A []) :=
  fun h => sortNotProof_of propLoopEnv_sortInvN_zero PropTypeAgreeN.zero propLoopEnv_constA h

/-- **`forallENotProof_of` fires**, at the same proposition. -/
theorem propLoopEnv_forallE_not_proof {Γ : List VExpr} {X Y : VExpr} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.forallE X Y) (.const `A []) :=
  fun h => forallENotProof_of propLoopEnv_sortInvN_zero PropTypeAgreeN.zero propLoopEnv_constA h

/-- **`propNotProof_of` fires**, at the environment's two propositions: `B` is not a proof of
`A`.  Both `A` and `B` are `⊢₀`-typed propositions here and the two are δ-equal, so this is
the sharpest instance the witness environment offers. -/
theorem propLoopEnv_B_not_proof_of_A {Γ : List VExpr} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.const `B []) (.const `A []) :=
  fun h => propNotProof_of propLoopEnv_sortInvN_zero PropTypeAgreeN.zero
    propLoopEnv_constB propLoopEnv_constA h

/-- **`sortForallEDisjoint_ofN` fires at the `const` case**, which is *empty over `∅`* —
`VEnv.empty` has no constants at all — and inhabited here.  This is the check that the
narrowed hypothesis is not being replayed on a degenerate environment. -/
theorem propLoopEnv_constA_not_forallE_typed {Γ : List VExpr} {X Y : VExpr} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.const `A []) (.forallE X Y) :=
  fun h => sortForallEDisjoint_ofN (T := .sort .zero) propLoopEnv_constA
    SortForallEDisjoint.AppCase.zero propLoopEnv_sortForallEDisjN_zero (Eq.refl true)
    .zero X Y .rfl h

/-- **`PropTypeAgreeN.eta_case` fires**, at a Π-typed variable in a well-formed context over
the witness environment — the same instance `RegPiSat.propLoopEnv_regPiOn_fires` uses. -/
theorem propLoopEnv_eta_case_fires :
    (IsPropN propLoopEnv U 0 [propArrow]
        (.lam (.const `A []) (.app (VExpr.bvar 0).lift (.bvar 0))) ↔
      IsPropN propLoopEnv U 0 [propArrow] (.bvar 0)) :=
  PropTypeAgreeN.eta_case propLoopEnv_sortForallEDisjN_zero SortForallEDisjoint.zero
    (Stratified.bvar (Lookup.zero' rfl))

end NonVacuity

/-! ## 3. `Ordered` is not enough -/

/-- A `VDefEq` identifying `Prop` with `∀ (_ : Prop), Prop`.  Both sides are typed at
`.sort (.succ .zero)`, so it satisfies `VDefEq.WF ∅`. -/
def sortPiRule : VDefEq :=
  ⟨0, .sort .zero, .forallE (.sort .zero) (.sort .zero), .sort (.succ .zero)⟩

def sortPiEnv : VEnv := VEnv.empty.addDefEq sortPiRule

theorem sortPiRule_wf : sortPiRule.WF ∅ := by
  refine ⟨.sortDF trivial trivial rfl, ?_⟩
  have h : (∅ : VEnv).HasType 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    VEnv.IsDefEq.forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)
  exact .defeqDF (.sortDF (l := .imax (.succ .zero) (.succ .zero)) (l' := .succ .zero)
    ⟨trivial, trivial⟩ trivial (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])) h

theorem sortPiEnv_ordered : Ordered sortPiEnv := .defeq .empty sortPiRule_wf

theorem sortPiEnv_defeqs : sortPiEnv.defeqs sortPiRule := Or.inl rfl

theorem sortPiEnv_conv : sortPiEnv.IsDefEqN 0 1 [] (.sort .zero)
    (.forallE (.sort .zero) (.sort .zero)) :=
  Stratified.extra (ls := []) sortPiEnv_defeqs nofun rfl

/-- **Clause (3) is false at an `Ordered` environment.** -/
theorem sortPiEnv_sortForallEDisjN_false : ¬ SortForallEDisjN sortPiEnv 0 1 :=
  fun h => h sortPiEnv_conv

/-- …and hence so is the hypothesis of
`IsDefEqU.sort_forallE_inv_of_sortForallEDisjN`, at an environment that theorem's own
`Ordered` premise admits. -/
theorem sortPiEnv_sortForallEDisjN_all_false : ¬ ∀ n, SortForallEDisjN sortPiEnv 0 n :=
  fun h => sortPiEnv_sortForallEDisjN_false (h 1)

/-- The same at the ambient judgment: `Theory/Typing/Injectivity.lean`'s
`IsDefEqU.sort_forallE_inv` is false at `sortPiEnv` too.  That target takes `VEnv.WF`, which
`sortPiEnv` does not satisfy — which is exactly the point of this section. -/
theorem sortPiEnv_ambient_conv :
    sortPiEnv.IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) :=
  ⟨_, VEnv.IsDefEq.extra (ls := []) sortPiEnv_defeqs nofun rfl⟩

/-- **`sortPiEnv` is `Ordered` and not `WF`.**  `Ordered.defeq` asks only that both sides of a
rule be typed at one type; `VEnv.WF` additionally forces every rule to come from a
declaration, and `VDefEq.IsDeclRule.lhs_ne_sort` says no declaration rule rewrites a sort. -/
theorem sortPiEnv_not_wf : ¬ sortPiEnv.WF :=
  fun h => (h.defeq_isDeclRule sortPiEnv_defeqs).lhs_ne_sort _ rfl

/-! ## 4. Weak-head β reduction to a sort: `trans` stops being the obstruction -/

/-- One **weak-head** β step: contract the head redex, reducing in function position only. -/
inductive HeadBeta : VExpr → VExpr → Prop
  | beta {A e a : VExpr} : HeadBeta (.app (.lam A e) a) (e.inst a)
  | app {f f' a : VExpr} : HeadBeta f f' → HeadBeta (.app f a) (.app f' a)

theorem HeadBeta.not_sort {v : VLevel} {Y : VExpr} : ¬ HeadBeta (.sort v) Y := nofun
theorem HeadBeta.not_lam {A e Y : VExpr} : ¬ HeadBeta (.lam A e) Y := nofun
theorem HeadBeta.not_forallE {A B Y : VExpr} : ¬ HeadBeta (.forallE A B) Y := nofun
theorem HeadBeta.not_bvar {i : Nat} {Y : VExpr} : ¬ HeadBeta (.bvar i) Y := nofun
theorem HeadBeta.not_const {c ls} {Y : VExpr} : ¬ HeadBeta (.const c ls) Y := nofun

/-- **`X` weak-head reduces, in zero or more β steps, to a sort of level `≈ u`.**

Minimal by design: no congruence below the head, no η, no δ.  It is the weakest predicate
that is invariant under `beta` *and* under reduction in function position — the second is what
`appDF` forces, and a version without it is refutable (see `sortRedInv_headOnly_false`
below). -/
inductive SortRed (u : VLevel) : VExpr → Prop
  | sort {v : VLevel} : v ≈ u → SortRed u (.sort v)
  | step {X Y : VExpr} : HeadBeta X Y → SortRed u Y → SortRed u X

theorem SortRed.sort_inv {u v : VLevel} (h : SortRed u (.sort v)) : v ≈ u := by
  cases h with
  | sort h => exact h
  | step h _ => exact absurd h HeadBeta.not_sort

theorem SortRed.not_forallE {u : VLevel} {A B : VExpr} : ¬ SortRed u (.forallE A B) := by
  intro h; cases h with | step h _ => exact absurd h HeadBeta.not_forallE

theorem SortRed.not_lam {u : VLevel} {A e : VExpr} : ¬ SortRed u (.lam A e) := by
  intro h; cases h with | step h _ => exact absurd h HeadBeta.not_lam

theorem SortRed.not_bvar {u : VLevel} {i : Nat} : ¬ SortRed u (.bvar i) := by
  intro h; cases h with | step h _ => exact absurd h HeadBeta.not_bvar

theorem SortRed.not_const {u : VLevel} {c ls} : ¬ SortRed u (.const c ls) := by
  intro h; cases h with | step h _ => exact absurd h HeadBeta.not_const

/-- The `beta` rule's case, both ways: the head redex has exactly one weak-head reduct. -/
theorem SortRed.beta_iff {u : VLevel} {A e a : VExpr} :
    SortRed u (.app (.lam A e) a) ↔ SortRed u (e.inst a) := by
  refine ⟨fun h => ?_, fun h => .step .beta h⟩
  cases h with
  | step h hY =>
    cases h with
    | beta => exact hY
    | app h => exact absurd h HeadBeta.not_lam

/-- **`SortRed`-invariance along a `⊢ₙ` conversion.**  Strictly stronger than clauses (1) and
(3) together, and — unlike them — closed under `trans`, by composition of `Iff`s. -/
def SortRedInv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X Y : VExpr} {u : VLevel},
    env.IsDefEqN U n Γ X Y → (SortRed u X ↔ SortRed u Y)

theorem sortInvN_of_sortRedInv (h : SortRedInv env U n) : SortInvN env U n := fun hc =>
  (SortRed.sort_inv ((h hc).1 (.sort rfl))).symm

theorem sortForallEDisjN_of_sortRedInv (h : SortRedInv env U n) : SortForallEDisjN env U n :=
  fun hc => SortRed.not_forallE ((h hc).1 (.sort rfl))

/-! ### The four residuals

Everything else in the induction is free.  **`trans` is free** — it composes two `Iff`s —
which is the correction this section makes to `docs/handoff-definv-one.md` §6's "what remains
for (1) and (3) is exactly the `trans` case".  Against `SortRedInv` the obligation moves to
`appDF`, and `appDF`, unlike `trans`, carries typing premises: its two functions are `⊢ₙ`-typed
at the **same** Π-type. -/

/-- The `appDF` residual.  This is where λ-injectivity is unavoidable: `SortRed` of an
application has to find a λ in the head, and the conversion `f ≡ₙ₊₁ f'` does not say that one
head is a λ iff the other is. -/
def SortRedAppDF (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A B : VExpr} {u : VLevel},
    env.IsDefEqN U (n+1) Γ f f' → env.HasTypeN U n Γ f (.forallE A B) →
    env.HasTypeN U n Γ f' (.forallE A B) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    (SortRed u (.app f a) ↔ SortRed u (.app f' a'))

/-- The `eta` residual: a Π-typed term does not weak-head reduce to a sort. -/
def PiTypedNotSortRed (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {u : VLevel},
    env.HasTypeN U n Γ e (.forallE A B) → ¬ SortRed u e

/-- The `proofIrrel` residual: a proof of a proposition does not weak-head reduce to a
sort. -/
def ProofNotSortRed (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {p h : VExpr} {u : VLevel},
    env.HasTypeN U n Γ p (.sort .zero) → env.HasTypeN U n Γ h p → ¬ SortRed u h

/-- The `extra` residual: the environment's own rules preserve `SortRed`. -/
def ExtraSortRed (env : VEnv) : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {u : VLevel}, env.defeqs df →
    (SortRed u (df.lhs.instL ls) ↔ SortRed u (df.rhs.instL ls))

/-- **`SortRedInv` at `n+1` from the four residuals at `n`, and from nothing else.**

`rfl`, `symm`, **`trans`**, `sortDF`, `constDF`, `lamDF`, `forallEDF` and `beta` all close
outright; the seven typing constructors die on the `Bool` discriminator. -/
theorem sortRedInv_of {m : Nat} {Γ X Y b} (H : Stratified env U m Γ X Y b) :
    ∀ n, m = n + 1 → SortRedAppDF env U n → PiTypedNotSortRed env U n →
      ProofNotSortRed env U n → ExtraSortRed env → b = false →
      ∀ u : VLevel, (SortRed u X ↔ SortRed u Y) := by
  induction H with
  | bvar | sort | const | app | lam | forallE | conv =>
    intro _ _ _ _ _ _ hb; exact nomatch hb
  | rfl => intro _ _ _ _ _ _ _ _; exact .rfl
  | symm _ ih => intro n hm h1 h2 h3 h4 hb u; exact (ih n hm h1 h2 h3 h4 hb u).symm
  | trans _ _ ih1 ih2 =>
    intro n hm h1 h2 h3 h4 hb u
    exact (ih1 n hm h1 h2 h3 h4 hb u).trans (ih2 n hm h1 h2 h3 h4 hb u)
  | sortDF _ _ h3 =>
    intro _ _ _ _ _ _ _ u
    exact ⟨fun h => .sort (h3.symm.trans h.sort_inv),
      fun h => .sort (h3.trans h.sort_inv)⟩
  | constDF => intro _ _ _ _ _ _ _ _; exact ⟨(absurd · SortRed.not_const),
      (absurd · SortRed.not_const)⟩
  | lamDF => intro _ _ _ _ _ _ _ _; exact ⟨(absurd · SortRed.not_lam),
      (absurd · SortRed.not_lam)⟩
  | forallEDF => intro _ _ _ _ _ _ _ _; exact ⟨(absurd · SortRed.not_forallE),
      (absurd · SortRed.not_forallE)⟩
  | @appDF _ _ _ _ _ _ _ _ hff' hf hf' haa' ha ha' _ _ _ _ _ _ =>
    intro n hm h1 _ _ _ _ u
    cases Nat.succ.inj hm
    exact h1 hff' hf hf' haa' ha ha'
  | beta => intro _ _ _ _ _ _ _ _; exact SortRed.beta_iff
  | eta he =>
    intro n hm _ h2 _ _ _ u
    cases Nat.succ.inj hm
    exact ⟨(absurd · SortRed.not_lam), (absurd · (h2 he))⟩
  | proofIrrel hp hh hh' =>
    intro n hm _ _ h3 _ _ u
    cases Nat.succ.inj hm
    exact ⟨(absurd · (h3 hp hh)), (absurd · (h3 hp hh'))⟩
  | extra h1 _ _ => intro _ _ _ _ _ h4 _ _; exact h4 h1

/-- **Clauses (1) and (3) at `n+1`**, from the four residuals at `n`. -/
theorem sortInvN_succ_of_residuals (h1 : SortRedAppDF env U n)
    (h2 : PiTypedNotSortRed env U n) (h3 : ProofNotSortRed env U n)
    (h4 : ExtraSortRed env) : SortInvN env U (n+1) :=
  sortInvN_of_sortRedInv fun h => sortRedInv_of h n rfl h1 h2 h3 h4 rfl _

theorem sortForallEDisjN_succ_of_residuals (h1 : SortRedAppDF env U n)
    (h2 : PiTypedNotSortRed env U n) (h3 : ProofNotSortRed env U n)
    (h4 : ExtraSortRed env) : SortForallEDisjN env U (n+1) :=
  sortForallEDisjN_of_sortRedInv fun h => sortRedInv_of h n rfl h1 h2 h3 h4 rfl _

/-! ### Three of the four residuals, discharged at the base index

So over `∅` — and over `propLoopEnv` — **clauses (1) and (3) at index 1 have exactly one open
residual left, `SortRedAppDF env U 0`.** -/

/-- **Weak-head β subject reduction at `⊢₀`.**  The one fact that makes the `eta` and
`proofIrrel` residuals free at the base index.  Both cases are `HasTypeN.app_inv` plus, for
the contraction, `Stratified.instN` at `m = 0` — the only index at which `instN` preserves
the index. -/
theorem HeadBeta.hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {X Y : VExpr}
    (h : HeadBeta X Y) : ∀ {T : VExpr}, env.HasTypeN U 0 Γ X T → env.HasTypeN U 0 Γ Y T := by
  induction h with
  | @beta A e a =>
    intro T hX
    obtain ⟨C, D, hlam, ha, hc⟩ := HasTypeN.app_inv hX
    obtain ⟨_, B, _, he, heq⟩ := HasTypeN.lam_inv hlam
    injection IsDefEqN.zero_iff.1 heq with hAC hBD
    cases hAC; cases hBD
    cases IsDefEqN.zero_iff.1 hc
    exact Stratified.instN henv ha .zero he
  | app _ ih =>
    intro T hX
    obtain ⟨C, D, hf, ha, hc⟩ := HasTypeN.app_inv hX
    cases IsDefEqN.zero_iff.1 hc
    exact Stratified.app (ih hf) ha

/-- A term that weak-head reduces to a sort is not `⊢₀`-typed at a Π-type. -/
theorem SortRed.not_hasTypeN_zero_forallE (henv : Ordered env) {Γ : List VExpr}
    {X A B : VExpr} {u : VLevel} (h : SortRed u X) :
    ¬ env.HasTypeN U 0 Γ X (.forallE A B) := by
  induction h with
  | sort _ => intro hX; cases IsDefEqN.zero_iff.1 (HasTypeN.sort_inv hX).2
  | step hb _ ih => intro hX; exact ih (hb.hasTypeN_zero henv hX)

/-- A term that weak-head reduces to a sort is not a `⊢₀` proof of a `⊢₀` proposition.  The
base case is `DefInvRefute.sort_not_proof0`; the step is subject reduction. -/
theorem SortRed.not_proof_hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {X p : VExpr}
    {u : VLevel} (hp : env.HasTypeN U 0 Γ p (.sort .zero)) (h : SortRed u X) :
    ¬ env.HasTypeN U 0 Γ X p := by
  induction h with
  | sort _ => intro hX; exact DefInvRefute.sort_not_proof0 hX hp
  | step hb _ ih => intro hX; exact ih (hb.hasTypeN_zero henv hX)

theorem PiTypedNotSortRed.zero (henv : Ordered env) : PiTypedNotSortRed env U 0 :=
  fun he hs => hs.not_hasTypeN_zero_forallE henv he

theorem ProofNotSortRed.zero (henv : Ordered env) : ProofNotSortRed env U 0 :=
  fun hp hh hs => hs.not_proof_hasTypeN_zero henv hp hh

/-- `SortRedInv` at the base index, where `≡₀` is syntactic equality — so the scheme is not
an empty one. -/
theorem SortRedInv.zero : SortRedInv env U 0 := fun h => by
  cases IsDefEqN.zero_iff.1 h; exact .rfl

/-- Over the empty environment the `extra` residual is vacuous. -/
theorem ExtraSortRed.empty : ExtraSortRed ∅ := fun h => nomatch h

/-- **And over `propLoopEnv` it is not vacuous — it is proved.**  Both of that environment's
δ-rules have a `.const` on each side, and `instL` keeps a `.const` a `.const`, so neither side
weak-head reduces to anything at all. -/
theorem ExtraSortRed.propLoopEnv : ExtraSortRed propLoopEnv := by
  intro df ls u h
  have hshape : (∃ c l, df.lhs = .const c l) ∧ ∃ c l, df.rhs = .const c l := by
    rcases h with rfl | rfl | h
    · exact ⟨⟨_, _, rfl⟩, _, _, rfl⟩
    · exact ⟨⟨_, _, rfl⟩, _, _, rfl⟩
    · exact h.elim
  obtain ⟨⟨c, l1, h1⟩, c', l2, h2⟩ := hshape
  rw [h1, h2]
  exact ⟨(absurd · SortRed.not_const), (absurd · SortRed.not_const)⟩

/-- **The whole reduction at index 1, with everything but `appDF` discharged**, over an
environment with constants and δ-rules. -/
theorem propLoopEnv_sortInvN_one_of_appDF (h1 : SortRedAppDF propLoopEnv U 0) :
    SortInvN propLoopEnv U 1 :=
  sortInvN_succ_of_residuals h1 (PiTypedNotSortRed.zero propLoopEnv_wf.ordered)
    (ProofNotSortRed.zero propLoopEnv_wf.ordered) ExtraSortRed.propLoopEnv

theorem propLoopEnv_sortForallEDisjN_one_of_appDF (h1 : SortRedAppDF propLoopEnv U 0) :
    SortForallEDisjN propLoopEnv U 1 :=
  sortForallEDisjN_succ_of_residuals h1 (PiTypedNotSortRed.zero propLoopEnv_wf.ordered)
    (ProofNotSortRed.zero propLoopEnv_wf.ordered) ExtraSortRed.propLoopEnv

/-- The same over `∅`, which is where `DefInvRefute` lives: **`SortInvN ∅ 1 1` and
`SortForallEDisjN ∅ 1 1` — the two live open goals — follow from `SortRedAppDF ∅ 1 0` and
nothing else.** -/
theorem empty_sortInvN_one_of_appDF (h1 : SortRedAppDF ∅ 1 0) : SortInvN ∅ 1 1 :=
  sortInvN_succ_of_residuals h1 (PiTypedNotSortRed.zero .empty)
    (ProofNotSortRed.zero .empty) ExtraSortRed.empty

theorem empty_sortForallEDisjN_one_of_appDF (h1 : SortRedAppDF ∅ 1 0) :
    SortForallEDisjN ∅ 1 1 :=
  sortForallEDisjN_succ_of_residuals h1 (PiTypedNotSortRed.zero .empty)
    (ProofNotSortRed.zero .empty) ExtraSortRed.empty

/-! ### Why the `app` step in `HeadBeta` is not optional

The obvious cheaper predicate — contract head redexes but never reduce *inside* the function
position — is refuted here.  It is the same design lesson `Theory/Typing/AppCase.lean` §1.3
records for `RelTaut`/`RelDisj`: the `appDF` rule is what forces the strengthening, and a
predicate that ignores it fails at `appDF` rather than at `trans`. -/

namespace HeadOnly

/-- `SortRed` without the `app` congruence: contract only the *outermost* head redex, and
never look inside the function. -/
inductive SortRedHead (u : VLevel) : VExpr → Prop
  | sort {v : VLevel} : v ≈ u → SortRedHead u (.sort v)
  | beta {A e a : VExpr} : SortRedHead u (e.inst a) → SortRedHead u (.app (.lam A e) a)

/-- `Prop`, used both as a domain and as the term the constant function returns. -/
def dom : VExpr := .sort .zero

/-- The constant function `fun _ : Prop => Prop`. -/
def cf : VExpr := .lam dom (.sort .zero)

/-- `cf` wrapped in one β-redex.  Same `⊢₀` type, one `⊢₁` conversion away, and **not** a
`.lam`. -/
def cf' : VExpr := .app (.lam dom cf) (.bvar 0)

def ctx : List VExpr := [dom]

theorem cf_type : (∅ : VEnv).HasTypeN 1 0 ctx cf (.forallE dom (.sort (.succ .zero))) :=
  .lam (.sort trivial) (.sort trivial)

theorem cf_type' {Γ : List VExpr} :
    (∅ : VEnv).HasTypeN 1 0 Γ cf (.forallE dom (.sort (.succ .zero))) :=
  .lam (.sort trivial) (.sort trivial)

theorem bvar_type : (∅ : VEnv).HasTypeN 1 0 ctx (.bvar 0) dom :=
  .bvar (Lookup.zero' rfl)

theorem cf'_type : (∅ : VEnv).HasTypeN 1 0 ctx cf' (.forallE dom (.sort (.succ .zero))) :=
  Stratified.app (A := dom) (B := .forallE dom (.sort (.succ .zero)))
    (Stratified.lam (u := .succ .zero) (.sort trivial) cf_type') bvar_type

/-- One `beta` step, in the direction that puts the redex on the left. -/
theorem cf_conv : (∅ : VEnv).IsDefEqN 1 1 ctx cf cf' :=
  .symm (Stratified.beta (A := dom) (e := cf) (e' := .bvar 0) cf_type' bvar_type)

theorem app_cf_sortRedHead : SortRedHead .zero (.app cf (.bvar 0)) := .beta (.sort rfl)

theorem app_cf'_not_sortRedHead : ¬ SortRedHead .zero (.app cf' (.bvar 0)) := nofun

/-- **The head-only predicate is not invariant along `⊢₁`.**  The two applications are
related by one `appDF` whose four typing premises are `⊢₀` derivations over `∅`, and only one
side is head-reducible to a sort — because the other's function is a redex, not a λ. -/
theorem sortRedHeadInv_one_false :
    ¬ ∀ {Γ : List VExpr} {X Y : VExpr} {u : VLevel},
        (∅ : VEnv).IsDefEqN 1 1 Γ X Y → (SortRedHead u X ↔ SortRedHead u Y) := by
  intro h
  exact app_cf'_not_sortRedHead
    ((h (.appDF cf_conv cf_type cf'_type .rfl bvar_type bvar_type)).1 app_cf_sortRedHead)

/-- The same instance in the shape of the residual: `SortRedAppDF`'s premises are all met and
its conclusion fails, for the head-only predicate. -/
theorem sortRedHead_appDF_false :
    ∃ (Γ : List VExpr) (f f' a A B : VExpr) (u : VLevel),
      (∅ : VEnv).IsDefEqN 1 1 Γ f f' ∧ (∅ : VEnv).HasTypeN 1 0 Γ f (.forallE A B) ∧
      (∅ : VEnv).HasTypeN 1 0 Γ f' (.forallE A B) ∧ (∅ : VEnv).HasTypeN 1 0 Γ a A ∧
      SortRedHead u (.app f a) ∧ ¬ SortRedHead u (.app f' a) :=
  ⟨ctx, cf, cf', .bvar 0, dom, .sort (.succ .zero), .zero, cf_conv, cf_type, cf'_type,
    bvar_type, app_cf_sortRedHead, app_cf'_not_sortRedHead⟩

/-- And the witness does **not** refute the real `SortRed`: `cf'` weak-head reduces to `cf`
by one `app` step, so both sides do reach the sort.  This is the check that the repair is a
repair and not a re-labelling. -/
theorem app_cf'_sortRed : SortRed .zero (.app cf' (.bvar 0)) :=
  .step (.app .beta) (.step .beta (.sort rfl))

/-- **`SortRedAppDF` has a non-reflexive instance that holds.**  The premises of the residual
are met at `f = cf`, `f' = cf'` — two syntactically different terms — and the conclusion is
true, because both applications weak-head reduce to `Prop`.  So the residual is not a
statement whose premises nothing satisfies, and not one whose conclusion only ever holds by
`f = f'`. -/
theorem sortRedAppDF_nondegenerate_instance :
    (∅ : VEnv).IsDefEqN 1 1 ctx cf cf' ∧ cf ≠ cf' ∧
      (SortRed .zero (.app cf (.bvar 0)) ↔ SortRed .zero (.app cf' (.bvar 0))) :=
  ⟨cf_conv, by simp [cf, cf'], iff_of_true (.step .beta (.sort rfl)) app_cf'_sortRed⟩

end HeadOnly

end VEnv
end Lean4Lean
