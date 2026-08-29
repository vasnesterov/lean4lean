import Lean4Lean.Theory.Typing.Stratified

/-!
# `thm:utype`: unique typing at the alternation index

`~/lean-type-theory/unique.tex:29–53`.  This file supplies:

* `VEnv.DefInv env U n` — "`⊢ₙ` has definitional inversion" (`unique.tex:29–35`), transcribed
  clause for clause;
* `VEnv.SubstC env U n` — "`⊢ₙ` conversions are closed under instantiation by `⊢ₙ`-typed
  terms".  **This is not in the reference; it is a step the reference takes without
  justification, and `Theory/Typing/SubstCRefute.lean` shows it is FALSE at `n = 1`.**
  See below;
* `VEnv.DefInv.zero` and `VEnv.SubstC.zero` — both hypotheses hold at `n = 0` (`thm:0dinv`);
* `VEnv.Stratified.uniq` — `thm:utype` (`unique.tex:40`), sorry-free from those two.  **Its
  `SubstC` hypothesis is unsatisfiable for `n = 1`, so this theorem has content only at
  `n = 0`** (`HasTypeN.uniq_zero`, which is unconditional).  It is kept because it is the
  exact statement whose hypotheses the refutation now pins down;
* `VEnv.IsDefEqU.sort_inv_of_sortInvN` and
  `VEnv.IsDefEqU.sort_forallE_inv_of_sortForallEDisjN` — the reductions of
  `Theory/Typing/Injectivity.lean`'s open `sort_inv`/`sort_forallE_inv` to `∀ n, SortInvN`
  and `∀ n, SortForallEDisjN`, i.e. to **clauses (1) and (3) of `DefInv` alone**.  They use
  neither `uniq` nor `SubstC` nor clause (2), so they are untouched by both refutations, and
  they are the part of this file that still carries the route.

  They were formerly stated against `∀ n, DefInv env U n`, which
  `Theory/Typing/DefInvRefute.lean`'s `defInv_all_false` refutes over `∅`; see
  `docs/handoff-definv-weakening.md` for the vacuity audit that produced the narrowing.

`Theory/Typing/Stratified.lean` supplies the index and the four "n-provability basics"; this
file is the first thing that uses them.

## The gap in `thm:utype`, and what `SubstC` is

`thm:utype`'s application case (`unique.tex:51`) ends "…so `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`": it
substitutes into a conversion and keeps the index `n`.  **That step is false.**
`Theory/Typing/SubstCRefute.lean` exhibits a counterexample at `n = 1` over the empty
environment, machine-checked, and every rule it relies on is one the reference states with
the same premises (`axioms.tex:38`'s β rule carries its two typing premises, which is what
makes the counterexample stick).

The rest of this section is the counting argument that located the failure before the
counterexample was built.  It is kept because it says *why* the failure is structural rather
than an accident of one example.

`⊢ₙ` is defined by a condition on *derivations* (`unique.tex:14`), and the derivation
transformation raises the index.  Substituting a derivation of `Γ ⊢ₘ e₂ : α` into one of
`Γ,x:α ⊢ₙ β ≡ β'` splices `e₂`'s conversions *underneath* `β`'s, so the alternation counts
add: writing `T(m,n)` for the index of the substituted derivation, `T(m,0) = m` and
`T(m,k+1) = T(m,k)+1`, hence `T(m,n) = m+n`.  That is exactly the index `Stratified.instN`
proves.  In `thm:utype`'s application case `m = n` — both derivations come out of the same
`⊢ₙ` derivation — so the reference's step lands at `2n`, while its consumer `thm:1dinv` needs
it at `n`, feeding it straight back into definitional inversion *at `n`*.  `DefInv` is
neither monotone nor antitone in `n` (clause (1) is antitone, clause (2) is neither), so a
conclusion at `2n` cannot be repaired downstream.

The wall is machine-witnessed and sits exactly where the counting says: an attempt at
`Stratified.instN` with the index preserved goes through for *every* rule except the four
whose typing premises drop an index — `appDF`, `beta`, `eta`, `proofIrrel` — where the
available `Γ ⊢ₙ₊₁ e₀ : A₀` cannot be lowered to the `Γ ⊢ₙ e₀ : A₀` the premise wants.

**What is known about `SubstC`, exactly.**  It holds at `n = 0` (`SubstC.zero`).  It holds at
every `n` for terms whose typing derivation is conversion-free (`SubstC.of_hasTypeN_zero`, an
instance of `Stratified.instN` at `m = 0`) — the only fragment `instN` reaches, since the
`m + n` bound collapses to `n` exactly when `m = 0`.  And it **fails** at `n = 1` as soon as
the substituted term's typing genuinely uses a conversion
(`SubstCRefute.substC_false`).  So the conversion-free fragment is not a limitation of the
proof: it is the whole of the true part.

What this does to the reference's induction: `DefInv 0` (proved) gives `uniq 0` (`SubstC 0`
holds), which the reference's §§3–4 would turn into `DefInv 1`.  The next step needs
`uniq 1`, and `SubstC 1` is false.  **The induction cannot pass `n = 1`.**

## The gap is not local to `thm:utype` — but it is not literally `SubstC` elsewhere

`unique.tex` §§3–4 substitutes at a fixed index three times more:

* `item:p_subst` (`unique.tex:126`) substitutes into `≡ₚ`, whose *reflexivity* and *proof
  irrelevance* rules (`unique.tex:113`, `:118`) carry typing premises `Γ ⊢ e : α` — `⊢ₙ`
  typings, under the §3 convention stated at `unique.tex:64`.  The reference's proof is "All
  parts are easy inductions."
* `item:gg_subst` (`unique.tex:162`) substitutes into `≫ᵏ`, whose `K⁺` rule carries
  `Γ ⊢ intro inv[p,h] : α` — and `unique.tex:107` says outright that this side condition
  "can also be written as a collection of `≡` judgments at `⊢ₙ`".
* `thm:ckappa`'s β case (`unique.tex:251`) has to meet `≡ᵏ`'s own side condition
  `Γ ⊢ e₁,e₂ : α` (`unique.tex:240`) at the contractum `e[e'/x]`.

**These are *not* `SubstC`.**  Each has to reconstruct a `⊢ₙ` **typing** of a substituted
term, not a `⊢ₙ` conversion, and that is a strictly weaker demand: a typing at `n` may use
`conv` at `n`, so the substituted term's own `⊢ₙ` typing is directly usable — which is
exactly what a conversion at `n`, whose typing premises sit at `n−1`, cannot do.  So the
counterexample in `SubstCRefute` does not settle them; it relates two *uninhabited* types.

The statement they need is `VEnv.SubstT` (`Theory/Typing/SubstTRefute.lean`), and **it is
false as well** — at `n = 1`, at substitution depth 1, which is the depth `p_subst`'s and
`gg_subst`'s inductions actually use, since both recurse under λ.  The witness is this one
plus a single move: put the redex in the *context*, where `Lookup` supplies one type and
`conv` the other.

So the plan "restate §§3–4 over `IsDefEqN`" is not expensive transcription — it has no proof
at the index at all.  See `docs/handoff-stratified.md` §12, which also records what is *not*
established: refuting the route is not refuting `item:p_subst`/`item:gg_subst` themselves.

## What would actually fix it, and why the obvious repair does not

With `SubstC` refuted, "prove it" is off the table and only a change to the *definitions*
remains.  Adding instantiation as a **rule** looks like the fix and is not one.  It works
locally: put
it on the conversion half only (the typing half would break `thm:utype`'s primary induction,
whose subject would become an arbitrary substituted term), and then `SubstC` is immediate,
`IsDefEqN.zero_iff` survives (the rule maps a syntactic equality to a syntactic equality),
`mono` and `stratifyN` are unaffected, and instantiation at a preserved index becomes
provable for the typing half too — by induction on the typing derivation alone, since typing
rules never change the index and the one rule mentioning a conversion, `conv`, is discharged
by the new rule.  The depth-0 form is cheap and this was measured, not estimated: adding
`| instC : (Γ ⊢[n] a : A) → (A::Γ ⊢[n] e ≡ e') → Γ ⊢[n] e.inst a ≡ e'.inst a` to
`Stratified` costs exactly four cases — one line each in `mono` and `eq_of_zero`, and in
`weakN`/`instN` a two-line case apiece (`rw [VExpr.liftN_inst_hi, VExpr.liftN_inst_hi]` and
`rw [← VExpr.inst_inst_hi _ _ _ 0 k, ← VExpr.inst_inst_hi _ _ _ 0 k]`; `beta`'s one-sided `▸`
is *not* the template, since both sides of a conversion move).  With those, all five landed
lemmas of `Stratified.lean` stay sorry-free.  The general-depth form is the one §§3–4 would
need — `instT` under a binder requires it — and that one needs a `Ctx.InstN` premise plus
lift/instantiate commutation lemmas for *contexts* that this tree lacks.

But it does not survive downstream.  `thm:1dinv` proves definitional inversion by inducting
on `⊢ₙ₊₁ X ≡ Y` through `thm:ckappa`; a new instantiation rule is a new case, and closing it
needs `≡ᵏ` to be closed under instantiation by `⊢ₙ₊₁`-typed terms — while `≡ₚ`'s and `↝ᵏ`'s
typing side conditions are at `⊢ₙ`.  Pushing the rule down into `≡ₚ` and `↝ᵏ` in turn is
worse: `thm:gg_compat` and `thm:tri` are proved by *inversion* on those relations, and a
substitution rule gives them a case whose subject is an arbitrary substituted term — the same
shape of failure, one level down.

**The missing machinery, stated precisely.**  What is needed is a stratification with both
of:

1. a conversion derivation at level `n+1` uses only typings at level `≤ n` — this is what
   breaks the circularity and is the entire point of the index; and
2. substituting a level-`m` typing derivation into a level-`n` derivation stays at level
   `≤ max(m,n)` — this is what every "substitution lemma" in the development assumes.

(1) and (2) are in tension: (1) forces the measure to count alternations, and alternations
compose additively under substitution, which is exactly what (2) forbids.  Any repair has to
either replace (1) with a different circularity-breaker, or make substitution structural
rather than a derivation transformation — explicit substitutions, or context morphisms
`Γ ⊢ₙ σ : Γ'` as judgment formers, so that "substitute" is a rule whose premises carry their
own index rather than an operation on finished derivations.  Neither exists in this tree, and
neither is in `unique.tex`.

Nothing below depends on how this is resolved: `thm:utype` is proved from `DefInv` and
`SubstC` as stated, and `sort_inv_of_defInv` needs only `DefInv`.

**Why `SubstC` is kept as a hypothesis rather than discharged by the depth-0 rule.**  Because
it is false, and a false hypothesis is worth naming.  Adding the rule would not *prove* it —
it would change the judgment `⊢ₙ` into a different relation, one that is no longer the
reference's `unique.tex:14`, and it would make `DefInv n` — the one remaining open goal on
this route — harder by exactly the case it removes here.  Naming the obligation keeps it
countable and refutable; folding it into the judgment would have hidden a false step inside a
definition that five landed lemmas already describe.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## The two hypotheses

`DefInv` is a **conjunction of three independent clauses**, and since
`Theory/Typing/DefInvRefute.lean` only clause (2) is known false.  The three are therefore
named separately *first*, and `DefInv` is assembled from them, so that a consumer can ask for
exactly the clause it uses and no consumer silently inherits the refuted one.  `DefInv`'s
field names are unchanged (`sort`, `forallE`, `sort_forallE`), so `dinv.sort h` and
`dinv.sort_forallE h` still elaborate exactly as before. -/

/-- **Clause (1) of definitional inversion, alone** (`unique.tex:32`): a `⊢ₙ` conversion
between two sorts equates their levels.

Not refuted by anything known.  `DefInvRefute.defInv_one_false` refutes clause (2) only, so
this clause survives the refutation and is one of the two the live reductions consume. -/
def SortInvN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, env.IsDefEqN U n Γ (.sort u) (.sort v) → u ≈ v

/-- **Clause (3) of definitional inversion, alone** (`unique.tex:34`): no `⊢ₙ` conversion
relates a sort to a Π-type.  Also not refuted. -/
def SortForallEDisjN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr},
    ¬ env.IsDefEqN U n Γ (.sort u) (.forallE A B)

/-- **Clause (2) of definitional inversion, alone** (`unique.tex:33`).

**FALSE.**  `Theory/Typing/DefInvRefute.lean`'s `defInv_one_false` refutes it at `n = 1` over
the empty environment, by context transport: a derivation of the premise may compose two
∀-congruences whose codomain premises live in `Γ,x:A` and `Γ,x:A'`, and `⊢₁` is not invariant
under that change of context because all of its typing premises sit at `⊢₀`, where typing is
syntactically unique.  Anything that consumes this clause is void at that instance. -/
def ForallEInvN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr},
    env.IsDefEqN U n Γ (.forallE A B) (.forallE A' B') →
    env.IsDefEqN U n Γ A A' ∧ env.IsDefEqN U n (A::Γ) B B'

/-- **`⊢ₙ` has definitional inversion** (`unique.tex:29–35`), transcribed clause for clause.

**Known false at `env = ∅`, `U = 1`, `n = 1`** (`DefInvRefute.defInv_one_false`), through
clause (2) alone.  Prefer `SortInvN` / `SortForallEDisjN` wherever only those are used. -/
structure DefInv (env : VEnv) (U n : Nat) : Prop where
  /-- `unique.tex:32`. -/
  sort : SortInvN env U n
  /-- `unique.tex:33`.  **This is the refuted clause.** -/
  forallE : ForallEInvN env U n
  /-- `unique.tex:34`. -/
  sort_forallE : SortForallEDisjN env U n

/-- **`⊢ₙ` conversions are closed under instantiation by `⊢ₙ`-typed terms.**

Not a definition of the reference's; it is the step `thm:utype`'s application case
(`unique.tex:51`) takes without justification.  **It is false**: see
`Theory/Typing/SubstCRefute.lean`, which refutes it at `n = 1`.  True at `n = 0`
(`SubstC.zero`) and on the conversion-free fragment (`SubstC.of_hasTypeN_zero`). -/
def SubstC (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B B' a : VExpr},
    env.HasTypeN U n Γ a A → env.IsDefEqN U n (A::Γ) B B' →
    env.IsDefEqN U n Γ (B.inst a) (B'.inst a)

/-- **`thm:0dinv`** (`unique.tex:56`): `⊢₀` has definitional inversion.

All three clauses are inversion on the term constructor, because `≡₀` *is* syntactic equality
(`IsDefEqN.zero_iff`).  This is the only instance of `DefInv` that exists; without it every
statement below is vacuous. -/
theorem DefInv.zero : env.DefInv U 0 where
  sort h := by have := IsDefEqN.zero_iff.1 h; injection this with h; subst h; rfl
  forallE h := by
    have := IsDefEqN.zero_iff.1 h; injection this with h1 h2
    exact ⟨IsDefEqN.zero_iff.2 h1, IsDefEqN.zero_iff.2 h2⟩
  sort_forallE h := by cases IsDefEqN.zero_iff.1 h

/-- Clause (1) at the base index. -/
theorem SortInvN.zero : env.SortInvN U 0 := DefInv.zero.sort

/-- Clause (3) at the base index. -/
theorem SortForallEDisjN.zero : env.SortForallEDisjN U 0 := DefInv.zero.sort_forallE

/-- Clause (2) at the base index — the *only* index at which it is known to hold, and
`DefInvRefute.defInv_step_zero_false` shows it does not survive one step. -/
theorem ForallEInvN.zero : env.ForallEInvN U 0 := DefInv.zero.forallE

/-- `SubstC` at the base index: substituting into a syntactic equality. -/
theorem SubstC.zero : env.SubstC U 0 := fun _ h =>
  IsDefEqN.zero_iff.2 (by rw [IsDefEqN.zero_iff.1 h])

/-- The fragment of `SubstC` that `Stratified.instN` does reach: the substituted term's
typing derivation must be conversion-free.  `instN` lands at `m + n`, so `m = 0` — and only
`m = 0` — preserves the index.

This is what makes `SubstC` a *gap* rather than a *hypothesis picked to make things work*:
the statement is provable exactly as far as the substitution machinery goes, and no further. -/
theorem SubstC.of_hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {A B B' a : VExpr}
    (h₀ : env.HasTypeN U 0 Γ a A) (H : env.IsDefEqN U n (A::Γ) B B') :
    env.IsDefEqN U n Γ (B.inst a) (B'.inst a) := by
  have := IsDefEqN.inst0 henv h₀ H
  rwa [Nat.zero_add] at this

/-! ## Congruence and equivalence at a fixed index

Every conversion *rule* of `Stratified` concludes at `n+1`, while `thm:utype`'s conclusion is
at `n`.  So each rule that `thm:utype` needs has to be re-proved as an admissible rule at
`n`, by cases on `n`: at `n = 0` the judgment is syntactic equality (`IsDefEqN.zero_iff`) and
the congruence is `congrArg`; at `n = k+1` it is the rule itself. -/

theorem IsDefEqN.symm' {Γ e e'} (H : env.IsDefEqN U n Γ e e') : env.IsDefEqN U n Γ e' e := by
  cases n with
  | zero => exact zero_iff.2 (zero_iff.1 H).symm
  | succ => exact .symm H

theorem IsDefEqN.trans' {Γ e₁ e₂ e₃} (h1 : env.IsDefEqN U n Γ e₁ e₂)
    (h2 : env.IsDefEqN U n Γ e₂ e₃) : env.IsDefEqN U n Γ e₁ e₃ := by
  cases n with
  | zero => exact zero_iff.2 ((zero_iff.1 h1).trans (zero_iff.1 h2))
  | succ => exact .trans h1 h2

/-- The `∀`-congruence at index `n`, on the codomain only — the shape `thm:utype`'s lambda
case needs, where the domain is fixed by the subject `.lam A body`. -/
theorem IsDefEqN.forallE_congr_r {Γ A B B'} (H : env.IsDefEqN U n (A::Γ) B B') :
    env.IsDefEqN U n Γ (.forallE A B) (.forallE A B') := by
  cases n with
  | zero => exact zero_iff.2 (congrArg _ (zero_iff.1 H))
  | succ => exact .forallEDF .rfl H

/-- The sort congruence `thm:utype`'s `forallE` case needs (`unique.tex:50`).  The two
premises live in *different contexts* — the codomain's level is compared in `A::Γ` — and the
conclusion in a third; nothing about the contexts is used, which is why they are all free. -/
theorem IsDefEqN.sort_imax_congr (dinv : env.SortInvN U n) {Γ Γ₁ Γ₂ : List VExpr}
    {u u' v v' : VLevel} (hu : u.WF U) (hu' : u'.WF U) (hv : v.WF U) (hv' : v'.WF U)
    (h1 : env.IsDefEqN U n Γ₁ (.sort u) (.sort u'))
    (h2 : env.IsDefEqN U n Γ₂ (.sort v) (.sort v')) :
    env.IsDefEqN U n Γ (.sort (.imax u v)) (.sort (.imax u' v')) := by
  cases n with
  | zero =>
    have e1 : u = u' := by injection zero_iff.1 h1
    have e2 : v = v' := by injection zero_iff.1 h2
    subst e1; subst e2; exact .rfl
  | succ =>
    exact .sortDF (by exact ⟨hu, hv⟩) (by exact ⟨hu', hv'⟩)
      (VLevel.imax_congr (dinv h1) (dinv h2))

/-! ## Inversion by subject shape

`thm:utype` is stated by the reference as a double induction, the secondary one peeling
conversion rules off the second derivation (`unique.tex:46–48`).  Peeling is the same work
for every subject shape, so it is done once here, as six inversion lemmas — each an induction
whose only interesting case is `conv`, discharged by transitivity at the index.  The primary
induction in `Stratified.uniq` then has no nested induction at all.

The `b = true` argument is how one induction over the `Bool`-indexed judgment is restricted
to its typing half: the eleven conversion constructors carry `b := false` and die on
`nomatch`. -/

theorem Stratified.bvar_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ i, e = .bvar i → b = true → ∃ A, Lookup Γ i A ∧ env.IsDefEqN U n Γ A T := by
  induction H with
  | bvar h => intro _ eq _; cases eq; exact ⟨_, h, .rfl⟩
  | sort | const | app | lam | forallE => intro _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro i eq hb
    have ⟨A, h1, h2⟩ := ih2 i eq hb
    exact ⟨A, h1, IsDefEqN.trans' h2 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

theorem HasTypeN.bvar_inv {Γ i T} (H : env.HasTypeN U n Γ (.bvar i) T) :
    ∃ A, Lookup Γ i A ∧ env.IsDefEqN U n Γ A T := H.bvar_inv' _ rfl rfl

theorem Stratified.sort_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ l, e = .sort l → b = true → l.WF U ∧ env.IsDefEqN U n Γ (.sort (.succ l)) T := by
  induction H with
  | sort h => intro _ eq _; cases eq; exact ⟨h, .rfl⟩
  | bvar | const | app | lam | forallE => intro _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro l eq hb
    have ⟨h1, h2⟩ := ih2 l eq hb
    exact ⟨h1, IsDefEqN.trans' h2 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

theorem HasTypeN.sort_inv {Γ l T} (H : env.HasTypeN U n Γ (.sort l) T) :
    l.WF U ∧ env.IsDefEqN U n Γ (.sort (.succ l)) T := H.sort_inv' _ rfl rfl

theorem Stratified.const_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ c ls, e = .const c ls → b = true →
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      env.IsDefEqN U n Γ (ci.type.instL ls) T := by
  induction H with
  | const h1 h2 h3 => intro _ _ eq _; cases eq; exact ⟨_, h1, h2, h3, .rfl⟩
  | bvar | sort | app | lam | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro c ls eq hb
    have ⟨ci, h1, h2, h3, h4⟩ := ih2 c ls eq hb
    exact ⟨ci, h1, h2, h3, IsDefEqN.trans' h4 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.const_inv {Γ c ls T} (H : env.HasTypeN U n Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      env.IsDefEqN U n Γ (ci.type.instL ls) T := H.const_inv' _ _ rfl rfl

theorem Stratified.app_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ f a, e = .app f a → b = true →
    ∃ A B, env.HasTypeN U n Γ f (.forallE A B) ∧ env.HasTypeN U n Γ a A ∧
      env.IsDefEqN U n Γ (B.inst a) T := by
  induction H with
  | app h1 h2 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, .rfl⟩
  | bvar | sort | const | lam | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro f a eq hb
    have ⟨A, B, h1, h2, h3⟩ := ih2 f a eq hb
    exact ⟨A, B, h1, h2, IsDefEqN.trans' h3 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.app_inv {Γ f a T} (H : env.HasTypeN U n Γ (.app f a) T) :
    ∃ A B, env.HasTypeN U n Γ f (.forallE A B) ∧ env.HasTypeN U n Γ a A ∧
      env.IsDefEqN U n Γ (B.inst a) T := H.app_inv' _ _ rfl rfl

theorem Stratified.lam_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ A body, e = .lam A body → b = true →
    ∃ u B, env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) body B ∧
      env.IsDefEqN U n Γ (.forallE A B) T := by
  induction H with
  | lam h1 h2 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, .rfl⟩
  | bvar | sort | const | app | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro A body eq hb
    have ⟨u, B, h1, h2, h3⟩ := ih2 A body eq hb
    exact ⟨u, B, h1, h2, IsDefEqN.trans' h3 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.lam_inv {Γ A body T} (H : env.HasTypeN U n Γ (.lam A body) T) :
    ∃ u B, env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) body B ∧
      env.IsDefEqN U n Γ (.forallE A B) T := H.lam_inv' _ _ rfl rfl

theorem Stratified.forallE_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ A B, e = .forallE A B → b = true →
    ∃ u v, u.WF U ∧ v.WF U ∧ env.HasTypeN U n Γ A (.sort u) ∧
      env.HasTypeN U n (A::Γ) B (.sort v) ∧
      env.IsDefEqN U n Γ (.sort (.imax u v)) T := by
  induction H with
  | forallE h1 h2 h3 h4 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, h3, h4, .rfl⟩
  | bvar | sort | const | app | lam => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro A B eq hb
    have ⟨u, v, h1, h2, h3, h4, h5⟩ := ih2 A B eq hb
    exact ⟨u, v, h1, h2, h3, h4, IsDefEqN.trans' h5 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.forallE_inv {Γ A B T} (H : env.HasTypeN U n Γ (.forallE A B) T) :
    ∃ u v, u.WF U ∧ v.WF U ∧ env.HasTypeN U n Γ A (.sort u) ∧
      env.HasTypeN U n (A::Γ) B (.sort v) ∧
      env.IsDefEqN U n Γ (.sort (.imax u v)) T := H.forallE_inv' _ _ rfl rfl

/-! ## `thm:utype` -/

/-- **Unique typing at the index** (`thm:utype`, `unique.tex:40–53`): if `⊢ₙ` has definitional
inversion and is closed under instantiation, then a term's `⊢ₙ` types are all `⊢ₙ`-equal.

The reference's proof is a double induction; here the secondary induction has been factored
out into the `*_inv` lemmas above, so this is a single induction on the first derivation, with
the hypotheses reverted because `n` is an index of `Stratified` and is generalised by it.

Case by case against `unique.tex:48–51`: `conv` is the reference's (1); `bvar`, `sort`,
`const`, `lam` are its (2) — `lam` is "trivial" there but needs the index-`n` `∀`-congruence
here; `forallE` is its (3) and `app` its (4).  `DefInv` is consumed in exactly `app` and
`forallE`; `SubstC` in exactly `app`. -/
theorem Stratified.uniq {Γ e A b} (H : Stratified env U n Γ e A b) :
    env.DefInv U n → env.SubstC U n → b = true →
    ∀ B, env.HasTypeN U n Γ e B → env.IsDefEqN U n Γ A B := by
  induction H with
  | bvar h =>
    intro _ _ _ _ H2
    have ⟨_, h1, h2⟩ := H2.bvar_inv
    exact Lookup.uniq h h1 ▸ h2
  | sort _ => intro _ _ _ _ H2; exact H2.sort_inv.2
  | const h1 _ _ =>
    intro _ _ _ _ H2
    have ⟨_, h1', _, _, h2⟩ := H2.const_inv
    cases Option.some.inj (h1'.symm.trans h1); exact h2
  | app _ ha ihf _ =>
    intro dinv hs _ _ H2
    have ⟨_, _, hf', _, hc⟩ := H2.app_inv
    exact IsDefEqN.trans' (hs ha (dinv.forallE (ihf dinv hs (Eq.refl true) _ hf')).2) hc
  | lam _ _ _ ihb =>
    intro dinv hs _ _ H2
    have ⟨_, _, _, hb', hc⟩ := H2.lam_inv
    exact IsDefEqN.trans' (IsDefEqN.forallE_congr_r (ihb dinv hs (Eq.refl true) _ hb')) hc
  | forallE hu hv _ _ ihA ihB =>
    intro dinv hs _ _ H2
    have ⟨_, _, hu', hv', hA', hB', hc⟩ := H2.forallE_inv
    exact IsDefEqN.trans' (IsDefEqN.sort_imax_congr dinv.sort hu hu' hv hv'
      (ihA dinv hs (Eq.refl true) _ hA') (ihB dinv hs (Eq.refl true) _ hB')) hc
  | conv h _ _ ih2 =>
    intro dinv hs _ _ H2
    exact IsDefEqN.trans' (IsDefEqN.symm' h) (ih2 dinv hs (Eq.refl true) _ H2)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

/-- `thm:utype` in the form it is used: `Γ ⊢ₙ e : A` and `Γ ⊢ₙ e : B` give `Γ ⊢ₙ A ≡ B`. -/
theorem HasTypeN.uniq (dinv : env.DefInv U n) (hs : env.SubstC U n) {Γ e A B}
    (H1 : env.HasTypeN U n Γ e A) (H2 : env.HasTypeN U n Γ e B) :
    env.IsDefEqN U n Γ A B := Stratified.uniq H1 dinv hs (Eq.refl true) _ H2

/-! ## Where the theorem has content, and where it does not

`DefInv` and `SubstC` are hypotheses everywhere above, and hypotheses nothing satisfies prove
nothing.  Both hold at `n = 0`, and `SubstC` is false at `n = 1`
(`SubstCRefute.substC_false`), so **`n = 0` is the whole of the theorem's content** until the
definitions change.

At `n = 0` it reads: *a term's conversion-free types are syntactically equal* — `uniq_zero`
below, which depends on no hypothesis at all — a real statement, not a tautology, over an
inhabited class of derivations (`sort_zero_ex`). -/

/-- `thm:utype` at the base index, unfolded through `IsDefEqN.zero_iff`: at index `0` unique
typing is *syntactic* uniqueness of the type.  Depends on no hypothesis at all — `DefInv.zero`
and `SubstC.zero` are both proved. -/
theorem HasTypeN.uniq_zero {Γ e A B}
    (H1 : env.HasTypeN U 0 Γ e A) (H2 : env.HasTypeN U 0 Γ e B) : A = B :=
  IsDefEqN.zero_iff.1 (H1.uniq DefInv.zero SubstC.zero H2)

/-- A derivation at index `0`, so `uniq_zero` is not speaking about the empty relation. -/
theorem sort_zero_ex {Γ : List VExpr} {l : VLevel} (h : l.WF U) :
    env.HasTypeN U 0 Γ (.sort l) (.sort (.succ l)) := .sort h

example (Γ : List VExpr) {l : VLevel} (h : l.WF U) :
    VExpr.sort (.succ l) = VExpr.sort (.succ l) :=
  HasTypeN.uniq_zero (sort_zero_ex (env := env) (Γ := Γ) h) (sort_zero_ex h)

/-! ## What this buys against the target

`Theory/Typing/Injectivity.lean`'s `IsDefEqU.sort_inv` and `IsDefEqU.sort_forallE_inv` —
still `sorry` there — follow from definitional inversion *at every index* and nothing else,
by `IsDefEqU.stratifyN`.  Neither `SubstC` nor `uniq` appears: these two need only `DefInv`,
which is why the refutation above leaves them standing.  That is the direction the target
needs; the converse (`IsDefEqN n → IsDefEqU`) is the reference's regularity upgrade, needs
`uniq` itself, and is not required here.

So `∀ n, DefInv env U n` remains a *sufficient* hypothesis for the sort half of the
injectivity cone, and it is the one surviving handle on the target.  What the refutation
removes is the reference's way of *establishing* that hypothesis: `unique.tex` proves
`DefInv (n+1)` from `DefInv n` via `uniq n`, and `uniq n` is unavailable for `n ≥ 1`.
`DefInv` itself is not refuted — nothing here says it is false, only that this route to it is
closed. -/

/-- `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`), reduced to **clause (1) alone** at
every index.

Formerly stated against `∀ n, DefInv env U n`, which `DefInvRefute.defInv_all_false` refutes
over `∅`; the proof never touched any clause but this one, so the hypothesis is narrowed
rather than the theorem lost.  `∀ n, SortInvN env U n` is not refuted by anything known. -/
theorem IsDefEqU.sort_inv_of_sortInvN (henv : Ordered env) {Γ : List VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (dinv : ∀ n, env.SortInvN U n)
    (h : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  dinv n hc

/-- `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean`), reduced to **clause (3)
alone** at every index.  Same narrowing, same reason.

**`Ordered env` is not enough to discharge `dinv`.**  `Theory/Typing/SortClauses.lean`'s
`sortPiEnv` is an `Ordered` environment carrying the rule `Prop ≡ ∀ (_ : Prop), Prop`, and at
it `SortForallEDisjN` is *false* at index 1.  The `Ordered` premise here is only what
`stratifyN` needs; a proof of the hypothesis has to use `VEnv.WF`, which is what
`Theory/Typing/Injectivity.lean`'s targets already assume. -/
theorem IsDefEqU.sort_forallE_inv_of_sortForallEDisjN (henv : Ordered env) {Γ : List VExpr}
    {u : VLevel} {A B : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (dinv : ∀ n, env.SortForallEDisjN U n) :
    ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B) := fun h =>
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  dinv n hc

/-! ## Can `DefInv` be proved directly, without `uniq`?

Asked because `uniq` is gone for `n ≥ 1` (`SubstCRefute`) while `DefInv` survives and is what
the two reductions above actually need.  Attempted: the direct induction on the conversion
derivation, all three clauses.  Everything closes except

* **`trans`** — `.sort u ≡ₙ e ≡ₙ .sort v` with `e` arbitrary — for all three clauses;
* **`proofIrrel`** — for all three clauses;
* **`symm`, clause (2) only** — the IH lands `B ≡ B'` in context `A'::Γ` while the conclusion
  is in `A::Γ`, so it wants context conversion at a preserved index.  That is the same family
  as the refuted `SubstC` (at a `bvar 0` occurrence the context's new head type is reachable
  only through a conversion, which raises the index), though it has not been refuted here.

Of these, `proofIrrel` **is** improved by the index, and `sort_proofIrrel` below is the
statement of that: unstratified, `Injectivity.lean`'s `proofIrrel` case needs `VEnv.SortUniq`
— universe uniqueness for an *arbitrary* subject.  At the index it needs only clause (1)
itself, on a different instance, and not even the `Prop`-ness premise.

It still does not close, and the reason is worth recording so it is not re-attempted: the
instance it recurses on is *not smaller*.  The derivation it builds has height
`max(h₂,h₃) + O(1)` against the `proofIrrel` node's `max(h₁,h₂,h₃) + 1`, so the obvious
well-founded measure gives `≤`, not `<`.

And `trans` cannot even be *stated* as a residual hypothesis without new machinery: any
formulation that avoids naming a reduction relation — e.g. "`Γ ⊢ₙ .sort u ≡ e` and
`Γ ⊢ₙ e ≡ .sort v` give `u ≈ v`" — is equivalent to clause (1) itself, by `trans`.  Saying
what is missing requires "`e` reduces to a sort", i.e. the κ-reduction of `unique.tex` §3.

So: `DefInv` does not yield to a direct argument, and the machinery it needs is the same
§§3–4 development in which the substitution obstruction was found at two further sites. -/

/-- The `proofIrrel` case of clause (1), at the index: it reduces to clause (1) itself.

Contrast `Theory/Typing/SortUniq.lean`'s `sort_not_proof`, which discharges the same case for
the unstratified judgment but needs `VEnv.SortUniq`.  Here the two `sort` typings are inverted
by `HasTypeN.sort_inv` and composed, and clause (1) finishes.  The `Γ ⊢ₙ p : .sort .zero`
premise is not needed at all. -/
theorem SortInvN.sort_proofIrrel (dinv1 : env.SortInvN U n)
    {Γ : List VExpr} {p : VExpr} {u v : VLevel}
    (h2 : env.HasTypeN U n Γ (.sort u) p) (h3 : env.HasTypeN U n Γ (.sort v) p) :
    u ≈ v :=
  VLevel.succ_congr_iff.1
    (dinv1 (IsDefEqN.trans' (HasTypeN.sort_inv h2).2 (IsDefEqN.symm' (HasTypeN.sort_inv h3).2)))

/-! ## `PropTypeAgree`, and what it buys

The set model's sole syntactic import (after its re-parameterisation) is

> `Γ ⊢ e : A`, `Γ ⊢ e : A'`, `A` a proposition ⟹ `A'` a proposition.

It is strictly weaker than unique typing — binary, not an equality — and it passes the
cumulativity check that refuted `SortUniq` (cumulativity retypes at *sorts* and never gives a
proof a second type).

**The criterion that decides these statements**, and it has now predicted twice before
explaining: *a conclusion **propagated along** a conversion tolerates an arbitrary middle
term; one **asserted of** its endpoints does not.*  `sort_inv`'s `trans` case fails because
`.sort u ≡ e₂ ≡ .sort v` says nothing about `e₂`.  `PropTypeAgree`'s residual —
`A ≡ₙ A' ⟹ (IsProp A ↔ IsProp A')` — is of the first kind, and its `trans` case closes by
composition.  `PropUniq`, the model's *other* import, is of the second kind and inherits
`sort_inv`'s wall.

**Status of the residual**, machine-checked at the index: `rfl`, `symm`, `trans` (composition),
`sortDF` (retype along the level equivalence) and `lamDF` (vacuous by `DefInv` clause (3))
close; `constDF`, `forallEDF`, `appDF`, `beta`, `eta`, `proofIrrel`, `extra` are open.
`forallEDF` resists on context conversion — which is *already* target-preserving here, so the
blocker is the index drop rather than an injectivity dependency — and `proofIrrel` is vacuous
*given the statement itself*, so it wants a separate argument rather than a case in the
induction.

Work this statement **at the index, not unstratified.**  Unstratified the `sortDF` case needs
`HasTypeStrong.sort_type`, which provably takes `SortUniq` as a hypothesis because this tree's
`IsDefEq` is type-indexed; at the index `HasTypeN.sort_inv` is free.  The setting that looks
like the escape is the one carrying the port's own defect. -/

/-- `A` is a proposition. -/
abbrev IsPropN (env : VEnv) (U n : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  env.HasTypeN U n Γ A (.sort .zero)

/-- **The set model's syntactic import**, at the index. -/
def PropTypeAgree (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr},
    env.HasTypeN U n Γ e A → env.HasTypeN U n Γ e A' →
    IsPropN env U n Γ A → IsPropN env U n Γ A'

/-- **The payoff, checked rather than assumed: a sort is not a proof.**

This is `Theory/Typing/SortUniq.lean`'s `sort_not_proof` at the index, and it is derived here
from `PropTypeAgree` and `DefInv` *at the same index* — so in the induction that proves
`DefInv (n+1)`, both are available as the induction hypothesis and nothing is circular. -/
theorem sortNotProof_of (dinv : env.SortInvN U n) (pta : env.PropTypeAgree U n)
    {Γ : List VExpr} {p : VExpr} {u : VLevel}
    (h1 : env.HasTypeN U n Γ p (.sort .zero)) (h2 : env.HasTypeN U n Γ (.sort u) p) :
    False := by
  have h4 : IsPropN env U n Γ (.sort (.succ u)) := pta h2 (.sort (HasTypeN.sort_inv h2).1) h1
  exact absurd (congrFun (dinv (HasTypeN.sort_inv h4).2) []) (by simp [VLevel.eval])

/-- **The payoff, second half: a Π-type is not a proof.**  Note this is *not* "a Π-type is not
a proposition", which is false — `∀ x : α, β` is a proposition whenever `β` is.  It says a
*term whose type is a Π* does not also inhabit a proposition. -/
theorem forallENotProof_of (dinv : env.SortInvN U n) (pta : env.PropTypeAgree U n)
    {Γ : List VExpr} {p A B : VExpr}
    (h1 : env.HasTypeN U n Γ p (.sort .zero)) (h2 : env.HasTypeN U n Γ (.forallE A B) p) :
    False := by
  obtain ⟨u, v, hu, hv, hA, hB, _⟩ := HasTypeN.forallE_inv h2
  have h4 : IsPropN env U n Γ (.sort (.imax u v)) := pta h2 (.forallE hu hv hA hB) h1
  exact absurd (congrFun (dinv (HasTypeN.sort_inv h4).2) []) (by simp [VLevel.eval])

/-! ## Is `PropTypeAgree` closable at the index? — **No: one new primitive is needed**

Three of its open cases were characterised as blocked.  They are **two** obstructions, not one
and not three, and the split is machine-checked below.

* **`forallEDF`** wants **context conversion at a preserved index** — `A::Γ ⊢ₙ B' : .sort .zero`
  transported to `A'::Γ` along `A ≡ₙ A'`.  Its induction drops an index exactly as
  `SubstC` does (the conversion is available at `n+1`, the typing premises want it at `n`), so
  it is in the family refuted in `Theory/Typing/SubstCRefute.lean`, and by the arithmetic in
  `docs/options-circularity-breakers.md` a rule cannot repair it.

* **`proofIrrel` is a self-reference; `eta` is a new statement.**  These look alike and are
  not.  `proofIrrel`'s residual is exactly `PropNotProof`, and `propNotProof_of` shows that is
  an *instance of `PropTypeAgree` itself* — so it is the same statement at a different
  subject, with the measure giving `≤` not `<`.  `eta`'s residual is exactly
  `SortForallEDisjoint`, which is **not** an instance of `PropTypeAgree`: it is a separate
  weakening of unique typing, about a term's types being a sort versus a Π rather than about
  propositionhood.

So `PropTypeAgree` is **not self-sufficient**.  The primitive to route or fund is
`SortForallEDisjoint`.

*On its semantic status, stated precisely.*  It passes the cumulativity check — cumulativity
retypes at sorts and never gives a Π-typed term a sort type.  **That licenses "not excluded",
not "open".**  A negative check rules a route out; passing one does not rule a route in.  In
fact the model route is closed for a different reason: `Theory/SetModel/` is parameterised on
`LevelAssign` (see `Typing/SortUniq.lean`), and a cut-down model bottoms out at
`sort_not_proof` — which is `PropTypeAgree` at a sort, i.e. the same self-reference this
docstring describes, reached from the semantic side.

*And a refutation is provably impossible at the model's own witness.*
`sortForallEDisjoint_of` below forces any counterexample to have an **application** subject;
the witness at which the model fails to separate — `False` versus `∀ x : False, B` — is a
**constant**, and the `const` case is proved.  So the model's non-separation is real and
cannot be lifted to syntax there.  The two facts are consistent, not in tension. -/

/-- **The primitive `PropTypeAgree` needs and does not contain**: no term has both a sort type
and a Π type.  `eta`'s case of `PropTypeAgree` is exactly this and nothing else. -/
def SortForallEDisjoint (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {u : VLevel},
    env.HasTypeN U n Γ e (.sort u) → env.HasTypeN U n Γ e (.forallE A B) → False

/-- No term is both a proposition and a proof.  `proofIrrel`'s case of `PropTypeAgree` is
exactly this — and `propNotProof_of` below shows it is `PropTypeAgree` itself at another
subject, so that case is self-reference rather than a missing statement. -/
def PropNotProof (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e p : VExpr},
    env.HasTypeN U n Γ e (.sort .zero) → env.HasTypeN U n Γ p (.sort .zero) →
    env.HasTypeN U n Γ e p → False

/-- `eta`'s case closes from `SortForallEDisjoint` and `DefInv`, and needs nothing else. -/
theorem PropTypeAgree.eta_case (dinv : env.SortForallEDisjN U n)
    (hd : env.SortForallEDisjoint U n)
    {Γ : List VExpr} {A B e : VExpr} (he : env.HasTypeN U n Γ e (.forallE A B)) :
    (IsPropN env U n Γ (.lam A (.app e.lift (.bvar 0))) ↔ IsPropN env U n Γ e) := by
  refine ⟨fun hp => ?_, fun hp => absurd (hd hp he) not_false⟩
  obtain ⟨_, _, _, _, hcc⟩ := HasTypeN.lam_inv hp
  exact absurd (IsDefEqN.symm' hcc) dinv

/-- `proofIrrel`'s case closes from `PropNotProof`, and needs nothing else. -/
theorem PropTypeAgree.proofIrrel_case (hnp : env.PropNotProof U n)
    {Γ : List VExpr} {p h h' : VExpr}
    (h1 : env.HasTypeN U n Γ p (.sort .zero))
    (h2 : env.HasTypeN U n Γ h p) (h3 : env.HasTypeN U n Γ h' p) :
    (IsPropN env U n Γ h ↔ IsPropN env U n Γ h') :=
  ⟨fun hp => absurd (hnp hp h1 h2) not_false, fun hp => absurd (hnp hp h1 h3) not_false⟩

/-- The one case of `SortForallEDisjoint` that does not close: the subject is an application,
whose type is not shape-pinned.  Relating the two types needs the function's two Π-types plus
substitution — and only a *disjointness* consequence of it, not the equality form refuted in
`Theory/Typing/SubstCRefute.lean`. -/
def SortForallEDisjoint.AppCase (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A B : VExpr} {u : VLevel},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.HasTypeN U n Γ (.app f a) (.forallE A B) → False

/-- **`SortForallEDisjoint` closes in six of its seven typing cases**, from `DefInv` alone.
`trans` never arises — it is a *conversion* rule, and this is an induction on typing — so the
statement is on the tractable side of the criterion, and more decisively than `PropTypeAgree`,
which does have a conversion induction underneath it.

**What this says about refuting it:** any counterexample must have an **application** as its
subject.  In particular a *constant* subject cannot be one, so the model's failure to separate
`False` from `∀ x : False, B` — real, and structural in ZF — **cannot be lifted to a syntactic
derivation at that instance**, because the `const` case below proves the syntactic statement
there. -/
theorem sortForallEDisjoint_ofN {Γ e T b} (H : Stratified env U n Γ e T b) :
    SortForallEDisjoint.AppCase env U n → env.SortForallEDisjN U n → b = true →
    ∀ u A B, env.IsDefEqN U n Γ T (.sort u) →
    env.HasTypeN U n Γ e (.forallE A B) → False := by
  induction H with
  | bvar h =>
    intro _ dinv _ u A B hT H2
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact dinv (IsDefEqN.trans' (IsDefEqN.symm' hT) (Lookup.uniq h hl ▸ hc))
  | sort _ =>
    intro _ dinv _ u A B hT H2
    exact dinv (HasTypeN.sort_inv H2).2
  | const h1 _ _ =>
    intro _ dinv _ u A B hT H2
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact dinv (IsDefEqN.trans' (IsDefEqN.symm' hT) hc)
  | lam _ _ =>
    intro _ dinv _ u A B hT _
    exact dinv (IsDefEqN.symm' hT)
  | forallE _ _ _ _ =>
    intro _ dinv _ u A B hT H2
    obtain ⟨_, _, _, _, _, _, hc⟩ := HasTypeN.forallE_inv H2
    exact dinv hc
  | conv h _ _ ih2 =>
    intro happ dinv _ u A₁ B₁ hT H2
    exact ih2 happ dinv (Eq.refl true) u A₁ B₁ (IsDefEqN.trans' h hT) H2
  | app hf ha _ _ =>
    intro happ _ _ u A B hT H2
    exact happ hf ha hT H2
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

/-- The same with the whole of `DefInv` in place of clause (3).

**This form is strictly weaker and is retained only for the one call site that has not been
updated** — `propForallEDisjoint_of` (`Theory/Typing/PropConv.lean:331`), a file this stream
does not own.  The fix there is one token: pass `dinv.sort_forallE` instead of `dinv` and call
`sortForallEDisjoint_ofN`.  Once that is done this declaration should be deleted; nothing else
in the tree uses it.  `DefInv` is refuted at `∅, 1, 1` (`DefInvRefute.defInv_one_false`), so
at that instance this form proves nothing and `sortForallEDisjoint_ofN` still does. -/
theorem sortForallEDisjoint_of {Γ e T b} (H : Stratified env U n Γ e T b) :
    SortForallEDisjoint.AppCase env U n → env.DefInv U n → b = true →
    ∀ u A B, env.IsDefEqN U n Γ T (.sort u) →
    env.HasTypeN U n Γ e (.forallE A B) → False :=
  fun happ dinv => sortForallEDisjoint_ofN H happ dinv.sort_forallE

/-- **The split, machine-checked:** `PropNotProof` *is* `PropTypeAgree` at another subject, so
`proofIrrel` is self-reference.  There is no corresponding derivation for
`SortForallEDisjoint`, which is why that one is a genuinely missing primitive. -/
theorem propNotProof_of (dinv : env.SortInvN U n) (pta : env.PropTypeAgree U n) :
    env.PropNotProof U n := by
  intro Γ e p hep hp hepp
  have := pta hepp hep hp
  exact absurd (congrFun (dinv (HasTypeN.sort_inv this).2) []) (by simp [VLevel.eval])

end VEnv
end Lean4Lean
