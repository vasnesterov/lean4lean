import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.DeclRules
import Lean4Lean.Theory.Typing.NotProof

/-!
# Structural inversion principles we cannot prove yet

Six statements, in two families.

## Sorts and Π-types

`sort_inv`, `forallE_inv_stratified`, `forallE_inv`, `sort_forallE_inv` — the original four.
`forallE_inv` is *derived* from the stratified form here.

**Do not plan against `Experimental/Reflect/Capstone.lean`.**  An earlier version of this
docstring said Capstone "now proves `forallE_inv` directly, relative to a `Params`
instance", and that the arrow would reverse once an instance landed.  That route is closed:
the `Params`-style side condition its main result carries is *provably unsatisfiable*, so
everything it exports is vacuously true.  Its proof *shapes* are still worth reading —
`sort_uniq_of_hasType` and `forallE_inv_stratified_params` name the real obligations
correctly — but nothing there is available as a proof.  Treat every statement under
`Lean4Lean/Experimental/` as unproved regardless of how it reads.

## Constant applications — three different facts, and they are not interchangeable

`docs/design-inductive.md`'s ledger entry **I13 records only the first of these**, under the
name `const_forallE_inv`, while five consumers across two streams need the second or the
third.  Distinguishing them is the point of this section; see `docs/research-const-inv.md`
§1.

* **(A) Disjointness** — a rule-free constant application is not a Π, and is not a sort.
  `const_forallE_inv` and `const_sort_inv` below.  **Three independent consumers, found by
  three streams separately:** `pat_major_not_pi` (ledger I14); this file's own inversion
  targets; and the set model's block-freeness lemma, whose base cases are exactly these two.
  The sort half went unstated in this tree until the third consumer asked for it — a missing
  statement is worse than an open one, because an open one is visible in a `sorry` count and
  a missing one is invisible until someone needs it.
* **(B) Injectivity** — two applications of the *same* constant force their level and
  argument lists to agree.  `const_app_inv` below.  Consumers:
  `Verify/TypeChecker/WHNF.lean`'s `reduceRecursor.WF` quotient branch and its `Quot.ind`
  arm (both need `Quot α r ≡ Quot α' r' → α ≡ α'`), and `TrProj.uniq` / `TrProj.defeqDFC`
  (`Verify/Typing/Lemmas.lean`).
* **(C) Rigidity** — a term definitionally equal to a constant application reduces to one
  with the same head, so its components can be read back in the smaller context.  Consumer:
  `TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`, see the route traced in its docstring).
  **Deliberately not stated here.**  Its only faithful formulation mentions weak-head
  reduction, which lives in `Theory/Typing/HeadReduction.lean` — downstream of this file and
  gated on `Params`.  Writing a reduction-free approximation is how one gets a fourth wrong
  statement; it should be stated where the reduction relation is in scope.

### Why (B) carries two side conditions

Both are load-bearing, and **both are machine-checked in
`Theory/Typing/ConstInvWitness.lean`** — as regression tests, not prose, so that dropping
either one makes that file prove `False`.

* `RuleFreeHead` — without it, a constant whose value is a constant function identifies all
  its arguments (`w1`).  This is the condition the ledger already records.
* `IsType` on the application — without it, `IsDefEq.proofIrrel` identifies *any* two
  applications that land in a proposition, **with no reduction and with no rule in the
  environment at all** (`w2`).  `RuleFreeHead` does not repair this, which is why the
  ledger's single condition is not enough.

Both consumers' sites satisfy `IsType` for free: they use the fact at the *type* of a term.

A fourth fact — no-confusion between *distinct* rule-free constants — is not stated because
no consumer has asked for it; (B) is same-head only.
-/

namespace Lean4Lean

/-- The head constant of an application spine, under any number of leading lambdas.

Spelled out here rather than reusing `PatternDecode.lean`'s `peelLams`/`spine` so that this
file keeps a short import list; the λ-peeling matters because a rule with parameters stores
its left-hand side λ-abstracted (`Theory/Quot.lean`'s `quotDefEq`, `VInductDecl'.iotaRule`),
while a δ-rule's is the bare `.const c (VLevel.params _)`. -/
def VExpr.headConst? : VExpr → Option Lean.Name
  | .const c _ => some c
  | .app f _ => f.headConst?
  | .lam _ b => b.headConst?
  | _ => none

/-- The head of an application spine, **without** peeling λ — unlike `headConst?`, which
does.  `headConst?` is the right instrument for `extra` (a rule's lhs is λ-abstracted);
`spineHead` is the right one for `beta`, where the spine head is a `.lam` and `headConst?`
would look straight through it. -/
def VExpr.spineHead : VExpr → VExpr
  | .app f _ => VExpr.spineHead f
  | e => e

theorem VExpr.spineHead_mkApp : ∀ (as : List VExpr) (f : VExpr),
    VExpr.spineHead (f.mkApp as) = VExpr.spineHead f
  | [], _ => rfl
  | a :: as, f => VExpr.spineHead_mkApp as (.app f a)

theorem VExpr.headConst?_instL : ∀ (e : VExpr) (ls : List VLevel),
    (e.instL ls).headConst? = e.headConst?
  | .const _ _, _ | .bvar _, _ | .sort _, _ | .forallE _ _, _ => rfl
  | .app f _, ls => VExpr.headConst?_instL f ls
  | .lam _ b, ls => VExpr.headConst?_instL b ls

theorem VExpr.headConst?_mkApp : ∀ (as : List VExpr) (f : VExpr),
    (f.mkApp as).headConst? = f.headConst?
  | [], _ => rfl
  | a :: as, f => VExpr.headConst?_mkApp as (.app f a)

/-- **Peeling the last argument off a spine.**  If `f.mkApp as` is an application then
either the spine is empty and `f` is that application, or the application's argument is the
spine's *last* entry and its function is the shorter spine.

`const_app_inv`'s `appDF` case is what needs this: the derivation hands back `.app f a`, and
the invariant has to read that back as `(.const c ls).mkApp (bs ++ [a])`. -/
theorem VExpr.mkApp_app_inv {g b : VExpr} :
    ∀ (as : List VExpr) (f : VExpr), f.mkApp as = .app g b →
      (as = [] ∧ f = .app g b) ∨ ∃ as', as = as' ++ [b] ∧ f.mkApp as' = g := by
  intro as
  induction as with
  | nil => intro f h; exact .inl ⟨rfl, h⟩
  | cons a as ih =>
    intro f h
    rw [VExpr.mkApp_cons] at h
    rcases ih (f.app a) h with ⟨hnil, heq⟩ | ⟨as', has, heq⟩
    · subst hnil
      injection heq with h1 h2
      exact .inr ⟨[], by simp [h2], h1⟩
    · exact .inr ⟨a :: as', by rw [has]; rfl, by rw [VExpr.mkApp_cons]; exact heq⟩

/-- A spine whose value is not an application is the empty spine. -/
theorem VExpr.mkApp_eq_of_not_app :
    ∀ (as : List VExpr) (f e : VExpr), f.mkApp as = e → (∀ g b, e ≠ .app g b) →
      as = [] ∧ f = e := by
  intro as
  cases as with
  | nil => intro f e h _; exact ⟨rfl, h⟩
  | cons a as =>
    intro f e h he
    rw [VExpr.mkApp_cons] at h
    rcases VExpr.mkApp_self_or_app as (f.app a) with h' | ⟨g, b, h'⟩
    · exact absurd (h.symm.trans h') (he _ _)
    · exact absurd (h.symm.trans h') (he _ _)

/-- `List.Forall₂` at a symmetric relation is symmetric. -/
theorem _root_.List.Forall₂.symm' {α} {R : α → α → Prop} (hR : ∀ {a b}, R a b → R b a) :
    ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₂ l₁
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hR h) (List.Forall₂.symm' hR t)

/-- `List.Forall₂` is closed under append. -/
theorem _root_.List.Forall₂.append' {α β} {R : α → β → Prop} :
    ∀ {l₁ r₁ l₂ r₂ : _}, List.Forall₂ R l₁ r₁ → List.Forall₂ R l₂ r₂ →
      List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h2 => .cons h (List.Forall₂.append' t h2)

namespace VEnv

/-- `c` heads no definitional-equality rule of `env`.

For an environment built by declarations this holds of every inductive type former, every
constructor, and of `Quot` — the rules are δ-rules headed by a `def`'s name, ι-rules headed
by a recursor, and `quotDefEq` headed by `Quot.lift` (`Theory/Typing/PatternRules.lean`'s
`Pat`).  Deriving it from `VEnv.WF` is ledger item M2 and needs the `VEnv.Sig` invariant. -/
def RuleFreeHead (env : VEnv) (c : Lean.Name) : Prop :=
  ∀ df, env.defeqs df → VExpr.headConst? df.lhs ≠ some c

/-! ## `IsDefEqU.sort_inv` is now proved

`VEnv.IsDefEqU.sort_inv` used to be the first theorem of this file, `sorry`-backed in its
`trans` and `proofIrrel` cases.  It is now **proved**, further down (section `UniqAux`),
with the same name, namespace and statement, so every consumer sees it unchanged.

The proof does not close the `trans` case — it *avoids* it.  `IsDefEqU U Γ (.sort u)
(.sort v)` unfolds to one type inhabited by both sorts, because conversion here is
type-indexed, so `VEnv.SortUniq` applies to the endpoints directly (`sort_inv_of_sortUniq`,
`Theory/Typing/SortUniq.lean`) and the conversion derivation is never opened.  `SortUniq` in
turn rides as a passenger conjunct inside `IsDefEq.uniq`'s own stratified induction.  Net:
`sort_inv` is a consequence of `IsDefEqU.forallE_inv_stratified` and of nothing else that is
open.

**The `trans` analysis that used to live here is still correct about the induction on
`IsDefEqStrong`** — that induction really does need a sort-only confluence, and the argument
that no such confluence is independent of `NormalEq` is unchanged.  What it missed is that
the statement has a *non-inductive* proof.  It is preserved in `docs/handoff-injectivity.md`.

**Consequence for the rest of the file.**  Since `SortUniq` is proved rather than assumed,
the `proofIrrel` case of `forallE_inv`, `sort_forallE_inv`, `const_forallE_inv` and
`const_sort_inv` closes *without* adding a hypothesis to any of their statements.  That trade
was previously thought to need a human call (`docs/handoff-injectivity.md` §9.1); it does
not, because nothing is weakened.  The residual of every one of them is now the **`trans`**
case alone: *a term convertible with a Π (resp. with a rule-free constant application)
reduces to one*.  The sort-flavoured residual is gone from this file entirely.

**Superseded in one respect (see section `RigidShapeBridge`).**  Those five `trans` residuals
are no longer five: they are *one*, `VEnv.WF.rigidShapeUniq`, and all five of `forallE_inv`,
`sort_forallE_inv`, `const_app_inv`, `const_forallE_inv` and `const_sort_inv` now derive their
`trans` case from it.  The file's hole count for this family dropped 5 → 1 with no statement
changed.  The description above of *what* the residual says is still accurate; what was wrong
was calling it five obligations.
-/

/-- **NOT PROVED**, and — unlike `sort_inv` — *not* reducible to the conversion-derivation
content alone.  Attempting the same induction on `IsDefEqStrong` that `sort_inv` uses shows
this statement needs **two independent things**, only one of which `sort_inv` shares:

1. the `trans` content of `sort_inv` — normalisation (see its docstring), and
2. **universe uniqueness** — `Γ ⊢ e : .sort u → Γ ⊢ e : .sort v → u ≈ v`, packaged as
   `VEnv.SortUniq` in `Theory/Typing/SortUniq.lean`.

These are the same two primitives `sort_inv` needs, so the family really is one obligation
and not several.  What is different here is that (2) is needed by the *structural* cases,
not only by `proofIrrel`.

*The two bullets below are analysis of the induction, not a machine-checked impossibility;
the corresponding claim for `sort_inv`'s `proofIrrel` case is machine-witnessed, in
`HasTypeStrong.sort_type`.*  (2) is forced by the *shape* of the conclusion, not by any
particular proof strategy: each
conjunct pairs a conversion `A ≡ A'` (resp. `B ≡ B'`) *at a level* `u` with a
`HasTypeStratified` derivation of `A` (resp. `B`) *at that same level* `u` and *at the index
`n` inherited from the hypothesis `h2`*.  The conversion's level comes from the derivation
being inverted; the stratified derivation's level comes from `h2` via
`HasTypeStratified.forallE_inv'`; nothing upstream of this file aligns them.  Concretely,
even the two easiest cases fail:

* `forallEDF` — the structural case — hands back `Γ ⊢ A ≡ A' : .sort u` and
  `A::Γ ⊢ B ≡ B' : .sort v`, while `h2.forallE_inv'` hands back `Γ ⊢ A : .sort u₀ !! n-1`
  and `A::Γ ⊢ B : .sort v₀ !! n-1`.  Retyping either side at the other's level needs
  `u ≈ u₀` / `v ≈ v₀`.
* `symm` — goal 2 closes (its `B`-side components arrive already paired), but goal 1 needs
  `A`'s stratified derivation at index `n`, and the induction hypothesis supplies `A'`'s at
  index `n'`.

Bumping the index is free (`HasTypeStratified.mono`); aligning the *levels* is not.
`Theory/Typing/Lemmas.lean`'s `HasType.sort_inv` is only "the level is `WF U`", and there is
no universe-uniqueness lemma anywhere upstream: the one in the tree, `IsDefEq.uniq`
(`Theory/Typing/UniqueTyping.lean`), is this lemma's own consumer.  This is the same
"pinning" difficulty that `Experimental/Reflect/Capstone.lean:95–99` describes and that its
`sort_uniq_of_hasType` was built to supply — and that route is closed (see the module
docstring).

So `forallE_inv_stratified` is not provable by induction on the conversion derivation in
isolation.  Closing it needs either a joint induction with `IsDefEq.uniq`, or a route
(a model, or Carneiro's stratified Church–Rosser) that delivers universe uniqueness
independently.

Worth knowing before restating it: **both consumers discard the first conjunct's
`HasTypeStratified` component** — `IsDefEq.uniq` (`UniqueTyping.lean:43`) binds only the
second conjunct, and `forallE_inv` below takes only the `IsDefEq`.  Dropping it would
weaken the statement at no cost to anyone, but it does *not* unblock the proof: the second
conjunct needs exactly the same level alignment for `B`. -/
theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

section UniqAux
/-!
## `SortUniq` and `IsDefEqU.sort_inv`, from `forallE_inv_stratified` alone

This section sits between `forallE_inv_stratified` and the rest of the family on purpose.
It proves `VEnv.SortUniq` — universe uniqueness — from `forallE_inv_stratified` and nothing
else that is open, and everything after it may therefore *use* universe uniqueness without
adding a hypothesis to any public statement.  That is what closes the `proofIrrel` case of
`forallE_inv`, `sort_forallE_inv`, `const_forallE_inv` and `const_sort_inv` below.

    forallE_inv_stratified  ⟹  uniqAux  ⟹  SortUniq  ⟹  sort_inv
                                       ⟹  uniq  (Theory/Typing/UniqueTyping.lean)

### What the trick is

`IsDefEq.uniq`'s induction (`Theory/Typing/UniqueTyping.lean:13`) calls `IsDefEqU.sort_inv`
nine times, and **every one of those calls is applied to an output of its own induction
hypothesis, at a point where both types are syntactic sorts.**  So the level equivalence they
extract can be *carried by the invariant* instead of imported: `UniqAux` below is `uniq`'s
invariant plus the conjunct

    ∀ s₁ s₂, A = .sort s₁ → B = .sort s₂ → s₁ ≈ s₂

which is exactly `VEnv.SortUniq`, read off at `A = .sort u`, `B = .sort v`.

### Why the extra conjunct costs nothing

It is not proved case by case — it is derived *once*, uniformly, from components the
invariant already carries (`sortType_level`).  Given `HTS Γ A (.sort u) true (n-1)`,
`HTS Γ B (.sort v) true (n-1)` and `u ≈ v`, with `A = .sort s₁` and `B = .sort s₂`: apply the
invariant **at index `n-1`** to `.sort s₁` at its two types `.sort u` and `.sort (.succ s₁)`
(the second by `sort'`, at index `0`) to get `u ≈ .succ s₁`, symmetrically `v ≈ .succ s₂`,
and compose.  The recursion is the well-founded one on `n` that the original proof already
runs, and it strictly decreases.  At `n = 0` the only derivation available is `sort'`, so the
type is pinned outright (`HasTypeStratified.sort_zero_inv`) — that is the base case.

**Where the type index pays.**  `HasTypeStratified`'s `defeq` premise carries the type as
`.sort u` *syntactically*, so "both types are sorts" is a pattern on the invariant rather
than a fact about a conversion derivation.

**Why the same move does not reach `forallE_inv_stratified` itself.**  A sort's type is
determined by the term, so the sort conjunct is recoverable from the invariant's typing
components.  A Π's *codomain conversion* is not determined by any typing: `piInvStrat_of`
below shows the missing ingredient is exactly `SortUniq` applied to `B` at two levels, one of
which comes from an unstratified `IsDefEq` and therefore carries **no index bound**.  Inside
`uniqQ` only bounded instances of `SortUniq` are available, so the circle does not close.
See `docs/handoff-injectivity.md`.

### Provenance

`uniqQ` is `IsDefEq.uniq`'s proof transcribed, with exactly two kinds of change: the nine
`IsDefEqU.sort_inv` calls become `hc _ _ rfl rfl` from the strengthened induction hypothesis,
and the binder order is adjusted so the same `induction … generalizing` shape elaborates
standalone.  `UniqueTyping.lean`'s `IsDefEq.uniq` is unedited; it now calls the **proved**
`IsDefEqU.sort_inv` below.
-/

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

/-- The statement of `IsDefEqU.forallE_inv_stratified` (`Theory/Typing/Injectivity.lean`),
packaged as a `Prop` so that the results below can be stated *relative* to it instead of
importing its `sorry`. -/
def PiInvStrat (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' V V' : VExpr} {n n' : Nat},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    env.HasTypeStratified U Γ (.forallE A B) V true n →
    env.HasTypeStratified U Γ (.forallE A' B') V' true n' →
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n'

/-- The statement of `IsDefEqU.forallE_inv` (`Theory/Typing/Injectivity.lean`), packaged the
same way.  This is the **unstratified** Π-injectivity: no index, no level alignment. -/
def PiInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u)

/-- **The only instance of `PiInvStrat` that anything in this tree consumes.**

`uniqQ` calls `hstrat` exactly once, in its `app` case, and that call
* discards the whole first (domain) conjunct, and
* passes the *same* index `n` for both stratified hypotheses.

So the obligation the entire `Verify/` cone rests on is this strictly weaker statement: no
domain conjunct, one index instead of two.  `PiInvStrat.app` is the (one-line) implication;
the converse is **not** claimed and is not needed anywhere.

Measured on this commit: in the import closure of `Verify/Bridge.lean`,
`IsDefEqU.forallE_inv_stratified` has exactly two direct consumers, `IsDefEq.uniq` and
`piInvStrat_axiom`; the second is only the packaging, and `uniq`'s single appeal is the call
below. -/
def PiInvStratApp (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' V V' : VExpr} {n : Nat},
    OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    env.HasTypeStratified U Γ (.forallE A B) V true n →
    env.HasTypeStratified U Γ (.forallE A' B') V' true n →
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n

/-- The narrowing, as a one-line implication.  Everything below consumes only the right-hand
side. -/
theorem PiInvStrat.app (h : PiInvStrat env U) : PiInvStratApp env U := by
  intro Γ A B A' B' V V' n hΓ h1 h2 h3
  exact (h hΓ h1 h2 h3).2

/-- The strengthened invariant of `IsDefEq.uniq`: the original conclusion, plus the level
equivalence in the case where both types are syntactic sorts. -/
def UniqAux (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {b : Bool} {n₁ n₂ : Nat},
    OnCtx Γ (env.IsType U) → n₁ ≤ n → n₂ ≤ n →
    env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
    ∃ u, env.IsDefEq U Γ A B (.sort u) ∧ ∃ v, u ≈ v ∧
      env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
      env.HasTypeStratified U Γ B (.sort v) true (n-1) ∧
      ∀ s₁ s₂, A = .sort s₁ → B = .sort s₂ → s₁ ≈ s₂

/-- At index `0` the only derivation of a sort's type is `sort'`, so the type is pinned. -/
theorem HasTypeStratified.sort_zero_inv {Γ : List VExpr} {s u : VLevel}
    (h : env.HasTypeStratified U Γ (.sort s) (.sort u) true 0) : u ≈ .succ s := by
  cases h with | base h => cases h with | sort' _ _ h3 => exact (VLevel.succ_congr h3).symm

/-- The level of a sort's type, read off the strengthened invariant one index down. -/
theorem sortType_level (henv : VEnv.WF env) {Γ : List VExpr} {s u : VLevel} {n : Nat}
    (IH : ∀ m, m < n → UniqAux env U m) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.HasTypeStratified U Γ (.sort s) (.sort u) true (n-1)) : u ≈ .succ s := by
  match n with
  | 0 => exact h.sort_zero_inv
  | m+1 =>
    have hs : s.WF U := h.hasType.sort_inv henv.ordered
    have ⟨_, _, _, _, _, _, hc⟩ := IH m (Nat.lt_succ_self _) hΓ (Nat.le_refl m) (Nat.zero_le m)
      h (.base (.sort' hs hs rfl))
    exact hc _ _ rfl rfl

/-- The body of `IsDefEq.uniq`'s induction, with each of its nine appeals to
`IsDefEqU.sort_inv` replaced by the strengthened invariant at a smaller index. -/
theorem uniqQ (henv : VEnv.WF env) (hstrat : PiInvStratApp env U) :
    ∀ {n : Nat}, (∀ m, m < n → UniqAux env U m) →
    ∀ {n₁ n₂ : Nat} {Γ : List VExpr} {e A B : VExpr} {b : Bool},
    OnCtx Γ (env.IsType U) → n₁ ≤ n → n₂ ≤ n →
    env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
    ∃ u, Γ ⊢ A ≡ B : .sort u ∧ ∃ v, u ≈ v ∧
      env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
      env.HasTypeStratified U Γ B (.sort v) true (n-1) := by
  intro n IH n₁ n₂ Γ e A B b hΓ le₁ le₂ H1
  induction H1 generalizing B n₂ n with
  | bvar a1 a2 =>
    intro (.bvar b1 b2); cases a1.uniq b1
    exact ⟨_, b2.hasType, _, rfl, b2.mono (by omega), b2.mono (by omega)⟩
  | sort' a1 a2 a3 =>
    intro (.sort' b1 b2 b3)
    have := VLevel.succ_congr (b3.symm.trans a3)
    exact ⟨_, .symm <| .sortDF b2 a2 this, _, VLevel.succ_congr this,
      .base <| .sort' a2 b2 this.symm, .base <| .sort' b2 a2 this⟩
  | const a1 a2 a3 a4 =>
    intro (.const b1 b2 b3 b4); cases a1.symm.trans b1
    replace le₁ := Nat.sub_le_sub_right le₁ 1
    exact ⟨_, a4.hasType, _, rfl, a4.mono le₁, a4.mono le₁⟩
  | app _ a2 a3 a4 _ a6 a7 _ _ ih3 =>
    intro (.app _ _ b3 b4 b5 _ b7)
    have ⟨_, c1, _, _, c3, c4⟩ := ih3 (n := n) IH hΓ (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b5
    have ⟨_, d3, d4, d5⟩ := hstrat hΓ ⟨_, c1⟩ c3 c4
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    refine have hΓ₁ := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, _, _, _, _, _, hc1⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ₁ le₁ (Nat.le_refl _) a4 d4; ?_
    have e3 := hc1 _ _ rfl rfl
    have e4 := have ⟨_, h⟩ := d4.hasType.isType henv hΓ₁; h.sort_inv henv
    refine have hΓ₂ := ⟨hΓ, _, b3.hasType⟩
      have ⟨_, _, _, _, _, _, hc2⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ₂ le₂ (Nat.le_refl _) b4 d5; ?_
    have e5 := hc2 _ _ rfl rfl
    exact ⟨_, .defeqDF (.sortDF e4 a2 e3.symm) (d3.instN henv a6.hasType .zero), _,
      e3.trans e5.symm, a7.mono le₁, b7.mono le₂⟩
  | lam a1 a2 _ a4 _ _ ih3 =>
    intro (.lam b1 b2 b3 b4)
    have ⟨_, c1, _, c2, c3, c4⟩ := ih3 (n := n) IH ⟨hΓ, _, a1.hasType⟩
      (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, _, _, _, hc1⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have e1 := hc1 _ _ rfl rfl
    refine have hΓ' := ⟨hΓ, _, a1.hasType⟩
      have ⟨_, h, _, _, _, _, hc2⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ' le₁ (Nat.le_refl _) a2 c3; ?_
    have f1 := h.sort_inv_l henv; have f2 := h.sort_inv_r henv
    have e2 := hc2 _ _ rfl rfl
    have ⟨_, _, _, _, _, _, hc3⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₂ (Nat.le_refl _) b2 c4
    have e3 := hc3 _ _ rfl rfl
    exact ⟨_, .forallEDF a1.hasType (.defeqDF (.symm <| .sortDF f1 f2 e2) c1),
      _, VLevel.imax_congr e1 (e2.trans <| c2.trans e3.symm), a4.mono le₁, b4.mono le₂⟩
  | forallE a1 a2 a3 a4 =>
    intro (.forallE b1 b2 b3 b4)
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, _, _, _, hc1⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a3 b3
    have e1 := hc1 _ _ rfl rfl
    refine have hΓ' := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, _, _, _, _, _, hc2⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₁ le₂ a4 b4; ?_
    have e2 := hc2 _ _ rfl rfl
    have := VLevel.imax_congr e1 e2
    exact ⟨_, .sortDF ⟨a1, a2⟩ ⟨b1, b2⟩ this, _, rfl,
      .base <| .sort' ⟨a1, a2⟩ ⟨a1, a2⟩ rfl, .base <| .sort' ⟨b1, b2⟩ ⟨a1, a2⟩ this.symm⟩
  | @base Γ e A n₁ a1 ih =>
    intro H2
    replace ih {n'} (le : n' ≤ n) {n₂' : Nat} {B' : VExpr} :=
      ih (n := n') (fun y h1 => IH y (Nat.lt_of_lt_of_le h1 le)) (n₂ := n₂') (B := B') hΓ
    generalize eq : true = b at H2
    induction H2 with cases eq
    | @base _ _  _ n' b1 => exact ih (Nat.le_refl _) le₁ le₂ b1
    | @defeq Γ B' B u n' _ b1 b2 b3 b4 b5 _ _ ih' =>
      have ⟨u₁, c1, u₂, c2, c3, c4⟩ := ih' a1 hΓ (Nat.le_of_succ_le le₂) ih rfl
      let n+1 := n
      replace le₂ := Nat.le_of_succ_le_succ le₂
      have ⟨_, _, _, _, _, _, hc⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ le₂ (Nat.le_refl _) b3 c4
      have e1 := hc _ _ rfl rfl
      have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
      have eq : u₁ ≈ u := c2.trans e1.symm
      exact ⟨_, c1.trans (.defeqDF (.symm <| .sortDF e2 b1 eq) b2), _, eq, c3, b4.mono le₂⟩
  | @defeq Γ A' A u n' _ a1 a2 a3 a4 a5 ih1 ih2 ih' =>
    intro H2
    have ⟨_, c1, u₂, c2, c3, c4⟩ := ih' IH hΓ (Nat.le_of_succ_le le₁) le₂ H2
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    have ⟨_, _, _, _, _, _, hc⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ (Nat.le_refl _) a3 c3
    have e1 := hc _ _ rfl rfl
    have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
    have eq : u ≈ u₂ := e1.trans c2
    exact ⟨_, a2.symm.trans (.defeqDF (.symm <| .sortDF a1 e2 e1) c1), _, eq, a4.mono le₁, c4⟩

/-- The strengthened invariant, at every index. -/
theorem uniqAux (henv : VEnv.WF env) (hstrat : PiInvStratApp env U) :
    ∀ n, UniqAux env U n := by
  intro n
  induction n using WellFounded.induction Nat.lt_wfRel.2 with | _ n IH
  intro Γ e A B b n₁ n₂ hΓ le₁ le₂ H1 H2
  obtain ⟨u, h, v, hv, c3, c4⟩ := uniqQ henv hstrat IH hΓ le₁ le₂ H1 H2
  refine ⟨u, h, v, hv, c3, c4, ?_⟩
  rintro s₁ s₂ rfl rfl
  have h1 := sortType_level henv IH hΓ c3
  have h2 := sortType_level henv IH hΓ c4
  exact VLevel.succ_congr_iff.1 (h1.symm.trans (hv.trans h2))

/-! ## Consequences -/

/-! ## `IsDefEqU.sort_inv`, proved

Formerly `Theory/Typing/Injectivity.lean`'s first theorem, where it was `sorry`-backed in its
`trans` and `proofIrrel` cases.  Statement byte-identical; the hypothesis list is unchanged.
-/

/-- **Universe uniqueness, from Π-injectivity alone.**  The only `sorry`-backed input is
`IsDefEqU.forallE_inv_stratified`. -/
theorem sortUniq_of_piInvStratApp (henv : VEnv.WF env) (hstrat : PiInvStratApp env U) :
    env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  obtain ⟨n₁, H1⟩ := (h1.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨n₂, H2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨_, _, _, _, _, _, hc⟩ :=
    uniqAux henv hstrat _ hΓ (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) H1 H2
  exact hc _ _ rfl rfl

/-- `IsDefEqU.forallE_inv_stratified` itself, as an inhabitant of `PiInvStrat`. -/
theorem piInvStrat_axiom (henv : VEnv.WF env) : PiInvStrat env U :=
  fun hΓ h1 h2 h3 => IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3

/-- …and of the narrowed form, which is the one every consumer below actually uses. -/
theorem piInvStratApp_axiom (henv : VEnv.WF env) : PiInvStratApp env U :=
  PiInvStrat.app (piInvStrat_axiom henv)

/-- Kept for readers who want the wide statement; it is *not* on any consumer's path. -/
theorem sortUniq_of_piInvStrat (henv : VEnv.WF env) (hstrat : PiInvStrat env U) :
    env.SortUniq U := sortUniq_of_piInvStratApp henv (PiInvStrat.app hstrat)

theorem WF.sortUniq' (henv : VEnv.WF env) : env.SortUniq U :=
  sortUniq_of_piInvStratApp henv (piInvStratApp_axiom henv)

/-- **Sort injectivity.**  `.sort u ≡ .sort v` forces `u ≈ v`.

Proved, not assumed: `WF.sortUniq'` supplies universe uniqueness and
`sort_inv_of_sortUniq` (`Theory/Typing/SortUniqDown.lean`) turns it into this, without ever
opening the conversion derivation — no `trans` case, no normalisation.  The only
`sorry`-backed input in the whole cone is `IsDefEqU.forallE_inv_stratified`. -/
theorem IsDefEqU.sort_inv {Γ : List VExpr} {u v : VLevel} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  sort_inv_of_sortUniq (WF.sortUniq' henv) henv.ordered hΓ h1

/-! ## The other direction: `PiInvStrat` from `PiInv` **plus** `SortUniq`

`forallE_inv_stratified`'s docstring says its obstruction is *level alignment*: the level the
conversion is stated at versus the level `HasTypeStratified.forallE_inv'` hands back.  The
theorem below machine-checks that reading — the alignment is `SortUniq`, and given `SortUniq`
the stratified statement is a two-step consequence of the unstratified one.

Read together with `sortUniq_of_piInvStrat`, this says: **relative to `PiInv`,
`PiInvStrat` and `SortUniq` are equivalent.**  The corner is a *circle*, not a chain — see
`docs/handoff-injectivity.md` for why the circle cannot be cut by moving `PiInv` into
`uniqAux`'s `app` case. -/
theorem piInvStrat_of (henv : VEnv.WF env) (hsu : env.SortUniq U) (hpi : PiInv env U) :
    PiInvStrat env U := by
  intro Γ A B A' B' V V' n n' hΓ h1 h2 h3
  obtain ⟨hn, uA, vB, hA, hB⟩ := h2.forallE_inv'
  obtain ⟨hn', uA', vB', hA', hB'⟩ := h3.forallE_inv'
  obtain ⟨⟨w1, hAA'⟩, w2, hBB'⟩ := hpi hΓ h1
  have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA.hasType⟩
  have hΓA' : OnCtx (A'::Γ) (env.IsType U) := ⟨hΓ, _, hA'.hasType⟩
  have huA : uA.WF U := have ⟨_, h⟩ := hA.hasType.isType henv hΓ; h.sort_inv henv
  have hw1 : w1.WF U := have ⟨_, h⟩ := hAA'.hasType.1.isType henv hΓ; h.sort_inv henv
  have hvB : vB.WF U := have ⟨_, h⟩ := hB.hasType.isType henv hΓA; h.sort_inv henv
  have hvB' : vB'.WF U := have ⟨_, h⟩ := hB'.hasType.isType henv hΓA'; h.sort_inv henv
  have hw2 : w2.WF U := have ⟨_, h⟩ := hBB'.hasType.1.isType henv hΓA; h.sort_inv henv
  -- (1) the domain: same context, so `SortUniq` applies directly.
  have e1 : uA ≈ w1 := hsu hΓ huA hw1 hA.hasType hAA'.hasType.1
  refine ⟨⟨uA, .defeqDF (.sortDF hw1 huA e1.symm) hAA', hA.mono (by omega)⟩, w2, hBB', ?_, ?_⟩
  -- (2a) the codomain on the left: `SortUniq` in `A::Γ`.
  · have e2 : vB ≈ w2 := hsu hΓA hvB hw2 hB.hasType hBB'.hasType.1
    have : n - 1 + 1 = n := by omega
    exact this ▸ HasTypeStratified.defeq (u := .succ vB) hvB (.sortDF hvB hw2 e2)
      (.base (.sort' hvB hvB rfl)) (.base (.sort' hw2 hvB e2.symm)) hB
  -- (2b) the codomain on the right: the conversion lives in `A::Γ`, so it must first be
  -- moved to `A'::Γ` along the domain conversion (`HasType.defeq_l`) before `SortUniq`
  -- can be applied there.
  · have e3 : vB' ≈ w2 :=
      hsu hΓA' hvB' hw2 hB'.hasType (hBB'.hasType.2.defeq_l henv.ordered hAA')
    have : n' - 1 + 1 = n' := by omega
    exact this ▸ HasTypeStratified.defeq (u := .succ vB') hvB' (.sortDF hvB' hw2 e3)
      (.base (.sort' hvB' hvB' rfl)) (.base (.sort' hw2 hvB' e3.symm)) hB'

/-- **The narrowed circle, both directions.**  Narrowing `PiInvStrat` to the single instance
`uniqQ` consumes does *not* cut the circle: `PiInvStratApp` is still equivalent to `SortUniq`
relative to `PiInv`.  What it does is make the residual smaller — the domain conjunct and the
second index are dead weight, and the statement that has to be proved is this one. -/
theorem piInvStratApp_of (henv : VEnv.WF env) (hsu : env.SortUniq U) (hpi : PiInv env U) :
    PiInvStratApp env U := PiInvStrat.app (piInvStrat_of henv hsu hpi)

/-- The circle, packaged.  `←` is `uniqAux`; `→` is `piInvStrat_of` composed with the
narrowing.  Both sides `sorry`-free; the `sorry` lives only in the *inhabitant*
`piInvStratApp_axiom`. -/
theorem sortUniq_iff_piInvStratApp (henv : VEnv.WF env) (hpi : PiInv env U) :
    env.SortUniq U ↔ PiInvStratApp env U :=
  ⟨fun hsu => piInvStratApp_of henv hsu hpi, sortUniq_of_piInvStratApp henv⟩

/-- **Non-vacuity of the narrowing.**  Forcing both stratified hypotheses to the *same* index
could have emptied the statement; it does not.  The witness is non-degenerate in the two ways
that matter: the two domains are **syntactically different** (so the conclusion is not an
instance of reflexivity), and the two codomains therefore live in **different contexts**, which
is the transport the second component of the conclusion has to perform.  Levels only:
`imax 0 0 ≈ 0` without the two being equal.  Holds over **every** environment, with no
`VEnv.WF` and no constant; `sorryAx`-free. -/
theorem piInvStratApp_fires :
    OnCtx ([] : List VExpr) (env.IsType 0) ∧
    (VExpr.sort (.imax .zero .zero) : VExpr) ≠ .sort .zero ∧
    env.IsDefEqU 0 [] (.forallE (.sort (.imax .zero .zero)) (.sort .zero))
      (.forallE (.sort .zero) (.sort .zero)) ∧
    env.HasTypeStratified 0 [] (.forallE (.sort (.imax .zero .zero)) (.sort .zero))
      (.sort (.imax (.succ (.imax .zero .zero)) (.succ .zero))) true 1 ∧
    env.HasTypeStratified 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) true 1 := by
  have hz : (VLevel.zero).WF 0 := trivial
  have hi : (VLevel.imax .zero .zero).WF 0 := ⟨trivial, trivial⟩
  have heq : (VLevel.imax .zero .zero) ≈ VLevel.zero := VLevel.imax_zero
  have hp1 : env.HasTypeStratified 0 [] (.forallE (.sort (.imax .zero .zero)) (.sort .zero))
      (.sort (.imax (.succ (.imax .zero .zero)) (.succ .zero))) true 1 :=
    .base (.forallE hi hz (.base (.sort' hi hi rfl)) (.base (.sort' hz hz rfl)))
  have hp2 : env.HasTypeStratified 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) true 1 :=
    .base (.forallE hz hz (.base (.sort' hz hz rfl)) (.base (.sort' hz hz rfl)))
  have hconv : env.IsDefEq 0 [] (.forallE (.sort (.imax .zero .zero)) (.sort .zero))
      (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ (.imax .zero .zero)) (.succ .zero))) :=
    IsDefEq.forallEDF (.sortDF hi hz heq) (.sortDF hz hz rfl)
  exact ⟨trivial, by simp, ⟨_, hconv⟩, hp1, hp2⟩


/-! ## `IsProof`, and the side condition that actually propagates

`const_app_inv` (below) needs to exclude `IsDefEqStrong.proofIrrel`, which identifies *any*
two inhabitants of a proposition and so refutes injectivity outright
(`Theory/Typing/ConstInvWitness.lean`'s `w2`).  Its statement does that with an `IsType`
side condition on the application — and **`IsType` does not propagate into the induction**:
at `appDF` the sub-spine has a Π type, not a sort, so the invariant cannot carry it.  That
is why the theorem was left an opaque `sorry` by a previous stream.

The fix is to carry the *negation of proof-ness* instead.  `¬ IsProof` is exactly what the
`proofIrrel` case needs, it is implied by `IsType` (`IsType.not_isProof`), and — unlike
`IsType` — it **does** propagate: if the head of an application is a proof then so is the
application (`IsProof.app'`), because a Π-type that is a `Prop` has a `Prop` codomain.  So
the contrapositive threads down the spine and the induction runs.

The three lemmas below need unique typing, which lives *downstream* of this file
(`IsDefEq.uniq`, `Theory/Typing/UniqueTyping.lean`).  They do not import it: `uniqAux` above
is that proof's own invariant and `piInvStrat_axiom` discharges its hypothesis, so the same
conclusion is available here under the primed name `WF.uniq'`.  Nothing new is assumed —
`WF.uniq'` has exactly `IsDefEq.uniq`'s cone, namely `forallE_inv_stratified`. -/

/-- `IsDefEq.uniq` (`Theory/Typing/UniqueTyping.lean`), re-derived at this height so that
this file can use unique typing without importing its own consumer. -/
theorem WF.uniq' {Γ : List VExpr} {e₁ e₂ e₃ A B : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    ∃ u, env.IsDefEq U Γ A B (.sort u) := by
  obtain ⟨n₁, H1⟩ := (h1.strong henv.ordered hΓ).hasType'.2.stratify
  obtain ⟨n₂, H2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨u, h, -⟩ := uniqAux henv (piInvStratApp_axiom henv) _ hΓ
    (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) H1 H2
  exact ⟨u, h⟩

/-- Retyping along a conversion between *terms*: `HasType.defeqU_l` at this height. -/
theorem HasType.defeqU_l' {Γ : List VExpr} {e₁ e₂ A : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) : env.HasType U Γ e₂ A := by
  obtain ⟨V, h1⟩ := h1
  obtain ⟨u, hu⟩ := WF.uniq' henv hΓ h2 h1
  exact (IsDefEq.defeqDF hu.symm h1).hasType.2

/-- **`e` is a proof**: it inhabits a proposition.  This is the honest form of
`const_app_inv`'s second side condition — see the section docstring. -/
def IsProof (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ p, env.HasType U Γ p (.sort .zero) ∧ env.HasType U Γ e p

/-- Proof-ness transports along a conversion. -/
theorem IsProof.defeqU {Γ : List VExpr} {e₁ e₂ : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEqU U Γ e₁ e₂)
    (hp : env.IsProof U Γ e₁) : env.IsProof U Γ e₂ :=
  let ⟨p, hp0, hep⟩ := hp; ⟨p, hp0, HasType.defeqU_l' henv hΓ h hep⟩

/-- **A type is not a proof.**  The companion of `VEnv.sort_not_proof` and
`VEnv.forallE_not_proof` (`Theory/Typing/SortUniq.lean`, `Theory/Typing/NotProof.lean`) at
one more level of generality: those two are about a *particular shape* being a type, this is
about being a type at all.  Same argument, same input — universe uniqueness, which
`WF.sortUniq'` supplies, so this costs no statement a hypothesis. -/
theorem IsType.not_isProof {Γ : List VExpr} {e : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsType U Γ e) : ¬ env.IsProof U Γ e := by
  rintro ⟨p, hp, hep⟩
  obtain ⟨u, hu⟩ := h
  obtain ⟨w, hw⟩ := WF.uniq' henv hΓ hep hu
  have h1 : env.HasType U Γ (.sort u) (.sort .zero) := HasType.defeqU_l' henv hΓ ⟨_, hw⟩ hp
  have hu' : u.WF U := h1.sort_inv henv.ordered
  have h2 : VLevel.zero ≈ VLevel.succ u :=
    WF.sortUniq' henv hΓ trivial hu' h1 (HasType.sort hu')
  exact absurd (congrFun h2 []) (by simp [VLevel.eval])

/-- **Proof-ness propagates up an application spine.**  If the function of a well-typed
application is a proof, so is the application.

*Why.*  A function that is a proof has a Π type that is a `Prop`, i.e. `imax u v ≈ 0`, and
`imax` is zero exactly when its **second** argument is (`VLevel.imax_eq_zero`).  So the
codomain is a `Prop` and the application inhabits it.

This is the whole reason the `const_app_inv` induction can run: contrapositively, `¬IsProof`
of an application gives `¬IsProof` of its function, which is precisely the direction the
`appDF` case travels.  `IsType` has no such closure property — the sub-spine of a spine that
is a type is a Π, not a type. -/
theorem IsProof.app' {Γ : List VExpr} {A B f a : VExpr} {u v : VLevel} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U (A::Γ) B (.sort v))
    (hf : env.HasType U Γ f (.forallE A B)) (ha : env.HasType U Γ a A)
    (h : env.IsProof U Γ f) : env.IsProof U Γ (.app f a) := by
  obtain ⟨p, hp, hfp⟩ := h
  obtain ⟨w, hw⟩ := WF.uniq' henv hΓ hfp hf
  have h1 : env.HasType U Γ (.forallE A B) (.sort .zero) :=
    HasType.defeqU_l' henv hΓ ⟨_, hw⟩ hp
  have hu : u.WF U := have ⟨_, h⟩ := hA.isType henv.ordered hΓ; h.sort_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
  have hv : v.WF U := have ⟨_, h⟩ := hB.isType henv.ordered hΓA; h.sort_inv henv.ordered
  have h2 : env.HasType U Γ (.forallE A B) (.sort (.imax u v)) := hA.forallE hB
  have e1 : VLevel.imax u v ≈ VLevel.zero :=
    WF.sortUniq' henv hΓ ⟨hu, hv⟩ trivial h2 h1
  have hB0 : env.HasType U (A::Γ) B (.sort .zero) :=
    IsDefEq.defeqDF (.sortDF hv trivial (VLevel.imax_eq_zero.1 e1)) hB
  exact ⟨B.inst a, hB0.instN henv.ordered .zero ha, hf.app ha⟩

/-! ### Non-vacuity of the `IsProof` machinery

`¬ IsProof` is a *hypothesis* of the `const_app_inv` induction, so if nothing could ever
satisfy `IsProof` the `proofIrrel` case would be closed for the uninteresting reason and the
`IsType` side condition would be pointless.  The witnesses below deny that.  Both live
entirely in the context, so they hold in **every** environment and at every universe count —
no constant, no rule, no `VEnv.WF`.

The second one is the load-bearing one: it exhibits a term that is **a proof and has a Π
type**.  That is precisely why `IsType` cannot be the invariant — the sub-spine of an
application need not be a type even when the application is — and why the invariant has to be
the thing that *is* closed downwards. -/

/-- **`IsProof` fires.**  In the context `[h : P, P : Prop]`, `h` is a proof. -/
theorem IsProof_fires {env : VEnv} {U : Nat} :
    env.IsProof U [.bvar 0, .sort .zero] (.bvar 0) ∧
    OnCtx [.bvar 0, .sort .zero] (env.IsType U) :=
  ⟨⟨.bvar 1, .bvar (.succ .zero), .bvar .zero⟩,
   ⟨⟨trivial, _, .sort trivial⟩, _, .bvar .zero⟩⟩

/-- **A proof can be a function.**  `.bvar 0` below inhabits `Π (x : Prop), P`, which is
itself a `Prop`, so it is a proof *and* has a Π type.

This is the counterexample to propagating `IsType` down a spine, and the reason
`const_app_inv`'s invariant is `¬ IsProof` instead. -/
theorem IsProof.forallE_fires {env : VEnv} {U : Nat} :
    env.HasType U [.forallE (.sort .zero) (.bvar 1), .sort .zero] (.bvar 0)
      (.forallE (.sort .zero) (.bvar 2)) ∧
    env.IsProof U [.forallE (.sort .zero) (.bvar 1), .sort .zero] (.bvar 0) := by
  have hP : env.HasType U [VExpr.sort .zero, VExpr.forallE (.sort .zero) (.bvar 1),
      VExpr.sort .zero] (.bvar 2) (.sort .zero) := .bvar (.succ (.succ .zero))
  have hpi : env.HasType U [VExpr.forallE (.sort .zero) (.bvar 1), VExpr.sort .zero]
      (.forallE (.sort .zero) (.bvar 2)) (.sort .zero) :=
    .defeqDF (.sortDF (l := VLevel.imax (.succ .zero) .zero) ⟨trivial, trivial⟩ trivial
      VLevel.imax_zero) (HasType.forallE (.sort trivial) hP)
  exact ⟨.bvar .zero, _, hpi, .bvar .zero⟩

/-- **`IsProof.app'` fires**, at that witness: the application of a proof-valued function is
a proof.  Stated as a use of the lemma rather than a restatement of it, so what is checked is
that its five hypotheses are jointly satisfiable. -/
theorem IsProof.app'_fires {env : VEnv} (henv : env.WF) {U : Nat} :
    env.IsProof U [.forallE (.sort .zero) (.bvar 1), .sort .zero]
      (.app (.bvar 0) (.bvar 1)) := by
  have hΓ : OnCtx [VExpr.forallE (.sort .zero) (.bvar 1), VExpr.sort .zero] (env.IsType U) :=
    ⟨⟨trivial, _, .sort trivial⟩, _,
      .defeqDF (.sortDF (l := VLevel.imax (.succ .zero) .zero) (l' := VLevel.zero)
          ⟨trivial, trivial⟩ trivial VLevel.imax_zero)
        (HasType.forallE (.sort trivial) (.bvar (.succ .zero)))⟩
  exact IsProof.app' henv hΓ (u := .succ .zero) (v := .zero) (.sort trivial)
    (.bvar (.succ (.succ .zero))) IsProof.forallE_fires.1 (.bvar (.succ .zero))
    IsProof.forallE_fires.2

end UniqAux

/-! ## The `trans` bridge: one statement for five inversions

The five theorems below — `forallE_inv`, `sort_forallE_inv`, `const_app_inv`,
`const_forallE_inv`, `const_sort_inv` — each run the same induction on `IsDefEqStrong` and
each leave the same case open: `trans`, where the middle term is arbitrary.  **The five
residuals are one statement**, and it is stated here once, as `VEnv.RigidShapeUniq`, so that
whatever eventually closes it closes all five at once.

### Why the residual is the statement, not a fragment of it

`trans` is not a special case that a normalisation lemma chips away at: **it is the theorem
again**.  Given `Γ ⊢ e₁ ≡ m : T` and `Γ ⊢ m ≡ e₂ : T` with `e₁`, `e₂` rigid, `IsDefEq.trans`
composes them into `Γ ⊢ e₁ ≡ e₂ : T`, which is exactly the hypothesis of the theorem being
proved.  So each theorem's induction reduces it to itself, and the induction hypotheses
`ih1`/`ih2` are unusable: they fire only when the *middle* term is syntactically rigid, which
is what nothing knows.  This is worth saying plainly because the previous comments at those
five sites ("nine of the eleven cases close", "the only residual") invite the reading that a
small extra lemma finishes the job.  It does not: the ten closing cases are *shape*
bookkeeping, and the eleventh carries all of the content.

`RigidShapeUniq` is therefore stated as the *whole* family, hoisted, with the middle term as
its subject — `e` below **is** the arbitrary middle term.  Two things make that hoisting
honest rather than cosmetic, and both are machine-checked:

* `rigidShapeUniq_of_family` derives it from the five conclusions, so it is **no stronger
  than the family**: if the five are true, it is true.  (It is not vacuous for the same
  reason — nothing here is a hypothesis of the five statements, whose text is unchanged.)
* the five proofs below derive the family from it, so it is no weaker.

### What will discharge it, and what will not

**Confluence, in the form of `IsDefEq.church_rosser`** (`Theory/Typing/ChurchRosser.lean`,
end of file): `Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≫≪ e₂`, i.e. common reducts related by `NormalEq`.
From it the bridge is a three-step argument: `ParRedS` out of a sort / a Π / a rule-free
constant spine preserves that shape; `NormalEq` between two such shapes is `refl`, `sortDF`,
`constDF`, `forallEDF` or `proofIrrel` (`etaL`/`etaR` need a `.lam` endpoint, `proofIrrel`
needs both endpoints to be proofs and is excluded by `¬ IsProof e`); and those five
constructors give exactly `Compat`.

**Not `NormalEq.descend`.**  Three corrections to the folklore that says otherwise:

1. *Subject matter.*  `descend`'s conclusion is `DescentOut Γ q g g' n1 n2` — a `ParRedS`
   reduction of `g` to a term matching a **`Pattern`**, with `≈`-related level lists and
   `NormalEq`-related matched arguments, or the proof escape.  It says nothing about Π-types
   or sorts.  It is a lemma *inside* the confluence development (it is what lets
   `NormalEq.parRed`'s `appDF` × `extra` case fire a rule on the left), two levels below the
   theorem that actually delivers this bridge.
2. *Direction of the import graph.*  `ChurchRosser.lean` imports `UniqueTyping.lean`, which
   imports this file, so **nothing in `ChurchRosser` is nameable here** — not `NormalEq`, not
   `ParRedS`, not `DescentOut`, not `Pattern`.  A bridge phrased in `descend`'s vocabulary
   could not be written in this file at all, let alone used by it.  The dependency is real
   and not merely an import artefact: `descend`'s own `appDF` case calls
   `IsDefEqU.forallE_inv` (`ChurchRosser.lean:1766`).  So "close `descend`, then close these
   five" is circular as the tree stands; breaking the circle means re-basing the parts of
   `ChurchRosser` that consume this family, which is a separate job.
3. *`descend` is false as stated.*  `Theory/Typing/DescendRefute.lean` exhibits machine-
   checked witnesses against three of its five open goals (`not_descendStatement`,
   `not_descendStatement_etaArg`, `not_descendStatement_etaFun`), so its statement must
   change before it can be closed.  Matching a bridge to that conclusion would be matching it
   to a refuted one.

So this bridge is deliberately phrased in the vocabulary this file *has*: conversion,
typing, `IsProof`, `RuleFreeHead`.  The `¬ IsProof` premise, not `IsType`, is what makes it
usable inside `const_app_inv`'s induction, where a sub-spine has a Π type and is not a type
(`IsProof.forallE_fires` above is that witness).
-/

section RigidShapeBridge
variable {env : VEnv} {U : Nat}

/-- One of the three **rigid shapes** whose conversion class this file reads back: a sort, a
Π, or an application spine headed by a constant that heads no rule.  Everything else — a
`.lam`, a `.bvar` spine, a spine headed by a δ- or ι-rule's constant — is deliberately absent:
those are not rigid, and no statement here claims anything about them. -/
inductive RigidShape where
  | sort (u : VLevel)
  | pi (A B : VExpr)
  | app (c : Lean.Name) (ls : List VLevel) (as : List VExpr)

/-- The term a shape denotes. -/
def RigidShape.toExpr : RigidShape → VExpr
  | .sort u => .sort u
  | .pi A B => .forallE A B
  | .app c ls as => (VExpr.const c ls).mkApp as

/-- The side condition a shape carries.  Only the application spine has one, and it is the
`RuleFreeHead` the const-family already takes: without it a δ-rule reduces the spine to
anything at all. -/
def RigidShape.RuleFree (env : VEnv) : RigidShape → Prop
  | .sort _ => True
  | .pi _ _ => True
  | .app c _ _ => env.RuleFreeHead c

/-- **What two shapes in one conversion class have in common.**  The diagonal entries are the
three injectivity facts; the six off-diagonal ones are `False`, i.e. disjointness.

Two deliberate weaknesses, both to keep this exactly as strong as the family it packages and
no stronger:

* the `app`/`app` entry is guarded by `c = c'`, so nothing is claimed about *distinct*
  rule-free heads — the no-confusion fact the module docstring says no consumer has asked for.
* the `pi`/`pi` entry carries the codomain conversion in **both** contexts, because
  `forallE_inv`'s induction carries it in both (that is how its `symm` case closes).  This is
  not an overreach: given the domain conversion, `IsDefEq.defeqDF_l` moves the codomain
  conversion from `A::Γ` to `A'::Γ`, and `rigidShapeUniq_of_family` does exactly that. -/
def RigidShape.Compat (env : VEnv) (U : Nat) (Γ : List VExpr) : RigidShape → RigidShape → Prop
  | .sort u, .sort v => u ≈ v
  | .sort _, .pi _ _ => False
  | .sort _, .app _ _ _ => False
  | .pi _ _, .sort _ => False
  | .pi A B, .pi A' B' =>
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u)
  | .pi _ _, .app _ _ _ => False
  | .app _ _ _, .sort _ => False
  | .app _ _ _, .pi _ _ => False
  | .app c ls as, .app c' ls' as' =>
    c = c' → List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

/-- **The bridge.**  A well-typed term that is not a proof is convertible with at most one
rigid shape, up to `Compat`: `e` is the arbitrary middle term of every `trans` case in this
file, and `s₁`, `s₂` are the two shapes the two halves of the `trans` hand back.

See the section docstring for what discharges this (confluence, via
`IsDefEq.church_rosser`), for why `NormalEq.descend`'s conclusion does not, and for the two
machine-checked bounds that keep it exactly as strong as the family it replaces. -/
def RigidShapeUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShape},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-! ### The nine entries are not one node: what `SortUniq` buys, and what it does not

`RigidShapeUniq` quantifies over a pair of shapes, so it has **nine** entries, and they are
not interchangeable.  Exactly one of them is a consequence of universe uniqueness:

* `sort`/`sort` is `IsDefEqU.sort_inv`, which `sort_inv_of_sortUniq`
  (`Theory/Typing/SortUniqDown.lean`) derives from `VEnv.SortUniq` **without opening the
  conversion derivation at all**.  `RigidShapeUniqNS` below therefore drops it, and
  `rigidShapeUniq_of_sortUniq` puts it back; the `sorry` moved to the narrower statement.
* the other eight do **not** follow from `SortUniq`, and the reason is visible in
  `sort_inv_of_sortUniq`'s argument: what makes it work is that *both* endpoints are sorts, so
  `HasTypeStrong.sort_type` pins the shared type `T` from both sides.  With endpoints of
  different shapes the shared type says nothing — `.sort u` and `.forallE (.sort u) (.sort u)`
  are types at one and the same universe `.succ u` (`Theory/Typing/UnivDiscrim.lean`'s
  "Reason 2", machine-checked there) — so the shared-type route is exhausted, not merely
  unfinished.

See `Theory/Typing/RigidNodeCircle.lean` for what the eight *do* reduce to. -/

/-- The two shapes are both sorts — the one entry of `RigidShape.Compat` that universe
uniqueness settles. -/
def RigidShape.BothSort : RigidShape → RigidShape → Prop
  | .sort _, .sort _ => True
  | _, _ => False

/-- **`RigidShapeUniq` minus its `sort`/`sort` entry** — the statement the `sorry` now sits
on.  `rigidShapeUniq_of_sortUniq` recovers the full bridge from this plus `VEnv.SortUniq`, so
no consumer sees a difference; what changed is that the open statement no longer contains a
case that is a theorem. -/
def RigidShapeUniqNS (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShape},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env → ¬ s₁.BothSort s₂ →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-- **The `pi`/`pi` entry alone**, with the `¬ IsProof` premise dropped (it is free at a Π,
`not_isProof_of_defeqU_forallE`).  This is the entry `IsDefEqU.forallE_inv` consumes, and
`rigidPiUniq_iff_piInv` below shows it *is* `VEnv.PiInv`: neither weaker nor stronger. -/
def RigidPiUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T A B A' B' : VExpr}, OnCtx Γ (env.IsType U) →
    env.IsDefEq U Γ e (.forallE A B) T → env.IsDefEq U Γ e (.forallE A' B') T →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u)

/-- A term convertible with a Π is not a proof — the `¬ IsProof` premise of the bridge,
discharged for free wherever one of the two shapes is a Π.  From `VEnv.SortUniq`, which
`WF.sortUniq'` proves above, so it costs no statement a hypothesis. -/
theorem not_isProof_of_defeqU_forallE {Γ : List VExpr} {e A B : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEqU U Γ e (.forallE A B)) :
    ¬ env.IsProof U Γ e := fun hp =>
  have ⟨_, hq, he⟩ := hp.defeqU henv hΓ h
  forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ hq he

/-- A term convertible with a sort is not a proof.  The sort half of
`not_isProof_of_defeqU_forallE`. -/
theorem not_isProof_of_defeqU_sort {Γ : List VExpr} {e : VExpr} {u : VLevel}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ e (.sort u)) : ¬ env.IsProof U Γ e := fun hp =>
  have ⟨_, hq, he⟩ := hp.defeqU henv hΓ h
  sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ hq he

/-- **The one open obligation of the whole inversion family** (`forallE_inv_stratified`
excepted — that is a different shape and has its own hole), **narrowed**: the `sort`/`sort`
entry has been removed, because `sort_inv_of_sortUniq` proves it from `VEnv.SortUniq` with no
normalisation argument.  Eight of the nine entries remain.

The name changed with the statement on purpose: `WF.rigidShapeUniq` below is now a theorem,
and anyone measuring the hole should measure *this*. -/
theorem WF.rigidShapeUniqNS (henv : VEnv.WF env) : env.RigidShapeUniqNS U := sorry

/-- **The `sort`/`sort` entry, put back from universe uniqueness.**  `sorry`-free: the whole
content of the bridge that `SortUniq` pays for is this one line, and
`sort_inv_of_sortUniq`'s argument never inspects the conversion derivation. -/
theorem rigidShapeUniq_of_sortUniq (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeUniqNS U) : env.RigidShapeUniq U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  cases s₁ with
  | sort u =>
    cases s₂ with
    | sort v => exact sort_inv_of_sortUniq hsu henv.ordered hΓ ⟨T, h₁.symm.trans h₂⟩
    | pi A B => exact h hΓ hnp hr₁ hr₂ not_false h₁ h₂
    | app c ls as => exact h hΓ hnp hr₁ hr₂ not_false h₁ h₂
  | pi A B => cases s₂ <;> exact h hΓ hnp hr₁ hr₂ not_false h₁ h₂
  | app c ls as => cases s₂ <;> exact h hΓ hnp hr₁ hr₂ not_false h₁ h₂

/-- The bridge as it was before the narrowing, so that every consumer below is unchanged. -/
theorem WF.rigidShapeUniq (henv : VEnv.WF env) : env.RigidShapeUniq U :=
  rigidShapeUniq_of_sortUniq henv (WF.sortUniq' henv) (WF.rigidShapeUniqNS henv)

/-- **The `pi`/`pi` entry, extracted.**  The `¬ IsProof` premise is discharged on the spot from
`SortUniq`, so `RigidPiUniq` carries none. -/
theorem RigidShapeUniqNS.piUniq (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeUniqNS U) : env.RigidPiUniq U := by
  intro Γ e T A B A' B' hΓ h₁ h₂
  refine h (s₁ := .pi A B) (s₂ := .pi A' B') hΓ (fun hp => ?_) trivial trivial not_false h₁ h₂
  have ⟨_, hq, he⟩ := hp.defeqU henv hΓ ⟨T, h₁⟩
  exact forallE_not_proof hsu henv.ordered hΓ hq he

/-- **The converse: `VEnv.PiInv` gives back the `pi`/`pi` entry.**  This is the pi branch of
`rigidShapeUniq_of_family`, isolated; `sorry`-free.  Together with
`forallE_inv_of_rigidPi` below it makes `rigidPiUniq_iff_piInv` an equivalence, i.e. the
`pi`/`pi` entry of the bridge *is* unstratified Π-injectivity, on the nose. -/
theorem PiInv.rigidPiUniq (henv : VEnv.WF env) (hpi : env.PiInv U) : env.RigidPiUniq U := by
  intro Γ e T A B A' B' hΓ h₁ h₂
  obtain ⟨⟨u, ha⟩, v, hb⟩ := hpi hΓ ⟨T, h₁.symm.trans h₂⟩
  exact ⟨⟨u, ha⟩, v, hb, ha.defeqDF_l henv.ordered hb⟩

/-- **The bridge is no stronger than the family it packages**, and therefore satisfiable if
the family is: this derives it from the five conclusions, taken as explicit hypotheses, with
no `sorry` of its own.  Read together with the five proofs below — which go the other way —
it says the bridge *is* the family, so hoisting it neither weakened nor strengthened
anything.

The one hypothesis that is not literally a theorem of this file is `happ`: it is
`const_app_inv` with `IsType` weakened to `¬ IsProof`.  That is the form
`const_app_inv`'s own induction proves (its invariant is `¬ IsProof`, because `IsType` does
not propagate down a spine), and `IsType.not_isProof` turns the stated theorem's side
condition into it, so nothing here asks for more than the file already has. -/
theorem rigidShapeUniq_of_family (henv : VEnv.WF env)
    (hsort : ∀ {Γ : List VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
      env.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v)
    (hpi : env.PiInv U)
    (hsortpi : ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, OnCtx Γ (env.IsType U) →
      ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B))
    (happ : ∀ {Γ : List VExpr} {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
      ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
      env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as') →
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as')
    (happpi : ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
      {A B : VExpr}, OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
      ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B))
    (happsort : ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
      {u : VLevel}, OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
      ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u)) :
    env.RigidShapeUniq U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have hs : env.IsDefEqU U Γ s₁.toExpr s₂.toExpr := ⟨T, h₁.symm.trans h₂⟩
  cases s₁ with
  | sort u =>
    cases s₂ with
    | sort v => exact hsort hΓ hs
    | pi A B => exact hsortpi hΓ hs
    | app c ls as => exact happsort hΓ hr₂ hs.symm
  | pi A B =>
    cases s₂ with
    | sort v => exact hsortpi hΓ hs.symm
    | pi A' B' =>
      obtain ⟨⟨u, ha⟩, v, hb⟩ := hpi hΓ hs
      exact ⟨⟨u, ha⟩, v, hb, ha.defeqDF_l henv.ordered hb⟩
    | app c ls as => exact happpi hΓ hr₂ hs.symm
  | app c ls as =>
    cases s₂ with
    | sort v => exact happsort hΓ hr₁ hs
    | pi A B => exact happpi hΓ hr₁ hs
    | app c' ls' as' =>
      rintro rfl
      exact happ hΓ hr₁ (fun hp => hnp (hp.defeqU henv hΓ ⟨T, h₁.symm⟩)) hs

end RigidShapeBridge

/-- **Π-injectivity, proved directly rather than through the stratified form.**  All eleven
`IsDefEqStrong` cases are now discharged; the proof is `sorry`-free **modulo the single
bridge `VEnv.WF.rigidShapeUniq`** (section `RigidShapeBridge`), which its `trans` case
applies at the two Π shapes.  `proofIrrel` closes outright, from `VEnv.SortUniq` being a
theorem.

**This corrects `forallE_inv_stratified`'s docstring, which is about that statement and not
about this one.**  That docstring says Π-injectivity needs universe uniqueness *in the
structural cases*, `forallEDF` included.  It does — in the *stratified* formulation, whose
conclusion pairs each conversion with a `HasTypeStratified` derivation *at a level chosen by
a different derivation*; aligning those two levels is the universe-uniqueness demand.  The
plain statement carries no such conjunct, so `forallEDF` hands both halves back on the nose
and there is no level to align.  Both consumers of the stratified form already discard the
`HasTypeStratified` components (its own docstring says so); what was not noticed is that
discarding them removes the *obstruction*, not merely the payload.

**The one real difficulty is `symm`, and it is dissolved by strengthening the induction, not
by a new lemma.**  Inverting `.forallE A' B' ≡ .forallE A B` gives the codomain conversion in
context `A'::Γ`, while the goal wants it in `A::Γ` — a context conversion, which is exactly
what blocks `DefInv` clause (2) and `PropConvInv`'s `forallEDF` case elsewhere in the tree.
It is avoidable here: `IsDefEqStrong.forallEDF` carries the codomain conversion **in both
contexts** (`A::Γ ⊢ body ≡ body'` and `A'::Γ ⊢ body ≡ body'`, `Strong.lean:54–55`), so
carrying *both* through the induction makes `symm` close by `IsDefEq.symm` alone.  The extra
conjunct is discarded at the end.

So Π-injectivity is **not** a second obligation beyond `sort_inv`: granted a `trans` case
(normalisation) and "a Π is not a proof", it follows.  See `docs/handoff-injectivity.md`. -/
theorem IsDefEqU.forallE_inv_of_rigidPi (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (hrp : env.RigidPiUniq U) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) := by
  have aux : ∀ {Γ : List VExpr} {e1 e2 T : VExpr}, env.IsDefEqStrong U Γ e1 e2 T →
      OnCtx Γ (env.IsType U) →
      ∀ A B A' B', e1 = .forallE A B → e2 = .forallE A' B' →
        (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
        ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u) := by
    intro Γ e1 e2 T H
    induction H with
    | forallEDF _ _ h3 h4 h5 =>
      rintro _ _ _ _ _ ⟨⟩ ⟨⟩
      exact ⟨⟨_, h3.defeq⟩, _, h4.defeq, h5.defeq⟩
    | symm _ ih =>
      rintro hΓ' A B A' B' rfl rfl
      obtain ⟨⟨u, ha⟩, v, hb1, hb2⟩ := ih hΓ' A' B' A B rfl rfl
      exact ⟨⟨u, ha.symm⟩, v, hb2.symm, hb1.symm⟩
    | defeqDF _ _ _ _ ih => exact ih
    | extra h1 => exact fun _ A B _ _ h _ => absurd h (henv.instL_lhs_ne_forallE h1 _ A B)
    | trans hd1 hd2 ih1 ih2 =>
      -- `Γ ⊢ .forallE A B ≡ e₂ ≡ .forallE A' B'` with `e₂` arbitrary — **the** residual of
      -- this family, discharged by `WF.rigidShapeUniq` (see its section docstring).  Note
      -- the two halves are at the *same* type, which is what the bridge asks for; the
      -- induction hypotheses are not used, and cannot be: they fire only when the middle
      -- term is syntactically a Π.
      rintro hΓ' A B A' B' rfl rfl
      exact hrp hΓ' hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 _ _ _ _ =>
      -- CLOSED: "a Π is not a proof", from `VEnv.SortUniq` — proved above (`WF.sortUniq'`),
      -- so this costs the statement no hypothesis.
      rintro hΓ' A B A' B' rfl rfl
      exact absurd (forallE_not_proof hsu henv.ordered hΓ'
        h1.defeq.hasType.1 h2.defeq.hasType.1) not_false
    | _ => rintro _ A B A' B' ⟨⟩ ⟨⟩
  obtain ⟨_, h1⟩ := h1
  obtain ⟨ha, u, hb, -⟩ := aux (h1.strong henv.ordered hΓ) hΓ _ _ _ _ rfl rfl
  exact ⟨ha, u, hb⟩

/-- Π-injectivity, unchanged in statement.  Every ingredient beyond the `pi`/`pi` entry of the
bridge is now discharged: see `forallE_inv_of_rigidPi`. -/
theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  forallE_inv_of_rigidPi henv (WF.sortUniq' henv)
    (RigidShapeUniqNS.piUniq henv (WF.sortUniq' henv) (WF.rigidShapeUniqNS henv)) hΓ h1

/-- **The `pi`/`pi` entry of the bridge is exactly `VEnv.PiInv`.**  `sorry`-free.

This is the first half of the classification of `WF.rigidShapeUniq` (see
`Theory/Typing/RigidNodeCircle.lean` for the rest).  It says the bridge does **not** reduce to
`VEnv.SortUniq`: modulo universe uniqueness it still contains unstratified Π-injectivity, and
`PiLevelPin.piInvCod_of_piInvStratApp`'s docstring records that `PiInvStratApp` — hence
`SortUniq`, by `piInvStratApp_iff_sortUniq` — recovers only `PiInvCod`, never the *domain*
conjunct of `PiInv`.  So `SortUniq → PiInv` is not available by any of the bracketings in this
file, and the injectivity corner has **two** nodes, not one. -/
theorem piInv_of_rigidPiUniq (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (hrp : env.RigidPiUniq U) : env.PiInv U :=
  fun hΓ h => IsDefEqU.forallE_inv_of_rigidPi henv hsu hrp hΓ h

@[inherit_doc piInv_of_rigidPiUniq]
theorem rigidPiUniq_iff_piInv (henv : VEnv.WF env) (hsu : env.SortUniq U) :
    env.RigidPiUniq U ↔ env.PiInv U :=
  ⟨piInv_of_rigidPiUniq henv hsu, PiInv.rigidPiUniq henv⟩

/-- **(A) Disjointness, sort/Π half** — a sort is not a Π.

Written out as the same induction as `sort_inv` and `const_forallE_inv`, for the same reason:
nine of the eleven `IsDefEqStrong` cases close outright, and what is left is the *same two*
labelled holes — `trans` and `proofIrrel`.  Machine-checking that reduction is the point.
Before this, the statement was one opaque `sorry` and the claim that it lives in the same
family as `sort_inv` was prose.

* `extra` closes from `VEnv.WF.instL_lhs_ne_sort` **and** `VEnv.WF.instL_lhs_ne_forallE`
  (`Theory/Typing/DeclRules.lean`): no rule's left-hand side is a sort, and none is a Π.
* every remaining structural case is vacuous on the *shape* of one endpoint.
* `trans` — the arbitrary middle term; discharged by `VEnv.WF.rigidShapeUniq` at the shapes
  `.sort u` and `.pi A B`, whose `RigidShape.Compat` entry is `False`.
* `proofIrrel` — needs "a sort is not a proof" *or* "a Π is not a proof"; either suffices,
  and the first is `VEnv.sort_not_proof` given `VEnv.SortUniq`.  So this statement's
  `proofIrrel` residual is **not a new obligation**: it is a strictly weaker demand than
  `sort_inv`'s, which needs the sort half specifically. -/
theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (u : VLevel) (A B : VExpr),
        (e₁ = .sort u ∧ e₂ = .forallE A B) ∨ (e₂ = .sort u ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun hΓ' u A B h => ih hΓ' u A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      -- The middle term is arbitrary: `WF.rigidShapeUniq` at the shapes `.sort u` and
      -- `.pi A B`, whose `Compat` entry is `False`.
      rintro hΓ' u A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact WF.rigidShapeUniq henv (s₁ := .sort u) (s₂ := .pi A B) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
      · exact WF.rigidShapeUniq henv (s₁ := .pi A B) (s₂ := .sort u) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      -- CLOSED: "a Π is not a proof" (the sort half would do equally well), from
      -- `VEnv.SortUniq` — proved above, so this costs the statement no hypothesis.
      rintro hΓ' u A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ u A B (⟨he, -⟩ | ⟨-, he⟩)
      · exact henv.instL_lhs_ne_sort h1 _ _ he
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ he
    | sortDF _ _ _ => rintro _ u A B (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | forallEDF _ _ _ _ _ => rintro _ u A B (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | bvar _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ u A B (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) hΓ u A B (.inl ⟨rfl, rfl⟩)

/-- **(B) Injectivity of a constant application.**  See the module docstring for why both
side conditions are needed, and `Theory/Typing/ConstInvWitness.lean` for the machine-checked
witness against each.

**Statement unchanged; the proof is now the same induction as the other four.**  This was an
opaque `sorry` because the `IsType` side condition does not propagate into the induction —
at `appDF` the sub-spine has a Π type, not a sort, so the invariant could not carry it.  The
fix is to carry `¬ IsProof` instead (`section UniqAux`'s `IsProof`, `IsType.not_isProof`,
`IsProof.app'`): it is what the `proofIrrel` case actually needs, it is *implied* by `IsType`
so the statement is unweakened, and it **does** propagate down a spine.  With that, twelve of
the thirteen `IsDefEqStrong` cases close and the residual is the **`trans`** case alone —
byte for byte the residual of `forallE_inv`, `sort_forallE_inv`, `const_forallE_inv` and
`const_sort_inv`.  So this is no longer an independent obligation: the whole family now rests
on one normalisation statement, and since `VEnv.WF.rigidShapeUniq` *is* that statement, all
five `trans` cases are literally the same appeal.  This case is also the reason the bridge's
premise is `¬ IsProof` and not `IsType`, for exactly the reason recorded in the next
paragraph.

Case by case: `constDF` gives the level list outright; `appDF` peels one argument off each
spine (`VExpr.mkApp_app_inv`) and appends the argument conversion; `extra` is blocked by
`RuleFreeHead`; `proofIrrel` by `¬IsProof`; `symm` and `defeqDF` are bookkeeping; the
remaining seven are vacuous on the spine head of the left endpoint. -/
theorem IsDefEqU.const_app_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (hrigid : RuleFreeHead env c)
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as')) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e₁ →
      ∀ (ls ls' : List VLevel) (as as' : List VExpr),
        e₁ = (VExpr.const c ls).mkApp as → e₂ = (VExpr.const c ls').mkApp as' →
        List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm hd ih =>
      intro hΓ' hnp ls₁ ls₁' as₁ as₁' he₁ he₂
      obtain ⟨h1, h2⟩ := ih hΓ' (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd.defeq⟩))
        ls₁' ls₁ as₁' as₁ he₂ he₁
      exact ⟨h1.symm' (fun h => Eq.symm h), h2.symm' IsDefEqU.symm⟩
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      -- The middle term is arbitrary: `WF.rigidShapeUniq` at two `.app` shapes with the
      -- same head.  This is the case that forces the bridge's premise to be `¬ IsProof`
      -- rather than `IsType`: here `e₁` may be a sub-spine, whose type is a Π.
      rintro hΓ' hnp ls₁ ls₁' as₁ as₁' rfl rfl
      exact WF.rigidShapeUniq henv (s₁ := .app c ls₁ as₁) (s₂ := .app c ls₁' as₁') hΓ'
        (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd1.defeq.symm⟩)) hrigid hrigid
        hd1.defeq.symm hd2.defeq rfl
    | proofIrrel h1 h2 _ =>
      -- CLOSED by the `¬IsProof` invariant, which the statement's `IsType` side condition
      -- supplies at the root (`IsType.not_isProof`) and `IsProof.app'` threads down.
      intro _ hnp _ _ _ _ _ _
      exact absurd ⟨_, h1.defeq.hasType.1, h2.defeq.hasType.1⟩ hnp
    | extra h1 =>
      intro _ _ ls₁ _ as₁ _ he₁ _
      exact absurd (by rw [← VExpr.headConst?_instL, he₁, VExpr.headConst?_mkApp]; rfl)
        (hrigid _ h1)
    | constDF h1 _ _ _ h5 =>
      intro _ _ ls₁ ls₁' as₁ as₁' he₁ he₂
      obtain ⟨rfl, he₁⟩ := VExpr.mkApp_eq_of_not_app as₁ _ _ he₁.symm nofun
      obtain ⟨rfl, he₂⟩ := VExpr.mkApp_eq_of_not_app as₁' _ _ he₂.symm nofun
      injection he₁ with _ he₁; injection he₂ with _ he₂
      exact ⟨he₁ ▸ he₂ ▸ h5, .nil⟩
    | appDF _ _ hA hB hf ha _ _ _ ihf =>
      intro hΓ' hnp ls₁ ls₁' as₁ as₁' he₁ he₂
      rcases VExpr.mkApp_app_inv as₁ _ he₁.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
      · exact absurd hbad nofun
      rcases VExpr.mkApp_app_inv as₁' _ he₂.symm with ⟨-, hbad⟩ | ⟨bs', rfl, hb'⟩
      · exact absurd hbad nofun
      have hnpf : ¬ env.IsProof U _ _ := fun hp =>
        hnp (hp.app' henv hΓ' hA.defeq hB.defeq hf.defeq.hasType.1 ha.defeq.hasType.1)
      obtain ⟨hl, hbs⟩ := ihf hΓ' hnpf ls₁ ls₁' bs bs' hb.symm hb'.symm
      exact ⟨hl, hbs.append' (.cons ⟨_, ha.defeq⟩ .nil)⟩
    | bvar _ _ _ | sortDF _ _ _ | lamDF _ _ _ _ _ _ _ | forallEDF _ _ _ _ _
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      intro _ _ ls₁ _ as₁ _ he₁ _
      have hs := congrArg VExpr.spineHead he₁
      rw [VExpr.spineHead_mkApp] at hs
      exact absurd hs nofun
  obtain ⟨_, h⟩ := h
  exact aux (h.strong henv.ordered hΓ) hΓ (IsType.not_isProof henv hΓ hty) ls ls' as as' rfl rfl

/-- **(A) Disjointness** — ledger item I13, and the only one of the three the ledger records.
Consumed by `pat_major_not_pi` (I14).  Needs no `IsType` side condition: `proofIrrel` cannot
identify a term with a Π, because a Π is a type. -/
theorem IsDefEqU.const_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (ls : List VLevel) (as A B : _),
        (e₁ = (VExpr.const c ls).mkApp as ∧ e₂ = .forallE A B) ∨
        (e₂ = (VExpr.const c ls).mkApp as ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun hΓ' ls as A B h => ih hΓ' ls as A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      -- The middle term is arbitrary: `WF.rigidShapeUniq` at `.app c ls as` and `.pi A B`,
      -- whose `Compat` entry is `False`.
      rintro hΓ' ls as A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact WF.rigidShapeUniq henv (s₁ := .app c ls as) (s₂ := .pi A B) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd2.defeq⟩) hrigid trivial
          hd1.defeq.symm hd2.defeq
      · exact WF.rigidShapeUniq henv (s₁ := .pi A B) (s₂ := .app c ls as) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial hrigid
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      -- CLOSED: "a Π is not a proof", from `VEnv.SortUniq` — proved above, so this costs the
      -- statement no hypothesis.
      rintro hΓ' ls as A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 h2 h3 =>
      rintro _ ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · exact hrigid _ h1 (by rw [← VExpr.headConst?_instL, he, VExpr.headConst?_mkApp]; rfl)
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ hf
    | beta _ _ _ _ _ _ _ _ =>
      rintro _ ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
    | eta _ _ _ _ _ _ _ _ =>
      rintro _ ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
    | forallEDF _ _ _ _ _ =>
      rintro _ ls as A B (⟨he, -⟩ | ⟨he, -⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | bvar _ _ _ | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ =>
      rintro _ ls as A B (⟨_, hf⟩ | ⟨_, hf⟩) <;> exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) hΓ ls as A B (.inl ⟨rfl, rfl⟩)

/-- **(A) Disjointness, sort half** — a rule-free constant application is not a sort.

Stated for the same reason `const_forallE_inv` is, and with the same side condition and the
same absence of an `IsType` one: `proofIrrel` cannot identify a constant application with a
sort, because that would make a sort a proof, which `VEnv.sort_not_proof`
(`Theory/Typing/SortUniq.lean`) refutes given `VEnv.SortUniq`.

**This statement did not exist in the tree until its third consumer asked for it.**  It is
needed by the set model's block-freeness lemma at the same base case that needs
`const_forallE_inv`, and nothing had ever written it down.  It is `sorry` like its sibling;
the point of stating it is that the next consumer finds a statement rather than a gap. -/
theorem IsDefEqU.const_sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (ls : List VLevel) (as : List VExpr) (u : VLevel),
        (e₁ = (VExpr.const c ls).mkApp as ∧ e₂ = .sort u) ∨
        (e₂ = (VExpr.const c ls).mkApp as ∧ e₁ = .sort u) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun hΓ' ls as u h => ih hΓ' ls as u h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      -- The middle term is arbitrary: `WF.rigidShapeUniq` at `.app c ls as` and `.sort u`,
      -- whose `Compat` entry is `False`.
      rintro hΓ' ls as u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact WF.rigidShapeUniq henv (s₁ := .app c ls as) (s₂ := .sort u) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd2.defeq⟩) hrigid trivial
          hd1.defeq.symm hd2.defeq
      · exact WF.rigidShapeUniq henv (s₁ := .sort u) (s₂ := .app c ls as) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial hrigid
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      -- CLOSED: "a sort is not a proof", from `VEnv.SortUniq` — proved above, so this costs
      -- the statement no hypothesis.
      rintro hΓ' ls as u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ ls as u (⟨he, -⟩ | ⟨-, he⟩)
      · exact hrigid _ h1 (by rw [← VExpr.headConst?_instL, he, VExpr.headConst?_mkApp]; rfl)
      · exact henv.instL_lhs_ne_sort h1 _ _ he
    | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _ | lamDF _ _ _ _ _ _ _ =>
      rintro _ ls as u (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | sortDF _ _ _ | bvar _ _ _ =>
      rintro _ ls as u (⟨he, -⟩ | ⟨he, -⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | forallEDF _ _ _ _ _ | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ ls as u (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) hΓ ls as u (.inl ⟨rfl, rfl⟩)

/-! ## The circle, stated

Two `sorry`-free implications, between statements packaged as `Prop`s in the `UniqAux`
section above:

* `sortUniq_of_piInvStratApp : PiInvStratApp → SortUniq`
* `piInvStratApp_of : SortUniq → PiInv → PiInvStratApp`
* `sortUniq_iff_piInvStratApp` — the two, packaged as an `↔`

and, for the wide form, `sortUniq_of_piInvStrat` / `piInvStrat_of`, which are the same two
composed with `PiInvStrat.app`.

**The circle survives narrowing.**  `PiInvStratApp` is the *only* instance of `PiInvStrat`
that anything consumes (`uniqQ`'s `app` case, once): no domain conjunct, one index instead of
two.  Narrowing to it shrinks the residual and changes nothing else — the equivalence with
`SortUniq` still holds in both directions, and `piInvStratApp_fires` checks that forcing both
indices equal did not empty the statement (the witness has syntactically different domains, so
the conclusion is not an instance of reflexivity).

So **relative to `PiInv` (the plain `forallE_inv`), `PiInvStrat`, `PiInvStratApp` and
`SortUniq` are all equivalent.**  `forallE_inv_stratified` is therefore not a passenger that
`uniqAux` could drop: replacing it in `uniqQ`'s `app` case by `PiInv` needs `SortUniq` applied to a
derivation that comes from an *unstratified* `IsDefEq` and so carries no index bound, while
`uniqQ` has `SortUniq` available only at indices `< n`.  That is where the route in
`docs/handoff-sortuniq.md` §9 fails, and it fails on the index bookkeeping, exactly where
that document predicted the question would be settled. -/

/-- `IsDefEqU.forallE_inv` as an inhabitant of `PiInv` — the anti-strawman check that `PiInv`
is that theorem's type verbatim, not a paraphrase. -/
theorem piInv_axiom (henv : VEnv.WF env) : env.PiInv U :=
  fun hΓ h1 => IsDefEqU.forallE_inv henv hΓ h1

/-- `forallE_inv_stratified`'s statement, from `SortUniq` and the *plain* Π-injectivity.
Its cone contains `IsDefEqU.forallE_inv` and **not** `IsDefEqU.forallE_inv_stratified`; what
it does contain is `SortUniq`, which in this tree has no source but
`forallE_inv_stratified`. -/
theorem piInvStrat_of_sortUniq (henv : VEnv.WF env) (hsu : env.SortUniq U) :
    env.PiInvStrat U := piInvStrat_of henv hsu (piInv_axiom henv)
