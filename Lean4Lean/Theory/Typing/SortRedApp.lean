import Lean4Lean.Theory.Typing.SortClauses

/-!
# `SortRedAppDF`: what is left of clauses (1) and (3), narrowed and constrained

`Theory/Typing/SortClauses.lean` reduces the two surviving clauses of definitional inversion
at index 1 to a single residual, `SortRedAppDF env U 0`, and leaves it undecided.  This file
does not decide it either.  What it does is:

1. **§1 — the residual is *equivalent* to the reduction it came from.**
   `SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1` (`empty_sortRedAppDF_iff`), and the same over
   `propLoopEnv`.  So "one residual is left" is a *reformulation*, not a weakening: nothing
   was given away, and nothing was gained in strength either.  Read
   `docs/handoff-definv-weakening.md` §4's headline with that in mind.
2. **§2 — the companion test of `docs/handoff-stratified.md` §5 fails, and it is checked.**
   At the function position of `appDF` the induction hypothesis `SortRed u f ↔ SortRed u f'`
   follows from the *ambient* typing premises alone (`sortRedAppDF_fun_ih_vacuous`): both
   sides are false because a `⊢₀`-typed term at a Π-type never weak-head reduces to a sort.
   The argument position is not vacuous (`sortRedAppDF_arg_ih_nonvacuous`).  So an induction
   on the conversion carrying `SortRed` as its predicate learns nothing where it must.
3. **§3–§4 — the obvious repair is *refuted*.**  The repair for a vacuous induction
   hypothesis is to generalise the predicate so the position becomes load-bearing: carry a
   spine, so that `appDF` recurses on `f ≡ f'` with the arguments appended.  The typing-free
   version of that predicate is **false at index 1** (`spineInv_one_false`), by a witness over
   a **well-formed** context: `fun (_ : P) => (the bound proof)` and
   `fun (_ : P) => (the ambient proof)` are `⊢₀`-typed at one Π-type `P → P` and identified by
   `lamDF` over `proofIrrel`, and applying both to `Prop` separates them.
   Consequently **the premise `Γ ⊢ₙ a : A` of the residual is load-bearing**
   (`ArgWitness.sortRedAppDF_needs_arg_typing`): every other premise is met at that witness
   and the conclusion fails.  Since `trans` carries no typing for its middle term, this is a
   hard constraint on any proof, of the same kind as `SortClauses` §3's "the proof must use
   `VEnv.WF`".
4. **§5 — two claims recorded as *analysis* in `docs/handoff-definv-weakening.md` §4 are now
   machine-checked**: `proofIrrel` can never fire on the function position
   (`proofIrrel_not_at_pi`), and `lamDF` cannot separate the domains
   (`lam_pair_at_one_type`).
5. **§6 — a `SortRed`-ing term's `⊢₀` type is a sort, and the level is pinned**
   (`SortRed.hasTypeN_zero_type`).  Hence the residual splits into exactly two branches by the
   shape of the codomain `B`: a closed sort, or `B = .bvar 0` — i.e. `f : ∀ X, X`.
6. **§8 — the `∀ X, X` branch is discharged**: its `SortRed u (.app f a)` premise has no
   instances at all over any ordered environment (`sortRedAppDFVar_premise_empty`).  The proof
   is: a `SortRed`-ing application exposes a λ in the function (`SortRed.app_head`);
   substituting a **sort** creates no new head redexes (`headBeta_inst_sort`); so a body
   `⊢₀`-typed at `.bvar 0` would have to weak-head reduce to a sort or to `.bvar 0`, and
   neither is `⊢₀`-typed at `.bvar 0`.  This also removes a circularity: that branch, had it
   instances, would have *proved* a sort-shape statement about the argument
   (`sortRedAppDFVar_forces_sort_arg`) — the very content clause (1) was to supply.
7. **§9 — the surviving branch, named.**  `SortRedLamExpose`: *weak-head λ-exposure is
   invariant along a `⊢ₙ₊₁` conversion at a Π-type, and the exposed bodies agree on `SortRed`
   after the two arguments are substituted.*  It is **equivalent** to the residual
   (`sortRedAppDFSort_iff_lamExpose`), and §11 assembles the chain.
8. **§7 and §10 — non-vacuity.**  Everything is replayed over `CycleConv.propLoopEnv`,
   including the §3 refutation (which works there with the environment's own constant as the
   proposition) and a non-degenerate instance of the surviving residual with `f ≠ f'`.

**Verdict: `SortRedAppDF ∅ 1 0` is still open** — neither proved nor refuted.  It is now
equal to `SortRedLamExpose ∅ 1 0`, one branch shorter and with two machine-checked constraints
on what a proof may look like.  See `docs/handoff-sortred.md`.

Everything below is sorry-free; axioms are `propext`, `Quot.sound` and `Classical.choice`,
verified by a `collectAxioms` sweep over the module's 111 declarations.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. The residual is equivalent to the whole reduction -/

theorem sortRedAppDF_of_sortRedInv (h : SortRedInv env U (n+1)) : SortRedAppDF env U n :=
  fun hff' hf hf' haa' ha ha' => h (.appDF hff' hf hf' haa' ha ha')

theorem empty_sortRedInv_one_of_appDF (h1 : SortRedAppDF ∅ 1 0) : SortRedInv ∅ 1 1 :=
  fun hc => sortRedInv_of hc 0 rfl h1 (PiTypedNotSortRed.zero .empty)
    (ProofNotSortRed.zero .empty) ExtraSortRed.empty rfl _

theorem empty_sortRedAppDF_iff : SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1 :=
  ⟨empty_sortRedInv_one_of_appDF, sortRedAppDF_of_sortRedInv⟩

/-! ## 2. The criterion, run against the residual -/

/-- **The induction hypothesis at the function position of `appDF` is vacuous.**  The two
typing premises alone — with no reference to the sub-derivation `Γ ⊢ₙ₊₁ f ≡ f'` — already
prove `SortRed u f ↔ SortRed u f'`, because a `⊢₀`-typed term at a Π-type never weak-head
reduces to a sort.  This is `docs/handoff-stratified.md` §5's companion test, and the
residual **fails** it: an induction on the conversion whose predicate is `SortRed` learns
nothing at the one position where it must learn something. -/
theorem sortRedAppDF_fun_ih_vacuous (henv : Ordered env) {Γ : List VExpr} {f f' A B : VExpr}
    {u : VLevel} (hf : env.HasTypeN U 0 Γ f (.forallE A B))
    (hf' : env.HasTypeN U 0 Γ f' (.forallE A B)) : SortRed u f ↔ SortRed u f' :=
  iff_of_false (PiTypedNotSortRed.zero henv hf) (PiTypedNotSortRed.zero henv hf')

/-- **The argument position is not vacuous**, at the same base index and over `∅`: two terms
`⊢₀`-typed at one and the same type, one of which weak-head reduces to a sort and the other of
which does not.  So the two recursive positions of `appDF` are genuinely different, and only
the argument one carries information. -/
theorem sortRedAppDF_arg_ih_nonvacuous :
    (∅ : VEnv).HasTypeN 1 0 [.sort (.succ .zero)] (.sort .zero) (.sort (.succ .zero)) ∧
    (∅ : VEnv).HasTypeN 1 0 [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) ∧
    SortRed .zero (.sort .zero) ∧ ¬ SortRed .zero (VExpr.bvar 0) :=
  ⟨.sort trivial, .bvar (Lookup.zero' rfl), .sort rfl, SortRed.not_bvar⟩

/-! ## 3. The argument typing premise is load-bearing -/

namespace ArgWitness

/-- A **well-formed** context over `∅`: a proposition `P` (`.bvar 1`) and a proof of it
(`.bvar 0`).  Nothing here is junk — each entry is a type in the preceding context. -/
def wctx : List VExpr := [.bvar 0, .sort .zero]

theorem wprop : (∅ : VEnv).HasTypeN 1 0 wctx (.bvar 1) (.sort .zero) :=
  .bvar (Lookup.succ' (Lookup.zero' rfl) rfl)

theorem wproof : (∅ : VEnv).HasTypeN 1 0 wctx (.bvar 0) (.bvar 1) :=
  .bvar (Lookup.zero' rfl)

/-- The context under one more binder of type `P`.  `.bvar 2` is `P`; `.bvar 0` and `.bvar 1`
are two proofs of it. -/
def wctx2 : List VExpr := VExpr.bvar 1 :: wctx

theorem wprop2 : (∅ : VEnv).HasTypeN 1 0 wctx2 (.bvar 2) (.sort .zero) :=
  .bvar (Lookup.succ' (Lookup.succ' (Lookup.zero' rfl) rfl) rfl)

theorem wproof2_zero : (∅ : VEnv).HasTypeN 1 0 wctx2 (.bvar 0) (.bvar 2) :=
  .bvar (Lookup.zero' rfl)

theorem wproof2_one : (∅ : VEnv).HasTypeN 1 0 wctx2 (.bvar 1) (.bvar 2) :=
  .bvar (Lookup.succ' (Lookup.zero' rfl) rfl)

/-- `fun (_ : P) => (the new proof)` — the identity on `P`. -/
def idP : VExpr := .lam (.bvar 1) (.bvar 0)

/-- `fun (_ : P) => (the ambient proof)` — the constant function on `P`. -/
def constP : VExpr := .lam (.bvar 1) (.bvar 1)

/-- Both are `⊢₀`-typed at **one and the same** Π-type `P → P`. -/
theorem idP_type : (∅ : VEnv).HasTypeN 1 0 wctx idP (.forallE (.bvar 1) (.bvar 2)) :=
  .lam wprop wproof2_zero

theorem constP_type : (∅ : VEnv).HasTypeN 1 0 wctx constP (.forallE (.bvar 1) (.bvar 2)) :=
  .lam wprop wproof2_one

/-- …and they are `⊢₁`-convertible, by `lamDF` over `proofIrrel`: the two bodies are proofs of
the proposition `.bvar 2`. -/
theorem idP_conv_constP : (∅ : VEnv).IsDefEqN 1 1 wctx idP constP :=
  .lamDF .rfl (.proofIrrel wprop2 wproof2_zero wproof2_one)

/-- The argument at which they differ: `Prop`.  It is `⊢₀`-typed — just **not** at the domain
`P`. -/
theorem arg_type : (∅ : VEnv).HasTypeN 1 0 wctx (.sort .zero) (.sort (.succ .zero)) :=
  .sort trivial

theorem app_idP_sortRed : SortRed .zero (.app idP (.sort .zero)) :=
  .step .beta (.sort rfl)

theorem app_constP_not_sortRed : ¬ SortRed .zero (.app constP (.sort .zero)) := by
  intro h
  cases h with
  | step hb hY =>
    cases hb with
    | beta => exact SortRed.not_bvar hY
    | app hb => exact absurd hb HeadBeta.not_lam

/-- **The premise `Γ ⊢ₙ a : A` of `SortRedAppDF` is load-bearing.**  Every other premise of
the residual is met — the two functions are `⊢₁`-convertible and `⊢₀`-typed at one Π-type, the
two arguments are equal (so `⊢₁`-convertible by `rfl`) and `⊢₀`-typed — and the conclusion is
**false**.  The single missing hypothesis is that the argument inhabits the domain.

So no proof of `SortRedAppDF` can avoid using the argument's typing, and in particular no
argument that works uniformly for `⊢₁`-convertible functions applied to arbitrary terms can
work.  This is a machine-checked constraint of the same kind as
`SortClauses.sortPiEnv_sortForallEDisjN_false`'s: that one says the proof must use `VEnv.WF`,
this one says it must use the argument typing. -/
theorem sortRedAppDF_needs_arg_typing :
    (∅ : VEnv).IsDefEqN 1 1 wctx idP constP ∧
    (∅ : VEnv).HasTypeN 1 0 wctx idP (.forallE (.bvar 1) (.bvar 2)) ∧
    (∅ : VEnv).HasTypeN 1 0 wctx constP (.forallE (.bvar 1) (.bvar 2)) ∧
    (∅ : VEnv).IsDefEqN 1 1 wctx (.sort .zero) (.sort .zero) ∧
    (∅ : VEnv).HasTypeN 1 0 wctx (.sort .zero) (.sort (.succ .zero)) ∧
    ¬ (SortRed .zero (.app idP (.sort .zero)) ↔ SortRed .zero (.app constP (.sort .zero))) :=
  ⟨idP_conv_constP, idP_type, constP_type, .rfl, arg_type,
    fun h => app_constP_not_sortRed (h.1 app_idP_sortRed)⟩

/-- The same fact stated without reference to the residual: **`⊢₁`-conversion is not a
congruence for `SortRed` under application.**  `idP ≡₁ constP`, but applying both to `Prop`
separates them. -/
theorem defEqN_one_not_sortRed_app_congr :
    ∃ (Γ : List VExpr) (X Y c : VExpr),
      (∅ : VEnv).IsDefEqN 1 1 Γ X Y ∧ SortRed .zero (.app X c) ∧ ¬ SortRed .zero (.app Y c) :=
  ⟨wctx, idP, constP, .sort .zero, idP_conv_constP, app_idP_sortRed, app_constP_not_sortRed⟩

end ArgWitness

/-! ## 4. The spine strengthening that would make `appDF` free is FALSE -/

/-- `X` applied to a spine, innermost argument first. -/
def _root_.Lean4Lean.VExpr.apps : VExpr → List VExpr → VExpr
  | e, [] => e
  | e, a :: as => (VExpr.app e a).apps as

/-- **The typing-free spine invariance.**  This is the natural strengthening of `SortRedInv`
under which the `appDF` case of `sortRedInv_of` becomes free: at `appDF` one would recurse on
`f ≡ f'` with the spine grown by `(a, a')`, and the vacuous function-position induction
hypothesis of §2 would become the goal itself.  It is refuted below. -/
def SpineInv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X Y : VExpr} {as as' : List VExpr} {u : VLevel},
    env.IsDefEqN U n Γ X Y → List.Forall₂ (env.IsDefEqN U n Γ) as as' →
    (SortRed u (X.apps as) ↔ SortRed u (Y.apps as'))

theorem sortRedInv_of_spineInv (h : SpineInv env U n) : SortRedInv env U n :=
  fun hc => h hc .nil

/-- **`SpineInv ∅ 1 1` is false**, at the §3 witness with the one-element spine `[Prop]`.

Consequence for the residual: the obvious way to discharge `SortRedAppDF` — generalise the
predicate so that the function position of `appDF` carries the argument along — **cannot be
done without carrying the argument's typing as well**.  A typing-free spine predicate is
refuted here, over a well-formed context, by `lamDF` over `proofIrrel`. -/
theorem spineInv_one_false : ¬ SpineInv ∅ 1 1 := fun h =>
  ArgWitness.app_constP_not_sortRed
    ((h ArgWitness.idP_conv_constP (as := [.sort .zero]) (as' := [.sort .zero])
      (List.Forall₂.cons .rfl .nil)).1 ArgWitness.app_idP_sortRed)

/-! ## 5. Two claims of `docs/handoff-definv-weakening.md` §4, machine-checked

Both were recorded there as *analysis*.  They are the reasons the two obvious refutations of
`SortRedAppDF` fail, so it matters that they are checked. -/

/-- A Π-type is never `⊢₀`-typed at `Prop`: its `⊢₀` type is `.sort (.imax u v)`, and `≡₀` is
syntactic. -/
theorem forallE_not_prop0 {Γ : List VExpr} {A B : VExpr} :
    ¬ env.HasTypeN U 0 Γ (.forallE A B) (.sort .zero) := by
  intro h
  obtain ⟨u, v, _, _, _, _, hc⟩ := h.forallE_inv
  exact nomatch IsDefEqN.zero_iff.1 hc

/-- **`proofIrrel` can never fire on the function position of `appDF`.**  Its subject must be
`⊢₀`-typed at a proposition, and a `⊢₀`-typed term at a Π-type has that Π-type as its *only*
`⊢₀` type. -/
theorem proofIrrel_not_at_pi {Γ : List VExpr} {p f A B : VExpr}
    (hp : env.HasTypeN U 0 Γ p (.sort .zero)) (hf : env.HasTypeN U 0 Γ f p)
    (hf' : env.HasTypeN U 0 Γ f (.forallE A B)) : False :=
  forallE_not_prop0 (HasTypeN.uniq_zero hf hf' ▸ hp)

/-- **`lamDF` cannot separate the domains.**  Two λs `⊢₀`-typed at one Π-type have that type's
domain as their own, and their bodies are `⊢₀`-typed at that type's codomain — so the `lamDF`
route to a counterexample has no freedom in `A`. -/
theorem lam_pair_at_one_type {Γ : List VExpr} {A₁ A₂ e₁ e₂ A B : VExpr}
    (h1 : env.HasTypeN U 0 Γ (.lam A₁ e₁) (.forallE A B))
    (h2 : env.HasTypeN U 0 Γ (.lam A₂ e₂) (.forallE A B)) :
    A₁ = A ∧ A₂ = A ∧ env.HasTypeN U 0 Γ (.lam A e₁) (.forallE A B) ∧
      env.HasTypeN U 0 Γ (.lam A e₂) (.forallE A B) := by
  obtain ⟨_, B₁, _, _, hc1⟩ := h1.lam_inv
  obtain ⟨_, B₂, _, _, hc2⟩ := h2.lam_inv
  injection IsDefEqN.zero_iff.1 hc1 with hA1 _
  injection IsDefEqN.zero_iff.1 hc2 with hA2 _
  exact ⟨hA1, hA2, hA1 ▸ h1, hA2 ▸ h2⟩

/-! ## 6. What `SortRed` forces on the `⊢₀` type, and the resulting split of the residual -/

/-- **A `⊢₀`-typed term that weak-head reduces to a sort has a sort as its type**, and the
level is pinned.  Subject reduction (`HeadBeta.hasTypeN_zero`) plus `≡₀ = ` syntactic
equality. -/
theorem SortRed.hasTypeN_zero_type (henv : Ordered env) {Γ : List VExpr} {X : VExpr}
    {u : VLevel} (h : SortRed u X) :
    ∀ {T : VExpr}, env.HasTypeN U 0 Γ X T → ∃ v, v ≈ u ∧ T = .sort (.succ v) := by
  induction h with
  | @sort v hv => intro T hX; exact ⟨v, hv, (IsDefEqN.zero_iff.1 hX.sort_inv.2).symm⟩
  | step hb _ ih => intro T hX; exact ih (hb.hasTypeN_zero henv hX)

/-- Instantiation produces a sort only in the two obvious ways. -/
theorem inst_eq_sort {B a : VExpr} {w : VLevel} (h : B.inst a = .sort w) :
    B = .sort w ∨ (B = .bvar 0 ∧ a = .sort w) := by
  cases B with
  | bvar i =>
    cases i with
    | zero => exact .inr ⟨rfl, by simpa [VExpr.inst] using h⟩
    | succ k => exact absurd h (by simp [VExpr.inst])
  | sort v => exact .inl (by simpa [VExpr.inst] using h)
  | const => exact absurd h (by simp [VExpr.inst])
  | app => exact absurd h (by simp [VExpr.inst])
  | lam => exact absurd h (by simp [VExpr.inst])
  | forallE => exact absurd h (by simp [VExpr.inst])

/-- **The codomain of a `SortRed`-ing application is one of exactly two shapes.**  Either the
codomain is a closed sort, or it is the bound variable itself and the argument *is* a sort. -/
theorem SortRed.app_codomain (henv : Ordered env) {Γ : List VExpr} {f a A B : VExpr}
    {u : VLevel} (hf : env.HasTypeN U 0 Γ f (.forallE A B)) (ha : env.HasTypeN U 0 Γ a A)
    (h : SortRed u (.app f a)) :
    ∃ v, v ≈ u ∧ (B = .sort (.succ v) ∨
      (B = .bvar 0 ∧ a = .sort (.succ v) ∧ A = .sort (.succ (.succ v)))) := by
  obtain ⟨v, hv, hT⟩ := h.hasTypeN_zero_type henv (Stratified.app hf ha)
  refine ⟨v, hv, ?_⟩
  rcases inst_eq_sort hT with hB | ⟨hB, hA⟩
  · exact .inl hB
  · subst hB; subst hA
    exact .inr ⟨rfl, rfl, (IsDefEqN.zero_iff.1 ha.sort_inv.2).symm⟩

/-! ### The directed form, and the two branches -/

/-- One direction suffices: the premises of the residual are symmetric. -/
def SortRedAppDF' (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A B : VExpr} {u : VLevel},
    env.IsDefEqN U (n+1) Γ f f' → env.HasTypeN U n Γ f (.forallE A B) →
    env.HasTypeN U n Γ f' (.forallE A B) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    SortRed u (.app f a) → SortRed u (.app f' a')

theorem sortRedAppDF_of_directed (h : SortRedAppDF' env U n) : SortRedAppDF env U n :=
  fun hff' hf hf' haa' ha ha' =>
    ⟨h hff' hf hf' haa' ha ha', h (.symm hff') hf' hf (.symm haa') ha' ha⟩

/-- The branch in which the codomain is a closed sort. -/
def SortRedAppDFSort (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A : VExpr} {w u : VLevel},
    env.IsDefEqN U (n+1) Γ f f' → env.HasTypeN U n Γ f (.forallE A (.sort w)) →
    env.HasTypeN U n Γ f' (.forallE A (.sort w)) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    SortRed u (.app f a) → SortRed u (.app f' a')

/-- The branch in which the codomain is the bound variable — `f : ∀ X, X`. -/
def SortRedAppDFVar (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A : VExpr} {u : VLevel},
    env.IsDefEqN U (n+1) Γ f f' → env.HasTypeN U n Γ f (.forallE A (.bvar 0)) →
    env.HasTypeN U n Γ f' (.forallE A (.bvar 0)) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    SortRed u (.app f a) → SortRed u (.app f' a')

/-- **The residual splits into exactly two branches at the base index.** -/
theorem sortRedAppDF'_of_split (henv : Ordered env) (h1 : SortRedAppDFSort env U 0)
    (h2 : SortRedAppDFVar env U 0) : SortRedAppDF' env U 0 := by
  intro Γ f f' a a' A B u hff' hf hf' haa' ha ha' hs
  obtain ⟨v, _, hB | ⟨hB, _, _⟩⟩ := hs.app_codomain henv hf ha
  · subst hB; exact h1 hff' hf hf' haa' ha ha' hs
  · subst hB; exact h2 hff' hf hf' haa' ha ha' hs

theorem sortRedAppDF_of_split (henv : Ordered env) (h1 : SortRedAppDFSort env U 0)
    (h2 : SortRedAppDFVar env U 0) : SortRedAppDF env U 0 :=
  sortRedAppDF_of_directed (sortRedAppDF'_of_split henv h1 h2)

/-- **The `∀ X, X` branch is circular against clause (1).**  If it holds and its left premise
ever fires, it *proves* that the right-hand argument is syntactically a sort — a sort-shape
statement about a `⊢ₙ₊₁` conversion, which is the content clause (1) was to supply.  So this
branch is either vacuous or at least as strong as what it is being used to prove. -/
theorem sortRedAppDFVar_forces_sort_arg (henv : Ordered env) (h : SortRedAppDFVar env U 0)
    {Γ : List VExpr} {f f' a a' A : VExpr} {u : VLevel}
    (hff' : env.IsDefEqN U 1 Γ f f') (hf : env.HasTypeN U 0 Γ f (.forallE A (.bvar 0)))
    (hf' : env.HasTypeN U 0 Γ f' (.forallE A (.bvar 0)))
    (haa' : env.IsDefEqN U 1 Γ a a') (ha : env.HasTypeN U 0 Γ a A)
    (ha' : env.HasTypeN U 0 Γ a' A) (hs : SortRed u (.app f a)) :
    ∃ v, v ≈ u ∧ a' = .sort (.succ v) := by
  obtain ⟨v, hv, hB⟩ := (h hff' hf hf' haa' ha ha' hs).app_codomain henv hf' ha'
  rcases hB with hB | ⟨_, ha2, _⟩
  · exact absurd hB (by simp)
  · exact ⟨v, hv, ha2⟩

/-! ## 7. Non-vacuity: everything replayed over `propLoopEnv`

The convention of `Theory/Typing/SortClauses.lean` §2: nothing is left standing only over `∅`,
where the `const` case of every induction is empty.  All of the following use the witness
environment's constant `A` as the proposition. -/

namespace PropLoopWitness

/-- A context holding one proof of the environment's proposition `A`. -/
def pctx : List VExpr := [.const `A []]

theorem pproof {Γ : List VExpr} : propLoopEnv.HasTypeN U 0 (.const `A [] :: Γ) (.bvar 0)
    (.const `A []) := .bvar (Lookup.zero' rfl)

theorem pproof' : propLoopEnv.HasTypeN U 0 (.const `A [] :: pctx) (.bvar 1) (.const `A []) :=
  .bvar (Lookup.succ' (Lookup.zero' rfl) rfl)

/-- The identity on `A`. -/
def pidA : VExpr := .lam (.const `A []) (.bvar 0)
/-- The function on `A` constant at the ambient proof. -/
def pconstA : VExpr := .lam (.const `A []) (.bvar 1)

theorem pidA_type : propLoopEnv.HasTypeN U 0 pctx pidA propArrow :=
  .lam propLoopEnv_constA pproof

theorem pconstA_type : propLoopEnv.HasTypeN U 0 pctx pconstA propArrow :=
  .lam propLoopEnv_constA pproof'

/-- Proof irrelevance at the environment's own proposition identifies them. -/
theorem pidA_conv : propLoopEnv.IsDefEqN U 1 pctx pidA pconstA :=
  .lamDF .rfl (.proofIrrel propLoopEnv_constA pproof pproof')

theorem papp_pidA : SortRed .zero (.app pidA (.sort .zero)) := .step .beta (.sort rfl)

theorem papp_pconstA_not : ¬ SortRed .zero (.app pconstA (.sort .zero)) := by
  intro h
  cases h with
  | step hb hY =>
    cases hb with
    | beta => exact SortRed.not_bvar hY
    | app hb => exact absurd hb HeadBeta.not_lam

/-- **§3 and §4 replayed over a non-empty environment.**  The two λs are `⊢₀`-typed at one
Π-type built from the environment's constant, they are `⊢₁`-convertible, and one argument
separates them — so the typing-free spine strengthening is false here too, and the argument
typing premise of the residual is load-bearing here too. -/
theorem propLoopEnv_spineInv_one_false : ¬ SpineInv propLoopEnv 1 1 := fun h =>
  papp_pconstA_not
    ((h pidA_conv (as := [.sort .zero]) (as' := [.sort .zero])
      (List.Forall₂.cons .rfl .nil)).1 papp_pidA)

theorem propLoopEnv_sortRedAppDF_needs_arg_typing :
    propLoopEnv.IsDefEqN 1 1 pctx pidA pconstA ∧
    propLoopEnv.HasTypeN 1 0 pctx pidA propArrow ∧
    propLoopEnv.HasTypeN 1 0 pctx pconstA propArrow ∧
    propLoopEnv.HasTypeN 1 0 pctx (.sort .zero) (.sort (.succ .zero)) ∧
    ¬ (SortRed .zero (.app pidA (.sort .zero)) ↔ SortRed .zero (.app pconstA (.sort .zero))) :=
  ⟨pidA_conv, pidA_type, pconstA_type, .sort trivial,
    fun h => papp_pconstA_not (h.1 papp_pidA)⟩

/-- **§6's type-forcing lemma fires** at a term that really does weak-head reduce, over the
witness environment, with the environment's constant in the domain. -/
theorem propLoopEnv_sortRed_beta :
    SortRed .zero (.app (.lam (.const `A []) (.sort .zero)) (VExpr.bvar 0)) :=
  .step .beta (.sort rfl)

theorem propLoopEnv_beta_type :
    propLoopEnv.HasTypeN 1 0 pctx (.app (.lam (.const `A []) (.sort .zero)) (.bvar 0))
      (.sort (.succ .zero)) :=
  Stratified.app (A := .const `A []) (B := .sort (.succ .zero))
    (.lam propLoopEnv_constA (.sort (l := .zero) trivial)) pproof

theorem propLoopEnv_hasTypeN_zero_type_fires :
    ∃ v, v ≈ VLevel.zero ∧ (VExpr.sort (.succ .zero) : VExpr) = .sort (.succ v) :=
  propLoopEnv_sortRed_beta.hasTypeN_zero_type propLoopEnv_wf.ordered propLoopEnv_beta_type

/-- **§5's `lam_pair_at_one_type` fires** at two *different* λs sharing one Π-type over the
witness environment. -/
theorem propLoopEnv_lam_pair_fires :
    (VExpr.const `A [] = .const `A []) ∧ (VExpr.const `A [] = .const `A []) ∧
      propLoopEnv.HasTypeN 1 0 pctx pidA propArrow ∧
      propLoopEnv.HasTypeN 1 0 pctx pconstA propArrow :=
  lam_pair_at_one_type pidA_type pconstA_type

/-- **§5's `proofIrrel_not_at_pi` fires**: the identity on `A` is not a proof of any
proposition of the witness environment. -/
theorem propLoopEnv_pidA_not_proof {p : VExpr}
    (hp : propLoopEnv.HasTypeN 1 0 pctx p (.sort .zero))
    (hf : propLoopEnv.HasTypeN 1 0 pctx pidA p) : False :=
  proofIrrel_not_at_pi hp hf pidA_type

/-- §1 over the same environment. -/
theorem propLoopEnv_sortRedInv_one_of_appDF (h1 : SortRedAppDF propLoopEnv U 0) :
    SortRedInv propLoopEnv U 1 :=
  fun hc => sortRedInv_of hc 0 rfl h1 (PiTypedNotSortRed.zero propLoopEnv_wf.ordered)
    (ProofNotSortRed.zero propLoopEnv_wf.ordered) ExtraSortRed.propLoopEnv rfl _

theorem propLoopEnv_sortRedAppDF_iff :
    SortRedAppDF propLoopEnv U 0 ↔ SortRedInv propLoopEnv U 1 :=
  ⟨propLoopEnv_sortRedInv_one_of_appDF, sortRedAppDF_of_sortRedInv⟩

end PropLoopWitness

/-! ## 8. The `∀ X, X` branch is vacuous — one of the two branches, discharged -/

/-- Reflexive-transitive weak-head β reduction. -/
inductive HeadBetaS : VExpr → VExpr → Prop
  | refl {X : VExpr} : HeadBetaS X X
  | head {X Y Z : VExpr} : HeadBeta X Y → HeadBetaS Y Z → HeadBetaS X Z

theorem HeadBetaS.hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {X Y : VExpr}
    (h : HeadBetaS X Y) : ∀ {T : VExpr}, env.HasTypeN U 0 Γ X T → env.HasTypeN U 0 Γ Y T := by
  induction h with
  | refl => exact id
  | head hb _ ih => exact fun hX => ih (hb.hasTypeN_zero henv hX)

/-- **A `SortRed`-ing application exposes a λ in the function.**  Weak-head reduction of
`.app f a` reduces `f` in place until it is a λ and then contracts; so the whole reduction
factors. -/
theorem SortRed.app_head {f a : VExpr} {u : VLevel} (h : SortRed u (.app f a)) :
    ∃ C e, HeadBetaS f (.lam C e) ∧ SortRed u (e.inst a) := by
  generalize hZ : VExpr.app f a = Z at h
  induction h generalizing f with
  | sort => exact absurd hZ (by simp)
  | @step X Y hb _ ih =>
    subst hZ
    cases hb with
    | @beta C e _ => exact ⟨C, e, .refl, by assumption⟩
    | @app _ f₁ _ hb' =>
      obtain ⟨C, e, hr, hs⟩ := ih rfl
      exact ⟨C, e, .head hb' hr, hs⟩

/-- Inversion for a weak-head step on an application. -/
theorem HeadBeta.app_inv {g b Y : VExpr} (h : HeadBeta (.app g b) Y) :
    (∃ C d, g = .lam C d ∧ Y = d.inst b) ∨ (∃ g', HeadBeta g g' ∧ Y = .app g' b) := by
  cases h with
  | beta => exact .inl ⟨_, _, rfl, rfl⟩
  | app hb => exact .inr ⟨_, hb, rfl⟩

/-- Substituting a **sort** creates no new head redexes, so weak-head reduction of
`X.inst (.sort w)` is exactly weak-head reduction of `X`. -/
theorem headBeta_inst_sort {X Y : VExpr} {w : VLevel}
    (h : HeadBeta (X.inst (.sort w)) Y) : ∃ X', HeadBeta X X' ∧ Y = X'.inst (.sort w) := by
  induction X generalizing Y with
  | bvar i =>
    cases i with
    | zero => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_sort)
    | succ k => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_bvar)
  | sort => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_sort)
  | const => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_const)
  | lam => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_lam)
  | forallE => exact absurd h (by simpa [VExpr.inst] using HeadBeta.not_forallE)
  | app f b ihf _ =>
    simp only [VExpr.inst] at h
    rcases h.app_inv with ⟨C, d, hlam, rfl⟩ | ⟨g', hb, rfl⟩
    · cases f with
      | lam C₀ d₀ =>
        simp only [VExpr.inst] at hlam
        injection hlam with _ hd
        subst hd
        exact ⟨d₀.inst b, .beta, (VExpr.inst0_inst_hi d₀ b (.sort w) 0).symm⟩
      | bvar i => cases i <;> simp [VExpr.inst] at hlam
      | sort => simp [VExpr.inst] at hlam
      | const => simp [VExpr.inst] at hlam
      | app => simp [VExpr.inst] at hlam
      | forallE => simp [VExpr.inst] at hlam
    · obtain ⟨f', hf', rfl⟩ := ihf hb
      exact ⟨.app f' b, .app hf', rfl⟩

/-- Hence a term that weak-head reduces to a sort **after** a sort is substituted for its
`.bvar 0` already weak-head reduces, before the substitution, to a sort or to `.bvar 0`. -/
theorem sortRed_inst_sort {X : VExpr} {w u : VLevel} (h : SortRed u (X.inst (.sort w))) :
    ∃ W, HeadBetaS X W ∧ ((∃ v, W = .sort v) ∨ W = .bvar 0) := by
  generalize hZ : X.inst (.sort w) = Z at h
  induction h generalizing X with
  | @sort v hv =>
    refine ⟨X, .refl, ?_⟩
    rcases inst_eq_sort hZ with hB | ⟨hB, _⟩
    · exact .inl ⟨v, hB⟩
    · exact .inr hB
  | step hb _ ih =>
    subst hZ
    obtain ⟨X', hX', rfl⟩ := headBeta_inst_sort hb
    obtain ⟨W, hW, hs⟩ := ih rfl
    exact ⟨W, .head hX' hW, hs⟩

theorem lift_ne_bvar_zero {A : VExpr} : A.lift ≠ .bvar 0 := by
  cases A <;> simp [VExpr.liftN, liftVar]

/-- **No `⊢₀`-typed term has the bound variable as its type and weak-head reduces to a sort
after that variable is instantiated by a sort.**  This is what makes the `∀ X, X` branch of
§6 vacuous. -/
theorem not_sortRed_inst_of_bvar_type (henv : Ordered env) {Γ : List VExpr} {A e : VExpr}
    {w u : VLevel} (he : env.HasTypeN U 0 (A::Γ) e (.bvar 0)) :
    ¬ SortRed u (e.inst (.sort w)) := by
  intro h
  obtain ⟨W, hW, hs⟩ := sortRed_inst_sort h
  have hWt := hW.hasTypeN_zero henv he
  rcases hs with ⟨v, rfl⟩ | rfl
  · exact absurd (IsDefEqN.zero_iff.1 hWt.sort_inv.2) (by simp)
  · obtain ⟨T, hl, hc⟩ := hWt.bvar_inv
    cases hl
    exact lift_ne_bvar_zero (IsDefEqN.zero_iff.1 hc)

/-- **The `∀ X, X` branch of §6 has no instances at all**, over any ordered environment: its
`SortRed u (.app f a)` premise is unsatisfiable.  So the branch holds vacuously, and with it
the circularity of `sortRedAppDFVar_forces_sort_arg` is removed. -/
theorem sortRedAppDFVar_premise_empty (henv : Ordered env) {Γ : List VExpr} {f a A : VExpr}
    {u : VLevel} (hf : env.HasTypeN U 0 Γ f (.forallE A (.bvar 0)))
    (ha : env.HasTypeN U 0 Γ a A) : ¬ SortRed u (.app f a) := by
  intro h
  obtain ⟨v, _, hB | ⟨_, rfl, _⟩⟩ := h.app_codomain henv hf ha
  · exact absurd hB (by simp)
  obtain ⟨C, e, hr, hs⟩ := h.app_head
  have hlam := hr.hasTypeN_zero henv hf
  obtain ⟨_, B, _, he, hc⟩ := hlam.lam_inv
  injection IsDefEqN.zero_iff.1 hc with hC hB
  subst hC; subst hB
  exact not_sortRed_inst_of_bvar_type henv he hs

theorem sortRedAppDFVar_vacuous (henv : Ordered env) : SortRedAppDFVar env U 0 :=
  fun _ hf _ _ ha _ hs => absurd hs (sortRedAppDFVar_premise_empty henv hf ha)

/-- **One of the two branches is gone.**  `SortRedAppDF env U 0` — the residual of both
surviving clauses — is now *exactly* its closed-sort-codomain branch. -/
theorem sortRedAppDF_of_sortBranch (henv : Ordered env) (h1 : SortRedAppDFSort env U 0) :
    SortRedAppDF env U 0 :=
  sortRedAppDF_of_split henv h1 (sortRedAppDFVar_vacuous henv)

theorem empty_sortInvN_one_of_sortBranch (h1 : SortRedAppDFSort ∅ 1 0) : SortInvN ∅ 1 1 :=
  empty_sortInvN_one_of_appDF (sortRedAppDF_of_sortBranch .empty h1)

theorem empty_sortForallEDisjN_one_of_sortBranch (h1 : SortRedAppDFSort ∅ 1 0) :
    SortForallEDisjN ∅ 1 1 :=
  empty_sortForallEDisjN_one_of_appDF (sortRedAppDF_of_sortBranch .empty h1)

/-! ## 9. What the surviving branch says, in one sentence -/

theorem HeadBetaS.app {f f₁ a : VExpr} (h : HeadBetaS f f₁) :
    HeadBetaS (.app f a) (.app f₁ a) := by
  induction h with
  | refl => exact .refl
  | head hb _ ih => exact .head (.app hb) ih

theorem SortRed.of_headBetaS {X Y : VExpr} {u : VLevel} (h : HeadBetaS X Y) :
    SortRed u Y → SortRed u X := by
  induction h with
  | refl => exact id
  | head hb _ ih => exact fun hY => .step hb (ih hY)

/-- **Weak-head λ-exposure is invariant along a `⊢ₙ₊₁` conversion at a Π-type**, and the
exposed bodies agree on `SortRed` after the two arguments are substituted.  This is what is
left of clauses (1) and (3) at index 1 — nothing else. -/
def SortRedLamExpose (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A e : VExpr} {w u : VLevel},
    env.IsDefEqN U (n+1) Γ f f' → env.HasTypeN U n Γ f (.forallE A (.sort w)) →
    env.HasTypeN U n Γ f' (.forallE A (.sort w)) →
    env.IsDefEqN U (n+1) Γ a a' → env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    HeadBetaS f (.lam A e) → SortRed u (e.inst a) →
    ∃ e', HeadBetaS f' (.lam A e') ∧ SortRed u (e'.inst a')

private theorem lam_dom_eq (henv : Ordered env) {Γ : List VExpr} {f C e A B : VExpr}
    (hf : env.HasTypeN U 0 Γ f (.forallE A B)) (hr : HeadBetaS f (.lam C e)) : C = A :=
  let ⟨_, _, _, _, hc⟩ := (hr.hasTypeN_zero henv hf).lam_inv
  (by injection IsDefEqN.zero_iff.1 hc)

theorem sortRedAppDFSort_of_lamExpose (henv : Ordered env) (h : SortRedLamExpose env U 0) :
    SortRedAppDFSort env U 0 := by
  intro Γ f f' a a' A w u hff' hf hf' haa' ha ha' hs
  obtain ⟨C, e, hr, hbody⟩ := hs.app_head
  cases lam_dom_eq henv hf hr
  obtain ⟨e', hr', hbody'⟩ := h hff' hf hf' haa' ha ha' hr hbody
  exact SortRed.of_headBetaS (HeadBetaS.app hr') (.step .beta hbody')

theorem lamExpose_of_sortRedAppDFSort (henv : Ordered env) (h : SortRedAppDFSort env U 0) :
    SortRedLamExpose env U 0 := by
  intro Γ f f' a a' A e w u hff' hf hf' haa' ha ha' hr hbody
  have hs : SortRed u (.app f a) :=
    SortRed.of_headBetaS (HeadBetaS.app hr) (.step .beta hbody)
  obtain ⟨C, e', hr', hbody'⟩ := (h hff' hf hf' haa' ha ha' hs).app_head
  cases lam_dom_eq henv hf' hr'
  exact ⟨e', hr', hbody'⟩

theorem sortRedAppDFSort_iff_lamExpose (henv : Ordered env) :
    SortRedAppDFSort env U 0 ↔ SortRedLamExpose env U 0 :=
  ⟨lamExpose_of_sortRedAppDFSort henv, sortRedAppDFSort_of_lamExpose henv⟩

/-- **The whole of what is left, at index 1 over `∅`.** -/
theorem empty_sortInvN_one_of_lamExpose (h : SortRedLamExpose ∅ 1 0) : SortInvN ∅ 1 1 :=
  empty_sortInvN_one_of_sortBranch (sortRedAppDFSort_of_lamExpose .empty h)

theorem empty_sortForallEDisjN_one_of_lamExpose (h : SortRedLamExpose ∅ 1 0) :
    SortForallEDisjN ∅ 1 1 :=
  empty_sortForallEDisjN_one_of_sortBranch (sortRedAppDFSort_of_lamExpose .empty h)

/-! ## 10. Non-vacuity of §§8–9, over `propLoopEnv` -/

namespace PropLoopWitness

/-- The `∀ X, X` type at the first universe, and a context holding a variable of it together
with a proof of the environment's proposition `A` — so the context is environment-dependent
and the `const` case is not empty. -/
def paradox : VExpr := .forallE (.sort (.succ .zero)) (.bvar 0)

def qctx : List VExpr := [paradox, .const `A []]

theorem qvar : propLoopEnv.HasTypeN 1 0 qctx (.bvar 0) paradox :=
  .bvar (Lookup.zero' rfl)

/-- **`sortRedAppDFVar_premise_empty` fires**: the paradoxical variable, applied to a sort,
does not weak-head reduce to a sort — over an environment with constants, at a context that
mentions one. -/
theorem propLoopEnv_var_branch_fires {u : VLevel} :
    ¬ SortRed u (.app (.bvar 0) (.sort .zero)) :=
  sortRedAppDFVar_premise_empty propLoopEnv_wf.ordered qvar (.sort trivial)

/-- The constant function to `Prop`, over the witness environment. -/
def kProp : VExpr := .lam (.const `A []) (.sort .zero)
/-- …wrapped in one β-redex, so it is `⊢₁`-convertible to `kProp` and is not a λ. -/
def kProp' : VExpr := .app (.lam (.const `A []) kProp) (.bvar 0)

theorem kProp_type {Γ : List VExpr} :
    propLoopEnv.HasTypeN U 0 Γ kProp (.forallE (.const `A []) (.sort (.succ .zero))) :=
  .lam propLoopEnv_constA (.sort trivial)

theorem kProp'_type :
    propLoopEnv.HasTypeN 1 0 pctx kProp' (.forallE (.const `A []) (.sort (.succ .zero))) :=
  Stratified.app (A := .const `A []) (B := .forallE (.const `A []) (.sort (.succ .zero)))
    (.lam propLoopEnv_constA kProp_type) pproof

theorem kProp_conv : propLoopEnv.IsDefEqN 1 1 pctx kProp kProp' :=
  .symm (Stratified.beta (A := .const `A []) (e := kProp) (e' := .bvar 0) kProp_type pproof)

/-- **The surviving residual `SortRedLamExpose` is not premise-empty**, over an environment
with constants: here are two `⊢₁`-convertible, syntactically different functions `⊢₀`-typed at
one Π-type whose domain is the environment's own proposition, at which every premise of the
residual holds — and its conclusion is true. -/
theorem propLoopEnv_lamExpose_instance :
    propLoopEnv.IsDefEqN 1 1 pctx kProp kProp' ∧ kProp ≠ kProp' ∧
    propLoopEnv.HasTypeN 1 0 pctx kProp (.forallE (.const `A []) (.sort (.succ .zero))) ∧
    propLoopEnv.HasTypeN 1 0 pctx kProp' (.forallE (.const `A []) (.sort (.succ .zero))) ∧
    HeadBetaS kProp (.lam (.const `A []) (.sort .zero)) ∧
    SortRed .zero ((VExpr.sort .zero).inst (.bvar 0)) ∧
    HeadBetaS kProp' (.lam (.const `A []) (.sort .zero)) ∧
    SortRed .zero ((VExpr.sort .zero).inst (.bvar 0)) :=
  ⟨kProp_conv, by simp [kProp, kProp'], kProp_type, kProp'_type, .refl, .sort rfl,
    .head .beta .refl, .sort rfl⟩

/-- §§8–9 over the same environment. -/
theorem propLoopEnv_sortInvN_one_of_lamExpose (h : SortRedLamExpose propLoopEnv U 0) :
    SortInvN propLoopEnv U 1 :=
  propLoopEnv_sortRedInv_one_of_appDF
    (sortRedAppDF_of_sortBranch propLoopEnv_wf.ordered
      (sortRedAppDFSort_of_lamExpose propLoopEnv_wf.ordered h))
    |> sortInvN_of_sortRedInv

theorem propLoopEnv_sortForallEDisjN_one_of_lamExpose (h : SortRedLamExpose propLoopEnv U 0) :
    SortForallEDisjN propLoopEnv U 1 :=
  propLoopEnv_sortRedInv_one_of_appDF
    (sortRedAppDF_of_sortBranch propLoopEnv_wf.ordered
      (sortRedAppDFSort_of_lamExpose propLoopEnv_wf.ordered h))
    |> sortForallEDisjN_of_sortRedInv

end PropLoopWitness

/-! ## 11. The chain, assembled -/

theorem sortRedAppDFSort_of_sortRedAppDF (h : SortRedAppDF env U n) :
    SortRedAppDFSort env U n :=
  fun hff' hf hf' haa' ha ha' hs => (h hff' hf hf' haa' ha ha').1 hs

theorem sortRedAppDF_iff_sortBranch (henv : Ordered env) :
    SortRedAppDF env U 0 ↔ SortRedAppDFSort env U 0 :=
  ⟨sortRedAppDFSort_of_sortRedAppDF, sortRedAppDF_of_sortBranch henv⟩

/-- **The full chain at index 1 over `∅`.**  Every link is an equivalence, so nothing has been
weakened along the way and nothing has been strengthened: `SortRedLamExpose ∅ 1 0` *is* the
open goal. -/
theorem empty_chain :
    (SortRedLamExpose ∅ 1 0 ↔ SortRedAppDFSort ∅ 1 0) ∧
    (SortRedAppDFSort ∅ 1 0 ↔ SortRedAppDF ∅ 1 0) ∧
    (SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1) :=
  ⟨(sortRedAppDFSort_iff_lamExpose .empty).symm, (sortRedAppDF_iff_sortBranch .empty).symm,
    empty_sortRedAppDF_iff⟩

end VEnv
end Lean4Lean
