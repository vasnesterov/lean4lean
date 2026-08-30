import Lean4Lean.Theory.Typing.SubstCRefute

/-!
# Pricing the hereditary shape agreement

`Theory/Typing/UniqueTypingN.lean` reduces `SortForallEDisjoint` to its one open case,
`SortForallEDisjoint.AppCase`, and `docs/handoff-stratified.md` §9 names what that case seems
to want:

> the types of a term agree on shape, **and** their codomains agree on shape after
> instantiation at any argument typed at both domains.

This file prices that statement.  Two facts, both machine-checked here, settle it:

1. **In the form that is usable — *disjointness* — the hereditary statement is `logically
   equivalent` to `SortForallEDisjoint` itself** (`SortForallEDisjointH.iff`).  It is not a
   strengthening at all.  The reason is one lemma, `Apply.hasType`: a spine peeled off a type
   of `e` is a type of the *applied term* `e a₁ ⋯ aₖ`, so quantifying over spines quantifies
   over terms, which the original statement already does.
2. **In the form that would be a genuine strengthening — *agreement*, an `iff` of shape
   predicates — the statement is FALSE** (`typeShapeAgree_false`), at `n = 1` over the empty
   environment, by the counterexample already in `Theory/Typing/SubstCRefute.lean`.

The two are the same content stated two ways, and the criterion in §5 of the handoff sorts
them the way it sorts everything else: the composable form is the `iff`, and the `iff` is
false; the true form is the negation, and it does not compose (see the module note at the end,
which is analysis, not machine-checked).

3. What survives is the *type-level* disjointness `SubstDisj` — not equivalent to
   `SortForallEDisjoint`, since it is about two types with no common term — together with
   `SubstDisj.zero` (it is satisfiable) and `applyDisj` (with `DefInv` it gives spine
   determinism at a type, which is what a `bvar` case needs — but **`DefInv` is refuted, and
   `applyDisj` consumes the refuted clause, so at `∅` and `n = 1` this half is now void**; see
   the note on `applyDisj` itself).  It is **not** shown sufficient:
   a spine induction on typing closes `app` and `bvar` but not `lam`, where bridging the two
   codomains of the body's two types needs an existence step that only the refuted `∀∃` form
   supplies.  That last sentence is analysis, not machine-checked.

`AppCase` itself is *not* the obstruction: it follows from `SortForallEDisjoint` in one line
(`SortForallEDisjoint.appCase`), because `Stratified.app` already gives the application the
type `B₀.inst a`.  So the app case of `sortForallEDisjoint_of` is the statement's own
fixpoint, and nothing that is equivalent to the statement can break it.
-/

namespace Lean4Lean

namespace VExpr

/-- `mkApps e [a₁, …, aₖ] = e a₁ ⋯ aₖ`. -/
def mkApps : VExpr → List VExpr → VExpr
  | e, [] => e
  | e, a :: as => mkApps (.app e a) as

@[simp] theorem mkApps_nil (e : VExpr) : mkApps e [] = e := rfl
@[simp] theorem mkApps_cons (e a : VExpr) (as : List VExpr) :
    mkApps e (a :: as) = mkApps (.app e a) as := rfl

end VExpr

namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## Spines

`Apply Γ T args R` peels `args` off the type `T`, each argument typed at the domain it is
peeled at, leaving `R`.  Both the head and the result are taken up to `⊢ₙ`-conversion, which
is what makes the relation invariant under retyping (`Apply.conv_head`). -/

inductive Apply (env : VEnv) (U n : Nat) (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | nil {T R : VExpr} : env.IsDefEqN U n Γ T R → Apply env U n Γ T [] R
  | cons {T A B a R : VExpr} {args : List VExpr} :
    env.IsDefEqN U n Γ T (.forallE A B) → env.HasTypeN U n Γ a A →
    Apply env U n Γ (B.inst a) args R → Apply env U n Γ T (a :: args) R

/-- A spine only ever sees its head through a conversion, so converting the head is free.
This is why no reformulation of the hereditary statement can gain anything at `trans` on the
*head*: the middle term of a head conversion inherits the very same spine. -/
theorem Apply.conv_head {Γ T T' args R} (h : env.IsDefEqN U n Γ T' T)
    (H : Apply env U n Γ T args R) : Apply env U n Γ T' args R := by
  cases H with
  | nil hR => exact .nil (IsDefEqN.trans' h hR)
  | cons hpi ha hrest => exact .cons (IsDefEqN.trans' h hpi) ha hrest

/-- **The lemma that collapses the hereditary statement.**  If `e` has type `T` and the spine
`args` peels `T` down to `R`, then the *applied term* `e a₁ ⋯ aₖ` has type `R`.

So a statement quantified over "two typings of `e` and a common spine" is a statement
quantified over "two typings of a term", which is what the unstrengthened statement already
quantifies over. -/
theorem Apply.hasType {Γ e T args R} (he : env.HasTypeN U n Γ e T)
    (H : Apply env U n Γ T args R) : env.HasTypeN U n Γ (e.mkApps args) R := by
  induction H generalizing e with
  | nil hR => exact .conv hR he
  | cons hpi ha _ ih => exact ih (.app (.conv hpi he) ha)

/-! ## The hereditary statement, in the form that is usable -/

/-- **The hereditary shape *disjointness*.**  Two types of one term, a common spine peeled off
both, and the two results cannot be a sort on one side and a Π on the other.

This is the statement `SortForallEDisjoint.AppCase` was said to need: shape agreement of the
types of `f`, propagated to the codomains after instantiation at an argument typed at both
domains.  The spine formulation is the hereditary one — `args = []` is the shape agreement of
the types themselves, `args = [a]` is the codomain clause, and longer spines iterate it. -/
def SortForallEDisjointH (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T₁ T₂ R₁ R₂ A B : VExpr} {args : List VExpr} {u : VLevel},
    env.HasTypeN U n Γ e T₁ → env.HasTypeN U n Γ e T₂ →
    Apply env U n Γ T₁ args R₁ → Apply env U n Γ T₂ args R₂ →
    env.IsDefEqN U n Γ R₁ (.sort u) → env.IsDefEqN U n Γ R₂ (.forallE A B) → False

/-- **The hereditary strengthening is not a strengthening.**  `SortForallEDisjointH` and
`SortForallEDisjoint` are logically equivalent, and both directions are one step.

* `→` is the spine of length zero;
* `←` is `Apply.hasType`: the two spine results are two types of the applied term.

**Consequence for the route.**  Nothing that is equivalent to `SortForallEDisjoint` can close
`SortForallEDisjoint.AppCase` — see `SortForallEDisjoint.appCase`, which derives `AppCase`
from the statement itself.  A hereditary *disjointness* is therefore not the missing
primitive; the only strengthening in the neighbourhood is the *agreement* form, refuted
below. -/
theorem SortForallEDisjointH.iff :
    env.SortForallEDisjointH U n ↔ env.SortForallEDisjoint U n := by
  constructor
  · intro h _ _ _ _ _ h1 h2
    exact h h1 h2 (.nil .rfl) (.nil .rfl) .rfl .rfl
  · intro h _ _ _ _ _ _ _ _ _ _ h1 h2 s1 s2 c1 c2
    exact h (.conv c1 (s1.hasType h1)) (.conv c2 (s2.hasType h2))

/-! ### The handoff's literal phrasing: an argument typed at **both** domains

`Apply` types each argument at the domain it is peeled at.  The handoff asks for the codomains
to agree "after instantiation at any argument typed at **both** domains", which is the *joint*
spine below — a formally weaker statement, since it has strictly more premises.  It collapses
too, and by the same lemma: a joint spine is a pair of spines. -/

/-- A joint spine: one argument list, typed at both sides' domains at every step. -/
inductive Apply₂ (env : VEnv) (U n : Nat) (Γ : List VExpr) :
    VExpr → VExpr → List VExpr → VExpr → VExpr → Prop
  | nil {T₁ T₂ R₁ R₂ : VExpr} :
    env.IsDefEqN U n Γ T₁ R₁ → env.IsDefEqN U n Γ T₂ R₂ → Apply₂ env U n Γ T₁ T₂ [] R₁ R₂
  | cons {T₁ T₂ A₁ B₁ A₂ B₂ a R₁ R₂ : VExpr} {args : List VExpr} :
    env.IsDefEqN U n Γ T₁ (.forallE A₁ B₁) → env.IsDefEqN U n Γ T₂ (.forallE A₂ B₂) →
    env.HasTypeN U n Γ a A₁ → env.HasTypeN U n Γ a A₂ →
    Apply₂ env U n Γ (B₁.inst a) (B₂.inst a) args R₁ R₂ →
    Apply₂ env U n Γ T₁ T₂ (a :: args) R₁ R₂

theorem Apply₂.left {Γ T₁ T₂ args R₁ R₂} (H : Apply₂ env U n Γ T₁ T₂ args R₁ R₂) :
    Apply env U n Γ T₁ args R₁ := by
  induction H with
  | nil h _ => exact .nil h
  | cons h1 _ ha1 _ _ ih => exact .cons h1 ha1 ih

theorem Apply₂.right {Γ T₁ T₂ args R₁ R₂} (H : Apply₂ env U n Γ T₁ T₂ args R₁ R₂) :
    Apply env U n Γ T₂ args R₂ := by
  induction H with
  | nil _ h => exact .nil h
  | cons _ h2 _ ha2 _ ih => exact .cons h2 ha2 ih

/-- The hereditary statement in the handoff's literal phrasing. -/
def SortForallEDisjointH₂ (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T₁ T₂ R₁ R₂ A B : VExpr} {args : List VExpr} {u : VLevel},
    env.HasTypeN U n Γ e T₁ → env.HasTypeN U n Γ e T₂ →
    Apply₂ env U n Γ T₁ T₂ args R₁ R₂ →
    env.IsDefEqN U n Γ R₁ (.sort u) → env.IsDefEqN U n Γ R₂ (.forallE A B) → False

/-- The joint form collapses as well: it is equivalent to `SortForallEDisjoint`, so demanding
the argument be typed at both domains buys nothing either. -/
theorem SortForallEDisjointH₂.iff :
    env.SortForallEDisjointH₂ U n ↔ env.SortForallEDisjoint U n := by
  constructor
  · intro h _ _ _ _ _ h1 h2
    exact h h1 h2 (.nil .rfl .rfl) .rfl .rfl
  · intro h _ _ _ _ _ _ _ _ _ _ h1 h2 s c1 c2
    exact h (.conv c1 (s.left.hasType h1)) (.conv c2 (s.right.hasType h2))

/-- **`AppCase` is the statement's own fixpoint.**  `Stratified.app` gives `.app f a` the type
`B₀.inst a`, and `conv` retypes it at the sort; so the app case of `sortForallEDisjoint_of`
follows from `SortForallEDisjoint` in one step.  This is why it cannot be closed by anything
that is merely equivalent to `SortForallEDisjoint`. -/
theorem SortForallEDisjoint.appCase (hd : env.SortForallEDisjoint U n) :
    SortForallEDisjoint.AppCase env U n :=
  fun hf ha hT H2 => hd (.conv hT (.app hf ha)) H2

/-! ## The statement in the form that would be a strengthening — and it is false -/

/-- `T` is *sort-shaped*: `⊢ₙ`-convertible to a sort. -/
def SortLike (env : VEnv) (U n : Nat) (Γ : List VExpr) (T : VExpr) : Prop :=
  ∃ u, env.IsDefEqN U n Γ T (.sort u)

/-- **Shape agreement**: the types of a term agree on being sort-shaped.

This is the `iff` form of "the types of a term agree on shape" — the form that *would* be a
strengthening of `SortForallEDisjoint` (it decides the shape of every type of every term,
rather than merely forbidding one pair), and the form that composes at `trans`, since an
`iff` propagated along a conversion tolerates an arbitrary middle term.

**It is false**: `typeShapeAgree_false`. -/
def TypeShapeAgree (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T₁ T₂ : VExpr},
    env.HasTypeN U n Γ e T₁ → env.HasTypeN U n Γ e T₂ →
    (env.SortLike U n Γ T₁ ↔ env.SortLike U n Γ T₂)

namespace ShapeAgreeRefute
open SubstCRefute

/-- The Π-body: `SubstCRefute`'s beta-redex `B`, whose instance at `a` is the stuck term
`lhs`. -/
def D : VExpr := .app (.lam A (.bvar 0)) (.bvar 0)

/-- The type the variable is declared at.  Closed, so `P.lift = P`. -/
def P : VExpr := .forallE A D

theorem P_lift : P.lift = P := rfl

/-- `x : ∀ (_ : A), D` in the one-element context. -/
theorem hx : (∅ : VEnv).HasTypeN 1 1 [P] (.bvar 0) P := P_lift ▸ Stratified.bvar Lookup.zero

/-- The counterexample's beta step, in the context the Π-congruence needs. -/
theorem hbeta : (∅ : VEnv).IsDefEqN 1 1 [A, P] D (.bvar 0) :=
  .beta (.bvar .zero) (.bvar .zero)

/-- `forallEDF` carries no typing premises, so the body conversion lifts to the Π for free —
the same step that refutes the instantiated form of `DefInv`'s clause (2). -/
theorem hpi : (∅ : VEnv).IsDefEqN 1 1 [P] P (.forallE A (.bvar 0)) := .forallEDF .rfl hbeta

theorem hx2 : (∅ : VEnv).HasTypeN 1 1 [P] (.bvar 0) (.forallE A (.bvar 0)) := .conv hpi hx

/-- The witness term, at its first type: `D.inst a` is `lhs`. -/
theorem happ1 : (∅ : VEnv).HasTypeN 1 1 [P] (.app (.bvar 0) a) lhs := .app hx a_hasType1

/-- The same term at its second type: `(.bvar 0).inst a` is `a`, a *sort*. -/
theorem happ2 : (∅ : VEnv).HasTypeN 1 1 [P] (.app (.bvar 0) a) a := .app hx2 a_hasType1

/-- `lhs` is `⊢₁`-related to nothing but itself, so it is not sort-shaped. -/
theorem lhs_not_sortLike {Γ : List VExpr} : ¬ (∅ : VEnv).SortLike 1 1 Γ lhs := by
  rintro ⟨u, h⟩
  exact absurd ((stuck h rfl rfl).1 rfl) (by simp [lhs])

/-- `a` is literally a sort. -/
theorem a_sortLike {Γ : List VExpr} : (∅ : VEnv).SortLike 1 1 Γ a := ⟨_, .rfl⟩

/-- **The witness context is not junk.**  `P` is a genuine Π-type: `A` is a sort and the
beta-redex `D` is typed at `.sort (succ p)` in `[A]`.  So `[P]` is a well-formed context and
the refutation does not turn on the absence of an `OnCtx` hypothesis. -/
theorem A_type {Γ : List VExpr} : (∅ : VEnv).HasTypeN 1 1 Γ A (.sort (.succ (.succ p))) :=
  Stratified.sort (l := .succ p) p_wf

theorem lam_type : (∅ : VEnv).HasTypeN 1 1 [A] (.lam A (.bvar 0)) (.forallE A A) :=
  Stratified.lam A_type (.bvar .zero)

theorem D_type : (∅ : VEnv).HasTypeN 1 1 [A] D (.sort (.succ p)) :=
  Stratified.app (A := A) (B := A) lam_type (.bvar .zero)

theorem P_type : (∅ : VEnv).HasTypeN 1 1 []
    P (.sort (.imax (.succ (.succ p)) (.succ p))) :=
  Stratified.forallE p_wf p_wf A_type D_type

end ShapeAgreeRefute

/-- **The agreement form of the hereditary shape statement is FALSE**, at `n = 1` over the
empty environment, and already at spine length zero — so no hereditary clause repairs it.

The witness is the `SubstC` counterexample, lifted from a *substituted conversion* to a *term
with two types*, which is the hypothesis `SubstCRefute` explicitly did not supply:

    P := ∀ (_ : A), (fun _ : A => x) x        x := .bvar 0,  A := .sort (succ p)

    [P] ⊢₁ .bvar 0 : P                        (the variable, at its declared type)
    [P] ⊢₁ .bvar 0 : ∀ (_ : A), .bvar 0       (retyped along `forallEDF` of the beta step)

so the single term `.app (.bvar 0) a` has the two types

    lhs = (fun _ : A => x) a   —  stuck: `⊢₁`-related to nothing but itself
    a   = .sort (max p p)      —  a sort

One is sort-shaped and the other is not.  Note what this does **not** refute: neither type is
a Π, so `SortForallEDisjoint` is untouched, and so is `PropTypeAgreeN` (`lhs` is typed at
`.sort (succ p)`, not at `Prop`).  What dies is exactly the *agreement* reading of "the types
of a term agree on shape". -/
theorem typeShapeAgree_false : ¬ (∅ : VEnv).TypeShapeAgree 1 1 := by
  intro h
  exact ShapeAgreeRefute.lhs_not_sortLike
    ((h ShapeAgreeRefute.happ2 ShapeAgreeRefute.happ1).1 ShapeAgreeRefute.a_sortLike)

/-- **Shape agreement under substitution** — the handoff's row 5, in its `iff` form.  This is
the statement the *type-level* form of the induction needs, where there is no common term:
two conversion-related bodies, instantiated at one typed argument, agree on shape. -/
def SubstShapeAgree (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B B' a : VExpr},
    env.HasTypeN U n Γ a A → env.IsDefEqN U n (A::Γ) B B' →
    (env.SortLike U n Γ (B.inst a) ↔ env.SortLike U n Γ (B'.inst a))

/-- **Row 5 of the criterion table, sharpened.**  "Shape-disjointness under substitution does
not inherit `SubstC`'s refutation" is correct for the *disjointness* form and **false for the
agreement form**: the `SubstC` counterexample refutes the `iff` directly, with no extra
construction — `B.inst a` is the stuck term and `B'.inst a` is a sort.

The two forms are not interchangeable: the `iff` is what composes at `trans` (it is
propagated along the conversion), and it is exactly the one that is false. -/
theorem substShapeAgree_false : ¬ (∅ : VEnv).SubstShapeAgree 1 1 := by
  intro h
  exact ShapeAgreeRefute.lhs_not_sortLike
    ((h SubstCRefute.a_hasType1 SubstCRefute.hBB').2 ShapeAgreeRefute.a_sortLike)

/-! ## The one surviving form, named, and the one thing it does buy -/

/-- **Shape disjointness under substitution, hereditary** — the form of row 5 that
`substShapeAgree_false` does *not* refute, stated so it can be routed rather than described.

Unlike `SortForallEDisjointH` this is **not** equivalent to `SortForallEDisjoint`: it is about
two types with no common term behind them, so `Apply.hasType` does not collapse it. -/
def SubstDisj (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B B' a R₁ R₂ C D : VExpr} {args : List VExpr} {u : VLevel},
    env.HasTypeN U n Γ a A → env.IsDefEqN U n (A::Γ) B B' →
    Apply env U n Γ (B.inst a) args R₁ → Apply env U n Γ (B'.inst a) args R₂ →
    env.IsDefEqN U n Γ R₁ (.sort u) → env.IsDefEqN U n Γ R₂ (.forallE C D) → False

/-- **Spine determinism at a type**, from `SubstDisj` and `DefInv` and nothing else — no
induction on the spine, because `DefInv`'s clause (2) already lands in the shape `SubstDisj`
consumes.

This is the leverage `SubstDisj` buys, and it is what the `bvar` case of a spine induction
needs: a variable's declared type may be decomposed as a Π in two ways, and the two
decompositions cannot send the same argument list to a sort and to a Π.

**VOID at `env = ∅, U = 1, n = 1`, and narrowing cannot save it.**  `VEnv.DefInv` is **false**
there (`DefInvRefute.defInv_one_false`), and the refutation goes through **clause (2)**
(`ForallEInvN`) alone.  The `cons` case below uses `dinv.forallE` — clause (2) — and that use
is not incidental: it is the whole reason there is no induction on the spine, since clause (2)
is what turns `B.inst a ≡ B'.inst a` into the `SubstDisj`-shaped premise.  So of the thirty-two
consumers narrowed in `docs/handoff-definv-rescue.md`, this is the one that could not be, and
it is the only void result there that no other theorem already supersedes.

**Consequence for this file.**  §3 of the module docstring above claims `applyDisj` gives
"spine determinism at a type"; at `∅` and `n = 1` that claim currently has **no content**.
`applyDisj_zero` (immediately below) is the unconditional base-index form and is unaffected —
it takes no hypothesis at all — and `SubstDisj.zero` is proved from it.  What remains true
without qualification is therefore the `n = 0` story, not the `n = 1` one.

**What would restore it.**  Either (a) a proof of `ForallEInvN env U n` at a *restricted*
class of environments that excludes the `∅, 1, 1` witness — the witness is a `⊢₀`-typed
`appDF`/`eta` configuration over `VEnv.empty`, so no environment condition rules it out, which
makes this route look closed; or (b) replacing the `cons` case's use of clause (2) by a
different bridge between the two codomains — which is precisely the "existence step" §3 of the
module docstring already records as missing, so (b) is not a smaller problem than the one this
file leaves open. `applyDisj` is kept, unmodified, as the record of what clause (2) would have
bought had it been true. -/
theorem applyDisj (dinv : env.DefInv U n) (hs : env.SubstDisj U n)
    {Γ : List VExpr} {T R₁ R₂ C D : VExpr} {args : List VExpr} {u : VLevel}
    (h1 : Apply env U n Γ T args R₁) (h2 : Apply env U n Γ T args R₂)
    (c1 : env.IsDefEqN U n Γ R₁ (.sort u)) (c2 : env.IsDefEqN U n Γ R₂ (.forallE C D)) :
    False := by
  cases h1 with
  | nil hR1 =>
    cases h2 with
    | nil hR2 =>
      exact dinv.sort_forallE <| IsDefEqN.trans' (IsDefEqN.symm' c1) <|
        IsDefEqN.trans' (IsDefEqN.symm' hR1) (IsDefEqN.trans' hR2 c2)
  | cons hpi1 ha1 hrest1 =>
    cases h2 with
    | cons hpi2 _ hrest2 =>
      exact hs ha1 (dinv.forallE (IsDefEqN.trans' (IsDefEqN.symm' hpi1) hpi2)).2
        hrest1 hrest2 c1 c2

/-- At the base index a spine is syntactically determined, because `≡₀` is equality. -/
theorem applyDisj_zero {Γ : List VExpr} {T R₁ : VExpr} {args : List VExpr}
    (h1 : Apply env U 0 Γ T args R₁) :
    ∀ {R₂ C D : VExpr} {u : VLevel}, Apply env U 0 Γ T args R₂ →
      env.IsDefEqN U 0 Γ R₁ (.sort u) → env.IsDefEqN U 0 Γ R₂ (.forallE C D) → False := by
  induction h1 with
  | nil hR1 =>
    intro _ _ _ _ h2 c1 c2
    cases h2 with
    | nil hR2 =>
      have e1 := IsDefEqN.zero_iff.1 hR1
      have e2 := IsDefEqN.zero_iff.1 hR2
      have e3 := IsDefEqN.zero_iff.1 c1
      have e4 := IsDefEqN.zero_iff.1 c2
      subst e1; subst e2; rw [e3] at e4; simp at e4
  | cons hpi1 _ _ ih =>
    intro _ _ _ _ h2 c1 c2
    cases h2 with
    | cons hpi2 _ hrest2 =>
      have e1 := IsDefEqN.zero_iff.1 hpi1
      have e2 := IsDefEqN.zero_iff.1 hpi2
      rw [e1] at e2
      injection e2 with _ eB
      subst eB
      exact ih hrest2 c1 c2

/-- **`SubstDisj` is satisfiable** — it holds at the base index, exactly as `DefInv.zero` and
`SubstC.zero` do.  Stated because a hypothesis nobody can instantiate makes every consumer
vacuous, and this file's whole point is that one of the two candidate forms is empty. -/
theorem SubstDisj.zero : env.SubstDisj U 0 := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hBB' h1 h2 c1 c2
  exact applyDisj_zero (IsDefEqN.zero_iff.1 hBB' ▸ h1) h2 c1 c2

/-! ## What is left, stated as the two horns

*Analysis, not machine-checked.*  The disjointness form does not compose at `trans`.  Its
induction, where it needs a conversion, has hypotheses

    ¬(R₁ sort-shaped ∧ R_X Π-shaped)      ¬(R_X sort-shaped ∧ R₂ Π-shaped)

and a middle term that is *neither* discharges neither: from `R₁` sort-shaped and `R₂`
Π-shaped one learns only that `R_X` is unclassified, which is consistent.  The witness above
is exactly such a middle term — `lhs` is neither — and it is reachable, so the gap is not
hypothetical.

Sharper, and this is the part worth carrying: **any transitive relation implying disjointness
must classify stuck terms.**  Suppose `R` is transitive and `R X Y` forbids "`X` sort-shaped
and `Y` Π-shaped".  The instance above forces `R lhs a` with `a` a sort; transitivity then
forbids `R lhs Z` for every Π-shaped `Z`.  So `R` has already decided, for the stuck term
`lhs`, that it is not Π-shaped — which is the target question at that term.  That is the same
conclusion §8 of the handoff reaches from the other side: what is needed is a *reduction
relation*, something that says what the middle term does. -/

end VEnv
end Lean4Lean


