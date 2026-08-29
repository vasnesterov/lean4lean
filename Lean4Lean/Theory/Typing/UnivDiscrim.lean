import Lean4Lean.Theory.Typing.ShapeSpine

/-!
# The `common_sort` move, and why it does not transfer to `SortForallEDisjoint`

`docs/design-shape-lattice.md` records a long series of refutations of `WShape.IsType.common`
("two related shapes share a classifying sort") and of every relativisation of it —
`Compat`-only, `LE_Interp`-relative, `TyDefEq`-relative.  **One statement survived**, and it
survived by working differently:

```
theorem LE_Interp.common_sort {ρ A U} {a a' : WShape n}
    (H : ∀ {b}, LE_Interp ρ b A → InterpTyped ρ b A (.sort U))
    (h : LE_Interp ρ a.T A) (h' : LE_Interp ρ a'.T A) (ha : a.IsType) (ha' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

Its shared boolean is `decide (U ≠ .zero)` — a function of `U`, **the universe of the
syntactic type `A`**, and of nothing else.  Nothing relates `a` to `a'`; `H` is applied to each
separately.  So the escape has three parts, and all three matter:

1. the datum is not computed from the two objects being compared, but **supplied by a third
   thing both are attached to** (the syntactic type `A`);
2. that datum comes from a judgment **one level up** — `A`'s own type `.sort U`, which the
   caller (`Adequacy:89`) holds as `IsDefEqStrong Γ A A' (.sort u)`, a *type-indexed*
   derivation that ships with its universe;
3. the hypothesis is a **uniformity** (`∀ b, …`) at a fixed `U`, so instantiating it twice
   yields the same answer and there is no `∃`-common to construct.

This file asks whether the same move closes `SortForallEDisjoint.AppCase`, and answers **no**.
Two independent reasons, the second machine-checked here.

## Reason 1 — in a one-layer setting the lemma degenerates to its own hypothesis

`common_sort` is a **coherence lemma between two layers**.  `LE_Interp ρ b A` relates a
*shape* to a *term*; shapes are a separate, simpler structure, and they are non-deterministic
exactly where terms are not.  What the lemma buys is: transport a fact that is *determinate on
the term layer* down to the *indeterminate shape layer*, at two shapes at once.

`SortForallEDisjoint` has no second layer.  The objects being compared (`B₀.inst a` and
`B₁.inst a`, the two types of `.app f a`) and the accompanying object (`.app f a` itself) are
all terms of the one syntax.  Written out in that setting, `H` says "`A` is a type at universe
`U`" — which is `common_sort`'s own hypothesis, with nothing left over.  *This is the same
collapse `Apply.hasType` produced for the hereditary form, reached from a different direction:
in a single-layer setting "consult the accompanying term" is "invoke the statement being
proved".*

## Reason 2 — the datum is empty: a universe does not determine a type's shape

Grant the level-`k+1` datum for free anyway.  Level `k` is "the types of a term"; level `k+1`
is "the universes of those types".  Then:

> for **every** `u`, the sort `.sort u` and the Π-type `∀ (_ : .sort u), .sort u` are types at
> one and the same universe `.succ u` (`succ_eq_imax`, which is `VLevel.imax_self`).

So the datum `common_sort` would read off does not separate the two shapes, whereas in the
shape model the `Prop`/`Type` boolean it reads off *is* precisely the fact needed.  That is
the disanalogy, and it is arithmetic rather than anything about the judgment:
`.sort u : .sort (.succ u)` and `.forallE A B : .sort (.imax p q)`, and the ranges of `.succ`
and `.imax` overlap.

Machine-checked twice, in both judgments this repo has:

* `univ_premises_satisfiable` — at the stratified index, **every** premise of the
  universe-relative statement `SortForallEDisjointUniv` except "the two types have a common
  inhabitant" is simultaneously satisfiable.  All the content stays in the common inhabitant,
  which is what the unrelativised statement already quantifies over: the relativisation
  removes no instance at all.
* `strong_univ_premises_satisfiable` — the same, in `HasTypeStrong`, and this is the decisive
  one.  **`HasTypeStrong` carries regularity in every constructor** (`bvar` ships
  `Γ ⊢ A : .sort u`, `app` ships `Γ ⊢ B.inst a : .sort v`, …), so there the universe premise
  is not something to be earned — it is free.  It is free, and it still does not discriminate.

## The variants that were checked and fall to the same fact

* *the universe of the application.*  In `AppCase`, `.app f a : .sort u` says the application
  *is* a type at universe `u`; on the other side it is a function and has no universe.  So `u`
  is not an independent handle — it is one half of the disjunction being refuted.
* *the codomain universes of `f`'s two Π-types.*  Suppose `Γ ⊢ B₀.inst a : .sort v₀` and
  `Γ ⊢ B₁.inst a : .sort v₁` were free (they are not — obtaining them substitutes into a
  typing derivation, which meets `SubstC`'s index drop).  With `B₀.inst a ≡ .sort u` one gets
  `v₀ ≈ .succ u`, and with `B₁.inst a ≡ .forallE A B` one gets `v₁ ≈ .imax p q`.  A
  contradiction needs `v₀ ≉ v₁`; nothing supplies it, and **even `v₀ ≈ v₁` is consistent**, by
  `succ_eq_imax`.  Dead twice over.

## What this leaves

`docs/design-shape-lattice.md`'s survivor was the route's last untried idea in this
neighbourhood, and it is now closed.  Nothing here refutes `SortForallEDisjoint` — it is
satisfiable (`SortForallEDisjoint.zero`) and still open; what is closed is the hope of
proving it by reading a discriminating datum off a universe.  The remaining direction is the
one §8 of `docs/handoff-stratified.md` reaches from three sides already: a **reduction
relation**, something that says what a middle term does.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## First: the primitive is satisfiable

`docs/handoff-stratified.md` funds `SortForallEDisjoint` as a primitive, and a primitive
nobody can instantiate makes every consumer vacuous.  It holds at the base index, exactly as
`DefInv.zero`, `SubstC.zero` and `SubstDisj.zero` do, and for the same reason: `≡₀` is
syntactic equality, so `⊢₀` typing is syntactically unique (`HasTypeN.uniq_zero`). -/

/-- **`SortForallEDisjoint` is satisfiable.**  At the base index a term's types are
syntactically equal, and `.sort u` is not `.forallE A B`. -/
theorem SortForallEDisjoint.zero : env.SortForallEDisjoint U 0 := by
  intro _ _ _ _ _ h1 h2
  exact VExpr.noConfusion (HasTypeN.uniq_zero h1 h2)

/-- And so is its one open case, at the same index. -/
theorem SortForallEDisjoint.AppCase.zero : SortForallEDisjoint.AppCase env U 0 :=
  SortForallEDisjoint.appCase SortForallEDisjoint.zero

/-! ## The level-arithmetic core -/

/-- **For every `u` there is a Π-type at exactly the universe of `.sort u`.**

`.sort u : .sort (.succ u)` and `.forallE A B : .sort (.imax p q)`; the ranges of `.succ` and
`.imax` overlap, and `imax_self` puts them on top of each other.  Any argument that hopes to
separate a sort-typed term from a Π-typed one by comparing *universes* has to contend with
this, whatever else it assumes and in whichever judgment it works. -/
theorem succ_eq_imax (u : VLevel) : VLevel.succ u ≈ VLevel.imax (.succ u) (.succ u) :=
  (VLevel.imax_self (a := .succ u)).symm

/-! ## The universe-relative form of the statement, at the index -/

/-- **`SortForallEDisjoint` with the `common_sort` datum bolted on**: the two types of `e` are
themselves types, at one universe `w`.

This is the strongest thing "read the fact off the accompanying term's universe rather than
off a relation between the two types" can mean here — `w` plays the role `common_sort`'s `U`
plays, and it is read off a typing judgment one level up rather than off any relation between
`T₁` and `T₂`. -/
def SortForallEDisjointUniv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T₁ T₂ A B : VExpr} {u w : VLevel},
    env.HasTypeN U n Γ e T₁ → env.HasTypeN U n Γ e T₂ →
    env.HasTypeN U n Γ T₁ (.sort w) → env.HasTypeN U n Γ T₂ (.sort w) →
    env.IsDefEqN U n Γ T₁ (.sort u) → env.IsDefEqN U n Γ T₂ (.forallE A B) → False

/-- The easy direction: the universe-relative form is weaker.  The converse needs regularity
at the index — `Γ ⊢ₙ e : T ⟹ ∃ w, Γ ⊢ₙ T : .sort w` — whose `app` case substitutes into a
typing derivation and so lands in `SubstC`'s refuted family. -/
theorem SortForallEDisjoint.univ (hd : env.SortForallEDisjoint U n) :
    env.SortForallEDisjointUniv U n :=
  fun h1 h2 _ _ c1 c2 => hd (.conv c1 h1) (.conv c2 h2)

namespace UnivDiscrim

/-- The Π-type placed at the same universe as `.sort u`. -/
def piAt (u : VLevel) : VExpr := .forallE (.sort u) (.sort u)

/-- `.sort u : .sort (.succ u)` — the sort side, at any index. -/
theorem sort_at {Γ : List VExpr} {u : VLevel} (h : u.WF U) :
    env.HasTypeN U n Γ (.sort u) (.sort (.succ u)) := .sort h

/-- `∀ (_ : .sort u), .sort u : .sort (.succ u)` — **the same universe**, by `succ_eq_imax`.

This is the whole disanalogy with `common_sort`: there the datum read off the universe is the
`Prop`/`Type` boolean, which *is* the fact needed; here the fact needed is sort-shaped versus
Π-shaped, and the universe does not carry it. -/
theorem pi_at {Γ : List VExpr} {u : VLevel} (h : u.WF U) :
    env.HasTypeN U (n+1) Γ (piAt u) (.sort (.succ u)) :=
  .conv (.sortDF (l := .imax (.succ u) (.succ u)) ⟨h, h⟩ h VLevel.imax_self)
    (.forallE h h (.sort h) (.sort h))

theorem sort_sortShaped {Γ : List VExpr} {u : VLevel} :
    env.IsDefEqN U n Γ (.sort u) (.sort u) := .rfl

theorem pi_piShaped {Γ : List VExpr} {u : VLevel} :
    env.IsDefEqN U n Γ (piAt u) (.forallE (.sort u) (.sort u)) := .rfl

end UnivDiscrim

/-- **The universe premise is empty.**  Every premise of `SortForallEDisjointUniv` *except*
the two typings of a common inhabitant `e` is simultaneously satisfiable, in any context, at
any index `n+1`, over any environment:

* `T₁` and `T₂` are both types, **at one and the same universe `w`**;
* `T₁` is sort-shaped and `T₂` is Π-shaped.

So relativising `SortForallEDisjoint` to a shared universe removes no instance at all: the
entire content of the statement remains in "`T₁` and `T₂` have a common inhabitant", which is
what the unrelativised statement already says.  `common_sort`'s move — read the answer off the
accompanying term's universe — has nothing to read here.

*Contrast, to make the disanalogy exact.*  In the shape model the analogous check **fails**:
`.sort U` at `U = .zero` and at `U ≠ .zero` are different type-shapes, so fixing `U` genuinely
cuts the space of classifying shapes down to one.  That is why `common_sort` closes and this
does not. -/
theorem univ_premises_satisfiable (env : VEnv) (U n : Nat) (Γ : List VExpr)
    {u : VLevel} (h : u.WF U) :
    ∃ (T₁ T₂ A B : VExpr) (w v : VLevel),
      env.HasTypeN U (n+1) Γ T₁ (.sort w) ∧ env.HasTypeN U (n+1) Γ T₂ (.sort w) ∧
      env.IsDefEqN U (n+1) Γ T₁ (.sort v) ∧
      env.IsDefEqN U (n+1) Γ T₂ (.forallE A B) :=
  ⟨.sort u, UnivDiscrim.piAt u, .sort u, .sort u, .succ u, u,
    UnivDiscrim.sort_at h, UnivDiscrim.pi_at h,
    UnivDiscrim.sort_sortShaped, UnivDiscrim.pi_piShaped⟩

/-! ## Why the `app` case resists: its induction hypothesis is vacuous

Independent of the universe question, and worth recording because it is the sharper diagnosis
of `SortForallEDisjoint.AppCase`.

`SortForallEDisjoint` **passes** the handoff's criterion (§5): its induction is on *typing*,
so it never looks at a conversion derivation and `trans` never arises.  It is nevertheless
open at `app`.  The reason is not `trans` and it is not composability — it is that at the one
recursive position that could reach what the case needs, the induction hypothesis is
*vacuously true*.

In `sortForallEDisjoint_of`'s `app` case the subject is `.app f a` and the recursive positions
are `f` (at type `.forallE A₀ B₀`) and `a` (at type `A₀`).  What the case needs is a fact about
`f`'s **two** Π-types.  But the IH at `f` is guarded by "`f`'s type is sort-shaped", and a
Π-type never is — so the IH there is derivable from `DefInv` alone, with the sub-derivation
unused (`appCase_ih_vacuous` below, which takes no `f`-derivation as an argument at all).
The IH at `a` is not vacuous, but it speaks about `a`, not about the application.

**The companion test this suggests**, offered alongside the criterion rather than as a
replacement: *at each recursive position of the proposed induction, is the induction
hypothesis non-vacuous?*  It is cheap to run — instantiate the IH at the position and try to
prove it from the ambient hypotheses without the sub-derivation — and it separates
`SortForallEDisjoint` from the statements the criterion already rejects, which fail for a
different reason.  Passing the criterion is necessary, not sufficient. -/

/-- **The `app` case's induction hypothesis at the function carries no information.**  It is
proved here from `DefInv` **clause (3)** alone; note the statement mentions `f` only in a
premise that is
never used, and no derivation about `f` is an argument.  So the `app` case of
`sortForallEDisjoint_of` is not a hard use of an induction hypothesis — there is nothing there
to use. -/
theorem appCase_ih_vacuous (dinv : env.SortForallEDisjN U n) {Γ : List VExpr}
    {f A₀ B₀ : VExpr} :
    ∀ {u : VLevel} {A B : VExpr}, env.IsDefEqN U n Γ (.forallE A₀ B₀) (.sort u) →
      env.HasTypeN U n Γ f (.forallE A B) → False :=
  fun h _ => dinv (IsDefEqN.symm' h)

/-! ## The same, in the judgment where the universe premise is free

`HasTypeStrong` carries regularity in *every* constructor: `bvar` ships `Γ ⊢ A : .sort u`,
`app` ships `Γ ⊢ B.inst a : .sort v`, `lam` ships `Γ ⊢ .forallE A B : .sort (.imax u v)`, and
`defeq` ships the shared universe of both sides of a conversion.  So this is the setting in
which `common_sort`'s hypothesis costs nothing at all — and it is still not a discriminator.
That is what makes the negative judgment-independent rather than an artifact of the
stratification. -/

/-- `.sort l` is a type, at any index, in `HasTypeStrong`. -/
theorem HasTypeStrong.sortType {Γ : List VExpr} {l : VLevel} (h : l.WF U) :
    env.HasTypeStrong U Γ (.sort l) (.sort (.succ l)) true :=
  .base (.sort' (l := l) (l' := l) h h rfl)

/-- **Regularity is free in `HasTypeStrong`** — every type in a derivation is itself a type,
and the proof needs no `Ordered`, no `OnCtx`, no `CtxStrong` and no hypothesis of any kind
beyond the derivation.  Every structural constructor already carries the typing of the type it
concludes at (`bvar` ships `Γ ⊢ A : .sort u`, `app` ships `Γ ⊢ B.inst a : .sort v`, `lam`
ships `Γ ⊢ .forallE A B : .sort (.imax u v)`, `defeq` ships `Γ ⊢ B : .sort u`); the two
remaining cases build the sort's own type.  Contrast `IsDefEqStrong.isType'`, which needs
`Ordered`, `OnTypes` and `CtxStrong`.

This is what makes the negative below decisive rather than an artifact of the stratified
index: in this judgment the `common_sort` datum is not something to be earned. -/
theorem HasTypeStrong.regular {Γ e A b} (H : env.HasTypeStrong U Γ e A b) :
    ∃ w, env.HasTypeStrong U Γ A (.sort w) true := by
  induction H with
  | bvar _ _ hA => exact ⟨_, hA⟩
  | sort' _ h' _ => exact ⟨_, HasTypeStrong.sortType h'⟩
  | const _ _ _ _ _ hΓt => exact ⟨_, hΓt⟩
  | app _ _ _ _ _ _ _ hBa => exact ⟨_, hBa⟩
  | lam _ _ _ _ _ hPi => exact ⟨_, hPi⟩
  | forallE hu hv _ _ => exact ⟨_, HasTypeStrong.sortType (l := .imax _ _) ⟨hu, hv⟩⟩
  | base _ ih => exact ih
  | defeq _ _ _ hB _ => exact ⟨_, hB⟩

/-- `SortForallEDisjoint`, stated in the unstratified type-indexed judgment. -/
def SortForallEDisjointS (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {u : VLevel},
    env.HasTypeStrong U Γ e (.sort u) true →
    env.HasTypeStrong U Γ e (.forallE A B) true → False

/-- The same, with `common_sort`'s datum supplied: each of the two types is itself a type, at
its own universe. -/
def SortForallEDisjointSUniv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {u w₁ w₂ : VLevel},
    env.HasTypeStrong U Γ e (.sort u) true →
    env.HasTypeStrong U Γ e (.forallE A B) true →
    env.HasTypeStrong U Γ (.sort u) (.sort w₁) true →
    env.HasTypeStrong U Γ (.forallE A B) (.sort w₂) true → False

/-- **The relativisation is not a relativisation.**  In the judgment where regularity is free,
supplying `common_sort`'s datum yields *literally the same statement* — the two are equivalent
in one line each way, by `HasTypeStrong.regular`.

This is trap #11 of `docs/handoff-stratified.md` in a new instance, and it is the direct
answer to "does the move transfer": the universe-relative statement is not a different, easier
statement to prove.  The only version that *is* different demands the two universes be
**shared**, and `strong_univ_premises_satisfiable` shows that version's premise is consistent
with a sort on one side and a Π on the other — so it discriminates nothing either. -/
theorem SortForallEDisjointSUniv.iff :
    env.SortForallEDisjointSUniv U ↔ env.SortForallEDisjointS U := by
  constructor
  · intro h _ _ _ _ _ h1 h2
    obtain ⟨_, r1⟩ := h1.regular
    obtain ⟨_, r2⟩ := h2.regular
    exact h h1 h2 r1 r2
  · intro h _ _ _ _ _ _ _ h1 h2 _ _
    exact h h1 h2

namespace UnivDiscrim

theorem sort_at' {Γ : List VExpr} {u : VLevel} (h : u.WF U) :
    env.HasTypeStrong U Γ (.sort u) (.sort (.succ u)) true :=
  HasTypeStrong.sortType h

theorem pi_at' {Γ : List VExpr} {u : VLevel} (h : u.WF U) :
    env.HasTypeStrong U Γ (piAt u) (.sort (.succ u)) true :=
  .defeq (u := .succ (.imax (.succ u) (.succ u))) ⟨h, h⟩
    (.sortDF ⟨h, h⟩ h VLevel.imax_self)
    (.base (.sort' ⟨h, h⟩ ⟨h, h⟩ rfl))
    (.base (.sort' h ⟨h, h⟩ (succ_eq_imax u)))
    (.base (.forallE h h (sort_at' h) (sort_at' h)))

end UnivDiscrim

/-- **The decisive form of the negative.**  In `HasTypeStrong`, where every rule already
carries the typing of the type it concludes at, a sort and a Π-type sit at *one and the same*
universe.  So the `common_sort` datum is available for free here and separates nothing.

Together with `univ_premises_satisfiable` this closes the universe route in both judgments the
repo has, and by a fact — `succ_eq_imax` — that mentions no judgment at all. -/
theorem strong_univ_premises_satisfiable (env : VEnv) (U : Nat) (Γ : List VExpr)
    {u : VLevel} (h : u.WF U) :
    env.HasTypeStrong U Γ (.sort u) (.sort (.succ u)) true ∧
    env.HasTypeStrong U Γ (.forallE (.sort u) (.sort u)) (.sort (.succ u)) true :=
  ⟨UnivDiscrim.sort_at' h, UnivDiscrim.pi_at' h⟩

end VEnv
end Lean4Lean
