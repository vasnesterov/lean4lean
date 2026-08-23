import Lean4Lean.Theory.Typing.SubstCRefute

/-!
# The Prop-shadow of `thm:utype`'s `app` case, and the model route's row zero

Two checks, both from `docs/thesis-architecture.md` §8, run in the order that document
prescribes.

## Check 1 (§8 item 2) — the Prop-shadow of the `app` case

`thm:utype`'s application case (`unique.tex:51`) bridges the two types `B₀.inst a` and
`B₁.inst a` of `.app f a` by substituting into a conversion, which is `SubstC` and is
machine-checked false (`Theory/Typing/SubstCRefute.lean`).  §8 item 2 asks whether the
*Prop-shadow* of that case — only `lvl(B₀.inst a) ≈ 0 ↔ lvl(B₁.inst a) ≈ 0` — closes without
`SubstC` and without `DefInv` clause (2), from the arithmetic `imax ℓ₁ ℓ₂ ≈ 0 ↔ ℓ₂ ≈ 0`.

**Answer: the arithmetic closes, and the case does not.**  `app_shadow_arith` below is the
positive half, machine-checked: from the induction hypothesis at `f` — the two Π-types of `f`
agree on propositionhood — the two *codomain* universes `v₀`, `v₁` agree on propositionhood.
It uses no `DefInv` clause at all, no `SubstC`, and no hypothesis about the argument `a`.

What it does not do is reach the statement.  The case is about the universes of `B₀.inst a`
and `B₁.inst a`, and `v₀`, `v₁` are the universes of `B₀`, `B₁` *under the binder*.  Closing
the gap needs two further statements, named below and neither of them `SubstC`:

* `InstLvl` — `Γ ⊢ₙ a : A`, `A::Γ ⊢ₙ B : .sort v` ⟹ `Γ ⊢ₙ B.inst a : .sort v`.  Substitution
  into a *typing* at a preserved index, at depth 0, with a closed target type.  This is a
  weakening of `VEnv.SubstT` (`Theory/Typing/SubstTRefute.lean`), which is false at depth 1;
  `InstLvl` is **not** refuted by that witness, nor by `SubstCRefute`'s (checked below,
  `substCRefute_witness_satisfies_instLvl`), and it is not proved: `Stratified.instN` lands it
  at `m + n`, so only `m = 0` (`InstLvl.of_hasTypeN_zero`) is available.
* `PropUniq` — a type's two sort-universes agree on propositionhood — at subject `B₀.inst a`,
  which is not a subterm of `.app f a`.  `docs/handoff-stratified.md` §5 places `PropUniq` in
  the `sort_inv` family.

And the *other* cases of `thm:utype`, which in the full statement close by `trans` on a common
shape-determined type, do not close for free in the shadow either: a shape-inversion lemma
delivers `T ≡ₙ A`, and carrying a universe across that conversion is `LvlConvInv` below.
`lvlConvInv_of_defInv_sort` shows the *sort* instance of `LvlConvInv` is free from `DefInv`
clause (1) — the shape cases therefore reduce to `LvlConvInv` at an arbitrary type, not to
clause (1).

## Check 2 (§8 item 1) — stratified regularity in the two-typing form is FALSE

§8 item 1 calls this "the whole route's row zero":

    Γ ⊢ₙ₊₁ e ≡ e' → (∃A, Γ ⊢ₙ e : A) ∧ (∃A', Γ ⊢ₙ e' : A')

Without it the interpretation has nothing to evaluate at a `trans` middle term, and the
model's supply of sort injectivity (`docs/thesis-architecture.md` §4) does not exist.

**It is false**, at `n + 1 = 1`, over the empty environment: `regularity_two_typing_false`.

    A₁ := .sort (max p p)      A₂ := .sort p        (max p p ≈ p, and A₁ ≠ A₂ syntactically)

    [] ⊢₁ .lam A₁ (.bvar 0)  ≡  .lam A₂ (.app (.lam A₁ (.bvar 0)) (.bvar 0))

by `sortDF` on the domains and `symm (beta …)` on the bodies, closed by `lamDF`.  The right
endpoint is not `⊢₀`-typeable (`rhs_not_hasType0`): typing it wants `.bvar 0` at the *annotated*
domain `A₁` while `Lookup` gives `A₂`, and at index `0` conversion is syntactic equality.

Three properties make this decisive rather than an artifact:

* **it does not use this tree's one deviation from the reference.**  `Stratified.rfl` is
  unconditional here while `axioms.tex:31`'s `refl` carries a typing premise, so a witness
  built from `rfl` at a junk term would not transfer.  This one uses only `sortDF`, `beta`,
  `symm` and `lamDF`, each of which the reference states with the same premises;
* **the left endpoint *is* `⊢₀`-typeable** (`lhs_hasType0`), so the failure is not a
  well-formedness accident affecting the whole conversion;
* **both endpoints are `⊢₁`-typeable** (`rhs_hasType1`), so what fails is exactly the index
  *drop* that the route needs — the conversion lives at `n+1`, the stage-`n` model can only
  evaluate `⊢ₙ`-typed terms, and the reasoning in `docs/thesis-architecture.md` §5 ("a `⊢ₙ₊₁`
  conversion's typing premises are `⊢ₙ`, so the terms it relates are interpretable by the
  stage-`n` model") confuses a rule's *premises* with a conversion's *endpoints*.

**Scope, stated narrowly.**  Refuted at `n = 0`, which is the base step of the very induction
the route runs (`soundness.tex:382` does `n = 0` and then `n → n+1`).  *Not* established for
`n ≥ 1`: for `n ≥ 1` this witness is `⊢ₙ`-typeable, since `sortDF` is then available inside a
`⊢ₙ` typing, and no general-`n` witness was built.  *Not* claimed: that part (4) of the joint
induction is false — only that it cannot be **stated** at `n+1` against the stage-`n`
interpretation.

### The stage-`n+1` obligations have no admissible order

`docs/thesis-architecture.md` §5 fixes the order "(4) at `n+1` first, then (1) and clause (3),
then (2)", and shows (2) at `n+1` is blocked by `SubstC`.  Check 2 closes the other end:

* **(4) before (2)** — the order §5 prescribes — needs the stage-`n` interpretation to be
  defined on the endpoints of a `⊢ₙ₊₁` conversion.  `tyRhs_not_hasType0` says it is not.  The
  reasoning that made the order look safe ("a `⊢ₙ₊₁` conversion's typing premises are `⊢ₙ`")
  is about a *rule's premises*, and the obligation is about a *conversion's endpoints*; the
  witness separates the two.
* **(2) before (4)** — build the stage-`n+1` interpretation first, so that (4) at `n+1` can be
  stated against it — is §5's blocked branch, and blocked by a machine-checked false lemma.

The restriction that would save the first branch — state (4) only for conversions whose
endpoints happen to be `⊢ₙ`-typed — loses exactly the case the route existed for:
`trans_derivation_with_untyped_middle` is a `⊢₁` derivation both of whose endpoints have `⊢₀`
universes and whose `trans` node has a middle term with none, so the restricted statement does
not compose at `trans`.  `trans` is the case `docs/thesis-architecture.md` §4 calls "the real
leverage" of the model route.

A consequence worth recording, because it links the two checks: `LvlConvInv`'s `trans` case
wants a universe for the middle term, and check 2 says a `⊢ₙ₊₁` conversion's middle term need
not even be `⊢ₙ`-typed.  So the shadow's conversion residual and the model route's row zero
fail on the same fact — which is a third statement of `docs/handoff-stratified.md` §8's
conclusion, now with the missing item named more precisely: not "something that says what the
middle term reduces to", but "something that says the middle term is *there* at all".
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## Check 1: the Prop-shadow of the `app` case -/

/-- **The positive half of check 1, machine-checked.**

The Prop-shadow of `thm:utype`'s application case, at the level of the *codomain universes*:
given the induction hypothesis at `f` in its shadow form — the two Π-types of `f` agree on
propositionhood — the two codomain universes agree on propositionhood.

Consumes **no `DefInv` clause**, **no `SubstC`**, and nothing about the argument `a`.  The
whole content is `VLevel.imax_eq_zero`, i.e. `imax ℓ₁ ℓ₂ ≈ 0 ↔ ℓ₂ ≈ 0`: a Π-type is a
proposition exactly when its codomain is, so propositionhood of a Π-type *is* propositionhood
of its codomain, and the index never has to look at the domain.

The two `.WF` premises are the ones `Stratified.forallE` carries; they are what lets the
induction hypothesis be applied at all, and they are free wherever the Π-types came from a
`forallE` typing. -/
theorem app_shadow_arith {Γ : List VExpr} {A₀ B₀ A₁ B₁ : VExpr} {u₀ v₀ u₁ v₁ : VLevel}
    (hu₀ : u₀.WF U) (hv₀ : v₀.WF U) (hu₁ : u₁.WF U) (hv₁ : v₁.WF U)
    (hA₀ : env.HasTypeN U n Γ A₀ (.sort u₀)) (hB₀ : env.HasTypeN U n (A₀::Γ) B₀ (.sort v₀))
    (hA₁ : env.HasTypeN U n Γ A₁ (.sort u₁)) (hB₁ : env.HasTypeN U n (A₁::Γ) B₁ (.sort v₁))
    (ih : ∀ {w₀ w₁ : VLevel}, env.HasTypeN U n Γ (.forallE A₀ B₀) (.sort w₀) →
      env.HasTypeN U n Γ (.forallE A₁ B₁) (.sort w₁) →
      (w₀ ≈ (.zero : VLevel) ↔ w₁ ≈ (.zero : VLevel))) :
    (v₀ ≈ (.zero : VLevel) ↔ v₁ ≈ (.zero : VLevel)) :=
  (VLevel.imax_eq_zero.symm.trans
      (ih (.forallE hu₀ hv₀ hA₀ hB₀) (.forallE hu₁ hv₁ hA₁ hB₁))).trans
    VLevel.imax_eq_zero

/-- **The first residual of check 1.**  Substitution into a *typing* at a preserved index, at
depth `0`, with a **closed** target type (`.sort v` has no bound variables, so the type side of
the substitution is inert).

This is strictly weaker than `VEnv.SubstT` (`Theory/Typing/SubstTRefute.lean`), which is false
at depth `1`, and weaker again than `SubstC`.  It is what turns `app_shadow_arith`'s conclusion
about `v₀`, `v₁` into a statement about the actual types `B₀.inst a`, `B₁.inst a` of
`.app f a`. -/
def InstLvl (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A a B : VExpr} {v : VLevel},
    env.HasTypeN U n Γ a A → env.HasTypeN U n (A::Γ) B (.sort v) →
    env.HasTypeN U n Γ (B.inst a) (.sort v)

/-- `InstLvl` at the base index. -/
theorem InstLvl.zero (henv : Ordered env) : env.InstLvl U 0 := fun h₀ H => by
  have := Stratified.instN henv h₀ .zero H
  rwa [Nat.zero_add] at this

/-- The fragment of `InstLvl` that `Stratified.instN` reaches: the substituted term's typing
derivation must be conversion-free, exactly as for `SubstC.of_hasTypeN_zero`.  `instN` lands at
`m + n`, so `m = 0` and only `m = 0` preserves the index. -/
theorem InstLvl.of_hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {A a B : VExpr}
    {v : VLevel} (h₀ : env.HasTypeN U 0 Γ a A) (H : env.HasTypeN U n (A::Γ) B (.sort v)) :
    env.HasTypeN U n Γ (B.inst a) (.sort v) := by
  have := Stratified.instN henv h₀ .zero H
  rwa [Nat.zero_add] at this

/-- **The second residual of check 1**: a type's universe is well defined up to
propositionhood.  `docs/handoff-stratified.md` §5 names this `PropUniq` and places it in the
`sort_inv` family (its conversion residual is asserted of endpoints, so `trans` fails).

It appears in the `app` case at subject `B₀.inst a`, which is **not** a subterm of `.app f a`,
so it cannot be supplied by the induction that is running. -/
def PropUniq (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u v : VLevel},
    env.HasTypeN U n Γ A (.sort u) → env.HasTypeN U n Γ A (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel))

/-- **The `app` case in full, in the shadow** — and this is the exact price.

Everything `thm:utype`'s `app` case needed from `SubstC` and from `DefInv` clause (2) is gone;
what replaces it is `InstLvl` and `PropUniq`.  The statement is the one the case has to
produce: the two types of `.app f a` agree on propositionhood. -/
theorem app_shadow_of (hinst : env.InstLvl U n) (huniq : env.PropUniq U n)
    {Γ : List VExpr} {a A₀ B₀ A₁ B₁ : VExpr} {u₀ v₀ u₁ v₁ u v : VLevel}
    (hu₀ : u₀.WF U) (hv₀ : v₀.WF U) (hu₁ : u₁.WF U) (hv₁ : v₁.WF U)
    (hA₀ : env.HasTypeN U n Γ A₀ (.sort u₀)) (hB₀ : env.HasTypeN U n (A₀::Γ) B₀ (.sort v₀))
    (hA₁ : env.HasTypeN U n Γ A₁ (.sort u₁)) (hB₁ : env.HasTypeN U n (A₁::Γ) B₁ (.sort v₁))
    (ha₀ : env.HasTypeN U n Γ a A₀) (ha₁ : env.HasTypeN U n Γ a A₁)
    (hT₀ : env.HasTypeN U n Γ (B₀.inst a) (.sort u))
    (hT₁ : env.HasTypeN U n Γ (B₁.inst a) (.sort v))
    (ih : ∀ {w₀ w₁ : VLevel}, env.HasTypeN U n Γ (.forallE A₀ B₀) (.sort w₀) →
      env.HasTypeN U n Γ (.forallE A₁ B₁) (.sort w₁) →
      (w₀ ≈ (.zero : VLevel) ↔ w₁ ≈ (.zero : VLevel))) :
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel)) :=
  ((huniq hT₀ (hinst ha₀ hB₀)).trans
      (app_shadow_arith hu₀ hv₀ hu₁ hv₁ hA₀ hB₀ hA₁ hB₁ ih)).trans
    (huniq (hinst ha₁ hB₁) hT₁)

/-- **The residual of the *other* cases** — the ones that in the full statement close by `trans`
on a common shape-determined type.

The shape-inversion lemmas (`HasTypeN.bvar_inv` and friends) deliver `Γ ⊢ₙ T ≡ A`, a
*conversion*, and the full statement composes conversions with `trans`.  The shadow cannot: it
has to carry a universe across the conversion, and that is this statement. -/
def LvlConvInv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' : VExpr} {u u' : VLevel},
    env.IsDefEqN U n Γ A A' → env.HasTypeN U n Γ A (.sort u) →
    env.HasTypeN U n Γ A' (.sort u') → (u ≈ (.zero : VLevel) ↔ u' ≈ (.zero : VLevel))

/-- `LvlConvInv`'s *sort* instance is free from `DefInv` clause (1), and in the strong form
(`u ≈ u'`, not merely the shadow) — which is exactly why the shape cases do **not** reduce to
clause (1): they need `LvlConvInv` at an *arbitrary* type, and clause (1) speaks only about two
sorts. -/
theorem lvlConvInv_of_defInv_sort
    (dinv1 : ∀ {Γ : List VExpr} {u v : VLevel}, env.IsDefEqN U n Γ (.sort u) (.sort v) → u ≈ v)
    {Γ : List VExpr} {l l' u u' : VLevel}
    (h : env.IsDefEqN U n Γ (.sort l) (.sort l'))
    (hu : env.HasTypeN U n Γ (.sort l) (.sort u))
    (hu' : env.HasTypeN U n Γ (.sort l') (.sort u')) :
    u ≈ u' :=
  ((dinv1 (HasTypeN.sort_inv hu).2).symm.trans
    (VLevel.succ_congr (dinv1 h))).trans (dinv1 (HasTypeN.sort_inv hu').2)

/-! ## Check 2: stratified regularity in the two-typing form is false

The statement `docs/thesis-architecture.md` §8 item 1 calls the route's row zero.  Everything
below lives in `VEnv.empty` with one universe parameter, as in
`Theory/Typing/SubstCRefute.lean`. -/

namespace RegularityRefute

open VExpr
open SubstCRefute (p p_wf)

/-- The annotated domain inside the redex, and the domain of the left λ. -/
def A₁ : VExpr := .sort (.max p p)

/-- The domain of the right λ.  `A₁ ≈ A₂` as levels, `A₁ ≠ A₂` as terms. -/
def A₂ : VExpr := .sort p

theorem A₁_wf : (VLevel.max p p).WF 1 := ⟨p_wf, p_wf⟩

/-- The right endpoint's body: the same stuck-shaped redex `SubstCRefute` uses, but with the
mismatch supplied by the *context* rather than by a substituted term. -/
def body : VExpr := .app (.lam A₁ (.bvar 0)) (.bvar 0)

/-- The left endpoint. -/
def lhs : VExpr := .lam A₁ (.bvar 0)

/-- The right endpoint. -/
def rhs : VExpr := .lam A₂ body

/-! ### The conversion, from four reference-faithful rules -/

/-- The domain step: `sortDF`, whose premises are two `WF`s and a level equivalence. -/
theorem domDF : (∅ : VEnv).IsDefEqN 1 1 [] A₁ A₂ :=
  .sortDF (by exact A₁_wf) (by exact p_wf) VLevel.max_self

/-- The body step: one `beta`, whose two typing premises are `bvar` rules at index `0`. -/
theorem bodyDF : (∅ : VEnv).IsDefEqN 1 1 [A₁] (.bvar 0) body :=
  .symm (.beta (Γ := [A₁]) (A := A₁) (e := .bvar 0) (e' := .bvar 0) (.bvar .zero) (.bvar .zero))

/-- **The conversion**: `lamDF` of the two steps above.  Uses no rule whose premises differ
from the reference's — in particular it does not use this tree's unconditional `rfl`. -/
theorem conv : (∅ : VEnv).IsDefEqN 1 1 [] lhs rhs := .lamDF domDF bodyDF

/-! ### The left endpoint is `⊢₀`-typeable, the right one is not -/

theorem lhs_hasType0 : (∅ : VEnv).HasTypeN 1 0 [] lhs (.forallE A₁ A₁) :=
  .lam (.sort (by exact A₁_wf)) (.bvar .zero)

/-- **The right endpoint is not `⊢₀`-typeable, at any type.**  Typing it wants `.bvar 0` at the
λ's *annotated* domain `A₁`, while `Lookup` in context `A₂::[]` gives `A₂`; at index `0`
conversion is syntactic equality (`IsDefEqN.zero_iff`) and `A₁ ≠ A₂`. -/
theorem rhs_not_hasType0 {T : VExpr} : ¬ (∅ : VEnv).HasTypeN 1 0 [] rhs T := by
  intro H
  obtain ⟨_, _, _, hbody, _⟩ := HasTypeN.lam_inv H
  obtain ⟨C, _, hlam, hv, _⟩ := HasTypeN.app_inv hbody
  obtain ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hlam
  injection IsDefEqN.zero_iff.1 heq with hAC
  obtain ⟨T', hl, hc⟩ := HasTypeN.bvar_inv hv
  cases hl
  have hEq : A₁ = (A₂ : VExpr).lift := hAC.trans (IsDefEqN.zero_iff.1 hc).symm
  simp [A₁, A₂, p, VExpr.lift, VExpr.liftN] at hEq

/-- Both endpoints are `⊢₁`-typeable — so what check 2 refutes is precisely the index *drop*,
not well-formedness of the conversion. -/
theorem rhs_hasType1 : (∅ : VEnv).HasTypeN 1 1 [] rhs (.forallE A₂ A₁) :=
  .lam (.sort (by exact p_wf))
    (.app (.lam (.sort (by exact A₁_wf)) (.bvar .zero))
      (.conv (.sortDF (by exact p_wf) (by exact A₁_wf) VLevel.max_self.symm) (.bvar .zero)))

/-! ### The refutation -/

/-- **`docs/thesis-architecture.md` §8 item 1 — "the whole route's row zero" — is FALSE.**

At `n + 1 = 1` over the empty environment there is a `⊢₁` conversion whose right endpoint has
no `⊢₀` type at all.  So a stage-`n` model cannot evaluate the endpoints of a `⊢ₙ₊₁`
conversion, and part (4) of the joint induction (`soundness.tex:372–380`) cannot be discharged
at `n + 1` from the stage-`n` interpretation. -/
theorem regularity_two_typing_false :
    ¬ ∀ {Γ : List VExpr} {e e' : VExpr}, (∅ : VEnv).IsDefEqN 1 1 Γ e e' →
      (∃ A, (∅ : VEnv).HasTypeN 1 0 Γ e A) ∧ (∃ A', (∅ : VEnv).HasTypeN 1 0 Γ e' A') := by
  intro H
  obtain ⟨_, h⟩ := (H conv).2
  exact rhs_not_hasType0 h

/-- The same, in the one-sided form the interpretation actually needs: it is the *right*
endpoint that has no stage-`n` denotation, while the left one does. -/
theorem regularity_two_typing_false' :
    ∃ (Γ : List VExpr) (e e' : VExpr), (∅ : VEnv).IsDefEqN 1 1 Γ e e' ∧
      (∃ A, (∅ : VEnv).HasTypeN 1 0 Γ e A) ∧ (∀ A', ¬ (∅ : VEnv).HasTypeN 1 0 Γ e' A') :=
  ⟨[], lhs, rhs, conv, ⟨_, lhs_hasType0⟩, fun _ => rhs_not_hasType0⟩

/-! ### The same witness at the level of *types*, which is what `lvl` needs

`soundness.tex:34–50`'s `lvl_v(Γ ⊢ α)` is defined on a **type**, from a derivation
`Γ ⊢ α : 𝒰_ℓ`.  Replacing the `lamDF` above by `forallEDF` — same two premises — turns the
witness into a pair of *types*, and the failure is then exactly "the right-hand type has no
stage-`n` universe". -/

def tyLhs : VExpr := .forallE A₁ (.bvar 0)

def tyRhs : VExpr := .forallE A₂ body

theorem tyConv : (∅ : VEnv).IsDefEqN 1 1 [] tyLhs tyRhs := .forallEDF domDF bodyDF

/-- The left type has a `⊢₀` universe. -/
theorem tyLhs_hasType0 :
    (∅ : VEnv).HasTypeN 1 0 [] tyLhs (.sort (.imax (.succ (.max p p)) (.max p p))) :=
  .forallE (by exact A₁_wf) (by exact A₁_wf) (.sort (by exact A₁_wf)) (.bvar .zero)

/-- The right type has a `⊢₁` universe … -/
theorem tyRhs_hasType1 :
    (∅ : VEnv).HasTypeN 1 1 [] tyRhs (.sort (.imax (.succ p) (.max p p))) :=
  .forallE (by exact p_wf) (by exact A₁_wf) (.sort (by exact p_wf))
    (.app (.lam (.sort (by exact A₁_wf)) (.bvar .zero))
      (.conv (.sortDF (by exact p_wf) (by exact A₁_wf) VLevel.max_self.symm) (.bvar .zero)))

/-- … and **no `⊢₀` universe at all**, so `lvl` at stage `0` is undefined on it. -/
theorem tyRhs_not_hasType0 {T : VExpr} : ¬ (∅ : VEnv).HasTypeN 1 0 [] tyRhs T := by
  intro H
  obtain ⟨_, _, _, _, _, hbody, _⟩ := HasTypeN.forallE_inv H
  obtain ⟨C, _, hlam, hv, _⟩ := HasTypeN.app_inv hbody
  obtain ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hlam
  injection IsDefEqN.zero_iff.1 heq with hAC
  obtain ⟨T', hl, hc⟩ := HasTypeN.bvar_inv hv
  cases hl
  have hEq : A₁ = (A₂ : VExpr).lift := hAC.trans (IsDefEqN.zero_iff.1 hc).symm
  simp [A₁, A₂, p, VExpr.lift, VExpr.liftN] at hEq

/-- **`trans`'s middle term, concretely.**  `LvlConvInv`'s `trans` case has to produce a
universe for the middle term of `A ≡ₙ₊₁ X ≡ₙ₊₁ A'`.  Here is an instance where both endpoints
have a stage-`n` universe and the middle term has none — so the shadow's conversion residual
and the model route's row zero (`regularity_two_typing_false`) fail on the same fact.

This is the concrete form of `docs/handoff-stratified.md` §5's `trans` obstruction: not "the
middle term need not be a sort", but "the middle term need not be interpretable at all". -/
theorem trans_middle_has_no_stage_universe :
    ∃ (A X A' : VExpr),
      (∅ : VEnv).IsDefEqN 1 1 [] A X ∧ (∅ : VEnv).IsDefEqN 1 1 [] X A' ∧
      (∃ u, (∅ : VEnv).HasTypeN 1 0 [] A (.sort u)) ∧
      (∃ u', (∅ : VEnv).HasTypeN 1 0 [] A' (.sort u')) ∧
      (∀ w, ¬ (∅ : VEnv).HasTypeN 1 0 [] X (.sort w)) :=
  ⟨tyLhs, tyRhs, tyLhs, tyConv, .symm tyConv, ⟨_, tyLhs_hasType0⟩, ⟨_, tyLhs_hasType0⟩,
    fun _ => tyRhs_not_hasType0⟩

/-- The `trans` derivation itself, so the point is not hypothetical: this is a `⊢₁` conversion
whose two endpoints have `⊢₀` universes and whose `trans` node has a middle term
(`tyRhs`) that has none.  Any induction over this derivation must evaluate that middle term.

The context here is `[]`, so the witness also survives the `⟦Γ⟧ ≠ ∅` side condition that
`soundness.tex:372–376` attaches to parts (1) and (2). -/
theorem trans_derivation_with_untyped_middle : (∅ : VEnv).IsDefEqN 1 1 [] tyLhs tyLhs :=
  .trans tyConv (.symm tyConv)

end RegularityRefute

/-! ## `InstLvl` against the two witnesses that killed its neighbours -/

/-- `SubstCRefute`'s witness does **not** refute `InstLvl`: at that instance the substituted
term `SubstCRefute.lhs` *is* `⊢₁`-typeable at the codomain's universe, so no contradiction is
available there.  (`SubstC` fails at the same instance because a *conversion* has to survive,
which is a strictly stronger demand.) -/
theorem substCRefute_witness_satisfies_instLvl :
    (∅ : VEnv).HasTypeN 1 1 [] SubstCRefute.lhs SubstCRefute.A :=
  .app (.lam (.sort (by exact SubstCRefute.p_wf)) (.bvar .zero)) SubstCRefute.a_hasType1

end VEnv
end Lean4Lean
