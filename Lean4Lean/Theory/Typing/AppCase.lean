import Lean4Lean.Theory.Typing.PropConv

/-!
# The shared `app` case

`docs/handoff-stratified.md` §16.4 records five statements about `⊢ₙ` that each close six of
their seven typing cases and each stop at an `app` case with the same subject shape:
`SortForallEDisjoint`, `PropForallEDisjoint`, `PropNotProof`, `PropUniq`, `PropTypeAgree`.
This file characterises that case exactly, prices what would discharge it, and closes three
candidate routes with machine-checked witnesses.

## What is here

1. **The obligation, stated once** (§1–2).  `AppData` is the premise bundle every one of the
   five carries once `HasTypeN.app_inv` has been run on the second typing: **one function with
   two Π-types, and one argument typed at both domains**.  Over it, each of the five `app`
   cases becomes a statement about the pair `(B₀.inst a, B₁.inst a)`, and each such statement
   is proved equivalent to the tree's own `*.AppCase`, both directions, with no hypotheses.
   So the five differ *only* in what they conclude about that one pair.

2. **The unifier, and its refutation** (§3–4).  The statement that decides all five at once is
   `thm:utype`'s own application case (`AppTypeUniq`): the two instantiated codomains are
   `⊢ₙ`-convertible.  It implies all five, each with the residual that statement already names
   (`DefInv`, `SortNotProp`, `PropConvInv`), and holds at the base index.  **It is false at
   `n = 1` over the empty environment**, and so is unique typing at the index itself
   (`uniqN_false`) — see the scope note below.

3. **The strengthened-induction schema, and its collapse** (§5, §8).  Any strengthening of the
   induction is a relation `R` on pairs of types satisfying (i) it relates any two types of any
   term, (ii) it is closed under instantiating two Π-codomains at a common argument, (iii) it
   separates sorts from Π's.  `relStrengthening_sound` shows (i)+(ii)+(iii) close the case;
   `sortForallEDisjoint_of_rel` shows (i)+(iii) *already prove the statement*, so no `R` makes
   the remaining obligation cheaper.  Four candidate `R`s are filled in and every one either
   fails a clause with a machine-checked witness or reproduces the statement.

4. **`PiCodConv`, refuted** (§6).  The one decomposition that is not a fixpoint —
   "two Π-types of one term have convertible codomains", which with `SubstDisj`
   (`Theory/Typing/ShapeSpine.lean`) closes the `app` case in a line — is **false at `n = 1`**,
   by the same witness lifted through one λ.

5. **The index does not help** (§7).  Four of the five statements are antitone in `n`, so
   `S (n+1) → S n` is free and the whole content is the upward direction.

## Scope of the `uniqN_false` result — read this before quoting it

`docs/reference-gap-thm-utype.md` §4 lists **`thm:utype`'s statement** under *not refuted*, on
the explicit ground that the `SubstC` counterexample "carries hypotheses this instance does not
supply: a single term `e₁` carrying *both* Π types, and an argument typed at *both* domains".
`ShapeSpine.lean`'s `ShapeAgreeRefute` supplies exactly that, and this file draws the
consequence: at `n = 1`, over the **empty** environment, the term `.app (.bvar 0) a` has two
`⊢₁` types that are not `⊢₁`-convertible.

What that does and does not settle:

* **Settled**: the *unconditional* form of `thm:utype` at `n = 1` is false.  No argument can
  prove `HasTypeN.uniq`'s conclusion at `n = 1` without an extra hypothesis.
* **Not settled**: `thm:utype` as the reference states it carries the hypothesis "`⊢ₙ` has
  definitional inversion", and `DefInv ∅ 1 1` is open.  `thm_utype_one_false_of_defInv` states
  the dichotomy: either `DefInv ∅ 1 1` fails — and then the route's own target `∀ n, DefInv`
  fails at its first non-trivial index — or `thm:utype` is false at `n = 1`.  Either way the
  reference's induction `DefInv n → uniq n → DefInv (n+1)` cannot be repaired at `n = 1`.
* **Not affected**: the five statements.  They are each strictly weaker than unique typing and
  none of them is refuted here — `witness_shapes` machine-checks that the witness's two types
  are not a (sort, Π) pair nor a (sort, sort) pair, which is §16.4's reading result for three
  of the five.  Nor is the route through them affected: `HasTypeN.uniq` is used nowhere in this
  tree at `n ≥ 1`; `DefInv (n+1)` is reached from `PropTypeAgree n` + `DefInv n`, not from
  `uniq n`.
* **Not a statement about Lean.**  `lhs_conv_a_succ` shows the same pair *is* convertible at
  `n = 2`.  The counterexample is about the alternation index, not about the terms: what fails
  is unique typing *at a fixed index*, which is what the reference's induction needs.

## Confidence

Everything in this file is machine-checked and sorry-free; axioms are `propext` and
`Quot.sound` only.  What is **not** claimed: that any of the five is true, or false, or that
the list of candidate `R`s in §8 is exhaustive.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. The premise bundle -/

/-- The hypotheses every one of the five `app` cases carries, after
`HasTypeN.app_inv` has been run on the second typing: **one function with two Π-types, and
one argument typed at both domains**. -/
structure AppData (env : VEnv) (U n : Nat) (Γ : List VExpr) (f a A₀ B₀ A₁ B₁ : VExpr) :
    Prop where
  fn₀ : env.HasTypeN U n Γ f (.forallE A₀ B₀)
  arg₀ : env.HasTypeN U n Γ a A₀
  fn₁ : env.HasTypeN U n Γ f (.forallE A₁ B₁)
  arg₁ : env.HasTypeN U n Γ a A₁

/-- The applied term, at its first type. -/
theorem AppData.hasType₀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (h : AppData env U n Γ f a A₀ B₀ A₁ B₁) :
    env.HasTypeN U n Γ (.app f a) (B₀.inst a) := .app h.fn₀ h.arg₀

/-- The applied term, at its second type. -/
theorem AppData.hasType₁ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (h : AppData env U n Γ f a A₀ B₀ A₁ B₁) :
    env.HasTypeN U n Γ (.app f a) (B₁.inst a) := .app h.fn₁ h.arg₁

theorem AppData.symm {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (h : AppData env U n Γ f a A₀ B₀ A₁ B₁) : AppData env U n Γ f a A₁ B₁ A₀ B₀ :=
  ⟨h.fn₁, h.arg₁, h.fn₀, h.arg₀⟩

/-- **Every `AppData` comes from an application with two types, and conversely.** -/
theorem AppData.of_hasType {Γ : List VExpr} {e T₁ T₂ f a : VExpr} (he : e = .app f a)
    (h1 : env.HasTypeN U n Γ e T₁) (h2 : env.HasTypeN U n Γ e T₂) :
    ∃ A₀ B₀ A₁ B₁, AppData env U n Γ f a A₀ B₀ A₁ B₁ ∧
      env.IsDefEqN U n Γ (B₀.inst a) T₁ ∧ env.IsDefEqN U n Γ (B₁.inst a) T₂ := by
  subst he
  obtain ⟨A₀, B₀, hf₀, ha₀, hc₀⟩ := h1.app_inv
  obtain ⟨A₁, B₁, hf₁, ha₁, hc₁⟩ := h2.app_inv
  exact ⟨A₀, B₀, A₁, B₁, ⟨hf₀, ha₀, hf₁, ha₁⟩, hc₀, hc₁⟩

/-! ## 2. The five app cases, restated over `AppData` -/

/-- `SortForallEDisjoint.AppCase`, with the second typing already inverted. -/
def AppDisj (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ A B : VExpr} {u : VLevel},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.forallE A B) → False

/-- `PropForallEDisjoint.AppCase`, likewise: the `u = .zero` instance. -/
def AppPropDisj (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ A B : VExpr},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort .zero) →
    env.IsDefEqN U n Γ (B₁.inst a) (.forallE A B) → False

/-- `PropUniq.AppCase`, likewise. -/
def AppUniqLvl (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel))

/-- `PropNotProof.AppCase`, likewise. -/
def AppNotProof (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ p : VExpr},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort .zero) →
    env.HasTypeN U n Γ p (.sort .zero) →
    env.IsDefEqN U n Γ (B₁.inst a) p → False

/-- `PropTypeAgree.AppCase`, likewise.  The third premise is the case's induction hypothesis
at the function, kept verbatim. -/
def AppPropAgree (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ A' : VExpr},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    (∀ {X : VExpr}, env.HasTypeN U n Γ f X →
      IsPropN env U n Γ (.forallE A₀ B₀) → IsPropN env U n Γ X) →
    env.IsDefEqN U n Γ (B₁.inst a) A' →
    IsPropN env U n Γ (B₀.inst a) → IsPropN env U n Γ A'

/-! ### …and each agrees with the tree's statement of it, in both directions

Left to right is `HasTypeN.app_inv` on the second typing; right to left is `Stratified.app`
followed by `conv`.  Neither direction uses a hypothesis, so the two formulations are
interchangeable at every index and over every environment. -/

theorem AppDisj.of_appCase (h : SortForallEDisjoint.AppCase env U n) : env.AppDisj U n := by
  intro _ _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact h d.fn₀ d.arg₀ c₀ (.conv c₁ d.hasType₁)

theorem AppDisj.appCase (h : env.AppDisj U n) : SortForallEDisjoint.AppCase env U n := by
  intro _ _ _ _ _ _ _ _ hf ha hT H2
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := H2.app_inv
  exact h ⟨hf, ha, hf₁, ha₁⟩ hT hc

theorem AppDisj.iff : env.AppDisj U n ↔ SortForallEDisjoint.AppCase env U n :=
  ⟨AppDisj.appCase, AppDisj.of_appCase⟩

theorem AppPropDisj.of_appCase (h : PropForallEDisjoint.AppCase env U n) :
    env.AppPropDisj U n := by
  intro _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact h d.fn₀ d.arg₀ c₀ (.conv c₁ d.hasType₁)

theorem AppPropDisj.appCase (h : env.AppPropDisj U n) :
    PropForallEDisjoint.AppCase env U n := by
  intro _ _ _ _ _ _ _ hf ha hT H2
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := H2.app_inv
  exact h ⟨hf, ha, hf₁, ha₁⟩ hT hc

theorem AppPropDisj.iff : env.AppPropDisj U n ↔ PropForallEDisjoint.AppCase env U n :=
  ⟨AppPropDisj.appCase, AppPropDisj.of_appCase⟩

theorem AppUniqLvl.of_appCase (h : PropUniq.AppCase env U n) : env.AppUniqLvl U n := by
  intro _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact h d.fn₀ d.arg₀ c₀ (.conv c₁ d.hasType₁)

theorem AppUniqLvl.appCase (h : env.AppUniqLvl U n) : PropUniq.AppCase env U n := by
  intro _ _ _ _ _ _ _ hf ha hT H2
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := H2.app_inv
  exact h ⟨hf, ha, hf₁, ha₁⟩ hT hc

theorem AppUniqLvl.iff : env.AppUniqLvl U n ↔ PropUniq.AppCase env U n :=
  ⟨AppUniqLvl.appCase, AppUniqLvl.of_appCase⟩

theorem AppNotProof.of_appCase (h : PropNotProof.AppCase env U n) : env.AppNotProof U n := by
  intro _ _ _ _ _ _ _ _ d c₀ hp c₁
  exact h d.fn₀ d.arg₀ c₀ hp (.conv c₁ d.hasType₁)

theorem AppNotProof.appCase (h : env.AppNotProof U n) : PropNotProof.AppCase env U n := by
  intro _ _ _ _ _ _ hf ha hT hp H2
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := H2.app_inv
  exact h ⟨hf, ha, hf₁, ha₁⟩ hT hp hc

theorem AppNotProof.iff : env.AppNotProof U n ↔ PropNotProof.AppCase env U n :=
  ⟨AppNotProof.appCase, AppNotProof.of_appCase⟩

theorem AppPropAgree.of_appCase (h : PropTypeAgree.AppCase env U n) :
    env.AppPropAgree U n := by
  intro _ _ _ _ _ _ _ _ d ihf c₁ hp
  exact h d.fn₀ d.arg₀ ihf (.conv c₁ d.hasType₁) hp

theorem AppPropAgree.appCase (h : env.AppPropAgree U n) : PropTypeAgree.AppCase env U n := by
  intro _ _ _ _ _ _ hf ha ihf H2 hp
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := H2.app_inv
  exact h ⟨hf, ha, hf₁, ha₁⟩ ihf hc hp

theorem AppPropAgree.iff : env.AppPropAgree U n ↔ PropTypeAgree.AppCase env U n :=
  ⟨AppPropAgree.appCase, AppPropAgree.of_appCase⟩


/-! ## 3. The unifier: `thm:utype`'s own application case

The five differ only in what they conclude *about* the pair `(B₀.inst a, B₁.inst a)`.  The
statement that decides all of them at once is the one `unique.tex:51` was trying to reach: the
two instantiated codomains are convertible. -/

/-- **`thm:utype`'s application case, at the index.**  `unique.tex:51` derives exactly this
(from `DefInv` clause (2) plus `SubstC`); `SubstC` is false, so the derivation is gone, but the
statement is not the derivation. -/
def AppTypeUniq (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ → env.IsDefEqN U n Γ (B₀.inst a) (B₁.inst a)

/-- **Unique typing at the index** — `thm:utype`'s conclusion, as a statement in its own right
(`Stratified.uniq` is the same thing carrying `DefInv` and `SubstC` as hypotheses). -/
def UniqN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr},
    env.HasTypeN U n Γ e A → env.HasTypeN U n Γ e B → env.IsDefEqN U n Γ A B

theorem UniqN.appTypeUniq (h : env.UniqN U n) : env.AppTypeUniq U n := by
  intro _ _ _ _ _ _ _ d; exact h d.hasType₀ d.hasType₁

theorem UniqN.zero : env.UniqN U 0 := fun h1 h2 =>
  IsDefEqN.zero_iff.2 (HasTypeN.uniq_zero h1 h2)

theorem AppTypeUniq.zero : env.AppTypeUniq U 0 := UniqN.zero.appTypeUniq

/-- `UniqN` is exactly `HasTypeN.uniq`'s conclusion, so `Stratified.uniq` is a proof of it from
`DefInv` + `SubstC`. -/
theorem UniqN.of_defInv_substC (dinv : env.DefInv U n) (hs : env.SubstC U n) :
    env.UniqN U n := fun h1 h2 => HasTypeN.uniq dinv hs h1 h2

/-! ### It discharges all five, each with the residual that statement already names -/

theorem AppTypeUniq.appDisj (dinv : env.DefInv U n) (h : env.AppTypeUniq U n) :
    env.AppDisj U n := by
  intro _ _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact dinv.sort_forallE
    (IsDefEqN.trans' (IsDefEqN.symm' c₀) (IsDefEqN.trans' (h d) c₁))

theorem AppTypeUniq.appPropDisj (dinv : env.DefInv U n) (h : env.AppTypeUniq U n) :
    env.AppPropDisj U n := by
  intro _ _ _ _ _ _ _ _ _ d c₀ c₁; exact h.appDisj dinv d c₀ c₁

theorem AppTypeUniq.appUniqLvl (dinv : env.DefInv U n) (h : env.AppTypeUniq U n) :
    env.AppUniqLvl U n := by
  intro _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact VLevel.equiv_congr_left
    (dinv.sort (IsDefEqN.trans' (IsDefEqN.symm' c₀) (IsDefEqN.trans' (h d) c₁)))

theorem AppTypeUniq.appNotProof (hsnp : env.SortNotProp U n) (h : env.AppTypeUniq U n) :
    env.AppNotProof U n := by
  intro _ _ _ _ _ _ _ _ d c₀ hp c₁
  exact hsnp
    (IsDefEqN.trans' (IsDefEqN.symm' c₁) (IsDefEqN.trans' (IsDefEqN.symm' (h d)) c₀)) hp

theorem AppTypeUniq.appPropAgree (pci : env.PropConvInv U n) (h : env.AppTypeUniq U n) :
    env.AppPropAgree U n := by
  intro _ _ _ _ _ _ _ _ d _ c₁ hp
  exact (pci (IsDefEqN.trans' (h d) c₁)).1 hp

/-! ## 4. …and it is FALSE

The witness is `ShapeSpine.lean`'s, unchanged.  `SubstCRefute` declined to claim a refutation
of `thm:utype`'s *statement* because its counterexample supplied no single term carrying both
Π types; `ShapeAgreeRefute` supplies exactly that, and this section draws the consequence.

    A := .sort (succ p)     D := (fun _ : A => x) x     P := ∀ (_ : A), D      (P closed)

    [P] ⊢₁ .bvar 0 : ∀ (_ : A), D            (the variable, at its declared type)
    [P] ⊢₁ .bvar 0 : ∀ (_ : A), .bvar 0      (retyped along `forallEDF` of the beta step)
    [P] ⊢₁ a : A                             (one `sortDF`)

so `AppData` holds at `f = .bvar 0`, `a = a`, and the two instantiated codomains are
`D.inst a = lhs` — stuck, `⊢₁`-related to nothing but itself — and `(.bvar 0).inst a = a`. -/

namespace AppCaseRefute
open SubstCRefute ShapeAgreeRefute

/-- The premise bundle, at the witness. -/
theorem witness : AppData (∅ : VEnv) 1 1 [P] (.bvar 0) a A D A (.bvar 0) :=
  ⟨hx, a_hasType1, hx2, a_hasType1⟩

/-- `lhs` and `a` are not `⊢₁`-convertible: `stuck`. -/
theorem lhs_not_conv_a {Γ : List VExpr} : ¬ (∅ : VEnv).IsDefEqN 1 1 Γ lhs a := fun h =>
  absurd ((stuck h rfl rfl).1 rfl) (by simp [a, lhs])

/-- **`thm:utype`'s application case is false at `n = 1`**, over the empty environment. -/
theorem appTypeUniq_false : ¬ (∅ : VEnv).AppTypeUniq 1 1 := fun h => lhs_not_conv_a (h witness)

/-- **Unique typing at the index is false at `n = 1`**, over the empty environment.

`docs/reference-gap-thm-utype.md` §4 lists "`thm:utype`'s statement" under *not refuted*, on
the ground that the `SubstC` counterexample supplies no single term with both Π types.  That
gap is now filled, and the verdict changes — see the module note below for the one hypothesis
this does **not** discharge. -/
theorem uniqN_false : ¬ (∅ : VEnv).UniqN 1 1 := fun h => appTypeUniq_false h.appTypeUniq

/-- The same, spelled out: a term, two `⊢₁` types, no `⊢₁` conversion between them. -/
theorem uniqN_witness :
    ∃ (Γ : List VExpr) (e A' B' : VExpr),
      (∅ : VEnv).HasTypeN 1 1 Γ e A' ∧ (∅ : VEnv).HasTypeN 1 1 Γ e B' ∧
      ¬ (∅ : VEnv).IsDefEqN 1 1 Γ A' B' :=
  ⟨[P], .app (.bvar 0) a, lhs, a, happ1, happ2, lhs_not_conv_a⟩

/-- **The dichotomy.**  `thm:utype` (`unique.tex:40`) is stated *under* the hypothesis that
`⊢ₙ` has definitional inversion, and `DefInv ∅ 1 1` is not known.  Either it holds — and then
`thm:utype` is false at `n = 1`, not merely unproved — or it fails, and the route's own target
`∀ n, DefInv` fails at its first non-trivial index.  Either way the reference's induction
`DefInv n → uniq n → DefInv (n+1)` cannot be repaired at `n = 1`. -/
theorem thm_utype_one_false_of_defInv (hdinv : (∅ : VEnv).DefInv 1 1) :
    ¬ ((∅ : VEnv).DefInv 1 1 → (∅ : VEnv).UniqN 1 1) := fun h => uniqN_false (h hdinv)

/-- **A cross-check on the two witnesses.**  `SubstCRefute.substC_false` refutes `SubstC 1`
directly; this rederives it (weakened by a `DefInv` hypothesis) from `uniqN_false` through
`Stratified.uniq`.  The two counterexamples are the same construction seen from the two sides
of `unique.tex:51` — one at the *conversion* it produces, one at the *typing* it was produced
for — and they agree. -/
theorem substC_false_of_defInv (hdinv : (∅ : VEnv).DefInv 1 1) : ¬ (∅ : VEnv).SubstC 1 1 :=
  fun hs => uniqN_false (UniqN.of_defInv_substC hdinv hs)

/-- **The environment is not junk.**  `∅` is `Ordered`; `ShapeSpine.lean`'s `P_type` shows the
one-entry context `[P]` is a genuine Π-type at the index, so the refutation does not turn on a
malformed environment or a malformed context. -/
theorem witness_env_ordered : (∅ : VEnv).Ordered := .empty

/-! ### What the witness does *not* refute

`docs/handoff-stratified.md` §16.4 records, as a **reading result**, that this witness refutes
none of the five.  Machine-checked here for the three shape statements; the two propositional
ones need one more fact, recorded honestly below. -/

/-- `lhs` is not Π-shaped either — same `stuck` argument as `lhs_not_sortLike`. -/
theorem lhs_not_piLike {Γ : List VExpr} {A' B' : VExpr} :
    ¬ (∅ : VEnv).IsDefEqN 1 1 Γ lhs (.forallE A' B') := fun h =>
  absurd ((stuck h rfl rfl).1 rfl) (by simp [lhs])

/-- **The witness refutes no shape statement.**  Of the two types it supplies, `a` is a sort
and `lhs` is neither sort-shaped nor Π-shaped — so the pair is neither a (sort, Π) pair
(`SortForallEDisjoint`, `PropForallEDisjoint`) nor a (sort, sort) pair (`PropUniq`). -/
theorem witness_shapes :
    (∅ : VEnv).SortLike 1 1 [P] a ∧
    ¬ (∅ : VEnv).SortLike 1 1 [P] lhs ∧
    ¬ ∃ A' B', (∅ : VEnv).IsDefEqN 1 1 [P] lhs (.forallE A' B') :=
  ⟨a_sortLike, lhs_not_sortLike, fun ⟨_, _, h⟩ => lhs_not_piLike h⟩

/-- `lhs` is `⊢₁`-typed at `A = .sort (succ p)`. -/
theorem lhs_hasType {Γ : List VExpr} : (∅ : VEnv).HasTypeN 1 1 Γ lhs A :=
  Stratified.app (A := A) (B := A) (Stratified.lam A_type (.bvar .zero)) a_hasType1

/-- **The propositional half, conditionally.**  For `PropNotProof` and `PropTypeAgree` the
witness would have to make one of its two types a *proposition*; `a` is a sort, so `DefInv`
excludes it there, and `lhs` is excluded by `PropUniq` at the same index — which this witness
does not refute.  So the witness refutes those two only if it refutes `PropUniq`, and it does
not. -/
theorem lhs_not_isPropN (huniq : (∅ : VEnv).PropUniq 1 1) {Γ : List VExpr} :
    ¬ IsPropN (∅ : VEnv) 1 1 Γ lhs := fun hp =>
  absurd (congrFun ((huniq lhs_hasType hp).2 (by rfl)) []) (by simp [A, VLevel.eval])

end AppCaseRefute


/-! ## 5. Can a *strengthened induction* close the `app` case?  — No, and here is why

`appCase_ih_vacuous` (`Theory/Typing/UnivDiscrim.lean`) diagnoses the `app` case as an
induction hypothesis with no content at the function position.  The repair that suggests
itself is to induct on a *stronger* conclusion: instead of "no term has both a sort type and a
Π type", prove "any two types of a term stand in `R`", for some relation `R` informative
enough to survive the `app` step.

Three conditions are what such an `R` has to satisfy, and they are exactly what the induction
consumes:

* **(i)** `R` relates any two types of any term — the strengthened conclusion;
* **(ii)** `R` is closed under the `app` step: from `R` at two Π-types of `f` and an argument
  typed at both domains, `R` at the two instantiated codomains;
* **(iii)** `R` separates sorts from Π-types — what makes the strengthening imply the target.

`relStrengthening_sound` below is the induction step this buys.  The two theorems after it are
the closure: **(iii) for any `R` satisfying (i) already implies the statement**, so no choice
of `R` makes the remaining obligation cheaper, and at the two extreme choices the content
simply moves — at the minimal `R` (i) and (ii) are free and (iii) is the statement; at the
maximal usable `R` (iii) is free and (i) is the statement, while (ii) is outright false. -/

/-- (i) `R` relates any two types of any term. -/
def RelTypePairs (env : VEnv) (U n : Nat) (R : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {e T₁ T₂ : VExpr},
    env.HasTypeN U n Γ e T₁ → env.HasTypeN U n Γ e T₂ → R Γ T₁ T₂

/-- (ii) `R` is closed under the `app` case's step. -/
def RelInstClosed (env : VEnv) (U n : Nat) (R : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {A₀ B₀ A₁ B₁ a : VExpr},
    R Γ (.forallE A₀ B₀) (.forallE A₁ B₁) →
    env.HasTypeN U n Γ a A₀ → env.HasTypeN U n Γ a A₁ → R Γ (B₀.inst a) (B₁.inst a)

/-- (iii) `R` separates sorts from Π-types. -/
def RelSeparates (env : VEnv) (U n : Nat) (R : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {T₁ T₂ A B : VExpr} {u : VLevel},
    R Γ T₁ T₂ → env.IsDefEqN U n Γ T₁ (.sort u) →
    env.IsDefEqN U n Γ T₂ (.forallE A B) → False

/-- **The strengthening does work, when it exists.**  (i) + (ii) + (iii) close the `app` case
outright. -/
theorem relStrengthening_sound {R : List VExpr → VExpr → VExpr → Prop}
    (h1 : env.RelTypePairs U n R) (h2 : env.RelInstClosed U n R)
    (h3 : env.RelSeparates U n R) : env.AppDisj U n := by
  intro _ _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact h3 (h2 (h1 d.fn₀ d.fn₁) d.arg₀ d.arg₁) c₀ c₁

/-- **…and it never makes the remaining obligation cheaper.**  Any `R` satisfying (i) and (iii)
already proves `SortForallEDisjoint` — with no induction, and without (ii).  So a strengthened
induction can only *add* obligations; (iii) is never weaker than the target it is meant to
reach. -/
theorem sortForallEDisjoint_of_rel {R : List VExpr → VExpr → VExpr → Prop}
    (h1 : env.RelTypePairs U n R) (h3 : env.RelSeparates U n R) :
    env.SortForallEDisjoint U n := fun hs hp => h3 (h1 hs hp) .rfl .rfl

/-! ### The two extreme choices of `R`, and what each costs -/

/-- The **minimal** `R` satisfying (i): "the two types have a common inhabitant". -/
def RelTaut (env : VEnv) (U n : Nat) (Γ : List VExpr) (T₁ T₂ : VExpr) : Prop :=
  ∃ e, env.HasTypeN U n Γ e T₁ ∧ env.HasTypeN U n Γ e T₂

theorem RelTaut.typePairs : env.RelTypePairs U n (env.RelTaut U n) := fun h1 h2 => ⟨_, h1, h2⟩

/-- (ii) is **free** at the minimal `R`: the common inhabitant of the two codomains is the
application. -/
theorem RelTaut.instClosed : env.RelInstClosed U n (env.RelTaut U n) := by
  intro _ _ _ _ _ _ h ha₀ ha₁
  obtain ⟨f, hf₀, hf₁⟩ := h
  exact ⟨.app f _, .app hf₀ ha₀, .app hf₁ ha₁⟩

/-- …and (iii) at the minimal `R` **is** `SortForallEDisjoint`.  This is the fixpoint of §9 of
the handoff, read off the schema: the strengthening moves the whole content into (iii). -/
theorem RelTaut.separates_iff :
    env.RelSeparates U n (env.RelTaut U n) ↔ env.SortForallEDisjoint U n :=
  ⟨fun h => sortForallEDisjoint_of_rel RelTaut.typePairs h,
   fun h _ _ _ _ _ _ hr c₁ c₂ =>
     have ⟨_, he₁, he₂⟩ := hr
     h (.conv c₁ he₁) (.conv c₂ he₂)⟩

/-- The **maximal usable** `R`: disjointness itself, asserted of the pair. -/
def RelDisj (env : VEnv) (U n : Nat) (Γ : List VExpr) (T₁ T₂ : VExpr) : Prop :=
  ∀ {u : VLevel} {A B : VExpr}, env.IsDefEqN U n Γ T₁ (.sort u) →
    env.IsDefEqN U n Γ T₂ (.forallE A B) → False

/-- (iii) is **free** at the maximal `R`. -/
theorem RelDisj.separates : env.RelSeparates U n (env.RelDisj U n) := fun h c₁ c₂ => h c₁ c₂

/-- …and (i) at the maximal `R` **is** `SortForallEDisjoint`.  The content has moved, not
shrunk — trap #11 in the schema. -/
theorem RelDisj.typePairs_iff :
    env.RelTypePairs U n (env.RelDisj U n) ↔ env.SortForallEDisjoint U n :=
    by
  refine ⟨fun h => sortForallEDisjoint_of_rel h RelDisj.separates, fun h => ?_⟩
  intro _ _ _ _ he₁ he₂ _ _ _ c₁ c₂
  exact h (.conv c₁ he₁) (.conv c₂ he₂)

/-- **And (ii) at the maximal `R` is FALSE**, already at the base index and over the empty
environment: two Π-types whose codomains are a constant sort and a constant Π satisfy the
premise vacuously and fail the conclusion.  So the disjointness relation cannot be carried
through the induction, which is the vacuity of `appCase_ih_vacuous` stated as a closure
failure. -/
theorem relDisj_instClosed_false :
    ¬ (∅ : VEnv).RelInstClosed 1 0 ((∅ : VEnv).RelDisj 1 0) := by
  intro h
  refine h (Γ := []) (A₀ := SubstCRefute.A) (B₀ := .sort SubstCRefute.p)
    (A₁ := SubstCRefute.A) (B₁ := .forallE (.sort SubstCRefute.p) (.sort SubstCRefute.p))
    (a := .sort SubstCRefute.p) ?_ (Stratified.sort SubstCRefute.p_wf)
    (Stratified.sort SubstCRefute.p_wf) .rfl .rfl
  intro _ _ _ h1 _
  exact absurd (IsDefEqN.zero_iff.1 h1) (by simp)

/-! ## 6. The other natural strengthening: carry the Π *components* — also FALSE

The relation the `app` case would really like is not disjointness but "two Π-types of one term
have convertible codomains": with it, `SubstDisj` (`Theory/Typing/ShapeSpine.lean`) closes the
case in one step, and neither statement is `SortForallEDisjoint` in disguise.  It is
`thm:utype` restricted to Π-typed subjects — and the `ShapeAgreeRefute` witness, lifted through
one λ, refutes it. -/

/-- **Unique typing restricted to Π-types**, componentwise on the codomain. -/
def PiCodConv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f A₀ B₀ A₁ B₁ : VExpr},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ f (.forallE A₁ B₁) →
    env.IsDefEqN U n (A₀ :: Γ) B₀ B₁

theorem PiCodConv.zero : env.PiCodConv U 0 := by
  intro _ _ _ _ _ _ h1 h2
  injection HasTypeN.uniq_zero h1 h2 with _ e
  exact IsDefEqN.zero_iff.2 e

/-- **What it would buy**: with `SubstDisj` it closes the `app` case, with no induction on a
spine and no appeal to `SubstC`. -/
theorem PiCodConv.appDisj (h : env.PiCodConv U n) (hs : env.SubstDisj U n) :
    env.AppDisj U n := by
  intro _ _ _ _ _ _ _ _ _ _ d c₀ c₁
  exact hs d.arg₀ (h d.fn₀ d.fn₁) (.nil .rfl) (.nil .rfl) c₀ c₁

namespace AppCaseRefute
open SubstCRefute ShapeAgreeRefute

theorem hbeta₂ : (∅ : VEnv).IsDefEqN 1 1 [A, A, P] D (.bvar 0) :=
  .beta (.bvar .zero) (.bvar .zero)

theorem hpi₂ : (∅ : VEnv).IsDefEqN 1 1 [A, P] P (.forallE A (.bvar 0)) :=
  .forallEDF .rfl hbeta₂

theorem hx₂ : (∅ : VEnv).HasTypeN 1 1 [A, P] (.bvar 1) P :=
  Stratified.bvar (.succ .zero)

theorem hx₂' : (∅ : VEnv).HasTypeN 1 1 [A, P] (.bvar 1) (.forallE A (.bvar 0)) :=
  .conv hpi₂ hx₂

/-- The λ-lift of the witness: one term with **two Π-types**, whose codomains are `lhs` and
`a`.  This is the hypothesis `PiCodConv` consumes. -/
theorem hlam₀ : (∅ : VEnv).HasTypeN 1 1 [P] (.lam A (.app (.bvar 1) a)) (.forallE A lhs) :=
  Stratified.lam A_type (Stratified.app hx₂ a_hasType1)

theorem hlam₁ : (∅ : VEnv).HasTypeN 1 1 [P] (.lam A (.app (.bvar 1) a)) (.forallE A a) :=
  Stratified.lam A_type (Stratified.app hx₂' a_hasType1)

/-- **`PiCodConv` is false at `n = 1`** over the empty environment.

So the failure of unique typing at the index is *not* confined to types that are neither sorts
nor Π's: it is already present at a term whose two types are both Π-types.  The
`PiCodConv` + `SubstDisj` decomposition of the `app` case is therefore closed. -/
theorem piCodConv_false : ¬ (∅ : VEnv).PiCodConv 1 1 := fun h =>
  lhs_not_conv_a (h hlam₀ hlam₁)

end AppCaseRefute

/-! ## 7. Induction on the index does not run in the useful direction

Four of the five statements are **antitone** in `n` (`Stratified.mono` moves their hypotheses
up), so `S (n+1) → S n` is free and `S n → S (n+1)` is the entire content.  There is no
strengthening to be had from the index either.  `PropTypeAgree` is the exception and is
neither monotone nor antitone: its conclusion `IsPropN` is itself a typing at the index. -/

theorem SortForallEDisjoint.antitone {m : Nat} (le : m ≤ n)
    (h : env.SortForallEDisjoint U n) : env.SortForallEDisjoint U m :=
  fun h1 h2 => h (h1.mono le) (h2.mono le)

theorem PropForallEDisjoint.antitone {m : Nat} (le : m ≤ n)
    (h : env.PropForallEDisjoint U n) : env.PropForallEDisjoint U m :=
  fun h1 h2 => h (h1.mono le) (h2.mono le)

theorem PropNotProof.antitone {m : Nat} (le : m ≤ n)
    (h : env.PropNotProof U n) : env.PropNotProof U m :=
  fun h1 h2 h3 => h (h1.mono le) (h2.mono le) (h3.mono le)

theorem PropUniq.antitone {m : Nat} (le : m ≤ n)
    (h : env.PropUniq U n) : env.PropUniq U m :=
  fun h1 h2 => h (h1.mono le) (h2.mono le)


/-! ## 8. The schema filled in: four candidate relations, four machine-checked failures

| `R Γ T₁ T₂` | (i) type-pairs | (ii) inst-closed | (iii) separates |
|---|---|---|---|
| `∃ e, e : T₁ ∧ e : T₂` (`RelTaut`) | free | free | **= the statement** |
| `T₁ ≡ₙ T₂` (unique typing) | **false** (`uniqN_false`) | **false** (`relConv_instClosed_false`) | free, from `DefInv` |
| `SortLike T₁ ↔ SortLike T₂` | **false** (`relShape_typePairs_false`) | false | free |
| disjointness (`RelDisj`) | **= the statement** | **false** (`relDisj_instClosed_false`) | free |

Every row either fails outright or reproduces the statement.  Nothing between the extremes has
been found, and the schema says what such a thing would have to be: a relation *strictly*
between "common inhabitant" and "disjointness" that is closed under codomain instantiation. -/

namespace AppCaseRefute
open SubstCRefute ShapeAgreeRefute

/-- Row 2, column (ii): `R := ⊢ₙ`-conversion is not closed under codomain instantiation.  This
is `SubstCRefute.defInv_forallE_inst_false` read in the schema. -/
theorem relConv_instClosed_false :
    ¬ (∅ : VEnv).RelInstClosed 1 1 (fun Γ T₁ T₂ => (∅ : VEnv).IsDefEqN 1 1 Γ T₁ T₂) := by
  intro h
  have hpi : (∅ : VEnv).IsDefEqN 1 1 []
      (.forallE A (.app (.lam A (.bvar 0)) (.bvar 0))) (.forallE A (.bvar 0)) :=
    .forallEDF .rfl hBB'
  exact lhs_not_conv_a (h hpi a_hasType1 a_hasType1)

/-- Row 3, column (i): `R := ` shape agreement does not hold of every pair of types of a term.
This is `ShapeSpine.typeShapeAgree_false` read in the schema. -/
theorem relShape_typePairs_false :
    ¬ (∅ : VEnv).RelTypePairs 1 1
        (fun Γ T₁ T₂ => ((∅ : VEnv).SortLike 1 1 Γ T₁ ↔ (∅ : VEnv).SortLike 1 1 Γ T₂)) :=
  fun h => typeShapeAgree_false fun h1 h2 => h h1 h2

/-! ### The counterexample is about the *index*, not about the terms

At `n = 2` the very same pair is convertible — one `beta` step, whose typing premises are now
allowed to sit at index `1`, which is exactly where `a`'s `sortDF` retyping lives.  So
`∀ n, UniqN n` fails while a *slackened* unique typing ("the two types are convertible at some
larger index") survives at this witness.  Slack is what `Stratified.instN` gives (`m + n`), and
it is precisely what the reference's induction cannot consume: `DefInv (n+1)` wants unique
typing at `n`, and a conclusion at `2n` cannot be lowered
(`docs/reference-gap-thm-utype.md` §2). -/

/-- The witness's two types **are** convertible one index up. -/
theorem lhs_conv_a_succ : (∅ : VEnv).IsDefEqN 1 2 [P] lhs a :=
  Stratified.beta (Stratified.bvar Lookup.zero) a_hasType1

/-- `UniqN` is neither monotone nor antitone in the index: its hypotheses rise with `n` and so
does its conclusion.  Here is the half that matters — the failure at `1` is not inherited
at `2` by this witness. -/
theorem uniqN_witness_repaired_at_two :
    ¬ (∅ : VEnv).IsDefEqN 1 1 [P] lhs a ∧ (∅ : VEnv).IsDefEqN 1 2 [P] lhs a :=
  ⟨lhs_not_conv_a, lhs_conv_a_succ⟩

end AppCaseRefute


/-! ## 9. The `Theory/SetModel/` route does not reach any of these — it is a different statement

*Source reading, plus one machine check; it cannot be a cone, and here is why.*

`Theory/SetModel/PropUniqFromFalse.lean` derives `PropUniq` from `PropTypeAgree`
(`PropUniq.of_propTypeAgree`), which looks like it would discharge one of the five.  **It is
not the same `PropUniq`.**  The name `Lean4Lean.VEnv.PropUniq` is declared twice in this
repository, with different arities and over different judgments:

* `Theory/Typing/PropShadow.lean:183` — `PropUniq (env : VEnv) (U n : Nat)`, over
  `HasTypeN` (the alternation index), conclusion `u ≈ .zero ↔ v ≈ .zero`.  This is the one in
  the five-statement table and the one `AppUniqLvl` is about.
* `Theory/SetModel/PropSplitAudit.lean:105` — `PropUniq (env : VEnv) (nv : ℕ)`, over the
  **unstratified** `HasType`, with `u.WF nv`/`v.WF nv` premises and a conclusion at one fixed
  valuation, `u.eval ls = 0 ↔ v.eval ls = 0`.

`Lean4Lean.VEnv.PropTypeAgree` is likewise declared twice
(`Theory/Typing/UniqueTypingN.lean:562` and `Theory/SetModel/PropSplitAudit.lean:119`), and the
two differ by more than the judgment: the `SetModel` one takes the sorts of *both* types as
premises and concludes pointwise at `ls`.

**Machine-checked**: the two module trees cannot be imported together at all — `import`ing
`Theory.SetModel.PropUniqFromFalse` after `Theory.Typing.UniqueTypingN` is rejected outright
("environment already contains `Lean4Lean.VEnv.PropTypeAgree`").  So no declaration in this
repository can state, let alone prove, a relation between the two.  Any claim of the form
"the model stream's `PropUniq` discharges the syntactic stream's" is unmeasurable as the tree
stands; **the two names must be disambiguated before either stream quotes the other.**

Three further reasons the route does not reach the `app` case even after the names are fixed,
recorded because they are independent of the collision:

1. **No stratification.**  `HasTypeN` and `Stratified` do not occur anywhere in
   `Theory/SetModel/` (checked by search).  All five `app` cases are statements at an index.
2. **Its hypothesis is inconsistency.**  `PropUniq.of_propTypeAgree` takes
   `∃ e, env.HasType 0 [] e falseProp` — an inhabitant of `∀ p : Prop, p` — which
   `PropUniqFromFalse.lean`'s own note says is "available inside the consistency proof and
   nowhere else".  It is not available over `∅`, which is where every witness in this file and
   in `SubstCRefute`/`ShapeAgreeRefute` lives.
3. **One of five is not five.**  Even granting the statement, `AppUniqLvl.iff` says
   `PropUniq.AppCase ↔ PropUniq`, so a proof of `PropUniq` closes *its own* `app` case and
   says nothing about the other four — §16.4's "not claimed: that the five are one statement"
   cuts here too.
-/

end VEnv
end Lean4Lean
