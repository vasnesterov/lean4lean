import Lean4Lean.Theory.Typing.AppCase

/-!
# `DefInv ∅ 1 1` is false — the dichotomy resolves, and it resolves against the route

`Theory/Typing/AppCase.lean` §4 leaves one question open, and states it as a dichotomy
(`AppCaseRefute.thm_utype_one_false_of_defInv`):

> Is `DefInv ∅ 1 1` true?  If **yes**, `thm:utype` (`unique.tex:40`) is false at `n = 1`.  If
> **no**, the route's own target `∀ n, DefInv env U n` fails over the empty environment at its
> first non-trivial index.

**It is no.**  `defInv_one_false` below refutes `DefInv ∅ 1 1` — specifically its clause (2),
the reference's `unique.tex:33` — at `n = 1`, over the empty environment, in a well-formed
one-entry context.

## The counterexample

One universe parameter `p := .param 0`, `∅` for the environment, so no constants and no
`defeqs`.  Two syntactically distinct but level-equivalent sorts, and one β-redex:

    dom  := .sort (max p p)     dom' := .sort p          (max p p ≈ p, and max p p ≠ p)
    cod  := (fun _ : dom' => x) x                        (x = .bvar 0, the ∀-bound variable)

Then, in the empty context,

    [] ⊢₁ ∀ x : dom.  x  ≡  ∀ x : dom'. cod

by two `forallEDF` steps composed with `trans`:

* `∀x:dom. x ≡ ∀x:dom'. x` — domains by `sortDF` (`max p p ≈ p`), codomains by `rfl`, which
  here is the *typed* reflexivity the reference has (`[dom] ⊢₀ x : dom` holds);
* `∀x:dom'. x ≡ ∀x:dom'. cod` — domains by `rfl`, codomains by one `beta` step **in the
  context `[dom']`**, where `x` is declared at `dom'` and the redex's annotation matches.

Clause (2) would return the codomain conversion **in the left context `[dom]`**:

    [dom] ⊢₁ x ≡ (fun _ : dom' => x) x

and that is false.  In `[dom]` the variable's unique `⊢₀` type is `dom`, not `dom'`, so `cod`
is not `⊢₀`-typeable there at all (`cod_not_hasType0`), and the `stuck` induction below — the
`SubstCRefute.stuck` argument, re-run with the context as a parameter — says `⊢₁` relates it
to nothing but itself.

**The guilty step is the context, not the term.**  Every rule of `⊢₁` that could move `cod`
carries a typing premise at `⊢₀` about the variable, and `⊢₀` has no conversion, so the
`sortDF` that makes `dom` and `dom'` interchangeable at `⊢₁` is unavailable one level down.
Clause (2) as stated transports a conversion from the context `Γ, x:α'` to the context
`Γ, x:α`, and `⊢₁` is not invariant under that transport.

## Scope — three separate claims, kept separate

1. **The stratified statement.**  `DefInv ∅ 1 1` is **false** (machine-checked).  So is
   `∀ n, DefInv ∅ 1 n` (`defInv_all_false`).  Both readings of clause (2)'s context are
   refuted: the left-domain reading by `defInv_one_false`, the right-domain reading by
   `defInv_forallE_right_false` (the same instance, `symm`'d).

2. **The reference's theorem.**  Clause (2) of `unique.tex:33` is transcribed here without
   deviation — the reference's ∀-congruence rule (`axioms.tex:37`) carries **no** typing
   premises, its β rule's premises are exactly the two used here, and the two `rfl`s used are
   backed by `⊢₀` typings, so the repo's one documented deviation (unconditional `rfl`) is
   **not** load-bearing.  Consequently `thm:1dinv` (`unique.tex:262`, "⊢ₙ₊₁ has definitional
   inversion") is false at `n + 1 = 1`, and the induction of `unique.tex`'s final proof cannot
   pass its first step.  `thm:utype`'s own *statement* is **not** refuted by this: at `n = 1`
   over `∅` its hypothesis is false, so `AppCaseRefute.thm_utype_one_false_of_defInv` is
   vacuous and `thm_utype_one_vacuous` below is a proof of `thm:utype` at that instance.

3. **Lean's type theory.**  Nothing.  `cod_conv_bvar_succ` machine-checks that the very
   conversion clause (2) asks for **does** hold one index up, `[dom] ⊢₂ x ≡ cod`, by the
   `sortDF` that retypes `x` at `dom'`.  What fails is definitional inversion *at a fixed
   alternation index*, which is the only form the reference's induction can consume.

## What survives, and it is the part that matters

`IsDefEqU.sort_inv_of_defInv` and `IsDefEqU.sort_forallE_inv_of_defInv`
(`Theory/Typing/UniqueTypingN.lean`) — the two reductions that still carry the route to
`Theory/Typing/Injectivity.lean`'s open sort goals — use `dinv n` at exactly one projection
each, `.sort` and `.sort_forallE`.  **Neither consumes clause (2).**  Restated against the
clause each actually uses (`sort_inv_of_sortInvN`, `sort_forallE_inv_of_sortForallEDisjN`
below) they go through verbatim, and their hypotheses `∀ n, SortInvN` / `∀ n, SortForallEDisjN`
are **not** refuted by anything known.

So the practical reading is not "the route is dead" but "the route was stated against a
hypothesis three times stronger than it needs, and the extra strength is what is false".

## What is not settled here

Clauses (1) and (3) of `DefInv ∅ 1 1` — the sort and sort/Π clauses, i.e. `SortInvN ∅ 1 1` and
`SortForallEDisjN ∅ 1 1`.  Neither is proved nor refuted; this witness does not reach them (it
never relates a sort to a non-sort).  Since `DefInv` is a structure, refuting clause (2)
refutes `DefInv`, so they are not needed for the verdict, but they remain open — and by the
paragraph above they are now the only clauses anything downstream wants.
-/

namespace Lean4Lean
namespace VEnv
namespace DefInvRefute

open SubstCRefute (p p_wf)

/-! ## The three terms -/

/-- The **left** domain: the ∀-bound variable's declared type on the left-hand Π. -/
def dom : VExpr := .sort (.max p p)

/-- The **right** domain.  `dom ≈ dom'` as types, and `dom ≠ dom'` as syntax — the whole
counterexample is the gap between those two facts. -/
def dom' : VExpr := .sort p

/-- The codomain that is stuck in `[dom]` and reducible in `[dom']`: a β-redex whose λ is
annotated at `dom'` and whose argument is the ∀-bound variable. -/
def cod : VExpr := .app (.lam dom' (.bvar 0)) (.bvar 0)

theorem max_equiv : (VLevel.max p p) ≈ p := by
  simp [VLevel.equiv_def, VLevel.eval]

theorem max_ne : (VLevel.max p p) ≠ p := by simp [p]

/-- The one conversion that is available at `⊢₁` and not at `⊢₀`. -/
theorem hdom {Γ : List VExpr} : (∅ : VEnv).IsDefEqN 1 1 Γ dom dom' :=
  .sortDF (by exact ⟨p_wf, p_wf⟩) (by exact p_wf) max_equiv

/-! ## `cod` is stuck in `[dom]`

Everything in this section is parametric in a context `Γ` in which the variable is *not*
`⊢₀`-typeable at `dom'`.  That hypothesis is the only thing the argument uses, and it is what
makes the failure a statement about the context rather than about the terms. -/

/-- The variable is `⊢₀`-typeable at `dom'` in `[dom']`… -/
theorem bvar_hasType0_right : (∅ : VEnv).HasTypeN 1 0 [dom'] (.bvar 0) dom' :=
  Stratified.bvar Lookup.zero

/-- …and not in `[dom]`, because `⊢₀` typing is syntactically unique and `max p p ≠ p`. -/
theorem bvar_not_hasType0_left : ¬ (∅ : VEnv).HasTypeN 1 0 [dom] (.bvar 0) dom' := by
  intro H
  have h := HasTypeN.uniq_zero (Stratified.bvar (A := dom) Lookup.zero) H
  exact max_ne (by injection h)

/-- With the variable untypeable at `dom'`, the whole redex is untypeable at `⊢₀`: the λ's
annotation forces the argument's type. -/
theorem cod_not_hasType0 {Γ : List VExpr} {T : VExpr}
    (hΓ : ¬ (∅ : VEnv).HasTypeN 1 0 Γ (.bvar 0) dom') :
    ¬ (∅ : VEnv).HasTypeN 1 0 Γ cod T := by
  intro H
  have ⟨C, _, hlam, hb, _⟩ := HasTypeN.app_inv H
  have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hlam
  injection IsDefEqN.zero_iff.1 heq with hAC
  exact hΓ (hAC ▸ hb)

/-- **`cod` is `⊢₁`-related to nothing but itself**, in any context where the variable is not
`⊢₀`-typeable at `dom'`.

This is `SubstCRefute.stuck` with the context carried in the motive rather than eliminated by
closedness.  Every rule of `⊢₁` other than `rfl`/`symm`/`trans` and the four congruences either
has the wrong head shape or carries a `⊢₀` typing premise about one of its two sides, and that
premise is exactly what `hΓ` denies.  The two context-changing congruences (`lamDF`,
`forallEDF`) are discharged by shape, so their induction hypotheses — which would need `hΓ` in
an *extended* context — are never used. -/
theorem stuck {Γ X Y m b} (H : Stratified (∅ : VEnv) 1 m Γ X Y b) :
    1 = m → false = b → ¬ (∅ : VEnv).HasTypeN 1 0 Γ (.bvar 0) dom' →
    (X = cod → Y = cod) ∧ (Y = cod → X = cod) := by
  induction H with
  | bvar | sort | const | app | lam | forallE | conv => intro _ hb _; exact nomatch hb
  | rfl => intro _ _ _; exact ⟨id, id⟩
  | symm _ ih => intro hm hb hΓ; exact ((ih hm hb hΓ).symm : _ ∧ _)
  | trans _ _ ih1 ih2 =>
    intro hm hb hΓ
    exact ⟨fun h => (ih2 hm hb hΓ).1 ((ih1 hm hb hΓ).1 h),
      fun h => (ih1 hm hb hΓ).2 ((ih2 hm hb hΓ).2 h)⟩
  | sortDF | constDF | lamDF | forallEDF =>
    intro _ _ _; constructor <;> (intro h; simp [cod] at h)
  | appDF _ hf hf' _ ha ha' =>
    intro hm _ hΓ
    cases hm
    constructor
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha) hΓ
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf'
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha') hΓ
  | beta he he' =>
    intro hm _ hΓ
    cases hm
    refine ⟨?_, ?_⟩
    · rintro ⟨⟩; exact absurd he' hΓ
    · rintro h
      exact absurd (h ▸ Stratified.instN .empty he' .zero he) (cod_not_hasType0 hΓ)
  | eta he =>
    intro hm _ hΓ
    cases hm
    constructor
    · intro h; simp [cod] at h
    · intro h; exact absurd (h ▸ he) (cod_not_hasType0 hΓ)
  | proofIrrel _ hh hh' =>
    intro hm _ hΓ
    cases hm
    exact ⟨fun h => absurd (h ▸ hh) (cod_not_hasType0 hΓ),
      fun h => absurd (h ▸ hh') (cod_not_hasType0 hΓ)⟩
  | extra h => exact nomatch h

/-- The conversion clause (2) demands, in the **left** domain's context.  It is false. -/
theorem bvar_not_conv_cod : ¬ (∅ : VEnv).IsDefEqN 1 1 [dom] (.bvar 0) cod := by
  intro h
  exact absurd ((stuck h rfl rfl bvar_not_hasType0_left).2 rfl) (by simp [cod])

/-- The same conversion in the **right** domain's context.  It is true — one `beta` step.  So
the two contexts are genuinely different, and clause (2)'s choice of context is load-bearing. -/
theorem bvar_conv_cod_right : (∅ : VEnv).IsDefEqN 1 1 [dom'] (.bvar 0) cod :=
  .symm (.beta (.bvar .zero) (.bvar .zero))

/-! ## The two Π-types -/

/-- `∀ x : dom. x`. -/
def piL : VExpr := .forallE dom (.bvar 0)

/-- `∀ x : dom'. (fun _ : dom' => x) x`. -/
def piR : VExpr := .forallE dom' cod

/-- **The two Π-types are `⊢₁`-convertible**, by two `forallEDF` steps.

Both codomain premises are honest: the first is reflexivity on the variable — available even
under the reference's *typed* reflexivity rule, since `[dom] ⊢₀ x : dom` — and the second is
one `beta` step in `[dom']`, whose two typing premises are `bvar` rules at `⊢₀`. -/
theorem hpi : (∅ : VEnv).IsDefEqN 1 1 [] piL piR :=
  .trans (.forallEDF hdom .rfl) (.forallEDF .rfl bvar_conv_cod_right)

/-- The first `forallEDF` step's codomain premise, stated separately: it is `rfl` *at a term
that is `⊢₀`-typed in that context*, so the repo's unconditional `rfl` is not being used for
anything the reference's typed `rfl` could not do. -/
theorem step1_codomain_typed0 : (∅ : VEnv).HasTypeN 1 0 [dom] (.bvar 0) dom :=
  Stratified.bvar Lookup.zero

/-! ## The contexts and the environment are not junk -/

/-- `∅` is `Ordered` — the same check `AppCaseRefute.witness_env_ordered` makes. -/
theorem env_ordered : (∅ : VEnv).Ordered := .empty

/-- Both domains are genuine types, already at `⊢₀`, so `[dom]` and `[dom']` are well-formed
one-entry contexts and the refutation does not turn on a malformed context. -/
theorem dom_type {Γ : List VExpr} :
    (∅ : VEnv).HasTypeN 1 0 Γ dom (.sort (.succ (.max p p))) :=
  Stratified.sort (by exact ⟨p_wf, p_wf⟩)

theorem dom'_type {Γ : List VExpr} :
    (∅ : VEnv).HasTypeN 1 0 Γ dom' (.sort (.succ p)) := Stratified.sort p_wf

/-- And both Π-types are genuine types at `⊢₁`: `piL` needs no conversion at all, `piR` needs
the variable at `dom'`, which is exactly the `bvar` rule in `[dom']`. -/
theorem piL_type : (∅ : VEnv).HasTypeN 1 1 []
    piL (.sort (.imax (.succ (.max p p)) (.max p p))) :=
  Stratified.forallE (by exact ⟨p_wf, p_wf⟩) (by exact ⟨p_wf, p_wf⟩)
    (dom_type.mono (Nat.zero_le 1)) (Stratified.bvar Lookup.zero)

theorem piR_type : (∅ : VEnv).HasTypeN 1 1 [] piR (.sort (.imax (.succ p) p)) :=
  Stratified.forallE p_wf p_wf (dom'_type.mono (Nat.zero_le 1))
    (Stratified.app (A := dom') (B := dom')
      (Stratified.lam (dom'_type.mono (Nat.zero_le 1)) (Stratified.bvar Lookup.zero))
      (Stratified.bvar Lookup.zero))

/-! ## The refutation -/

/-- **`DefInv ∅ 1 1` is FALSE.**  Clause (2) — `unique.tex:33` — applied to `hpi` returns the
codomain conversion in the left domain's context, and `bvar_not_conv_cod` forbids it. -/
theorem defInv_one_false : ¬ (∅ : VEnv).DefInv 1 1 :=
  fun d => bvar_not_conv_cod (d.forallE hpi).2

/-- The same, spelled out as an explicit witness pair. -/
theorem defInv_one_witness :
    ∃ (Γ : List VExpr) (A B A' B' : VExpr),
      (∅ : VEnv).IsDefEqN 1 1 Γ (.forallE A B) (.forallE A' B') ∧
      ¬ (∅ : VEnv).IsDefEqN 1 1 (A :: Γ) B B' :=
  ⟨[], dom, .bvar 0, dom', cod, hpi, bvar_not_conv_cod⟩

/-- **The route's own target is false**: `⊢ₙ` does not have definitional inversion for every
`n`, over the empty environment.  This is the hypothesis of
`IsDefEqU.sort_inv_of_defInv`/`IsDefEqU.sort_forallE_inv_of_defInv`, so those two reductions
now reduce the open sort goals to something known to be false. -/
theorem defInv_all_false : ¬ ∀ n, (∅ : VEnv).DefInv 1 n :=
  fun h => defInv_one_false (h 1)

/-- **The mirrored reading fails too.**  Stating clause (2) with the codomain conversion in the
*right* domain's context is refuted by the same instance, `symm`'d — so "compare the codomains
under `α'` instead of under `α`" is not a repair. -/
theorem defInv_forallE_right_false :
    ¬ ∀ {Γ : List VExpr} {A B A' B' : VExpr},
        (∅ : VEnv).IsDefEqN 1 1 Γ (.forallE A B) (.forallE A' B') →
        (∅ : VEnv).IsDefEqN 1 1 (A' :: Γ) B B' := by
  intro h
  exact bvar_not_conv_cod (IsDefEqN.symm' (h (.symm hpi)))

/-! ## What survives: the two live reductions consume only clauses (1) and (3)

This is the actionable half of the result.  `IsDefEqU.sort_inv_of_defInv` and
`IsDefEqU.sort_forallE_inv_of_defInv` (`Theory/Typing/UniqueTypingN.lean`) are the two
reductions that still carry the route to `Theory/Typing/Injectivity.lean`'s open sort goals.
Read their proofs: each uses `(dinv n)` at exactly **one** projection — `.sort` and
`.sort_forallE` respectively.  **Neither touches clause (2)**, which is the only clause
refuted above.

So the refutation does *not* kill those reductions; it kills the hypothesis they were stated
against.  Restated against the clause each actually consumes, both go through verbatim, and
their hypotheses are **not** refuted by anything known.  The named forms below are the
statements a repair of `UniqueTypingN.lean` would use.  (Stating them is not editing that
file; the two theorems there are unchanged and still true — their hypothesis is simply now
known to be unsatisfiable over `∅`.) -/

variable {env : VEnv} {U n : Nat}

/-- **Clause (1) of `DefInv`, alone** (`unique.tex:32`).  Open: neither proved nor refuted. -/
def SortInvN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, env.IsDefEqN U n Γ (.sort u) (.sort v) → u ≈ v

/-- **Clause (3) of `DefInv`, alone** (`unique.tex:34`).  Open: neither proved nor refuted. -/
def SortForallEDisjN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr},
    ¬ env.IsDefEqN U n Γ (.sort u) (.forallE A B)

theorem sortInvN_of_defInv (d : env.DefInv U n) : SortInvN env U n := fun h => d.sort h

theorem sortForallEDisjN_of_defInv (d : env.DefInv U n) : SortForallEDisjN env U n :=
  fun h => d.sort_forallE h

theorem sortInvN_zero : SortInvN env U 0 := sortInvN_of_defInv DefInv.zero

theorem sortForallEDisjN_zero : SortForallEDisjN env U 0 :=
  sortForallEDisjN_of_defInv DefInv.zero

/-- `IsDefEqU.sort_inv_of_defInv` with the hypothesis narrowed to the clause it uses. -/
theorem sort_inv_of_sortInvN (henv : Ordered env) {Γ : List VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (dinv : ∀ n, SortInvN env U n)
    (h : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  dinv n hc

/-- `IsDefEqU.sort_forallE_inv_of_defInv` with the hypothesis narrowed to the clause it
uses. -/
theorem sort_forallE_inv_of_sortForallEDisjN (henv : Ordered env) {Γ : List VExpr}
    {u : VLevel} {A B : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (dinv : ∀ n, SortForallEDisjN env U n) :
    ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B) := fun h =>
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  dinv n hc

/-! ## A by-product for clauses (1) and (3): `proofIrrel` never touches a sort, a Π or a λ

These are the `proofIrrel` cases of the two clauses this file leaves open, discharged for any
environment and any context.  They are stated here because `docs/reference-gap-thm-utype.md`
§9a lists `proofIrrel` as one of the two open cases of a direct proof of `DefInv`, and at
`⊢₀`-typed premises it is not open at all: `⊢₀` typing is syntactically unique, and a sort, a Π
and a λ have `⊢₀` types of the shapes `.sort (.succ _)`, `.sort (.imax _ _)` and
`.forallE _ _`, none of which is itself `⊢₀`-typed at `.sort .zero`.

They do **not** close those clauses — `trans` through a β-redex remains, and that is the
confluence obligation. -/

/-- A sort is not a `⊢₀` proof of a `⊢₀` proposition. -/
theorem sort_not_proof0 {Γ : List VExpr} {u : VLevel} {q : VExpr}
    (h : env.HasTypeN U 0 Γ (.sort u) q) (hq : env.HasTypeN U 0 Γ q (.sort .zero)) : False := by
  cases IsDefEqN.zero_iff.1 h.sort_inv.2
  cases IsDefEqN.zero_iff.1 hq.sort_inv.2

/-- A Π-type is not a `⊢₀` proof of a `⊢₀` proposition. -/
theorem forallE_not_proof0 {Γ : List VExpr} {A B q : VExpr}
    (h : env.HasTypeN U 0 Γ (.forallE A B) q) (hq : env.HasTypeN U 0 Γ q (.sort .zero)) :
    False := by
  have ⟨_, _, _, _, _, _, hc⟩ := h.forallE_inv
  cases IsDefEqN.zero_iff.1 hc
  cases IsDefEqN.zero_iff.1 hq.sort_inv.2

/-- A λ is not a `⊢₀` proof of a `⊢₀` proposition. -/
theorem lam_not_proof0 {Γ : List VExpr} {A e q : VExpr}
    (h : env.HasTypeN U 0 Γ (.lam A e) q) (hq : env.HasTypeN U 0 Γ q (.sort .zero)) :
    False := by
  have ⟨_, _, _, _, hc⟩ := h.lam_inv
  cases IsDefEqN.zero_iff.1 hc
  have ⟨_, _, _, _, _, _, hc2⟩ := hq.forallE_inv
  cases IsDefEqN.zero_iff.1 hc2

/-! ## Scope: the same conversion one index up, and `thm:utype` at this instance -/

/-- **The failure is about the index, not about the terms.**  One index up, the `sortDF` that
makes `dom` and `dom'` interchangeable is available *to the typing judgment*, so the variable
is `⊢₁`-typed at `dom'` and the `beta` step goes through — `[dom] ⊢₂ x ≡ cod`.

This is the exact analogue of `AppCaseRefute.lhs_conv_a_succ`, and it is why nothing here is a
claim about Lean's type theory. -/
theorem cod_conv_bvar_succ : (∅ : VEnv).IsDefEqN 1 2 [dom] (.bvar 0) cod :=
  .symm (.beta (n := 1) (.bvar .zero) (.conv hdom (.bvar .zero)))

/-- **The dichotomy of `AppCaseRefute.thm_utype_one_false_of_defInv` resolves to its second
horn.**  `thm:utype` at `n = 1` over `∅` is *vacuously true*: its hypothesis is false.  So
`uniqN_false` refutes the **unconditional** form of `thm:utype` and nothing more, and this
theorem is the honest statement of the conditional form at that instance. -/
theorem thm_utype_one_vacuous : (∅ : VEnv).DefInv 1 1 → (∅ : VEnv).UniqN 1 1 :=
  fun d => absurd d defInv_one_false

/-- The reference's induction (`unique.tex`, proof of `thm:unique`) is
`DefInv n → (§§3–4) → DefInv (n+1)`, with `DefInv 0` proved (`DefInv.zero`).  Its first step is
therefore `DefInv 0 → DefInv 1`, and it is false — the antecedent is a theorem and the
consequent is refuted here.  So the break is in `thm:1dinv`/§§3–4, not only in `thm:utype`. -/
theorem defInv_step_zero_false : ¬ ((∅ : VEnv).DefInv 1 0 → (∅ : VEnv).DefInv 1 1) :=
  fun h => defInv_one_false (h DefInv.zero)

end DefInvRefute
end VEnv
end Lean4Lean
