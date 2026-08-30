import Lean4Lean.Theory.Typing.UnivDiscrim
import Lean4Lean.Theory.Typing.PropShadow

/-!
# `PropTypeAgreeN` and `PropUniqN` at the index, by induction on **typing**

`docs/handoff-stratified.md` §5 records that `PropTypeAgreeN`'s cases reduce, via the
`HasTypeN.*_inv` lemmas, to

    PropConvInv :  Γ ⊢ₙ A ≡ A'  ⟹  (IsPropN A ↔ IsPropN A')

and that "six of twelve conversion cases close, machine-checked in a scratch file".  This file
is that analysis, landed — every case either closes from `DefInv` alone or is reduced to a
**named residual** — plus four results that were not in the scratch.

*(The count is **five**, not six: `rfl`, `symm`, `trans`, `sortDF`, `lamDF`, with seven
residuals, and `5 + 7 = 12`.  §5's own "Open:" list already had seven entries; the top-of-file
table says five.  Corrected in §16.5 of the handoff.)*

## The four new results

1. **`PropUniqN` is not in the `sort_inv`/normalisation family.**  §5's table files it as
   "endpoint-asserted, `trans` fails, needs normalisation".  That verdict is about the *route*
   §5 ran (invert both typings, compose into a sort–sort conversion, induct on **that**), not
   about the statement.  Run the criterion's own first clause — *does the statement's
   induction ever have to look at a conversion derivation at all?* — and the answer is **no**,
   by exactly the manoeuvre `sortForallEDisjoint_of` uses.  `propUniq_of`: **six of seven
   typing cases close from `DefInv` alone, `app` open.**  `PropUniqN` belongs on the
   `SortForallEDisjoint` row, not the `sort_inv` row.

2. **`PropTypeAgreeN` itself closes in six of seven typing cases** from `DefInv` plus its own
   conversion residual (`propTypeAgree_of`), and its `app` case is priced exactly at
   `RegPi` + `InstLvl` + `PropUniqN` + `PropConvInv` (`propTypeAgree_appCase_of`) — the same
   price `Theory/Typing/PropShadow.lean`'s `app_shadow_of` pays for the shadow, plus
   `RegPi`, which the shadow's universe-carrying formulation hid.

3. **`eta`'s residual is sharper than `SortForallEDisjoint`.**  `PropTypeAgreeN.eta_case`
   applies its hypothesis at `u = .zero` and nowhere else, so the case needs only
   `PropForallEDisjoint` — the `u = .zero` instance — whose 6-of-7 case analysis is inherited
   from `sortForallEDisjoint_of`.

4. **`proofIrrel`'s residual has a second reduction that does not go through
   `PropTypeAgreeN`.**  `propNotProof_of` (`UniqueTypingN.lean`) derives `PropNotProof` from
   `PropTypeAgreeN` itself — self-reference, measure `≤` not `<`.  `propNotProof_of'` below
   derives it by the *typing* induction instead and gets six of seven cases from `DefInv` plus
   one new, strictly weaker statement, `SortNotProp`, with only `app` open.

## The answer to "are `eta` and `proofIrrel` one obstruction?"

**One at `app`, two elsewhere**, and the reason is a fact about `DefInv` worth stating alone:

> `DefInv` is a **shape**-inversion principle.  A residual of the form "a term with a sort type
> does not also have a type of kind `X`" is free at every shape-pinned subject when `X` is a
> *syntactic shape* — clause (3) decides `sort` versus `forallE` — and is not free when `X` is
> a *typing* ("… and that type is a proposition"), because `DefInv` transports no typing along
> a conversion.

`eta` is the first kind and pays nothing beyond `DefInv`; `proofIrrel` is the second and pays
`SortNotProp`.  Both then stop at an `app` case with the same subject shape, and
`propNotProof_appCase_ih_vacuous` shows the companion test gives the same answer there as
`appCase_ih_vacuous` does for `SortForallEDisjoint`: the induction hypothesis at the function
is vacuous, so there is nothing at that position to use.

## The convergence

Four statements, four `app` cases, one subject shape:

| statement | cases from `DefInv` | extra | open |
|---|---|---|---|
| `SortForallEDisjoint` (`UniqueTypingN.lean`) | 6 of 7 | — | `app` |
| `PropForallEDisjoint` (= it at `u = 0`) | 6 of 7 | — | `app` |
| `PropNotProof` | 6 of 7 | `SortNotProp` | `app` |
| `PropUniqN` | 6 of 7 | — | `app` |
| `PropTypeAgreeN` | 6 of 7 | `PropConvInv` | `app` |

And each of those `app` cases is **its own statement's fixpoint** — `PropUniqN.appCase`,
`PropNotProof.appCase`, `PropTypeAgreeN.appCase`, `PropForallEDisjoint.appCase`, one line each,
by the same `Stratified.app` + `conv` step that gives `SortForallEDisjoint.appCase`.  So in
every case the `app` position is not a smaller sub-problem; it is the whole remaining content.

*Not claimed*: that the five `app` cases are one statement.  They are not obviously so, and
the natural unifier — "the types of an application agree on shape" — is **false**
(`typeShapeAgree_false`, `Theory/Typing/ShapeSpine.lean`).  *Checked by reading, not
machine-checked*: that witness refutes none of the `app` cases named here, because it supplies
a term with one sort-shaped type and one stuck type, while each case below needs **two**
sort-shaped ones (or a sort and a proposition).

## Confidence and satisfiability

Everything here is machine-checked and sorry-free; axioms are `propext`, `Quot.sound` and
`Classical.choice` (the last through `VLevel.imax_eq_zero`), all on `Guard.lean`'s whitelist.
Every statement in the file is shown to hold at the base index, and each reduction is replayed
there (`propConvInv_zero_from_residuals` and friends), so none of it is vacuous — the one
exception is `RegPi`, which is **not** shown satisfiable and is flagged at its definition.

What is *not* claimed: that any residual named here is true, or false, or that these are the
only reductions.  Each case is stated so that it closes from its residual **and nothing
else**, which is what makes them obligations rather than descriptions.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## `DefInv` without the refuted clause

`VEnv.DefInv` is **false** at `env = ∅, U = 1, n = 1` (`DefInvRefute.defInv_one_false`), and
the refutation goes through **clause (2)** (`ForallEInvN`) alone.  Anything in this file that
still took `DefInv` as a hypothesis was therefore *vacuous* at that instance.  Nothing here
uses clause (2), so every consumer below is stated against the clause — or the pair of
clauses — it actually consumes:

* `env.SortInvN U n` — clause (1), `unique.tex:32`;
* `env.SortForallEDisjN U n` — clause (3), `unique.tex:34`;
* `env.SortDisjInvN U n` — the two of them together, for the consumers that need both.

See `docs/handoff-definv-rescue.md` for the audit and the non-vacuity replays. -/

/-- **Clauses (1) and (3) of `DefInv`, with the refuted clause (2) dropped.**

Field names match `DefInv`'s (`sort`, `sort_forallE`) so a consumer's proof body is
unchanged by the narrowing.  `DefInv.toSortDisjInvN` is the one-way implication; there is no
converse, which is the point — `DefInv ∅ 1 1` is refuted and this is not. -/
structure SortDisjInvN (env : VEnv) (U n : Nat) : Prop where
  /-- Clause (1): a term with two sort types has equivalent levels. -/
  sort : env.SortInvN U n
  /-- Clause (3): a sort and a Π-type are never convertible. -/
  sort_forallE : env.SortForallEDisjN U n

theorem DefInv.toSortDisjInvN (d : env.DefInv U n) : env.SortDisjInvN U n :=
  ⟨d.sort, d.sort_forallE⟩

/-- The bundle is satisfied at the base index — so every consumer below has a real instance
to fire at, over any environment.  See §"Replays" at the end of this file. -/
theorem SortDisjInvN.zero : env.SortDisjInvN U 0 := ⟨SortInvN.zero, SortForallEDisjN.zero⟩

/-! ## Two facts from `DefInv` that the easy cases are made of -/

/-- **A sort is not a proposition.**  `Γ ⊢ₙ .sort l : .sort .zero` would need
`.succ l ≈ .zero`.  Clause (1) only. -/
theorem not_isPropN_sort (dinv : env.SortInvN U n) {Γ : List VExpr} {l : VLevel} :
    ¬ IsPropN env U n Γ (.sort l) := fun h =>
  absurd (congrFun (dinv (HasTypeN.sort_inv h).2) []) (by simp [VLevel.eval])

/-- **A λ is not a proposition.**  Its type is a Π, and `DefInv` clause (3) keeps a Π and a
sort apart.  Clause (3) only. -/
theorem not_isPropN_lam (dinv : env.SortForallEDisjN U n) {Γ : List VExpr} {A b : VExpr} :
    ¬ IsPropN env U n Γ (.lam A b) := fun h => by
  obtain ⟨_, _, _, _, hc⟩ := HasTypeN.lam_inv h
  exact dinv (IsDefEqN.symm' hc)

/-- Retyping a type at `.sort .zero` once its universe is known to be `≈ .zero`.  Needs
`n = k+1`, because at `n = 0` the conversion judgment is syntactic equality and `≈` is not. -/
theorem isPropN_of_equiv_zero {k : Nat} {Γ : List VExpr} {B : VExpr} {v : VLevel}
    (hv : v.WF U) (h : v ≈ .zero) (hB : env.HasTypeN U (k+1) Γ B (.sort v)) :
    IsPropN env U (k+1) Γ B :=
  .conv (.sortDF hv trivial h) hB

/-! ## The statement and its seven residuals -/

/-- **`PropTypeAgreeN`'s conversion residual.**  Stated as an `iff` because the directed form
fails at `symm`; propagated *along* the conversion rather than asserted of its endpoints,
which is what makes `trans` close by composition (`docs/handoff-stratified.md` §5). -/
def PropConvInv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' : VExpr},
    env.IsDefEqN U n Γ A A' → (IsPropN env U n Γ A ↔ IsPropN env U n Γ A')

/-- Residual of the `constDF` case: **a constant's type stays a proposition when its level
arguments move**.  This is level-substitution congruence at `ci.type`, in the only instance
the case needs (target `.sort .zero`).

The general `instL` congruence — `ls ≈ ls' ⟹ E.instL ls ≡ₙ E.instL ls'` — goes through by
induction on `E` for `.bvar`, `.sort`, `.const`, `.lam` and `.forallE` and **resists at
`.app`**, because `Stratified.appDF` carries four typing premises which the induction has no
way to supply.  Hence the narrower statement. -/
def PropConstDF (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Name} {ci : VConstant} {ls ls' : List VLevel},
    env.IsDefEqN U n Γ (.const c ls) (.const c ls') →
    env.constants c = some ci → (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    (env.IsDefEqN U n Γ (ci.type.instL ls) (.sort .zero) ↔
      env.IsDefEqN U n Γ (ci.type.instL ls') (.sort .zero))

/-- Residual of the `forallEDF` case, stated with the induction hypothesis the case actually
has (the codomain `iff`, in the **left** context `A::Γ`).  `propForallEDF_of` below shows it
follows from context conversion plus regularity along a conversion. -/
def PropForallEDF (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' B B' : VExpr},
    env.IsDefEqN U n Γ (.forallE A B) (.forallE A' B') →
    env.IsDefEqN U n Γ A A' → env.IsDefEqN U n (A::Γ) B B' →
    (IsPropN env U n (A::Γ) B ↔ IsPropN env U n (A::Γ) B') →
    (IsPropN env U n Γ (.forallE A B) ↔ IsPropN env U n Γ (.forallE A' B'))

/-- Residual of the `appDF` case.  All six premises are given at the *conclusion's* index —
the rule supplies its four typing premises one index lower, and they are raised by
`Stratified.mono`, so this is the weaker (easier) placement. -/
def PropAppDF (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f f' a a' A B : VExpr},
    env.IsDefEqN U n Γ (.app f a) (.app f' a') →
    env.IsDefEqN U n Γ f f' → (IsPropN env U n Γ f ↔ IsPropN env U n Γ f') →
    env.HasTypeN U n Γ f (.forallE A B) → env.HasTypeN U n Γ f' (.forallE A B) →
    env.IsDefEqN U n Γ a a' → (IsPropN env U n Γ a ↔ IsPropN env U n Γ a') →
    env.HasTypeN U n Γ a A → env.HasTypeN U n Γ a' A →
    (IsPropN env U n Γ (.app f a) ↔ IsPropN env U n Γ (.app f' a'))

/-- Residual of the `beta` case.  It asks for propositionhood to survive one β-step, which is
substitution at a preserved index — the family `Theory/Typing/SubstCRefute.lean` and
`Theory/Typing/SubstTRefute.lean` refute in their stronger forms. -/
def PropBetaConv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A e e' B : VExpr},
    env.IsDefEqN U n Γ (.app (.lam A e) e') (e.inst e') →
    env.HasTypeN U n (A::Γ) e B → env.HasTypeN U n Γ e' A →
    (IsPropN env U n Γ (.app (.lam A e) e') ↔ IsPropN env U n Γ (e.inst e'))

/-- Residual of the `extra` case: **the environment's rules do not change propositionhood.**

Unlike `DefInv`'s clauses (1) and (3), this one is *not* discharged by
`VEnv.WF.instL_lhs_ne_sort` / `instL_lhs_ne_forallE` (`Theory/Typing/DeclRules.lean`): those
say the left-hand side is not a `.sort` and not a `.forallE`, and a rule's left-hand side
*can* be a proposition (`def MyProp : Prop := True`).  See the section at the end of this
file. -/
def PropExtraConv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {df : VDefEq} {ls : List VLevel},
    env.IsDefEqN U n Γ (df.lhs.instL ls) (df.rhs.instL ls) →
    env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    (IsPropN env U n Γ (df.lhs.instL ls) ↔ IsPropN env U n Γ (df.rhs.instL ls))

/-- **`eta`'s residual, sharpened.**  `SortForallEDisjoint` at `u = .zero` and nothing more:
*a term that is a proposition does not also have a Π type*. -/
def PropForallEDisjoint (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr},
    env.HasTypeN U n Γ e (.sort .zero) → env.HasTypeN U n Γ e (.forallE A B) → False

theorem SortForallEDisjoint.propForallE (hd : env.SortForallEDisjoint U n) :
    env.PropForallEDisjoint U n := fun h1 h2 => hd h1 h2

/-! ## The twelve cases -/

/-- **Every case of `PropConvInv`, machine-checked.**

`rfl`, `symm`, `trans` close by composition — the criterion's whole point.  `sortDF` and
`lamDF` are vacuous from `DefInv`.  The seven typing constructors die on `b = false`.  The
remaining five are each reduced to their residual and to nothing else. -/
theorem propConvInv_of {Γ A A' b} (H : Stratified env U n Γ A A' b) :
    b = false → env.SortDisjInvN U n →
    env.PropConstDF U n → env.PropForallEDF U n → env.PropAppDF U n →
    env.PropBetaConv U n → env.PropForallEDisjoint U n → env.PropNotProof U n →
    env.PropExtraConv U n →
    (IsPropN env U n Γ A ↔ IsPropN env U n Γ A') := by
  induction H with
  | bvar | sort | const | app | lam | forallE | conv =>
    intro hb; exact nomatch hb
  | rfl => intro _ _ _ _ _ _ _ _ _; exact Iff.rfl
  | symm _ ih =>
    intro _ d r1 r2 r3 r4 r5 r6 r7
    exact (ih (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7).symm
  | trans _ _ ih1 ih2 =>
    intro _ d r1 r2 r3 r4 r5 r6 r7
    exact (ih1 (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7).trans
      (ih2 (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7)
  | sortDF _ _ _ =>
    intro _ d _ _ _ _ _ _ _
    exact ⟨fun h => absurd h (not_isPropN_sort d.sort), fun h => absurd h (not_isPropN_sort d.sort)⟩
  | lamDF _ _ _ _ =>
    intro _ d _ _ _ _ _ _ _
    exact ⟨fun h => absurd h (not_isPropN_lam d.sort_forallE),
      fun h => absurd h (not_isPropN_lam d.sort_forallE)⟩
  | constDF h1 h2 h3 h4 h5 =>
    intro _ _ r1 _ _ _ _ _ _
    have hlen' := (List.Forall₂.length_eq h5).symm.trans h4
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨ci', h1', _, _, hc⟩ := HasTypeN.const_inv h
      cases Option.some.inj (h1'.symm.trans h1)
      exact .conv ((r1 (.constDF h1 h2 h3 h4 h5) h1 h2 h3 h4 h5).1 hc) (.const h1 h3 hlen')
    · obtain ⟨ci', h1', _, _, hc⟩ := HasTypeN.const_inv h
      cases Option.some.inj (h1'.symm.trans h1)
      exact .conv ((r1 (.constDF h1 h2 h3 h4 h5) h1 h2 h3 h4 h5).2 hc) (.const h1 h2 h4)
  | forallEDF hA hB ihA ihB =>
    intro _ d r1 r2 r3 r4 r5 r6 r7
    exact r2 (.forallEDF hA hB) hA hB (ihB (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7)
  | appDF hff hf hf' haa ha ha' ihf _ _ iha _ _ =>
    intro _ d r1 r2 r3 r4 r5 r6 r7
    exact r3 (.appDF hff hf hf' haa ha ha') hff (ihf (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7)
      (hf.mono (Nat.le_succ _)) (hf'.mono (Nat.le_succ _))
      haa (iha (Eq.refl false) d r1 r2 r3 r4 r5 r6 r7)
      (ha.mono (Nat.le_succ _)) (ha'.mono (Nat.le_succ _))
  | beta he he' _ _ =>
    intro _ _ _ _ _ r4 _ _ _
    exact r4 (.beta he he') (he.mono (Nat.le_succ _)) (he'.mono (Nat.le_succ _))
  | eta he _ =>
    intro _ d _ _ _ _ r5 _ _
    exact ⟨fun h => absurd h (not_isPropN_lam d.sort_forallE),
      fun h => absurd (r5 h (he.mono (Nat.le_succ _))) not_false⟩
  | proofIrrel hp h2 h3 _ _ _ =>
    intro _ _ _ _ _ _ _ r6 _
    exact ⟨fun h => absurd (r6 h (hp.mono (Nat.le_succ _)) (h2.mono (Nat.le_succ _))) not_false,
      fun h => absurd (r6 h (hp.mono (Nat.le_succ _)) (h3.mono (Nat.le_succ _))) not_false⟩
  | extra h1 h2 h3 =>
    intro _ _ _ _ _ _ _ _ r7
    exact r7 (.extra h1 h2 h3) h1 h2 h3

/-- The statement form of `propConvInv_of`. -/
theorem propConvInv_of' (dinv : env.SortDisjInvN U n)
    (r1 : env.PropConstDF U n) (r2 : env.PropForallEDF U n) (r3 : env.PropAppDF U n)
    (r4 : env.PropBetaConv U n) (r5 : env.PropForallEDisjoint U n)
    (r6 : env.PropNotProof U n) (r7 : env.PropExtraConv U n) :
    env.PropConvInv U n := fun H =>
  propConvInv_of H (Eq.refl false) dinv r1 r2 r3 r4 r5 r6 r7

/-! ## `forallEDF`, unpacked into the two statements it is made of -/

/-- Context conversion at a **preserved** index, at the one target the `forallEDF` case needs.
`docs/handoff-stratified.md` §5 records the diagnostic: context conversion at a preserved index
closes for every rule except `appDF`, `beta`, `eta`, `proofIrrel`. -/
def CtxConvProp (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' B : VExpr},
    env.IsDefEqN U n Γ A A' → env.HasTypeN U n (A::Γ) B (.sort .zero) →
    env.HasTypeN U n (A'::Γ) B (.sort .zero)

/-- Regularity **along** a conversion, at a preserved index: a term convertible with a type is
a type.  Note this is *not* the statement `Theory/Typing/PropShadow.lean`'s
`regularity_two_typing_false` refutes — that one drops the index, and its witness's right
endpoint is `⊢₁`-typeable (`rhs_hasType1`), so the index-preserving form survives it. -/
def RegConv (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
    env.IsDefEqN U n Γ A A' → u.WF U → env.HasTypeN U n Γ A (.sort u) →
    ∃ u', u'.WF U ∧ env.HasTypeN U n Γ A' (.sort u')

/-- **`forallEDF` closes from context conversion and regularity-along-conversion**, and
nothing else.  Stated at `n+1` because retyping a `.sort v` with `v ≈ .zero` at `.sort .zero`
uses `sortDF`, which does not exist at index `0`. -/
theorem propForallEDF_of (dinv : env.SortInvN U n)
    (hctx : env.CtxConvProp U n) (hreg : env.RegConv U n) :
    env.PropForallEDF U n := by
  cases n with
  | zero =>
    intro _ _ _ _ _ h _ _ _
    injection IsDefEqN.zero_iff.1 h with h1 h2; subst h1; subst h2; exact Iff.rfl
  | succ k =>
  have main : ∀ {Γ : List VExpr} {A A' B B' : VExpr},
      env.IsDefEqN U (k+1) Γ A A' →
      (IsPropN env U (k+1) (A::Γ) B → IsPropN env U (k+1) (A::Γ) B') →
      IsPropN env U (k+1) Γ (.forallE A B) → IsPropN env U (k+1) Γ (.forallE A' B') := by
    intro Γ A A' B B' hA ih hp
    obtain ⟨u, v, hu, hv, hA0, hB0, hc⟩ := HasTypeN.forallE_inv hp
    have hv0 : v ≈ .zero := VLevel.imax_eq_zero.1 (dinv hc)
    have hB' : IsPropN env U (k+1) (A::Γ) B' := ih (isPropN_of_equiv_zero hv hv0 hB0)
    obtain ⟨u', hu', hA'⟩ := hreg hA hu hA0
    have : env.HasTypeN U (k+1) Γ (.forallE A' B') (.sort (.imax u' .zero)) :=
      .forallE hu' trivial hA' (hctx hA hB')
    exact isPropN_of_equiv_zero (by exact ⟨hu', trivial⟩) (VLevel.imax_eq_zero.2 (by rfl)) this
  intro Γ A A' B B' _ hA hB ihB
  exact ⟨main hA ihB.1,
    main (IsDefEqN.symm' hA) (fun h => hctx hA (ihB.2 (hctx (IsDefEqN.symm' hA) h)))⟩

/-! ## `eta`'s residual: six of seven cases, inherited -/

/-- **`PropForallEDisjoint` closes in six of its seven typing cases**, from `DefInv` alone —
inherited verbatim from `sortForallEDisjoint_of`, since the `u = .zero` instance is an
instance.  Only the `app` case remains, and only at `u = .zero`. -/
theorem propForallEDisjoint_of (happ : SortForallEDisjoint.AppCase env U n)
    (dinv : env.SortForallEDisjN U n) : env.PropForallEDisjoint U n := fun h1 h2 =>
  sortForallEDisjoint_ofN h1 happ dinv (Eq.refl true) _ _ _ .rfl h2

/-- The `app` case of `eta`'s residual, at `u = .zero` only — strictly less than
`SortForallEDisjoint.AppCase`. -/
def PropForallEDisjoint.AppCase (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A B : VExpr},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort .zero) →
    env.HasTypeN U n Γ (.app f a) (.forallE A B) → False

theorem SortForallEDisjoint.AppCase.propAppCase (h : SortForallEDisjoint.AppCase env U n) :
    PropForallEDisjoint.AppCase env U n := fun h1 h2 h3 h4 => h h1 h2 h3 h4

/-- **The sharpening, run at the `app` case too.**  `sortForallEDisjoint_of` closes six of
seven cases at an arbitrary `u`; re-run at `u = .zero` it needs only the `u = .zero` app case,
so `eta`'s residual is strictly less than `SortForallEDisjoint` all the way down. -/
theorem propForallEDisjointCases {Γ e T b} (H : Stratified env U n Γ e T b) :
    PropForallEDisjoint.AppCase env U n → env.SortForallEDisjN U n → b = true →
    env.IsDefEqN U n Γ T (.sort .zero) →
    ∀ A B, env.HasTypeN U n Γ e (.forallE A B) → False := by
  induction H with
  | bvar h =>
    intro _ dinv _ hT A B H2
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact dinv (IsDefEqN.trans' (IsDefEqN.symm' hT) (Lookup.uniq h hl ▸ hc))
  | sort _ =>
    intro _ dinv _ _ A B H2
    exact dinv (HasTypeN.sort_inv H2).2
  | const h1 _ _ =>
    intro _ dinv _ hT A B H2
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact dinv (IsDefEqN.trans' (IsDefEqN.symm' hT) hc)
  | lam _ _ => intro _ dinv _ hT _ _ _; exact dinv (IsDefEqN.symm' hT)
  | forallE _ _ _ _ =>
    intro _ dinv _ _ A B H2
    obtain ⟨_, _, _, _, _, _, hc⟩ := HasTypeN.forallE_inv H2
    exact dinv hc
  | conv h _ _ ih2 =>
    intro happ dinv _ hT A B H2
    exact ih2 happ dinv (Eq.refl true) (IsDefEqN.trans' h hT) A B H2
  | app hf ha _ _ => intro happ _ _ hT A B H2; exact happ hf ha hT H2
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

/-- The statement form: **`eta`'s residual costs `DefInv` plus the `u = .zero` app case, and
nothing else.** -/
theorem propForallEDisjoint_of' (happ : PropForallEDisjoint.AppCase env U n)
    (dinv : env.SortForallEDisjN U n) : env.PropForallEDisjoint U n := fun h1 h2 =>
  propForallEDisjointCases h1 happ dinv (Eq.refl true) .rfl _ _ h2

/-! ## `proofIrrel`'s residual, reduced without `PropTypeAgreeN`

`propNotProof_of` (`Theory/Typing/UniqueTypingN.lean`) derives `PropNotProof` from
`PropTypeAgreeN` itself, which is why `docs/handoff-stratified.md` §5 files `proofIrrel` as
self-reference.  The reduction below is different: it is the *same induction on the typing
judgment* that `sortForallEDisjoint_of` runs, and it reaches six of seven cases with a new,
strictly narrower statement in place of `PropTypeAgreeN`. -/

/-- **Nothing convertible with a sort is a proposition.**

The exact extra ingredient `proofIrrel`'s residual needs beyond `DefInv`, and the precise
place where it differs from `eta`'s: `DefInv` clause (3) decides *sort versus Π* because both
are syntactic shapes, and it decides nothing about *being a proposition*, which is a typing.

Implied by `PropConvInv` + `DefInv` (transport `IsPropN` along the conversion, then
`not_isPropN_sort`), hence strictly weaker than the statement whose case needs it. -/
def SortNotProp (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u : VLevel},
    env.IsDefEqN U n Γ A (.sort u) → env.HasTypeN U n Γ A (.sort .zero) → False

theorem SortNotProp.of_propConvInv (dinv : env.SortInvN U n) (h : env.PropConvInv U n) :
    env.SortNotProp U n := fun hc hp => not_isPropN_sort dinv (h hc |>.1 hp)

/-- The one case of `PropNotProof` that the typing induction does not reach — the same
application subject that blocks `SortForallEDisjoint`. -/
def PropNotProof.AppCase (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ p : VExpr},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort .zero) →
    env.HasTypeN U n Γ p (.sort .zero) → env.HasTypeN U n Γ (.app f a) p → False

/-- **`PropNotProof` closes in six of its seven typing cases**, from `DefInv` and
`SortNotProp`.  `trans` never arises — this is an induction on typing, so the statement is on
the tractable side of the criterion, exactly like `SortForallEDisjoint`.

The three cases that consume `SortNotProp` are `bvar`, `const` and `forallE`: in each the
second typing's inversion hands back a conversion whose *other* endpoint is a sort, and what
has to be refuted is that its subject is a proposition. -/
theorem propNotProof_of' {Γ e T b} (H : Stratified env U n Γ e T b) :
    b = true → env.SortDisjInvN U n → env.SortNotProp U n → PropNotProof.AppCase env U n →
    env.IsDefEqN U n Γ T (.sort .zero) →
    ∀ p, env.HasTypeN U n Γ p (.sort .zero) → env.HasTypeN U n Γ e p → False := by
  induction H with
  | bvar h =>
    intro _ _ hsnp _ hT p hp H2
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact hsnp (IsDefEqN.trans' (IsDefEqN.symm' (Lookup.uniq h hl ▸ hc)) hT) hp
  | sort _ =>
    intro _ dinv _ _ hT _ _ _
    exact absurd (congrFun (dinv.sort hT) []) (by simp [VLevel.eval])
  | const h1 _ _ =>
    intro _ _ hsnp _ hT p hp H2
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact hsnp (IsDefEqN.trans' (IsDefEqN.symm' hc) hT) hp
  | lam _ _ =>
    intro _ dinv _ _ hT _ _ _
    exact dinv.sort_forallE (IsDefEqN.symm' hT)
  | forallE _ _ _ _ =>
    intro _ _ hsnp _ _ p hp H2
    obtain ⟨_, _, _, _, _, _, hc⟩ := HasTypeN.forallE_inv H2
    exact hsnp (IsDefEqN.symm' hc) hp
  | app hf ha _ _ =>
    intro _ _ _ happ hT p hp H2
    exact happ hf ha hT hp H2
  | conv h _ _ ih2 =>
    intro _ dinv hsnp happ hT p hp H2
    exact ih2 (Eq.refl true) dinv hsnp happ (IsDefEqN.trans' h hT) p hp H2
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro hb; exact nomatch hb

/-- The statement form. -/
theorem propNotProof_of'' (dinv : env.SortDisjInvN U n) (hsnp : env.SortNotProp U n)
    (happ : PropNotProof.AppCase env U n) : env.PropNotProof U n := fun he hp hep =>
  propNotProof_of' he (Eq.refl true) dinv hsnp happ .rfl _ hp hep

/-! ## The `extra` case is not settled by rule shape

`DefInv` clauses (1) and (3) discharge their `extra` cases from
`VEnv.WF.instL_lhs_ne_sort` and `instL_lhs_ne_forallE`: the *conclusion* there is that an
endpoint is a `.sort` or a `.forallE`, and no rule's left-hand side is either.
`PropConvInv`'s conclusion is a **typing**, and a rule's left-hand side can perfectly well be
a proposition — `def MyProp : Prop := True` is a δ-rule between two propositions, whose
left-hand side is a `.const`, one of the three shapes `IsDeclRule.lhs_shape` permits.  So the
shape argument that closes `DefInv`'s `extra` case says nothing here, and `PropExtraConv`
stays as a residual. -/


/-! ## `PropUniqN` is not in the `trans` family — the route was, the statement is not

`docs/handoff-stratified.md` §5 files `PropUniqN` (`Theory/Typing/PropShadow.lean`) as
"endpoint-asserted, `trans` fails, needs normalisation", on the strength of this route: invert
both typings to the shape-determined type, compose, and the residual becomes
`.sort u ≡ₙ X ≡ₙ .sort v ⟹ (u ≈ 0 ↔ v ≈ 0)`, whose middle term need not be a sort.

**That is a fact about the route, not about the statement.**  The criterion's own first
clause — *does the statement's induction ever have to look at a conversion derivation at
all?* — answers **no** for `PropUniqN`, by exactly the manoeuvre `sortForallEDisjoint_of`
uses: induct on the *typing* judgment, keep the second typing as a hypothesis, and invert it
with the `HasTypeN.*_inv` lemmas.  `trans` is then a conversion rule and never arises.

Six of seven cases close **from `DefInv` alone**, with only `app` open — the same position,
with the same subject shape, as `SortForallEDisjoint`, `PropForallEDisjoint` and
`PropNotProof`.  So the correct entry for `PropUniqN` in §5's table is the
`SortForallEDisjoint` row, not the `sort_inv` row.

*What this does not show* (trap #8): that `PropUniqN` is true, or that its `app` case is any
easier than the three others.  What it removes is the claim that `PropUniqN` needs a
normalisation argument. -/

/-- The one case of `PropUniqN` the typing induction does not reach. -/
def PropUniqN.AppCase (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ : VExpr} {u v : VLevel},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.HasTypeN U n Γ (.app f a) (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel))

/-- **`PropUniqN` closes in six of its seven typing cases, from `DefInv` alone.**

`bvar`, `sort` and `const` compose the two inverted conversions into a sort–sort conversion
and read `u ≈ v` off `DefInv` clause (1) — note this gives the *strong* form, not merely the
shadow.  `lam` is vacuous by clause (3).  `forallE` is the only case with inductive content,
and it is where `VLevel.imax_eq_zero` does its work: a Π-type is a proposition exactly when
its codomain is, so the induction hypothesis at the codomain — a subterm, under a binder — is
exactly what the case needs.  `conv` composes.  `trans` never arises. -/
theorem propUniq_of {Γ e T b} (H : Stratified env U n Γ e T b) :
    b = true → env.SortDisjInvN U n → PropUniqN.AppCase env U n →
    ∀ u v, env.IsDefEqN U n Γ T (.sort u) → env.HasTypeN U n Γ e (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel)) := by
  induction H with
  | bvar h =>
    intro _ dinv _ u v hT H2
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact VLevel.equiv_congr_left
      (dinv.sort (IsDefEqN.trans' (IsDefEqN.symm' hT) (Lookup.uniq h hl ▸ hc)))
  | sort _ =>
    intro _ dinv _ u v hT H2
    exact VLevel.equiv_congr_left
      (dinv.sort (IsDefEqN.trans' (IsDefEqN.symm' hT) (HasTypeN.sort_inv H2).2))
  | const h1 _ _ =>
    intro _ dinv _ u v hT H2
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact VLevel.equiv_congr_left (dinv.sort (IsDefEqN.trans' (IsDefEqN.symm' hT) hc))
  | lam _ _ =>
    intro _ dinv _ u v hT _
    exact absurd (IsDefEqN.symm' hT) dinv.sort_forallE
  | forallE _ _ _ _ _ ihB =>
    intro _ dinv happ u v hT H2
    obtain ⟨_, _, _, _, _, hB₁, hc⟩ := HasTypeN.forallE_inv H2
    refine (VLevel.equiv_congr_left (dinv.sort hT)).symm.trans
      (Iff.trans ?_ (VLevel.equiv_congr_left (dinv.sort hc)))
    exact VLevel.imax_eq_zero.trans
      ((ihB (Eq.refl true) dinv happ _ _ .rfl hB₁).trans VLevel.imax_eq_zero.symm)
  | app hf ha _ _ =>
    intro _ _ happ u v hT H2
    exact happ hf ha hT H2
  | conv h _ _ ih2 =>
    intro _ dinv happ u v hT H2
    exact ih2 (Eq.refl true) dinv happ u v (IsDefEqN.trans' h hT) H2
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro hb; exact nomatch hb

/-- The statement form. -/
theorem propUniq_of' (dinv : env.SortDisjInvN U n) (happ : PropUniqN.AppCase env U n) :
    env.PropUniqN U n := fun h1 h2 => propUniq_of h1 (Eq.refl true) dinv happ _ _ .rfl h2

theorem PropUniqN.zero : env.PropUniqN U 0 := by
  intro _ _ _ _ h1 h2
  injection HasTypeN.uniq_zero h1 h2 with e; subst e; exact Iff.rfl

theorem PropUniqN.AppCase.zero : PropUniqN.AppCase env U 0 := by
  intro _ _ _ _ _ _ _ hf ha hB H2
  have h : env.HasTypeN U 0 _ (.app _ _) _ := .app hf ha
  rw [IsDefEqN.zero_iff.1 hB] at h
  injection HasTypeN.uniq_zero h H2 with e; subst e; exact Iff.rfl

/-- Non-vacuity: `propUniq_of'` reproves `PropUniqN.zero` from residuals that hold. -/
theorem propUniq_zero_from_residuals : env.PropUniqN U 0 :=
  propUniq_of' SortDisjInvN.zero PropUniqN.AppCase.zero


/-! ## `PropTypeAgreeN` itself, by the same typing induction

With `PropConvInv` as the conversion residual, `PropTypeAgreeN`'s own induction is on the
typing judgment, and it closes in six of seven cases — `app` again.  `lam` is the one case
with inductive content, and it goes through because a Π-type is a proposition exactly when its
codomain is (`VLevel.imax_eq_zero`), so the induction hypothesis at the *body* is exactly what
is needed. -/

/-- A Π-type is a proposition iff its codomain is — the inversion half.  At `n = 0` the
hypothesis is unsatisfiable (`≡₀` is syntactic equality and `.imax u v` is never `.zero`), so
the case is discharged there rather than proved. -/
theorem isPropN_forallE_inv (dinv : env.SortInvN U n) {Γ : List VExpr} {A B : VExpr}
    (h : IsPropN env U n Γ (.forallE A B)) :
    ∃ u, u.WF U ∧ env.HasTypeN U n Γ A (.sort u) ∧ IsPropN env U n (A::Γ) B := by
  cases n with
  | zero =>
    obtain ⟨_, _, _, _, _, _, hc⟩ := HasTypeN.forallE_inv h
    exact absurd (IsDefEqN.zero_iff.1 hc) (by simp)
  | succ k =>
    obtain ⟨u, v, hu, hv, hA, hB, hc⟩ := HasTypeN.forallE_inv h
    exact ⟨u, hu, hA, isPropN_of_equiv_zero hv (VLevel.imax_eq_zero.1 (dinv hc)) hB⟩

/-- …and the introduction half. -/
theorem isPropN_forallE {k : Nat} {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (hu : u.WF U) (hA : env.HasTypeN U (k+1) Γ A (.sort u))
    (hB : IsPropN env U (k+1) (A::Γ) B) : IsPropN env U (k+1) Γ (.forallE A B) := by
  have h1 : env.HasTypeN U (k+1) Γ (.forallE A B) (.sort (.imax u .zero)) :=
    .forallE hu trivial hA hB
  exact isPropN_of_equiv_zero (by exact ⟨hu, trivial⟩) (VLevel.imax_eq_zero.2 (by rfl)) h1

/-- Propositionhood of a Π-type moves with its codomain. -/
theorem isPropN_forallE_congr (dinv : env.SortInvN U n) {Γ : List VExpr} {A B B' : VExpr}
    (ih : IsPropN env U n (A::Γ) B → IsPropN env U n (A::Γ) B')
    (h : IsPropN env U n Γ (.forallE A B)) : IsPropN env U n Γ (.forallE A B') := by
  cases n with
  | zero =>
    obtain ⟨_, _, _, _, _, _, hc⟩ := HasTypeN.forallE_inv h
    exact absurd (IsDefEqN.zero_iff.1 hc) (by simp)
  | succ k =>
    obtain ⟨u, hu, hA, hB⟩ := isPropN_forallE_inv dinv h
    exact isPropN_forallE hu hA (ih hB)

/-- The one case of `PropTypeAgreeN` the typing induction does not reach.  It carries the
induction hypothesis at the function, because the case has it. -/
def PropTypeAgreeN.AppCase (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A' : VExpr},
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    (∀ {X : VExpr}, env.HasTypeN U n Γ f X →
      IsPropN env U n Γ (.forallE A₀ B₀) → IsPropN env U n Γ X) →
    env.HasTypeN U n Γ (.app f a) A' →
    IsPropN env U n Γ (B₀.inst a) → IsPropN env U n Γ A'

/-- **`PropTypeAgreeN` closes in six of its seven typing cases**, from `DefInv` and its own
conversion residual `PropConvInv`.  `sort` and `forallE` are vacuous (their type is a sort,
and a sort is not a proposition); `bvar`, `const` and `conv` are `PropConvInv` at the
inversion's conversion; `lam` is the inductive case. -/
theorem propTypeAgree_of {Γ e T b} (H : Stratified env U n Γ e T b) :
    b = true → env.SortInvN U n → env.PropConvInv U n → PropTypeAgreeN.AppCase env U n →
    ∀ A', env.HasTypeN U n Γ e A' → IsPropN env U n Γ T → IsPropN env U n Γ A' := by
  induction H with
  | bvar h =>
    intro _ _ pci _ A' H2 hp
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact (pci (Lookup.uniq h hl ▸ hc)).1 hp
  | sort _ => intro _ dinv _ _ _ _ hp; exact absurd hp (not_isPropN_sort dinv)
  | const h1 _ _ =>
    intro _ _ pci _ A' H2 hp
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact (pci hc).1 hp
  | lam _ _ _ ih2 =>
    intro _ dinv pci happ A' H2 hp
    obtain ⟨_, _, _, hbody₂, hc₂⟩ := HasTypeN.lam_inv H2
    exact (pci hc₂).1 (isPropN_forallE_congr dinv
      (fun h => ih2 (Eq.refl true) dinv pci happ _ hbody₂ h) hp)
  | forallE _ _ _ _ => intro _ dinv _ _ _ _ hp; exact absurd hp (not_isPropN_sort dinv)
  | app hf ha ihf _ =>
    intro _ dinv pci happ A' H2 hp
    exact happ hf ha (fun H hpi => ihf (Eq.refl true) dinv pci happ _ H hpi) H2 hp
  | conv h _ _ ih2 =>
    intro _ dinv pci happ A' H2 hp
    exact ih2 (Eq.refl true) dinv pci happ A' H2 ((pci h).2 hp)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro hb; exact nomatch hb

/-- The statement form. -/
theorem propTypeAgree_of' (dinv : env.SortInvN U n) (pci : env.PropConvInv U n)
    (happ : PropTypeAgreeN.AppCase env U n) : env.PropTypeAgreeN U n :=
  fun h1 h2 hp => propTypeAgree_of h1 (Eq.refl true) dinv pci happ _ h2 hp

/-! ## Pricing `PropTypeAgreeN`'s `app` case

`Theory/Typing/PropShadow.lean`'s `app_shadow_of` prices the *shadow* of `thm:utype`'s `app`
case at `InstLvl` + `PropUniqN`.  The same price buys this case, with one more item that the
shadow's universe-carrying formulation hid: **regularity at a Π-type**, which is not free at
the index (`Stratified.lam` does not ship `A::Γ ⊢ B : .sort v`). -/

/-- Regularity at a Π-type, at the index: the two components of a function's type are types.
`HasTypeStrong` ships this in every constructor (`HasTypeStrong.regular`, trap #12);
`Stratified` does not.

**Not shown satisfiable, and that is a finding, not an oversight.**  Even at the base
index `RegPi` does not hold unconditionally: `Lookup` can hand back a Π-type whose components
were never typed, so it needs a well-formed-context hypothesis (`OnCtx`) that
`Theory/Typing/Injectivity.lean`'s targets do not carry.  Contrast `HasTypeStrong.regular`
(`Theory/Typing/UnivDiscrim.lean`), which is free — trap #12 cuts the other way here. -/
def RegPi (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f A B : VExpr}, env.HasTypeN U n Γ f (.forallE A B) →
    ∃ u v, u.WF U ∧ v.WF U ∧
      env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) B (.sort v)

/-- **The `app` case, priced exactly.**  `RegPi` and `InstLvl` turn the hypothesis
"`B₀.inst a` is a proposition" into "`B₀` is a proposition under the binder" — and the step
that actually needs `PropUniqN` is that one, because `B₀.inst a` carries two universes (`v₀`
from `InstLvl` and `.zero` from the hypothesis) and nothing else compares them.  The other
side needs no `PropUniqN`: `InstLvl` at `v = .zero` is enough. -/
theorem propTypeAgree_appCase_of {k : Nat} (dinv : env.SortInvN U (k+1))
    (hreg : env.RegPi U (k+1))
    (hinst : env.InstLvl U (k+1)) (huniq : env.PropUniqN U (k+1))
    (pci : env.PropConvInv U (k+1)) : PropTypeAgreeN.AppCase env U (k+1) := by
  intro Γ f a A₀ B₀ A' hf ha ihf H2 hp
  obtain ⟨A₁, B₁, hf₁, ha₁, hc⟩ := HasTypeN.app_inv H2
  obtain ⟨u₀, v₀, hu₀, hv₀, hA₀, hB₀⟩ := hreg hf
  have hv₀0 : v₀ ≈ (.zero : VLevel) := (huniq (hinst ha hB₀) hp).2 (by rfl)
  have hpi₀ : IsPropN env U (k+1) Γ (.forallE A₀ B₀) :=
    isPropN_forallE hu₀ hA₀ (isPropN_of_equiv_zero hv₀ hv₀0 hB₀)
  obtain ⟨_, hu₁, hA₁, hB₁⟩ := isPropN_forallE_inv dinv (ihf hf₁ hpi₀)
  exact (pci hc).1 (hinst ha₁ hB₁)


/-! ## Each `app` case is its own statement's fixpoint

`ShapeSpine.lean`'s `SortForallEDisjoint.appCase` records this for `SortForallEDisjoint`:
`Stratified.app` already gives `.app f a` the type `B₀.inst a` and `conv` retypes it, so the
case follows from the statement in one step and cannot be closed by anything merely equivalent
to it.  The same one-liner works for all four statements here, which is the honest framing:
the `app` case is not a smaller sub-problem, it is the whole remaining content. -/

theorem PropUniqN.appCase (h : env.PropUniqN U n) : PropUniqN.AppCase env U n :=
  fun hf ha hT H2 => h (.conv hT (.app hf ha)) H2

theorem PropNotProof.appCase (h : env.PropNotProof U n) : PropNotProof.AppCase env U n :=
  fun hf ha hT hp H2 => h (.conv hT (.app hf ha)) hp H2

theorem PropTypeAgreeN.appCase (h : env.PropTypeAgreeN U n) : PropTypeAgreeN.AppCase env U n :=
  fun hf ha _ H2 hp => h (.app hf ha) H2 hp

theorem PropForallEDisjoint.appCase (h : env.PropForallEDisjoint U n) :
    PropForallEDisjoint.AppCase env U n :=
  fun hf ha hT H2 => h (.conv hT (.app hf ha)) H2

/-! ### …and therefore each `app` case is *equivalent* to its statement

Both directions are machine-checked, so this is trap #11 read the useful way: the `app` case
is **not** a weaker sub-goal that a cheaper argument might reach.  It also settles the
non-vacuity question these reductions raise — `propUniq_of` cannot be secretly proving
`PropUniqN` from `DefInv` alone, because that is exactly what the `↔` forbids unless
`PropUniqN` itself is so provable. -/

theorem PropUniqN.appCase_iff (dinv : env.SortDisjInvN U n) :
    PropUniqN.AppCase env U n ↔ env.PropUniqN U n :=
  ⟨fun h => propUniq_of' dinv h, PropUniqN.appCase⟩

theorem PropNotProof.appCase_iff (dinv : env.SortDisjInvN U n) (hsnp : env.SortNotProp U n) :
    PropNotProof.AppCase env U n ↔ env.PropNotProof U n :=
  ⟨fun h => propNotProof_of'' dinv hsnp h, PropNotProof.appCase⟩

theorem PropTypeAgreeN.appCase_iff (dinv : env.SortInvN U n) (pci : env.PropConvInv U n) :
    PropTypeAgreeN.AppCase env U n ↔ env.PropTypeAgreeN U n :=
  ⟨fun h => propTypeAgree_of' dinv pci h, PropTypeAgreeN.appCase⟩

theorem PropForallEDisjoint.appCase_iff (dinv : env.SortForallEDisjN U n) :
    PropForallEDisjoint.AppCase env U n ↔ env.PropForallEDisjoint U n :=
  ⟨fun h => propForallEDisjoint_of' h dinv, PropForallEDisjoint.appCase⟩

/-! ## Satisfiability: every statement in this file holds at the base index

`DefInv.zero`, `SubstC.zero`, `SortForallEDisjoint.zero` and `SubstDisj.zero` are all recorded
for the same reason — a hypothesis nothing satisfies proves nothing.  The seven residuals
above are stated *with the conversion node's own conclusion as a premise*, which is what makes
them true at `n = 0`: there `≡₀` is syntactic equality, so the premise collapses each case to
reflexivity.  Without that premise `PropConstDF` is **false** at `n = 0` — `.param 0` under
`ls = [.zero]` and `ls' = [.max .zero .zero]` are `≈`-equal and not equal — so the placement is
not cosmetic. -/

theorem PropConvInv.zero : env.PropConvInv U 0 := fun h => by
  rw [IsDefEqN.zero_iff.1 h]

theorem PropConstDF.zero : env.PropConstDF U 0 := by
  intro _ _ _ _ _ h _ _ _ _ _
  injection IsDefEqN.zero_iff.1 h with _ h; subst h; exact Iff.rfl

theorem PropForallEDF.zero : env.PropForallEDF U 0 := by
  intro _ _ _ _ _ h _ _ _
  injection IsDefEqN.zero_iff.1 h with h1 h2; subst h1; subst h2; exact Iff.rfl

theorem PropAppDF.zero : env.PropAppDF U 0 := by
  intro _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _
  injection IsDefEqN.zero_iff.1 h with h1 h2; subst h1; subst h2; exact Iff.rfl

theorem PropBetaConv.zero : env.PropBetaConv U 0 := by
  intro _ _ _ _ _ h _ _; rw [IsDefEqN.zero_iff.1 h]

theorem PropExtraConv.zero : env.PropExtraConv U 0 := by
  intro _ _ _ h _ _ _; rw [IsDefEqN.zero_iff.1 h]

theorem PropForallEDisjoint.zero : env.PropForallEDisjoint U 0 :=
  SortForallEDisjoint.zero.propForallE

theorem PropForallEDisjoint.AppCase.zero : PropForallEDisjoint.AppCase env U 0 :=
  SortForallEDisjoint.AppCase.zero.propAppCase

theorem PropNotProof.zero : env.PropNotProof U 0 := by
  intro _ _ _ he hp hep
  have e := HasTypeN.uniq_zero he hep
  subst e
  exact not_isPropN_sort SortInvN.zero hp

theorem SortNotProp.zero : env.SortNotProp U 0 :=
  SortNotProp.of_propConvInv SortInvN.zero PropConvInv.zero

theorem PropNotProof.AppCase.zero : PropNotProof.AppCase env U 0 := by
  intro _ _ _ _ _ _ hf ha hB hp H2
  have : env.HasTypeN U 0 _ (.app _ _) _ := .app hf ha
  rw [IsDefEqN.zero_iff.1 hB] at this
  have e := HasTypeN.uniq_zero this H2
  subst e
  exact not_isPropN_sort SortInvN.zero hp

theorem CtxConvProp.zero : env.CtxConvProp U 0 := by
  intro _ _ _ _ h hB; rw [← IsDefEqN.zero_iff.1 h]; exact hB

theorem RegConv.zero : env.RegConv U 0 := by
  intro _ _ _ _ h hu hA; rw [← IsDefEqN.zero_iff.1 h]; exact ⟨_, hu, hA⟩

/-- **The case analysis is not vacuous**: at the base index all seven residuals hold, and
`propConvInv_of'` reproves `PropConvInv.zero` from them. -/
theorem propConvInv_zero_from_residuals : env.PropConvInv U 0 :=
  propConvInv_of' SortDisjInvN.zero PropConstDF.zero PropForallEDF.zero PropAppDF.zero
    PropBetaConv.zero PropForallEDisjoint.zero PropNotProof.zero PropExtraConv.zero

/-- …and so is `propNotProof_of''`. -/
theorem propNotProof_zero_from_residuals : env.PropNotProof U 0 :=
  propNotProof_of'' SortDisjInvN.zero SortNotProp.zero PropNotProof.AppCase.zero

theorem PropTypeAgreeN.zero : env.PropTypeAgreeN U 0 := by
  intro _ _ _ _ h1 h2 hp; exact HasTypeN.uniq_zero h1 h2 ▸ hp

theorem PropTypeAgreeN.AppCase.zero : PropTypeAgreeN.AppCase env U 0 := by
  intro _ _ _ _ _ _ hf ha _ H2 hp
  have h : env.HasTypeN U 0 _ (.app _ _) _ := .app hf ha
  exact HasTypeN.uniq_zero h H2 ▸ hp

/-- …and so is `propTypeAgree_of'`. -/
theorem propTypeAgree_zero_from_residuals : env.PropTypeAgreeN U 0 :=
  propTypeAgree_of' SortInvN.zero PropConvInv.zero PropTypeAgreeN.AppCase.zero

/-- …and so is `propForallEDF_of`. -/
theorem propForallEDF_zero_from_residuals : env.PropForallEDF U 0 :=
  propForallEDF_of SortInvN.zero CtxConvProp.zero RegConv.zero

/-! ## The companion test at the two `app` cases

`docs/handoff-stratified.md` §5's companion test: at each recursive position, instantiate the
induction hypothesis and try to prove it from the ambient hypotheses *without* the
sub-derivation.  `appCase_ih_vacuous` (`Theory/Typing/UnivDiscrim.lean`) runs it for
`SortForallEDisjoint`.  It gives the same answer for `PropNotProof`, and for the same reason:
the recursive position that could reach what the case needs is the function `f`, whose type is
a Π, and both induction hypotheses are guarded by "the type is convertible with a sort". -/

/-- **`PropNotProof`'s `app` case has no inductive content either.**  The induction hypothesis
at `f` is proved here from `DefInv` alone; `f` appears only in a premise that is never used,
and no derivation about `f` is an argument. -/
theorem propNotProof_appCase_ih_vacuous (dinv : env.SortForallEDisjN U n)
    {Γ : List VExpr} {f A₀ B₀ : VExpr} :
    ∀ {p A B : VExpr}, env.IsDefEqN U n Γ (.forallE A₀ B₀) (.sort .zero) →
      env.HasTypeN U n Γ p (.sort .zero) → env.HasTypeN U n Γ f (.forallE A B) → False :=
  fun h _ _ => dinv (IsDefEqN.symm' h)

end VEnv
end Lean4Lean
