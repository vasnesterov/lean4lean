# Handoff: `SortRedAppDF ∅ 1 0` — still open, one branch shorter, two constraints tighter

**Input to this stream:** `docs/handoff-definv-weakening.md` §7.1 — *"`SortRedAppDF ∅ 1 0`.
It is now the single residual between the tree and both surviving clauses at index 1 … A
refutation is worth as much as a proof."*

**Verdict: neither.**  `SortRedAppDF ∅ 1 0` is **not proved and not refuted**.  It is now
*equal* to a shorter statement, and there are two machine-checked constraints on what any
proof of it may look like.  Both were found by trying to refute it and failing at a
one-hypothesis margin, which is worth knowing before the next attempt.

**Everything marked *machine-checked* is a sorry-free declaration** in the new file
`Lean4Lean/Theory/Typing/SortRedApp.lean`, built by
`~/.elan/bin/lake build Lean4Lean.Theory.Typing.SortRedApp`; a `collectAxioms` sweep over the
module's **114 declarations** reports axioms `propext`, `Quot.sound`, `Classical.choice` only,
and zero `sorry`.  Claims marked *analysis* are not machine-checked and are labelled as such
every time.

---

## 0. Headline

| claim | status |
|---|---|
| `SortRedAppDF ∅ 1 0` | **open** |
| `SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1` | **machine-checked** (`empty_sortRedAppDF_iff`) — the "one residual" is a *reformulation*, not a weakening |
| `SortRedAppDF env U 0 ↔ SortRedAppDFSort env U 0` (any `Ordered env`) | **machine-checked** (`sortRedAppDF_iff_sortBranch`) — the `∀ X, X` branch is **discharged** |
| `SortRedAppDFSort env U 0 ↔ SortRedLamExpose env U 0` | **machine-checked** (`sortRedAppDFSort_iff_lamExpose`) |
| the typing-free spine strengthening (`SpineInv ∅ 1 1`) | **FALSE**, machine-checked (`spineInv_one_false`), and false over `propLoopEnv` too |
| the argument-typing premise of the residual | **load-bearing**, machine-checked (`ArgWitness.sortRedAppDF_needs_arg_typing`) |
| the companion test of `docs/handoff-stratified.md` §5 at the `appDF` function position | **fails**, machine-checked (`sortRedAppDF_fun_ih_vacuous`) |

So the open goal is now, in full:

> **`SortRedLamExpose ∅ 1 0`** — *if `Γ ⊢₁ f ≡ f'` with `f, f'` both `⊢₀`-typed at
> `∀ (_ : A), .sort w`, and `Γ ⊢₁ a ≡ a'` with `a, a'` both `⊢₀`-typed at `A`, and `f`
> weak-head β-reduces to `.lam A e` with `SortRed u (e.inst a)`, then `f'` weak-head
> β-reduces to some `.lam A e'` with `SortRed u (e'.inst a')`.*

Weak-head λ-exposure is invariant along `⊢₁`, and the exposed bodies agree on `SortRed` after
the two arguments are substituted.  That is all that is left of clauses (1) and (3) at index 1.

---

## 1. The criterion, run **before** the work — and its answer

`docs/handoff-stratified.md` §5 asks two questions.  Written down before anything was
attempted, and both answers were later confirmed in Lean:

* *Does the induction have to look at a conversion derivation?*  **Yes** — the residual's
  premise `Γ ⊢ₙ₊₁ f ≡ f'` is an arbitrary conversion.
* *Is the conclusion propagated along the conversion or asserted of its endpoints?*
  **Propagated** — `SortRedInv` is an `iff`, and `trans` composes.  So the criterion's first
  clause **passes**, which is exactly what `SortClauses.sortRedInv_of` already exploits.
* *Companion test: is the induction hypothesis non-vacuous at each recursive position?*
  **No.**  At the `appDF` function position the induction hypothesis is
  `SortRed u f ↔ SortRed u f'`, and it follows from the ambient typing premises **alone**:
  both sides are false, because a `⊢₀`-typed term at a Π-type never weak-head reduces to a
  sort.  *Machine-checked*: `sortRedAppDF_fun_ih_vacuous`.  The argument position **is**
  non-vacuous — *machine-checked*: `sortRedAppDF_arg_ih_nonvacuous` exhibits two terms
  `⊢₀`-typed at one type, one of which weak-head reduces to a sort and one of which does not.

That is the same diagnosis `UnivDiscrim.appCase_ih_vacuous` gives for
`SortForallEDisjoint`'s `app` case, and it predicted the rest of this session: *the predicate
must be strengthened at the function position, or nothing will happen there.*

---

## 2. The residual is not smaller than the reduction it came from

*Machine-checked.*  `sortRedAppDF_of_sortRedInv` is one line — `SortRedInv env U (n+1)`
applied to `Stratified.appDF` — and `SortClauses.sortRedInv_of` is the converse at `n = 0`
over `∅`, since the other three residuals are discharged there.  Hence

    empty_sortRedAppDF_iff : SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1

and `PropLoopWitness.propLoopEnv_sortRedAppDF_iff` over the non-empty witness environment.

**Correction to `docs/handoff-definv-weakening.md` §4.**  That document's headline —
"`SortRedAppDF ∅ 1 0 → SortInvN ∅ 1 1 ∧ SortForallEDisjN ∅ 1 1`, one residual is what is
left" — is correct as stated, and it is easy to read it as "the obligation has shrunk to a
fragment".  It has not: the residual is *equivalent* to `SortRedInv ∅ 1 1`, which is the whole
reduction.  What §4 really established is that **every other constructor is free**, which is
worth just as much but is a different claim.  Nothing was given away; nothing was gained in
strength.

---

## 3. The obvious repair, and its refutation

A vacuous induction hypothesis is repaired by generalising the predicate so the position
becomes load-bearing.  Here the standard generalisation is a **spine** (a Krivine stack):
prove `SortRed u (X.apps as) ↔ SortRed u (Y.apps as')` for `⊢ₙ₊₁`-related spines, so that at
`appDF` the recursion on `f ≡ f'` carries `(a, a')` and the induction hypothesis *is* the goal.

*Analysis* (not machine-checked, and recorded because it is what motivated the check below):
under that generalisation `appDF` closes outright, `sortDF`/`constDF`/`forallEDF` close on
spine length, `beta` and `eta` reduce to an argument-congruence residual, `proofIrrel` closes
from the head-shape of a `⊢₀` proof, and everything else moves into one **substitution**
residual coming from `lamDF`.

*Machine-checked*: that predicate, **stated without typing on the spine, is false**.

    SpineInv (env) (U n) : ∀ Γ X Y as as' u, IsDefEqN U n Γ X Y →
      Forall₂ (IsDefEqN U n Γ) as as' → (SortRed u (X.apps as) ↔ SortRed u (Y.apps as'))

    spineInv_one_false : ¬ SpineInv ∅ 1 1

The witness (`namespace ArgWitness`) is small and lives over a **well-formed** context — junk
contexts are *not* the mechanism:

* `wctx = [.bvar 0, .sort .zero]` — a proposition `P` (`.bvar 1`) and a proof of it
  (`.bvar 0`).  Each entry is a type in the preceding context.
* `idP    = .lam (.bvar 1) (.bvar 0)` — `fun (_ : P) => (the bound proof)`;
  `constP = .lam (.bvar 1) (.bvar 1)` — `fun (_ : P) => (the ambient proof)`.
* Both are `⊢₀`-typed at **one and the same** Π-type `.forallE (.bvar 1) (.bvar 2)` = `P → P`
  (`idP_type`, `constP_type`), and `idP ≡₁ constP` by `lamDF` over `proofIrrel`
  (`idP_conv_constP`).
* `SortRed .zero (.app idP Prop)` holds and `SortRed .zero (.app constP Prop)` does not
  (`app_idP_sortRed`, `app_constP_not_sortRed`), because `(.bvar 0).inst Prop = Prop` while
  `(.bvar 1).inst Prop = .bvar 0`.

`PropLoopWitness.propLoopEnv_spineInv_one_false` is the same refutation over
`CycleConv.propLoopEnv`, with the environment's own constant `A` as the proposition — so this
is not an artefact of the empty environment.

### 3.1 What that costs any future proof

*Machine-checked*, `ArgWitness.sortRedAppDF_needs_arg_typing`: at that same witness **every
premise of `SortRedAppDF` is met except `Γ ⊢₀ a : A`**, and the conclusion is false.  The two
functions are `⊢₁`-convertible and `⊢₀`-typed at one Π-type; the two arguments are *equal*
(hence `⊢₁`-convertible by `rfl`) and `⊢₀`-typed — just not at the domain.

> **Constraint.**  Any proof of `SortRedAppDF` must use the premise `Γ ⊢ₙ a : A`.

This sits beside `SortClauses.sortPiEnv_sortForallEDisjN_false`'s constraint ("any proof of
the clauses must use `VEnv.WF`, not merely `Ordered`") and is sharper in one respect: the
premise that must be used is one that **`trans` does not carry**, since a `trans` middle term
has no typing at all (`PropShadow.trans_middle_has_no_stage_universe`).  A predicate that is
typing-free enough to compose at `trans` is, by the witness above, too weak at `appDF`; a
predicate carrying the typing does not obviously compose at `trans`.  That tension is the
whole of the remaining difficulty, and it is now exhibited rather than asserted.

*Analysis*: the escape is a **heterogeneously typed** spine — the two heads typed at one type,
but after the first argument the two sides are typed at `B.inst a` and `B.inst a'`, which are
only `⊢ₙ₊₁`-related.  That was not attempted here.

### 3.2 The refutation attempts that failed, and exactly where

Two attempts to turn §3's witness into a refutation of `SortRedAppDF` itself.  Both fail at
the same place, and the reason is *machine-checked*.

1. **`lamDF` over `proofIrrel` at the residual.**  To use `idP`/`constP` as `f`/`f'` one needs
   an argument `a` with `Γ ⊢₀ a : P`.  Since `P` is a proposition, `a` is a proof, and
   `SortClauses.ProofNotSortRed.zero` says a `⊢₀` proof of a `⊢₀` proposition never weak-head
   reduces to a sort — so `.app idP a` reduces to `a` and does not `SortRed`.  The separation
   disappears exactly when the missing premise is supplied.
2. **`proofIrrel` directly on the function.**  Blocked: a Π-type is never `⊢₀`-typed at
   `.sort .zero` (`forallE_not_prop0`), and `⊢₀` types are syntactically unique
   (`HasTypeN.uniq_zero`), so `proofIrrel` cannot relate two Π-typed terms
   (`proofIrrel_not_at_pi`).  `lamDF` likewise cannot separate the domains
   (`lam_pair_at_one_type`).

**Both of these were recorded as *analysis* in `docs/handoff-definv-weakening.md` §4; they are
now machine-checked.**

---

## 4. What `SortRed` forces on the `⊢₀` type, and the split

*Machine-checked.*

* `SortRed.hasTypeN_zero_type` — if `SortRed u X` and `Γ ⊢₀ X : T` then `T = .sort (.succ v)`
  with `v ≈ u`.  Subject reduction (`SortClauses.HeadBeta.hasTypeN_zero`) plus `≡₀ =`
  syntactic equality.  So the level is pinned by the type.
* `inst_eq_sort` — `B.inst a = .sort w` iff `B = .sort w`, or `B = .bvar 0` and `a = .sort w`.
* `SortRed.app_codomain` — hence a `SortRed`-ing application has a codomain of exactly one of
  two shapes: a **closed sort**, or **`.bvar 0`** (with the argument itself a sort and the
  domain `.sort (.succ (.succ v))`, i.e. `f : ∀ (X : Type v⁺), X`).

`sortRedAppDF_of_split` turns this into a two-branch decomposition of the residual, via a
directed form (`SortRedAppDF'`, `sortRedAppDF_of_directed`: one direction suffices, because
the premises are symmetric under `Stratified.symm`).

---

## 5. The `∀ X, X` branch is discharged

*Machine-checked*, over **any** `Ordered env` — `VEnv.WF` is not needed here.

    sortRedAppDFVar_premise_empty :
      Ordered env → Γ ⊢₀ f : .forallE A (.bvar 0) → Γ ⊢₀ a : A → ¬ SortRed u (.app f a)

The proof is three steps, each its own lemma:

1. `SortRed.app_head` — a `SortRed`-ing application **exposes a λ**: `SortRed u (.app f a)`
   gives `HeadBetaS f (.lam C e)` and `SortRed u (e.inst a)`.  (`HeadBetaS` is
   reflexive-transitive `HeadBeta`; weak-head reduction of an application reduces the function
   in place until it is a λ and then contracts, so the reduction factors.)
2. `headBeta_inst_sort` — **substituting a sort creates no new head redexes**: a weak-head
   step of `X.inst (.sort w)` is a weak-head step of `X`, transported.  The one non-formal
   step is `VExpr.inst0_inst_hi`.  Hence `sortRed_inst_sort`: if `X.inst (.sort w)` weak-head
   reduces to a sort then `X` already weak-head reduces to a sort or to `.bvar 0`.
3. Neither survives the typing: `A::Γ ⊢₀ e : .bvar 0` rules out `.sort v` (its type is
   `.sort (.succ v)`) and rules out `.bvar 0` (whose type is `A.lift`, and
   `lift_ne_bvar_zero`).

By `SortRed.app_codomain` the branch's argument is a sort, which is what step 2 needs.

**This also removes a circularity.**  *Machine-checked*, `sortRedAppDFVar_forces_sort_arg`:
had that branch any instances, it would have *proved* that the right-hand argument is
syntactically a sort — a sort-shape statement about a `⊢ₙ₊₁` conversion, which is the content
clause (1) was supposed to supply.  It has none, so the residual no longer contains a copy of
its own conclusion.

---

## 6. The surviving branch, named

*Machine-checked*, `sortRedAppDFSort_iff_lamExpose` (an **iff**, so nothing is lost):

    SortRedLamExpose env U n :
      Γ ⊢ₙ₊₁ f ≡ f' → Γ ⊢ₙ f : ∀(_:A), .sort w → Γ ⊢ₙ f' : ∀(_:A), .sort w →
      Γ ⊢ₙ₊₁ a ≡ a' → Γ ⊢ₙ a : A → Γ ⊢ₙ a' : A →
      HeadBetaS f (.lam A e) → SortRed u (e.inst a) →
      ∃ e', HeadBetaS f' (.lam A e') ∧ SortRed u (e'.inst a')

`empty_chain` assembles the four-link chain, every link an equivalence:

    SortRedLamExpose ∅ 1 0 ↔ SortRedAppDFSort ∅ 1 0 ↔ SortRedAppDF ∅ 1 0 ↔ SortRedInv ∅ 1 1

and `empty_sortInvN_one_of_lamExpose`, `empty_sortForallEDisjN_one_of_lamExpose` connect it to
the two live clauses; `PropLoopWitness.propLoopEnv_sortInvN_one_of_lamExpose` and its
companion do the same over the non-empty environment.

*Analysis*: this is λ-injectivity for `⊢₁` restricted to the sort-codomain case, i.e. exactly
the head-shape half of a Church–Rosser argument.  `~/lean-type-theory/unique.tex` §§3–4 is the
reference's version; the reference's substitution lemmas were closed as unusable at the index
in `docs/handoff-stratified.md` §12 (`SubstT` is false), so the reference's route is *not*
available and this is not a matter of transcribing it.

---

## 7. Non-vacuity

The convention of `SortClauses.lean` §2 — replay at index zero, over a **non-empty**
environment — is followed for everything here (§§7 and 10 of the file, all
*machine-checked*, all over `CycleConv.propLoopEnv`):

| what fires | at what |
|---|---|
| §3's refutation | `propLoopEnv_spineInv_one_false`, `propLoopEnv_sortRedAppDF_needs_arg_typing` — the same construction with the environment's constant `A` as the proposition |
| `SortRed.hasTypeN_zero_type` | `propLoopEnv_hasTypeN_zero_type_fires`, at a term that really does β-reduce, with a constant in the domain |
| `lam_pair_at_one_type` | `propLoopEnv_lam_pair_fires`, at two *different* λs sharing one Π-type |
| `proofIrrel_not_at_pi` | `propLoopEnv_pidA_not_proof` |
| `sortRedAppDFVar_premise_empty` (§5) | `propLoopEnv_var_branch_fires`, at a context holding a variable of `∀ (X : Type 0), X` **and** a proof of the environment's proposition |
| `SortRedLamExpose` (§6) is **not premise-empty** | `propLoopEnv_lamExpose_instance`: two `⊢₁`-convertible, syntactically different functions `⊢₀`-typed at one Π-type over the witness environment, meeting every premise, at which the conclusion is **true** |

The last row is the important one: the surviving residual is neither premise-empty nor true
only by `f = f'`.  (`SortClauses.HeadOnly.sortRedAppDF_nondegenerate_instance` is the
corresponding check over `∅`.)

---

## 8. What to pick up first

1. **`SortRedLamExpose ∅ 1 0`.**  It is the whole of the open goal (§6), it is one branch
   shorter than what this stream was handed, and both of the cheap refutation routes are now
   closed with reasons (§3.2).  Any attempt should start from the two constraints: the proof
   must use `Γ ⊢₀ a : A` (§3.1) and — for the clauses themselves, per
   `docs/handoff-definv-weakening.md` §6 — `VEnv.WF`.
2. **The heterogeneously typed spine** (§3.1, *analysis*).  The typing-free spine is refuted;
   the version that carries `Γ ⊢ₙ a : A` on each spine element, with the two sides' types only
   `⊢ₙ₊₁`-related after the first argument, is **not** refuted and is the only generalisation
   of `SortRed` this stream found that survives §3's witness.  Its `trans` case is where it
   will live or die, since a `trans` middle term carries no typing.
3. **Do not re-attempt the head-only or typing-free predicates.**  `SortClauses.HeadOnly`
   refutes the first; §3 here refutes the second.  Both are machine-checked, both over
   well-formed contexts, and both are false over `propLoopEnv` as well as `∅`.
4. `sortRedAppDF_of_directed` and `sortRedAppDF_iff_sortBranch` mean a future proof only has
   to do **one direction** and only the **closed-sort-codomain** case.  Use them; they are
   free.

## 9. Corrections to what this stream was handed

* `docs/handoff-definv-weakening.md` §0.4 / §4 — "**one residual is what is left**" is true
  but reads as a reduction in strength.  It is an equivalence (§2 above, machine-checked).
  The real content of §4 is that every constructor other than `appDF` is free.
* `docs/handoff-definv-weakening.md` §4's two "*analysis, not machine-checked*" claims — that
  `lamDF` forces `A = A'` and `v = v'`, and that `proofIrrel` would need `⊢₀ (∀A.B) : Prop` —
  are now machine-checked (`lam_pair_at_one_type`, `forallE_not_prop0`,
  `proofIrrel_not_at_pi`).  One caveat on the `lamDF` half: as *stated* there it is about λs
  **whose bodies are sorts**, and for those it is correct (`.sort v` and `.sort v'` typed at
  one `B` forces `v = v'`).  The general reading — "the shared `⊢₀` type pins the bodies" — is
  **false**, and `ArgWitness.idP`/`constP` is the counterexample: two λs at one Π-type with
  different bodies.  That is exactly the pair that refutes the spine predicate, so the
  stronger reading was hiding the witness.
* The relay to this stream said the `trans` case "reappears *inside* `SortRedAppDF`, now
  attached to typing premises — check whether it is now tractable".  Answer: the relocation is
  real, but the typing premises are attached to `f`, `f'`, `a`, `a'` and **not** to a `trans`
  middle term, so `trans` is no more tractable inside the residual than outside it.  What the
  relocation buys is §4–§6: the codomain split, the discharged branch, and the named surviving
  statement.

## 10. Files

* `Lean4Lean/Theory/Typing/SortRedApp.lean` — new, 114 declarations, sorry-free, axioms
  `propext` / `Quot.sound` / `Classical.choice` only.  Nothing else in the tree was edited.
* `Lean4Lean/Theory/Typing/ParamsWitness.lean` (another stream's in-flight file) was red at
  the time of writing, so `lake build Lean4Lean.Theory` fails for a reason unrelated to this
  work; `lake build Lean4Lean.Theory.Typing.SortRedApp` is green.
