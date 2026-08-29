# Handoff: the shared `app` case — `Theory/Typing/AppCase.lean`

**Target of this stream:** the one open case that `SortForallEDisjoint`, `PropForallEDisjoint`,
`PropNotProof`, `PropUniq` and `PropTypeAgree` all stop at
(`docs/handoff-stratified.md` §16.4).

**Everything below marked *machine-checked* is a sorry-free declaration in
`Lean4Lean/Theory/Typing/AppCase.lean`, axioms `[propext, Quot.sound]` only.**  Claims marked
*analysis* or *source reading* are not.  The distinction is load-bearing in three places.

---

## 0. The headline, in one paragraph

The five `app` cases have one natural unifier: `thm:utype`'s own application case, "the two
instantiated codomains of the function's two Π-types are `⊢ₙ`-convertible".  It implies all
five (each with the residual that statement already names) and it holds at the base index.
**It is false at `n = 1` over the empty environment**, and so is unique typing at the index
itself.  The witness is not new — it is `ShapeSpine.lean`'s `ShapeAgreeRefute`, unchanged; what
is new is that nobody had applied it to `uniq`.  `docs/reference-gap-thm-utype.md` §4 lists
"`thm:utype`'s statement" under *not refuted* on the explicit ground that the `SubstC`
counterexample supplies "no single term carrying both Π types, and an argument typed at both
domains".  `ShapeAgreeRefute` supplies exactly that.  **That section needs amending; see §6.**

**None of the five is refuted by this.**  They are each strictly weaker than unique typing,
and the route through them does not use `uniq` at any index above `0` (checked: the only
consumer of `HasTypeN.uniq` in the tree is `uniq_zero`).

---

## 1. What is proved, sorry-free

### 1.1 The obligation, characterised exactly

`AppData env U n Γ f a A₀ B₀ A₁ B₁` — the premise bundle every one of the five carries once
`HasTypeN.app_inv` has been run on the second typing:

    Γ ⊢ₙ f : ∀A₀.B₀     Γ ⊢ₙ a : A₀     Γ ⊢ₙ f : ∀A₁.B₁     Γ ⊢ₙ a : A₁

**one function with two Π-types, and one argument typed at both domains.**  Over it the five
`app` cases become five statements about the single pair `(B₀.inst a, B₁.inst a)`:

| statement | conclusion about the pair | equivalent to |
|---|---|---|
| `AppDisj` | not (`≡ .sort u` on the left, `≡ .forallE A B` on the right) | `SortForallEDisjoint.AppCase` |
| `AppPropDisj` | the same at `u = .zero` | `PropForallEDisjoint.AppCase` |
| `AppUniqLvl` | if both `≡` sorts, the levels agree on being `0` | `PropUniq.AppCase` |
| `AppNotProof` | if the left `≡ Prop` and the right `≡ p`, then `p` is not a proposition | `PropNotProof.AppCase` |
| `AppPropAgree` | if the left is a proposition so is the right | `PropTypeAgree.AppCase` |

**Machine-checked, both directions, with no hypotheses at all** — `AppDisj.iff`,
`AppPropDisj.iff`, `AppUniqLvl.iff`, `AppNotProof.iff`, `AppPropAgree.iff`.  Left-to-right is
`HasTypeN.app_inv`; right-to-left is `Stratified.app` + `conv`.  So the five differ *only* in
what they conclude about that one pair, and the `AppData` form is interchangeable with the
tree's own at every index and over every environment.

### 1.2 The unifier, and its refutation

| name | what | status |
|---|---|---|
| `AppTypeUniq` | the two instantiated codomains are `⊢ₙ`-convertible — `unique.tex:51`'s conclusion | defined |
| `UniqN` | unique typing at the index — `HasTypeN.uniq`'s conclusion | defined |
| `AppTypeUniq.{appDisj, appPropDisj, appUniqLvl, appNotProof, appPropAgree}` | it discharges **all five**, with `DefInv` / `SortNotProp` / `PropConvInv` as the only extras — each already that statement's own named residual | machine-checked |
| `UniqN.appTypeUniq`, `UniqN.of_defInv_substC` | `UniqN` ⟹ `AppTypeUniq`; and `Stratified.uniq` proves `UniqN` from `DefInv` + `SubstC` | machine-checked |
| `UniqN.zero`, `AppTypeUniq.zero` | both hold at the base index — not vacuous | machine-checked |
| **`AppCaseRefute.appTypeUniq_false`** | **`AppTypeUniq` is false at `n = 1` over `∅`** | machine-checked |
| **`AppCaseRefute.uniqN_false`** | **unique typing at the index is false at `n = 1` over `∅`** | machine-checked |
| `AppCaseRefute.uniqN_witness` | the same, as an explicit `∃`: a term, two `⊢₁` types, no `⊢₁` conversion | machine-checked |
| `AppCaseRefute.thm_utype_one_false_of_defInv` | the dichotomy — see §2 | machine-checked |
| `AppCaseRefute.substC_false_of_defInv` | cross-check: `uniqN_false` rederives `substC_false` (weakened by a `DefInv` hypothesis) through `Stratified.uniq` | machine-checked |
| `AppCaseRefute.witness_env_ordered` | `∅` is `Ordered`; `ShapeSpine.P_type` already showed `[P]` is a genuine Π-type | machine-checked |
| `AppCaseRefute.lhs_conv_a_succ` | **the same pair *is* convertible at `n = 2`** — the counterexample is about the index, not the terms | machine-checked |

The witness, for reference (all of it is `ShapeSpine.lean`'s `ShapeAgreeRefute`, unchanged):

    p := .param 0    a := .sort (max p p)    A := .sort (succ p)
    D := (fun _ : A => x) x                  P := ∀ (_ : A), D        (P closed)

    [P] ⊢₁ .bvar 0 : ∀ (_ : A), D            (the variable, at its declared type)
    [P] ⊢₁ .bvar 0 : ∀ (_ : A), .bvar 0      (retyped along `forallEDF` of the beta step)
    [P] ⊢₁ a : A                             (one `sortDF`; `a` is *not* ⊢₀-typeable at `A`)

so `.app (.bvar 0) a` has the two `⊢₁` types `D.inst a = lhs` and `(.bvar 0).inst a = a`, and
`SubstCRefute.stuck` says `lhs` is `⊢₁`-related to nothing but itself.

### 1.3 The strengthened-induction schema, and its collapse

This is the direct answer to "what extra data carried through the typing induction makes the
function-position IH non-vacuous?".

A strengthening is a relation `R : List VExpr → VExpr → VExpr → Prop` with

* **(i)** `RelTypePairs` — `R` relates any two types of any term (the strengthened conclusion);
* **(ii)** `RelInstClosed` — `R` survives the `app` step: from `R` at two Π-types of `f` and an
  argument typed at both domains, `R` at the two instantiated codomains;
* **(iii)** `RelSeparates` — `R` forbids sort-on-the-left, Π-on-the-right.

| name | what | status |
|---|---|---|
| `relStrengthening_sound` | (i) + (ii) + (iii) ⟹ `AppDisj`.  So the schema really is the induction | machine-checked |
| **`sortForallEDisjoint_of_rel`** | **(i) + (iii) ⟹ `SortForallEDisjoint`**, with no induction and without (ii) | machine-checked |

The second is the closure: **no choice of `R` makes the remaining obligation cheaper.**  (iii)
is antitone in `R` and (i) says `R` contains the minimal relation, so (iii) for *any* admissible
`R` already implies (iii) for the minimal one — which is the statement.  A strengthening can
only add obligations.

Filled in at the four candidates:

| `R Γ T₁ T₂` | (i) | (ii) | (iii) |
|---|---|---|---|
| `∃ e, e : T₁ ∧ e : T₂` (`RelTaut`) | free (`RelTaut.typePairs`) | free (`RelTaut.instClosed`) | **= the statement** (`RelTaut.separates_iff`) |
| `T₁ ≡ₙ T₂` (unique typing) | **false** (`uniqN_false`) | **false** (`relConv_instClosed_false`) | free from `DefInv` |
| `SortLike T₁ ↔ SortLike T₂` | **false** (`relShape_typePairs_false`) | false | free |
| disjointness (`RelDisj`) | **= the statement** (`RelDisj.typePairs_iff`) | **false** (`relDisj_instClosed_false`) | free (`RelDisj.separates`) |

Every row is machine-checked.  `relConv_instClosed_false` is `SubstCRefute.defInv_forallE_inst_false`
read in the schema; `relShape_typePairs_false` is `ShapeSpine.typeShapeAgree_false` read in the
schema; `relDisj_instClosed_false` is new and holds already at `n = 0` (two Π-types whose
codomains are a constant sort and a constant Π).

**Read `RelTaut` and `RelDisj` together — that is the finding.**  At the minimal `R`, (i) and
(ii) are free and (iii) is the statement; at the maximal usable `R`, (iii) is free, (i) is the
statement and (ii) is outright false.  The content moves and never shrinks.  This is §9 of the
handoff's fixpoint observation, sharpened: the missing property is named — *closure under
codomain instantiation* — and both natural closures are false while the disjointness closure
is the goal itself.

### 1.4 `PiCodConv` — the one decomposition that was not a fixpoint, refuted

    PiCodConv :  Γ ⊢ₙ f : ∀A₀.B₀ → Γ ⊢ₙ f : ∀A₁.B₁ → A₀::Γ ⊢ₙ B₀ ≡ B₁

i.e. **unique typing restricted to Π-typed subjects, componentwise on the codomain**.  It is
genuinely not equivalent to `SortForallEDisjoint`, and with `SubstDisj`
(`ShapeSpine.lean`, satisfiable, not refuted) it closes the `app` case in one step:

| name | what | status |
|---|---|---|
| `PiCodConv.appDisj` | `PiCodConv` + `SubstDisj` ⟹ `AppDisj`, no spine induction, no `SubstC` | machine-checked |
| `PiCodConv.zero` | satisfiable at the base index | machine-checked |
| **`AppCaseRefute.piCodConv_false`** | **`PiCodConv` is false at `n = 1` over `∅`** | machine-checked |

The refutation is the same witness lifted through one λ: in `[P]`, the term
`.lam A (.app (.bvar 1) a)` has the two Π-types `∀A.lhs` and `∀A.a` (both closed codomains),
and `PiCodConv` would hand back `A::[P] ⊢₁ lhs ≡ a`.  **Consequence worth carrying: the failure
of unique typing at the index is *not* confined to types that are neither sorts nor Π's.  It is
already present at a term whose two types are both Π-types.**  So "restrict `uniq` to the shapes
the case actually needs" is closed as a family, not just at this instance.

### 1.5 The index

`SortForallEDisjoint.antitone`, `PropForallEDisjoint.antitone`, `PropNotProof.antitone`,
`PropUniq.antitone` — machine-checked: `S (n+1) → S m` for `m ≤ n`, since `Stratified.mono`
raises their hypotheses and their conclusions carry no index.  So induction on `n` runs the
wrong way: the whole content is the upward direction.  `PropTypeAgree` is the exception and is
neither monotone nor antitone (its conclusion `IsPropN` is itself a typing at the index); so is
`UniqN`.

---

## 2. The one open input that now decides a published theorem

`thm:utype` (`unique.tex:40`) is stated *under* the hypothesis "`⊢ₙ` has definitional
inversion".  `uniqN_false` refutes its **unconditional** form at `n = 1`.  Whether it refutes
the theorem as stated turns on one open question:

> **Is `DefInv ∅ 1 1` true?**

`thm_utype_one_false_of_defInv` (machine-checked) states the dichotomy:

* if **yes** — `thm:utype` is **false** at `n = 1`, not merely unproved, and the reference's
  induction `DefInv n → uniq n → DefInv (n+1)` is broken at its first step by the theorem
  rather than by the proof;
* if **no** — the route's own target `∀ n, DefInv env U n` fails over the empty environment at
  its first non-trivial index, which closes `IsDefEqU.sort_inv_of_defInv` as a route.

Either way `unique.tex`'s induction cannot be repaired at `n = 1`.  **This is the single most
valuable thing to settle next; see §5.**

---

## 3. What is stated but open

* `AppDisj`, `AppPropDisj`, `AppUniqLvl`, `AppNotProof`, `AppPropAgree` — the five, unchanged
  in strength.  Nothing here proves or refutes any of them.
* `SubstDisj` (`ShapeSpine.lean`) — still not refuted; the `ShapeAgreeRefute` witness does not
  reach it (it would need `lhs` sort-shaped, or `a` Π-shaped, and neither is available —
  `a` Π-shaped is `DefInv 1` clause (3) and open).
* `DefInv ∅ 1 1` — see §2.
* Whether there is any `R` strictly between `RelTaut` and `RelDisj` that is inst-closed.  The
  schema says that is exactly what a strengthening would have to be; §1.3's table is four
  points, not an exhaustion.

---

## 4. What was tried and where it failed, with the exact step

1. **A single statement discharging all five.**  Found: `AppTypeUniq`.  It discharges all five
   (machine-checked).  Failed at: it is false — `appTypeUniq_false`, `n = 1`, over `∅`.
2. **A strengthened induction making the function-position IH non-vacuous.**  Found: the
   minimal such strengthening, `RelTaut`, at which the IH *is* non-vacuous and both (i) and
   (ii) are free.  Failed at: (iii) at `RelTaut` **is** `SortForallEDisjoint`
   (`RelTaut.separates_iff`), and `sortForallEDisjoint_of_rel` shows no other `R` does better.
3. **Carrying the Π components** (`PiCodConv` + `SubstDisj`).  The one decomposition into two
   statements neither of which is a fixpoint of the target, and it does close the case
   (`PiCodConv.appDisj`).  Failed at: `PiCodConv` is false — `piCodConv_false`, the witness
   lifted through one λ.
4. **Induction on the index.**  Failed at: four of the five are antitone in `n`, so the family
   is decreasing and there is no monotone strengthening to be had (§1.5).
5. **Index slack.**  `lhs_conv_a_succ` shows the failing pair is convertible at `n = 2`, so a
   *slackened* unique typing survives this witness.  Failed at: slack is unusable.  `∃ m, ⊢ₘ A ≡ B`
   is, by basics (3)/(4), the ambient conversion — i.e. `thm:unique` itself, the target — and
   `DefInv (n+1)` needs its input at `n`, not at `m + n`
   (`docs/reference-gap-thm-utype.md` §2's arithmetic).  *Analysis, not machine-checked.*
6. **The `Theory/SetModel/` route.**  See §6.3 — it is a different statement and cannot be
   stated across the boundary.

---

## 5. What I would pick up first

**Decide `DefInv ∅ 1 1`.**  It is a self-contained, finite question — one environment, one
index — and it now decides whether a published theorem is false (§2).  Nothing else in this
neighbourhood has that leverage.

*Analysis, not machine-checked*, on how it looks:

* **Clauses (1) and (3) look reachable by one induction** with the invariant "if one endpoint of
  a `⊢₁` conversion is a sort, so is the other, with `≈` levels".  Over `∅` the rules generating
  `≡₁` are `rfl`/`symm`/`trans`/`sortDF`/`appDF`/`lamDF`/`forallEDF`/`beta`/`eta`/`proofIrrel`
  (no `constDF`, no `extra` — `∅` has neither constants nor `defeqs`), and every typing premise
  sits at `⊢₀`, where typing is syntactically unique (`HasTypeN.uniq_zero`).  In particular
  `proofIrrel` cannot relate a sort to anything: `⊢₀ .sort u : q` pins `q = .sort (.succ u)`,
  and then `⊢₀ q : .sort .zero` would need `.succ (.succ u) = .zero`.
* **The catch is that a sort *is* `≡₁`-related to non-sorts**: `(λ_:A. .sort u) c ≡₁ .sort u`
  by `beta`.  So the invariant has to be "sort-shaped", not "is a sort", and the induction has
  to survive `trans` through a redex.  That is a confluence argument — but a confluence argument
  at index `1`, where all typing premises are `⊢₀` and therefore rigid.  This is `thm:1dinv` at
  its base case, and it is the smallest instance of `unique.tex` §§3–4 that exists.
* **Clause (2) is the hard one** and needs the same confluence argument on Π-shapes.
* If you get clauses (1)+(3) but not (2), that is already enough for the dichotomy's "yes"
  branch only if all three hold — `DefInv` is a structure.  A partial result does not decide
  §2, but a *refutation* of any one clause does.

Second: whether the *five* survive over `∅` at `n = 1`.  The witness does not refute them
(§6.2), and `sortForallEDisjoint_of` says any counterexample must have an application subject —
so a search for one is a search among applications, which is where this file's witnesses live.

---

## 6. Corrections and cautions

### 6.1 To `docs/reference-gap-thm-utype.md` §4

Its "**Not refuted, and not claimed: `thm:utype`'s statement.** Its application case carries
hypotheses this instance does not supply: a single term `e₁` carrying *both* Π types, and an
argument typed at *both* domains" — those hypotheses **are** now supplied, by
`ShapeSpine.lean`'s `ShapeAgreeRefute`, which post-dates that document.  The correct scope is
§2 above: the unconditional form is refuted, the conditional form is refuted iff
`DefInv ∅ 1 1`.  *I have not edited that file — it belongs to another stream's result.*

### 6.2 To `docs/handoff-stratified.md` §16.4

It records, as a *reading result*, that the `typeShapeAgree_false` witness "refutes none of the
five".  Now verified for **three of five** — `witness_shapes` machine-checks that of the two
types the witness supplies, `a` is sort-shaped and `lhs` is neither sort-shaped
(`lhs_not_sortLike`, already in the tree) nor Π-shaped (`lhs_not_piLike`, new).  That settles
`SortForallEDisjoint`, `PropForallEDisjoint` and `PropUniq`, whose hypotheses need a (sort, Π)
or (sort, sort) pair.

For `PropNotProof` and `PropTypeAgree` the check needs `¬ IsPropN [P] lhs`, and **I could not
close it unconditionally.**  What is machine-checked is `lhs_not_isPropN`: it follows from
`PropUniq ∅ 1 1` (since `lhs : .sort (.succ p)` and a second type `.sort .zero` would force
`.succ p ≈ .zero`).  So the honest statement is: *the witness refutes those two only if it also
refutes `PropUniq` — and it does not refute `PropUniq`.*  §16.4's claim stands, but its
justification for two of the five runs through one of the five.

### 6.3 On the two `PropUniq`s and the two `PropTypeAgree`s

`Lean4Lean.VEnv.PropUniq` and `Lean4Lean.VEnv.PropTypeAgree` are **each declared twice, with
different statements**:

* `Theory/Typing/PropShadow.lean:183` — `PropUniq (env) (U n : Nat)`, over `HasTypeN`,
  conclusion `u ≈ .zero ↔ v ≈ .zero`.  This is the one in the five-statement table.
* `Theory/SetModel/PropSplitAudit.lean:105` — `PropUniq (env) (nv : ℕ)`, over the
  **unstratified** `HasType`, with `WF` premises and a conclusion at one fixed valuation
  `ls`: `u.eval ls = 0 ↔ v.eval ls = 0`.
* `Theory/Typing/UniqueTypingN.lean:562` vs `Theory/SetModel/PropSplitAudit.lean:119` for
  `PropTypeAgree`; the `SetModel` one additionally takes the *sorts of both types* as premises.

**Machine-checked by me:** the two module trees **cannot be imported together** — Lean rejects
`import Lean4Lean.Theory.SetModel.PropUniqFromFalse` after
`Lean4Lean.Theory.Typing.UniqueTypingN` with *"environment already contains
`Lean4Lean.VEnv.PropTypeAgree`"*.  No declaration in this repository can therefore relate them.
**Neither stream may quote the other's `PropUniq`/`PropTypeAgree` until the names are
disambiguated.**

Does the `SetModel` route (`PropUniqFromFalse.lean`'s `PropUniq.of_propTypeAgree`) reach the
`app` case of any of the five?  **No**, for three independent reasons (*source reading*, except
the import check above):

1. `HasTypeN` and `Stratified` occur **nowhere** in `Theory/SetModel/` (checked by search).
   All five `app` cases are statements at an index.
2. Its hypothesis is `∃ e, env.HasType 0 [] e falseProp` — an inhabitant of `∀ p : Prop, p`,
   i.e. the environment is inconsistent.  `PropUniqFromFalse.lean`'s own note says it is
   "available inside the consistency proof and nowhere else".  It is not available over `∅`,
   where every witness in this neighbourhood lives.
3. Even granting a statement match, `AppUniqLvl.iff` says `PropUniq.AppCase ↔ PropUniq`, so a
   proof of `PropUniq` closes *its own* `app` case and says nothing about the other four.

### 6.4 To the briefing this stream received

* "`PropConv.lean` records a witness refuting the natural unifier" — the witness is in
  `Theory/Typing/ShapeSpine.lean` (`typeShapeAgree_false`, `ShapeAgreeRefute`); `PropConv.lean`
  §16.4 only cites it.
* "the natural unifier is **false**" — true of *that* unifier (shape agreement).  There is a
  second, genuine unifier that the tree had not named — `AppTypeUniq`, which really does imply
  all five — and it is false too, by the same witness.  The two are different statements and
  the second is the informative one.
* Nothing in this file leans on `RegPi` or `propTypeAgree_appCase_of`, so the `regPi_false`
  result does not touch it.

### 6.5 Two things not to redo

* **Do not re-derive the witness.**  `ShapeAgreeRefute` in `ShapeSpine.lean` is complete and
  every result here is one or two lines on top of it.
* **Do not read `uniqN_false` as "unique typing is false for Lean".**  `lhs_conv_a_succ` is in
  the file for exactly this reason: the same pair is convertible at `n = 2`.  What fails is
  unique typing *at a fixed alternation index*, which is the only form the reference's
  induction can use.
