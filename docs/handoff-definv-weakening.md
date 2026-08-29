# Handoff: the `DefInv` weakening, the vacuity audit, and what is left of clauses (1) and (3)

**Input to this stream:** `docs/handoff-definv-one.md` — `DefInv ∅ 1 1` is **refuted**, through
**clause (2) only**, and the recommendation that whoever owns `Theory/Typing/UniqueTypingN.lean`
narrow every consumer to the clause it actually uses.

**Everything marked *machine-checked* is a sorry-free declaration in this repository**, built
by `~/.elan/bin/lake build Lean4Lean.Theory` at the commit this document lands on; axioms are
`propext`, `Quot.sound`, `Classical.choice` only — verified for all 116 declarations of the new
file `Theory/Typing/SortClauses.lean` by a `collectAxioms` sweep over its module.  Claims marked
*measured* come from `scripts/definv-cone.lean` (the transitive `getUsedConstantsAsSet` cone,
`allowOpaque := true`).  Claims marked *analysis* are neither.

---

## 0. Headline

1. **The weakening is done** in `UniqueTypingN.lean` and `PropShadow.lean`.  `DefInv` is now
   *assembled from* three separately named clauses — `SortInvN`, `ForallEInvN`,
   `SortForallEDisjN` — and **ten** consumers were narrowed.  One of the ten
   (`sortForallEDisjoint_of`) also keeps a `DefInv`-taking wrapper, because a single call site
   in a file this stream does not own has not been updated; see §5.
2. **The vacuity audit is in §2**, as an explicit list, measured rather than grepped.  **Five
   declarations genuinely consume the refuted clause; thirty-two are rescuable by the same
   narrowing and live in files this stream does not own.**
3. **Non-vacuity** (§3): every narrowed consumer is fired at index `0` over
   `CycleConv.propLoopEnv`, at instances that do not exist over `∅` — the `const` case of
   `sortForallEDisjoint_ofN` among them.
4. **New, and it corrects the input handoff** (§4): `docs/handoff-definv-one.md` §6 says "what
   remains for (1) and (3) is exactly the `trans` case".  Against the right predicate it is not.
   `SortRed` — weak-head β reduction to a sort — makes `trans` free, and reduces clauses (1) and
   (3) at index `n+1` to **four** residuals at `n`, of which **three are proved**.  So

       SortRedAppDF ∅ 1 0  →  SortInvN ∅ 1 1 ∧ SortForallEDisjN ∅ 1 1

   *machine-checked*, and the same over `propLoopEnv`.  One residual is what is left.
5. **`Ordered` is not enough** (§6): there is an `Ordered` environment at which clause (3) is
   **false** at index 1, and at which `Injectivity.lean`'s `IsDefEqU.sort_forallE_inv` is false
   too.  It is not `VEnv.WF`.  So no proof of the surviving clauses can use only the `Ordered`
   premise the two live reductions carry.

---

## 1. What was weakened, and to what

All in `Theory/Typing/UniqueTypingN.lean` unless noted.  **Machine-checked** — every one of
these compiles with the narrowed hypothesis and the proof body otherwise unchanged.

`DefInv` is unchanged as a *statement*; it is now written as a structure over three named
predicates, with the **field names kept** (`sort`, `forallE`, `sort_forallE`), so every existing
`dinv.sort h` / `dinv.sort_forallE h` in the tree still elaborates.

| new name | statement |
|---|---|
| `VEnv.SortInvN env U n` | clause (1), `unique.tex:32` — **not refuted** |
| `VEnv.ForallEInvN env U n` | clause (2), `unique.tex:33` — **FALSE** (`DefInvRefute.defInv_one_false`) |
| `VEnv.SortForallEDisjN env U n` | clause (3), `unique.tex:34` — **not refuted** |
| `SortInvN.zero`, `SortForallEDisjN.zero`, `ForallEInvN.zero` | all three at the base index |

| declaration | was | is now |
|---|---|---|
| `IsDefEqU.sort_inv_of_defInv` → **`IsDefEqU.sort_inv_of_sortInvN`** | `∀ n, DefInv` | `∀ n, SortInvN` |
| `IsDefEqU.sort_forallE_inv_of_defInv` → **`IsDefEqU.sort_forallE_inv_of_sortForallEDisjN`** | `∀ n, DefInv` | `∀ n, SortForallEDisjN` |
| `IsDefEqN.sort_imax_congr` | `DefInv` | `SortInvN` |
| `DefInv.sort_proofIrrel` → **`SortInvN.sort_proofIrrel`** | inline clause (1) | `SortInvN` (same statement, named) |
| `sortNotProof_of` | `DefInv` | `SortInvN` |
| `forallENotProof_of` | `DefInv` | `SortInvN` |
| `propNotProof_of` | `DefInv` | `SortInvN` |
| `PropTypeAgree.eta_case` | `DefInv` | `SortForallEDisjN` |
| `sortForallEDisjoint_of` → **`sortForallEDisjoint_ofN`** | `DefInv` | `SortForallEDisjN` |
| `PropShadow.lvlConvInv_of_defInv_sort` → **`lvlConvInv_of_sortInvN`** | inline clause (1) | `SortInvN` |

The two renames of the live reductions match the names `DefInvRefute` already used for the
same statements (`sort_inv_of_sortInvN`, `sort_forallE_inv_of_sortForallEDisjN`).  They could
not be literally reused: `DefInvRefute` imports `UniqueTypingN`, not the other way round.
`SortClauses.sortInvN_eq_defInvRefute` and `sortForallEDisjN_eq_defInvRefute` machine-check
that the two pairs of predicates are the *same* definition (`rfl`), so nothing was restated
with a different meaning.

**`PropShadow.lean` needed almost nothing.**  *Measured*: no declaration in that file is in the
`DefInv` cone at all.  `app_shadow_arith`, `app_shadow_of`, `InstLvl`, `PropUniq`, `LvlConvInv`
never mentioned `DefInv`, and `lvlConvInv_of_defInv_sort` already spelled clause (1) out inline
rather than taking the structure.  Only the name and the docstring changed.

**Kept at `DefInv` deliberately**: `Stratified.uniq`, `HasTypeN.uniq`.  They consume clause (2)
(`dinv.forallE` in the `app` case) and cannot be narrowed.  Their docstrings already record that
they are content-free above `n = 0` because `SubstC` is false; clause (2)'s refutation is a
second, independent reason.

---

## 2. The vacuity audit

*Measured* with `scripts/definv-cone.lean` (new, committed alongside this document; it reuses
`scripts/cone-measure.lean`'s `allowOpaque := true` fix for the `.thmInfo` scan trap).  A
name-based grep is not used anywhere below.

Cone sizes, after the weakening: transitive users of `VEnv.DefInv` **96**; of `DefInv.sort`
**70**; of `DefInv.forallE` **43**; of `DefInv.sort_forallE` **29**.  Of the 96, **55** carry
the hypothesis in their own *type* (the remaining 41 merely instantiate at `DefInv.zero`, or at
`HasTypeN.uniq_zero`, which are theorems — those are **not** vacuous and are excluded below).
Eight of the 55 are compiler-generated (`DefInv.mk`, `.mk._flat_ctor`, `.rec`, `.recOn`,
`.casesOn`, and the three projections), and six more are `DefInvRefute`'s own refutations and
implications, which take `DefInv` deliberately.  **39 real declarations remain**, and they split
5 / 1 / 1 / 32 across §§2a–2b below.

The classification below is the tool's: a declaration "consumes clause (k)" iff its transitive
dependency set reaches the corresponding projection (or `DefInv.rec`/`.casesOn`, which destructs
all three).

### 2a. Genuinely void — consume clause (2), which is refuted (5)

At `env = ∅, U = 1, n = 1` these prove nothing.  **They are not false, and their conclusions
are not refuted** — the theorems are simply vacuous at that instance.

| declaration | file | clauses | note |
|---|---|---|---|
| `Stratified.uniq` | `UniqueTypingN.lean` | (1),(2) | also carries `SubstC`, already false |
| `HasTypeN.uniq` | `UniqueTypingN.lean` | (1),(2) | ditto |
| `UniqN.of_defInv_substC` | `AppCase.lean` | (1),(2) | ditto |
| `AppCaseRefute.substC_false_of_defInv` | `AppCase.lean` | (1),(2) | a *negative* result whose hypothesis is now known false, so it says nothing new; `SubstCRefute.substC_false` proves the same thing unconditionally |
| `applyDisj` | `ShapeSpine.lean` | (2),(3) | **the only one that is void and not otherwise covered.**  Spine determinism from `SubstDisj` + `DefInv`; it needs clause (2) and cannot be rescued by narrowing |

`AppCaseRefute.thm_utype_one_false_of_defInv` (`AppCase.lean`) is a sixth entry of a different
kind: it consumes no clause, but its hypothesis is literally `DefInv ∅ 1 1`, so it is vacuously
true.  `DefInvRefute.thm_utype_one_vacuous` already records this and supersedes it.

### 2b. Rescuable by the same narrowing — do **not** consume clause (2) (32)

Every one of these lives in a file this stream does not own.  The column says which clause the
proof actually reaches; narrowing is mechanical (replace `env.DefInv U n` by `env.SortInvN U n`
and/or `env.SortForallEDisjN U n`, and drop the `.sort` / `.sort_forallE` projections in the
body).

**`Theory/Typing/AppCase.lean` (3)** — the three named in `docs/handoff-definv-one.md` §6:

| declaration | clause |
|---|---|
| `AppTypeUniq.appDisj` | (3) |
| `AppTypeUniq.appPropDisj` | (3) |
| `AppTypeUniq.appUniqLvl` | (1) |

**`Theory/Typing/PropConv.lean` (23):**

| declaration | clauses | | declaration | clauses |
|---|---|---|---|---|
| `not_isPropN_sort` | (1) | | `propUniq_of` | (1),(3) |
| `not_isPropN_lam` | (3) | | `propUniq_of'` | (1),(3) |
| `isPropN_forallE_inv` | (1) | | `propNotProof_of'` | (1),(3) |
| `isPropN_forallE_congr` | (1) | | `propNotProof_of''` | (1),(3) |
| `propConvInv_of` | (1),(3) | | `propNotProof_appCase_ih_vacuous` | (3) |
| `propConvInv_of'` | (1),(3) | | `propTypeAgree_of` | (1) |
| `propForallEDF_of` | (1) | | `propTypeAgree_of'` | (1) |
| `propForallEDisjointCases` | (3) | | `propTypeAgree_appCase_of` | (1) |
| `propForallEDisjoint_of` | (3) | | `SortNotProp.of_propConvInv` | (1) |
| `propForallEDisjoint_of'` | (3) | | `PropUniq.appCase_iff` | (1),(3) |
| `PropForallEDisjoint.appCase_iff` | (3) | | `PropNotProof.appCase_iff` | (1),(3) |
| `PropTypeAgree.appCase_iff` | (1) | | | |

**`Theory/Typing/RegPiSat.lean` (5):** `propTypeAgree_appCase_on_of` (1), `propTypeAgree_on_of`
(1), `propTypeAgree_on_of'` (1), `propTypeAgreeOn_of_residuals` (1),
`propConvInv_from_sortNotProp_cycle` (1),(3).

**`Theory/Typing/UnivDiscrim.lean` (1):** `appCase_ih_vacuous` (3).

**`Theory/Typing/DefInvRefute.lean` (2):** `sortInvN_of_defInv` (1), `sortForallEDisjN_of_defInv`
(3) — these are *deliberately* stated against `DefInv`; they are the implications, not
consumers.  Nothing to do.

### 2c. Not vacuous, though a cone-only tool flags them

The 41 declarations excluded above reach `DefInv.forallE` only through `DefInv.zero` — a
theorem — or through `HasTypeN.uniq_zero`, which is unconditional.  They are base-index replays
(`PropUniq.zero`, `UniqN.zero`, `SortForallEDisjoint.zero`, `PropTypeAgree.zero`, …) and are
sound as they stand.  Distinguishing them from 2a is exactly why the audit reads the
declaration's **type** and not only its dependency cone.

---

## 3. Non-vacuity of the weakened statements

The repo convention (`Theory/Typing/RegPiSat.lean`'s `RegPiOn` treatment) is: replay at index
zero, and **not over the empty environment**.  All in `Theory/Typing/SortClauses.lean` §2,
**machine-checked**, over `CycleConv.propLoopEnv` — two constants `A B : Prop`, two δ-rules
`A ≡ B`, `B ≡ A`, `propLoopEnv_wf` — so both the `const` case of the inductions and the
`defeqs` field are inhabited.

| what fires | conclusion, at a real instance |
|---|---|
| `SortInvN.zero`, `SortForallEDisjN.zero` | both clauses hold at index 0 over `propLoopEnv` |
| `sortNotProof_of` | `propLoopEnv_sort_not_proof` — no sort inhabits the proposition `A` |
| `forallENotProof_of` | `propLoopEnv_forallE_not_proof` — no Π-type inhabits `A` |
| `propNotProof_of` | `propLoopEnv_B_not_proof_of_A` — `B` is not a proof of `A`, and both are genuine `⊢₀` propositions of that environment |
| `sortForallEDisjoint_ofN` | `propLoopEnv_constA_not_forallE_typed` — **fires through the `const` case, which is empty over `∅`**: `VEnv.empty` has no constants at all |
| `PropTypeAgree.eta_case` | `propLoopEnv_eta_case_fires`, at the Π-typed variable in the context `[propArrow]` that `RegPiSat.propLoopEnv_regPiOn_fires` uses |

**One honest limitation, stated rather than papered over.**  The two `∀ n` reductions
(`sort_inv_of_sortInvN`, `sort_forallE_inv_of_sortForallEDisjN`) cannot be given a satisfied
hypothesis, because `∀ n, SortInvN env U n` at any environment *is* the open goal.  What §4
supplies instead is a *conditional* discharge with one named residual, and §6 supplies the
environment condition under which the hypothesis is not already false.  Clause (3) at index 0 is
in any case a shape fact with **no inhabited instance** — `≡₀` is syntactic equality, so
`.sort u ≡₀ .forallE A B` cannot arise — which is why the non-vacuity above is stated about the
*consumers* and not about the clauses themselves.

---

## 4. The live open goals, and what is now left of them

`Theory/Typing/SortClauses.lean` §4–§5.  All **machine-checked**.

    inductive HeadBeta : VExpr → VExpr → Prop            -- one weak-head β step
      | beta : HeadBeta (.app (.lam A e) a) (e.inst a)
      | app  : HeadBeta f f' → HeadBeta (.app f a) (.app f' a)

    inductive SortRed (u : VLevel) : VExpr → Prop        -- ↝*wh a sort of level ≈ u
      | sort : v ≈ u → SortRed u (.sort v)
      | step : HeadBeta X Y → SortRed u Y → SortRed u X

    SortRedInv env U n  :  Γ ⊢ₙ X ≡ Y → (SortRed u X ↔ SortRed u Y)

* `sortInvN_of_sortRedInv`, `sortForallEDisjN_of_sortRedInv` — `SortRedInv` implies **both**
  surviving clauses.
* `sortRedInv_of` — `SortRedInv env U (n+1)` from **four** residuals at `n`.  Free: `rfl`,
  `symm`, **`trans`**, `sortDF`, `constDF`, `lamDF`, `forallEDF`, `beta`.
* Residuals: `SortRedAppDF` (`appDF`), `PiTypedNotSortRed` (`eta`), `ProofNotSortRed`
  (`proofIrrel`), `ExtraSortRed` (`extra`).
* **Three of the four are discharged**: `PiTypedNotSortRed.zero` and `ProofNotSortRed.zero`
  from weak-head subject reduction at `⊢₀` (`HeadBeta.hasTypeN_zero`, which is
  `HasTypeN.app_inv` plus `Stratified.instN` at `m = 0`) together with
  `DefInvRefute.sort_not_proof0`; `ExtraSortRed.empty` is vacuous over `∅`, and
  `ExtraSortRed.propLoopEnv` is *proved* over the witness environment.
* Hence, machine-checked:
  `empty_sortInvN_one_of_appDF : SortRedAppDF ∅ 1 0 → SortInvN ∅ 1 1` and
  `empty_sortForallEDisjN_one_of_appDF : SortRedAppDF ∅ 1 0 → SortForallEDisjN ∅ 1 1`,
  and `propLoopEnv_sortInvN_one_of_appDF` / `propLoopEnv_sortForallEDisjN_one_of_appDF` over
  the non-empty environment.

**The design is forced.**  The cheaper predicate — contract the outermost head redex but never
reduce inside the function position — is **refuted**: `HeadOnly.sortRedHeadInv_one_false`, at
`n = 1` over `∅`, by one `appDF` whose four typing premises are `⊢₀` derivations.  The witness
is `cf := fun _ : Prop => Prop` against `cf' := (fun _ : Prop => cf) x`, both `⊢₀`-typed at
`∀ (_ : Prop), Type`, one `beta` step apart.  `HeadOnly.app_cf'_sortRed` checks the real
`SortRed` survives that same witness, so the `app` step is load-bearing rather than decorative,
and `HeadOnly.sortRedAppDF_nondegenerate_instance` records that same pair as an instance of
`SortRedAppDF` with `f ≠ f'` at which the residual's conclusion is **true** — so the residual is
neither premise-empty nor true only by reflexivity.  `SortRedInv.zero` holds unconditionally, so
the whole scheme is inhabited at the base index.

### What this does **not** claim

`trans` is free *at the top level of `sortRedInv_of`*.  It reappears inside `SortRedAppDF`,
whose premise `Γ ⊢ₙ₊₁ f ≡ f'` is an arbitrary conversion.  What changed is the *shape* of the
obligation: it is now one statement about applications whose two function endpoints are
`⊢ₙ`-typed **at the same Π-type**, instead of an obligation spread over every rule with a
`trans` middle term that carries no typing at all (which is what
`Theory/Typing/PropShadow.lean`'s `trans_middle_has_no_stage_universe` shows is the worst case).
*Analysis, not machine-checked*: that shared `⊢₀` type is genuinely restrictive — it is what
kills the two obvious routes to a counterexample.  `lamDF` would relate `.lam A (.sort v)` to
`.lam A' (.sort v')`, and the shared `⊢₀` type forces `A = A'` and `v = v'` syntactically;
`proofIrrel` would need `⊢₀ (∀A.B) : .sort .zero`, which `HasTypeN.forallE_inv` refutes because
the `⊢₀` type of a Π is `.sort (.imax _ _)` and `.imax _ _ ≠ .zero`.  **`SortRedAppDF ∅ 1 0` is
neither proved nor refuted.**

---

## 5. What broke, and what this stream did not touch

**One call site.**  Weakening `sortForallEDisjoint_of` in place produces exactly one error, in a
file this stream does not own:

    error: Lean4Lean/Theory/Typing/PropConv.lean:331:33: Type mismatch
      dinv
    has type
      env.DefInv U n
    but is expected to have type
      ¬env.IsDefEqN U n Γ (VExpr.sort u) (A.forallE B)

The fix is one token: in `propForallEDisjoint_of`, call `sortForallEDisjoint_ofN` and pass
`dinv.sort_forallE` instead of `dinv`.

**Rather than leave the tree red**, the narrowed induction was landed under the new name
`sortForallEDisjoint_ofN` and `sortForallEDisjoint_of` kept as a two-line wrapper
(`fun happ dinv => sortForallEDisjoint_ofN H happ dinv.sort_forallE`), documented as such.
`~/.elan/bin/lake build Lean4Lean.Theory` is green.  **When PropConv.lean is updated,
`sortForallEDisjoint_of` should be deleted** — nothing else in the tree uses it (*measured*).

Nothing else in the tree broke.  No file outside `Theory/Typing/UniqueTypingN.lean`,
`Theory/Typing/PropShadow.lean`, the new `Theory/Typing/SortClauses.lean` and the new
`scripts/definv-cone.lean` was edited.

---

## 6. `Ordered` is not enough — a correction to the two live reductions

`Theory/Typing/SortClauses.lean` §3, **machine-checked**.

    sortPiRule : VDefEq := ⟨0, Prop, ∀ (_ : Prop), Prop, Type⟩
    sortPiEnv  : VEnv   := ∅.addDefEq sortPiRule

* `sortPiRule_wf` — both sides are `HasType`-typed at `.sort (.succ .zero)`, since
  `imax 1 1 ≈ 1`.  So `VDefEq.WF ∅` holds and `sortPiEnv_ordered : Ordered sortPiEnv`.
* `sortPiEnv_sortForallEDisjN_false : ¬ SortForallEDisjN sortPiEnv 0 1` — one `Stratified.extra`.
* `sortPiEnv_sortForallEDisjN_all_false : ¬ ∀ n, SortForallEDisjN sortPiEnv 0 n` — **this is
  exactly the hypothesis of `IsDefEqU.sort_forallE_inv_of_sortForallEDisjN`**, false at an
  environment that theorem's `Ordered env` premise admits.
* `sortPiEnv_ambient_conv` — `Injectivity.lean`'s `IsDefEqU.sort_forallE_inv` is false there too.
* `sortPiEnv_not_wf : ¬ sortPiEnv.WF` — via `DeclRules.lean`'s `IsDeclRule.lhs_ne_sort`.

**Consequence.**  The reductions themselves are correct as stated (a stronger environment
premise would only weaken them), but *any* proof of `∀ n, SortForallEDisjN env U n` must use
`VEnv.WF env`, not merely `Ordered env`.  `Theory/Typing/DeclRules.lean` already carries the
tool — `WF.instL_lhs_ne_sort` — and it is what discharges `ExtraSortRed`'s `sort` constructor;
what it does **not** discharge is `ExtraSortRed`'s `beta` constructor, since a declaration rule's
`lhs` may be `app`- or `lam`-headed.  Clause (1) at an `Ordered` environment is *not* refuted by
this witness and remains open: `VDefEq.WF` pins both sides of a rule at one type, which blocks
the sort-to-sort analogue.

---

## 7. What to pick up first

1. **`SortRedAppDF ∅ 1 0`.**  It is now the *single* residual between the tree and both
   surviving clauses at index 1 (§4), it is a finite question over one environment, and it is
   the direct successor to `docs/handoff-definv-one.md` §6's question.  A refutation is worth as
   much as a proof; two refutation attempts and why they fail are in §4.
2. **The 32 rescuable declarations** (§2b).  Mechanical, and until it is done the three
   statements `docs/handoff-definv-one.md` names (`AppTypeUniq.appDisj`, `.appPropDisj`,
   `.appUniqLvl`) read as progress while proving nothing at the refuted instance.  Start with
   `PropConv.lean:331`, which also unblocks deleting `sortForallEDisjoint_of` (§5).
3. **`applyDisj`** (`ShapeSpine.lean`) is the one void result that narrowing cannot save (§2a).
   Its docstring should say so, and `ShapeSpine.lean`'s §"Spine determinism" claim should be
   re-priced: over `∅` at `n = 1` it currently has no content.
4. **`ExtraSortRed` under `VEnv.WF`.**  §6 says `WF` kills the `sort` constructor but not
   `beta`.  Sharpening `VDefEq.IsDeclRule.lhs_shape` to "app-headed rules have a `const`-headed
   spine head" would discharge `ExtraSortRed` for every well-formed environment in one step, and
   that is a small, self-contained lemma about `Theory/Typing/DeclRules.lean`.

## 8. Corrections to what this stream was handed

* `docs/handoff-definv-one.md` §6, "**What remains for (1) and (3) is exactly the `trans`
  case**" — **not correct as a statement about the obligation**, only about the naive
  shape invariant.  §4 above makes `trans` free and leaves `appDF`.  The document's larger
  point — that a reduction relation has to be named — stands, and `SortRed` is that relation.
* `docs/handoff-definv-one.md` §5 recommends splitting `DefInv` into its three clauses and says
  "everything else in that file … genuinely needs more than one clause and should keep
  `DefInv`".  *Measured*: only `Stratified.uniq` and `HasTypeN.uniq` do.
  `IsDefEqN.sort_imax_congr`, `DefInv.sort_proofIrrel`, `sortNotProof_of`, `forallENotProof_of`,
  `propNotProof_of`, `PropTypeAgree.eta_case` and `sortForallEDisjoint_of` all needed exactly
  one clause and have been narrowed.
* `docs/handoff-definv-one.md` §5's note that `DefInvRefute`'s `SortInvN`/`SortForallEDisjN` sit
  in a local namespace "to avoid the double-declaration problem" — the `VEnv`-level names are now
  declared in `UniqueTypingN.lean` and there is **no** ambiguity: Lean's name resolution prefers
  the innermost namespace, so `DefInvRefute`'s own references still resolve to its own copies.
  Checked by building.  The two pairs are `rfl`-equal (§1).
* `docs/handoff-appcase.md` §6.3's warning about `PropUniq`/`PropTypeAgree` being declared twice
  is unaffected by anything here; `SortClauses.lean` imports only `Theory/Typing/`.
