# Handoff: the `DefInv` rescue — 32 vacuous results narrowed, 5 recorded void

**Input to this stream:** `docs/handoff-definv-weakening.md` §2 — the measured vacuity audit.
`VEnv.DefInv` is machine-checked **false** at `env = ∅, U = 1, n = 1`
(`DefInvRefute.defInv_one_false`), through **clause (2)** (`ForallEInvN`) alone.  39 real
declarations carried `DefInv` in their own type; 5 genuinely consume the refuted clause, 1 is
vacuously true, and **32 were tagged rescuable**.

**Conventions.**  *Machine-checked* = a sorry-free declaration in this repository at the
commit this document lands on, built by `~/.elan/bin/lake build Lean4Lean.Theory`.  A
`collectAxioms` sweep over the five owned modules reports **346 declarations, 0 outside the
`propext` / `Quot.sound` / `Classical.choice` whitelist**.  *Measured* = output of
`scripts/definv-cone.lean` (unchanged; it is the same tool that produced the input audit).
*Analysis* = neither, and is labelled inline.

---

## 0. Headline

1. **All 32 are rescued** (§2).  Every one now carries the clause, or the pair of clauses, it
   actually consumes; none carries clause (2).  *Measured*: the population of declarations
   whose **type** mentions `DefInv` falls from **54 to 23**, and the 31-row difference is
   exactly the 32 rescued minus one new deliberate implication (§1).
2. **Every tag in the input audit is correct** (§2.4).  Each narrowing was verified by
   compilation, not assumed.
3. **Non-vacuity is discharged for 29 of the 32** (§3), by firing each over
   `CycleConv.propLoopEnv` at index `0`.  **Three cannot be** — they are stated only at
   `n = k+1` — and §3.3 says exactly what the narrowing buys them instead.  This is stated as
   a limitation rather than papered over.
4. **The 5 void results are marked in place** (§4), each with what would restore it.
   `applyDisj` (`ShapeSpine.lean`) is the one narrowing cannot save, and its module docstring's
   "spine determinism" claim is re-priced.
5. **One thing is left, and it is in a file this stream does not own** (§5):
   `UniqueTypingN.lean`'s two-line wrapper `sortForallEDisjoint_of`.  *Measured*: it now has
   **zero** users.  Deleting it is the last step to "nothing outside the 5 known-void results
   carries `DefInv`", and this stream may not make it.
6. **Nothing was found false.**  The method note asked for it; no statement narrowed here
   turned out to be refutable rather than merely vacuous.

---

## 1. The narrowing, and the one new definition

`DefInv` remains a structure over `SortInvN` (clause 1), `ForallEInvN` (clause 2) and
`SortForallEDisjN` (clause 3), unchanged.  Nine of the 32 consume **both** surviving clauses,
so `Theory/Typing/PropConv.lean` declares one new predicate for them:

```lean
structure SortDisjInvN (env : VEnv) (U n : Nat) : Prop where
  sort : env.SortInvN U n
  sort_forallE : env.SortForallEDisjN U n

theorem DefInv.toSortDisjInvN (d : env.DefInv U n) : env.SortDisjInvN U n
theorem SortDisjInvN.zero : env.SortDisjInvN U 0
```

It is `DefInv` with the refuted clause deleted, and the field names are `DefInv`'s, so the
nine proof bodies are unchanged by the narrowing.  `DefInv.toSortDisjInvN` is the only
declaration this stream added whose type mentions `DefInv`; it is an implication, in the same
category as `DefInvRefute.sortInvN_of_defInv`, not a consumer.

*Analysis, not machine-checked*: `SortDisjInvN` is **strictly** weaker than `DefInv` — no
environment is known at which `DefInv` fails and `SortDisjInvN` holds, so strictness is not
exhibited by a witness.  What is machine-checked is the direction that matters: `DefInv ∅ 1 1`
is false and `SortDisjInvN ∅ 1 1` is open, with `SortClauses.empty_sortInvN_one_of_appDF` and
`empty_sortForallEDisjN_one_of_appDF` reducing both halves of it to the single residual
`SortRedAppDF ∅ 1 0`.

---

## 2. The before/after audit

### 2.1 The numbers

*Measured*, `~/.elan/bin/lake env lean scripts/definv-cone.lean`, same tool both times.

| | before | after |
|---|---|---|
| declarations whose **type** mentions `DefInv` | 54 | **23** |
| …of which compiler-generated (`.mk`, `.mk._flat_ctor`, `.rec`, `.recOn`, `.casesOn`, 3 projections) | 8 | 8 |
| …`DefInv.zero` (a theorem, not a consumer) | 1 | 1 |
| …`DefInvRefute`'s own refutations and implications | 6 | 6 |
| …deliberate implications added here (`DefInv.toSortDisjInvN`) | 0 | 1 |
| **real consumers** | **39** | **7** |

Cone sizes (transitive users): `DefInv` 96 → 129; `DefInv.sort` 70 → 72; `DefInv.forallE`
43 → 56; `DefInv.sort_forallE` 29 → 31.  **These went up, and that is not a regression.**  The
cone counts *proof-term* reachability, and the ~50 non-vacuity replays added in §3 all go
through `SortInvN.zero` / `SortForallEDisjN.zero`, which are defined as `DefInv.zero.sort` and
`DefInv.zero.sort_forallE` — reaching a **proved theorem**, which is §2c of the input audit's
"not vacuous" category.  The number that measures vacuity is the type-mentions row above, and
it fell by 31.

### 2.2 The 7 that remain

| declaration | file | status |
|---|---|---|
| `Stratified.uniq` | `UniqueTypingN.lean` | **void** (clause 2 + `SubstC`) |
| `HasTypeN.uniq` | `UniqueTypingN.lean` | **void** (clause 2 + `SubstC`) |
| `UniqN.of_defInv_substC` | `AppCase.lean` | **void**; marked in place (§4) |
| `AppCaseRefute.substC_false_of_defInv` | `AppCase.lean` | **void**, superseded; marked (§4) |
| `applyDisj` | `ShapeSpine.lean` | **void**, not superseded; marked (§4) |
| `AppCaseRefute.thm_utype_one_false_of_defInv` | `AppCase.lean` | **vacuously true**, superseded; marked (§4) |
| `sortForallEDisjoint_of` | `UniqueTypingN.lean` | **dead wrapper**, 0 users — see §5 |

The first six are exactly the input audit's §2a plus its sixth entry.  The seventh is the
deferral this stream was asked to end and could not; it is the only unfinished item.

### 2.3 What each of the 32 was narrowed to

Every row is *machine-checked*: the declaration compiles with the stated hypothesis and its
proof body otherwise unchanged.

**`Theory/Typing/PropConv.lean` (23)**

| declaration | now takes | | declaration | now takes |
|---|---|---|---|---|
| `not_isPropN_sort` | `SortInvN` | | `propUniq_of` | `SortDisjInvN` |
| `not_isPropN_lam` | `SortForallEDisjN` | | `propUniq_of'` | `SortDisjInvN` |
| `isPropN_forallE_inv` | `SortInvN` | | `propNotProof_of'` | `SortDisjInvN` |
| `isPropN_forallE_congr` | `SortInvN` | | `propNotProof_of''` | `SortDisjInvN` |
| `propConvInv_of` | `SortDisjInvN` | | `propNotProof_appCase_ih_vacuous` | `SortForallEDisjN` |
| `propConvInv_of'` | `SortDisjInvN` | | `propTypeAgree_of` | `SortInvN` |
| `propForallEDF_of` | `SortInvN` | | `propTypeAgree_of'` | `SortInvN` |
| `propForallEDisjointCases` | `SortForallEDisjN` | | `propTypeAgree_appCase_of` | `SortInvN` |
| `propForallEDisjoint_of` | `SortForallEDisjN` | | `SortNotProp.of_propConvInv` | `SortInvN` |
| `propForallEDisjoint_of'` | `SortForallEDisjN` | | `PropUniq.appCase_iff` | `SortDisjInvN` |
| `PropForallEDisjoint.appCase_iff` | `SortForallEDisjN` | | `PropNotProof.appCase_iff` | `SortDisjInvN` |
| `PropTypeAgree.appCase_iff` | `SortInvN` | | | |

**`Theory/Typing/RegPiSat.lean` (5):** `propTypeAgree_appCase_on_of`, `propTypeAgree_on_of`,
`propTypeAgree_on_of'`, `propTypeAgreeOn_of_residuals` → `SortInvN`;
`propConvInv_from_sortNotProp_cycle` → `SortDisjInvN`.

**`Theory/Typing/AppCase.lean` (3):** `AppTypeUniq.appDisj`, `AppTypeUniq.appPropDisj` →
`SortForallEDisjN`; `AppTypeUniq.appUniqLvl` → `SortInvN`.

**`Theory/Typing/UnivDiscrim.lean` (1):** `appCase_ih_vacuous` → `SortForallEDisjN`.

Seven `DefInv.zero` instantiations inside `PropConv.lean`'s and `RegPiSat.lean`'s base-index
replay sections were retargeted to `SortInvN.zero` / `SortDisjInvN.zero` at the same time.

### 2.4 The tags were verified, not trusted

The task's failure mode is a mis-tagged consumer that stays vacuous silently.  Two checks:

* **Sufficiency — machine-checked.**  Each declaration was rewritten to take *only* the tagged
  clause(s) and the body left alone.  Lean accepts it.  A consumer tagged (1) that secretly
  reached clause (2) could not compile against `SortInvN`, so no such consumer survives.  All
  32 tags were correct; **no correction to the input audit's §2b is needed**.
* **Necessity — read off source, not machine-checked.**  For the nine `SortDisjInvN`
  consumers, both projections were confirmed used by reading the proof: `propConvInv_of` uses
  `.sort` in `sortDF` and `.sort_forallE` in `lamDF` and `eta`; `propNotProof_of'` uses `.sort`
  in `sort` and `.sort_forallE` in `lam`; `propUniq_of` uses `.sort` in four cases and
  `.sort_forallE` in `lam`; the other six inherit through those three.  Necessity is moot for
  the 23 single-clause consumers.

---

## 3. Non-vacuity

The repo convention (`SortClauses.lean` §2): replay at index `0`, over
`CycleConv.propLoopEnv` — two constants `A B : Prop`, two δ-rules `A ≡ B`, `B ≡ A`,
`propLoopEnv_wf` — **not** over `∅`, because the `const` case of these inductions and the
`defeqs` field of `PropExtraConv` are empty over `VEnv.empty`.

All firings are **machine-checked**, in `RegPiSat.lean` §8 (`section NonVacuity`) and
`AppCase.lean` §"Non-vacuity".

### 3.1 The hypotheses are inhabited

`propLoopEnv_sortInvN0`, `propLoopEnv_sortForallEDisjN0`, `propLoopEnv_sortDisjInvN0` — all
three narrowed hypotheses hold at index `0` over the witness environment.

### 3.2 The 29 firings

| fired consumer(s) | witness / conclusion |
|---|---|
| `not_isPropN_lam` | `propLoopEnv_id_not_isProp` — the identity λ **on the environment's own proposition `A`**, a term that does not exist over `∅` |
| `propForallEDisjointCases`, `propForallEDisjoint_of`, `propForallEDisjoint_of'` | `propLoopEnv_propForallEDisjoint0`, `…0'` — both routes; the first goes through `sortForallEDisjoint_ofN`, i.e. through the call site moved in §5 |
| ↳ real instance | `propLoopEnv_constA_not_pi` — `A` is a `⊢₀`-typed proposition here, so the premise is inhabited |
| `PropForallEDisjoint.appCase_iff` | `propLoopEnv_propForallEDisjoint_iff0` |
| `propNotProof_appCase_ih_vacuous`, `appCase_ih_vacuous` | `propLoopEnv_propNotProof_ih_vacuous`, `propLoopEnv_appCase_ih_vacuous`, at the environment's Π-type `propArrow` |
| `AppTypeUniq.appDisj`, `.appPropDisj` | `propLoopEnv_appDisj0`, `propLoopEnv_appPropDisj0` (in `AppCase.lean`) |
| `not_isPropN_sort` | `propLoopEnv_not_isPropN_sort` |
| `isPropN_forallE_inv`, `isPropN_forallE_congr` | `propLoopEnv_isPropN_forallE_inv`, `…_congr`, at `propArrow` — see the caveat below |
| `propForallEDF_of` | `propLoopEnv_propForallEDF0` |
| `SortNotProp.of_propConvInv` | `propLoopEnv_sortNotProp0` |
| `propTypeAgree_of`, `propTypeAgree_of'`, `PropTypeAgree.appCase_iff` | `propLoopEnv_propTypeAgree0`, `propLoopEnv_propTypeAgree_iff0` |
| `propTypeAgree_on_of`, `propTypeAgree_on_of'` | `propLoopEnv_propTypeAgreeOn0`; its `Regular` premise goes through `propLoopEnv_constPropType`, which **needs** the constants |
| `AppTypeUniq.appUniqLvl` | `propLoopEnv_appUniqLvl0` (in `AppCase.lean`) |
| `propConvInv_of`, `propConvInv_of'` | `propLoopEnv_propConvInv0`, from seven residuals — the seventh, `PropExtraConv`, is discharged by `propLoopEnv_propExtraConv_zero`, i.e. at an environment with **two δ-rules**, where over `∅` it would be vacuous |
| `propNotProof_of'`, `propNotProof_of''` | `propLoopEnv_propNotProof0` |
| ↳ real instance | `propLoopEnv_B_not_proof_A0` — `B` is not a proof of `A`, two genuine `⊢₀` propositions of this environment |
| `propUniq_of`, `propUniq_of'` | `propLoopEnv_propUniq0` |
| `PropUniq.appCase_iff`, `PropNotProof.appCase_iff` | `propLoopEnv_propUniq_iff0`, `propLoopEnv_propNotProof_iff0` |
| `propConvInv_from_sortNotProp_cycle` | `propLoopEnv_propConvInv_cycle0` — all nine hypotheses discharged, including the `PropConvInv` that makes it a cycle |

**One caveat, stated rather than hidden.**  `isPropN_forallE_inv` and `isPropN_forallE_congr`
have a premise — `IsPropN env U 0 Γ (.forallE A B)` — that is **empty at index `0`**, because
`≡₀` is syntactic equality and `.imax u v` is never `.zero`.  Their own docstrings already say
so, and their proofs discharge the `n = 0` case rather than proving it.  What fires at
`propLoopEnv` is the statement at a real environment and a real Π-type; the premise's
inhabitedness is a separate, index-`≥ 1` question that this replay does not settle.

### 3.3 The three that cannot be fired, and what the narrowing buys them

`propTypeAgree_appCase_of` (`PropConv.lean`), `propTypeAgree_appCase_on_of` and
`propTypeAgreeOn_of_residuals` (`RegPiSat.lean`) are stated only at `n = k+1`.  Their narrowed
hypothesis at the smallest index is `SortInvN env U 1`, which is **open** at every environment
— so there is no index-`0` replay for them, and none is claimed.

The narrowing is not empty for them either, and this is the sharpest statement of what the
whole round is worth:

* **before**, at `env = ∅, U = 1, k = 0`, their hypothesis was `DefInv ∅ 1 1`, which
  `DefInvRefute.defInv_one_false` **refutes** — the three theorems were literally vacuous
  there;
* **after**, it is `SortInvN ∅ 1 1`, which is not refuted, and
  `SortClauses.empty_sortInvN_one_of_appDF` (*machine-checked*, in a file downstream of these)
  reduces it to the single residual `SortRedAppDF ∅ 1 0`.

Their instance at `k = 0` is therefore **open rather than empty**.  This note is recorded in
`RegPiSat.lean` §8 as well, since a reader of the source needs it there.

---

## 4. What stayed void, marked in place

All five are **kept, not deleted** — a recorded refutation is a result — and each now carries
the marking at the top of its own docstring, where a reader hits it before the statement.

| declaration | file | marking | what would restore it |
|---|---|---|---|
| `applyDisj` | `ShapeSpine.lean` | **VOID, and narrowing cannot save it** | see below — this is the only one with no substitute |
| `UniqN.of_defInv_substC` | `AppCase.lean` | **VOID — both hypotheses refuted** | nothing short of new definitions: it needs clause (2), and `SubstC` is independently false |
| `AppCaseRefute.substC_false_of_defInv` | `AppCase.lean` | **VOID, and superseded** | nothing needed — `SubstCRefute.substC_false` proves the same conclusion unconditionally |
| `AppCaseRefute.thm_utype_one_false_of_defInv` | `AppCase.lean` | **VACUOUSLY TRUE, and superseded** | nothing needed — `DefInvRefute.thm_utype_one_vacuous` records the same fact unconditionally; the dichotomy it states has collapsed to its second horn |
| `Stratified.uniq`, `HasTypeN.uniq` | `UniqueTypingN.lean` | *not touched by this stream* — file not owned; `docs/handoff-definv-weakening.md` §1 records that their docstrings already state they are content-free above `n = 0` | as above: clause (2) plus `SubstC`, both refuted |

### `applyDisj` — the one that matters

`applyDisj`'s `cons` case uses `dinv.forallE`, and the use is not incidental: clause (2) is
precisely what turns `B.inst a ≡ B'.inst a` into the `SubstDisj`-shaped premise, which is why
the theorem needs **no induction on the spine**.  Narrowing is therefore impossible.

Two consequences, both now written into `ShapeSpine.lean`:

1. Its module docstring's §3 claimed `applyDisj` gives "spine determinism at a type".  At `∅`
   and `n = 1` that claim now has **no content**, and §3 says so.  `applyDisj_zero`
   (unconditional, no hypothesis at all) and `SubstDisj.zero`, which is proved from it, are
   unaffected — the `n = 0` story stands, the `n = 1` one does not.
2. *Measured*: `applyDisj` has **zero users** in the tree.  Nothing downstream is silently
   resting on it.

**What would restore it** (*analysis, not machine-checked*): either (a) a proof of
`ForallEInvN` at a class of environments excluding the refutation's witness — but the witness
is a `⊢₀`-typed configuration over `VEnv.empty`, which no environment condition can exclude, so
this route looks closed; or (b) a different bridge between the two codomains in the `cons`
case — which is exactly the "existence step" that `ShapeSpine.lean` §3 already records as
missing, so (b) is not a smaller problem than the one the file already leaves open.

---

## 5. The one unfinished item — and it needs the orchestrator

Task item 4 asked for two things.  The first is done:

* **`PropConv.lean:331` is moved.**  `propForallEDisjoint_of` now takes
  `env.SortForallEDisjN U n` and calls `sortForallEDisjoint_ofN h1 happ dinv …` directly.
  *Machine-checked*; `propLoopEnv_propForallEDisjoint0` fires it (§3.2).

The second cannot be done by this stream:

* **`sortForallEDisjoint_of` still exists**, at `Theory/Typing/UniqueTypingN.lean:776`.  That
  file is **not in this stream's owned list**, and the stream's brief forbids editing files it
  does not own.  The wrapper is now dead: *measured*, it has **zero** direct users anywhere in
  `Lean4Lean` (only prose mentions remain, in `PropConv.lean`, `UnivDiscrim.lean`,
  `ShapeSpine.lean` and `UniqueTypingN.lean` itself, all of which read fine as references to
  the induction rather than to the wrapper).

  The exact edit is: delete the declaration `sortForallEDisjoint_of` and its docstring at
  `UniqueTypingN.lean:768–780` (the docstring beginning "The same with the whole of `DefInv` in
  place of clause (3)" through the `fun happ dinv => sortForallEDisjoint_ofN …` body).  `docs/handoff-definv-weakening.md` §5 already documented it
  for deletion.  Until it happens, **the target end state of this round is not reached** —
  one declaration outside the 5 known-void results still carries `DefInv`.  Reporting the
  round as complete without this would be the partial-rescue-reported-as-complete failure the
  brief names, so it is called out here instead.

---

## 6. Build state

* `~/.elan/bin/lake build Lean4Lean.Theory` — green.
* No `sorry` introduced.  The pre-existing `sorry`s in `Theory/Typing/Injectivity.lean` (6)
  and `Theory/Inductive/Decl.lean` (1) are untouched and in files this stream does not own.
* `collectAxioms` over `PropConv`, `RegPiSat`, `AppCase`, `UnivDiscrim`, `ShapeSpine`:
  **346 declarations, 0 outside the `propext` / `Quot.sound` / `Classical.choice` whitelist**.
* Files edited: the five owned ones only, plus this document.  One import added
  (`AppCase.lean` now imports `Theory/Typing/CycleConv.lean`, for `propLoopEnv`; no cycle —
  `CycleConv` imports `LogRelRowZero`, `Injectivity`, `SortUniq`).

---

## 7. What to pick up first

1. **Delete `sortForallEDisjoint_of`** (§5).  One declaration, zero users, and it is the last
   thing between the tree and "nothing outside the 5 known-void results carries `DefInv`".
   Needs whoever owns `UniqueTypingN.lean`.
2. **`SortRedAppDF ∅ 1 0`** — unchanged from `docs/handoff-definv-weakening.md` §7.1, and this
   round raises its value: it is now the single residual standing between the tree and
   `SortInvN ∅ 1 1`, which is the hypothesis of **23 of the 32 rescued declarations** (14 directly, 9
   through `SortDisjInvN`) at their smallest instance, and the *only* thing that would make §3.3's three theorems non-vacuous
   at `k = 0`.
3. **`ShapeSpine.lean`'s `lam` case** (§4).  With `applyDisj` void, the file's spine-induction
   story rests entirely on `applyDisj_zero`.  Whether `SubstDisj` is still worth carrying is
   now an open question the file itself raises and does not answer.
4. **`ExtraSortRed` under `VEnv.WF`** — unchanged from `docs/handoff-definv-weakening.md` §7.4.

## 8. Corrections to what this stream was handed

* `docs/handoff-definv-weakening.md` §2b's 32 tags: **all correct**, verified by compilation
  (§2.4).  No correction.
* §2's arithmetic: "Eight of the 55 are compiler-generated … and six more are `DefInvRefute`'s"
  leaving 39.  The tool reports **54** type-mention rows, not 55, and the residue is
  54 − 8 − 6 − `DefInv.zero` = 39, which is the number §2 goes on to use.  The "55" is an
  off-by-one in the prose; the 39 it lands on is right.
* Task item 4's "delete the wrapper.  That file is yours now" — the *call site* is in
  `PropConv.lean` and is this stream's; the **wrapper is in `UniqueTypingN.lean`**, which is
  not.  See §5.
* Nothing in this round contradicts the input document's §§1, 3–6.
