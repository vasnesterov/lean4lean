# Handoff: `SortUniq` decided — and `sort_inv` with it

**Files added (both new, both `sorry`-free in their own source):**
`Lean4Lean/Theory/Typing/SortUniqDown.lean`, `Lean4Lean/Theory/Typing/UniqSort.lean`.
**File edited:** `Lean4Lean/Theory/Typing/SortUniq.lean` — **docstring only**, the `def
SortUniq` is byte-identical. No other file was touched.

**Sorry count unchanged: 21** (`lake env lean scripts/sorry-census.lean`, re-run at the end).
Nothing was deleted from the census; what changed is which of its entries are *independent*.

---

## Verdict, in three lines

1. **`VEnv.SortUniq` exactly as written is FALSE** — it has no hypothesis on `env`.
   Machine-checked witness: `VEnv.sortUniq_badEnv`. Missing-guard defect;
   `VEnv.badEnv_not_wf` shows the witness is not `VEnv.WF`.
2. **`SortUniq` implies `IsDefEqU.sort_inv`**, `trans` case included, with no normalisation
   argument — `VEnv.sort_inv_of_sortUniq`, `sorryAx`-free.
3. **`SortUniq` is a theorem relative to `IsDefEqU.forallE_inv_stratified` alone** —
   `VEnv.WF.sortUniq'`. And therefore so are `IsDefEqU.sort_inv` (`IsDefEqU.sort_inv'`) and
   `IsDefEq.uniq` (`IsDefEq.uniq'`).

So the answer to the brief's question — *one primitive or two?* — is **one, and it is neither
of the two that were named.** `sort_inv`'s `trans` and `SortUniq` are both consequences of
Π-injectivity in the stratified form.

    forallE_inv_stratified  ⟹  uniqAux  ⟹  SortUniq  ⟹  sort_inv
                                       ⟹  uniq

---

## The criterion answer, written down before any attempt

`docs/handoff-stratified.md` §5: *does the statement's induction ever have to look at a
conversion derivation at all?*

> **Yes, unavoidably.** In this tree `HasType env U Γ e A` is *defined* as
> `IsDefEq env U Γ e e A`, so both of `SortUniq`'s premises **are** conversion derivations.
> Any induction must peel `HasTypeStrong`'s `defeq` chain, whose links are stated at
> different sort levels. The conclusion `u ≈ v` is **asserted of the endpoints**, not
> propagated along. **Prediction: `trans` blocks it; obstruction identical to `sort_inv`'s.**

Companion test: at `bvar` and `const` the two derivations give literally the same type, so
the IH carries nothing; at `app` the position that decides the case is the function `f`,
whose type is a Π, so the IH — guarded by "the type is sort-shaped" — is unavailable. Same
shape as `appCase_ih_vacuous`/`SortForallEDisjoint`.

**Outcome vs prediction.** The prediction was correct about *that* induction, and correct
that `SortUniq` and `sort_inv` share one obstruction. It was **wrong about the verdict**,
because the statement is not proved by its own induction at all: it is carried as a conjunct
inside a *different* statement's induction (`uniq`'s), where the recursive position that
supplies it is `uniq`'s own, not `SortUniq`'s.

> **Criterion note, please propagate.** §5's criterion prices *the induction on the
> statement's own derivation*. Two things it cannot see, both of which decided this session:
>
> * **Non-inductive reductions.** `SortUniq ⟹ sort_inv` is four lines and never opens a
>   conversion derivation. A statement that fails the criterion can still be a cheap
>   *source*.
> * **Passenger conjuncts.** A statement that has no workable induction of its own can ride
>   along inside another statement's induction, if that induction already reaches the
>   positions it needs. Before declaring a statement blocked, check whether some *already
>   proved* induction in the tree calls it — and whether the call sites are its own induction
>   hypothesis. Here all nine were.
>
> Concrete test to add to the trap list: **grep the open lemma's call sites inside proved
> theorems. If every call is on an IH output, the lemma is a passenger, not a primitive.**

---

## 1. The main result: `uniq`'s invariant carries universe uniqueness

`IsDefEq.uniq` (`Theory/Typing/UniqueTyping.lean:13`) proves, by well-founded induction on a
stratification index `n`:

    ∃ u, Γ ⊢ A ≡ B : .sort u ∧ ∃ v, u ≈ v ∧ HTS Γ A (.sort u) true (n-1)
                                          ∧ HTS Γ B (.sort v) true (n-1)

Its proof calls `IsDefEqU.sort_inv` **nine** times (`UniqueTyping.lean` lines 50, 54, 65, 69,
71, 80, 83, 98, 108 — do not confuse these with the unrelated level-`WF` extraction
`HasType.sort_inv`, which also appears there). **Every one of the nine is applied to an
output of the proof's own induction hypothesis, at a point where both types are syntactic sorts.** So the fact being
imported is derivable inside the induction rather than from outside it.

`Theory/Typing/UniqSort.lean` adds the conjunct

    ∀ s₁ s₂, A = .sort s₁ → B = .sort s₂ → s₁ ≈ s₂

to the invariant (`VEnv.UniqAux`) and proves the whole thing (`VEnv.uniqAux`). That conjunct
**is** `SortUniq`, read off at `A = .sort u`, `B = .sort v`.

**The conjunct is free, and that is the whole trick.** It is not proved case by case. It is
derived once, uniformly, from components the invariant already carries
(`VEnv.sortType_level`): given `HTS Γ A (.sort u) true (n-1)`, `HTS Γ B (.sort v) true (n-1)`
and `u ≈ v`, with `A = .sort s₁` and `B = .sort s₂`, apply the invariant **at index `n-1`** to
the term `.sort s₁` at its two types `.sort u` and `.sort (.succ s₁)` (the latter by `sort'`,
at index `0`) to get `u ≈ .succ s₁`; symmetrically `v ≈ .succ s₂`; compose with `u ≈ v`. The
recursion is the well-founded one the original proof already runs, and it strictly decreases.
At `n = 0` the only derivation of anything is `sort'`, so the type is pinned outright
(`VEnv.HasTypeStratified.sort_zero_inv`) — that is the base case, and it is three tokens long.

**Why this is available here and not in the reference.** `HasTypeStratified`'s `defeq`
premise carries the type as `.sort u` *syntactically*, so "both types are sorts" is a pattern
on the invariant rather than a fact about a conversion. This is the same type-index artifact
that `Injectivity.lean` blames for putting the `UniqueTyping` family in 23 backbone
declarations. It cuts both ways.

**Provenance.** `VEnv.uniqQ` is `IsDefEq.uniq`'s proof transcribed, with exactly two kinds of
change: the nine `sort_inv` calls become `hc _ _ rfl rfl` from the strengthened IH, and the
binder order is adjusted so the same `induction … generalizing` shape elaborates standalone.
`UniqueTyping.lean` was **not** edited.

### Measured (cut instrument, not a Lean theorem)

Forward transitive closure over declaration *values* (`ConstantInfo.value? (allowOpaque :=
true)` — the `.thmInfo` trap `scripts/cone-measure.lean` documents), with named declarations
treated as leaves:

| seed | contains `IsDefEqU.sort_inv`? | with `forallE_inv_stratified` cut: declarations directly using `sorryAx` |
|---|---|---|
| `VEnv.uniqAux` | **no** | none |
| `VEnv.WF.sortUniq'` | **no** | none |
| `VEnv.IsDefEqU.sort_inv'` | **no** | none |
| `VEnv.IsDefEq.uniq'` | **no** | none |

For contrast, the same measurement on the existing declarations: `IsDefEq.uniq` and
`SortUniqFacts.WF.sortUniq` each need **both** `sort_inv` and `forallE_inv_stratified`;
cutting both leaves neither with any `sorryAx` user.

---

## 2. `SortUniq ⟹ sort_inv` (`SortUniqDown.lean`)

`VEnv.sort_inv_of_sortUniq`, axioms `[propext, Quot.sound]`:

```
theorem sort_inv_of_sortUniq (huniq : env.SortUniq U) (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v
```

`IsDefEqU.sort_inv`'s statement with `Ordered env` in place of `VEnv.WF env` — a weaker
hypothesis, so strictly stronger than what `Injectivity.lean` asks for.

**Why.** `IsDefEqU Γ (.sort u) (.sort v)` unfolds to `∃ A, IsDefEq Γ (.sort u) (.sort v) A`:
*one* type `A` inhabited by *both* endpoints, because conversion here is type-indexed. That
is `SortUniq`'s premise shape. `HasTypeStrong.sort_type` (itself `huniq`-dependent) converts
`A` to `.sort w`; then `.sort v` inhabits both `.sort w` and `.sort (.succ v)`, so
`w ≈ .succ v`; symmetrically `w ≈ .succ u'` with `u ≈ u'`. **The conversion derivation is
never inspected** — no `trans`, no `proofIrrel`, no reduction. Carneiro's three-place
conversion (`~/lean-type-theory/axioms.tex:30–41`) carries no type, so this implication does
not exist in the reference.

**Collapse test.** Not a tautology: `SortUniq` is instantiated at `e := .sort v` with levels
one `succ` above the target's, and the reduction runs through `sort_type`'s induction on
`HasTypeStrong`.

### The sandwich, as `sorryAx`-free hypothesis-level implications

`SortUniqDown.lean` packages the two inputs of `SortUniqFacts.WF.sortUniq` as `Prop`s —
`VEnv.UniqTy` (the statement of `IsDefEq.uniq`) and `VEnv.SortInv` (the statement of
`IsDefEqU.sort_inv`) — and proves, `sorryAx`-free:

* `VEnv.sortUniq_of : UniqTy → SortInv → SortUniq`
* `VEnv.sortInv_of_sortUniq : SortUniq → Ordered → SortInv`

`SortUniqFacts`' own version cannot be used for this, because both its inputs are open and it
is `sorryAx`-tainted; it establishes no strength relation.

**Strictness — analysis, not machine-checked, same status as `SortUniq.lean`'s cumulativity
check.** Adding cumulativity to the rule set falsifies `SortUniq` (that check) but adds only
*typing* derivations, relating no new pair of terms by conversion, so `SortInv` survives it.
Hence `SortInv` does not imply `SortUniq` without `UniqTy`.

---

## 3. The statement as written is FALSE (`SortUniqDown.lean`)

`VEnv.SortUniq` carries **no hypothesis on `env`**. One rule refutes it:

* `VEnv.badDefEq` — the rule `.sort .zero ≡ .sort .zero : .sort 2`
* `VEnv.badEnv` — the environment carrying exactly that rule
* `VEnv.badEnv_sort_two` — `[] ⊢ .sort .zero : .sort 2`, by `IsDefEq.extra`
* `VEnv.sortUniq_badEnv : ¬ badEnv.SortUniq U` — against `[] ⊢ .sort .zero : .sort 1` from
  `HasType.sort`, and `1 ≉ 2`

**Every guard in the statement holds at this witness.** `OnCtx [] _` is trivial; both levels
are closed, so `WF` at any `U`. The guards analysed in `SortUniq.lean`'s "Two guards" section
— the ones `LevelAssignUnsat.lean` motivated — are not the ones that were missing.

**A missing-guard defect, not a refutation of the intended fact.**
`VEnv.badEnv_not_wf : ¬ badEnv.WF` is machine-checked, by the already-proved
`VEnv.WF.instL_lhs_ne_sort` ("no rule rewrites a sort", `DeclRules.lean:234`).

**The definition was deliberately left unguarded.** Adding `env.WF` to it changes the
hypothesis shape of `Typing/CycleConv.lean`'s `propLoop_no_direct_collapse`, a file this
stream does not own. Recorded in `SortUniq.lean`'s docstring instead. The edit, if wanted,
is `def SortUniq` plus one hypothesis at `CycleConv.lean:225`.

**Auto-bound implicits: checked, clean.** `set_option pp.all true in #print
Lean4Lean.VEnv.SortUniq` shows exactly `{Γ e u v}`, all four used, nothing captured. Same
check run on `IsDefEqU.forallE_inv_stratified` — now the single load-bearing hypothesis —
shows `{env Γ U A B A' B' V n V' n'}`, all used, nothing stray.

---

## 4. What `SortUniq` buys, corrected

| `Injectivity.lean` statement | granted `SortUniq` |
|---|---|
| `IsDefEqU.sort_inv` | **closed entirely** — `sort_inv_of_sortUniq` |
| `IsDefEqU.forallE_inv` | `proofIrrel` closed (`NotProof.forallE_not_proof`); **`trans` open** |
| `IsDefEqU.sort_forallE_inv` | `proofIrrel` closed; `trans` open |
| `IsDefEqU.const_forallE_inv` | `proofIrrel` closed; `trans` open |
| `IsDefEqU.const_sort_inv` | `proofIrrel` closed; `trans` open |
| `IsDefEqU.forallE_inv_stratified` | level alignment supplied; `trans` open |
| `IsDefEqU.const_app_inv` | untouched (opaque `sorry`) |

**The residual is a different `trans` from the one this stream was told about.** What remains
is the **Π/const-flavoured** normalisation statement — *a term convertible with a Π (resp. a
rule-free constant application) reduces to one*. The sort-flavoured `trans` is gone.

**Why the type-index trick does not extend to `sort_forallE_inv`.** A sort and a Π can share
a type: `.sort (.succ u)` versus `.sort (.imax uA uB)`, and `.succ u ≈ .imax uA uB` is
satisfiable. So the shared type yields no contradiction. Same for `const_sort_inv`. The type
index only decides statements whose *type* determines the datum being compared, and a sort's
level is the one such datum.

---

## 5. Attempts that failed, and their exact failing steps

### Attempt A — induct on `HasTypeStrong Γ e (.sort u) b`, second typing as a side hypothesis

**Fails at the first case, `bvar`.** Using the second typing means inverting it, and
`HasType.bvar_inv` (`Strong.lean:932`) returns only `∃ A, Lookup Γ i A` — it drops the
conversion between the ascribed type and the looked-up one. Recovering it means composing
`HasTypeStrong`'s `defeq` chain, whose links are `IsDefEqStrong Γ A B (.sort uᵢ)` with a
**different level at each link**; `IsDefEqStrong.trans` demands one shared type index, so
composing two links needs `.sort u₁ ≡ .sort u₂ ⟹ u₁ ≈ u₂` — which is `sort_inv`, which by §2
is `SortUniq` again. Self-reference; the height measure gives `≤`, not `<`.

*This is the attempt the criterion predicted, and it is genuinely dead. §1 is not a repair of
it — it abandons it and rides `uniq`'s induction instead.*

### Attempt B, first form — "the `defeq` case blocks the strengthened invariant"

Recorded because it was **wrong**, and the error is instructive. Reading the `defeq` case
(`UniqueTyping.lean:102–112`) it looks as though the strengthened conjunct cannot propagate:
the IH speaks about `A'`, which need not be a sort, and transferring "is a sort at level `s`"
across `A' ≡ .sort s` is `sort_inv` again. **That reading is wrong** because the conjunct is
not propagated case by case at all — it is derived from the invariant's *components*, which
are present in every case uniformly. Generalising the discharge to the whole induction, rather
than case-analysing it, is what closed the statement.

### Not attempted, and why

Refuting the `VEnv.WF`-guarded form: it would need a `VEnv.WF` environment with one term at
two inequivalent sorts, hence a conversion between distinct sorts, hence a refutation of
`sort_inv` — the *weaker* statement. §1 now proves the guarded form outright (relative to
`forallE_inv_stratified`), so this line is closed for good.

---

## 6. Non-vacuity

Fired at `CycleConv.propLoopEnv` — a **proved** `VEnv.WF` environment (`propLoopEnv_wf`)
whose head reduction has a two-cycle, so `propLoop_headStep_not_wf` machine-checks that **no
normalisation argument terminates there**:

* `VEnv.propLoop_sortUniq : propLoopEnv.SortUniq 0` — an actual instance of the hypothesis,
  the first in the tree (`UniqSort.lean`).
* `VEnv.propLoop_no_direct_collapse'` — `CycleConv.lean`'s `propLoop_no_direct_collapse` with
  its `SortUniq` hypothesis discharged.
* `VEnv.propLoop_zero_not_defeq_one'` — `Prop` and `Type` stay apart there, unconditionally.
* `VEnv.propLoop_sort_inv`, `VEnv.propLoop_sort_defeq_refl`,
  `VEnv.propLoop_zero_not_defeq_one` (`SortUniqDown.lean`) — the conditional forms, showing
  the constrained relation is inhabited (`IsDefEqU 0 [] (.sort .zero) (.sort .zero)`) and not
  total.

That `sort_inv_of_sortUniq` fires in an environment where normalisation provably fails is the
point: it is not a normalisation argument in disguise.

The refutation side is fired at its own witness by construction (`badEnv`), and
`badEnv_not_wf` separates it from the intended domain.

---

## 7. Corrections to the brief this stream was given

1. *"They reduce to exactly two primitives: `sort_inv`'s `trans` and `SortUniq`."*
   **Both wrong.** They are not two (§2: `SortUniq ⟹ sort_inv`), and neither is a primitive
   (§1: both follow from `forallE_inv_stratified`).
2. *"`SortUniq` is a genuine keystone: closing it removes four of the seven holes' hard case
   at a stroke."* True, and it removes a fifth hole entirely — but it is not something to
   *close*, it is something that falls out.
3. *"Check `SortUniq`'s own statement for the auto-bound-implicit defect."* Checked: clean.
   The statement does have a defect, a different one — a missing environment guard (§3).
4. *"Confluence will not help you… `IsDefEq.church_rosser` depends on `forallE_inv`,
   `sort_inv`, `uniq`, `weakN_iff` and `NormalEq.descend`."* Still true as a measurement, but
   the `sort_inv` and `uniq` entries are now discharged by `UniqSort.lean` relative to
   `forallE_inv_stratified`, so that dependency list is shorter than it reads.
5. `scripts/sorry-census.lean`'s per-module **name lists are truncated** — it prints 4 names
   for `Injectivity.lean`'s 7. The seven are `sort_inv`, `forallE_inv_stratified`,
   `forallE_inv`, `sort_forallE_inv`, `const_app_inv`, `const_forallE_inv`, `const_sort_inv`.
   The *count* is right; do not read the name list as complete.

---

## 8. Reference check

`~/lean-type-theory/unique.tex:266` gets universe uniqueness from unique typing *at the
previous stratification index*. §1 is the same shape — universe uniqueness from unique typing
one index down — but it does **not** need Carneiro's stratified Church–Rosser to get there,
because this tree's `HasTypeStratified` already supplies the index and its `defeq` premise
already carries the type syntactically. So the reference's ordering is reproduced without the
κ-reduction development, in this one place. *(Analysis; the Lean content is §1's theorems.)*

---

## 9. What the next stream should do

* **The single live target in this corner is `IsDefEqU.forallE_inv_stratified`.** `sort_inv`,
  `SortUniq` and `uniq` are all downstream of it and of nothing else that is open.
* **A cheap census win is available and needs an owner for `Injectivity.lean`.**
  `IsDefEqU.sort_inv` has exactly **two** direct users in the whole tree — `IsDefEq.uniq` and
  one declaration in `ChurchRosser.lean` — and `UniqSort.IsDefEq.uniq'` replaces the first.
  Deleting `sort_inv` from `Injectivity.lean` and re-exporting `UniqSort.IsDefEqU.sort_inv'`
  in its place takes the census from **21 to 20**. It is a reordering, not a proof: this
  stream does not own `Injectivity.lean`, `UniqueTyping.lean` or `ChurchRosser.lean`, so it
  stopped here. *The exact edit: remove `IsDefEqU.sort_inv` and its two `sorry`s from
  `Injectivity.lean`; move `UniqSort.lean` below `Injectivity.lean` in the import order (it
  already is); point `UniqueTyping.lean:50,54,…` at `uniqAux`'s conjunct (or simply delete
  `IsDefEq.uniq` in favour of `IsDefEq.uniq'`); point `ChurchRosser.lean`'s one use at
  `IsDefEqU.sort_inv'`.*
* **The next reduction to try, and it is the same trick again.**
  `forallE_inv_stratified`'s docstring says its obstruction is *level alignment* — the
  conversion's level versus the level `HasTypeStratified.forallE_inv'` (`Strong.lean:1055`)
  hands back — and that alignment is `SortUniq`. Inside `uniqAux`'s `app` case, `SortUniq` is
  available *at a smaller index*. So the same passenger-conjunct move may replace
  `forallE_inv_stratified` in `uniqAux` by the **unstratified** `IsDefEqU.forallE_inv` plus a
  re-stratification through `forallE_inv'`. That would leave the whole corner resting on one
  statement whose only residual is "a term convertible with a Π reduces to a Π". **Not
  attempted; the index bookkeeping in the `app` case is where it will succeed or fail.**
* Do **not** spend a session proving `SortUniq` directly. It has no workable induction of its
  own (§5, Attempt A) and it does not need one.
