# Handoff: `Theory/Typing/Injectivity.lean` and its family

Session result, written for whoever picks this up next. Claims are marked
**[machine]** (a `sorry`-free Lean declaration in this tree, or a `lake build` /
`#print axioms` / cone-script run on this commit) or **[analysis]** (read off source or
argued, not machine-checked). The distinction is load-bearing: this corner has produced
wrong verdicts in four sessions, every one of them from analysis, and every correction from
a machine run.

Everything below was verified against a `lake build` of the whole package. One file fails,
`Lean4Lean/Verify/StructureBridge.lean` — it is **untracked, another stream's in-progress
work**, and nothing in this stream touches it or is touched by it. `git status` shows this
stream's only modification is `Theory/Typing/Injectivity.lean`. **[machine]**

---

## 0. Headline

1. **`const_app_inv` is no longer opaque.** It was `:= sorry` with an *empty* dependency
   cone. It is now the same 13-case induction on `IsDefEqStrong` as its four siblings, and
   **`trans` is its only residual** — byte for byte the residual of `forallE_inv`,
   `sort_forallE_inv`, `const_forallE_inv` and `const_sort_inv`. The statement is unchanged:
   `git diff` on the file removes exactly two lines, a docstring closer and `:= sorry`.
   **[machine]**
2. **The blocker a previous stream recorded was real, and it is dissolved by weakening the
   invariant.** That stream wrote: *"its `proofIrrel` case is not refutable without the
   `IsType` side condition, and `IsType` does not propagate into the induction (at `appDF`
   the sub-spine has a Π type). Settle the invariant before writing anything."* Both halves
   are correct. The invariant is **`¬ IsProof`**: implied by `IsType` (so no statement is
   weakened), sufficient for `proofIrrel` (so the case still closes), and — unlike `IsType`
   — **closed downward along a spine**. **[machine]**
3. **The census did not move: 19 → 19.** No hole closed. What closed is one statement's
   *independence*: `const_app_inv` was a second mathematical obligation and is now the same
   one as the rest. **[machine]**
4. **The K-rule has not landed in the form this corner needs.** `Theory/Typing/KRule.lean`
   exists (another stream) and proves `KStep.defeq` and non-vacuity, but a grep for `KStep`
   over the whole package returns **zero occurrences outside that file**: `ParRed`,
   `CParRed` and `NormalEq.parRed` are unextended. So the re-test the brief asked for is not
   yet possible. Measured, not assumed. **[machine]**

Nothing was refuted this session.

---

## 1. Census, before and after **[machine]**

`lake env lean scripts/sorry-census.lean`, run at the start and at the end. **Identical**:

| module | count |
|---|---|
| `Theory.Inductive.Decl` | 1 |
| `Theory.Typing.ChurchRosser` | 1 |
| **`Theory.Typing.Injectivity`** | **6** |
| `Theory.Typing.UniqueTyping` | 1 |
| `Verify.Environment` | 1 |
| `Verify.Environment.Boundaries` | 1 |
| `Verify.Soundness` | 2 |
| `Verify.TypeChecker.InferType` | 1 |
| `Verify.TypeChecker.IsDefEq` | 2 |
| `Verify.TypeChecker.WHNF` | 1 |
| `Verify.Typing.Lemmas` | 2 |
| **TOTAL** | **19** |

`Injectivity.lean`'s six, by content — **the change is in the last row**:

| declaration | residual before | residual after |
|---|---|---|
| `IsDefEqU.forallE_inv_stratified` | opaque `:= sorry` | opaque `:= sorry` — §5 |
| `IsDefEqU.forallE_inv` | `trans` only | `trans` only |
| `IsDefEqU.sort_forallE_inv` | `trans` only | `trans` only |
| `IsDefEqU.const_forallE_inv` | `trans` only | `trans` only |
| `IsDefEqU.const_sort_inv` | `trans` only | `trans` only |
| **`IsDefEqU.const_app_inv`** | **opaque `:= sorry`** | **`trans` only** |

Every `trans` says the same thing: *a term convertible with a Π (resp. with a rule-free
constant application, resp. with a sort) reduces to one*. That is a normalisation statement.
After this session it is the **only** non-opaque residual in the file, and
`forallE_inv_stratified` is the only opaque one.

---

## 2. `const_app_inv`: what was actually wrong, and what fixed it

### 2.1 The diagnosis that was already in the tree, and is correct **[analysis, confirmed]**

`ConstInvWitness.lean`'s `w2` machine-checks that `const_app_inv` **without** its second side
condition is inconsistent: `mkP : Type 0 → P` is an axiom heading no rule, so `RuleFreeHead`
holds of it, and yet `IsDefEq.proofIrrel` identifies `mkP A` with `mkP B` for any `A`, `B`.
The condition has to say that the application is a *type*, not a *proof*.

The previous stream then found that the condition cannot be threaded: an induction on
`IsDefEqStrong` reaches `appDF`, where the invariant must be re-established at the function
side `f` of `.app f a` — and `f`'s type is `.forallE A B`, not a sort. `IsType` is simply
false of the sub-spine. That is why the theorem was left opaque rather than half-written.

### 2.2 The fix: weaken the invariant until it propagates **[machine]**

`IsType` was the wrong carrier because it is *stronger than the `proofIrrel` case needs* and
*not closed downward*. The weakest thing `proofIrrel` needs is the negation of

```
VEnv.IsProof env U Γ e  :=  ∃ p, env.HasType U Γ p (.sort .zero) ∧ env.HasType U Γ e p
```

and three facts about it, all proved in `Injectivity.lean`'s `section UniqAux`:

* `IsType.not_isProof` — **a type is not a proof.** Same argument and same input as
  `VEnv.sort_not_proof` (`SortUniq.lean`) and `VEnv.forallE_not_proof` (`NotProof.lean`):
  universe uniqueness, which `WF.sortUniq'` supplies in-file, so the public statement gains
  no hypothesis. Those two lemmas are about a *particular shape* being a type; this is about
  being a type at all.
* `IsProof.app'` — **proof-ness propagates up an application spine.** If `f` is a proof and
  `Γ ⊢ f : .forallE A B`, then `.forallE A B` is a `Prop`, i.e. `imax u v ≈ 0`; `imax` is
  zero exactly when its *second* argument is (`VLevel.imax_eq_zero`); so the codomain is a
  `Prop` and `.app f a` inhabits it. Contrapositively, `¬IsProof (.app f a) ⟹ ¬IsProof f`,
  which is the direction the `appDF` case travels.
* `IsProof.defeqU` — proof-ness transports along a conversion, for the `symm` case.

So the invariant is `¬ env.IsProof U Γ e₁`, discharged at the root by
`IsType.not_isProof henv hΓ hty` from the theorem's own unchanged hypothesis.

### 2.3 The thirteen cases **[machine]**

| case | how it closes |
|---|---|
| `constDF` | the level list is the constructor's own premise; both spines are empty |
| `appDF` | peel one argument off each spine (`VExpr.mkApp_app_inv`), recurse on the function, append the argument conversion |
| `extra` | `RuleFreeHead`, via `headConst?_instL` / `headConst?_mkApp` — same as `const_forallE_inv` |
| `proofIrrel` | `¬IsProof` |
| `symm`, `defeqDF` | bookkeeping |
| `bvar`, `sortDF`, `lamDF`, `forallEDF`, `beta`, `eta` | vacuous on `VExpr.spineHead` of the left endpoint |
| **`trans`** | **OPEN** — the middle term is arbitrary |

New supporting lemmas, all in `Injectivity.lean`: `VExpr.mkApp_app_inv` (a spine that is an
application has that application's argument as its last entry), `VExpr.mkApp_eq_of_not_app`,
`List.Forall₂.symm'`, `List.Forall₂.append'`.

### 2.4 Unique typing at this height **[machine]**

`IsProof.app'` and `IsType.not_isProof` need unique typing, and `IsDefEq.uniq` lives in
`UniqueTyping.lean`, which **imports** `Injectivity.lean`. They do not import it: `uniqAux`
(already in this file, from the previous session) *is* `IsDefEq.uniq`'s own invariant and
`piInvStrat_axiom` discharges its hypothesis, so `WF.uniq'` re-derives the same conclusion
here. `HasType.defeqU_l'` is the one retyping lemma the argument uses, primed so that
`UniqueTyping.lean`'s unprimed original still elaborates. **Nothing new is assumed**:
`WF.uniq'` has exactly `IsDefEq.uniq`'s cone.

### 2.5 Non-vacuity **[machine]**

`¬IsProof` is a hypothesis of the induction, so if nothing satisfied `IsProof` the
`proofIrrel` case would be closed for the uninteresting reason. Two witnesses, both living
entirely in the context and therefore holding in **every** environment at **every** universe
count, with no constant and no `VEnv.WF`:

* `IsProof_fires` — in `[h : P, P : Prop]`, `h` is a proof. Axioms `[propext]`; **no
  `sorryAx`**.
* `IsProof.forallE_fires` — **a proof can be a function.** `.bvar 0` inhabits
  `Π (x : Prop), P`, which is itself a `Prop`. Axioms `[propext, Quot.sound]`; **no
  `sorryAx`**. This is the counterexample that makes §2.1's blocker true: the function side
  of an application really can be a proof, so `IsType` really cannot be carried.
* `IsProof.app'_fires` — the lemma applied at that witness, so what is checked is that its
  five hypotheses are jointly satisfiable. Tainted, but only through `WF.uniq'`.

### 2.6 An honest regression **[machine]**

`const_app_inv` now depends on `IsDefEqU.forallE_inv_stratified`, through `WF.uniq'` and
`WF.sortUniq'`. Before, its cone was empty — because it was an opaque `sorry`. This is the
same trade the previous session recorded at its §4.1, and it is worth the same: an empty
cone on an opaque statement is not independence, it is absence.

Forward cone over declaration *values* (theorem bodies included), reporting which of the
seven open statements each declaration reaches. Measured on this commit. **[machine]**

```
  forallE_inv_stratified  -> []
  weakN_iff               -> []
  uniqAux                 -> []                          (sorry-free)
  forallE_inv             -> [forallE_inv_stratified]
  sort_forallE_inv        -> [forallE_inv_stratified]
  const_forallE_inv       -> [forallE_inv_stratified]
  const_sort_inv          -> [forallE_inv_stratified]
  const_app_inv           -> [forallE_inv_stratified]     <- new edge, §2.6
  sort_inv                -> [forallE_inv_stratified]
  WF.sortUniq'            -> [forallE_inv_stratified]
  WF.uniq'                -> [forallE_inv_stratified]
  IsType.not_isProof      -> [forallE_inv_stratified]
  IsProof.app'            -> [forallE_inv_stratified]
  IsDefEq.uniq            -> [forallE_inv_stratified]
```

**Read the shape**: every statement of this family now bottoms out in exactly one open
thing, and it is `forallE_inv_stratified`. There is no second obligation left in the file.

---

## 3. Method note this session earns

The brief's defect-class list — auto-bound implicits; under-constrained scope; the general
"a statement carrying less information than its conclusion needs" — is about statements that
are **too weak**. This session's blocker was the mirror image: an invariant that was **too
strong to propagate**.

> When an induction cannot re-establish its invariant at a sub-derivation, the move is not
> always to strengthen the invariant. Ask what the *hard case* actually needs — here,
> `proofIrrel` needs only "not a proof", not "is a type" — and then ask whether that weaker
> consequence is closed under the induction's structural step. Weaken until it propagates;
> the public statement keeps the strong hypothesis and discharges the weak one at the root.

The audit that finds this is the same information-flow audit, run on the *invariant* rather
than the statement: `IsType` is not derivable from the `appDF` case's components, `¬IsProof`
is (from `¬IsProof` of the conclusion plus the case's own typing premises).

---

## 4. Prior sessions' results, still standing **[machine]**

Unchanged and not re-derived here; kept because the cross-references are load-bearing.

* **`sort_inv` is proved.** `IsDefEqU U Γ (.sort u) (.sort v)` unfolds to one type inhabited
  by both endpoints, so `SortUniq` applies to the endpoints directly
  (`sort_inv_of_sortUniq`) and the conversion derivation is never opened. No `trans`.
* **`SortUniq` is a theorem** (`WF.sortUniq'`), relative to `forallE_inv_stratified` alone,
  by carrying universe uniqueness as a conjunct in `IsDefEq.uniq`'s own invariant
  (`uniqAux`). This is what closes the four `proofIrrel` holes with **no statement gaining a
  hypothesis** — and now the fifth, `const_app_inv`'s, through `IsType.not_isProof`.
* **The corner is a CIRCLE.** `sortUniq_of_piInvStrat : PiInvStrat → SortUniq` and
  `piInvStrat_of : SortUniq → PiInv → PiInvStrat`, both `sorry`-free. So relative to plain
  Π-injectivity, `forallE_inv_stratified` and `SortUniq` are **equivalent**.
  `piInv_axiom` / `piInvStrat_axiom` are the anti-strawman checks that the packaged `Prop`s
  are those theorems' types verbatim.
* **Non-vacuity of the `SortUniq` route**: `propLoop_sortUniq` fires at a proved-`VEnv.WF`
  environment whose head reduction provably has a two-cycle, so the route is not a
  normalisation argument in disguise.
* **`NormalEq.descend` is machine-checked false** (`docs/handoff-descend.md`). Do not route
  through `ChurchRosser.lean`. Not touched this session.

---

## 5. What is still open, and the exact failing step

### 5.1 `forallE_inv_stratified` — the circle **[analysis, from the previous session]**

Inside `uniqQ`'s `app` case at index `n`, with `IH : ∀ m < n, UniqAux env U m`:
`forallE_inv'` re-stratifies fine and yields an index-bounded derivation, but plain
`forallE_inv` returns an **unstratified** `IsDefEq` whose level is tied to no index;
aligning the two is `SortUniq` at an index `IH` cannot reach. Three escapes are written out
in the previous version of this document and each returns to its own conclusion; do not
re-attempt them.

**Correction to that document's §8 item 3.** It proposed a lexicographic measure on
`(index, term size)` to make the unbounded side reachable, and flagged that the `app` case's
`IH` calls are on `B`, a subterm of the *type*. That flag is a distraction; the idea is dead
for a more basic reason. **The unbounded derivation is not a recursive call at all.** It is
an *input*, manufactured by `HasTypeStrong.stratify` from a derivation `forallE_inv` built
itself; its index is a function of that fresh derivation's height. No measure on an
induction can bound an index the induction never generates. **[analysis]**

### 5.2 The five `trans` cases

One normalisation statement, five instances. Nothing in the tree currently supplies it:
`ChurchRosser.lean`'s relation is refuted at `descend`; `HeadReduction.lean`'s has never had
a confluence argument run over it; `RawDefEq.lean`'s three-place judgment is unexplored.
`docs/handoff-descend.md` §5 and this document both say: **price `HeadReduction.lean`
before anyone spends a session on a `trans` case.**

**A dead end worth not re-walking.** For `const_app_inv` specifically, one might hope the
*level* half `Forall₂ (· ≈ ·) ls ls'` falls out of unique typing the way `sort_inv` did:
both spines have the same type, so `instAll (ci.type.instL ls) as ≡ instAll (ci.type.instL
ls') as'`. It sometimes does — for `Quot.{u} α r : Sort u` the type mentions the level, so
`sort_inv` gives `u ≈ u'` outright. It does not in general (`c : Nat → Nat` gives `c 0` and
`c 1` the same type), and the *argument* half never does. **[analysis]**

### 5.3 `IsDefEqU.weakN_iff` — not attempted, and re-confirmed blocked **[analysis]**

`Strengthen.lean` (this stream's file, unchanged) already establishes, `sorry`-free,
`weakN_iff ↔ TypingStrengthening ↔ PiDescend`. Reading `PiDescend`'s statement: given
`f.liftN n k : .forallE A B` in `Γ'` and `f` well-formed in `Γ`, produce a Π type for `f` in
`Γ`. `f` has *some* type `T` in `Γ`, so unique typing in `Γ'` gives `T.liftN n k ≡ .forallE
A B`, and what is then needed is that `T.liftN n k` **reduces** to a Π and that lifting
commutes with reduction. That is the same reduction relation as §5.2, reached from a
different direction. The brief's instruction — re-test only if the K-rule lands — stands,
and per §0.4 it has not.

---

## 6. The K-rule, measured **[machine]**

`Theory/Typing/KRule.lean` is new this session (another stream, untracked). It proves
`KStep.defeq` (admissibility: a `K⁺` step is already an `IsDefEqU`), `KStep.stuck_fires`
(non-vacuity against `HeadRedStuck.lean`'s measured hole) and `Params.no_kpattern`.

**What it does not yet do, and this is what this corner is waiting for:** `grep -rn KStep
Lean4Lean/` returns hits only inside `KRule.lean`. `ParRed`, `CParRed` and
`NormalEq.parRed` are unextended, and its own docstring says the `Params` instance supplying
the canonical-form side condition (ledger M3) is not built. So there is still **no candidate
reduction relation with a confluence argument**, and re-testing the circle or `weakN_iff`
against it would be testing against nothing. Re-run this grep before assuming otherwise.

---

## 7. Corrections this session makes to existing documents

| document | claim | correction |
|---|---|---|
| `docs/handoff-injectivity.md` (prev.) §6 | `const_app_inv`'s "`proofIrrel` case is not refutable without the `IsType` side condition, and `IsType` does not propagate into the induction… **Settle the invariant before writing anything.**" | The diagnosis is right and the instruction is now carried out. The invariant is `¬IsProof`, which `IsType` implies and which *is* closed downward. §2. |
| `docs/handoff-injectivity.md` (prev.) §1 table | `const_app_inv` | opaque `sorry` → **`trans` only**. §1. |
| `docs/handoff-injectivity.md` (prev.) §8 item 3 | a lexicographic measure "might make the unbounded side reachable… the first thing to check is that the `app` case's `IH` calls are on `B`" | Dead, for a more basic reason: the unbounded derivation is an *input*, not a recursive call. §5.1. |
| `docs/handoff-typechecker.md` §286, `docs/handoff-projections.md` §36 | `quotReduceRec.WF` / `TrProj.uniq` are "blocked on `const_app_inv`" | Still true — `const_app_inv` is reduced, not proved. What changed is that it is no longer a *separate* obligation: it is the family's shared `trans`. |
| `docs/design-inductive.md` ledger I13a | `const_app_inv` … status **research** | Its side-condition question is settled (`¬IsProof`, machine-checked). Its remaining status is the family's `trans`. Ledger row is another stream's to edit. |

---

## 8. What to pick up first

1. **`HeadReduction.lean`.** It is the only untried reduction relation, every open statement
   in this corner except `forallE_inv_stratified` is one `trans` away, and `weakN_iff` is
   one `PiDescend` away which is the same question. Nothing incremental remains in
   `Injectivity.lean`.
2. **Re-grep `KStep` before planning around the K-rule.** §6. If `ParRed` has gained a `K⁺`
   constructor and a confluence argument, the circle and `weakN_iff` both become re-testable
   in the same session.
3. **Do not** re-attempt §5.1's three escapes, §5.1's lexicographic measure, or §5.2's
   unique-typing shortcut for `const_app_inv`'s level half.
4. **Do not** route through `ChurchRosser`. `descend` is false.
