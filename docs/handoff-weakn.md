> **2026-08-29 — superseded in part; read `docs/handoff-descend.md` first.**
> Two claims below are now known wrong. (i) §4.1's "`Params` has no instance … the fatal
> blocker" was corrected by `docs/handoff-params.md`: `VEnv.paramsOfWF` / `paramsOfDelta`
> build one, and `Theory/Typing/DescendRefute.lean` uses `paramsOfDelta`.  (ii) §4.3's step 3
> ("discharge `NormalEq.descend`'s five `sorry`s") is not a matter of effort: **three of the
> five goals are FALSE**, machine-checked, so the Church–Rosser route needs a restatement
> rather than a completion.  Everything else below stands and was **not** re-measured.

# Handoff: strengthening — `IsDefEqU.weakN_iff`'s `sorry`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:174`. **Still open; the statement has not moved and nothing
was refuted.**

Marks: **[machine-checked]** = a Lean declaration in this tree, named; **[measured]** = a
machine run whose output is reproduced; **[read]** = read off source; **[analysis]** = neither.

This pass **corrected the previous version of this document twice**, both correction
[machine-checked] or [measured]. Read §0 before anything else.

---

## 0. The three things to know before touching this

0. **`TransStrengthening` is not a residual — it *is* the target.**  Instantiate its middle
   term `b` at `e2.liftN n k` and its second premise at the reflexivity the first premise
   already carries (`IsDefEq.hasType.2`), and you have `Strengthening`.
   **[machine-checked, sorry-free: `TransStrengthening.strengthening`, `Strengthening.iff_trans`]**
   Consequences, all mechanical:
   * the previous headline —
     `Strengthening ↔ SortDescend ∧ PiDescend ∧ TransStrengthening` (`Strengthening.iff_descend`)
     — is **a tautology read as a reduction**: the `←` direction never uses its first two
     hypotheses (**[machine-checked: `Strengthening.of_trans_only`]**);
   * `Strengthening.of_typing (HT) (Htr)` is provable from `Htr` alone.  Its real content is
     the *case analysis* — eleven of twelve conversion rules need nothing but
     `TypingStrengthening` — not a reduction of the target.  That case analysis is still
     worth having (§2.2); the theorem's statement oversold it.
   * so the target has **one** genuinely open piece at the conversion level, and it is the
     target.  §1's criterion said exactly this and it was right.
1. **What survives is about the target's *reflexive instance*, and this pass halved it.**
   `TypingStrengthening ↔ SortDescend ∧ PiDescend` (previous pass, sorry-free) becomes

       TypingStrengthening  ↔  PiDescend

   because `PiDescend` implies `SortDescend`: apply it to the *closed* identity function
   `fun (_ : Sort u) => _`, whose domain is a sort by construction and which is its own lift,
   at the argument `e`.  **[machine-checked: `PiDescend.sortDescend`,
   `TypingStrengthening.iff_piDescend`]**  Cost: `IsDefEqU.forallE_inv` — the collapse is not
   sorry-free, whereas `TypingStrengthening.iff_descend` was.  Pay it or don't; both
   statements are in the tree.
2. **The Church–Rosser route recommended as "step 2" is blocked twice over, and the second
   blocker is fatal.**  See §4.  Do not spend the 110 lines.

---

## 1. The criterion, applied — unchanged, and confirmed

> *Does the statement's induction ever have to look at a conversion derivation at all?  If it
> does, it is tractable exactly when its conclusion is propagated along the conversion rather
> than asserted of its endpoints.*

**Yes it must, and the conclusion is endpoint-asserted.**  `HasType e A` is *defined* as
`IsDefEq e e A` (`Theory/Typing/Basic.lean:60`), so the core judgment offers nothing else to
induct on. **[read]**  At `trans` the middle term is arbitrary and both induction hypotheses
are vacuous. **[machine-checked: `Strengthening.of_typing`, whose `trans` case is the
hypothesis `TransStrengthening`.]**  §0.0 now says what that means precisely: the `trans` case
is the whole statement.

The escape one level out is real and is where all the tractable content lives:
`Theory/Typing/Strong.lean`'s syntax-directed `HasTypeStrong`, whose only non-syntax-directed
rule keeps the same term.  It serves the *reflexive* instance only, which is why §0.1 is about
`TypingStrengthening` and not about `Strengthening`.

Row for §5's table of `docs/handoff-stratified.md` (revised):

| statement | induction sees a conversion? | conclusion | `trans` | outcome |
|---|---|---|---|---|
| `IsDefEqU.weakN_iff` (`Strengthening`) | yes, in the core judgment | endpoint-asserted | **is the statement** | needs a reduction relation |
| `TypingStrengthening` (its reflexive instance) | **no** — induction on `HasTypeStrong` | — | never arises | tractable; residual = `PiDescend`, **equivalent** |

*Why no propagated restatement exists* (**[analysis]**, unchanged, and now with the reason
sharpened).  The natural propagated predicate is
`Rel(a,b) := ∀ a₀, Γ' ⊢ a ≡ a₀↑ → ∃ b₀, Γ' ⊢ b ≡ b₀↑ ∧ Γ ⊢ a₀ ≡ b₀` (plus its mirror).  It
does make `trans` free — compose the two witnesses.  But reading the target off `Rel(e1↑,e2↑)`
needs *coherence* — "any two strengthenings of the same `Γ'`-term are `Γ`-convertible" — and
coherence at `e2↑` **is** the target.  Coherence propagates along conversion but has no base
case.  That is the precise sense in which this needs a deterministic reduction and not a
relation.

---

## 2. What is in the tree — `Theory/Typing/Strengthen.lean` (520 lines, no `sorry`)

Three definitions, so residuals can be named:

```lean
def Strengthening (env) (U) : Prop :=            -- the target
  ∀ {n k Γ Γ' e1 e2}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

def TypingStrengthening (env) (U) : Prop :=      -- its reflexive instance
  ∀ {n k Γ Γ' e A}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.HasType U Γ' (e.liftN n k) A → VExpr.WF env U Γ e

def TransStrengthening (env) (U) : Prop :=       -- NOT a residual: equals `Strengthening`
  ∀ {n k Γ Γ' e1 e2 b A}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.IsDefEq U Γ' (e1.liftN n k) b A → env.IsDefEq U Γ' b (e2.liftN n k) A →
    env.IsDefEqU U Γ e1 e2
```

| name | statement | status |
|---|---|---|
| `Ctx.LiftN.exists_instN` | a `LiftN 1 k` witness is an `InstN` witness for any substituted term | sorry-free |
| `IsDefEqU.strengthen_of_instN`, `IsDefEq.strengthen_of_instN` | **strengthening holds when the stripped entry is inhabited** | sorry-free |
| `VExpr.liftN_eq_*`, `VExpr.liftVar_eq_zero`, `Lookup.weakN_inv` | inversion of `liftN` against a head constructor | sorry-free |
| `Strengthening.typing`, `Strengthening.trans` | the target implies its two "residuals" | sorry-free |
| **`TransStrengthening.strengthening`** | **`TransStrengthening ⟹ Strengthening`** | **new**, sorry-free |
| **`Strengthening.iff_trans`** | **`Strengthening ↔ TransStrengthening`** | **new**, sorry-free |
| **`Strengthening.of_trans_only`** | §8's `←` with its first two hypotheses deleted | **new**, sorry-free |
| `TypingStrengthening.of` / `.sortDescend` / `.piDescend` / `.iff_descend` | `TypingStrengthening ↔ SortDescend ∧ PiDescend` | sorry-free |
| **`PiDescend.sortDescend`** | **`PiDescend ⟹ SortDescend`** | **new**, `sorryAx` via `forallE_inv` |
| **`TypingStrengthening.iff_piDescend`** | **`TypingStrengthening ↔ PiDescend`** | **new**, `sorryAx` via `forallE_inv` |
| `TypingStrengthening.typed` | the existential form implies the *typed* form | `sorryAx` via `forallE_inv` |
| `Strengthening.of_typing` | the eleven-of-twelve case analysis | `sorryAx` via `forallE_inv` |
| `Strengthening.iff_typed` | `Strengthening ↔ TypedStrengthening ∧ TypingStrengthening` | `sorryAx`; **still genuine**, see §6 |
| `Strengthening.iff_descend` | the old capstone | `sorryAx`; **tautological**, see §0.0 |

**Axiom cones and non-circularity, measured.**  For every new declaration a forward
reachability search over the declaration graph (`getUsedConstantsAsSet`, `allowOpaque := true`)
reports **NO PATH to `IsDefEqU.weakN_iff`**. **[measured]**  The `sorryAx` taint of
`PiDescend.sortDescend` and `TypingStrengthening.iff_piDescend` is through exactly
`IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified` and nothing else. **[measured]**
`TransStrengthening.strengthening` and `Strengthening.iff_trans` are `[propext]` only.

### 2.1 The inhabited case, and why no model argument reaches this

`(e.liftN 1 k).inst e₀ k = e`, so if the stripped hypothesis has *any* inhabitant downstairs,
`IsDefEqU.instN` turns the `Γ'`-conversion into a `Γ`-conversion.  **The difficulty is confined
to context entries uninhabited downstairs** — and over an uninhabited `Γ'` every soundness
statement is vacuous, so `Theory/SetModel/` cannot see the difference. **[read + machine-checked]**

### 2.2 The eleven-of-twelve case analysis (still useful, now correctly labelled)

`Strengthening.of_typing` closes every rule but `trans` from `TypingStrengthening` alone:
`bvar`, `sortDF`, `constDF`, `extra` (closed rules, `ClosedN.liftN_eq`), `symm`, `defeqDF`,
`appDF`/`lamDF`/`forallEDF` (via `Strong.lean`'s inversions and `IsDefEqU.of_l`), `beta` (plus
`uniqU` + `forallE_inv`), `eta`, `proofIrrel`.  This is a **map of the induction**, not a
reduction: `trans` is the statement.  Its value is that anyone who lands a reduction relation
has eleven rules already written.

### 2.3 The existential and typed forms are the same unknown

`TypingStrengthening` implies the typed form by applying itself to the ascription redex
`(fun _ : A => #0) e` (`TypingStrengthening.typed`). **[machine-checked]**  So there is no
weaker "untyped" version of the unknown to look for.

### 2.4 `TypingStrengthening` is exactly `PiDescend`

```lean
def SortDescend (env) (U) : Prop :=
  ∀ …, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.HasType U Γ' (e.liftN n k) (.sort u) → VExpr.WF env U Γ e → ∃ u₀, env.HasType U Γ e (.sort u₀)

def PiDescend (env) (U) : Prop :=
  ∀ …, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
    VExpr.WF env U Γ f → VExpr.WF env U Γ a →
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀
```

* `TypingStrengthening.iff_descend : TypingStrengthening ↔ SortDescend ∧ PiDescend`, sorry-free
  (previous pass).
* **`PiDescend.sortDescend : PiDescend → SortDescend`** (this pass).  Witness: the closed
  identity `idU := .lam (.sort u) (.bvar 0)`, which satisfies `idU.liftN n k = idU`
  syntactically and is typed `Sort u → Sort u` by construction.  `PiDescend` at `idU` and the
  argument `e` returns `Γ ⊢ idU : A₀ → B₀` and `Γ ⊢ e : A₀`; `uniqU` + `forallE_inv` identify
  `A₀` with `Sort u`.  **This is the only place a *sort* is recovered from a *Π*, and it is
  what costs Π-injectivity.**
* hence **`TypingStrengthening.iff_piDescend : TypingStrengthening ↔ PiDescend`**.

The converse direction `SortDescend → PiDescend` is **open and not attempted**; there is no
reason to expect it (a sort target says nothing about Π shape).

*Why `TypingStrengthening`'s induction works where `Strengthening`'s does not.*  It has a
syntax-directed judgment, `HasTypeStrong` (`Strong.lean:99`), reached by
`IsDefEq.strong … |>.hasType'.1`; its one non-syntax-directed rule, `defeq`, keeps the same
term.  So it never inspects a conversion and **passes** §5's criterion, like `PropUniq` and
`SortForallEDisjoint`.  Of its eight rules `bvar`, `sort'`, `const`, `base`, `defeq` are free,
`lam`/`forallE` need `SortDescend`, `app` needs `PiDescend`.

### 2.5 Where a shape induction on `PiDescend` goes  **[analysis, not machine-checked]**

Inducting on the shape of `f` downstairs (`Γ ⊢ f : T`, `Γ' ⊢ f↑ : Π A B`, so
`Γ' ⊢ T↑ ≡ Π A B` by `uniq`):

* `f = .lam C d` — `Γ ⊢ f : Π C D`, so `Γ' ⊢ A ≡ C↑` by `forallE_inv`, and with
  `Γ' ⊢ S↑ ≡ A` (`S` = `a`'s type downstairs) this leaves `Γ' ⊢ S↑ ≡ C↑` ⟹ `Γ ⊢ S ≡ C`:
  **strengthening at types**, both sides lifted;
* `f = .sort _` or `.forallE _ _` — `T` is a sort, so `Γ' ⊢ .sort _ ≡ Π A B` contradicts
  `IsDefEqU.sort_forallE_inv` (open, `Injectivity.lean:312`);
* `f = .bvar _`, `.const _ _`, `.app _ _` — need "`T↑` is Π-shaped upstairs ⟹ `T` is Π-shaped
  downstairs", with **no** term-shape information about `T`.

So `PiDescend` sits in the same family as `Injectivity.lean`'s open statements, and the honest
summary is that it wants *Π-shape descent for conversion*.  Nothing here reduces it to a
smaller statement; recording the case split so the next pass does not redo it.

---

## 3. Cone

**Unchanged — no `sorry` was removed, so there is no before/after to report.**  §3 of the
previous version's figures were not re-measured this pass and are reproduced as inherited
[measured] claims:

| cut | `IsDefEqU.sort_inv` transitive users (scope A, 11338 decls) |
|---|---|
| none | 129 |
| (E) | 66 |
| (E) + `piUniq` | 56 |
| (E) + `IsDefEq.weakN_iff'` | **31** |
| (E) + `piUniq` + `weakN_iff'` | 2 |

`IsDefEqU.weakN_iff`: 5 direct users, 58 transitive (scope A) / 93 (scope B) / **119** (scope C
= scope B + `import Lean4Lean.Theory`).

**The instrument's coverage caveat stands and matters**: `scripts/cone-measure.lean`'s scope B
is advertised as "all `Lean4Lean.*` modules" but is only what its own import list reaches, and
**nothing under `Verify/` imports `ChurchRosser.lean`** — it is reachable only through
`Lean4Lean/Theory.lean`.  Adding `import Lean4Lean.Theory` raises 12756 → 13532 declarations.

---

## 4. The Church–Rosser route: **closed, for a reason that is not the circularity**

`Theory/Typing/ChurchRosser.lean` really does prove what the route wants
(`IsDefEq.church_rosser`, `ParRed.weakN_inv`, `NormalEq.weakN_iff` / `.weakN_inv_DFC`).
It still cannot be used, and the previous version of this document mispriced why.

### 4.1 The fatal blocker: `Params` has no instance, and it is an assumption about the environment

Every declaration in `ChurchRosser.lean` from line 83 on lives under `variable [Params]`, and
`Params` carries `env` and `henv : env.WF` as **fields**.  So

```
@IsDefEq.church_rosser : ∀ {Γ} [inst : Params], OnCtx Γ (Params.env.IsType Params.univs) →
  ∀ {e₁ e₂ A}, Params.env.IsDefEq Params.univs Γ e₁ e₂ A → CRDefEq Γ e₁ e₂
```

**[measured, `#check`]** — it is a statement about `Params.env`, not about an arbitrary
`VEnv.WF` environment.  `IsDefEqU.weakN_iff` quantifies over all of them.

`synthInstance?` over the whole `Lean4Lean.Theory` import closure reports
**NO instance of `Lean4Lean.VEnv.Params`** **[measured]**, and a grep over the package finds
none. **[measured]**  The class's own `extra_pat` docstring says why: every `extra` rule of the
environment must be a `Pat`-registered simple pattern under leading lambdas, with the
uniqueness conditions `pat_uniq` / `pat_app_l_uniq` / `pat_app_uniq`.  `VEnv.WF`
(`Theory/Typing/Env.lean:86`) supplies δ-rules, the quotient rules and ι-rules but **no such
invariant**. **[read]**

**So even a fully de-circularised `ChurchRosser.lean` proves nothing about
`UniqueTyping.lean:174`.**  The prerequisite is *instantiating `Params` from `VEnv.WF`* — a
separate project, of the same shape as ledger item M2 (`RuleFreeHead` from `VEnv.Sig`).

### 4.2 The circularity is real and **twice as large as previously priced**

Forward reachability over the declaration graph **[measured]**:

```
IsDefEq.church_rosser → CRDefEq.trans → NormalEq.trans → NormalEq.weakN_iff
                      → NormalEq.weakN_inv_DFC → HasType.weakN_iff → … → IsDefEqU.weakN_iff
ParRed.weakN_inv      → IsDefEqU.weakN_iff
NormalEq.parRed       → ParRedExt.parRed_beta → HasType.weakN_iff → … → IsDefEqU.weakN_iff
```

A sweep for declarations whose transitive dependencies contain any of `IsDefEqU.weakN_iff`,
`IsDefEq.weakN_iff'`, `IsDefEq.weakN_iff`, `HasType.weakN_iff`, `VExpr.WF.weakN_iff`,
`OnCtx.weakN_inv` finds **four** in `ChurchRosser.lean`, not two **[measured]**:

| declaration | line | call sites | kind of use |
|---|---|---|---|
| `NormalEq.weakN_inv_DFC` | 327 | 335, 355, 358, 360, 370, 378, 379, 395, 397, 413, 415, 424, 427, 428, 429 (15) | same term — `TypingStrengthening` and `TypedStrengthening` |
| `ParRed.weakN_inv` | 765 | 809 (1) | `extra` case, strictly smaller term — absorbable |
| `hasType_app_bvar0` | 1151 | 1161 (1) | same term, on an η-expansion |
| `ParRedExt.parRed_beta` | 1167 | 1221, 1281, 1283 (3) | same term |

`NormalEq.weakN_inv_DFC` additionally uses `OnCtx.weakN_inv`, which is itself a consumer of
`IsDefEq.weakN_iff'`; that one is covered by `TypingStrengthening.typed` (§2.3).

Note also that `ChurchRosser.lean` is not sorry-free for independent reasons: five `sorry`s in
`NormalEq.descend` plus `IsDefEqU.forallE_inv_stratified`. **[read]**

### 4.3 Verdict

Three prerequisites, in this order, before the route delivers anything:
1. instantiate `Params` from `VEnv.WF` (nobody has; §4.1);
2. re-prove **four** declarations (~20 call sites) from `TypingStrengthening` / the typed form
   rather than from `IsDefEqU.weakN_iff`, and relocate `IsDefEq.uniq` (which has **NO PATH** to
   `weakN_iff` **[measured]**, so it *can* move) into a file below the `NormalEq` development;
3. discharge `NormalEq.descend`'s five `sorry`s and `forallE_inv_stratified`.

**Recommendation: do not start here.**  The 110-line estimate in the previous version of this
document covered step 2 for one of the four declarations only, and steps 1 and 3 were not
counted at all.

---

## 5. Routes attempted, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU`, statement as given | `trans`, and `trans` **is** the statement (§0.0). **[machine-checked]** |
| the "prove the typed form instead" lead | same `trans`; the two forms are inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| find a *propagated* restatement | the propagated relation makes `trans` free but needs a coherence clause whose base case is the target. §1. **[analysis]** |
| Church–Rosser | `Params` has no instance, and the circularity covers four declarations. §4. **[measured]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited `Γ'`. §2.1. **[read/argued]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of `weakN_iff`, not toward it. **[read]** |
| substitution (inhabited case) | **succeeds**, in the tree. **[machine-checked]** |
| induction on `HasTypeStrong` for the reflexive instance | **succeeds**; residual is `PiDescend` alone. §2.4. **[machine-checked]** |
| `PiDescend ⟹ SortDescend` | **succeeds**, at the cost of `forallE_inv`. §2.4. **[machine-checked]** |
| `SortDescend ⟹ PiDescend` | **not attempted**; no reason to expect it. |

---

## 6. What is *not* tautological

`Strengthening.iff_typed` (`Strengthening ↔ TypedStrengthening ∧ TypingStrengthening`) is
**not** a victim of §0.0's collapse: `TypedStrengthening` requires the *type* to be lifted, and
`IsDefEqU`'s existential type is not, so no trivial instantiation recovers `Strengthening` from
it.  Likewise `TypingStrengthening.iff_descend` / `.iff_piDescend` are genuine — they are about
the reflexive instance, where the `trans` collapse cannot happen because `HasType` is
reflexivity by definition and the induction is on `HasTypeStrong`.

The check that separates the two cases, and the one to run on any future "reduction": **can the
residual's own quantifiers be instantiated so that its premises degenerate into the target's?**
For `TransStrengthening` the answer was yes, in one line.

---

## 7. Non-vacuity — `Theory/Typing/StrengthenWitness.lean` (new, sorry-free)

Every statement named above is replayed at an instance over `CycleConv.propLoopEnv` — a
`VEnv.WF` environment (`propLoopEnv_wf`) with two constants and two δ-rules — with
`Γ = []`, `Γ' = [A]` where `A` is an actual *proposition of the environment*
(`propLoop_isProp`), so the instance does not exist over `VEnv.empty`, which has no constants:

`propLoopEnv_sortDescend_fires`, `propLoopEnv_piDescend_fires`,
`propLoopEnv_piDescend_sortDescend_fires` (§0.1's new theorem),
`propLoopEnv_typingStrengthening_fires`, `propLoopEnv_trans_strengthening_fires` (§0.0's new
theorem), `propLoopEnv_strengthening_fires`.

The last two fire at the environment's δ-loop `A ≡ B` — **not** a reflexivity, and a conversion
that exists only because of the rules.  The stripped entry is deliberately a *proposition*:
`IsDefEqU.strengthen_of_instN` discharges strengthening outright when the stripped entry is
inhabited downstairs, so a witness stripping an obviously-inhabited `Sort` would be testing the
easy half.

---

## 8. What to pick up first

1. **`PiDescend`** — the only open statement other than the target itself, and equivalent to the
   target's reflexive instance (`TypingStrengthening.iff_piDescend`).  §2.5 has its case split.
   Its induction never sees a conversion, and it is stated in the idiom of
   `Theory/Typing/Injectivity.lean`, whose `sort_forallE_inv` closes two of its five cases.
   **Whether it is provable is open and this pass makes no prediction.**
2. **The target itself.**  It needs a deterministic reduction relation (§1).  The two candidate
   sources in the tree — `ChurchRosser.lean` and `HeadReduction.lean` — are both gated on
   `Params` (§4.1), so *the first tractable step toward a reduction relation is instantiating
   `Params` from `VEnv.WF`*, not anything in this file.  `Theory/Typing/RawDefEq.lean`'s
   three-place judgment is the other foundation stone and has no `Params` gate; nobody has run
   a reduction over it.
3. **Do not** re-attempt: a direct conversion induction; "prove the typed form instead"; a model
   argument; `skips`; or re-deriving `Strengthening` from `TransStrengthening`-shaped residuals.
   §5 has the reason for each, and §0.0 makes the last one a one-liner.

## 9. Files

* `Lean4Lean/Theory/Typing/Strengthen.lean` — 520 lines, no `sorry`; §9 is new this pass.
* `Lean4Lean/Theory/Typing/StrengthenWitness.lean` — **new**, sorry-free, §7.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**; the `sorry` at :174 is still
  there and this pass did not earn the right to remove it.
* `scripts/cone-measure.lean` — **unchanged**; see §3 for the coverage caveat.
