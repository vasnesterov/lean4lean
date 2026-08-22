# Foundation: gaps found while building the set-theoretic model

Working notes from building `Lean4Lean/Theory/SetModel/` (six files, ~3900 lines)
on top of Foundation's `FirstOrder/SetTheory/`. The goal there is Carneiro's ZFC
model of Lean's type theory, developed *internally to an arbitrary model* `V` of
first-order `𝗭𝗙`, in Foundation's own idiom:

```lean
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
```

Everything below is something we had to build locally that arguably belongs
upstream, ordered by how much it cost and how much it would save others. Each
entry says what is missing, where it should live, what it cost us, and — where
we have it — the statement or the one-line fix.

Foundation is a pinned dependency here and was never modified; every workaround
lives in `Lean4Lean/Theory/SetModel/`.

---

## 1. `definability` fails opaquely — two distinct causes, one of them a bug

**Severity: highest.** This one is a one-line fix upstream, it silently blocks
real work, and it fails with an undiagnosable error.

`Foundation/FirstOrder/Basic/Definability.lean` proves
`DefinableFunction₁.comp` … `DefinableFunction₅.comp`, but registers only the
first three with the `definability` tactic:

```lean
attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction₁.comp
  DefinableFunction₂.comp
  DefinableFunction₃.comp        -- stops here
```

(`Definability.lean:477-480`. Compare the neighbouring block, which does go up to
`DefinableRel₄.comp`.) So a definable function of four or five set arguments is
out of the tactic's reach even though the composition lemma exists.

**Why this matters.** The minor premise of an inductive type's recursor is a
function of exactly four set arguments — the constructor tag `q`, the
non-recursive field data `a`, the tuple of recursive components `f`, and the
tuple of recursive results `h`:

```lean
e : V → V → V → V → V
```

Every recursor construction hits this. There is no way to route around it except
by currying through Kuratowski pairs, which corrupts the statement of the ι-rule.

**Why it is expensive to diagnose.** `definability` does not report "no rule
applies". It reports

```
aesop: internal error during proof reconstruction: goal 20 was not normalised
```

and, at the `sep`/`repl` call site, the wholly unrelated

```
could not synthesize default value for parameter 'hP' using tactics
```

Neither mentions arity, the tactic, or the missing lemma. We lost a debugging
cycle on it and only found it by reading the `attribute` block.

**Fix.** Add two names:

```lean
attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction₄.comp
  DefinableFunction₅.comp
```

**Our workaround:** the same two lines, in `SetModel/Inductive.lean` just after
the `open`s. A pure aesop rule-set addition; Foundation untouched.

### 1b. The same error has a second, unrelated trigger

Registering `₄.comp`/`₅.comp` does **not** exhaust this failure mode. Building
`Quot`'s denotation (`SetModel/QuotInterp.lean`) hit

```
aesop: internal error during proof reconstruction: goal 70 was not normalised
```

with the composition rules already registered, on a goal of arity 3. The trigger
is different: **an existential nested under a quantifier over sets.**

We isolated it rather than working around it, by proving the same statement in
two forms that differ only in that clause. `eqvClosure A R` is `lfp`, i.e.
`⋂ˢ` of the prefixed points, and `⋂ˢ`'s membership condition is

```
p ∈ ⋂ˢ X  ↔  IsNonempty X ∧ ∀ S ∈ X, p ∈ S
```

* With the `IsNonempty` clause — `definability` fails with the internal error.
* Without it, stating the same set by its universal property
  (`quotEqv A R := {p ∈ A ×ˢ A ; ∀ S ∈ ℘(A ×ˢ A), eqvStep A R S ⊆ S → p ∈ S}`)
  — `definability` succeeds.

Nothing else changed. So the widened statement of this gap is: `definability`
reports the same undiagnosable internal error for **at least two structurally
unrelated reasons**, and the arity fix addresses only one of them.

### 1c. `definability` silently discards its `config` argument

```lean
macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [Definability]))
```

(`Basic/Definability.lean:502`.) The `(config)?` is parsed and then **never
referenced in the expansion**, so `definability (config := …)` type-checks,
runs, and ignores what you asked for. A one-line fix; but until it lands there
is no way to tune the tactic except by calling `aesop` directly with the rule
set.

### The depth limit is *masking* the bug, not competing with it

This is the important correction, and it came from testing rather than
reasoning. The natural reading of 1a/1b is that some goals exhaust the search
budget and others trip the internal error. That is wrong. On the goal

```lean
ℒₛₑₜ-function₂ (fun ρ r ↦ quotVal (ρ ‘ 0) r i)     -- with quotVal_definable in context
```

* at the default limits: `maximum rule application depth (30) was reached`;
* calling `aesop` directly with `maxRuleApplicationDepth := 300`,
  `maxRuleApplications := 5000`: `internal error … goal 106 was not normalised`.

**Raising the limits does not fix the search; it exposes the defect underneath.**
So "`definability` needs a depth bump for downstream users" would have been the
wrong report — a bump alone makes this class of goals fail *differently*, not
succeed. The depth ceiling is currently the only thing keeping the failure
legible.

That also sharpens what to send upstream: the reproduction should be run at
raised limits, or the maintainers will see the depth message and conclude it is
a tuning question.

### Which failures are bugs, and which are limitations

The two symptoms need separating, because only one of them is worth a report:

| symptom | verdict |
|---|---|
| `Tactic 'aesop' failed … maximum rule application depth (30) was reached` | **limitation.** Honest failure, names its own cause, fixable by raising limits or supplying lemmas. |
| `aesop: internal error during proof reconstruction: goal N was not normalised` | **bug.** An internal invariant violation, not a proof-search failure. |

A tactic that cannot prove a goal should say so. This one reports a violated
internal invariant, which means proof reconstruction reached a state the
implementation did not expect. That is a defect regardless of whether the goal
was provable.

### Worth reporting upstream: yes

Recorded as a judgement since `Foundation` is pinned and this is not a "fix it"
question.

**Report it, to Foundation first.** The reasoning:

* It is a genuine bug by the criterion above, not a strength limitation.
* It is cheap to report: `quotEqv` versus the `⋂ˢ` form is a minimal
  reproduction that isolates one clause, and `SetModel/QuotInterp.lean` carries
  both halves already.
* It is expensive to *not* report: the error names neither the tactic's
  difficulty nor the offending subterm, so every encounter costs a debugging
  cycle. We have now lost two.
* The likely root cause is in the interaction between Foundation's
  `Definability` rule set and `aesop`'s normalisation, not in `aesop` alone —
  which is why Foundation is the right first recipient. They are better placed
  than we are to decide whether to forward it.

What we cannot say from here is whether the underlying defect is aesop's or is
provoked by a particular rule's shape in the `Definability` set. Both symptoms
disappear under the workarounds below, so we have no evidence isolating that.

### The three workarounds, and when each is needed

In increasing order of how much they change the statement:

1. **The `mem_ext_iff` route.** Restate `T = f a b …` as a first-order
   membership formula and call `definability` on that. This is Foundation's own
   idiom — `eqvStep_definable` is proved this way — and it is the first thing to
   try.
2. **Pass `sep`'s (or `repl`'s) definability argument explicitly** rather than
   through its `autoParam`. The `autoParam` runs `definability` *without* the
   local hypotheses that make it succeed, so a definition can fail to elaborate
   even when the corresponding standalone lemma is provable. See also gap #8.
3. **Replace a least fixed point by its Π₁ characterisation.** Needed when the
   fixed point appears inside a function that must itself be definable. This is
   the one that changes the statement, and it is worth stating as a rule:

   > A least fixed point is fine to *reason* with and bad to *compute inside a
   > definable function*. Where a definable version is needed, state the fixed
   > point by its universal property instead.

   This is not only about quotients. `Ind` and `indRec`
   (`SetModel/Inductive.lean`) are also `lfp`s, so the same substitution is
   already known to be needed when the inductive oracle is built.

---

## 2. `value_eq_of_kpair_mem` — applying an internal function

**Where it belongs:** `SetTheory/Function.lean`, next to `value_mem_range`.

Foundation defines `value` (`f ‘ x`) and proves exactly one lemma about it,
`value_mem_range`. The lemma that says `‘` computes is absent:

```lean
lemma value_eq_of_kpair_mem {f x y : V} [IsFunction f] (h : ⟨x, y⟩ₖ ∈ f) : f ‘ x = y
```

together with its converse companion

```lean
lemma kpair_value_mem {X Y g b : V} (hg : g ∈ (Y ^ X : V)) (hb : b ∈ X) : (⟨b, g ‘ b⟩ₖ : V) ∈ g
```

**Cost.** Every construction that *applies* an internal function needs it. We
hand-rolled it before noticing, and it is used in four of our six files (the
choice function, the quotient lift, the recursor's graph, the cardinality
transport). It now lives once in `SetModel/Rank.lean` (~20 lines for the pair).

This is the single most conspicuous omission in `SetTheory/Function.lean`: as
shipped, the library can *define* functions but not *evaluate* them.

Also missing next door: `Y ^ ∅ = {∅}` in general (only `empty_function_empty :
(∅ : V) ^ (∅ : V) = {∅}` is proved). See `eq_empty_of_mem_function_empty` in
`SetModel/Inductive.lean`.

---

## 3. No cardinal arithmetic

**Where it belongs:** a new `SetTheory/Cardinal.lean`.

`SetTheory/Function.lean` defines `CardLE` (`≤#`), `CardLT`, `CardEQ` and proves
five facts: `cardLE_of_subset`, `CardLE.refl/trans`, `cardLT_power`,
`two_pow_cardEQ_power`. That is the whole cardinality theory.

**Cost:** `SetModel/Cardinal.lean`, 458 lines, to reach `|V_β| < κ` for
inaccessible `κ` (needed for replacement inside `V_κ`). Reusable pieces that
should be upstream:

```lean
-- build `X ≤# Y` from a definable meta-level injection; without this every
-- cardinality argument hand-builds an internal set of Kuratowski pairs
theorem cardLE_of_definable_injOn {X Y : V} (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hmap : ∀ x ∈ X, F x ∈ Y) (hinj : ∀ x ∈ X, ∀ y ∈ X, F x = F y → x = y) : X ≤# Y

theorem power_cardLE_power {X Y : V} (h : X ≤# Y) : ℘ X ≤# ℘ Y

lemma mem_image_iff {f A y : V} : y ∈ (f “ A) ↔ ∃ x ∈ A, (⟨x, y⟩ₖ : V) ∈ f

noncomputable def InjSet (Y X : V) : V := {f ∈ (Y ^ X : V) ; Injective f}
lemma isNonempty_InjSet_iff {X Y : V} : IsNonempty (InjSet Y X) ↔ X ≤# Y

def IsLeastCard (X a : V) : Prop   -- the least ordinal `X` injects into
```

`cardLE_of_definable_injOn` is the one to take first: it is what made the rest of
the file short.

**Worth recording, because it is a nice shortcut.** The textbook route to
`|V_β| < κ` goes through `|α × β| = max(|α|,|β|)` for infinite cardinals
(Gödel pairing / Hessenberg). That is avoidable. At a limit stage one needs
`|α × b| < κ`, and Foundation's *own* bound for `prod` gives
`α ×ˢ b ⊆ ℘ ℘ (α ∪ b)` (`prod_subset_power_power_union`), while `α ∪ b` is just
`max α b` for ordinals — so two applications of strong-limitness plus
`power_cardLE_power` replace the whole of cardinal multiplication. The result
needs no Cantor–Schröder–Bernstein either (every step is a chain of `≤#`, never a
two-sided squeeze) and mentions no cardinal *numbers* at all.

Still missing, and the one thing we could not reach: **Hartogs' theorem** (the
ordinals injecting into `X` form an ordinal not injecting into `X`), which needs
the Mostowski collapse of a well-ordering onto an ordinal. It is what a cardinal
*successor* requires, and hence what a cofinality argument requires.

---

## 4. No `sep`-as-a-definable-function

**Where it belongs:** `SetTheory/Z.lean`, next to `sep`.

There is no way to see `fun S ↦ sep A (P S)` as an `ℒₛₑₜ-function₁`. Any
monotone operator defined by separation — i.e. any operator you would feed to a
least-fixed-point construction — needs this, and each time you must hand-roll:

```lean
lemma foo_definable (A R : V) : ℒₛₑₜ-function₁[V] (foo A R) := by
  suffices ℒₛₑₜ-relation[V] (fun T S ↦ T = foo A R S) by exact this
  have e : ∀ T S : V, T = foo A R S ↔ ∀ z, z ∈ T ↔ (z ∈ A ∧ …) := by
    intro T S; rw [mem_ext_iff]; simp [foo]
  simp only [e]
  definability
```

**Cost:** six instances of that boilerplate, ~8 lines each:
`accStep_definable` and `eqvClass.definable` (`SetModel/Inaccessible.lean`),
`eqvStep_definable` (`SetModel/Universe.lean`), `indStep_definable` and
`recStep_definable` (`SetModel/Inductive.lean`), `InjSet_definable`
(`SetModel/Cardinal.lean`).

A single general lemma of roughly the shape

```lean
lemma sep_definable {A : V} {P : V → V → Prop} (hP : ℒₛₑₜ-relation P) :
    ℒₛₑₜ-function₁[V] (fun S ↦ sep A (P S))
```

removes all six.

---

## 5. `𝗔𝗖` only in disjoint-family form

**Where it belongs:** `SetTheory/ZF.lean` or a new `SetTheory/Choice.lean`.

`Axiom.choice` is stated for a pairwise-disjoint family of nonempty sets. The
usable form — "every set has a choice function" — is not derived, so everyone who
uses choice internally must redo the `{x} ×ˢ x` disjointification.

**Cost:** ~60 lines in `SetModel/Universe.lean` (`internal_choice`,
`exists_choiceFunction`, `exists_choiceFunction_value`). The useful statement:

```lean
theorem exists_choiceFunction (S : V) :
    ∃ c : V, IsFunction c ∧ (∀ x ∈ S, IsNonempty x → ∃ y ∈ x, ⟨x, y⟩ₖ ∈ c) ∧
      (∀ x y : V, ⟨x, y⟩ₖ ∈ c → x ∈ S ∧ y ∈ x)
```

Note also that `Theory.models V 𝗔𝗖 …` needs `Axiom.choice ∈ (𝗔𝗖 : SetTheory)`,
and the `simpa [models_iff, Axiom.choice]` normal form of the axiom is not
documented anywhere; we recovered it by copying the shape out of
`SetTheory/Universe.lean`'s `models_ac` proof. A `lemma choice_iff` stating the
model-side reading would save that archaeology — and the same goes for every
other axiom.

---

## 6. `Recursion.lean` stops one step short

**Where it belongs:** `SetTheory/Recursion.lean` itself.

The file proves that an *attempt* function of every ordinal length exists
(`attempt_function_exists`), which is the hard part, but exports nothing usable:

- there is no packaged recursion `transrec F : V → V` with `transrec F α = F ⟨transrec F β | β < α⟩`;
- there is no recursion *equation* — the fact that the attempt of length `α`
  enumerates exactly the values below `α`;
- **`ℒₛₑₜ-function₁ (attemptOrEmpty F)` is proved inside the body of
  `Replacement.replAttemptOrEmpty` and never exported.** We had to copy that
  proof verbatim.

**Cost:** ~50 lines at the top of `SetModel/Rank.lean` (`transrec`,
`attemptOrEmpty_definable`, `transrec_definable`, `isAttempt_attemptOrEmpty`,
`attemptOrEmpty_restrict`, `mem_range_attemptOrEmpty`). Every one of them is
generic — none mentions the cumulative hierarchy — so all six belong upstream.

---

## 7. `Ordinal V` is missing basic API

**Where it belongs:** `SetTheory/Ordinal.lean`.

No notion of limit ordinal, and no successor/order interaction:

```lean
structure IsLimitOrdinal (α : Ordinal V) : Prop where
  pos : ⊥ < α
  succ_lt : ∀ β < α, β.succ < α

lemma succ_le_of_lt {α β : Ordinal V} (h : β < α) : β.succ ≤ α
lemma le_of_lt_succ {α β : Ordinal V} (h : β < α.succ) : β ≤ α
```

`IsLimitOrdinal` is the hypothesis of essentially every closure property of the
cumulative hierarchy, so its absence is felt immediately. Also absent, and
elementary: `rank α = α` for an ordinal `α` — though that one presupposes a
`rank`, which Foundation also does not have (see §9).

**Cost:** ~15 lines in `SetModel/Rank.lean`, but they gate everything after them.

---

## 8. `repl`'s `autoParam` is in the wrong argument position

**Where it belongs:** `SetTheory/ZF.lean`.

```lean
noncomputable def repl (F : V → V) (hF : ℒₛₑₜ-function₁ F := by definability) (X : V) : V
```

The `autoParam` sits *between* the two arguments a caller wants to supply, so
`repl F X` does not elaborate — you must write `repl F (X := X)` or pass the
definability proof explicitly. Compare `sep x P (hP := by definability)` and
`replRelOverSet X R h (hR := by definability)`, where the `autoParam` is last and
the natural call works.

Moving `hF` after `X` is source-compatible with keyword callers and fixes the
positional ones. Small, but it trips every first use.

---

## 9. `InaccessibleCardinal.lean` is syntax-only

**Where it belongs:** `SetTheory/InaccessibleCardinal.lean`.

The file defines the `ℒₛₑₜ`-formulas `IsCardinal.dfn`, `IsRegular.dfn`,
`IsStrongLimit.dfn`, `IsInaccessible.dfn`, `inaccessibleChain`, and the theory
`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` — and stops. There are no Lean-level predicates and no `Defined`
instances, so nothing in it can be used inside a model, which is the only thing
one would want it for.

**Cost:** ~120 lines in `SetModel/Inaccessible.lean`: the four predicates with
their `Defined … via …` instances against Foundation's own formulas, the chain
predicate, and the extraction of an `∈`-increasing chain of `n` inaccessibles
from the axiom schema. The `Defined` instances are one line each
(`⟨fun v ↦ by simp [P, P.dfn]⟩`) — they were simply never written.

Related, and trivial: **there is no `[V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖`
instance.** `Basic/Model.lean` has the chain `𝗭𝗙𝗖 → 𝗭𝗙 → 𝗭` but
`InaccessibleCardinal.lean` adds only the `⪯` instance, not the `⊧*` one, so the
chain breaks at the top. One line:

```lean
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 :=
  models_of_ss inferInstance zfc_subset_zfcInacc
```

---

## 10. No cumulative hierarchy, no rank, no `∈`-induction

**Where it belongs:** a new `SetTheory/Rank.lean`.

Foundation has ordinals, transfinite induction and transfinite recursion, but not
`V_α`, not `rank`, and — the one that bites hardest — **no `∈`-induction**.
`Ordinal.lean` has `IsWellFoundedRel.mem`, but nothing usable follows from it;
`foundation` alone (every nonempty set has an `∈`-minimal element) does not give
induction over the whole model. Getting there needs the transitive closure of
`{a}`, which needs its own transfinite recursion.

**Cost:** `SetModel/Rank.lean`, 606 lines. All of it is generic set theory with
no Lean-type-theory content:

```lean
noncomputable def Vset (α : Ordinal V) : V
theorem mem_Vset_iff {α : Ordinal V} {z : V} : z ∈ Vset α ↔ ∃ β < α, z ⊆ Vset β
theorem mem_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ x : V, (∀ y ∈ x, P y) → P x) : ∀ x : V, P x
noncomputable def rank (x : V) : Ordinal V
theorem mem_Vset_iff_rank_lt {x : V} {α : Ordinal V} : x ∈ Vset α ↔ rank x < α
theorem rank_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ x : V, (∀ y : V, rank y < rank x → P y) → P x) : ∀ x : V, P x
```

`mem_induction` and `rank_induction` are the two that anything recursive needs.

---

## The `isDefEq` divergence hazard, and the discipline that avoids it

**New instance (2026-08): coercion indices.** Ascribing a type to a `have` whose
index is a coerced numeral loops, where taking the lemma's own form does not:

```lean
-- loops at whnf, 1M heartbeats
have hval : (snoc ∅ α) ‘ ((0 : ℕ) : V) = α := snoc_value_at_len M L hnil
-- fine
have hval := snoc_value_at_len M L (v := α) hnil
rw [List.length_nil] at hval
```

The lemma's index is `((Γ.length : ℕ) : V)`; ascribing `((0 : ℕ) : V)` asks
`whnf` to reconcile two coercion shapes and it unfolds the von Neumann numerals.
Rewriting at the `ℕ` level is one syntactic step. The discipline is the same as
for the other instances — **do not ascribe a type that differs from the lemma's
even when the two are "obviously" equal** — but this one is worth calling out
because the difference is invisible at a glance and the symptom is identical to
the unrelated `mkLam` proof-term blow-up.

This is not a missing lemma; it is a property of the `Ordinal V` encoding that
costs hours if you meet it without warning. It bit us in **every one of the six
files**, and each time it presented as a hang, never as a type error.

**The shape.** `Ordinal V` is a structure with a `val : V` field, and `Vset` is
defined by `Vset α = vsetV α.val`. So whenever the elaborator has to solve

```
Ordinal.val ?β  =?=  x            -- x a concrete term of type V
```

it is outside the pattern fragment. Lean falls back on structure eta, assigning
`?β := ⟨x, ?ord⟩` and then trying to synthesise `?ord : IsOrdinal x`; if that
fails or is postponed it starts delta-unfolding, and the terms in question are
`Classical.choose!` of large existence proofs (`attemptOrEmpty`, `lfp`, `rank`).
The result is a `(deterministic) timeout at isDefEq` that does **not** go away at
2,000,000 heartbeats — it is a genuine loop, not slowness.

**How it presents.** Always as one of

```
(deterministic) timeout at `isDefEq`,  maximum number of heartbeats … reached
(deterministic) timeout at `whnf`,     maximum number of heartbeats … reached
```

reported at the *declaration* line, with no indication of which subterm is
responsible. Bisecting with `sorry` is the only reliable way to localise it.

**Concrete triggers we hit.**

| Trigger | File |
|---|---|
| `attemptOrEmpty_restrict F hF hle` with `β` implicit, matched against a raw `x : V` | `Rank.lean` |
| `Vset_mono …` elaborated against a goal ending in `vsetV b` | `Inaccessible.lean`, `Cardinal.lean` |
| `lt_def.mp h` elaborated against an expected type `rankV (F x) ∈ k` | `Inaccessible.lean` |
| `sUnion_mem_Vset` etc. against `U κ (i+1)`, where `U` is defined by recursion on `ℕ` | `Universe.lean` |
| `rank_Vset` rewriting under `vsetV (κ j)` | `Universe.lean` |

**The discipline.** Three rules, and following them we have not hit the hazard
since:

1. **Rewrite the goal into canonical form before applying any lemma.** Keep one
   bridging `Iff.rfl` per encoding and `rw` with it first:
   ```lean
   lemma mem_vsetV_iff_mem_Vset {k z : V} [IsOrdinal k] :
       z ∈ vsetV k ↔ z ∈ Vset (IsOrdinal.toOrdinal k) := Iff.rfl
   ```
   then `rw [mem_vsetV_iff_mem_Vset] at h ⊢` (and `rw [U_succ]` first where the
   stage is `U κ (i+1)`). After that every `isDefEq` call has two concrete sides.
2. **Never let an `Ordinal V` implicit be solved from a `V`-level goal.** Pass it:
   `attemptOrEmpty_restrict F hF (β := IsOrdinal.toOrdinal x) hle`.
3. **Introduce intermediate `have`s with fully spelled-out types**, then `exact`.
   ```lean
   have hsub : F x ⊆ Vset (IsOrdinal.toOrdinal b : Ordinal V) := …
   exact hsub                      -- one cheap concrete-vs-concrete check
   ```
   Chaining `subset_trans`/`refine` across an encoding boundary is what leaves a
   projection applied to a metavariable.

**Upstream mitigation.** Two possibilities, either of which would help a lot:
mark `Ordinal.val` `@[reducible]`-unfriendly / add `@[simp]` normal forms so the
canonical direction is forced; or expose a `V`-level `Vset : V → V` API (which is
what we ended up doing locally as `vsetV`) so that callers never have to cross
the boundary at all.

---

## Summary table

| # | Gap | Home in Foundation | Cost here | Fix size |
|---|---|---|---|---|
| 1a | `definability` blind to arity 4–5 | `Basic/Definability.lean:477` | debugging cycle; blocks all recursors | **2 lines** |
| 1b | same internal error, second trigger: `∃` under a set quantifier | unknown — rule set or `aesop` | second debugging cycle; forces restating `lfp`s | unknown; **worth reporting** |
| 1c | `definability` parses `config` and discards it | `Basic/Definability.lean:502` | no way to tune the tactic | **1 line** |
| 2 | `value_eq_of_kpair_mem` | `SetTheory/Function.lean` | ~20 lines, used in 4 files | ~20 lines |
| 3 | No cardinal arithmetic | new `SetTheory/Cardinal.lean` | 458 lines | medium |
| 4 | No `sep`-as-definable-function | `SetTheory/Z.lean` | 6 × ~8 lines | ~15 lines |
| 5 | `𝗔𝗖` only disjoint-family | `SetTheory/ZF.lean` | ~60 lines | ~60 lines |
| 6 | `Recursion.lean` exports nothing usable | `SetTheory/Recursion.lean` | ~50 lines | ~50 lines |
| 7 | No `IsLimitOrdinal`, no succ/order API | `SetTheory/Ordinal.lean` | ~15 lines | ~15 lines |
| 8 | `repl`'s `autoParam` mis-positioned | `SetTheory/ZF.lean` | friction | **1 line** |
| 9 | `InaccessibleCardinal.lean` syntax-only | same file | ~120 lines | ~120 lines |
| 10 | No `V_α` / `rank` / `∈`-induction | new `SetTheory/Rank.lean` | 606 lines | large |
| — | `isDefEq` divergence hazard | — | recurring; see above | docs, or a `V`-level API |

If only two things are contributed upstream, they should be **#1** (see below)
and **#2** (twenty lines, and without it the library can define functions but
not apply them).

**#1 is now two items.** #1a is the two-line `attribute` addition — trivial,
known, and unblocks an entire class of constructions. #1b is a defect we can
reproduce but not diagnose: the identical internal error, on a goal of arity 3,
with the composition rules already registered. Only #1b is a *bug report* rather
than a contribution; see "Worth reporting upstream" under gap 1 for the criterion
separating the two and the minimal reproduction.
