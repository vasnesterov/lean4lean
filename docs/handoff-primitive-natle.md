# RESOLVED — read this box before anything below it

**The fix was one token, and most of this document describes a wrong turn.** `f743c46`'s design was
correct; only one of its six lemmas (`Nat.pos_of_ne_zero`) is outside the checked declaration's
cone. Swapping it for `Nat.zero_lt_of_ne_zero` — same statement, same binder kinds, in both cones,
and the lemma `Nat.gcd`'s own `decreasing_by` uses — restores the shape `Boundaries.lean` was
already proved against. `lake build` FULL=0, guards `24 / INCOMPLETE / 2/2` unmoved, **no proof-side
work needed**, `init` 53090 declarations, false-primitive audit unchanged.

What is **superseded and must not be acted on**:

- **§1's cone figures (135 / 147) are wrong** — they are 238 and 352, and only *one* constant was
  ever missing (`scripts/gcd-cone-probe.lean`, ledger row 121h).
- **§2's claim that the binder's proposition is true "at the literal instances the fuel induction
  consumes" is FALSE.** `reflects_fuel_gcd` calls `hgo` *before* splitting on `x = 0`, so `x = 0`
  states are consumed too and the obligation there is `y + 1 ≤ f`: `Nat.gcd 0 5` needs `6 ≤ 0`,
  `Nat.gcd 4 6` needs `3 ≤ 2` (`scripts/gcd-fuel-zero-gap.lean`). No witness family closes that.
- **§4's `Condition.natLE` route is reverted from the implementation.** It closes only the `x ≠ 0`
  half, and it was manufacturing witnesses for a gap that the variable-binding redesign had itself
  created by hoisting the proof out of the `dite`'s else-λ, where `¬(m = 0)` is in scope.

What is **still true and worth keeping**: §2's observation that the proposition is false in general
(the inverse of this repo's usual vacuity trap — a sound, non-vacuous *check* whose *spec-side*
hypothesis cannot be discharged); §3's finding that the theory had no producer of `natLE` witnesses;
and the machinery built to fix that (`VExpr.gcdCtxWF`, `IsDefEqU.instGcdWF`,
`Condition.check.WF_natLE_pinned`, `trExprS_ofTrueType_inv'`), which remains in
`Verify/PrimitiveWF.lean` with hole cone `[]` and no frozen axiom, explicitly marked **unused by
the implementation** and available to any future five-binder route.

---

# The `Nat.gcd` / `Nat.bitwise` fuel bound: variable-bound, and what the verification now needs

Written 2026-09-02 by the orchestrator, from a measurement stream's report. Companion to ledger
rows 121–121e and `docs/handoff-primitive-false.md`.

## 1. Why the implementation changed

Commit `f743c46` closed a **real soundness hole**: before it, a declaration named `Nat.gcd` with a
wrong body passed the recognizer while `TypeChecker.reduceNat` accelerated it *by name*, which
yields `False` (`scripts/primitive-false-audit.lean` derives it in three lines). To close it, the
recognizer checks a fuel-recurrence equation whose recursive call takes a **proof** of the fuel
decrease — and `f743c46` wrote that proof out of six lemmas:

    Nat.pos_of_ne_zero, Nat.mod_lt, Nat.lt_of_lt_of_le, Nat.le_of_lt_succ,
    Nat.div_lt_self, Nat.le.refl

**Measured**: the transitive cone of `Nat.gcd` is 135 constants and of `Nat.bitwise` 147, and
**all six are absent from both**. `Nat.div_rec_fuel_lemma`, which the already-proved `Nat.mod` /
`Nat.div` branches use, **is** present — which is exactly why only these two branches broke. Under
the Kernel Arena's `--import <ndjson>` path (replay adds only the submitted declaration's cone) the
recognizer could not type-check its own reference term, and the *genuine* `Nat.gcd` was rejected
with `(kernel) unknown constant 'Nat.pos_of_ne_zero'`. `init`, `std` and `perf/grind-ring-5` all
failed for twelve days. Reverting is not available: it reopens the hole.

The fix (installed): bind the proof as a variable at `goType`'s own third binder instantiated at the
smaller argument.

```lean
withCheckedLocalDecl `hrec .default
  (mkApp2 q(@LE.le Nat instLENat) (succ (mkApp u.measure (pk (mod n m) m))) fuel) fun prf => do
```

**Confirmed by the stream, not assumed**: this type *is* `NatWFUnfold.goType`'s third binder at
`x := pk (mod n m) m`, `fuel := fuel` (`goType` is `Primitive.lean:402`; for `Nat.bitwise`, `u.goType`
is closed in the `f` binder so stripping `mkApp u.go f` is identity on it). The accept set is
unchanged wherever the old term type-checked — the two proof types are defeq (delta on
`Nat.lt`/`instLENat`, plus the measure equation) and both sit in a proof position of a `Nat`-valued
application, so kernel proof irrelevance fires — and strictly larger where the old constants were
absent, which is the point. Non-vacuity re-measured: all eight wrong bodies still rejected
(`badGcd`, `bigGcd`, `w1`, `w2`, `w3`, `s1`, `badBitwise`, `wb`), the four genuine ones accepted.
`w1/w2/w3` are wrong *recursive arguments* and are the ones that matter.

## 2. The trap this created, and it is the inverse of the usual one

**The proposition the new binder inhabits is FALSE in general.** Machine-checked, both branches:

```lean
example : ¬ (∀ m n fuel : Nat, Nat.succ m ≤ Nat.succ fuel → Nat.succ (n % m) ≤ fuel)
example : ¬ (∀ n fuel : Nat, Nat.succ n ≤ Nat.succ fuel → Nat.succ (n / 2) ≤ fuel)
```

Witness `m = n = fuel = 0`: `0 % 0 = 0`, so the hypothesis `1 ≤ 1` holds and the goal is `1 ≤ 0`.

This does **not** weaken the check. A defeq check against a free variable compares terms; it is not
semantic quantification, and the audit above is the evidence. What it breaks is the *verification*:
`Verify/Environment/Boundaries.lean` must **instantiate** that binder, and at the literal instances
the induction actually consumes, the proposition *is* true (`x ≠ 0 → x ≤ f → y % x + 1 ≤ f`) — but a
term witnessing it is required, and there was no producer.

Note the shape, because it is the mirror image of this repo's usual failure: the ordinary trap is a
green statement whose hypothesis is uninhabited. Here the *check* is sound and non-vacuous while the
*hypothesis of the spec-side lemma* is what cannot be discharged. Instruments that read conclusions
see nothing wrong in either case.

## 3. Why the old proofs cannot simply be re-threaded

The extra `vlam` is the easy half. `hgoeq0` now lives at a **5-binder** context (`m, n, fuel, h,
hrec`) and its RHS mentions `hrec`, while `VEnv.reflects_gcd_of_equations` wants it at
`VExpr.gcdCtx` (4 binders). Every route out of a context here is instantiation: `IsDefEqU.instN`
(`Theory/Typing/Lemmas.lean:681`) demands `h₀ : env.HasType U Γ₀ e₀ A₀`, an actual witness;
`IsDefEqU.instGcd`'s docstring says the proof binder is substituted by a term *the caller supplies
together with its typing*. No strengthening lemma applies, because the RHS does mention the new bvar.

In the old proof that witness **was the recognizer's written-out term**:
`reflects_gcd_of_equations`'s `hK` (`Verify/PrimitiveWF.lean:797`) takes the instantiated `KA`, feeds
`hsel`'s output to `ok_of_goApp`, and reads the type off the well-formed `go` application. Remove the
term and `hK` has nothing to type.

Searched and found empty: every `natLEApp` occurrence in `Verify/Primitive.lean` and
`Verify/PrimitiveWF.lean` is a **consumer or an inverter — there is no producer**. `HasPrimitives`
(`Verify/Typing/Expr.lean:287`) has no `Nat.le` field, and the theory treats
`natLE = LE.le Nat instLENat` as opaque constants, so `Nat.le`'s constructors are unavailable. The
only witnesses reachable from the branch's own facts are `natLE (natLit (k+1)) (natLit (k+1))`, via
`u.prfA` from the entry equation; `hRD` (`Condition.natEq`) yields `Eq`/`¬Eq`, not `≤`. Since the
recurrence drops fuel by 1 while the measure jumps `x ↦ y % x`, the reflexive family never covers the
needed instances, and bridging them by a fuel-monotonicity lemma is the same goal again.

## 4. The route now installed in the implementation

One line added to each branch, beside the existing `Condition.natEq` / `Condition.bool` checks:

```lean
let cle := Condition.natLE; cle.check fail (dite := true)
```

`Condition.natLE` is `Primitive.lean:135`. `Condition.check.WF_natLE`
(`Verify/Primitive.lean:3801`) yields
`ReflectsCondAppDAll FD .natLE (.const ``Nat.decLe []) OT OF PR Nat.ble`, and
`ReflectsCondAppD.natLE_le` (`Verify/Primitive.lean:989`) then gives, for `i+1 ≤ f`, a well-formed
`dite` whose `.wf_r` types `OT (natLE (i+1) f) (PR (i+1) f)` at
`natLEApp (natLit (i+1)) (natLit f)` — **exactly the `hK` family**, uniform in `f x y h`, which
`reflects_fuel_gcd` already accepts as a function `K : Nat → Nat → Nat → VExpr → VExpr`.

**Cone-checked before installing**: every constant `Condition.natLE` and `Reflection.defn₁` mention
(`Nat.decLe`, `Nat.ble`, `Nat.le_of_ble_eq_true`, `Nat.not_le_of_not_ble_eq_true`, `Bool.noConfusion`,
`instDecidableEqBool`, `ite`, `dite`, …) has **missing-from-cone = [] for both `Nat.gcd` and
`Nat.bitwise`**. So this does not reintroduce `f743c46`'s failure mode. It is the machinery the
proved `Nat.mod` / `Nat.div` branches already use.

Rejected alternatives, with reasons:

- **`env.contains` guards on the old constructed proof.** The gate failing rejects the genuine
  `Nat.gcd`, which is the bug itself. Also: neither fallback is open — `fail` throws, and
  `return false` makes `checkName` throw `unexpected use of primitive name`, because the name is in
  `Environment.primitives`. A name in that list may be declared **only** if the recognizer succeeds.
- **Checking `Nat.le`'s constructors** (`Nat.le.refl`, `Nat.le.step`, plus the `LE.le`/`Nat.le`
  unfolding) and building `Nat.le.step^(f-i-1) Nat.le.refl` in the verification. All three constants
  are in both cones, so it would work, but it needs a new inhabitation lemma from scratch where the
  `Condition.natLE` route reuses two existing ones.

## 5. What is open

### 5.1 First correction: the two errors are not where §5 said, and not what it said

Ground truth on 2026-09-02, from `lake build` and from the LSP on the file (both agree):

```
error: Lean4Lean/Verify/Environment/Boundaries.lean:517:56: unsolved goals   -- Nat.gcd
error: Lean4Lean/Verify/Environment/Boundaries.lean:802:56: unsolved goals   -- Nat.bitwise
        ...  ⊢ Expr.FVarsIn (fun x => x ∈ (VContext.mlctx ?m.6154).vlctx.fvars) ?m.6161
```

Not `711:23` / `1057:23`, and not `Application type mismatch`. Both are the `(by simp [FVarsIn])`
of the *first* `M.WF.withCheckedLocalDecl` after the `Condition.bool` check, and both fail with
**unassigned metavariables**, which is the signature of a monadic `refine` chain that no longer
lines up with the program. The cause is one step earlier than §5 assumed: the proof script never
consumes the new `let cle := Condition.natLE; cle.check fail (dite := true)` bind at all. The
error's hypothesis list confirms it — it carries `hRD` (`natEq`) and `hB1` (`bool`) and **no**
`natLE` fact. So the `hrec` binder was never threaded either; `Boundaries.lean`'s two branches are
still at the pre-`f743c46` shape.

### 5.2 Second correction, and this is the blocking one: **§2's claim about the instances is false**

§2 says the proposition the new binder inhabits "is false in general" but that "at the literal
instances the fuel induction consumes, the proposition *is* true (`x ≠ 0 → x ≤ f → y % x + 1 ≤ f`)".
The parenthesis is the whole claim, and the induction does **not** only consume `x ≠ 0` instances.

`VEnv.reflects_fuel_gcd`'s `succ f` case (`Verify/PrimitiveWF.lean`) runs

```lean
| succ f ih =>
  intro x y hx h hok
  have e1 := hgo f x y h hok          -- ← unconditional, BEFORE the split
  have e2 := hsel f x y h hok e1.wf_r
  ...
  by_cases hx0 : x = 0
```

so the recurrence equation must be instantiated at the `x = 0` states too, and there the binder's
type is `Nat.succ (y % 0) ≤ f`, i.e. `y + 1 ≤ f`. The invariant `x < fuel` degenerates to `0 ≤ f`
there and gives nothing.

**Machine-checked** in `scripts/gcd-fuel-zero-gap.lean` (`lake env lean` it; every claim is a
`#guard_msgs`/`decide`, none is prose):

| instance | trace | obligation at the last state | verdict |
| --- | --- | --- | --- |
| `Nat.gcd 0 5` | `[(1,0,5)]` — the entry state itself | `5 % 0 + 1 = 6 ≤ 0` | **false** |
| `Nat.gcd 4 6` | `[(5,4,6), (4,2,4), (3,0,2)]` | `2 % 0 + 1 = 3 ≤ 2` | **false** |

The same file proves the positive half (`x ≠ 0 → x ≤ f → Nat.succ (y % x) ≤ f`) and the negative
half (`¬ ∀ y f, 0 ≤ f → Nat.succ (y % 0) ≤ f`), so the split is exactly `x = 0` vs `x ≠ 0`.

`Nat.bitwise` has the identical gap at `n = 0`: its binder asks for `n / 2 + 1 ≤ f`, which the
invariant `n ≤ f` gives for `n ≥ 1` and not for `n = 0`, and `Nat.bitwise g 0 b` enters at `f = 0`.

**Why no witness family can fix this.** Instantiating the fifth binder is `IsDefEqU.instN`, which
demands `env.HasType 0 [] w A₀`; `A₀` is defeq (via the checked measure equation and
`HasPrimitives.natMod`) to `natLEApp (natLit (y % x + 1)) (natLit f)`. At the `x = 0` states that
proposition is *semantically false*, so in a consistent environment **nothing inhabits it**. This
is not a missing lemma, and it is not a gap the `Condition.natLE` route can close: §4's route is
correct as far as it goes and it closes precisely the `x ≠ 0` half.

The only route that would close the `x = 0` half without touching the implementation is
`VEnv.IsDefEqU.weakN_iff` (strengthening: drop the unused binder from the context). That is the
project's central open hole. Measured hole cones (`deps`-walk over `sorryAx` users, same algorithm
as `scripts/hole-cone.lean`):

* `VEnv.reflects_gcd_of_equations` today: `[IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]`
* `VEnv.reflects_bitwise_of_equations` today: the same two
* `weakN_iff` is **not** in either, and it has 296 users of its own

So using it would be a real, measurable enlargement of these two theorems' hole cones, on top of
a hole that is actively being attacked in five files. I did not do it. It is the owner's call.

### 5.3 What I proved and left in the tree (all compiles, no new axioms, no new `sorry`)

Every one of these is needed by *any* fix, and the first two are needed by the branch as written
(its `env.contains` guard lists `Nat`, `Bool`, `Nat.mod`, `Nat.beq` and **not** `Nat.ble`, so the
existing `Condition.check.WF_natLE` was unusable there):

| declaration | file | what changed | `#print axioms` |
| --- | --- | --- | --- |
| `trExprS_ofTrueType_inv'` | `Verify/Primitive.lean` | **new** — inverts `∀ (p : Prop), r.type p true → p`, the type `Reflection.checkNatDITE` checks `r.ofTrue` against | `propext, Classical.choice, Quot.sound` |
| `Reflection.checkNatDITE.WF` | `Verify/Primitive.lean` | conclusion **strengthened**: now also yields `OT`'s declared type (needs a new `hRTb` hypothesis, supplied by the one caller) | 24, incl. `sorryAx` |
| `Condition.check.WF` | `Verify/Primitive.lean` | conclusion **strengthened**: the `dite` clause now also yields `∀ a b, g a b = true → HasType (OT (P a b) (PR a b)) (P a b)` | 24, incl. `sorryAx` |
| `Condition.check.WF_natLE` | `Verify/Primitive.lean` | hypothesis `hble : venv.contains ``Nat.ble` **dropped** (derived from the check's own `TrExprS` of `.const ``Nat.ble []`), witness family propagated | 24, incl. `sorryAx` |
| `Condition.check.WF_natLE_pinned` | `Verify/Primitive.lean` | `hsafe` and `hbleE` **dropped**; conclusion gains `∀ i f, i ≤ f → HasType (OT (natLE i f) (PR i f)) (natLE i f)` | 24, incl. `sorryAx` |
| `VExpr.gcdCtxWF`, `IsDefEqU.instGcdWF` | `Verify/PrimitiveWF.lean` | **new** — the 5-binder context and its instantiation (four numerals/`h`, then the witness) | `propext, Classical.choice, Quot.sound`; hole cone `[]` |
| `VEnv.reflects_fuel_gcd` | `Verify/PrimitiveWF.lean` | `hK` gains `x < f + 1` (a *weakening* of `hK`, so the theorem is stronger) | `propext, sorryAx, Classical.choice, Quot.sound` |

Re-measure with `scripts/natle-witness-axioms.lean`.  The 24-axiom sets are the `Lean.Expr.*_eq` /
`ptrEq*_eq` implementation-bridge axioms plus `propext`/`Classical.choice`/`Quot.sound`/`sorryAx` —
`sorryAx` was already there before these edits (the `M.WF` layer reaches it), and the only axioms
the *new* material introduces are `propext`, `Classical.choice`, `Quot.sound`, all already inside
Guard's whitelist.  **No new frozen-axiom dependency**: guard 1 still reads exactly 24 and guard 2
still reports "axioms within whitelist ✓".
| `Boundaries.lean` `Nat.mod`/`Nat.div` | `Verify/Environment/…` | the two `WF_natLE_pinned` call sites updated to the new signature | — |

`Condition.check.WF_natLE_pinned`'s new conjunct is **the producer §3 said did not exist**: "every
`natLEApp` occurrence … is a consumer or an inverter — there is no producer". It is exhibited, not
argued — it is `ofTrue`'s *declared* type applied to the reflection proof, and its non-vacuity is
witnessed at every `i ≤ f`:

```
∀ i f : Nat, i ≤ f →
  c.venv.HasType 0 [] (.app (.app OT (.natLEApp (.natLit i) (.natLit f)))
    (.app (.app PR (.natLit i)) (.natLit f))) (.natLEApp (.natLit i) (.natLit f))
```

Note it goes through `ofTrue`'s type, **not** through `ReflectsCondAppD.natLE_le`'s `.wf_r` as §4
proposed. §4's route also needs the `Decidable` instance's typing at a pair of numerals, and
`Reflection.check` only `checkType`s `r.toDec` (no declared type), so `D a b`'s type is not pinned
and the well-formed `dite` §4 wants cannot be built. The `ofTrue` route needs nothing extra.

`Condition.check.WF_natEq` deliberately *drops* the new conjunct rather than exposing it: nothing
consumes an `Eq` witness. That is a conclusion-side omission, not a weakening of anything used.

### 5.4 What is still open, and the options

`lake build` is at the same two errors it started at (517:56 and 802:56); guards unchanged —
guard 1 `24`, guard 2 `INCOMPLETE: sorryAx present`, guard 3 `2/2`.

Options, all of them implementation-side except the last. **Option 1 is a one-token change and I
believe it is the answer**; see §5.5.

1. **Put the proof term back under the `dite`'s else-λ, with one constant swapped.** §5.5.
2. **Bind an implication** `¬(m = 0) → Nat.succ (measure (pk (mod n m) m)) ≤ fuel` and apply it to
   the else-λ's `.bvar 0`. The `x ≠ 0` instances are then inhabited by a constant function
   `.lam (¬P) w` from the witness family of §5.3 (needs `Not`'s typing, which
   `Reflection.checkNatDITE` already checks but does not expose — a two-line change to its WF). The
   `x = 0` instances need `¬(0 = 0) → P`, i.e. ex falso, i.e. `False.elim`/`absurd` reflected — new
   machinery, and neither the `Reflection` types nor `HasPrimitives` provides it today. (Both
   constants *are* in both cones, per `scripts/gcd-cone-probe.lean`.)
3. **Accept `weakN_iff`** and strengthen away the unused binder, with the hole-cone delta in 5.2
   recorded in the ledger.

### 5.5 Third correction, and the cheap way out: **§1's cone measurement is wrong — only ONE of the six is missing**

The deleted code is the tell. `git diff Lean4Lean/Primitive.lean` shows what `f743c46` had, and
what it had was **already inside the `dite`'s else-λ**:

```lean
-- `.bvar 0` is the ¬(m = 0) that `Condition.dite`'s else-branch `lam0` binds.
let hpos := mkApp2 q(@Nat.pos_of_ne_zero) m (.bvar 0)
let prf := mkApp5 q(@Nat.lt_of_lt_of_le) (mod n m) m fuel
  (mkApp3 q(@Nat.mod_lt) n m hpos) (mkApp3 q(@Nat.le_of_lt_succ) m fuel h)
```

That is exactly the shape that has no `x = 0` problem: the proof lives where `¬(m = 0)` is in
scope, so nothing false ever has to be inhabited, and `Boundaries.lean` / `PrimitiveWF.lean` were
*already proved* against it. Hoisting it out of the λ is what created §5.2's gap.

§1 says the six constants it used are "**all six absent from both**" cones (135 for `Nat.gcd`, 147
for `Nat.bitwise`). Re-measured with `scripts/gcd-cone-probe.lean` (transitive
`getUsedConstants` closure of type *and* value, which is what a dependency-closure replay adds),
against the pinned toolchain's own environment:

| cone | size | of the six: PRESENT | of the six: ABSENT |
| --- | --- | --- | --- |
| `Nat.gcd` | **238** | `Nat.mod_lt`, `Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`, `Nat.le.refl` | `Nat.pos_of_ne_zero`, `Nat.div_lt_self` |
| `Nat.bitwise` | **352** | `Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`, `Nat.div_lt_self`, `Nat.le.refl` | `Nat.pos_of_ne_zero`, `Nat.mod_lt` |

Cross-check the *used* set against the branch that used it:

* `Nat.gcd`'s deleted term names `Nat.pos_of_ne_zero`, `Nat.lt_of_lt_of_le`, `Nat.mod_lt`,
  `Nat.le_of_lt_succ`. Only the first is absent. (`Nat.div_lt_self` is absent but `Nat.gcd` never
  used it.)
* `Nat.bitwise`'s deleted term names `Nat.lt_of_lt_of_le`, `Nat.div_lt_self`,
  `Nat.pos_of_ne_zero`, `Nat.le.refl`, `Nat.le_of_lt_succ`. Only the third is absent.
  (`Nat.mod_lt` is absent but `Nat.bitwise` never used it.)

So **exactly one constant is missing, in both branches, and it is the one the arena named**:
`(kernel) unknown constant 'Nat.pos_of_ne_zero'`. And it has a drop-in replacement that **is** in
both cones — `Nat.gcd`'s own `decreasing_by` uses it
(`~/lean4/src/Init/Data/Nat/Gcd.lean:41`, `zero_lt_of_ne_zero`):

```
@Nat.pos_of_ne_zero     : ∀ {n : Nat}, n ≠ 0 → 0 < n
@Nat.zero_lt_of_ne_zero : ∀ {a : Nat}, a ≠ 0 → 0 < a
```

Same statement, same implicit/explicit split, so `mkApp2 q(@Nat.pos_of_ne_zero) m (.bvar 0)`
becomes `mkApp2 q(@Nat.zero_lt_of_ne_zero) m (.bvar 0)` and nothing else moves.

**The experiment, in order** (I did not run it: it edits `Lean4Lean/Primitive.lean`, which is off
limits to me):

1. Revert both branches to the `f743c46` proof terms (the deleted lines above and their
   `Nat.bitwise` twin), swapping `Nat.pos_of_ne_zero` → `Nat.zero_lt_of_ne_zero` in each. Keep the
   `let cle := Condition.natLE; cle.check …` lines or drop them — they are accept-set-neutral
   either way, and §5.3's witness family stays available for future use.
2. `lake build` — `Boundaries.lean`'s two branches should go green with **no** change, since they
   are the proofs written against exactly this shape.
3. `build_checker` + `uv run lka.py run --checker lean4lean-local` (note row 120b: `run` does not
   build), and check `init`, `std`, `perf/grind-ring-5`.
4. `scripts/primitive-false-audit.lean` — all eight wrong bodies still rejected.

**Caveat, stated because it is the difference between this working and not.** My cone sizes (238 /
352) disagree with §1's (135 / 147), so one of the two measurements is of a different object. Mine
is the transitive closure over type-and-value in the pinned toolchain's environment; §1's provenance
is not recorded. If §1 measured the arena's `--import <ndjson>` payload and that payload really is
smaller, then `Nat.mod_lt` (for `Nat.gcd`) or `Nat.div_lt_self` (for `Nat.bitwise`) could still be
missing and step 3 would fail with a *different* `unknown constant` — which is itself the useful
answer, and is one arena run away. What is certain either way is that §1's "all six absent" is not
true of the environment `lake env lean` sees, and that the arena's own error message named only
`Nat.pos_of_ne_zero`.

Do **not** discharge the goal by adding an inhabitation hypothesis to `reflects_gcd_of_equations`
or `reflects_bitwise_of_equations`: at the `x = 0` / `n = 0` instances that hypothesis is false, so
the theorem would be vacuous exactly where it matters. Two streams have now stopped here; the
second one (this one) stopped with the counterexample in hand rather than the suspicion.

## 6. Status of the two goals when this was written

Goal 1 **holds and is measured** — arena 185 correct / 6 either / 0 incorrect, from
`build-checker` + `run` against a binary built from this tree, `init` ✅ `std` ✅
`perf/grind-ring-5` ✅, `nested-nonuniform-param` rejected (the flip that proves the new
uniform-occurrence check is reached). That run predates the `Condition.natLE` line, so it must be
repeated. Goal 2 is open: guard 2 prints `INCOMPLETE: sorryAx present`, census 13.
