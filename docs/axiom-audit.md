# Audit of the 32 frozen axioms in `Lean4Lean/Verify/Axioms.lean`

Audited against toolchain **`leanprover/lean4:v4.33.0-rc2`**
(`~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean`) and the C++ kernel
at `~/lean4/src` (master `fd0efc4`).

This document is a **read-only audit**. Nothing in `Lean4Lean/` was changed.
Every "proposed correction" below is a proposal only; `Verify/Axioms.lean` and
`Verify/Guard.lean` remain byte-identical.

---

## 0. Why this matters

`Verify/Guard.lean` check 2 whitelists these 32 axioms **by name**:

```lean
let allowed : NameSet := axiomWhitelist.foldl (·.insert ·) {}
for n in axioms do
  if n == ``sorryAx then sorries := true
  else unless allowed.contains n do throwError "guard VIOLATION: …"
```

The check asks *which* axioms `kernel_sound` uses, never whether that set is
**consistent**. So a whitelisted axiom that proves `False` does not trip any
guard — it makes `kernel_sound` provable *vacuously* while guard 2 prints
"proof COMPLETE, no sorry". The end-to-end theorem would then assert nothing.

Two of the 32 do exactly that, and one of them does it **on its own**:

```
$ lake env lean scratch/A3_alone.lean
'contradiction_alone' depends on axioms: [propext, Quot.sound, Expr.looseBVarRange_eq]

$ lake env lean scratch/B_imax.lean
'contradiction' depends on axioms: [propext, Quot.sound, mkLevelIMaxCore_eq]
```

and, as an immediate corollary, every proposition — including `kernel_sound`'s —
is provable while staying strictly inside the whitelist:

```
theorem anything (P : Prop) : P := contradiction.elim
-- 'anything' depends on axioms: [propext, Quot.sound, Expr.looseBVarRange_eq, Expr.mkData_eq]
```

(that run used the two-axiom version; `A3_alone.lean` shows `Expr.looseBVarRange_eq`
suffices by itself.)

Today this is *latent*, not exploited: `kernel_sound`'s current axiom cone is
`{propext, sorryAx, Classical.choice, Quot.sound}` — `Verify/Soundness.lean`
imports nothing from the refinement layer, so none of the 32 is reachable yet.
The inconsistency is **pre-authorised**, not yet used.

---

## 1. Summary table

Verdicts:

* **inconsistent** — a **machine-checked** proof of `False` exists (alone, or
  with another whitelisted axiom).
* **inconsistent (argued)** — a complete argument for `False` exists but I did
  not mechanise the witness; the missing step is stated explicitly.
* **false** — the axiom does not describe the function that actually runs, but
  no Lean-internal contradiction is derivable (the upstream side is
  `opaque`/`partial`, hence logically unconstrained). Sub-labelled *(runtime)*
  when a `#eval` counterexample exists, *(source)* when the divergence is on an
  input where the C code aborts, so no value can be observed.
* **true** — no counterexample found under differential testing plus a reading
  of the C++/Lean source; the axiom is a faithful description of the
  implementation.
* **true\*** — true only under a side condition that the axiom does not state;
  outside it, the real function aborts the process rather than returning a
  different value.

| # | Axiom | Verdict | One-line reason |
|---|---|---|---|
| 1 | `Std.TreeMap.all_eq_all_toList` | **true — provable now** | `Impl.all_eq_all_toListModel` + `Const.toList_eq_toListModel_map`, one `simp` |
| 2 | `Std.TreeMap.any_eq_any_toList` | **true — provable now** | same, after a 10-line mirror of the upstream `all` lemma |
| 3 | `Lean.PersistentArray.toList'_push` | **false** *(runtime)* | no `WF arr` hypothesis; a malformed `arr` silently drops 32 elements |
| 4 | `Lean.PersistentHashMap.WF.toList'_insert` | true | matches `insertAux`; unprovable while `insertAux` is `partial` |
| 5 | `Lean.PersistentHashMap.WF.find?_eq` | true | matches `findAux`; ditto |
| 6 | `Lean.PersistentHashMap.findAux_isSome` | true | `containsAux` is a clause-for-clause copy of `findAux` |
| 7 | `Lean.Syntax.structEq_eq` | true | `Substring.Raw.Internal.beq` *is* the `BEq Substring.Raw` instance at runtime |
| 8 | `Lean.Level.mkMaxAux_eq` | true | verbatim transcription; `Total.mkMaxAux` is genuinely recursive |
| 9 | `Lean.Level.skipExplicit_eq` | true | verbatim transcription |
| 10 | `Lean.Level.isExplicitSubsumedAux_eq` | true | verbatim transcription |
| 11 | `Lean.Level.normalize_eq` | true | clause-by-clause identical; agrees on 21 523 360 levels |
| 12 | `Lean.Level.mkData_eq` | **false** *(source)* | asserts a *return value* (`0`) where the C function calls `lean_internal_panic` and aborts; jointly inconsistent with 13/14 |
| 13 | `Lean.Level.hasParam_eq` | ~~inconsistent (argued) (with 12)~~ → **consistent, independent, and provable under a side condition** | the argued route needed the *unconditional* 12; with `H : d < 2^24` it is dead. §12.1 exhibits a model of 12+13+14 (machine-checked), a second model of 12 that refutes 13/14 (so 13 is *not* derivable from 12), and `hasParam_eq_of_dep`, which proves 13 outright from 12 under `dep l < 2^24` |
| 14 | `Lean.Level.hasMVar_eq` | ~~inconsistent (argued) (with 12)~~ → same as 13 | see §12.1; `hasMVar_eq_of_dep` |
| 15 | `Lean.Level.instLawfulBEqLevel` | true | C `operator==(level,level)` is exactly structural equality |
| 16 | `Lean.Level.mkLevelIMaxCore_eq` | **INCONSISTENT (alone)** | `mkIMaxCore` has an extra `\|\| u matches .succ .zero` branch upstream does not have |
| 17 | `Lean.Expr.mkData_eq` | **false** *(source)* | same panic-vs-abort mismatch as 12 |
| 18 | `Lean.Expr.mkAppData_eq` | true | matches `lean_expr_mk_app_data`; the `assert!` is unreachable |
| 19 | `Lean.Expr.looseBVarRange_eq` | **INCONSISTENT (alone)** | equates a 20-bit field read (always `< 2²⁰`) with an unbounded model |
| 20 | `Lean.Expr.replace_eq` | true | `lean_replace_expr`'s cache is keyed on pointer and `f?` is pure |
| 21 | `Lean.Expr.liftLooseBVars_eq` | **false — now DELETED** | the `extern "C"` wrapper returns `e` unchanged when `s` or `d` fails `lean_is_scalar`; 0 dependents, so removed rather than weakened (§11.2) |
| 22 | `Lean.Expr.lowerLooseBVars_eq` | true | matches, including the `s < d ⇒ id` wrapper branch |
| 23 | `Lean.Expr.instantiate1_eq` | true | matches `instantiate(a, 1, &e)` exactly |
| 24 | `Lean.Expr.instantiate_eq` | **false** *(runtime)* | `instantiate` is *simultaneous*; `instantiateList` is *sequential* |
| 25 | `Lean.Expr.instantiateRev_eq` | true | `instantiate_rev` indexes `subst[n-1-i]`, i.e. `reverse` |
| 26 | `Lean.Expr.instantiateRange_eq` | true\* | needs `start ≤ stop ≤ subst.size`; otherwise `INTERNAL PANIC` |
| 27 | `Lean.Expr.instantiateRevRange_eq` | true\* | same |
| 28 | `Lean.Expr.abstract_eq` | **false** *(runtime)* | C `abstract` does not shift loose bvars, and resolves duplicates last-wins |
| 29 | `Lean.Expr.abstractRange_eq` | true | `lean_expr_abstract_range` uses `min n xs.size` = `extract 0 n` |
| 30 | `Lean.Expr.hasLooseBVar_eq` | true | matches `has_loose_bvar`, including the non-scalar-index shortcut |
| 31 | `Lean.Expr.eqv_eq` | true | hash/ptr shortcuts are sound; hashes ignore binder names & mdata, as `eqv'` does. **Depends on 15.** |
| 32 | `Lean.Expr.equal_eq` | true | same with `CompareBinderInfo = true` |

**Score, out of 32:**

* **2 inconsistent on their own** — #16, #19. Each proves `False` with no help.
* ~~**3 jointly inconsistent (argued, not mechanised)** — #12 with either of #13,
  #14.~~ **Withdrawn:** the argument needed the *unconditional* #12 and dies with
  the `H : d < 2^24` repair. §12.1 machine-checks a joint model. #13 and #14 are
  now *provable* under a `dep l < 2^24` side condition and can leave the
  whitelist.
* **5 false of the implementation** — #3, #17, #21, #24, #28 (#12 is false in the
  same sense and is already counted above). **#21 has since been deleted** from
  `Verify/Axioms.lean`; the whitelist is now 28.
* **2 true only under a side condition they do not state** — #26, #27.
* **20 true**, of which **2** (#1, #2) are now provable outright from upstream.

---

## 2. Method

Three independent checks were applied to every axiom.

1. **Source reading.** Every upstream definition was read in the pinned
   toolchain source, and every `@[extern]` was followed into `~/lean4/src`
   (`kernel/expr.cpp`, `kernel/instantiate.cpp`, `kernel/abstract.cpp`,
   `kernel/expr_eq_fn.cpp`, `kernel/level.cpp`, `kernel/replace_fn.cpp`).

   > **Correction (see §11.1). Read the wrapper before the worker.** As
   > originally run, this check read the C *worker* functions
   > (`lift_loose_bvars`, `has_loose_bvar`, `instantiate_core`, …) and described
   > them faithfully, but skipped the `extern "C"` wrapper that Lean actually
   > calls — which is where argument validation lives. **For every `@[extern]`
   > axiom, read the wrapper first and enumerate every early return before
   > reading the algorithm.** Any `Nat` argument crossing into C arrives boxed
   > and is therefore *always* `lean_is_scalar`-guarded (the threshold is
   > `LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1`, i.e. `2^63`); the guard either panics
   > or silently substitutes a fallback, and **the fallback is what the axiom
   > has to match**. Seven of the fourteen `Expr`/container axioms sit on such a
   > guard, resolving four different ways (§11.1), and one of them —
   > `liftLooseBVars_eq` — was false because of it and has been deleted.
   >
   > The same discipline applies to `@[extern]`/`@[export]` *name pairings*: an
   > identity that holds only because two C symbols link to each other (§11.8,
   > `Substring.Raw.Internal.beq`) is weaker than a definitional one and can
   > never be discharged by `rfl`. Record which kind you have.
2. **Differential testing** of the compiled function against the pure model, on
   a generated corpus. Scratch files (outside the repo, in the session
   scratchpad):
   * `D_diff.lean` — 1456-expression corpus; `liftLooseBVars`, `lowerLooseBVars`,
     `hasLooseBVar`, `looseBVarRange`, `instantiate1`, `instantiate`,
     `instantiateRev`, `instantiate{,Rev}Range`, `abstract`, `abstractRange`,
     `eqv`, `equal`, `replace`.
   * `E_level.lean` — `normalize` on `gen 3` (21 523 360 levels), plus
     `skipExplicit`, `isExplicitSubsumedAux`, `mkMaxAux`, and `Level.beq`
     against a hand-written structural equality.
   * `I_phm.lean` / `I5.lean` — `PersistentHashMap.find?`/`insert`/`containsAux`
     against the `toList'` model, over maps of up to 300 keys including
     deliberate low-bit-collision key sets (`i*32`), plus malformed hand-built
     `Node`s; and `Syntax.structEq` including two `Substring`s with equal
     content but different backing strings.
3. **Refutation attempts.** Each axiom was checked for (a) a Lean-internal
   contradiction, and (b) a runtime counterexample. Every "true" verdict below
   survived a deliberate attempt to break it; none was granted on inspection
   alone.

A note on what these axioms *can* mean. All the upstream functions involved are
either `opaque` (`@[extern]`) or `partial` — the Lean kernel refuses to unfold
both. So an equation `f = model` is normally *logically consistent whatever the
implementation does*; its only content is fidelity to compiled code. The two
exceptions, and the reason two axioms are outright inconsistent, are:

* `Lean.Level.mkLevelIMaxCore` is a **plain `private def`**, not opaque — so its
  equation is decidable in Lean, and it is false; and
* `Expr.looseBVarRange` is a **transparent field read** of a computed field, so
  it carries a *provable upper bound* that the model violates.

That is a useful rule for future axioms: **never equate a transparent
definition, or a bounded quantity, with an unbounded model.**

---

## 3. The two outright inconsistencies

### 3.1 `Lean.Expr.looseBVarRange_eq` — inconsistent on its own

```lean
/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
@[simp] axiom looseBVarRange_eq (e : Expr) : e.looseBVarRange = e.looseBVarRange'
```

**Claim in plain terms.** The cached `looseBVarRange` field of an `Expr` equals
the structurally-computed loose-bvar range.

**Why it is false.** `Expr.Data` packs `looseBVarRange` into **20 bits**
(`Lean/Expr.lean:127`), and `Expr.Data.looseBVarRange c = (c >>> 44).toUInt32`.
Because `UInt64` has 64 bits, that read is `< 2²⁰` *unconditionally*. The model
`looseBVarRange'` has no such bound: `(Expr.bvar 1048575).looseBVarRange' = 2²⁰`.

Upstream agrees the value is not representable — it refuses to build it:

```cpp
// ~/lean4/src/kernel/expr.cpp:105
extern "C" LEAN_EXPORT uint64_t lean_expr_mk_data(uint64_t hash, object * bvarRange, …) {
    if (!is_scalar(bvarRange)) lean_internal_panic("too many bound variables");
    size_t range = unbox(bvarRange);
    if (range > 1048575) lean_internal_panic("too many bound variables");
```

**Machine-checked witness**, in full (`scratchpad/A3_alone.lean`; self-contained
— it does *not* use `mkData_eq`, and does not use the repo's `bv_decide`-backed
`Data.looseBVarRange_le`, so the axiom cone is minimal):

```lean
import Lean4Lean.Verify.Axioms
open Lean

/-- `Expr.Data.looseBVarRange` reads bits 44..63, so it is always `< 2^20`. -/
theorem range_lt (c : UInt64) : (Expr.Data.looseBVarRange c).toNat < 2^20 := by
  show (UInt64.toUInt32 (UInt64.shiftRight c 44)).toNat < 2^20
  have h64 : c.toNat < 2^64 := c.toNat_lt_size
  have hs : (UInt64.shiftRight c 44).toNat = c.toNat / 2^44 := by
    show (c >>> (44 : UInt64)).toNat = _
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (UInt64.shiftRight c 44).toNat < 2^20 := by rw [hs]; omega
  simp [UInt64.toNat_toUInt32]; omega

theorem contradiction_alone : False := by
  have h1 := range_lt (Expr.bvar 1048575).data
  rw [show Expr.Data.looseBVarRange (Expr.bvar 1048575).data
        = (Expr.looseBVarRange (Expr.bvar 1048575)).toUInt32 from by
      simp [Expr.looseBVarRange]] at h1
  rw [Expr.looseBVarRange_eq] at h1
  simp [Expr.looseBVarRange'] at h1

#print axioms contradiction_alone
-- 'contradiction_alone' depends on axioms: [propext, Quot.sound, Expr.looseBVarRange_eq]
```

The repo's own `Lean.Expr.looseBVarRange_le : looseBVarRange e ≤ 2^20 - 1`
(`Verify/Expr.lean:583`) is the same fact, already proved.

**Is a top-level bound enough as a side condition? No.** The field is computed
bottom-up, so *every subterm's* `mkData` call must be in range. Machine-checked
(`scratchpad/A4_lam.lean`, uses `mkData_eq`):

```lean
def bad : Expr := .lam `x (.bvar 0) (.bvar 1048575) .default

theorem bad_model : bad.looseBVarRange' = 1048575 := by
  simp [bad, Expr.looseBVarRange']                      -- ≤ 2^20-1 ✓

theorem body_data : (Expr.bvar 1048575).data = (0 : UInt64) := by
  show Expr.data (.bvar 1048575) = (0 : UInt64)
  rw [Expr.data, Expr.mkData_eq]
  show Expr.mkData' _ (1048575+1) 0 false false false false = (0 : UInt64)
  unfold Expr.mkData'
  rw [if_neg (by decide)]
  simp only [panicWithPosWithDecl, panic, panicCore]
  rfl

theorem dom_range : (Expr.bvar 0).data.looseBVarRange.toNat = 1 := by
  show (Expr.data (.bvar 0)).looseBVarRange.toNat = 1
  rw [Expr.data]; exact Expr.mkData_looseBVarRange (by decide)

theorem bad_real : bad.looseBVarRange = 1 := by                -- the field says 1
  show (Expr.data (.lam `x (.bvar 0) (.bvar 1048575) .default)).looseBVarRange.toNat = 1
  rw [Expr.data]
  simp only [Expr.mkDataForBinder, body_data, dom_range]
  rw [show Expr.Data.looseBVarRange (0 : UInt64) = 0 from rfl]
  exact Expr.mkData_looseBVarRange (by decide)
```

**Proposed correction.** Add a *per-subterm* side condition:

```lean
/-- Every `bvar` index occurring in `e` fits the 20-bit `looseBVarRange` field,
so the cached range is exact for `e` and every subterm of `e`. -/
def Expr.BVarBounded : Expr → Prop
  | .bvar i          => i + 1 ≤ 2^20 - 1
  | .mdata _ b
  | .proj _ _ b      => b.BVarBounded
  | .app f a         => f.BVarBounded ∧ a.BVarBounded
  | .lam _ t b _
  | .forallE _ t b _ => t.BVarBounded ∧ b.BVarBounded
  | .letE _ t v b _  => t.BVarBounded ∧ v.BVarBounded ∧ b.BVarBounded
  | _                => True

@[simp] axiom looseBVarRange_eq (e : Expr) (h : e.BVarBounded) :
    e.looseBVarRange = e.looseBVarRange'
```

(`.lam`/`.forallE`/`.letE` need only their children checked: the parent's own
`mkData` argument is a `max` of quantities bounded by the children's ranges.)

**What the repair costs.** 4 direct users, including
`Lean4Lean.BetaReduce.cheapBetaReduce`, `TypeChecker.Inner.inferType'.WF` and
`TypeChecker.Inner.isDefEqForall.WF` (it is `@[simp]`, so most uses are implicit
— re-run `J2_usage.lean` for the exact list). Each would acquire a
`BVarBounded` obligation on the expression being checked.

*Is it dischargeable?* Not from anything the repo currently tracks. `TrExprS`
gives `Closed`/`FVarsIn` — every bvar is bound by an enclosing binder — which
bounds a subterm's bvar indices by its **binder depth**, and nothing bounds the
binder depth. Two ways to close it, in increasing order of honesty:

* **(a) Cheapest, and what I recommend.** Make `BVarBounded` a consequence of an
  invariant the refinement layer already has, by bounding the local-context
  length: `TrExprS` relates `e` to a `VExpr` in a `VLCtx` of length `n`, and
  every loose bvar in a subterm at binder depth `d` is `< n + d`. Adding
  `n + depth e ≤ 2^20 - 1` to the `TrExprS`/`VLCtx` well-formedness is a local
  change and discharges `BVarBounded` structurally. It also matches reality:
  a 2²⁰-deep local context cannot be built without the C runtime aborting.
* **(b) Most explicit.** Have `Lean4Lean.addDecl` reject declarations containing
  `bvar i` with `i ≥ 2²⁰ - 1` (an O(size) pass over a term it already
  traverses), and thread the resulting `BVarBounded` as a precondition. Costs a
  new check but makes the assumption visible and testable.

*A tempting repair that is wrong:* replacing the RHS with
`if e.looseBVarRange' ≤ 2^20-1 then e.looseBVarRange' else 0`. That reifies
Lean's `panic! = default` convention, but the C function **aborts** rather than
returning `0` — the corrected axiom would then be a *different* false statement
about the executable (it would claim the checker keeps running with range 0).

**Provable from upstream?** No — `Expr.mkData` is `opaque`, so the field's value
is not derivable in Lean at all. The corrected form is not provable either; it
stays an assumption, but a true one.

---

### 3.2 `Lean.Level.mkLevelIMaxCore_eq` — inconsistent on its own

```lean
@[inline] private def mkIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero || u matches .succ .zero then v     -- ← extra disjunct
  else if u == v then u
  else elseK ()

open private mkLevelIMaxCore from Lean.Level in
/-- Workaround for https://github.com/leanprover/lean4/pull/7631#issuecomment-3289800246 -/
@[simp] axiom mkLevelIMaxCore_eq (e : Expr) (n : Nat) : mkLevelIMaxCore = mkIMaxCore
```

**Why it is false.** Upstream, in the pinned toolchain *and* on `lean4` master
(`src/Lean/Level.lean:542`), has no such disjunct:

```lean
@[inline] private def mkLevelIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero then v
  else if u == v then u
  else elseK ()
```

The workaround anticipated a simplification upstream never adopted. (The
simplification is *semantically* valid — `imax 1 v = v` for every `v` — but that
is not what the function computes.)

`mkLevelIMaxCore` is a plain `private def`, **not** `opaque`, so the equation is
decidable. Take `u = .succ .zero`, `v = .param x`, `elseK = fun _ => .zero`.
`mkIMaxCore` returns `v`; upstream returns `if u == v then u else .zero`. Both
branches of that `if` differ from `v`, so no assumption about `Level.beq` is
needed.

**Machine-checked witness**, in full (`scratchpad/B_imax.lean`):

```lean
import Lean4Lean.Verify.Axioms
open Lean Lean.Level
open private mkLevelIMaxCore from Lean.Level
open private mkIMaxCore from Lean4Lean.Verify.Axioms

def u : Level := .succ .zero
def v : Level := .param `x

theorem model : simpLevelIMax' u v .zero = v := by
  show mkLevelIMaxCore u v (fun _ => .zero) = v
  rw [mkLevelIMaxCore_eq (default : Expr) 0]; show mkIMaxCore u v (fun _ => .zero) = v
  unfold mkIMaxCore; simp [u, v, Level.isNeverZero, Level.isZero]
theorem real : simpLevelIMax' u v .zero = (if u == v then u else .zero) := rfl
theorem contradiction : False := by
  have h := model
  rw [real] at h
  split at h
  · exact absurd h (by intro hh; exact Level.noConfusion hh)
  · exact absurd h (by intro hh; exact Level.noConfusion hh)

#print axioms contradiction
-- 'contradiction' depends on axioms: [propext, Quot.sound, mkLevelIMaxCore_eq]
```

**Proposed correction: delete the axiom.** Make `mkIMaxCore` a verbatim copy and
the equation becomes `rfl`:

```lean
@[inline] private def mkIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero then v
  else if u == v then u
  else elseK ()

open private mkLevelIMaxCore from Lean.Level in
@[simp] theorem mkLevelIMaxCore_eq : mkLevelIMaxCore = mkIMaxCore := rfl
```

Note also that the two binders `(e : Expr) (n : Nat)` in the axiom are entirely
spurious — the statement does not mention them.

**What the repair costs.** **Zero.** The reverse-dependency scan finds
`mkLevelIMaxCore_eq` has **0 direct users** anywhere in the `Lean4Lean` cone. It
can be replaced by the `rfl` theorem, or removed outright, without touching a
single proof.

**Provable from upstream?** The corrected statement, yes — by `rfl`. It should
not be an axiom at all.

---

## 4. `mkData_eq` and the panic branch (axioms 12, 13, 14, 17)

```lean
def Expr.mkData' (h : UInt64) (looseBVarRange : Nat := 0) … : Expr.Data :=
  let approxDepth : UInt8 := if approxDepth > 255 then 255 else approxDepth.toUInt8
  assert! (looseBVarRange ≤ Nat.pow 2 20 - 1)
  …
axiom Expr.mkData_eq : @mkData = @mkData'

def Level.mkData' (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big" else …
axiom Level.mkData_eq : @mkData = @mkData'
```

`assert! c; b` elaborates to `if c then b else panic! …`
(`Lean/Elab/BuiltinNotation.lean:214`), and `panic msg = panicCore msg = default`
(`Init/Prelude.lean:3705`) is a **plain `def`**, so `panic! … = (0 : UInt64)` is
provable. The C functions do not return `0`; they call `lean_internal_panic`,
which **aborts the process**. So in the out-of-range branch both axioms assert a
value the implementation never produces.

**In range, both are faithful.** I checked the arithmetic line by line against
`lean_expr_mk_data` / `lean_level_mk_data`: the `approxDepth > 255` saturation,
the truncation `uint32_t h = hash`, and the shift amounts (32/40/41/42/43/44 for
`Expr`; 32/33/40 for `Level`) all match, and the summands occupy disjoint bit
ranges so `+` behaves as `|||`. `Expr.mkAppData_eq` (#18) likewise matches
`lean_expr_mk_app_data`, and its `assert!` is *unreachable*: its argument is a
`max` of two 20-bit field reads, hence always `≤ 2²⁰-1`. `mixHash` and the C++
`hash(uint64,uint64)` are literally the same function
(`runtime/object.cpp:1866`).

**Consequences.**

* `Expr.mkData_eq` + `Expr.looseBVarRange_eq` ⟹ `False` (`scratchpad/A_mkdata.lean`,
  `[propext, Quot.sound, Expr.looseBVarRange_eq, Expr.mkData_eq]`) — though
  §3.1 shows `looseBVarRange_eq` needs no partner.
* `Level.mkData_eq` + `Level.hasParam_eq` ⟹ `False`. **Argued, not mechanised.**
  Let `L n := .succ^[n] (.param `x)`. For `n ≤ 2²⁴-1` the summands are disjoint,
  so `(L n).data.depth.toNat = n` by induction; at `n = 2²⁴` the guard fires and
  `(L (2^24)).data = default = 0`, whence `hasParam = false` while
  `hasParam' = true`. The single missing lemma is
  `(Level.mkData' h d mv hp).depth.toNat = d` for `d ≤ 16777215` — a pure
  `UInt64` bit fact. **The repo already proves it**:
  `Lean.Level.mkData_depth (H : d < 2^24)` at `Verify/Level.lean:41`. Only the
  16 777 216-step induction and the final step remain; I did not complete it.
  The same argument runs verbatim for `hasMVar_eq`.
  (`hasParam_eq`/`hasMVar_eq` are *not* refutable alone: `hasParam` is a `Bool`
  field read, with no provable bound for the model to violate.)

**Proposed correction — add the range hypothesis to the two `mkData_eq`s:**

```lean
axiom Expr.mkData_eq (h : UInt64) (br : Nat) (d : UInt32) (fv ev lv lp : Bool)
    (H : br ≤ 2^20 - 1) :
    mkData h br d fv ev lv lp = mkData' h br d fv ev lv lp

axiom Level.mkData_eq (h : UInt64) (d : Nat) (mv hp : Bool) (H : d < 2^24) :
    mkData h d mv hp = mkData' h d mv hp
```

**What the repair costs — mostly nothing, because the users already carry the
hypothesis.** Direct users:

| user | already has the bound? |
|---|---|
| `Lean.Level.mkData_depth` (`Verify/Level.lean:41`) | yes — `(H : d < 2 ^ 24)` |
| `Lean.Level.mkData_hasParam` (`:57`) | yes — `(H : d < 2 ^ 24)` |
| `Lean.Level.mkData_hasMVar` (`:72`) | yes — `(H : d < 2 ^ 24)` |
| `Lean.Expr.mkData_flags` (`Verify/Expr.lean:260`) | yes — `(H : br ≤ 2 ^ 20 - 1)` |
| `Lean.Expr.mkData_looseBVarRange` (`Verify/Expr.lean:566`) | yes — `(H : br ≤ 2 ^ 20 - 1)` |
| `Lean.Expr.mkAppData_flag`, `mkAppData_looseBVarRange` | yes — derive `hm` from `Data.looseBVarRange_le` |
| **`Lean.Expr.mkData_flags_of_false`** (`Verify/Expr.lean:305`) | **no** |

The single exception is worth spelling out, because it is exactly the place
where the panic branch is being *used as a fact*:

```lean
private theorem mkData_flags_of_false (br d h) :
    (mkData h br d false false false false).hasFVar = false ∧ … := by
  by_cases H : br ≤ 2 ^ 20 - 1
  · exact mkData_flags H
  · rw [mkData_eq, mkData', if_neg H]     -- ← relies on panic! = 0
    exact ⟨rfl, rfl, rfl, rfl⟩
```

Under the corrected axiom this branch is unavailable and
`mkData_flags_of_false` acquires an `br ≤ 2^20 - 1` hypothesis, which propagates
to its four `_of_false` corollaries and their users (facts like
`Expr.hasFVar (.bvar i) = false`). That obligation is the *same* `BVarBounded`
obligation as §3.1 and should be discharged the same way — which is an argument
for doing §3.1 and §4 as one change rather than two.

---

## 5. The four "false but consistent" axioms

These four mis-describe the compiled function. None yields a Lean contradiction
(the upstream side is `opaque` or `partial`), so the damage is not vacuity — it
is that the verified algorithm is **not the algorithm that runs**.

### 5.1 `Lean.Expr.instantiate_eq` — sequential vs simultaneous

```lean
@[simp] def instantiateList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => instantiateList (instantiate1' e a k) as k

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiate_eq (e : Expr) (subst) :
    e.instantiate subst = e.instantiateList subst.toList
```

`Expr.instantiate` is **simultaneous**: a loose `bvar i` at binding depth `d` is
replaced by `lift_loose_bvars(subst[i-d], d)`, and the loose bvars *inside* the
substituted term are neither re-substituted nor renumbered
(`kernel/instantiate.cpp:54`, and the docstring at `Lean/Expr.lean:1406`).
`instantiateList` re-enters the result of each step, so a loose bvar contributed
by `subst[0]` is substituted again by `subst[1]`.

**Machine-checked counterexample** (`scratchpad/C_eval.lean`):

```
e = .bvar 0,  subst = #[.bvar 0, .sort .zero]
  instantiate     : Lean.Expr.bvar 0
  instantiateList : Lean.Expr.sort (Lean.Level.zero)

e = .app (.bvar 0) (.bvar 1),  subst = #[.app (.const `f []) (.bvar 0), .const `b []]
  instantiate     : (f #0) b
  instantiateList : (f b) b
```

**Proposed correction.**

```lean
@[simp] axiom instantiate_eq (e : Expr) (subst : Array Expr)
    (h : ∀ a ∈ subst, a.looseBVarRange' = 0) :
    e.instantiate subst = e.instantiateList subst.toList
```

Differential testing confirms the two agree for every `e` in the 1456-expression
corpus once all substituends are closed (`instantiate_eq (closed subst): OK`).
The alternative — rewriting the RHS as a genuinely simultaneous model — is
strictly more work, because the repo has a substantial `instantiateList_*` lemma
library (`Verify/TypeChecker/InferType.lean`, `IsDefEq.lean`) built on the
sequential shape.

**What the repair costs.** 8 direct users, all in the `TypeChecker` WF proofs
(`inferLambda.loop.WF`, `inferLet.loop.WF`, `inferForall.loop.WF`,
`whnfCore'.WF`, …); `instantiateRev_eq` (7 users) reduces to it. The substituends
at those sites are (a) `fvars` arrays — trivially closed — and (b) application
spine arguments in `inferApp`/beta reduction, which are closed under the
standing "the checked term has no loose bvars" invariant that `TrExprS` already
provides. `Verify/TypeChecker/InferType.lean:259` already invokes exactly this
fact (`ha0.looseBVarRange_zero`). **Dischargeable, mechanically.**

**Provable from upstream?** No — `Expr.instantiate` is `opaque`.

### 5.2 `Lean.Expr.abstract_eq` — two independent errors

```lean
def abstract1 (v : FVarId) : Expr → (k :_:= 0) → Expr
  | .bvar i, d => .bvar (if i < d then i else i + 1)      -- ← shifts loose bvars
  | e@(.fvar v'), d => if v == v' then .bvar d else e
  …
@[simp] axiom abstract_eq (e : Expr) (xs : List FVarId) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs
```

The C `abstract` (`kernel/abstract.cpp:38`) rewrites **only** `fvar`/`mvar`
nodes; `bvar`s fall through untouched. It also short-circuits
`if (!has_fvar(e) && !has_mvar(e)) return e;`. And on duplicates it scans
`i = n-1 … 0` and returns the **last** match, whereas sequential `abstract1`
gives the first-abstracted variable the *highest* index.

**Machine-checked counterexamples** (`scratchpad/C_eval.lean`):

```
e = .app (.fvar x) (.bvar 0),  xs = [x]
  abstract     : .app (.bvar 0) (.bvar 0)     -- variable capture
  abstractList : .app (.bvar 0) (.bvar 1)

e = .bvar 0, xs = [x]         abstract: .bvar 0   abstractList: .bvar 1
e = .fvar x, xs = [x, x]      abstract: .bvar 0   abstractList: .bvar 1
```

**Proposed correction.**

```lean
@[simp] axiom abstract_eq (e : Expr) (xs : List FVarId)
    (he : e.looseBVarRange' = 0) (hx : xs.Nodup) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs
```

Differential testing over the 1456-expression corpus restricted to
loose-bvar-free `e` and nodup `xs` passes
(`abstract_eq (closed e, nodup xs): OK`).

**What the repair costs.** 1 direct user, `Lean.LocalContext.mkBinding_eq`
(`Verify/LocalContext.lean:44`), which also consumes `abstractRange_eq` and
`hasLooseBVar_eq`. The `xs` there are the local context's fvars, and
`Lean4Lean/Std/NodupKeys.lean` plus `LocalContext.WF.nodup` already supply
nodup-ness. `he` follows from the same `Closed` invariant as §5.1.
**Dischargeable**, though it means threading `LocalContext.WF` into
`mkBinding_eq`, which currently takes no well-formedness argument.

The `Nodup` half is worth stating even if `he` is dropped: it is the difference
between `abstract` binding the *outermost* and the *innermost* occurrence of a
repeated variable, which changes the meaning of a constructed binder.

**Provable from upstream?** No — `Expr.abstract` is `opaque`.

### 5.3 `Lean.PersistentArray.toList'_push` — missing `WF`

```lean
/-- We cannot prove this because `insertNewLeaf` is partial -/
@[simp] axiom toList'_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).toList' = arr.toList' ++ [x]
```

Its neighbour in the same file takes the hypothesis this one omits:

```lean
@[simp] theorem WF.toList'_length (h : WF arr) : arr.toList'.length = arr.size
```

`insertNewLeaf`'s last clause is `| n, _, _, _ => n  -- unreachable`, reached
whenever the root is a `leaf`. `mkNewTail` then also sets `tail := #[]`, so the
whole tail is discarded.

**Machine-checked counterexample** (`scratchpad/C_eval.lean`; `flat` is a
computable mirror of `PersistentArrayNode.toList'`):

```lean
def bad : PersistentArray Nat :=
  { root := .leaf #[], tail := Array.replicate 31 (7:Nat), size := 31, shift := 5, tailOff := 0 }
-- (bad.push 99).toList' = []
-- bad.toList' ++ [99]   = [7,7,…,7,99]   (32 elements)
```

**Proposed correction.**

```lean
@[simp] axiom WF.toList'_push {α} {arr : PersistentArray α} (h : WF arr) (x : α) :
    (arr.push x).toList' = arr.toList' ++ [x]
```

**What the repair costs.** 6 direct users
(`TypeChecker.MLCtx.WF.decls_size`, `MLCtx.WF.toList_eq`,
`LocalContext.WF.nodup`, `PersistentArray.WF.toList'_length` itself, …). All of
them are already in a `WF` context: `Verify/LocalContext.lean:132` proves
`WF.decls_wf : lctx.WF → lctx.decls.WF`, and `WF.toList'_length` is by induction
on the very `WF` derivation. **Dischargeable, and cheap** — the change is
`simp [toList'_push]` → `simp [h.decls_wf.toList'_push]` at each site.

**Provable from upstream?** No — `insertNewLeaf`, `mkNewPath` are still
`partial` in v4.33.0-rc2 (`Lean/Data/PersistentArray.lean:109,115`).

### 5.4 `Lean.Expr.mkData_eq` / `Lean.Level.mkData_eq`

Covered in §4.

---

## 6. Two axioms stated at the wrong generality

```lean
@[simp] axiom instantiateRange_eq (e : Expr) (subst) :
    e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)
@[simp] axiom instantiateRevRange_eq (e : Expr) (subst) :
    e.instantiateRevRange start stop subst = e.instantiateRev (subst.extract start stop)
```

The C wrappers *panic* — that is, abort — when the range is bad:

```cpp
// kernel/instantiate.cpp:82
if (b > e || e > sz) lean_internal_panic("invalid range for Expr.instantiateRange");
```

whereas `Array.extract` clamps, so the model returns a value. Confirmed
(`scratchpad/K_panic.lean`):

```
INTERNAL PANIC: invalid range for Expr.instantiateRange
"model: Lean.Expr.bvar 0"
```

Inside the range both are exact — `lean_expr_instantiate_range` literally calls
the core with `(e - b)` entries starting at `subst + b`, and differential
testing over the corpus passes (`instantiateRange_eq: OK`,
`instantiateRevRange_eq: OK`).

This is *not* a soundness hole by itself: an aborted process accepts nothing.
But it is a false statement about the executable, and it is the kind of thing
that should not be silently assumed.

**Proposed correction.**

```lean
@[simp] axiom instantiateRange_eq (e : Expr) (subst : Array Expr)
    (h₁ : start ≤ stop) (h₂ : stop ≤ subst.size) :
    e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)
```

(and the same two hypotheses on `instantiateRevRange_eq`).

**What the repair costs.** 1 direct user each
(`TypeChecker.Inner.whnfCore'.WF`, `TypeChecker.Inner.inferApp.loop.WF`),
corresponding to `TypeChecker.lean:197,201,389` and `Inductive/Add.lean:626`.
At every one of those sites the bound is immediate — the stop index is either
`args.size` or an index the surrounding loop already bounds by it.
**Dischargeable, trivially.**

---

## 7. The 22 axioms that survived

Grouped by what makes them true, with the refutation attempt that failed noted.

### 7.1 `Expr` bit-twiddling and traversal (18, 20–23, 25, 29–32)

| axiom | evidence |
|---|---|
| `mkAppData_eq` | Matches `lean_expr_mk_app_data` (`kernel/expr.cpp:120`) field by field. The `assert!` is unreachable (its argument is a `max` of 20-bit reads). `mixHash` ≡ C++ `hash(uint64,uint64)` (`runtime/object.cpp:1866`). |
| `replace_eq` | `lean_replace_expr` = `replace_fn` with a pointer-keyed cache (`kernel/replace_fn.cpp:151`). The cache is sound because `f? : Expr → Option Expr` is a pure Lean function; the node rebuild (`update_mdata`/`update_proj`/`update_app`/`update_binding`/`update_let`) matches `replaceNoCache`'s `update*!`. Corpus test OK. |
| `liftLooseBVars_eq` | Matches `lift_loose_bvars` including the `d = 0 ⇒ id` and non-scalar-argument shortcuts. 1456×3×3 test OK. |
| `lowerLooseBVars_eq` | Matches, including the wrapper's `if (lean_unbox(s) < lean_unbox(d)) return e;` which the model reproduces as `if s < d then e`. 1456×4×4 test OK. |
| `instantiate1_eq` | `lean_expr_instantiate1` = `instantiate(a, 1, &e)`; at depth `d`, `bvar d ↦ lift(subst, d)`, `bvar i>d ↦ bvar (i-1)`. 1456×~100 test OK. |
| `instantiateRev_eq` | `instantiate_rev` indexes `subst[n - (vidx-offset) - 1]`, i.e. exactly `reverse`. Test OK **including** substituends with loose bvars (both sides are the C function). |
| `abstractRange_eq` | `lean_expr_abstract_range` uses `min(n, size)` entries, which is `xs.extract 0 n`. No panic path. Test OK. |
| `hasLooseBVar_eq` | Matches `has_loose_bvar` (`kernel/expr.cpp:389`); the `!lean_is_scalar(i) ⇒ false` path agrees with the model because no `bvar` index can be that large. Test OK. |
| `eqv_eq` | `expr_eq_fn<false>` is structural, modulo three shortcuts, all sound: `is_eqp` (pointer ⇒ equal); `hash(a) != hash(b) ⇒ false` — sound because the cached hash never depends on binder names, binder info, the `letE` `nondep` flag, or the `mdata` `KVMap` (see the `data` computed field, `Lean/Expr.lean:480–510`), which are exactly the fields `eqv'` ignores or compares separately; and the "optimistic" `check_cache`, which is sound because a `false` result short-circuits the whole `&&`-chain before the pair can be revisited. 1456² test OK. |
| `equal_eq` | Same with `CompareBinderInfo = true`; binder names/info and `letE` names are compared, exactly as `eqv' (strict := true)`. 1456² test OK. |

**Caveat on `eqv_eq`/`equal_eq`:** their truth *depends on* `instLawfulBEqLevel`.
The `Const` case compares level lists with `Level.beq`; if `beq` could return
`true` for structurally different levels, their hashes could differ and the C
hash shortcut would return `false` where `eqv'` returns `true`. This dependency
is not recorded anywhere.

### 7.2 `Level` (8–11, 15)

| axiom | evidence |
|---|---|
| `mkMaxAux_eq`, `skipExplicit_eq`, `isExplicitSubsumedAux_eq` | Verbatim clause-for-clause transcriptions of the three `private partial def`s at `Lean/Level.lean:339,359,375`. I confirmed with `#print` that the `Total.*` copies are **genuinely recursive** (`WellFounded.Nat.fix (fun x => lvls.size - x)`, `._unary`) — Lean inferred the termination measures — so these are real totality claims, not just unfolding equations. Tested over ~1600-element `Array Level` inputs. |
| `normalize_eq` | Clause-by-clause identical to `partial def normalize` (`Lean/Level.lean:381`). One structural difference is benign: upstream's `getMaxArgsAux` takes `normalize` as a parameter, so `Total.getMaxArgsAux`'s 3-argument call cannot resolve to it, and `#print` confirms `Total.normalize._mutual` calls `Total.mkMaxAux` and `Total.skipExplicit` (so `normalize_eq` *depends on* those two axioms). It uses upstream's `isExplicitSubsumed` and `accMax`, which are total. **Tested on `gen 3` = 21 523 360 levels: OK.** Since the axiom equates a `partial def` with a total function, it also asserts termination; the `Total.normalize` termination proof plus identical clauses is the argument, and the 21.5M-case test is the evidence. |
| `instLawfulBEqLevel` | `Level.beq` is `@[extern "lean_level_eq"] opaque`, so this is irreducibly an assumption. C `operator==(level,level)` (`kernel/level.cpp:125`) is exactly structural equality: the `kind`, `hash` and `get_depth` early-outs only reject, and a structurally equal pair agrees on all three (they are computed fields of the structure); `Param`/`MVar` compare names structurally. Tested `Level.beq` against a hand-written structural equality on 3280² pairs: OK. |

### 7.3 Data structures and `Syntax` (4–7)

| axiom | evidence |
|---|---|
| `PersistentHashMap.findAux_isSome` | `containsAux` (`:229`) is a clause-for-clause copy of `findAux` (`:157`), and `containsAtAux`/`findAtAux` likewise. Both use `entries[j]!` with the same `Inhabited` default on out-of-range, so even malformed nodes agree. Tested on built maps **and** on hand-built malformed `Node`s (all-`entry` arrays, mis-placed `ref`s, duplicate-key and empty `collision`s): `findAux_isSome: OK (11 nodes x 60 keys x 4 shifts)`. Under-sized `entries` arrays were checked separately and also agree — both functions take the same `getElem!` panic path and both return `false`/`none`. This one needs no `WF` and is stated at the right generality. |
| `PersistentHashMap.WF.find?_eq` | The `WF` hypothesis (`empty`/`insert`) is exactly what is needed: it guarantees at most one entry per `==`-class, so `findAux`'s "stop at the first `Entry.entry`" is complete and `List.lookup`'s "first match" is unambiguous. `PartialEquivBEq` + `LawfulHashable` are needed and are present. Tested on maps up to 300 keys including a key set engineered to collide in the low 35 bits: OK. |
| `PersistentHashMap.WF.toList'_insert` | Matches `insertAux`, including the collision-node split at `maxCollisions = 4` and the `depth ≥ maxDepth = 7` cutoff. Tested as a multiset equality over the same corpus: OK. |
| `Syntax.structEq_eq` | The only textual divergence from upstream (`Init/Meta/Defs.lean:520`) is that `structEq'` writes `rawVal == rawVal'` where upstream writes `Substring.Raw.Internal.beq rawVal rawVal'`. These are the same function at runtime: `Internal.beq` is `@[extern "lean_substring_beq"] opaque` (`Init/Data/String/Bootstrap.lean:192`) and `lean_substring_beq` is the `@[export]` of `Substring.Raw.beq`, which is the `BEq Substring.Raw` instance (`Substring.lean:457,463,466`). The `node` clause matches via the file's own `structEq'_node` theorem. Tested including two `Substring`s with equal content but different backing strings: OK. |

---

## 8. Free wins — two axioms are provable today

`Std.TreeMap.all_eq_all_toList` and `any_eq_any_toList` cite
[lean4#12798](https://github.com/leanprover/lean4/issues/12798). Upstream has
since added `Std.DTreeMap.Internal.Impl.all_eq_all_toListModel`
(`Std/Data/DTreeMap/Internal/WF/Lemmas.lean:1907`) and
`Impl.Const.toList_eq_toListModel_map`. Both axioms follow.

Verified (`scratchpad/F_treemap.lean`), no axioms beyond the standard three:

```lean
import Std.Data.DTreeMap.Internal.WF.Lemmas

theorem all_eq_all_toList' {p : α → β → Bool} :
    t.all p = t.toList.all fun a => p a.1 a.2 := by
  simp [TreeMap.all, TreeMap.toList, DTreeMap.all, DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.all_eq_all_toListModel,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, Function.comp_def]
-- 'all_eq_all_toList'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`any` needs a 10-line mirror of upstream's lemma first (upstream proved only the
`all` form):

```lean
namespace Std.DTreeMap.Internal.Impl
theorem any_eq_any_toListModel {p : (a : α) → β a → Bool} {m : Impl α β} :
    m.any p = m.toListModel.any (fun x => p x.1 x.2) := by
  simp [any, ForIn.forIn, Id.run_bind]
  rw [forIn_eq_forIn_toListModel, ← toList_eq_toListModel, forIn_eq_forIn']
  induction m.toList with
  | nil => simp
  | cons hd tl ih =>
    simp only [forIn'_eq_forIn, List.any_cons]
    by_cases h : p hd.fst hd.snd = true
    · simp [h]
    · simp only [forIn'_eq_forIn] at ih
      simp [h, ih]
end Std.DTreeMap.Internal.Impl
```

(No `Ord α` instance on the helper — upstream's `all` lemma has none, and adding
one prevents `simp` from matching.)

**Cost:** the 9 users (5 for `all`, 4 for `any`, all in
`Verify/Level.lean`'s `Normalize.NormLevel`) are unaffected — an axiom becoming
a theorem of the same statement is transparent to them. Requires importing
`Std.Data.DTreeMap.Internal.WF.Lemmas`.

**This shrinks the trusted base from 32 to 30 at zero proof cost.**

Everything else was re-checked against the current toolchain and is still
necessary: `PersistentHashMap.{insertAux, findAux, containsAux}`,
`PersistentArray.{insertNewLeaf, mkNewPath}`, `Syntax.structEq` and
`Level.{normalize, mkMaxAux, skipExplicit, isExplicitSubsumedAux}` are all still
`partial`, and every `Expr`/`Level` primitive involved is still
`@[extern] opaque`. `mkLevelIMaxCore_eq` (§3.2) is the one further axiom that
can be deleted — after the extra branch is removed it is `rfl`.

---

## 9. Adjacent finding: 9 unwhitelisted axioms already in the checker's cone

Guard check 1 enumerates axioms **declared in module `Lean4Lean.Verify.Axioms`**
only. A scan of all `Lean4Lean.*` modules finds **nine more axioms** that no
guard currently sees:

```
Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7
Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9
Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8
_private.Lean4Lean.Verify.Expr.0.Lean.Expr.mkData_flags._native.bv_decide.ax_1_12
Lean.Level.mkData_depth._native.bv_decide.ax_1_9
Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8
Lean.Level.mkData_hasMVar._native.bv_decide.ax_1_8
Lean4Lean.ptrEqExpr_eq
Lean4Lean.ptrEqConstantInfo_eq
```

* The seven `_native.bv_decide.ax_*` come from `bv_decide` in
  `Verify/Expr.lean` and `Verify/Level.lean` (7 call sites). They put an
  external SAT solver + LRAT certificate check into the trusted base.
* `Lean4Lean.ptrEqExpr_eq : ptrEqExpr a b → a = b` and
  `ptrEqConstantInfo_eq` (`Lean4Lean/PtrEq.lean:17,22`) are the pointer-equality
  assumptions, used by `EquivManager.isEquiv`, `TypeChecker.lean:739,851,876`
  and `Verify/TypeChecker/IsDefEq.lean:384`. They are **true** — physical
  equality implies structural equality — and unavoidable given
  `ptrAddrUnsafe`; the file's own comment already documents the failure mode
  (the kernel becomes *more* rejecting, never more accepting, if addresses
  differ spuriously).

None of the nine is in `axiomWhitelist`. They are invisible today only because
`kernel_sound` is `sorry` and does not import the refinement layer. **The moment
the proof is wired up, guard 2 will fail on all nine.** That should be
anticipated now rather than discovered as a surprise at the finish line: either
the seven `bv_decide` uses are replaced by kernel-checked bit reasoning
(`decide`/`omega`/`Nat`-level arithmetic — these are all small, fixed-width
facts), or the whitelist is deliberately extended with sign-off.

Note also that guard 1's "exactly 32" check reads *only* `Verify/Axioms.lean`,
so it cannot detect a new `axiom` added anywhere else in the repo. That is a gap
in the guard, independent of the axioms themselves.

---

## 10. Prioritised actions

**P0 — restore non-vacuity. Nothing downstream is meaningful until these land.**

1. **`Lean.Expr.looseBVarRange_eq`** (§3.1). Proves `False` alone. Add the
   per-subterm `BVarBounded` side condition, and discharge it from a
   local-context-length bound in `TrExprS`/`VLCtx` (option (a)). *This is the
   single most urgent item in the repo's trusted base.*
2. **`Lean.Level.mkLevelIMaxCore_eq`** (§3.2). Proves `False` alone. Delete the
   spurious `|| u matches .succ .zero` disjunct; the axiom then becomes `rfl`
   and can be removed. **Zero users — this is a free fix.**
3. **`Lean.Expr.mkData_eq` and `Lean.Level.mkData_eq`** (§4). Add the range
   hypotheses. Five of the six users already carry them; the sixth,
   `mkData_flags_of_false`, is repaired by the same `BVarBounded` work as (1),
   so do (1) and (3) together.
4. Complete the `Level.mkData_eq` + `hasParam_eq` refutation, or accept the
   argument in §4 — either way (3) fixes it.

**P1 — make the verified algorithm the algorithm that runs.**

5. **`Lean.Expr.instantiate_eq`** (§5.1). Add `∀ a ∈ subst, a.looseBVarRange' = 0`.
   8 users; obligations already available at every site.
6. **`Lean.Expr.abstract_eq`** (§5.2). Add `e.looseBVarRange' = 0` and
   `xs.Nodup`. 1 user; needs `LocalContext.WF` threaded into `mkBinding_eq`.
7. **`Lean.PersistentArray.toList'_push`** (§5.3). Add `WF arr`. 6 users, all of
   which already have a `WF` in scope via `LocalContext.WF.decls_wf`.
8. **`instantiateRange_eq` / `instantiateRevRange_eq`** (§6). Add
   `start ≤ stop ≤ subst.size`. 2 users; trivially dischargeable.

**P2 — shrink the trusted base and close the guard's blind spots.**

9. Prove and delete `Std.TreeMap.{all,any}_eq_all_toList` (§8). 32 → 30.
10. Delete `mkLevelIMaxCore_eq` after (2). 30 → 29.
11. Replace the seven `bv_decide` calls in `Verify/{Expr,Level}.lean` with
    kernel-checked reasoning, or whitelist their axioms explicitly (§9).
12. Extend guard 1 to scan **all** `Lean4Lean.*` modules for `axiom`
    declarations, not just `Verify/Axioms.lean` (§9). As written it cannot see a
    new axiom introduced anywhere else in the repo.
13. Record that `eqv_eq`/`equal_eq` depend on `instLawfulBEqLevel` (§7.1), so
    that a future weakening of the latter is not made in isolation.

**P3 — a rule for future axioms.** The two outright inconsistencies share one
cause: an equation between a model and something that is **not opaque** — a
plain `def` (`mkLevelIMaxCore`) or a transparent, provably-bounded field read
(`looseBVarRange`). An axiom about an `@[extern] opaque` or `partial` constant
can only ever be *wrong about the implementation*; an axiom about a transparent
one can be *wrong about mathematics*. Before adding any axiom, check that its
left-hand side is genuinely opaque, and that no bound provable about the
left-hand side is violated by the right.

---

## 11. Reproduction

All scratch files are outside the repo, in this session's scratchpad
(`/tmp/claude-1000/-home-vasilii-lean4lean/…/scratchpad/`). Run each with

```
export PATH="$HOME/.elan/bin:$PATH"
cd ~/lean4lean && lake env lean <file>
```

| file | what it shows |
|---|---|
| `A3_alone.lean` | `False` from `Expr.looseBVarRange_eq` alone |
| `A_mkdata.lean` | `False` from `looseBVarRange_eq` + `mkData_eq`; and `anything (P : Prop) : P` |
| `A4_lam.lean` | a top-level range bound is not a sufficient side condition |
| `B_imax.lean` | `False` from `mkLevelIMaxCore_eq` alone |
| `C_eval.lean` | runtime counterexamples for `instantiate_eq`, `abstract_eq`, `toList'_push` |
| `D_diff.lean` | differential test, 14 `Expr` axioms, 1456-expression corpus |
| `E_level.lean` | differential test, 5 `Level` axioms, up to 21 523 360 levels |
| `I_phm.lean` | differential test, `WF.find?_eq`, `WF.toList'_insert`, `structEq_eq` |
| `I5.lean` | differential test, `findAux_isSome`, incl. malformed nodes |
| `F_treemap.lean` | proofs of the two `Std.TreeMap` axioms |
| `K_panic.lean` | `instantiateRange` aborts out of range |
| `J2_usage.lean` | reverse-dependency scan: users of each axiom, and the 9 unwhitelisted axioms |

---

## 11. Adversarial pass on the `Expr` axioms: the `lean_is_scalar` guard class

*Scope of this pass: the `Expr` axioms (17, 18, 20–32) and the container axioms
(3–7). The `Level` section (8–16) and `Std.TreeMap` (1, 2) belong to other
streams and were not touched.*

The pass was run as an attempt to **derive `False`**, not to re-confirm verdicts.
It did not find an inconsistency. It found one **false axiom** and a systematic
gap in how §7.1 read the C entry points, plus three failed attacks worth
recording so they are not re-run.

### 11.1 The finding: every `Nat` argument crossing into C is bignum-guarded first

Each `@[extern]` C entry point in scope that takes a `Nat` begins with a
`lean_is_scalar` test — *before* the range test §6 and §7.1 record.
`LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1`, so the guard fires at `2^63` on 64-bit.

| axiom | C guard (verbatim) | fallback | consequence |
|---|---|---|---|
| 21 `liftLooseBVars_eq` | `if (!lean_is_scalar(s) \|\| !lean_is_scalar(d))` | `return e;` | **FALSE** — see 11.2 |
| 22 `lowerLooseBVars_eq` | `if (!lean_is_scalar(s) \|\| !lean_is_scalar(d) \|\| unbox(s) < unbox(d))` | `return e;` | attack fails — 11.3 |
| 30 `hasLooseBVar_eq` | `if (!lean_is_scalar(i))` | `return false;` | attack fails — 11.3 |
| 29 `abstractRange_eq` | `if (!lean_is_scalar(n))` | `abstract_core(e, array_size(subst), subst)` | attack fails — 11.4 |
| 26 `instantiateRange_eq` | `if (!lean_is_scalar(begin) \|\| !lean_is_scalar(end))` | **`lean_internal_panic`** | side condition insufficient — 11.5 |
| 27 `instantiateRevRange_eq` | same | **`lean_internal_panic`** | same |
| 17 `Expr.mkData_eq` | `if (!is_scalar(bvarRange)) panic` *and* `if (range > 1048575) panic` | — | **covered** — 11.6 |

§6 describes `lean_expr_instantiate_range` as *"starts with
`if (b > e || e > sz) lean_internal_panic(...)`"*. That is the **second**
statement of the function, not the first.

> **Method note — read the entry point, not the worker.** This is the failure
> this project keeps hitting: a reading that is accurate about what it looked at
> and silent about what came before it. §7.1's entries describe the *worker*
> functions (`lift_loose_bvars`, `has_loose_bvar`, `instantiate_core`) faithfully;
> what they skip is the `extern "C"` wrapper, which is where argument validation
> lives. **For any `@[extern]` axiom, read the wrapper first and enumerate every
> early return before reading the algorithm.** A `Nat` argument crossing into C is
> boxed, so it is *always* bignum-guarded; the guard either panics or silently
> substitutes a fallback value, and the fallback is what the axiom has to match.
> Seven of the fourteen axioms in this scope sit on such a guard.

### 11.2 Axiom 21 `Lean.Expr.liftLooseBVars_eq` is **false**

```c
extern "C" LEAN_EXPORT object * lean_expr_lift_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d)) { lean_inc(e); return e; }
    return lift_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
}
```

Witness `e := .bvar 0`, `s := 0`, `d := 2^63`. Both halves are machine-checked,
and they are **different kinds of evidence**:

* **C side — differential test, compiled code.** `#eval` runs the `@[extern]`
  implementation:
  `#eval idx ((Expr.bvar 0).liftLooseBVars 0 (2^63))` prints `"bvar 0"`.
* **Model side — kernel reduction, no compilation.**
  `theorem : Expr.liftLooseBVars' (.bvar 0) 0 (2^63) = .bvar (2^63)` by `simp`,
  and `… ≠ .bvar 0`. (`decide`/`simp` only; **no `native_decide`** anywhere in
  this pass.)

So the axiom asserts `.bvar 0 = .bvar (2^63)`.

What makes this worse than 26/27: **the call completes.** There is no panic and
no unrepresentable input — `2^63` is an ordinary `Nat` literal and `.bvar 0` an
ordinary `Expr`. Only the *model's output* is not runtime-constructible, which is
why the disagreement cannot be exhibited by evaluating both sides at once
(`#eval` of the model's answer trips `lean_expr_mk_data`'s own panic,
`INTERNAL PANIC: too many bound variables` — observed).

**Not an inconsistency.** `Expr.liftLooseBVars` is `opaque @[extern]`, and a
search of the toolchain source found **no theorem anywhere in core about it**, so
there is no second fact to contradict. This is the same category as 12/17: an
equation asserted on a branch the implementation handles differently.

#### The fix: **delete the axiom**, do not patch it

The choice between `d < 2^63` and a `USize` restatement was to be made on which
one the consumers satisfy without new work. Measuring that answered a different
question: **there are no consumers.**

A scan of every non-internal `Lean4Lean.*` declaration, collecting each one's
axiom cone (`Lean.collectAxioms`), gives:

| axiom | dependent `Lean4Lean` declarations |
|---|---|
| **`Lean.Expr.liftLooseBVars_eq`** | **0** |
| `Lean.Expr.instantiateRange_eq` | 35 |
| `Lean.Expr.lowerLooseBVars_eq` | 41 |
| `Lean.Expr.hasLooseBVar_eq` | 41 |
| `Lean.Expr.abstractRange_eq` | 41 |
| `Lean.Expr.instantiateRevRange_eq` | 43 |
| `Lean.Expr.replace_eq` | 44 |
| `Lean.Expr.mkData_eq`, `mkAppData_eq` | 48 each |
| `Lean.Syntax.structEq_eq` | 66 |
| `Lean.PersistentArray.WF.toList'_push` | 113 |
| `Lean.PersistentHashMap.findAux_isSome` | 105 |
| `Lean.PersistentHashMap.WF.toList'_insert`, `WF.find?_eq` | 162 each |

`liftLooseBVars_eq` is the only one at zero, and it is zero for a structural
reason, not by accident: **the checker never calls `Expr.liftLooseBVars`.** A
reverse scan finds no occurrence of `liftLooseBVars` or `lowerLooseBVars` outside
`Verify/` and `Experimental/`, and the only textual matches inside `Verify/` are
`liftLooseBVars_eq_self`, `liftLooseBVars_zero` and `liftLooseBVars_add` — all
theorems about the **model** `liftLooseBVars'`, none about the opaque constant.
The axiom is `@[simp]`, so it has no explicit call sites either way; the cone
scan is what settles it, because a `@[simp]` lemma that fires does appear in the
proof term.

So deleting it cannot break a proof, and it removes a live false axiom rather
than domesticating one. `CLAUDE.md` counts shrinking the whitelist as progress;
this is the rare case where the correct fix is subtraction.

*Fallback, if the reviewer prefers to keep the statement for future use:* the C
guard is `!lean_is_scalar(s) || !lean_is_scalar(d)`, so **both** arguments must be
bounded — the hypothesis is `s < 2^63 ∧ d < 2^63`, not `d < 2^63` alone. A `USize`
restatement does not fit without changing the signature, since
`Expr.liftLooseBVars : Expr → Nat → Nat → Expr`.

*Either way this is a frozen-file change and needs sign-off.*

### 11.3 Failed attacks: axioms 22 and 30

Both carry the same guard, and both **survive**, for the same reason: the C
fallback coincides with the model on every input a real `Expr` can supply.

* **22.** The fallback is `return e`. With `s` non-scalar, every bvar index in a
  constructible `e` is `< 2^20 < s`, so the model's `if i < s then i` also
  leaves the term alone. Machine-checked:
  `∀ i, i < 2^63 → lowerLooseBVars' (.bvar i) (2^63) 1 = .bvar i`. The other
  three sign patterns (`s` scalar/`d` non-scalar, both non-scalar, `s < d`) all
  land in the model's own `if s < d then e` branch.
  *An earlier witness of mine, `(.bvar 7).lowerLooseBVars (2^63) 1`, was wrong:*
  `#eval` returned `bvar 7` and so does the model.
* **30.** The fallback is `return false`. For non-scalar `i`, no constructible
  `e` contains `.bvar i`, so the model also returns `false`. Machine-checked:
  `∀ i n, i ≠ n → hasLooseBVar' (.bvar i) n = false`. §7.1's entry already said
  "including the non-scalar-index shortcut"; this confirms it.

Both disagree only at `.bvar i` with `i ≥ 2^63`, which `lean_expr_mk_data`
refuses to build.

### 11.4 Failed attack: axiom 29 `abstractRange_eq`

The only unconditional range axiom, and the guard is present — but the fallback
is `lean_expr_abstract_core(e, lean_array_size(subst), subst)`, i.e. *the whole
array*, and `Array.extract 0 n` clamps to the whole array for `n ≥ size`. The two
agree at **every** input, logical or not. §7.1's verdict stands; the reason is
the clamp, which §7.1 did not state.

### 11.5 Axioms 26/27: the side condition is necessary but **not sufficient**

`h₁ : start ≤ stop` and `h₂ : stop ≤ subst.size` exclude the second guard
(`b > e || e > sz`). They do **not** exclude the first: `stop` may be non-scalar
provided `subst.size` is too. That requires `subst.size ≥ 2^63`, which is
expressible (`⟨List.replicate (2^63) e⟩`) though not constructible — so this is
strictly weaker than 11.2, where the witness is an ordinary literal.

*Suggested fix (frozen file — needs sign-off):* strengthen `h₂` to
`stop ≤ subst.size ∧ subst.size < 2^63`, or state the axiom over `USize`.

### 11.6 Axiom 17 `Expr.mkData_eq`: the Level-side consequence does **not** carry over

The question §4 raises for the `Expr` twin is answered: `lean_expr_mk_data`
panics twice — `if (!is_scalar(bvarRange))` and `if (range > 1048575)` — and the
axiom's hypothesis `H : br ≤ 2^20 - 1` implies **both** are passed. The
`approxDepth` clamp matches too (`if (approxDepth > 255) approxDepth = 255`
against the model's `if approxDepth > 255 then 255 else …`). Unlike 12, which was
jointly inconsistent with 13/14, the `Expr` `mkData_eq` is correctly guarded and
no analogous consequence exists.

### 11.7 Axiom 3 `PersistentArray.toList'_push`: the `WF` hypothesis is adequate

§5.3 showed `WF` is *necessary*. It is also *sufficient for this codebase*, in
the strongest available sense: `WF` is generated by `empty` and `push` only, and
a reverse scan shows `lean4lean` uses **no other `PersistentArray` operation** —
`push` (2 sites), `WF` (2), `toList'` (1), and nothing else. So `WF` is exactly
the reachable set, not an approximation to it. The axiom stays unprovable while
`insertNewLeaf` is `partial`; that is an implementation limit, not a gap in the
hypothesis.

### 11.8 The container axioms 4–7: four more failed attacks

**6 `findAux_isSome` — survives.** The suspicious feature is the statement's
generality: no `WF`, no `PartialEquivBEq`, no `LawfulHashable`, and an arbitrary
`node`. That is nevertheless fine, because both sides use the *same* `==` and the
two functions are parallel clause for clause, including the collision path
(`findAtAux` / `containsAtAux`, which differ only in returning `some vals[i]`
versus `true`). The `entries[j]!` panic-index is shared: whatever `default :
Entry` is, `findAux` returns `some v`/`none` exactly when `containsAux` returns
`true`/`false`. Unprovable only because all four functions are `partial`; they
are in fact total (nodes are inductive, so the `ref` recursion is well-founded).

**4 `WF.toList'_insert` and 5 `WF.find?_eq` — survive a non-reflexive `BEq`.**
The attack: `PartialEquivBEq` requires symmetry and transitivity but **not
reflexivity**, so `⟨fun _ _ => false⟩` is a legal instance, and `LawfulHashable`
(`a == b → hash a = hash b`) is then vacuous. Under it, `a == a` is false, so a
key can be inserted twice and the filter `(¬a == ·.1)` deletes nothing. Both
axioms still hold: `find?` degenerates to `none` on both sides, and for
`toList'_insert` the left side gains a second entry for `a` exactly as the
unfiltered right side does. The permutation survives.

**7 `Syntax.structEq_eq` — survives, but the reason in §7.3 is not the whole
story.** Upstream's `structEq` compares `rawVal` with
`Substring.Raw.Internal.beq`, while the model `structEq'` uses `==`. §7.3 says
`Internal.beq` *is* the `BEq Substring.Raw` instance at runtime. Two corrections:

* It is **not** a definitional identity. `example : @Substring.Raw.Internal.beq =
  (· == ·) := rfl` **fails** — `Internal.beq` is `opaque @[extern]`, while the
  instance is `⟨Substring.Raw.beq⟩` with `beq` a plain `def`. The identity holds
  through the linker: `@[extern "lean_substring_beq"]` on `Internal.beq` pairs
  with `@[export lean_substring_beq] Internal.beqImpl := Substring.Raw.beq`. That
  is a genuinely weaker kind of assurance than definitional equality, and it is
  why this axiom can never be discharged by unfolding.
* The attack that motivated the check — `Internal.beq` being *position*-sensitive
  while `==` is content-only — **fails**. `Substring.Raw.sameAs` is the
  position-sensitive comparison, and `structEq` does not use it. Differential
  test: substrings with the same content over *different* underlying strings and
  at *different* `startPos` (`"xfoo".drop 1` vs `"foo"`, `startPos` 1 vs 0) give
  `structEq = structEq' = true`; differing content and differing `val` both give
  `false = false`.

**Axiom 31 `eqv_eq` — deliberately not attacked.** Its dependency on 15
`instLawfulBEqLevel` is a cross-section question, and running it from one side
only is the weaker test. To be run jointly with the `Level` stream.

### 11.9 Evidence strength in this section

Kept separate on purpose, per §2:

| claim | evidence |
|---|---|
| 21 is false | differential test (compiled C, `#eval`) **+** kernel-checked model side **+** source reading |
| 21 has no consumers, so delete it | **axiom-cone scan** of every `Lean4Lean.*` declaration **+** reverse-dependency scan |
| 22, 30, 29 survive | source reading **+** kernel-checked agreement lemmas |
| 26/27 condition insufficient | source reading only — the witness is not constructible, so no differential test is possible |
| 17 is covered | source reading only |
| 3's hypothesis is adequate | source reading **+** reverse-dependency scan |
| 6 survives | source reading only |
| 4, 5 survive a non-reflexive `BEq` | source reading **+** hand-executed instance argument; *not* machine-checked |
| 7 survives | differential test **+** `rfl`-refutation of the definitional reading **+** source reading |

No claim here is a proof, and none should be recorded as one. The cone scan is
the strongest instrument used in this pass — it is a complete search over the
environment, not a sample — which is why the 21 recommendation is *delete* rather
than *weaken*.

---

## 12. Joint consistency: the `Level` thread closed, and a structural survey

*(Added by the axiom-consistency stream. Machine-checked artefact:
`Lean4Lean/Tests/AxiomConsistency.lean`, builds clean —
`lake build Lean4Lean.Tests.AxiomConsistency`, exit 0.)*

### 12.0 The method, and what it can and cannot show

Consistency of this axiom set is not machine-checkable and is not the guard's
job (guard 2 whitelists **by name**, deliberately: every entry asserts that a
Lean model agrees with a C++ implementation, a claim about the world outside
the proof). An *in*consistency, however, is machine-checkable — that is the
asymmetry this section works with.

The one positive instrument available is **model exhibition**. Almost every
constant these axioms speak about is `opaque` (or `partial`, which compiles to
`opaque`), i.e. a *free* symbol with no definitional unfolding. A set of
assumptions about free symbols is consistent exactly when some definable
function satisfies them all; exhibiting one is a relative-consistency proof and
*is* machine-checkable. Where the model exists, the axiom is safe; where an
axiom instead constrains a free symbol *through* a definable observation with
provable properties, it can still be refutable — and that is where both known
`False`-proofs lived.

### 12.1 Axioms 13/14 (`Level.hasParam_eq`, `hasMVar_eq`) — **settled**

The audit's "inconsistent (argued) (with 12)" verdict is **dead**, and the
docstrings' claim that the two "should now be provable using `mkData_eq` and
friends" is **also wrong**. Both are now machine-checked, in
`Lean4Lean/Tests/AxiomConsistency.lean`:

* **§1 `mkDataM`** — interpret `Level.mkData h d mv hp` as
  `mkData' h (min d (2^24-1)) mv hp` (clamp instead of panic). It agrees with
  `mkData'` below `2^24`, so it validates axiom 12, and it stores both flag bits
  faithfully at *every* depth, so `mkDataM_validates_hasParam_eq` /
  `mkDataM_validates_hasMVar_eq` hold **by induction on `Level`**.
  ⇒ **12 + 13 + 14 are jointly consistent.** No contradiction survives the
  `H : d < 2 ^ 24` repair.
* **§2 `mkDataZ`** — interpret `mkData` as `mkData'` in range and `0` out of
  range (what the *old*, unconditional `mkData_eq` forced, since
  `panic! _ : Level.Data` reduces to `default = 0`). This still validates axiom
  12, but `mkDataZ_refutes_hasParam_eq` / `..._hasMVar_eq` show it **falsifies**
  13 and 14 on `succ^[2^24] (.param x)` / `succ^[2^24] (.mvar x)`.
  ⇒ **13 and 14 are independent of 12.** They cannot be derived from
  `mkData_eq` "and friends"; nothing constrains `mkData` at `d ≥ 2^24`.

  Both models are stated against `dataOf f` — `Lean/Level.lean:98-106`'s
  computed field with `mkData` replaced by `f` — and the file checks clause by
  clause, by `rfl`, that `dataOf mkData` is the real `Level.data`.

  (Note the reason the two *cannot* be validated against the implementation
  either: at depth `2^24` `lean_level_mk_data` calls `lean_internal_panic` and
  **aborts**. Beyond that depth the axioms assert something the implementation
  has no behaviour for at all — consistent, but empty of implementation content.)

* **§3 — the free win.** Restricted to levels the runtime can actually build,
  both are **provable**:

  ```lean
  def dep : Level → Nat            -- structural depth
  theorem hasParam_eq_of_dep (l : Level) (h : dep l < 2 ^ 24) : l.hasParam = l.hasParam'
  theorem hasMVar_eq_of_dep  (l : Level) (h : dep l < 2 ^ 24) : l.hasMVar  = l.hasMVar'
  theorem depth_eq_of_dep    (l : Level) (h : dep l < 2 ^ 24) : l.depth    = dep l
  ```

  `#print axioms hasParam_eq_of_dep` → `[propext, Quot.sound,
  Lean.Level.mkData_eq]`, exactly — all three already whitelisted, nothing else.
  **No `hasParam_eq`, no `hasMVar_eq`, and no non-kernel-checked tactic** (see
  §12.5). So axioms 13 and 14 can be **retired from the whitelist**
  (29 → 27) at the cost of a `dep l < 2 ^ 24` side condition — the `Level`
  analogue of `Expr.BVarBounded`, and strictly cheaper than it: `dep` is
  strictly increasing on subterms, so the **single top-level bound suffices**,
  no per-subterm recursion. Discharge sites are `Verify/Level.lean:94`
  (`getUndefParam.F`), `Verify/Level.lean:140-145` (`substParams'`) and
  `Verify/Expr.lean:549-550, 622-623` (`hasLevelMVar'`/`hasLevelParam'`).
  Editing the frozen `Axioms.lean` needs sign-off; the proof is ready.

### 12.2 Structural survey: what each axiom can possibly conflict with

Computed mechanically (transitive closure of the axiom *statement* down to
`opaque`/`axiom` constants). Every whitelisted axiom mentions at least one free
symbol, so none is a bare claim about fully-defined Lean functions — the two
`Std.TreeMap` axioms were the only ones of that shape, and §8 removed them.

The free symbol each axiom **pins** (bold) and the ones it merely **uses**:

| pins | axiom(s) | also uses |
|---|---|---|
| `Expr.abstract` | `abstract_eq` (cond.) | — |
| `Expr.abstractRange` | `abstractRange_eq` | `Expr.abstract` |
| `Expr.equal` | `equal_eq` | `Level.beq`, `Syntax.structEq` |
| `Expr.eqv` | `eqv_eq` | `Level.beq`, `Syntax.structEq` |
| `Expr.hasLooseBVar` | `hasLooseBVar_eq` | — |
| `Expr.instantiate` | `instantiate_eq` (cond.) | — |
| `Expr.instantiate1` | `instantiate1_eq` | — |
| `Expr.instantiateRev` | `instantiateRev_eq` | `Expr.instantiate` |
| `Expr.instantiateRange` | `instantiateRange_eq` (cond.) | `Expr.instantiate` |
| `Expr.instantiateRevRange` | `instantiateRevRange_eq` (cond.) | `Expr.instantiateRev` |
| `Expr.liftLooseBVars` | `liftLooseBVars_eq` | — |
| `Expr.lowerLooseBVars` | `lowerLooseBVars_eq` | — |
| `Expr.replaceImpl` | `replace_eq` | — |
| `Expr.mkData` | `Expr.mkData_eq` (cond.), **`looseBVarRange_eq`** | — |
| `Expr.mkAppData` | `mkAppData_eq`, **`looseBVarRange_eq`** | — |
| `Level.mkData` | `Level.mkData_eq` (cond.), **`hasParam_eq`**, **`hasMVar_eq`** | (in `looseBVarRange_eq`) |
| `Level.beq` | `instLawfulBEqLevel` | — |
| `Level.mkMaxAux` | `mkMaxAux_eq` | `Level.beq` |
| `Level.skipExplicit` | `skipExplicit_eq` | — |
| `Level.isExplicitSubsumedAux` | `isExplicitSubsumedAux_eq` | — |
| `Level.normalize` | `normalize_eq` | `Level.beq`, `isExplicitSubsumedAux` |
| `Syntax.structEq` | `structEq_eq` | — |
| `PHM.findAux` | **`WF.find?_eq`** | — |
| `PHM.insertAux` | **`WF.toList'_insert`** | — |
| `PHM.containsAux` | `findAux_isSome` | `PHM.findAux` |
| `PArray.insertNewLeaf`, `mkNewPath` | **`WF.toList'_push`** | — |

`mixHash`, `String.hash`, `String.Internal.append` and
`System.Platform.getNumBits` also appear, but no whitelisted axiom constrains
them, so they are inert parameters.

Two facts follow.

* **The relation is acyclic.** For every "definitional" pin `f = g`, `g` does
  not transitively mention `f` — checked mechanically for `structEq'`,
  `Total.mkMaxAux`, `Total.skipExplicit`, `Total.isExplicitSubsumedAux` and
  `Total.normalize` (each reaches its opaque partner **zero** times). In
  particular `Total.normalize` uses `Total.mkMaxAux` / `Total.skipExplicit`,
  *not* the opaque originals, so `normalize_eq` is not a fixed-point equation
  and the four `Level`-normalisation axioms can be interpreted bottom-up.
  Likewise `instantiate → instantiateRev → instantiateRevRange`,
  `instantiate → instantiateRange`, `abstract → abstractRange`,
  `Level.beq → {mkMaxAux, normalize, eqv, equal}`,
  `findAux → containsAux` are all DAG edges. A simultaneous interpretation
  therefore exists in topological order, for all of class (A) below.
* **Every axiom that pins nothing new is bold above.** Bold = the axiom
  constrains a free symbol *through* a definable observation instead of
  defining it. That is class (B): `looseBVarRange_eq`, `hasParam_eq`,
  `hasMVar_eq`, `WF.toList'_push`, `WF.toList'_insert`, `WF.find?_eq` — **six**
  axioms, and **both** historical `False`-proofs (§3.1 `looseBVarRange_eq`,
  §5.3 `toList'_push`) were in it. Class (A), the other 23, is jointly
  consistent by the DAG argument.

> **Operational conclusion.** *Stop auditing the set for consistency and attack
> class (B).* The 23 class-(A) axioms cannot produce a contradiction: each pins
> a free symbol to a total definable function, the pinning relation is acyclic,
> so an interpretation validating all of them exists by topological order. They
> can still be **false of the C++ kernel** — §11.2's `liftLooseBVars_eq` is
> exactly that — but falsity there is a testing/reading problem, not a
> soundness-of-the-proof problem. Every route by which this axiom set could make
> `kernel_sound` vacuous runs through one of the six class-(B) axioms, and two
> of those six (#13, #14) are now closed by §12.1. **Four remain:**
> `Expr.looseBVarRange_eq`, `PersistentArray.WF.toList'_push`,
> `PersistentHashMap.WF.toList'_insert`, `PersistentHashMap.WF.find?_eq`.
>
> *(Updated: §13 closed `Expr.looseBVarRange_eq` too — it is derivable as
> stated, at zero cost. **Three remain**, all container axioms; see §13.6.)*

### 12.3 Attacks attempted and failed

Recorded because a serious failed attack is stronger evidence than a source
reading, and weaker than a proof. None of these is a proof of consistency.

1. **`instLawfulBEqLevel` (#15) + `eqv_eq` (#31)** — the flagged
   cross-dependency. `Lean/Level.lean:255-256` shows `Level.beq` is
   `@[extern "lean_level_eq"] opaque` (the `Level` inductive derives only
   `Inhabited, Repr`), and `Lean/Expr.lean:808-809` shows `Expr.eqv` is a
   *separate* opaque. So `Level.beq := structural equality` validates #15 and
   `Expr.eqv := eqv'` validates #31, independently. **Fails at the first step:
   there is no shared constant to force apart.** The route that *would* have
   worked — a core `LawfulBEq Expr`, which `eqv'` refutes since it ignores
   binder names and binder info at `strict := false` — does not exist (see 5).
2. **`eqv_eq` (#31) + `equal_eq` (#30)** — if `Expr.equal` were defined in Lean
   as `Expr.eqv` with a flag, the two axioms would give
   `eqv' e₁ e₂ false = eqv' e₁ e₂ true`, refuted by any two `lam`s differing
   only in binder name. **Fails:** `Lean/Expr.lean:818-819` shows `Expr.equal`
   is an independent `@[extern "lean_expr_equal"] opaque`; nothing in Lean ties
   it to `eqv`.
3. **`instantiate*_eq` / `abstract*_eq` mutual definability** — if any of the
   ten substitution/abstraction primitives were a Lean `def` in terms of
   another, the "equivalent to …" equations could collide. **Fails:** all ten
   (`instantiate`, `instantiate1`, `instantiateRev`, `instantiateRange`,
   `instantiateRevRange`, `abstract`, `abstractRange`, `liftLooseBVars`,
   `lowerLooseBVars`, `hasLooseBVar`) are independent `@[extern] opaque`s
   (`Lean/Expr.lean:1329-1498`); the equivalences appear **only in docstrings**.
   The only Lean-level links are the derived wrappers `replaceFVar` /
   `replaceFVars`, which are *users*, not constraints.
4. **`looseBVarRange_eq` (#18) at the `BVarBounded` boundary** — the §3.1
   refutation's route re-run against the repaired axiom. Every `mkData` call in
   the `Expr.data` computed field (`Lean/Expr.lean:470-513`) was checked against
   what `BVarBounded` supplies: `.bvar i` needs `i+1 ≤ 2^20-1`, which *is*
   `BVarBounded`'s `bvar` clause; `.lam`/`.forallE` pass `max t' (b'-1)` and
   `.letE` passes `max (max t' v') (b'-1)`, both `≤` the children's bound by
   `BVarBounded.looseBVarRange'_le`; `.mdata`/`.proj` pass through; `.app` goes
   via `mkAppData`, which takes no `Nat` and needs no bound. `mkDataForBinder`
   and `mkDataForLet` (`Lean/Expr.lean:178-181`) are verbatim pass-throughs to
   `mkData`, so they introduce no argument permutation. **Fails: the side
   condition is exactly, not approximately, what is needed.** It also follows
   that #18 ought to be *provable* under `BVarBounded`, the same free win as
   §12.1 — not attempted here.
5. **Environment sweep: does anything already *prove* something about these
   opaques?** A refutation could come from a pre-existing core/Batteries/
   Foundation theorem contradicting an axiom's right-hand side. Enumerating
   **every** constant in the imported environment whose *type* mentions any of
   the 27 pinned opaques (private manglings such as
   `_private.Lean.Level.0.Lean.Level.mkMaxAux` resolved, not grepped) gives
   **25 hits: 21 of the whitelisted axioms themselves, plus exactly four
   auto-generated lemmas** — `PersistentArray.mkNewTail.eq_1` (an unfolding
   equation) and the LCNF `instantiateForall.go` `eq_def` / `_unary.eq_def` /
   `_unary._proof_1` (the last being `ps.size - (i+1) < ps.size - i`, with
   `instantiate1` occurring only as an inert argument). The other 8 whitelisted
   axioms reach their opaque only after unfolding a definition, which is
   precisely class (B) plus `replace_eq` and `instLawfulBEqLevel`.
   **Fails: no theorem anywhere asserts a behavioural property of any pinned
   opaque.** So no whitelisted axiom can contradict prior
   knowledge; contradictions can only arise *between* whitelisted axioms, and
   only via a shared pin or via class (B).
6. **Off-by-one at the two `mkData` panic boundaries** — the shape of the two
   bugs already found. `kernel/expr.cpp:109` panics on `range > 1048575`, and
   `Expr.mkData_eq`'s hypothesis is `br ≤ 2^20 - 1 = 1048575`: **exact match**.
   `kernel/level.cpp:47` panics on `d > 16777215`, and `Level.mkData_eq`'s is
   `d < 2^24`, i.e. `d ≤ 16777215`: **exact match**. `BVarBounded`'s `bvar`
   clause `i + 1 ≤ 2^20 - 1` matches the C guard exactly too. **Fails.**
7. **`mkAppData_eq` (#17) is unconditional — is its `assert!` reachable?** Its
   argument is `max fData.looseBVarRange aData.looseBVarRange`, a `max` of two
   reads of `(c >>> 44).toUInt32`, hence `≤ 2^20-1` unconditionally, so the
   `panic! = 0` branch is dead and the missing side condition costs nothing.
   Line-by-line against `lean_expr_mk_app_data` (`kernel/expr.cpp:120-126`):
   the depth arithmetic is `uint16_t` on **both** sides (the model's
   `.toUInt16` matches, so there is no `uint8` wraparound at depth 255), the
   `>255 → 255` clamp, the `uint32_t h` truncation and the shift amounts
   32/40-43/44 all agree. **Fails.**

### 12.4 What remains unverified

* **Class (B), the `PersistentArray`/`PersistentHashMap` three**
  (`WF.toList'_push`, `WF.toList'_insert`, `WF.find?_eq`). These constrain
  `insertNewLeaf`/`mkNewPath`/`insertAux`/`findAux` through `toList'`, the same
  shape as the two axioms that proved `False`. Their `WF` hypotheses block the
  known counterexamples (§5.3), and no *new* attack succeeded, but **no model
  has been exhibited**: doing so means proving the real persistent-array and
  HAMT algorithms correct, which is the substance of the axioms. Highest
  residual risk in the set.
* ~~**`Expr.looseBVarRange_eq` + `Expr.mkData_eq` + `mkAppData_eq`** — attack 4
  fails and the hand analysis says a clamping model works exactly as
  `mkDataM` does for `Level`, but the `Expr` model has **not been mechanised**
  (its `data` field has eleven clauses against `Level`'s six).~~ **Done in
  §13**: the hand analysis held, the clamping model is mechanised, and the
  axiom turned out to be outright *derivable* rather than merely consistent.
* **Truth vs consistency.** Everything above is about consistency. The axioms
  can be jointly consistent and still not describe the C++ kernel; that gap is
  what guard 2's by-name whitelist exists to make visible, and §7's
  differential testing is the evidence for it.

### 12.5 `bv_decide` is not kernel-checked — and three of its axioms are already in the repo

The first version of §12.1's proofs reused `Verify/Level.lean`'s `bv_decide`
bit-blasting and so carried entries like
`mkData'_hasParam._native.bv_decide.ax_1_8`. **Those are not certificates in
any kernel-checked sense.** `bv_decide` discharges its LRAT check through
`Lean.Meta.nativeEqTrue` (`Lean/Meta/Native.lean:37-77`), which:

1. builds an auxiliary `def` whose value is the `Bool` check,
2. `addAndCompile`s it and calls `unsafe evalConst Bool` — i.e. **runs compiled
   machine code**, and
3. if that returns `true`, calls `addDecl` on a fresh **`axiomDecl`** asserting
   `Std.Tactic.BVDecide.Reflect.verifyBVExpr <expr> <cert> = true`.

The kernel never checks the claim. This is `native_decide`'s trust model —
compiler, runtime and SAT-certificate checker all enter the TCB — and in one
respect it is worse: instead of a single named, auditable axiom
(`Lean.ofReduceBool`), each invocation mints a **fresh anonymous axiom** whose
statement mentions two auto-generated definitions, so the trust surface grows
silently with every use and is invisible to a by-name whitelist review.

**Retiring #13/#14 in exchange for these would not have been 29 → 27**; it
would have swapped two well-understood interface axioms for an unbounded family
of compiled-evaluation axioms. Recorded because the count exists precisely to
make that kind of trade visible.

**Bit-blasting turned out to be unnecessary.** §0 of
`Lean4Lean/Tests/AxiomConsistency.lean` now proves the same three facts by
pushing `UInt64` to `Nat` (`UInt64.toNat_add`, `toNat_shiftLeft`,
`toNat_shiftRight`, `toNat_and`, `toNat_toUInt32`, `Nat.and_one_is_mod`,
`Nat.shiftRight_eq_div_pow`) and closing with `omega`, via one packing lemma

```lean
theorem mkData'_toNat (H : d < 2 ^ 24) :
    (mkData' h d hmv hp).toNat
      = h.toNat % 2^32 + (if hmv then 1 else 0) * 2^32
        + (if hp then 1 else 0) * 2^33 + d * 2^40
```

and one field-extraction lemma over an arbitrary `UInt64`. Result:
`mkData'_depth`, `mkData'_hasParam`, `mkData'_hasMVar` each depend on
**`[propext, Quot.sound]`** and nothing else — `Classical.choice` drops out
too. The file no longer imports `Std.Tactic.BVDecide`.

**Latent guard-2 failure already in the repo.** The environment contains
exactly three `_native` axioms, all from `Verify/Level.lean`:

```
Lean.Level.mkData_depth._native.bv_decide.ax_1_9
Lean.Level.mkData_hasMVar._native.bv_decide.ax_1_8
Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8
```

None is in `axiomWhitelist`. They are **not** in `kernel_sound`'s cone *today*
only because that cone is still 4 constants wide (the proof is mostly
`sorryAx`); `Lean.Level.mkData_hasParam` already reports
`[propext, Classical.choice, Quot.sound, Lean.Level.mkData_eq,
Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8]`. **Guard 2 will fail the
build the moment those three lemmas enter the real proof.** The §0 proofs are a
drop-in replacement (same statements modulo `mkData_eq`), so the fix is
mechanical; `Verify/Level.lean` is owned by another stream and was not touched.

A cheap standing check, worth adding wherever the guard lives: no axiom whose
name contains `_native` may appear in any cone, whitelisted or not.

---

## 13. The #31/#15 cross-section, and the container axioms' reachable set

Two follow-ups to §12, run with both sides in hand. Neither found an
inconsistency. One corrects a recorded justification; the other bounds class
(B)'s risk without removing it.

### 13.1 "#31 depends on #15" is a **documentation artifact**

§1's table annotates `Expr.eqv_eq` with "**Depends on 15.**", and §12.2 lists it
as *using* `Level.beq`. §12.3's attack 1 already showed the pair cannot be forced
apart. The remaining question is different: **is the recorded dependency real at
the proof level, or is it a note about meaning?** It is the latter, and the
distinction matters.

Measured with a constant-dependency scan (statement + value + the `brecOn`
helper):

| declaration | mentions `Level.instLawfulBEqLevel`? |
|---|---|
| `Lean.Expr.eqv_eq` | **no** |
| `Lean.Expr.eqv'` | **no** |
| `Lean.Expr.eqv'._f` | **no** |

There is no proof-level dependency at all. What #31's *truth* actually rests on
is strictly weaker and different in kind: that `BEq Level` is **the same
function** the C comparison uses.

* `example : (BEq.beq : Level → Level → Bool) = Lean.Level.beq := rfl` — the
  instance *is* `Level.beq`, definitionally.
* `Level.beq` is `@[extern "lean_level_eq"]`.
* `kernel/expr_eq_fn.cpp:84` compares a `const`'s levels with
  `compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2)
  { return l1 == l2; })`, and `:53` compares `sort_level(a) == sort_level(b)` —
  i.e. `operator==(level, level)`, which is that same symbol.

**Sameness is what #31 needs; lawfulness is what #15 asserts.** They are
independent: if #15 were refuted — if `lean_level_eq` did any normalisation and
so were not structural — **#31 would be unaffected**, because both sides of
`eqv_eq` would use the same non-structural comparison and would still agree.

That is why the annotation is worth removing rather than leaving as a harmless
approximation: it invites the inference *"refuting 15 propagates to 31"*, which
is false, and it is the §7.3 shape again — a right verdict resting on a wrong
recorded reason. *(Frozen-file docs only; no code change proposed.)*

### 13.2 The `LawfulBEq Expr` route, re-swept over the whole import closure

§12.3 records that the attack which *would* have worked — a core
`LawfulBEq Expr`, which `eqv'` refutes since at `strict := false` it ignores
binder names and binder info — fails because core has no such instance. That
check was against core. Re-run as an environment-wide scan for **any** instance
whose type is `LawfulBEq Expr` or `LawfulBEq Level` anywhere in this repo's
import closure (core + Batteries + Foundation + `Lean4Lean`):

```
LawfulBEq instances for Expr/Level in the import closure: [Lean.Level.instLawfulBEqLevel]
```

The only one is axiom #15 itself, and it is for `Level`, not `Expr`. The route is
closed over the whole closure, not merely over core.

### 13.3 `WF` is exactly the reachable set for the `PersistentHashMap` axioms too

§11.7 established this for `PersistentArray.WF.toList'_push`: `WF` is generated
by `empty` and `push`, and `lean4lean` uses no other `PersistentArray`
operation, so `WF` is the reachable set rather than an approximation of it. The
same argument **does** hold for `WF.toList'_insert` (#4) and `WF.find?_eq` (#5),
by a slightly longer chain, since the maps are never touched directly — they
arrive through `Lean.Kernel.Environment`'s `ConstMap = SMap Name ConstantInfo`.

A constant-dependency scan over `Lean4Lean.*` finds only **7** distinct
`PersistentHashMap`/`PersistentArray` constants referenced at all, none of them
`insert`/`find?`; the operations come in via `SMap`, whose used surface is five
functions — `insert`, `find?`, `find?'`, `stage`, `fromHashMap`. Following each:

* `structure SMap` declares `map₂ : PHashMap α β := {}` — the persistent half
  **defaults to empty**.
* `fromHashMap m s = { map₁ := m, stage₁ := s }` sets only `map₁` and the stage,
  so it leaves `map₂ = ∅`. It never builds a non-empty `PersistentHashMap`.
* `SMap.insert ⟨false, m₁, m₂⟩ k v = ⟨false, m₁, m₂.insert k v⟩` — the only
  operation that grows `map₂`, and it is `PersistentHashMap.insert`. At stage 1
  it touches the `HashMap` only.
* `find?` / `find?'` only read; `stage` / `switch` only flip a `Bool`.
* The single construction site is
  `Kernel.Environment.mk (constants := SMap.fromHashMap constantMap false)`
  (`Lean4Lean/Environment/Basic.lean:123`) — **stage 2**, so every later insert
  lands in `map₂`, starting from `∅`.

So every `PersistentHashMap` value this checker can produce is
`empty` followed by `insert`s — precisely `WF`'s two generators. `erase`,
`modify`, `insertIfNew`, `ofList` and the rest of the API are unreachable.

**What this does and does not buy.** It rules out the failure mode that actually
produced a `False` here: §5.3's `toList'_push` was false because it was stated
for arbitrary — including unreachable, malformed — arrays. A hypothesis that is
exactly the reachable set cannot be applied outside its intended domain. It does
**not** make the axioms true *on* that domain: no model of the HAMT or of the
persistent-array trie exists, so an error in the algorithms themselves would not
be caught by this argument. Class (B) risk is **bounded, not removed**, and
§12.4's assessment stands.

### 13.4 Failed attacks in this section

1. **#31 + #15 forced apart** — fails; §12.3's reason confirmed, and strengthened
   by 13.1: there is not even a proof-level dependency to exploit.
2. **#31 + any `LawfulBEq Expr`** — fails; no such instance exists in the whole
   import closure (13.2).
3. **`WF` too weak for the `PersistentHashMap` axioms** (i.e. some reachable map
   is built by an operation outside `empty`/`insert`) — fails; the `SMap` surface
   is five functions and only one of them writes `map₂` (13.3).

### 13.5 Evidence strength

| claim | evidence |
|---|---|
| #31 has no proof-level dependency on #15 | constant-dependency scan (complete over statement, value, `brecOn` helper) |
| #31 rests on *sameness*, not lawfulness | `rfl` on the instance **+** `@[extern]` name **+** C source reading |
| no `LawfulBEq Expr` in the closure | environment-wide instance scan (complete search) |
| `WF` is the reachable set for #4/#5 | constant-dependency scan **+** source reading of all five `SMap` entry points |
| #4/#5 are *true* | **none — still no model.** Unchanged from §12.4 |

The last row is the point of the table.

---

## 13. Class (B), second front: `Expr.looseBVarRange_eq` is a theorem

*(Axiom-consistency stream. Machine-checked artefact:
`Lean4Lean/Tests/AxiomConsistencyExpr.lean`; `lake build
Lean4Lean.Tests.AxiomConsistencyExpr` exits 0. Measured against the **28**-axiom
whitelist at `04a35ff`.)*

§12.2 reduced the consistency question to class (B) — the six axioms that
constrain a free symbol *through* a definable observation with provable
properties — and closed two of them (#13, #14). This section closes a third,
the one that originally proved `False`.

The trio in play:

| axiom | side condition |
|---|---|
| `Lean.Expr.mkData_eq` | `br ≤ 2 ^ 20 - 1` |
| `Lean.Expr.mkAppData_eq` | none |
| `Lean.Expr.looseBVarRange_eq` | `e.BVarBounded` |

### 13.1 The result is *stronger* than the `Level` case

For `Level`, §12.1 found `hasParam_eq` **independent** of `mkData_eq`: nothing
constrains `Level.mkData` at depth `≥ 2 ^ 24`, so the axiom had to be replaced
by a theorem carrying a *new* side condition, at a cost in discharge
obligations. The `Expr` case is different and better:

```lean
theorem looseBVarRange_eq_proved (e : Expr) (h : e.BVarBounded) :
    e.looseBVarRange = e.looseBVarRange'
```

`#print axioms` → `[propext, Quot.sound, Lean.Expr.mkAppData_eq,
Lean.Expr.mkData_eq]`. The statement is **literally identical** to the axiom's
(checked with `pp.fullNames`; `Lean.Expr.looseBVarRange_eq` does not appear in
its own cone). So this is a **drop-in replacement at zero downstream cost** —
unlike #13/#14 it introduces no new obligation anywhere, because the side
condition it needs is the one the axiom already states.

**`Lean.Expr.looseBVarRange_eq` should be deleted: 28 → 27.**

**Landed.** With the frozen-file exception, `Verify/Axioms.lean` now declares
the theorem in place of the axiom and `Verify/Guard.lean` is re-pinned to 27.
Verified rather than read:

* `lake build` (all default targets, 1291 jobs) exits 0 — **zero downstream
  churn**, as the identical-statement claim predicted;
* guard 1 prints `declares exactly the 27 frozen axioms ✓`, guard 2 unchanged
  (`within whitelist ✓`, still INCOMPLETE on `sorryAx`), guard 3 unchanged
  (`54/54 remaining ✓`);
* re-derived independently with guard 1's own instrument — enumerating
  `axiomInfo` constants whose declaring module is `Lean4Lean.Verify.Axioms`,
  not a grep — giving **27**, with `Lean.Expr.looseBVarRange_eq` absent from the
  list and present as a `thmInfo` of the identical type;
* `#print axioms Lean.Expr.looseBVarRange_eq` (with `pp.fullNames`) →
  `[propext, Quot.sound, Lean.Expr.mkAppData_eq, Lean.Expr.mkData_eq]`, and no
  `_native` axiom is reachable from `Axioms.lean`.

*Layering:* the proof went inline into `Axioms.lean`, in a `section` with a
`local reducible` attribute on `Expr.Data` and every helper `private`. This
inverts nothing — everything it needs (`mkData'`, `mkAppData'`,
`looseBVarRange'`, `BVarBounded`, and the two axioms) is already declared in
that file above it. The `Verify/Level.lean` stream faced a genuinely different
problem: its bit lemmas were needed by a *consumer* of the frozen file, so a
shared home would have had to import `Axioms.lean`, and it chose duplication.
The same choice applies to the helpers here: they duplicate facts
`Verify/Expr.lean` also proves (still with `bv_decide`), and the private copies
are deliberate for the same reason.

### 13.2 Why it goes through, and what `BVarBounded` is actually for

Checking every `mkData` call in the `Expr.data` computed field
(`Lean/Expr.lean:471-513`) against what has to be `≤ 2 ^ 20 - 1`:

| clause | range argument | bounded by |
|---|---|---|
| `const`, `sort`, `fvar`, `mvar`, `lit` | `0` | trivially |
| `mdata`, `proj` | `e.data.looseBVarRange.toNat` | **`looseBVarRange_lt`**, unconditionally |
| `lam`, `forallE` | `max t.…range (b.…range - 1)` | **`looseBVarRange_lt`**, unconditionally |
| `letE` | `max (max t.… v.…) (b.… - 1)` | **`looseBVarRange_lt`**, unconditionally |
| `app` | — (`mkAppData`, takes no `Nat`) | n/a |
| `bvar idx` | `idx + 1` | **`BVarBounded` — the only clause that does any work** |

So the operative content of `BVarBounded` is exactly *"every `bvar` index
occurring in `e` is `< 2 ^ 20 - 1`"*; its recursion through `app`/`lam`/`letE`
exists only to reach the `bvar` leaves. Every other call is bounded for free by
the 20-bit field read. This is worth stating because it says the side condition
cannot be weakened at the leaves and need not be strengthened anywhere else.

### 13.3 The side condition is load-bearing — refuted, not merely separated

For `Level` the evidence that the condition mattered was a *model separation*
(§12.1 §2). Here something stronger is available, and it is recorded as a
different strength of evidence:

```lean
theorem not_looseBVarRange_eq_unconditional :
    ¬ ∀ e : Expr, e.looseBVarRange = e.looseBVarRange'
```

`#print axioms` → `[propext, Quot.sound]`. **No axiom at all**, and no
interpretation of `mkData` can rescue it: `looseBVarRange` is a 20-bit field
read and `looseBVarRange'` is unbounded, so `.bvar (2 ^ 20 - 1)` refutes the
unconditional form outright. This is §3.1's original `False`-proof restated as a
negation, so that it establishes the necessity of `BVarBounded` without
introducing an inconsistency. `bvar_big_not_bvarBounded` records that the
witness is not `BVarBounded`, so §13.1 and §13.3 do not collide.

### 13.4 Joint consistency of the trio

`mkDataC h br d … := mkData' h (min br (2 ^ 20 - 1)) d …` (clamp instead of
panic, exactly as `mkDataM` does for `Level`) and `mkAppDataC := mkAppData'`
validate `Expr.mkData_eq` and `Expr.mkAppData_eq` simultaneously
(`mkDataC_validates_mkData_eq`, `mkAppDataC_validates_mkAppData_eq`, both
axiom-free). With §13.1 — which *derives* `looseBVarRange_eq` from those two —
that settles **joint consistency of all three**.

### 13.5 Four more `bv_decide` axioms replaced

§E0 of the artefact is kernel-checked throughout, and covers the remaining
`_native` axioms in the repo. Before this section the environment contained
four, all in `Verify/Expr.lean`:

```
Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7
Lean.Expr.mkData_flags._native.bv_decide.ax_1_12          (private)
Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9
Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8
```

`looseBVarRange_lt`, `mkData'_looseBVarRange` and `mkAppData'_looseBVarRange`
replace three of them; `mkData_flags` (the four flag bits) is the same technique
and was not needed here. As in §12.5 they sit outside `kernel_sound`'s cone only
because that cone is still 4 constants wide.

The `|||`-structured `mkAppData'` needed one extra idea over the `+`-structured
`mkData'`: `>>>` distributes over `|||` (`Nat.shiftRight_or_distrib`), so the
field read is computed piecewise and the three sub-44 pieces vanish, rather than
proving disjointness of the disjuncts.

### 13.6 Class (B) after this section

| axiom | status |
|---|---|
| `Level.hasParam_eq` | **closed** §12.1 — provable under `dep l < 2 ^ 24` |
| `Level.hasMVar_eq` | **closed** §12.1 — same |
| `Expr.looseBVarRange_eq` | **closed** §13.1 — provable as stated, zero cost |
| `PersistentArray.WF.toList'_push` | open |
| `PersistentHashMap.WF.toList'_insert` | open |
| `PersistentHashMap.WF.find?_eq` | open |

**Class (B) is now exactly the three container axioms**, and they share a shape
the other three did not: their right-hand sides are not bit arithmetic but the
correctness of a persistent-array and a HAMT algorithm, so "exhibit a model"
means proving those algorithms correct. That is the whole remaining consistency
risk in the file, and it belongs to the container stream.

The 23 class-(A) axioms remain jointly consistent by §12.2's DAG argument, and
the environment sweep of §12.3 (item 5) still bounds where any contradiction
could come from: no theorem anywhere asserts a behavioural property of any
pinned opaque, so a contradiction can only arise between whitelisted axioms.
