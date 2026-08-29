# Handoff: killing the four container axioms

**Stream:** containers.  **Status:** **landed** by the orchestrator as commit `961871b`
("pure containers replace the persistent HAMT and trie"), after independent re-verification —
so §4's landing instructions and §9's worktree/patch notes are historical.  The
`Verify/Axioms.lean` and `Verify/Guard.lean` edits are **stated below, still not made** — they
are frozen files and need human sign-off; until then the four axioms remain *declared* and
guard 1 still reads 29.  `divergences.md` §8 was appended as part of the same commit.

Everything below describes the state as validated before landing; the worktree
`/home/vasilii/lean4lean-wt-containers` and `docs/handoff-containers.patch` referenced in
places no longer exist, having been consumed by the merge.

---

## 0. Result in one line

All **four** container axioms — `PersistentArray.WF.toList'_push`,
`PersistentHashMap.WF.toList'_insert`, `PersistentHashMap.WF.find?_eq`,
`PersistentHashMap.findAux_isSome` — plus the theorem `PersistentArray.WF.toList'_length` that
depends on one of them, have **zero dependents** after the change (machine-checked
constant-dependency scan over the whole environment, §5).  Guard 1 would go **29 → 25**.

The route taken is **(a), replace the container**.  Route (b) is not merely expensive, it is
**impossible**; §2 gives the machine-checked reason.

---

## 1. Scope correction to `docs/axiom-audit.md` §13.3 — the orchestrator should read this

§13.3 says:

> `PersistentHashMap` is never touched directly — it arrives through
> `Lean.Kernel.Environment`'s `ConstMap = SMap Name ConstantInfo` […] The single construction
> site is `Kernel.Environment.mk (constants := SMap.fromHashMap constantMap false)`.

That is **one of two arrival paths**, and not the one that carried most of the risk.  The
second, which §13.3 does not mention at all, is

```
Lean.LocalContext.fvarIdToDecl : PersistentHashMap FVarId LocalDecl
Lean.LocalContext.decls        : PersistentArray (Option LocalDecl)
```

reached from `Lean4Lean.addDecl` through `LocalContext.mkLocalDecl` / `mkLetDecl` / `find?` in
the type checker's telescope code.  Measured (§5): of the axioms' direct users before this
change, **5 of 12 were `Lean.LocalContext.*` lemmas**, and the `PersistentArray` axiom was
reachable through the local context and *nothing else* — the environment's `SMap` never touches
`PersistentArray` at all.

**The audit's verdict survives; its argument did not cover the dominant path.**  I re-checked
the `WF`-is-the-reachable-set claim on that second path with the same structural instrument and
it does hold: the only `LocalContext` writers reachable from `addDecl` are `mkLocalDecl` and
`mkLetDecl`, which are exactly `map.insert` + `decls.push` from `{}` — i.e. precisely `WF`'s two
generators, on both containers.  No `mkAuxDecl`, `LocalContext.addDecl`, `erase`, `pop` or
`isSubPrefixOf` is reachable.

Two smaller corrections:

* §14.4 and the task framing count **3** class-(B) axioms.  The file declares **4**;
  `findAux_isSome` is in exactly the same boat (§11.8 itself says it is "unprovable only
  because all four functions are `partial`") and it goes with the others.
* §13.3 lists the `SMap` surface as five functions including `find?` and `fromHashMap`.  In
  `addDecl`'s cone the surface is **three** — `insert`, `find?'`, `contains`.  `SMap.find?` and
  `SMap.fromHashMap` appear only in the `Main`/`Replay` import path, outside that cone.

---

## 2. Route (b) is impossible, not expensive — machine-checked

Route (b) was "give structural or well-founded definitions of the upstream functions and
discharge the axiom statements as theorems".  It cannot be done, and the obstruction is not
that the functions are hard to define: it is that **the upstream constants have no definition
in the environment at all**.

`partial def` in Lean 4 elaborates to an `opaque` constant plus an `unsafe` companion.  An
`opaque` constant has no defining equations and the kernel never delta-reduces it, so *no*
equation about it is provable — whether or not the function it stands for is in fact total.
Measured with `Lean.Meta.getEqnsFor?` / `getUnfoldEqnFor?`:

```
Lean.PersistentArray.insertNewLeaf:                opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentArray.mkNewPath:                    opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.insertAux:                  opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.insertAtCollisionNodeAux:   opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.findAux:                    opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.findAtAux:                  opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.containsAux:                opaqueInfo, equation lemmas: 0, unfolding thm: false
Lean.PersistentHashMap.containsAtAux:              opaqueInfo, equation lemmas: 0, unfolding thm: false
```

§11.8's remark that these functions "are in fact total (nodes are inductive, so the `ref`
recursion is well-founded)" is true but **irrelevant to provability**: totality of the intended
function says nothing about the `opaque` constant that stands in for it.  (It is also not quite
right for `mkNewPath`, whose recursion is on `shift - initShift : USize`, which underflows for
any `shift` that is not a multiple of 5 — so it is total only on well-formed inputs.)

A one-line corollary worth recording: **even `PersistentHashMap.empty.find? k = none` and
`PersistentHashMap.empty.contains k = false` are unprovable**, because both go straight through
`findAux`/`containsAux`.  This is what forces the environment half of the change (§4): it is
not enough to keep `map₂` empty, the code must never *read* it.

---

## 3. What was built

### 3.1 A pure local context — `Lean4Lean/Std/LocalContext.lean` (new, owned)

```
structure Lean4Lean.LocalContext where
  fvarIdToDecl : Std.HashMap FVarId LocalDecl := {}
  decls        : Array (Option LocalDecl)     := #[]
```

with `mkLocalDecl`, `mkLetDecl`, `find?`, `findFVar?`, `get!`, `getFVar!`, `contains`,
`containsFVar`, `isEmpty`, `empty`, and `mkBinding` / `mkLambda` / `mkForall` (a verbatim copy
of the upstream `mkBinding` body, which consults the context only through `findFVar?`).  Plus a
`LawfulBEq FVarId` instance (`LawfulHashable FVarId` then comes for free) and a `MonadLCtx`
class mirroring `Lean.MonadLCtx`.

Three deliberate choices:

* **`auxDeclToFullName` is dropped.**  The kernel never writes it, and it is the sole reason
  `Lean.Name.quickCmp` (an `@[extern]` function) is *structurally* reachable from `addDecl` —
  `Lean4Lean/Tests/KernelHardening.lean` says at line ~698 that removing it "would mean
  replacing `Lean.LocalContext`, not anything in this repo".  This does exactly that.
* **The name is `Lean4Lean.LocalContext`, not `Lean4Lean.LCtx`.**  Inside `namespace Lean4Lean`
  with `open Lean` in scope, namespace-prefix resolution picks `Lean4Lean.LocalContext` over
  `Lean.LocalContext` without ambiguity, so `Lean4Lean/Inductive/Add.lean`, `Quot.lean` and
  `Primitive.lean` needed **zero** edits.
* **`LocalContext.toLean`** converts to `Lean.LocalContext` at the five `Kernel.Exception`
  throw sites, whose constructors take the upstream type.  Error payloads are therefore
  byte-identical to before.  It is only ever evaluated on a failure path, and the refinement
  proofs constrain only successful runs, so it costs nothing in the proof.  (Consequence: the
  upstream `partial` container functions are still *reachable* from `addDecl`, on error paths
  only; no axiom mentions them any more, which is what matters.  Dropping `toLean` in favour of
  `{}` would remove them entirely at the price of losing the local context from five error
  messages — offered as a follow-up, not taken.)

### 3.2 `Verify/LocalContext.lean` ported

`WF` becomes

```
inductive WF : LocalContext → Prop
  | nil : WF ⟨∅, #[]⟩
  | cons : d.fvarId = fv → map[fv]? = none → d.index = arr.size →
           WF ⟨map, arr⟩ → WF ⟨map.insert fv d, arr.push d⟩
```

and the four lemmas that used to consume axioms are now proved from `Std.HashMap` /
`Array` lemmas:

| was | now |
|---|---|
| `WF.map_wf`, `WF.decls_wf`, `WF.map_toList` | **deleted** — they existed only to feed the axioms |
| `mkLocalDecl_toList` / `mkLetDecl_toList` (needed `decls.WF`) | `@[simp]`, **unconditional** |
| `WF.find?_eq_find?_toList` | proved by induction on `WF` via `Std.HashMap.getElem?_insert` |
| `WF.nodup`, `WF.toList_length` | proved by induction on `WF` |
| `TrLCtx.contains` (used `findAux_isSome`) | `Std.HashMap.contains_eq_isSome_getElem?` |

Every statement that downstream files consume kept its name and its type.

### 3.3 The environment's constant map moves to `SMap` stage 1

`Lean.Kernel.Environment.constants : SMap Name ConstantInfo` is an upstream field type and
cannot be replaced.  What *can* change is the stage.  At stage 1 all four operations this
kernel uses (`insert`, `find?`, `find?'`, `contains`) dispatch to the `Std.HashMap` half and
`map₂` is never read or written; at stage 2 every one of them reads `map₂`, and §2 shows that
even reading an *empty* `map₂` is unprovable.  So:

* `Lean4Lean/Environment/Basic.lean`: `Kernel.Environment.empty` loses its `stage₁` parameter
  and builds `constants := {}` (stage 1); `finalizeImport` uses `SMap.fromHashMap constantMap`
  (default stage 1) instead of `... false`.
* `Lean4Lean/Std/SMap.lean`: `SMap.WF` becomes `⟨stage : s.stage₁ = true, map₂ : s.map₂ = ∅⟩`
  — an invariant that `insert` preserves and that makes the whole `PersistentHashMap` half
  unreachable.  `WF.empty`, `WF.insert`, `WF.find?_insert`, `WF.toList'_insert`, `WF.find?_eq`,
  `WF.find?'_eq_find?` keep their statements; the free-standing `SMap.find?_isSome` becomes
  `SMap.WF.find?_isSome` (it needs the invariant now — at stage 2 it needs `containsAux`).
* `Lean4Lean/Std/PersistentHashMap.lean` shrinks to the one lemma that is actually provable,
  `toList'_empty` (structural recursion on the `Node` inductive), which `SMap.toList'` still
  uses.
* `Lean4Lean/Replay.lean` drops its explicit `(stage₁ := false)`; its comment is rewritten to
  record the cost rather than the old choice.
* `Lean4Lean/Verify/Bridge.lean`: `constants_empty` is now `= {}`, `constants_empty_wf` is
  `⟨rfl, rfl⟩`, `constants_empty_find?` no longer needs `PersistentHashMap.WF.empty.find?_eq`,
  and `constants_empty_ne` is **deleted** — with the empty environment at stage 1 it is
  *false*, and it had no users (documentation only).

---

## 4. Files changed (12) and who owns them

| file | owner | why |
|---|---|---|
| `Lean4Lean/Std/LocalContext.lean` (new) | me | the container |
| `Lean4Lean/Std/SMap.lean` | me | stage-1 `WF` |
| `Lean4Lean/Std/PersistentHashMap.lean` | me | trimmed to the provable lemma |
| `Lean4Lean/Environment/Basic.lean` | me | `empty` / `finalizeImport` at stage 1 |
| `Lean4Lean/LocalContext.lean` | **not me** | 1 line: the import |
| `Lean4Lean/TypeChecker.lean` | **not me** | 6 lines: `.ofLean` in the `TermElabM` lift, `.toLean` at 5 throw sites |
| `Lean4Lean/Replay.lean` | **not me** | 1 line + comment |
| `Lean4Lean/Verify/LocalContext.lean` | **not me** | the port (§3.2) |
| `Lean4Lean/Verify/TypeChecker/Basic.lean` | **not me** | 5 lines: `decls_wf.toList'_push` uses drop out |
| `Lean4Lean/Verify/Bridge.lean` | **not me** | 4 lemmas (§3.3) |
| `Lean4Lean/Verify/Primitive.lean` | **not me** | 1 line: `SMap.find?_isSome` → `hwf.find?_isSome` |
| `Lean4Lean/Verify/Environment/Checker.lean` | **not me** | 2 lines: same |

**The change is atomic** — landing only my four files breaks the build, because `Bridge.lean`
constructs the old `SMap.WF` and `Verify/LocalContext.lean` consumes the old
`Std/PersistentHashMap.lean`.  That is why nothing is landed in the main tree beyond the new,
inert `Lean4Lean/Std/LocalContext.lean` (nothing imports it, so `lake build` does not even
compile it; `lake build Lean4Lean.Std.LocalContext` does, and succeeds).

To land the rest:

```
git apply --exclude=Lean4Lean/Std/LocalContext.lean docs/handoff-containers.patch
```

`git apply --check` on that command **passes against the main tree as of this writing**, after
other streams had already changed `Lean4Lean/Verify/Environment.lean` and
`Lean4Lean/Verify/Environment/Basic.lean` (neither of which this patch touches).
`Lean4Lean/Verify/TypeChecker/Basic.lean` was under active edit by another stream while I
worked, so that hunk is the one most likely to need re-basing later.

---

## 5. Measurements

All figures are **measured**, not read off source, unless the row says otherwise.

### Before (main tree, `08e2592` + other streams' working-tree edits)

```
arena:  correct: 185 ✅   either: 6 🤷   (0 incorrect)      real 4m20s
guard 1: Axioms.lean declares exactly the 29 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (54/54 remaining) ✓
lean4lean --fresh Init.Core:  checked 3953 declarations, real 6.91s
```

### After (worktree `/home/vasilii/lean4lean-wt-containers`)

```
arena:  correct: 185 ✅   either: 6 🤷   (0 incorrect)      real 5m31s   (per-test detail in §5.1)
guard 1: Axioms.lean declares exactly the 29 frozen axioms ✓      (unchanged: the axioms are
                                                                   still declared, just unused)
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (54/54 remaining) ✓
KernelHardening: unmodelled body-less opaques in addDecl's cone: 27 (classified: 27)
                 quickCmp-ordered lookups on a decision path: 0 ([])
lean4lean --fresh Init.Core:  checked 3953 declarations, real 6.71s
```

`lake build` (everything, including `Lean4Lean.Tests.KernelHardening`) succeeds.

### Axiom dependents — the point of the exercise

Constant-dependency scan (statement + value) over the *whole* environment, i.e. a complete
search, not a grep:

| axiom | direct users before | direct users after |
|---|---|---|
| `PersistentArray.WF.toList'_push` | 5 (`LocalContext.WF.map_toList`, `LocalContext.WF.nodup`, `LocalContext.mkLetDecl_toList`, `LocalContext.mkLocalDecl_toList`, `PersistentArray.WF.toList'_length`) | **1** — only `PersistentArray.WF.toList'_length`, which is itself in `Axioms.lean` and now has **0** users |
| `PersistentHashMap.WF.toList'_insert` | 4 | **0** |
| `PersistentHashMap.WF.find?_eq` | 6 | **0** |
| `PersistentHashMap.findAux_isSome` | 1 | **0** |

### Reachable container surface from `Lean4Lean.addDecl`

Same traversal as guard 3 (used-constants closure of statement and value, following
`@[implemented_by]` and `_unsafe_rec`).  8459 constants reachable, 95 of them in the container
namespaces.  The **operations** are exactly:

* `PersistentArray`: `push` (→ `mkNewTail`, `insertNewLeaf`, `mkNewPath`).  Not `set`, `get!`,
  `modify`, `pop`, or any fold.
* `PersistentHashMap`: `insert`, `find?`, `contains` (→ their aux functions).  Not `erase`,
  `modify`, `insertIfNew`, `ofList`, `toList`, or any fold.
* `SMap`: `insert`, `find?'`, `contains`.
* `LocalContext`: `mkLocalDecl`, `mkLetDecl`, `find?`, `findFVar?`, `get!`, `mkBinding`,
  `mkForall`, `mkLambda`, `fvarIdToDecl`.

### 5.1 Arena, after

```
correct: 185 ✅   either: 6 🤷   (0 incorrect)      real 5m31s
```

**No test changed verdict** — a per-test diff over all 191 results (`_results/*.json`) shows
zero correctness differences.  Timing, summed over all 191 tests, went 252.4 s → 323.7 s
(×1.28).  The whole of that is the two large tests:

| test | before | after | ratio |
|---|---|---|---|
| `std` | 138.86 s | 193.83 s | **×1.40** |
| `init` | 84.76 s | 100.92 s | ×1.19 |
| `perf/discarded-argument-match` | 7.85 s | 8.23 s | ×1.05 |
| `perf/app-lam` | 5.34 s | 5.17 s | ×0.97 |
| everything else | < 3 s | < 3 s | ≈ ×1.0 |

Peak RSS on `init`: 560 MB → 603 MB (+8 %).

**The ratio grows with module size** (×1.19 on `init`, ×1.40 on the larger `std`), which is the
signature of the super-linear term in §6.2 starting to show.  Two points are not a curve, and
nothing at Mathlib scale was measured, so the honest statement is: the arena still passes, in
5½ minutes instead of 4⅓, and the trend is the one the theory predicts.

---

## 6. Performance: what changed and what was measured

Two containers got *worse* asymptotics in exchange for being verifiable.  Neither showed up in
the measurements above, but the second one is a real risk at Mathlib scale and upstream's own
comment predicted it.

1. **Local context.**  `Array.push` and `Std.HashMap.insert` are O(1) amortised when the
   structure is unshared and O(size) when it is shared; the local context is threaded through
   `withReader`, so an inner frame's `push` copies while the outer frame still holds the old
   value.  Local contexts are telescope-sized (tens of entries), so this is noise — and it is
   what the `--fresh Init.Core` timing above exercises.
2. **Environment constant map.**  This is the one to watch.  `Lean4Lean/Replay.lean` used to
   say, in a comment that is now rewritten:

   > `stage₁ := false` is very important here: while a declaration is being added the
   > environment is also held by the replay state, so the map is shared and `stage₁ := true`
   > would lead to quadratic performance.

   That is exactly the trade being made.  At stage 2 an added constant goes into the
   `PersistentHashMap`, which shares structure; at stage 1 it goes into a `Std.HashMap` whose
   bucket array is copied on every shared insert — O(n) per declaration, O(n²) overall.
   Measured at n ≈ 4000 (`--fresh Init.Core`): **no regression at all** (6.71 s vs 6.91 s).
   Measured on the arena's two largest tests: `init` ×1.19, `std` ×1.40 — the ratio grows with
   module size, which is the term showing up.  **Not measured at Mathlib scale (n ≈ 2·10⁵),**
   where a ×1.4-and-rising trend is the thing to watch.  If that matters, the
   fix is to remove the *sharing* rather than the stage — `Lean4Lean/Replay.lean` holding the
   environment in its state alongside `addDecl` is what forces the copy — and that is a
   `Replay.lean` change, not a container change.

Both go in `divergences.md`; the exact text to append is in §8.

---

## 7. The `Verify/Axioms.lean` and `Verify/Guard.lean` edits — stated, not made

### 7.1 `Lean4Lean/Verify/Axioms.lean`

Delete these three blocks (line numbers as of `Axioms.lean` md5 `9d8d80be0d6d8654c783a937f531d773`; do them **bottom-up** so earlier numbers stay valid):

* **lines 50–71** — the doc comment `/-- We cannot prove this because `insertNewLeaf` is
  partial. … -/` and the axiom it documents:

  ```lean
  @[simp] axiom WF.toList'_push {α} {arr : PersistentArray α} (h : WF arr) (x : α) :
      (arr.push x).toList' = arr.toList' ++ [x]
  ```

* **lines 78–82** — the theorem that depends on it, which has no other users:

  ```lean
  @[simp] theorem WF.toList'_length (h : WF arr) : arr.toList'.length = arr.size := by
    induction h with
    | empty => simp
    | push h ih => simp [h.toList'_push, ih]
  ```

* **lines 103–117** — all three `PersistentHashMap` axioms with their doc comments (117 is the blank line before `end PersistentHashMap`):

  ```lean
  /-- We can't prove this because `Lean.PersistentHashMap.insertAux` is opaque -/
  axiom WF.toList'_insert …
  /-- We can't prove this because `Lean.PersistentHashMap.findAux` is opaque -/
  axiom WF.find?_eq …
  /-- We can't prove this because `Lean.PersistentHashMap.{findAux, containsAux}` are opaque -/
  axiom findAux_isSome …
  ```

Nothing else has to move.  `PersistentArrayNode.toList'`, `PersistentArray.{toList', WF,
toList'_empty, size_empty, size_push, bad}` and `PersistentHashMap.{Node.toList', WF}` become
dead but are harmless; `PersistentHashMap.toList'` must **stay**, because `SMap.toList'` still
mentions it.  Deleting the dead ones is optional and can be a separate sign-off.

### 7.2 `Lean4Lean/Verify/Guard.lean`

Remove these four lines from `frozenAxioms`:

```lean
  `Lean.PersistentArray.WF.toList'_push,
  `Lean.PersistentHashMap.WF.find?_eq,
  `Lean.PersistentHashMap.WF.toList'_insert,
  `Lean.PersistentHashMap.findAux_isSome,
```

and change `29` to `25` at lines 12, 17, 35, 182, 199, 205 and 218 (`grep -n 29
Lean4Lean/Verify/Guard.lean` finds exactly these plus the historical re-pin notes at lines 46,
50 and 63, which are prose about earlier counts and must **not** be touched).  A new re-pin
paragraph for the `frozenAxioms` doc comment:

> Re-pinned again from 29 to 25: the four container axioms
> (`Lean.PersistentArray.WF.toList'_push`, `Lean.PersistentHashMap.WF.toList'_insert`,
> `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.findAux_isSome`) were
> **deleted**.  They were the whole of class (B) — the only assumptions in the trusted base
> with no model — and they were unprovable because the upstream `PersistentArray` and
> `PersistentHashMap` helpers are `partial`, hence `opaque`, hence have no defining equations
> at all.  Rather than assume them, the checker no longer uses those containers: the local
> context is now `Std.HashMap` + `Array` (`Lean4Lean/Std/LocalContext.lean`) and the
> environment's constant map is kept at `SMap` stage 1, where every operation dispatches to the
> verified `Std.HashMap` half.  See `docs/handoff-containers.md`.

### 7.3 How to verify after landing

I did **not** edit `Axioms.lean` or `Guard.lean`, not even in the worktree — the freeze admits
no exceptions for subagents.  The evidence that the deletions are safe is the dependent scan in
§5: an axiom with zero dependents can be removed without affecting any other declaration, and
the only in-file user of `toList'_push` (`toList'_length`) is deleted with it and itself has
zero users, so `Axioms.lean` still elaborates.  After the frozen edits, the check is simply

```
lake build Lean4Lean.Verify.Guard
# expect: guard 1: Axioms.lean declares exactly the 25 frozen axioms ✓
#         guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
#         guard 3: checker cone implementation gaps within frozen list (54/54 remaining) ✓
```

---

## 8. `divergences.md` — text to append **when the patch lands**

Not appended yet: until the patch is applied these statements would describe a tree that does
not behave that way.

> * [`Lean4Lean.LocalContext`](Lean4Lean/Std/LocalContext.lean): the kernel's local context is a
>   `Std.HashMap FVarId LocalDecl` plus an `Array (Option LocalDecl)`, where the C++ kernel (and
>   `Lean.LocalContext`) uses a persistent hash-array-mapped trie and a persistent array. Every
>   operation the kernel performs returns the same value; the `auxDeclToFullName` field, which
>   the kernel never writes, is dropped. Complexity differs: `Array.push`/`Std.HashMap.insert`
>   are O(1) amortised when unshared but copy when shared, and the context is shared across
>   `withReader` frames, so building an n-binder telescope is O(n²) rather than O(n log n).
>   Local contexts are telescope-sized. The
>   `Lean.Kernel.Exception` payloads still carry a `Lean.LocalContext`, rebuilt at the throw
>   site, so error messages are unchanged.
> * [`Lean.Kernel.Environment.empty`](Lean4Lean/Environment/Basic.lean), `finalizeImport`: the
>   constant map is built at `SMap` **stage 1**, so added constants go into the `Std.HashMap`
>   half rather than the `PersistentHashMap` half. Lookups agree exactly. Complexity differs and
>   upstream's own comment in `Lean4Lean/Replay.lean` named it: the replay state holds the
>   environment while a declaration is being added, so the map is shared and each insert copies
>   its bucket array — O(n) per declaration, O(n²) for a whole module, against O(log n) per
>   declaration for the persistent map. Measured: `--fresh Init.Core` (n ≈ 4000) is unchanged
>   (6.71 s vs 6.91 s), the Kernel Arena's `init` test is ×1.19 and its larger `std` test ×1.40,
>   so the ratio grows with module size; it has not been measured at Mathlib scale.
>   Both changes exist to remove the four `PersistentArray`/`PersistentHashMap` axioms, whose
>   subjects are `partial` upstream and therefore `opaque`: nothing at all can be proved about
>   them. See `docs/handoff-containers.md`.

---

## 9. Housekeeping

* Worktree: `/home/vasilii/lean4lean-wt-containers`, created with `git worktree add --detach`
  (no branch, no commit, no push).  Delete with
  `git worktree remove --force /home/vasilii/lean4lean-wt-containers` once the patch is applied.
* The temporary arena checker (`~/lean-kernel-arena/checkers/lean4lean-wt.yaml`, its 8.2 GB
  build copy under `_build/checkers/`, and its 191 `_results/lean4lean-wt_*.json` files) was
  created for the measurement in §5.1 and has been **removed again**; the arena checkout is
  back to exactly the files it had, with the `lean4lean-local` baseline results intact.
* `Lean4Lean/Std/LocalContext.lean` is the only file added to the main tree.  Nothing imports
  it, so `lake build` ignores it; `lake build Lean4Lean.Std.LocalContext` compiles it and
  succeeds.  It is inert until the patch is applied.
