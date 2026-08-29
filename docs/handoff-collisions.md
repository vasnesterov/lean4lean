# Handoff: the `PatternRules` / `Verify` import wall is down

**Status: resolved.** `Lean4Lean/Theory/Typing/PatternRules.lean`'s import cone and
`Lean4Lean/Verify/`'s import cone now compile in a single file. Standing regression test:
`Lean4Lean/Experimental/ConeJoin.lean` (`lake build Lean4Lean.Experimental.ConeJoin`).

## 1. How the collision set was measured

Not by grep. A script loads each cone with `importModules` into its own `Environment`,
enumerates `env.constants.map₁` and tags every name with `env.getModuleIdxFor?`, then the
two name→module tables are intersected. A name is a *candidate* collision iff it appears in
both tables with **different** source modules.

Script (kept in the session scratchpad, reproduce with `lake env lean --run`):

```lean
import Lean
open Lean
def dumpCone (mods : Array Name) (out : System.FilePath) : IO Unit := do
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  let names := env.header.moduleNames
  let mut lines : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    let modStr := match env.getModuleIdxFor? n with
      | some i => (names[i.toNat]!).toString
      | none => "<local>"
    lines := lines.push s!"{n}\t{modStr}"
  IO.FS.writeFile out (String.intercalate "\n" lines.toList)
def main (args : List String) : IO Unit :=
  dumpCone ((args.tail!).toArray.map (·.toName)) args.head!
```

Then `LC_ALL=C sort -t$'\t' -k1,1` each table and `join`, keeping rows whose two module
columns differ. (Do **not** omit `LC_ALL=C`: a locale-collated `sort` desynchronises `join`
and yields ~1000 phantom rows. That is how the "15 names / 7 declarations" figure in the
previous relay was inflated.)

Cones measured: `Lean4Lean.Theory.Typing.PatternRules` versus
`Lean4Lean.Verify.TypeChecker` + `Lean4Lean.Verify.Environment`.

## 2. The measured set — before

**22 candidate names.** Only **12 of them are hard collisions** (Lean actually refuses the
import); the other 10 are *realized* constants, which Lean's importer deduplicates instead
of rejecting. The distinction is not cosmetic and was not in the previous relay.

### Hard collisions — 12 names from 5 source declarations

| name | Theory side | Verify side |
|---|---|---|
| `VEnv.addDefEqs_le` (+ `._f`, `.match_1_1`) | `Theory/Typing/DeltaUnique.lean:773` | `Verify/Environment/Lemmas.lean:181` |
| `VEnv.addConst_defeqs` | `Theory/Typing/DeltaUnique.lean:75` | `Verify/TypeChecker/Reduce.lean:141` |
| `VEnv.addConsts_defeqs` (+ `._f`, `.match_1_1`) | `Theory/Typing/DeltaUnique.lean:576` | `Verify/TypeChecker/Reduce.lean:145` |
| `VEnv.addDefEqs_defeqs` (+ `._f`, `.match_1_1`) | `Theory/Typing/DeltaUnique.lean:777` | `Verify/TypeChecker/Reduce.lean:157` |

(`._f` is the structural-recursion helper, `.match_1_1` the match auxiliary; they are
declared eagerly with the theorem, so they collide with it and disappear with it.)

A fifth, latent duplication of the same four statements sat in
`Theory/Typing/DeclRules.lean` under `_eq` names (`addConst_defeqs_eq`,
`addConstList_defeqs_eq`, `addConsts_defeqs_eq`) — a workaround whose file comment says in
so many words that it exists *because* of this collision. Removed too (§3).

### Not collisions — 10 realized constants

`Lean.mkRecName.eq_1`; `VInductDecl'.ctorsAll.eq_1`; `VInductDecl'.selfLvls.eq_1`;
`List.lookup.eq_1/.eq_2/.eq_def`; and six `Std.DHashMap.Internal.Raw₀.*.congr_simp`.
These are equation/congruence lemmas generated on demand (`realizeConst`) and cached in
whichever module first needed them, so the same name legitimately lives in two `.olean`s.
Proof that they are harmless: eight of the ten *already* appear twice inside a single cone
that compiles today (e.g. `Theory/Inductive/Lemmas.lean` and `Theory/Inductive/Structure.lean`
are both in both cones), and the acceptance test in §4 compiles with all ten still present.

**Correction to the previous relay.** The two "colliding equation lemmas across
`Theory/Inductive/Lemmas.lean` and `Theory/Inductive/Structure.lean`" are
`VInductDecl'.ctorsAll.eq_1` and `VInductDecl'.selfLvls.eq_1`; they are realized constants
and were never blocking anything. They needed no fix, and restructuring their generating
definitions would have been wasted work. Likewise `HasArgs.defeqDFC` is declared **only** in
`Theory/Typing/PatternRules.lean` — there is no second declaration of that name anywhere in
the tree, so it was never a collision either.

So: **5 blocking declarations, not 7; 12 blocking names, not 15.**

## 3. What was done — all five deduplicated, none renamed

Every colliding pair was the **same statement**, so `rename` was never needed. Checked one
by one:

- `addConst_defeqs` — identical statement and identical proof
  (`unfold VEnv.addConst at h; split at h <;> cases h; rfl`). The `Verify/` copy left `n`
  and `ci` to **auto-bound implicits** (no `variable` line in `Reduce.lean`); binder *order*
  therefore differed, the proposition did not.
- `addConsts_defeqs` — same statement, cosmetically different proofs of the `[]` case.
- `addDefEqs_defeqs` — same statement, same proof modulo one `rw [VEnv.addDefEqs, …]` the
  `Verify/` copy performed explicitly.
- `addDefEqs_le` — same proposition; the `Theory/` copy took `(cis) (env)` **explicit**, the
  `Verify/` copy `{cis'} {venv}` implicit.
- `addConstList_defeqs` — one copy in `DeltaUnique.lean`, one in `DeclRules.lean` under
  `addConstList_defeqs_eq`.

**No collision turned out to be two different statements sharing a name**, so nothing was
being silently shadowed at a call site. That was the failure mode worth looking for; it did
not occur here.

Canonical home: **`Lean4Lean/Theory/Typing/EnvLemmas.lean`** — the deepest module both cones
already import (`Verify/Environment/Basic.lean` imports it directly; `DeltaUnique.lean` and
`DeclRules.lean` import it directly). All binders implicit, matching the `Verify/` call
style, which is the majority of call sites.

Diff (net **−40 lines**, all mechanical):

| file | change |
|---|---|
| `Theory/Typing/EnvLemmas.lean` | **+** the five canonical theorems |
| `Theory/Typing/DeltaUnique.lean` | **−** `addConst_defeqs`, `addConsts_defeqs`, `addConstList_defeqs`, `addDefEqs_le`, `addDefEqs_defeqs` |
| `Verify/Environment/Lemmas.lean` | **−** `VEnv.addDefEqs_le` |
| `Verify/TypeChecker/Reduce.lean` | **−** `VEnv.addConst_defeqs`, `VEnv.addConsts_defeqs`, `VEnv.addDefEqs_defeqs` |
| `Theory/Typing/DeclRules.lean` | **−** the three `_eq` clones; call sites renamed to the canonical names; stale file comment updated |
| `Theory/Typing/PatternRules.lean` | `(VEnv.addDefEqs_le cis _)` → `VEnv.addDefEqs_le` (binders became implicit) |
| `Theory/Inductive/Nested.lean` | `(VEnv.addDefEqs_le _ _)` → `VEnv.addDefEqs_le` (ditto) |
| `Verify/InductFlip.lean` | comment only: its §4 note asserted the wall as a live fact |

No proof was "improved" while in there. No `sorry` added or removed (per-file counts
unchanged). No frozen file touched.

## 4. Acceptance test

`Lean4Lean/Experimental/ConeJoin.lean` imports `Theory.Typing.PatternRules`,
`Theory.Typing.ParamsBuild`, `Verify.TypeChecker`, `Verify.Environment` **and**
`Verify.Soundness`, and `#check`s a representative from each. It builds:

```
$ lake build Lean4Lean.Experimental.ConeJoin
ℹ [1215/1215] Built Lean4Lean.Experimental.ConeJoin (1.6s)
@VEnv.paramsOfWF : {env : VEnv} → env.WF → (U : ℕ) → env.PatWF U → VEnv.Params
@VEnv.IsDefEq.church_rosser : ∀ {Γ : List VExpr} [inst : VEnv.Params], …
kernel_sound : ∀ (ds : List Lean.Declaration) (fuel : FuelConfig) …
@VEnv.HasArgs.defeqDFC : …
Build completed successfully (1215 jobs).
```

It is deliberately **not** in `defaultTargets`, so it costs the normal build nothing; build
it explicitly when touching either cone.

Re-measurement after the fix (`PatternRules` + `ParamsBuild` versus `Verify.TypeChecker` +
`Verify.Environment` + `Verify.Soundness`): **12 candidate names, 0 hard collisions** — the
12 are exactly the realized constants listed in §2, and the acceptance test compiles.

## 5. What is now reachable from `Verify/` that was not

**Yes, `VEnv.paramsOfWF` is reachable — measured, not inferred.** Adding
`import Lean4Lean.Theory.Typing.ParamsBuild` as the first line of the real, non-frozen
`Lean4Lean/Verify/Environment.lean` and running `lake build Lean4Lean.Verify.Environment`
succeeds (`Built Lean4Lean.Verify.Environment (2.1s)`). The import was reverted — this was a
measurement, not a change; a consumer should add it when it has a use.

Before the fix, `Theory/Typing/DeltaUnique`, `Theory/Typing/PatternDecode` and
`Theory/Typing/PatternRules` were the **only three** `Lean4Lean` modules in the `PatternRules`
cone that the `Verify/` cone did not already contain — every other Theory module was shared.
So the wall was three modules wide, and with it down the whole of `ParamsBuild`,
`ChurchRosser` and the head-reduction machinery underneath them is now importable into any
non-frozen `Verify/` module.

**What this does *not* yet do — read this before claiming progress on goal 2.**
`Verify/Soundness.lean` imports exactly two things: `Lean4Lean.Environment` and
`Foundation.FirstOrder.SetTheory.InaccessibleCardinal`. It does **not** import
`Lean4Lean.Verify.*` at all, and `kernel_sound`'s proof is a bare `sorry`. So there is at
present *no* import path from `paramsOfWF` to the file that must prove `kernel_sound` —
removing the collision was necessary, not sufficient. The honest claim is: the wall between
the two halves of the development is gone, and any non-frozen `Verify/` module can now be
the bridge.

## 6. Needs the human

**One item, and it is not caused by this change.** Whoever eventually proves `kernel_sound`
must add an import to `Lean4Lean/Verify/Soundness.lean`, which is frozen. The edit would be a
single line at the top of that file — an `import` of whichever non-frozen `Verify/` module
carries the proof (today the natural candidate is `Lean4Lean.Verify.Environment`). No such
edit is proposed now and none was made; flagging it because this work removes the *other*
obstacle and leaves that one as the next structural blocker.

Nothing in this change touches Guard's whitelist or allowlist: the five canonical lemmas are
`Theory`-side propositions with no executable content, and none of the renamed/removed names
appears in `Verify/Guard.lean`.

## 7. Build state

```
Build completed successfully (1340 jobs).
guard 1: Axioms.lean declares exactly the 25 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (54/54 remaining) ✓
```

Identical to the pre-change baseline in every number.
