# Handoff: the inductive side — the sorry inventory, the false branch, and the nested wall

Scope: the five `sorry`s the brief assigned to this stream, the `AddInduct` flip's true file
set, `addDecl.WF`'s `inductDecl` branch, and the safety gate.

New file, owned: **`Lean4Lean/Verify/Inductive/AddDeclWF.lean`** (42 declarations, 0
`sorryAx`, axioms `propext`/`Classical.choice`/`Quot.sound` only).
Edited, owned: `Lean4Lean/Verify/Environment/Lemmas.lean` (one statement corrected, §5.2).

Build state at the end of this stream: `lake build Lean4Lean Lean4Lean.Verify
Lean4Lean.Theory` green, 1292 jobs, no new `sorry`, no new axiom, no frozen file touched.

Everything below is either **[MC]** machine-checked (a Lean proof in this tree, named), **[EV]**
checked by evaluation (a `#eval` that fails the build on regression — a test, not a proof), or
**[SRC]** read off source without a proof.

---

## 0. The headline

**(a) The five `sorry`s do not exist.**  There is no `sorry` in any file this stream owns —
not in `Verify/Inductive/Add.lean`, not in `Verify/InductFlip.lean`, not in
`Verify/Environment/{Basic,Lemmas,Induct}.lean`.  §1 has the measurement.

**(b) The flip does not fix the nested case, and the obstruction is not the one the tree
records.**  `Verify/Environment/Induct.lean` says nested blocks are outside `TrIndDecl`
because the declaration is not recoverable.  That is true and beside the point: the checker's
nested path adds a recursor constant (`T.rec_1`) that **no** `VInductDecl'` translating the
block can name, so `AddInductStages` — the flip's intended `AddInduct` — is *refuted*, not
merely unproved, for a nested block.  `Theory/Inductive/NestedBuild.lean` closes the
declaration side and leaves this one untouched, because the obstruction is on the
constant-map side.

* `tBlock_not_addInductStages` **[MC]** — for the concrete nested block `inductive T | mk :
  Box T → T`, no `D` with `TrIndDecl … [tIndType] false D` stands in `AddInductStages`
  between a map without `T.rec_1` and one with it.
* check B in `AddDeclWF.lean` §4 **[EV]** — the checker's own output *is* such a pair of maps
  (`T.rec_1` absent before, present after, `T.numNested = 1`).

**(c) `Aligned.addInduct`'s statement was false, not weak** — and it is in an owned file, so
it is fixed.  See §5.2.  `docs/handoff-addinduct.md` §1.1 filed it under "statements that stay
true after the flip"; it does not.

---

## 1. The sorry inventory

Measured, not grepped: transitive `sorryAx` reachability over the whole environment's
`getUsedConstantsAsSet` graph (the `deps` function of `scripts/cone-measure.lean`, with the
`.thmInfo` / `allowOpaque := true` trap handled), reverse-BFS from `sorryAx`.

| module | declarations | `sorryAx`-tainted | written `sorry`s |
|---|---|---|---|
| `Verify/Inductive/Add.lean` | 214 | **5** | 0 |
| `Verify/InductFlip.lean` | 51 | 0 | 0 |
| `Verify/Inductive/AddDeclWF.lean` (new) | 42 | 0 | 0 |
| `Verify/Environment/Basic.lean` | 109 | 0 | 0 |
| `Verify/Environment/Lemmas.lean` | 60 | 0 | 0 |
| `Verify/Environment/Induct.lean` | 31 | 0 | 0 |

The five tainted declarations in `Verify/Inductive/Add.lean` **[MC]**:

`AddInductive.M.WF.ensureType`, `.whnf`, `.field_step`, `.elim_field_step`, `.positivity_none`.

All five are tainted *by inheritance*, through
`TypeChecker.{ensureType,checkType,isDefEq,whnf}.WF`, i.e. through the five declared `sorry`s
in `Verify/TypeChecker/{InferType,IsDefEq,WHNF}.lean` — another stream's files.  Nothing in
this stream's files adds taint, and there is nothing here to close: closing them is the
type-checker stream's work.

The brief's "4 `sorry`s in `Add.lean`, 1 in `InductFlip.lean`" is a stale relay.  The most
likely origin is this table's middle column read as the left one.

---

## 2. `addDecl.WF`'s `inductDecl` branch

### 2.1 It is false, and here is the proof obligation split

`Verify/Environment.lean:248` carries `| inductDecl _ _ _ _ => sorry` against the uniform
postcondition

```lean
fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

* `addDecl_inductDecl_post_false` **[MC]** — that postcondition is `False` at any `env'` whose
  map holds an `.inductInfo` (one line from `VEnvs.WF.no_inductInfo`).
* `addDecl_inductDecl_WF_false` **[MC]** — therefore the branch is refuted outright, *given*
  that the checker accepts one inductive declaration from one modelled environment.
* check A **[EV]** — it does: `addDecl (Kernel.Environment.empty `main) uDecl` with `uDecl =
  inductive U : Type | unit : U` returns `.ok`, and the output map holds a safe `.inductInfo`
  at `R10.Wit.U`.  `Bridge.hasEmptyModel` supplies the `ves.WF env` side.

Why check A is a test and not a proof: `addDecl` does not reduce in the kernel.  `by rfl` on
`isOkB (addDecl (Environment.empty `main) uDecl)` fails in two seconds, at an irreducible
head, so short of `native_decide` — which `Verify/Guard.lean` forbids — there is no way to
make it one.  This is recorded so the next stream does not spend the attempt again.

### 2.2 There is no branch-local restatement

`addDecl.WF`'s conclusion is uniform across the constructors of `Declaration`.  One cannot
weaken the `inductDecl` arm and leave the others alone: what must change is a definition the
postcondition quantifies over, and the minimal such change is `AddInduct`'s.  With
`AddInduct := AddInductStages`, the branch's statement is **true as written** for a safe,
non-nested block, and the work it needs is the obligation of §2.3.  For the other two shapes
the statement stays false however `AddInduct` is defined, for reasons §3 and §0(b) give.

### 2.3 The obligation that replaces the `sorry`

In `AddDeclWF.lean` §3, and it elaborates, so the shape is checked rather than described:

```lean
def InductStepSafe (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∃ D : VInductDecl',
    TrIndDecl venv lp np types false D ∧ D.WF venv ∧ AddInductStages m venv D m' venv'

def AddInductiveObligation : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig),
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        env'.quotInit = env.quotInit ∧
        ∃ ves' : VEnvs, ∀ safety,
          InductStepSafe env.constants env'.constants (ves.venv safety) (ves'.venv safety)
            lp np types
```

Three conjuncts, none redundant: `TrIndDecl` says the abstract declaration describes the
syntax the user wrote, `VInductDecl'.WF` says it is a legitimate declaration,
`AddInductStages` says the checker's output map and the abstract environment are the ones
that declaration builds.

It is a **definition of the output map, not a check on it** — the shape
`Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` demands and `fooComp_WFC` showed a
re-staged check does not achieve.  `InductStepSafe.find?_of_not_mem` **[MC]** is that
property at the level the branch consumes it: outside `indDeclNames types` the map is
unchanged, so a `VInductDecl'` that under-reports its constructors cannot be paired with the
map the checker produced.

Supporting lemmas, all **[MC]**: `InductStepSafe.induct_premises` (exactly what `TrEnv'.induct`
consumes post-flip), `.le`, `.map_wf`, `.find?_of_not_mem`.

### 2.4 Non-vacuity: the obligation has a model

`R10.Wit` supplied `decl.WF VEnv.empty` and `AddInductStages` but never the *syntactic* half,
so the two had never been joined.  They are joined now:

* `R10.Wit.trIndDecl_wit : TrIndDecl VEnv.empty [] 0 [uIndType] false decl` **[MC]**
* `R10.Wit.inductStepSafe_wit` **[MC]** — for any well-formed empty constant map,
  `∃ m' venv', InductStepSafe m m' VEnv.empty venv' [] 0 [uIndType]`.

So `AddInductiveObligation` is not vacuously satisfiable-looking; its per-safety body has a
closed instance at a real one-constructor block, with the constructor obligation discharged by
a `VIndCtor.WF` rather than dodged by `absurd`.

---

## 3. The safety gate: wired on the abstract side, blocked on the flip

`AddIndConsts.cons` carries `TrConstant .safe`, and `AddIndConsts.find?` already turns that
into `ci.safety = .safe`.  `docs/handoff-addinduct.md` §3 calls that "the whole gate, and it
is already written".  It *was* written, but only in `ConstantInfo.safety`'s vocabulary, never
in the checker's, which is `InductiveVal.isUnsafe`.  Reading it back is §1 of the new file:

* `ConstantInfo.safety_ctorInfo`, `.safety_recInfo` **[MC]** (the `.inductInfo` case already
  existed in `Verify/EqSafety.lean`)
* `AddInductStages.inductInfo_not_unsafe`, `.ctorInfo_not_unsafe`, `.recInfo_not_unsafe`
  **[MC]** — any constant of the three shapes that `AddInductStages` *introduces* (as opposed
  to one already in the map) has `isUnsafe = false`.

**What blocks the wiring**: nothing but the flip.  `TrEnv'.induct` is the only consumer, and
it takes `AddInduct`, which is empty.  The gate is therefore complete and inert; the flip
turns it on, and §4 says exactly which files the flip needs.

### 3.1 The hole the gate does not close, and the flip does not either

`unsafe_induct_unreachable` **[MC]** states both halves in one theorem:

1. `AddInductStages` never introduces an unsafe `.inductInfo`, so a flipped `TrEnv'.induct`
   cannot take an unsafe block at *any* safety level;
2. `∀ ci, .unsafe ≤ ci.safety`, so `TrEnv'.ignore`'s premise `¬ safety ≤ ci.safety` fails for
   every constant at `safety = .unsafe` and `ignore` cannot take it either.

So `TrEnv' .unsafe` has no rule at all for an unsafe inductive, before or after the flip, and
`addDecl.WF`'s `inductDecl` branch is false at `isUnsafe = true` for that reason alone.  Two
files still carry the false claim that "unsafe blocks are taken by `TrEnv'.ignore` instead"
(`Theory/Inductive/Decl.lean`'s R10 handover; `Verify/Environment/Induct.lean`'s `TrIndDecl.safe`
docstring already carries the correction).

Closing it is a **design decision, not a proof obligation**, and it is independent of
`AddInduct`.  Two shapes:

* a `TrEnv'` rule that is the inductive analogue of `unsafeDef` — admit the block's constants
  without a positivity witness, gated on a member being unsafe.  This needs a matching
  `VDecl`, i.e. Theory-side work; note the recursor types of a non-nested block are *not*
  `checkType`d by `Environment.addInductive` **[SRC]** (only the nested path re-checks them),
  so `VDecl.axiom`'s `ci.WF env` premise is not free.
* or a `VEnvs.WF` that does not demand a model at `.unsafe`.  Nothing downstream of
  `addDecl.WF` consumes the `.unsafe` model — `Bridge.foldAddDecl_tr` takes `.safe` **[SRC]** —
  but `addMutual.WF` uses `wf.toVEnvAt v₀.safety` while checking an unsafe block **[SRC]**, so
  this is a real trade, not free.

---

## 4. The flip: assessment with current ownership

**Verdict: still not landable within this stream's files.  Do not half-land it.**

The 2-of-7 ownership split of `docs/handoff-addinduct.md` §6 has changed but not enough.  The
current, re-measured file set:

| # | file | owned? | what the flip does to it |
|---|---|---|---|
| 1 | `Verify/Environment/Basic.lean` | **yes** | `inductive AddInduct` → `def AddInduct := AddInductStages`; `to_addInduct := AddInductStages.to_addInduct` |
| 2 | `Verify/Environment/Lemmas.lean` | **yes** | `Aligned.addInduct`'s `nomatch H` → `Aligned.addInductStages`; `TrEnv'.of_value`'s induct arm → `AddInductStages.of_value_arm` |
| 3 | `Verify/SafeFragment.lean` | no | `AddInduct.le`'s `nomatch H` → `AddInductStages.le` (one line) |
| 4 | `Verify/Environment/Extension.lean` | no | delete `TrEnv'.no_inductInfo` (becomes false) |
| 5 | `Verify/TypeChecker/Reduce.lean` | no | `find?_shape` ×2 and `defeqs_shape` gain disjuncts; delete `TrEnv.not_inductInfo`/`.not_ctorInfo`/`.not_recInfo`/`VContext.not_inductInfo`; delete-or-`sorry` `reduceProjCore_none`/`reduceProjCore.WF`; **move** `Aligned.addInductStages` up to (2) |
| 6 | `Verify/TypeChecker/WHNF.lean` | no | `inductiveReduceRec_eq_none` dies |
| 7 | `Verify/TypeChecker/InferType.lean` | no | `inferProj_always_throws` dies |
| 8 | `Verify/TypeChecker/IsDefEq.lean` | no | `tryEtaStructCore_never_true` dies (`isDefEqUnitLike_never_true` with it) |

**Correction to `docs/handoff-addinduct.md` §6.**  Its item (3), `Verify/Environment.lean`, is
**no longer part of the patch**: `checkEqType.WF` is already
`checkEqType.WF_quotReady_closed`'s statement and `addQuot.WF` is already `addQuot.WF'`
(commit `3e8e6ea`), and neither proof cases on `AddInduct` **[SRC]**, confirmed by a
tree-wide grep: the only *proof-level* uses of `AddInduct` outside owned files are rows 3–8.
So the count went 7 files (4 unowned) → 8 files (6 unowned), because the three
`Verify/TypeChecker/` leaves are counted separately here and `Verify/Environment.lean` dropped
out.

**Why `Aligned.addInductStages` cannot be smuggled into an owned file**: duplicating it in
`Lemmas.lean` under the same name breaks `Reduce.lean` with `environment already contains`;
duplicating it under a different name buys nothing, since `Reduce.lean` needs editing anyway
for row 5.

The human's standing ruling (do not take the nine `Verify/TypeChecker/` `sorry`s yet) is
**reinforced**, not weakened, by §0(b): the flip now buys strictly less than the previous
measurement suggested, because it does not make `addDecl.WF`'s `inductDecl` branch true for a
nested declaration either.  The order that makes sense is: fix `AddInduct` for nested blocks
first (§6.1), *then* flip once, *then* take the nine.

---

## 5. Corrections to standing claims

Each is machine-checked here unless marked.

| where | claim | correction |
|---|---|---|
| the brief | 4 `sorry`s in `Verify/Inductive/Add.lean`, 1 in `Verify/InductFlip.lean` | Zero, in both.  Five declarations in `Add.lean` are `sorryAx`-*tainted*, through the type checker (§1). |
| `docs/handoff-addinduct.md` §1.1 | `Aligned.addInduct` is tier 1 — "statement stays true after the flip" | False; it was tier 2.  See §5.2. |
| `docs/handoff-addinduct.md` §6 (3) | `Verify/Environment.lean` is part of the flip patch | Not any more (§4). |
| `docs/handoff-addinduct.md` §7.2 / `Verify/Environment/Basic.lean` §R10 | the flip's only remaining cost is the nine `Verify/TypeChecker/` declarations | Understates it: `AddInductStages` is *refuted* for a nested block (§0b), so the flip leaves `addDecl.WF`'s `inductDecl` branch false for every nested declaration. |
| `Verify/Environment/Induct.lean` module docstring | nested blocks are outside `TrIndDecl` because "`addInductive` discards the auxiliary environment and rebuilds" | Correct but not the binding obstruction; the binding one is on the constant-map side (§6.1). Not edited — the paragraph is not wrong, only incomplete. |

### 5.2 `Aligned.addInduct` — fixed in place

It read

```lean
theorem Aligned.addInduct (H : AddInduct C₁ venv₁ decl C₂ venv₂) :
    Aligned safety C₁ env₁ → Aligned safety C₂ env₂ := nomatch H
```

with `env₁`/`env₂` **auto-bound implicits unrelated to `venv₁`/`venv₂`**.  As written it says
an inductive step carries alignment between two *arbitrary* abstract environments — a false
statement, provable only because `AddInduct` is empty.  Now:

```lean
theorem Aligned.addInduct {C₁ C₂ : ConstMap} {venv₁ venv₂ : VEnv} {decl : VInductDecl'}
    (H : AddInduct C₁ venv₁ decl C₂ venv₂) :
    Aligned safety C₁ venv₁ → Aligned safety C₂ venv₂ := nomatch H
```

`TrEnv'.aligned`'s `induct` arm (`ih.addInduct h`) is unchanged and the tree is green.  This
matters beyond hygiene: `Aligned.find?` — hence `TrEnv.find?`, hence
`checkEqType.WF_quotReady_closed` and `Bridge.hasType_falseProp` — reaches the inductive case
only through `Aligned.addInduct`, so the flip's arm for it has to be the *named-environment*
statement or the whole `find?` chain silently proves nothing.

---

## 6. What to pick up next

1. **`AddInduct` for nested blocks.**  Now the first item, ahead of the flip.  The checker's
   nested path (`Lean4Lean/Inductive/Add.lean`, everything after `if numNested = 0 then return
   env'`) rebuilds from the *pre-block* environment and adds, per auxiliary nested type, one
   renamed recursor (`mkAuxRecNameMap`: `_nested.J.rec` ↦ `I.rec_1`, `I.rec_2`, …) **[SRC]**,
   observed as `T.rec_1` **[EV]**.  Two shapes, and the choice is a design decision:
   * a fourth `AddIndConsts` stage over an explicit auxiliary-recursor list, with the list a
     *function* of the block (so it stays a definition of the map, not a check on it);
   * or auxiliary recursors as a field of `VInductDecl'`, which pushes the choice into
     `Theory/`.
   `Theory/Inductive/NestedBuild.lean`'s `replaceIfNested`-as-a-construction is the
   declaration side of this and is already done; only the constant-map side is open.
2. **`AddInductiveObligation` (§2.3).**  The refinement of `Environment.addInductive`.  This
   is where `Verify/Inductive/Add.lean`'s R1–R10 framework is aimed; note that **nothing in
   `Verify/` refines the top-level `Environment.addInductive` today** — the framework covers
   `AddInductive.M` and its phases, not the wrapper.  In particular no lemma yet says the
   successful wrapper inserts the block's `.inductInfo`s, which is why §2.1's second half is
   `[EV]` rather than `[MC]`.
3. **The `.unsafe` rule (§3.1).**  Independent of everything above; needs a decision from the
   human between the two shapes.
4. **The flip (§4)**, once 1 is done, as one coordinated commit across eight files, six of
   them unowned by this stream.

---

## 7. Inventory of what this stream proved

All in `Lean4Lean/Verify/Inductive/AddDeclWF.lean` unless marked, all `sorryAx`-free (42
declarations, transitive check), axioms `propext`/`Classical.choice`/`Quot.sound` only.

*§1 the safety gate.*  `ConstantInfo.safety_ctorInfo`, `.safety_recInfo`;
`AddInductStages.inductInfo_not_unsafe`, `.ctorInfo_not_unsafe`, `.recInfo_not_unsafe`;
`unsafe_induct_unreachable`.

*§2 the nested wall.*  `indDeclNames`, `exists_getElem?_of_lt`, `TrIndDecl.mem_indDeclNames`,
`TrIndDecl.not_addInductStages`, `trec1_not_declared`, `tBlock_not_addInductStages`.

*§3 the restated obligation.*  `InductStepSafe`, `.induct_premises`, `.le`, `.map_wf`,
`.find?_of_not_mem`; `AddInductiveObligation`; `R10.Wit.uIndType`, `.tr_uType`, `.tr_uUnit`,
`.trIndDecl_wit`, `.inductStepSafe_wit`.

*§4 the falsity.*  `addDecl_inductDecl_post_false`, `addDecl_inductDecl_WF_false`; the block
literals `uDecl`, `boxIndType`, `tIndType`, `boxDecl`, `tDecl`; build-time checks A and B.

*Owned file edited.*  `Verify/Environment/Lemmas.lean`: `Aligned.addInduct`'s statement (§5.2).

**Not proved, and not attempted:** the flip; `AddInductiveObligation`; nested `AddInduct`; the
`.unsafe` rule; the nine `Verify/TypeChecker/` declarations.
