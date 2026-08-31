# Frozen-edit requests

`Lean4Lean/Verify/Soundness.lean`, `Lean4Lean/Verify/Axioms.lean` and `Lean4Lean/Verify/Guard.lean`
are frozen by `CLAUDE.md`: no AI agent may edit them without explicit human approval for that
specific change, and subagents may never edit them at all.

Proposals accumulate in the docstrings of the files that prove them, which makes them easy to
lose. This file is the index. **Nothing here has been made.** Each entry states the exact edit,
what it buys, what it costs, and where the supporting proof or measurement lives.

Status values: `MERGED`; `PR OPEN` — the edit is on a branch and under review; `READY` — the
supporting work is complete and the edit can be made as written; `NOT READY` — the edit is written
down but its premise is not yet established.

By standing instruction from the human (2026-08-31): **every frozen-file change goes out as a PR**,
not as a direct commit to master.

**A `READY` here means "believed ready", not "built".** Entry 2 was marked `READY` on the strength
of a by-name search and turned out to break the build. Before promoting anything to `PR OPEN`,
make the edit on a branch and run a full `lake build`.

---

## 1. Guard 3's `partial` detection is measuring the wrong thing — **`MERGED`**

**PR #41, merged 2026-08-31** (`53f4dc2`). The count came out at exactly the predicted **2/54**.
Guard 3 on master now reads `checker cone implementation gaps within frozen list (2/54 remaining)`,
and the two survivors are `ptrEqExpr` / `ptrEqConstantInfo`, both `@[implemented_by]`, both
deliberate and both axiomatised.

**Follow-up now available and not yet done:** 52 of the 54 `implGapWhitelist` entries are dead.
Check 3 only throws for a flagged name *absent* from the whitelist, so dead entries are harmless —
but CLAUDE.md counts shrinking the allowlist as progress, and the whitelist is now 96% noise.
Trimming it is a separate frozen edit and would need its own PR.

**File:** `Verify/Guard.lean`, inside check 3.
**Evidence:** `Lean4Lean/Tests/KernelHardening.lean`, final section, measured 2026-08-31 by
replaying check 3's own walk from `Lean4Lean.addDecl`.

Of the 51 names check 3 currently flags: 2 are `@[implemented_by]` (`ptrEqExpr`,
`ptrEqConstantInfo` — both deliberate and axiomatised), **0** are `@[extern]`, **0** are
genuinely `partial`, and 49 are ordinary total definitions. The 49 are flagged only because the
guard tests `env.contains (n ++ "_unsafe_rec")` and the equation compiler emits an `_unsafe_rec`
companion for *every* computable recursive definition. The `-- partial` comments on those
entries in `implGapWhitelist` are simply wrong. `Compiler.getImplementedBy?` cannot separate
them: it returns `none` for structural, well-founded and `partial` definitions alike.

**The edit**, inside check 3:

```lean
    if env.contains (.str n "_unsafe_rec") then
      match env.find? n with
      | some (.opaqueInfo _) => kinds := "partial" :: kinds
      | _ => pure ()   -- ordinary recursive def: `_unsafe_rec` is codegen, not `partial`
```

**Buys:** the guard would say what it means. Reachable count 51 → 2; 52 of 54
`implGapWhitelist` entries become removable.
**Costs:** it is a *narrowing*. The `_unsafe_rec` companion is what the compiled executable
actually runs, so each of the 49 names a mechanical compiler transcription of a definition this
project verifies in its `brecOn` form. That is the trust assumption every compiled Lean function
carries — which is why the count is uninformative — but narrowing check 3 means the guard stops
mentioning it at all.

**Two coverage gaps found by the same measurement, not addressed by this edit:** an `unsafe def`
with no `_unsafe_rec` companion and no attribute is invisible to check 3
(`Lean4Lean.ptrEqExpr.unsafe_1` is in the cone and is not flagged), and the `Lean4Lean.*` module
filter hides every upstream gap.

## 2. The axiom `Expr.replace_eq` is now unused — **`PR OPEN`** (was refuted, then made true)

**PR:** https://github.com/vasnesterov/lean4lean/pull/42 (branch `frozen/drop-replace-eq`, two
files, one commit). Frozen axiom list **25 → 24**.

**The history matters more than the edit.** This entry was `READY`, then refuted, then made
genuinely ready by changing the checker rather than the argument:

1. Marked `READY` on the strength of a by-name grep.
2. **Refuted** — applying it broke the build twelve times at `Verify/Expr.lean:1360`. The axiom is
   `@[simp]` and was silently bridging `replace` to `replaceNoCache` inside
   `instantiateLevelParamsCore_eq`. No grep can see an implicit rewrite.
3. **Made true** by `24d3c5b`: six level-parameter sites re-pointed to core's own pure
   `Lean.Expr.instantiateLevelParamsNoCache`, after which an 8444-constant walk of `addDecl`'s cone
   finds `replaceImpl`, `Expr.replace`, `Expr.instantiateLevelParams`,
   `Expr.instantiateLevelParamsCore` and `ConstantInfo.instantiateTypeLevelParams` all absent.
4. Verified by **build**: 1436 jobs green on the branch, guard 1 at 24 axioms; and independently
   1384 jobs plus Arena 185/6/0 in a separate tree copy.

The axiom could never have become a theorem — upstream `Expr.replace` is `replaceImpl`, `opaque`
with `@[extern "lean_replace_expr"]`, no Lean body. Orphaning was the only route.

---

### Superseded text of entry 2, kept for the lesson

**`NOT READY` — premise refuted**

**Files:** `Verify/Axioms.lean` (delete the axiom) and `Verify/Guard.lean` (guard 1 checks for
*exactly* 25 axioms, so the count becomes 24).

**This entry was wrong and no PR was opened.** It read, verbatim: *"The two call sites in
`Lean4Lean/Inductive/Add.lean` that made the cached version reachable now call the pure version
directly, so nothing in the tree consumes the axiom. **Costs:** none known."* Both sentences are
false.

**Measured 2026-08-31** by making the edit on a branch and running a full `lake build`: **the
build fails**, at `Verify/Expr.lean:1360`, twelve times — once per `Expr` constructor.

The consumer is `instantiateLevelParamsCore_eq`. Upstream `Lean.instantiateLevelParamsCore` is
implemented with `Expr.replace`, so `simp [instantiateLevelParamsCore]` on that proof's first line
leaves a goal about `replace`, while the proof's own helper is stated about `replaceNoCache`.
`replace_eq` is `@[simp]`, so it was bridging the two **silently**. The evidence in this entry was
a by-name search, which cannot see an implicit `simp` use — that is the whole reason the claim
survived, and it is the lesson: **an `@[simp]` axiom's consumers cannot be established by grep;
only a build with it removed settles the question.**

**Why it is not merely "not yet".** The axiom cannot become a theorem: upstream `Expr.replace` is
`replaceImpl`, which is `opaque` with `@[extern "lean_replace_expr"]`, so there is no Lean body to
prove it from. And no change under `Lean4Lean/` can orphan it while the checker calls
`Lean.instantiateLevelParamsCore`, because that call site is upstream.

**What would make it `READY`:** have the checker stop calling
`Lean.instantiateLevelParamsCore` and call a pure Lean reimplementation instead — the direction
`CLAUDE.md` explicitly encourages, and the pure model already exists in this tree as
`Lean4Lean.instantiateLevelParamsCore'` (`Verify/Expr.lean`). Then the axiom is genuinely
unreachable and the deletion is a one-line change. Any behavioural difference goes in
`divergences.md`.

## 3. `kernel_sound := Bridge.kernel_sound_of …` — `NOT READY`

**File:** `Verify/Soundness.lean`.
**Evidence:** `Verify/SoundnessAssembly.lean` (the assembly, proved) and
`Verify/PreludeVacuity.lean` (why it is not ready).

The shape of the eventual edit is

```lean
    import Lean4Lean.Verify.SoundnessAssembly          -- added
    theorem kernel_sound ... :=
      Bridge.kernel_sound_of <prelude proof> <upper bound proof> ds fuel env hok hax hfalse
```

**Why not ready** (unchanged, and now more precisely blocked — see the note after this entry):
`Bridge.kernel_sound_of` is correctly proved, but its route runs through
`Bridge.addDeclWF`, hence `addDecl.WF`, whose `inductDecl` branch is *refuted*
(`Verify/Inductive/AddDeclWF.lean` §4), and through `foldAddDecl_tr`, which is a *false statement*
(`Verify/PreludeVacuity.lean`, `foldAddDecl_tr_false`). Both trace to `AddInduct` having no
constructors. `Bridge.PreludeBridge stdPrelude` is meanwhile *vacuously true*, so inhabiting it
would buy nothing.

**Do not** discharge this by assuming `foldAddDecl_tr` as a hypothesis, which
`Verify/Inductive/AddDeclWF.lean` §5.4 item 3 suggests:
`anything_of_foldAddDecl_tr_hypothesis` proves that assuming it yields *any* proposition, so
guard 2 would print "proof COMPLETE" over an empty proof.

**What would make entry 3 ready, as of 2026-08-31.** Every route from the checker to the abstract
environment passes through `TrEnv .safe`, which is unsatisfiable while `AddInduct` has no
constructors. Giving it constructors needs the *nested* form, which needs
`addInductR_ordered'`'s `hctors`/`hrecs`/`hrules` — and `hctors` is **false** as stated
(`nfnAuxDirty_refutation`). The design ruling is recorded in `ORCHESTRATOR.md`: `VIndCtor.typeR`
becomes the substitution, which is the faithful model of the implementation's whole-expression
`restoreNested`. That work is in flight. Entry 3 cannot become ready before it lands, and **must
not** be made to typecheck by assuming `foldAddDecl_tr` or `Bridge.AddDeclWF` — both are false
statements, and `anything_of_foldAddDecl_tr_hypothesis` / `anything_of_addDeclWF_hypothesis` prove
that assuming either yields any proposition at all.

---

## Not a frozen edit, but the decision everything above waits on

Giving `AddInduct` (`Verify/Environment/Basic.lean`, currently no constructors) its constructors
is **not** a frozen edit — that file is proof machinery agents may design. It is a human
*decision* because it takes the sorry census from 14 to 17. `docs/handoff-addinduct.md` §6 has
the construction, §7.2 recommends "not yet", and `docs/critical-path.md` corrections 3 and 4
re-price it: every route from the checker to the abstract environment passes through
`TrEnv .safe`, which cannot hold of any environment containing `Eq` while `AddInduct` is empty.
