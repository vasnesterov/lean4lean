# handoff-telecongr: `HasArgs.congr_tele` + `TeleDefEq.instN`, and what they actually buy

*Stream started 2026-09-03. Written incrementally; sections appear in the order they were
established, not in order of importance. Grading follows `docs/vacuity-ledger.md` §0.*

## 0. THE BRIEF'S FRAMING IS STALE AT ITS FIRST WORD

My brief's outcome 1 reads "`congr_tele` / `TeleDefEq.instN` **proved**". Both are **already
proved**, in the tree, hole-free, at:

* `VEnv.TeleDefEq.instN` — `Lean4Lean/Theory/Inductive/NestedTele.lean:1516`
* `VEnv.HasArgs.congr_tele` — `Lean4Lean/Theory/Inductive/NestedTele.lean:1553`

plus `VEnv.TeleDefEq.weakN` at `:1535`, `VExpr.instAllTele_bvars_lift` at `:1601`,
`VIndRestore.atRecTele_fieldTypesR_closedTele` at `:1819`, and
`VIndRestore.atRecTele_fieldTypesR_substC_eq` at `:1850`. All six carry proof bodies.

So the relayed target was **mis-stated**: nothing here needs proving. The open question is
**consumption**. That is recorded first because it is the one thing about my brief that a reader
must not carry forward: this is the "uncomposed pair already composed in a file nobody had read"
misfire, warned about in my own brief, occurring in the same brief that warned about it.

(Note the name drift the two relaying streams both carried: they wrote `TeleDefEq.inst`; the
declaration is `TeleDefEq.instN`. `VEnv.TeleDefEq.inst` does not exist.)

## 1. THE `Faithful` COST IS **NOT** AVAILABLE AT (A) — the relayed claim is half wrong

The (B) stream's relayed line was: `hAs` comes out of `MinorCtorHargs` "via `instAt_ctor_hpi`,
cost: a `Faithful` hypothesis, **already available at every witness**".

`VIndRestore.Faithful` (`Theory/Inductive/Restore.lean:803`) has **all three** clauses guarded by
`T.name ∈ K`:

    ty_agree      : ... D.types[j]? = some T → T.name ∈ K → ...
    ctor_agree    : ... D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors, ...
    ctors_complete: ... D.types[j]? = some T → T.name ∈ K → ...

and `Restore.lean:826` says so in its own docstring ("**`Faithful` is vacuous at `K = []`**").

* **(B)'s `hAs`**: `recConstsR_wf_of_recHargsD`'s `hminD` is demanded only under
  `D.types[t]? = some T → T.name ∈ K` (`RecTyped.lean:786`). `ctor_agree` **is** available. ✓
* **(A)'s `hbv`**: §7's `hbeta` is quantified at `T.name ∉ K` (`CtorBeta.lean:556`) — `C` is a
  constructor of a member the step **declares**; only the *field's* target `T'` is in `K`. So
  `ctor_agree` at `j`/`T`/`C` is **unavailable**, and with it `instAt_ctor_body_eq`'s free
  `D.params = C.params` (`NestedTele.lean:1255`, the "F3's syntactic half, for free" of §T10).

So the two obligations do **not** share the `Faithful` route, and the brief's "cost already
available at every witness" is false at (A). At (A) the only relation between `C.params` and
`D.params` is `VIndCtor.WF.params_eq` (`Decl.lean:670`), an `IsDefEqCtx` — which is precisely why
`congr_tele` is *needed* there rather than a convenience. The brief's "one lemma, two obligations"
survives; its "one cost, two obligations" does not.

## 2. OBLIGATION (A)'s `hbv` IS DISCHARGED — outcome 1's first half

`Lean4Lean/Theory/Inductive/TeleCongr.lean`. Everything hole-free; axiom lines in §6 of the file.

### What was missing, and it was not `congr_tele`

`congr_tele` consumes a **`TeleDefEq`**; `VIndCtor.WF.params_eq` (`Decl.lean:670`) is an
**`IsDefEqCtx`**. The two relations agree entrywise but **recurse from opposite ends** —
`IsDefEqCtx` outward from its base (`succ` types its new entry in the *already built* context),
`TeleDefEq` from the telescope's front — so neither `induction` alone bridges them. The bridge is
an induction on the `IsDefEqCtx` with a `TeleDefEq` **accumulator**:

    TeleDefEq.of_isDefEqCtx_aux : env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.TeleDefEq U Γ₁ Bs Bs' → env.TeleDefEq U [] (Γ₁.reverse ++ Bs) (Γ₂.reverse ++ Bs')

at `Bs = Bs' = []` giving `TeleDefEq U [] As As'` from `IsDefEqCtx U [] As.reverse As'.reverse`.
Two more were needed and neither was in the tree: `TeleDefEq.substC` (`params_eq` lives in the
source environment, `hbv` in the substituted one) and `TeleDefEq.weak0` (`weakN` at
`Ctx.LiftN Γ.length 0 [] Γ`, with both `liftTele`s removed by closedness — `hbv` names its
telescope *unlifted*, so `ClosedTele D.params 0` is load-bearing, not decoration).

**So the relayed diagnosis was right about the destination and wrong about the blocker**: the pair
was proved and unused, and what was actually missing was the `IsDefEqCtx`/`TeleDefEq` vocabulary
bridge. Three small lemmas, ~25 lines, all four compiled first try.

### The result

* `VIndCtor.WF.hasArgs_params_bvars` — §7's `hbv` at any block `Δ` above the parameters, from
  `params_eq` + `params_len` + `ClosedTele D.params 0` + the σ-identity on `D.params`.
* `VIndCtor.WF.hasArgs_params_bvars_of_wf` — the same with those last two discharged from
  `D.WF env` and `env.addIndTypes D = some env₃`.
* `VEnv.ctorConstsCR_wf_of_betaD₄` — **§7 with `hbeta`'s `hbv` component deleted**. Five data
  become four. Proved by feeding the above into `ctorConstsCR_wf_of_betaD` unchanged.

### The price, stated exactly

**One hypothesis added: `henv : env.Ordered`.** Nothing else. In particular *no* `hfresh`:

* `VIndRestore.csubstTy_freshIn` (§2 of the file) proves `(R.csubstTy D K).FreshIn env` from the
  **type-staging equation alone** — `csubstTy`'s domain is only the companion *type* names, so
  `csubst_freshIn`'s first branch suffices where `csubst_freshIn` needs all three. And
  `ctorConstsCR_wf_of_betaD` already carries that equation as `h₃`.
* The environment is the thing to get right here: this is freshness in **`env`**, before
  `addIndTypes`. `(R.csubstTy D K).FreshIn env₃` is **false** whenever `K` names a member of `D`,
  because `env₃` declares precisely the names `csubstTy` substitutes. A route that reached for
  `hfresh` at `env₃` would have been building on a false hypothesis.

`env.Ordered` is free at every caller: `CtorBeta.lean:625` *derives* `henv₃` from `henv₁`, so any
caller that can supply `henv₃` already has it.

### Anti-vacuity, run rather than argued

Deleting a conjunct from a demanded bundle **weakens** the premise, so it cannot empty it; adding
`henv` could. `InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_betaD₄` instantiates §4 at
`ntreeAux` (`NTree`/`List`, `D.np = 1`, a real nested block with a companion-pointing recursive
field) at exactly `CtorBeta.lean` §7b's standard — four staging equations hypothesised, everything
else supplied — and the `HasArgs` line §7b had to build by hand is **gone from the witness**, with
nothing replacing it. `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

**Grade: a discharge, not a reduction.** The component is gone from the bundle and nothing was
added to the bundle in its place. This is not the flip and does not close a census hole; §7 is
still a reduction of (A) to `hargs`, one component lighter.

### The frozen-file / not-mine edit this implies (NOT made)

`CtorBeta.lean` is not mine. The edit it wants is: replace `ctorConstsCR_wf_of_betaD`'s five-part
`hbeta` with the four-part one and add `henv`, i.e. make `ctorConstsCR_wf_of_betaD₄` *the*
statement and delete the old one. `§7b`'s witness then loses its `hbv` block. I have proved the
replacement rather than performing it; `TeleCongr.lean` imports `CtorBeta.lean`, so nothing there
needs to change for §4 to be usable.

## 3. OBLIGATION (B)'s `hAs` IS DISCHARGED — outcome 1's second half, with the grade lower

`TeleCongr.lean` §6/§6b. Hole-free (`minorCtor_hAs` `[propext, Quot.sound]`;
`minorCtorHargs_of_hargs` `[propext, Classical.choice, Quot.sound]`).

### The chain composes, and §T12.1's arithmetic prediction was correct

`VIndRestore.minorCtor_hAs` derives `MinorCtorHargs`'s third conjunct at the `As` that
`instAt_ctor_hpi` delivers. The five steps are exactly §T12.1's, and the one claim in §T12.1 that
could have been wrong — "`k` in `substC_minorType_defeq` is `nr + nf + (D.nm + q)`, **the same
offset**" — is right: the only arithmetic the proof needs is
`D.nm + q + (nr + nf) = nr + nf + (D.nm + q)`.

Consumed: `MinorFldDefEq` (which (B)'s closure already demands at *every* entry, so this is not a
new charge), plus §T13's two side conditions and §T16.2's parameter σ-identity.

`VIndRestore.minorCtorHargs_of_hargs` then produces `MinorCtorHargs` from **two** components
instead of four: `hpi` from `instAt_ctor_hpi`, `hAs` from the above, leaving `hcbody` and `hfun`.

### The `Faithful` cost, and where the relayed claim was right

Here `Faithful.ctor_agree` *is* available — `hminD` is demanded only at `T.name ∈ K`
(`RecTyped.lean:786`), exactly `ctor_agree`'s guard. So the (B) stream's guess was correct **for
(B)** and wrong for (A) (§1 above). `hlen`/`hagree` are what enter; `npJ` comes along, and at the
witness it is `1`.

### Anti-vacuity: run at the entry where the telescope MOVES

Row 205's failure mode is a hypothesis set jointly unsatisfiable at every real block while the
axiom line is clean. `ntreeAux.ctorsAll = [(0, ntreeNode), (1, nlistNil), (1, nlistCons)]`, and the
easy entry is the wrong one: `q = 1` is `nlistNil`, which has **no fields**, so `RecTyped.lean`'s
`ntree_minorFld_nil` gives `MinorFldDefEq` free, `hAs` is `.nil`, and §6 says nothing. So the check
is at **`q = 2`, `nlistCons`** — two recursive fields, and
`ntree_nlistCons_fieldTypesR_ne` proves the restored telescope really differs from the source one
there, so `congr_tele` is doing work rather than closing a `refl`.

`ntree_minorCtorHargs_sides_at_cons` exhibits **all five non-data hypotheses simultaneously** at
that entry (`[propext, Quot.sound]`), `hagree` included, from the block's own `Faithful` witness at
`npJ = 1`. Both σ-identities and `hlen` are `rfl`; `ClosedTele` is an explicit term.

**Grade: a reduction of `MinorCtorHargs` from four components to two, not a discharge of (B).**
`hcbody` and `hfun` are `hargs` and stay open; `hfld` is `MinorFldDefEq`, still a bundle member and
still open at the moving entry. This is graded the way `RecTyped.lean` §6c grades its own.

### The chain is composed end to end, not asserted

`minorCtorHargs_of_hargs` takes `hσf`/`hclF` as facts. `minorCtorHargs_of_hargs'` takes their
*producers' inputs* instead, so `§T13 → §T12.1 → §6 → MinorCtorHargs` is one call chain with
nothing hypothesised in the middle. This matters for the measurement in §4 below: without it, two
of the five relayed declarations would still have had zero users after my work, and I would have
been reporting "the chain composes" while in fact hypothesising the two links.

## 4. THE ZERO-USER CLAIM, MEASURED AGAINST THE COMPILED ENVIRONMENT

Second-hand claim; checked with `lean_references` (LSP index over the built workspace), not grep.
Counts are *total occurrences including the declaration site*.

| declaration | before | after | note |
| --- | --- | --- | --- |
| `VEnv.HasArgs.congr_tele` (`NestedTele.lean:1553`) | 3 = decl + **2 self-recursive** | 5 | genuinely zero external users |
| `VEnv.TeleDefEq.instN` (`:1518`) | 3 = decl + **2 real users** | 3 | **NOT zero-user** — see below |
| `VExpr.instAllTele_bvars_lift` (`:1601`) | 2 = decl + 1 self-recursive | 3 | genuinely zero external users |
| `VIndRestore.atRecTele_fieldTypesR_substC_eq` (`:1850`) | 1 = decl only | 2 | genuinely zero users |
| `VIndCtor.atRecTele_fieldTypesR_closedTele` (`:1819`) | 1 = decl only | 2 | genuinely zero users |

**Correction to the relayed list**: `TeleDefEq.instN` was **not** zero-user. It is called twice, in
`HasArgs.congr_tele`'s own proof body (`NestedTele.lean:1559`, `:1561`) — in the same file,
thirty-five lines below it, inside the very theorem the list named alongside it. So the claim is
**four of five**, not five of five. The (B) stream flagged the list as a guess; the flag was
warranted, and this is the shape the flag should be read in — not "wrong", but "one row of five
was arrived at by looking at the wrong thing".

**And one the list did not mention**: `VEnv.TeleDefEq.weakN` (`:1535`) already had **two** users
(`NestedTele.lean:3494`, `:3512`) before my work. It is the third member of the same §T12.1 triple
and was never unused, so "the §T12.1 machinery is entirely unconsumed" would have been false too.

## 5. WHERE MY BRIEF WAS WRONG — the highest-value output

1. **"`congr_tele` / `TeleDefEq.instN` proved" was the target.** Both were already proved, with
   bodies, in the tree (§0). The task was consumption. This is the "already-composed pair"
   misfire the brief itself warned about, in the brief that warned about it.
2. **"cost: a `Faithful` hypothesis, already available at every witness" is false at (A)**
   (§1). All three `Faithful` clauses are guarded by `T.name ∈ K`; (A)'s field β-step is
   quantified at `T.name ∉ K`. Had I taken that route at (A) I would have been reaching for a
   hypothesis that cannot be supplied there.
3. **"five declarations with zero users" is four** (§4). And a sixth in the same triple,
   `TeleDefEq.weakN`, had two users all along.
4. **The pair is named as the blocker; the actual blocker was neither member of it.** What was
   missing was `IsDefEqCtx → TeleDefEq`, a vocabulary bridge nobody had written, plus
   `TeleDefEq.substC`. `congr_tele` could not be *reached* from `params_eq`, which is why it sat
   unused rather than being merely unapplied.
5. **`TeleDefEq.inst` (the name both relaying streams used) does not exist.** The declaration is
   `TeleDefEq.instN`. Two independent streams carried the same wrong name, which suggests both
   read it off the same prose rather than off the declaration.

Two things my brief got right and that mattered: "one lemma, two obligations" (the same
`congr_tele` closes both, from different premises), and "`PiInv`-free" (nothing here touches it).

## 6. WHAT TO PICK UP FIRST

1. **Make `ctorConstsCR_wf_of_betaD₄` the statement.** `CtorBeta.lean` is not mine. The edit:
   delete `hbeta`'s `hbv` component from `ctorConstsCR_wf_of_betaD`, add `henv : env.Ordered`,
   and drop the `hbv` block from §7b's witness. `TeleCongr.lean` §4 is the proof that this is
   sound; §5 is the proof that it is still inhabited. `HasArgs.congr_tele`'s docstring at
   `NestedTele.lean:1550` and `CtorBeta.lean` §6d's parenthetical both need their "outstanding
   obstruction" wording retired.
2. **Make `MinorCtorHargs` a two-component bundle.** `RecTyped.lean`'s `def MinorCtorHargs`
   (`:704`) should lose `hpi` and `hAs`; `minorCtorHargs_of_hargs'` is the proof that they are
   derivable and `ntree_minorCtorHargs_sides_at_cons` that the residual premises hold at the
   moving entry. `recConstsR_wf_of_recHargsD`'s `hminD` then asks for `hcbody`/`hfun` only. This
   is a `RecTyped.lean` edit; that file is not mine either.
3. **`hargs`, still.** Both obligations now bottom out in strictly less, and in the *same* less:
   (A) in `hbeta`'s four, (B) in `hcbody`/`hfun`. Every one of those is `hargs`. Nothing here
   moved that, and `instAt_indep_of_tyArgs` still says no restoration-independent argument will.
4. **`MinorFldDefEq` at the moving entry.** §6 consumes it and cannot produce it. §7 shows every
   *other* input to §6b is available at `nlistCons`; `hfld` there is the single remaining
   non-`hargs` gap in the minor block, and `NestedTele.lean` §T16.1 claims to reduce it to the
   same head datum. Unverified by me.
5. **Generalise `TeleDefEq.of_isDefEqCtx` off `Γ₀ = []`.** The accumulator proof works for any
   base; I stated it only at `[]` because `params_eq` is there. A general form would state the
   difference telescope, which needs an `Ξ`-indexed shape. Not needed by anything today.

## 7. WHAT IS *NOT* CLAIMED

* The flip is **not** made, and nothing here closes a census hole (13 before, 13 after).
* (B) is **not** discharged: `hcbody`, `hfun` and `hfld` are open. §6b is a reduction of one of
  (B)'s four data families from four components to two.
* (A) is **not** discharged either: §4 is `ctorConstsCR_wf_of_betaD` with one hypothesis removed,
  and that theorem was and remains a *reduction* of (A) to `hargs`.
* `MinorFldDefEq` at `q = 2` / `nlistCons` is **not** inhabited here. §7's witness deliberately
  excludes it and says so.
* No `σ.WF` was used anywhere in this file. (A)'s route uses `CSubst.WF` at `(R.csubstTy D K)`,
  which is `ctorConstsCR_wf_of_betaD`'s own hypothesis, unchanged; §6's route uses none at all.

## 8. Verification

* `lake build` green, **1575 jobs** (1571 before this file).
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**, `BUILT: 392; in population
  but NOT BUILT: 0`. Unchanged in both directions — this file adds none and closes none.
* `TeleCongr.olean` present at `.lake/build/lib/lean/Lean4Lean/Theory/Inductive/TeleCongr.olean`,
  checked directly rather than inferred from a green build.
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — empty.
* Guards `24 / INCOMPLETE / 2-2`. Recorded, but **not** evidence for anything here: Guard's
  closure is 24 modules and excludes all of `Theory/Inductive/`.
* Frozen files: `git diff --stat` on `Verify/Soundness.lean`, `Verify/Axioms.lean`,
  `Verify/Guard.lean` is empty. Not opened, not touched.
* 13 theorems in the module; all `#print axioms` lines in §8 of the file, none carrying `sorryAx`.
* Files created: `Lean4Lean/Theory/Inductive/TeleCongr.lean`, `docs/handoff-telecongr.md`. No
  other file edited; `NestedTele.lean` and `RestoreBridge.lean` show in `git status` from
  concurrent streams, not from me.
