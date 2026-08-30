# Handoff: the projection cluster

**Census: 20 → 19.**  `TrProj.wf` is **proved**.  `TrProj.weak'_inv`, `TrProj.uniq`
(`Verify/Typing/Lemmas.lean`) and `inferProj.WF` (`Verify/TypeChecker/InferType.lean`) are
still open.  Full `lake build` green; all three of `Verify/Guard.lean`'s checks pass
(guard 2 still reports `proof INCOMPLETE: sorryAx present`, as it must while 19 holes remain).

> The previous edition of this file said the census was 21.  It is now 20 → 19 because another
> stream proved `IsDefEqU.sort_inv` in the meantime (`Injectivity.lean` 7 → 6).  Use
> `lake env lean scripts/sorry-census.lean`; never grep.

Everything below is separated into **machine-checked** (a named, `sorry`-free declaration in
the tree) and **read off source** (an argument from reading definitions, not checked).

---

## 0. Pick this up first

1. **`inferProj.WF`** — a decision, not a proof problem.  §6.  Unchanged, and still the
   orchestrator's call.
2. **`RecTypeResidual`** (§3.4).  Three syntactic equations, and they are all things
   `D.recType 0` genuinely determines.  Discharging it completes ledger G4 outright, because
   both halves of `VEnv.StructureUniq` are now proved *given* it.
3. **`TrProj.uniq` / `.weak'_inv`** wait on facts other streams own — `IsDefEqU.const_app_inv`
   (census hole) and the two `Verify/Typing/Rigidity.lean` statements.  Nothing in this cluster
   unblocks them.

---

## 1. Status of the four

| | status | blocked on |
|---|---|---|
| `TrProj.wf` | **PROVED** | — (cone contains `IsDefEqU.weakN_iff`'s `sorry`, another stream's) |
| `TrProj.weak'_inv` | open | **(C)** `ConstRigid` + (B)'s level half + `IsDefEqU.weak'_iff` |
| `TrProj.uniq` | open | **(D)** `ConstNoConf` + `IsDefEqU.const_app_inv` + G4 + a `projTerm` congruence |
| `inferProj.WF` | open **by deliberate choice** | see §6 |

---

## 2. `TrProj.wf` — proved, by the route the old docstring set aside

### 2.1 What was dead, and stays dead

Machine-checked (`Verify/Typing/ProjLevelWitness.lean`, `barRefutes`, unchanged): the subgoal
the old proof reduced to — `lvl_k.inst us ≈ .zero` at an *unused* field `k < i` — is **false**,
at `structure Bar : Prop where (n : Prop) (h : ∀ p : Prop, p)`.  That refutation is untouched
and still correct; what changed is that nothing needs that subgoal any more.

### 2.2 The route that worked: **swap**, not compress

The previous edition listed, under "two routes that do **not** work, checked so nobody re-tries
them":

> Replacing the unused telescope entry by an inhabited type (`.sort (.succ .zero)`, inhabited
> by `.sort .zero`) and using the modified context.  The field type's typing then lives in the
> *swapped* context, and "swap a context entry the subject and type both skip" is not free — a
> subderivation may still mention it.

**The premise is right and the conclusion is wrong**, and this is the correction that unlocked
the lemma.  The swap is not free; it costs *exactly one* `VEnv.HasType.weakN_iff` per swapped
binder — strengthen the binder away, weaken the new one in — and "a subderivation may still
mention it" is precisely what strengthening rules out.  `HasType.weakN_iff` is already in the
tree (`Theory/Typing/UniqueTyping.lean`), backed by `IsDefEqU.weakN_iff`'s existing `sorry`.

The swap **beats** the compressed route the previous edition preferred, for a reason that
edition did not identify: it keeps the projection's spine **saturated**.  The compressed route
must shorten the spine; the naive alternative (junk at the unused position) needs an inhabitant
of the unused field's *own* type, and in general there is none — `structure Bar : Prop where
(n : Nat) (h : True)` would need an inhabitant of `Nat` in an arbitrary context of an arbitrary
environment.  `VExpr.swapUnit := .sort (.succ .zero)` is a type in every context of every
environment **and** is inhabited there by `.sort .zero`, so neither problem arises.

### 2.3 The machinery, all machine-checked (`Verify/Typing/ProjSkip.lean`)

| name | what it does |
|---|---|
| `VExpr.inst_congr_skips`, `instAll_congr_skips` | one skipped spine position is irrelevant |
| `VExpr.InstAllSkip`, `instAll_congr_of_skip`, `InstAllSkip.build` | the multi-position form; the builder needs only the *original* term's skip data, because `Skips.inst_of_lt` says substituting above an index cannot create an occurrence at it |
| `VInductDecl'.projCore_congr_earlier` | its `projCore` instance |
| `VEnv.HasType.swapSkipped` / `.swapTele` / `.swapCtx`, `OnCtx.swapCtx` | the swap, one binder / one middle-of-telescope binder / a whole telescope.  `.swapTele` is one line on top of `Ctx.LiftN.tele` (B6) |
| `VExpr.SwapCtx`, `.build`, `.buildPair`, `.appendKeep`, `VExpr.swapSpine_exists` | the swap description and its builders |
| `VExpr.liftTele_of_skips` | a telescope whose entries each skip their own offset *is* a `liftTele` — `.swap`'s first premise |
| `VExpr.Skips.instL'`, `.inst_of_lt`, `.instAll_of_lt` | carrying skips through `instL` and through the parameter spine |
| `VIndCtor.swapCtx_fields`, `.swapData` | the projection instance: the derivation exists **unconditionally**, because used positions need nothing and unused ones are covered by `VIndCtor.not_fieldUsed_skips` |
| `ftype_hasType_swapped`, `instAll_field_isType_swapped` | field `i` typed over the swapped prefix; the crux |
| `VEnv.HasArgs.ofGetD`, `VEnv.HasArgsDF.ofGetD` | `ofMap` for a spine that is not `(range i).map f` |
| `projArgs_hasArgs_swapped`, `projMotiveBody_hasType_swapped`, `projMotiveBody_hasType_guarded`, `projMotiveTerm_hasType_swapped` | the chain, needing `ProjHasType` at the **used** indices only |

`VIndCtor.not_fieldUsed_skips` was described in `Theory/Inductive/Structure.lean` as "stated
and unused".  It is now load-bearing twice over.

### 2.4 What changed in `Verify/Typing/Lemmas.lean`

`projMinor_hasType` and `projTerm_hasType` now take the **guarded** F17 premise

    ∀ k ≤ i, (k = i ∨ C.FieldUsed D 0 k) → lvl_k.inst us ≈ D.elimLvl.inst (D.projLvls C us k)

and the guarded induction hypothesis `∀ k < i, C.FieldUsed D 0 k → ProjHasType … k`.  Both are
*weaker* hypotheses than before, so both theorems are strictly stronger; no statement was
narrowed.  `TrProj.wf` is then a transcription of `TrProj`'s own recorded F17 clause — the
`sorry` and the whole case split it sat in are gone.

The strong induction in `projTerm_hasType` now runs over the **used** earlier indices only,
which is exactly the set at which `ProjHasType` is true.  At an unused index it is *false*, and
that is what `barRefutes` measures.

### 2.5 Non-vacuity — checked, at the configuration that refutes the old route

`Verify/Typing/ProjWfWitness.lean` (new).  Machine-checked, and `#print axioms`-clean apart
from `propext`/`Quot.sound`/`Classical.choice`:

* `barEnv_TrProj` — an **actual `TrProj` derivation** at `barDecl`, `i = 1`, over the unused
  field 0.  Every clause of the constructor is discharged, F17 included, and F17 is discharged
  in its *guarded* form: `barField0_lvl_ne_zero` machine-checks that field 0 is **not**
  `≈ .zero`, so a blanket F17 clause would have had no witness here at all.
* `barEnv_TrProj_target` (`rfl`) — the term produced is
  `Bar.rec (fun _ : Bar => ∀ p : Prop, p) (fun (n : Prop) (h : ∀ p : Prop, p) => h) e`, with no
  projection of field 0 anywhere in it.
* `barEnv_TrProj_wf` — `TrProj.wf` applied to that derivation.
* `bar_swapTele`, `bar_swapCtx`, `bar_liftTele_of_skips` (`ProjSkip.lean`) — the swap machinery
  fired at the two-field witness, including with the swapped binder **not** innermost.

**One hypothesis could not be discharged and is carried instead:** `VEnv.WF barEnv`.  That is
*not* a fact about `barDecl` — it is that `VInductDecl'` is not yet wired into `VDecl.induct`
(`Theory/Inductive/Decl.lean`: "the primed name is temporary"), so `VEnv.WF'`, an induction
over `VDecl`s, has no step that produces `barEnv`.  Whoever does that wiring gets
`barEnv_TrProj_wf` unconditional for free, and it is worth doing for exactly that reason: it is
the only thing standing between this tree and an end-to-end checked projection.

---

## 3. Ledger G4 (`VEnv.StructureUniq`) — the level half proved, the syntactic residual **refuted and replaced**

`Verify/Typing/StructureUniq.lean`.

### 3.1 The equality form is FALSE — unchanged

`structureUniq_eq_false`.  `barDeclEq` is `barDecl` with one `VIndField.lvl` replaced by an
`≈`-equal one; `addInduct'` cannot see the difference (`barDeclEq_addInduct`, `rfl`), both
declarations are well-formed, and both are `IsStructure barEnv `Bar`` *through the same
`addInduct'` step*.  No hypothesis on `env` rescues it.

### 3.2 The level half: **PROVED** — `structureLvlAgree_of_structureAgree`

The previous edition recorded this as blocked on the `SortUniq` family, and at the time
`SortUniq` was a hypothesis nothing in the tree exhibited.  It is now a **theorem**:
`VEnv.WF.sortUniq'` (`Theory/Typing/Injectivity.lean`) proves `env.SortUniq U` for every
`VEnv.WF` environment, with `IsDefEqU.forallE_inv_stratified` as its only open input.

Given the syntactic half, both derivations type the *same* subject in the *same* context —
`VIndCtor.WF.result` for `D.lvl`, `VIndField.WF.hasType` for each `F.lvl` — and universe
uniqueness does the rest.  The environment fact used is `VIndCtor.WF env D 0 T C` **at `env`
itself**, which `VEnv.IsStructure.iotaCtx` delivers (`VEnv.IsStructure.ctorWF`, new); no manual
transport along the `addInduct'` stages is needed.

### 3.3 `RecTypeInj` is **FALSE** — `recTypeInj_false`

The previous edition said "pick this up second: `RecTypeInj` … discharges the whole syntactic
half of ledger G4".  **It cannot.**

`StructureAgree.ctorParams` claims `C₁.params = C₂.params`, and `C.params` occurs **nowhere** in
`D.recType` — not in `motiveType`, `minorType`, `ihType`, `ctorApp'` or `tyApp'`.  The recursor
is built over `D.params`; the constructor's own copy (F3) is spliced only into `VIndCtor.type`,
the *constructor constant's* type.  A hypothesis set mentioning only `recType` therefore cannot
pin it.

Machine-checked witness: `barDeclPar` is `barDecl` with `C.params` changed;
`barDeclPar_recType_eq` and `barDeclPar_recs_eq` are `rfl`, so every `RecTypeInj` hypothesis
holds and `ctorParams` fails.  Consequence: `structureAgree_of_recTypeInj` is a reduction to a
statement that can never be supplied — true, and useless.

> This is the fifth statement in this development to turn out **false rather than open**, and
> the third whose defect is a *missing hypothesis* rather than a wrong conclusion.  The tell
> was the same each time: a statement carrying strictly less information than its conclusion
> needs.  Auditing the *information flow* — which record fields the hypotheses can even see —
> catches all three; auditing for auto-bound implicits catches none of them.

### 3.4 The replacement — `structureAgree_ctor`, `structureUniq_of`, `RecTypeResidual`

Machine-checked:

* `VIndCtor.piDepth_type` — `C.type D j` is `mkPi` of exactly `np + nf` binders over a `mkApp`,
  which is never a `.forallE`, so the binder count is read off the term.
* `structureAgree_ctor` — given `C₁.name = C₂.name` and `D₁.np = D₂.np`, the **constructor
  constant** hands over `ctorParams`, the field `type`s and `ctorArgs`, through
  `VIndCtor.skeleton_type`, which inverts `VIndCtor.type` on the nose.  No recursor reasoning.
* `VIndCtor.recArg_eq_none`, `VIndField.Agree.forall₂_of` — for a structure `noRec` makes the
  `recArg` half of `VIndField.Agree` free.
* **`VEnv.structureUniq_of`** — `env.WF → env.RecTypeResidual → env.StructureUniq`.  *Both*
  halves discharged.

So ledger G4 is now exactly:

```
def VEnv.RecTypeResidual (env : VEnv) : Prop :=
  ∀ S D₁ D₂ T₁ T₂ C₁ C₂, env.IsStructure S D₁ T₁ C₁ → env.IsStructure S D₂ T₂ C₂ →
    D₁.params = D₂.params ∧ T₁.indices = T₂.indices ∧ C₁.name = C₂.name
```

Read off source (not machine-checked), the shape of the remaining argument: `recType 0` is
`mkPi (atRecTele params ++ motives ++ minors ++ indices') (…)` with `nm = nmin = 1` by
`IsStructure`, so once the split point `np` is known the three components are prefixes of one
`mkPi` telescope, and `C.name` is read out of the minor premise's `ctorApp'`.  `np` itself is
pinned by an **environment** fact, not a syntactic one: the block's own constants cannot occur
in `D.params` (they are typed before the block exists), while the motive type mentions
`const S selfLvls`, so the first telescope entry mentioning `S` is the motive.  *That* is why
`RecTypeInj`'s "no hypothesis on `env` at all" was the wrong shape, quite apart from
`C.params`; `RecTypeResidual` is stated at the two `IsStructure` derivations for exactly this
reason.  Also read off source: `atRecTele` is `instL selfLvls`, which is the identity on
level-well-formed terms when `isLE = false` (`VLevel.inst_id`) and an injective shift when it
is `true`; the `true` case wants an `instL`-injectivity lemma that does not exist yet.

**Correction to `Theory/Inductive/Structure.lean`.**  `IsStructure`'s docstring says G4 "needs
`VEnv.Sig` (I1)".  `VEnv.Sig` is used nowhere in any of the above.  The level half needs
`VEnv.WF` (through `SortUniq`); the syntactic half needs the constructor constant plus
`RecTypeResidual`.

### 3.5 Non-vacuity

`barDeclEq_StructureAgree` and `barDeclEq_StructureLvlAgree` hold at exactly the pair that
refutes the equality form, at the tree's only *two-field* structure witness, one of whose
fields is not `≈ .zero`.  Not fired: `structureAgree_ctor` at `barEnv`, because `barEnv.Ordered`
is not in the tree for the same reason `barEnv.WF` is not (§2.5); its conclusion is separately
machine-checked at that pair by `barDeclEq_StructureAgree`.

---

## 4. Facts (C) and (D) — unchanged

`Verify/Typing/Rigidity.lean`, sorry-free, both still **stated and unproved**.  `ConstRigid`
(head-only weak-head rigidity for a rule-free constant, under `[VEnv.Params]`) and
`ConstNoConf` (no confusion between *distinct* rule-free constants) are what `TrProj.weak'_inv`
and `TrProj.uniq` respectively need, and they belong in `Theory/Typing/Injectivity.lean` — they
are here only because that file is another stream's.  Nothing in `Rigidity.lean` depends on
`Verify/`, so it moves verbatim.

`barEnv_ruleFreeHead` (machine-checked) shows the premise both are gated on is reachable.

---

## 5. `TrProj.uniq` and `TrProj.weak'_inv`

Neither moved, and neither can move here.

* `TrProj.uniq` needs (D) `ConstNoConf` — because its two structure names are genuinely
  independent.  That is **not** an auto-bound-implicit accident: narrowing to a shared `s` was
  tried and reverted, because `IsDefEqE.trExpr`'s `proj` case (`Verify/EquivManager.lean:117`)
  instantiates them differently, `RelevantEq.proj` dropping the structure name faithfully to
  `EquivManager.isEquiv`.  It also needs `IsDefEqU.const_app_inv` (census hole), G4 (§3 — now
  reduced to `RecTypeResidual`), and a `projTerm` congruence lemma that does not exist and is
  mechanical.
* `TrProj.weak'_inv` needs (C) `ConstRigid`, (B)'s level half, and `IsDefEqU.weak'_iff` (the
  last is proved modulo `IsDefEqU.weakN_iff`, so it is not a separate hole).

**Correction:** the previous `TrProj.wf` docstring said these two "unblock on the same event"
as `TrProj.wf`.  They do not, and `TrProj.wf` landing without them proves it.

**Loose end, still not investigated:** whether `EquivManager.isEquiv` ignoring a projection's
structure name matches the C++ kernel.  `~/lean4/src/kernel/equiv_manager.cpp` does not exist
at that path in this checkout.  If it diverges it is a `divergences.md` entry; if `isEquiv` can
return `true` for `.proj Foo 0 e` vs `.proj Bar 0 e` on reachable inputs it may be a
`bugs-found.md` entry.  Neither is established.

---

## 6. `inferProj.WF` — a decision, not a proof problem

Unchanged from the previous edition, and left open on the standing ruling.
`inferProj_always_throws` proves `(inferProj st i e ety).WF c s Q` for **any** postcondition,
because `inferProj`'s `.inductInfo` gate cannot fire while `AddInduct` has no constructors.  So
`inferProj.WF := inferProj_always_throws hty` closes it in one line and takes the census to 18.

Not done, deliberately: closing it vacuously hides that `inferProj.WF` is **false once the
branch is live**, because `inferProj` never checks recursiveness while `VEnv.IsStructure.noRec`
demands `C.recFields = []` (`bugs-found.md` item 10 — the kernel accepts `.proj` on
`inductive R | mk : R → Nat → R`).  Closing it would not hide the tripwire —
`inferProj_always_throws` goes red at the same moment — but it would move the number without
moving the obligation.  Both options are one line; the orchestrator picks.

---

## 7. Files

New:

* `Lean4Lean/Verify/Typing/ProjWfWitness.lean` — §2.5.

Edited (all owned by this stream):

* `Lean4Lean/Verify/Typing/ProjSkip.lean` — the swap machinery, §2.3.  Now imports
  `Theory/Typing/UniqueTyping` and `Theory/Inductive/StructureClosed`.
* `Lean4Lean/Verify/Typing/StructureUniq.lean` — §3.  Now imports `StructureClosed` and
  `Theory/Typing/Injectivity`.
* `Lean4Lean/Verify/Typing/Lemmas.lean` — `projMinor_hasType` and `projTerm_hasType` guarded,
  `TrProj.wf` proved, docstrings corrected.  Now imports `Verify/Typing/ProjSkip` (no cycle:
  `ProjSkip` depends on nothing in `Verify/Typing/Lemmas`).

Unchanged: `Theory/Inductive/StructureClosed.lean`, `Verify/Typing/Rigidity.lean`,
`Verify/Typing/ProjLevelWitness.lean`, `Verify/TypeChecker/InferType.lean`.

**Auto-bound-implicit audit.**  Every new statement is a `def … : Prop`, a `structure`, an
`inductive` with all binders explicit, or a theorem whose binders were `#check`ed.  No capture.
The defect that actually bit this session was a different one — see §3.3.
