# Handoff: the projection cluster

Four of the tree's 21 `sorry`s: `TrProj.wf`, `TrProj.weak'_inv`, `TrProj.uniq`
(`Verify/Typing/Lemmas.lean`) and `inferProj.WF` (`Verify/TypeChecker/InferType.lean`).
**All four are still open**; the census is unchanged at 21. What changed is that the three
statements they were blocked on but which *did not exist* now exist, one of them is refuted in
the form everyone would have written, and `TrProj.wf`'s route is live again.

Everything below is separated into **machine-checked** (a named, sorry-free declaration in the
tree — `#print axioms` clean apart from `propext`/`Quot.sound`/`Classical.choice`, all on
`Guard.lean`'s whitelist) and **read off source** (an argument from reading definitions, not
checked).

---

## 0. Pick this up first

1. **`TrProj.wf`, and it no longer needs a new statement.** §4. The work is a guarded re-proof
   of four lemmas in `Theory/Inductive/StructureClosed.lean` plus `projTerm_hasType`; the only
   judgement it needs beyond that is `VEnv.IsType.weakN_iff` at `Ctx.LiftN.one`, which is
   *already in the tree*, backed by `IsDefEqU.weakN_iff`'s existing `sorry`. This is bulk, not
   mathematics, and it is the only one of the four that is not gated on the injectivity family.
2. **`RecTypeInj`** (§2). Purely syntactic — no `VEnv`, no `IsDefEq`, no universes — and it
   discharges the whole syntactic half of ledger G4. It is a `mkPi`-telescope decomposition.
3. Everything else waits on facts (B)/(C)/(D) or on `SortUniq`.

---

## 1. Status of the four

| | status | blocked on |
|---|---|---|
| `TrProj.wf` | open; **its current subgoal is refuted**, and a **live route** replaces it | `IsDefEqU.weakN_iff` (existing `sorry`, another stream) + bulk re-proof |
| `TrProj.weak'_inv` | open; residual is **three** things, not one | **(C)** `ConstRigid` (new) + (B)'s level half + `IsDefEqU.weak'_iff` |
| `TrProj.uniq` | open; residual is **four** things | **(D)** `ConstNoConf` (new) + `StructureUniq` (new) + (B) + a `projTerm` congruence |
| `inferProj.WF` | open **by deliberate choice**, and closeable in one line today | see §6 — a decision for the orchestrator, not a proof problem |

**The existential trick does not apply to any of the four.** Checked, one by one:
`TrProj.wf`'s conclusion `VExpr.WF env U Γ e'` is existential only in the *type*, and `e'` is
given by the hypothesis; `weak'_inv`'s `∃ e''` does not dissolve the need to type `e` in the
smaller context, because nothing forces the recorded `ps`/`ιs` to be lifts; `uniq`'s two
targets are both given; `inferProj.WF` is already vacuous for an unrelated reason. The trick
worked for `TrProj.defeqDFC` and stops there.

---

## 2. New statement 1 — `IsStructure` uniqueness (ledger G4)

`Verify/Typing/StructureUniq.lean`. New file, sorry-free.

### 2.1 The equality form is FALSE, machine-checked, and no `env` hypothesis rescues it

`structureUniq_eq_false`. `barDeclEq` is `ProjLevelWitness.lean`'s `barDecl` with field 0's
*recorded* level `.succ .zero` replaced by `.max (.succ .zero) (.succ .zero)`. Then:

* `barDeclEq_addInduct : VEnv.empty.addInduct' barDeclEq = VEnv.empty.addInduct' barDecl` — by
  `rfl`. `VIndField.lvl` is invisible to `addInduct'`.
* `barDeclEq_WF : barDeclEq.WF .empty` — a full second `VInductDecl'.WF` witness.
* `barEnv_IsStructureEq : barEnv.IsStructure `Bar` barDeclEq barTypeEq barCtorEq`.

So `barEnv` is a structure environment for `Bar` twice, with different records, **through the
same `addInduct'` step**. Both derivations share their `decl` witness, so adding `VEnv.WF`,
`VEnv.Sig`, or anything else about `env` cannot separate them. Writing
`D₁ = D₂ ∧ T₁ = T₂ ∧ C₁ = C₂` would have been a fourth wrong statement.

### 2.2 What survives

`VEnv.StructureUniq env` — every quantifier explicit, `#print`ed and audited for capture:

```
∀ (S : Name) (D₁ D₂ : VInductDecl') (T₁ T₂ : VIndType) (C₁ C₂ : VIndCtor),
  env.IsStructure S D₁ T₁ C₁ → env.IsStructure S D₂ T₂ C₂ →
    StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ ∧ StructureLvlAgree D₁ C₁ D₂ C₂
```

`StructureAgree` is equality on everything `addInduct'` writes into a constant (uvars, params,
isLE, `T.name`, `T.type`, `T.indices`, `C.name`, `C.params`, `C.args`, and the fields'
`type`/`recArg`). `StructureLvlAgree` is `≈` on `D.lvl` and on every `C.fields[k].lvl`. `≈` is
the right relation and not a dodge: `VInductDecl'.projTerm` reads `VIndField.lvl` only through
`.inst us` inside `projCore`'s `lvls`, where `IsDefEq.constDF` accepts `≈`.

**Non-vacuity, machine-checked**: `barDeclEq_StructureAgree` and `barDeclEq_StructureLvlAgree`
hold at exactly the pair that refutes the equality form, at the tree's only *two-field*
structure witness, one of whose fields is not `≈ .zero`.

### 2.3 The split, and a correction to the ledger

Machine-checked (`IsStructure.const_ty`, `.const_ctor`, `.const_rec`, `.fingerprint`,
`.isLE_eq`): two `IsStructure` derivations at one name force `D₁.uvars = D₂.uvars`,
`T₁.type = T₂.type`, `D₁.recUvars = D₂.recUvars`, `D₁.recType 0 = D₂.recType 0`, and hence
`D₁.isLE = D₂.isLE`.

Machine-checked (`structureAgree_of_recTypeInj`): the **whole syntactic half** follows from
`RecTypeInj`, a purely syntactic statement, **using no hypothesis on `env` at all**.

> **Correction.** `Theory/Inductive/Structure.lean` says G4 "needs `VEnv.Sig` (I1)". For the
> syntactic half that is wrong: the recursor constant is a complete fingerprint of the block,
> and the environment argument is three lines. What `VEnv.Sig` would be needed for is not this.

Read off source (not machine-checked): `RecTypeInj` should be true, because
`D.recType 0 = mkPi (params ++ motives ++ minors ++ liftTele … indices) …` and peeling that
telescope recovers `D.params`, `T.indices`, `C.fields`' types and — through the minor
premise's conclusion `motive (C.name params fields)` — `C.name`. Evidence that the minor
premise really does carry `C.name`: renaming `barCtor` to `Bar.mk'` makes the explicit
`constants` map fail to match by `rfl`, i.e. the recursor type changes. A consequence worth
recording: **two blocks that declare the same type name with different constructor names
cannot both be `≤` a common environment**, so the "union environment" counterexample to the
`≈`-form does not exist.

Machine-checked (`barDeclEq_recType_eq : barDeclEq.recType 0 = barDecl.recType 0`, by `rfl`):
**the level half is not reachable syntactically.** `VIndField.lvl` occurs in no constant
`addInduct'` declares. Its only source is `VIndField.WF.hasType`, which says `F.lvl` is *a*
sort of `F.type` in both derivations — so `StructureLvlAgree` is a **`SortUniq`-family
consumer**, the same family as `Injectivity.lean`'s `sort_inv`. That dependency is new; nobody
had recorded it, and the ledger's "needs `VEnv.Sig`" names the wrong obligation for it.

---

## 3. New statements 2 and 3 — facts (C) and (D)

`Verify/Typing/Rigidity.lean`. New file, sorry-free. Both belong in
`Theory/Typing/Injectivity.lean` and are here only because that file is another stream's;
nothing in this file depends on `Verify/`, so it moves verbatim.

### 3.1 (C) `VEnv.ConstRigid`

Stated **with weak-head reduction**, under `[VEnv.Params]`, importing
`Theory/Typing/HeadReduction.lean` — i.e. where the reduction relation is in scope, which is
the condition `Injectivity.lean` set for stating it at all:

```
∀ (Γ : List VExpr) (e : VExpr) (c : Name) (us : List VLevel) (as : List VExpr),
  OnCtx Γ (Params.env.IsType Params.univs) →
  Params.env.RuleFreeHead c →
  Params.env.IsType Params.univs Γ ((VExpr.const c us).mkApp as) →
  Params.env.IsDefEqU Params.univs Γ e ((VExpr.const c us).mkApp as) →
  ∃ us' as', VEnv.WHRedS Γ e ((VExpr.const c us').mkApp as')
```

Head only. The levels and arguments are (B)'s business; folding them in is how three facts
become one wrong one. `ConstRigid.at_lift` records the shape the consumer needs, so the two
cannot drift apart.

### 3.2 (D) `VEnv.ConstNoConf` — the "fourth fact", and it now has a consumer

`Injectivity.lean` says a fourth fact, no-confusion between *distinct* rule-free constants, "is
not stated because no consumer has asked for it". One has. See §5.

```
∀ (Γ : List VExpr) (c c' : Name) (us us' : List VLevel) (as as' : List VExpr),
  OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' →
  env.IsType U Γ ((VExpr.const c us).mkApp as) →
  env.IsDefEqU U Γ ((VExpr.const c us).mkApp as) ((VExpr.const c' us').mkApp as') →
  c = c'
```

Params-free, same shape and same two side conditions as (B).

### 3.3 Non-vacuity

A `Params` instance does not exist in this tree, so (C) cannot be fired at `barEnv` today.
What is checked instead is that the premise both facts are gated on is reachable:

* Machine-checked: `barEnv_ruleFreeHead : barEnv.RuleFreeHead `Bar``, sorry-free, via
  `addInduct'_defeqs_inv` (new, proved here) and `barDecl_iotaRules_heads` (`rfl`: the ι-rules
  are headed by `Bar.rec`).
* Read off source: at a `TrEnv'`-built environment the *temporal* argument of
  `TrEnv'.ruleFreeHead_quot` (`Verify/TypeChecker/Reduce.lean`, sorry-free) should transfer —
  `addConst` refuses a name already present, a `TrEnv'` chain only grows `constants`, ι-rules
  are headed by `mkRecName T.name ≠ S` and quot rules by `Quot.lift`. Not done: it belongs on
  the `Verify/Environment` side and waits on `AddInduct` acquiring constructors. **Do not
  charge this to `VEnv.Sig`.**

Side conditions: both are transcribed from (B)'s, whose necessity is machine-checked in
`Theory/Typing/ConstInvWitness.lean`. Read off source: with `IsType` present, `proofIrrel`
cannot fire at the top of (C), because it would need the common type `.sort u` to be a
proposition, i.e. `.succ u ≈ .zero`.

---

## 4. `TrProj.wf` — the refutation, and the live route

### 4.1 What is dead

Machine-checked, `Verify/Typing/ProjLevelWitness.lean`'s `barRefutes` (previous round): the
subgoal the current proof reduces to — `lvl_k.inst us ≈ .zero` at an unused field `k < i` — is
**false**. The inline comment at the `sorry` claimed "one `Ctx.LiftN.one` strengthening step
per unused field"; that is wrong about the *shape* — the goal is a level equivalence and
strengthening produces typing judgements. The comment is now corrected in place.

### 4.2 What is live

`Verify/Typing/ProjSkip.lean`. New file, sorry-free.

The mechanism: `projCore`'s only use of the earlier projections is inside its motive,
`instAll ftype (ps.map (·.liftN _) ++ earlier)`. In `instAll e as k` the element at list
position `j` substitutes at de Bruijn index `as.length - 1 - j` (`instAll_cons`), so with
`|ps| = np`, `|earlier| = i`, entry `earlier[k]` substitutes at index `i - 1 - k` — **exactly
the index `VIndCtor.not_fieldUsed_skips` proves `ftype` skips** when field `k` is unused. So
the ill-typed projection is not in the term being typed.

Machine-checked:

* `VExpr.inst_congr_skips`, `VExpr.instAll_congr_skips` — the substitution lemma.
* `VInductDecl'.projCore_congr_earlier` — its `projCore` instance.
* `barDecl_projCore_indep` (`rfl`): at the two-field witness, field 0's projection is
  irrelevant to `.proj Bar 1`.
* `barDecl_projTerm_eq` (`rfl`): `projTerm … 1 e` equals the instance that supplies a
  trivially well-typed term at the unused position instead of the ill-typed one.
* `barDecl_projTerm_spelled` (`rfl`): the whole term is
  `Bar.rec (fun _ : Bar => ∀ p : Prop, p) (fun (n : Prop) (h : ∀ p : Prop, p) => h) e`. No
  occurrence of a projection of field 0 anywhere. `TrProj.wf` is **true** at the very witness
  that refutes its current proof's subgoal.

`VIndCtor.not_fieldUsed_skips` is described in `Theory/Inductive/Structure.lean` as "stated and
unused". This is the use.

### 4.3 The residual, and the correction that makes it live

Read off source: the route types the motive body from the *compressed* spine, dropping the
positions the field type skips. That needs the field type's typing in the compressed context,
i.e. single-binder strengthening for a type:

    IsType (A :: Δ) (X.liftN 1)  ⟹  IsType Δ X

> **Correction to `TrProj.wf`'s docstring.** It says the rescoped target and
> `NormalEq.weakN_inv_DFC` are "gated on a `VEnv.Params` instance" and to "re-evaluate when
> `VEnv.Params` completes". That is too pessimistic. `VEnv.IsType.weakN_iff`
> (`Theory/Typing/UniqueTyping.lean:221`) **already exists**, at `Ctx.LiftN.one`, and is used
> freely elsewhere in `Lemmas.lean` (`HasType.weak'_iff` in the `lam`/`forallE` cases of
> `TrExprS.weakFV'_inv`, `VExpr.WF.weak'_iff` in the `app` case). It is backed by
> `IsDefEqU.weakN_iff`'s `sorry` at `UniqueTyping.lean:172` — an *existing* hole owned by
> another stream. Using it costs a dependency, not a new statement. Nothing here waits on
> `Params`.

Remaining work, all bulk: guarded re-proofs of `projArgs_hasArgs`, `projMotiveBody_hasType`
(both `Theory/Inductive/StructureClosed.lean`, which this stream does not own),
`projMinor_hasType` and `projTerm_hasType` (`Verify/Typing/Lemmas.lean`), with `hlv` weakened
from `∀ k ≤ i` to F17's guarded `∀ k ≤ i, (k = i ∨ C.FieldUsed D 0 k)`. Plus one bounded
syntactic step: bridging `not_fieldUsed_skips`'s `i - 1 - k` to the skip *after* the `ps`
substitutions (substituting at indices `≥ i` cannot create an occurrence below `i`).

Two routes that do **not** work, checked so nobody re-tries them:

* Replacing the unused telescope entry by an inhabited type (`.sort (.succ .zero)`, inhabited
  by `.sort .zero`) and using the modified context. The field type's typing then lives in the
  *swapped* context, and "swap a context entry the subject and type both skip" is not free — a
  subderivation may still mention it.
* Adding the unused field's type to `Γ` and using `bvar 0`. Adding an assumption and removing
  it again *is* strengthening.

---

## 5. `TrProj.uniq` — a reverted narrowing, and what it found

`TrProj.uniq` is stated with the two structure names `s₁`, `s₂` **independent**. That looks
exactly like the auto-bound-implicit defect this session has hit twice, and it was narrowed to
a shared `s` on the reading that its only consumer is `TrExprS.uniq`'s `proj` case.

**That reading is wrong and the narrowing was reverted.** Machine-checked, in the negative
sense that the tree goes red: there is a **second consumer**, `IsDefEqE.trExpr`'s `proj` case
(`Verify/EquivManager.lean:117`), and it instantiates the two names *differently*, because

    RelevantEq.proj : RelevantEq e₁ e₂ → RelevantEq (.proj _ i e₁) (.proj _ i e₂)

drops the structure name. That is faithful to the checker: `EquivManager.isEquiv`
(`Lean4Lean/EquivManager.lean`) has
`| .proj _ i1 e1, .proj _ i2 e2 => pure (i1 == i2) <&&> isEquiv e1 e2`. So the general form is
demanded, and `TrProj.uniq` must derive `s₁ = s₂` — which is fact **(D)**, §3.2. Do not
re-attempt the narrowing without changing `RelevantEq` and `isEquiv` together; that is a
checker change, not a proof change.

**Loose end, not investigated, flagged for whoever owns the checker:** the C++ `equiv_manager`
was not consulted (`~/lean4/src/kernel/equiv_manager.cpp` does not exist at that path in this
checkout), so it is *unknown* whether ignoring the projection's structure name matches the C++
kernel or diverges from it. If it diverges it is a `divergences.md` entry; if `isEquiv` can
return `true` for `.proj Foo 0 e` vs `.proj Bar 0 e` on inputs the kernel actually reaches, it
may be a `bugs-found.md` entry. Neither is established here.

The four obligations, with §2 and §3 filling in two of them, are in `TrProj.uniq`'s docstring.
The fourth — a congruence lemma for `VInductDecl'.projTerm` under level equivalence on `us` and
`IsDefEqU` on `ps`, `ιs`, subject — does not exist, is mechanical, and had not been costed.

---

## 6. `inferProj.WF` — a decision, not a proof problem

Machine-checked, already in the tree: `inferProj_always_throws` proves
`(inferProj st i e ety).WF c s Q` for **any** postcondition `Q`, because `inferProj`'s
`.inductInfo` gate cannot fire while `AddInduct` has no constructors. So
`inferProj.WF := inferProj_always_throws hty` closes that `sorry` in one line, today, and the
census drops 21 → 20.

**Not done, deliberately.** The previous round left it open on the argument in its docstring:
closing it vacuously hides that `inferProj.WF` is **false once the branch is live**, because
`inferProj` never checks recursiveness while `VEnv.IsStructure.noRec` demands
`C.recFields = []` (`bugs-found.md` item 10 — the kernel accepts `.proj` on
`inductive R | mk : R → Nat → R`). Overriding that is a judgement call about what the census
number is *for*, and it belongs to whoever owns the number, not to this stream. Both options
are one line; the orchestrator should pick.

Note that closing it would not hide the tripwire: `inferProj_always_throws` keeps its own
docstring and goes red at the same moment.

---

## 7. Files

New, all sorry-free, all `#print axioms` clean:

* `Lean4Lean/Verify/Typing/StructureUniq.lean` — §2.
* `Lean4Lean/Verify/Typing/Rigidity.lean` — §3.
* `Lean4Lean/Verify/Typing/ProjSkip.lean` — §4.2.

Edited: `Lean4Lean/Verify/Typing/Lemmas.lean` — docstrings and the comment at `TrProj.wf`'s
`sorry` only; no statement in the tree was changed (the one attempt is §5). Census unchanged at
21; `lake build` green on the default targets.

**Auto-bound-implicit audit.** Every new statement is a `def … : Prop` or a `structure` with
all binders explicit; `#print` output was inspected for each of `VEnv.StructureUniq`,
`RecTypeInj`, `StructureAgree`, `StructureLvlAgree`, `VEnv.ConstRigid`, `VEnv.ConstNoConf`,
`VExpr.instAll_congr_skips`, `VInductDecl'.projCore_congr_earlier`. No capture. The existing
statement that *looked* like the defect — `TrProj.uniq` — is not one; §5.
