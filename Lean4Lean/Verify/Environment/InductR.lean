import Lean4Lean.Verify.Environment.Induct
import Lean4Lean.Theory.Inductive.NestedHead
import Lean4Lean.Environment
import Lean4Lean.Theory.Inductive.NestedBuild
import Lean4Lean.Theory.Typing.Meta

/-!
# The constant-map side of a **nested** inductive block

`Verify/Inductive/AddDeclWF.lean` §2 proved that `AddInductStages` — the intended definition
of `AddInduct` — is **refuted** for a nested block: the checker's nested path adds one
*renamed* auxiliary recursor per nested type (`mkAuxRecNameMap`: `_nested.J.rec ↦ I.rec_1`),
and `I.rec_1` is `mkRecName` of no type the block declares, while `AddInductStages` is exact
on the map.  That refutation is `TrIndDecl.not_addInductStages` / `tBlock_not_addInductStages`
and it stands: it is a statement about `AddInductStages`, which does not change.

This file supplies the repair.  It is **not** a new mechanism: `Theory/Inductive/Companion.lean`
and `Theory/Inductive/NestedHead.lean` already model exactly this renaming on the abstract
side —

* `VInductDecl'.typeConstsC K` / `ctorConstsCR R K` — the members named in `K` are *not*
  declared (their type constants and constructors already exist, under their restored names);
* `VInductDecl'.recConstsR R K` — **every** member gets a recursor, including the ones in `K`,
  under `R.recName (mkRecName ·)`;
* `VEnv.addInductR D K R` — the environment step built from those three lists plus
  `iotaRulesR R`, whose every emitted ι-rule is keyed to a constant the *same* step declares
  (`VInductDecl'.iotaRulesR_key_declared`, `VEnv.addInductR_key_declared`).

`AddInductStagesR` below is the constant-map fold over those same three lists, in the same
three-stage shape `AddInductStages` has, and it discharges into `VEnv.addInductR` exactly as
`AddInductStages.to_addInduct` discharges into `VEnv.addInduct'`.

## The invariant

> **Every constant the step adds to the map is one the translated declaration accounts for.**

Formally, in two halves:

* `AddInductStagesR.find?_of_not_mem` — outside `D.allNamesCR R K`, the output map *equals*
  the input map.  This is what makes the relation a **definition of the output map** rather
  than a check on it, and it is inherited verbatim from `AddIndConsts.find?_of_not_mem`,
  which is already list-generic.
* `TrIndDeclN.mem_indDeclNamesN` — `D.allNamesCR R K ⊆ indDeclNamesN types numNested`, the
  names a `Lean.Declaration.inductDecl` block with `numNested` auxiliary types can
  legitimately introduce: the type names, the constructor names, `mkRecName` of each type
  name, **and** `appendIndexAfter' (mkRecName types[0].name) k` for `1 ≤ k ≤ numNested`, which
  is precisely `mkAuxRecNameMap`'s output (`Lean4Lean/Inductive/Add.lean`).

Composed: `InductStepNested.find?_of_not_mem`.  Nothing outside `indDeclNamesN` moves, and the
auxiliary recursor names are pinned to `types[0].name` and `numNested` — *a function of the
declaration*, not a free parameter.  The relation therefore still bites: §4's negative
controls show `T.rec_2` at `numNested = 1`, and `T.rec_1` at `numNested = 0`, are refuted
exactly as before.

## What is **not** fixed here, stated exactly

`TrEnv'.wf` discharges `TrEnv'.induct` into `VDecl.WF.induct` (`Theory/Typing/Env.lean`),
whose second hypothesis is `env.addInduct' decl = some env'`.  A nested step produces
`env.addInductR D K R = some env'` instead, and no `VInductDecl'` has `addInduct'` equal to a
nested `addInductR` — the constant lists differ.  So flipping `AddInduct` to
`AddInductStagesR` additionally requires that rule to be generalised, in a file this stream
does **not** own.

The generalisation must be `VEnv.AddNestedStep` (`Theory/Inductive/Restore.lean`), not bare
`addInductR`: with `K` and `R` free, a step could drop constants or rename them arbitrarily.

**CORRECTION (this round).**  This paragraph used to say the obstruction is that
`VEnv.AddNestedB` "quantifies over the declaration history `ds`, and `VDecl.WF` does not carry
`ds`".  That was the *stateability* obstruction and it is **gone**: `ds` was only ever used for
"this block was declared earlier", which is now `VInductDecl'.Declared` over the environment
alone (`Theory/Inductive/Decl.lean`), discharged from a history by `VEnv.WF'.declared`; and
`VEnv.addInductR`/`VIndRestore.Faithful` moved upstream of `Theory/Typing/Env.lean` into
`Theory/Inductive/Restore.lean`, so the rule is nameable there (machine-checked by the
`example` in that file).

What actually stands between here and the rule is two *theorems*, neither of which is about
the constant map: `VEnv.addInductR_ordered` — `Ordered` for a nested step, i.e. the **restored**
constructor and recursor types are well typed and the restored ι-rules well formed, factored
into its three remaining obligations at `Theory/Inductive/NestedOrdered.lean` — and the
`DeltaUnique` freshness transcription, which is *false* as it stands for a nested block
(`VEnv.iotaRulesR_major_not_fresh`, `nfn_companion_key_not_fresh`).  See
`docs/handoff-inductive-add.md` §5.

Everything on *this* side of that line is proved below and fires at a nested witness.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. `AddInductStagesR`: the three stages, companion-aware and renamed -/

/-- **The nested-aware constant-map step.**  `AddInductStages` with `D.typeConsts`,
`D.ctorConsts`, `D.recConsts` replaced by their companion-aware, restored forms, and the
ι-rules likewise.  `K` names the members that are *not* declared (the auxiliary nested types,
whose real counterparts are already in the environment); `R` is the restoration, whose
`recName` component is `mkAuxRecNameMap`'s renaming.

At `K = []` and `R = D.idRestore` this **is** `AddInductStages` for a canonical block
(`AddInductStagesR.of_addInductStages` and `AddInductStages.toR` below), so nothing already
proved about the non-nested case is given up. -/
def AddInductStagesR (m₁ : ConstMap) (env₁ : VEnv) (D : VInductDecl')
    (K : List Name) (R : VIndRestore) (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  ∃ mt et mc ec e₃,
    AddIndConsts (IndShapeOf D R.ctorName) (D.typeConstsC K) m₁ env₁ mt et ∧
    AddIndConsts (CtorShapeOf D R.ctorName R.tyName) (D.ctorConstsCR R K) mt et mc ec ∧
    AddIndConsts (fun ci => ∃ v, ci = .recInfo v) (D.recConstsR R K) mc ec m₂ e₃ ∧
    env₂ = e₃.addIndRulesR D K R

theorem AddInductStagesR.to_addInductR {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) : env₁.addInductR D K R = some env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  have : env₁.addConstList (D.allConstsCR R K) = some e₃ := by
    simp only [VInductDecl'.allConstsCR, VEnv.addConstList_append, h1.to_addConstList,
      h2.to_addConstList, h3.to_addConstList, Option.bind_some]
  rw [VEnv.addInductR, this]; rfl

theorem AddInductStagesR.le {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) :
    env₁ ≤ env₂ := VEnv.addInductR_le H.to_addInductR

theorem AddInductStagesR.map_wf {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} (H : AddInductStagesR m₁ env₁ D K R m₂ env₂)
    (hwf : m₁.WF) : m₂.WF := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  exact h3.map_wf (h2.map_wf (h1.map_wf hwf))

/-- **The strong form of `find?_shape`, nested-aware.**  As in the non-nested case, a name the
block introduces carries the *bookkeeping* of the member it belongs to, not merely one of the
three `ConstantInfo` shapes.  The renaming is threaded: constructor names are read modulo
`R.ctorName` and a constructor's `induct` field modulo `R.tyName`. -/
theorem AddInductStagesR.find?_shape' {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} {name ci}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (hwf : m₁.WF) (h : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨
    ((IndShapeOf D R.ctorName ci ∨ CtorShapeOf D R.ctorName R.tyName ci ∨
        (∃ v, ci = .recInfo v)) ∧
      ci.name = name ∧ ci.safety = .safe) := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  rcases h3.find? (h2.map_wf (h1.map_wf hwf)) h with h | ⟨hS, h⟩
  · rcases h2.find? (h1.map_wf hwf) h with h | ⟨hS, h⟩
    · rcases h1.find? hwf h with h | ⟨hS, h⟩
      exacts [.inl h, .inr ⟨.inl hS, h⟩]
    · exact .inr ⟨.inr (.inl hS), h⟩
  · exact .inr ⟨.inr (.inr hS), h⟩

/-- **The new disjunct of `TrEnv'.find?_shape`, nested-aware.**  Unchanged in shape from
`AddInductStages.find?_shape`: a name the block introduces carries one of the three inductive
`ConstantInfo` shapes and is `safe`-tagged; every other name is unchanged.  The safety gate of
`Verify/Inductive/AddDeclWF.lean` §1 therefore transfers verbatim. -/
theorem AddInductStagesR.find?_shape {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} {name ci}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (hwf : m₁.WF) (h : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨
    (((∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)) ∧
      ci.name = name ∧ ci.safety = .safe) :=
  (H.find?_shape' hwf h).imp id fun ⟨hS, h⟩ =>
    ⟨hS.imp IndShapeOf.inductInfo (·.imp CtorShapeOf.ctorInfo id), h⟩

/-- **The only rules a nested block adds are its restored ι-rules.**  The three constant
stages add none. -/
theorem AddInductStagesR.defeqs {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} {df}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (h : env₂.defeqs df) :
    env₁.defeqs df ∨ df ∈ D.iotaRulesRS R K := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  have hstage : e₃.defeqs = env₁.defeqs := by rw [h3.defeqs, h2.defeqs, h1.defeqs]
  rw [VEnv.addIndRulesR] at h
  refine (VEnv.addDefEqList_defeqs_inv _ _ h).imp (fun h => ?_) id
  rwa [hstage] at h

/-- **The anti-lie half.**  Outside `D.allNamesCR R K` the output map *is* the input map. -/
theorem AddInductStagesR.find?_of_not_mem {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {n : Name}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (hwf : m₁.WF) (h : n ∉ D.allNamesCR R K) :
    m₂.find? n = m₁.find? n := by
  simp only [VInductDecl'.allNamesCR, VInductDecl'.allConstsCR, List.map_append,
    List.mem_append, not_or] at h
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, -⟩ := H
  rw [h3.find?_of_not_mem (h2.map_wf (h1.map_wf hwf)) h.2,
    h2.find?_of_not_mem (h1.map_wf hwf) h.1.2, h1.find?_of_not_mem hwf h.1.1]

/-- The staged environment `VInductDecl'.WFC.ctors` is stated over is produced by the
relation itself, exactly as in the non-nested case. -/
theorem AddInductStagesR.addIndTypesC {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) :
    ∃ et, env₁.addIndTypesC D K = some et := by
  obtain ⟨mt, et, mc, ec, e₃, h1, -, -, -⟩ := H
  exact ⟨et, h1.to_addConstList⟩

/-! ### Conservativity: at `K = []`, `R = idRestore`, this is `AddInductStages`

`Theory/Inductive/NestedHead.lean` Part 3 does the work; these two are the constant-map
statements of it.  So `AddInductStagesR` is a *generalisation* of `AddInductStages`, and the
non-nested theory (`Verify/InductFlip.lean`, `AddDeclWF.lean` §1 and §3) is unaffected. -/

theorem AddInductStages.toR {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductStages m₁ env₁ D m₂ env₂) :
    AddInductStagesR m₁ env₁ D [] D.idRestore m₂ env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  refine ⟨mt, et, mc, ec, e₃, ?_, ?_, ?_, ?_⟩
  · rwa [VInductDecl'.typeConstsC_nil]
  · rwa [D.ctorConstsCR_id, VInductDecl'.ctorConstsC_nil]
  · rwa [D.recConstsR_id]
  · rw [VEnv.addIndRulesR_id _]

theorem AddInductStagesR.of_addInductStages {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} (H : AddInductStagesR m₁ env₁ D [] D.idRestore m₂ env₂)
    : AddInductStages m₁ env₁ D m₂ env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  rw [VInductDecl'.typeConstsC_nil] at h1
  rw [D.ctorConstsCR_id, VInductDecl'.ctorConstsC_nil] at h2
  rw [D.recConstsR_id] at h3
  exact ⟨mt, et, mc, ec, e₃, h1, h2, h3, by rw [VEnv.addIndRulesR_id _]⟩

/-! ## 2. The names a nested block may introduce, and the translation that pins them

`Verify/Environment/Induct.lean`'s `indDeclNames` lists the names a *non-nested* block
introduces: the type names, the constructor names, and `mkRecName` of each type name.  The
nested path adds exactly one more family, and `mkAuxRecNameMap` (`Lean4Lean/Inductive/Add.lean`)
fixes it completely:

```
let mainName := types[0].name
for indName in allNames.drop types.length do
  recMap := (mkRecName indName, appendIndexAfter' (mkRecName mainName) nextIdx) :: recMap
  nextIdx := nextIdx + 1
```

so the extra names are `types[0].name ++ "rec_1"`, `… "rec_2"`, …, one per auxiliary type.
They are a **function of the declaration and `numNested`**, which is what keeps the invariant
from going slack: §4's negative controls show a second auxiliary recursor at `numNested = 1`,
and the first at `numNested = 0`, are still refuted. -/

/-- The `k`-th auxiliary recursor name of a block: `mkAuxRecNameMap`'s
`appendIndexAfter' (mkRecName types[0].name) (k+1)`. -/
def auxRecName (types : List InductiveType) (k : Nat) : Name :=
  Lean4Lean.appendIndexAfter' (Lean.mkRecName (types.headD default).name) (k + 1)

/-- Every name a `Lean.Declaration.inductDecl` block with `numNested` auxiliary nested types
can legitimately introduce.  At `numNested = 0` this is `indDeclNames`
(`indDeclNamesN_zero`). -/
def indDeclNamesN (types : List InductiveType) (numNested : Nat) : List Name :=
  indDeclNames types ++ (List.range numNested).map (auxRecName types)

@[simp] theorem indDeclNamesN_zero (types : List InductiveType) :
    indDeclNamesN types 0 = indDeclNames types := by simp [indDeclNamesN]

/-- The constructor half of the nested translation.  Two differences from `TrIndCtor`: the
name is compared against `R.ctorName C.name` (the *restored* name, which for a member the
user wrote is the name itself), and the stored type is the restored `VIndCtor.typeR` — which
is the type `Environment.addInductive` actually puts in the environment, `restoreNested`
having rewritten the auxiliary heads back. -/
def TrIndCtorR (env : VEnv) (Us : List Name) (D : VInductDecl') (R : VIndRestore) (j : Nat)
    (c : Constructor) (C : VIndCtor) : Prop :=
  c.name = R.ctorName C.name ∧ TrExprS env Us [] c.type (C.typeR D R j)

/-- **The nested translation relation.**  `TrIndDecl` with four additions, all of them
*name* discipline — the semantic content stays in `VInductDecl'.WF` exactly as before:

* `length`/`companions` say `D` is the user's block followed by `numNested` auxiliary
  members, and that `K` is exactly that auxiliary tail;
* `ctorName_own` says the two sides' constructor names agree on the user's members;
* `recName_own` says a member the user wrote keeps its recursor name;
* `recName_aux` says an auxiliary member's recursor is renamed to `mkAuxRecNameMap`'s name.

These are facts `Environment.addInductive`'s nested path establishes by
construction, and together with `AddInductStagesR.find?_of_not_mem` the first two groups give
the invariant: *every constant the step adds to the map is one the translated declaration
accounts for* (`mem_indDeclNamesN`).

`ctorName_own` was added 2026-09-01; its producer side, the consumer audit that a new conjunct
on a *hypothesis* relation requires, and the `RestoreData.ctor` result it unblocks are in
`Verify/Inductive/TrIndDeclNCtorOwn.lean`. -/
structure TrIndDeclN (env : VEnv) (Us : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (numNested : Nat)
    (D : VInductDecl') (K : List Name) (R : VIndRestore) : Prop where
  /-- Safe blocks only, for the reason `TrIndDecl.safe` records. -/
  safe : isUnsafe = false
  uvars : Us.length = D.uvars
  np : nparams = D.np
  /-- The auxiliary members are appended after the user's. -/
  length : D.types.length = types.length + numNested
  /-- **`K` is exactly the auxiliary tail.**  Left-to-right this is what stops a user member
  being silently dropped from the map; right-to-left it is what makes the auxiliary members
  undeclared. -/
  companions : ∀ (j : Nat) T, D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j)
  trType : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T
  trCtorsLen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    t.ctors.length = T.ctors.length
  /-- Staged over the *companion-aware* `addIndTypesC`: only the user's type constants are
  declared, which is exactly the environment `AddInductStagesR`'s first stage produces. -/
  trCtors : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → TrIndCtorR env₁ Us D R j c C
  /-- **The two sides' constructor names agree pointwise on the user's members.**

  Not derivable from `trCtors`, which compares against `R.ctorName C.name` — the *restored*
  name — so it says nothing about `C.name` itself.  This clause is what breaks the circle
  recorded at `docs/vacuity-ledger.md` row 80a/91c: `RestoreData.ctor`'s prefix half was
  reachable only through `VIndRestore.OwnId.ctorName`, whose own proof
  (`Result.mkRestore_ownId`) runs *through* `RestoreData.ctor`.  With `ctorName_own` the
  derivation mentions no `R` at all (`Result.ctor_prefix_of_run`).

  **Unstaged, deliberately.**  `trCtors` is quantified over `env.addIndTypesC D K = some env₁`
  because `TrExprS` of a constructor type needs the block's type constants declared; a *name*
  equation needs no environment, and staging it would push the premise onto every consumer.
  The cost is paid by the one bridge that can only get it from `trCtors`: `TrIndDecl.toN` takes
  the `addIndTypes` success as an explicit premise, which is available at its only call site
  (`Verify/Inductive/AddInductiveStep.lean`'s `addInductiveStepWF_of_run`, from
  `AddInductStages.addIndTypes`). -/
  ctorName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name
  /-- A member the user wrote keeps its recursor name. -/
  recName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    R.recName (Lean.mkRecName T.name) = Lean.mkRecName t.name
  /-- **`mkAuxRecNameMap`, as a clause.** -/
  recName_aux : ∀ (j : Nat) T, D.types[j]? = some T → types.length ≤ j →
    R.recName (Lean.mkRecName T.name) = auxRecName types (j - types.length)

/-- **The invariant.**  Every constant the step declares is one the translated declaration
accounts for: a type name, a constructor name, `mkRecName` of a type name, or one of the
`numNested` auxiliary recursor names `mkAuxRecNameMap` produces.

This is `TrIndDecl.mem_indDeclNames` with the auxiliary family added, and it is the exact
statement `AddDeclWF.lean` §2 showed no `VInductDecl'` could satisfy against
`AddInductStages`. -/
theorem TrIndDeclN.mem_indDeclNamesN {env env₁ : VEnv} {Us : List Name} {np numNested : Nat}
    {types : List InductiveType} {iu : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} (h : TrIndDeclN env Us np types iu numNested D K R)
    (hst : env.addIndTypesC D K = some env₁)
    {n : Name} (hn : n ∈ D.allNamesCR R K) : n ∈ indDeclNamesN types numNested := by
  have hown : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
      ∃ t, types[j]? = some t ∧ t.name = T.name := by
    intro j T hT hK
    have hj : j < types.length := Nat.lt_of_not_le fun hle => hK ((h.companions j T hT).2 hle)
    obtain ⟨t, ht⟩ := exists_getElem?_of_lt hj
    exact ⟨t, ht, (h.trType j t T ht hT).1⟩
  simp only [VInductDecl'.allNamesCR, VInductDecl'.allConstsCR, List.map_append,
    List.mem_append] at hn
  simp only [indDeclNamesN, indDeclNames, List.mem_append]
  rcases hn with (hn | hn) | hn
  · -- a declared type name: the member is one the user wrote
    simp only [VInductDecl'.typeConstsC, VInductDecl'.typeConsts, List.mem_map,
      List.mem_filterMap] at hn
    obtain ⟨c, ⟨c₀, hc₀, hif⟩, rfl⟩ := hn
    split at hif
    · exact absurd hif (by simp)
    · rename_i hK; cases hif
      obtain ⟨T, hT, rfl⟩ := hc₀
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
      obtain ⟨t, ht, hname⟩ := hown j T hj hK
      exact .inl (.inl (.inl (List.mem_map.2 ⟨t, List.mem_iff_getElem?.2 ⟨j, ht⟩, hname⟩)))
  · -- a declared constructor name: its member is one the user wrote, and `R.ctorName`
    -- restores it to the name the user wrote
    simp only [VInductDecl'.ctorConstsCR, List.mem_map, List.mem_filterMap] at hn
    obtain ⟨c, ⟨⟨j, C⟩, hjC, hif⟩, rfl⟩ := hn
    split at hif
    · exact absurd hif (by simp)
    · rename_i hK; cases hif
      obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
      rw [List.getD_eq_getElem?_getD, hT] at hK
      obtain ⟨t, ht, -⟩ := hown j T hT hK
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hC
      have hqlt : q < t.ctors.length := by
        rw [h.trCtorsLen j t T ht hT]; exact List.getElem?_eq_some_iff.1 hq |>.1
      obtain ⟨c', hc'⟩ := exists_getElem?_of_lt hqlt
      have hname := (h.trCtors env₁ hst j t T ht hT q c' C hc' hq).1
      refine .inl (.inl (.inr (List.mem_flatMap.2 ⟨t, List.mem_iff_getElem?.2 ⟨j, ht⟩, ?_⟩)))
      exact List.mem_map.2 ⟨c', List.mem_iff_getElem?.2 ⟨q, hc'⟩, hname⟩
  · -- a recursor name: `mkRecName` of a user member, or `mkAuxRecNameMap`'s `I.rec_k`
    simp only [VInductDecl'.recConstsR, List.mem_map] at hn
    obtain ⟨c, ⟨⟨T, j⟩, hTj, rfl⟩, rfl⟩ := hn
    have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
    by_cases hle : types.length ≤ j
    · refine .inr (List.mem_map.2 ⟨j - types.length, ?_, (h.recName_aux j T hT hle).symm⟩)
      refine List.mem_range.2 ?_
      have hjlt : j < D.types.length := List.getElem?_eq_some_iff.1 hT |>.1
      rw [h.length] at hjlt; omega
    · obtain ⟨t, ht⟩ := exists_getElem?_of_lt (Nat.lt_of_not_le hle)
      exact .inl (.inr (List.mem_map.2 ⟨t, List.mem_iff_getElem?.2 ⟨j, ht⟩,
        (h.recName_own j t T ht hT).symm ▸ rfl⟩))

/-! ### Conservativity of the translation

At `numNested = 0`, `K = []`, `R = D.idRestore`, `TrIndDeclN` **is** `TrIndDecl`.  So the
non-nested theory is unchanged and `Verify/Environment/Induct.lean`'s witnesses transfer. -/

theorem TrIndDecl.toN {env : VEnv} {Us : List Name} {np : Nat} {types : List InductiveType}
    {iu : Bool} {D : VInductDecl'} (h : TrIndDecl env Us np types iu D)
    (hst : ∃ et, env.addIndTypes D = some et) :
    TrIndDeclN env Us np types iu 0 D [] D.idRestore where
  safe := h.safe
  uvars := h.uvars
  np := h.np
  length := by rw [← h.length]; rfl
  companions := by
    intro j T hT
    simp only [List.not_mem_nil, false_iff, Nat.not_le]
    rw [h.length]; exact List.getElem?_eq_some_iff.1 hT |>.1
  trType := h.trType
  trCtorsLen := h.trCtorsLen
  trCtors := by
    intro env₁ hst j t T ht hT q c C hc' hC
    rw [VEnv.addIndTypesC_nil] at hst
    obtain ⟨hname, htr⟩ := h.trCtors env₁ hst j t T ht hT q c C hc' hC
    refine ⟨hname, ?_⟩
    rwa [VIndCtor.typeR_id]
  ctorName_own := by
    intro j t T ht hT q c C hc' hC
    obtain ⟨et, het⟩ := hst
    exact (h.trCtors et het j t T ht hT q c C hc' hC).1
  recName_own := by
    intro j t T ht hT
    rw [VInductDecl'.idRestore]; exact congrArg Lean.mkRecName (h.trType j t T ht hT).1.symm
  recName_aux := by
    intro j T hT hle
    have := List.getElem?_eq_some_iff.1 hT |>.1
    rw [← h.length] at this
    exact absurd this (Nat.not_lt.2 hle)

/-! ## 3. The refutation, re-run

`TrIndDecl.not_addInductStages` (`Verify/Environment/Induct.lean`) is unchanged and still
true.  Its nested-aware counterpart is below, and it is *strictly weaker in exactly one
family*: the auxiliary recursor names.  Everything else is still refuted. -/

/-- **The invariant, as a refutation.**  If the checker's output map holds a name outside
`indDeclNamesN types numNested`, then no `(D, K, R)` translating the declaration stands in
`AddInductStagesR` between the two maps.

Compare `TrIndDecl.not_addInductStages`: the *only* difference is that `indDeclNamesN`
contains `mkAuxRecNameMap`'s `numNested` auxiliary recursor names.  §4's negative controls
check that the difference is exactly that and no more. -/
theorem TrIndDeclN.not_addInductStagesR {env env₂ : VEnv} {Us : List Name} {np numNested : Nat}
    {types : List InductiveType} {iu : Bool} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} {m₁ m₂ : ConstMap}
    (h : TrIndDeclN env Us np types iu numNested D K R) (hwf : m₁.WF)
    {n : Name} (h₁ : m₁.find? n = none) (h₂ : m₂.find? n ≠ none)
    (hn : n ∉ indDeclNamesN types numNested) :
    ¬ AddInductStagesR m₁ env D K R m₂ env₂ := by
  intro H
  obtain ⟨et, hst⟩ := H.addIndTypesC
  exact h₂ <| by
    rw [H.find?_of_not_mem hwf fun hm => hn (h.mem_indDeclNamesN hst hm), h₁]

/-! ## 4. The obligation, nested-aware

`Verify/Inductive/AddDeclWF.lean` §3's `InductStepSafe` with `AddInductStages` replaced by
`AddInductStagesR`, `TrIndDecl` by `TrIndDeclN`, and `VInductDecl'.WF` by the companion-aware
`VInductDecl'.WFC` (`Theory/Inductive/CompanionResolve.lean`), which is the one that does not
go vacuous on a block with companion members.

It remains a **definition of the output map, not a check on it**: `find?_of_not_mem` below is
the property at the level the branch consumes it. -/

/-- The `inductDecl` branch's obligation at one safety level, for a safe block with
`numNested` auxiliary nested types.

**Which well-formedness, and why.**  `D` is the *auxiliary* block — the user's members
followed by `numNested` companion members with fresh `_nested.*` names — and
`AddInductive.run` checks it in a scratch environment in which **all** of its type constants,
auxiliary ones included, are declared.  That is `VInductDecl'.WF`, whose `ctors` clause is
staged over `env.addIndTypes D`, **not** `VInductDecl'.WFC … K`, whose clause is staged over
`addIndTypesC D K` — an environment in which a companion member's own constructor type is not
even well-formed.  (`WFC` exists for the *other* companion shape, a block re-declaring a type
that is already in the environment; `Theory/Inductive/Companion.lean`'s `fooCompDecl`.  The
nested path never does that: `mkUniqueName` gives the auxiliary members fresh names.)

**The vacuity guard.**  `WF.ctors`'s premise is `env.addIndTypes D = some env₁`, which is
`none` when a member's name collides — the exact mechanism by which `fooComp_WF` holds
vacuously and `fooComp_inconsistent` bites.  `AddInductStagesR` alone does *not* supply that
premise, because it only declares the non-companion types.  So the success is a **conjunct
here**, and `ctors_nonvacuous` reads it back. -/
def InductStepNested (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) (numNested : Nat) : Prop :=
  ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore),
    TrIndDeclN venv lp np types false numNested D K R ∧
    (∃ et, venv.addIndTypes D = some et) ∧
    D.WF venv ∧
    AddInductStagesR m venv D K R m' venv'

/-- **The constructor obligation is not vacuous.**  Contrast `fooComp_WF`
(`Theory/Inductive/Companion.lean`), where the same clause is discharged by `absurd` because
`addIndTypes` returns `none`. -/
theorem InductStepNested.ctors_nonvacuous {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) :
    ∃ (D : VInductDecl') (et : VEnv), venv.addIndTypes D = some et ∧
      ∀ j (T : VIndType), D.types[j]? = some T → ∀ C ∈ T.ctors, C.WF et D j T := by
  obtain ⟨D, _, _, -, ⟨et, het⟩, hwf, -⟩ := h
  exact ⟨D, et, het, fun j T hT C hC => hwf.ctors et het j T hT C hC⟩

theorem InductStepNested.le {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) : venv ≤ venv' :=
  let ⟨_, _, _, _, _, _, hadd⟩ := h; hadd.le

theorem InductStepNested.map_wf {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) (hwf : m.WF) : m'.WF :=
  let ⟨_, _, _, _, _, _, hadd⟩ := h; hadd.map_wf hwf

/-- **The output map is determined outside the block**, auxiliary recursors included. -/
theorem InductStepNested.find?_of_not_mem {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) (hwf : m.WF)
    {n : Name} (hn : n ∉ indDeclNamesN types numNested) : m'.find? n = m.find? n := by
  obtain ⟨D, K, R, htr, -, -, hadd⟩ := h
  obtain ⟨et, hst⟩ := hadd.addIndTypesC
  exact hadd.find?_of_not_mem hwf fun hm => hn (htr.mem_indDeclNamesN hst hm)

/-- Every constant the step declares carries one of the three inductive shapes and is
`safe`-tagged — the safety gate of `Verify/Inductive/AddDeclWF.lean` §1, unchanged. -/
theorem InductStepNested.find?_shape {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) (hwf : m.WF)
    {name ci} (hf : m'.find? name = some ci) :
    m.find? name = some ci ∨
    (((∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)) ∧
      ci.name = name ∧ ci.safety = .safe) :=
  let ⟨_, _, _, _, _, _, hadd⟩ := h; hadd.find?_shape hwf hf

/-- The premises a flipped `TrEnv'.induct` consumes. -/
theorem InductStepNested.induct_premises {m m' venv venv' lp np types numNested}
    (h : InductStepNested m m' venv venv' lp np types numNested) :
    ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore),
      D.WF venv ∧ AddInductStagesR m venv D K R m' venv' :=
  let ⟨D, K, R, _, _, hwf, hadd⟩ := h; ⟨D, K, R, hwf, hadd⟩

/-! ## 5. The re-run, at the block that produced the refutation

`inductive Box (A : Type) | mk : A → Box A` then `inductive T | mk : Box T → T`.  The second
is nested: elaboration introduces `_nested.Box_1` and the final environment carries the
auxiliary recursor as `T.rec_1`.  The block literals and the build-time checks are moved here
verbatim from `Verify/Inductive/AddDeclWF.lean` §4. -/

/-- `∀ (A : Type), A → Box A` -/
def boxMkTypeE : Expr :=
  .forallE `A (.sort 1) (.forallE `a (.bvar 0) (.app (.const `Box []) (.bvar 1)) .default)
    .default

/-- `inductive Box (A : Type) : Type where | mk : A → Box A` -/
def boxIndType : InductiveType :=
  { name := `Box, type := .forallE `A (.sort 1) (.sort 1) .default,
    ctors := [{ name := `Box.mk, type := boxMkTypeE }] }

/-- `Box T → T` -/
def tMkTypeE : Expr :=
  .forallE `b (.app (.const `Box []) (.const `T [])) (.const `T []) .default

/-- `inductive T : Type where | mk : Box T → T` — a **nested** block: `Box T` is a nested
occurrence, so elaboration introduces an auxiliary type `_nested.Box_1` and, with it, an
auxiliary recursor that the final environment carries under the name `T.rec_1`. -/
def tIndType : InductiveType :=
  { name := `T, type := .sort 1, ctors := [{ name := `T.mk, type := tMkTypeE }] }

def boxDecl : Declaration := .inductDecl [] 1 [boxIndType] false
def tDecl : Declaration := .inductDecl [] 0 [tIndType] false

/-- `T.rec_1` is not a name the `T` block declares. -/
theorem trec1_not_declared : (`T.rec_1 : Name) ∉ indDeclNames [tIndType] := by
  simp [indDeclNames, tIndType, Lean.mkRecName]

/-- **The nested block refutes the flipped `AddInduct`.**  No `VInductDecl'` translating the
`T` block stands in `AddInductStages` between a map without `T.rec_1` and one with it — and
check B below verifies by evaluation that those are exactly the maps the checker produces.

So the flip of `docs/handoff-addinduct.md` §6, even carried out in full, does **not** make
`addDecl.WF`'s `inductDecl` branch true for a nested declaration.

**This theorem is unchanged and still true.**  What changed is that `AddInductStages` is no
longer the intended definition of `AddInduct`: the repair is `AddInductStagesR` (§1), whose
recursor stage runs over `recConstsR R` and therefore *does* declare `T.rec_1`.  The
nested-aware counterpart of this theorem is `TrIndDeclN.not_addInductStagesR`, and
`trec1_mem_indDeclNamesN` shows its side condition fails here — the wall is gone.  The
negative controls that follow show it is gone only for the auxiliary family. -/
theorem tBlock_not_addInductStages {env env₂ : VEnv} {D : VInductDecl'} {m₁ m₂ : ConstMap}
    (h : TrIndDecl env [] 0 [tIndType] false D) (hwf : m₁.WF)
    (h₁ : m₁.find? `T.rec_1 = none) (h₂ : m₂.find? `T.rec_1 ≠ none) :
    ¬ AddInductStages m₁ env D m₂ env₂ :=
  h.not_addInductStages hwf h₁ h₂ trec1_not_declared

/- **Check B** (test, not a proof).  The nested block `T` adds `T.rec_1` — a recursor whose
name is `mkRecName` of no type the block declares — so `tBlock_not_addInductStages`'s premises
are met by the checker's own output. -/
#eval show Lean.CoreM Unit from do
  let e0 := Kernel.Environment.empty `main
  let .ok e1 := Lean4Lean.addDecl e0 boxDecl (check := true)
    | throwError "check B: the checker rejected the Box block"
  let .ok e2 := Lean4Lean.addDecl e1 tDecl (check := true)
    | throwError "check B: the checker rejected the nested T block"
  unless (e1.constants.find? `T.rec_1).isNone do
    throwError "check B: T.rec_1 was already present before the T block"
  unless (e2.constants.find? `T.rec_1).isSome do
    throwError "check B: the nested block did NOT add T.rec_1 -- the finding has regressed"
  let some (.inductInfo v) := e2.constants.find? `T | throwError "check B: T missing"
  unless v.numNested = 1 do throwError "check B: T is not nested"

/-! ### The re-run

`tBlock_not_addInductStages` above is unchanged and still true: it is a statement about
`AddInductStages`, which this file does not touch.  What it no longer refutes is
`AddInduct`, because `AddInductStages` is no longer the intended definition of `AddInduct`.

The nested-aware refutation `TrIndDeclN.not_addInductStagesR` has one side condition,
`n ∉ indDeclNamesN types numNested`, and at `n := T.rec_1`, `types := [tIndType]`,
`numNested := 1` that condition is **false**.  So the theorem is inapplicable to the block:
the wall is gone, and gone for the stated reason rather than by weakening the relation. -/

/-- **The wall is gone.**  `T.rec_1` *is* a name the nested `T` block accounts for, at
`numNested = 1`. -/
theorem trec1_mem_indDeclNamesN : (`T.rec_1 : Name) ∈ indDeclNamesN [tIndType] 1 := by decide

/-- **Negative control 1.**  At `numNested = 0` — a block with no auxiliary nested type —
`T.rec_1` is still outside the accounted names, so `not_addInductStagesR` still refutes.  The
repair is therefore *gated on `numNested`*, not a blanket permission. -/
theorem trec1_not_mem_indDeclNamesN_zero : (`T.rec_1 : Name) ∉ indDeclNamesN [tIndType] 0 := by
  decide

/-- **Negative control 2.**  A *second* auxiliary recursor is still refuted at
`numNested = 1`. -/
theorem trec2_not_mem_indDeclNamesN : (`T.rec_2 : Name) ∉ indDeclNamesN [tIndType] 1 := by
  decide

/-- The auxiliary recursor names of the `T` block, computed: `T.rec_1`, `T.rec_2`, ….  This
is `mkAuxRecNameMap`'s output read back as an equation. -/
theorem auxRecName_tIndType (k : Nat) :
    auxRecName [tIndType] k = .str `T ("rec" ++ "_" ++ toString (k + 1)) := rfl

/-- **Negative control 3.**  An unrelated constant is refuted at every `numNested`: the
relation still pins the map outside the block, and the auxiliary family does not leak. -/
theorem foo_not_mem_indDeclNamesN (n : Nat) : (`Foo : Name) ∉ indDeclNamesN [tIndType] n := by
  simp only [indDeclNamesN, indDeclNames, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_range, not_or]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro ⟨a, ha, h⟩; simp only [List.mem_singleton] at ha; subst ha; simp [tIndType] at h
  · rintro ⟨a, ha, b, hb, h⟩; simp only [List.mem_singleton] at ha; subst ha
    simp [tIndType] at hb; subst hb; simp at h
  · rintro ⟨a, ha, h⟩; simp only [List.mem_singleton] at ha; subst ha
    simp [tIndType, Lean.mkRecName] at h
  · rintro ⟨a, -, h⟩; rw [auxRecName_tIndType] at h; simp at h

/-- **The nested block is no longer refuted, stated as one theorem.**  Every hypothesis of
`TrIndDeclN.not_addInductStagesR` except the name condition is available for the `T` block —
and the name condition is `False`.  So there is no derivation of `¬ AddInductStagesR` from
this route, in contrast with `tBlock_not_addInductStages`. -/
theorem tBlock_not_refuted_at_trec1
    {env env₂ : VEnv} {Us : List Name} {np : Nat} {D : VInductDecl'} {K : List Name}
    {R : VIndRestore} {m₁ m₂ : ConstMap}
    (h : TrIndDeclN env Us np [tIndType] false 1 D K R) (hwf : m₁.WF)
    (h₁ : m₁.find? `T.rec_1 = none) (h₂ : m₂.find? `T.rec_1 ≠ none) :
    ¬ ((`T.rec_1 : Name) ∉ indDeclNamesN [tIndType] 1) :=
  fun hn => hn trec1_mem_indDeclNamesN

/- **Check C** (test, not a proof).  **The invariant is exact at a real nested block.**  The
set of constants the checker's nested path adds for `T` is *precisely*
`indDeclNamesN [tIndType] 1` — no more (which is what `find?_of_not_mem` asserts) and no less
(which is what makes the name list a definition rather than a permissive over-approximation).

This is the [EV] half of §2's invariant, and its negative control is check C', which checks
that `indDeclNamesN [tIndType] 0` — the pre-repair list — is *not* the added set. -/
#eval show Lean.CoreM Unit from do
  let e0 := Kernel.Environment.empty `main
  let .ok e1 := Lean4Lean.addDecl e0 boxDecl (check := true)
    | throwError "check C: the checker rejected the Box block"
  let .ok e2 := Lean4Lean.addDecl e1 tDecl (check := true)
    | throwError "check C: the checker rejected the nested T block"
  let before := e1.constants.toList.map (·.1)
  let after := e2.constants.toList.map (·.1)
  let added := after.filter (!before.contains ·)
  let expected := indDeclNamesN [tIndType] 1
  for n in added do
    unless expected.contains n do
      throwError "check C: the T block added {n}, which indDeclNamesN does not account for"
  for n in expected do
    unless added.contains n do
      throwError "check C: indDeclNamesN lists {n}, which the T block does not add"
  -- check C': the pre-repair name list is strictly smaller, so C is not vacuous
  let expected0 := indDeclNamesN [tIndType] 0
  if added.all (expected0.contains ·) then
    throwError "check C': indDeclNames already accounted for every added name -- \
      the nested finding has regressed"

/- **Check D** (test, not a proof).  The *shapes* the invariant predicts, at the same nested
block: `T` carries an `.inductInfo`, `T.mk` a `.ctorInfo`, and **both** `T.rec` and `T.rec_1`
a `.recInfo`, all with `isUnsafe = false`.  That is `AddInductStagesR.find?_shape` together
with the safety gate of `Verify/Inductive/AddDeclWF.lean` §1, checked against the checker at a
block with an auxiliary recursor. -/
#eval show Lean.CoreM Unit from do
  let e0 := Kernel.Environment.empty `main
  let .ok e1 := Lean4Lean.addDecl e0 boxDecl (check := true)
    | throwError "check D: the checker rejected the Box block"
  let .ok e2 := Lean4Lean.addDecl e1 tDecl (check := true)
    | throwError "check D: the checker rejected the nested T block"
  let some (.inductInfo vi) := e2.constants.find? `T | throwError "check D: T is not inductInfo"
  unless vi.isUnsafe = false do throwError "check D: T is unsafe"
  let some (.ctorInfo vc) := e2.constants.find? `T.mk | throwError "check D: T.mk is not ctorInfo"
  unless vc.isUnsafe = false do throwError "check D: T.mk is unsafe"
  for n in [`T.rec, `T.rec_1] do
    let some (.recInfo vr) := e2.constants.find? n
      | throwError "check D: {n} is not a recInfo"
    unless vr.isUnsafe = false do throwError "check D: {n} is unsafe"
    unless vr.all = [`T] do
      throwError "check D: {n}.all = {vr.all}, expected [T] (the block's own types)"

/-! ## 6. The witness: `AddInductStagesR` fires at a real nested block

`Theory/Inductive/NestedBuild.lean` §6 builds the auxiliary block for

```
inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α
inductive NFn          | node : PFn NFn → NFn
```

as `nfnAux`/`nfnK`/`nfnRestore`, proves `nfnAux_WF` (in *any* environment), and checks its
recursor types against Lean's own kernel: `nfnAux.recTypeR nfnRestore 0 = type_of% @NFn.rec`
and `… 1 = type_of% @NFn.rec_1`, both by `rfl`.  What it does not have is the constant-map
side.  This section supplies it, so that all three conjuncts of `InductStepNested` meet at one
block — the shape the companion refutation
(`Theory/Inductive/Companion.lean`'s `fooComp_inconsistent`) demands and a vacuous witness
would not achieve.

`exprOf%` below is the `Expr`-side counterpart of `Theory/Meta.lean`'s
`vconst(type_of% …)`: it splices the constant's **stored type, as Lean's kernel holds it**,
into the statement.  So `tr_recType0` is literally "the kernel's `NFn.rec` type translates to
the abstract block's `recTypeR`", not a hand transcription that could drift. -/

/-! `exprOf% c` splices `c`'s stored type into a term as a closed `Expr` literal — the
`Expr`-side counterpart of `vconst(type_of% …)`. -/
open Lean Elab Term in
elab "exprOf% " n:ident : term => do
  let n ← realizeGlobalConstNoOverload n
  let ci ← getConstInfo n
  return Lean.toExpr ci.type

/-- `TrExprS` by structure, the `tr_tac` of `Verify/QuotConsts.lean` under a name that does
not clash with it (this module and that one are both imported by
`Verify/Inductive/AddDeclWF.lean`). -/
syntax "trS_tac" : tactic
macro_rules | `(tactic| trS_tac) => `(tactic|
  first
  | exact TrExprS.sort rfl
  | exact TrExprS.bvar rfl
  | exact TrExprS.const (by assumption) rfl rfl
  | refine TrExprS.forallE ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ <;>
      [skip; type_tac; skip; type_tac; trS_tac; trS_tac]
  | refine TrExprS.app (A := ?_) (B := ?_) ?_ ?_ ?_ ?_ <;>
      [skip; skip; type_tac; type_tac; trS_tac; trS_tac]
)

namespace NestedWit
open InductiveDeclExamples

/-- The three constant lists the step folds over.  Read them: **one** type constant (the
companion `_nested.PFn_1` is not declared), **one** constructor constant (the companion's
`_nested.PFn_1.mk` is not declared either), and **two** recursors — the second of which is
the renamed auxiliary one, `NFn.rec_1`.  That is the whole finding of
`Verify/Inductive/AddDeclWF.lean` §2, now accommodated. -/
example : nfnAux.typeConstsC nfnK = [(``NFn, ⟨0, .sort (.succ .zero)⟩)] := rfl
example : nfnAux.ctorConstsCR nfnRestore nfnK
    = [(``NFn.node, ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)] := rfl
example : nfnAux.recConstsR nfnRestore nfnK
    = [(``NFn.rec, ⟨1, nfnAux.recTypeR nfnRestore 0⟩),
       (``NFn.rec_1, ⟨1, nfnAux.recTypeR nfnRestore 1⟩)] := rfl

/-- The user's declaration, syntactically: `inductive NFn | node : PFn NFn → NFn`. -/
def nfnIndType : InductiveType :=
  { name := ``NFn, type := exprOf% NFn,
    ctors := [{ name := ``NFn.node, type := exprOf% NFn.node }] }

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
  (hPFnMk : env.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩)
  (hNFn : env.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩)
  (hNode : env.constants ``NFn.node = some ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)

include hPFn hNFn in
/-- Lean's stored type for `NFn.node` translates to the abstract restored constructor type. -/
theorem tr_nodeType : TrExprS env [] [] (exprOf% NFn.node)
    (nfnNode.typeR nfnAux nfnRestore 0) := by
  show TrExprS env [] [] _ (vconst(type_of% @NFn.node)).type
  trS_tac

include hPFn hPFnMk hNFn hNode in
/-- **Lean's stored type for `NFn.rec` translates to `recTypeR … 0`.** -/
theorem tr_recType0 : TrExprS env [`u] [] (exprOf% NFn.rec)
    (nfnAux.recTypeR nfnRestore 0) := by
  show TrExprS env [`u] [] _ (vconst(type_of% @NFn.rec)).type
  trS_tac

include hPFn hPFnMk hNFn hNode in
/-- **…and for the *renamed auxiliary* recursor `NFn.rec_1` to `recTypeR … 1`.**  This is the
constant that refuted `AddInductStages`. -/
theorem tr_recType1 : TrExprS env [`u] [] (exprOf% NFn.rec_1)
    (nfnAux.recTypeR nfnRestore 1) := by
  show TrExprS env [`u] [] _ (vconst(type_of% @NFn.rec_1)).type
  trS_tac

end

def nfnInd : InductiveVal where
  name := ``NFn; levelParams := []; type := exprOf% NFn
  numParams := 0; numIndices := 0; all := [``NFn]; ctors := [``NFn.node]
  numNested := 1; isRec := true; isUnsafe := false; isReflexive := false

def nfnNodeCI : ConstructorVal where
  name := ``NFn.node; levelParams := []; type := exprOf% NFn.node
  induct := ``NFn; cidx := 0; numParams := 0; numFields := 1; isUnsafe := false

/-- **The strengthened type-stage shape at the nested witness.**  `NFn` is the block's member
`0`; its one declared constructor is `NFn.node`, and the renaming `nfnRestore.ctorName` is the
identity on it (it moves only `_nested.PFn_1.mk`).  The `isRec` clause is discharged the other
way round from `R10.Wit`: `nfnInd.isRec = true`, and the implication is one-directional
precisely so that a genuinely recursive block carries no obligation here. -/
theorem indShapeOf_nfnInd : IndShapeOf nfnAux nfnRestore.ctorName (.inductInfo nfnInd) := by
  refine ⟨nfnInd, rfl, ⟨_, List.mem_cons_self, rfl⟩, fun T hT hn => ?_⟩
  -- the block has two members; `_nested.PFn_1` is not named `NFn`, so the ∀ bites only at `NFn`
  have hts : nfnAux.types
      = [{ name := ``NFn, type := .sort (.succ .zero), indices := [], ctors := [nfnNode] },
         { name := `_nested.PFn_1, type := .sort (.succ .zero), indices := [],
           ctors := [pfnAuxMk] }] := rfl
  rw [hts] at hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact ⟨nfnInd, rfl, rfl, rfl, rfl, by decide, fun h => absurd h (by decide)⟩
  · exact absurd hn (by decide)

/-- …and the strengthened constructor-stage shape.  `nfnRestore.tyName 0 = ``NFn`, so the
`induct` field of the declared constructor is pinned to the member it belongs to even though
the block is nested and the restoration is not the identity. -/
theorem ctorShapeOf_nfnNodeCI :
    CtorShapeOf nfnAux nfnRestore.ctorName nfnRestore.tyName (.ctorInfo nfnNodeCI) := by
  have hcs : nfnAux.ctorsAll = [(0, nfnNode), (1, pfnAuxMk)] := rfl
  refine ⟨nfnNodeCI, rfl, ⟨(0, nfnNode), by rw [hcs]; exact List.mem_cons_self, by decide⟩,
    fun jC hjC hn => ?_⟩
  rw [hcs] at hjC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjC
  rcases hjC with rfl | rfl
  · exact ⟨nfnNodeCI, rfl, by decide, by decide, rfl, rfl⟩
  · exact absurd hn (by decide)

def nfnRecCI : RecursorVal where
  name := ``NFn.rec; levelParams := [`u]; type := exprOf% NFn.rec
  all := [``NFn]; numParams := 0; numIndices := 0; numMotives := 2; numMinors := 2
  rules := []; k := false; isUnsafe := false

def nfnRec1CI : RecursorVal where
  name := ``NFn.rec_1; levelParams := [`u]; type := exprOf% NFn.rec_1
  all := [``NFn]; numParams := 0; numIndices := 0; numMotives := 2; numMinors := 2
  rules := []; k := false; isUnsafe := false

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
  (hPFnMk : env.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩)

include hPFn in
/-- **The syntactic half at the nested witness.**  Note `recName_aux`: the auxiliary member's
recursor is named `auxRecName [nfnIndType] 0`, i.e. `mkAuxRecNameMap`'s `NFn.rec_1`, which is
exactly what `nfnRestore.recName` produces. -/
theorem trIndDeclN_wit : TrIndDeclN env [] 0 [nfnIndType] false 1 nfnAux nfnK nfnRestore where
  safe := rfl
  uvars := rfl
  np := rfl
  length := rfl
  companions := by
    rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  trType := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; exact ⟨rfl, .sort rfl⟩
    · simp at ht
  trCtorsLen := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  trCtors := by
    rintro env₁ hst (_ | j) t T ht hT (_ | q) c C hc hC
    · cases ht; cases hT; cases hc; cases hC
      have hle : env ≤ env₁ := VEnv.addConstList_le hst
      refine ⟨rfl, tr_nodeType (hle.constants hPFn) ?_⟩
      exact VEnv.addConstList_constants hst (``NFn, ⟨0, .sort (.succ .zero)⟩)
        (by exact List.Mem.head _)
    · cases ht; cases hT; simp [nfnIndType] at hc
    · simp at ht
    · simp at ht
  ctorName_own := by
    rintro (_ | j) t T ht hT (_ | q) c C hc hC
    · cases ht; cases hT; cases hc; cases hC; rfl
    · cases ht; cases hT; simp [nfnIndType] at hc
    · simp at ht
    · simp at ht
  recName_own := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  recName_aux := by
    rintro (_ | _ | j) T hT hle
    · simp at hle
    · cases hT; rfl
    · simp [nfnAux] at hT

end

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
  (hPFnMk : env.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩)
  (hfresh : ∀ n ∈ [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1], env.constants n = none)
  (hfreshAux : env.constants `_nested.PFn_1 = none)

include hPFn hPFnMk hfresh in
/-- **`AddInductStagesR` fires at a nested block, and it declares the renamed auxiliary
recursor.**  Four stages' worth of constants land in the map — `NFn`, `NFn.node`, `NFn.rec`
and `NFn.rec_1` — and the companion member `_nested.PFn_1` and its constructor land nowhere,
which is what `typeConstsC`/`ctorConstsCR` filter out.

`NFn.rec_1` is the constant that refutes `AddInductStages` (`AddDeclWF.lean` §2). -/
theorem addInductStagesR_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', AddInductStagesR m env nfnAux nfnK nfnRestore m' env' ∧
      m'.find? ``NFn.rec_1 = some (.recInfo nfnRec1CI) ∧
      m'.find? ``NFn.rec = some (.recInfo nfnRecCI) ∧
      m'.find? `_nested.PFn_1 = none ∧
      (∃ ci, env'.constants ``NFn.rec_1 = some ci) := by
  have f0 := hfresh ``NFn (by simp)
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := env) (name := ``NFn)
    (ci := ⟨0, .sort (.succ .zero)⟩) f0
  have c1 := VEnv.addConst_constants_eq he1
  have hNFn1 : e1.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  have hPFn1 : e1.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c1]; simp [hPFn]
  have hPFnMk1 : e1.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c1]; simp [hPFnMk]
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := ``NFn.node)
    (ci := ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩) (by rw [c1]; simp [hfresh ``NFn.node])
  have c2 := VEnv.addConst_constants_eq he2
  have hNFn2 : e2.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c2]; simp [hNFn1]
  have hPFn2 : e2.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c2]; simp [hPFn1]
  have hPFnMk2 : e2.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c2]; simp [hPFnMk1]
  have hNode2 : e2.constants ``NFn.node = some ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩ := by
    rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := ``NFn.rec)
    (ci := ⟨1, nfnAux.recTypeR nfnRestore 0⟩)
    (by rw [c2, c1]; simp [hfresh ``NFn.rec])
  have c3 := VEnv.addConst_constants_eq he3
  have hNFn3 : e3.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c3]; simp [hNFn2]
  have hPFn3 : e3.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c3]; simp [hPFn2]
  have hPFnMk3 : e3.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c3]; simp [hPFnMk2]
  have hNode3 : e3.constants ``NFn.node = some ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩ := by
    rw [c3]; simp [hNode2]
  obtain ⟨e4, he4⟩ := VEnv.addConst_eq_none (env := e3) (name := ``NFn.rec_1)
    (ci := ⟨1, nfnAux.recTypeR nfnRestore 1⟩)
    (by rw [c3, c2, c1]; simp [hfresh ``NFn.rec_1])
  -- the map side
  have w1 := hwf.insert ``NFn (.inductInfo nfnInd) (hfr _)
  have f2 : (m.insert ``NFn (.inductInfo nfnInd)).find? ``NFn.node = none := by
    rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert ``NFn.node (.ctorInfo nfnNodeCI) f2
  have f3 : ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node
      (.ctorInfo nfnNodeCI)).find? ``NFn.rec = none := by
    rw [w1.find?_insert, hwf.find?_insert]; simp [hfr]
  have w3 := w2.insert ``NFn.rec (.recInfo nfnRecCI) f3
  have f4 : (((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node
      (.ctorInfo nfnNodeCI)).insert ``NFn.rec (.recInfo nfnRecCI)).find? ``NFn.rec_1 = none := by
    rw [w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp [hfr]
  have w4 := w3.insert ``NFn.rec_1 (.recInfo nfnRec1CI) f4
  have s1 : AddIndConsts (IndShapeOf nfnAux nfnRestore.ctorName) (nfnAux.typeConstsC nfnK)
      m env (m.insert ``NFn (.inductInfo nfnInd)) e1 :=
    .cons (ci := .inductInfo nfnInd) rfl indShapeOf_nfnInd ⟨by decide, rfl, .sort rfl⟩
      (hfr _) he1 .nil
  have s2 : AddIndConsts (CtorShapeOf nfnAux nfnRestore.ctorName nfnRestore.tyName)
      (nfnAux.ctorConstsCR nfnRestore nfnK)
      (m.insert ``NFn (.inductInfo nfnInd)) e1
      ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)) e2 :=
    .cons (ci := .ctorInfo nfnNodeCI) rfl ctorShapeOf_nfnNodeCI
      ⟨by decide, rfl, tr_nodeType hPFn1 hNFn1⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) (nfnAux.recConstsR nfnRestore nfnK)
      ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)) e2
      ((((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)).insert
        ``NFn.rec (.recInfo nfnRecCI)).insert ``NFn.rec_1 (.recInfo nfnRec1CI)) e4 :=
    .cons (ci := .recInfo nfnRecCI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_recType0 hPFn2 hPFnMk2 hNFn2 hNode2⟩ f3 he3 <|
    .cons (ci := .recInfo nfnRec1CI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_recType1 hPFn3 hPFnMk3 hNFn3 hNode3⟩ f4 he4 .nil
  refine ⟨_, _, ⟨_, _, _, _, e4, s1, s2, s3, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [w3.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp [hfr]
  · exact ⟨_, by rw [VEnv.addIndRulesR, VEnv.addDefEqList_constants]
                 exact VEnv.addConst_self he4⟩

include hPFn hPFnMk hfresh hfreshAux in
/-- **`InductStepNested` has a model, at a nested block.**  All three conjuncts at once:
the syntactic translation (`trIndDeclN_wit`), the declaration's well-formedness
(`NestedBuild.lean`'s `nfnAux_WF`, whose `binders_indep` clause is discharged by the
substitution theorem rather than by emptiness), and the constant-map step
(`addInductStagesR_wit`), which declares `NFn.rec_1`.

This is the joint non-vacuity the companion refutation demands: the two premises of a
flipped `TrEnv'.induct` do not excuse each other here, because `AddInductStagesR` itself
supplies the `addIndTypesC` success that `WF`'s constructor clause is staged over. -/
theorem inductStepNested_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', InductStepNested m m' env env' [] 0 [nfnIndType] 1 ∧
      m'.find? ``NFn.rec_1 = some (.recInfo nfnRec1CI) := by
  obtain ⟨m', env', H, hrec1, -, -, -⟩ := addInductStagesR_wit hPFn hPFnMk hfresh hwf hfr
  refine ⟨m', env', ⟨nfnAux, nfnK, nfnRestore, trIndDeclN_wit hPFn, ?_, nfnAux_WF, H⟩,
    hrec1⟩
  refine VEnv.addConstList_eq_some_iff.2 ⟨?_, ?_⟩
  · rintro n hn
    simp only [nfnAux, VInductDecl'.typeConsts, List.map_map, List.map_cons, List.map_nil,
      Function.comp, List.mem_cons, List.not_mem_nil, or_false] at hn
    obtain rfl | rfl := hn
    exacts [hfresh _ (by simp), hfreshAux]
  · decide

end

/-! ### …at a closed environment

Everything above is stated at any `env` holding `PFn`/`PFn.mk` and fresh at the block's
names.  The declaration history supplies one: `env₂` with
`VEnv.empty.addInduct' pfnDecl = some env₂`, i.e. the environment in which `PFn` has just
been declared.  This is the closed instance. -/

theorem inductStepNested_wit_closed {env₂ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂)
    {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', InductStepNested m m' env₂ env' [] 0 [nfnIndType] 1 ∧
      m'.find? ``NFn.rec_1 = some (.recInfo nfnRec1CI) := by
  refine inductStepNested_wit (VEnv.addInduct'_types h (List.Mem.head _))
    (VEnv.addInduct'_ctors h (List.Mem.head _)) (fun n hn => nfn_fresh h n hn) ?_ hwf hfr
  rw [VEnv.addInduct'_constants_of_not_mem h (by decide)]; rfl

end NestedWit

end Lean4Lean
