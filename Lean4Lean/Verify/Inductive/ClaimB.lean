import Lean4Lean.Verify.Inductive.SurfaceMap
import Lean4Lean.Verify.Inductive.FlipWiring
import Lean4Lean.Theory.Inductive.RestoreOpWit
import Lean4Lean.Theory.Inductive.MemberRedex

/-!
# Claim B: the surface map composed with a real supplier, and what `recArg` costs

Two things, and the second one is a **negative** result that closes a question rather than
opening one.

## §1 (B5) The composition: `OracleSound` gets its first producer

`Lean4Lean.OracleSound` (`Verify/Inductive/SurfaceMap.lean`) had **five consumers and no
producer** when this file was written (`scripts/shape.lean`, `HEADS="OracleSound"`: five hits,
all taking it as a hypothesis; `HEADS="OracleSound ConstLookup"`: nothing).  So every arm of the
surface map that needs the oracle — `trType`, `trCtors`, and the supplier-neutral
`CtorStoresTr` — was conditional on a premise nothing in the tree discharged.

This file discharges it, from `Lean4Lean.ctorTr?`.

**The supplier choice here is forced, not a preference**, and that is worth recording because
the alternative was proposed twice.  `OracleSound` quantifies over a **pure function**
`tr : Expr → Option VExpr`.  `ctorTr?` is one.  `Lean4Lean.TypeChecker.checkType.WF` is a
*monadic postcondition with an existential at a `VContext`* —
`M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'` — so it cannot instantiate
`OracleSound` at all without first extracting a pure function from a monadic run.  The fragment
route also happens to be the clean one: `ctorTr?`'s cone is 0-hole and touches none of the
watched names, where the checker route's cone carries eight holes and both
`VEnv.IsDefEq.uniq`/`uniqU`.

Note what the producer does **not** need.  `OracleSound` is *soundness only* —
`∀ e e', tr e = some e' → TrExprS env Us [] e e'` — with no totality clause, so no completeness
lemma for the fragment is required, and `Lean4Lean.CtorsInFragment` stays where it is (it is
what the `↔` forms need, not what the arms need).

## §2 (B7) `VIndField.recArg`: a tension in `Theory/Inductive/Decl.lean`, resolved by measurement

`Decl.lean` says two things that look incompatible with `Lean4Lean.VIndRestore.recog`:

* L963-967: `VIndField.recArg` is "unrecoverable from the declaration";
* L1044's table attributes it to the **checker**, `checkPositivity`/`isRecArg`.

while `recog` *reads a `VIndRecArg` off a field type* and takes no surface data — its docstring
says "nothing about `D` enters".

**They are consistent, and the reconciling word is `whnf`.**  `recog` is a purely syntactic
matcher; `isRecArg` classifies a field by reducing it.  §2 exhibits the separation at a block the
kernel *accepts*: `Lean4Lean.ROWit`'s `roT`, whose single field's stored type is the β-redex
`(fun x : Type => roT) Prop`.  There `recArg = some roRec` and `recog` returns `none`
(`recog_roRedex_none`), while on the canonical form of the very same `recArg` it returns it back
on the nose (`recog_roCanon`).  So:

* `recog` is **sound** (`VIndRestore.recog_sound`) and that is all it claims;
* `recog` is **incomplete, and provably so** — not by omission but by necessity, since
  `VIndField.WF.pos`'s `some` branch ties `F.type` to `r.canonType D i` by `IsDefEqType` only;
* therefore `Decl.lean`'s two claims stand as written, and B7 closes as *"the recogniser exists,
  is sound, and cannot be completed; `recArg` stays existential in the translation relation"*.

The residual is stated exactly, and it is small: `recog` closes `recArg` for every block whose
recursive fields are stored **syntactically** canonical, which is every block in this repo's
example set (§2.3).  What it cannot do is close it for blocks in `roT`'s class, and no
`whnf`-free function can.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 B5 — the oracle, supplied

### §1.1 The supplier as a pure function -/

/-- **The oracle.**  `ctorTr?` returns the translation *and its type*; `OracleSound` wants a
`Expr → Option VExpr`, so the type component is dropped.  Kept as a `def` rather than inlined so
that the arms below read as "the map, at *this* supplier" and so that `#print axioms` has a name
to report. -/
def ctorOracle (Γc : Name → Option VConstant) (Us : List Name) : Expr → Option VExpr :=
  fun e => (ctorTr? Γc Us e []).map (·.1)

/-- **B5, the producer.**  `OracleSound`'s first and (at the time of writing) only producer: the
premise five theorems in `SurfaceMap.lean` assume is discharged by `trExprS_of_ctorTr`, whose own
hypothesis is a `ConstLookup` — a leaf lookup table, no `HasType`, no `VEnv.WF`. -/
theorem oracleSound_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) : OracleSound (ctorOracle Γc Us) env Us := by
  intro e e' h
  obtain ⟨⟨e₁, t'⟩, htr, rfl⟩ := Option.map_eq_some_iff.1 h
  exact trExprS_of_ctorTr hΓc htr

/-- The empty table needs no environment at all (`constLookup_none`), so the oracle is sound at
**every** environment on the sort-telescope fragment. -/
theorem oracleSound_none {env : VEnv} {Us : List Name} :
    OracleSound (ctorOracle (fun _ => none) Us) env Us :=
  oracleSound_of_ctorTr constLookup_none

/-- The staged form the `trCtors` arm actually asks for: sound at every *staged* environment,
from a `ConstLookup` at every staged environment.  This is the shape
`Lean4Lean.constLookup_staged_of_split` produces. -/
theorem oracleSound_staged_of_ctorTr {env : VEnv} {Us K : List Name} {D : VInductDecl'}
    {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁) :
    ∀ env₁, env.addIndTypesC D K = some env₁ → OracleSound (ctorOracle Γc Us) env₁ Us :=
  fun env₁ hst => oracleSound_of_ctorTr (hΓc env₁ hst)

/-! ### §1.2 The map's arms, at a real supplier

Each of these is a `SurfaceMap.lean` theorem with its `OracleSound` hypothesis *gone*, replaced
by a `ConstLookup`.  Nothing is re-proved: the content is the composition. -/

/-- **`TrIndDeclN.trType` at the map's output, unconditionally on the oracle.** -/
theorem trType_surfInductDecl?_ctorTr {env : VEnv} {Γc : Name → Option VConstant}
    {Us : List Name} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? (ctorOracle Γc Us) uvars ps lvl isLE rtypes = some D)
    (hΓc : ConstLookup Γc env) :
    ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T → TrIndType env Us t T :=
  trType_surfInductDecl? h (oracleSound_of_ctorTr hΓc)

/-- **The supplier-neutral premise `CtorStoresTr`, at the map's output.**  This is the arm worth
the most: `SurfaceMap.lean`'s own `trCtors` arm is *derived from* `CtorStoresTr`
(`trCtors_of_ctorStoresTr`), so discharging the neutral form discharges the field and leaves the
statement free of any inferencer's name. -/
theorem ctorStoresTr_surfInductDecl?_ctorTr {env : VEnv} {Γc : Name → Option VConstant}
    {Us : List Name} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? (ctorOracle Γc Us) uvars ps lvl isLE rtypes = some D)
    (hΓc : ConstLookup Γc env) : CtorStoresTr env Us rtypes D D.idRestore :=
  ctorStoresTr_surfInductDecl? h (oracleSound_of_ctorTr hΓc)

/-- **`TrIndDeclN.trCtors` at the map's output**, with the field's own staging. -/
theorem trCtors_surfInductDecl?_ctorTr {env : VEnv} {Γc : Name → Option VConstant}
    {Us K : List Name} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? (ctorOracle Γc Us) uvars ps lvl isLE rtypes = some D)
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D D.idRestore j c C :=
  trCtors_surfInductDecl? h (oracleSound_staged_of_ctorTr hΓc)

/-- **All three at once, at the map's output.**  The three arms `SurfaceMap.lean` leaves
conditional, discharged together from one `ConstLookup` per staged environment plus one at the
base environment.  `trCtorsLen` and `ctorName_own` are not here because they never needed the
oracle. -/
theorem surfInductDecl?_arms_ctorTr {env : VEnv} {Γc : Name → Option VConstant}
    {Us K : List Name} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? (ctorOracle Γc Us) uvars ps lvl isLE rtypes = some D)
    (hΓc : ConstLookup Γc env)
    (hst : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁) :
    (∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T → TrIndType env Us t T) ∧
    CtorStoresTr env Us rtypes D D.idRestore ∧
    (∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D D.idRestore j c C) :=
  ⟨trType_surfInductDecl?_ctorTr h hΓc,
   ctorStoresTr_surfInductDecl?_ctorTr h hΓc,
   trCtors_surfInductDecl?_ctorTr h hst⟩

/-! ### §1.3 The neutral primitive, straight from the supplier

`ctorStoresTr_surfInductDecl?_ctorTr` above routes through the map, so it only speaks at
`D.idRestore`.  This one does not go through the map at all, so `R` stays arbitrary — which is
what makes it usable at the *real* restoration (§3) and not only at the identity. -/

/-- **`CtorStoresTr` at an arbitrary restoration, from `ctorTr?`.**  No `surfInductDecl?`: the
per-constructor data is a computation against whatever `D` and `R` are supplied. -/
theorem ctorStoresTr_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {rtypes : List InductiveType} {D : VInductDecl'} {R : VIndRestore}
    (hΓc : ConstLookup Γc env)
    (h : ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')) :
    CtorStoresTr env Us rtypes D R := by
  intro j t T ht hT q c C hc hC
  obtain ⟨hn, t', htr⟩ := h j t T ht hT q c C hc hC
  exact ⟨hn, C.typeR D R j, trExprS_of_ctorTr hΓc htr, rfl⟩

/-- …and it is not merely *an* existential: on the fragment the witness is pinned.  `ctorTr?`'s
terms are `.proj`-free (`isUnique_of_ctorTr`), so `ctorStoresTr_rigid` applies and the stored type
**is** the translation. -/
theorem ctorStoresTr_of_ctorTr_rigid {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {rtypes : List InductiveType} {D : VInductDecl'} {R : VIndRestore}
    (hΓc : ConstLookup Γc env)
    (hcs : CtorStoresTr env Us rtypes D R)
    {j : Nat} {t : InductiveType} {T : VIndType} (ht : rtypes[j]? = some t)
    (hT : D.types[j]? = some T) {q : Nat} {c : Constructor} {C : VIndCtor}
    (hc : t.ctors[q]? = some c) (hC : T.ctors[q]? = some C)
    {ct t' : VExpr} (hfrag : ctorTr? Γc Us c.type [] = some (ct, t')) :
    C.typeR D R j = ct :=
  ctorStoresTr_rigid hcs ht hT hc hC (isUnique_of_ctorTr hfrag) (trExprS_of_ctorTr hΓc hfrag)

/-! ## §2 B7 — `VIndField.recArg`, recovered by a two-stage reader

### §2.0 The tension, and its resolution

`Theory/Inductive/Decl.lean` says `VIndField.recArg` is "unrecoverable from the declaration"
(L963-967) and attributes it to the checker's `checkPositivity`/`isRecArg` (L1044 table), while
`Lean4Lean.VIndRestore.recog` reads a `VIndRecArg` off a field type with no surface data at all.

**Both are correct, and the reconciling word is `whnf`.**  `recog` is a *purely syntactic*
matcher — it takes `(splitPis S.piArity S).2.spineFn` and demands it be
`.const (R.tyName k) (R.tyLvls k)` — whereas `AddInductive.isRecArg` classifies a field by
*reducing* it.  Where the two disagree, `recog` says `none` and the kernel says `some`, and the
disagreement is not hypothetical: `Lean4Lean.ROWit`'s block

```lean
inductive roT : Type where | mk : ((fun x : Type => roT) Prop) → roT
```

is **accepted** by `AddInductive.run`, `Environment.addInductive` and `Lean4Lean.addDecl`
(`Theory/Inductive/RestoreOpWit.lean`, executed), with the field's type stored as the β-redex
verbatim and `recArg = some roRec`.  §2.1-§2.2 exhibit `recog` failing there and succeeding on the
canonical form of the very same `recArg`.

That is the *single-stage* answer, and it is not the current state of the tree.
`Lean4Lean.MRedex.recog_none_of_lamHead` (`Theory/Inductive/MemberRedex.lean`) already states the
negative half in general, and the repair has already landed: `Lean4Lean.VNestedOcc.field`
(`Theory/Inductive/NestedBuild.lean`) is a **two-stage** reader, `recog` and then `recog` after one
head-β step.  `Verify/Inductive/MemberRedexScan.lean` §2 measured it on the running environment —
47 safe blocks with a nested-shaped field, 790 auxiliary constructor fields, 3 misclassified by
stage 1, **3 of 3 fixed by stage 2, 0 residual**.

§2.3 puts that two-stage reader in the *declaration* setting, which is where B7 asks the question
(`VNestedOcc.field` lives in the construction setting and builds a whole `VIndField` from a
*source* field).  So B7's answer is:

* `recArg` is recovered from `(D, i, F.type)` alone by `VInductDecl'.recArgOf` below;
* it is **sound up to one head-β step** (`recArgOf_sound`), which is inside the slack
  `VIndField.WF.pos` allows (its `some` branch ties `F.type` to `r.canonType D i` by
  `IsDefEqType`, not by equality);
* it is **complete on the entire measured population** (790/790), and at `roDecl`
  (`recArgOf_roRedex`), the block where the single-stage reader fails;
* the residue is **named, not measured away**: a redex under a binder, or one needing δ.  Those
  need `isRecArg`'s full loop, and that is exactly what `Decl.lean` L1044 attributes to the
  checker.

So `Decl.lean`'s two claims stand as written for a single-stage read, and the sharp restatement is
**"recoverable up to the `whnf` gap"** — with the gap now one head-β step wide on everything
measured.

### §2.1 `recog` fires on the canonical form and returns the stored data verbatim -/

/-- **The positive half.**  On the canonical form, `recog` recovers `recArg` **exactly**, so the
recogniser is not vacuous: on a syntactically canonical block `recArg` genuinely *is* a function
of the declaration. -/
theorem recog_roCanon :
    ROWit.roDecl.idRestore.recog ROWit.roDecl.nm 0 (ROWit.roRec.canonType ROWit.roDecl 0)
      = some ROWit.roRec := rfl

/-! ### §2.2 …and returns `none` on the type the kernel actually stores -/

/-- **The negative half.**  The field's stored type is the redex, `recog` returns `none`, and the
true `recArg` is `some roRec`.  An instance of `MRedex.recog_none_of_lamHead`, kept as a closed
computation so that the claim is anchored on the stored form rather than on a `vconst` equation
(`MemberRedex.lean` records that `vconst(type_of% ·)` β-reduces and is blind in exactly this
corner). -/
theorem recog_roRedex_none :
    ROWit.roDecl.idRestore.recog ROWit.roDecl.nm 0 ROWit.roField.type = none := rfl

/-- …and the same fact from the general lemma, so the witness is visibly an *instance* rather than
an independent claim. -/
theorem recog_roRedex_none' :
    ROWit.roDecl.idRestore.recog ROWit.roDecl.nm 0 ROWit.roField.type = none :=
  MRedex.recog_none_of_lamHead (A := .sort (.succ .zero)) (b := .const ROWit.roName []) rfl

/-- **Single-stage recovery is incomplete**, stated as such: a block, a field, and a `VIndRecArg`
with the field's `recArg` set to it, whose canonical form `recog` recognises and whose *stored*
type it does not, the two differing by one β step.  `ROWit.ro_pos_beta` supplies the `IsDefEqType`
that `VIndField.WF.pos` asks for at this very block, so the field is well formed and the reader is
still wrong. -/
theorem recog_incomplete :
    ∃ (D : VInductDecl') (F : VIndField) (r : VIndRecArg),
      F.recArg = some r ∧
      D.idRestore.recog D.nm 0 (r.canonType D 0) = some r ∧
      D.idRestore.recog D.nm 0 F.type = none ∧
      F.type ≠ r.canonType D 0 :=
  ⟨ROWit.roDecl, ROWit.roField, ROWit.roRec, rfl, recog_roCanon, recog_roRedex_none, by decide⟩

/-! ### §2.3 The two-stage reader, in the declaration setting

`VNestedOcc.field`'s two stages, lifted off the nested-occurrence construction and stated as what
B7 actually asks for: a function of the declaration and a stored field type. -/

/-- **`recArg`, read off the declaration.**  Stage 1 is `recog`; stage 2 is `recog` after one head
β-contraction.  Nothing but `D` and `S` enters. -/
def VInductDecl'.recArgOf (D : VInductDecl') (i : Nat) (S : VExpr) : Option VIndRecArg :=
  (D.idRestore.recog D.nm i S).orElse fun _ =>
    D.idRestore.recog D.nm i (VExpr.betaHead S)

/-- **Soundness, with the head-β step visible in the conclusion.**  Either the reader's answer
restores to the stored type on the nose, or it restores to its head β-contraction — and the second
disjunct is inside `VIndField.WF.pos`'s `IsDefEqType` slack, which is why it is admissible at all.
Stating the disjunction rather than hiding it behind a defeq is the point: the reader is *not*
sound up to arbitrary conversion, only up to one head β step. -/
theorem recArgOf_sound {D : VInductDecl'} {i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : D.recArgOf i S = some r) :
    r.canonTypeR D D.idRestore i = S ∨
      r.canonTypeR D D.idRestore i = VExpr.betaHead S := by
  rw [VInductDecl'.recArgOf] at h
  cases h1 : D.idRestore.recog D.nm i S with
  | some r' => rw [h1] at h; cases h; exact .inl (VIndRestore.recog_sound h1 D)
  | none =>
    rw [h1, Option.orElse] at h
    exact .inr (VIndRestore.recog_sound h D)

/-- The recognised member is a member of the block, whichever stage answered. -/
theorem recArgOf_idx_lt {D : VInductDecl'} {i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : D.recArgOf i S = some r) : r.idx < D.nm := by
  rw [VInductDecl'.recArgOf] at h
  cases h1 : D.idRestore.recog D.nm i S with
  | some r' => rw [h1] at h; cases h; exact VIndRestore.recog_idx_lt h1
  | none => rw [h1, Option.orElse] at h; exact VIndRestore.recog_idx_lt h

/-- **B7's headline.**  At `roDecl` — the block where the single-stage reader is wrong
(`recog_roRedex_none`) and where the kernel stores the redex verbatim — the two-stage reader
returns the stored `recArg` **on the nose**. -/
theorem recArgOf_roRedex :
    ROWit.roDecl.recArgOf 0 ROWit.roField.type = ROWit.roField.recArg := rfl

/-- …and it agrees with the single-stage reader wherever that one already fired, so nothing is
reclassified: the two-stage reader is conservative. -/
theorem recArgOf_eq_recog_of_some {D : VInductDecl'} {i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : D.idRestore.recog D.nm i S = some r) : D.recArgOf i S = some r := by
  rw [VInductDecl'.recArgOf, h]; rfl

/-- The class the reader closes without any β step at all: a field stored syntactically canonical
at a member the recogniser reaches first.  Every recursive field of every example block in this
repo is in it (`Theory/Inductive/NestedHead.lean`'s field data is syntactically canonical), and
`roT` is the counterexample class — one head-β step wide. -/
theorem recArgOf_eq_recArg {D : VInductDecl'} {F : VIndField} {r : VIndRecArg} {i : Nat}
    (hr : F.recArg = some r) (hrec : D.idRestore.recog D.nm i F.type = some r) :
    D.recArgOf i F.type = F.recArg := by
  rw [recArgOf_eq_recog_of_some hrec, hr]

/-! ## §3 B6 — the real restoration: exactly what remains

The name side is done: `Lean4Lean.skelPrefix_of_surfInductDecl?_run` chains with
`Lean4Lean.runSkelExtends` by `rfl`.  What remains is **one thing**, and §2 identifies it.

`VIndField.typeR F D R i` is `F.type` when `F.recArg = none` and `R.restore D i F.type` when it is
`some _` (`Theory/Inductive/Restore.lean`).  The surface map sets `recArg := none` at **every**
field (`SurfaceMap.lean:145`).  Therefore at the map's output
`C.fieldTypesR D R = C.fields.map (·.type)` for **every** `R`: the restoration is a no-op on the
entire field telescope, and the only `R`-dependence left in
`C.typeR D R j = mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)` is
the **result head**.

So the map's output cannot match a user constructor type at the real restoration no matter which
restoration is supplied — `NTree.node`'s field is `List (NTree α)` and the map's is
`_nested.List_1 α`, and no `R` moves it while `recArg = none`.  **B6 is blocked on populating
`recArg`, and that is the only blocker.**

The concrete remaining obligation, in three parts:

1. **Populate `recArg` in the map.**  `VInductDecl'.recArgOf` (§2.3) is the function to use:
   replace `recArg := none` by `recArg := D.recArgOf i A` at field `A`, index `i`.  §2.3 shows it
   is sound up to one head-β step and complete at `roDecl`; on the map's own output the second
   stage is never needed, because the map's field types are segments of `ctorTr?`'s output and
   `ctorTr?` has no `.lam` case at all (`TrExprSGeneral.lean`: `| fvar | mvar | lam | letE | lit |
   proj => none`), so every field type it produces is `.lam`-free at the spine head and stage 1
   answers.  **That last step is stated, not proved here** — it is the one new lemma part 1 needs,
   and it is a structural induction over `ctorTr?`, not a defeq argument.
   Note the ordering constraint this creates: `recArgOf` needs `D`, and `D` is what the map is
   building, so the map must be restructured to compute the field telescope first and the `recArg`s
   second — a two-pass `surfIndCtor?`.  That is the concrete shape of part 1.
2. **Re-prove the collapse.**  `typeR_surfIndCtor?` (`SurfaceMap.lean`) currently gets
   `C.fieldTypesR = C.fields.map (·.type)` for free from `recArg = none`.  With `recArg` populated
   it needs `VIndRestore.restore_noK` at each recursive field instead — the machinery exists
   (`Theory/Inductive/Restore.lean`'s `restore_canonType`, `typeR_eq_canonTypeR_of_canon`), and
   this is a rewrite chain, not a new induction.
3. **`ctorStoresTr_of_ctorTr` (§1.3) is already stated at arbitrary `R`**, so the `trCtors` arm
   does *not* need re-proving for part 1 — that was the point of not routing it through the map.

Part 1 is the whole of B6's remaining risk; parts 2 and 3 are bookkeeping against existing
lemmas.  Nothing above is claimed to be proved.
-/

/-! ## §4 Axioms

Every declaration in this file, individually.  `propext`/`Quot.sound`/`Classical.choice` are the
whitelist; anything else, and in particular `sorryAx`, is a failure. -/

#print axioms Lean4Lean.ctorOracle
#print axioms Lean4Lean.oracleSound_of_ctorTr
#print axioms Lean4Lean.oracleSound_none
#print axioms Lean4Lean.oracleSound_staged_of_ctorTr
#print axioms Lean4Lean.trType_surfInductDecl?_ctorTr
#print axioms Lean4Lean.ctorStoresTr_surfInductDecl?_ctorTr
#print axioms Lean4Lean.trCtors_surfInductDecl?_ctorTr
#print axioms Lean4Lean.surfInductDecl?_arms_ctorTr
#print axioms Lean4Lean.ctorStoresTr_of_ctorTr
#print axioms Lean4Lean.ctorStoresTr_of_ctorTr_rigid
#print axioms Lean4Lean.recog_roCanon
#print axioms Lean4Lean.recog_roRedex_none
#print axioms Lean4Lean.recog_roRedex_none'
#print axioms Lean4Lean.recog_incomplete
#print axioms Lean4Lean.VInductDecl'.recArgOf
#print axioms Lean4Lean.recArgOf_sound
#print axioms Lean4Lean.recArgOf_idx_lt
#print axioms Lean4Lean.recArgOf_roRedex
#print axioms Lean4Lean.recArgOf_eq_recog_of_some
#print axioms Lean4Lean.recArgOf_eq_recArg

end Lean4Lean
