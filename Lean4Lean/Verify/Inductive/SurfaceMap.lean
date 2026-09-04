import Lean4Lean.Verify.Inductive.CtorsLenGeneral

/-!
# The surface→abstract construction: `List InductiveType → Option VInductDecl'`

`Verify/Inductive/CtorsLenGeneral.lean` reduced `TrIndDeclN.trCtorsLen` to one `List` equation,
`SkelPrefix types D := ∃ tail, D.nameSkelV = surfNameSkel types ++ tail`, proved the reduction is
an *equivalence*, and proved (§3 there, `trCtorsLen_not_of_sansLen`) that the field is
**independent of the other eleven**, so the missing lemma is necessarily outside the relation.
It named what is missing: a construction taking the *post-nested-elimination* member list to a
`VInductDecl'`.  This file builds it.

## What the construction is, and why it has an oracle parameter

`ElimNestedInductive.Result.types` is a `List InductiveType`; the map is stated at that type, so
it is more general than the field and needs no import of `Lean4Lean.Inductive.Add`.

A *total* `List InductiveType → VInductDecl'` cannot exist: the abstract side is a `VExpr`, the
surface side a `Lean.Expr`, and `TrExprS`'s application constructor carries two typing premises,
so no purely syntactic total function lands in the relation.  The type-translation half is
already solved by `Verify/Inductive/TrExprSGeneral.lean`'s `ctorTr?`, a **type inferencer** whose
whole environment hypothesis is a lookup table and which *produces* typing as an output of its
induction.  So the construction here is parameterised by a translation oracle
`tr : Expr → Option VExpr` and requires **no typing at all**; the typing enters exactly once, as
`OracleSound tr env Us := ∀ e e', tr e = some e' → TrExprS env Us [] e e'`, which is
`Lean4Lean.trExprS_of_ctorTr`'s conclusion verbatim.  Instantiating
`tr := fun e => (ctorTr? Γc Us e []).map (·.1)` one module downstream discharges it.

**Why the oracle is a parameter and not `ctorTr?` itself.**  Measured, not assumed
(`docs/handoff-surfacemap.md` M5): `ctorTr?`'s module has a 197-module import closure that
contains `Verify/Inductive/NestedRestoreWit.lean`, `Verify/Inductive/AddDeclWF.lean`,
`Verify/Inductive/ValAtParam.lean` and `Verify/Inductive/NestedRunInvariant.lean` — four modules
holding hand-built instances — because `TrExprSGeneral` sits on `ExprConstructionScope`, which
imports `ValAtParam`.  `ctorTr?` is therefore *unreachable under structural exclusion*.  Making
the oracle a parameter keeps this file's closure at the 147 modules of `CtorsLenGeneral` and
moves the `ctorTr?` instantiation to a consumer, where it is one rewrite.

## What is built

* §1 two total decompositions with round-trip equations: `VExpr.peelPis` (strip every leading
  `forallE`) and `VExpr.spine` (strip an application spine).  Both are inverses of
  `VExpr.mkPi` / `VExpr.mkApp` on the nose, unconditionally.
* §2 the map: `surfIndCtor?`, `surfIndType?`, `surfInductDecl?`.  A constructor's abstract record
  is read off its translated type: the first `np` binders are `C.params`, the rest are
  `C.fields`, and the target's spine, after the `bvars` that name the parameters, is `C.args`.
  Every check is decidable, so the map **computes** (§6 is `rfl`).
* §3 **the skeleton equation** `D.nameSkelV = surfNameSkel rtypes`, which is `SkelPrefix` with
  `tail = []`, hence strictly stronger.  `surfNameSkel` and `nameSkelV` read nothing but
  `VIndType.name` and `VIndCtor.name`, so this half is *independent of the oracle's output*: it
  holds on every success, with no typing.
* §4 **the reassembly equation** `C.typeR D D.idRestore j = ct`: what the map produces is,
  at the identity restoration, the very expression the oracle returned.  This is the input
  `trIndCtorR_iff_of_ctorTr` asks for.
* §5 the three fields the construction owed — `trCtorsLen` (through `trCtorsLen_of_skelPrefix`,
  not re-proved), `trType`, `trCtors` — plus `ctorName_own` and `trType`'s name half, free.
* §6 the arity-0 witness at `InductiveDeclExamples.ntreeAux`, with two negative controls.

## The restoration is the identity here, and that is a boundary, not an oversight

The map's domain is the **post-elimination** member list, whose auxiliary member is still called
`_nested.List_1`.  Against that list the abstract block needs no restoration, so §4/§5 are stated
at `D.idRestore`.  Relating the **user's original** block to the same `D` needs the real
restoration (`ntreeRestore` at `ntreeAux`), and that is a different obligation, listed under
Claim B in `docs/handoff-surfacemap.md`.  Composing the two is exactly what
`ElimNestedInductive.runSkelExtends` does on the name side: `surfNameSkel` is
`ElimNestedInductive.nameSkel`'s body verbatim, so §3 chains with it by `rfl` (§5.5).

## Structural exclusions

This file imports **exactly one** module, `Lean4Lean.Verify.Inductive.CtorsLenGeneral`; the
closure is **148** modules (`CtorsLenGeneral`'s 147 plus this file).  Measured, not asserted:
**32 modules in the tree mention `TrIndDeclN`, `TrIndCtorR` or `TrIndType`, and this closure
contains 3 of them** — `Verify.Environment.Induct` (declares `TrIndDecl`),
`Verify.Environment.InductR` (declares `TrIndDeclN`/`TrIndType`/`TrIndCtorR` and the `exprOf%`
elaborator) and `Verify.Inductive.CtorsLenGeneral` (declares `SkelPrefix` and the reduction §5
uses).  All three are unavoidable: the statements are about their contents.  The other **28 are
excluded**, among them every module holding a hand-built instance:
`Verify.Inductive.NestedRestoreWit` (`trIndDeclN_wit'` at the degenerate `nfnAux`),
`Verify.Inductive.AddDeclWF` (`R10.Wit.trIndDecl_wit`), `Verify.Inductive.StagesFiring`,
`Verify.Inductive.CtorPointwise`, `Verify.Inductive.TrIndDeclNProducer` (the *`ntreeAux`*
hand-built `trType`/`trCtors` witnesses — §6's own block),
`Verify.Inductive.TrExprSGeneral`, `Verify.Inductive.FlipWiring`,
`Verify.Inductive.FragmentWiden`, `Verify.Inductive.FlipConstruct` (`tr_ntreeType`,
`tr_ntreeNodeType`), `Verify.Inductive.TrTypeProducer`, `Verify.Inductive.TrSpineProducer`,
`Verify.Inductive.TrIndDeclNCtorOwn`, `Verify.Inductive.ValAtParam`,
`Verify.Inductive.NestedRunInvariant`, `Verify.Inductive.NestedRestore`,
`Verify.Inductive.RestoreFaithful`, `Verify.Inductive.RunIdentity`,
`Verify.Inductive.SpineClause`.
**Disclosed as not droppable**: the three above, plus `Theory.Inductive.NestedHead`, which
declares `ntreeAux` and `NTree` — §6 is *about* them — and
`Theory.Typing.PatternDecode` / `Theory.Typing.PatWFIota`, which supply §1's decompositions.
`Verify.Environment.Induct` carries one hand-built `TrIndDecl` at the `Eq` block: a different
relation and a different block from §6's.

Because `ValAtParam` is excluded, §6 restates `NTree`'s own stored type with the same `exprOf%`
splice `ntreeIndType` uses; the auxiliary member's types are written out, since
`_nested.List_1` is a name Lean never declares.
-/

set_option autoImplicit false

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The two decompositions were already in the tree

`VExpr.peelPis` (strip every leading `forallE`) and `VExpr.spine` (strip an application spine)
are `Theory/Typing/PatternDecode.lean`'s, and their round-trip equations are
`VExpr.mkPi_peelPis` (`Theory/Typing/PatWFIota.lean`) and `VExpr.mkApp_spine`.  All four are
citable at this file's position (`scripts/can-cite.py`), so §1 is *nothing* — measured, after
first writing it and being told by the elaborator that both definitions already existed. -/

/-! ## §2 The map -/

/-- **A constructor's abstract record, read off its translated type.**

`tr c.type` is a `VExpr`; strip its binders, take the first `np` as the constructor's own
parameter telescope and the rest as its fields, and require the target to be the block member
`self` at the block's own levels, applied to the parameters (`bvars`) followed by the index
arguments.  Those trailing arguments are `C.args`.

`recArg` is `none` at every field and `lvl` is the block's universe.  Neither is read by any
field of `TrIndDeclN`: `VIndField.typeR` at `D.idRestore` is `F.type` for *both* branches
(`VIndField.typeR_id`, unconditional), and `lvl` appears only in `VIndField.WF`.  Detecting
recursive positions is `AddInductive.isRecArg`'s job and belongs to `VInductDecl'.WF`, not to the
translation relation. -/
def surfIndCtor? (tr : Expr → Option VExpr) (uvars np : Nat) (fl : VLevel) (self : Name)
    (c : Constructor) : Option VIndCtor :=
  (tr c.type).bind fun ct =>
    if np ≤ (VExpr.peelPis ct).1.length ∧
       (VExpr.spine (VExpr.peelPis ct).2).1 = .const self (VLevel.params uvars) ∧
       (VExpr.spine (VExpr.peelPis ct).2).2.take np
         = VExpr.bvars ((VExpr.peelPis ct).1.length - np) np then
      some { name := c.name
             params := (VExpr.peelPis ct).1.take np
             fields := ((VExpr.peelPis ct).1.drop np).map
               fun A => { type := A, lvl := fl, recArg := none }
             args := (VExpr.spine (VExpr.peelPis ct).2).2.drop np }
    else none

/-- **The map at a constructor, inverted once.**  Every later fact about `surfIndCtor?` reads
this and nothing else, so the definition's shape is asserted in exactly one place. -/
theorem surfIndCtor?_eq_some {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {self : Name} {c : Constructor} {C : VIndCtor}
    (h : surfIndCtor? tr uvars np fl self c = some C) :
    ∃ ct, tr c.type = some ct ∧
      np ≤ (VExpr.peelPis ct).1.length ∧
      (VExpr.spine (VExpr.peelPis ct).2).1 = .const self (VLevel.params uvars) ∧
      (VExpr.spine (VExpr.peelPis ct).2).2.take np
        = VExpr.bvars ((VExpr.peelPis ct).1.length - np) np ∧
      C = { name := c.name
            params := (VExpr.peelPis ct).1.take np
            fields := ((VExpr.peelPis ct).1.drop np).map
              fun A => { type := A, lvl := fl, recArg := none }
            args := (VExpr.spine (VExpr.peelPis ct).2).2.drop np } := by
  rw [surfIndCtor?, Option.bind_eq_some_iff] at h
  obtain ⟨ct, hct, h⟩ := h
  refine ⟨ct, hct, ?_⟩
  split at h
  · next hg => exact ⟨hg.1, hg.2.1, hg.2.2, (Option.some.inj h).symm⟩
  · exact absurd h nofun

/-- **A member's abstract record.**  `type` is the oracle's output on the *stored* type, verbatim
— `TrIndType` compares exactly that.  `indices` is `[]`: no field of `TrIndDeclN` reads it
(`TrIndType` is `t.name = T.name ∧ TrExprS env Us [] t.type T.type`), and the index telescope is
recovered by `VIndType.WF`, which is not this relation. -/
def surfIndType? (tr : Expr → Option VExpr) (uvars np : Nat) (fl : VLevel)
    (t : InductiveType) : Option VIndType := do
  let T ← tr t.type
  let cs ← t.ctors.mapM (surfIndCtor? tr uvars np fl t.name)
  return { name := t.name, type := T, indices := [], ctors := cs }

/-- **THE CONSTRUCTION.**  The four data the relation leaves free — `uvars`, the parameter
telescope, the block universe and `isLE` — are inputs, because `TrIndDeclN` constrains only
`Us.length = D.uvars`, `nparams = D.np` and `isUnsafe = false`; nothing in it pins `D.params`,
`D.lvl` or `D.isLE`. -/
def surfInductDecl? (tr : Expr → Option VExpr) (uvars : Nat) (ps : List VExpr) (lvl : VLevel)
    (isLE : Bool) (rtypes : List InductiveType) : Option VInductDecl' := do
  let Ts ← rtypes.mapM (surfIndType? tr uvars ps.length lvl)
  return { uvars := uvars, params := ps, lvl := lvl, types := Ts, isLE := isLE }

/-! ### The pieces of the definition, extracted once -/

/-- A produced constructor keeps the surface name. -/
theorem surfIndCtor?_name {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel} {self : Name}
    {c : Constructor} {C : VIndCtor} (h : surfIndCtor? tr uvars np fl self c = some C) :
    C.name = c.name := by
  obtain ⟨_, _, _, _, _, rfl⟩ := surfIndCtor?_eq_some h; rfl

/-- A produced member keeps the surface name. -/
theorem surfIndType?_name {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {t : InductiveType} {T : VIndType} (h : surfIndType? tr uvars np fl t = some T) :
    T.name = t.name := by
  simp only [surfIndType?, Option.bind_eq_some_iff, bind] at h
  obtain ⟨_, _, _, _, h⟩ := h
  cases h; rfl

/-- A produced member's stored type **is** the oracle's output. -/
theorem surfIndType?_type {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {t : InductiveType} {T : VIndType} (h : surfIndType? tr uvars np fl t = some T) :
    tr t.type = some T.type := by
  simp only [surfIndType?, Option.bind_eq_some_iff, bind] at h
  obtain ⟨A, hA, _, _, h⟩ := h
  cases h; exact hA

/-- A produced member's constructor list is the surface list, mapped. -/
theorem surfIndType?_ctors {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {t : InductiveType} {T : VIndType} (h : surfIndType? tr uvars np fl t = some T) :
    t.ctors.mapM (surfIndCtor? tr uvars np fl t.name) = some T.ctors := by
  simp only [surfIndType?, Option.bind_eq_some_iff, bind] at h
  obtain ⟨_, _, cs, hcs, h⟩ := h
  cases h; exact hcs

/-- The block's member list is the surface list, mapped. -/
theorem surfInductDecl?_types {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) :
    rtypes.mapM (surfIndType? tr uvars ps.length lvl) = some D.types := by
  simp only [surfInductDecl?, Option.bind_eq_some_iff, bind] at h
  obtain ⟨Ts, hTs, h⟩ := h
  cases h; exact hTs

/-- …and the other four block data are the inputs. -/
theorem surfInductDecl?_data {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) :
    D.uvars = uvars ∧ D.params = ps ∧ D.lvl = lvl ∧ D.isLE = isLE := by
  simp only [surfInductDecl?, Option.bind_eq_some_iff, bind] at h
  obtain ⟨_, _, h⟩ := h
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §3 The skeleton equation

The headline.  `surfNameSkel` and `VInductDecl'.nameSkelV` read nothing but `VIndType.name` and
`VIndCtor.name`, so this is provable from the two name lemmas alone: **no typing, no oracle
soundness, and no property of `tr` whatever**. -/

/-- A `Forall₂` transported to a `map` equation, once, so §3 costs no bookkeeping. -/
private theorem forall₂_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} {P : α → β → Prop}
    (hfg : ∀ a b, P a b → g b = f a) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ P l l' → l'.map g = l.map f := by
  intro l l' h
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons]; rw [hfg _ _ hab, ih]

/-- A `Forall₂` at one index. -/
private theorem forall₂_getElem? {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ P l l' →
      ∀ (j : Nat) (a : α) (b : β), l[j]? = some a → l'[j]? = some b → P a b := by
  intro l l' h
  induction h with
  | nil => intro j a b ha; simp at ha
  | cons hab _ ih =>
    intro j a b ha hb
    match j with
    | 0 => cases ha; cases hb; exact hab
    | j+1 => exact ih j a b (by simpa using ha) (by simpa using hb)

/-- `mapM` transported to a `map` equation. -/
private theorem map_eq_map_of_mapM {α β γ : Type} {f : α → Option β} {g : β → γ} {g' : α → γ}
    (hg : ∀ a b, f a = some b → g b = g' a) {l : List α} {l' : List β}
    (h : l.mapM f = some l') : l'.map g = l.map g' :=
  forall₂_map_eq hg (List.mapM_eq_some.1 h)

/-- `mapM` at one index. -/
private theorem mapM_getElem? {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (j : Nat) (a : α) (b : β)
    (ha : l[j]? = some a) (hb : l'[j]? = some b) : f a = some b :=
  forall₂_getElem? (List.mapM_eq_some.1 h) j a b ha hb

/-- …and `mapM` preserves length. -/
private theorem mapM_length {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : l'.length = l.length :=
  (List.Forall₂.length_eq (List.mapM_eq_some.1 h)).symm

/-- A produced member's constructor **names** are the surface names. -/
theorem surfIndType?_ctorNames {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {t : InductiveType} {T : VIndType} (h : surfIndType? tr uvars np fl t = some T) :
    T.ctors.map (·.name) = t.ctors.map (·.name) :=
  map_eq_map_of_mapM (fun _ _ hc => surfIndCtor?_name hc) (surfIndType?_ctors h)

/-- **THE SKELETON EQUATION.**  Not `SkelPrefix` with an unknown tail: an equation, so the
construction's output has *exactly* the surface block's name skeleton. -/
theorem nameSkelV_surfInductDecl? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) :
    D.nameSkelV = surfNameSkel rtypes := by
  rw [VInductDecl'.nameSkelV, surfNameSkel]
  refine map_eq_map_of_mapM (fun t T hT => ?_) (surfInductDecl?_types h)
  rw [surfIndType?_name hT, surfIndType?_ctorNames hT]

/-- …hence `SkelPrefix`, with the empty tail. -/
theorem skelPrefix_surfInductDecl? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) : SkelPrefix rtypes D :=
  ⟨[], by rw [nameSkelV_surfInductDecl? h, List.append_nil]⟩

/-- The member count matches, so the length bound `skelPrefix_iff_trCtorsLen` wants is free. -/
theorem length_surfInductDecl? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) :
    D.types.length = rtypes.length :=
  mapM_length (surfInductDecl?_types h)

/-! ## §4 The reassembly equation

What the map produces is, at the identity restoration, the very expression the oracle returned.
This is what `Lean4Lean.trIndCtorR_iff_of_ctorTr` asks a `VIndCtor` for, and it is the whole
content of the constructor half of the construction. -/

/-- **THE REASSEMBLY EQUATION.**  `VIndCtor.typeR` is `mkPi (C.params ++ C.fieldTypesR D R)
(D.tyAppR R j C.fields.length C.args)`; at `D.idRestore` `fieldTypesR` is `fields.map (·.type)`
(`VIndCtor.fieldTypesR_id`, unconditional) and `tyAppR` is `tyApp` (`tyAppR_id`), and the map's
three guards are exactly what makes the three pieces reassemble to `ct`.

The three hypotheses on `D` are what `surfInductDecl?` provides: `uvars` and `np` are the
inputs, and `hself` is the member's own name — supplied by `surfIndType?`, which passes `t.name`
to `surfIndCtor?` as `self`. -/
theorem typeR_surfIndCtor? {tr : Expr → Option VExpr} {uvars np : Nat} {fl : VLevel}
    {self : Name} {c : Constructor} {C : VIndCtor} {ct : VExpr} {D : VInductDecl'} {j : Nat}
    (hu : D.uvars = uvars) (hnp : D.np = np)
    (hself : (D.types.getD j default).name = self) (hct : tr c.type = some ct)
    (h : surfIndCtor? tr uvars np fl self c = some C) :
    C.typeR D D.idRestore j = ct := by
  obtain ⟨ct', hct', _, hhd, hsp, rfl⟩ := surfIndCtor?_eq_some h
  cases Option.some.inj (hct'.symm.trans hct)
  rw [VIndCtor.typeR_id, VIndCtor.type, VIndCtor.canonResult, VInductDecl'.tyApp]
  -- the field telescope is the tail of the peeled telescope
  have hfields : (((VExpr.peelPis ct).1.drop np).map
      (fun A => ({ type := A, lvl := fl, recArg := none } : VIndField))).map (·.type)
      = (VExpr.peelPis ct).1.drop np := by
    rw [List.map_map]; exact List.map_id _
  have hlen : (((VExpr.peelPis ct).1.drop np).map
      (fun A => ({ type := A, lvl := fl, recArg := none } : VIndField))).length
      = (VExpr.peelPis ct).1.length - np := by
    rw [List.length_map, List.length_drop]
  dsimp only
  rw [hfields, hlen, hself, VInductDecl'.ownLvls, hu, hnp, ← hsp, ← hhd,
    List.take_append_drop, List.take_append_drop, VExpr.mkApp_spine, VExpr.mkPi_peelPis]

/-! ## §5 The three fields, and two more for free

`trCtorsLen` comes through `Lean4Lean.trCtorsLen_of_skelPrefix` — *not* re-proved here — and so
do `ctorName_own` and `trType`'s name half.  `trType` and `trCtors` are the two that need the
oracle, and they need it only through `OracleSound`. -/

/-- **The one typing input.**  `Lean4Lean.trExprS_of_ctorTr`'s conclusion verbatim: instantiate
`tr := fun e => (ctorTr? Γc Us e []).map (·.1)` and this is discharged by that theorem, whose own
hypothesis is a `ConstLookup` — a lookup table, no `HasType`, no `VEnv.WF`.  The construction
itself never mentions it; §3 and §4 hold without it. -/
def OracleSound (tr : Expr → Option VExpr) (env : VEnv) (Us : List Name) : Prop :=
  ∀ (e : Expr) (e' : VExpr), tr e = some e' → TrExprS env Us [] e e'

/-- **`TrIndDeclN.trCtorsLen`, at the construction's output.**  Through §2 of
`CtorsLenGeneral.lean`; nothing about `tr` is used. -/
theorem trCtorsLen_surfInductDecl? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) : TrCtorsLen rtypes D :=
  trCtorsLen_of_skelPrefix (skelPrefix_surfInductDecl? h)

/-- **`TrIndDeclN.ctorName_own`, likewise free.** -/
theorem ctorNameOwn_surfInductDecl? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) : CtorNameOwn rtypes D :=
  ctorNameOwn_of_skelPrefix (skelPrefix_surfInductDecl? h)

/-- **`TrIndDeclN.trType`.**  Both halves: the name from §3, the `TrExprS` from the oracle. -/
theorem trType_surfInductDecl? {env : VEnv} {Us : List Name} {tr : Expr → Option VExpr}
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D) (hO : OracleSound tr env Us) :
    ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T → TrIndType env Us t T := by
  intro j t T ht hT
  have hj := mapM_getElem? (surfInductDecl?_types h) j t T ht hT
  exact ⟨(surfIndType?_name hj).symm, hO _ _ (surfIndType?_type hj)⟩

/-- **`TrIndDeclN.trCtors`, at the identity restoration.**  The staging is the field's own:
quantified over `env.addIndTypesC D K = some env₁`, with the oracle sound at the *staged*
environment — which is exactly the shape `Lean4Lean.constLookup_staged_of_split` produces. -/
theorem trCtors_surfInductDecl? {env : VEnv} {Us : List Name} {K : List Name}
    {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D : VInductDecl'}
    (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D)
    (hO : ∀ env₁, env.addIndTypesC D K = some env₁ → OracleSound tr env₁ Us) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, rtypes[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D D.idRestore j c C := by
  intro env₁ hst j t T ht hT q c C hc hC
  have hj := mapM_getElem? (surfInductDecl?_types h) j t T ht hT
  have hq := mapM_getElem? (surfIndType?_ctors hj) q c C hc hC
  obtain ⟨ct, hct, _, _, _, _⟩ := surfIndCtor?_eq_some hq
  obtain ⟨hu, hps, _, _⟩ := surfInductDecl?_data h
  refine ⟨(surfIndCtor?_name hq).symm, ?_⟩
  rw [typeR_surfIndCtor? hu (by rw [VInductDecl'.np, hps])
    ((congrArg VIndType.name (VInductDecl'.getD_types hT)).trans (surfIndType?_name hj))
    hct hq]
  exact hO env₁ hst _ _ hct

/-! ### §5.5 Chaining to the user's block

`surfNameSkel` is `ElimNestedInductive.nameSkel`'s body verbatim, so `runSkelExtends`'s
conclusion `∃ tail, nameSkel r.types = nameSkel types ++ tail` **is** this lemma's hypothesis by
`rfl` — no bridge lemma, and `NestedRunInvariant` stays out of the closure. -/

/-- **The user's block inherits `SkelPrefix` from the construction's.**  So the three fields of
§5 hold at the *user's* member list too, which is the list `TrIndDeclN` quantifies over. -/
theorem skelPrefix_of_surfInductDecl?_run {tr : Expr → Option VExpr} {uvars : Nat}
    {ps : List VExpr} {lvl : VLevel} {isLE : Bool} {types rtypes : List InductiveType}
    {D : VInductDecl'} (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D)
    {tail : List (Name × List Name)} (hrun : surfNameSkel rtypes = surfNameSkel types ++ tail) :
    SkelPrefix types D :=
  ⟨tail, (nameSkelV_surfInductDecl? h).trans hrun⟩

/-- …hence `trCtorsLen` at the user's list, which is the field's own quantification. -/
theorem trCtorsLen_of_surfInductDecl?_run {tr : Expr → Option VExpr} {uvars : Nat}
    {ps : List VExpr} {lvl : VLevel} {isLE : Bool} {types rtypes : List InductiveType}
    {D : VInductDecl'} (h : surfInductDecl? tr uvars ps lvl isLE rtypes = some D)
    {tail : List (Name × List Name)} (hrun : surfNameSkel rtypes = surfNameSkel types ++ tail) :
    TrCtorsLen types D :=
  trCtorsLen_of_skelPrefix (skelPrefix_of_surfInductDecl?_run h hrun)

/-! ## §6 The arity-0 witness at `ntreeAux`

`InductiveDeclExamples.ntreeAux` (`Theory/Inductive/NestedHead.lean`) is the parameterised nested
block: `inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α` after nested
elimination, `uvars = 1`, `params = [Type u]`, two members, one companion.  It is **not**
`nfnAux`, whose `uvars = 0` and `params = []`.

`ntreeRTypes` is `ElimNestedInductive.run`'s output on that declaration, spelled as a
`List InductiveType`: the user's member with its constructor's type **rewritten** so the nested
`List (NTree α)` has become `_nested.List_1 α`, followed by the auxiliary member.  `NTree`'s own
stored type is `exprOf% NTree`, Lean's own; `_nested.List_1` is a name Lean never declares, so
its three types are written out.

The witness is reached through §3/§4/§5 — the only block-specific input is that the map
*succeeds*, which is one `rfl` — and not through a `rfl` on any field's text. -/

namespace InductiveDeclExamples

/-- **The oracle, at this block.**  This is `ctorTr?`'s *first component* with the environment
and the typing checks deleted.  It is restated rather than imported because `ctorTr?` is
unreachable under structural exclusion (module docstring); it is **not** sound on its own, and
nothing in §1–§5 mentions it — its only role is to make §6 a computation instead of a table of
hand-written `VExpr`s.  `OracleSound` at a real environment is `ctorTr?`'s job, one module
downstream. -/
def vtr? (Us : List Name) : Expr → Option VExpr
  | .sort u => (VLevel.ofLevel Us u).map .sort
  | .bvar i => some (.bvar i)
  | .const c us => (us.mapM (VLevel.ofLevel Us)).map (.const c)
  | .app f a => (vtr? Us f).bind fun f' => (vtr? Us a).map fun a' => .app f' a'
  | .forallE _ d b _ => (vtr? Us d).bind fun d' => (vtr? Us b).map fun b' => .forallE d' b'
  | .mdata _ e => vtr? Us e
  | _ => none

/-- `∀ (α : Type u), Type u` — the stored type of the auxiliary member. -/
def nlistTypeE : Expr :=
  .forallE `α (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default

/-- `∀ (α : Type u), α → _nested.List_1.{u} α → NTree.{u} α` — `NTree.node` **after** nested
elimination: the field Lean stores as `List (NTree α)` has become the auxiliary member. -/
def ntreeNodeRE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `as (.app (.const `_nested.List_1 [.param `u]) (.bvar 1))
        (.app (.const ``NTree [.param `u]) (.bvar 2)) .default) .default) .default

/-- `∀ (α : Type u), _nested.List_1.{u} α`. -/
def nlistNilE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.app (.const `_nested.List_1 [.param `u]) (.bvar 0)) .default

/-- `∀ (α : Type u), NTree.{u} α → _nested.List_1.{u} α → _nested.List_1.{u} α`.  Its **first**
field is recursive into `NTree` — the parameter position of `List` has become a recursive
position, which is the whole content of nested induction. -/
def nlistConsE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (.app (.const ``NTree [.param `u]) (.bvar 0))
      (.forallE `as (.app (.const `_nested.List_1 [.param `u]) (.bvar 1))
        (.app (.const `_nested.List_1 [.param `u]) (.bvar 2)) .default) .default) .default

/-- **`ElimNestedInductive.run`'s output**, as a `List InductiveType`: the user's member followed
by the one auxiliary member. -/
def ntreeRTypes : List InductiveType :=
  [{ name := ``NTree, type := exprOf% NTree,
     ctors := [{ name := ``NTree.node, type := ntreeNodeRE }] },
   { name := `_nested.List_1, type := nlistTypeE,
     ctors := [{ name := `_nested.List_1.nil, type := nlistNilE },
               { name := `_nested.List_1.cons, type := nlistConsE }] }]

/-- Erase every field's `recArg`.  `VIndField.typeR` at `D.idRestore` is `F.type` on *both*
branches (`VIndField.typeR_id`, unconditional) and `TrIndDeclN` never reads `recArg`, so this is
precisely the data the translation relation cannot see; `VInductDecl'.WF` is what sees it, and
recovering it is `AddInductive.isRecArg`'s job, not the map's. -/
def eraseRecArgs (D : VInductDecl') : VInductDecl' :=
  { D with types := D.types.map fun T =>
      { T with ctors := T.ctors.map fun C =>
        { C with fields := C.fields.map fun F => { F with recArg := none } } } }

/-- **The map reproduces `ntreeAux` on the nose, up to `recArg`.**  Not "some block with the
right names": every member name, stored type, `indices`, and every constructor's `name`,
`params`, `fields` (types *and* universes) and `args` agree with
`Theory/Inductive/NestedHead.lean`'s hand-written `ntreeAux` — the only difference is the
`recArg` tags, which no field of `TrIndDeclN` reads. -/
theorem ntreeRTypes_maps :
    surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some (eraseRecArgs ntreeAux) := rfl

/-- **Negative control 1 — the premise is not slack.**  Duplicate the surface constructor and the
skeleton equation fails, so §3's equation is doing work a `rfl` on the field's text would
otherwise do by accident. -/
def ntreeRTypesDbl : List InductiveType :=
  [{ (ntreeRTypes.headD default) with
      ctors := (ntreeRTypes.headD default).ctors ++ (ntreeRTypes.headD default).ctors }] ++
    ntreeRTypes.tail

theorem ntreeAux_not_nameSkelV_dbl : ntreeAux.nameSkelV ≠ surfNameSkel ntreeRTypesDbl := by
  intro h
  have h0 := congrArg (fun l => l[0]?) h
  simp only [VInductDecl'.nameSkelV, surfNameSkel, ntreeAux, ntreeRTypesDbl, ntreeRTypes,
    List.map_cons, List.map_nil, List.cons_append, List.getElem?_cons_zero] at h0
  exact absurd h0 (by decide)

/-- **Negative control 2 — the map itself refuses a wrong block.**  Rename the auxiliary member
but not the occurrences of it inside the constructor types: every name is still fresh and every
constructor type still translates, but `_nested.List_1.cons`'s target no longer heads at its own
member, so `surfIndCtor?`'s head guard fires and the construction returns `none`.  A map that
merely copied names would have succeeded here. -/
def ntreeRTypesRenamed : List InductiveType :=
  [ntreeRTypes.headD default,
   { (ntreeRTypes.tail.headD default) with name := `_nested.List_2 }]

theorem ntreeRTypesRenamed_fails :
    surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypesRenamed = none := rfl

/-- **THE WITNESS — arity 0.**  The three fields the surface→abstract construction owed, at the
parameterised nested block, reached through the map.

The only block-specific input is `ntreeRTypes_maps`, which is the *map succeeding*; §3 turns it
into the skeleton equation, §5 into the fields, and §4 into the constructor types.  `trType` and
`trCtors` are stated as the map's `TrIndType` / `TrIndCtorR` obligations against an arbitrary
environment and an arbitrary sound oracle — the typing is not assumed at a fixed environment, it
is quantified. -/
theorem ntreeAux_surfaceMap_witness :
    -- non-degeneracy: this is not `nfnAux`
    ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
    ntreeAux.types.length = 2 ∧ ntreeNode.fields.length = 2 ∧
    -- the map succeeds, and its output is `ntreeAux` up to `recArg`
    surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some (eraseRecArgs ntreeAux) ∧
    -- §3 at this block: THE SKELETON EQUATION, and it is `ntreeAux`'s own skeleton
    (eraseRecArgs ntreeAux).nameSkelV = surfNameSkel ntreeRTypes ∧
    ntreeAux.nameSkelV = surfNameSkel ntreeRTypes ∧
    -- §5 at this block: the three fields, plus `ctorName_own`
    SkelPrefix ntreeRTypes ntreeAux ∧
    TrCtorsLen ntreeRTypes ntreeAux ∧
    CtorNameOwn ntreeRTypes ntreeAux ∧
    (∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T → t.name = T.name) ∧
    (∀ (env : VEnv) (Us : List Name), OracleSound (vtr? [`u]) env Us →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t →
        (eraseRecArgs ntreeAux).types[j]? = some T → TrIndType env Us t T) ∧
    -- …and `trType` at `ntreeAux` itself: `TrIndType` reads only `T.name` and `T.type`, both of
    -- which `eraseRecArgs` leaves alone, so the two propositions are the same one
    (∀ (env : VEnv) (Us : List Name), OracleSound (vtr? [`u]) env Us →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t →
        ntreeAux.types[j]? = some T → TrIndType env Us t T) ∧
    (∀ (env : VEnv) (K : List Name) (Us : List Name),
      (∀ env₁, env.addIndTypesC (eraseRecArgs ntreeAux) K = some env₁ →
        OracleSound (vtr? [`u]) env₁ Us) →
      ∀ env₁, env.addIndTypesC (eraseRecArgs ntreeAux) K = some env₁ →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t →
        (eraseRecArgs ntreeAux).types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us (eraseRecArgs ntreeAux) (eraseRecArgs ntreeAux).idRestore j c C) ∧
    -- …and `trCtors` at `ntreeAux` itself.  `VIndCtor.typeR` at `D.idRestore` is
    -- `VIndCtor.type` (`VIndCtor.typeR_id`, unconditional) and `VIndField.typeR` is `F.type` on
    -- *both* branches, so erasing `recArg` does not move the constructor's stored type; at this
    -- closed block the two are the same term and the two propositions are the same one.
    (∀ (env : VEnv) (K : List Name) (Us : List Name),
      (∀ env₁, env.addIndTypesC (eraseRecArgs ntreeAux) K = some env₁ →
        OracleSound (vtr? [`u]) env₁ Us) →
      ∀ env₁, env.addIndTypesC (eraseRecArgs ntreeAux) K = some env₁ →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us ntreeAux ntreeAux.idRestore j c C) ∧
    -- anti-vacuity: `j = 0` is a matching pair with a nonzero count on both sides, and the
    -- constructor whose name is compared is Lean's own `NTree.node`
    (∃ t T, ntreeRTypes[0]? = some t ∧ ntreeAux.types[0]? = some T ∧
      t.ctors.length = 1 ∧ T.ctors.length = 1 ∧
      t.ctors.map (·.name) = [``NTree.node] ∧ T.ctors = [ntreeNode]) ∧
    -- …and `j = 1` is the companion, where the *user's* block has no member: `ntreeRTypes`
    -- does, because it is the post-elimination list, and it has two constructors there
    (ntreeRTypes[1]?.map (·.ctors.length) = some 2 ∧
      ntreeAux.types[1]?.map (·.ctors.length) = some 2) ∧
    -- **the one thing the map does NOT recover**, machine-checked rather than asserted in
    -- prose: `recArg`.  `ntreeNode` has one recursive field, the map's constructor has none —
    -- and no field of `TrIndDeclN` can tell them apart, because `VIndField.typeR` at
    -- `D.idRestore` is `F.type` on both branches.  Recovering it is `isRecArg`'s job and
    -- `VInductDecl'.WF`'s obligation, listed under Claim B.
    ntreeNode.recFields.length = 1 ∧
    (((eraseRecArgs ntreeAux).types.getD 0 default).ctors.getD 0 default).recFields.length = 0 ∧
    -- the two negative controls
    ntreeAux.nameSkelV ≠ surfNameSkel ntreeRTypesDbl ∧
    surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypesRenamed = none := by
  have hmap := ntreeRTypes_maps
  have hskel := nameSkelV_surfInductDecl? hmap
  have hskel' : ntreeAux.nameSkelV = surfNameSkel ntreeRTypes := by
    rw [← hskel]; rfl
  have hpre : SkelPrefix ntreeRTypes ntreeAux := ⟨[], by rw [hskel', List.append_nil]⟩
  exact ⟨rfl, rfl, rfl, rfl, hmap, hskel, hskel', hpre,
    trCtorsLen_of_skelPrefix hpre, ctorNameOwn_of_skelPrefix hpre,
    fun _ _ _ ht hT => name_eq_of_skelPrefix hpre ht hT,
    fun _ _ hO => trType_surfInductDecl? hmap hO,
    fun env Us hO j t T ht hT => by
      match j, hT with
      | 0, hT =>
        cases hT
        have H := trType_surfInductDecl? hmap hO 0 t
          ((eraseRecArgs ntreeAux).types.getD 0 default) ht rfl
        exact ⟨H.1, H.2⟩
      | 1, hT =>
        cases hT
        have H := trType_surfInductDecl? hmap hO 1 t
          ((eraseRecArgs ntreeAux).types.getD 1 default) ht rfl
        exact ⟨H.1, H.2⟩
      | j+2, hT => exact absurd hT nofun,
    fun _ _ _ hO => trCtors_surfInductDecl? hmap hO,
    fun env K Us hO env₁ hst j t T ht hT q c C hc hC => by
      have gen := trCtors_surfInductDecl? hmap hO env₁ hst
      match j, hT with
      | 0, hT =>
        cases hT
        match q, hC with
        | 0, hC =>
          cases hC
          have H := gen 0 t ((eraseRecArgs ntreeAux).types.getD 0 default) ht rfl 0 c
            (((eraseRecArgs ntreeAux).types.getD 0 default).ctors.getD 0 default) hc rfl
          exact ⟨H.1, H.2⟩
        | q+1, hC => exact absurd hC nofun
      | 1, hT =>
        cases hT
        match q, hC with
        | 0, hC =>
          cases hC
          have H := gen 1 t ((eraseRecArgs ntreeAux).types.getD 1 default) ht rfl 0 c
            (((eraseRecArgs ntreeAux).types.getD 1 default).ctors.getD 0 default) hc rfl
          exact ⟨H.1, H.2⟩
        | 1, hC =>
          cases hC
          have H := gen 1 t ((eraseRecArgs ntreeAux).types.getD 1 default) ht rfl 1 c
            (((eraseRecArgs ntreeAux).types.getD 1 default).ctors.getD 1 default) hc rfl
          exact ⟨H.1, H.2⟩
        | q+2, hC => exact absurd hC nofun
      | j+2, hT => exact absurd hT nofun,
    ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl,
    ntreeAux_not_nameSkelV_dbl, ntreeRTypesRenamed_fails⟩

end InductiveDeclExamples

/-! ## §7 Axiom checks

Every declaration this file adds, per the process rule: a silently-holed declaration is caught
only by its own `#print axioms` line. -/

#print axioms Lean4Lean.surfIndCtor?
#print axioms Lean4Lean.surfIndCtor?_eq_some
#print axioms Lean4Lean.surfIndType?
#print axioms Lean4Lean.surfInductDecl?
#print axioms Lean4Lean.surfIndCtor?_name
#print axioms Lean4Lean.surfIndType?_name
#print axioms Lean4Lean.surfIndType?_type
#print axioms Lean4Lean.surfIndType?_ctors
#print axioms Lean4Lean.surfInductDecl?_types
#print axioms Lean4Lean.surfInductDecl?_data
#print axioms Lean4Lean.surfIndType?_ctorNames
#print axioms Lean4Lean.nameSkelV_surfInductDecl?
#print axioms Lean4Lean.skelPrefix_surfInductDecl?
#print axioms Lean4Lean.length_surfInductDecl?
#print axioms Lean4Lean.typeR_surfIndCtor?
#print axioms Lean4Lean.OracleSound
#print axioms Lean4Lean.trCtorsLen_surfInductDecl?
#print axioms Lean4Lean.ctorNameOwn_surfInductDecl?
#print axioms Lean4Lean.trType_surfInductDecl?
#print axioms Lean4Lean.trCtors_surfInductDecl?
#print axioms Lean4Lean.skelPrefix_of_surfInductDecl?_run
#print axioms Lean4Lean.trCtorsLen_of_surfInductDecl?_run
#print axioms Lean4Lean.InductiveDeclExamples.vtr?
#print axioms Lean4Lean.InductiveDeclExamples.nlistTypeE
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNodeRE
#print axioms Lean4Lean.InductiveDeclExamples.nlistNilE
#print axioms Lean4Lean.InductiveDeclExamples.nlistConsE
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypes
#print axioms Lean4Lean.InductiveDeclExamples.eraseRecArgs
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypes_maps
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesDbl
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_nameSkelV_dbl
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesRenamed
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesRenamed_fails
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_surfaceMap_witness

end Lean4Lean
