import Lean4Lean.Theory.Inductive.NestedHead

/-!
# The abstract `replaceIfNested`: the auxiliary member as a *function* of `J`

`Theory/Inductive/NestedHead.lean` made `restoreNested` a parameter of the recursor
construction and stated what it owes as `VIndRestore.Faithful`.  Two of that structure's
three clauses — `ctor_agree` and `ctors_complete` — are *equations a caller supplies*, and
`docs/handoff-nested-restore.md` §7.1 names them as the one remaining place a caller can lie.
The shape is exactly `InductiveDeclExamples.fooComp_inconsistent`'s: a field the spec merely
checks, where the implementation *copies*.

This file closes it the way `resolveC` was meant to and could not: by **building** the
auxiliary member from the history block `J` and the instantiation, so that the two clauses
become theorems about a construction.

The construction mirrors `ElimNestedInductive.replaceIfNested` (`Lean4Lean/Inductive/Add.lean`)
step for step:

| `Add.lean` | here |
|---|---|
| `auxJ_type := J_info.type.instantiateLevelParams … I_lvls` then `instantiateForallParams I_nparams args` then `lctx.mkForall As` | `VNestedOcc.instAt` |
| `auxJ_ctors ← J_info.ctors.mapM …` — **`J`'s whole constructor list** | `VNestedOcc.member`'s `ctors` field |
| `auxJ_ctor_type` — the same instantiation on each constructor | `VNestedOcc.ctor` |
| the later `replaceAllNested` pass, which turns a `J`-headed field back into an auxiliary-headed one | `VIndRestore.recog` |

The last row is the interesting one.  `replaceAllNested` *replaces* `J Ds π` by `Iaux As π`;
`VIndRestore.recog` reads the same rewrite off the restoration `R` — it recognises a field
whose **restored** form is `∀ ξ, (R.tyName k).{R.tyLvls k} (R.tyArgs k) π` and returns the
`VIndRecArg` whose *stored* form is the block-headed one.  Recognition rather than replacement
is what makes `ctor_agree` come out **unconditionally**: `VIndField.typeR` is a left inverse of
the recognition by construction (`recog_sound`), so no canonicity or shape hypothesis on `J`
is needed.

## What is new, and what is inherited

* `VIndRestore.recog` and `recog_sound` — the recogniser and its soundness.
* `VNestedOcc` — the data of one nested occurrence, exactly `replaceIfNested`'s input.
* `VNestedOcc.member` — the auxiliary member, **a function**.
* `VNestedOcc.member_typeR` / `ctor_typeR` — `Faithful.ty_agree` and `ctor_agree` as
  *theorems*; `member_ctors_complete` — `ctors_complete` as a theorem.
* `VNestedOcc.member_Canonical` — `VIndCtor.Canonical` holds by construction, so
  `NestedHead.lean`'s conservativity side condition is discharged for a built member.
* `VEnv.AddNestedB` — the step with `Faithful` replaced by "every companion member **is**
  the member built from a history block the environment declares", and
  `AddNestedB.toAddNested`.

`Theory/Inductive/NestedHead.lean` is unchanged; everything here is additive.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars liftTele shift shiftTele instAll instAllTele splitPis
  spineArgs piArity)

/-! ## Part 1: the syntactic scaffolding a recogniser needs -/

namespace VExpr

/-- The head of an application spine (`Lean.Expr.getAppFn`). -/
def spineFn : VExpr → VExpr
  | .app f _ => f.spineFn
  | e => e

@[simp] theorem spineFn_app {f a : VExpr} : (VExpr.app f a).spineFn = f.spineFn := rfl
@[simp] theorem spineFn_const {c : Lean.Name} {ls : List VLevel} :
    (VExpr.const c ls).spineFn = .const c ls := rfl

/-- Every term is its head applied to its spine. -/
theorem mkApp_spineFn_spineArgs : ∀ e : VExpr, mkApp e.spineFn e.spineArgs = e
  | .app f a => by
    rw [spineFn_app, spineArgs, VExpr.mkApp_append, mkApp_spineFn_spineArgs f]; rfl
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ => rfl

/-- `splitPis` never loses anything: re-assembling its output returns the input, at **every**
`n`, because the `n+1`-at-a-non-`forallE` case returns the empty telescope. -/
theorem mkPi_splitPis : ∀ (n : Nat) (e : VExpr),
    mkPi (splitPis n e).1 (splitPis n e).2 = e
  | 0, _ => rfl
  | _+1, .forallE A B => by
    rw [splitPis]
    show mkPi (A :: (splitPis _ B).1) (splitPis _ B).2 = _
    rw [VExpr.mkPi_cons, mkPi_splitPis]
  | _+1, .bvar _ | _+1, .sort _ | _+1, .const _ _ | _+1, .lam _ _ | _+1, .app _ _ => rfl

end VExpr

/-! ## Part 2: the recogniser

`VIndRestore.recogAt R i k S` asks: *is `S` the restored form of a recursive field at member
`k`?*  It splits `S`'s leading pis, and checks that what remains is the constant
`R.tyName k` at the levels `R.tyLvls k`, applied to the stored instantiation `R.tyArgs k`
weakened past those binders, and then to some index arguments.

Nothing about `D` enters: `VInductDecl'.tyAppR` ignores its `VInductDecl'` argument, so the
recogniser is a function of the restoration alone.  That is what breaks the circularity —
an auxiliary member's *own* field types mention the block being declared. -/

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

namespace VIndRestore

/-- Recognise `S` as a restored recursive field at block member `k`, in a field context with
`i` earlier fields. -/
def recogAt (R : VIndRestore) (i k : Nat) (S : VExpr) : Option VIndRecArg :=
  let ξ := (splitPis S.piArity S).1
  let b := (splitPis S.piArity S).2
  let sp := b.spineArgs
  let nA := (R.tyArgs k).length
  if b.spineFn = VExpr.const (R.tyName k) (R.tyLvls k) ∧
      sp.take nA = (R.tyArgs k).map (·.liftN (ξ.length + i)) ∧ nA ≤ sp.length then
    some { binders := ξ, idx := k, args := sp.drop nA }
  else none

/-- Recognise at any member of an `nm`-member block, preferring the earliest. -/
def recog (R : VIndRestore) (nm i : Nat) (S : VExpr) : Option VIndRecArg :=
  (List.range nm).findSome? fun k => R.recogAt i k S

/-- **Soundness of the recogniser.**  What it returns *restores* to what it was given —
so `VIndField.typeR` is a left inverse of it, whatever `D` is. -/
theorem recogAt_sound {R : VIndRestore} {i k : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recogAt i k S = some r) (D : VInductDecl') : r.canonTypeR D R i = S := by
  rw [recogAt] at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases h
    rw [VIndRecArg.canonTypeR, VIndRecArg.canonResultR, VInductDecl'.tyAppR,
      VInductDecl'.tyAppH, ← h2, List.take_append_drop, ← h1,
      VExpr.mkApp_spineFn_spineArgs, VExpr.mkPi_splitPis]
  · exact absurd h nofun

theorem recog_sound {R : VIndRestore} {nm i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recog nm i S = some r) (D : VInductDecl') : r.canonTypeR D R i = S := by
  rw [recog, List.findSome?_eq_some_iff] at h
  obtain ⟨_, _, _, _, hk, -⟩ := h
  exact recogAt_sound hk D

/-- The recognised index is a member of the block. -/
theorem recogAt_idx {R : VIndRestore} {i k : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recogAt i k S = some r) : r.idx = k := by
  rw [recogAt] at h; split at h
  · cases h; rfl
  · exact absurd h nofun

/-- The recognised binder telescope is `S`'s own leading pi telescope. -/
theorem recogAt_binders {R : VIndRestore} {i k : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recogAt i k S = some r) : r.binders = (splitPis S.piArity S).1 := by
  rw [recogAt] at h; split at h
  · cases h; rfl
  · exact absurd h nofun

theorem recog_binders {R : VIndRestore} {nm i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recog nm i S = some r) : r.binders = (splitPis S.piArity S).1 := by
  rw [recog, List.findSome?_eq_some_iff] at h
  obtain ⟨_, _, _, _, hk, -⟩ := h
  exact recogAt_binders hk


theorem recog_idx_lt {R : VIndRestore} {nm i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : R.recog nm i S = some r) : r.idx < nm := by
  rw [recog, List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, k, l₂, he, hk, -⟩ := h
  have hm : k ∈ List.range nm := by rw [he]; simp
  rw [recogAt_idx hk]; simpa using hm

end VIndRestore


/-! ## Part 3: the substitution lemma the construction runs on

`instAt` substitutes the nested spine for `J`'s parameter run.  The one arithmetic fact this
needs and `Theory/Inductive/` did not have is the shifted form of
`VExpr.map_instAll_bvars`: the parameter run at depth `k`, instantiated at that same depth,
gives the spine weakened past the `k` binders — which is precisely `tyAppH`'s stored block. -/

namespace VExpr

/-- `map_instAll_bvars` at a nonzero cut. -/
theorem map_instAll_bvars_at : ∀ (as : List VExpr) (k : Nat),
    (bvars k as.length).map (instAll · as k) = as.map (·.liftN k)
  | [], _ => rfl
  | a :: as, k => by
    have h1 : instAll (VExpr.bvar (k + as.length)) (a :: as) k = a.liftN k := by
      rw [instAll_cons,
        show (VExpr.bvar (k + as.length)).inst a (k + as.length) = a.liftN (k + as.length) 0 from by
          simp only [inst, instVar, if_neg (Nat.lt_irrefl _), if_true],
        ← liftN'_liftN' (n1 := k) (n2 := as.length) (k1 := 0) (k2 := k)
          (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero k).symm),
        instAll_liftN]
    have h2 : (bvars k as.length).map (instAll · (a :: as) k) = as.map (·.liftN k) := by
      have hc : (bvars k as.length).map (instAll · (a :: as) k)
          = (bvars k as.length).map (instAll · as k) := by
        refine List.map_congr_left fun e he => ?_
        obtain ⟨v, hv, rfl⟩ := mem_bvars.1 he
        rw [instAll_cons,
          show (VExpr.bvar (k + v)).inst a (k + as.length) = .bvar (k + v) from by
            simp only [inst, instVar, if_pos (by omega : k + v < k + as.length)]]
      rw [hc, map_instAll_bvars_at as k]
    rw [List.length_cons, bvars_succ, List.map_cons, h1, h2, List.map_cons]

end VExpr

/-! ## Part 4: the block header

An auxiliary member's *own* field types are headed by constants of the block being
declared — including its own name — so the construction cannot take the finished
`VInductDecl'` as input.  `VIndHeader` is the part it can: the parameter telescope, the
universe count, the member count, and the member names. -/

/-- The part of a block a self-referential stored field type needs. -/
structure VIndHeader where
  uvars : Nat
  params : List VExpr
  nm : Nat
  names : Nat → Lean.Name

/-- Every block has one. -/
def VInductDecl'.header (D : VInductDecl') : VIndHeader where
  uvars := D.uvars
  params := D.params
  nm := D.nm
  names j := (D.types.getD j default).name

/-- `VIndRecArg.canonType` against a header. -/
def VIndRecArg.canonTypeH (r : VIndRecArg) (H : VIndHeader) (i : Nat) : VExpr :=
  mkPi r.binders ((VExpr.const (H.names r.idx) (VLevel.params H.uvars)).mkApp
    (bvars (r.binders.length + i) H.params.length ++ r.args))

theorem VIndRecArg.canonTypeH_header (r : VIndRecArg) (D : VInductDecl') (i : Nat) :
    r.canonTypeH D.header i = r.canonType D i := rfl

/-! ## Part 5: `replaceIfNested`, abstractly

`VNestedOcc` is exactly `replaceIfNested`'s input: the previously declared block `J`, which
member of it is nested, the levels the occurrence is at, the nested spine `Ds` over the new
block's parameters, and the two names the pass invents. -/

/-- One nested occurrence. -/
structure VNestedOcc where
  /-- `J`'s block, as the declaration history holds it. -/
  decl : VInductDecl'
  /-- Which member of `J`'s block this auxiliary member stands for.  `replaceIfNested`
  makes one auxiliary member for **every** member of `I_val.all`, so `idx` ranges over the
  whole block, not just the occurrence's own head. -/
  idx : Nat
  /-- `I_lvls`, the levels the occurrence is at. -/
  lvls : List VLevel
  /-- `Ds`, the nested spine, over the new block's parameters. -/
  args : List VExpr
  /-- `mkUniqueName (`_nested ++ J_name)`. -/
  auxName : Lean.Name
  /-- `J_ctor_name.replacePrefix J_name auxJ_name`. -/
  ctorName : Lean.Name → Lean.Name

namespace VNestedOcc
variable (N : VNestedOcc)

/-- The member of `J`'s block being nested. -/
def src : VIndType := N.decl.types.getD N.idx default

/-- The name the auxiliary member is *presented* as, i.e. `R.tyName`'s value. -/
def tyName : Lean.Name := N.src.name

/-- **`Add.lean`'s `lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args`.**
`J`'s stored type (or a constructor's), instantiated at the occurrence's levels and spine and
re-abstracted over the new block's parameters. -/
def instAt (H : VIndHeader) (e : VExpr) : VExpr :=
  mkPi H.params (VExpr.instAll (splitPis N.decl.np (e.instL N.lvls)).2 N.args)

/-- One field of an auxiliary constructor.  The substituted type is `S`; the recogniser
decides whether it is a recursive position of the *new* block, and if so the field is stored
in its block-headed form — which is what the implementation's later `replaceAllNested` pass
writes. -/
def field (H : VIndHeader) (R : VIndRestore) (i : Nat) (F₀ : VIndField) : VIndField :=
  let S := VExpr.instAll (F₀.type.instL N.lvls) N.args i
  match R.recog H.nm i S with
  | some r => { type := r.canonTypeH H i, lvl := F₀.lvl.inst N.lvls, recArg := some r }
  | none => { type := S, lvl := F₀.lvl.inst N.lvls, recArg := none }

/-- The field telescope, in declaration order from index `i`. -/
def fieldsFrom (N : VNestedOcc) (H : VIndHeader) (R : VIndRestore) :
    Nat → List VIndField → List VIndField
  | _, [] => []
  | i, F₀ :: Fs => N.field H R i F₀ :: fieldsFrom N H R (i+1) Fs

/-- One auxiliary constructor. -/
def ctor (H : VIndHeader) (R : VIndRestore) (C₀ : VIndCtor) : VIndCtor where
  name := N.ctorName C₀.name
  params := H.params
  fields := N.fieldsFrom H R 0 C₀.fields
  args := C₀.args.map fun a => VExpr.instAll (a.instL N.lvls) N.args C₀.fields.length

/-- **The auxiliary member.**  Its constructor list is `J`'s, mapped — which is
`Faithful.ctors_complete`, by construction rather than by hypothesis. -/
def member (H : VIndHeader) (R : VIndRestore) : VIndType where
  name := N.auxName
  type := N.instAt H N.src.type
  indices := VExpr.instAllTele (N.src.indices.map (·.instL N.lvls)) N.args 0
  ctors := N.src.ctors.map (N.ctor H R)

@[simp] theorem length_fieldsFrom (H : VIndHeader) (R : VIndRestore) :
    ∀ (i : Nat) (Fs : List VIndField), (N.fieldsFrom H R i Fs).length = Fs.length
  | _, [] => rfl
  | i, _ :: Fs => by rw [fieldsFrom, List.length_cons, List.length_cons,
      length_fieldsFrom H R (i+1) Fs]

theorem getElem?_fieldsFrom (H : VIndHeader) (R : VIndRestore) :
    ∀ (i : Nat) (Fs : List VIndField) (k : Nat),
      (N.fieldsFrom H R i Fs)[k]? = (Fs[k]?).map (N.field H R (i + k))
  | _, [], k => by rw [fieldsFrom]; simp
  | i, F₀ :: Fs, 0 => by rw [fieldsFrom]; simp
  | i, F₀ :: Fs, k+1 => by
    rw [fieldsFrom, List.getElem?_cons_succ, List.getElem?_cons_succ,
      getElem?_fieldsFrom H R (i+1) Fs k,
      show i + 1 + k = i + (k+1) from by omega]

/-- **The recogniser is a section of `VIndField.typeR`.**  Whatever branch `field` takes, its
restored stored type is the substituted type it was built from — unconditionally: no
canonicity, no shape hypothesis on `J`. -/
theorem field_typeR (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') (i : Nat)
    (F₀ : VIndField) :
    (N.field H R i F₀).typeR D R i = VExpr.instAll (F₀.type.instL N.lvls) N.args i := by
  rw [field]
  split <;> rename_i heq
  · rw [VIndField.typeR]; exact R.recog_sound heq D
  · rw [VIndField.typeR]

theorem fieldTypes_from (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') :
    ∀ (Fs : List VIndField) (i : Nat),
      ((N.fieldsFrom H R i Fs).zipIdx i).map (fun p => p.1.typeR D R p.2)
        = VExpr.instAllTele (Fs.map (fun F => F.type.instL N.lvls)) N.args i
  | [], _ => rfl
  | F₀ :: Fs, i => by
    rw [fieldsFrom, List.zipIdx_cons, List.map_cons, List.map_cons, VExpr.instAllTele_cons,
      field_typeR, fieldTypes_from H R D Fs (i+1)]

theorem ctor_fieldTypesR (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') (C₀ : VIndCtor) :
    (N.ctor H R C₀).fieldTypesR D R
      = VExpr.instAllTele (C₀.fields.map (fun F => F.type.instL N.lvls)) N.args 0 := by
  rw [VIndCtor.fieldTypesR, ctor, fieldTypes_from]

/-- The constructor's *result*, substituted, is the restored head applied to the substituted
index arguments — the one place the arithmetic of the parameter run and the stored spine
meet. -/
theorem canonResult_instAll (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') (j : Nat)
    (C₀ : VIndCtor) (hname : R.tyName j = N.tyName) (hls : R.tyLvls j = N.lvls)
    (hargs : R.tyArgs j = N.args) (hA : N.args.length = N.decl.np)
    (hlv : N.lvls.length = N.decl.uvars) :
    VExpr.instAll ((C₀.canonResult N.decl N.idx).instL N.lvls) N.args C₀.fields.length
      = D.tyAppR R j C₀.fields.length (N.ctor H R C₀).args := by
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.instL_mkApp,
    show (VExpr.const (N.decl.types.getD N.idx default).name N.decl.ownLvls).instL N.lvls
        = VExpr.const N.tyName N.lvls from by
      rw [VExpr.instL, VInductDecl'.ownLvls, VLevel.inst_map_id hlv]; rfl,
    List.map_append, VExpr.map_instL_bvars, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_append, ← hA, VExpr.map_instAll_bvars_at, VInductDecl'.tyAppR,
    VInductDecl'.tyAppH, hname, hls, hargs, ctor, List.map_map]
  rfl

/-- **`Faithful.ctor_agree`, as a theorem.**  The auxiliary constructor's *restored* stored
type is `J`'s constructor's stored type, instantiated at the occurrence's levels and spine and
re-abstracted over the block's parameters.

There is no canonicity hypothesis and no hypothesis about `J`'s field shapes: the recogniser
is a section of `VIndField.typeR` whatever it returns (`field_typeR`).  The three `R`
equations say only that the restoration presents member `j` as this occurrence; the two
length equations are `replaceIfNested`'s own `assert!`s. -/
theorem ctor_typeR (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') (j : Nat)
    (C₀ : VIndCtor)
    (hname : R.tyName j = N.tyName) (hls : R.tyLvls j = N.lvls) (hargs : R.tyArgs j = N.args)
    (hnp : C₀.params.length = N.decl.np) (hA : N.args.length = N.decl.np)
    (hlv : N.lvls.length = N.decl.uvars) :
    (N.ctor H R C₀).typeR D R j = N.instAt H (C₀.type N.decl N.idx) := by
  rw [VIndCtor.typeR, ctor_fieldTypesR, instAt, VIndCtor.type]
  simp only [VExpr.instL_mkPi, VExpr.mkPi_append, List.map_map]
  rw [show N.decl.np = (C₀.params.map (VExpr.instL N.lvls)).length from by
      rw [List.length_map, hnp],
    VExpr.splitPis_mkPi, VExpr.instAll_mkPi, List.length_map, Nat.zero_add]
  show mkPi (N.ctor H R C₀).params _ = _
  congr 1
  rw [show (N.ctor H R C₀).fields.length = C₀.fields.length from
      N.length_fieldsFrom H R 0 C₀.fields]
  congr 1
  exact (canonResult_instAll N H R D j C₀ hname hls hargs hA hlv).symm

/-- `VIndRestore.instAt` and `VNestedOcc.instAt` are the same operation: the former reads its
level list and spine off the restoration, the latter off the occurrence. -/
theorem instAt_eq (H : VIndHeader) (R : VIndRestore) (D : VInductDecl') (j npJ : Nat)
    (e : VExpr) (hp : H.params = D.params) (hls : R.tyLvls j = N.lvls)
    (hargs : R.tyArgs j = N.args) (hnpJ : npJ = N.decl.np) :
    R.instAt D npJ j e = N.instAt H e := by
  rw [VIndRestore.instAt, instAt, hp, hls, hargs, hnpJ]

/-- **`Faithful.ctors_complete`, by construction.**  The auxiliary member's constructor list
*is* `J`'s, mapped: `replaceIfNested` writes `J_info.ctors.mapM`, and so does this. -/
theorem member_ctors_complete (H : VIndHeader) (R : VIndRestore)
    (hcn : ∀ C ∈ N.src.ctors, R.ctorName (N.ctorName C.name) = C.name) :
    (N.member H R).ctors.map (fun C => R.ctorName C.name) = N.src.ctors.map (·.name) := by
  rw [member, List.map_map]
  exact List.map_congr_left fun C hC => hcn C hC

/-- **`VIndCtor.Canonical` holds by construction.**  A built field's stored type is the
block-headed canonical form whenever it has a `recArg` at all, because that is the only branch
the recogniser takes.  So `NestedHead.lean`'s conservativity side condition costs a built
member nothing. -/
theorem ctor_Canonical (R : VIndRestore) (D : VInductDecl') (C₀ : VIndCtor) :
    (N.ctor D.header R C₀).Canonical D := by
  intro i F r hF hr
  rw [ctor, getElem?_fieldsFrom] at hF
  obtain ⟨F₀, -, rfl⟩ := Option.map_eq_some_iff.1 hF
  rw [field] at hr ⊢
  split at hr <;> [skip; exact absurd hr nofun]
  cases hr
  show r.canonTypeH D.header (0 + i) = _
  rw [Nat.zero_add, VIndRecArg.canonTypeH_header]

theorem member_Canonical (R : VIndRestore) (D : VInductDecl') (C : VIndCtor)
    (hC : C ∈ (N.member D.header R).ctors) : C.Canonical D := by
  rw [member, List.mem_map] at hC
  obtain ⟨C₀, -, rfl⟩ := hC
  exact N.ctor_Canonical R D C₀

/-! ### What the occurrence owes the history

Note what is *not* here: nothing about the auxiliary member.  Every clause is either a
length equation `replaceIfNested` itself asserts, or a fact about the constants the
environment already holds — which is what the step that declared `J` produced
(`VEnv.addInduct'_types`, `VEnv.addInduct'_ctors`). -/

/-- The occurrence is of a block the history declared, at the arity it was declared with. -/
structure Occurs (N : VNestedOcc) (env : VEnv) : Prop where
  /-- `J` is a block the environment already carries: `addInduct'` ran on it below `env`.

  This used to be `VDecl.induct N.decl ∈ ds`, and `ds` was threaded from here all the way out
  to `VEnv.AddNestedB` — which is what made the step unstateable as a `VDecl.WF` rule, since
  `VDecl.WF env d env'` carries no history.  `VInductDecl'.Declared` is the same fact stated
  over `env` alone (`Theory/Inductive/Decl.lean`), and a history discharges it
  (`VEnv.WF'.declared`, `Theory/Inductive/Nested.lean`). -/
  hist : N.decl.Declared env
  /-- `idx` names a member of it. -/
  idx_lt : N.idx < N.decl.types.length
  /-- **Universe-count agreement** (`docs/handoff-nested-restore.md` §5's fourth item): the
  occurrence is at `J`'s own universe arity.  `replaceIfNested` gets this from the occurrence
  `I.{I_lvls}` being a well-formed constant application. -/
  lvls_len : N.lvls.length = N.decl.uvars
  /-- `replaceIfNested`'s `assert! I_nparams ≤ args.size`, at the parameter prefix. -/
  args_len : N.args.length = N.decl.np
  /-- The environment holds `J`'s member as the history declares it. -/
  ty_const : env.constants N.tyName = some ⟨N.decl.uvars, N.src.type⟩
  /-- …and each of its constructors, at the recorded parameter count. -/
  ctor_params : ∀ C ∈ N.src.ctors, C.params.length = N.decl.np
  ctor_const : ∀ C ∈ N.src.ctors,
    env.constants C.name = some ⟨N.decl.uvars, C.type N.decl N.idx⟩

theorem Occurs.src_mem {N : VNestedOcc} {env : VEnv} (h : N.Occurs env) :
    N.decl.types[N.idx]? = some N.src := by
  rw [src, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.idx_lt]; rfl

end VNestedOcc

/-! ## Part 6: the step, with nowhere left to lie

`VEnv.AddNested` (`NestedHead.lean`) takes `VIndRestore.Faithful` as a hypothesis, and two of
its three clauses are equations a caller supplies.  `VInductDecl'.Built` replaces all three by
one: **the companion member is the value the construction computes.** -/

/-- Every member of `D` named in `K` is the auxiliary member built from the occurrence
`occ j`, and the restoration presents it as that occurrence. -/
structure VInductDecl'.Built (D : VInductDecl') (R : VIndRestore) (K : List Lean.Name)
    (env : VEnv) (occ : Nat → VNestedOcc) : Prop where
  /-- **The one clause that replaces `ty_agree`, `ctor_agree` and `ctors_complete`.** -/
  member : ∀ j T, D.types[j]? = some T → T.name ∈ K → T = (occ j).member D.header R
  occurs : ∀ j T, D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env
  tyName : ∀ j T, D.types[j]? = some T → T.name ∈ K → R.tyName j = (occ j).tyName
  tyLvls : ∀ j T, D.types[j]? = some T → T.name ∈ K → R.tyLvls j = (occ j).lvls
  tyArgs : ∀ j T, D.types[j]? = some T → T.name ∈ K → R.tyArgs j = (occ j).args
  /-- The naming residue: `restoreCtorName` inverts the auxiliary constructor naming.  This is
  an equation between *names* only — no expression, no type, no constructor list. -/
  ctorName_inv : ∀ j T, D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ (occ j).src.ctors, R.ctorName ((occ j).ctorName C.name) = C.name
  /-- **The restoration is the identity off `K`.**  `Built`'s other six clauses, like
  `Faithful`'s three, are all guarded by `T.name ∈ K`, so without this one the restoration is
  unconstrained on the members the step actually declares — see `VIndRestore.OwnId`
  (`Theory/Inductive/Restore.lean`) for what goes wrong. -/
  own : R.OwnId D K

/-- **`Faithful` is a consequence of the construction.**  This is `docs/handoff-nested-restore.md`
§7.1: `ctors_complete` and `ctor_agree` stop being hypotheses. -/
theorem VInductDecl'.Built.toFaithful {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {env : VEnv} {occ : Nat → VNestedOcc}
    (h : D.Built R K env occ) :
    R.Faithful D env K (fun j => (occ j).decl.np) where
  ty_agree := by
    intro j T hT hK
    have ho := h.occurs j T hT hK
    refine ⟨_, by rw [h.tyName j T hT hK]; exact ho.ty_const, ?_, ?_⟩
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl, h.member j T hT hK]
      rfl
  ctor_agree := by
    intro j T hT hK C hC
    have ho := h.occurs j T hT hK
    rw [h.member j T hT hK, VNestedOcc.member, List.mem_map] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    refine ⟨⟨(occ j).decl.uvars, C₀.type (occ j).decl (occ j).idx⟩, ?_, ?_, ?_⟩
    · rw [show ((occ j).ctor D.header R C₀).name = (occ j).ctorName C₀.name from rfl,
        h.ctorName_inv j T hT hK C₀ hC₀]
      exact ho.ctor_const C₀ hC₀
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl]
      exact ((occ j).ctor_typeR D.header R D j C₀ (h.tyName j T hT hK)
        (h.tyLvls j T hT hK) (h.tyArgs j T hT hK) (ho.ctor_params C₀ hC₀) ho.args_len
        ho.lvls_len).symm
  ctors_complete := by
    intro j T hT hK
    have ho := h.occurs j T hT hK
    refine ⟨(occ j).decl, (occ j).idx, (occ j).src, ho.hist, ho.src_mem, ?_, rfl, ?_⟩
    · rw [h.tyName j T hT hK]; rfl
    · rw [h.member j T hT hK]
      exact (occ j).member_ctors_complete D.header R (h.ctorName_inv j T hT hK)

/-- The canonicity side condition, on the members the *user* wrote.  A built member gets it
for free (`VNestedOcc.member_Canonical`). -/
def VInductDecl'.CanonicalOwn (D : VInductDecl') (K : List Lean.Name) : Prop :=
  ∀ j C, (j, C) ∈ D.ctorsAll → (D.types.getD j default).name ∉ K → C.Canonical D

theorem VInductDecl'.Built.canonical {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {env : VEnv} {occ : Nat → VNestedOcc}
    (h : D.Built R K env occ) (hown : D.CanonicalOwn K) : D.Canonical := by
  intro j C hjC
  obtain ⟨T, hT, hC⟩ := D.mem_ctorsAll hjC
  have hname : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  by_cases hK : T.name ∈ K
  · rw [h.member j T hT hK] at hC
    exact (occ j).member_Canonical R D C hC
  · exact hown j C hjC (by rw [hname]; exact hK)

/-- **The nested declaration step, with the auxiliary members built rather than checked.**

Compare `VEnv.AddNested`: `VIndRestore.Faithful` is gone, and `VInductDecl'.Canonical` is
weakened to the members the user wrote. -/
def VEnv.AddNestedB (env : VEnv) (D : VInductDecl') (K : List Lean.Name)
    (R : VIndRestore) (occ : Nat → VNestedOcc) (env' : VEnv) : Prop :=
  D.WF env ∧ D.CanonicalOwn K ∧ D.Built R K env occ ∧ env.addInductR D K R = some env'

theorem VEnv.AddNestedB.toAddNested {env env' : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} {R : VIndRestore} {occ : Nat → VNestedOcc}
    (h : VEnv.AddNestedB env D K R occ env') :
    VEnv.AddNested env D K R (fun j => (occ j).decl.np) env' :=
  ⟨h.1, h.2.2.1.canonical h.2.1, h.2.2.1.own, h.2.2.1.toFaithful, h.2.2.2⟩

/-- **The constructive form implies the rule's premise.**  `VDecl.WF.inductNested`
(`Theory/Typing/Env.lean`) takes `VEnv.AddNestedStep`, i.e. `AddNested` with `npJ`
existentially quantified; a built block supplies it as `(occ j).decl.np`, and `Built.occurs`
pins that to the parameter count of the block the environment holds. -/
theorem VEnv.AddNestedB.toAddNestedStep {env env' : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} {R : VIndRestore} {occ : Nat → VNestedOcc}
    (h : VEnv.AddNestedB env D K R occ env') :
    VEnv.AddNestedStep env D K R env' :=
  ⟨_, h.toAddNested⟩

/-! ## Part 7: `BindersIndep` under the substitution

`VIndRecArg.BindersIndep` (`Theory/Inductive/Decl.lean`) forbids a recursive field's binder
telescope `ξ` from mentioning an *earlier recursive* field.  `docs/handoff-nested-restore.md`
§5 records it as *reached but not exercised*: every recursive field of `ntreeAux` has `ξ = []`.

For a built member the clause is a **substitution lemma**.  `ξ` is the leading pi telescope of
`instAll (F₀.type.instL ls) A i`, and `instAll` at cut `i` touches only the indices at or above
`i` — `J`'s parameters — while every earlier field sits strictly below.  So a `Skips` fact
about `J`'s own constructor transfers verbatim.  What the substitution *cannot* do is create a
dependence that was not there: that is `Skips.instAll` below, and it is the whole content. -/

namespace VExpr

/-- A term lifted past `m` binders mentions nothing below `m`. -/
theorem skips_liftN_lo {a : VExpr} {m j : Nat} (h : j < m) : (liftN m a 0).Skips 1 j := by
  refine skips_iff_exists.2 ⟨liftN (m-1) a 0, ?_⟩
  rw [liftN'_liftN' (n1 := m-1) (n2 := 1) (k1 := 0) (k2 := j) (Nat.zero_le _) (by omega),
    show m - 1 + 1 = m from by omega]

/-- **Substitution above the cut preserves independence below it.** -/
theorem Skips.instN {e a : VExpr} {m j : Nat} (hj : j < m) (he : e.Skips 1 j) :
    (e.inst a m).Skips 1 j := by
  rw [skips_iff] at he ⊢
  induction e generalizing j m with
  | bvar i =>
    simp only [Skips'] at he
    rw [inst, instVar]
    split
    · exact he
    · split
      · exact skips_iff.1 (skips_liftN_lo hj)
      · simp only [Skips']; omega
  | sort => exact trivial
  | const => exact trivial
  | app f a ihf iha => exact ⟨ihf hj he.1, iha hj he.2⟩
  | lam A b ihA ihb => exact ⟨ihA hj he.1, ihb (Nat.succ_lt_succ hj) he.2⟩
  | forallE A b ihA ihb => exact ⟨ihA hj he.1, ihb (Nat.succ_lt_succ hj) he.2⟩

theorem Skips.instAll : ∀ (as : List VExpr) {e : VExpr} {k j : Nat}, j < k → e.Skips 1 j →
    (instAll e as k).Skips 1 j
  | [], _, _, _, _, he => he
  | a :: as, e, k, j, hj, he => by
    rw [instAll_cons]
    exact Skips.instAll as hj (he.instN (a := a) (by omega))

/-- **Independence descends into a pi telescope.**  The `k`-th binder of a telescope sits `k`
binders deeper, so what the whole term skips at `t` the binder skips at `k + t`. -/
theorem skips_splitPis : ∀ (n : Nat) (S : VExpr) (t k : Nat) (B : VExpr),
    S.Skips 1 t → (splitPis n S).1[k]? = some B → B.Skips 1 (k + t)
  | 0, _, _, k, _, _, hk => by simp [splitPis] at hk
  | n+1, .forallE A C, t, 0, B, hS, hk => by
    simp only [splitPis, List.getElem?_cons_zero, Option.some.injEq] at hk
    cases hk
    rw [skips_iff] at hS ⊢
    rw [Nat.zero_add]; exact hS.1
  | n+1, .forallE A C, t, k+1, B, hS, hk => by
    simp only [splitPis, List.getElem?_cons_succ] at hk
    have hC : C.Skips 1 (t+1) := by rw [skips_iff] at hS ⊢; exact hS.2
    have := skips_splitPis n C (t+1) k B hC hk
    rwa [show k + (t+1) = k + 1 + t from by omega] at this
  | n+1, .bvar _, _, _, _, _, hk | n+1, .sort _, _, _, _, _, hk
  | n+1, .const _ _, _, _, _, _, hk | n+1, .app _ _, _, _, _, _, hk
  | n+1, .lam _ _, _, _, _, _, hk => by simp [splitPis] at hk

end VExpr

namespace VNestedOcc
variable (N : VNestedOcc)

/-- **What the construction reduces `BindersIndep` to.**  A field of `J` whose auxiliary
counterpart is *recursive* must be invisible to the later fields of `J`.

This is the syntactic residue of `VIndRecArg.exists_indep`'s open argument: an earlier field
becomes recursive exactly when its `J`-type is a parameter position of `J`, and nothing in
`J`'s own declaration can eliminate an abstract parameter — so a later field's type cannot
depend on its *value*.  Turning that into a proof is the same defeq problem `exists_indep`
records; `SrcIndep` is the checkable statement it would discharge. -/
def SrcIndep (N : VNestedOcc) (H : VIndHeader) (R : VIndRestore) (C₀ : VIndCtor) : Prop :=
  ∀ i i' t F F', C₀.fields[i]? = some F → C₀.fields[i']? = some F' →
    ((N.field H R i' F').recArg).isSome → i' + 1 + t = i → (F.type.instL N.lvls).Skips 1 t

/-- **`BindersIndep`, for a built constructor, is a theorem.**  No defeq, no environment: the
substitution moves the `Skips` facts and the pi-splitting distributes them over `ξ`. -/
theorem bindersIndep (H : VIndHeader) (R : VIndRestore) (C₀ : VIndCtor)
    (h : N.SrcIndep H R C₀) (i : Nat) (F : VIndField) (r : VIndRecArg)
    (hF : (N.fieldsFrom H R 0 C₀.fields)[i]? = some F) (hr : F.recArg = some r) :
    r.BindersIndep ((N.fieldsFrom H R 0 C₀.fields).take i) i := by
  rw [getElem?_fieldsFrom, Nat.zero_add] at hF
  obtain ⟨F₀, hF₀, rfl⟩ := Option.map_eq_some_iff.1 hF
  intro i' t F' hF' hrec hti k B hB
  have hi' : i' < i := by omega
  simp only [List.getElem?_take, if_pos hi'] at hF'
  rw [getElem?_fieldsFrom, Nat.zero_add] at hF'
  obtain ⟨F₀', hF₀', rfl⟩ := Option.map_eq_some_iff.1 hF'
  have hrb : r.binders = (splitPis
      (VExpr.instAll (F₀.type.instL N.lvls) N.args i).piArity
      (VExpr.instAll (F₀.type.instL N.lvls) N.args i)).1 := by
    rw [field] at hr
    split at hr <;> [skip; exact absurd hr nofun]
    rename_i heq
    cases hr
    exact VIndRestore.recog_binders heq
  rw [hrb] at hB
  exact VExpr.skips_splitPis _ _ t k B
    (VExpr.Skips.instAll _ (by omega) (h i i' t F₀ F₀' hF₀ hF₀' hrec hti)) hB

end VNestedOcc

/-! ## Part 8: the witness, rebuilt

`NestedHead.lean`'s `ntreeAux` is `inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α`
after nested elimination.  Its auxiliary member `_nested.List_1` was *written out* there.  Here
it is **computed** from `List`'s own block and the instantiation `[NTree α]`, and the two agree
on the nose. -/

namespace InductiveDeclExamples

open VNestedOcc

/-- The nested occurrence `List (NTree α)`, as `replaceIfNested` sees it. -/
def listOcc : VNestedOcc where
  decl := listDecl
  idx := 0
  lvls := [.param 0]
  args := [.app (.const ``NTree [.param 0]) (.bvar 0)]
  auxName := `_nested.List_1
  ctorName n := if n = ``List.nil then `_nested.List_1.nil
                else if n = ``List.cons then `_nested.List_1.cons else n

/-- **The auxiliary member is not data any more.**  `_nested.List_1`, its stored type, its
index telescope and *both* its constructors — including the `recArg` on `cons`'s **first**
field, which exists only because the instantiation turned `List`'s parameter position into a
recursive one — are the value the construction computes from `List`'s block. -/
theorem ntreeAux_member_built :
    ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) := rfl

/-- The recogniser fires on the field that nesting creates: `List`'s `cons` has a
*non-recursive* first field, and the instantiation makes it recursive into `NTree`. -/
theorem listOcc_recog_field0 :
    ntreeRestore.recog ntreeAux.header.nm 0
        (VExpr.instAll ((listCons.fields.getD 0 default).type.instL listOcc.lvls) listOcc.args 0)
      = some { binders := [], idx := 0, args := [] } := rfl

/-- …and on the one the auxiliary member's self-reference creates. -/
theorem listOcc_recog_field1 :
    ntreeRestore.recog ntreeAux.header.nm 1
        (VExpr.instAll ((listCons.fields.getD 1 default).type.instL listOcc.lvls) listOcc.args 1)
      = some { binders := [], idx := 1, args := [] } := rfl

/-- **Negative control.**  Delete the head generalisation — present member 1 at the parameter
run instead of at `[NTree α]` — and the second field is no longer recognised, so the built
member loses the recursion. -/
theorem listOcc_recog_field1_fails :
    { ntreeRestore with tyArgs := fun _ => VExpr.bvars 0 1 }.recog ntreeAux.header.nm 1
        (VExpr.instAll ((listCons.fields.getD 1 default).type.instL listOcc.lvls) listOcc.args 1)
      = none := rfl

/-- `ntreeAux` with the companion member's index telescope replaced by a nonsense one. -/
def ntreeAuxI : VInductDecl' :=
  { ntreeAux with
    types :=
      [{ name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
         indices := [], ctors := [ntreeNode] },
       { name := `_nested.List_1,
         type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
         indices := [.sort .zero], ctors := [nlistNil, nlistCons] }] }

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

theorem listOcc_occurs : listOcc.Occurs env₁ where
  hist := ⟨_, _, h, .rfl⟩
  idx_lt := by decide
  lvls_len := rfl
  args_len := rfl
  ty_const := list_const h
  ctor_params := by
    intro C hC
    simp only [show listOcc.src.ctors = [listNil, listCons] from rfl, List.mem_cons,
      List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC <;> rfl
  ctor_const := by
    intro C hC
    simp only [show listOcc.src.ctors = [listNil, listCons] from rfl, List.mem_cons,
      List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · exact listNil_const h
    · exact listCons_const h

/-- **The companion member is built, not supplied.**  This is what replaces
`ntreeRestore_faithful`'s three clauses. -/
theorem ntreeAux_built :
    ntreeAux.Built ntreeRestore ntreeK env₁ (fun _ => listOcc) where
  member := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; rfl
    · simp [ntreeAux] at hT
  occurs := fun _ _ _ _ => listOcc_occurs h
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [ntreeAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [ntreeAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [ntreeAux] at hT
  ctorName_inv := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · simp only [show listOcc.src.ctors = [listNil, listCons] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC
      obtain rfl | rfl := hC <;> rfl
    · simp [ntreeAux] at hT
  own := ntreeRestore_ownId

/-! ### `Built` is strictly stronger than `Faithful`

`VIndRestore.Faithful` never mentions the companion member's *index telescope*: its three
clauses compare stored types and constructor names, and `VInductDecl'.tyAppR` ignores its
`VInductDecl'` argument, so `C.typeR D R j` does not depend on `T.indices` either.  Change the
companion's `indices` and `Faithful` still holds; `Built` does not, because the member is no
longer the one the construction computes.

(`VInductDecl'.WF.types`' `canon` clause does constrain `T.indices` up to defeq, so this is not
by itself a soundness hole — it is the machine-checked demonstration that the strengthening is
real, and it is exactly the kind of slack a *checked* field leaves and a *computed* one does
not.) -/

theorem ntreeAuxI_faithful :
    ntreeRestore.Faithful ntreeAuxI env₁ ntreeK (fun _ => 1) where
  ty_agree := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact ⟨_, list_const h, rfl, rfl⟩
    · simp [ntreeAuxI] at hT
  ctor_agree := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      obtain rfl | rfl := hC
      · exact ⟨_, listNil_const h, rfl, rfl⟩
      · exact ⟨_, listCons_const h, rfl, rfl⟩
    · simp [ntreeAuxI] at hT
  ctors_complete := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact ⟨listDecl, 0, listType, ⟨_, _, h, .rfl⟩, rfl, rfl, rfl, rfl⟩
    · simp [ntreeAuxI] at hT

omit h in
theorem ntreeAuxI_not_built :
    ¬ ntreeAuxI.Built ntreeRestore ntreeK env₁ (fun _ => listOcc) := by
  intro hb
  exact absurd (congrArg VIndType.indices (hb.member 1 _ rfl (by decide))) (by decide)

omit h in
theorem ntreeAux_canonicalOwn : ntreeAux.CanonicalOwn ntreeK :=
  fun j C hjC _ => ntreeAux_Canonical j C hjC

/-- **The step, with the auxiliary member built.**  Same environment extension as
`ntreeAux_AddNested`, but nothing about `_nested.List_1` is asserted: it is computed. -/
theorem ntreeAux_AddNestedB :
    ∃ env₂, VEnv.AddNestedB env₁ ntreeAux ntreeK ntreeRestore
      (fun _ => listOcc) env₂ :=
  ⟨(ntreeAux_admitted h).choose, ntreeAux_WF h, ntreeAux_canonicalOwn, ntreeAux_built h,
    (ntreeAux_admitted h).choose_spec⟩

/-- **The rule's premise is inhabited at a real nested block.**  `VEnv.AddNestedStep`
(`Theory/Inductive/Restore.lean`) is exactly what `VDecl.WF.inductNested` would take
(`Theory/Typing/Env.lean`); this is a model of it at `NTree`/`List`, with the auxiliary
member computed rather than asserted. -/
theorem ntreeAux_AddNestedStep :
    ∃ env₂, VEnv.AddNestedStep env₁ ntreeAux ntreeK ntreeRestore env₂ :=
  let ⟨env₂, hb⟩ := ntreeAux_AddNestedB h
  ⟨env₂, hb.toAddNestedStep⟩

/-- …and it delivers `NestedHead.lean`'s step, `Faithful` included. -/
theorem ntreeAux_AddNested_of_built :
    ∃ env₂, VEnv.AddNested env₁ ntreeAux ntreeK ntreeRestore
      (fun _ => 1) env₂ :=
  let ⟨env₂, hb⟩ := ntreeAux_AddNestedB h
  ⟨env₂, hb.toAddNested⟩

/-- The three clauses `docs/handoff-nested-restore.md` §7.1 named are now consequences. -/
theorem ntreeRestore_faithful_of_built :
    ntreeRestore.Faithful ntreeAux env₁ ntreeK (fun _ => 1) :=
  (ntreeAux_built h).toFaithful

end

/-! ## Part 9: a nested witness with a non-empty `ξ`

`docs/handoff-nested-restore.md` §5's first open item: every recursive field of `ntreeAux` has
`ξ = []`, so `VIndField.WF.binders_indep` is *reached but not exercised*, and **no nested
witness with a non-empty `ξ` existed**.  Here is one.

`PFn α` has a higher-order field `Prop → α`; nesting `PFn` at `NFn` turns that parameter
position into a recursive one, and the recognised `ξ` is `[Prop]`.  The induction hypothesis
Lean generates for it is `(a : Prop) → motive_1 (a_1 a)` — the configuration `Acc` has for an
ordinary block and no nested block had. -/

inductive PFn (α : Type) where
  | mk : α → (Prop → α) → PFn α

/-- The nested declaration.  Lean's own kernel runs the nested elimination on it. -/
inductive NFn where
  | node : PFn NFn → NFn

/-! ### `PFn`, as a block of the declaration history -/

def pfnMk : VIndCtor where
  name := ``PFn.mk
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .bvar 0, lvl := .succ .zero, recArg := none },
     { type := .forallE (.sort .zero) (.bvar 2),
       lvl := .imax (.succ .zero) (.succ .zero), recArg := none }]
  args := []

def pfnType : VIndType where
  name := ``PFn
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  indices := []
  ctors := [pfnMk]

def pfnDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types := [pfnType]

example : pfnType.type = (vconst(type_of% @PFn)).type := rfl
example : pfnMk.type pfnDecl 0 = (vconst(type_of% @PFn.mk)).type := rfl
example : pfnDecl.recType 0 = (vconst(type_of% @PFn.rec)).type := rfl

/-! ### Why `VIndRestore.OwnId` is a conjunct of `VEnv.AddNested`

The configuration `VIndRestore.Faithful` alone admits, at a real block.  `pfnJunkRestore`
presents **`PFn` itself** — the member the step declares, not a companion — as `Nat`, at no
levels and no arguments.  `Faithful` holds of it, because at `K = []` all three of its clauses
are vacuous; `D.WF env` and `D.Canonical`, the other two hypotheses of
`VEnv.addInductR_ordered'`, do not mention `R` at all; and `VEnv.addInductR` succeeds, because
its success is a freshness-and-`Nodup` condition on names, which the junk restoration does not
disturb.  What it declares is `PFn.mk` at a type whose **result** is `Nat`.

So obligation (A) of `VEnv.addInductR_ordered'` is not open at this restoration, it is false,
and no proof from `Faithful` + `D.WF env` could ever have existed.  `VIndRestore.OwnId` is the
missing conjunct and `pfnJunk_not_ownId` is where it bites. -/

def pfnJunkRestore : VIndRestore where
  tyName _ := ``Nat
  tyLvls _ := []
  tyArgs _ := []
  ctorName := id
  recName := id

/-- The declared constructor's result type is `Nat` — not `PFn α`. -/
theorem pfnJunk_ctorConstsCR :
    pfnDecl.ctorConstsCR pfnJunkRestore []
      = [(``PFn.mk, ⟨0, mkPi (pfnMk.params ++ pfnMk.fieldTypesR pfnDecl pfnJunkRestore)
            (.const ``Nat [])⟩)] := rfl

/-- …and for contrast, the real one's is `PFn` applied to the parameter. -/
theorem pfn_idRestore_ctorConstsCR :
    pfnDecl.ctorConstsCR pfnDecl.idRestore []
      = [(``PFn.mk, ⟨0, pfnMk.type pfnDecl 0⟩)] := by
  rw [VInductDecl'.ctorConstsCR]
  show [(id ``PFn.mk, (⟨0, pfnMk.typeR pfnDecl pfnDecl.idRestore 0⟩ : VConstant))] = _
  rw [VIndCtor.typeR_id (by rintro (_ | _ | i) F r hF hr <;> simp [pfnMk] at hF ⊢ <;>
    (try subst hF) <;> simp_all)]
  rfl

/-- The step is admitted at the junk restoration: `addInductR` cannot see the difference. -/
theorem pfnJunk_admitted :
    ∃ env, VEnv.empty.addInductR pfnDecl [] pfnJunkRestore = some env := ⟨_, rfl⟩

theorem pfnJunk_not_ownId : ¬ pfnJunkRestore.OwnId pfnDecl [] := by
  intro h
  have := h.tyName 0 pfnType rfl (by decide)
  exact absurd this (by decide)

/-- **The junk restoration passes every `R`-dependent hypothesis `Faithful` offers.**  The
three conjuncts are, in order: `Faithful`; the step succeeds; and `OwnId` — the only one that
excludes it. -/
theorem pfnJunk_would_have_passed (npJ : Nat → Nat) :
    pfnJunkRestore.Faithful pfnDecl VEnv.empty [] npJ ∧
      (∃ env, VEnv.empty.addInductR pfnDecl [] pfnJunkRestore = some env) ∧
      ¬ pfnJunkRestore.OwnId pfnDecl [] :=
  ⟨VIndRestore.faithful_of_nil .., pfnJunk_admitted, pfnJunk_not_ownId⟩

/-! ### The nested occurrence and the auxiliary block -/

def pfnOcc : VNestedOcc where
  decl := pfnDecl
  idx := 0
  lvls := []
  args := [.const ``NFn []]
  auxName := `_nested.PFn_1
  ctorName n := if n = ``PFn.mk then `_nested.PFn_1.mk else n

def nfnRestore : VIndRestore where
  tyName j := if j = 1 then ``PFn else ``NFn
  tyLvls _ := []
  tyArgs j := if j = 1 then [.const ``NFn []] else []
  ctorName n := if n = `_nested.PFn_1.mk then ``PFn.mk else n
  recName n := if n = `_nested.PFn_1.rec then ``NFn.rec_1 else n

def nfnNode : VIndCtor where
  name := ``NFn.node
  params := []
  fields := [{ type := .const `_nested.PFn_1 [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

/-- The auxiliary constructor, written out — **and checked against the construction** by
`nfnAux_member_built`.  Its second field is recursive with `ξ = [Prop]`. -/
def pfnAuxMk : VIndCtor where
  name := `_nested.PFn_1.mk
  params := []
  fields :=
    [{ type := .const ``NFn [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [] } },
     { type := .forallE (.sort .zero) (.const ``NFn []),
       lvl := .imax (.succ .zero) (.succ .zero),
       recArg := some { binders := [.sort .zero], idx := 0, args := [] } }]
  args := []

def nfnAux : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``NFn, type := .sort (.succ .zero), indices := [], ctors := [nfnNode] },
     { name := `_nested.PFn_1, type := .sort (.succ .zero), indices := [],
       ctors := [pfnAuxMk] }]

def nfnK : List Lean.Name := [`_nested.PFn_1]

/-- **`VIndRestore.OwnId` at the second witness.**  `NFn` — the member the step declares — is
renamed to nothing, re-levelled to nothing and re-instantiated at nothing; only
`_nested.PFn_1` moves. -/
theorem nfnRestore_ownId : nfnRestore.OwnId nfnAux nfnK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAux] at hT


/-- The auxiliary member is the constructed one — including the `ξ = [Prop]` binder telescope,
which the recogniser reads off the substituted type. -/
theorem nfnAux_member_built :
    nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore) := rfl

/-- **The witness the handoff asks for**: a nested block with a recursive field whose binder
telescope is non-empty. -/
theorem pfnAuxMk_xi_nonempty :
    ∃ r, (pfnAuxMk.fields.getD 1 default).recArg = some r ∧ r.binders ≠ [] :=
  ⟨_, rfl, by decide⟩

/-! ### …checked against Lean's own kernel -/

example : nfnNode.typeR nfnAux nfnRestore 0 = (vconst(type_of% @NFn.node)).type := rfl
example : nfnAux.recTypeR nfnRestore 0 = (vconst(type_of% @NFn.rec)).type := rfl
example : nfnAux.recTypeR nfnRestore 1 = (vconst(type_of% @NFn.rec_1)).type := rfl
example : nfnAux.iotaLamR nfnRestore 0 nfnNode = vrecrule(NFn.rec, 0) := rfl
example : nfnAux.iotaLamR nfnRestore 1 pfnAuxMk = vrecrule(NFn.rec_1, 0) := rfl

/-! ### `SrcIndep`, `BindersIndep`, and non-vacuity -/

/-- `PFn.mk`'s second field does not mention its first — the syntactic condition the
substitution transports. -/
theorem pfnOcc_srcIndep : pfnOcc.SrcIndep nfnAux.header nfnRestore pfnMk := by
  intro i i' t F F' hF hF' _ hti
  match i, hF with
  | 0, hF => omega
  | 1, hF =>
    obtain ⟨rfl, rfl⟩ : i' = 0 ∧ t = 0 := by omega
    simp only [pfnMk, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hF
    subst hF
    exact rfl
  | (n+2), hF => simp [pfnMk] at hF

theorem pfnAuxMk_fields :
    pfnAuxMk.fields = pfnOcc.fieldsFrom nfnAux.header nfnRestore 0 pfnMk.fields := rfl

/-- **`BindersIndep` for the built constructor, as a theorem** — via
`VNestedOcc.bindersIndep`, not by emptiness. -/
theorem pfnAuxMk_bindersIndep (i : Nat) (F : VIndField) (r : VIndRecArg)
    (hF : pfnAuxMk.fields[i]? = some F) (hr : F.recArg = some r) :
    r.BindersIndep (pfnAuxMk.fields.take i) i := by
  rw [pfnAuxMk_fields] at hF ⊢
  exact pfnOcc.bindersIndep nfnAux.header nfnRestore pfnMk pfnOcc_srcIndep i F r hF hr

/-- **…and it is not vacuous.**  At field 1 the clause's premise is inhabited: there *is* an
earlier field (`i' = 0`), it *is* recursive, and `ξ` *is* non-empty — the three conditions no
witness before this one met simultaneously. -/
theorem pfnAuxMk_bindersIndep_nonvacuous :
    ∃ (i i' t k : Nat) (F' : VIndField) (r : VIndRecArg) (B : VExpr),
      (pfnAuxMk.fields.take i)[i']? = some F' ∧ F'.recArg.isSome = true ∧ i' + 1 + t = i ∧
        pfnAuxMk.fields[i]?.bind (·.recArg) = some r ∧ r.binders[k]? = some B :=
  ⟨1, 0, 0, 0, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-- For contrast: **every** recursive field of `ntreeAux` has `ξ = []`, which is why
`ntreeAux_binders_indep` discharges the clause by emptiness.  That is the gap this witness
closes. -/
theorem ntreeAux_binders_all_nil :
    ∀ p ∈ ntreeAux.ctorsAll, ∀ F ∈ p.2.fields, (F.recArg.map (·.binders)).getD [] = [] := by
  decide

theorem pfnAuxMk_binders_not_nil :
    ((pfnAuxMk.fields.getD 1 default).recArg.map (·.binders)).getD []
      = [VExpr.sort .zero] := rfl

/-! ### The auxiliary block is well-formed, with `binders_indep` doing work

This is `ntreeAux_WF`'s counterpart at the harder configuration.  Field 1 of
`_nested.PFn_1.mk` is recursive with `ξ = [Prop]` **and** follows a recursive field, so
`VIndField.WF.binders_indep` is discharged by `pfnAuxMk_bindersIndep` — i.e. by the
substitution theorem — rather than by emptiness. -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

theorem pfn_const : env₂.constants ``PFn = some ⟨0, pfnType.type⟩ :=
  VEnv.addInduct'_types h (List.Mem.head _)

theorem pfnMk_const : env₂.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.head _)

omit h in
theorem nfn_const_staged {env₃ : VEnv} (hs : env₂.addIndTypes nfnAux = some env₃) :
    env₃.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (``NFn, ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

omit h in
theorem pfnaux_const_staged {env₃ : VEnv} (hs : env₂.addIndTypes nfnAux = some env₃) :
    env₃.constants `_nested.PFn_1 = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (`_nested.PFn_1, ⟨0, .sort (.succ .zero)⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

omit h in
/-- The auxiliary block is well-formed — in *any* environment, since it has no parameters and
its field types mention only block constants and `Prop`. -/
theorem nfnAux_WF : nfnAux.WF env₂ where
  types_ne := by simp [nfnAux]
  params := trivial
  types := by
    intro T hT
    simp only [nfnAux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := trivial, isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₃ hs j T hT C hC
    have hn := nfn_const_staged hs
    have hp := pfnaux_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [nfnAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [nfnNode, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, nfnAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | (_ + 1), hF => simp [nfnNode] at hF
    | 1, hT =>
      simp only [nfnAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [pfnAuxMk, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, nfnAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | 1, hF =>
        simp only [pfnAuxMk, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by
                  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_ <;>
                    type_tac
                level := fun ls => by simp [VLevel.eval, nfnAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; exact pfnAuxMk_bindersIndep 1 _ _ rfl rfl
                pos := ⟨by decide, rfl,
                        by rintro B hB; simp at hB; subst hB; trivial, nofun,
                        ⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | (_ + 2), hF => simp [pfnAuxMk] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, nfnAux])

/-! ### …and the step goes through -/

theorem pfnOcc_occurs : pfnOcc.Occurs env₂ where
  hist := ⟨_, _, h, .rfl⟩
  idx_lt := by decide
  lvls_len := rfl
  args_len := rfl
  ty_const := pfn_const h
  ctor_params := by
    intro C hC
    simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; rfl
  ctor_const := by
    intro C hC
    simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; exact pfnMk_const h

theorem nfnAux_built :
    nfnAux.Built nfnRestore nfnK env₂ (fun _ => pfnOcc) where
  member := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; rfl
    · simp [nfnAux] at hT
  occurs := fun _ _ _ _ => pfnOcc_occurs h
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAux] at hT
  ctorName_inv := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · simp [nfnAux] at hT
  own := nfnRestore_ownId

omit h in
theorem nfnAux_canonicalOwn : nfnAux.CanonicalOwn nfnK := by
  intro j C hjC _
  rw [show nfnAux.ctorsAll = [((0 : Nat), nfnNode), (1, pfnAuxMk)] from rfl] at hjC
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hjC
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hjC
  · intro i F r hF hr
    match i, hF with
    | 0, hF => simp only [nfnNode] at hF; cases hF; cases hr; rfl
    | (_ + 1), hF => simp [nfnNode] at hF
  · exact (pfnOcc.member_Canonical nfnRestore nfnAux _
      (by rw [show (pfnOcc.member nfnAux.header nfnRestore).ctors = [pfnAuxMk] from rfl]
          exact List.Mem.head _))

omit h in
theorem nfnAux_allNamesCR : nfnAux.allNamesCR nfnRestore nfnK =
    [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1] := rfl

theorem nfn_fresh (n : Lean.Name)
    (hn : n ∈ [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1]) : env₂.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem nfnAux_admitted :
    ∃ env₃, env₂.addInductR nfnAux nfnK nfnRestore = some env₃ := by
  refine VEnv.addInductR_eq_some_iff.2 ⟨?_, ?_⟩ <;> rw [nfnAux_allNamesCR]
  · intro n hn; exact nfn_fresh h n hn
  · decide

/-- **The second end-to-end nested witness**, at the configuration `ntreeAux` could not
reach: a recursive field with a non-empty binder telescope. -/
theorem nfnAux_AddNestedB :
    ∃ env₃, VEnv.AddNestedB env₂ nfnAux nfnK nfnRestore
      (fun _ => pfnOcc) env₃ :=
  ⟨(nfnAux_admitted h).choose, nfnAux_WF, nfnAux_canonicalOwn, nfnAux_built h,
    (nfnAux_admitted h).choose_spec⟩

/-- The same at `NFn`/`PFn`, the block `Verify/Environment/InductR.lean`'s constant-map
witness uses — so the abstract step and the constant-map step have a model at *one* block. -/
theorem nfnAux_AddNestedStep :
    ∃ env₃, VEnv.AddNestedStep env₂ nfnAux nfnK nfnRestore env₃ :=
  let ⟨env₃, hb⟩ := nfnAux_AddNestedB h
  ⟨env₃, hb.toAddNestedStep⟩

/-- **`DeltaUnique`'s freshness argument fails here, concretely.**
`Theory/Typing/DeltaUnique.lean`'s `keys_induct` proves the `induct` arm of `VEnv.WF'.keys`
from "every name in a new rule's key is absent from `env`".  The companion's ι-rule is keyed
`[NFn.rec_1, PFn.mk]`, and `PFn.mk` is a constant `env₂` **already holds** — it is `PFn`'s own
constructor, which the previous declaration step declared.  So the nested arm has to argue
from the freshness of the key's *head* alone.  See
`VEnv.iotaRulesR_major_not_fresh` (`Theory/Inductive/NestedOrdered.lean`) for the general
statement; this is the model of it. -/
theorem nfn_companion_key_not_fresh :
    ∃ df ∈ nfnAux.iotaRulesR nfnRestore, ∃ n ∈ df.key, env₂.contains n := by
  refine ⟨nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk, ?_, ``PFn.mk, ?_, _, pfnMk_const h⟩
  · rw [VInductDecl'.iotaRulesR]
    exact List.mem_map.2 ⟨((1, pfnAuxMk), 1), show _ ∈ [((0, nfnNode), 0), ((1, pfnAuxMk), 1)] from List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · rw [nfnAux.key_iotaRuleR nfnRestore 1 1 pfnAuxMk]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem nfnAux_AddNested :
    ∃ env₃, VEnv.AddNested env₂ nfnAux nfnK nfnRestore
      (fun _ => 1) env₃ :=
  let ⟨env₃, hb⟩ := nfnAux_AddNestedB h
  ⟨env₃, hb.toAddNested⟩

end

/-! ## Part 10: regression

Everything `docs/handoff-nested-restore.md` §4 lists, re-elaborated here, so that a change
breaking any of it breaks this file too.  Nothing in `NestedHead.lean` or
`CompanionResolve.lean` was edited to make this file go through. -/

example := @ntreeAux_WF
example := @ntreeAux_Canonical
example := @ntreeRestore_faithful
example := @ntreeAux_admitted
example := @ntreeAux_AddNested
example := @ntreeAux_recs_declared
example := @ntreeNode_typeR
example := @ntreeAux_recTypeR_0
example := @ntreeAux_recTypeR_1
example := @ntreeAux_iotaLamR_0
example := @ntreeAux_iotaLamR_1
example := @ntreeAux_iotaLamR_2
example := @ntreeAux_allNamesCR
example := @ntreeAux_keys_declared
example := @ntreeAux_iotaRule_key_not_declared
example := @ntreeAux_resolveC_none
example := @ntreeAuxL_resolveC_loses_recursion
example := @ntreeAux_CompanionShape_vacuous
example := @ntreeAux_not_CompanionComplete
example := @ntreeAux_not_CompanionSound
example := @ntreeAux_staging
example := @fooComp_inconsistent
example := @fooComp_killed
example := @VEnv.AddNested_nil
example := @VEnv.AddNested_keys_declared

end InductiveDeclExamples

end Lean4Lean
