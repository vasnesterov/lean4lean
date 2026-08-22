import Lean4Lean.Theory.Inductive.Telescope
import Lean4Lean.Theory.Typing.Lemmas

/-!
# The abstract specification of inductive types

This is the *data* half of the inductive keystone: the structured inductive declaration
record `VInductDecl'`, its well-formedness predicate `VInductDecl'.WF`, and the
environment extension `VEnv.addInduct'` (recursor types and ι-rules included).

It follows `docs/design-inductive.md` §2–§5.  The metatheory (`addInduct_WF`, the
`Params` instance, `TrProj`, …) is deliberately *not* here.

## Why a structured record

The kernel builds the recursor from the **whnf-normalised** telescopes it walked while
checking (`Lean4Lean/Inductive/Add.lean`, `checkInductiveTypes`), and those are not
recoverable from the stored closed types.  Likewise the classification of a constructor
field as recursive/non-recursive, together with its `ξ`-binders and `π`-indices, is
computed by `checkPositivity`/`isRecArg` and is an input to both the minor premises and
the ι-rules.  So the declaration record carries the decomposition, with the *surface*
types kept alongside and tied to the canonical ones by `IsDefEqU`
(`VIndType.WF.canon`).

## Conventions

Telescopes are stored in **declaration order** (outermost binder first); the
corresponding typing context (`Lookup`/`OnCtx`, innermost-first) is `.reverse`.
All the de Bruijn arithmetic is the `mkPi`/`mkLams`/`mkApp`/`bvars`/`liftTele`/`shift`
algebra of `Lean4Lean/Theory/Inductive/Telescope.lean`.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams bvars liftTele shift shiftTele)

/-! ## Occurrence check -/

namespace VExpr

/-- `e` mentions none of the constants in `S`.  This is the abstract counterpart of the
kernel's `hasIndOcc` (`Add.lean:118`), used for both the strict-positivity condition (F7)
and the freshness of a constructor's result indices (F5). -/
def NoConsts (S : List Name) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _ => c ∉ S
  | .app a b | .lam a b | .forallE a b => NoConsts S a ∧ NoConsts S b

end VExpr

/-! ## The declaration record (design §2.2) -/

/-- Data of a *recursive* constructor field, i.e. one whose type is definitionally
`∀ ξ, I_idx params π`.  This is what `isRecArg` (`Add.lean:173`) computes. -/
structure VIndRecArg where
  /-- `ξ`, in declaration order, over `params ++ fields<i`.  Contains no block constant. -/
  binders : List VExpr
  /-- Which type of the block this field recurses into. -/
  idx : Nat
  /-- `π`, the index arguments, over `params ++ fields<i ++ ξ`.  No block constant. -/
  args : List VExpr
  deriving Inhabited

/-- One constructor field, living in the context `params ++ fields<i`. -/
structure VIndField where
  /-- The field's type, exactly as it appears in the constructor's type (F2). -/
  type : VExpr
  /-- A level with `⊢ type : Sort lvl`.  Sorts are not unique in the abstract theory
  (`IsDefEqU.sort_inv` is open), so the witness is *recorded*, not derived. -/
  lvl : VLevel
  /-- `none` for a non-recursive field; `some r` when `type` is definitionally
  `mkPi r.binders (I_{r.idx} params r.args)`.

  (The design document calls this field `rec`; that name is taken by the structure's
  own recursor `VIndField.rec`, so it is spelled `recArg` here.) -/
  recArg : Option VIndRecArg
  deriving Inhabited

structure VIndCtor where
  name : Name
  /-- The constructor's own parameter binder types (F3): `nparams` of them, pairwise
  definitionally equal to the block's `params` but not necessarily syntactically equal. -/
  params : List VExpr
  /-- The fields, in declaration order, over the block's `params`. -/
  fields : List VIndField
  /-- The index arguments of the result, over `params ++ fields`.  No block constant (F5). -/
  args : List VExpr
  deriving Inhabited

structure VIndType where
  name : Name
  /-- The type **as stored in the environment**.  Only definitionally a pi-telescope (F1). -/
  type : VExpr
  /-- The index telescope, in declaration order, over the block's `params`. -/
  indices : List VExpr
  ctors : List VIndCtor
  deriving Inhabited

/-- A (mutual) inductive declaration, in the decomposed form the recursor construction
needs.  The primed name is temporary: wiring this into `VDecl.induct` in place of the
current `VInductDecl` is a separate step. -/
structure VInductDecl' where
  uvars : Nat
  /-- The parameter telescope, in declaration order.  `nparams = params.length`. -/
  params : List VExpr
  /-- The common result universe of the block.  F4 gives only `isEquiv`, and that slack
  is absorbed into `VIndType.WF.canon`. -/
  lvl : VLevel
  types : List VIndType
  /-- Whether the recursor eliminates into an arbitrary universe (F9/F10).  A *claim*:
  `WF` only constrains it in the `true` direction, so it need not be decidable. -/
  isLE : Bool
  deriving Inhabited

/-! ## Derived accessors (design §2.3) -/

namespace VInductDecl'
variable (D : VInductDecl')

/-- Number of parameters. -/
abbrev np : Nat := D.params.length
/-- Number of types in the block (= number of motives). -/
abbrev nm : Nat := D.types.length

/-- All constructors of the block in kernel order, tagged with their type's index (F12).
The `q`-th entry of this list is the constructor of the `q`-th minor premise. -/
def ctorsAll : List (Nat × VIndCtor) :=
  D.types.zipIdx.flatMap fun (T, j) => T.ctors.map fun C => (j, C)

/-- Number of minor premises. -/
abbrev nmin : Nat := D.ctorsAll.length

def blockNames : List Name := D.types.map (·.name)


/-- The elimination universe (F10): a *fresh* parameter prepended at index 0 for a large
eliminator, `.zero` otherwise. -/
def elimLvl : VLevel := if D.isLE then .param 0 else .zero

/-- The recursor's universe-parameter count (F10). -/
def recUvars : Nat := if D.isLE then D.uvars + 1 else D.uvars

/-- The block's own universe parameters in its own numbering. -/
def ownLvls : List VLevel := VLevel.params D.uvars

/-- The same, in the *recursor's* numbering (shifted by one when `isLE`). -/
def selfLvls : List VLevel :=
  (List.range D.uvars).map fun i => .param (if D.isLE then i + 1 else i)

/-- `e` contains no constant of the block being declared. -/
def NoBlock (e : VExpr) : Prop := e.NoConsts D.blockNames

/-- Re-index a term stored at the block's **own** universe numbering (`ownLvls`) into the
**recursor's** numbering (`selfLvls`).

This is needed because `recType`/`minorType`/`iotaLhs` splice stored telescopes — the
parameters, the indices, the constructor's field types and result indices, a recursive
field's `ξ`/`π` — into terms built at the recursor's levels, where a fresh elimination
universe has been prepended at index 0 (F10).  The C++ kernel does not need this step
because its universe parameters are *names*, not de Bruijn indices; it is an artifact of
the `VLevel` encoding.  When `isLE = false` this is the identity on well-formed terms
(`VLevel.inst_id`). -/
def atRec (e : VExpr) : VExpr := e.instL D.selfLvls

/-- `atRec` entrywise on a telescope. -/
def atRecTele (As : List VExpr) : List VExpr := As.map (·.instL D.selfLvls)

/-! ### Canonical applications -/

/-- `I_j` at the block's own levels, applied to the parameters (which sit `k` binders
away, i.e. occupy de Bruijn indices `k … k+np-1`) and then to `args`. -/
def tyApp (j k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (D.types.getD j default).name D.ownLvls).mkApp (bvars k D.np ++ args)

/-- The same at the *recursor's* level numbering; used inside recursor types and ι-rules. -/
def tyApp' (j k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (D.types.getD j default).name D.selfLvls).mkApp (bvars k D.np ++ args)

/-- A constructor applied to the parameters (at `k`) and to `args`, at the recursor's
level numbering. -/
def ctorApp' (C : VIndCtor) (k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const C.name D.selfLvls).mkApp (bvars k D.np ++ args)

end VInductDecl'

/-! ## Canonical types (design §3) -/

/-- Canonical type of an inductive type of the block: `∀ params indices, Sort lvl`.
By F1 the *stored* `T.type` is only definitionally this. -/
def VIndType.canonType (T : VIndType) (D : VInductDecl') : VExpr :=
  mkPi (D.params ++ T.indices) (.sort D.lvl)

/-- The result of a recursive field, `I_{r.idx} params π`, in the context
`ξ.reverse ++ (fields<i).reverse ++ params.reverse`. -/
def VIndRecArg.canonResult (r : VIndRecArg) (D : VInductDecl') (i : Nat) : VExpr :=
  D.tyApp r.idx (r.binders.length + i) r.args

/-- The canonical type of a recursive field, `∀ ξ, I_{r.idx} params π`. -/
def VIndRecArg.canonType (r : VIndRecArg) (D : VInductDecl') (i : Nat) : VExpr :=
  mkPi r.binders (r.canonResult D i)

/-- Result type of a constructor, over `params ++ fields`. -/
def VIndCtor.canonResult (C : VIndCtor) (D : VInductDecl') (j : Nat) : VExpr :=
  D.tyApp j C.fields.length C.args

/-- Type of a constructor, exactly as stored in the environment.  Unlike `VIndType.type`
this is *derived*: by F2 the kernel walks a constructor's pi-spine without `whnf`, so the
stored type is this telescope on the nose. -/
def VIndCtor.type (C : VIndCtor) (D : VInductDecl') (j : Nat) : VExpr :=
  mkPi (C.params ++ C.fields.map (·.type)) (C.canonResult D j)

/-- The recursive fields of a constructor, as `(declaration index, data)` pairs, in
declaration order. -/
def VIndCtor.recFields (C : VIndCtor) : List (Nat × VIndRecArg) :=
  C.fields.zipIdx.filterMap fun (F, i) => F.recArg.map fun r => (i, r)

/-! ## Staged environments (design §4)

The kernel checks constructors in an environment that already contains the block's type
constants (`Add.lean:458`), and a constructor's type mentions them.  So `WF` stages the
environment, mirroring `declareInductiveTypes` / `checkConstructors`. -/

/-- The block's type constants, in declaration order. -/
def VInductDecl'.typeConsts (D : VInductDecl') : List (Name × VConstant) :=
  D.types.map fun T => (T.name, ⟨D.uvars, T.type⟩)

/-- The block's constructor constants, in kernel order (grouped by type). -/
def VInductDecl'.ctorConsts (D : VInductDecl') : List (Name × VConstant) :=
  D.ctorsAll.map fun (j, C) => (C.name, ⟨D.uvars, C.type D j⟩)

/-- Add a list of named constants left to right.  `none` as soon as one name is already
taken, so success implies every name is fresh *and* the list has no duplicates. -/
def VEnv.addConstList (env : VEnv) (cs : List (Name × VConstant)) : Option VEnv :=
  cs.foldlM (fun env c => env.addConst c.1 c.2) env

/-- Add only the block's type constants. -/
def VEnv.addIndTypes (env : VEnv) (D : VInductDecl') : Option VEnv :=
  env.addConstList D.typeConsts

/-- Add the block's constructors, on top of `addIndTypes`. -/
def VEnv.addIndCtors (env : VEnv) (D : VInductDecl') : Option VEnv :=
  env.addConstList D.ctorConsts

/-! ## Well-formedness (design §4) -/

/-- `as` is a well-typed instantiation of the declaration-order telescope `As`: each `aᵢ`
is typed at `Aᵢ` with the earlier arguments already substituted.  This is the hypothesis
shape of `HasType.mkApp'` ("apply a function of `mkPi` type to a whole spine"). -/
inductive VEnv.HasArgs (env : VEnv) (U : Nat) (Γ : List VExpr) : List VExpr → List VExpr → Prop
  | nil : HasArgs env U Γ [] []
  | cons {A As a as} :
    env.HasType U Γ a A → HasArgs env U Γ (VExpr.instTele a As) as →
    HasArgs env U Γ (A :: As) (a :: as)

/-- `IsDefEqU` refined to say the two sides are equal **as types**.

Stronger than `IsDefEqU`, and it is what the refinement naturally produces: the kernel
walks a pi-spine with `whnf` and `ensureSort`, and each step is a `forallEDF`/`sortDF`
congruence, all of which are typed at a sort.  Going back from `IsDefEqU` would need
`IsDefEqU.of_l`, which lives in `Typing/UniqueTyping.lean` -- downstream of the
injectivity stream and of `VEnv.WF`, hence of `addInduct_WF` itself.  Recording the sort
here keeps the inductive spec out of that cycle. -/
def VEnv.IsDefEqType (env : VEnv) (U : Nat) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∃ u, env.IsDefEq U Γ A B (.sort u)


/-- Well-formedness of one constructor field.  `Γ` is
`((C.fields.take i).map (·.type)).reverse ++ D.params.reverse`, the context of field `i`. -/
structure VIndField.WF (env : VEnv) (D : VInductDecl') (Γ : List VExpr) (i : Nat)
    (F : VIndField) : Prop where
  /-- The recorded sort really is a sort of the field's type. -/
  hasType : env.HasType D.uvars Γ F.type (.sort F.lvl)
  /-- Carneiro's level constraint.  The kernel checks the strictly stronger
  `ℓ ≈ 0 ∨ ℓ' ≤ ℓ` (F6, `Add.lean:226`); that implies this one, so refinement goes
  through and the spec is not hostage to the kernel's level-algebra incompleteness.
  See `divergences.md` (the `imax 1 u ≤ u` entry). -/
  level : VLevel.imax F.lvl D.lvl ≤ D.lvl
  /-- Strict positivity (F7).  A field is *either* free of the block's constants *or*
  strictly of the shape `∀ ξ, I_j params π` with `ξ` and `π` themselves block-free. -/
  pos :
    match F.recArg with
    | none =>
      -- **Only definitionally** block-free: `checkPositivity` (`Add.lean:190`) applies
      -- `hasIndOcc` to `whnf dom`, not to `dom`.  Both kernels accept
      -- `| mk : (r : T) -> (fun _ : T => Nat) r -> T`, whose stored field type mentions
      -- both the block constant and the earlier recursive field `r`; only its whnf is
      -- block-free.  A syntactic `D.NoBlock F.type` here would reject it.
      ∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A
    | some r =>
      r.idx < D.nm ∧
      r.args.length = (D.types.getD r.idx default).indices.length ∧
      (∀ B ∈ r.binders, D.NoBlock B) ∧
      (∀ a ∈ r.args, D.NoBlock a) ∧
      OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars) ∧
      env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl) ∧
      -- The index arguments are well-typed against `I_{r.idx}`'s index telescope, moved
      -- into `ξ.reverse ++ Γ` (where the parameters sit `|ξ| + i` binders up, which is
      -- exactly where `bvars (|ξ|+i) np` points).  **Recorded, not derived**: extracting
      -- it from the well-typedness of `I p π` is application inversion, and while
      -- `HasType.app_inv` is available (`Typing/Strong.lean`), pinning the existential
      -- domain it returns to the declared index telescope needs `IsDefEqU.forallE_inv`
      -- (`Typing/Injectivity.lean`, `sorry`, and downstream of `VEnv.WF` hence of
      -- `addInduct_WF`).  The refinement supplies it for free: `inferType` on an
      -- application checks each argument against the domain.
      --
      -- NOTE (`docs/model-interface.md` §2): the `none` branch below must stay
      -- *definitional*.  Weakening it to a syntactic `D.NoBlock F.type` would both reject
      -- declarations both kernels accept (see the comment there) and break the model's
      -- argument that `Fld : V → V` is independent of the family being constructed, which
      -- goes through defeq-invariance of the interpretation.
      (∀ T', D.types[r.idx]? = some T' →
        env.HasArgs D.uvars (r.binders.reverse ++ Γ)
          (liftTele (r.binders.length + i) T'.indices) r.args) ∧
      env.IsDefEqType D.uvars Γ F.type (r.canonType D i)

/-- Well-formedness of one constructor, stated in the environment that already contains
the block's *type* constants. -/
structure VIndCtor.WF (env : VEnv) (D : VInductDecl') (j : Nat) (T : VIndType)
    (C : VIndCtor) : Prop where
  /-- F3: the constructor's own parameter binders are a definitionally equal copy of the
  block's. -/
  params_len : C.params.length = D.np
  params_eq : VEnv.IsDefEqCtx env D.uvars [] C.params.reverse D.params.reverse
  /-- Every field is well-formed in its own context. -/
  fields : ∀ i (F : VIndField), C.fields[i]? = some F →
    F.WF env D (((C.fields.take i).map (·.type)).reverse ++ D.params.reverse) i
  /-- F5: the result is an application of `I_j` to the parameters and `args`… -/
  args_len : C.args.length = T.indices.length
  /-- …with the non-parameter arguments free of the block's constants… -/
  args_fresh : ∀ a ∈ C.args, D.NoBlock a
  /-- …and well-typed against `I_j`'s index telescope, moved into the field context (where
  the parameters sit `nf` binders up).  Recorded for the same reason as
  `VIndField.WF.pos`'s clause. -/
  args_ty : env.HasArgs D.uvars ((C.fields.map (·.type)).reverse ++ D.params.reverse)
    (liftTele C.fields.length T.indices) C.args
  /-- The result type is a type; this also delivers well-typedness of `C.args`. -/
  result : env.HasType D.uvars ((C.fields.map (·.type)).reverse ++ D.params.reverse)
    (C.canonResult D j) (.sort D.lvl)

/-- Well-formedness of one type of the block, in the *original* environment. -/
structure VIndType.WF (env : VEnv) (D : VInductDecl') (T : VIndType) : Prop where
  indices : OnCtx (T.indices.reverse ++ D.params.reverse) (env.IsType D.uvars)
  isType : env.IsType D.uvars [] T.type
  /-- F1/F4: the stored type is only *definitionally* the canonical pi-telescope, because
  the kernel whnfs at every spine step; and the block's common `lvl` need only be
  `isEquiv` to each type's result level. -/
  canon : env.IsDefEqType D.uvars [] T.type (T.canonType D)

/-- Carneiro's `Γ; t : F ⊢ K LE`, in the form F9 (`isLargeEliminator`, `Add.lean:258`)
delivers it.  Purely syntactic/level-theoretic: no environment appears.

In the one-constructor case, field `i` (declaration order) is `.bvar (nf-1-i)` in the
context `fields.reverse ++ params.reverse`, and `C.args` lives there, so
`.bvar (nf-1-i) ∈ C.args` is exactly the kernel's `type.getAppArgs.contains arg` — a
field variable can never be one of the `nparams` leading parameter arguments, which is
why only `args` is scanned. -/
def VInductDecl'.LECond (D : VInductDecl') : Prop :=
  D.lvl.IsNeverZero ∨
  ∃ T, D.types = [T] ∧
    (T.ctors = [] ∨
     ∃ C, T.ctors = [C] ∧
       ∀ i (F : VIndField), C.fields[i]? = some F →
         F.lvl ≈ VLevel.zero ∨ VExpr.bvar (C.fields.length - 1 - i) ∈ C.args)

/-- Well-formedness of a whole inductive declaration.

Note what is *not* here: well-formedness of the recursor types and ι-rules is a
**theorem** (`addInduct_WF`), not a hypothesis; and neither K-like reduction nor
structure eta contributes a side condition (design §6). -/
structure VInductDecl'.WF (env : VEnv) (D : VInductDecl') : Prop where
  types_ne : D.types ≠ []
  params : OnCtx D.params.reverse (env.IsType D.uvars)
  types : ∀ T ∈ D.types, T.WF env D
  /-- Constructors are checked in the environment extended by the block's types. -/
  ctors : ∀ env₁, env.addIndTypes D = some env₁ →
    ∀ j (T : VIndType), D.types[j]? = some T →
      ∀ (C : VIndCtor), C ∈ T.ctors → C.WF env₁ D j T
  isLE : D.isLE = true → D.LECond

/-! ## The environment extension (design §5) -/

namespace VInductDecl'
variable (D : VInductDecl')

/-! ### Motives

Motive `t` lives over `params ++ motives<t`, so `t` binders sit between it and the
parameters. -/

def motiveType (t : Nat) : VExpr :=
  let T := D.types.getD t default
  let ni := T.indices.length
  mkPi (liftTele t (D.atRecTele T.indices)) <|
    .forallE (D.tyApp' t (ni + t) (bvars 0 ni)) (.sort D.elimLvl)

def motives : List VExpr := (List.range D.nm).map D.motiveType

/-! ### Minor premises

Minor `q` — the `q`-th entry `(t, C)` of `ctorsAll` — lives over
`params ++ motives ++ minors<q`, so `off := nm + q` binders separate its fields from the
parameters.  This is `mkRecInfos.loopCtors`/`loopU` (`Add.lean:379–393`) transcribed. -/

/-- One entry of `ihTypes`: the induction hypothesis for the recursive field at declaration
position `i`, which is the `s`-th recursive field of `C`.

`d` counts the binders sitting below `fields<i`: the remaining fields `i…nf-1` plus the
`s` induction hypotheses already introduced. -/
def ihType (q : Nat) (C : VIndCtor) (i : Nat) (r : VIndRecArg) (s : Nat) : VExpr :=
  let off := D.nm + q
  let nf := C.fields.length
  let d := nf - i + s
  let nxi := r.binders.length
  mkPi (shiftTele off d i (D.atRecTele r.binders)) <|
    (VExpr.bvar (nxi + s + nf + q + (D.nm - 1 - r.idx))).mkApp <|
      -- `r.args` are not a telescope: they all live in the same context, one `ξ`-scope
      -- deep, so the inner-binder count is `nxi` for every one of them.
      r.args.map (fun a => shift off d i (D.atRec a) nxi) ++
      [(VExpr.bvar (nxi + s + (nf - 1 - i))).mkApp (bvars 0 nxi)]

/-- The induction-hypothesis telescope of minor `q` (F14's `δ`), in declaration order,
over `params ++ motives ++ minors<q ++ fields`. -/
def ihTypes (q : Nat) (C : VIndCtor) : List VExpr :=
  C.recFields.zipIdx.map fun ((i, r), s) => D.ihType q C i r s

def minorType (q t : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + q
  let nf := C.fields.length
  let V := D.ihTypes q C
  let nr := V.length
  mkPi (liftTele off (D.atRecTele (C.fields.map (·.type))) ++ V) <|
    (VExpr.bvar (nr + nf + q + (D.nm - 1 - t))).mkApp <|
      C.args.map (fun a => shift off nr nf (D.atRec a)) ++
      [D.ctorApp' C (nr + nf + off) (bvars nr nf)]

def minors : List VExpr := D.ctorsAll.zipIdx.map fun ((t, C), q) => D.minorType q t C

/-! ### The recursor type (F11) -/

/-- `∀ params motives minors indices (major), motive_j indices major`. -/
def recType (j : Nat) : VExpr :=
  let T := D.types.getD j default
  let ni := T.indices.length
  mkPi (D.atRecTele D.params ++ D.motives ++ D.minors ++
        liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) <|
    .forallE (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)) <|
      (VExpr.bvar (1 + ni + D.nmin + (D.nm - 1 - j))).mkApp (bvars 1 ni ++ [.bvar 0])

/-! ### The ι-rules (F13/F14)

The rule's binder context is `params ++ motives ++ minors ++ fields`, with
`off := nm + nmin`. -/

def iotaCtx (C : VIndCtor) : List VExpr :=
  D.atRecTele D.params ++ D.motives ++ D.minors ++
    liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type)))

/-- The induction-hypothesis *values* (F14's `v`), living in `iotaCtx C`.

Unlike `ihTypes` these are not a telescope — they are all arguments in the same context —
so the offset below the fields is `nf - i`, with no `s`. -/
def ihValues (C : VIndCtor) : List VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  C.recFields.map fun (i, r) =>
    let d := nf - i
    let nxi := r.binders.length
    mkLams (shiftTele off d i (D.atRecTele r.binders)) <|
      (VExpr.const (Lean.mkRecName (D.types.getD r.idx default).name)
          (VLevel.params D.recUvars)).mkApp <|
        bvars (nxi + nf + off) D.np ++ bvars (nxi + nf + D.nmin) D.nm ++
        bvars (nxi + nf) D.nmin ++
        r.args.map (fun a => shift off d i (D.atRec a) nxi) ++
        [(VExpr.bvar (nxi + (nf - 1 - i))).mkApp (bvars 0 nxi)]

/-- The kernel's `RecursorRule.rhs` (F13):
`λ params motives minors fields. minor_q fields ihs`. -/
def iotaLam (q : Nat) (C : VIndCtor) : VExpr :=
  let nf := C.fields.length
  mkLams (D.iotaCtx C) <|
    (VExpr.bvar (nf + (D.nmin - 1 - q))).mkApp (bvars 0 nf ++ D.ihValues C)

/-- The ι-rule's left-hand side, un-abstracted, in the context `(iotaCtx C).reverse`:
`I_j.rec params motives minors π[p,b] (c params b)`.

Note the index arguments *are* present here even though `reduceRecursor` discards them
(F13); they are what makes the major-premise position depend only on the recursor's
name, which the `Params` orthogonality axioms need. -/
def iotaLhs (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  (VExpr.const (Lean.mkRecName (D.types.getD j default).name)
      (VLevel.params D.recUvars)).mkApp <|
    bvars (nf + off) D.np ++ bvars (nf + D.nmin) D.nm ++ bvars nf D.nmin ++
    C.args.map (fun a => (D.atRec a).liftN off nf) ++
    [D.ctorApp' C (nf + off) (bvars 0 nf)]

/-- The common type of the two sides of the ι-rule: `motive_j π[p,b] (c params b)`. -/
def iotaType (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf := C.fields.length
  (VExpr.bvar (nf + D.nmin + (D.nm - 1 - j))).mkApp <|
    C.args.map (fun a => (D.atRec a).liftN off nf) ++
    [D.ctorApp' C (nf + off) (bvars 0 nf)]

/-- One ι-rule.

**Do not "simplify" `rhs` to `iotaLam`'s body.**  It is the η-expansion `λ Γ'. (iotaLam) Γ'`
for two load-bearing reasons: it is literally what `reduceRecursor` computes (an unreduced
β-redex chain, `Reduce.lean:99–107`), and it makes `Params.extra_pat` hold **on the nose**,
since the pattern's right-hand side is `RHS.fixed (iotaLam …)` applied to the matched
argument paths.

That second reason has since become the decisive one.  The `Params` obligation for ι-rules
is now just four fields -- `pat_simple`, `pat_uniq`, `pat_wf`, `extra_pat` (the design's
four `pat_major_*` fields never existed, and the three `pat_app_*` ones have no consumer) --
and of those, `pat_simple` holds by construction of `SimplePattern.iota` and `extra_pat`'s
λ-peeled form matches this `rhs` definitionally.  So the shape chosen here is what leaves
`pat_wf` as the only field with real content. -/
def iotaRule (j q : Nat) (C : VIndCtor) : VDefEq :=
  let Γ' := D.iotaCtx C
  { uvars := D.recUvars
    lhs := mkLams Γ' (D.iotaLhs j C)
    rhs := mkLams Γ' ((D.iotaLam q C).mkApp (bvars 0 Γ'.length))
    type := mkPi Γ' (D.iotaType j C) }

def iotaRules : List VDefEq :=
  D.ctorsAll.zipIdx.map fun ((j, C), q) => D.iotaRule j q C

end VInductDecl'

/-- The block's recursor constants, in declaration order. -/
def VInductDecl'.recConsts (D : VInductDecl') : List (Name × VConstant) :=
  D.types.zipIdx.map fun (T, j) => (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)

/-- Everything `addInduct'` declares, in the order it declares it. -/
def VInductDecl'.allConsts (D : VInductDecl') : List (Name × VConstant) :=
  D.typeConsts ++ D.ctorConsts ++ D.recConsts

/-- Every name the declaration introduces: the types, then the constructors, then the
recursors -- the order in which `addInduct'` adds them. -/
def VInductDecl'.allNames (D : VInductDecl') : List Name := D.allConsts.map (·.1)

/-- Add the block's recursors, on top of `addIndCtors`. -/
def VEnv.addIndRecs (env : VEnv) (D : VInductDecl') : Option VEnv :=
  env.addConstList D.recConsts

/-- Add the block's ι-rules. -/
def VEnv.addIndRules (env : VEnv) (D : VInductDecl') : VEnv :=
  D.iotaRules.foldl VEnv.addDefEq env

/-- The environment extension performed by an inductive declaration.

Same shape as `VEnv.addQuot`, deliberately: `addQuot_WF` is the template for
`addInduct_WF`.  Because `addConst` fails on a duplicate name, `addInduct' = some _`
already implies that all of `D.allNames` are fresh **and pairwise distinct** — the global
disjointness invariant the `Params` orthogonality axioms need. -/
def VEnv.addInduct' (env : VEnv) (D : VInductDecl') : Option VEnv := do
  let env ← env.addIndTypes D
  let env ← env.addIndCtors D
  let env ← env.addIndRecs D
  return env.addIndRules D

end Lean4Lean
